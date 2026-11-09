module

public import CFSG.HardMathSupport.Timmesfeld.Steinberg.ThreeCharDataE8

@[expose] public section

namespace CertificateChecks.KernelDirect.C13691

open CFSG.HardMathSupport.Timmesfeld.Steinberg CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

variable {τ : Tag}

theorem decodeT_succ (n r : ℕ) : decodeT (n + 1) r = r % 256 :: decodeT n (r / 256) := by
  simp only [decodeT, List.range_succ_eq_map, List.map_cons, List.map_map]
  congr 1
  · simp
  · refine List.map_congr_left fun j _ => ?_
    simp [Nat.div_div_eq_div_mul, pow_succ']

theorem decodeT_encodeT : ∀ l : List ℕ, (∀ y ∈ l, y < 256) → decodeT l.length (encodeT l) = l
  | [], _ => by simp [decodeT]
  | a :: l, h => by
    have ha := h a (by simp)
    have e : encodeT (a :: l) = a + 256 * encodeT l := rfl
    have h1 : (a + 256 * encodeT l) % 256 = a := by omega
    have h2 : (a + 256 * encodeT l) / 256 = encodeT l := by omega
    rw [List.length_cons, decodeT_succ, e, h1, h2,
      decodeT_encodeT l fun y hy => h y (by simp [hy])]

noncomputable def memR (x : ℕ) (t : KTree) : Bool :=
  KTree.rec false (fun _ k _ ihl ihr => if x < k then ihl else if k < x then ihr else true) t

theorem memR_eq (x : ℕ) : ∀ t : KTree, memR x t = t.mem x
  | .nil => rfl
  | .node l k r => by
    change (if x < k then memR x l else if k < x then memR x r else true) = _
    rw [memR_eq x l, memR_eq x r]
    rfl

def digitP (P x : ℕ) : ℕ := P / 256 ^ x % 256

theorem getD_eq_digitP : ∀ (l : List ℕ) (x : ℕ), (∀ y ∈ l, y < 256) →
    l.getD x 0 = digitP (encodeT l) x
  | [], x, _ => by simp [digitP, encodeT]
  | a :: l, 0, h => by
    have ha := h a (by simp)
    change a = (a + 256 * encodeT l) / 256 ^ 0 % 256
    omega
  | a :: l, x + 1, h => by
    have ha := h a (by simp)
    rw [List.getD_cons_succ, getD_eq_digitP l x fun y hy => h y (by simp [hy])]
    change _ = (a + 256 * encodeT l) / 256 ^ (x + 1) % 256
    rw [pow_succ', ← Nat.div_div_eq_div_mul]
    unfold digitP
    congr 2
    omega

def htP (H x : ℕ) : ℤ := (digitP H x : ℤ) - 32

def htR (H x : ℕ) : ℤ := Int.sub (Int.ofNat (Nat.mod (Nat.div H (Nat.pow 256 x)) 256)) 32

theorem htR_eq (H : ℕ) : htR H = htP H := rfl

noncomputable def encDig (P : ℕ) (t : List ℕ) : ℕ :=
  List.rec 0 (fun x _ acc => Nat.add (Nat.mod (Nat.div P (Nat.pow 256 x)) 256) (Nat.mul 256 acc)) t

theorem encDig_eq (P : ℕ) : ∀ t : List ℕ, encDig P t = encodeT (t.map (digitP P))
  | [] => rfl
  | x :: t => by
    change digitP P x + 256 * encDig P t = _
    rw [encDig_eq P t]
    rfl

noncomputable def mapR (P : ℕ) (t : List ℕ) : List ℕ :=
  List.rec [] (fun x _ acc => Nat.mod (Nat.div P (Nat.pow 256 x)) 256 :: acc) t

theorem mapR_eq (P : ℕ) : ∀ t : List ℕ, mapR P t = t.map (digitP P)
  | [] => rfl
  | x :: t => by
    change digitP P x :: mapR P t = _
    rw [mapR_eq P t]
    rfl

noncomputable def dotR (f : ℕ → ℤ) (bv : List ℤ) : List ℕ → ℤ :=
  List.rec (fun _ => 0) (fun c _ ih t => List.rec 0
    (fun x xs _ => Int.add (if c = 0 then 0 else Int.mul c (f x)) (ih xs)) t) bv

theorem dotR_eq (f : ℕ → ℤ) : ∀ (bv : List ℤ) (t : List ℕ), dotR f bv t = dotL bv (t.map f)
  | [], t => by
    change (0 : ℤ) = _
    simp [dotL]
  | _ :: _, [] => by
    change (0 : ℤ) = _
    simp [dotL]
  | c :: cs, x :: xs => by
    change (if c = 0 then 0 else c * f x) + dotR f cs xs = _
    rw [dotR_eq f cs xs]
    simp only [dotL, List.map_cons, List.zipWith_cons_cons, List.sum_cons]
    split_ifs with h <;> simp [h]

noncomputable def fastStep (τ : Tag) (P H : ℕ) (Δl : List (List ℤ)) (tree : KTree)
    (t : List ℕ) (r : ℕ) : Bool :=
  if r < 256 ^ τ.rank then memR r tree && Nat.beq r (encDig P t)
  else match Δl[r - 256 ^ τ.rank]? with
    | some bv => !decide (0 < dotR (htR H) bv (mapR P t))
    | none => false

noncomputable def fastAll (τ : Tag) (Ps : List ℕ) (H : ℕ) (Δl : List (List ℤ)) (tree : KTree) :
    List ℕ → List (List ℕ) → List (List ℕ) → Bool
  | [], _, _ => true
  | _ :: _, [], _ => false
  | _ :: _, _ :: _, [] => false
  | k :: ks, tup :: tups, row :: rows =>
    (decodeT τ.rank k == tup) &&
      (List.range τ.rank).all (fun i => fastStep τ (Ps.getD i 0) H Δl tree tup (row.getD i 0)) &&
      fastAll τ Ps H Δl tree ks tups rows

theorem stepAux_of_fastStep {T : RootTables} {Δl : List (List ℤ)} {tree : KTree}
    {t : List ℕ} {i P H r : ℕ} (hI : ∀ x, (T.imgs.getD i []).getD x 0 = digitP P x)
    (hH : ∀ y, T.hts.getD (digitP P y) 0 = htP H (digitP P y))
    (ht : t.length = τ.rank) (h : fastStep τ P H Δl tree t r = true) :
    StabCert3.stepAux τ T Δl tree (imgL T i t) = true := by
  have himg : imgL T i t = t.map (digitP P) := List.map_congr_left fun x _ => hI x
  have hhs : hsL T (t.map (digitP P)) = (t.map (digitP P)).map (htP H) := by
    simp only [hsL, List.map_map]
    exact List.map_congr_left fun y _ => hH y
  rw [himg]
  unfold fastStep at h
  split at h
  · simp only [Bool.and_eq_true, memR_eq, encDig_eq] at h
    obtain ⟨hm, he⟩ := h
    have he' := Nat.eq_of_beq_eq_true he
    have hdec : decodeT τ.rank (encodeT (t.map (digitP P))) = t.map (digitP P) := by
      have := decodeT_encodeT (t.map (digitP P)) (by simp [digitP, Nat.mod_lt])
      rwa [List.length_map, ht] at this
    unfold StabCert3.stepAux
    rw [hdec, ← he', hm]
    simp
  · rw [mapR_eq] at h
    split at h
    · rename_i bv hbv
      have hmem : bv ∈ Δl := List.mem_of_getElem? hbv
      have hd : dTestL Δl (hsL T (t.map (digitP P))) = false := by
        rw [Bool.eq_false_iff]
        intro hd
        simp only [dTestL, List.all_eq_true, decide_eq_true_eq] at hd
        simp only [Bool.not_eq_true', decide_eq_false_iff_not] at h
        rw [dotR_eq, htR_eq, ← hhs] at h
        exact h (hd bv hmem)
      simp [StabCert3.stepAux, hd]
    · exact absurd h (by simp)

theorem all_stepAux_of_fastAll {T : RootTables} {Ps : List ℕ} {H : ℕ} {Δl : List (List ℤ)}
    {tree : KTree} (hI : ∀ i < τ.rank, ∀ x, (T.imgs.getD i []).getD x 0 = digitP (Ps.getD i 0) x)
    (hH : ∀ i < τ.rank, ∀ y,
      T.hts.getD (digitP (Ps.getD i 0) y) 0 = htP H (digitP (Ps.getD i 0) y)) :
    ∀ (keys : List ℕ) (tups rows : List (List ℕ)), fastAll τ Ps H Δl tree keys tups rows = true →
      (keys.all fun k => (List.range τ.rank).all fun i =>
        StabCert3.stepAux τ T Δl tree (imgL T i (decodeT τ.rank k))) = true
  | [], _, _, _ => rfl
  | _ :: _, [], _, h => by simp [fastAll] at h
  | _ :: _, _ :: _, [], h => by simp [fastAll] at h
  | k :: ks, tup :: tups, row :: rows, h => by
    simp only [fastAll, Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at h
    obtain ⟨⟨hk, hs⟩, hr⟩ := h
    simp only [List.all_cons, Bool.and_eq_true, List.all_eq_true]
    refine ⟨fun i hi => ?_, fun x hx => List.all_eq_true.1
      (List.all_eq_true.1 (all_stepAux_of_fastAll hI hH ks tups rows hr) x hx)⟩
    have hi' := List.mem_range.1 hi
    rw [hk]
    exact stepAux_of_fastStep (hI i hi') (hH i hi') (by rw [← hk]; simp [decodeT]) (hs i hi)

theorem getD_lt_of_all {l : List ℕ} {b x : ℕ} (hb : 0 < b) (h : ∀ y ∈ l, y < b) :
    l.getD x 0 < b := by
  rcases lt_or_ge x l.length with hx | hx
  · rw [List.getD_eq_getElem _ _ hx]
    exact h _ (List.getElem_mem hx)
  · rw [List.getD_eq_default _ _ hx]
    exact hb

theorem getD_eq_htP {l : List ℤ} {H x : ℕ} (hb : ∀ h ∈ l, -32 ≤ h ∧ h < 224)
    (hH : encodeT (l.map fun h => (h + 32).toNat) = H) (hx : x < l.length) :
    l.getD x 0 = htP H x := by
  have hall : ∀ y ∈ l.map (fun h => (h + 32).toNat), y < 256 := by
    simp only [List.mem_map]
    rintro y ⟨h, hh, rfl⟩
    have := hb h hh
    omega
  rw [htP, ← hH, ← getD_eq_digitP _ _ hall, List.getD_eq_getElem _ _ hx,
    List.getD_eq_getElem _ _ (by simpa using hx), List.getElem_map]
  have := hb _ (List.getElem_mem hx)
  omega

def e8ThreePs : List ℕ :=
  [89010710832726081258207695087766398200463822447299177309155950223496954771480073381370072123293542863666917681001240833256283624818489754498555458322516498157961804482136594522793577247931580969788919151717011204250375395838515833249763021009372996813790394276571930277680059071460880890989908604662129022113247131338312116266517895322679779819626508977962131054664801157016321681014941285255716885368621272211462762802988025965992631326069250879488166621064336762475956670274769308471563445497416518581046246431104946712360878611623974622039994175281513662114477524384232309000,
    89010710832726081258207694470442990890415515907869505779886046783396593103640325839892511643681981986162254957591558308685964926615759728467511235118665001233818740385399390901689204368962475112015703403693624400271714451472598171513675180897910456117989325841506258199375245204113263228777869367042200487651237736212000732122744295449498403536248818762319423155378669290615440768437604596047795875216167189021753281884432776001928819603815486524924527055899562613801810009627394022056681198409426139376673702664229374796888588155338570416165387393982045041438705604446763747840,
    89010710832726081258207694162343316416520743934833888554169891495955323651620152927734580516746067841961750947020686085945714659399602198773860883655777330057381498402205953603756174901056105804781890149560606415937690719442113994425150191211162517318371450274933269762232191684432189961131985307330009180903635803958640394192176421256977244821896278794895674787449004133544647674865309223652462386159860903053840768867423467135706882763078190031264035265969225967655596427564728602547226965189411755555944032614673702986694527253041247169227900477019519170271200725572076175625,
    89010710832726081258167316742817111858294325275036403260066597373445222969466303429860922259219528879929195473893346275529145034484616876716112906061514358982216786919788099420357786551583028325340943464439994945803179680089474620286890835813939055116281939722480452062319075887806300703768298350781696318932005763867578005513840632339908178319026058992790035346890912089776204346735459511032444581540032981950090818199726131355414776745177066531241297849415737218457523345217761794590417006893712365436636682112488267211160925628955797863204522479160605880967411022375531907840,
    89010710832726078611972480487740564865013298473574976328944954134456327284865961289716890820218830100492605777403994125833473809195044404827417494095797970075206970148418528423995926160544986078440518003909517423566942690941370572260537746666343952716802142533037816043123211579114155684164472179528106630940350586743601550550985538002513418888193547290612747125140928725796452419810975123804981827755094876758572242533872794989594596064603427185205881045216604549916329774851847516547008580299959337238849603513733266073271454452322354227927052072151437772419676362821433688320,
    89010710832552657587183667791156813198524440350351853816782733431091576398866055840793800400142071074497172173548804546548878458482500516096310519223865372323802588234813981328060658174618210340413770537734060573165051860010165968149955420621960514868463277438777783608661026192087831201300907722338615286427310094980195721092873410447546211439989274635625612773438679931465062557145457807614895227065601178988688189733812154145143897281906453450171259285161580193342006294745359904266602041590072464109002891460789622876321102533401062645385222816997417989792460202409860399360,
    89010699467232377027554784478407598184718476799534965190152491955430984881266199533006488366586396525393847940432801676891044982896061688467681114338651890362170337483169470564696543734439842263583183894083537598066282033534663265000291384112472455700783829789168127111359935076718971916512653331693725946015487667288988242196906461020166295432321794813530310110649809501584288168619378429276772480733972812118093524561556239503956052652022195188554112550264661852092020784826263706361665606622906102083373677519948717678393658244704722681076820407193621662048003785174970138880,
    88265861837325621189058000145852453397091210463921930350571492796122659908312032561426501150512066209527817503427558144168677221847401295442589276365006810773037662698873245037647687471534781180432188889776128520254184642228846001144169300736512664833234539515614938290125899094505784929183815306387429202845156500428931651406970764961731901383283627854431742951417424945035069896671101045399624337955161209468627078685136034741132861190543109113317624190633363423449421519875066101231496217756148459296262002941982001319520113739908372754817022308303477463314793404491683201280]

def e8ThreeH : ℕ :=
  1201364902607829168600078333990834474687171363748044497777490677070274114180099312578719286128793996087196498227835093807010345830901974671095359860764317569689644704000441677832033906841417803408734710687729812029007714736887749732753192670573300625684570724815567057341833071520293127698834804960394783174449054010278853943323161585224393394043994803958447551389625909369176375251010352484368804434215783577089916399936634714727357919855773617942104046250784325285258204515222140080010984229888046096910391416960857746276905120898329095788996437956302550515996786788430586145

set_option maxRecDepth 100000 in
theorem e8Three_imgs : ∀ i < Tag.E8.rank, ∀ x,
    ((RootTables.ofCert e8Certificate).imgs.getD i []).getD x 0 = digitP (e8ThreePs.getD i 0) x := by
  have hrows : ((List.range 8).all fun i =>
      ((RootTables.ofCert e8Certificate).imgs.getD i []).all (fun y => decide (y < 240)) &&
        encodeT ((RootTables.ofCert e8Certificate).imgs.getD i []) == e8ThreePs.getD i 0) =
      true := by
    decide +kernel
  simp only [List.all_eq_true, Bool.and_eq_true, beq_iff_eq, List.mem_range,
    decide_eq_true_eq] at hrows
  intro i hi x
  obtain ⟨hlt, he⟩ := hrows i hi
  rw [← he]
  exact getD_eq_digitP _ _ fun y hy => by have := hlt y hy; omega

set_option maxRecDepth 100000 in
theorem e8Three_hts : ∀ i < Tag.E8.rank, ∀ y,
    (RootTables.ofCert e8Certificate).hts.getD (digitP (e8ThreePs.getD i 0) y) 0 =
      htP e8ThreeH (digitP (e8ThreePs.getD i 0) y) := by
  have hrows : ((List.range 8).all fun i =>
      ((RootTables.ofCert e8Certificate).imgs.getD i []).all (fun y => decide (y < 240))) =
      true := by
    decide +kernel
  have hhts : ((RootTables.ofCert e8Certificate).hts.all fun h => decide (-32 ≤ h ∧ h < 224)) =
      true := by
    decide +kernel
  have hhtsP : encodeT ((RootTables.ofCert e8Certificate).hts.map fun h => (h + 32).toNat) =
      e8ThreeH := by
    decide +kernel
  have hlen : (RootTables.ofCert e8Certificate).hts.length = 240 := by
    decide +kernel
  simp only [List.all_eq_true, List.mem_range, decide_eq_true_eq] at hrows hhts
  intro i hi y
  refine getD_eq_htP hhts hhtsP ?_
  rw [hlen, ← e8Three_imgs i hi]
  exact getD_lt_of_all (by norm_num) (hrows i hi)

end CertificateChecks.KernelDirect.C13691
