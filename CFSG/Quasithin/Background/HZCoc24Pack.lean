module

public import CFSG.Quasithin.Background.HModChk
public import CFSG.Quasithin.Background.HFixSylMathieu

public section

namespace CFSG.Quasithin.H.Coc24Pack

open CFSG.Quasithin.H.ModChk CFSG.Quasithin.H.FixSyl

@[expose] def lane (x p : ℕ) : ℕ := Nat.land (Nat.shiftRight x (Nat.mul 5 p)) 31

@[expose] def packN (f : ℕ → ℕ) (n : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ) 0 (fun t acc => Nat.add acc (Nat.shiftLeft (f t) (Nat.mul 5 t))) n

@[expose] def getK (a j : ℕ) : ℕ :=
  Bool.rec (motive := fun _ => ℕ) 0 (lane a j) (Nat.blt j 24)

@[expose] def cK (a b : ℕ) : ℕ := packN (fun p => getK a (lane b p)) 24

@[expose] def idK : ℕ := 984818244535754528103549039458486304

@[expose, irreducible] def dec (x : ℕ) : Array ℕ := ((List.range 24).map fun p => lane x p).toArray

@[expose] def wK (L : List ℕ) (w : List ℕ) : ℕ :=
  List.rec (motive := fun _ => ℕ) idK (fun i _ ih => cK (L.getD i idK) ih) w

theorem lane_eq (x t : ℕ) : lane x t = x / 32 ^ t % 32 := by
  have h31 : (31 : ℕ) = 2 ^ 5 - 1 := rfl
  change (x >>> (5 * t)) &&& 31 = _
  rw [h31, Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow, pow_mul]
  rfl

theorem lane_lt (x t : ℕ) : lane x t < 32 := by
  rw [lane_eq]
  exact Nat.mod_lt _ (by norm_num)

theorem packN_succ (f : ℕ → ℕ) (n : ℕ) : packN f (n + 1) = packN f n + f n * 32 ^ n := by
  change packN f n + (f n <<< (5 * n)) = _
  rw [Nat.shiftLeft_eq, pow_mul]
  rfl

theorem packN_lt (f : ℕ → ℕ) (hf : ∀ t, f t < 32) (n : ℕ) : packN f n < 32 ^ n := by
  induction n with
  | zero => exact Nat.one_pos
  | succ n ih =>
    rw [packN_succ, pow_succ]
    have he := hf n
    nlinarith [Nat.one_le_pow n 32 (by norm_num)]

theorem packN_lane (f : ℕ → ℕ) (hf : ∀ t, f t < 32) (n t : ℕ) (ht : t < n) :
    lane (packN f n) t = f t := by
  rw [lane_eq]
  induction n with
  | zero => omega
  | succ n ih =>
    rw [packN_succ]
    have hP := packN_lt f hf n
    have he := hf n
    rcases Nat.lt_succ_iff_lt_or_eq.1 ht with h | h
    · obtain ⟨d, rfl⟩ : ∃ d, n = t + (d + 1) := ⟨n - t - 1, by omega⟩
      have key : f (t + (d + 1)) * 32 ^ (t + (d + 1)) = f (t + (d + 1)) * 32 ^ d * 32 * 32 ^ t := by
        ring
      rw [key, Nat.add_mul_div_right _ _ (pow_pos (by norm_num) _), Nat.add_mul_mod_self_right]
      exact ih (by omega)
    · subst h
      rw [Nat.add_mul_div_right _ _ (pow_pos (by norm_num) _), Nat.div_eq_of_lt hP, zero_add,
        Nat.mod_eq_of_lt he]

theorem getK_lt (a j : ℕ) : getK a j < 32 := by
  unfold getK
  cases Nat.blt j 24
  · exact Nat.zero_lt_succ _
  · exact lane_lt a j

theorem dec_get (x j : ℕ) : (dec x)[j]! = getK x j := by
  unfold dec getK
  cases hb : Nat.blt j 24
  · have h : ¬ j < 24 := fun h' => by simp [Nat.blt_eq.mpr h'] at hb
    rw [getElem!_neg _ j (by simpa using h)]
    rfl
  · have h : j < 24 := Nat.blt_eq.mp hb
    rw [getElem!_pos _ j (by simpa using h)]
    simp

theorem cArr_dec (a b : ℕ) : cArr (dec a) (dec b) = dec (cK a b) := by
  have hr : ∀ i ∈ List.range 24, (dec a)[(dec b)[i]!]! = lane (cK a b) i := by
    intro i hi
    have hi' := List.mem_range.1 hi
    rw [dec_get, dec_get, cK, packN_lane _ (fun t => getK_lt _ _) 24 i hi']
    have hb : Nat.blt i 24 = true := Nat.blt_eq.mpr hi'
    simp [getK, hb]
  unfold cArr
  conv_rhs => unfold dec
  rw [List.map_congr_left hr]

theorem idArr_dec : idArr = dec idK := by
  unfold dec
  decide +kernel

theorem wArr_dec (L w : List ℕ) : wArr (L.map dec) w = dec (wK L w) := by
  induction w with
  | nil => exact idArr_dec
  | cons i w ih =>
    rw [wArr.eq_2, ih, idArr_dec, List.getD_map, cArr_dec]
    rfl

theorem dec_inj {a b : ℕ} (h : a = b) : dec a = dec b := congrArg dec h

@[expose] def ktTab : ℕ :=
  60273068971149450910074051835829740050453660483222362658488234463854906807868844013205514430152728424141904445153758084780375418810902417564216668723999797562443213517859365213287710878396814782012705303236120852321686838225469496212587344535420583018044675663223133218138127320765162459974826379398059617227833898591198017627657710517088993714667100231798888543604505332180266023657760163888012845186712969931280387538349958491952931702303690927962793812942249325665825459716649245009771547368979511533015297876636936650888733019736126014587103304342676503137363678801891418042644242995367260432329646310422143460746303644207685278545893939671194979108832365626622031075052373161057994413151242872966973422188669039846696420803569100411522418934745963837837462753764763649927822009835107687275295758541393153050298692984580466327445769425445629068752594604085622725779271725807597830642642225049057227061225960304085856194337153296048229181284386170876857750100309453333985698031963184902246979143981891835397137126103022166047952629665887270760627242239625467033828323250369377407026620347433084477908862066804567418741485492551301634975911778797538776495438315711365424575702591793352927056607497589913950138088147883899661342305076967947210161326486793767114012892911520909746660949871967475947594883301546167617627373787854082443277918565698611020347487592056379519013010066443535429508694217459599029329440745490189918433769460005036500422270100743169770422104932956774521150745597338350761418638266284677655373129758442050351763862502815625130007917421196351920934887984216699128461656980507022806918983601694828118853189335835361997774105398685014864994824677134142718619382689289311046646102250245742999999494423383242772624481509626209137706962337970643330738019842580512013013664662956707823092767866993779593067385099514564915644403967680435061642551148905759445980929900339122926320808301023355320230242211262329334187218892963436162873546262862550977171475746227173525436802715677571239075816470997524801544352279811780202767243249000130518998251145737910535554896139217633023203295919264587449266798728006758631473556121201250775183164198862562619160630672212295460043150083418131371527837134918711952217638237740727606263276034631809409045024448228223843431570674897080233750223385910414583892000

@[expose] def kaTab : ℕ :=
  3564223804748491015793730699302132220861309071402445242636742982105451637997357778999375016676566196031252118235219862076295894908682636258667810255057744872177986194779624041918980852298726567621479955197248864880672

@[expose] def KT (c : ℕ) : ℕ :=
  Nat.land (Nat.shiftRight ktTab (Nat.mul 120 c)) 1329227995784915872903807060280344575

@[expose] def KA (i : ℕ) : ℕ :=
  Nat.land (Nat.shiftRight kaTab (Nat.mul 120 i)) 1329227995784915872903807060280344575

@[expose] def xK : ℕ := 387164785644157352384353642843878863

@[expose] def xiK : ℕ := 175450778703662247919127191165057452

@[expose] def yK : ℕ := 344409751248537383086909064529693232

@[expose] def yiK : ℕ := 298765085421624714157958291879507407

@[expose] def hexW (c : ℕ) : List ℕ :=
  (List.range 6).map fun j =>
    ((List.range 6).filter fun i => c.testBit i).foldl (fun a i => a ^^^ (ksWord i).getD j 0) 0

@[expose] def ksC (c : ℕ) : Array ℕ :=
  ((List.range 24).map fun p => (p % 4 ^^^ (hexW c).getD (p / 4) 0) + 4 * (p / 4)).toArray

theorem ksC_list : ∀ c < 64,
    ((List.range 24).map fun p => (p % 4 ^^^ (hexW c).getD (p / 4) 0) + 4 * (p / 4)) ==
      (List.range 24).map (fun p => lane (KT c) p) := by
  decide +kernel

theorem ksC_dec : ∀ c < 64, ksC c = dec (KT c) := by
  intro c hc
  unfold ksC dec
  rw [eq_of_beq (ksC_list c hc)]

theorem ksArr_list : ∀ i < 6,
    ((List.range 24).map fun p => (p % 4 ^^^ (ksWord i).getD (p / 4) 0) + 4 * (p / 4)) ==
      (List.range 24).map (fun p => lane (KA i) p) := by
  decide +kernel

theorem ksArr_dec : ∀ i < 6, ksArr i = dec (KA i) := by
  intro i hi
  unfold ksArr dec
  rw [eq_of_beq (ksArr_list i hi)]

theorem xor_pow_lt {c i : ℕ} (hc : c < 64) (hi : i < 6) : c ^^^ 2 ^ i < 64 :=
  Nat.xor_lt_two_pow (n := 6) hc (Nat.pow_lt_pow_right (by norm_num) hi)

end CFSG.Quasithin.H.Coc24Pack
