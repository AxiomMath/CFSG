module

public import CFSG.Monster.B.GSide.HSylowBetaCertDataInputs

public section

namespace CertificateChecks.KernelBM.CTIB.HC5

open CFSG.Monster.B.GSide CFSG.Monster.B.CTIB.Native CFSG.Monster.B.CTIB CFSG.KC.BM
  CFSG.KC.BM.CosetQ CertificateChecks.KernelBM.CTIB CertificateChecks.KernelBM.CTIB.CosetQ
  CertificateChecks.KernelBM.CTIB.QK

@[expose] def Pset : List ℕ :=
  [0, 86921, 118446, 135412, 167379, 253530, 889064, 971669, 990523, 1015836, 1051608, 1087231,
   1164662, 1186604, 1263781, 1299842, 1856926, 1983850, 2021453, 2037475, 2105295, 2232123,
   2265628, 2317490, 2953728, 3066970, 3267257, 3316164, 3364714, 3394125, 3987318, 4131116,
   4234535, 4408189, 5004870, 5030753, 5049807, 5131954, 5331025, 5408267, 6080697, 6096407,
   6134576, 6261700, 6324968, 6376518, 6410593, 6537621, 7094665, 7134382, 7180071, 7229821,
   7275252, 7315411, 7345175, 7375152, 7423902, 7472355, 8145489, 8198616, 8226047, 8280741,
   8308610, 8360971, 8388608, 8475529, 8507054, 8524020, 8555987, 8642138, 9277672, 9360277,
   9379131, 9404444, 9440216, 9475839, 9553270, 9575212, 9652389, 9688450, 10245534, 10372458,
   10410061, 10426083, 10493903, 10620731, 10654236, 10706098, 11342336, 11455578, 11655865,
   11704772, 11753322, 11782733, 12375926, 12519724, 12623143, 12796797, 13393478, 13419361,
   13438415, 13520562, 13719633, 13796875, 14469305, 14485015, 14523184, 14650308, 14713576,
   14765126, 14799201, 14926229, 15483273, 15522990, 15568679, 15618429, 15663860, 15704019,
   15733783, 15763760, 15812510, 15860963, 16534097, 16587224, 16614655, 16669349, 16697218,
   16749579]

@[expose] def Ul : List ℕ :=
  [167378, 2, 7180067, 8198608, 2985783, 4166699, 1015900, 128, 7134638, 2318002, 5048783,
   2315442, 840545, 2240315, 16384, 6182989, 8247158, 8312694, 5916010, 7701759, 6539853, 5278000]

@[expose] def flipM : ℕ := 3922389

@[expose] noncomputable def memN (L : List ℕ) (x : ℕ) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun h _ ih => Nat.beq h x || ih) L

theorem memN_iff {L : List ℕ} {x : ℕ} : memN L x = true ↔ x ∈ L := by
  induction L with
  | nil => exact ⟨fun h => absurd h Bool.false_ne_true, fun h => absurd h List.not_mem_nil⟩
  | cons a L ih =>
    change (Nat.beq a x || memN L x) = true ↔ _
    rw [Bool.or_eq_true, Nat.beq_eq, ih, List.mem_cons, eq_comm]

@[expose] noncomputable def stepK (m p : ℕ) : ℕ :=
  mulQ LOq (mulQ LOq (nthN Ul m) (p % 2 ^ 23)) (2 ^ m) +
    2 ^ 23 * ((p / 2 ^ 23) ^^^ (flipM / 2 ^ m % 2))

@[expose] noncomputable def closK : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun p _ ih => allLt 22 (fun m => memN Pset (stepK m p)) && ih) Pset

@[expose] noncomputable def orbK : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun p _ ih => (!Nat.beq (p / 2 ^ 23) 0 || memN hc5Orbit p) && ih) Pset

theorem clos_ok : closK = true := by quickRfl

theorem orb_ok : orbK = true := by quickRfl

theorem pset_zero : memN Pset 0 = true := by quickRfl

theorem ul_ok : ∀ m < 22, nthN Ul m = hc5Inv (hc5ConjR (2 ^ m)) := by decide +kernel

theorem flip_ok : ∀ m < 22, flipM / 2 ^ m % 2 = (!hc5Comm (2 ^ m)).toNat := by decide +kernel


theorem clos_neg : (List.rec (motive := fun _ => Bool) true
    (fun p _ ih => allLt 22 (fun m => memN (Pset.drop 1) (stepK m p)) && ih) Pset) = false := by
  decide +kernel

theorem orb_neg : (List.rec (motive := fun _ => Bool) true
    (fun p _ ih => (!Nat.beq (p / 2 ^ 23) 0 || memN (hc5Orbit.drop 1) p) && ih) Pset) = false := by
  decide +kernel

theorem closK_sound (h : closK = true) : ∀ p ∈ Pset, ∀ m < 22, stepK m p ∈ Pset := by
  have key : ∀ L : List ℕ, (List.rec (motive := fun _ => Bool) true
      (fun p _ ih => allLt 22 (fun m => memN Pset (stepK m p)) && ih) L) = true →
      ∀ p ∈ L, ∀ m < 22, stepK m p ∈ Pset := by
    intro L
    induction L with
    | nil => intro _ p hp; exact absurd hp List.not_mem_nil
    | cons a L ih =>
      intro hL p hp m hm
      change (allLt 22 (fun m => memN Pset (stepK m a)) &&
        List.rec (motive := fun _ => Bool) true
          (fun p _ ih => allLt 22 (fun m => memN Pset (stepK m p)) && ih) L) = true at hL
      rw [Bool.and_eq_true] at hL
      rcases List.mem_cons.1 hp with rfl | hp
      · exact memN_iff.1 (allLt_true.1 hL.1 m hm)
      · exact ih hL.2 p hp m hm
  exact key Pset h

theorem orbK_sound (h : orbK = true) : ∀ p ∈ Pset, p / 2 ^ 23 = 0 → p ∈ hc5Orbit := by
  have key : ∀ L : List ℕ, (List.rec (motive := fun _ => Bool) true
      (fun p _ ih => (!Nat.beq (p / 2 ^ 23) 0 || memN hc5Orbit p) && ih) L) = true →
      ∀ p ∈ L, p / 2 ^ 23 = 0 → p ∈ hc5Orbit := by
    intro L
    induction L with
    | nil => intro _ p hp; exact absurd hp List.not_mem_nil
    | cons a L ih =>
      intro hL p hp h0
      change ((!Nat.beq (a / 2 ^ 23) 0 || memN hc5Orbit a) &&
        List.rec (motive := fun _ => Bool) true
          (fun p _ ih => (!Nat.beq (p / 2 ^ 23) 0 || memN hc5Orbit p) && ih) L) = true at hL
      rw [Bool.and_eq_true] at hL
      rcases List.mem_cons.1 hp with rfl | hp
      · rw [h0] at hL
        exact memN_iff.1 (by simpa using hL.1)
      · exact ih hL.2 p hp h0
  exact key Pset h

abbrev QG : Type := QC (gArr ())

theorem relH : RelOK (gArr ()) hc5Imgs := by
  have h : relOK (loOf (gArr ())) AH6 = true := by
    rw [← lo_eq]
    quickRfl
  have e : hc5Imgs = arrOf AH6 := by decide +kernel
  rw [e]
  exact (relOK_spec _ symG h).2

@[expose] noncomputable def αQ : QG →* QG := homOf (gArr ()) hc5Imgs relH

@[expose] def dQ : QG := ⟨10541, by decide⟩

@[expose] def eQ : QG := ⟨4456968, by decide⟩

@[expose] noncomputable def cQ (a : QG) : QG := dQ⁻¹ * αQ a * dQ

@[expose] noncomputable def zQ (a : QG) : QG := (cQ a)⁻¹ * a

@[expose] noncomputable def nQ (a : QG) : Bool := !hc5Comm a.1

theorem cQ_lt (a : QG) : (cQ a).1 < 2 ^ 23 := (cQ a).2

theorem cQ_mul (a b : QG) : cQ (a * b) = cQ a * cQ b := by
  simp only [cQ, map_mul]
  group

theorem zQ_mul (a b : QG) : zQ (a * b) = (cQ b)⁻¹ * zQ a * b := by
  simp only [zQ, cQ_mul]
  group

theorem cQ_one : cQ 1 = 1 := by
  simp only [cQ, map_one]
  group

theorem cQ_x : cQ xQ = xQ := by
  rw [cQ, αQ, hom_x, mul_assoc, xQ_comm dQ, ← mul_assoc, inv_mul_cancel, one_mul]

theorem hc5Inv_eq {k : ℕ} (hk : k < 2 ^ 23) : hc5Inv k = qinvG (gArr ()) k := by
  set a : QG := ⟨k, hk⟩
  have hp : piQ (a * a) = piQ (1 : QG) := by
    rw [piQ_mul, Nat.xor_self, piQ_one]
  rw [hc5Inv, qinvG]
  rcases eq_or_x hp with h | h
  · have h1 : qmul (gArr ()) k k = 0 := congrArg Subtype.val h
    rw [ite_eq_left h1, h1, qmul_zero_left _ hk]
  · have h1 : qmul (gArr ()) k k = 2 ^ 22 := by
      have := congrArg Subtype.val h
      rw [one_mul] at this
      exact this
    rw [ite_eq_right (by rw [h1]; decide), h1]
    exact congrArg Subtype.val (xQ_comm a).symm

theorem cQ_val (a : QG) : (cQ a).1 = hc5ConjR a.1 := by
  rw [cQ, QC.mul_val, QC.mul_val, QC.inv_val, αQ, homOf_val, hc5ConjR, hc5Inv_eq (by decide)]
  rfl

theorem zQ_val (a : QG) : (zQ a).1 = hc5Z a.1 := by
  rw [zQ, QC.mul_val, QC.inv_val, hc5Z, ← cQ_val, hc5Inv_eq (cQ a).2]

theorem nQ_val (a : QG) : nQ a = !hc5Comm a.1 := rfl

theorem x_ne_one : (xQ : QG) ≠ 1 := fun h => absurd (congrArg Subtype.val h) (by decide)

theorem comm_or (a : QG) : a * eQ = eQ * a ∨ a * eQ = eQ * a * xQ :=
  eq_or_x (by rw [piQ_mul, piQ_mul, Nat.xor_comm])

theorem nQ_of_comm {a : QG} (h : a * eQ = eQ * a) : nQ a = false := by
  have e : hc5Comm a.1 = true := beq_iff_eq.2 (congrArg Subtype.val h)
  rw [nQ, e]
  rfl

theorem nQ_of_x {a : QG} (h : a * eQ = eQ * a * xQ) : nQ a = true := by
  have e : hc5Comm a.1 = false := by
    refine Bool.eq_false_iff.2 fun hb => ?_
    have h' : a * eQ = eQ * a := QC.ext' (beq_iff_eq.1 hb)
    rw [h'] at h
    exact x_ne_one (mul_left_cancel (a := eQ * a) (by rw [mul_one]; exact h)).symm
  rw [nQ, e]
  rfl

theorem nQ_mul (a b : QG) : nQ (a * b) = (nQ a ^^ nQ b) := by
  rcases comm_or a with ha | ha <;> rcases comm_or b with hb | hb
  · rw [nQ_of_comm ha, nQ_of_comm hb, nQ_of_comm (by rw [mul_assoc, hb, ← mul_assoc, ha,
      mul_assoc])]
    rfl
  · have e : a * b * eQ = eQ * (a * b) * xQ := by
      rw [mul_assoc, hb]
      simp only [← mul_assoc]
      rw [ha]
    rw [nQ_of_comm ha, nQ_of_x hb, nQ_of_x e]
    rfl
  · have e : a * b * eQ = eQ * (a * b) * xQ := by
      rw [mul_assoc, hb]
      simp only [← mul_assoc]
      rw [ha, mul_assoc (eQ * a) xQ b, xQ_comm b]
      simp only [mul_assoc]
    rw [nQ_of_x ha, nQ_of_comm hb, nQ_of_x e]
    rfl
  · have e : a * b * eQ = eQ * (a * b) := by
      rw [mul_assoc, hb]
      simp only [← mul_assoc]
      rw [ha, mul_assoc (eQ * a) xQ b, xQ_comm b]
      simp only [mul_assoc]
      rw [xQ_sq, mul_one]
    rw [nQ_of_x ha, nQ_of_x hb, nQ_of_comm e]
    rfl

@[expose] noncomputable def enc (a : QG) : ℕ := (zQ a).1 + 2 ^ 23 * (nQ a).toNat

theorem enc_mod (a : QG) : enc a % 2 ^ 23 = (zQ a).1 := by
  rw [enc, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (zQ a).2]

theorem enc_div (a : QG) : enc a / 2 ^ 23 = (nQ a).toNat := by
  rw [enc, Nat.add_mul_div_left _ _ (by decide), Nat.div_eq_of_lt (zQ a).2, Nat.zero_add]

theorem enc_step (a : QG) {m : ℕ} (hm : m < 22) : stepK m (enc a) = enc (a * eK m hm) := by
  have hz : (zQ (a * eK m hm)).1 = mulQ LOq (mulQ LOq (nthN Ul m) (zQ a).1) (2 ^ m) := by
    have e0 : (eK (G := gArr ()) m hm).1 = 2 ^ m := rfl
    have e1 : hc5ConjR (2 ^ m) = (cQ (eK (G := gArr ()) m hm)).1 := by rw [cQ_val, e0]
    rw [zQ_mul, QC.mul_val, QC.mul_val, QC.inv_val, mulQ_eq, mulQ_eq, ul_ok m hm, e1,
      hc5Inv_eq (cQ_lt _)]
    rfl
  have hn : nQ (eK (G := gArr ()) m hm) = !hc5Comm (2 ^ m) := by
    rw [nQ_val]
    rfl
  rw [stepK, enc_mod, enc_div, ← hz, flip_ok m hm, enc, nQ_mul, hn]
  cases nQ a <;> cases hc5Comm (2 ^ m) <;> rfl

theorem enc_mem (a : QG) : enc a ∈ Pset := by
  have hcl := closK_sound clos_ok
  have h0 : (0 : ℕ) ∈ Pset := memN_iff.1 pset_zero
  refine gen_induct (fun a => enc a ∈ Pset) ?_ ?_ (fun a m hm ha => ?_) a
  · have hz : (zQ (1 : QG)).1 = 0 := by rw [zQ, cQ_one, inv_one, one_mul]; rfl
    have hn : nQ (1 : QG) = false := nQ_of_comm (by rw [one_mul, mul_one])
    rw [enc, hz, hn]
    exact h0
  · have hz : (zQ (xQ : QG)).1 = 0 := by rw [zQ, cQ_x, inv_mul_cancel]; rfl
    have hn : nQ (xQ : QG) = false := nQ_of_comm (xQ_comm eQ).symm
    rw [enc, hz, hn]
    exact h0
  · rw [← enc_step a hm]
    exact hcl _ ha m hm

theorem hc5_brute : Nat.all (2 ^ 23) (fun m _ => !hc5Comm m || hc5Orbit.contains (hc5Z m)) =
    true := by
  rw [Nat.all_eq_finRange_all, List.all_eq_true]
  rintro ⟨m, hm⟩ -
  change (!hc5Comm m || hc5Orbit.contains (hc5Z m)) = true
  cases hc : hc5Comm m
  · rfl
  set a : QG := ⟨m, hm⟩
  have hn : nQ a = false := by
    change (!hc5Comm m) = false
    rw [hc]
    rfl
  have hmem := orbK_sound orb_ok _ (enc_mem a) (by rw [enc_div, hn]; rfl)
  rw [enc, hn, zQ_val] at hmem
  simpa using hmem

@[expose] noncomputable def invK (k : ℕ) : ℕ := if mulQ LOq k k = 0 then k else mulQ LOq k (2 ^ 22)

@[expose] noncomputable def zK (m : ℕ) : ℕ :=
  mulQ LOq (invK (mulQ LOq (mulQ LOq (invK 10541) (autQ LOq AH6 m)) 10541)) m

@[expose] noncomputable def commK (m : ℕ) : Bool := mulQ LOq m 4456968 == mulQ LOq 4456968 m

theorem hc5Z_eq : hc5Z = zK := by
  have e : hc5Imgs = arrOf AH6 := by decide +kernel
  funext m
  simp only [hc5Z, zK, hc5ConjR, hc5Inv, invK, mulQ_eq, QK.autQ_eq, e]

theorem hc5Comm_eq : hc5Comm = commK := by
  funext m
  simp only [hc5Comm, commK, mulQ_eq]

theorem hc5_wit : hc5Wit.length = 64 ∧ hc5Orbit.length = 64 ∧
    (List.range 64).all (fun i => decide (hc5Wit.getD i 0 < 2 ^ 23) &&
      hc5Comm (hc5Wit.getD i 0) && hc5Z (hc5Wit.getD i 0) == hc5Orbit.getD i 0) = true := by
  rw [hc5Z_eq, hc5Comm_eq]
  decide +kernel

theorem hc5_nodup : hc5Orbit.Nodup := by decide +kernel

@[expose] def walks : List ℕ :=
  [773983849874164, 4246308800806191356, 7843755671230936, 142667121409203152, 4177513538360331,
   24113351671649795, 25858154211118543, 60159414489386951, 967225163025875, 2016447059410194395,
   12943267011121533, 13223803507856245, 6015907749125298, 420338737141472954, 1679880532119905,
   48114618943787881, 25605345993707186, 2282726166949940410, 416393394786107, 4498914567130419,
   33026439596758430, 3060755471030166, 401728264362661, 571886213652961453, 1925713688937834,
   236389138057058, 8681113199249708, 2216319805754148, 2162591907530654, 214694350095205782,
   1501242105922787, 96253357608797931, 2249038859737900, 773194167673559332, 799813747644159,
   2301153236655314167, 6610243210284839, 143928233361509679, 192376454861705, 134534796285399425,
   3075871603449414, 1971849538495339598, 3341268370248597, 125746736966324637, 236863761763398,
   285679353325768270, 16586670555223914, 530782285741905250, 51638934001745, 16729059494287961,
   7590947450784728, 51639584501795280, 201617112368663, 15188566361048095, 490060674765847,
   394064371379344927, 1512308087146661, 139433103374895789, 61886951264667833, 4465626388679345,
   30776392129910499, 26928000504894699, 410895834628989, 783028025725239669, 134918382424308,
   1150651404919378684, 67848140430651, 30961548206481203, 1618331504384452, 276689213715815372,
   102766258275702, 215044679838058366, 1089468525304505, 206452544043866289, 1642108441959216,
   69732862233516344, 2241763186295189, 4017051297779270557, 12761993584955054,
   1151616894240148646, 6183480190868775, 1008620201580994351, 133944545335152872,
   2161582512672445152, 966447741239324, 26668341847097876, 15012041054805166, 1951455580315302,
   1890467041790545, 35742901190805593, 4219363729916769, 132111466182001001, 403497755378408,
   33491051983700192, 3342148873148493, 534710024708741701, 6182258310174582, 105687994190058878,
   979343383561471, 399524916463351, 6004841766963789, 286782315994531909, 3754794299722032,
   2249588622003000, 1527628202778575, 211375985346747847, 129420827103744, 8839147695318306824,
   3014576013549523, 414039656501059035, 13226563017629274, 1111683220329978962, 122022745050052,
   1152182474862463436, 7579471264863618, 207013294972065674, 824071758299529, 120189450900226945,
   208585665464194, 278871329832879498, 554130882874458, 97578861825019474, 6745362847142428,
   1729359569763078164, 764567098656267, 8936234258170883]

open CertificateChecks.KernelBM.CTIB.Inner in
theorem rank_facts : ∀ j < 63, hc5Orbit.getD (j + 1) 0 < 2 ^ 23 ∧
    qmul gArr (hc5Orbit.getD (j + 1) 0) (hc5Orbit.getD (j + 1) 0) = 0 ∧
    walkOK (walks.getD (2 * j) 0) = true ∧ eRec (walks.getD (2 * j) 0) = 1 ∧
    eV (walks.getD (2 * j) 0) = hc5Orbit.getD (j + 1) 0 % 2 ^ 22 ∧
    eV (walks.getD (2 * j) 0) ≠ 0 ∧
    qmul gArr (2 ^ 22) (hc5Orbit.getD (j + 1) 0) % 2 ^ 22 = hc5Orbit.getD (j + 1) 0 % 2 ^ 22 ∧
    walkOK (walks.getD (2 * j + 1) 0) = true ∧ eRec (walks.getD (2 * j + 1) 0) = 2 ∧
    eV (walks.getD (2 * j + 1) 0) = qmul gArr 4456968 (hc5Orbit.getD (j + 1) 0) % 2 ^ 22 ∧
    eV (walks.getD (2 * j + 1) 0) ≠ 0 ∧
    qmul gArr 4456968 (qmul gArr (2 ^ 22) (hc5Orbit.getD (j + 1) 0)) % 2 ^ 22 =
      eV (walks.getD (2 * j + 1) 0) := by
  decide +kernel

open CertificateChecks.KernelBM.CTIB.Inner in
theorem hc5_rank_codes (hC : CensusLists) :
    hc5Orbit.all (fun z => decide (z < 2 ^ 23) && (z == 0 ||
      (qmul gArr z z == 0 && innerTyRank (innerTy innerTab z) == 2048 &&
        innerTyRank (innerTy innerTab (qmul gArr (2 ^ 22) z)) == 2048 &&
        innerTyRank (innerTy innerTab (qmul gArr 4456968 z)) == 2168 &&
        innerTyRank (innerTy innerTab (qmul gArr 4456968 (qmul gArr (2 ^ 22) z))) == 2168))) =
      true := by
  rw [List.all_eq_true]
  intro z hz
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hz
  have hlen : hc5Orbit.length = 64 := rfl
  rcases i with _ | j
  · have e : hc5Orbit[0] = 0 := rfl
    rw [e]
    rfl
  have hj : j < 63 := by omega
  have eg : hc5Orbit[j + 1] = hc5Orbit.getD (j + 1) 0 := (List.getD_eq_getElem _ _ hi).symm
  rw [eg]
  obtain ⟨hlt, hsq, wa, ka, va, a0, ex, wb, kb, vb, b0, ey⟩ := rank_facts j hj
  rw [innerTy_walk hC wa va.symm a0, innerTy_walk hC wa (ex.trans va.symm) a0,
    innerTy_walk hC wb vb.symm b0, innerTy_walk hC wb ey b0, ka, kb, hsq]
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq]
  exact ⟨hlt, Or.inr (by simp [innerTyRank])⟩

end CertificateChecks.KernelBM.CTIB.HC5

end
