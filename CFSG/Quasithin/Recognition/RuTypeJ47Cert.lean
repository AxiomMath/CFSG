module

public import CFSG.Quasithin.Recognition.RuTypeTwoF4M
public import CFSG.Quasithin.Recognition.CertTwoF4Table
public import CFSG.Quasithin.Recognition.RuRank3Tits13
public import Certificates.Certificate7094
public import Certificates.Certificate2262
public import Certificates.Certificate2263
public import Certificates.Certificate2264
public import Certificates.Certificate2268
public import Certificates.Certificate2269
public import Certificates.Certificate2270
public import Certificates.Certificate7092
public import Certificates.Certificate8071
public import Certificates.Certificate8072
public import Certificates.Certificate8075
public import Certificates.Certificate8076
public import Certificates.Certificate8079
public import CFSG.Quasithin.Background.F6Basic
public import CFSG.Quasithin.Recognition.CertTitsAmalgamLocal
public import CFSG.Quasithin.Recognition.CertTwoLocalPair
public import CFSG.Quasithin.Recognition.GoldschmidtTripleQuotient

public section

namespace CFSG.Quasithin.RuType.J47

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Quasithin.RuRank3
  CFSG.Sporadic.Schreier.Tits CFSG.Certificates CFSG.Certificates.Native
open scoped Pointwise

local notation "TA" => CFSG.Sporadic.Schreier.Tits.titsA

theorem checkAll_spec :
    checkInTitsA = true ∧ checkLetterFix = true ∧ checkConjChain = true ∧ checkU = true ∧
      checkI = true ∧ checkFix = true ∧ checkBall = true ∧ checkY = true := by
  have h := Certificates.certificate7094
  simp only [checkAll, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩

theorem data_spec {a : Array ℕ} (ha : a ∈ dataArrs) :
    isInvA 1755 a (invA a) = true ∧ inTitsA a = true := by
  have h := checkAll_spec.1
  rw [checkInTitsA, List.all_eq_true] at h
  have := h a ha
  rw [Bool.and_eq_true] at this
  exact this

theorem letterFix_spec :
    titsPiArr[0]! = 0 ∧ lineFixedA titsPiArr 0 = true ∧ a1Arr[0]! = 1 ∧
      lineFixedA a1Arr 0 = true ∧ f2Arr[0]! = 0 ∧ eArr[0]! = 0 ∧
      eqA 1755 (mulA eArr eArr) (idA 1755) = true ∧ lineMapsA (mulA a1Arr eArr) 0 5 = true ∧
      jArr[0]! = 10 ∧ lineFixedA cArr 0 = true ∧ b0Arr[0]! = 0 ∧ aaArr[0]! = 0 ∧
      abArr[0]! = 0 := by
  have h := checkAll_spec.2.1
  simp only [checkLetterFix, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩, h13⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩

theorem chain_spec :
    inS titsZArr = true ∧ inS v1Arr = true ∧ inS v2Arr = true ∧ inS uArr = true ∧
      inS zpArr = true ∧ inS jpArr = true ∧ inS tArr = true ∧ inS w1Arr = true ∧
      inS tpArr = true := by
  have h := checkAll_spec.2.2.1
  simp only [checkConjChain, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at h
  exact h

theorem u_spec :
    eqA 1755 uArr titsZArr = false ∧
      eqA 1755 (mulA uArr titsZArr) (mulA titsZArr uArr) = true ∧
      eqA 1755 (powArr 1755 b0Arr 5) (idA 1755) = true ∧ eqA 1755 b0Arr (idA 1755) = false ∧
      eqA 1755 (mulA (mulA uArr b0Arr) uArr) (powArr 1755 b0Arr 4) = true := by
  have h := checkAll_spec.2.2.2.1
  simp only [checkU, Bool.and_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  exact ⟨h1, h2, h3, h4, h5⟩

theorem i_spec :
    eqA 1755 (mulA aaArr abArr) (mulA abArr aaArr) = true ∧
      eqA 1755 (mulA aaArr uArr) (mulA uArr aaArr) = true ∧
      eqA 1755 (mulA abArr uArr) (mulA uArr abArr) = true ∧ normB aaArr = true ∧
      normB abArr = true ∧
      (allLt 16 fun p => allLt 16 fun q => p == q || !(eqA 1755 (prodI p) (prodI q))) = true ∧
      (allLt 16 fun p => !(eqA 1755 (mulA (prodI p) (prodI p)) (idA 1755)) ||
        eqA 1755 (prodI p) (idA 1755) || eqA 1755 (prodI p) titsZArr ||
        eqA 1755 (prodI p) uArr || eqA 1755 (prodI p) tArr) = true := by
  have h := checkAll_spec.2.2.2.2.1
  rw [checkI] at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7⟩

theorem fix_spec : ptFixCount uArr = 91 ∧ ptFixCount tArr = 27 := by
  have h := checkAll_spec.2.2.2.2.2.1
  simp only [checkFix, Bool.and_eq_true, beq_iff_eq] at h
  exact h

theorem ball_spec :
    onLine 0 0 = true ∧ onLine 1 0 = true ∧ onLine 1 5 = true ∧ onLine 10 5 = true ∧
      ballFixed uArr 10 = true ∧ (allLt 1755 fun q => q == 10 || ballMoved uArr q) = true ∧
      (allLt 2925 fun v => !(onLine 0 v) || (List.range 3).all fun k =>
        allLt 2925 fun w => !(onLine titsLinePtArr[3 * v + k]! w && onLine 10 w) ||
          (v == 0 && titsLinePtArr[3 * v + k]! == 1)) = true ∧
      (allLt 2925 fun w => !(onLine 1 w && onLine 10 w) || w == 5) = true := by
  have h := checkAll_spec.2.2.2.2.2.2.1
  rw [checkBall] at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩

theorem y_spec :
    eqA 1755 (powArr 1755 cArr 3) (idA 1755) = true ∧ eqA 1755 cArr (idA 1755) = false ∧
      eqA 1755 (mulA cArr tpArr) (mulA tpArr cArr) = true ∧
      eqA 1755 (conjA cArr zpArr) jpArr = true := by
  have h := checkAll_spec.2.2.2.2.2.2.2
  simp only [checkY, Bool.and_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  exact ⟨h1, h2, h3, h4⟩

theorem piArr_zero : titsPiArr[0]! = 0 := letterFix_spec.1
theorem piArr_line : lineFixedA titsPiArr 0 = true :=
  letterFix_spec.2.1
theorem a1Arr_zero : a1Arr[0]! = 1 := letterFix_spec.2.2.1
theorem a1Arr_line : lineFixedA a1Arr 0 = true :=
  letterFix_spec.2.2.2.1
theorem f2Arr_zero : f2Arr[0]! = 0 := letterFix_spec.2.2.2.2.1
theorem eArr_zero : eArr[0]! = 0 := letterFix_spec.2.2.2.2.2.1
theorem eArr_sq :
    eqA 1755 (mulA eArr eArr) (idA 1755) = true := letterFix_spec.2.2.2.2.2.2.1
theorem a1eArr_line : lineMapsA (mulA a1Arr eArr) 0 5 = true :=
  letterFix_spec.2.2.2.2.2.2.2.1
theorem jArr_zero : jArr[0]! = 10 :=
  letterFix_spec.2.2.2.2.2.2.2.2.1
theorem cArr_line : lineFixedA cArr 0 = true :=
  letterFix_spec.2.2.2.2.2.2.2.2.2.1
theorem b0Arr_zero : b0Arr[0]! = 0 :=
  letterFix_spec.2.2.2.2.2.2.2.2.2.2.1
theorem aaArr_zero : aaArr[0]! = 0 :=
  letterFix_spec.2.2.2.2.2.2.2.2.2.2.2.1
theorem abArr_zero : abArr[0]! = 0 :=
  letterFix_spec.2.2.2.2.2.2.2.2.2.2.2.2

theorem inS_z : inS titsZArr = true := chain_spec.1
theorem inS_v1 : inS v1Arr = true := chain_spec.2.1
theorem inS_v2 : inS v2Arr = true := chain_spec.2.2.1
theorem inS_u : inS uArr = true := chain_spec.2.2.2.1
theorem inS_zp : inS zpArr = true := chain_spec.2.2.2.2.1
theorem inS_jp : inS jpArr = true := chain_spec.2.2.2.2.2.1
theorem inS_t : inS tArr = true := chain_spec.2.2.2.2.2.2.1
theorem inS_w1 : inS w1Arr = true := chain_spec.2.2.2.2.2.2.2.1
theorem inS_tp : inS tpArr = true := chain_spec.2.2.2.2.2.2.2.2

theorem b0Arr_pow :
    eqA 1755 (powArr 1755 b0Arr 5) (idA 1755) = true := u_spec.2.2.1
theorem b0Arr_ne : eqA 1755 b0Arr (idA 1755) = false :=
  u_spec.2.2.2.1
theorem uArr_b0 :
    eqA 1755 (mulA (mulA uArr b0Arr) uArr) (powArr 1755 b0Arr 4) = true := u_spec.2.2.2.2

theorem aa_comm_ab :
    eqA 1755 (mulA aaArr abArr) (mulA abArr aaArr) = true := i_spec.1
theorem aa_comm_u :
    eqA 1755 (mulA aaArr uArr) (mulA uArr aaArr) = true := i_spec.2.1
theorem ab_comm_u :
    eqA 1755 (mulA abArr uArr) (mulA uArr abArr) = true := i_spec.2.2.1
theorem aa_normB : normB aaArr = true := i_spec.2.2.2.1
theorem ab_normB : normB abArr = true := i_spec.2.2.2.2.1
theorem prodI_distinct :
    (allLt 16 fun p => allLt 16 fun q => p == q || !(eqA 1755 (prodI p) (prodI q))) = true :=
  i_spec.2.2.2.2.2.1
theorem prodI_inv :
    (allLt 16 fun p => !(eqA 1755 (mulA (prodI p) (prodI p)) (idA 1755)) ||
      eqA 1755 (prodI p) (idA 1755) || eqA 1755 (prodI p) titsZArr ||
      eqA 1755 (prodI p) uArr || eqA 1755 (prodI p) tArr) = true :=
  i_spec.2.2.2.2.2.2

theorem fix_u : ptFixCount uArr = 91 := fix_spec.1
theorem fix_t : ptFixCount tArr = 27 := fix_spec.2

theorem onLine_0_0 : onLine 0 0 = true := ball_spec.1
theorem onLine_1_0 : onLine 1 0 = true := ball_spec.2.1
theorem onLine_1_5 : onLine 1 5 = true := ball_spec.2.2.1
theorem onLine_10_5 : onLine 10 5 = true := ball_spec.2.2.2.1
theorem ball_fixed : ballFixed uArr 10 = true :=
  ball_spec.2.2.2.2.1
theorem ball_moved :
    (allLt 1755 fun q => q == 10 || ballMoved uArr q) = true := ball_spec.2.2.2.2.2.1
theorem inc_check :
    (allLt 2925 fun v => !(onLine 0 v) || (List.range 3).all fun k =>
      allLt 2925 fun w => !(onLine titsLinePtArr[3 * v + k]! w && onLine 10 w) ||
        (v == 0 && titsLinePtArr[3 * v + k]! == 1)) = true := ball_spec.2.2.2.2.2.2.1
theorem lp_check :
    (allLt 2925 fun w => !(onLine 1 w && onLine 10 w) || w == 5) = true := ball_spec.2.2.2.2.2.2.2

theorem cArr_pow :
    eqA 1755 (powArr 1755 cArr 3) (idA 1755) = true := y_spec.1
theorem cArr_ne : eqA 1755 cArr (idA 1755) = false := y_spec.2.1
theorem cArr_comm_tp :
    eqA 1755 (mulA cArr tpArr) (mulA tpArr cArr) = true := y_spec.2.2.1
theorem cArr_conj_zp : eqA 1755 (conjA cArr zpArr) jpArr = true :=
  y_spec.2.2.2

theorem rep_mulA {t u : Array ℕ} {g h : Equiv.Perm (Fin 1755)} (ht : Rep 1755 t g)
    (hu : Rep 1755 u h) : Rep 1755 (mulA t u) (g * h) := by
  unfold mulA
  exact rep_compA ht hu

theorem rep_conjA {t x : Array ℕ} {g y : Equiv.Perm (Fin 1755)} (ht : Rep 1755 t g)
    (hti : Rep 1755 (invA t) g⁻¹) (hx : Rep 1755 x y) : Rep 1755 (conjA t x) (g * y * g⁻¹) := by
  unfold conjA
  exact rep_mulA (rep_mulA ht hx) hti

theorem rep_conjInvA {t x : Array ℕ} {g y : Equiv.Perm (Fin 1755)} (ht : Rep 1755 t g)
    (hti : Rep 1755 (invA t) g⁻¹) (hx : Rep 1755 x y) :
    Rep 1755 (conjInvA t x) (g⁻¹ * y * g) := by
  unfold conjInvA
  exact rep_mulA (rep_mulA hti hx) ht

theorem apply_eq_of_get {a : Array ℕ} {g : Equiv.Perm (Fin 1755)} (ha : Rep 1755 a g)
    {x y : Fin 1755} (h : a[(x : ℕ)]! = (y : ℕ)) : g x = y :=
  Fin.ext (by rw [← ha x]; exact h)

theorem apply_ne_of_get {a : Array ℕ} {g : Equiv.Perm (Fin 1755)} (ha : Rep 1755 a g)
    {x y : Fin 1755} (h : a[(x : ℕ)]! ≠ (y : ℕ)) : g x ≠ y := fun he =>
  h (by rw [ha x, he])

noncomputable abbrev perm (a : Array ℕ) : Equiv.Perm (Fin 1755) := permOfArr 1755 a

theorem rep_perm {a : Array ℕ} (ha : a ∈ dataArrs) :
    Rep 1755 a (perm a) :=
  (rep_permOfArr (data_spec ha).1).1

theorem rep_perm_inv {a : Array ℕ} (ha : a ∈ dataArrs) :
    Rep 1755 (invA a) (perm a)⁻¹ :=
  (rep_permOfArr (data_spec ha).1).2

theorem perm_mem_titsA {a : Array ℕ}
    (ha : a ∈ dataArrs) : perm a ∈ TA :=
  mem_titsA_of_inTitsA (rep_perm ha) (data_spec ha).2

theorem a1_mem : a1Arr ∈ dataArrs := by simp [dataArrs]
theorem f2_mem : f2Arr ∈ dataArrs := by simp [dataArrs]
theorem e_mem : eArr ∈ dataArrs := by simp [dataArrs]
theorem c_mem : cArr ∈ dataArrs := by simp [dataArrs]
theorem b0_mem : b0Arr ∈ dataArrs := by simp [dataArrs]
theorem aa_mem : aaArr ∈ dataArrs := by simp [dataArrs]
theorem ab_mem : abArr ∈ dataArrs := by simp [dataArrs]

noncomputable abbrev a1P : Equiv.Perm (Fin 1755) := perm a1Arr
noncomputable abbrev f2P : Equiv.Perm (Fin 1755) := perm f2Arr
noncomputable abbrev eP : Equiv.Perm (Fin 1755) := perm eArr
noncomputable abbrev cP : Equiv.Perm (Fin 1755) := perm cArr
noncomputable abbrev b0P : Equiv.Perm (Fin 1755) := perm b0Arr
noncomputable abbrev aaP : Equiv.Perm (Fin 1755) := perm aaArr
noncomputable abbrev abP : Equiv.Perm (Fin 1755) := perm abArr

@[expose] noncomputable def jP : Equiv.Perm (Fin 1755) := a1P * eP * a1P⁻¹
@[expose] noncomputable def v1P : Equiv.Perm (Fin 1755) := a1P⁻¹ * titsZ * a1P
@[expose] noncomputable def v2P : Equiv.Perm (Fin 1755) := eP * v1P * eP⁻¹
@[expose] noncomputable def uP : Equiv.Perm (Fin 1755) := a1P * v2P * a1P⁻¹
@[expose] noncomputable def tP : Equiv.Perm (Fin 1755) := uP * titsZ
@[expose] noncomputable def zpP : Equiv.Perm (Fin 1755) := f2P⁻¹ * v1P * f2P
@[expose] noncomputable def jpP : Equiv.Perm (Fin 1755) := f2P⁻¹ * eP * f2P
@[expose] noncomputable def w1P : Equiv.Perm (Fin 1755) := a1P⁻¹ * tP * a1P
@[expose] noncomputable def tpP : Equiv.Perm (Fin 1755) := f2P⁻¹ * w1P * f2P

theorem jP_def : jP = a1P * eP * a1P⁻¹ := rfl
theorem v1P_def : v1P = a1P⁻¹ * titsZ * a1P := rfl
theorem v2P_def : v2P = eP * v1P * eP⁻¹ := rfl
theorem uP_def : uP = a1P * v2P * a1P⁻¹ := rfl
theorem tP_def : tP = uP * titsZ := rfl
theorem zpP_def : zpP = f2P⁻¹ * v1P * f2P := rfl
theorem jpP_def : jpP = f2P⁻¹ * eP * f2P := rfl
theorem w1P_def : w1P = a1P⁻¹ * tP * a1P := rfl
theorem tpP_def : tpP = f2P⁻¹ * w1P * f2P := rfl

theorem rep_a1 : Rep 1755 a1Arr a1P := rep_perm a1_mem

theorem rep_f2 : Rep 1755 f2Arr f2P := rep_perm f2_mem

theorem rep_e : Rep 1755 eArr eP := rep_perm e_mem

theorem rep_c : Rep 1755 cArr cP := rep_perm c_mem

theorem rep_b0 : Rep 1755 b0Arr b0P := rep_perm b0_mem

theorem rep_aa : Rep 1755 aaArr aaP := rep_perm aa_mem

theorem rep_ab : Rep 1755 abArr abP := rep_perm ab_mem

theorem rep_j : Rep 1755 jArr jP :=
  rep_conjA rep_a1 (rep_perm_inv a1_mem) rep_e

theorem rep_v1 :
    Rep 1755 v1Arr v1P :=
  rep_conjInvA rep_a1 (rep_perm_inv a1_mem) titsZ_rep

theorem rep_v2 :
    Rep 1755 v2Arr v2P :=
  rep_conjA rep_e (rep_perm_inv e_mem) rep_v1

theorem rep_u :
    Rep 1755 uArr uP :=
  rep_conjA rep_a1 (rep_perm_inv a1_mem) rep_v2

theorem rep_t :
    Rep 1755 tArr tP :=
  rep_mulA rep_u titsZ_rep

theorem rep_zp :
    Rep 1755 zpArr zpP :=
  rep_conjInvA rep_f2 (rep_perm_inv f2_mem) rep_v1

theorem rep_jp : Rep 1755 jpArr jpP :=
  rep_conjInvA rep_f2 (rep_perm_inv f2_mem) rep_e

theorem rep_w1 :
    Rep 1755 w1Arr w1P :=
  rep_conjInvA rep_a1 (rep_perm_inv a1_mem) rep_t

theorem rep_tp :
    Rep 1755 tpArr tpP :=
  rep_conjInvA rep_f2 (rep_perm_inv f2_mem) rep_w1

theorem titsLine_mem_iff
    (p : Fin 1755) (v : Fin 2925) : p ∈ titsLine v ↔ onLine p v = true := by
  have hpt : ∀ k < 3, (titsLinePt v k : ℕ) = titsLinePtArr[3 * (v : ℕ) + k]! :=
    fun k hk => titsLinePt_val v hk
  have h0 := hpt 0 (by norm_num)
  rw [Nat.add_zero] at h0
  rw [titsLine_eq, Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton, onLine,
    Bool.or_eq_true, Bool.or_eq_true, beq_iff_eq, beq_iff_eq, beq_iff_eq, ← h0,
    ← hpt 1 (by norm_num), ← hpt 2 (by norm_num), Fin.ext_iff, Fin.ext_iff, Fin.ext_iff]
  constructor
  · rintro (h | h | h)
    · exact Or.inl (Or.inl h.symm)
    · exact Or.inl (Or.inr h.symm)
    · exact Or.inr h.symm
  · rintro ((h | h) | h)
    · exact Or.inl h.symm
    · exact Or.inr (Or.inl h.symm)
    · exact Or.inr (Or.inr h.symm)

theorem card_titsLine
    (v : Fin 2925) : (titsLine v).card = 3 := by
  obtain ⟨h1, h2⟩ := titsLinePt_lt v
  rw [titsLine_eq, Finset.card_insert_of_notMem, Finset.card_pair (ne_of_lt h2)]
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
  exact ⟨ne_of_lt h1, ne_of_lt (h1.trans h2)⟩

theorem linePt_mem
    (v : Fin 2925) {k : ℕ} (hk : k < 3) : titsLinePt v k ∈ titsLine v := by
  rw [titsLine_eq]
  interval_cases k <;> simp

theorem exists_linePt_of_mem
    {p : Fin 1755} {v : Fin 2925} (h : p ∈ titsLine v) : ∃ k < 3, titsLinePt v k = p := by
  rw [titsLine_eq, Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at h
  rcases h with h | h | h
  · exact ⟨0, by norm_num, h.symm⟩
  · exact ⟨1, by norm_num, h.symm⟩
  · exact ⟨2, by norm_num, h.symm⟩

theorem lineMapsA_spec
    {a : Array ℕ} {g : Equiv.Perm (Fin 1755)} (ha : Rep 1755 a g) (v w : Fin 2925)
    (h : lineMapsA a v w = true) : g • titsLine v = titsLine w := by
  rw [lineMapsA, List.all_eq_true] at h
  apply Finset.eq_of_subset_of_card_le
  · intro y hy
    rw [Finset.mem_smul_finset] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    obtain ⟨k, hk, rfl⟩ := exists_linePt_of_mem hx
    have h1 := h k (List.mem_range.2 hk)
    rw [← titsLinePt_val v hk, ha (titsLinePt v k)] at h1
    exact (titsLine_mem_iff _ w).2 h1
  · rw [Finset.card_smul_finset, card_titsLine, card_titsLine]

theorem smul_mem_lineHom
    {g : Equiv.Perm (Fin 1755)} (hg : g ∈ TA) {p : Fin 1755}
    {v : Fin 2925} (hp : p ∈ titsLine v) : g p ∈ titsLine (titsLineHom ⟨g, hg⟩ v) := by
  rw [titsLine_lineHom]
  exact Finset.smul_mem_smul_finset hp

theorem fix_zero_of_mem_titsH
    {x : Equiv.Perm (Fin 1755)} (hx : x ∈ titsH) : x 0 = 0 := by
  rw [titsH_eq_stab] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  have h := MulAction.mem_stabilizer_iff.mp (Subgroup.mem_comap.mp hy)
  simpa using h

theorem mem_titsH_of
    {x : Equiv.Perm (Fin 1755)} (hx : x ∈ titsD)
    (h0 : x 0 = 0) : x ∈ titsH := by
  rw [titsH_eq_stab]
  exact ⟨⟨x, hx⟩, Subgroup.mem_comap.mpr (MulAction.mem_stabilizer_iff.mpr h0), rfl⟩

theorem line_fix_of_mem_titsN
    {x : Equiv.Perm (Fin 1755)}
    (hx : x ∈ titsN) : x • titsLine 0 = titsLine 0 := by
  rw [titsN_eq_stab] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  have h := MulAction.mem_stabilizer_iff.mp (Subgroup.mem_comap.mp hy)
  rw [Equiv.Perm.smul_def] at h
  exact (lineHom_fixed_iff (Subgroup.inclusion titsD_le_titsA y) 0).mp h

theorem mem_titsN_of
    {x : Equiv.Perm (Fin 1755)}
    (hx : x ∈ titsD) (hL : x • titsLine 0 = titsLine 0) : x ∈ titsN := by
  rw [titsN_eq_stab]
  exact ⟨⟨x, hx⟩, Subgroup.mem_comap.mpr (MulAction.mem_stabilizer_iff.mpr
    ((lineHom_fixed_iff (Subgroup.inclusion titsD_le_titsA ⟨x, hx⟩) 0).mpr hL)), rfl⟩

theorem tπ_zero : tπ 0 = 0 :=
  apply_eq_of_get tπ_rep piArr_zero

theorem tπ_line :
    tπ • titsLine 0 = titsLine 0 :=
  (lineFixedA_iff tπ_rep 0).mp piArr_line

theorem tπ_inv_zero :
    tπ⁻¹ 0 = 0 := by
  rw [Equiv.Perm.inv_eq_iff_eq]
  exact tπ_zero.symm

theorem tπ_inv_line :
    tπ⁻¹ • titsLine 0 = titsLine 0 := by
  conv_lhs => rw [← tπ_line]
  rw [inv_smul_smul]

theorem mem_twoF4H_iff
    {x : Equiv.Perm (Fin 1755)} (hx : x ∈ TA) : x ∈ twoF4H ↔ x 0 = 0 := by
  have hM : x ∈ twoF4M := by rw [twoF4M_eq_titsA]; exact hx
  constructor
  · rintro (h | h)
    · exact fix_zero_of_mem_titsH h
    · have h0 := fix_zero_of_mem_titsH h
      rwa [Equiv.Perm.mul_apply, tπ_inv_zero] at h0
  · intro h0
    rcases hM with hD | hD
    · exact Or.inl (mem_titsH_of hD h0)
    · refine Or.inr (mem_titsH_of hD ?_)
      rw [Equiv.Perm.mul_apply, tπ_inv_zero, h0]

theorem mem_twoF4N_iff
    {x : Equiv.Perm (Fin 1755)} (hx : x ∈ TA) :
    x ∈ twoF4N ↔ x • titsLine 0 = titsLine 0 := by
  have hM : x ∈ twoF4M := by rw [twoF4M_eq_titsA]; exact hx
  constructor
  · rintro (h | h)
    · exact line_fix_of_mem_titsN h
    · have h0 := line_fix_of_mem_titsN h
      rwa [mul_smul, tπ_inv_line] at h0
  · intro h0
    rcases hM with hD | hD
    · exact Or.inl (mem_titsN_of hD h0)
    · refine Or.inr (mem_titsN_of hD ?_)
      rw [mul_smul, tπ_inv_line, h0]

theorem mem_twoF4S_iff
    {x : Equiv.Perm (Fin 1755)} (hx : x ∈ TA) :
    x ∈ twoF4S ↔ x 0 = 0 ∧ x • titsLine 0 = titsLine 0 := by
  rw [← twoF4H_inf_twoF4N, Subgroup.mem_inf, mem_twoF4H_iff hx, mem_twoF4N_iff hx]

theorem mem_twoF4S_of_inS
    {a : Array ℕ} {x : Equiv.Perm (Fin 1755)} (ha : Rep 1755 a x) (hx : x ∈ TA)
    (h : inS a = true) : x ∈ twoF4S := by
  rw [inS, Bool.and_eq_true, beq_iff_eq] at h
  exact (mem_twoF4S_iff hx).2 ⟨apply_eq_of_get ha h.1, (lineFixedA_iff ha 0).mp h.2⟩

theorem mem_A_of_mem_twoF4H
    {x : Equiv.Perm (Fin 1755)} (hx : x ∈ twoF4H) : x ∈ TA := by
  rw [← twoF4M_eq_titsA]
  rcases hx with h | h
  · exact Or.inl (titsH_le_titsD h)
  · exact Or.inr (titsH_le_titsD h)

theorem titsZ_mem_A :
    titsZ ∈ TA :=
  titsD_le_titsA (titsS_le_titsD titsZ_mem_titsS)

theorem a1P_mem_A : a1P ∈ TA :=
  perm_mem_titsA a1_mem

theorem f2P_mem_A : f2P ∈ TA :=
  perm_mem_titsA f2_mem

theorem eP_mem_A : eP ∈ TA :=
  perm_mem_titsA e_mem

theorem cP_mem_A : cP ∈ TA :=
  perm_mem_titsA c_mem

theorem b0P_mem_A : b0P ∈ TA :=
  perm_mem_titsA b0_mem

theorem aaP_mem_A : aaP ∈ TA :=
  perm_mem_titsA aa_mem

theorem abP_mem_A : abP ∈ TA :=
  perm_mem_titsA ab_mem

theorem jP_mem_A : jP ∈ TA :=
  mul_mem (mul_mem a1P_mem_A eP_mem_A) (inv_mem a1P_mem_A)

theorem v1P_mem_A :
    v1P ∈ TA :=
  mul_mem (mul_mem (inv_mem a1P_mem_A) titsZ_mem_A) a1P_mem_A

theorem v2P_mem_A :
    v2P ∈ TA :=
  mul_mem (mul_mem eP_mem_A v1P_mem_A) (inv_mem eP_mem_A)

theorem uP_mem_A :
    uP ∈ TA :=
  mul_mem (mul_mem a1P_mem_A v2P_mem_A) (inv_mem a1P_mem_A)

theorem tP_mem_A :
    tP ∈ TA :=
  mul_mem uP_mem_A titsZ_mem_A

theorem zpP_mem_A :
    zpP ∈ TA :=
  mul_mem (mul_mem (inv_mem f2P_mem_A) v1P_mem_A) f2P_mem_A

theorem jpP_mem_A : jpP ∈ TA :=
  mul_mem (mul_mem (inv_mem f2P_mem_A) eP_mem_A) f2P_mem_A

theorem w1P_mem_A :
    w1P ∈ TA :=
  mul_mem (mul_mem (inv_mem a1P_mem_A) tP_mem_A) a1P_mem_A

theorem tpP_mem_A :
    tpP ∈ TA :=
  mul_mem (mul_mem (inv_mem f2P_mem_A) w1P_mem_A) f2P_mem_A

theorem a1P_zero : a1P 0 = 1 :=
  apply_eq_of_get rep_a1 a1Arr_zero

theorem a1P_line :
    a1P • titsLine 0 = titsLine 0 :=
  (lineFixedA_iff rep_a1 0).mp a1Arr_line

theorem a1P_inv_line :
    a1P⁻¹ • titsLine 0 = titsLine 0 := by
  conv_lhs => rw [← a1P_line]
  rw [inv_smul_smul]

theorem a1P_inv_one : a1P⁻¹ 1 = 0 := by
  rw [Equiv.Perm.inv_eq_iff_eq]
  exact a1P_zero.symm

theorem f2P_zero : f2P 0 = 0 :=
  apply_eq_of_get rep_f2 f2Arr_zero

theorem eP_zero : eP 0 = 0 :=
  apply_eq_of_get rep_e eArr_zero

theorem eP_mul_self : eP * eP = 1 :=
  eq_of_eqA (rep_mulA rep_e rep_e) rep_idA eArr_sq

theorem eP_inv : eP⁻¹ = eP :=
  inv_eq_of_mul_eq_one_right eP_mul_self

theorem a1eP_line :
    (a1P * eP) • titsLine 0 = titsLine 5 :=
  lineMapsA_spec (rep_mulA rep_a1 rep_e) 0 5
    a1eArr_line

theorem jP_zero : jP 0 = 10 :=
  apply_eq_of_get rep_j jArr_zero

theorem jP_mul_self : jP * jP = 1 := by
  calc jP * jP = a1P * (eP * eP) * a1P⁻¹ := by unfold jP; group
    _ = 1 := by rw [eP_mul_self]; group

theorem jP_inv : jP⁻¹ = jP :=
  inv_eq_of_mul_eq_one_right jP_mul_self

theorem jP_ten : jP 10 = 0 := by
  rw [← jP_zero, ← Equiv.Perm.mul_apply, jP_mul_self, Equiv.Perm.one_apply]

theorem jP_line :
    jP • titsLine 0 = titsLine 5 := by
  rw [show jP = (a1P * eP) * a1P⁻¹ from rfl, mul_smul, a1P_inv_line, a1eP_line]

theorem jP_line5 :
    jP • titsLine 5 = titsLine 0 := by
  rw [← jP_line, ← mul_smul, jP_mul_self, one_smul]

theorem a1P_mem_N :
    a1P ∈ twoF4N :=
  (mem_twoF4N_iff a1P_mem_A).2 a1P_line

theorem a1P_not_mem_H :
    a1P ∉ twoF4H := by
  rw [mem_twoF4H_iff a1P_mem_A, a1P_zero]
  decide

theorem f2P_mem_H :
    f2P ∈ twoF4H :=
  (mem_twoF4H_iff f2P_mem_A).2 f2P_zero

theorem eP_mem_H :
    eP ∈ twoF4H :=
  (mem_twoF4H_iff eP_mem_A).2 eP_zero

theorem eP_not_mem_N :
    eP ∉ twoF4N := by
  rw [mem_twoF4N_iff eP_mem_A]
  intro h
  have h5 := a1eP_line
  rw [mul_smul, h, a1P_line] at h5
  exact absurd (titsLine_injective h5) (by decide)

theorem cP_mem_N :
    cP ∈ twoF4N :=
  (mem_twoF4N_iff cP_mem_A).2 ((lineFixedA_iff rep_c 0).mp
    cArr_line)

theorem b0P_mem_H :
    b0P ∈ twoF4H :=
  (mem_twoF4H_iff b0P_mem_A).2 (apply_eq_of_get rep_b0
    b0Arr_zero)

theorem aaP_mem_H :
    aaP ∈ twoF4H :=
  (mem_twoF4H_iff aaP_mem_A).2 (apply_eq_of_get rep_aa
    aaArr_zero)

theorem abP_mem_H :
    abP ∈ twoF4H :=
  (mem_twoF4H_iff abP_mem_A).2 (apply_eq_of_get rep_ab
    abArr_zero)

theorem titsZ_mem_S :
    titsZ ∈ twoF4S :=
  mem_twoF4S_of_inS titsZ_rep titsZ_mem_A inS_z

theorem v1P_mem_S :
    v1P ∈ twoF4S :=
  mem_twoF4S_of_inS rep_v1 v1P_mem_A inS_v1

theorem v2P_mem_S :
    v2P ∈ twoF4S :=
  mem_twoF4S_of_inS rep_v2 v2P_mem_A inS_v2

theorem uP_mem_S :
    uP ∈ twoF4S :=
  mem_twoF4S_of_inS rep_u uP_mem_A inS_u

theorem zpP_mem_S :
    zpP ∈ twoF4S :=
  mem_twoF4S_of_inS rep_zp zpP_mem_A inS_zp

theorem jpP_mem_S :
    jpP ∈ twoF4S :=
  mem_twoF4S_of_inS rep_jp jpP_mem_A inS_jp

theorem tP_mem_S :
    tP ∈ twoF4S :=
  mem_twoF4S_of_inS rep_t tP_mem_A inS_t

theorem w1P_mem_S :
    w1P ∈ twoF4S :=
  mem_twoF4S_of_inS rep_w1 w1P_mem_A inS_w1

theorem tpP_mem_S :
    tpP ∈ twoF4S :=
  mem_twoF4S_of_inS rep_tp tpP_mem_A inS_tp

theorem uP_eq : uP = jP * titsZ * jP⁻¹ := by
  unfold uP v2P v1P jP
  group

theorem uP_mul_self :
    uP * uP = 1 := by
  rw [uP_eq]
  calc jP * titsZ * jP⁻¹ * (jP * titsZ * jP⁻¹) = jP * (titsZ * titsZ) * jP⁻¹ := by group
    _ = 1 := by rw [titsZ_mul_self]; group

theorem b0P_pow_five : b0P ^ 5 = 1 :=
  eq_of_eqA (rep_powArr rep_b0 5) rep_idA b0Arr_pow

theorem b0P_ne_one : b0P ≠ 1 := fun h => by
  have h1 := (eqA_iff rep_b0 rep_idA).2 h
  rw [b0Arr_ne] at h1
  exact Bool.false_ne_true h1

theorem uP_inv_b0P :
    uP * b0P * uP⁻¹ = b0P⁻¹ := by
  have h := eq_of_eqA (rep_mulA (rep_mulA rep_u rep_b0) rep_u)
    (rep_powArr rep_b0 4) uArr_b0
  rw [inv_eq_of_mul_eq_one_right uP_mul_self, h, eq_inv_iff_mul_eq_one, ← pow_succ]
  exact b0P_pow_five

@[expose] noncomputable def iEl (p : ℕ) : Equiv.Perm (Fin 1755) := aaP ^ (p / 4) * abP ^ (p % 4)

theorem iEl_def (p : ℕ) : iEl p = aaP ^ (p / 4) * abP ^ (p % 4) := rfl

theorem rep_iEl (p : ℕ) : Rep 1755 (prodI p) (iEl p) := by
  unfold prodI
  exact rep_mulA (rep_powArr rep_aa _) (rep_powArr rep_ab _)

theorem aaP_comm_abP : aaP * abP = abP * aaP :=
  eq_of_eqA (rep_mulA rep_aa rep_ab)
    (rep_mulA rep_ab rep_aa) aa_comm_ab

theorem aaP_comm_uP :
    aaP * uP = uP * aaP :=
  eq_of_eqA (rep_mulA rep_aa rep_u) (rep_mulA rep_u rep_aa) aa_comm_u

theorem abP_comm_uP :
    abP * uP = uP * abP :=
  eq_of_eqA (rep_mulA rep_ab rep_u) (rep_mulA rep_u rep_ab) ab_comm_u

theorem normB_spec {g : Array ℕ} {x : Equiv.Perm (Fin 1755)}
    (hg : Rep 1755 g x) (hgi : Rep 1755 (invA g) x⁻¹) (h : normB g = true) :
    ∃ k : ℕ, x * b0P * x⁻¹ = b0P ^ k := by
  rw [normB, List.any_eq_true] at h
  obtain ⟨k, -, hk⟩ := h
  exact ⟨k, eq_of_eqA (rep_conjA hg hgi rep_b0) (rep_powArr rep_b0 k) hk⟩

theorem aaP_norm : ∃ k : ℕ, aaP * b0P * aaP⁻¹ = b0P ^ k :=
  normB_spec rep_aa (rep_perm_inv aa_mem) aa_normB

theorem abP_norm : ∃ k : ℕ, abP * b0P * abP⁻¹ = b0P ^ k :=
  normB_spec rep_ab (rep_perm_inv ab_mem) ab_normB

theorem iEl_inj {p q : ℕ} (hp : p < 16) (hq : q < 16)
    (h : iEl p = iEl q) : p = q := by
  have h1 := allLt_spec (allLt_spec prodI_distinct hp) hq
  simp only [Bool.or_eq_true, beq_iff_eq, Bool.not_eq_true'] at h1
  rcases h1 with h1 | h1
  · exact h1
  · rw [(eqA_iff (rep_iEl p) (rep_iEl q)).2 h] at h1
    exact absurd h1 (by decide)

theorem iEl_inv
    {p : ℕ} (hp : p < 16) (h2 : iEl p * iEl p = 1) :
    iEl p = 1 ∨ iEl p = titsZ ∨ iEl p = uP ∨ iEl p = tP := by
  have h1 := allLt_spec prodI_inv hp
  simp only [Bool.or_eq_true, Bool.not_eq_true'] at h1
  have hA := (eqA_iff (rep_mulA (rep_iEl p) (rep_iEl p)) rep_idA).2 h2
  rcases h1 with (((h | h) | h) | h) | h
  · rw [hA] at h
    exact absurd h (by decide)
  · exact Or.inl (eq_of_eqA (rep_iEl p) rep_idA h)
  · exact Or.inr (Or.inl (eq_of_eqA (rep_iEl p) titsZ_rep h))
  · exact Or.inr (Or.inr (Or.inl (eq_of_eqA (rep_iEl p) rep_u h)))
  · exact Or.inr (Or.inr (Or.inr (eq_of_eqA (rep_iEl p) rep_t h)))

theorem card_fix_conj (g y : Equiv.Perm (Fin 1755)) :
    Fintype.card {x // (g * y * g⁻¹) x = x} = Fintype.card {x // y x = x} := by
  apply Fintype.card_congr
  refine Equiv.subtypeEquiv g⁻¹ fun x => ?_
  simp only [Equiv.Perm.mul_apply]
  constructor
  · intro h
    have h1 := congrArg (fun w => g⁻¹ w) h
    simpa using h1
  · intro h
    show g (y (g⁻¹ x)) = x
    rw [h]
    simp

theorem conj_uP_ne_tP
    (g : Equiv.Perm (Fin 1755)) : g * uP * g⁻¹ ≠ tP := by
  intro h
  have h1 := card_fix_conj g uP
  rw [h, card_fixedPoints rep_t, card_fixedPoints rep_u, fix_u, fix_t] at h1
  norm_num at h1

def Coll (p q : Fin 1755) : Prop := ∃ v : Fin 2925, p ∈ titsLine v ∧ q ∈ titsLine v

def InBall (q r : Fin 1755) : Prop := ∃ p, Coll q p ∧ Coll p r

theorem coll_smul
    {g : Equiv.Perm (Fin 1755)} (hg : g ∈ TA) {p q : Fin 1755}
    (h : Coll p q) : Coll (g p) (g q) := by
  obtain ⟨v, hp, hq⟩ := h
  exact ⟨titsLineHom ⟨g, hg⟩ v, smul_mem_lineHom hg hp, smul_mem_lineHom hg hq⟩

theorem inBall_smul
    {g : Equiv.Perm (Fin 1755)} (hg : g ∈ TA) {q r : Fin 1755}
    (h : InBall q r) : InBall (g q) (g r) := by
  obtain ⟨p, h1, h2⟩ := h
  exact ⟨g p, coll_smul hg h1, coll_smul hg h2⟩

theorem imp_of_or {b c : Bool} (h : (!b || c) = true) (hb : b = true) : c = true := by
  rw [hb] at h
  simpa using h

theorem perm_comm_apply {f g : Equiv.Perm (Fin 1755)} (h : f * g = g * f) (x : Fin 1755) :
    g (f x) = f (g x) := by
  rw [← Equiv.Perm.mul_apply, ← h, Equiv.Perm.mul_apply]

theorem perm_inv_apply_self (c : Equiv.Perm (Fin 1755)) (x : Fin 1755) : c⁻¹ (c x) = x := by
  rw [← Equiv.Perm.mul_apply, inv_mul_cancel, Equiv.Perm.one_apply]

theorem perm_apply_inv_self (c : Equiv.Perm (Fin 1755)) (x : Fin 1755) : c (c⁻¹ x) = x := by
  rw [← Equiv.Perm.mul_apply, mul_inv_cancel, Equiv.Perm.one_apply]

theorem ball_fixed_ten
    {r : Fin 1755}
    (hr : InBall 10 r) : uP r = r := by
  obtain ⟨p, ⟨v, h10, hp⟩, ⟨w, hpw, hrw⟩⟩ := hr
  have hb := ball_fixed
  rw [ballFixed, allLt_iff] at hb
  have h1 := imp_of_or (hb v v.2) ((titsLine_mem_iff 10 v).1 h10)
  rw [List.all_eq_true] at h1
  obtain ⟨k, hk, rfl⟩ := exists_linePt_of_mem hp
  have h2 := h1 k (List.mem_range.2 hk)
  rw [allLt_iff] at h2
  have h3 := imp_of_or (h2 w w.2) (by
    rw [← titsLinePt_val v hk]
    exact (titsLine_mem_iff _ w).1 hpw)
  rw [List.all_eq_true] at h3
  obtain ⟨k', hk', rfl⟩ := exists_linePt_of_mem hrw
  have h4 := h3 k' (List.mem_range.2 hk')
  rw [beq_iff_eq, ← titsLinePt_val w hk'] at h4
  exact apply_eq_of_get rep_u h4

theorem eq_ten_of_ball_fixed
    {q : Fin 1755}
    (hq : ∀ r, InBall q r → uP r = r) : q = 10 := by
  by_contra hne
  have hq' : (q : ℕ) ≠ 10 := fun h => hne (Fin.ext h)
  have hb := allLt_spec ball_moved q.2
  rw [Bool.or_eq_true, beq_iff_eq] at hb
  rcases hb with hb | hb
  · exact hq' hb
  rw [ballMoved, List.any_eq_true] at hb
  obtain ⟨v, -, hv⟩ := hb
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true, List.mem_range,
    bne_iff_ne] at hv
  obtain ⟨⟨hv1, hqv⟩, k, hk, w, -, ⟨hw1, hpw⟩, k', hk', hne'⟩ := hv
  set vF : Fin 2925 := ⟨v, hv1⟩
  set wF : Fin 2925 := ⟨w, hw1⟩
  have hqL : q ∈ titsLine vF := (titsLine_mem_iff q vF).2 hqv
  have hpL : titsLinePt vF k ∈ titsLine wF := (titsLine_mem_iff _ wF).2 (by
    rw [titsLinePt_val vF hk]
    exact hpw)
  have hball : InBall q (titsLinePt wF k') :=
    ⟨titsLinePt vF k, ⟨vF, hqL, linePt_mem vF hk⟩, ⟨wF, hpL, linePt_mem wF hk'⟩⟩
  refine apply_ne_of_get rep_u ?_ (hq _ hball)
  rw [titsLinePt_val wF hk']
  exact hne'

theorem fix_ten_of_comm
    {c : Equiv.Perm (Fin 1755)}
    (hc : c ∈ TA) (hcu : c * uP = uP * c) : c 10 = 10 := by
  apply eq_ten_of_ball_fixed
  intro r hr
  have h1 : InBall 10 (c⁻¹ r) := by
    have h := inBall_smul (inv_mem hc) hr
    rwa [perm_inv_apply_self] at h
  have h2 := ball_fixed_ten h1
  have hcomm : ∀ x, uP (c x) = c (uP x) := fun x => perm_comm_apply hcu x
  calc uP r = uP (c (c⁻¹ r)) := by rw [perm_apply_inv_self]
    _ = c (uP (c⁻¹ r)) := hcomm _
    _ = c (c⁻¹ r) := by rw [h2]
    _ = r := perm_apply_inv_self c r

theorem fix_of_comm_uP
    {c : Equiv.Perm (Fin 1755)}
    (hc : c ∈ TA) (hcu : c * uP = uP * c) (hc0 : c 0 = 0) :
    c 1 = 1 ∧ c 10 = 10 ∧ c • titsLine 0 = titsLine 0 ∧ c • titsLine 5 = titsLine 5 := by
  have h10 := fix_ten_of_comm hc hcu
  have h00 := onLine_0_0
  have h10L := onLine_1_0
  have h15 := onLine_1_5
  have h105 := onLine_10_5
  have hinc := inc_check
  have hlp := lp_check
  set v' := titsLineHom ⟨c, hc⟩ 0
  set w' := titsLineHom ⟨c, hc⟩ 5
  have hL0 : titsLine v' = c • titsLine 0 := titsLine_lineHom _ _
  have hL5 : titsLine w' = c • titsLine 5 := titsLine_lineHom _ _
  have h0v : (0 : Fin 1755) ∈ titsLine v' := by
    rw [← hc0]
    exact smul_mem_lineHom hc ((titsLine_mem_iff 0 0).2 h00)
  have h1v : c 1 ∈ titsLine v' := smul_mem_lineHom hc ((titsLine_mem_iff 1 0).2 h10L)
  have h1w : c 1 ∈ titsLine w' := smul_mem_lineHom hc ((titsLine_mem_iff 1 5).2 h15)
  have h10w : (10 : Fin 1755) ∈ titsLine w' := by
    rw [← h10]
    exact smul_mem_lineHom hc ((titsLine_mem_iff 10 5).2 h105)
  obtain ⟨k, hk, hck⟩ := exists_linePt_of_mem h1v
  have hi := imp_of_or (allLt_spec hinc v'.2) ((titsLine_mem_iff 0 v').1 h0v)
  rw [List.all_eq_true] at hi
  have hi2 := hi k (List.mem_range.2 hk)
  rw [allLt_iff] at hi2
  have hi3 := imp_of_or (hi2 w' w'.2) (by
    rw [Bool.and_eq_true]
    refine ⟨?_, (titsLine_mem_iff 10 w').1 h10w⟩
    rw [← titsLinePt_val v' hk, hck]
    exact (titsLine_mem_iff _ w').1 h1w)
  rw [Bool.and_eq_true, beq_iff_eq, beq_iff_eq] at hi3
  obtain ⟨hv0, hp1⟩ := hi3
  have hc1 : c 1 = 1 := by
    rw [← hck]
    apply Fin.ext
    rw [titsLinePt_val v' hk]
    exact hp1
  have h1w' : (1 : Fin 1755) ∈ titsLine w' := hc1 ▸ h1w
  have hw5 := imp_of_or (allLt_spec hlp w'.2) (by
    rw [Bool.and_eq_true]
    exact ⟨(titsLine_mem_iff 1 w').1 h1w', (titsLine_mem_iff 10 w').1 h10w⟩)
  rw [beq_iff_eq] at hw5
  refine ⟨hc1, h10, ?_, ?_⟩
  · rw [← hL0, show v' = 0 from Fin.ext hv0]
  · rw [← hL5, show w' = 5 from Fin.ext hw5]

theorem x1_zero {c : Equiv.Perm (Fin 1755)} (hc1 : c 1 = 1) :
    (a1P⁻¹ * c * a1P) 0 = 0 := by
  rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, a1P_zero, hc1, a1P_inv_one]

theorem x2_zero {c : Equiv.Perm (Fin 1755)} (hc1 : c 1 = 1) :
    (eP * (a1P⁻¹ * c * a1P) * eP⁻¹) 0 = 0 := by
  rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, eP_inv, eP_zero, x1_zero hc1, eP_zero]

theorem x3_zero {c : Equiv.Perm (Fin 1755)} (hc10 : c 10 = 10) :
    (jP * c * jP⁻¹) 0 = 0 := by
  rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, jP_inv, jP_zero, hc10, jP_ten]

theorem x1_line
    {c : Equiv.Perm (Fin 1755)}
    (hcL0 : c • titsLine 0 = titsLine 0) : (a1P⁻¹ * c * a1P) • titsLine 0 = titsLine 0 := by
  rw [mul_smul, mul_smul, a1P_line, hcL0, a1P_inv_line]

theorem eP_line :
    eP • titsLine 0 = a1P⁻¹ • titsLine 5 := by
  rw [← a1eP_line, mul_smul, inv_smul_smul]

theorem x2_line
    {c : Equiv.Perm (Fin 1755)}
    (hcL5 : c • titsLine 5 = titsLine 5) :
    (eP * (a1P⁻¹ * c * a1P) * eP⁻¹) • titsLine 0 = titsLine 0 := by
  have hx1 : (a1P⁻¹ * c * a1P) • (a1P⁻¹ • titsLine 5) = a1P⁻¹ • titsLine 5 := by
    rw [mul_smul, mul_smul, smul_inv_smul, hcL5]
  rw [mul_smul, mul_smul, eP_inv, eP_line, hx1, ← eP_line, ← mul_smul, eP_mul_self, one_smul]

theorem x3_line
    {c : Equiv.Perm (Fin 1755)}
    (hcL5 : c • titsLine 5 = titsLine 5) : (jP * c * jP⁻¹) • titsLine 0 = titsLine 0 := by
  rw [mul_smul, mul_smul, jP_inv, jP_line, hcL5, jP_line5]

theorem chain_of_comm_uP
    {c : Equiv.Perm (Fin 1755)}
    (hcH : c ∈ twoF4H) (hcu : c * uP = uP * c) :
    c ∈ twoF4S ∧ a1P⁻¹ * c * a1P ∈ twoF4S ∧ eP * (a1P⁻¹ * c * a1P) * eP⁻¹ ∈ twoF4S ∧
      jP * c * jP⁻¹ ∈ twoF4S := by
  have hcA : c ∈ TA := mem_A_of_mem_twoF4H hcH
  have hc0 : c 0 = 0 := (mem_twoF4H_iff hcA).1 hcH
  obtain ⟨hc1, hc10, hcL0, hcL5⟩ := fix_of_comm_uP hcA hcu hc0
  have hx1A : a1P⁻¹ * c * a1P ∈ TA := mul_mem (mul_mem (inv_mem a1P_mem_A) hcA) a1P_mem_A
  have hx2A : eP * (a1P⁻¹ * c * a1P) * eP⁻¹ ∈ TA :=
    mul_mem (mul_mem eP_mem_A hx1A) (inv_mem eP_mem_A)
  have hx3A : jP * c * jP⁻¹ ∈ TA := mul_mem (mul_mem jP_mem_A hcA) (inv_mem jP_mem_A)
  exact ⟨(mem_twoF4S_iff hcA).2 ⟨hc0, hcL0⟩, (mem_twoF4S_iff hx1A).2 ⟨x1_zero hc1, x1_line hcL0⟩,
    (mem_twoF4S_iff hx2A).2 ⟨x2_zero hc1, x2_line hcL5⟩,
    (mem_twoF4S_iff hx3A).2 ⟨x3_zero hc10, x3_line hcL5⟩⟩

theorem cP_pow_three : cP ^ 3 = 1 :=
  eq_of_eqA (rep_powArr rep_c 3) rep_idA cArr_pow

theorem cP_ne_one : cP ≠ 1 := fun h => by
  have h1 := (eqA_iff rep_c rep_idA).2 h
  rw [cArr_ne] at h1
  exact Bool.false_ne_true h1

theorem cP_comm_tpP :
    cP * tpP = tpP * cP :=
  eq_of_eqA (rep_mulA rep_c rep_tp) (rep_mulA rep_tp rep_c) cArr_comm_tp

theorem cP_conj_zpP :
    cP * zpP * cP⁻¹ = jpP :=
  eq_of_eqA (rep_conjA rep_c (rep_perm_inv c_mem) rep_zp) rep_jp cArr_conj_zp

end CFSG.Quasithin.RuType.J47
