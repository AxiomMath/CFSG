module

public import CFSG.LieType.Universal.SpecialLinear
public import CFSG.LieType.Universal.Unitary.Clause0
public import CFSG.Quasithin.EmptyFaithfulMultiple.F618CompBasic

public section

namespace CFSG.Quasithin.EmptyFaithfulMultiple

namespace F618Comp

open CFSG.Assembly.LowTwoRank Matrix

structure GoodQuasi (Q : Type*) [Group Q] : Prop where
  quasisimple : CFSG.IsQuasisimple Q
  odd_card_center : Odd (Nat.card ↥(Subgroup.center Q))
  notSL2 : NotSL2 Q

theorem card_center_congr {Q Q' : Type*} [Group Q] [Group Q'] (e : Q ≃* Q') :
    Nat.card ↥(Subgroup.center Q) = Nat.card ↥(Subgroup.center Q') := by
  have h1 := Subgroup.map_center_eq e
  have h2 : Nat.card ↥((Subgroup.center Q).map (e : Q →* Q')) =
      Nat.card ↥(Subgroup.center Q) := Subgroup.card_map_of_injective e.injective
  rw [h1] at h2
  exact h2.symm

theorem GoodQuasi.of_mulEquiv {Q Q' : Type*} [Group Q] [Group Q'] (e : Q ≃* Q')
    (h : GoodQuasi Q') : GoodQuasi Q :=
  ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm h.1, (card_center_congr e) ▸ h.2,
    h.3.of_mulEquiv e⟩

theorem GoodQuasi.socle {Q : Type*} [Group Q] (h : GoodQuasi Q) : Socle Q :=
  socle_of_isQuasisimple h.1 h.2 h.3

theorem odd_card_of_pow_three {Q : Type*} [Group Q] [Finite Q] (h : ∀ x : Q, x ^ 3 = 1) :
    Odd (Nat.card Q) := by
  rw [Nat.odd_iff]
  by_contra hne
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := Q) 2 (Nat.dvd_of_mod_eq_zero (by omega))
  have h3 := orderOf_dvd_of_pow_eq_one (h x)
  rw [hx] at h3
  norm_num at h3

variable {K : Type} [Field K]

theorem det_eq_one_of_mem_statedSL {n : ℕ} {A : GL (Fin n) K} (h : A ∈ StatedSL n K) :
    (A : Matrix (Fin n) (Fin n) K).det = 1 :=
  CFSG.Open.StatedAPI.det_of_mem_statedSL h

theorem mem_statedSL_of_det {n : ℕ} {A : GL (Fin n) K}
    (h : (A : Matrix (Fin n) (Fin n) K).det = 1) : A ∈ StatedSL n K :=
  CFSG.Open.StatedAPI.mem_statedSL_of_det h

theorem center_statedSL (n : ℕ) :
    Subgroup.center ↥(StatedSL n K) = (StatedScalars (Fin n) K).subgroupOf (StatedSL n K) := by
  rw [← map_center_eq_statedScalars, Subgroup.map_center_eq]

theorem pow_three_eq_one_of_scalar {H : Subgroup (GL (Fin 3) K)}
    (hdet : ∀ A ∈ H, (A : Matrix (Fin 3) (Fin 3) K).det = 1) (z : ↥H)
    (hz : z ∈ (StatedScalars (Fin 3) K).subgroupOf H) : z ^ 3 = 1 := by
  rw [Subgroup.mem_subgroupOf] at hz
  obtain ⟨c, hc⟩ := hz
  have hd := hdet z z.2
  rw [← hc, Matrix.GeneralLinearGroup.coe_scalar] at hd
  have hc3 : (c : K) ^ 3 = 1 := by
    simpa [Matrix.det_diagonal, Matrix.scalar_apply] using hd
  have hcu : c ^ 3 = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val, hc3, Units.val_one])
  apply Subtype.ext
  rw [SubgroupClass.coe_pow, ← hc, ← map_pow, hcu, map_one, OneMemClass.coe_one]

@[expose] def rotMat (K : Type) [Field K] : Matrix (Fin 3) (Fin 3) K :=
  !![0, 1, 0; -1, 0, 0; 0, 0, 1]

theorem det_rotMat : (rotMat K).det = 1 := by
  simp [rotMat, Matrix.det_fin_three]

@[expose] noncomputable def rotGL (K : Type) [Field K] : GL (Fin 3) K :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (rotMat K) (by rw [det_rotMat]; exact one_ne_zero)

theorem coe_rotGL : ((rotGL K : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = rotMat K :=
  Matrix.GeneralLinearGroup.val_mkOfDetNeZero _ _

theorem rotMat_sq : rotMat K ^ 2 = !![-1, 0, 0; 0, -1, 0; 0, 0, 1] := by
  rw [sq, rotMat, Matrix.mul_fin_three]
  simp

theorem rotMat_pow_four : rotMat K ^ 4 = 1 := by
  rw [show 4 = 2 * 2 from rfl, pow_mul, rotMat_sq, sq, Matrix.mul_fin_three, Matrix.one_fin_three]
  simp

theorem rotMat_sq_ne_scalar (h2 : (2 : K) ≠ 0) (c : K) :
    rotMat K ^ 2 ≠ Matrix.scalar (Fin 3) c := by
  intro h
  have h0 := congrFun (congrFun h 0) 0
  have h22 := congrFun (congrFun h 2) 2
  rw [rotMat_sq] at h0 h22
  simp at h0 h22
  apply h2
  linear_combination h22 - h0

theorem notSL2_of_rotGL_mem {H : Subgroup (GL (Fin 3) K)} (hR : rotGL K ∈ H)
    (h2 : (2 : K) ≠ 0) : NotSL2 ↥H ∧ NotSL2 (StatedProj H) := by
  set x : ↥H := ⟨rotGL K, hR⟩
  have hx4 : x ^ 4 = 1 := by
    apply Subtype.ext
    apply Units.ext
    rw [SubgroupClass.coe_pow, Units.val_pow_eq_pow_val]
    change (rotGL K : Matrix (Fin 3) (Fin 3) K) ^ 4 = 1
    rw [coe_rotGL, rotMat_pow_four]
  have hx2 : x ^ 2 ∉ (StatedScalars (Fin 3) K).subgroupOf H := by
    rw [Subgroup.mem_subgroupOf]
    rintro ⟨c, hc⟩
    apply rotMat_sq_ne_scalar h2 (c : K)
    have := congrArg (fun A : GL (Fin 3) K => (A : Matrix (Fin 3) (Fin 3) K)) hc
    simp only [Matrix.GeneralLinearGroup.coe_scalar] at this
    rw [this, SubgroupClass.coe_pow, Units.val_pow_eq_pow_val]
    change rotMat K ^ 2 = (rotGL K : Matrix (Fin 3) (Fin 3) K) ^ 2
    rw [coe_rotGL]
  refine ⟨notSL2_of_pow x hx4 fun h => hx2 (h ▸ Subgroup.one_mem _),
    notSL2_of_pow (x : StatedProj H) ?_ ?_⟩
  · rw [← QuotientGroup.mk_pow, hx4, QuotientGroup.mk_one]
  · rw [← QuotientGroup.mk_pow]
    intro h
    exact hx2 ((QuotientGroup.eq_one_iff _).mp h)

theorem goodQuasi_of_scalars [Finite K] {H : Subgroup (GL (Fin 3) K)}
    (hq : CFSG.IsQuasisimple ↥H) (hc : Subgroup.center ↥H = (StatedScalars (Fin 3) K).subgroupOf H)
    (hdet : ∀ A ∈ H, (A : Matrix (Fin 3) (Fin 3) K).det = 1) (hR : rotGL K ∈ H)
    (h2 : (2 : K) ≠ 0) : GoodQuasi ↥H ∧ GoodQuasi (StatedProj H) := by
  obtain ⟨hS, hS'⟩ := notSL2_of_rotGL_mem hR h2
  refine ⟨⟨hq, odd_card_of_pow_three fun z => ?_, hS⟩, ?_⟩
  · apply Subtype.ext
    rw [SubgroupClass.coe_pow, OneMemClass.coe_one]
    exact pow_three_eq_one_of_scalar hdet z (hc ▸ z.2)
  · have e : StatedProj H ≃* ↥H ⧸ Subgroup.center ↥H := QuotientGroup.quotientMulEquivOfEq hc.symm
    have : IsSimpleGroup (↥H ⧸ Subgroup.center ↥H) := hq.2.1
    have : IsSimpleGroup (StatedProj H) := e.isSimpleGroup
    obtain ⟨a, b, hab⟩ := hq.2.2
    have hnab : ∃ a b : StatedProj H, a * b ≠ b * a :=
      ⟨e.symm a, e.symm b, fun h => hab (e.symm.injective (by rw [map_mul, map_mul, h]))⟩
    refine ⟨isQuasisimple_of_isSimpleGroup hnab, ?_, hS'⟩
    rw [center_eq_bot_of_isSimpleGroup hnab, Subgroup.card_bot]
    exact odd_one

theorem two_ne_zero_of_charP {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) [CharP K p] : (2 : K) ≠ 0 := by
  intro h
  have h' : ((2 : ℕ) : K) = 0 := by exact_mod_cast h
  rw [CharP.cast_eq_zero_iff K p] at h'
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h')

theorem charP_of_card [Finite K] {p f : ℕ} [Fact p.Prime] (h : Nat.card K = p ^ f) :
    CharP K p := by
  have := Fintype.ofFinite K
  exact charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card]; exact h)

theorem rotGL_mem_statedSL : rotGL K ∈ StatedSL 3 K :=
  mem_statedSL_of_det (by rw [coe_rotGL, det_rotMat])

theorem goodQuasi_statedSL [Finite K] (h2 : (2 : K) ≠ 0) :
    GoodQuasi ↥(StatedSL 3 K) ∧ GoodQuasi (StatedProj (StatedSL 3 K)) :=
  goodQuasi_of_scalars
    (CFSG.LocalCores.isQuasisimple_of_mulEquiv (specialLinearGroupEquivStatedSL 3 K)
      (CFSG.LieType.Universal.SpecialLinear.isQuasisimple 2 K le_rfl))
    (center_statedSL 3) (fun _ hA => det_eq_one_of_mem_statedSL hA) rotGL_mem_statedSL h2

section Unitary

variable [Finite K] {p : ℕ} [Fact p.Prime] [CharP K p]

theorem mem_statedSU_iff (hK : Nat.card K = p ^ 2) (A : GL (Fin 3) K) :
    A ∈ StatedSU 3 p K ↔ (A : Matrix (Fin 3) (Fin 3) K).det = 1 ∧
      CFSG.LieType.Universal.Unitary.conjTr (CFSG.LieType.BorelTits.unitaryInvolution K p 1)
        (A : Matrix (Fin 3) (Fin 3) K) * (A : Matrix (Fin 3) (Fin 3) K) = 1 := by
  have hK1 : Nat.card K = (p ^ 1) ^ 2 := by rw [pow_one]; exact hK
  have := CFSG.LieType.Universal.Unitary.SUid_eq_statedSU hK1 3
  rw [pow_one] at this
  rw [← this]
  exact CFSG.LieType.Universal.Unitary.mem_SUid

theorem rotGL_mem_statedSU (hK : Nat.card K = p ^ 2) : rotGL K ∈ StatedSU 3 p K := by
  rw [mem_statedSU_iff hK, coe_rotGL]
  refine ⟨det_rotMat, ?_⟩
  have hmap : (rotMat K).map (CFSG.LieType.BorelTits.unitaryInvolution K p 1) = rotMat K := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [rotMat]
  rw [CFSG.LieType.Universal.Unitary.conjTr, hmap]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rotMat, Matrix.mul_apply, Fin.sum_univ_three]

theorem goodQuasi_statedSU (hp2 : p ≠ 2) (hK : Nat.card K = p ^ 2) :
    GoodQuasi ↥(StatedSU 3 p K) ∧ GoodQuasi (StatedProj (StatedSU 3 p K)) := by
  have hK1 : Nat.card K = (p ^ 1) ^ 2 := by rw [pow_one]; exact hK
  have h := CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card hK1 (n := 3) le_rfl
    (by rw [pow_one]; intro h; simp only [Prod.mk.injEq, true_and] at h; exact hp2 h)
  rw [pow_one] at h
  exact goodQuasi_of_scalars h.1 h.2 (fun A hA => ((mem_statedSU_iff hK A).mp hA).1)
    (rotGL_mem_statedSU hK) (two_ne_zero_of_charP (Fact.out) hp2)

end Unitary

theorem socle_of_isSLEps3 {D : Type} [Group D] {p : ℕ} (hp2 : p ≠ 2) (h : F6.IsSLEps3 p D) :
    Socle D := by
  obtain ⟨hp, K, _, _, h⟩ := h
  have : Fact p.Prime := ⟨hp⟩
  rcases h with ⟨-, hK, e | e⟩ | ⟨-, hK, e | e⟩
  · have : CharP K p := charP_of_card (f := 1) (by rw [pow_one]; exact hK)
    exact ((goodQuasi_statedSL (two_ne_zero_of_charP hp hp2)).1.of_mulEquiv e.some).socle
  · have : CharP K p := charP_of_card (f := 1) (by rw [pow_one]; exact hK)
    exact ((goodQuasi_statedSL (two_ne_zero_of_charP hp hp2)).2.of_mulEquiv e.some).socle
  · have : CharP K p := charP_of_card hK
    exact ((goodQuasi_statedSU hp2 hK).1.of_mulEquiv e.some).socle
  · have : CharP K p := charP_of_card hK
    exact ((goodQuasi_statedSU hp2 hK).2.of_mulEquiv e.some).socle

end F618Comp

end CFSG.Quasithin.EmptyFaithfulMultiple
