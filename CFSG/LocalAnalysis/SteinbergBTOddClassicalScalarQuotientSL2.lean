module

public import CFSG.LocalAnalysis.SteinbergCDEvenOrderFourTools
public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalPSLTwoSections
public import CFSG.LinearAlgebra.SL2MinimalFaithfulMatrix
public import CFSG.LocalAnalysis.ComponentInitial.BasicFacts
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherMonomial
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBAlternatingIsometryTwo
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBUnitaryTwoEndpoint
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticBConjugation
import CFSG.GroupTheory.ElementaryAbelianTransport

public noncomputable section

namespace CFSG.LocalAnalysis.SteinbergBT

open Matrix Subgroup CFSG.Assembly.LowTwoRank

section Centre

variable {G H : Type*} [Group G] [Group H]

theorem mem_center_iff_of_card_center_eq_two (h2 : Nat.card (center G) = 2) {z : G}
    (hz : z ∈ center G) (hz1 : z ≠ 1) (g : G) : g ∈ center G ↔ g = 1 ∨ g = z := by
  constructor
  · intro hg
    by_cases hg1 : g = 1
    · exact Or.inl hg1
    right
    obtain ⟨y, -, hy⟩ := (Nat.card_eq_two_iff' (1 : center G)).1 h2
    have h1 := hy ⟨g, hg⟩ (fun h => hg1 (congrArg Subtype.val h))
    have h2 := hy ⟨z, hz⟩ (fun h => hz1 (congrArg Subtype.val h))
    exact congrArg Subtype.val (h1.trans h2.symm)
  · rintro (rfl | rfl)
    · exact one_mem _
    · exact hz

theorem mulEquiv_mem_center_iff (e : G ≃* H) (g : G) : e g ∈ center H ↔ g ∈ center G := by
  simp only [mem_center_iff]
  constructor
  · intro h x
    apply e.injective
    rw [map_mul, map_mul, h]
  · intro h y
    obtain ⟨x, rfl⟩ := e.surjective y
    rw [← map_mul, ← map_mul, h]

theorem map_center_mulEquiv (e : G ≃* H) : (center G).map (e : G →* H) = center H := by
  ext y
  obtain ⟨x, rfl⟩ := e.surjective y
  rw [mem_map]
  constructor
  · rintro ⟨x', hx', hxx'⟩
    rw [← hxx']
    exact (mulEquiv_mem_center_iff e x').2 hx'
  · intro hx
    exact ⟨x, (mulEquiv_mem_center_iff e x).1 hx, rfl⟩

theorem card_center_mulEquiv (e : G ≃* H) : Nat.card (center G) = Nat.card (center H) := by
  refine Nat.card_congr (e.toEquiv.subtypeEquiv fun g => ?_)
  exact (mulEquiv_mem_center_iff e g).symm

theorem mk_mem_center {A : Subgroup G} [A.Normal] {z : G} (hz : z ∈ center G) :
    (z : G ⧸ A) ∈ center (G ⧸ A) := by
  rw [mem_center_iff]
  intro y
  induction y using QuotientGroup.induction_on with
  | H g =>
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, (mem_center_iff.1 hz g)]

theorem isEmpty_mulEquiv_SL2_of_orderOf_eq_four {x : G} (hx : orderOf x = 4) (K : Type*)
    [Field K] (h2 : (2 : K) = 0) : IsEmpty (G ≃* SpecialLinearGroup (Fin 2) K) :=
  ⟨fun e => SteinbergCD.SL_two_orderOf_ne_four h2 (e x) (by rw [MulEquiv.orderOf_eq, hx])⟩

end Centre

section SL2

theorem center_SL2_eq_bot_of_two_eq_zero (K : Type*) [Field K] (h2 : (2 : K) = 0) :
    center (SpecialLinearGroup (Fin 2) K) = ⊥ := by
  rw [eq_bot_iff]
  intro A hA
  obtain ⟨r, hr, hrA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hA
  rw [Fintype.card_fin] at hr
  have hr1 : r = 1 := by
    have h : (r - 1) ^ 2 = 0 := by linear_combination hr - (r - 1) * h2
    exact sub_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 h)
  rw [mem_bot]
  ext i j
  rw [← hrA, hr1]
  simp

@[expose] def negOneSL2 (k : Type*) [Field k] : SpecialLinearGroup (Fin 2) k :=
  ⟨-1, by simp [det_fin_two]⟩

theorem mem_center_SL2_iff {k : Type*} [Field k] (A : SpecialLinearGroup (Fin 2) k) :
    A ∈ center (SpecialLinearGroup (Fin 2) k) ↔
      (A : Matrix (Fin 2) (Fin 2) k) = 1 ∨ (A : Matrix (Fin 2) (Fin 2) k) = -1 := by
  rw [Matrix.SpecialLinearGroup.mem_center_iff, Fintype.card_fin]
  constructor
  · rintro ⟨r, hr, hrA⟩
    rcases sq_eq_one_iff.1 hr with rfl | rfl
    · left
      rw [← hrA]
      simp
    · right
      rw [← hrA]
      ext i j
      simp [Matrix.scalar_apply, Matrix.neg_apply, Matrix.one_apply, Matrix.diagonal_apply]
      split_ifs <;> simp
  · rintro (h | h)
    · exact ⟨1, one_pow 2, by rw [h]; simp⟩
    · refine ⟨-1, by norm_num, ?_⟩
      rw [h]
      ext i j
      simp [Matrix.scalar_apply, Matrix.neg_apply, Matrix.one_apply, Matrix.diagonal_apply]
      split_ifs <;> simp

theorem card_center_SL2 {k : Type*} [Field k] (h2 : (2 : k) ≠ 0) :
    Nat.card (center (SpecialLinearGroup (Fin 2) k)) = 2 := by
  have hneg : ((negOneSL2 k : SpecialLinearGroup (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) ≠ 1 := by
    intro h
    have h00 := congrFun (congrFun h 0) 0
    simp [negOneSL2] at h00
    apply h2
    linear_combination -h00
  have hmem : negOneSL2 k ∈ center (SpecialLinearGroup (Fin 2) k) :=
    (mem_center_SL2_iff _).2 (Or.inr rfl)
  refine (Nat.card_eq_two_iff' (1 : center (SpecialLinearGroup (Fin 2) k))).2
    ⟨⟨negOneSL2 k, hmem⟩, fun h => hneg (by
      have := congrArg (fun x : center (SpecialLinearGroup (Fin 2) k) =>
        ((x : SpecialLinearGroup (Fin 2) k) : Matrix (Fin 2) (Fin 2) k)) h
      simpa using this), fun y hy => ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  rcases (mem_center_SL2_iff (y : SpecialLinearGroup (Fin 2) k)).1 y.2 with h | h
  · exact absurd (Subtype.ext (Subtype.ext (by simpa using h))) hy
  · rw [h]
    rfl

@[expose] def upperSL {K : Type*} [Field K] (c : K) : SpecialLinearGroup (Fin 2) K :=
  ⟨!![1, c; 0, 1], by simp [det_fin_two]⟩

theorem coe_upperSL {K : Type*} [Field K] (c : K) :
    (upperSL c : Matrix (Fin 2) (Fin 2) K) = !![1, c; 0, 1] := rfl

@[expose] def upperHom (K : Type*) [Field K] :
    Multiplicative K →* SpecialLinearGroup (Fin 2) K where
  toFun c := upperSL c.toAdd
  map_one' := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  map_mul' a b := by
    ext i j
    rw [Matrix.SpecialLinearGroup.coe_mul, coe_upperSL, coe_upperSL, coe_upperSL]
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, add_comm]

theorem upperHom_injective (K : Type*) [Field K] : Function.Injective (upperHom K) := by
  intro a b h
  have h1 := congrArg
    (fun A : SpecialLinearGroup (Fin 2) K => (A : Matrix (Fin 2) (Fin 2) K) 0 1) h
  change (upperSL a.toAdd : Matrix (Fin 2) (Fin 2) K) 0 1 =
    (upperSL b.toAdd : Matrix (Fin 2) (Fin 2) K) 0 1 at h1
  rw [coe_upperSL, coe_upperSL] at h1
  exact Multiplicative.toAdd.injective (by simpa using h1)

theorem isElementaryAbelian_of_mulEquiv {G H : Type*} [Group G] [Group H] {p : ℕ}
    (e : G ≃* H) [IsElementaryAbelian p H] : IsElementaryAbelian p G :=
  CFSG.IsElementaryAbelian.of_mulEquiv e.symm inferInstance

theorem isElementaryAbelian_multiplicative (K : Type*) [Field K] (h2 : (2 : K) = 0) :
    IsElementaryAbelian 2 (Multiplicative K) :=
  { toIsMulCommutative := ⟨⟨fun a b => mul_comm a b⟩⟩
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.2 fun a => by
      apply Multiplicative.toAdd.injective
      rw [toAdd_pow, toAdd_one, two_nsmul, ← two_mul, h2, zero_mul] }

theorem two_ne_zero_of_odd_card {k : Type*} [Field k] [Finite k] (hk : Odd (Nat.card k)) :
    (2 : k) ≠ 0 := by
  intro h
  have : CharP k 2 := CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero h
  have := Fintype.ofFinite k
  have hmod := FiniteField.even_card_iff_char_two.1 (ringChar.eq k 2)
  rw [← Nat.card_eq_fintype_card] at hmod
  have := Nat.odd_iff.1 hk
  omega

open CFSG.ComponentClassification.OutcomeLocal in
theorem sl2_odd_scalar_quotient_core {L : Type*} [Group L] {k : Type} [Field k] [Finite k]
    (hk : Odd (Nat.card k)) (e : L ≃* SpecialLinearGroup (Fin 2) k) (A : Subgroup L) [A.Normal]
    (hA : A ≤ center L) {n : ℕ} (hn : 2 ≤ n) (K : Type*) [Field K] (hK : Nat.card K = 2 ^ n)
    (φ : L ⧸ A ≃* SpecialLinearGroup (Fin 2) K) :
    n = 2 ∧ Nat.card k = 5 ∧ A = center L ∧ Nat.card (center L) = 2 := by
  have : CharP K 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
      (by omega) hK
  have h2K : (2 : K) = 0 := CharTwo.two_eq_zero
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  have h2k : (2 : k) ≠ 0 := two_ne_zero_of_odd_card hk
  have hcA : center L ≤ A := by
    intro z hz
    have h1 := (mulEquiv_mem_center_iff φ _).2 (mk_mem_center (A := A) hz)
    rw [center_SL2_eq_bot_of_two_eq_zero K h2K, mem_bot, MulEquiv.map_eq_one_iff] at h1
    exact (QuotientGroup.eq_one_iff z).1 h1
  have hAc : A = center L := le_antisymm hA hcA
  have hcard2 : Nat.card (center L) = 2 := by
    rw [card_center_mulEquiv e, card_center_SL2 h2k]
  let ψ : SpecialLinearGroup (Fin 2) K ≃* StatedProj (StatedSL 2 k) :=
    ((φ.symm.trans (QuotientGroup.quotientMulEquivOfEq hAc)).trans
      (QuotientGroup.congr (center L) (center (SpecialLinearGroup (Fin 2) k)) e
        (map_center_mulEquiv e))).trans (projectiveSpecialLinearGroupEquivStatedProj 2 k)
  let ι : Multiplicative K →* StatedProj (StatedSL 2 k) := ψ.toMonoidHom.comp (upperHom K)
  have hι : Function.Injective ι := ψ.injective.comp (upperHom_injective K)
  let eU : Multiplicative K ≃* ι.range := MonoidHom.ofInjective hι
  let eQ : (ι.range ⧸ (⊥ : Subgroup ι.range)) ≃* Multiplicative K :=
    QuotientGroup.quotientBot.trans eU.symm
  have := isElementaryAbelian_multiplicative K h2K
  have hEA : IsElementaryAbelian 2 (ι.range ⧸ (⊥ : Subgroup ι.range)) :=
    isElementaryAbelian_of_mulEquiv eQ
  have hle := (odd_projective_linear_two_elementary_two_sections hk).2.2.1 ι.range ⊥ hEA
  rw [Nat.card_congr eQ.toEquiv, Nat.card_congr Multiplicative.toAdd, hK] at hle
  have hn2 : n = 2 := by
    by_contra hne
    have : 2 ^ 3 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hL := card_eq_card_quotient_mul_card_subgroup A
  rw [Nat.card_congr φ.toEquiv, Nat.card_congr e.toEquiv,
    CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two,
    CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, hK, hn2, hAc, hcard2] at hL
  norm_num at hL
  set Q := Nat.card k with hQ
  have hQ5 : Q = 5 := by
    rcases (show Q ≤ 4 ∨ Q = 5 ∨ 6 ≤ Q by omega) with h | h | h
    · interval_cases Q <;> omega
    · exact h
    · have h1 : 35 ≤ Q ^ 2 - 1 := by
        have : 36 ≤ Q ^ 2 := by nlinarith
        omega
      have : 6 * 35 ≤ Q * (Q ^ 2 - 1) := Nat.mul_le_mul h h1
      omega
  exact ⟨hn2, hQ5, hAc, hcard2⟩

end SL2

section Rotation

variable {F : Type*} [Field F] {d : ℕ}

@[expose] def rotMatrix (a b : Fin d) : Matrix (Fin d) (Fin d) F :=
  1 - single a a 1 - single b b 1 - single a b 1 + single b a 1

theorem rotMatrix_mul_self {a b : Fin d} (hab : a ≠ b) :
    rotMatrix (F := F) a b * rotMatrix a b = 1 - 2 • single a a 1 - 2 • single b b 1 := by
  simp only [rotMatrix, sub_mul, mul_sub, add_mul, mul_add, one_mul, mul_one,
    single_mul_single_same, single_mul_single_of_ne _ _ _ _ hab,
    single_mul_single_of_ne _ _ _ _ hab.symm]
  abel

theorem rotMatrix_sq_mul_self {a b : Fin d} (hab : a ≠ b) :
    (1 - 2 • single a a 1 - 2 • single b b 1 : Matrix (Fin d) (Fin d) F) *
      (1 - 2 • single a a 1 - 2 • single b b 1) = 1 := by
  simp only [sub_mul, mul_sub, one_mul, mul_one, smul_mul_assoc, mul_smul_comm,
    single_mul_single_same, single_mul_single_of_ne _ _ _ _ hab,
    single_mul_single_of_ne _ _ _ _ hab.symm, smul_zero]
  abel

theorem rotMatrix_transpose_mul {a b : Fin d} (hab : a ≠ b) :
    (rotMatrix (F := F) a b)ᵀ * rotMatrix a b = 1 := by
  simp only [rotMatrix, transpose_add, transpose_sub, transpose_one, transpose_single, sub_mul,
    mul_sub, add_mul, mul_add, one_mul, mul_one, single_mul_single_same,
    single_mul_single_of_ne _ _ _ _ hab, single_mul_single_of_ne _ _ _ _ hab.symm]
  abel

theorem rotMatrix_map {S : Type*} [FunLike S F F] [RingHomClass S F F] (φ : S) (a b : Fin d) :
    (rotMatrix (F := F) a b).map φ = rotMatrix a b := by
  ext i j
  simp only [rotMatrix, Matrix.map_apply, Matrix.add_apply, Matrix.sub_apply, single_apply,
    one_apply]
  split_ifs <;> simp

theorem rot_sq_apply_left {a b : Fin d} (hab : a ≠ b) :
    (1 - 2 • single a a 1 - 2 • single b b 1 : Matrix (Fin d) (Fin d) F) a a = -1 := by
  simp [hab.symm]
  norm_num

theorem rot_sq_apply_other {a b c : Fin d} (hca : c ≠ a) (hcb : c ≠ b) :
    (1 - 2 • single a a 1 - 2 • single b b 1 : Matrix (Fin d) (Fin d) F) c c = 1 := by
  simp [hca.symm, hcb.symm]

theorem rotMatrix_eq_reflectionMatrix (hd : 2 ≤ d) :
    rotMatrix (F := F) (⟨0, by omega⟩ : Fin d) ⟨1, by omega⟩ =
      CFSG.LocalAnalysis.ComponentInitial.LinearFlag.reflectionMatrix d F 1 := by
  rw [CFSG.LocalAnalysis.ComponentInitial.LinearFlag.reflectionMatrix_eq_single 1 le_rfl
    (by omega)]
  rfl

@[expose] def rotSL (hd : 2 ≤ d) : SpecialLinearGroup (Fin d) F :=
  ⟨rotMatrix ⟨0, by omega⟩ ⟨1, by omega⟩, by
    rw [rotMatrix_eq_reflectionMatrix hd]
    exact CFSG.LocalAnalysis.ComponentInitial.LinearFlag.det_reflectionMatrix 1 le_rfl
      (by omega)⟩

theorem coe_rotSL (hd : 2 ≤ d) :
    (rotSL (F := F) hd : Matrix (Fin d) (Fin d) F) = rotMatrix ⟨0, by omega⟩ ⟨1, by omega⟩ :=
  rfl

theorem coe_rotSL_sq (hd : 2 ≤ d) :
    ((rotSL (F := F) hd ^ 2 : SpecialLinearGroup (Fin d) F) : Matrix (Fin d) (Fin d) F) =
      1 - 2 • single ⟨0, by omega⟩ ⟨0, by omega⟩ 1 - 2 • single ⟨1, by omega⟩ ⟨1, by omega⟩ 1 := by
  rw [Matrix.SpecialLinearGroup.coe_pow, sq, coe_rotSL]
  exact rotMatrix_mul_self (Fin.ne_of_val_ne (by simp))

theorem rotSL_pow_four (hd : 2 ≤ d) : rotSL (F := F) hd ^ 4 = 1 := by
  apply Subtype.ext
  rw [show 4 = 2 * 2 from rfl, pow_mul, Matrix.SpecialLinearGroup.coe_pow, coe_rotSL_sq, sq,
    rotMatrix_sq_mul_self (Fin.ne_of_val_ne (by simp)), Matrix.SpecialLinearGroup.coe_one]

end Rotation

section SymplecticRotation

variable {F : Type*} [Field F] {m : ℕ}

@[expose] def spRot (i : Fin m) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) F :=
  fromBlocks (1 - single i i 1) (single i i 1) (-single i i 1) (1 - single i i 1)

theorem single_mul_single_self (i : Fin m) :
    (single i i (1 : F)) * single i i 1 = single i i 1 := by
  rw [single_mul_single_same, mul_one]

theorem spRot_mul_self (i : Fin m) :
    spRot (F := F) i * spRot i =
      fromBlocks (1 - 2 • single i i 1) 0 0 (1 - 2 • single i i 1) := by
  rw [spRot, fromBlocks_multiply]
  simp only [sub_mul, mul_sub, one_mul, mul_one, neg_mul, mul_neg, single_mul_single_self]
  congr 1 <;> abel

theorem spRot_sq_mul_self (i : Fin m) :
    fromBlocks (1 - 2 • single i i 1) 0 0 (1 - 2 • single i i 1) *
      fromBlocks (1 - 2 • single i i 1) 0 0 (1 - 2 • single i i 1) =
      (1 : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) F) := by
  rw [fromBlocks_multiply, ← fromBlocks_one]
  simp only [sub_mul, mul_sub, one_mul, mul_one, smul_mul_assoc, mul_smul_comm,
    single_mul_single_self, mul_zero, zero_mul, add_zero, zero_add]
  congr 1 <;> abel

theorem spRot_symplectic (i : Fin m) :
    (spRot (F := F) i)ᵀ * Matrix.J (Fin m) F * spRot i = Matrix.J (Fin m) F := by
  rw [spRot, Matrix.J, fromBlocks_transpose, fromBlocks_multiply, fromBlocks_multiply]
  simp only [transpose_sub, transpose_one, transpose_single, transpose_neg, sub_mul, mul_sub,
    one_mul, mul_one, neg_mul, mul_neg, mul_zero, single_mul_single_self, neg_neg, add_zero,
    zero_add]
  congr 1 <;> abel

theorem spRot_sq_apply_left (i : Fin m) :
    (fromBlocks (1 - 2 • single i i 1) 0 0 (1 - 2 • single i i 1) :
      Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) F) (Sum.inl i) (Sum.inl i) = -1 := by
  simp
  norm_num

theorem spRot_sq_apply_other {i j : Fin m} (hji : j ≠ i) :
    (fromBlocks (1 - 2 • single i i 1) 0 0 (1 - 2 • single i i 1) :
      Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) F) (Sum.inl j) (Sum.inl j) = 1 := by
  simp [hji.symm]

end SymplecticRotation

section Linear

variable {L : Type*} [Group L] {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem mem_center_of_forall_smul (ι : L →* (V ≃ₗ[K] V)) (hι : Function.Injective ι) {g : L}
    {c : K} (hg : ∀ v, ι g v = c • v) : g ∈ center L := by
  rw [mem_center_iff]
  intro x
  apply hι
  refine LinearEquiv.ext fun v => ?_
  rw [map_mul, map_mul, LinearEquiv.mul_apply, LinearEquiv.mul_apply, hg, hg, map_smul]

theorem basisMatrixEquiv_apply_self_of_smul {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι K V) (g : V ≃ₗ[K] V) (c : K) (hg : ∀ v, g v = c • v) (i : ι) :
    (CFSG.ComponentClassification.CatalogueBAlternatingIsometry.basisMatrixEquiv b g).val i i =
      c := by
  rw [CFSG.ComponentClassification.CatalogueBAlternatingIsometry.basisMatrixEquiv_val,
    LinearMap.toMatrix_apply, LinearEquiv.coe_coe, hg, map_smul, Finsupp.smul_apply,
    b.repr_self, Finsupp.single_eq_same, smul_eq_mul, mul_one]

theorem orderOf_four_of_basisMatrix (ι' : L →* (V ≃ₗ[K] V)) {ι : Type*} [Fintype ι]
    [DecidableEq ι] (b : Module.Basis ι K V) {g : L} (hg4 : g ^ 4 = 1) {i j : ι}
    (hij : (CFSG.ComponentClassification.CatalogueBAlternatingIsometry.basisMatrixEquiv b
        (ι' (g ^ 2))).val i i ≠
      (CFSG.ComponentClassification.CatalogueBAlternatingIsometry.basisMatrixEquiv b
        (ι' (g ^ 2))).val j j) :
    orderOf g = 4 ∧ (¬∃ c : K, ∀ v, ι' (g ^ 2) v = c • v) ∧
      ∀ (A : Subgroup L) [A.Normal], (∀ x ∈ A, ∃ c : K, ∀ v, ι' x v = c • v) →
        orderOf (g : L ⧸ A) = 4 := by
  have hns : ¬∃ c : K, ∀ v, ι' (g ^ 2) v = c • v := fun ⟨c, hc⟩ => hij (by
    rw [basisMatrixEquiv_apply_self_of_smul b _ c hc i,
      basisMatrixEquiv_apply_self_of_smul b _ c hc j])
  have hg2 : g ^ 2 ≠ 1 := fun h => hns ⟨1, fun v => by rw [h, map_one, one_smul]; rfl⟩
  exact ⟨SteinbergCD.orderOf_eq_four hg4 hg2, hns,
    fun A _ hA => SteinbergCD.orderOf_mk_eq_four hg4 fun hmem => hns (hA _ hmem)⟩

theorem ne_one_of_forall_neg (ι : L →* (V ≃ₗ[K] V)) (h2 : (2 : K) ≠ 0) [Nontrivial V] {z : L}
    (hz : ∀ v, ι z v = -v) : z ≠ 1 := by
  intro h
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  have h1 := hz v
  rw [h, map_one] at h1
  change v = -v at h1
  apply hv
  have h3 : (2 : K) • v = 0 := by
    rw [two_smul]
    nth_rewrite 1 [h1]
    exact neg_add_cancel v
  exact (smul_eq_zero.1 h3).resolve_left h2

theorem mem_iff_of_center_card_two (ι : L →* (V ≃ₗ[K] V)) (hι : Function.Injective ι)
    (A : Subgroup L) (hAc : A = center L) (hc2 : Nat.card (center L) = 2) {z : L}
    (hz : ∀ v, ι z v = -v) (hz1 : z ≠ 1) (g : L) :
    g ∈ A ↔ (∀ v, ι g v = v) ∨ ∀ v, ι g v = -v := by
  have hzc : z ∈ center L := mem_center_of_forall_smul ι hι (c := -1) fun v => by
    rw [hz, neg_one_smul]
  rw [hAc, mem_center_iff_of_card_center_eq_two hc2 hzc hz1]
  refine or_congr ⟨fun h v => by rw [h, map_one]; rfl, fun h => hι ?_⟩
    ⟨fun h v => by rw [h, hz], fun h => hι ?_⟩
  · exact LinearEquiv.ext fun v => by rw [h, map_one]; rfl
  · exact LinearEquiv.ext fun v => by rw [h, hz]

end Linear

theorem two_eq_zero_of_card {K : Type*} [Field K] {n : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = 2 ^ n) :
    (2 : K) = 0 := by
  have : CharP K 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two hn hK
  exact CharTwo.two_eq_zero

section SpecialLinear

open CFSG.LocalAnalysis.ComponentInitial

theorem linear_exists_orderOf_eq_four {k : Type*} [Field k] (h2 : (2 : k) ≠ 0) {d : ℕ}
    (hd : 3 ≤ d) :
    ∃ g : SpecialLinearGroup (Fin d) k, orderOf g = 4 ∧ g ^ 2 ∉ LinearFlag.scalars d k ∧
      ∀ (A : Subgroup (SpecialLinearGroup (Fin d) k)) [A.Normal], A ≤ LinearFlag.scalars d k →
        orderOf (g : SpecialLinearGroup (Fin d) k ⧸ A) = 4 := by
  set g := rotSL (F := k) (d := d) (by omega)
  have hg4 : g ^ 4 = 1 := rotSL_pow_four _
  have hnot : g ^ 2 ∉ LinearFlag.scalars d k := by
    rintro ⟨u, -, hu⟩
    have h1 := congrFun (congrFun hu ⟨0, by omega⟩) ⟨0, by omega⟩
    have h3 := congrFun (congrFun hu ⟨2, by omega⟩) ⟨2, by omega⟩
    rw [coe_rotSL_sq] at h1 h3
    rw [rot_sq_apply_left (Fin.ne_of_val_ne (by simp))] at h1
    rw [rot_sq_apply_other (Fin.ne_of_val_ne (by simp)) (Fin.ne_of_val_ne (by simp))] at h3
    simp only [scalar_apply, diagonal_apply_eq] at h1 h3
    apply h2
    linear_combination h3 - h1
  exact ⟨g, SteinbergCD.orderOf_eq_four hg4 fun h => hnot (h ▸ one_mem _), hnot,
    fun A _ hA => SteinbergCD.orderOf_mk_eq_four hg4 fun h => hnot (hA h)⟩

theorem linear_scalar_quotient_SL2 {k : Type} [Field k] [Finite k] (hk : Odd (Nat.card k))
    {n : ℕ} (hn : 2 ≤ n) (K : Type*) [Field K] (hK : Nat.card K = 2 ^ n) {d : ℕ} (hd : 2 ≤ d)
    (A : Subgroup (SpecialLinearGroup (Fin d) k)) [A.Normal] (hA : A ≤ LinearFlag.scalars d k)
    (φ : SpecialLinearGroup (Fin d) k ⧸ A ≃* SpecialLinearGroup (Fin 2) K) :
    n = 2 ∧ Nat.card k = 5 ∧ d = 2 ∧ A = LinearFlag.scalars d k ∧ Nat.card A = 2 ∧
      ∀ g, g ∈ A ↔ (g : Matrix (Fin d) (Fin d) k) = 1 ∨ (g : Matrix (Fin d) (Fin d) k) = -1 := by
  have h2k := two_ne_zero_of_odd_card hk
  have hd2 : d = 2 := by
    by_contra hne
    obtain ⟨g, -, -, hg⟩ := linear_exists_orderOf_eq_four h2k (show 3 ≤ d by omega)
    exact (isEmpty_mulEquiv_SL2_of_orderOf_eq_four (hg A hA) K
      (two_eq_zero_of_card (by omega) hK)).false φ
  subst hd2
  obtain ⟨hn2, hk5, hAc, hc2⟩ := sl2_odd_scalar_quotient_core hk (MulEquiv.refl _) A
    (hA.trans (LinearFlag.scalars_le_center 2 k)) hn K hK φ
  refine ⟨hn2, hk5, rfl, hAc.trans (LinearFlag.scalars_eq_center 2 k).symm, by rw [hAc, hc2],
    fun g => ?_⟩
  rw [hAc]
  exact mem_center_SL2_iff g

end SpecialLinear

section Unitary

open CFSG.ComponentClassification CatalogueBUnitaryIsometry CatalogueBUnitaryTwo
  CFSG.LieType.Universal.Unitary

variable {p f : ℕ} [Fact p.Prime] {E : Type} [Field E] [Finite E]
  {V : Type*} [AddCommGroup V] [Module E V]

theorem two_ne_zero_of_charP {F : Type*} [Field F] [CharP F p] (hp : p ≠ 2) : (2 : F) ≠ 0 := by
  intro h
  have h' : ((2 : ℕ) : F) = 0 := by exact_mod_cast h
  rw [CharP.cast_eq_zero_iff F p] at h'
  exact hp ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_two).1 h')

@[expose] def suToAut {hE : Nat.card E = (p ^ f) ^ 2}
    (h : V →ₛₗ[(unitaryFieldConjugation p f hE).toRingHom] V →ₗ[E] E) :
    specialIsometry h →* (V ≃ₗ[E] V) :=
  (isometryGroup h).subtype.comp (specialIsometry h).subtype

theorem suToAut_injective {hE : Nat.card E = (p ^ f) ^ 2}
    (h : V →ₛₗ[(unitaryFieldConjugation p f hE).toRingHom] V →ₗ[E] E) :
    Function.Injective (suToAut h) :=
  (isometryGroup h).subtype_injective.comp (specialIsometry h).subtype_injective

theorem unitary_exists_orderOf_eq_four [FiniteDimensional E V] (hp : p ≠ 2)
    (hE : Nat.card E = (p ^ f) ^ 2)
    (h : V →ₛₗ[(unitaryFieldConjugation p f hE).toRingHom] V →ₗ[E] E) (hsym : h.IsSymm)
    (hnd : h.Nondegenerate) (hd : 3 ≤ Module.finrank E V) :
    ∃ g : specialIsometry h, orderOf g = 4 ∧
      (¬∃ c : E, ∀ v, (((g ^ 2 : specialIsometry h) : isometryGroup h) : V ≃ₗ[E] V) v = c • v) ∧
      ∀ (A : Subgroup (specialIsometry h)) [A.Normal],
        (∀ x ∈ A, ∃ c : E, ∀ v, ((x : isometryGroup h) : V ≃ₗ[E] V) v = c • v) →
          orderOf (g : specialIsometry h ⧸ A) = 4 := by
  have : CharP E p := unitaryFieldCharP p f hE
  have h2 : (2 : E) ≠ 0 := two_ne_zero_of_charP hp
  obtain ⟨hσ2, hσ1, -⟩ := unitaryFieldConjugation_data p f hE
  obtain ⟨b, hb⟩ := CatalogueBHermitian.exists_orthonormal_basis h hsym hnd hσ2 hσ1
  let R : GL (Fin (Module.finrank E V)) E :=
    Matrix.SpecialLinearGroup.toGL (rotSL (F := E) (d := Module.finrank E V) (by omega))
  have hRm : (R : Matrix (Fin (Module.finrank E V)) (Fin (Module.finrank E V)) E) =
      rotMatrix ⟨0, by omega⟩ ⟨1, by omega⟩ := rfl
  have hR : R ∈ SUid (unitaryFieldConjugation p f hE) (Module.finrank E V) := by
    refine mem_SUid.2 ⟨(rotSL (F := E) (d := Module.finrank E V) (by omega)).2, ?_⟩
    rw [conjTr, hRm, rotMatrix_map (unitaryFieldConjugation p f hE)]
    exact rotMatrix_transpose_mul (Fin.ne_of_val_ne (by simp))
  let e := specialIsometryMatrixEquiv h b hb
  let g := e.symm ⟨R, hR⟩
  have hgb : CatalogueBAlternatingIsometry.basisMatrixEquiv b (suToAut h g) = R :=
    congrArg Subtype.val (e.apply_symm_apply ⟨R, hR⟩)
  have hg4 : g ^ 4 = 1 := by
    apply e.injective
    rw [map_pow, MulEquiv.apply_symm_apply, map_one]
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one, ← map_pow, rotSL_pow_four, map_one]
  have hg2 : (CatalogueBAlternatingIsometry.basisMatrixEquiv b (suToAut h (g ^ 2))).val =
      1 - 2 • single (⟨0, by omega⟩ : Fin (Module.finrank E V)) ⟨0, by omega⟩ 1 -
        2 • single (⟨1, by omega⟩ : Fin (Module.finrank E V)) ⟨1, by omega⟩ 1 := by
    rw [map_pow, map_pow, hgb, Units.val_pow_eq_pow_val, hRm, sq]
    exact rotMatrix_mul_self (Fin.ne_of_val_ne (by simp))
  obtain ⟨hord, hns, hA⟩ := orderOf_four_of_basisMatrix (suToAut h) b hg4
    (i := ⟨0, by omega⟩) (j := ⟨2, by omega⟩) (by
      rw [hg2, rot_sq_apply_left (Fin.ne_of_val_ne (by simp)),
        rot_sq_apply_other (Fin.ne_of_val_ne (by simp)) (Fin.ne_of_val_ne (by simp))]
      intro h1
      apply h2
      linear_combination -h1)
  exact ⟨g, hord, hns, fun A _ hAs => hA A hAs⟩

@[expose] def negSU [FiniteDimensional E V] {hE : Nat.card E = (p ^ f) ^ 2}
    (h : V →ₛₗ[(unitaryFieldConjugation p f hE).toRingHom] V →ₗ[E] E)
    (hdim : Module.finrank E V = 2) : specialIsometry h :=
  ⟨⟨LinearEquiv.neg E, (mem_isometryGroup_iff h _).2 fun x y => by
    change h (-x) (-y) = h x y
    rw [show h (-x) = -(h x) from map_neg h x, LinearMap.neg_apply, map_neg, neg_neg]⟩, by
    rw [mem_specialIsometry_iff]
    change LinearMap.det (-LinearMap.id : V →ₗ[E] V) = 1
    rw [← neg_one_smul E LinearMap.id, LinearMap.det_smul, LinearMap.det_id, hdim]
    norm_num⟩

theorem unitary_scalar_quotient_SL2 [FiniteDimensional E V] (hp : p ≠ 2) (hf : 1 ≤ f)
    (hE : Nat.card E = (p ^ f) ^ 2)
    (h : V →ₛₗ[(unitaryFieldConjugation p f hE).toRingHom] V →ₗ[E] E) (hsym : h.IsSymm)
    (hnd : h.Nondegenerate) (hdim : 2 ≤ Module.finrank E V) {n : ℕ} (hn : 2 ≤ n) (K : Type*)
    [Field K] (hK : Nat.card K = 2 ^ n) (A : Subgroup (specialIsometry h)) [A.Normal]
    (hA : ∀ g ∈ A, ∃ c : E, ∀ v, ((g : isometryGroup h) : V ≃ₗ[E] V) v = c • v)
    (φ : specialIsometry h ⧸ A ≃* SpecialLinearGroup (Fin 2) K) :
    n = 2 ∧ p ^ f = 5 ∧ Module.finrank E V = 2 ∧ Nat.card A = 2 ∧
      (∀ g, g ∈ A ↔ (∀ v, ((g : isometryGroup h) : V ≃ₗ[E] V) v = v) ∨
        ∀ v, ((g : isometryGroup h) : V ≃ₗ[E] V) v = -v) ∧
      ∀ g : specialIsometry h, (∃ c : E, ∀ v, ((g : isometryGroup h) : V ≃ₗ[E] V) v = c • v) →
        g ∈ A := by
  have : CharP E p := unitaryFieldCharP p f hE
  have h2 : (2 : E) ≠ 0 := two_ne_zero_of_charP hp
  have hd2 : Module.finrank E V = 2 := by
    by_contra hne
    obtain ⟨g, -, -, hg⟩ := unitary_exists_orderOf_eq_four hp hE h hsym hnd (by omega)
    exact (isEmpty_mulEquiv_SL2_of_orderOf_eq_four (hg A hA) K
      (two_eq_zero_of_card (by omega) hK)).false φ
  obtain ⟨hfix, -, -, e, -⟩ := odd_unitary_two_special_linear_isomorphism p f hp hf hE h hsym
    hnd hd2
  have hodd : Odd (Nat.card (CatalogueBLinearTwoDescent.fixedSubfield E
      (unitaryFieldConjugation p f hE))) := by
    rw [hfix]
    exact ((Fact.out : p.Prime).odd_of_ne_two hp).pow
  have hAz : A ≤ center (specialIsometry h) := fun g hg => by
    obtain ⟨c, hc⟩ := hA g hg
    exact mem_center_of_forall_smul (suToAut h) (suToAut_injective h) hc
  obtain ⟨hn2, h5, hAc, hc2⟩ := sl2_odd_scalar_quotient_core hodd e A hAz hn K hK φ
  have : Nontrivial V := Module.nontrivial_of_finrank_pos (R := E) (by omega)
  have hz : ∀ v, suToAut h (negSU h hd2) v = -v := fun v => by
    change (LinearEquiv.neg E) v = -v
    rfl
  refine ⟨hn2, hfix ▸ h5, hd2, by rw [hAc, hc2], fun g => ?_, fun g ⟨c, hc⟩ => ?_⟩
  · exact mem_iff_of_center_card_two (suToAut h) (suToAut_injective h) A hAc hc2 hz
      (ne_one_of_forall_neg (suToAut h) h2 hz) g
  · rw [hAc]
    exact mem_center_of_forall_smul (suToAut h) (suToAut_injective h) hc

end Unitary

section Symplectic

open CFSG.ComponentClassification CatalogueBAlternatingIsometry CatalogueBSymplecticB
open LinearMap (BilinForm)

theorem symplectic_exists_orderOf_eq_four {k : Type*} [Field k] (h2 : (2 : k) ≠ 0) {V : Type*}
    [AddCommGroup V] [Module k V] [FiniteDimensional k V] (B : BilinForm k V) (hB : B.IsAlt)
    (hnd : B.Nondegenerate) {r : ℕ} (hr : 2 ≤ r) (hdim : Module.finrank k V = 2 * r) :
    ∃ g : isometryGroup B, orderOf g = 4 ∧
      (¬∃ c : k, ∀ v, ((g ^ 2 : isometryGroup B) : V ≃ₗ[k] V) v = c • v) ∧
      ∀ (A : Subgroup (isometryGroup B)) [A.Normal],
        (∀ x ∈ A, ∃ c : k, ∀ v, (x : V ≃ₗ[k] V) v = c • v) →
          orderOf (g : isometryGroup B ⧸ A) = 4 := by
  obtain ⟨m, b, hm, hb⟩ := exists_symplectic_basis B hB hnd
  have hmr : 2 ≤ m := by omega
  set i₀ : Fin m := ⟨0, by omega⟩
  set i₁ : Fin m := ⟨1, by omega⟩
  set M := spRot (F := k) i₀
  have hM2 : M * M = fromBlocks (1 - 2 • single i₀ i₀ 1) 0 0 (1 - 2 • single i₀ i₀ 1) :=
    spRot_mul_self i₀
  have hM4 : M ^ 4 = 1 := by
    rw [show 4 = 2 * 2 from rfl, pow_mul, sq M, sq, hM2, spRot_sq_mul_self]
  set U : GL (Fin m ⊕ Fin m) k := ⟨M, M ^ 3, by rw [← pow_succ', hM4], by rw [← pow_succ, hM4]⟩
  have hU : U ∈ TauCeti.GLSymplectic (Fin m) k :=
    TauCeti.GLSymplectic.mem_iff'.2 (spRot_symplectic i₀)
  set eB := isometryMatrixEquiv b B hb
  set g := eB.symm ⟨U, hU⟩
  have hgb : basisMatrixEquiv b ((isometryGroup B).subtype g) = U :=
    congrArg Subtype.val (eB.apply_symm_apply ⟨U, hU⟩)
  have hg4 : g ^ 4 = 1 := by
    apply eB.injective
    rw [map_pow, MulEquiv.apply_symm_apply, map_one]
    apply Subtype.ext
    apply Units.ext
    rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val, Subgroup.coe_one, Units.val_one]
    exact hM4
  have hg2 : (basisMatrixEquiv b ((isometryGroup B).subtype (g ^ 2))).val =
      fromBlocks (1 - 2 • single i₀ i₀ 1) 0 0 (1 - 2 • single i₀ i₀ 1) := by
    rw [map_pow, map_pow, hgb, Units.val_pow_eq_pow_val, sq]
    exact hM2
  obtain ⟨hord, hns, hA⟩ := orderOf_four_of_basisMatrix (isometryGroup B).subtype b hg4
    (i := Sum.inl i₀) (j := Sum.inl i₁) (by
      rw [hg2, spRot_sq_apply_left, spRot_sq_apply_other (Fin.ne_of_val_ne (by simp [i₀, i₁]))]
      intro h1
      apply h2
      linear_combination -h1)
  exact ⟨g, hord, hns, fun A _ hAs => hA A hAs⟩

theorem symplectic_scalar_quotient_SL2 {k : Type} [Field k] [Finite k] (hk : Odd (Nat.card k))
    {V : Type*} [AddCommGroup V] [Module k V] [FiniteDimensional k V] (B : BilinForm k V)
    (hB : B.IsAlt) (hnd : B.Nondegenerate) {r : ℕ} (hr : 1 ≤ r)
    (hdim : Module.finrank k V = 2 * r) {n : ℕ} (hn : 2 ≤ n) (K : Type*) [Field K]
    (hK : Nat.card K = 2 ^ n) (A : Subgroup (isometryGroup B)) [A.Normal]
    (hA : ∀ g ∈ A, ∃ c : k, ∀ v, (g : V ≃ₗ[k] V) v = c • v)
    (φ : isometryGroup B ⧸ A ≃* SpecialLinearGroup (Fin 2) K) :
    n = 2 ∧ Nat.card k = 5 ∧ r = 1 ∧ Nat.card A = 2 ∧
      (∀ g, g ∈ A ↔ (∀ v, (g : V ≃ₗ[k] V) v = v) ∨ ∀ v, (g : V ≃ₗ[k] V) v = -v) ∧
      ∀ g : isometryGroup B, (∃ c : k, ∀ v, (g : V ≃ₗ[k] V) v = c • v) → g ∈ A := by
  have h2 := two_ne_zero_of_odd_card hk
  have hr1 : r = 1 := by
    by_contra hne
    obtain ⟨g, -, -, hg⟩ := symplectic_exists_orderOf_eq_four h2 B hB hnd (show 2 ≤ r by omega)
      hdim
    exact (isEmpty_mulEquiv_SL2_of_orderOf_eq_four (hg A hA) K
      (two_eq_zero_of_card (by omega) hK)).false φ
  subst hr1
  obtain ⟨e⟩ := exists_planeIsometryEquivSL B hB hnd (by omega)
  have hAz : A ≤ center (isometryGroup B) := fun g hg => by
    obtain ⟨c, hc⟩ := hA g hg
    exact mem_center_of_forall_smul (isometryGroup B).subtype (isometryGroup B).subtype_injective
      hc
  obtain ⟨hn2, hk5, hAc, hc2⟩ := sl2_odd_scalar_quotient_core hk e A hAz hn K hK φ
  have : Nontrivial V := Module.nontrivial_of_finrank_pos (R := k) (by omega)
  have hz : ∀ v, (isometryGroup B).subtype (negIsometry B) v = -v := fun v => rfl
  refine ⟨hn2, hk5, rfl, by rw [hAc, hc2], fun g => ?_, fun g ⟨c, hc⟩ => ?_⟩
  · exact mem_iff_of_center_card_two (isometryGroup B).subtype
      (isometryGroup B).subtype_injective A hAc hc2 hz (ne_one_of_forall_neg _ h2 hz) g
  · rw [hAc]
    exact mem_center_of_forall_smul (isometryGroup B).subtype (isometryGroup B).subtype_injective
      hc

end Symplectic

open CFSG.ComponentClassification CatalogueBUnitaryIsometry CatalogueBUnitaryTwo
  CatalogueBAlternatingIsometry CFSG.LocalAnalysis.ComponentInitial
open LinearMap (BilinForm)

universe u

theorem odd_classical_scalar_quotients_even_SL2_small_exception {n : ℕ} (hn : 2 ≤ n)
    (K : Type*) [Field K] (hK : Nat.card K = 2 ^ n) :
    (∀ (k : Type) [Field k] [Finite k], Odd (Nat.card k) → ∀ d : ℕ, 2 ≤ d →
      ∀ (A : Subgroup (SpecialLinearGroup (Fin d) k)) [A.Normal], A ≤ LinearFlag.scalars d k →
        Nonempty (SpecialLinearGroup (Fin d) k ⧸ A ≃* SpecialLinearGroup (Fin 2) K) →
          n = 2 ∧ Nat.card k = 5 ∧ d = 2 ∧ A = LinearFlag.scalars d k ∧ Nat.card A = 2 ∧
            ∀ g, g ∈ A ↔
              (g : Matrix (Fin d) (Fin d) k) = 1 ∨ (g : Matrix (Fin d) (Fin d) k) = -1) ∧
    (∀ (p f : ℕ) [Fact p.Prime], p ≠ 2 → 1 ≤ f → ∀ (E : Type) [Field E] [Finite E]
      (hE : Nat.card E = (p ^ f) ^ 2) (V : Type u) [AddCommGroup V] [Module E V]
      [FiniteDimensional E V] (h : V →ₛₗ[(unitaryFieldConjugation p f hE).toRingHom] V →ₗ[E] E),
      h.IsSymm → h.Nondegenerate → 2 ≤ Module.finrank E V →
      ∀ (A : Subgroup (specialIsometry h)) [A.Normal],
        (∀ g ∈ A, ∃ c : E, ∀ v, ((g : isometryGroup h) : V ≃ₗ[E] V) v = c • v) →
        Nonempty (specialIsometry h ⧸ A ≃* SpecialLinearGroup (Fin 2) K) →
          n = 2 ∧ p ^ f = 5 ∧ Module.finrank E V = 2 ∧ Nat.card A = 2 ∧
            (∀ g, g ∈ A ↔ (∀ v, ((g : isometryGroup h) : V ≃ₗ[E] V) v = v) ∨
              ∀ v, ((g : isometryGroup h) : V ≃ₗ[E] V) v = -v) ∧
            ∀ g : specialIsometry h,
              (∃ c : E, ∀ v, ((g : isometryGroup h) : V ≃ₗ[E] V) v = c • v) → g ∈ A) ∧
    (∀ (k : Type) [Field k] [Finite k], Odd (Nat.card k) → ∀ (V : Type u) [AddCommGroup V]
      [Module k V] [FiniteDimensional k V] (B : BilinForm k V), B.IsAlt → B.Nondegenerate →
      ∀ r : ℕ, 1 ≤ r → Module.finrank k V = 2 * r →
      ∀ (A : Subgroup (isometryGroup B)) [A.Normal],
        (∀ g ∈ A, ∃ c : k, ∀ v, (g : V ≃ₗ[k] V) v = c • v) →
        Nonempty (isometryGroup B ⧸ A ≃* SpecialLinearGroup (Fin 2) K) →
          n = 2 ∧ Nat.card k = 5 ∧ r = 1 ∧ Nat.card A = 2 ∧
            (∀ g, g ∈ A ↔ (∀ v, (g : V ≃ₗ[k] V) v = v) ∨ ∀ v, (g : V ≃ₗ[k] V) v = -v) ∧
            ∀ g : isometryGroup B, (∃ c : k, ∀ v, (g : V ≃ₗ[k] V) v = c • v) → g ∈ A) ∧
    (∀ (k : Type) [Field k] [Finite k], Odd (Nat.card k) → ∀ d : ℕ, 3 ≤ d →
      ∃ g : SpecialLinearGroup (Fin d) k, orderOf g = 4 ∧ g ^ 2 ∉ LinearFlag.scalars d k ∧
        ∀ (A : Subgroup (SpecialLinearGroup (Fin d) k)) [A.Normal], A ≤ LinearFlag.scalars d k →
          orderOf (g : SpecialLinearGroup (Fin d) k ⧸ A) = 4) ∧
    (∀ (p f : ℕ) [Fact p.Prime], p ≠ 2 → ∀ (E : Type) [Field E] [Finite E]
      (hE : Nat.card E = (p ^ f) ^ 2) (V : Type u) [AddCommGroup V] [Module E V]
      [FiniteDimensional E V] (h : V →ₛₗ[(unitaryFieldConjugation p f hE).toRingHom] V →ₗ[E] E),
      h.IsSymm → h.Nondegenerate → 3 ≤ Module.finrank E V →
      ∃ g : specialIsometry h, orderOf g = 4 ∧
        (¬∃ c : E, ∀ v, (((g ^ 2 : specialIsometry h) : isometryGroup h) : V ≃ₗ[E] V) v = c • v) ∧
        ∀ (A : Subgroup (specialIsometry h)) [A.Normal],
          (∀ x ∈ A, ∃ c : E, ∀ v, ((x : isometryGroup h) : V ≃ₗ[E] V) v = c • v) →
            orderOf (g : specialIsometry h ⧸ A) = 4) ∧
    (∀ (k : Type) [Field k] [Finite k], Odd (Nat.card k) → ∀ (V : Type u) [AddCommGroup V]
      [Module k V] [FiniteDimensional k V] (B : BilinForm k V), B.IsAlt → B.Nondegenerate →
      ∀ r : ℕ, 2 ≤ r → Module.finrank k V = 2 * r →
      ∃ g : isometryGroup B, orderOf g = 4 ∧
        (¬∃ c : k, ∀ v, ((g ^ 2 : isometryGroup B) : V ≃ₗ[k] V) v = c • v) ∧
        ∀ (A : Subgroup (isometryGroup B)) [A.Normal],
          (∀ x ∈ A, ∃ c : k, ∀ v, (x : V ≃ₗ[k] V) v = c • v) →
            orderOf (g : isometryGroup B ⧸ A) = 4) := by
  refine ⟨fun k _ _ hk d hd A _ hA ⟨φ⟩ => linear_scalar_quotient_SL2 hk hn K hK hd A hA φ,
    fun p f _ hp hf E _ _ hE V _ _ _ h hsym hnd hdim A _ hA ⟨φ⟩ =>
      unitary_scalar_quotient_SL2 hp hf hE h hsym hnd hdim hn K hK A hA φ,
    fun k _ _ hk V _ _ _ B hB hnd r hr hdim A _ hA ⟨φ⟩ =>
      symplectic_scalar_quotient_SL2 hk B hB hnd hr hdim hn K hK A hA φ,
    fun k _ _ hk d hd => linear_exists_orderOf_eq_four (two_ne_zero_of_odd_card hk) hd,
    fun p f _ hp E _ _ hE V _ _ _ h hsym hnd hd =>
      unitary_exists_orderOf_eq_four hp hE h hsym hnd hd,
    fun k _ _ hk V _ _ _ B hB hnd r hr hdim =>
      symplectic_exists_orderOf_eq_four (two_ne_zero_of_odd_card hk) B hB hnd hr hdim⟩

end CFSG.LocalAnalysis.SteinbergBT
