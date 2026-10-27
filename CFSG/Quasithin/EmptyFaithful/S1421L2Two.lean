module

public import CFSG.Quasithin.EmptyFaithful.S1421Surv

public section

open scoped MatrixGroups commutatorElement Pointwise

namespace CFSG.Quasithin

open CFSG.Open

namespace S1421L2Two

private theorem isSolvable_of_equiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y)
    [Group.IsSolvable Y] : Group.IsSolvable X :=
  Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective

private theorem card_perm_three : Nat.card (Equiv.Perm (Fin 3)) = 6 := by
  rw [Nat.card_perm]; simp [Nat.factorial]

private theorem pow_six_eq_one_of_equiv_perm_three {X : Type*} [Group X]
    (φ : X ≃* Equiv.Perm (Fin 3)) (x : X) : x ^ 6 = 1 := by
  apply φ.injective
  rw [map_pow, map_one, ← card_perm_three]
  exact pow_card_eq_one'

private theorem commutator_mem_of_closure {Γ : Type*} [Group Γ] {S : Set Γ} {N : Subgroup Γ}
    (hN : Subgroup.closure S ≤ Subgroup.normalizer (N : Set Γ))
    (hS : ∀ s ∈ S, ∀ t ∈ S, ⁅s, t⁆ ∈ N)
    {x y : Γ} (hx : x ∈ Subgroup.closure S) (hy : y ∈ Subgroup.closure S) : ⁅x, y⁆ ∈ N := by
  have conj : ∀ g ∈ Subgroup.closure S, ∀ n ∈ N, g * n * g⁻¹ ∈ N := fun g hg n hn =>
    (Subgroup.mem_normalizer_iff.mp (hN hg) n).mp hn
  induction hx, hy using Subgroup.closure_induction₂ with
  | mem x y hx hy => exact hS x hx y hy
  | one_left x hx => simp [N.one_mem]
  | one_right x hx => simp [N.one_mem]
  | mul_left x y z hx hy hz h1 h2 =>
    have : ⁅x * y, z⁆ = x * ⁅y, z⁆ * x⁻¹ * ⁅x, z⁆ := by
      simp only [commutatorElement_def]; group
    rw [this]
    exact N.mul_mem (conj x hx _ h2) h1
  | mul_right y z x hy hz hx h1 h2 =>
    have : ⁅x, y * z⁆ = ⁅x, y⁆ * (y * ⁅x, z⁆ * y⁻¹) := by
      simp only [commutatorElement_def]; group
    rw [this]
    exact N.mul_mem h1 (conj y hy _ h2)
  | inv_left x y hx hy h =>
    have : ⁅x⁻¹, y⁆ = x⁻¹ * ⁅x, y⁆⁻¹ * x⁻¹⁻¹ := by
      simp only [commutatorElement_def]; group
    rw [this]
    exact conj x⁻¹ (Subgroup.inv_mem _ hx) _ (N.inv_mem h)
  | inv_right x y hx hy h =>
    have : ⁅x, y⁻¹⁆ = y⁻¹ * ⁅x, y⁆⁻¹ * y⁻¹⁻¹ := by
      simp only [commutatorElement_def]; group
    rw [this]
    exact conj y⁻¹ (Subgroup.inv_mem _ hy) _ (N.inv_mem h)

private theorem mem_normalizer_zpowers {Γ : Type*} [Group Γ] {s c : Γ}
    (h1 : s * c * s⁻¹ ∈ Subgroup.zpowers c) (h2 : s⁻¹ * c * s ∈ Subgroup.zpowers c) :
    s ∈ Subgroup.normalizer (Subgroup.zpowers c : Set Γ) := by
  rw [Subgroup.mem_normalizer_iff]
  intro n
  constructor
  · intro hn
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hn
    rw [← conj_zpow]
    exact Subgroup.zpow_mem _ h1 k
  · intro hn
    have : n = s⁻¹ * (s * n * s⁻¹) * s := by group
    rw [this]
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hn
    rw [← hk]
    have h3 : s⁻¹ * c ^ k * s = (s⁻¹ * c * s) ^ k := by
      simpa using (conj_zpow (a := s⁻¹) (b := c) (i := k)).symm
    rw [h3]
    exact Subgroup.zpow_mem _ h2 k

private theorem isSolvable_closure_of_zpowers {Γ : Type*} [Group Γ] {S : Set Γ} {c : Γ}
    (hc : c ∈ Subgroup.closure S)
    (hnorm : ∀ s ∈ S, s * c * s⁻¹ ∈ Subgroup.zpowers c ∧ s⁻¹ * c * s ∈ Subgroup.zpowers c)
    (hcomm : ∀ s ∈ S, ∀ t ∈ S, ⁅s, t⁆ ∈ Subgroup.zpowers c) :
    Group.IsSolvable (Subgroup.closure S) := by
  have hnormalizer : Subgroup.closure S ≤ Subgroup.normalizer (Subgroup.zpowers c : Set Γ) := by
    rw [Subgroup.closure_le]
    intro s hs
    exact mem_normalizer_zpowers (hnorm s hs).1 (hnorm s hs).2
  have hNH : Subgroup.zpowers c ≤ Subgroup.closure S := by
    rw [Subgroup.zpowers_le]; exact hc
  have : ((Subgroup.zpowers c).subgroupOf (Subgroup.closure S)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNH).mpr hnormalizer
  have : Group.IsSolvable ((Subgroup.zpowers c).subgroupOf (Subgroup.closure S)) :=
    Group.isSolvable_of_isSolvable_injective (f := (Subgroup.subgroupOfEquivOfLe hNH).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hNH).injective
  have : IsMulCommutative (Subgroup.closure S ⧸
      (Subgroup.zpowers c).subgroupOf (Subgroup.closure S)) := by
    rw [Subgroup.Normal.quotient_commutative_iff_commutator_le, commutator_def]
    refine Subgroup.commutator_le.mpr fun x _ y _ => ?_
    rw [Subgroup.mem_subgroupOf]
    exact commutator_mem_of_closure hnormalizer hcomm x.2 y.2
  exact Group.isSolvable_of_subgroup_quotient
    ((Subgroup.zpowers c).subgroupOf (Subgroup.closure S))

private theorem card_zpowers_sup_zpowers_le {Γ : Type*} [Group Γ] {a c : Γ}
    (ha : a ∈ Subgroup.normalizer (Subgroup.zpowers c : Set Γ)) :
    Nat.card ↥(Subgroup.zpowers c ⊔ Subgroup.zpowers a) ≤ orderOf c * orderOf a := by
  have hle : Subgroup.zpowers a ≤ Subgroup.normalizer (Subgroup.zpowers c : Set Γ) := by
    rw [Subgroup.zpowers_le]; exact ha
  have h := Subgroup.coe_mul_of_right_le_normalizer_left (Subgroup.zpowers c) (Subgroup.zpowers a)
    hle
  calc Nat.card ↥(Subgroup.zpowers c ⊔ Subgroup.zpowers a)
      = Nat.card ↥((Subgroup.zpowers c : Set Γ) * (Subgroup.zpowers a : Set Γ)) := by
        rw [← h]; rfl
    _ ≤ Nat.card ↥(Subgroup.zpowers c : Set Γ) * Nat.card ↥(Subgroup.zpowers a : Set Γ) :=
        Set.natCard_mul_le
    _ = orderOf c * orderOf a := by
        rw [← Nat.card_zpowers c, ← Nat.card_zpowers a]; rfl

private theorem center_sl_two_eq_bot {K : Type*} [Field K] [CharP K 2] :
    Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K) = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  obtain ⟨r, hr, hrz⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hz
  have hr2 : r ^ 2 = 1 := by simpa using hr
  have hchar : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have h1 : (r - 1) ^ 2 = 0 := by linear_combination hr2 + (1 - r) * hchar
  have h2 : r = 1 := sub_eq_zero.mp (pow_eq_zero_iff (two_ne_zero) |>.mp h1)
  subst h2
  rw [Subgroup.mem_bot]
  apply Subtype.ext
  rw [← hrz]
  simp

private noncomputable def pslEquivSl (K : Type*) [Field K] [CharP K 2] :
    Matrix.ProjectiveSpecialLinearGroup (Fin 2) K ≃* Matrix.SpecialLinearGroup (Fin 2) K :=
  (QuotientGroup.quotientMulEquivOfEq center_sl_two_eq_bot).trans QuotientGroup.quotientBot

private noncomputable def slNonzeroPerm (F : Type) [Field F] :
    SL(2, F) →* Equiv.Perm {v : Fin 2 → F // v ≠ 0} where
  toFun A := Equiv.Perm.subtypePerm (MulAction.toPermHom SL(2, F) (Fin 2 → F) A) (by
    intro v
    simp only [MulAction.toPermHom_apply, MulAction.toPerm_apply, ne_eq]
    constructor
    · intro h h0
      apply h
      rw [h0, smul_zero]
    · intro h h0
      apply h
      have := congrArg (fun w => A⁻¹ • w) h0
      simpa [smul_smul] using this)
  map_one' := by
    ext v
    simp
  map_mul' A B := by
    ext v : 1
    apply Subtype.ext
    change (A * B) • (v : Fin 2 → F) = A • B • (v : Fin 2 → F)
    rw [mul_smul]

private theorem slNonzeroPerm_apply (F : Type) [Field F] (A : SL(2, F))
    (v : {v : Fin 2 → F // v ≠ 0}) :
    ((slNonzeroPerm F A v : {v : Fin 2 → F // v ≠ 0}) : Fin 2 → F) = A • (v : Fin 2 → F) :=
  rfl

private theorem slNonzeroPerm_injective (F : Type) [Field F] :
    Function.Injective (slNonzeroPerm F) := by
  rw [injective_iff_map_eq_one]
  intro A hA
  have key : ∀ v : Fin 2 → F, v ≠ 0 → A • v = v := by
    intro v hv
    have := congrArg (fun σ : Equiv.Perm {v : Fin 2 → F // v ≠ 0} => (σ ⟨v, hv⟩ : Fin 2 → F)) hA
    simpa [slNonzeroPerm_apply] using this
  have e0 := key (Pi.single 0 1) (by
    intro h; have := congrFun h 0; simp at this)
  have e1 := key (Pi.single 1 1) (by
    intro h; have := congrFun h 1; simp at this)
  rw [Matrix.SpecialLinearGroup.smul_def] at e0 e1
  have a00 : (A : Matrix (Fin 2) (Fin 2) F) 0 0 = 1 := by simpa using congrFun e0 0
  have a10 : (A : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := by simpa using congrFun e0 1
  have a01 : (A : Matrix (Fin 2) (Fin 2) F) 0 1 = 0 := by simpa using congrFun e1 0
  have a11 : (A : Matrix (Fin 2) (Fin 2) F) 1 1 = 1 := by simpa using congrFun e1 1
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [a00, a10, a01, a11]

private theorem card_galoisField_two_one : Nat.card (GaloisField 2 1) = 2 := by
  simpa using GaloisField.card 2 1 one_ne_zero

private theorem card_nonzero_vectors :
    Nat.card {v : Fin 2 → GaloisField 2 1 // v ≠ 0} = 3 := by
  classical
  let _ : Fintype (GaloisField 2 1) := Fintype.ofFinite _
  have hq : Fintype.card (GaloisField 2 1) = 2 := by
    rw [← Nat.card_eq_fintype_card]; exact card_galoisField_two_one
  rw [Nat.card_eq_fintype_card]
  have h1 : Fintype.card {v : Fin 2 → GaloisField 2 1 // v ≠ 0} =
      Fintype.card (Fin 2 → GaloisField 2 1) -
        Fintype.card {v : Fin 2 → GaloisField 2 1 // v = 0} :=
    Fintype.card_subtype_compl (fun v : Fin 2 → GaloisField 2 1 => v = 0)
  rw [h1, Fintype.card_subtype_eq, Fintype.card_fun, hq, Fintype.card_fin]
  norm_num

private theorem card_sl_two_galoisField_two_one : Nat.card (SL(2, GaloisField 2 1)) = 6 := by
  classical
  let _ : Fintype (GaloisField 2 1) := Fintype.ofFinite _
  have hq : Fintype.card (GaloisField 2 1) = 2 := by
    rw [← Nat.card_eq_fintype_card]; exact card_galoisField_two_one
  rw [Matrix.card_SL_field 2, hq]
  simp only [Fin.prod_univ_two, Fin.val_zero, Fin.val_one, pow_zero, pow_one]
  norm_num

private noncomputable def slTwoEquivPermThree :
    SL(2, GaloisField 2 1) ≃* Equiv.Perm (Fin 3) := by
  classical
  have hcardN : Nat.card {v : Fin 2 → GaloisField 2 1 // v ≠ 0} = 3 := card_nonzero_vectors
  have hbij : Function.Bijective (slNonzeroPerm (GaloisField 2 1)) := by
    refine ⟨slNonzeroPerm_injective _, ?_⟩
    have : Finite (Equiv.Perm {v : Fin 2 → GaloisField 2 1 // v ≠ 0}) := inferInstance
    have h1 : Nat.card (Equiv.Perm {v : Fin 2 → GaloisField 2 1 // v ≠ 0}) = 6 := by
      rw [Nat.card_perm, hcardN]; rfl
    exact (Function.Injective.bijective_of_nat_card_le (slNonzeroPerm_injective _)
      (by rw [h1, card_sl_two_galoisField_two_one])).2
  exact (MulEquiv.ofBijective (slNonzeroPerm (GaloisField 2 1)) hbij).trans
    (Equiv.permCongrHom ((Finite.equivFin _).trans (finCongr hcardN)))

end S1421L2Two

theorem isL2Quot_one_iff_perm3 {X : Type*} [Group X] :
    IsL2Quot 1 X ↔ Nonempty (X ≃* Equiv.Perm (Fin 3)) := by
  let e : Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 1) ≃*
      Equiv.Perm (Fin 3) :=
    (S1421L2Two.pslEquivSl (GaloisField 2 1)).trans S1421L2Two.slTwoEquivPermThree
  constructor
  · rintro ⟨f⟩
    exact ⟨f.trans e⟩
  · rintro ⟨f⟩
    exact ⟨f.trans e.symm⟩

theorem not_isL2Quot_of_perm3 {f : ℕ} (hf : 2 ≤ f) {X : Type*} [Group X]
    (h : IsL2Quot f X) (e : X ≃* Equiv.Perm (Fin 3)) : False := by
  obtain ⟨g⟩ := h
  have h4 : 4 ≤ Nat.card (GaloisField 2 f) := by
    rw [GaloisField.card 2 f (by omega)]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 f)) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple h4
  have : IsSimpleGroup (Equiv.Perm (Fin 3)) := (g.symm.trans e).symm.isSimpleGroup
  have h3 : Equiv.swap (0 : Fin 3) 1 * Equiv.swap 1 2 ∈ alternatingGroup (Fin 3) := by
    rw [Equiv.Perm.mem_alternatingGroup]
    simp [Equiv.Perm.sign_mul]
  have h3' : Equiv.swap (0 : Fin 3) 1 ∉ alternatingGroup (Fin 3) := by
    rw [Equiv.Perm.mem_alternatingGroup]
    simp
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (alternatingGroup (Fin 3)) with h | h
  · rw [h, Subgroup.mem_bot] at h3
    revert h3
    decide
  · rw [h] at h3'
    exact h3' (Subgroup.mem_top _)

theorem isSolvable_of_isL2Quot_one {X : Type*} [Group X] (h : IsL2Quot 1 X) :
    Group.IsSolvable X := by
  obtain ⟨e⟩ := isL2Quot_one_iff_perm3.mp h
  have : Group.IsSolvable (Equiv.Perm (Fin 3)) := Equiv.Perm.isSolvable (by simp)
  exact S1421L2Two.isSolvable_of_equiv e

theorem isSolvable_of_equiv_dihedral_five {X : Type*} [Group X] (e : X ≃* DihedralGroup 5) :
    Group.IsSolvable X := by
  have : IsZGroup (DihedralGroup 5) := IsZGroup.of_squarefree (by
    rw [DihedralGroup.nat_card]
    exact (Nat.squarefree_mul (by norm_num)).mpr
      ⟨Nat.prime_two.squarefree, Nat.prime_five.squarefree⟩)
  exact S1421L2Two.isSolvable_of_equiv e

theorem isSolvable_of_equiv_perm_four {X : Type*} [Group X] (e : X ≃* Equiv.Perm (Fin 4)) :
    Group.IsSolvable X := by
  have : Group.IsSolvable (Equiv.Perm (Fin 4)) := Equiv.Perm.isSolvable (by simp)
  exact S1421L2Two.isSolvable_of_equiv e

theorem isSolvable_of_equiv_z2_perm_four {X : Type*} [Group X]
    (e : X ≃* Multiplicative (ZMod 2) × Equiv.Perm (Fin 4)) : Group.IsSolvable X := by
  have : Group.IsSolvable (Equiv.Perm (Fin 4)) := Equiv.Perm.isSolvable (by simp)
  exact S1421L2Two.isSolvable_of_equiv e

theorem not_equiv_dihedral5_perm3 {X : Type*} [Group X] (e : X ≃* DihedralGroup 5) :
    ¬ Nonempty (X ≃* Equiv.Perm (Fin 3)) := by
  rintro ⟨φ⟩
  have h := Nat.card_congr (e.symm.trans φ).toEquiv
  rw [DihedralGroup.nat_card, S1421L2Two.card_perm_three] at h
  omega

theorem not_isSolvable_perm5 {X : Type*} [Group X] (e : X ≃* Equiv.Perm (Fin 5)) :
    ¬ Group.IsSolvable X := fun _ =>
  Equiv.Perm.not_isSolvable_fin_5 (Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective)

namespace S1421L2Two

section Matrices

variable {K : Type*} [Field K]

private def matA : Matrix (Fin 4) (Fin 4) K :=
  !![1, 1, 0, 1; 0, 1, 1, 1; 0, 0, 1, 1; 0, 0, 0, 1]

private def matB : Matrix (Fin 4) (Fin 4) K :=
  !![1, 0, 1, 1; 0, 1, 0, 1; 0, 0, 1, 0; 0, 0, 0, 1]

private def matC : Matrix (Fin 4) (Fin 4) K :=
  !![1, 1, 1, 1; 0, 1, 1, 0; 0, 0, 1, 1; 0, 0, 0, 1]

private def matW : Matrix (Fin 4) (Fin 4) K :=
  !![0, 0, 0, 1; 0, 0, 1, 0; 0, 1, 0, 0; 1, 0, 0, 0]

private def matComm : Matrix (Fin 4) (Fin 4) K :=
  !![1, 0, 1, 1; 0, 1, 0, 1; 1, 0, 0, 1; 1, 1, 1, 1]

private def matComm2 : Matrix (Fin 4) (Fin 4) K :=
  !![1, 1, 0, 1; 1, 0, 1, 0; 0, 1, 0, 0; 1, 0, 0, 0]

private theorem matA_mul_matC (h2 : (1 : K) + 1 = 0) :
    (matA * matC : Matrix (Fin 4) (Fin 4) K) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [matA, matC, Matrix.mul_apply, Fin.sum_univ_four, h2]

private theorem matC_mul_matA (h2 : (1 : K) + 1 = 0) :
    (matC * matA : Matrix (Fin 4) (Fin 4) K) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [matA, matC, Matrix.mul_apply, Fin.sum_univ_four, h2]

private theorem matW_mul_matW : (matW * matW : Matrix (Fin 4) (Fin 4) K) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [matW, Matrix.mul_apply, Fin.sum_univ_four]

private theorem matA_mul_matA (h2 : (1 : K) + 1 = 0) :
    (matA * matA : Matrix (Fin 4) (Fin 4) K) = matB := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [matA, matB, Matrix.mul_apply, Fin.sum_univ_four, h2]

private theorem matB_mul_matA (h2 : (1 : K) + 1 = 0) :
    (matB * matA : Matrix (Fin 4) (Fin 4) K) = matC := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [matA, matB, matC, Matrix.mul_apply, Fin.sum_univ_four, h2]

private theorem matB_mul_matB (h2 : (1 : K) + 1 = 0) :
    (matB * matB : Matrix (Fin 4) (Fin 4) K) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [matB, Matrix.mul_apply, Fin.sum_univ_four, h2]

private theorem matA_mul_matW_mul_matC_mul_matW (h2 : (1 : K) + 1 = 0) :
    (matA * matW * matC * matW : Matrix (Fin 4) (Fin 4) K) = matComm := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [matA, matW, matC, matComm, Matrix.mul_apply, Fin.sum_univ_four, h2]

private theorem matA_conj (h2 : (1 : K) + 1 = 0) :
    (matA * matComm * matC : Matrix (Fin 4) (Fin 4) K) = matComm * matComm * matComm := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [matA, matC, matComm, Matrix.mul_apply, Fin.sum_univ_four, h2]

private theorem matC_conj (h2 : (1 : K) + 1 = 0) :
    (matC * matComm * matA : Matrix (Fin 4) (Fin 4) K) = matComm * matComm := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [matA, matC, matComm, Matrix.mul_apply, Fin.sum_univ_four, h2]

private theorem matW_conj (h2 : (1 : K) + 1 = 0) :
    (matW * matComm * matW : Matrix (Fin 4) (Fin 4) K) = matComm * matComm * matComm * matComm := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [matW, matComm, Matrix.mul_apply, Fin.sum_univ_four, h2]

private theorem matComm_mul_matComm (h2 : (1 : K) + 1 = 0) :
    (matComm * matComm : Matrix (Fin 4) (Fin 4) K) = matComm2 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [matComm, matComm2, Matrix.mul_apply, Fin.sum_univ_four, h2]

private theorem matComm2_mul_matComm2_mul_matComm (h2 : (1 : K) + 1 = 0) :
    (matComm2 * matComm2 * matComm : Matrix (Fin 4) (Fin 4) K) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [matComm, matComm2, Matrix.mul_apply, Fin.sum_univ_four, h2]

private theorem matComm2_mul_matComm_mul_matB (h2 : (1 : K) + 1 = 0) :
    (matComm2 * matComm * matB : Matrix (Fin 4) (Fin 4) K) = matW := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [matComm, matComm2, matB, matW, Matrix.mul_apply, Fin.sum_univ_four, h2]

private def unitA (h2 : (1 : K) + 1 = 0) : GL (Fin 4) K :=
  ⟨matA, matC, matA_mul_matC h2, matC_mul_matA h2⟩

private def unitW : GL (Fin 4) K := ⟨matW, matW, matW_mul_matW, matW_mul_matW⟩

private theorem unitA_val (h2 : (1 : K) + 1 = 0) :
    ((unitA h2 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = matA := rfl

private theorem unitA_inv_val (h2 : (1 : K) + 1 = 0) :
    (((unitA h2)⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = matC := rfl

private theorem unitW_val : ((unitW : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = matW := rfl

private theorem unitW_inv_val :
    (((unitW : GL (Fin 4) K)⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = matW := rfl

private theorem comm_val (h2 : (1 : K) + 1 = 0) :
    ((⁅unitA h2, unitW⁆ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = matComm := by
  simp only [commutatorElement_def, Units.val_mul, unitA_val, unitW_val, unitA_inv_val,
    unitW_inv_val]
  rw [matA_mul_matW_mul_matC_mul_matW h2]

private theorem unitA_conj_comm (h2 : (1 : K) + 1 = 0) :
    unitA h2 * ⁅unitA h2, unitW⁆ * (unitA h2)⁻¹ = ⁅unitA h2, unitW⁆ ^ 3 := by
  ext1
  simp only [Units.val_mul, comm_val h2, unitA_val, unitA_inv_val, pow_succ, pow_zero, one_mul]
  exact matA_conj h2

private theorem unitA_inv_conj_comm (h2 : (1 : K) + 1 = 0) :
    (unitA h2)⁻¹ * ⁅unitA h2, unitW⁆ * unitA h2 = ⁅unitA h2, unitW⁆ ^ 2 := by
  ext1
  simp only [Units.val_mul, comm_val h2, unitA_val, unitA_inv_val, pow_succ, pow_zero, one_mul]
  exact matC_conj h2

private theorem unitW_conj_comm (h2 : (1 : K) + 1 = 0) :
    (unitW : GL (Fin 4) K) * ⁅unitA h2, unitW⁆ * unitW⁻¹ = ⁅unitA h2, unitW⁆ ^ 4 := by
  ext1
  simp only [Units.val_mul, comm_val h2, unitW_val, unitW_inv_val, pow_succ, pow_zero, one_mul]
  exact matW_conj h2

private theorem isSolvable_closure_unitA_unitW (h2 : (1 : K) + 1 = 0) :
    Group.IsSolvable (Subgroup.closure ({unitA h2, unitW} : Set (GL (Fin 4) K))) := by
  refine isSolvable_closure_of_zpowers (c := ⁅unitA h2, unitW⁆) ?_ ?_ ?_
  · rw [commutatorElement_def]
    refine Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ ?_ ?_) ?_) ?_
    · exact Subgroup.subset_closure (by simp)
    · exact Subgroup.subset_closure (by simp)
    · exact Subgroup.inv_mem _ (Subgroup.subset_closure (by simp))
    · exact Subgroup.inv_mem _ (Subgroup.subset_closure (by simp))
  · rintro s (rfl | rfl)
    · rw [unitA_conj_comm h2, unitA_inv_conj_comm h2]
      exact ⟨Subgroup.pow_mem _ (Subgroup.mem_zpowers _) 3,
        Subgroup.pow_mem _ (Subgroup.mem_zpowers _) 2⟩
    · have hw : (unitW : GL (Fin 4) K)⁻¹ = unitW := rfl
      have h4 := unitW_conj_comm h2
      rw [hw] at h4 ⊢
      rw [h4]
      exact ⟨Subgroup.pow_mem _ (Subgroup.mem_zpowers _) 4,
        Subgroup.pow_mem _ (Subgroup.mem_zpowers _) 4⟩
  · rintro s (rfl | rfl) t (rfl | rfl)
    · rw [commutatorElement_self]; exact Subgroup.one_mem _
    · exact Subgroup.mem_zpowers _
    · rw [← commutatorElement_inv]; exact Subgroup.inv_mem _ (Subgroup.mem_zpowers _)
    · rw [commutatorElement_self]; exact Subgroup.one_mem _

private theorem one_add_one_of_charP [CharP K 2] : (1 : K) + 1 = 0 := by
  rw [one_add_one_eq_two]; exact CharP.cast_eq_zero K 2

private theorem unitA_sq_ne_one (h2 : (1 : K) + 1 = 0) : (unitA h2) ^ 2 ≠ 1 := by
  intro h
  have h1 := congrArg (fun u : GL (Fin 4) K => (u : Matrix (Fin 4) (Fin 4) K)) h
  simp only [Units.val_pow_eq_pow_val, unitA_val, Units.val_one] at h1
  rw [pow_two, matA_mul_matA h2] at h1
  have := congrFun (congrFun h1 0) 2
  simp [matB] at this

private theorem unitA_pow_four (h2 : (1 : K) + 1 = 0) : (unitA h2) ^ 4 = 1 := by
  ext1
  have : (matA ^ 4 : Matrix (Fin 4) (Fin 4) K) = matA * matA * (matA * matA) := by
    simp only [pow_succ, pow_zero, one_mul, mul_assoc]
  simp only [Units.val_pow_eq_pow_val, unitA_val, Units.val_one, this, matA_mul_matA h2,
    matB_mul_matB h2]

private theorem orderOf_unitA (h2 : (1 : K) + 1 = 0) : orderOf (unitA h2) = 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := orderOf_eq_prime_pow (x := unitA h2) (n := 1) (p := 2)
    (by simpa using unitA_sq_ne_one h2) (by simpa using unitA_pow_four h2)
  simpa using h

private theorem unitA_pow_six_ne_one (h2 : (1 : K) + 1 = 0) : (unitA h2) ^ 6 ≠ 1 := by
  rw [show 6 = 4 + 2 from rfl, pow_add, unitA_pow_four h2, one_mul]
  exact unitA_sq_ne_one h2

private theorem orderOf_comm (h2 : (1 : K) + 1 = 0) : orderOf (⁅unitA h2, unitW⁆ : GL (Fin 4) K) = 5 := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have h5 : (⁅unitA h2, unitW⁆ : GL (Fin 4) K) ^ 5 = 1 := by
    ext1
    have : (matComm ^ 5 : Matrix (Fin 4) (Fin 4) K) = matComm2 * matComm2 * matComm := by
      rw [← matComm_mul_matComm h2]
      simp only [pow_succ, pow_zero, one_mul, mul_assoc]
    simp only [Units.val_pow_eq_pow_val, comm_val h2, Units.val_one, this,
      matComm2_mul_matComm2_mul_matComm h2]
  refine orderOf_eq_prime h5 ?_
  intro h
  have h1 := congrArg (fun u : GL (Fin 4) K => (u : Matrix (Fin 4) (Fin 4) K)) h
  simp only [comm_val h2, Units.val_one] at h1
  have := congrFun (congrFun h1 0) 2
  simp [matComm] at this

private theorem unitW_eq (h2 : (1 : K) + 1 = 0) :
    (unitW : GL (Fin 4) K) = ⁅unitA h2, unitW⁆ ^ 3 * (unitA h2 * unitA h2) := by
  ext1
  simp only [Units.val_mul, Units.val_pow_eq_pow_val, comm_val h2, unitA_val, matA_mul_matA h2,
    unitW_val]
  have : (matComm ^ 3 : Matrix (Fin 4) (Fin 4) K) = matComm2 * matComm := by
    rw [← matComm_mul_matComm h2]
    simp only [pow_succ, pow_zero, one_mul, mul_assoc]
  rw [this]
  exact (matComm2_mul_matComm_mul_matB h2).symm

private theorem card_closure_unitA_unitW_le [Finite K] (h2 : (1 : K) + 1 = 0) :
    Nat.card ↥(Subgroup.closure ({unitA h2, unitW} : Set (GL (Fin 4) K))) ≤ 20 := by
  have hn : unitA h2 ∈ Subgroup.normalizer
      (Subgroup.zpowers (⁅unitA h2, unitW⁆ : GL (Fin 4) K) : Set (GL (Fin 4) K)) := by
    refine mem_normalizer_zpowers ?_ ?_
    · rw [unitA_conj_comm h2]; exact Subgroup.pow_mem _ (Subgroup.mem_zpowers _) 3
    · rw [unitA_inv_conj_comm h2]; exact Subgroup.pow_mem _ (Subgroup.mem_zpowers _) 2
  have hle : Subgroup.closure ({unitA h2, unitW} : Set (GL (Fin 4) K)) ≤
      Subgroup.zpowers (⁅unitA h2, unitW⁆ : GL (Fin 4) K) ⊔ Subgroup.zpowers (unitA h2) := by
    rw [Subgroup.closure_le]
    rintro s (rfl | rfl)
    · exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
    · have h3 : (⁅unitA h2, unitW⁆ : GL (Fin 4) K) ^ 3 * (unitA h2 * unitA h2) ∈
          Subgroup.zpowers (⁅unitA h2, unitW⁆ : GL (Fin 4) K) ⊔ Subgroup.zpowers (unitA h2) :=
        Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.pow_mem _ (Subgroup.mem_zpowers _) 3))
          (Subgroup.mul_mem _ (Subgroup.mem_sup_right (Subgroup.mem_zpowers _))
            (Subgroup.mem_sup_right (Subgroup.mem_zpowers _)))
      rwa [← unitW_eq h2] at h3
  calc _ ≤ _ := Subgroup.card_le_of_le hle
    _ ≤ orderOf (⁅unitA h2, unitW⁆ : GL (Fin 4) K) * orderOf (unitA h2) :=
        card_zpowers_sup_zpowers_le hn
    _ = 20 := by rw [orderOf_comm h2, orderOf_unitA h2]

end Matrices

private theorem unitA_mem_sz (a : ℕ) :
    unitA (one_add_one_of_charP (K := GaloisField 2 (2 * a + 1))) ∈ Sz a := by
  apply Subgroup.subset_closure
  refine Or.inl ⟨1, 0, ?_⟩
  rw [unitA_val]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [matA]

private abbrev F2 : Type := GaloisField 2 (2 * 0 + 1)

private theorem f2_eq_zero_or_eq_one (x : F2) : x = 0 ∨ x = 1 := by
  have hcard : Nat.card F2 = 2 := by
    have := GaloisField.card 2 (2 * 0 + 1) (by norm_num)
    simpa using this
  have : Finite F2 := inferInstance
  classical
  let _ : Fintype F2 := Fintype.ofFinite _
  have hc : Fintype.card F2 = 2 := by rw [← Nat.card_eq_fintype_card]; exact hcard
  have hx := FiniteField.pow_card x
  rw [hc] at hx
  have h2 : x * (x - 1) = 0 := by linear_combination hx
  rcases mul_eq_zero.mp h2 with h | h
  · exact Or.inl h
  · exact Or.inr (sub_eq_zero.mp h)

private theorem sz_zero_le_closure :
    Sz 0 ≤ Subgroup.closure ({unitA (one_add_one_of_charP (K := F2)), unitW} :
      Set (GL (Fin 4) F2)) := by
  have h2 : (1 : F2) + 1 = 0 := one_add_one_of_charP
  unfold Sz
  rw [Subgroup.closure_le]
  intro g hg
  simp only [SzGenerators, Set.mem_ofPred_eq] at hg
  have hA : unitA h2 ∈ Subgroup.closure ({unitA h2, unitW} : Set (GL (Fin 4) F2)) :=
    Subgroup.subset_closure (by simp)
  rcases hg with ⟨α, β, h⟩ | ⟨x, h⟩ | h
  · rcases f2_eq_zero_or_eq_one α with rfl | rfl <;> rcases f2_eq_zero_or_eq_one β with rfl | rfl
    · have : g = 1 := Units.ext (by
        rw [h]; ext i j; fin_cases i <;> fin_cases j <;> simp)
      rw [this]; exact Subgroup.one_mem _
    · have : g = unitA h2 * unitA h2 := Units.ext (by
        rw [h, Units.val_mul, unitA_val, matA_mul_matA h2]
        ext i j; fin_cases i <;> fin_cases j <;> simp [matB])
      rw [this]; exact Subgroup.mul_mem _ hA hA
    · have : g = unitA h2 := Units.ext (by
        rw [h, unitA_val]; ext i j; fin_cases i <;> fin_cases j <;> simp [matA])
      rw [this]; exact hA
    · have : g = unitA h2 * unitA h2 * unitA h2 := Units.ext (by
        rw [h, Units.val_mul, Units.val_mul, unitA_val, matA_mul_matA h2, matB_mul_matA h2]
        ext i j; fin_cases i <;> fin_cases j <;> simp [matC, h2])
      rw [this]; exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hA hA) hA
  · have hx : (x : F2) = 1 := by
      rcases f2_eq_zero_or_eq_one (x : F2) with h0 | h1
      · exact absurd h0 x.ne_zero
      · exact h1
    have : g = 1 := Units.ext (by
      rw [h, hx]; ext i j; fin_cases i <;> fin_cases j <;> simp)
    rw [this]; exact Subgroup.one_mem _
  · have : g = unitW := Units.ext (by rw [h]; rfl)
    rw [this]; exact Subgroup.subset_closure (by simp)

private theorem card_sz_zero_le : Nat.card ↥(Sz 0) ≤ 20 :=
  (Subgroup.card_le_of_le sz_zero_le_closure).trans (card_closure_unitA_unitW_le _)

private theorem unitW_mem_sz (a : ℕ) :
    (unitW : GL (Fin 4) (GaloisField 2 (2 * a + 1))) ∈ Sz a := by
  apply Subgroup.subset_closure
  exact Or.inr (Or.inr rfl)

private theorem twenty_dvd_card_sz_zero : 20 ∣ Nat.card ↥(Sz 0) := by
  have h2 : (1 : F2) + 1 = 0 := one_add_one_of_charP
  have ha : unitA h2 ∈ Sz 0 := unitA_mem_sz 0
  have hw : (unitW : GL (Fin 4) F2) ∈ Sz 0 := unitW_mem_sz 0
  have hc : (⁅unitA h2, unitW⁆ : GL (Fin 4) F2) ∈ Sz 0 := by
    rw [commutatorElement_def]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ ha hw)
      (Subgroup.inv_mem _ ha)) (Subgroup.inv_mem _ hw)
  have h4 : 4 ∣ Nat.card ↥(Sz 0) := by
    have := Subgroup.card_dvd_of_le
      (show Subgroup.zpowers (unitA h2) ≤ Sz 0 by rwa [Subgroup.zpowers_le])
    rwa [Nat.card_zpowers, orderOf_unitA h2] at this
  have h5 : 5 ∣ Nat.card ↥(Sz 0) := by
    have := Subgroup.card_dvd_of_le
      (show Subgroup.zpowers (⁅unitA h2, unitW⁆ : GL (Fin 4) F2) ≤ Sz 0 by
        rwa [Subgroup.zpowers_le])
    rwa [Nat.card_zpowers, orderOf_comm h2] at this
  exact (show Nat.Coprime 4 5 by norm_num).mul_dvd_of_dvd_of_dvd h4 h5

private theorem isSolvable_sz_zero : Group.IsSolvable ↥(Sz 0) := by
  have : Group.IsSolvable (Subgroup.closure ({unitA (one_add_one_of_charP (K := F2)), unitW} :
      Set (GL (Fin 4) F2))) := isSolvable_closure_unitA_unitW _
  exact Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion sz_zero_le_closure)
    (Subgroup.inclusion_injective sz_zero_le_closure)

end S1421L2Two

theorem card_sz_zero : Nat.card ↥(CFSG.Open.Sz 0) = 20 :=
  le_antisymm S1421L2Two.card_sz_zero_le
    (Nat.le_of_dvd Nat.card_pos S1421L2Two.twenty_dvd_card_sz_zero)

theorem isSolvable_of_equiv_sz_zero {X : Type*} [Group X] (e : X ≃* ↥(CFSG.Open.Sz 0)) :
    Group.IsSolvable X := by
  have := S1421L2Two.isSolvable_sz_zero
  exact S1421L2Two.isSolvable_of_equiv e

theorem not_equiv_sz_perm3 (a : ℕ) {X : Type*} [Group X] (e : X ≃* ↥(CFSG.Open.Sz a)) :
    ¬ Nonempty (X ≃* Equiv.Perm (Fin 3)) := by
  rintro ⟨φ⟩
  have h1 : (⟨_, S1421L2Two.unitA_mem_sz a⟩ : ↥(CFSG.Open.Sz a)) ^ 6 = 1 :=
    S1421L2Two.pow_six_eq_one_of_equiv_perm_three (e.symm.trans φ) _
  have h2 := congrArg Subtype.val h1
  exact S1421L2Two.unitA_pow_six_ne_one _ (by simpa using h2)

theorem not_equiv_statedSU_perm3 {X : Type*} [Group X] {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = 4 ^ 2) (e : X ≃* CFSG.Open.StatedSU 3 4 F) :
    ¬ Nonempty (X ≃* Equiv.Perm (Fin 3)) := by
  rintro ⟨φ⟩
  have h5 : 5 ∣ Nat.card Fˣ := by rw [Nat.card_units, hF]; norm_num
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨ζ, hζ⟩ := exists_prime_orderOf_dvd_card' 5 h5
  have hζ5 : ζ ^ 5 = 1 := hζ ▸ pow_orderOf_eq_one ζ
  have hζ1 : ζ ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hζ
    omega
  have hz5 : (ζ : F) ^ 5 = 1 := by
    rw [← Units.val_pow_eq_pow_val, hζ5, Units.val_one]
  have h4a : (ζ : F) ^ 4 * (ζ : F) = 1 := by rw [← pow_succ]; exact hz5
  have h4b : ((ζ : F) ^ 4)⁻¹ * (ζ : F)⁻¹ = 1 := by
    rw [← mul_inv_rev, ← pow_succ', hz5, inv_one]
  set M : Matrix (Fin 3) (Fin 3) F := Matrix.diagonal ![(ζ : F), ((ζ⁻¹ : Fˣ) : F), 1] with hM
  set M' : Matrix (Fin 3) (Fin 3) F := Matrix.diagonal ![((ζ⁻¹ : Fˣ) : F), (ζ : F), 1] with hM'
  have hMM' : M * M' = 1 := by
    rw [hM, hM', Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    ext i
    fin_cases i <;> simp
  have hM'M : M' * M = 1 := by
    rw [hM, hM', Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    ext i
    fin_cases i <;> simp
  let u : GL (Fin 3) F := ⟨M, M', hMM', hM'M⟩
  have hu : u ∈ CFSG.Open.StatedSU 3 4 F := by
    apply Subgroup.subset_closure
    refine ⟨?_, ?_⟩
    · show M.det = 1
      simp [hM, Matrix.det_diagonal, Fin.prod_univ_three]
    · show Matrix.transpose (M.map (· ^ 4)) * M = 1
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [hM, Matrix.mul_apply, Matrix.diagonal_apply, h4a, h4b]
  have h1 : (⟨u, hu⟩ : ↥(CFSG.Open.StatedSU 3 4 F)) ^ 6 = 1 :=
    S1421L2Two.pow_six_eq_one_of_equiv_perm_three (e.symm.trans φ) _
  have h2 : u ^ 6 = 1 := congrArg Subtype.val h1
  have h3 := congrArg (fun v : GL (Fin 3) F => (v : Matrix (Fin 3) (Fin 3) F)) h2
  simp only [Units.val_pow_eq_pow_val, Units.val_one] at h3
  have h00 := congrFun (congrFun h3 0) 0
  rw [show (u : Matrix (Fin 3) (Fin 3) F) = M from rfl, hM, Matrix.diagonal_pow] at h00
  simp at h00
  have : (ζ : F) = 1 := by
    have h6' : (ζ : F) ^ 6 = (ζ : F) := by rw [pow_succ, hz5, one_mul]
    rw [← h6']; exact h00
  exact hζ1 (Units.ext this)

theorem listedGroupFacts : ListedGroupFacts where
  l2_ne_perm3 _ hf _ _ h := fun ⟨e⟩ => not_isL2Quot_of_perm3 hf h e
  l2_one_solvable _ _ h := isSolvable_of_isL2Quot_one h
  dihedral5_solvable _ _ := fun ⟨e⟩ => isSolvable_of_equiv_dihedral_five e
  sz0_solvable _ _ := fun ⟨e⟩ => isSolvable_of_equiv_sz_zero e
  perm4_solvable _ _ := fun ⟨e⟩ => isSolvable_of_equiv_perm_four e
  z2perm4_solvable _ _ := fun ⟨e⟩ => isSolvable_of_equiv_z2_perm_four e
  sz_ne_perm3 a _ _ := fun ⟨e⟩ => not_equiv_sz_perm3 a e
  su3_ne_perm3 _ _ _ _ _ hF := fun ⟨e⟩ => not_equiv_statedSU_perm3 hF e
  dihedral5_ne_perm3 _ _ := fun ⟨e⟩ => not_equiv_dihedral5_perm3 e
  perm5_not_solvable _ _ := fun ⟨e⟩ => not_isSolvable_perm5 e

end CFSG.Quasithin
