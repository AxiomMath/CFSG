module

public import CFSG.RankThree.PartOne.SEITZ7.D4AB
public import CFSG.RankThree.PartOne.CTP.SeitzMaxSL2

public section

namespace CFSG.RankThree.PartOne.SEITZ8

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Steinberg.TwistedD4
  CFSG.RankThree.PartOne.SEITZ7 CFSG.RankThree.PartOne.CTP
open scoped commutatorElement Matrix

section Matrices

variable {L : Type} [Field L]

local notation "SL2" => Matrix.SpecialLinearGroup (Fin 2) L

theorem sl2_top_of_upper_lower {S : Subgroup SL2} (hu : ∀ c, u2 c ∈ S) (hl : ∀ c, l2 c ∈ S) :
    S = ⊤ := by
  rw [eq_top_iff, ← CFSG.LocalAnalysis.ComponentInitial.sl2_closure_upper_lower (K := L),
    Subgroup.closure_le]
  rintro g (⟨c, rfl⟩ | ⟨c, rfl⟩)
  · have : CFSG.LocalAnalysis.ComponentInitial.sl2Upper L c = u2 c :=
      Subtype.ext (by rw [u2_coe]; rfl)
    rw [SetLike.mem_coe, this]
    exact hu c
  · have : CFSG.LocalAnalysis.ComponentInitial.sl2Lower L c = l2 c :=
      Subtype.ext (by rw [l2_coe]; rfl)
    rw [SetLike.mem_coe, this]
    exact hl c

theorem u2_mulVec (c : L) (v : Fin 2 → L) :
    ((u2 c : SL2) : Matrix (Fin 2) (Fin 2) L) *ᵥ v = ![v 0 + c * v 1, v 1] := by
  rw [u2_coe]
  ext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem l2_mulVec (c : L) (v : Fin 2 → L) :
    ((l2 c : SL2) : Matrix (Fin 2) (Fin 2) L) *ᵥ v = ![v 0, c * v 0 + v 1] := by
  rw [l2_coe]
  ext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

@[expose] def dgm (s : L) (hs : s ≠ 0) : SL2 :=
  ⟨!![s, 0; 0, s⁻¹], by simp [Matrix.det_fin_two, hs]⟩

theorem dgm_mulVec (s : L) (hs : s ≠ 0) (v : Fin 2 → L) :
    ((dgm s hs : SL2) : Matrix (Fin 2) (Fin 2) L) *ᵥ v = ![s * v 0, s⁻¹ * v 1] := by
  ext i
  fin_cases i <;> simp [dgm, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem dgm_mul_u2_mul_dgm_inv (s : L) (hs : s ≠ 0) (a : L) :
    dgm s hs * u2 a * (dgm s hs)⁻¹ = u2 (s ^ 2 * a) := by
  ext i j
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_inv, u2_coe, u2_coe]
  fin_cases i <;> fin_cases j <;>
    simp [dgm, Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp

end Matrices

theorem conj_inv_eq {G : Type*} [Group G] {g x y : G} (h : g * x * g⁻¹ = y) :
    g⁻¹ * y * g = x := by
  rw [← h]
  group

theorem conj_mul_eq {G : Type*} [Group G] (g a b : G) :
    g * (a * b) * g⁻¹ = (g * a * g⁻¹) * (g * b * g⁻¹) := by
  group

variable {K : Type} [Field K] [CharP K 2]

section Weyl

omit [CharP K 2] [Field K] in
theorem reflect_two_check :
    reflect d4 (nd 2) (d4Root 0) = d4Root 5 ∧ reflect d4 (nd 2) (d4Root 1) = d4Root 7 ∧
    reflect d4 (nd 2) (d4Root 3) = d4Root 9 ∧ reflect d4 (nd 2) (d4Root 5) = d4Root 0 ∧
    reflect d4 (nd 2) (d4Root 7) = d4Root 1 ∧ reflect d4 (nd 2) (d4Root 9) = d4Root 3 ∧
    reflect d4 (nd 2) (d4Root 12) = d4Root 12 ∧ reflect d4 (nd 2) (d4Root 15) = d4Root 15 ∧
    reflect d4 (nd 2) (d4Root 13) = d4Root 13 ∧ reflect d4 (nd 2) (d4Root 19) = d4Root 22 ∧
    reflect d4 (nd 2) (d4Root 22) = d4Root 19 ∧ reflect d4 (nd 2) (d4Root 2) = d4Root 8 := by
  decide +kernel

variable (K) in
noncomputable abbrev nB : adjointGroup d4 K := weylElement d4 K (nd 2)

theorem nB_xd {p q : ℕ} (hp : p < 24) (h : reflect d4 (nd 2) (d4Root p) = d4Root q) (c : K) :
    nB K * xd p c * (nB K)⁻¹ = xd q c :=
  weylElement_conj_xd (nd 2) hp h c

variable (σ : K →+* K)

theorem nB_xB (c : K) : nB K * xB c * (nB K)⁻¹ = xd 8 c :=
  nB_xd (by norm_num) reflect_two_check.2.2.2.2.2.2.2.2.2.2.2 c

theorem nB_xA (c : K) : nB K * xA σ c * (nB K)⁻¹ = xAB σ c := by
  obtain ⟨h0, h1, h3, -⟩ := reflect_two_check
  unfold xA xAB
  rw [conj_mul_eq, conj_mul_eq, nB_xd (by norm_num) h0, nB_xd (by norm_num) h1,
    nB_xd (by norm_num) h3]

theorem nB_xAB (c : K) : nB K * xAB σ c * (nB K)⁻¹ = xA σ c := by
  obtain ⟨-, -, -, h5, h7, h9, -⟩ := reflect_two_check
  unfold xA xAB
  rw [conj_mul_eq, conj_mul_eq, nB_xd (by norm_num) h5, nB_xd (by norm_num) h7,
    nB_xd (by norm_num) h9]

theorem nB_xAAB (c : K) : nB K * xAAB σ c * (nB K)⁻¹ = xAAB σ c := by
  obtain ⟨-, -, -, -, -, -, h12, h15, h13, -⟩ := reflect_two_check
  unfold xAAB
  rw [conj_mul_eq, conj_mul_eq, nB_xd (by norm_num) h12, nB_xd (by norm_num) h15,
    nB_xd (by norm_num) h13]

theorem nB_xN (c : K) : nB K * xN c * (nB K)⁻¹ = xH c := by
  obtain ⟨-, -, -, -, -, -, -, -, -, h19, -⟩ := reflect_two_check
  exact nB_xd (by norm_num) h19 c

theorem nB_xH (c : K) : nB K * xH c * (nB K)⁻¹ = xN c := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, h22, -⟩ := reflect_two_check
  exact nB_xd (by norm_num) h22 c

end Weyl

section Levi

variable {σ : K →+* K}

local notation "SL2F" => Matrix.SpecialLinearGroup (Fin 2) (fixedField σ)

theorem sl2Upper_eq_u2' {k : Type} [Field k] (c : k) : sl2Upper c = u2 c :=
  Subtype.ext (by rw [u2_coe]; rfl)

theorem sl2Lower_eq_l2' {k : Type} [Field k] (c : k) : sl2Lower c = l2 c :=
  Subtype.ext (by rw [l2_coe]; rfl)

variable (σ) in
@[expose] noncomputable def rhoB : SL2F →* adjointGroup d4 K := slLongE σ

omit [CharP K 2] in
theorem rhoB_u2 (c : fixedField σ) : rhoB σ (u2 c) = xB (c : K) := by
  rw [rhoB, ← sl2Upper_eq_u2', slLongE_upper]
  simp only [xB, xd, d4Root_dict.1]

omit [CharP K 2] in
theorem rhoB_l2 (c : fixedField σ) : rhoB σ (l2 c) = xd 8 (c : K) := by
  rw [rhoB, ← sl2Lower_eq_l2', slLongE_lower]
  simp only [xd, d4Root_dict.2.1]

@[expose] noncomputable def dv (a b : fixedField σ) : adjointGroup d4 K :=
  xH (a : K) * xN (b : K)

@[expose] noncomputable def dvv (v : Fin 2 → fixedField σ) : adjointGroup d4 K :=
  dv (v 0) (v 1)

theorem dv_mul (a b a' b' : fixedField σ) : dv a b * dv a' b' = dv (a + a') (b + b') := by
  unfold dv xH xN
  push_cast
  d4coll

theorem commute_xH_xN (a b : K) : Commute (xH a) (xN b) := commute_22_19 a b

theorem dv_eq_ordT (a b : fixedField σ) : dv a b = ordT σ (mkT 0 0 0 0 (b : K) (a : K)) := by
  rw [ordT_mkT]
  simp only [xB, xA, xAB, xAAB, map_zero, xd_zero, one_mul, mul_one]
  exact (commute_xH_xN _ _).eq

theorem dv_inj {a b a' b' : fixedField σ} (h : dv a b = dv a' b') : a = a' ∧ b = b' := by
  rw [dv_eq_ordT, dv_eq_ordT] at h
  obtain ⟨-, -, -, -, h3, h7⟩ := ordT_inj σ h
  simp only [mkT] at h3 h7
  exact ⟨Subtype.ext (by simpa using h7), Subtype.ext (by simpa using h3)⟩

theorem dvv_injective : Function.Injective (dvv : (Fin 2 → fixedField σ) → adjointGroup d4 K) := by
  intro v w h
  obtain ⟨h0, h1⟩ := dv_inj h
  funext i
  fin_cases i
  · exact h0
  · exact h1

omit [CharP K 2] in
theorem dv_zero : dv (0 : fixedField σ) 0 = 1 := by simp [dv, xH, xN, xd_zero]

theorem nB_dv (a b : fixedField σ) : nB K * dv a b * (nB K)⁻¹ = dv b a := by
  unfold dv
  rw [conj_mul_eq, nB_xH, nB_xN]
  exact (commute_xH_xN _ _).symm.eq

theorem nB_inv_dv (a b : fixedField σ) : (nB K)⁻¹ * dv a b * nB K = dv b a :=
  conj_inv_eq (nB_dv b a)

theorem xB_conj_dv (c a b : fixedField σ) :
    xB (c : K) * dv a b * (xB (c : K))⁻¹ = dv (a + c * b) b := by
  unfold dv xB xH xN
  rw [xd_inv]
  push_cast
  d4coll
  rw [add_comm]

theorem x8_conj_dv (c a b : fixedField σ) :
    xd 8 (c : K) * dv a b * (xd 8 (c : K))⁻¹ = dv a (b + c * a) := by
  have e : xd 8 (c : K) * dv a b * (xd 8 (c : K))⁻¹ =
      nB K * (xB (c : K) * ((nB K)⁻¹ * dv a b * nB K) * (xB (c : K))⁻¹) * (nB K)⁻¹ := by
    rw [← nB_xB (c : K)]
    group
  rw [e, nB_inv_dv, xB_conj_dv, nB_dv]

@[expose] def ActsAs (g : adjointGroup d4 K) (A : SL2F) : Prop :=
  ∀ v : Fin 2 → fixedField σ,
    g * dvv v * g⁻¹ = dvv ((A : Matrix (Fin 2) (Fin 2) (fixedField σ)) *ᵥ v)

omit [CharP K 2] in
theorem ActsAs.one : ActsAs (1 : adjointGroup d4 K) (1 : SL2F) := fun v => by simp

omit [CharP K 2] in
theorem ActsAs.mul {g g' : adjointGroup d4 K} {A B : SL2F} (hg : ActsAs g A)
    (hg' : ActsAs g' B) : ActsAs (g * g') (A * B) := fun v => by
  rw [show g * g' * dvv v * (g * g')⁻¹ = g * (g' * dvv v * g'⁻¹) * g⁻¹ by group, hg' v, hg,
    Matrix.SpecialLinearGroup.coe_mul, Matrix.mulVec_mulVec]

omit [CharP K 2] in
theorem ActsAs.inv {g : adjointGroup d4 K} {A : SL2F} (hg : ActsAs g A) :
    ActsAs g⁻¹ A⁻¹ := fun v => by
  have h := hg (((A⁻¹ : SL2F) : Matrix (Fin 2) (Fin 2) (fixedField σ)) *ᵥ v)
  rw [Matrix.mulVec_mulVec, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
    Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec] at h
  rw [inv_inv, ← h]
  group

theorem ActsAs.unique {g : adjointGroup d4 K} {A B : SL2F} (hA : ActsAs g A)
    (hB : ActsAs g B) : A = B := by
  have h : ∀ v, ((A : Matrix (Fin 2) (Fin 2) (fixedField σ))) *ᵥ v =
      ((B : Matrix (Fin 2) (Fin 2) (fixedField σ))) *ᵥ v :=
    fun v => dvv_injective ((hA v).symm.trans (hB v))
  exact Subtype.ext (Matrix.ext_of_mulVec_single fun i => h _)

theorem actsAs_xB (c : fixedField σ) : ActsAs (xB (c : K)) (u2 c) := fun v => by
  rw [u2_mulVec, dvv, dvv, xB_conj_dv]
  simp

theorem actsAs_x8 (c : fixedField σ) : ActsAs (xd 8 (c : K)) (l2 c) := fun v => by
  rw [l2_mulVec, dvv, dvv, x8_conj_dv]
  simp [add_comm]

theorem actsAs_rhoB (A : SL2F) : ActsAs (rhoB σ A) A := by
  let S : Subgroup SL2F :=
    { carrier := {A | ActsAs (rhoB σ A) A}
      mul_mem' := fun {A B} (hA : ActsAs (rhoB σ A) A) (hB : ActsAs (rhoB σ B) B) => by
        show ActsAs (rhoB σ (A * B)) (A * B)
        rw [map_mul]
        exact ActsAs.mul hA hB
      one_mem' := by
        show ActsAs (rhoB σ 1) 1
        rw [map_one]
        exact ActsAs.one
      inv_mem' := fun {A} (hA : ActsAs (rhoB σ A) A) => by
        show ActsAs (rhoB σ A⁻¹) A⁻¹
        rw [map_inv]
        exact ActsAs.inv hA }
  have hS : S = ⊤ := sl2_top_of_upper_lower
    (fun c => by
      show ActsAs (rhoB σ (u2 c)) (u2 c)
      rw [rhoB_u2]
      exact actsAs_xB c)
    (fun c => by
      show ActsAs (rhoB σ (l2 c)) (l2 c)
      rw [rhoB_l2]
      exact actsAs_x8 c)
  have : A ∈ S := hS ▸ Subgroup.mem_top A
  exact this

end Levi

end CFSG.RankThree.PartOne.SEITZ8
