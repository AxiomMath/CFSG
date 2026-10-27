module

public import CFSG.RankThree.PartOne.SEITZ6.G2MU
public import CFSG.RankThree.PartOne.SEITZ6.G2Pair
public import CFSG.LocalAnalysis.ComponentInitial.CentralSL2Semilinear
public import CFSG.ClassicalInvolution.WeakCT.StandardPair
public import CFSG.LieType.CurtisTits.SpecialLinear
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHigherLinearFieldDeterminant
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
public import CFSG.LocalAnalysis.SectionRank.Ccomm.Supercritical
public import CFSG.RankThree.PartOne.CTP.SeitzLinear
public import CFSG.RankThree.PartOne.KC.LinearCommutatorOdd
public import CFSG.RankThree.PartOne.KC.LinearDegreeFive
public import CFSG.RankThree.PartOne.KC.LinearEndpointStatements
public import CFSG.RankThree.PartOne.KC.PlaneReductionGeneral
public import CFSG.RankThree.PartOne.S11d.OutLinear
public import CFSG.RankThree.Theta.ThreeComponentOrbitCover
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
public import CFSG.Walter.Defs
public import Certificates.Certificate1
public import Certificates.Certificate2

public section

namespace CFSG.RankThree.PartOne.SEITZ2

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.RankThree.PartOne.SEITZ3 CFSG.RankThree.PartOne.SEITZ6
  CFSG.RankThree.PartOne.CTP
open scoped commutatorElement Matrix

variable {K : Type} [Field K]

local notation "SL2" => Matrix.SpecialLinearGroup (Fin 2) K

section Matrices

theorem sl2_top_of_upper_lower {S : Subgroup SL2} (hu : ∀ c, u2 c ∈ S) (hl : ∀ c, l2 c ∈ S) :
    S = ⊤ := by
  rw [eq_top_iff, ← CFSG.LocalAnalysis.ComponentInitial.sl2_closure_upper_lower (K := K),
    Subgroup.closure_le]
  rintro g (⟨c, rfl⟩ | ⟨c, rfl⟩)
  · have : CFSG.LocalAnalysis.ComponentInitial.sl2Upper K c = u2 c :=
      Subtype.ext (by rw [u2_coe]; rfl)
    rw [SetLike.mem_coe, this]
    exact hu c
  · have : CFSG.LocalAnalysis.ComponentInitial.sl2Lower K c = l2 c :=
      Subtype.ext (by rw [l2_coe]; rfl)
    rw [SetLike.mem_coe, this]
    exact hl c

theorem u2_mulVec (c : K) (v : Fin 2 → K) :
    ((u2 c : SL2) : Matrix (Fin 2) (Fin 2) K) *ᵥ v = ![v 0 + c * v 1, v 1] := by
  rw [u2_coe]
  ext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem l2_mulVec (c : K) (v : Fin 2 → K) :
    ((l2 c : SL2) : Matrix (Fin 2) (Fin 2) K) *ᵥ v = ![v 0, c * v 0 + v 1] := by
  rw [l2_coe]
  ext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

@[expose] def dg (s : K) (hs : s ≠ 0) : SL2 :=
  ⟨!![s, 0; 0, s⁻¹], by simp [Matrix.det_fin_two, hs]⟩

theorem dg_mulVec (s : K) (hs : s ≠ 0) (v : Fin 2 → K) :
    ((dg s hs : SL2) : Matrix (Fin 2) (Fin 2) K) *ᵥ v = ![s * v 0, s⁻¹ * v 1] := by
  ext i
  fin_cases i <;> simp [dg, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem dg_mul_u2_mul_dg_inv (s : K) (hs : s ≠ 0) (a : K) :
    dg s hs * u2 a * (dg s hs)⁻¹ = u2 (s ^ 2 * a) := by
  ext i j
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_inv, u2_coe, u2_coe]
  fin_cases i <;> fin_cases j <;>
    simp [dg, Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp

theorem conj_inv_eq {G : Type*} [Group G] {g x y : G} (h : g * x * g⁻¹ = y) :
    g⁻¹ * y * g = x := by
  rw [← h]
  group

theorem conj_mul_eq {G : Type*} [Group G] (g a b : G) :
    g * (a * b) * g⁻¹ = (g * a * g⁻¹) * (g * b * g⁻¹) := by
  group

theorem reflect_e0_4 : reflect .G2 e0 (rt 4) = rt 1 := by decide +kernel

theorem reflect_e0_8 : reflect .G2 e0 (rt 8) = rt 8 := by decide +kernel

end Matrices

section Levi

theorem exists_rhoB : ∃ φ : SL2 →* adjointGroup .G2 K, Function.Injective φ ∧
    (∀ c, φ (u2 c) = xp 0 c) ∧ (∀ c, φ (l2 c) = xp 2 c) := by
  obtain ⟨φ, hinj, hu, hl⟩ := g2_exists_sl2_hom (K := K) e0
  refine ⟨φ, hinj, fun c => ?_, fun c => ?_⟩
  · rw [← sl2Upper_eq_u2, hu, xp, rt0_eq, xPar_simple]
  · rw [← sl2Lower_eq_l2, hl, xp, rt2_eq, xPar_neg_simple]

variable (K) in
@[expose] noncomputable def rhoB : SL2 →* adjointGroup .G2 K :=
  Classical.choose (exists_rhoB (K := K))

theorem rhoB_u2 (c : K) : rhoB K (u2 c) = xp 0 c :=
  (Classical.choose_spec (exists_rhoB (K := K))).2.1 c

theorem rhoB_l2 (c : K) : rhoB K (l2 c) = xp 2 c :=
  (Classical.choose_spec (exists_rhoB (K := K))).2.2 c

variable (K) in
noncomputable abbrev nB : adjointGroup .G2 K := weylElement .G2 K e0

variable [CharP K 2]

theorem nB_x0 (c : K) : nB K * xp 0 c * (nB K)⁻¹ = xp 2 c :=
  weylElement_conj_xp e0 (by norm_num) reflect_0 c

theorem nB_x1 (c : K) : nB K * xp 1 c * (nB K)⁻¹ = xp 4 c :=
  weylElement_conj_xp e0 (by norm_num) reflect_1 c

theorem nB_x4 (c : K) : nB K * xp 4 c * (nB K)⁻¹ = xp 1 c :=
  weylElement_conj_xp e0 (by norm_num) reflect_e0_4 c

theorem nB_x8 (c : K) : nB K * xp 8 c * (nB K)⁻¹ = xp 8 c :=
  weylElement_conj_xp e0 (by norm_num) reflect_e0_8 c

theorem nB_x3 (c : K) : nB K * xp 3 c * (nB K)⁻¹ = xp 7 c :=
  weylElement_conj_xp e0 (by norm_num) reflect_3' c

theorem nB_x7 (c : K) : nB K * xp 7 c * (nB K)⁻¹ = xp 3 c :=
  weylElement_conj_xp e0 (by norm_num) reflect_7 c

@[expose] noncomputable def dv (a b : K) : adjointGroup .G2 K := xp 7 a * xp 3 b

@[expose] noncomputable def dvv (v : Fin 2 → K) : adjointGroup .G2 K := dv (v 0) (v 1)

theorem dv_inj {a b a' b' : K} (h : dv a b = dv a' b') : a = a' ∧ b = b' := by
  unfold dv at h
  have e : ∀ x y : K, xp 7 x * xp 3 y =
      xp 0 0 * xp 1 0 * xp 4 0 * xp 8 0 * xp 3 y * xp 7 x := fun x y => by
    simp only [xp_zero, one_mul]
    exact (commute_37 y x).eq.symm
  rw [e, e] at h
  obtain ⟨-, -, -, -, h3, h7⟩ := six_inj h
  exact ⟨h7, h3⟩

theorem dvv_injective : Function.Injective (dvv : (Fin 2 → K) → adjointGroup .G2 K) := by
  intro v w h
  obtain ⟨h0, h1⟩ := dv_inj h
  ext i
  fin_cases i
  · exact h0
  · exact h1

theorem nB_dv (a b : K) : nB K * dv a b * (nB K)⁻¹ = dv b a := by
  unfold dv
  rw [conj_mul_eq, nB_x7, nB_x3]
  exact (commute_37 a b).eq

theorem nB_inv_dv (a b : K) : (nB K)⁻¹ * dv a b * nB K = dv b a :=
  conj_inv_eq (nB_dv b a)

theorem x0_conj_dv (c a b : K) : xp 0 c * dv a b * (xp 0 c)⁻¹ = dv (a + c * b) b := by
  unfold dv
  rw [xp_inv]
  g2coll
  rw [add_comm]

theorem x2_conj_dv (c a b : K) : xp 2 c * dv a b * (xp 2 c)⁻¹ = dv a (b + c * a) := by
  have e : xp 2 c * dv a b * (xp 2 c)⁻¹ =
      nB K * (xp 0 c * ((nB K)⁻¹ * dv a b * nB K) * (xp 0 c)⁻¹) * (nB K)⁻¹ := by
    rw [← nB_x0 c]
    group
  rw [e, nB_inv_dv, x0_conj_dv, nB_dv]

@[expose] def ActsAs (g : adjointGroup .G2 K) (A : SL2) : Prop :=
  ∀ v : Fin 2 → K, g * dvv v * g⁻¹ = dvv ((A : Matrix (Fin 2) (Fin 2) K) *ᵥ v)

omit [CharP K 2] in
theorem ActsAs.one : ActsAs (1 : adjointGroup .G2 K) 1 := fun v => by simp

omit [CharP K 2] in
theorem ActsAs.mul {g g' : adjointGroup .G2 K} {A B : SL2} (hg : ActsAs g A)
    (hg' : ActsAs g' B) : ActsAs (g * g') (A * B) := fun v => by
  rw [show g * g' * dvv v * (g * g')⁻¹ = g * (g' * dvv v * g'⁻¹) * g⁻¹ by group, hg' v, hg,
    Matrix.SpecialLinearGroup.coe_mul, Matrix.mulVec_mulVec]

omit [CharP K 2] in
theorem ActsAs.inv {g : adjointGroup .G2 K} {A : SL2} (hg : ActsAs g A) :
    ActsAs g⁻¹ A⁻¹ := fun v => by
  have h := hg (((A⁻¹ : SL2) : Matrix (Fin 2) (Fin 2) K) *ᵥ v)
  rw [Matrix.mulVec_mulVec, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
    Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec] at h
  rw [inv_inv, ← h]
  group

theorem ActsAs.unique {g : adjointGroup .G2 K} {A B : SL2} (hA : ActsAs g A)
    (hB : ActsAs g B) : A = B := by
  have h : ∀ v, ((A : Matrix (Fin 2) (Fin 2) K)) *ᵥ v = ((B : Matrix (Fin 2) (Fin 2) K)) *ᵥ v :=
    fun v => dvv_injective ((hA v).symm.trans (hB v))
  exact Subtype.ext (Matrix.ext_of_mulVec_single fun i => h _)

theorem actsAs_x0 (c : K) : ActsAs (xp 0 c) (u2 c) := fun v => by
  rw [u2_mulVec, dvv, dvv, x0_conj_dv]
  simp

theorem actsAs_x2 (c : K) : ActsAs (xp 2 c) (l2 c) := fun v => by
  rw [l2_mulVec, dvv, dvv, x2_conj_dv]
  simp [add_comm]

theorem actsAs_rhoB (A : SL2) : ActsAs (rhoB K A) A := by
  let S : Subgroup SL2 :=
    { carrier := {A | ActsAs (rhoB K A) A}
      mul_mem' := fun {A B} (hA : ActsAs (rhoB K A) A) (hB : ActsAs (rhoB K B) B) => by
        show ActsAs (rhoB K (A * B)) (A * B)
        rw [map_mul]
        exact ActsAs.mul hA hB
      one_mem' := by
        show ActsAs (rhoB K 1) 1
        rw [map_one]
        exact ActsAs.one
      inv_mem' := fun {A} (hA : ActsAs (rhoB K A) A) => by
        show ActsAs (rhoB K A⁻¹) A⁻¹
        rw [map_inv]
        exact ActsAs.inv hA }
  have hS : S = ⊤ := sl2_top_of_upper_lower
    (fun c => by
      show ActsAs (rhoB K (u2 c)) (u2 c)
      rw [rhoB_u2]
      exact actsAs_x0 c)
    (fun c => by
      show ActsAs (rhoB K (l2 c)) (l2 c)
      rw [rhoB_l2]
      exact actsAs_x2 c)
  have : A ∈ S := hS ▸ Subgroup.mem_top A
  exact this

end Levi

end CFSG.RankThree.PartOne.SEITZ2
