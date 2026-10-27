module

public import CFSG.OddTranspositions.PartFour.SpPlaneSL2
public import CFSG.LocalAnalysis.WeakClosure81.SevenKUnitary
import CFSG.OddTranspositions.PartFour.UnitaryClass
import CFSG.GroupTheory.SteinbergBKLinearPlaneSL2
import CFSG.LocalAnalysis.StandardType.GGRankOneSl2
import CFSG.LocalAnalysis.OddStandard.Seitz77Nat16Inv
import CFSG.LocalAnalysis.SeitzReduction.F4PilotNonsplitSL2
public import CFSG.LocalAnalysis.WeakClosure81.W16Gt2KFactsH
public import CFSG.RankThree.PartOne.SEITZ2.SUnPlane
import CFSG.CGT.Timmesfeld75.L2Real

public section

namespace CFSG.OddTranspositions.PartFour

open CFSG.Timmesfeld CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72
open CFSG.Timmesfeld.Connectivity CFSG.LocalAnalysis.WeakClosure81.SevenK
open CFSG.Open CFSG.ClassicalGroups.Unitary CFSG.LieType.BorelTits
open CFSG.LieType.Universal.Unitary
open CFSG.LocalAnalysis.WeakClosure81 CFSG.RankThree.PartOne.SEITZ2
open CFSG.RankThree.PartOne.CTP (u2 l2 u2_coe l2_coe)
open scoped Matrix

variable {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}


private theorem unitaryPlane_add_smul_add_smul {d : ℕ} {a b : Fin d → F} (α β γ δ ε : F) :
    α • a + β • b + γ • (δ • a + ε • b) = (α + γ * δ) • a + (β + γ * ε) • b := by
  module

private theorem unitaryPlane_herm_b_plane {d : ℕ} {a b : Fin d → F}
    (hF : Nat.card F = (2 ^ f) ^ 2) (ha : herm (unitaryInvolution F 2 f) a a = 0) (hb : herm
      (unitaryInvolution F 2 f) b b = 0)
    (hab : herm (unitaryInvolution F 2 f) a b = 1) (p r : F) : herm (unitaryInvolution F 2 f) b (p
      • a + r • b) = p := by
  have hba : herm (unitaryInvolution F 2 f) b a = 1 := by rw [herm_conj (unitaryInvolution F 2 f)
    (unitaryInvolution_involutive hF), hab, map_one]
  simp only [herm_add_right, herm_smul_right, hba, hb, mul_one, mul_zero, add_zero]

private theorem unitaryPlane_herm_a_plane {d : ℕ} {a b : Fin d → F}
    (ha : herm (unitaryInvolution F 2 f) a a = 0) (hb : herm (unitaryInvolution F 2 f) b b = 0)
      (hab : herm (unitaryInvolution F 2 f) a b = 1) (p r : F) :
    herm (unitaryInvolution F 2 f) a (p • a + r • b) = r := by
  simp only [herm_add_right, herm_smul_right, ha, hab, mul_one, mul_zero, zero_add, add_zero]

private theorem unitaryPlane_smul_add_smul_inj {d : ℕ} {a b : Fin d → F}
    (hF : Nat.card F = (2 ^ f) ^ 2) (ha : herm (unitaryInvolution F 2 f) a a = 0) (hb : herm
      (unitaryInvolution F 2 f) b b = 0)
    (hab : herm (unitaryInvolution F 2 f) a b = 1) {α β α' β' : F} (h : α • a + β • b = α' • a +
      β' • b) :
    α = α' ∧ β = β' := by
  have h1 := congrArg (herm (unitaryInvolution F 2 f) b) h
  have h2 := congrArg (herm (unitaryInvolution F 2 f) a) h
  rw [unitaryPlane_herm_b_plane hF ha hb hab, unitaryPlane_herm_b_plane hF ha hb hab] at h1
  rw [unitaryPlane_herm_a_plane ha hb hab, unitaryPlane_herm_a_plane ha hb hab] at h2
  exact ⟨h1, h2⟩

private theorem unitaryPlane_herm_plane_self {d : ℕ} {a b : Fin d → F}
    (hF : Nat.card F = (2 ^ f) ^ 2) (ha : herm (unitaryInvolution F 2 f) a a = 0) (hb : herm
      (unitaryInvolution F 2 f) b b = 0)
    (hab : herm (unitaryInvolution F 2 f) a b = 1) (p r : fixSub (unitaryInvolution F 2 f)) :
    herm (unitaryInvolution F 2 f) ((p : F) • a + (r : F) • b) ((p : F) • a + (r : F) • b) = 0 := by
  have hba : herm (unitaryInvolution F 2 f) b a = 1 := by rw [herm_conj (unitaryInvolution F 2 f)
    (unitaryInvolution_involutive hF), hab, map_one]
  have hp : (unitaryInvolution F 2 f) (p : F) = (p : F) := mem_fixSub.1 p.2
  have hr : (unitaryInvolution F 2 f) (r : F) = (r : F) := mem_fixSub.1 r.2
  simp only [herm_add_left, herm_add_right, herm_smul_left, herm_smul_right, ha, hb, hab, hba,
    hp, hr]
  linear_combination ((p : F) * (r : F)) * (CharTwo.two_eq_zero : (2 : F) = 0)

private theorem unitaryPlane_planeSUN_plane {d : ℕ} {a b : Fin d → F}
    (hF : Nat.card F = (2 ^ f) ^ 2) (ha : herm (unitaryInvolution F 2 f) a a = 0) (hb : herm
      (unitaryInvolution F 2 f) b b = 0)
    (hab : herm (unitaryInvolution F 2 f) a b = 1) (g : Matrix.SpecialLinearGroup (Fin 2) (fixSub
      (unitaryInvolution F 2 f))) (x y : F) :
    planeSUN (unitaryInvolution_involutive hF) ha hb hab g • (x • a + y • b) =
      (ent g 0 0 * x + ent g 0 1 * y) • a + (ent g 1 0 * x + ent g 1 1 * y) • b := by
  show planeEltN (unitaryInvolution_involutive hF) ha hb hab g • (x • a + y • b) = _
  rw [planeEltN_smul, unitaryPlane_herm_b_plane hF ha hb hab,
    unitaryPlane_herm_a_plane ha hb hab]
  rw [unitaryPlane_add_smul_add_smul, unitaryPlane_add_smul_add_smul]
  have e1 : x + x * (ent g 0 0 - 1) + y * ent g 0 1 = ent g 0 0 * x + ent g 0 1 * y := by ring
  have e2 : y + x * ent g 1 0 + y * (ent g 1 1 - 1) = ent g 1 0 * x + ent g 1 1 * y := by ring
  rw [e1, e2]

private theorem unitaryPlane_planeSUN_a {d : ℕ} {a b : Fin d → F}
    (hF : Nat.card F = (2 ^ f) ^ 2) (ha : herm (unitaryInvolution F 2 f) a a = 0) (hb : herm
      (unitaryInvolution F 2 f) b b = 0)
    (hab : herm (unitaryInvolution F 2 f) a b = 1) (g : Matrix.SpecialLinearGroup (Fin 2) (fixSub
      (unitaryInvolution F 2 f))) :
    planeSUN (unitaryInvolution_involutive hF) ha hb hab g • a =
      ent g 0 0 • a + ent g 1 0 • b := by
  simpa using unitaryPlane_planeSUN_plane hF ha hb hab g 1 0

private theorem unitaryPlane_planeSUN_b {d : ℕ} {a b : Fin d → F}
    (hF : Nat.card F = (2 ^ f) ^ 2) (ha : herm (unitaryInvolution F 2 f) a a = 0) (hb : herm
      (unitaryInvolution F 2 f) b b = 0)
    (hab : herm (unitaryInvolution F 2 f) a b = 1) (g : Matrix.SpecialLinearGroup (Fin 2) (fixSub
      (unitaryInvolution F 2 f))) :
    planeSUN (unitaryInvolution_involutive hF) ha hb hab g • b =
      ent g 0 1 • a + ent g 1 1 • b := by
  simpa using unitaryPlane_planeSUN_plane hF ha hb hab g 0 1

private theorem unitaryPlane_planeSUN_injective {d : ℕ} {a b : Fin d → F}
    (hF : Nat.card F = (2 ^ f) ^ 2) (ha : herm (unitaryInvolution F 2 f) a a = 0) (hb : herm
      (unitaryInvolution F 2 f) b b = 0)
    (hab : herm (unitaryInvolution F 2 f) a b = 1) :
    Function.Injective (planeSUN (unitaryInvolution_involutive hF) ha hb hab) := by
  intro g g' hgg
  have h1 : planeSUN (unitaryInvolution_involutive hF) ha hb hab g • a =
      planeSUN (unitaryInvolution_involutive hF) ha hb hab g' • a := by rw [hgg]
  have h2 : planeSUN (unitaryInvolution_involutive hF) ha hb hab g • b =
      planeSUN (unitaryInvolution_involutive hF) ha hb hab g' • b := by rw [hgg]
  rw [unitaryPlane_planeSUN_a hF ha hb hab g, unitaryPlane_planeSUN_a hF ha hb hab g'] at h1
  rw [unitaryPlane_planeSUN_b hF ha hb hab g, unitaryPlane_planeSUN_b hF ha hb hab g'] at h2
  have h1' : ent g 0 0 = ent g' 0 0 ∧ ent g 1 0 = ent g' 1 0 :=
    unitaryPlane_smul_add_smul_inj hF ha hb hab h1
  have h2' : ent g 0 1 = ent g' 0 1 ∧ ent g 1 1 = ent g' 1 1 :=
    unitaryPlane_smul_add_smul_inj hF ha hb hab h2
  obtain ⟨e00, e10⟩ := h1'
  obtain ⟨e01, e11⟩ := h2'
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j
  · simpa using Subtype.ext e00
  · simpa using Subtype.ext e01
  · simpa using Subtype.ext e10
  · simpa using Subtype.ext e11

private noncomputable abbrev unitaryPlane_Phi {d : ℕ} {a b : Fin d → F}
    (hF : Nat.card F = (2 ^ f) ^ 2) (ha : herm (unitaryInvolution F 2 f) a a = 0) (hb : herm
      (unitaryInvolution F 2 f) b b = 0)
    (hab : herm (unitaryInvolution F 2 f) a b = 1) :
    Matrix.SpecialLinearGroup (Fin 2) (fixSub (unitaryInvolution F 2 f)) →* StatedProj (StatedSU d
      (2 ^ f) F) :=
  (kFactsSuProj hF d).comp (planeSUN (unitaryInvolution_involutive hF) ha hb hab)

private noncomputable def unitaryPlane_S0 {d : ℕ} (hF : Nat.card F = (2 ^ f) ^ 2) :
    Set (StatedProj (StatedSU d (2 ^ f) F)) :=
  {y | ∃ c : Fin d → F, c ≠ 0 ∧ herm (unitaryInvolution F 2 f) c c = 0 ∧ y = kFactsSuProjTv hF d c
    1}

private theorem unitaryPlane_Phi_apply {d : ℕ} {a b : Fin d → F}
    (hF : Nat.card F = (2 ^ f) ^ 2) (ha : herm (unitaryInvolution F 2 f) a a = 0) (hb : herm
      (unitaryInvolution F 2 f) b b = 0)
    (hab : herm (unitaryInvolution F 2 f) a b = 1) (g : Matrix.SpecialLinearGroup (Fin 2) (fixSub
      (unitaryInvolution F 2 f))) :
    unitaryPlane_Phi hF ha hb hab g =
      kFactsSuProj hF d (planeSUN (unitaryInvolution_involutive hF) ha hb hab g) := rfl

private theorem unitaryPlane_Phi_injective {d : ℕ} {a b : Fin d → F}
    (hF : Nat.card F = (2 ^ f) ^ 2) (hd : 3 ≤ d) (ha : herm (unitaryInvolution F 2 f) a a = 0)
    (hb : herm (unitaryInvolution F 2 f) b b = 0) (hab : herm (unitaryInvolution F 2 f) a b = 1) :
    Function.Injective (unitaryPlane_Phi hF ha hb hab) := by
  intro A B hAB
  have h1 : unitaryPlane_Phi hF ha hb hab (A⁻¹ * B) = 1 := by
    rw [map_mul, map_inv, hAB, inv_mul_cancel]
  obtain ⟨w, hw1, hw2, hw3⟩ :=
    exists_norm_one_perp_pair (isUnitaryInvolution_unitaryInvolution hF) hd ha hb hab
  have hw0 : w ≠ 0 := by
    intro h; rw [h, herm_zero_left] at hw1; exact zero_ne_one hw1
  have hwx : planeSUN (unitaryInvolution_involutive hF) ha hb hab (A⁻¹ * B) • w = w := by
    show planeEltN (unitaryInvolution_involutive hF) ha hb hab _ • w = w
    rw [planeEltN_smul, hw3, hw2, zero_smul, zero_smul, add_zero, add_zero]
  have h2 : kFactsSuProj hF d (planeSUN (unitaryInvolution_involutive hF) ha hb hab (A⁻¹ * B)) =
      kFactsSuProj hF d 1 := by
    rw [← unitaryPlane_Phi_apply hF ha hb hab (A⁻¹ * B), h1, map_one]
  obtain ⟨u, hu⟩ := (kFacts_suProj_eq_iff hF (1 : ↥(SUid (unitaryInvolution F 2 f) d))
    (planeSUN (unitaryInvolution_involutive hF) ha hb hab (A⁻¹ * B))).mp h2.symm
  have hu' : (((planeSUN (unitaryInvolution_involutive hF) ha hb hab (A⁻¹ * B) :
        ↥(SUid (unitaryInvolution F 2 f) d)) : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) = (u : F)
          • 1 := by
    simpa using hu
  have h3 : w = (u : F) • w := by
    nth_rewrite 1 [← hwx]
    rw [smul_def, hu', Matrix.smul_mulVec, Matrix.one_mulVec]
  have hu1 : (u : F) = 1 := by
    have h4 : ((1 : F) - (u : F)) • w = 0 := by
      rw [sub_smul, one_smul]
      nth_rewrite 1 [h3]
      rw [sub_self]
    rcases smul_eq_zero.mp h4 with h5 | h5
    · exact (sub_eq_zero.mp h5).symm
    · exact absurd h5 hw0
  have h5 : planeSUN (unitaryInvolution_involutive hF) ha hb hab (A⁻¹ * B) =
      planeSUN (unitaryInvolution_involutive hF) ha hb hab 1 := by
    refine Subtype.ext (Units.ext ?_)
    rw [hu', hu1, one_smul]
    simp
  exact inv_mul_eq_one.mp (unitaryPlane_planeSUN_injective hF ha hb hab h5)

private theorem unitaryPlane_smul_add_smul {d : ℕ} {a b : Fin d → F} (γ δ ε γ' δ' ε' : F) :
    γ • (δ • a + ε • b) + γ' • (δ' • a + ε' • b) =
      (γ * δ + γ' * δ') • a + (γ * ε + γ' * ε') • b := by
  module

private noncomputable def unitaryPlane_tvMat (p r s : fixSub (unitaryInvolution F 2 f)) :
    Matrix.SpecialLinearGroup (Fin 2) (fixSub (unitaryInvolution F 2 f)) :=
  ⟨!![1 + s * p * r, s * p * p; s * r * r, 1 + s * p * r], by
    have h2 : (2 : ↥(fixSub (unitaryInvolution F 2 f))) = 0 := CharTwo.two_eq_zero
    rw [Matrix.det_fin_two]
    simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
    linear_combination (s * p * r) * h2⟩

private theorem unitaryPlane_tvMat_entries (p r s : fixSub (unitaryInvolution F 2 f)) :
    ent (unitaryPlane_tvMat p r s) 0 0 = 1 + (s : F) * (p : F) * (r : F) ∧
      ent (unitaryPlane_tvMat p r s) 0 1 = (s : F) * (p : F) * (p : F) ∧
      ent (unitaryPlane_tvMat p r s) 1 0 = (s : F) * (r : F) * (r : F) ∧
      ent (unitaryPlane_tvMat p r s) 1 1 = 1 + (s : F) * (p : F) * (r : F) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [unitaryPlane_tvMat, ent]

private theorem unitaryPlane_planeSUN_tvMat {d : ℕ} {a b : Fin d → F}
    (hF : Nat.card F = (2 ^ f) ^ 2) (ha : herm (unitaryInvolution F 2 f) a a = 0) (hb : herm
      (unitaryInvolution F 2 f) b b = 0)
    (hab : herm (unitaryInvolution F 2 f) a b = 1) (p r s : fixSub (unitaryInvolution F 2 f)) :
    planeSUN (unitaryInvolution_involutive hF) ha hb hab (unitaryPlane_tvMat p r s) =
      suTv (isUnitaryInvolution_unitaryInvolution hF)
        ((p : F) • a + (r : F) • b) (s : F) := by
  apply ext_smul
  intro v
  have hs : (s : F) + (unitaryInvolution F 2 f) (s : F) = 0 := by
    rw [mem_fixSub.1 s.2]; exact CharTwo.add_self_eq_zero _
  rw [suTv_smul (isUnitaryInvolution_unitaryInvolution hF)
    (unitaryPlane_herm_plane_self hF ha hb hab p r) hs]
  show planeEltN (unitaryInvolution_involutive hF) ha hb hab (unitaryPlane_tvMat p r s) • v =
    v + ((s : F) * herm (unitaryInvolution F 2 f) ((p : F) • a + (r : F) • b) v) • ((p : F) • a +
      (r : F) • b)
  obtain ⟨e00, e01, e10, e11⟩ := unitaryPlane_tvMat_entries p r s
  rw [planeEltN_smul, e00, e01, e10, e11, herm_add_left, herm_smul_left, herm_smul_left,
    mem_fixSub.1 p.2, mem_fixSub.1 r.2]
  have e1 : herm (unitaryInvolution F 2 f) b v * ((1 + (s : F) * (p : F) * (r : F)) - 1) +
      herm (unitaryInvolution F 2 f) a v * ((s : F) * (p : F) * (p : F)) =
      ((s : F) * ((p : F) * herm (unitaryInvolution F 2 f) a v +
        (r : F) * herm (unitaryInvolution F 2 f) b v)) * (p : F) := by ring
  have e2 : herm (unitaryInvolution F 2 f) b v * ((s : F) * (r : F) * (r : F)) +
      herm (unitaryInvolution F 2 f) a v * ((1 + (s : F) * (p : F) * (r : F)) - 1) =
      ((s : F) * ((p : F) * herm (unitaryInvolution F 2 f) a v +
        (r : F) * herm (unitaryInvolution F 2 f) b v)) * (r : F) := by ring
  have key : herm (unitaryInvolution F 2 f) b v •
        ((1 + (s : F) * (p : F) * (r : F) - 1) • a + ((s : F) * (r : F) * (r : F)) • b) +
      herm (unitaryInvolution F 2 f) a v •
        (((s : F) * (p : F) * (p : F)) • a + (1 + (s : F) * (p : F) * (r : F) - 1) • b) =
      ((s : F) * ((p : F) * herm (unitaryInvolution F 2 f) a v +
        (r : F) * herm (unitaryInvolution F 2 f) b v)) • ((p : F) • a + (r : F) • b) := by
    rw [unitaryPlane_smul_add_smul, smul_add, smul_smul, smul_smul, e1, e2]
  rw [add_assoc]
  exact congrArg (fun z => v + z) key

private theorem unitaryPlane_Phi_tvMat {d : ℕ} {a b : Fin d → F}
    (hF : Nat.card F = (2 ^ f) ^ 2) (ha : herm (unitaryInvolution F 2 f) a a = 0) (hb : herm
      (unitaryInvolution F 2 f) b b = 0)
    (hab : herm (unitaryInvolution F 2 f) a b = 1) (p r s : fixSub (unitaryInvolution F 2 f)) :
    unitaryPlane_Phi hF ha hb hab (unitaryPlane_tvMat p r s) =
      kFactsSuProjTv hF d ((p : F) • a + (r : F) • b) (s : F) := by
  rw [unitaryPlane_Phi_apply, unitaryPlane_planeSUN_tvMat hF]
  rfl

private theorem unitaryPlane_planeSUN_coord {d : ℕ} {a b : Fin d → F}
    (hF : Nat.card F = (2 ^ f) ^ 2) (ha : herm (unitaryInvolution F 2 f) a a = 0) (hb : herm
      (unitaryInvolution F 2 f) b b = 0)
    (hab : herm (unitaryInvolution F 2 f) a b = 1) (g : Matrix.SpecialLinearGroup (Fin 2) (fixSub
      (unitaryInvolution F 2 f)))
    (v w : Fin 2 → fixSub (unitaryInvolution F 2 f))
    (hvw : w = (g : Matrix (Fin 2) (Fin 2) (fixSub (unitaryInvolution F 2 f))) *ᵥ v) :
    planeSUN (unitaryInvolution_involutive hF) ha hb hab g •
        ((v 0 : F) • a + (v 1 : F) • b) = (w 0 : F) • a + (w 1 : F) • b := by
  have h := unitaryPlane_planeSUN_plane hF ha hb hab g (v 0 : F) (v 1 : F)
  rw [hvw, h]
  have e1 : ent g 0 0 * (v 0 : F) + ent g 0 1 * (v 1 : F) =
      ((((g : Matrix (Fin 2) (Fin 2) (fixSub (unitaryInvolution F 2 f))) *ᵥ v) 0 : fixSub
        (unitaryInvolution F 2 f)) : F) := by
    simp [ent, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  have e2 : ent g 1 0 * (v 0 : F) + ent g 1 1 * (v 1 : F) =
      ((((g : Matrix (Fin 2) (Fin 2) (fixSub (unitaryInvolution F 2 f))) *ᵥ v) 1 : fixSub
        (unitaryInvolution F 2 f)) : F) := by
    simp [ent, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  rw [e1, e2]

private theorem unitaryPlane_conj {d : ℕ} {a b : Fin d → F}
    (hF : Nat.card F = (2 ^ f) ^ 2) (ha : herm (unitaryInvolution F 2 f) a a = 0) (hb : herm
      (unitaryInvolution F 2 f) b b = 0)
    (hab : herm (unitaryInvolution F 2 f) a b = 1) (g : Matrix.SpecialLinearGroup (Fin 2) (fixSub
      (unitaryInvolution F 2 f)))
    (v w : Fin 2 → fixSub (unitaryInvolution F 2 f))
    (hvw : w = (g : Matrix (Fin 2) (Fin 2) (fixSub (unitaryInvolution F 2 f))) *ᵥ v)
    (s : F) (hs : (unitaryInvolution F 2 f) s = s) :
    unitaryPlane_Phi hF ha hb hab g *
        kFactsSuProjTv hF d ((v 0 : F) • a + (v 1 : F) • b) s *
        (unitaryPlane_Phi hF ha hb hab g)⁻¹ =
      kFactsSuProjTv hF d ((w 0 : F) • a + (w 1 : F) • b) s := by
  have he : herm (unitaryInvolution F 2 f) ((v 0 : F) • a + (v 1 : F) • b) ((v 0 : F) • a + (v 1 :
    F) • b) = 0 :=
    unitaryPlane_herm_plane_self hF ha hb hab (v 0) (v 1)
  have hs0 : s + (unitaryInvolution F 2 f) s = 0 := by
    rw [hs]; exact CharTwo.add_self_eq_zero _
  have h := kFacts_suProj_conj_suProjTv hF
    (planeSUN (unitaryInvolution_involutive hF) ha hb hab g) he hs0
  have h2 := unitaryPlane_planeSUN_coord hF ha hb hab g v w hvw
  rw [h2] at h
  simpa [unitaryPlane_Phi_apply] using h

private theorem unitaryPlane_transitive {d : ℕ} {a b : Fin d → F}
    (hF : Nat.card F = (2 ^ f) ^ 2) (ha : herm (unitaryInvolution F 2 f) a a = 0) (hb : herm
      (unitaryInvolution F 2 f) b b = 0)
    (hab : herm (unitaryInvolution F 2 f) a b = 1) {v w : Fin 2 → fixSub (unitaryInvolution F 2
      f)} (hv : v ≠ 0) (hw : w ≠ 0) :
    ∃ g ∈ (unitaryPlane_Phi hF ha hb hab).range,
      g * kFactsSuProjTv hF d ((v 0 : F) • a + (v 1 : F) • b) 1 * g⁻¹ =
        kFactsSuProjTv hF d ((w 0 : F) • a + (w 1 : F) • b) 1 := by
  obtain ⟨A, hA⟩ := CFSG.GroupTheory.SteinbergBK.exists_sl2_mulVec_eq
    (k := ↥(fixSub (unitaryInvolution F 2 f))) v w hv hw
  refine ⟨unitaryPlane_Phi hF ha hb hab A, ⟨A, rfl⟩, ?_⟩
  rw [unitaryPlane_conj hF ha hb hab A v w hA.symm 1 (map_one (unitaryInvolution F 2 f))]

private theorem unitaryPlane_herm_plane_plane {d : ℕ} {a b : Fin d → F}
    (hF : Nat.card F = (2 ^ f) ^ 2) (ha : herm (unitaryInvolution F 2 f) a a = 0)
    (hb : herm (unitaryInvolution F 2 f) b b = 0)
    (hab : herm (unitaryInvolution F 2 f) a b = 1)
    (v w : Fin 2 → fixSub (unitaryInvolution F 2 f)) :
    herm (unitaryInvolution F 2 f) ((v 0 : F) • a + (v 1 : F) • b)
        ((w 0 : F) • a + (w 1 : F) • b) =
      (v 0 : F) * (w 1 : F) + (v 1 : F) * (w 0 : F) := by
  have hba : herm (unitaryInvolution F 2 f) b a = 1 := by
    rw [herm_conj _ (unitaryInvolution_involutive hF), hab, map_one]
  have hv0 : (unitaryInvolution F 2 f) (v 0 : F) = (v 0 : F) := mem_fixSub.1 (v 0).2
  have hv1 : (unitaryInvolution F 2 f) (v 1 : F) = (v 1 : F) := mem_fixSub.1 (v 1).2
  simp only [herm_add_left, herm_add_right, herm_smul_left, herm_smul_right,
    unitaryPlane_herm_b_plane hF ha hb hab, unitaryPlane_herm_a_plane ha hb hab, ha, hb, hab,
    hba, hv0, hv1]
  ring

private theorem unitaryPlane_plane_ne_zero {d : ℕ} {a b : Fin d → F}
    (hF : Nat.card F = (2 ^ f) ^ 2) (ha : herm (unitaryInvolution F 2 f) a a = 0)
    (hb : herm (unitaryInvolution F 2 f) b b = 0)
    (hab : herm (unitaryInvolution F 2 f) a b = 1)
    {v : Fin 2 → fixSub (unitaryInvolution F 2 f)} (hv : v ≠ 0) :
    ((v 0 : F) • a + (v 1 : F) • b) ≠ 0 := by
  intro h
  apply hv
  have h2 : (v 0 : F) = 0 ∧ (v 1 : F) = 0 :=
    unitaryPlane_smul_add_smul_inj hF ha hb hab (α := (v 0 : F)) (β := (v 1 : F))
      (α' := 0) (β' := 0) (by rw [h]; simp)
  funext i
  fin_cases i
  · exact Subtype.ext h2.1
  · exact Subtype.ext h2.2

private theorem unitaryPlane_plane_add_smul {d : ℕ} {a b : Fin d → F}
    (v w : Fin 2 → fixSub (unitaryInvolution F 2 f))
    (lam : fixSub (unitaryInvolution F 2 f)) :
    ((v 0 : F) • a + (v 1 : F) • b) + (lam : F) • ((w 0 : F) • a + (w 1 : F) • b) =
      ((v 0 + lam * w 0 : fixSub (unitaryInvolution F 2 f)) : F) • a +
        ((v 1 + lam * w 1 : fixSub (unitaryInvolution F 2 f)) : F) • b := by
  rw [unitaryPlane_add_smul_add_smul]
  simp

private theorem unitaryPlane_Vmem {d : ℕ} {a b : Fin d → F}
    (hF : Nat.card F = (2 ^ f) ^ 2) (ha : herm (unitaryInvolution F 2 f) a a = 0)
    (hb : herm (unitaryInvolution F 2 f) b b = 0)
    (hab : herm (unitaryInvolution F 2 f) a b = 1)
    {v : Fin 2 → fixSub (unitaryInvolution F 2 f)} (hv : v ≠ 0) :
    Vmem (unitaryPlane_S0 hF) (kFactsSuProjTv hF d ((v 0 : F) • a + (v 1 : F) • b) 1) =
      {y | ∃ s : F, s ≠ 0 ∧ (unitaryInvolution F 2 f) s = s ∧
        y = kFactsSuProjTv hF d ((v 0 : F) • a + (v 1 : F) • b) s} := by
  have hz0 : ((v 0 : F) • a + (v 1 : F) • b) ≠ 0 := unitaryPlane_plane_ne_zero hF ha hb hab hv
  have hzi : herm (unitaryInvolution F 2 f) ((v 0 : F) • a + (v 1 : F) • b)
      ((v 0 : F) • a + (v 1 : F) • b) = 0 :=
    unitaryPlane_herm_plane_self hF ha hb hab (v 0) (v 1)
  change Vmem {y | ∃ c' : Fin d → F, c' ≠ 0 ∧
      herm (unitaryInvolution F 2 f) c' c' = 0 ∧ y = kFactsSuProjTv hF d c' 1}
      (kFactsSuProjTv hF d ((v 0 : F) • a + (v 1 : F) • b) 1) = _
  rw [Vmem_setOf_kFactsSuProjTv hF hz0 hzi]
  ext y
  constructor
  · rintro ⟨s, hs0, hs, hy⟩
    refine ⟨s, hs0, ?_, hy⟩
    have h : (unitaryInvolution F 2 f) s = -s := by linear_combination hs
    rwa [CharTwo.neg_eq] at h
  · rintro ⟨s, hs0, hs, hy⟩
    exact ⟨s, hs0, by rw [hs]; exact CharTwo.add_self_eq_zero _, hy⟩

private theorem unitaryPlane_tv_mem {d : ℕ} {a b : Fin d → F}
    (hF : Nat.card F = (2 ^ f) ^ 2) (ha : herm (unitaryInvolution F 2 f) a a = 0)
    (hb : herm (unitaryInvolution F 2 f) b b = 0)
    (hab : herm (unitaryInvolution F 2 f) a b = 1)
    (p r s : fixSub (unitaryInvolution F 2 f)) :
    kFactsSuProjTv hF d ((p : F) • a + (r : F) • b) (s : F) ∈
      (unitaryPlane_Phi hF ha hb hab).range :=
  ⟨unitaryPlane_tvMat p r s, unitaryPlane_Phi_tvMat hF ha hb hab p r s⟩

private theorem unitaryPlane_Phi_u2 {d : ℕ} {a b : Fin d → F}
    (hF : Nat.card F = (2 ^ f) ^ 2) (ha : herm (unitaryInvolution F 2 f) a a = 0)
    (hb : herm (unitaryInvolution F 2 f) b b = 0)
    (hab : herm (unitaryInvolution F 2 f) a b = 1)
    (c : fixSub (unitaryInvolution F 2 f)) :
    unitaryPlane_Phi hF ha hb hab (u2 c) = kFactsSuProjTv hF d a (c : F) := by
  have hs : (c : F) + (unitaryInvolution F 2 f) (c : F) = 0 := by
    rw [mem_fixSub.1 c.2]; exact CharTwo.add_self_eq_zero _
  have h : planeSUN (unitaryInvolution_involutive hF) ha hb hab (u2 c) =
      suTv (isUnitaryInvolution_unitaryInvolution hF) a (c : F) :=
    (isTv_planeSUN_u2 (unitaryInvolution_involutive hF) ha hb hab c).unique
      (fun x => suTv_smul (isUnitaryInvolution_unitaryInvolution hF) ha hs x)
  rw [unitaryPlane_Phi_apply, h]
  rfl

private theorem unitaryPlane_Phi_l2 {d : ℕ} {a b : Fin d → F}
    (hF : Nat.card F = (2 ^ f) ^ 2) (ha : herm (unitaryInvolution F 2 f) a a = 0)
    (hb : herm (unitaryInvolution F 2 f) b b = 0)
    (hab : herm (unitaryInvolution F 2 f) a b = 1)
    (c : fixSub (unitaryInvolution F 2 f)) :
    unitaryPlane_Phi hF ha hb hab (l2 c) = kFactsSuProjTv hF d b (c : F) := by
  have hs : (c : F) + (unitaryInvolution F 2 f) (c : F) = 0 := by
    rw [mem_fixSub.1 c.2]; exact CharTwo.add_self_eq_zero _
  have h : planeSUN (unitaryInvolution_involutive hF) ha hb hab (l2 c) =
      suTv (isUnitaryInvolution_unitaryInvolution hF) b (c : F) :=
    (isTv_planeSUN_l2 (unitaryInvolution_involutive hF) ha hb hab c).unique
      (fun x => suTv_smul (isUnitaryInvolution_unitaryInvolution hF) hb hs x)
  rw [unitaryPlane_Phi_apply, h]
  rfl

private theorem unitaryPlane_closure_range_u2_l2 :
    Subgroup.closure (Set.range (u2 : fixSub (unitaryInvolution F 2 f) →
        Matrix.SpecialLinearGroup (Fin 2) (fixSub (unitaryInvolution F 2 f))) ∪
      Set.range (l2 : _ → Matrix.SpecialLinearGroup (Fin 2) (fixSub (unitaryInvolution F 2 f)))) =
        ⊤ := by
  have hu : (u2 : fixSub (unitaryInvolution F 2 f) →
        Matrix.SpecialLinearGroup (Fin 2) (fixSub (unitaryInvolution F 2 f))) =
      CFSG.LieType.Steinberg.sl2Upper (k := fixSub (unitaryInvolution F 2 f)) := by
    funext d; apply Subtype.ext; rw [u2_coe]; rfl
  have hl : (l2 : fixSub (unitaryInvolution F 2 f) →
        Matrix.SpecialLinearGroup (Fin 2) (fixSub (unitaryInvolution F 2 f))) =
      CFSG.LieType.Steinberg.sl2Lower (k := fixSub (unitaryInvolution F 2 f)) := by
    funext d; apply Subtype.ext; rw [l2_coe]; rfl
  rw [hu, hl]
  exact CFSG.StandardType.RankOneXfer.closure_sl2Upper_sl2Lower_eq_top

private theorem unitaryPlane_closure_le {d : ℕ} {a b : Fin d → F}
    (hF : Nat.card F = (2 ^ f) ^ 2) (ha : herm (unitaryInvolution F 2 f) a a = 0)
    (hb : herm (unitaryInvolution F 2 f) b b = 0)
    (hab : herm (unitaryInvolution F 2 f) a b = 1)
    {v w : Fin 2 → fixSub (unitaryInvolution F 2 f)} (hv : v ≠ 0) :
    Subgroup.closure (insert (kFactsSuProjTv hF d ((w 0 : F) • a + (w 1 : F) • b) 1)
      (Vmem (unitaryPlane_S0 hF) (kFactsSuProjTv hF d ((v 0 : F) • a + (v 1 : F) • b) 1))) ≤
      (unitaryPlane_Phi hF ha hb hab).range := by
  refine (Subgroup.closure_le _).mpr ?_
  intro e he
  rcases he with rfl | heV
  · exact unitaryPlane_tv_mem hF ha hb hab (w 0) (w 1) 1
  · rw [unitaryPlane_Vmem hF ha hb hab hv] at heV
    obtain ⟨s, hs0, hs, rfl⟩ := heV
    exact unitaryPlane_tv_mem hF ha hb hab (v 0) (v 1) ⟨s, mem_fixSub.2 hs⟩

private theorem unitaryPlane_smul_vec {d : ℕ} {a b : Fin d → F}
    (v : Fin 2 → fixSub (unitaryInvolution F 2 f)) (lam : fixSub (unitaryInvolution F 2 f)) :
    (lam : F) • ((v 0 : F) • a + (v 1 : F) • b) =
      ((lam * v 0 : fixSub (unitaryInvolution F 2 f)) : F) • a +
        ((lam * v 1 : fixSub (unitaryInvolution F 2 f)) : F) • b := by
  rw [smul_add, smul_smul, smul_smul]
  simp

private theorem unitaryPlane_exists_sq (c : fixSub (unitaryInvolution F 2 f)) :
    ∃ mu : fixSub (unitaryInvolution F 2 f), mu * mu = c := by
  obtain ⟨mu, hmu⟩ := isSquare_of_charTwo' c
  exact ⟨mu, hmu.symm⟩

private theorem unitaryPlane_tv_zero {d : ℕ} {a b : Fin d → F}
    (hF : Nat.card F = (2 ^ f) ^ 2) (ha : herm (unitaryInvolution F 2 f) a a = 0)
    (hb : herm (unitaryInvolution F 2 f) b b = 0)
    (hab : herm (unitaryInvolution F 2 f) a b = 1)
    (v : Fin 2 → fixSub (unitaryInvolution F 2 f)) :
    kFactsSuProjTv hF d ((v 0 : F) • a + (v 1 : F) • b) 0 = 1 := by
  have hzi : herm (unitaryInvolution F 2 f) ((v 0 : F) • a + (v 1 : F) • b)
      ((v 0 : F) • a + (v 1 : F) • b) = 0 :=
    unitaryPlane_herm_plane_self hF ha hb hab (v 0) (v 1)
  have h : suTv (isUnitaryInvolution_unitaryInvolution hF)
      ((v 0 : F) • a + (v 1 : F) • b) 0 = 1 :=
    IsTv.unique (t := suTv (isUnitaryInvolution_unitaryInvolution hF)
        ((v 0 : F) • a + (v 1 : F) • b) 0) (t' := 1)
      (fun x => suTv_smul (isUnitaryInvolution_unitaryInvolution hF) hzi (by simp) x)
      (IsTv.one (a := ((v 0 : F) • a + (v 1 : F) • b)))
  rw [kFactsSuProjTv, h, map_one]

private theorem unitaryPlane_exists_sl2_pair {v v' : Fin 2 → fixSub (unitaryInvolution F 2 f)}
    (h : v 0 * v' 1 - v 1 * v' 0 ≠ 0) :
    ∃ (B : Matrix.SpecialLinearGroup (Fin 2) (fixSub (unitaryInvolution F 2 f)))
      (mu : fixSub (unitaryInvolution F 2 f)), mu ≠ 0 ∧
      (B : Matrix (Fin 2) (Fin 2) (fixSub (unitaryInvolution F 2 f))) *ᵥ Pi.single 0 1 = v ∧
      (B : Matrix (Fin 2) (Fin 2) (fixSub (unitaryInvolution F 2 f))) *ᵥ Pi.single 1 1 = mu • v'
        := by
  set D : fixSub (unitaryInvolution F 2 f) := v 0 * v' 1 - v 1 * v' 0 with hD
  set mu : fixSub (unitaryInvolution F 2 f) := D⁻¹ with hmu
  have hmu0 : mu ≠ 0 := inv_ne_zero h
  have hdet : (!![v 0, mu * v' 0; v 1, mu * v' 1] :
      Matrix (Fin 2) (Fin 2) (fixSub (unitaryInvolution F 2 f))).det = 1 := by
    have h1 : (!![v 0, mu * v' 0; v 1, mu * v' 1] :
        Matrix (Fin 2) (Fin 2) (fixSub (unitaryInvolution F 2 f))).det =
        v 0 * (mu * v' 1) - mu * v' 0 * v 1 := by
      rw [Matrix.det_fin_two]
      simp
    rw [h1, hmu]
    have hD' : v 0 * (D⁻¹ * v' 1) - D⁻¹ * v' 0 * v 1 = D⁻¹ * D := by rw [hD]; ring
    rw [hD', inv_mul_cancel₀ h]
  refine ⟨⟨!![v 0, mu * v' 0; v 1, mu * v' 1], hdet⟩, mu, hmu0, ?_, ?_⟩
  · rw [Matrix.mulVec_single_one]
    funext i
    fin_cases i <;> simp [Matrix.col]
  · rw [Matrix.mulVec_single_one]
    funext i
    fin_cases i <;> simp [Matrix.col]

private theorem unitaryPlane_single_zero :
    (Pi.single (0 : Fin 2) 1 : Fin 2 → fixSub (unitaryInvolution F 2 f)) = ![1, 0] := by
  funext i
  fin_cases i <;> simp [Pi.single_eq_same, Pi.single_eq_of_ne]

private theorem unitaryPlane_single_one :
    (Pi.single (1 : Fin 2) 1 : Fin 2 → fixSub (unitaryInvolution F 2 f)) = ![0, 1] := by
  funext i
  fin_cases i <;> simp [Pi.single_eq_same, Pi.single_eq_of_ne]

private theorem unitaryPlane_herm_plane_comm {d : ℕ} {a b : Fin d → F}
    (hF : Nat.card F = (2 ^ f) ^ 2) (ha : herm (unitaryInvolution F 2 f) a a = 0)
    (hb : herm (unitaryInvolution F 2 f) b b = 0)
    (hab : herm (unitaryInvolution F 2 f) a b = 1) (v w : Fin 2 → fixSub (unitaryInvolution F 2
      f)) :
    herm (unitaryInvolution F 2 f) ((w 0 : F) • a + (w 1 : F) • b)
        ((v 0 : F) • a + (v 1 : F) • b) =
      herm (unitaryInvolution F 2 f) ((v 0 : F) • a + (v 1 : F) • b)
        ((w 0 : F) • a + (w 1 : F) • b) := by
  rw [unitaryPlane_herm_plane_plane hF ha hb hab w v,
    unitaryPlane_herm_plane_plane hF ha hb hab v w]
  ring

private theorem unitaryPlane_herm_plane_fixed {d : ℕ} {a b : Fin d → F}
    (hF : Nat.card F = (2 ^ f) ^ 2) (ha : herm (unitaryInvolution F 2 f) a a = 0)
    (hb : herm (unitaryInvolution F 2 f) b b = 0)
    (hab : herm (unitaryInvolution F 2 f) a b = 1) (v w : Fin 2 → fixSub (unitaryInvolution F 2
      f)) :
    (unitaryInvolution F 2 f) (herm (unitaryInvolution F 2 f) ((w 0 : F) • a + (w 1 : F) • b)
        ((v 0 : F) • a + (v 1 : F) • b)) =
      herm (unitaryInvolution F 2 f) ((w 0 : F) • a + (w 1 : F) • b)
        ((v 0 : F) • a + (v 1 : F) • b) := by
  rw [unitaryPlane_herm_plane_plane hF ha hb hab w v, map_add, map_mul, map_mul,
    mem_fixSub.1 (w 0).2, mem_fixSub.1 (v 1).2, mem_fixSub.1 (w 1).2, mem_fixSub.1 (v 0).2]

private theorem unitaryPlane_exists_sl2_map_pair {v v' : Fin 2 → fixSub (unitaryInvolution F 2 f)}
    (h : v 0 * v' 1 - v 1 * v' 0 ≠ 0) :
    ∃ (B : Matrix.SpecialLinearGroup (Fin 2) (fixSub (unitaryInvolution F 2 f)))
      (mu : fixSub (unitaryInvolution F 2 f)), mu ≠ 0 ∧
      (B : Matrix (Fin 2) (Fin 2) (fixSub (unitaryInvolution F 2 f))) *ᵥ
        (![1, 0] : Fin 2 → fixSub (unitaryInvolution F 2 f)) = v ∧
      (B : Matrix (Fin 2) (Fin 2) (fixSub (unitaryInvolution F 2 f))) *ᵥ
        (![0, 1] : Fin 2 → fixSub (unitaryInvolution F 2 f)) = mu • v' := by
  obtain ⟨B, mu, hmu, h1, h2⟩ := unitaryPlane_exists_sl2_pair h
  have h1' : (B : Matrix (Fin 2) (Fin 2) (fixSub (unitaryInvolution F 2 f))) *ᵥ
      (![1, 0] : Fin 2 → fixSub (unitaryInvolution F 2 f)) = v := by
    rw [← unitaryPlane_single_zero]
    exact h1
  have h2' : (B : Matrix (Fin 2) (Fin 2) (fixSub (unitaryInvolution F 2 f))) *ᵥ
      (![0, 1] : Fin 2 → fixSub (unitaryInvolution F 2 f)) = mu • v' := by
    rw [← unitaryPlane_single_one]
    exact h2
  exact ⟨B, mu, hmu, h1', h2'⟩

private theorem unitaryPlane_rootGroup_image {d : ℕ} {a b : Fin d → F}
    (hF : Nat.card F = (2 ^ f) ^ 2) (ha : herm (unitaryInvolution F 2 f) a a = 0)
    (hb : herm (unitaryInvolution F 2 f) b b = 0)
    (hab : herm (unitaryInvolution F 2 f) a b = 1)
    {v w : Fin 2 → fixSub (unitaryInvolution F 2 f)}
    {C : Subgroup (StatedProj (StatedSU d (2 ^ f) F))}
    (lam : fixSub (unitaryInvolution F 2 f))
    (hlam : (lam : F) = herm (unitaryInvolution F 2 f) ((w 0 : F) • a + (w 1 : F) • b)
      ((v 0 : F) • a + (v 1 : F) • b))
    (hyC : kFactsSuProjTv hF d ((w 0 : F) • a + (w 1 : F) • b) 1 ∈ C)
    (hzC : ∀ s : F, (unitaryInvolution F 2 f) s = s →
      kFactsSuProjTv hF d ((v 0 : F) • a + (v 1 : F) • b) s ∈ C) :
    ∀ s : F, (unitaryInvolution F 2 f) s = s →
      kFactsSuProjTv hF d
        (((v 0 + lam * w 0 : fixSub (unitaryInvolution F 2 f)) : F) • a +
          ((v 1 + lam * w 1 : fixSub (unitaryInvolution F 2 f)) : F) • b) s ∈ C := by
  intro s hs
  have hs0 : s + (unitaryInvolution F 2 f) s = 0 := by
    rw [hs]; exact CharTwo.add_self_eq_zero _
  have hzi : herm (unitaryInvolution F 2 f) ((v 0 : F) • a + (v 1 : F) • b)
      ((v 0 : F) • a + (v 1 : F) • b) = 0 :=
    unitaryPlane_herm_plane_self hF ha hb hab (v 0) (v 1)
  have hwzi : herm (unitaryInvolution F 2 f) ((w 0 : F) • a + (w 1 : F) • b)
      ((w 0 : F) • a + (w 1 : F) • b) = 0 :=
    unitaryPlane_herm_plane_self hF ha hb hab (w 0) (w 1)
  have hconj := kFacts_suProj_conj_suProjTv hF
    (suTv (isUnitaryInvolution_unitaryInvolution hF) ((w 0 : F) • a + (w 1 : F) • b) 1) hzi hs0
  have hvec : suTv (isUnitaryInvolution_unitaryInvolution hF)
      ((w 0 : F) • a + (w 1 : F) • b) 1 • ((v 0 : F) • a + (v 1 : F) • b) =
      (((v 0 + lam * w 0 : fixSub (unitaryInvolution F 2 f)) : F) • a +
        ((v 1 + lam * w 1 : fixSub (unitaryInvolution F 2 f)) : F) • b) := by
    rw [suTv_smul (isUnitaryInvolution_unitaryInvolution hF) hwzi
      (by rw [map_one]; exact CharTwo.add_self_eq_zero 1), one_mul, ← hlam,
      unitaryPlane_plane_add_smul]
  rw [hvec] at hconj
  rw [← hconj]
  exact C.mul_mem (C.mul_mem hyC (hzC s hs)) (C.inv_mem hyC)

private theorem unitaryPlane_Phi_le_closure_of_u2_l2 {d : ℕ} {a b : Fin d → F}
    (hF : Nat.card F = (2 ^ f) ^ 2) (ha : herm (unitaryInvolution F 2 f) a a = 0)
    (hb : herm (unitaryInvolution F 2 f) b b = 0)
    (hab : herm (unitaryInvolution F 2 f) a b = 1)
    {C : Subgroup (StatedProj (StatedSU d (2 ^ f) F))}
    {B : Matrix.SpecialLinearGroup (Fin 2) (fixSub (unitaryInvolution F 2 f))}
    (hu : ∀ c : fixSub (unitaryInvolution F 2 f),
      unitaryPlane_Phi hF ha hb hab (B * u2 c * B⁻¹) ∈ C)
    (hl : ∀ c : fixSub (unitaryInvolution F 2 f),
      unitaryPlane_Phi hF ha hb hab (B * l2 c * B⁻¹) ∈ C) :
    (unitaryPlane_Phi hF ha hb hab).range ≤ C := by
  let H : Subgroup (Matrix.SpecialLinearGroup (Fin 2) (fixSub (unitaryInvolution F 2 f))) :=
    C.comap ((unitaryPlane_Phi hF ha hb hab).comp (MulAut.conj B).toMonoidHom)
  have htop : H = ⊤ := by
    refine le_antisymm le_top ?_
    rw [← unitaryPlane_closure_range_u2_l2]
    refine (Subgroup.closure_le H).mpr ?_
    rintro X (hX | hX)
    · obtain ⟨c, rfl⟩ := hX
      exact hu c
    · obtain ⟨c, rfl⟩ := hX
      exact hl c
  intro Y hY
  obtain ⟨Z, rfl⟩ := hY
  have hZ : B⁻¹ * Z * B ∈ H := by rw [htop]; exact Subgroup.mem_top _
  rw [Subgroup.mem_comap] at hZ
  have heq : (MulAut.conj B) (B⁻¹ * Z * B) = Z := by
    change B * (B⁻¹ * Z * B) * B⁻¹ = Z
    group
  have hZ' : unitaryPlane_Phi hF ha hb hab ((MulAut.conj B) (B⁻¹ * Z * B)) ∈ C := hZ
  rw [heq] at hZ'
  exact hZ'

private theorem unitaryPlane_lam {d : ℕ} {a b : Fin d → F}
    (hF : Nat.card F = (2 ^ f) ^ 2) (ha : herm (unitaryInvolution F 2 f) a a = 0)
    (hb : herm (unitaryInvolution F 2 f) b b = 0)
    (hab : herm (unitaryInvolution F 2 f) a b = 1)
    {v w : Fin 2 → fixSub (unitaryInvolution F 2 f)}
    (hne : herm (unitaryInvolution F 2 f) ((v 0 : F) • a + (v 1 : F) • b)
      ((w 0 : F) • a + (w 1 : F) • b) ≠ 0)
    {C : Subgroup (StatedProj (StatedSU d (2 ^ f) F))}
    (hyC : kFactsSuProjTv hF d ((w 0 : F) • a + (w 1 : F) • b) 1 ∈ C)
    (hzC : ∀ s : F, (unitaryInvolution F 2 f) s = s →
      kFactsSuProjTv hF d ((v 0 : F) • a + (v 1 : F) • b) s ∈ C) :
    ∃ lam : fixSub (unitaryInvolution F 2 f),
      (lam : F) = herm (unitaryInvolution F 2 f) ((w 0 : F) • a + (w 1 : F) • b)
        ((v 0 : F) • a + (v 1 : F) • b) ∧ (lam : F) ≠ 0 ∧
      ∀ s : F, (unitaryInvolution F 2 f) s = s →
        kFactsSuProjTv hF d
          (((v 0 + lam * w 0 : fixSub (unitaryInvolution F 2 f)) : F) • a +
            ((v 1 + lam * w 1 : fixSub (unitaryInvolution F 2 f)) : F) • b) s ∈ C := by
  refine ⟨⟨herm (unitaryInvolution F 2 f) ((w 0 : F) • a + (w 1 : F) • b)
      ((v 0 : F) • a + (v 1 : F) • b),
      mem_fixSub.2 (unitaryPlane_herm_plane_fixed hF ha hb hab v w)⟩, rfl, ?_, ?_⟩
  · show (herm (unitaryInvolution F 2 f) ((w 0 : F) • a + (w 1 : F) • b)
      ((v 0 : F) • a + (v 1 : F) • b) : F) ≠ 0
    rw [unitaryPlane_herm_plane_comm hF ha hb hab v w]
    exact hne
  · exact unitaryPlane_rootGroup_image hF ha hb hab _ rfl hyC hzC

private theorem unitaryPlane_coord_det_ne_zero {d : ℕ} {a b : Fin d → F}
    (hF : Nat.card F = (2 ^ f) ^ 2) (ha : herm (unitaryInvolution F 2 f) a a = 0)
    (hb : herm (unitaryInvolution F 2 f) b b = 0)
    (hab : herm (unitaryInvolution F 2 f) a b = 1)
    {v w : Fin 2 → fixSub (unitaryInvolution F 2 f)}
    (hne : herm (unitaryInvolution F 2 f) ((v 0 : F) • a + (v 1 : F) • b)
      ((w 0 : F) • a + (w 1 : F) • b) ≠ 0)
    {lam : fixSub (unitaryInvolution F 2 f)} (hlam0 : (lam : F) ≠ 0) :
    v 0 * (![v 0 + lam * w 0, v 1 + lam * w 1] :
        Fin 2 → fixSub (unitaryInvolution F 2 f)) 1 -
      v 1 * (![v 0 + lam * w 0, v 1 + lam * w 1] :
        Fin 2 → fixSub (unitaryInvolution F 2 f)) 0 ≠ 0 := by
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  have hmul : (v 0 : F) * ((v 1 : F) + (lam : F) * (w 1 : F)) -
      (v 1 : F) * ((v 0 : F) + (lam : F) * (w 0 : F)) =
      (lam : F) * herm (unitaryInvolution F 2 f) ((v 0 : F) • a + (v 1 : F) • b)
        ((w 0 : F) • a + (w 1 : F) • b) := by
    rw [unitaryPlane_herm_plane_plane hF ha hb hab v w]
    linear_combination (-((lam : F) * (v 1 : F) * (w 0 : F))) *
      (CharTwo.two_eq_zero : (2 : F) = 0)
  intro h0
  have h0F : (v 0 : F) * ((v 1 : F) + (lam : F) * (w 1 : F)) -
      (v 1 : F) * ((v 0 : F) + (lam : F) * (w 0 : F)) = 0 := by
    have h1 := congrArg (fun z : fixSub (unitaryInvolution F 2 f) => (z : F)) h0
    simpa only [Subfield.coe_sub, Subfield.coe_mul, Subfield.coe_add, Subfield.coe_zero]
      using h1
  rw [hmul] at h0F
  exact mul_ne_zero hlam0 hne h0F

private theorem unitaryPlane_u2_mem {d : ℕ} {a b : Fin d → F}
    (hF : Nat.card F = (2 ^ f) ^ 2) (ha : herm (unitaryInvolution F 2 f) a a = 0)
    (hb : herm (unitaryInvolution F 2 f) b b = 0)
    (hab : herm (unitaryInvolution F 2 f) a b = 1)
    {v : Fin 2 → fixSub (unitaryInvolution F 2 f)}
    {C : Subgroup (StatedProj (StatedSU d (2 ^ f) F))}
    {B : Matrix.SpecialLinearGroup (Fin 2) (fixSub (unitaryInvolution F 2 f))}
    (hBe : (B : Matrix (Fin 2) (Fin 2) (fixSub (unitaryInvolution F 2 f))) *ᵥ
      (![1, 0] : Fin 2 → fixSub (unitaryInvolution F 2 f)) = v)
    (hzC : ∀ s : F, (unitaryInvolution F 2 f) s = s →
      kFactsSuProjTv hF d ((v 0 : F) • a + (v 1 : F) • b) s ∈ C)
    (c : fixSub (unitaryInvolution F 2 f)) :
    unitaryPlane_Phi hF ha hb hab (B * u2 c * B⁻¹) ∈ C := by
  have hBe' : v = (B : Matrix (Fin 2) (Fin 2) (fixSub (unitaryInvolution F 2 f))) *ᵥ
      (![1, 0] : Fin 2 → fixSub (unitaryInvolution F 2 f)) := hBe.symm
  have hconj := unitaryPlane_conj hF ha hb hab B
    (![1, 0] : Fin 2 → fixSub (unitaryInvolution F 2 f)) v hBe' (c : F) (mem_fixSub.1 c.2)
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Subfield.coe_one, Subfield.coe_zero, one_smul, zero_smul, add_zero] at hconj
  rw [map_mul, map_mul, map_inv, unitaryPlane_Phi_u2, hconj]
  exact hzC (c : F) (mem_fixSub.1 c.2)

private theorem unitaryPlane_l2_mem {d : ℕ} {a b : Fin d → F}
    (hF : Nat.card F = (2 ^ f) ^ 2) (ha : herm (unitaryInvolution F 2 f) a a = 0)
    (hb : herm (unitaryInvolution F 2 f) b b = 0)
    (hab : herm (unitaryInvolution F 2 f) a b = 1)
    {v w wv : Fin 2 → fixSub (unitaryInvolution F 2 f)}
    {lam mu : fixSub (unitaryInvolution F 2 f)}
    {C : Subgroup (StatedProj (StatedSU d (2 ^ f) F))}
    {B : Matrix.SpecialLinearGroup (Fin 2) (fixSub (unitaryInvolution F 2 f))}
    (hwvz : ((wv 0 : F) • a + (wv 1 : F) • b) =
      (((v 0 + lam * w 0 : fixSub (unitaryInvolution F 2 f)) : F) • a +
        ((v 1 + lam * w 1 : fixSub (unitaryInvolution F 2 f)) : F) • b))
    (hBf : (B : Matrix (Fin 2) (Fin 2) (fixSub (unitaryInvolution F 2 f))) *ᵥ
      (![0, 1] : Fin 2 → fixSub (unitaryInvolution F 2 f)) = mu • wv)
    (hz'C : ∀ s : F, (unitaryInvolution F 2 f) s = s →
      kFactsSuProjTv hF d
        (((v 0 + lam * w 0 : fixSub (unitaryInvolution F 2 f)) : F) • a +
          ((v 1 + lam * w 1 : fixSub (unitaryInvolution F 2 f)) : F) • b) s ∈ C)
    (hwvi : herm (unitaryInvolution F 2 f)
      (((v 0 + lam * w 0 : fixSub (unitaryInvolution F 2 f)) : F) • a +
        ((v 1 + lam * w 1 : fixSub (unitaryInvolution F 2 f)) : F) • b)
      (((v 0 + lam * w 0 : fixSub (unitaryInvolution F 2 f)) : F) • a +
        ((v 1 + lam * w 1 : fixSub (unitaryInvolution F 2 f)) : F) • b) = 0)
    (c : fixSub (unitaryInvolution F 2 f)) :
    unitaryPlane_Phi hF ha hb hab (B * l2 c * B⁻¹) ∈ C := by
  have hs : (c : F) + (unitaryInvolution F 2 f) (c : F) = 0 := by
    rw [mem_fixSub.1 c.2]; exact CharTwo.add_self_eq_zero _
  have hBf' : mu • wv = (B : Matrix (Fin 2) (Fin 2) (fixSub (unitaryInvolution F 2 f))) *ᵥ
      (![0, 1] : Fin 2 → fixSub (unitaryInvolution F 2 f)) := hBf.symm
  have hconj := unitaryPlane_conj hF ha hb hab B
    (![0, 1] : Fin 2 → fixSub (unitaryInvolution F 2 f)) (mu • wv) hBf' (c : F)
    (mem_fixSub.1 c.2)
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Subfield.coe_one, Subfield.coe_zero, one_smul, zero_smul, zero_add] at hconj
  simp only [Pi.smul_apply, smul_eq_mul] at hconj
  rw [← unitaryPlane_smul_vec wv mu, hwvz] at hconj
  rw [kFacts_suProjTv_smul_vec hF hwvi hs (mu : F)] at hconj
  rw [map_mul, map_mul, map_inv, unitaryPlane_Phi_l2, hconj]
  exact hz'C ((unitaryInvolution F 2 f) (mu : F) * (mu : F) * (c : F)) (by
    rw [map_mul, map_mul]
    simp only [mem_fixSub.1 (mu).2, mem_fixSub.1 c.2])

private theorem unitaryPlane_Phi_range_le_closure {d : ℕ} {a b : Fin d → F}
    (hF : Nat.card F = (2 ^ f) ^ 2) (ha : herm (unitaryInvolution F 2 f) a a = 0)
    (hb : herm (unitaryInvolution F 2 f) b b = 0)
    (hab : herm (unitaryInvolution F 2 f) a b = 1)
    {v w : Fin 2 → fixSub (unitaryInvolution F 2 f)} (hv : v ≠ 0) (hw : w ≠ 0)
    (hne : herm (unitaryInvolution F 2 f) ((v 0 : F) • a + (v 1 : F) • b)
      ((w 0 : F) • a + (w 1 : F) • b) ≠ 0) :
    (unitaryPlane_Phi hF ha hb hab).range ≤
      Subgroup.closure (insert (kFactsSuProjTv hF d ((w 0 : F) • a + (w 1 : F) • b) 1)
        (Vmem (unitaryPlane_S0 hF)
          (kFactsSuProjTv hF d ((v 0 : F) • a + (v 1 : F) • b) 1))) := by
  set C : Subgroup (StatedProj (StatedSU d (2 ^ f) F)) :=
    Subgroup.closure (insert (kFactsSuProjTv hF d ((w 0 : F) • a + (w 1 : F) • b) 1)
      (Vmem (unitaryPlane_S0 hF)
        (kFactsSuProjTv hF d ((v 0 : F) • a + (v 1 : F) • b) 1))) with hC
  have hyC : kFactsSuProjTv hF d ((w 0 : F) • a + (w 1 : F) • b) 1 ∈ C :=
    Subgroup.subset_closure (by simp)
  have hzC : ∀ s : F, (unitaryInvolution F 2 f) s = s →
      kFactsSuProjTv hF d ((v 0 : F) • a + (v 1 : F) • b) s ∈ C := by
    intro s hs
    rcases eq_or_ne s 0 with rfl | hs0
    · rw [unitaryPlane_tv_zero hF ha hb hab v]
      exact Subgroup.one_mem C
    · have hmem : kFactsSuProjTv hF d ((v 0 : F) • a + (v 1 : F) • b) s ∈
          Vmem (unitaryPlane_S0 hF)
            (kFactsSuProjTv hF d ((v 0 : F) • a + (v 1 : F) • b) 1) := by
        rw [unitaryPlane_Vmem hF ha hb hab hv]
        exact ⟨s, hs0, hs, rfl⟩
      exact Subgroup.subset_closure (by simp [hmem])
  obtain ⟨lam, _, hlam0, hz'C⟩ := unitaryPlane_lam hF ha hb hab hne hyC hzC
  set wv : Fin 2 → fixSub (unitaryInvolution F 2 f) :=
    ![v 0 + lam * w 0, v 1 + lam * w 1] with hwv
  have hwvz : ((wv 0 : F) • a + (wv 1 : F) • b) =
      (((v 0 + lam * w 0 : fixSub (unitaryInvolution F 2 f)) : F) • a +
        ((v 1 + lam * w 1 : fixSub (unitaryInvolution F 2 f)) : F) • b) := by
    simp [hwv]
  have hwvi : herm (unitaryInvolution F 2 f)
      (((v 0 + lam * w 0 : fixSub (unitaryInvolution F 2 f)) : F) • a +
        ((v 1 + lam * w 1 : fixSub (unitaryInvolution F 2 f)) : F) • b)
      (((v 0 + lam * w 0 : fixSub (unitaryInvolution F 2 f)) : F) • a +
        ((v 1 + lam * w 1 : fixSub (unitaryInvolution F 2 f)) : F) • b) = 0 :=
    unitaryPlane_herm_plane_self hF ha hb hab (v 0 + lam * w 0) (v 1 + lam * w 1)
  have hdet : v 0 * wv 1 - v 1 * wv 0 ≠ 0 :=
    unitaryPlane_coord_det_ne_zero hF ha hb hab hne hlam0
  obtain ⟨B, mu, hmu0, hBe, hBf⟩ := unitaryPlane_exists_sl2_map_pair hdet
  exact unitaryPlane_Phi_le_closure_of_u2_l2 (B := B) hF ha hb hab
    (fun c => unitaryPlane_u2_mem hF ha hb hab hBe hzC c)
    (fun c => unitaryPlane_l2_mem hF ha hb hab hwvz hBf hz'C hwvi c)

private theorem unitaryPlane_closure_eq {d : ℕ} {a b : Fin d → F}
    (hF : Nat.card F = (2 ^ f) ^ 2) (ha : herm (unitaryInvolution F 2 f) a a = 0)
    (hb : herm (unitaryInvolution F 2 f) b b = 0)
    (hab : herm (unitaryInvolution F 2 f) a b = 1)
    {v w : Fin 2 → fixSub (unitaryInvolution F 2 f)} (hv : v ≠ 0) (hw : w ≠ 0)
    (hne : herm (unitaryInvolution F 2 f) ((v 0 : F) • a + (v 1 : F) • b)
      ((w 0 : F) • a + (w 1 : F) • b) ≠ 0) :
    Subgroup.closure (insert (kFactsSuProjTv hF d ((w 0 : F) • a + (w 1 : F) • b) 1)
      (Vmem (unitaryPlane_S0 hF)
        (kFactsSuProjTv hF d ((v 0 : F) • a + (v 1 : F) • b) 1))) =
      (unitaryPlane_Phi hF ha hb hab).range :=
  le_antisymm (unitaryPlane_closure_le hF ha hb hab hv)
    (unitaryPlane_Phi_range_le_closure hF ha hb hab hv hw hne)

private theorem unitaryPlane_card_fixSub (hF : Nat.card F = (2 ^ f) ^ 2) :
    Nat.card (fixSub (unitaryInvolution F 2 f)) = 2 ^ f := by
  haveI : Fact (Nat.Prime 2) := Nat.fact_prime_two
  have h := CFSG.LieType.Steinberg.card_fixedSubfield (F := F) (p := 2) (f := f) hF
  simpa [fixSub, CFSG.LieType.Steinberg.fixedSubfield] using h

private theorem unitaryPlane_uE_eq_u2 (c : fixSub (unitaryInvolution F 2 f)) :
    CFSG.OddStandard.Seitz77.Nat16.uE c = u2 c := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [CFSG.OddStandard.Seitz77.Nat16.uE, u2_coe]

private theorem unitaryPlane_e1_ne_zero :
    (![1, 0] : Fin 2 → fixSub (unitaryInvolution F 2 f)) ≠ 0 := by
  intro h
  have := congrFun h 0
  simp at this

private theorem unitaryPlane_e2_ne_zero :
    (![0, 1] : Fin 2 → fixSub (unitaryInvolution F 2 f)) ≠ 0 := by
  intro h
  have := congrFun h 1
  simp at this

private theorem unitaryPlane_mulVec_ne_zero
    (B : Matrix.SpecialLinearGroup (Fin 2) (fixSub (unitaryInvolution F 2 f)))
    {x : Fin 2 → fixSub (unitaryInvolution F 2 f)} (hx : x ≠ 0) :
    (B : Matrix (Fin 2) (Fin 2) (fixSub (unitaryInvolution F 2 f))) *ᵥ x ≠ 0 := by
  intro h
  apply hx
  have h2 : ((B⁻¹ * B : Matrix.SpecialLinearGroup (Fin 2) (fixSub (unitaryInvolution F 2 f))) :
      Matrix (Fin 2) (Fin 2) (fixSub (unitaryInvolution F 2 f))) *ᵥ x = x := by
    rw [inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec]
  rw [Matrix.SpecialLinearGroup.coe_mul, ← Matrix.mulVec_mulVec] at h2
  rw [h, Matrix.mulVec_zero] at h2
  exact h2.symm

private theorem unitaryPlane_involution_eq_tv {d : ℕ} {a b : Fin d → F}
    (hF : Nat.card F = (2 ^ f) ^ 2) (ha : herm (unitaryInvolution F 2 f) a a = 0)
    (hb : herm (unitaryInvolution F 2 f) b b = 0)
    (hab : herm (unitaryInvolution F 2 f) a b = 1)
    {A : Matrix.SpecialLinearGroup (Fin 2) (fixSub (unitaryInvolution F 2 f))}
    (hA1 : A ≠ 1) (hA2 : A * A = 1) :
    ∃ v : Fin 2 → fixSub (unitaryInvolution F 2 f), v ≠ 0 ∧
      unitaryPlane_Phi hF ha hb hab A =
        kFactsSuProjTv hF d ((v 0 : F) • a + (v 1 : F) • b) 1 := by
  obtain ⟨B, c, hc0, hAB⟩ :=
    CFSG.OddStandard.Seitz77.Nat16.exists_conj_uE_of_involution A hA1 hA2
  rw [unitaryPlane_uE_eq_u2] at hAB
  obtain ⟨mu, hmu⟩ := unitaryPlane_exists_sq c
  have hmu0 : mu ≠ 0 := by
    rintro rfl
    rw [zero_mul] at hmu
    exact hc0 hmu.symm
  set w : Fin 2 → fixSub (unitaryInvolution F 2 f) :=
    (B : Matrix (Fin 2) (Fin 2) (fixSub (unitaryInvolution F 2 f))) *ᵥ
      (![1, 0] : Fin 2 → fixSub (unitaryInvolution F 2 f)) with hw
  have hw0 : w ≠ 0 := unitaryPlane_mulVec_ne_zero B unitaryPlane_e1_ne_zero
  have hs : (c : F) + (unitaryInvolution F 2 f) (c : F) = 0 := by
    rw [mem_fixSub.1 c.2]; exact CharTwo.add_self_eq_zero _
  have hconj := unitaryPlane_conj hF ha hb hab B
    (![1, 0] : Fin 2 → fixSub (unitaryInvolution F 2 f)) w rfl (c : F) (mem_fixSub.1 c.2)
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Subfield.coe_one, Subfield.coe_zero, one_smul, zero_smul, add_zero] at hconj
  have hA : unitaryPlane_Phi hF ha hb hab A =
      kFactsSuProjTv hF d ((w 0 : F) • a + (w 1 : F) • b) (c : F) := by
    rw [hAB, map_mul, map_mul, map_inv, unitaryPlane_Phi_u2, hconj]
  have hzi : herm (unitaryInvolution F 2 f) ((w 0 : F) • a + (w 1 : F) • b)
      ((w 0 : F) • a + (w 1 : F) • b) = 0 :=
    unitaryPlane_herm_plane_self hF ha hb hab (w 0) (w 1)
  have hsmul : kFactsSuProjTv hF d ((w 0 : F) • a + (w 1 : F) • b) (c : F) =
      kFactsSuProjTv hF d
        (((mu * w 0 : fixSub (unitaryInvolution F 2 f)) : F) • a +
          ((mu * w 1 : fixSub (unitaryInvolution F 2 f)) : F) • b) 1 := by
    have hceq : (c : F) = (unitaryInvolution F 2 f) (mu : F) * (mu : F) * 1 := by
      rw [mem_fixSub.1 mu.2, mul_one, ← hmu]
      simp
    rw [← unitaryPlane_smul_vec w mu, kFacts_suProjTv_smul_vec hF hzi
      (by rw [map_one]; exact CharTwo.add_self_eq_zero 1) (mu : F), hceq]
  have hsm : mu • w ≠ 0 := by
    intro h0
    apply hw0
    funext i
    have h1 := congrFun h0 i
    simp only [Pi.smul_apply, Pi.zero_apply, smul_eq_mul] at h1
    exact (mul_eq_zero.mp h1).resolve_left hmu0
  refine ⟨mu • w, hsm, ?_⟩
  rw [hA, hsmul]
  simp only [Pi.smul_apply, smul_eq_mul]

private theorem unitaryPlane_involution_mem {d : ℕ} {a b : Fin d → F}
    (hF : Nat.card F = (2 ^ f) ^ 2) (ha : herm (unitaryInvolution F 2 f) a a = 0)
    (hb : herm (unitaryInvolution F 2 f) b b = 0)
    (hab : herm (unitaryInvolution F 2 f) a b = 1)
    {A : Matrix.SpecialLinearGroup (Fin 2) (fixSub (unitaryInvolution F 2 f))}
    (hA1 : A ≠ 1) (hA2 : A * A = 1) :
    unitaryPlane_Phi hF ha hb hab A ∈ unitaryPlane_S0 hF := by
  obtain ⟨v, hv0, hv⟩ := unitaryPlane_involution_eq_tv hF ha hb hab hA1 hA2
  exact ⟨_, unitaryPlane_plane_ne_zero hF ha hb hab hv0,
    unitaryPlane_herm_plane_self hF ha hb hab (v 0) (v 1), hv⟩

private theorem unitaryPlane_two_involutions (hF : Nat.card F = (2 ^ f) ^ 2) :
    ∃ aa bb : Matrix.SpecialLinearGroup (Fin 2) (fixSub (unitaryInvolution F 2 f)),
      aa * aa = 1 ∧ bb * bb = 1 ∧ aa ≠ 1 ∧ bb ≠ 1 ∧
        orderOf (aa * bb) = 2 ^ f + 1 := by
  obtain ⟨A, hA⟩ := CFSG.SeitzReduction.F4Pilot.exists_orderOf_eq_natCard_add_one
    (K := fixSub (unitaryInvolution F 2 f))
  rw [unitaryPlane_card_fixSub hF] at hA
  have hf1 : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with h0 | h0
    · exfalso
      rw [h0, pow_zero, one_pow] at hF
      have h1 := Finite.one_lt_card (α := F)
      rw [hF] at h1
      omega
    · exact h0
  have h3 : 3 ≤ orderOf A := by
    rw [hA]
    have h2 : 2 ≤ 2 ^ f := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf1
    omega
  obtain ⟨aa, haa, haA⟩ := CFSG.CGT.Timmesfeld75.exists_mul_self_eq_one_conj_eq_inv A
  let bb : Matrix.SpecialLinearGroup (Fin 2) (fixSub (unitaryInvolution F 2 f)) := aa * A
  have hbb : bb * bb = 1 := by
    show (aa * A) * (aa * A) = 1
    rw [← mul_assoc (aa * A) aa A, haA, inv_mul_cancel]
  have hAab : A = aa * bb := by
    show A = aa * (aa * A)
    rw [← mul_assoc, haa, one_mul]
  have hAne : A * A ≠ 1 := by
    intro h2'
    have hdvd : orderOf A ∣ 2 := orderOf_dvd_of_pow_eq_one (by rwa [pow_two])
    have hle : orderOf A ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
    omega
  have ha1 : aa ≠ 1 := by
    intro h
    apply hAne
    rw [show bb = aa * A from rfl, h, one_mul] at hbb
    exact hbb
  have hb1 : bb ≠ 1 := by
    intro h
    apply hAne
    rw [hAab, h, mul_one]
    exact haa
  exact ⟨aa, bb, haa, hbb, ha1, hb1, by rw [← hAab, hA]⟩

private theorem unitaryPlane_exists_orderOf_mul {d : ℕ} {a b : Fin d → F}
    (hF : Nat.card F = (2 ^ f) ^ 2) (hd : 3 ≤ d)
    (ha : herm (unitaryInvolution F 2 f) a a = 0)
    (hb : herm (unitaryInvolution F 2 f) b b = 0)
    (hab : herm (unitaryInvolution F 2 f) a b = 1) :
    ∃ x ∈ unitaryPlane_S0 hF, x ∈ (unitaryPlane_Phi hF ha hb hab).range ∧
      ∃ y ∈ unitaryPlane_S0 hF, y ∈ (unitaryPlane_Phi hF ha hb hab).range ∧
        orderOf (x * y) = 2 ^ f + 1 := by
  obtain ⟨aa, bb, haa, hbb, ha1, hb1, hord⟩ := unitaryPlane_two_involutions hF
  refine ⟨unitaryPlane_Phi hF ha hb hab aa, unitaryPlane_involution_mem hF ha hb hab ha1 haa,
    ⟨aa, rfl⟩, unitaryPlane_Phi hF ha hb hab bb,
    unitaryPlane_involution_mem hF ha hb hab hb1 hbb, ⟨bb, rfl⟩, ?_⟩
  have hxy : unitaryPlane_Phi hF ha hb hab aa * unitaryPlane_Phi hF ha hb hab bb =
      unitaryPlane_Phi hF ha hb hab (aa * bb) := by rw [map_mul]
  rw [hxy, orderOf_injective (f := unitaryPlane_Phi hF ha hb hab)
    (unitaryPlane_Phi_injective hF hd ha hb hab) (aa * bb), hord]

private theorem unitaryPlane_tv_zero_any {d : ℕ} (hF : Nat.card F = (2 ^ f) ^ 2)
    {c : Fin d → F} (hci : herm (unitaryInvolution F 2 f) c c = 0) :
    kFactsSuProjTv hF d c 0 = 1 := by
  have h : suTv (isUnitaryInvolution_unitaryInvolution hF) c 0 = 1 :=
    IsTv.unique (t := suTv (isUnitaryInvolution_unitaryInvolution hF) c 0) (t' := 1)
      (fun x => suTv_smul (isUnitaryInvolution_unitaryInvolution hF) hci (by simp) x)
      (IsTv.one (a := c))
  rw [kFactsSuProjTv, h, map_one]

private theorem unitaryPlane_tv_sq {d : ℕ} (hF : Nat.card F = (2 ^ f) ^ 2)
    {c : Fin d → F} (hci : herm (unitaryInvolution F 2 f) c c = 0) :
    kFactsSuProjTv hF d c 1 * kFactsSuProjTv hF d c 1 = 1 := by
  have h1 : (1 : F) + (unitaryInvolution F 2 f) 1 = 0 := by
    rw [map_one]; exact CharTwo.add_self_eq_zero 1
  have h : suTv (isUnitaryInvolution_unitaryInvolution hF) c 1 *
      suTv (isUnitaryInvolution_unitaryInvolution hF) c 1 =
      suTv (isUnitaryInvolution_unitaryInvolution hF) c 0 := by
    rw [suTv_mul_suTv (isUnitaryInvolution_unitaryInvolution hF) hci h1 h1]
    congr 1
    exact CharTwo.add_self_eq_zero 1
  have h2 : kFactsSuProjTv hF d c 0 = 1 := unitaryPlane_tv_zero_any hF hci
  rw [kFactsSuProjTv, ← map_mul, h]
  exact h2

private theorem unitaryPlane_tv_ne_one {d : ℕ} (hF : Nat.card F = (2 ^ f) ^ 2)
    {c : Fin d → F} (hc0 : c ≠ 0) (hci : herm (unitaryInvolution F 2 f) c c = 0) :
    kFactsSuProjTv hF d c 1 ≠ 1 := by
  intro h
  have h0 : kFactsSuProjTv hF d c 0 = 1 := unitaryPlane_tv_zero_any hF hci
  have h1 : kFactsSuProjTv hF d c 1 = kFactsSuProjTv hF d c 0 := by rw [h, h0]
  exact one_ne_zero (kFacts_suProjTv_injective hF hc0 hci
    (by rw [map_one]; exact CharTwo.add_self_eq_zero 1) (by simp) h1)

private theorem unitaryPlane_S0_range {d : ℕ} {a b : Fin d → F}
    (hF : Nat.card F = (2 ^ f) ^ 2) (hd : 3 ≤ d) (ha : herm (unitaryInvolution F 2 f) a a = 0)
    (hb : herm (unitaryInvolution F 2 f) b b = 0)
    (hab : herm (unitaryInvolution F 2 f) a b = 1)
    {A : Matrix.SpecialLinearGroup (Fin 2) (fixSub (unitaryInvolution F 2 f))}
    (hA : unitaryPlane_Phi hF ha hb hab A ∈ unitaryPlane_S0 hF) :
    ∃ v : Fin 2 → fixSub (unitaryInvolution F 2 f), v ≠ 0 ∧
      unitaryPlane_Phi hF ha hb hab A =
        kFactsSuProjTv hF d ((v 0 : F) • a + (v 1 : F) • b) 1 := by
  obtain ⟨c, hc0, hci, hcA⟩ := hA
  have hsq : unitaryPlane_Phi hF ha hb hab (A * A) = 1 := by
    rw [map_mul, hcA, unitaryPlane_tv_sq hF hci]
  have hAA : A * A = 1 := unitaryPlane_Phi_injective hF hd ha hb hab (by rw [hsq, map_one])
  by_cases hA1 : A = 1
  · rw [hA1, map_one] at hcA
    exact absurd hcA.symm (unitaryPlane_tv_ne_one hF hc0 hci)
  · exact unitaryPlane_involution_eq_tv hF ha hb hab hA1 hAA

private theorem unitaryPlane_mem_range_S0 {d : ℕ} {a b : Fin d → F}
    (hF : Nat.card F = (2 ^ f) ^ 2) (hd : 3 ≤ d)
    (ha : herm (unitaryInvolution F 2 f) a a = 0)
    (hb : herm (unitaryInvolution F 2 f) b b = 0)
    (hab : herm (unitaryInvolution F 2 f) a b = 1)
    {z : StatedProj (StatedSU d (2 ^ f) F)}
    (hzS : z ∈ unitaryPlane_S0 hF) (hzR : z ∈ (unitaryPlane_Phi hF ha hb hab).range) :
    ∃ v : Fin 2 → fixSub (unitaryInvolution F 2 f), v ≠ 0 ∧
      z = kFactsSuProjTv hF d ((v 0 : F) • a + (v 1 : F) • b) 1 := by
  obtain ⟨A, rfl⟩ := hzR
  exact unitaryPlane_S0_range hF hd ha hb hab hzS

private theorem unitaryPlane_transport_closure {d : ℕ} {a b : Fin d → F}
    (hF : Nat.card F = (2 ^ f) ^ 2) (hd : 3 ≤ d)
    (ha : herm (unitaryInvolution F 2 f) a a = 0)
    (hb : herm (unitaryInvolution F 2 f) b b = 0)
    (hab : herm (unitaryInvolution F 2 f) a b = 1)
    {X : Type} [Group X] (φ : X ≃* StatedProj (StatedSU d (2 ^ f) F))
    {S : Set X} (hclass : φ '' S = unitaryPlane_S0 hF)
    {K0 : Subgroup X}
    (hK0 : K0 = (unitaryPlane_Phi hF ha hb hab).range.map φ.symm.toMonoidHom) :
    ∀ x ∈ S, x ∈ K0 → ∀ y ∈ S, y ∈ K0 → ¬ Commute x y →
      Subgroup.closure (insert y (Vmem S x)) = K0 := by
  intro x hxS hxK y hyS hyK hnc
  rw [hK0] at hxK hyK
  have hx' : φ x ∈ unitaryPlane_S0 hF := by
    rw [← hclass]; exact Set.mem_image_of_mem φ hxS
  have hy' : φ y ∈ unitaryPlane_S0 hF := by
    rw [← hclass]; exact Set.mem_image_of_mem φ hyS
  have hxpl : φ x ∈ (unitaryPlane_Phi hF ha hb hab).range := by
    obtain ⟨z, hz, hzx⟩ := Subgroup.mem_map.mp hxK
    rw [← hzx]; simpa using hz
  have hypl : φ y ∈ (unitaryPlane_Phi hF ha hb hab).range := by
    obtain ⟨z, hz, hzy⟩ := Subgroup.mem_map.mp hyK
    rw [← hzy]; simpa using hz
  have hnc' : ¬ Commute (φ x) (φ y) := by
    intro h
    exact hnc (by simpa using h.map φ.symm.toMonoidHom)
  obtain ⟨v, hv0, hvx⟩ := unitaryPlane_mem_range_S0 hF hd ha hb hab hx' hxpl
  obtain ⟨w, hw0, hwy⟩ := unitaryPlane_mem_range_S0 hF hd ha hb hab hy' hypl
  have hs1 : (1 : F) + (unitaryInvolution F 2 f) 1 = 0 := by
    rw [map_one]; exact CharTwo.add_self_eq_zero 1
  have hne : herm (unitaryInvolution F 2 f) ((v 0 : F) • a + (v 1 : F) • b)
      ((w 0 : F) • a + (w 1 : F) • b) ≠ 0 := by
    intro h0
    apply hnc'
    rw [hvx, hwy]
    exact (commute_kFactsSuProjTv_iff hF
      (unitaryPlane_plane_ne_zero hF ha hb hab hv0)
      (unitaryPlane_herm_plane_self hF ha hb hab (v 0) (v 1))
      (unitaryPlane_plane_ne_zero hF ha hb hab hw0)
      (unitaryPlane_herm_plane_self hF ha hb hab (w 0) (w 1)) one_ne_zero hs1
      one_ne_zero hs1).mpr h0
  have hpl := unitaryPlane_closure_eq hF ha hb hab hv0 hw0 hne
  rw [← hvx, ← hwy] at hpl
  have h1 : Subgroup.map φ.toMonoidHom (Subgroup.closure (insert y (Vmem S x))) =
      (unitaryPlane_Phi hF ha hb hab).range := by
    change Subgroup.map (φ : X →* StatedProj (StatedSU d (2 ^ f) F))
      (Subgroup.closure (insert y (Vmem S x))) = _
    rw [CFSG.Fischer.map_closure_image φ, Set.image_insert_eq,
      ← Vmem_image_mulEquiv φ S x, hclass, hpl]
  have h2 : Subgroup.map φ.toMonoidHom K0 = (unitaryPlane_Phi hF ha hb hab).range := by
    rw [hK0, Subgroup.map_map]
    have hid : φ.toMonoidHom.comp φ.symm.toMonoidHom = MonoidHom.id _ := by
      ext z; simp
    rw [hid, Subgroup.map_id]
  exact Subgroup.map_injective (f := φ.toMonoidHom) φ.injective (h1.trans h2.symm)

private theorem unitaryPlane_transport_conj {d : ℕ} {a b : Fin d → F}
    (hF : Nat.card F = (2 ^ f) ^ 2) (hd : 3 ≤ d)
    (ha : herm (unitaryInvolution F 2 f) a a = 0)
    (hb : herm (unitaryInvolution F 2 f) b b = 0)
    (hab : herm (unitaryInvolution F 2 f) a b = 1)
    {X : Type} [Group X] (φ : X ≃* StatedProj (StatedSU d (2 ^ f) F))
    {S : Set X} (hclass : φ '' S = unitaryPlane_S0 hF)
    {K0 : Subgroup X}
    (hK0 : K0 = (unitaryPlane_Phi hF ha hb hab).range.map φ.symm.toMonoidHom) :
    ∀ x ∈ S, x ∈ K0 → ∀ y ∈ S, y ∈ K0 → ∃ g ∈ K0, g * x * g⁻¹ = y := by
  intro x hxS hxK y hyS hyK
  rw [hK0] at hxK hyK ⊢
  have hx' : φ x ∈ unitaryPlane_S0 hF := by
    rw [← hclass]; exact Set.mem_image_of_mem φ hxS
  have hy' : φ y ∈ unitaryPlane_S0 hF := by
    rw [← hclass]; exact Set.mem_image_of_mem φ hyS
  have hxpl : φ x ∈ (unitaryPlane_Phi hF ha hb hab).range := by
    obtain ⟨z, hz, hzx⟩ := Subgroup.mem_map.mp hxK
    rw [← hzx]; simpa using hz
  have hypl : φ y ∈ (unitaryPlane_Phi hF ha hb hab).range := by
    obtain ⟨z, hz, hzy⟩ := Subgroup.mem_map.mp hyK
    rw [← hzy]; simpa using hz
  obtain ⟨v, hv0, hvx⟩ := unitaryPlane_mem_range_S0 hF hd ha hb hab hx' hxpl
  obtain ⟨w, hw0, hwy⟩ := unitaryPlane_mem_range_S0 hF hd ha hb hab hy' hypl
  obtain ⟨g', hg'pl, hg'⟩ := unitaryPlane_transitive hF ha hb hab hv0 hw0
  rw [← hvx, ← hwy] at hg'
  refine ⟨φ.symm g', Subgroup.mem_map.mpr ⟨g', hg'pl, rfl⟩, ?_⟩
  apply φ.injective
  rw [map_mul, map_mul, map_inv, φ.apply_symm_apply]
  exact hg'

private theorem unitaryPlane_transport_order {d : ℕ} {a b : Fin d → F}
    (hF : Nat.card F = (2 ^ f) ^ 2) (hd : 3 ≤ d)
    (ha : herm (unitaryInvolution F 2 f) a a = 0)
    (hb : herm (unitaryInvolution F 2 f) b b = 0)
    (hab : herm (unitaryInvolution F 2 f) a b = 1)
    {X : Type} [Group X] (φ : X ≃* StatedProj (StatedSU d (2 ^ f) F))
    {S : Set X} (hclass' : φ.symm '' unitaryPlane_S0 hF = S)
    {K0 : Subgroup X}
    (hK0 : K0 = (unitaryPlane_Phi hF ha hb hab).range.map φ.symm.toMonoidHom) :
    ∃ x ∈ S, x ∈ K0 ∧ ∃ y ∈ S, y ∈ K0 ∧ orderOf (x * y) = 2 ^ f + 1 := by
  obtain ⟨x', hx'S, hx'pl, y', hy'S, hy'pl, hord⟩ :=
    unitaryPlane_exists_orderOf_mul hF hd ha hb hab
  rw [hK0]
  refine ⟨φ.symm x', ?_, Subgroup.mem_map.mpr ⟨x', hx'pl, rfl⟩,
    φ.symm y', ?_, Subgroup.mem_map.mpr ⟨y', hy'pl, rfl⟩, ?_⟩
  · rw [← hclass']; exact Set.mem_image_of_mem φ.symm hx'S
  · rw [← hclass']; exact Set.mem_image_of_mem φ.symm hy'S
  · have h1 : orderOf (φ.symm x' * φ.symm y') = orderOf (x' * y') := by
      rw [← map_mul]
      exact orderOf_injective (f := φ.symm.toMonoidHom) φ.symm.injective (x' * y')
    rw [h1, hord]

theorem exists_subgroup_of_isUnitaryTransvection {X : Type} [Group X]
    (hZ : Subgroup.center X = ⊥) {s : X} {d f : ℕ} (hd : 3 ≤ d)
    (hs : IsUnitaryTransvection X d f s) :
    ∃ K0 : Subgroup X,
      (∀ x ∈ {x | IsConj s x}, x ∈ K0 → ∀ y ∈ {x | IsConj s x}, y ∈ K0 → ¬ Commute x y →
        Subgroup.closure (insert y (Vmem {x | IsConj s x} x)) = K0) ∧
      (∀ x ∈ {x | IsConj s x}, x ∈ K0 → ∀ y ∈ {x | IsConj s x}, y ∈ K0 →
        ∃ g ∈ K0, g * x * g⁻¹ = y) ∧
      ∃ x ∈ {x | IsConj s x}, x ∈ K0 ∧ ∃ y ∈ {x | IsConj s x}, y ∈ K0 ∧
        orderOf (x * y) = 2 ^ f + 1 := by
  obtain ⟨K, hKfield, hKfinite, hKchar, hK, φ, e₀, he₀0, he₀, hφs⟩ :=
    exists_mulEquiv_of_isUnitaryTransvection hZ hs
  letI : Field K := hKfield
  letI : Finite K := hKfinite
  letI : CharP K 2 := hKchar
  obtain ⟨b, hb, hab⟩ := exists_partner (isUnitaryInvolution_unitaryInvolution hK) he₀0 he₀
  have hclass : φ '' {x | IsConj s x} = unitaryPlane_S0 hK := by
    rw [CFSG.Fischer.image_setOf_isConj φ s, hφs,
      setOf_isConj_kFactsSuProjTv hK hd he₀0 he₀]
    rfl
  have hclass' : φ.symm '' unitaryPlane_S0 hK = {x | IsConj s x} := by
    rw [← hclass, CFSG.Fischer.image_symm_image]
  exact ⟨_, unitaryPlane_transport_closure hK hd he₀ hb hab φ hclass rfl,
    unitaryPlane_transport_conj hK hd he₀ hb hab φ hclass rfl,
    unitaryPlane_transport_order hK hd he₀ hb hab φ hclass' rfl⟩

end CFSG.OddTranspositions.PartFour
