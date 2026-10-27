module

public import CFSG.ClassicalGroups.Orthogonal.StatedOmegaElementary
public import CFSG.ClassicalGroups.Orthogonal.MinusSplitTorus
public import CFSG.ClassicalGroups.Alternating.TransvectionGeneration
public import CFSG.RankThree.GF2n.Smith81.OrthRootBack
public import CFSG.CGT.PushingUpLit.CGT6X.ExtCocycle
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightF8Nat
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Sixteen4FNtOmegaBigCocycle

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.ClassicalGroups.Orthogonal CFSG.Open CFSG.CGT.PushingUpLit.CGT6X
open CFSG.LieType.Universal.Spin
open CFSG.RankThree.PartTwo.Sec19.Census194.RonanC194.OmegaEven
open QuadraticMap
open scoped Matrix

variable {K : Type} [Field K]

private abbrev SixV (K : Type) : Type := Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → K

private abbrev SixN (K : Type) : Type := Multiplicative (SixV K)

private noncomputable def sixQ (b d : K) : QuadraticForm K (SixV K) :=
  quadMinus 3 K b d

private noncomputable def sixPair (b d : K) : HypPair (sixQ b d) :=
  minusPair (n := 3) K b d (⟨0, by omega⟩ : Fin (3 - 1))

private noncomputable def sixPair2 (b d : K) : HypPair (sixQ b d) :=
  minusPair (n := 3) K b d (⟨1, by omega⟩ : Fin (3 - 1))

private noncomputable def sixX (b d : K) : SixV K := (sixPair b d).e

private noncomputable def sixY (b d : K) : SixV K := (sixPair b d).f

private noncomputable def sixX2 (b d : K) : SixV K := (sixPair2 b d).e

private noncomputable def sixY2 (b d : K) : SixV K := (sixPair2 b d).f

private noncomputable def sixU (b d : K) : Submodule K (SixV K) :=
  (sixPair b d).perp

private theorem sixPair_orth (b d : K) : (sixPair b d).Orth (sixPair2 b d) :=
  minusPair_orth (n := 3) (K := K) (b := b) (c := d) (by decide)

private theorem sixQ_x (b d : K) : sixQ b d (sixX b d) = 0 :=
  (sixPair b d).Q_e

private theorem sixQ_y (b d : K) : sixQ b d (sixY b d) = 0 :=
  (sixPair b d).Q_f

private theorem sixQ_x2 (b d : K) : sixQ b d (sixX2 b d) = 0 :=
  (sixPair2 b d).Q_e

private theorem sixQ_y2 (b d : K) : sixQ b d (sixY2 b d) = 0 :=
  (sixPair2 b d).Q_f

private theorem sixB_xy (b d : K) : polar (sixQ b d) (sixX b d) (sixY b d) = 1 :=
  (sixPair b d).polar_ef

private theorem sixB_yx (b d : K) : polar (sixQ b d) (sixY b d) (sixX b d) = 1 := by
  rw [QuadraticMap.polar_comm, sixB_xy]

private theorem sixB_xx (b d : K) : polar (sixQ b d) (sixX b d) (sixX b d) = 0 :=
  polar_self_eq_zero (sixQ_x b d)

private theorem sixB_yy (b d : K) : polar (sixQ b d) (sixY b d) (sixY b d) = 0 :=
  polar_self_eq_zero (sixQ_y b d)

private theorem sixB_x2y2 (b d : K) : polar (sixQ b d) (sixX2 b d) (sixY2 b d) = 1 :=
  (sixPair2 b d).polar_ef

private theorem sixX2_mem_U (b d : K) : sixX2 b d ∈ sixU b d := by
  rw [sixU, HypPair.mem_perp]
  have h := sixPair_orth b d
  exact ⟨h.ee, h.fe⟩

private theorem sixY2_mem_U (b d : K) : sixY2 b d ∈ sixU b d := by
  rw [sixU, HypPair.mem_perp]
  have h := sixPair_orth b d
  exact ⟨h.ef, h.ff⟩

private theorem sixX2_ne_zero (b d : K) : sixX2 b d ≠ 0 := by
  intro h
  have h1 := sixB_x2y2 b d
  rw [h, QuadraticMap.polar_zero_left] at h1
  exact zero_ne_one h1

variable [Finite K] [CharP K 2]

omit [CharP K 2] in
private theorem sixQ_nondegenerate (b d : K)
    (hirr : ∀ s : K, s ^ 2 + b * s + d ≠ 0) :
    (polarBilin (sixQ b d)).Nondegenerate :=
  nondegenerate_polarBilin_quadMinus_of_finite 3 K hirr

omit [CharP K 2] in
private theorem sixU_nondegenerate (b d : K)
    (hirr : ∀ s : K, s ^ 2 + b * s + d ≠ 0) :
    (polarBilin ((sixQ b d).restrict (sixU b d))).Nondegenerate :=
  nondegenerate_polarBilin_restrict
    ((sixPair b d).polarNondegOn_perp (sixQ_nondegenerate b d hirr))

private theorem sixU_span_singular (b d : K)
    (hirr : ∀ s : K, s ^ 2 + b * s + d ≠ 0) :
    Submodule.span K {v : sixU b d | (sixQ b d).restrict (sixU b d) v = 0} = ⊤ :=
  CFSG.RankThree.GF2n.Smith81.orthRoot_span_singular ((sixQ b d).restrict (sixU b d)) (sixU_nondegenerate b d hirr)
    (e := ⟨sixX2 b d, sixX2_mem_U b d⟩)
    (by
      intro h
      exact sixX2_ne_zero b d (congrArg Subtype.val h))
    (sixQ_x2 b d)

private noncomputable def sixCoeffX (b d : K) (v : SixV K) : K :=
  polar (sixQ b d) v (sixY b d)

private noncomputable def sixCoeffY (b d : K) (v : SixV K) : K :=
  polar (sixQ b d) v (sixX b d)

private noncomputable def sixProj (b d : K) (v : SixV K) : SixV K :=
  v - sixCoeffX b d v • sixX b d - sixCoeffY b d v • sixY b d

omit [Finite K] [CharP K 2] in
private theorem sixCoeffX_x (b d : K) : sixCoeffX b d (sixX b d) = 1 :=
  sixB_xy b d

omit [Finite K] [CharP K 2] in
private theorem sixCoeffX_y (b d : K) : sixCoeffX b d (sixY b d) = 0 :=
  sixB_yy b d

omit [Finite K] [CharP K 2] in
private theorem sixCoeffY_x (b d : K) : sixCoeffY b d (sixX b d) = 0 :=
  sixB_xx b d

omit [Finite K] [CharP K 2] in
private theorem sixCoeffY_y (b d : K) : sixCoeffY b d (sixY b d) = 1 :=
  sixB_yx b d

omit [Finite K] [CharP K 2] in
private theorem sixProj_x (b d : K) : sixProj b d (sixX b d) = 0 := by
  rw [sixProj, sixCoeffX_x, sixCoeffY_x]
  simp

omit [Finite K] [CharP K 2] in
private theorem sixProj_y (b d : K) : sixProj b d (sixY b d) = 0 := by
  rw [sixProj, sixCoeffX_y, sixCoeffY_y]
  simp

omit [Finite K] [CharP K 2] in
private theorem sixCoeffX_of_mem_U (b d : K) {v : SixV K} (hv : v ∈ sixU b d) :
    sixCoeffX b d v = 0 := by
  rw [sixCoeffX, QuadraticMap.polar_comm]
  exact (HypPair.mem_perp.mp hv).2

omit [Finite K] [CharP K 2] in
private theorem sixCoeffY_of_mem_U (b d : K) {v : SixV K} (hv : v ∈ sixU b d) :
    sixCoeffY b d v = 0 := by
  rw [sixCoeffY, QuadraticMap.polar_comm]
  exact (HypPair.mem_perp.mp hv).1

omit [Finite K] [CharP K 2] in
private theorem sixProj_of_mem_U (b d : K) {v : SixV K} (hv : v ∈ sixU b d) :
    sixProj b d v = v := by
  rw [sixProj, sixCoeffX_of_mem_U b d hv, sixCoeffY_of_mem_U b d hv]
  simp

omit [Finite K] [CharP K 2] in
private theorem sixProj_mem_U (b d : K) (v : SixV K) : sixProj b d v ∈ sixU b d := by
  simpa only [sixProj, sixCoeffX, sixCoeffY, sixX, sixY, sixU, HypPair.proj] using
    (sixPair b d).proj_mem_perp v

omit [Finite K] [CharP K 2] in
private theorem six_decomp (b d : K) (v : SixV K) :
    v = sixCoeffX b d v • sixX b d + sixCoeffY b d v • sixY b d + sixProj b d v := by
  simpa only [sixProj, sixCoeffX, sixCoeffY, sixX, sixY, HypPair.proj] using
    (sixPair b d).eq_add_proj v

omit [Finite K] [CharP K 2] in
private theorem sixProj_add (b d : K) (v w : SixV K) :
    sixProj b d (v + w) = sixProj b d v + sixProj b d w := by
  rw [sixProj, sixProj, sixProj, sixCoeffX, sixCoeffY, sixCoeffX, sixCoeffY, sixCoeffX,
    sixCoeffY, QuadraticMap.polar_add_left, QuadraticMap.polar_add_left, add_smul, add_smul]
  abel

omit [Finite K] [CharP K 2] in
private theorem sixProj_smul (b d : K) (a : K) (v : SixV K) :
    sixProj b d (a • v) = a • sixProj b d v := by
  rw [sixProj, sixProj, sixCoeffX, sixCoeffY, sixCoeffX, sixCoeffY,
    QuadraticMap.polar_smul_left, QuadraticMap.polar_smul_left, smul_sub, smul_sub,
    smul_smul, smul_smul]
  module

private noncomputable def sixProjLM (b d : K) : SixV K →ₗ[K] SixV K where
  toFun := sixProj b d
  map_add' := sixProj_add b d
  map_smul' := sixProj_smul b d

private noncomputable def sixT (b d : K) (u : sixU b d) :
    ↥(elementaryGroup (sixQ b d)) :=
  ⟨eichler (sixQ b d) (sixX b d) (u : SixV K),
    eichler_mem_elementaryGroup (sixQ b d) (sixX b d) (u : SixV K)⟩

private noncomputable def sixR (b d : K) (u : sixU b d) :
    ↥(elementaryGroup (sixQ b d)) :=
  ⟨eichler (sixQ b d) (sixY b d) (u : SixV K),
    eichler_mem_elementaryGroup (sixQ b d) (sixY b d) (u : SixV K)⟩

omit [Finite K] [CharP K 2] in
private theorem sixT_coe (b d : K) (u : sixU b d) :
    (sixT b d u : SixV K ≃ₗ[K] SixV K) =
      eichler (sixQ b d) (sixX b d) (u : SixV K) := rfl

omit [Finite K] [CharP K 2] in
private theorem sixR_coe (b d : K) (u : sixU b d) :
    (sixR b d u : SixV K ≃ₗ[K] SixV K) =
      eichler (sixQ b d) (sixY b d) (u : SixV K) := rfl

omit [Finite K] [CharP K 2] in
private theorem sixT_x (b d : K) (u : sixU b d) :
    (sixT b d u : SixV K ≃ₗ[K] SixV K) (sixX b d) = sixX b d :=
  eichler_apply_self (sixX b d) (u : SixV K)

omit [Finite K] [CharP K 2] in
private theorem sixB_x_u (b d : K) (u : sixU b d) :
    polar (sixQ b d) (sixX b d) (u : SixV K) = 0 :=
  (HypPair.mem_perp.mp u.2).1

omit [Finite K] [CharP K 2] in
private theorem sixB_y_u (b d : K) (u : sixU b d) :
    polar (sixQ b d) (sixY b d) (u : SixV K) = 0 :=
  (HypPair.mem_perp.mp u.2).2

omit [Finite K] [CharP K 2] in
private theorem sixB_u_x (b d : K) (u : sixU b d) :
    polar (sixQ b d) (u : SixV K) (sixX b d) = 0 := by
  rw [QuadraticMap.polar_comm]
  exact sixB_x_u b d u

omit [Finite K] [CharP K 2] in
private theorem sixB_u_y (b d : K) (u : sixU b d) :
    polar (sixQ b d) (u : SixV K) (sixY b d) = 0 := by
  rw [QuadraticMap.polar_comm]
  exact sixB_y_u b d u

omit [Finite K] in
private theorem sixT_y (b d : K) (u : sixU b d) :
    (sixT b d u : SixV K ≃ₗ[K] SixV K) (sixY b d) =
      sixY b d + (u : SixV K) + sixQ b d (u : SixV K) • sixX b d := by
  rw [sixT_coe, eichler_apply (sixQ_x b d) (sixB_x_u b d u), sixB_yx]
  change sixY b d + 1 • (u : SixV K) -
      (polar (sixQ b d) (sixY b d) (u : SixV K) +
        sixQ b d (u : SixV K) * 1) • sixX b d =
    sixY b d + (u : SixV K) + sixQ b d (u : SixV K) • sixX b d
  rw [sixB_y_u b d u]
  simp only [one_smul]
  rw [CharTwo.sub_eq_add]
  simp

omit [Finite K] in
private theorem sixT_U (b d : K) (u v : sixU b d) :
    (sixT b d u : SixV K ≃ₗ[K] SixV K) (v : SixV K) =
      (v : SixV K) + polar (sixQ b d) (u : SixV K) (v : SixV K) • sixX b d := by
  rw [sixT_coe, eichler_apply (sixQ_x b d) (sixB_x_u b d u)]
  rw [sixB_u_x b d v]
  have hvu : polar (sixQ b d) (v : SixV K) (u : SixV K) =
      polar (sixQ b d) (u : SixV K) (v : SixV K) :=
    QuadraticMap.polar_comm (sixQ b d) (v : SixV K) (u : SixV K)
  rw [hvu]
  simp only [zero_smul, add_zero]
  rw [CharTwo.sub_eq_add]
  simp

omit [Finite K] [CharP K 2] in
private theorem sixR_y (b d : K) (u : sixU b d) :
    (sixR b d u : SixV K ≃ₗ[K] SixV K) (sixY b d) = sixY b d :=
  eichler_apply_self (sixY b d) (u : SixV K)

omit [Finite K] in
private theorem sixR_x (b d : K) (u : sixU b d) :
    (sixR b d u : SixV K ≃ₗ[K] SixV K) (sixX b d) =
      sixX b d + (u : SixV K) + sixQ b d (u : SixV K) • sixY b d := by
  rw [sixR_coe, eichler_apply (sixQ_y b d) (sixB_y_u b d u), sixB_xy]
  change sixX b d + 1 • (u : SixV K) -
      (polar (sixQ b d) (sixX b d) (u : SixV K) +
        sixQ b d (u : SixV K) * 1) • sixY b d =
    sixX b d + (u : SixV K) + sixQ b d (u : SixV K) • sixY b d
  rw [sixB_x_u b d u]
  simp only [one_smul]
  rw [CharTwo.sub_eq_add]
  simp

omit [Finite K] in
private theorem sixR_U (b d : K) (u v : sixU b d) :
    (sixR b d u : SixV K ≃ₗ[K] SixV K) (v : SixV K) =
      (v : SixV K) + polar (sixQ b d) (u : SixV K) (v : SixV K) • sixY b d := by
  rw [sixR_coe, eichler_apply (sixQ_y b d) (sixB_y_u b d u)]
  rw [sixB_u_y b d v]
  have hvu : polar (sixQ b d) (v : SixV K) (u : SixV K) =
      polar (sixQ b d) (u : SixV K) (v : SixV K) :=
    QuadraticMap.polar_comm (sixQ b d) (v : SixV K) (u : SixV K)
  rw [hvu]
  simp only [zero_smul, add_zero]
  rw [CharTwo.sub_eq_add]
  simp

omit [Finite K] [CharP K 2] in
private theorem sixT_add (b d : K) (u v : sixU b d) :
    sixT b d (u + v) = sixT b d u * sixT b d v := by
  apply Subtype.ext
  exact (eichler_mul (HypPair.mem_perp.mp u.2).1 (HypPair.mem_perp.mp v.2).1).symm

omit [Finite K] [CharP K 2] in
private theorem sixR_add (b d : K) (u v : sixU b d) :
    sixR b d (u + v) = sixR b d u * sixR b d v := by
  apply Subtype.ext
  exact (eichler_mul (HypPair.mem_perp.mp u.2).2 (HypPair.mem_perp.mp v.2).2).symm

omit [Finite K] in
private theorem sixT_decomp_apply (b d : K) (u : sixU b d) (a c : K) (w : sixU b d) :
    (sixT b d u : SixV K ≃ₗ[K] SixV K)
        (a • sixX b d + c • sixY b d + (w : SixV K)) =
      (a + c * sixQ b d (u : SixV K) +
          polar (sixQ b d) (u : SixV K) (w : SixV K)) • sixX b d +
        c • sixY b d + ((w : SixV K) + c • (u : SixV K)) := by
  rw [map_add, map_add, map_smul, map_smul, sixT_x, sixT_y, sixT_U]
  module

omit [Finite K] in
private theorem sixR_decomp_apply (b d : K) (u : sixU b d) (a c : K) (w : sixU b d) :
    (sixR b d u : SixV K ≃ₗ[K] SixV K)
        (a • sixX b d + c • sixY b d + (w : SixV K)) =
      a • sixX b d +
        (c + a * sixQ b d (u : SixV K) +
          polar (sixQ b d) (u : SixV K) (w : SixV K)) • sixY b d +
        ((w : SixV K) + a • (u : SixV K)) := by
  rw [map_add, map_add, map_smul, map_smul, sixR_x, sixR_y, sixR_U]
  module

private noncomputable def sixSigma (b d : K)
    (g : ↥(elementaryGroup (sixQ b d))) : MulAut (SixN K) where
  toFun m := Multiplicative.ofAdd
    ((g : SixV K ≃ₗ[K] SixV K) (Multiplicative.toAdd m))
  invFun m := Multiplicative.ofAdd
    ((g : SixV K ≃ₗ[K] SixV K).symm (Multiplicative.toAdd m))
  left_inv m := by
    show Multiplicative.ofAdd
      ((g : SixV K ≃ₗ[K] SixV K).symm
        ((g : SixV K ≃ₗ[K] SixV K) (Multiplicative.toAdd m))) = m
    rw [LinearEquiv.symm_apply_apply]
    rfl
  right_inv m := by
    show Multiplicative.ofAdd
      ((g : SixV K ≃ₗ[K] SixV K)
        ((g : SixV K ≃ₗ[K] SixV K).symm (Multiplicative.toAdd m))) = m
    rw [LinearEquiv.apply_symm_apply]
    rfl
  map_mul' m n := by
    show Multiplicative.ofAdd
      ((g : SixV K ≃ₗ[K] SixV K) (Multiplicative.toAdd (m * n))) =
        Multiplicative.ofAdd ((g : SixV K ≃ₗ[K] SixV K) (Multiplicative.toAdd m)) *
          Multiplicative.ofAdd ((g : SixV K ≃ₗ[K] SixV K) (Multiplicative.toAdd n))
    rw [toAdd_mul, map_add]
    exact ofAdd_add _ _

private noncomputable def sixSigmaHom (b d : K) :
    ↥(elementaryGroup (sixQ b d)) →* MulAut (SixN K) where
  toFun := sixSigma b d
  map_one' := by
    refine MulEquiv.ext fun m => ?_
    change Multiplicative.ofAdd
      ((1 : SixV K ≃ₗ[K] SixV K) (Multiplicative.toAdd m)) = m
    rfl
  map_mul' g h := by
    refine MulEquiv.ext fun m => ?_
    change Multiplicative.ofAdd
      (((g * h : ↥(elementaryGroup (sixQ b d))) : SixV K ≃ₗ[K] SixV K)
        (Multiplicative.toAdd m)) =
        Multiplicative.ofAdd
          ((g : SixV K ≃ₗ[K] SixV K)
            ((h : SixV K ≃ₗ[K] SixV K) (Multiplicative.toAdd m)))
    rfl

omit [Finite K] [CharP K 2] in
private theorem sixSigmaHom_apply (b d : K)
    (g : ↥(elementaryGroup (sixQ b d))) (m : SixN K) :
    sixSigmaHom b d g m = Multiplicative.ofAdd
      ((g : SixV K ≃ₗ[K] SixV K) (Multiplicative.toAdd m)) := rfl

omit [Finite K] [CharP K 2] in
private theorem six_toAdd_cocycle (b d : K) {c : ↥(elementaryGroup (sixQ b d)) → SixN K}
    (hc : IsCocycle (sixSigmaHom b d) c)
    (g h : ↥(elementaryGroup (sixQ b d))) :
    Multiplicative.toAdd (c (g * h)) =
      Multiplicative.toAdd (c g) +
        (g : SixV K ≃ₗ[K] SixV K) (Multiplicative.toAdd (c h)) := by
  rw [hc g h, toAdd_mul, sixSigmaHom_apply, toAdd_ofAdd]

omit [Finite K] [CharP K 2] in
private theorem six_toAdd_mem_Z1A (b d : K)
    {c : ↥(elementaryGroup (sixQ b d)) → SixN K}
    (hc : IsCocycle (sixSigmaHom b d) c) :
    (fun g => Multiplicative.toAdd (c g)) ∈
      CFSG.Quasithin.JonesParshall.Z1A (w183ElemAct (sixQ b d)) := by
  intro g h
  simpa only [w183ElemAct_apply] using six_toAdd_cocycle b d hc g h

omit [Finite K] in
private theorem sixN_sq (v : SixN K) : v ^ 2 = 1 := by
  apply Multiplicative.toAdd.injective
  rw [toAdd_pow, toAdd_one]
  simpa using CharTwo.two_nsmul (Multiplicative.toAdd v)

omit [Finite K] [CharP K 2] in
private theorem sixX_eq (b d : K) :
    sixX b d = Pi.single (Sum.inl (0 : Fin (3 - 1))) (1 : K) :=
  minusPair_e (n := 3) (K := K) (b := b) (c := d) (i := ⟨0, by omega⟩)

omit [Finite K] [CharP K 2] in
private theorem sixY_eq (b d : K) :
    sixY b d = Pi.single (Sum.inr (Sum.inl (0 : Fin (3 - 1)))) (1 : K) :=
  minusPair_f (n := 3) (K := K) (b := b) (c := d) (i := ⟨0, by omega⟩)

omit [Finite K] in
private theorem six_card_K_even : Even (Nat.card K) := by
  have h2 : AddMonoid.exponent K = 2 := by
    rw [← ringChar_eq_addMonoidExponent, ringChar.eq K 2]
  have hdvd : 2 ∣ Nat.card K := by
    rw [← h2]
    exact AddGroup.exponent_dvd_nat_card
  exact even_iff_two_dvd.mpr hdvd

omit [Finite K] in
private theorem six_card_units_odd (hK : 2 < Nat.card K) : Odd (Nat.card K - 1) := by
  obtain ⟨k, hk⟩ := six_card_K_even (K := K)
  refine ⟨k - 1, by omega⟩

omit [Finite K] in
private theorem six_card_units_odd' (hK : 2 < Nat.card K) : Odd (Nat.card Kˣ) := by
  rw [Nat.card_units K]
  exact six_card_units_odd hK

omit [CharP K 2] [Finite K] in
private theorem six_pow_card_units (a : Kˣ) : a ^ (Nat.card K - 1) = 1 := by
  rw [← Nat.card_units K]
  exact pow_card_eq_one'

private noncomputable def sixDiag (b d : K) (hK : 2 < Nat.card K) (a : Kˣ) :
    StatedOmega (StatedQuadMinus 3 K b d) :=
  minusDiagGL (n := 3) (b := b) (c := d) (r := Nat.card K - 1)
    (six_card_units_odd hK) (Pi.mulSingle (0 : Fin (3 - 1)) a) (by
      intro j
      fin_cases j
      · simpa [Pi.mulSingle] using six_pow_card_units a
      · simp [Pi.mulSingle])

private noncomputable def sixDiagHom (b d : K) (hK : 2 < Nat.card K) :
    Kˣ →* StatedOmega (StatedQuadMinus 3 K b d) where
  toFun := sixDiag b d hK
  map_one' := by
    apply Subtype.ext
    change ((sixDiag b d hK (1 : Kˣ) : StatedOmega (StatedQuadMinus 3 K b d)) :
      GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) K) = 1
    rw [sixDiag, coe_minusDiagGL]
    have h1 : (Pi.mulSingle (0 : Fin (3 - 1)) (1 : Kˣ) : Fin (3 - 1) → Kˣ) = 1 := by
      funext j
      fin_cases j <;> simp
    rw [h1]
    simp
  map_mul' a a' := by
    apply Subtype.ext
    change ((sixDiag b d hK (a * a') : StatedOmega (StatedQuadMinus 3 K b d)) :
      GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) K) =
      ((sixDiag b d hK a : StatedOmega (StatedQuadMinus 3 K b d)) :
        GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) K) *
      ((sixDiag b d hK a' : StatedOmega (StatedQuadMinus 3 K b d)) :
        GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) K)
    rw [sixDiag, sixDiag, sixDiag, coe_minusDiagGL, coe_minusDiagGL, coe_minusDiagGL,
      ← map_mul, ← map_mul]
    congr 1
    have hm : (Pi.mulSingle (0 : Fin (3 - 1)) (a * a') : Fin (3 - 1) → Kˣ) =
        Pi.mulSingle (0 : Fin (3 - 1)) a * Pi.mulSingle (0 : Fin (3 - 1)) a' := by
      funext j
      fin_cases j <;> simp
    rw [hm]

private noncomputable def sixS (b d : K) (hirr : ∀ s : K, s ^ 2 + b * s + d ≠ 0)
    (hK : 2 < Nat.card K) :
    Kˣ →* ↥(elementaryGroup (sixQ b d)) :=
  (statedOmegaMinusEquiv (m := 3) (by norm_num) hirr).toMonoidHom.comp
    (sixDiagHom b d hK)

private theorem sixS_apply (b d : K) (hirr : ∀ s : K, s ^ 2 + b * s + d ≠ 0)
    (hK : 2 < Nat.card K) (a : Kˣ) (v : SixV K) :
    (sixS b d hirr hK a : SixV K ≃ₗ[K] SixV K) v =
      (fun j => ((torusEntMinus 2 K (Pi.mulSingle (0 : Fin (3 - 1)) a) j : Kˣ) : K) *
        v j) := by
  rw [sixS]
  change (statedOmegaMinusEquiv (m := 3) (by norm_num) hirr
    (sixDiagHom b d hK a)).app v = _
  rw [statedOmegaMinusEquiv_app (m := 3) (by norm_num) hirr]
  change (((sixDiag b d hK a : StatedOmega (StatedQuadMinus 3 K b d)) : GL
    (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) K) : Matrix
      (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) K) *ᵥ v = _
  rw [sixDiag, coe_minusDiagGL, mulVec_diagGL]

private theorem sixS_x (b d : K) (hirr : ∀ s : K, s ^ 2 + b * s + d ≠ 0)
    (hK : 2 < Nat.card K) (a : Kˣ) :
    (sixS b d hirr hK a : SixV K ≃ₗ[K] SixV K) (sixX b d) = a • sixX b d := by
  rw [sixS_apply]
  ext j
  rw [sixX_eq]
  rcases j with i | i | k
  · fin_cases i <;> simp [Pi.mulSingle, torusEntMinus, Units.smul_def, smul_eq_mul]
  · fin_cases i <;> simp [Pi.mulSingle, torusEntMinus, Units.val_inv_eq_inv_val]
  · fin_cases k <;> simp [Pi.mulSingle, torusEntMinus]

private theorem sixS_y (b d : K) (hirr : ∀ s : K, s ^ 2 + b * s + d ≠ 0)
    (hK : 2 < Nat.card K) (a : Kˣ) :
    (sixS b d hirr hK a : SixV K ≃ₗ[K] SixV K) (sixY b d) = a⁻¹ • sixY b d := by
  rw [sixS_apply]
  ext j
  rw [sixY_eq]
  rcases j with i | i | k
  · fin_cases i <;> simp [Pi.mulSingle, torusEntMinus]
  · fin_cases i <;> simp [Pi.mulSingle, torusEntMinus, Units.val_inv_eq_inv_val, Units.smul_def, smul_eq_mul]
  · fin_cases k <;> simp [Pi.mulSingle, torusEntMinus]

private theorem sixS_U (b d : K) (hirr : ∀ s : K, s ^ 2 + b * s + d ≠ 0)
    (hK : 2 < Nat.card K) (a : Kˣ) (u : sixU b d) :
    (sixS b d hirr hK a : SixV K ≃ₗ[K] SixV K) (u : SixV K) = (u : SixV K) := by
  have h0 : (u : SixV K) (Sum.inl (0 : Fin (3 - 1))) = 0 := by
    rw [← polar_single_inr_quadMinus (n := 3) (b := b) (c := d) (0 : Fin (3 - 1))
      (u : SixV K)]
    have h := sixB_y_u b d u
    rwa [sixY_eq] at h
  have h1 : (u : SixV K) (Sum.inr (Sum.inl (0 : Fin (3 - 1)))) = 0 := by
    rw [← polar_single_inl_quadMinus (n := 3) (b := b) (c := d) (0 : Fin (3 - 1))
      (u : SixV K)]
    have h := sixB_x_u b d u
    rwa [sixX_eq] at h
  rw [sixS_apply]
  ext j
  rcases j with i | i | k
  · fin_cases i
    · simp [Pi.mulSingle, torusEntMinus, h0]
    · simp [Pi.mulSingle, torusEntMinus]
  · fin_cases i
    · simp [Pi.mulSingle, torusEntMinus, h1]
    · simp [Pi.mulSingle, torusEntMinus]
  · fin_cases k <;> simp [Pi.mulSingle, torusEntMinus]

private theorem sixS_decomp_apply (b d : K)
    (hirr : ∀ s : K, s ^ 2 + b * s + d ≠ 0) (hK : 2 < Nat.card K)
    (a : Kˣ) (a0 c : K) (w : sixU b d) :
    (sixS b d hirr hK a : SixV K ≃ₗ[K] SixV K)
        (a0 • sixX b d + c • sixY b d + (w : SixV K)) =
      ((a : K) * a0) • sixX b d + (((a : K)⁻¹) * c) • sixY b d + (w : SixV K) := by
  rw [map_add, map_add, map_smul, map_smul, sixS_x, sixS_y, sixS_U]
  simp only [Units.smul_def, Units.val_inv_eq_inv_val, smul_smul]
  module

private theorem six_torus_coboundary (b d : K)
    (hirr : ∀ s : K, s ^ 2 + b * s + d ≠ 0) (hK : 2 < Nat.card K)
    {c : ↥(elementaryGroup (sixQ b d)) → SixN K}
    (hc : IsCocycle (sixSigmaHom b d) c) :
    ∃ m : SixN K, ∀ a : Kˣ,
      c (sixS b d hirr hK a) = sixSigmaHom b d (sixS b d hirr hK a) m * m⁻¹ := by
  have hc' : IsCocycle ((sixSigmaHom b d).comp (sixS b d hirr hK))
      (fun a : Kˣ => c (sixS b d hirr hK a)) := by
    intro a a'
    simpa [map_mul] using hc (sixS b d hirr hK a) (sixS b d hirr hK a')
  exact coboundary_of_odd_card (ρ := (sixSigmaHom b d).comp (sixS b d hirr hK))
    (sixN_sq (K := K)) (six_card_units_odd' hK) hc'

private noncomputable def sixCoeffXLM (b d : K) : SixV K →ₗ[K] K where
  toFun := sixCoeffX b d
  map_add' := fun v w => QuadraticMap.polar_add_left (sixQ b d) v w (sixY b d)
  map_smul' := fun a v => QuadraticMap.polar_smul_left (sixQ b d) a v (sixY b d)

private noncomputable def sixCoeffYLM (b d : K) : SixV K →ₗ[K] K where
  toFun := sixCoeffY b d
  map_add' := fun v w => QuadraticMap.polar_add_left (sixQ b d) v w (sixX b d)
  map_smul' := fun a v => QuadraticMap.polar_smul_left (sixQ b d) a v (sixX b d)

omit [Finite K] [CharP K 2] in
private theorem sixCoeffXLM_apply (b d : K) (v : SixV K) :
    sixCoeffXLM b d v = sixCoeffX b d v := rfl

omit [Finite K] [CharP K 2] in
private theorem sixCoeffYLM_apply (b d : K) (v : SixV K) :
    sixCoeffYLM b d v = sixCoeffY b d v := rfl

omit [Finite K] [CharP K 2] in
private theorem sixProjLM_apply (b d : K) (v : SixV K) :
    sixProjLM b d v = sixProj b d v := rfl

private noncomputable def sixAlpha (b d : K)
    (c : ↥(elementaryGroup (sixQ b d)) → SixN K) (u : sixU b d) : K :=
  sixCoeffX b d (Multiplicative.toAdd (c (sixT b d u)))

private noncomputable def sixGamma (b d : K)
    (c : ↥(elementaryGroup (sixQ b d)) → SixN K) (u : sixU b d) : K :=
  sixCoeffY b d (Multiplicative.toAdd (c (sixT b d u)))

private noncomputable def sixEta (b d : K)
    (c : ↥(elementaryGroup (sixQ b d)) → SixN K) (u : sixU b d) : sixU b d :=
  ⟨sixProj b d (Multiplicative.toAdd (c (sixT b d u))),
    sixProj_mem_U b d (Multiplicative.toAdd (c (sixT b d u)))⟩

private noncomputable def sixAlphaR (b d : K)
    (c : ↥(elementaryGroup (sixQ b d)) → SixN K) (u : sixU b d) : K :=
  sixCoeffX b d (Multiplicative.toAdd (c (sixR b d u)))

private noncomputable def sixGammaR (b d : K)
    (c : ↥(elementaryGroup (sixQ b d)) → SixN K) (u : sixU b d) : K :=
  sixCoeffY b d (Multiplicative.toAdd (c (sixR b d u)))

private noncomputable def sixEtaR (b d : K)
    (c : ↥(elementaryGroup (sixQ b d)) → SixN K) (u : sixU b d) : sixU b d :=
  ⟨sixProj b d (Multiplicative.toAdd (c (sixR b d u))),
    sixProj_mem_U b d (Multiplicative.toAdd (c (sixR b d u)))⟩

omit [Finite K] [CharP K 2] in
private theorem six_decomp_T (b d : K)
    (c : ↥(elementaryGroup (sixQ b d)) → SixN K) (u : sixU b d) :
    Multiplicative.toAdd (c (sixT b d u)) =
      sixAlpha b d c u • sixX b d + sixGamma b d c u • sixY b d +
        (sixEta b d c u : SixV K) := by
  rw [sixAlpha, sixGamma, sixEta]
  exact six_decomp b d (Multiplicative.toAdd (c (sixT b d u)))

omit [Finite K] [CharP K 2] in
private theorem six_decomp_R (b d : K)
    (c : ↥(elementaryGroup (sixQ b d)) → SixN K) (u : sixU b d) :
    Multiplicative.toAdd (c (sixR b d u)) =
      sixAlphaR b d c u • sixX b d + sixGammaR b d c u • sixY b d +
        (sixEtaR b d c u : SixV K) := by
  rw [sixAlphaR, sixGammaR, sixEtaR]
  exact six_decomp b d (Multiplicative.toAdd (c (sixR b d u)))

omit [Finite K] [CharP K 2] in
private theorem sixT_cocycle (b d : K)
    {c : ↥(elementaryGroup (sixQ b d)) → SixN K}
    (hc : IsCocycle (sixSigmaHom b d) c) (u v : sixU b d) :
    Multiplicative.toAdd (c (sixT b d (u + v))) =
      Multiplicative.toAdd (c (sixT b d u)) +
        (sixT b d u : SixV K ≃ₗ[K] SixV K)
          (Multiplicative.toAdd (c (sixT b d v))) := by
  simpa [sixT_add] using six_toAdd_cocycle b d hc (sixT b d u) (sixT b d v)

omit [Finite K] [CharP K 2] in
private theorem sixR_cocycle (b d : K)
    {c : ↥(elementaryGroup (sixQ b d)) → SixN K}
    (hc : IsCocycle (sixSigmaHom b d) c) (u v : sixU b d) :
    Multiplicative.toAdd (c (sixR b d (u + v))) =
      Multiplicative.toAdd (c (sixR b d u)) +
        (sixR b d u : SixV K ≃ₗ[K] SixV K)
          (Multiplicative.toAdd (c (sixR b d v))) := by
  simpa [sixR_add] using six_toAdd_cocycle b d hc (sixR b d u) (sixR b d v)

omit [Finite K] [CharP K 2] in
private theorem sixCoeffX_of_mem_U_subtype (b d : K) (v : sixU b d) :
    sixCoeffX b d (v : SixV K) = 0 :=
  sixCoeffX_of_mem_U b d v.2

omit [Finite K] [CharP K 2] in
private theorem sixCoeffY_of_mem_U_subtype (b d : K) (v : sixU b d) :
    sixCoeffY b d (v : SixV K) = 0 :=
  sixCoeffY_of_mem_U b d v.2

omit [Finite K] [CharP K 2] in
private theorem sixProj_of_mem_U_subtype (b d : K) (v : sixU b d) :
    sixProj b d (v : SixV K) = (v : SixV K) :=
  sixProj_of_mem_U b d v.2

omit [Finite K] in
private theorem sixT_cocycle_decomp (b d : K)
    {c : ↥(elementaryGroup (sixQ b d)) → SixN K}
    (hc : IsCocycle (sixSigmaHom b d) c) (u v : sixU b d) :
    sixAlpha b d c (u + v) • sixX b d + sixGamma b d c (u + v) • sixY b d +
        (sixEta b d c (u + v) : SixV K) =
      (sixAlpha b d c u • sixX b d + sixGamma b d c u • sixY b d +
          (sixEta b d c u : SixV K)) +
        ((sixAlpha b d c v + sixGamma b d c v * sixQ b d (u : SixV K) +
            polar (sixQ b d) (u : SixV K) (sixEta b d c v : SixV K)) • sixX b d +
          sixGamma b d c v • sixY b d +
          ((sixEta b d c v : SixV K) + sixGamma b d c v • (u : SixV K))) := by
  have h := sixT_cocycle b d hc u v
  rw [six_decomp_T b d c (u + v)] at h
  rw [six_decomp_T b d c u] at h
  rw [six_decomp_T b d c v] at h
  rw [sixT_decomp_apply b d u (sixAlpha b d c v) (sixGamma b d c v) (sixEta b d c v)] at h
  exact h

omit [Finite K] in
private theorem sixAlpha_add (b d : K)
    {c : ↥(elementaryGroup (sixQ b d)) → SixN K}
    (hc : IsCocycle (sixSigmaHom b d) c) (u v : sixU b d) :
    sixAlpha b d c (u + v) =
      sixAlpha b d c u + sixAlpha b d c v +
        sixGamma b d c v * sixQ b d (u : SixV K) +
          polar (sixQ b d) (u : SixV K) (sixEta b d c v : SixV K) := by
  have h := congrArg (sixCoeffXLM b d) (sixT_cocycle_decomp b d hc u v)
  simp only [map_add, map_smul] at h
  simp only [sixCoeffXLM_apply, sixCoeffX_x, sixCoeffX_y, sixCoeffX_of_mem_U_subtype] at h
  simpa [mul_add, add_mul, add_assoc, add_comm, add_left_comm] using h

omit [Finite K] in
private theorem sixEta_add (b d : K)
    {c : ↥(elementaryGroup (sixQ b d)) → SixN K}
    (hc : IsCocycle (sixSigmaHom b d) c) (u v : sixU b d) :
    sixEta b d c (u + v) = sixEta b d c u + sixEta b d c v +
      sixGamma b d c v • u := by
  apply Subtype.ext
  have h := congrArg (sixProjLM b d) (sixT_cocycle_decomp b d hc u v)
  simp only [map_add, map_smul] at h
  simp only [sixProjLM_apply, sixProj_x, sixProj_y, sixProj_of_mem_U_subtype] at h
  simpa [sixEta, add_assoc] using h

omit [Finite K] in
private theorem sixT_comm_vec (b d : K)
    {c : ↥(elementaryGroup (sixQ b d)) → SixN K}
    (hc : IsCocycle (sixSigmaHom b d) c) (u v : sixU b d) :
    sixGamma b d c v • u = sixGamma b d c u • v := by
  have h1 := sixEta_add b d hc u v
  have h2 := sixEta_add b d hc v u
  rw [add_comm v u] at h2
  have h : sixEta b d c u + sixEta b d c v + sixGamma b d c v • u =
      sixEta b d c v + sixEta b d c u + sixGamma b d c u • v :=
    h1.symm.trans h2
  have h' : sixEta b d c u + sixEta b d c v + sixGamma b d c v • u =
      sixEta b d c u + sixEta b d c v + sixGamma b d c u • v := by
    calc sixEta b d c u + sixEta b d c v + sixGamma b d c v • u
        = sixEta b d c v + sixEta b d c u + sixGamma b d c u • v := h
      _ = sixEta b d c u + sixEta b d c v + sixGamma b d c u • v := by abel
  exact add_left_cancel h'

omit [Finite K] [CharP K 2] in
private theorem sixU_zero_of_comm (b d : K) (f : sixU b d → K)
    (h : ∀ u v : sixU b d, f v • u = f u • v) : ∀ u : sixU b d, f u = 0 := by
  let u0 : sixU b d := ⟨sixX2 b d, sixX2_mem_U b d⟩
  let v0 : sixU b d := ⟨sixY2 b d, sixY2_mem_U b d⟩
  have hB : polar (sixQ b d) (u0 : SixV K) (v0 : SixV K) = 1 := sixB_x2y2 b d
  have hcomm := h u0 v0
  have hv : f v0 = 0 := by
    have hp := congrArg (fun w : sixU b d =>
      polar (sixQ b d) (w : SixV K) (v0 : SixV K)) hcomm
    rw [Submodule.coe_smul, Submodule.coe_smul, QuadraticMap.polar_smul_left,
      QuadraticMap.polar_smul_left, hB, polar_self_eq_zero (sixQ_y2 b d)] at hp
    simpa using hp
  have hu : f u0 = 0 := by
    have hp := congrArg (fun w : sixU b d =>
      polar (sixQ b d) (w : SixV K) (u0 : SixV K)) hcomm
    rw [Submodule.coe_smul, Submodule.coe_smul, QuadraticMap.polar_smul_left,
      QuadraticMap.polar_smul_left,
      QuadraticMap.polar_comm (sixQ b d) (sixY2 b d) (sixX2 b d), sixB_x2y2,
      polar_self_eq_zero (sixQ_x2 b d)] at hp
    simpa using hp.symm
  have hu0ne : u0 ≠ 0 := by
    intro hzero
    exact sixX2_ne_zero b d (congrArg Subtype.val hzero)
  intro u
  have hcomm' := h u0 u
  rw [hu, zero_smul] at hcomm'
  rcases smul_eq_zero.mp hcomm' with hzero | hzero
  · exact hzero
  · exact absurd hzero hu0ne

omit [Finite K] in
private theorem sixGamma_zero (b d : K)
    {c : ↥(elementaryGroup (sixQ b d)) → SixN K}
    (hc : IsCocycle (sixSigmaHom b d) c) :
    ∀ u : sixU b d, sixGamma b d c u = 0 :=
  sixU_zero_of_comm b d (sixGamma b d c) (sixT_comm_vec b d hc)

private theorem sixT_scaling_toAdd (b d : K)
    (hirr : ∀ s : K, s ^ 2 + b * s + d ≠ 0) (hK : 2 < Nat.card K)
    {c : ↥(elementaryGroup (sixQ b d)) → SixN K}
    (hc : IsCocycle (sixSigmaHom b d) c)
    (hcS : ∀ a : Kˣ, c (sixS b d hirr hK a) = 1) (a : Kˣ) (u : sixU b d) :
    Multiplicative.toAdd (c (sixT b d (a • u))) =
      (sixS b d hirr hK a : SixV K ≃ₗ[K] SixV K)
        (Multiplicative.toAdd (c (sixT b d u))) := by
  have hd0 : Multiplicative.toAdd (c (sixS b d hirr hK a)) = 0 := by
    rw [hcS a, toAdd_one]
  have hdx : (sixS b d hirr hK a : SixV K ≃ₗ[K] SixV K) (sixPair b d).e =
      (a : K) • (sixPair b d).e := by
    simpa [sixX, Units.smul_def] using sixS_x b d hirr hK a
  have hdU : ∀ z ∈ (sixPair b d).perp,
      (sixS b d hirr hK a : SixV K ≃ₗ[K] SixV K) z = z := by
    intro z hz
    simpa using sixS_U b d hirr hK a ⟨z, hz⟩
  have h := w183_root_conj (f := fun g => Multiplicative.toAdd (c g))
    (six_toAdd_mem_Z1A b d hc) (sixPair b d) (d := sixS b d hirr hK a)
    hd0 (c := (a : K)) hdx hdU (u := (u : SixV K)) u.2
  simpa [sixT, w183El, sixX, Submodule.coe_smul, Units.smul_def] using h

private theorem sixAlpha_smul (b d : K)
    (hirr : ∀ s : K, s ^ 2 + b * s + d ≠ 0) (hK : 2 < Nat.card K)
    {c : ↥(elementaryGroup (sixQ b d)) → SixN K}
    (hc : IsCocycle (sixSigmaHom b d) c)
    (hcS : ∀ a : Kˣ, c (sixS b d hirr hK a) = 1) (a : Kˣ) (u : sixU b d) :
    sixAlpha b d c (a • u) = (a : K) * sixAlpha b d c u := by
  have h := sixT_scaling_toAdd b d hirr hK hc hcS a u
  rw [six_decomp_T b d c (a • u), six_decomp_T b d c u] at h
  rw [sixS_decomp_apply b d hirr hK a (sixAlpha b d c u) (sixGamma b d c u)
    (sixEta b d c u)] at h
  simp only [sixGamma_zero b d hc, zero_smul, mul_zero, add_zero, Units.smul_def] at h
  have hx := congrArg (sixCoeffXLM b d) h
  simp only [map_add, map_smul] at hx
  simp only [sixCoeffXLM_apply, sixCoeffX_x, sixCoeffX_of_mem_U_subtype] at hx
  simpa [Units.smul_def] using hx

private theorem sixEta_smul (b d : K)
    (hirr : ∀ s : K, s ^ 2 + b * s + d ≠ 0) (hK : 2 < Nat.card K)
    {c : ↥(elementaryGroup (sixQ b d)) → SixN K}
    (hc : IsCocycle (sixSigmaHom b d) c)
    (hcS : ∀ a : Kˣ, c (sixS b d hirr hK a) = 1) (a : Kˣ) (u : sixU b d) :
    sixEta b d c (a • u) = sixEta b d c u := by
  apply Subtype.ext
  have h := sixT_scaling_toAdd b d hirr hK hc hcS a u
  rw [six_decomp_T b d c (a • u), six_decomp_T b d c u] at h
  rw [sixS_decomp_apply b d hirr hK a (sixAlpha b d c u) (sixGamma b d c u)
    (sixEta b d c u)] at h
  simp only [sixGamma_zero b d hc, zero_smul, mul_zero, add_zero, Units.smul_def] at h
  have hx := congrArg (sixProjLM b d) h
  simp only [map_add, map_smul] at hx
  simp only [sixProjLM_apply, sixProj_x, sixProj_of_mem_U_subtype] at hx
  simpa [sixEta, Units.smul_def] using hx

omit [Finite K] in
private theorem sixEta_add' (b d : K)
    {c : ↥(elementaryGroup (sixQ b d)) → SixN K}
    (hc : IsCocycle (sixSigmaHom b d) c) (u v : sixU b d) :
    sixEta b d c (u + v) = sixEta b d c u + sixEta b d c v := by
  rw [sixEta_add b d hc u v, sixGamma_zero b d hc v, zero_smul, add_zero]

omit [Finite K] in
private theorem sixU_eta_zero (b d : K) (hK : 2 < Nat.card K)
    (η : sixU b d → sixU b d)
    (hadd : ∀ u v : sixU b d, η (u + v) = η u + η v)
    (hsmul : ∀ (a : Kˣ) (u : sixU b d), η (a • u) = η u) :
    ∀ u : sixU b d, η u = 0 := by
  obtain ⟨a0, ha0, ha1⟩ :=
    CFSG.ClassicalGroups.Alternating.exists_ne_zero_ne_one_of_two_lt_card hK
  have hne : (1 + a0 : K) ≠ 0 := by
    intro h
    have h1 : a0 = -1 := by linear_combination h
    have h2 : a0 = 1 := by simpa [CharTwo.neg_eq] using h1
    exact ha1 h2
  intro u
  have hscale : η ((1 + a0 : K) • u) = η u := by
    simpa using hsmul (Units.mk0 (1 + a0) hne) u
  have hadd' : η ((1 + a0 : K) • u) = η u + η u := by
    rw [add_smul, one_smul, hadd]
    congr 1
    simpa using hsmul (Units.mk0 a0 ha0) u
  have h : η u = η u + η u := hscale.symm.trans hadd'
  exact (add_left_cancel (a := η u) (b := 0) (c := η u) (by simpa using h)).symm

private theorem sixEta_zero (b d : K)
    (hirr : ∀ s : K, s ^ 2 + b * s + d ≠ 0) (hK : 2 < Nat.card K)
    {c : ↥(elementaryGroup (sixQ b d)) → SixN K}
    (hc : IsCocycle (sixSigmaHom b d) c)
    (hcS : ∀ a : Kˣ, c (sixS b d hirr hK a) = 1) :
    ∀ u : sixU b d, sixEta b d c u = 0 :=
  sixU_eta_zero b d hK (sixEta b d c)
    (sixEta_add' b d hc) (sixEta_smul b d hirr hK hc hcS)

private theorem sixAlpha_add' (b d : K)
    (hirr : ∀ s : K, s ^ 2 + b * s + d ≠ 0) (hK : 2 < Nat.card K)
    {c : ↥(elementaryGroup (sixQ b d)) → SixN K}
    (hc : IsCocycle (sixSigmaHom b d) c)
    (hcS : ∀ a : Kˣ, c (sixS b d hirr hK a) = 1) (u v : sixU b d) :
    sixAlpha b d c (u + v) = sixAlpha b d c u + sixAlpha b d c v := by
  rw [sixAlpha_add b d hc u v, sixGamma_zero b d hc v,
    sixEta_zero b d hirr hK hc hcS v]
  simp

private theorem sixAlpha_zero (b d : K)
    (hirr : ∀ s : K, s ^ 2 + b * s + d ≠ 0) (hK : 2 < Nat.card K)
    {c : ↥(elementaryGroup (sixQ b d)) → SixN K}
    (hc : IsCocycle (sixSigmaHom b d) c)
    (hcS : ∀ a : Kˣ, c (sixS b d hirr hK a) = 1) :
    sixAlpha b d c 0 = 0 := by
  have h := sixAlpha_add b d hc 0 0
  rw [sixGamma_zero b d hc, sixEta_zero b d hirr hK hc hcS] at h
  simp at h
  exact (add_left_cancel (a := sixAlpha b d c 0) (b := 0) (c := sixAlpha b d c 0)
    (by simpa using h)).symm

private noncomputable def sixAlphaLM (b d : K)
    (hirr : ∀ s : K, s ^ 2 + b * s + d ≠ 0) (hK : 2 < Nat.card K)
    {c : ↥(elementaryGroup (sixQ b d)) → SixN K}
    (hc : IsCocycle (sixSigmaHom b d) c)
    (hcS : ∀ a : Kˣ, c (sixS b d hirr hK a) = 1) :
    sixU b d →ₗ[K] K where
  toFun := sixAlpha b d c
  map_add' := sixAlpha_add' b d hirr hK hc hcS
  map_smul' := fun a u => by
    by_cases ha : a = 0
    · subst ha
      simp [sixAlpha_zero b d hirr hK hc hcS]
    · simpa [Units.smul_def] using
        sixAlpha_smul b d hirr hK hc hcS (Units.mk0 a ha) u

private theorem sixAlpha_exists_z (b d : K)
    (hirr : ∀ s : K, s ^ 2 + b * s + d ≠ 0) (hK : 2 < Nat.card K)
    {c : ↥(elementaryGroup (sixQ b d)) → SixN K}
    (hc : IsCocycle (sixSigmaHom b d) c)
    (hcS : ∀ a : Kˣ, c (sixS b d hirr hK a) = 1) :
    ∃ z : sixU b d, ∀ u : sixU b d,
      sixAlpha b d c u = polar (sixQ b d) (u : SixV K) (z : SixV K) := by
  let B := polarBilin ((sixQ b d).restrict (sixU b d))
  let hB : B.Nondegenerate := sixU_nondegenerate b d hirr
  let α : sixU b d →ₗ[K] K := sixAlphaLM b d hirr hK hc hcS
  let z : sixU b d := (LinearMap.BilinForm.toDual B hB).symm α
  refine ⟨z, fun u => ?_⟩
  have h := LinearMap.BilinForm.apply_toDual_symm_apply (B := B) (hB := hB) α u
  change polar ((sixQ b d).restrict (sixU b d)) z u = α u at h
  rw [polar_restrict] at h
  change polar (sixQ b d) (z : SixV K) (u : SixV K) = sixAlpha b d c u at h
  change sixAlpha b d c u = polar (sixQ b d) (u : SixV K) (z : SixV K)
  rw [← h, QuadraticMap.polar_comm]

omit [Finite K] in
private theorem sixR_cocycle_decomp (b d : K)
    {c : ↥(elementaryGroup (sixQ b d)) → SixN K}
    (hc : IsCocycle (sixSigmaHom b d) c) (u v : sixU b d) :
    sixAlphaR b d c (u + v) • sixX b d + sixGammaR b d c (u + v) • sixY b d +
        (sixEtaR b d c (u + v) : SixV K) =
      (sixAlphaR b d c u • sixX b d + sixGammaR b d c u • sixY b d +
          (sixEtaR b d c u : SixV K)) +
        (sixAlphaR b d c v • sixX b d +
          (sixGammaR b d c v + sixAlphaR b d c v * sixQ b d (u : SixV K) +
            polar (sixQ b d) (u : SixV K) (sixEtaR b d c v : SixV K)) • sixY b d +
          ((sixEtaR b d c v : SixV K) + sixAlphaR b d c v • (u : SixV K))) := by
  have h := sixR_cocycle b d hc u v
  rw [six_decomp_R b d c (u + v)] at h
  rw [six_decomp_R b d c u] at h
  rw [six_decomp_R b d c v] at h
  rw [sixR_decomp_apply b d u (sixAlphaR b d c v) (sixGammaR b d c v) (sixEtaR b d c v)] at h
  exact h

omit [Finite K] in
private theorem sixGammaR_add (b d : K)
    {c : ↥(elementaryGroup (sixQ b d)) → SixN K}
    (hc : IsCocycle (sixSigmaHom b d) c) (u v : sixU b d) :
    sixGammaR b d c (u + v) =
      sixGammaR b d c u + sixGammaR b d c v +
        sixAlphaR b d c v * sixQ b d (u : SixV K) +
          polar (sixQ b d) (u : SixV K) (sixEtaR b d c v : SixV K) := by
  have h := congrArg (sixCoeffYLM b d) (sixR_cocycle_decomp b d hc u v)
  simp only [map_add, map_smul] at h
  simp only [sixCoeffYLM_apply, sixCoeffY_x, sixCoeffY_y, sixCoeffY_of_mem_U_subtype] at h
  simpa [mul_add, add_mul, add_assoc, add_comm, add_left_comm] using h

omit [Finite K] in
private theorem sixEtaR_add (b d : K)
    {c : ↥(elementaryGroup (sixQ b d)) → SixN K}
    (hc : IsCocycle (sixSigmaHom b d) c) (u v : sixU b d) :
    sixEtaR b d c (u + v) = sixEtaR b d c u + sixEtaR b d c v +
      sixAlphaR b d c v • u := by
  apply Subtype.ext
  have h := congrArg (sixProjLM b d) (sixR_cocycle_decomp b d hc u v)
  simp only [map_add, map_smul] at h
  simp only [sixProjLM_apply, sixProj_x, sixProj_y, sixProj_of_mem_U_subtype] at h
  simpa [sixEtaR, add_assoc] using h

omit [Finite K] in
private theorem sixR_comm_vec (b d : K)
    {c : ↥(elementaryGroup (sixQ b d)) → SixN K}
    (hc : IsCocycle (sixSigmaHom b d) c) (u v : sixU b d) :
    sixAlphaR b d c v • u = sixAlphaR b d c u • v := by
  have h1 := sixEtaR_add b d hc u v
  have h2 := sixEtaR_add b d hc v u
  rw [add_comm v u] at h2
  have h : sixEtaR b d c u + sixEtaR b d c v + sixAlphaR b d c v • u =
      sixEtaR b d c v + sixEtaR b d c u + sixAlphaR b d c u • v :=
    h1.symm.trans h2
  have h' : sixEtaR b d c u + sixEtaR b d c v + sixAlphaR b d c v • u =
      sixEtaR b d c u + sixEtaR b d c v + sixAlphaR b d c u • v := by
    calc sixEtaR b d c u + sixEtaR b d c v + sixAlphaR b d c v • u
        = sixEtaR b d c v + sixEtaR b d c u + sixAlphaR b d c u • v := h
      _ = sixEtaR b d c u + sixEtaR b d c v + sixAlphaR b d c u • v := by abel
  exact add_left_cancel h'

omit [Finite K] in
private theorem sixAlphaR_zero (b d : K)
    {c : ↥(elementaryGroup (sixQ b d)) → SixN K}
    (hc : IsCocycle (sixSigmaHom b d) c) :
    ∀ u : sixU b d, sixAlphaR b d c u = 0 :=
  sixU_zero_of_comm b d (sixAlphaR b d c) (sixR_comm_vec b d hc)

private theorem sixR_scaling_toAdd (b d : K)
    (hirr : ∀ s : K, s ^ 2 + b * s + d ≠ 0) (hK : 2 < Nat.card K)
    {c : ↥(elementaryGroup (sixQ b d)) → SixN K}
    (hc : IsCocycle (sixSigmaHom b d) c)
    (hcS : ∀ a : Kˣ, c (sixS b d hirr hK a) = 1) (a : Kˣ) (u : sixU b d) :
    Multiplicative.toAdd (c (sixR b d (a⁻¹ • u))) =
      (sixS b d hirr hK a : SixV K ≃ₗ[K] SixV K)
        (Multiplicative.toAdd (c (sixR b d u))) := by
  let P' : HypPair (sixQ b d) :=
    ⟨sixY b d, sixX b d, sixQ_y b d, sixQ_x b d, sixB_yx b d⟩
  have hP'e : P'.e = sixY b d := rfl
  have hP'f : P'.f = sixX b d := rfl
  have hd0 : Multiplicative.toAdd (c (sixS b d hirr hK a)) = 0 := by
    rw [hcS a, toAdd_one]
  have hdx : (sixS b d hirr hK a : SixV K ≃ₗ[K] SixV K) P'.e =
      ((a⁻¹ : Kˣ) : K) • P'.e := by
    rw [hP'e]
    simpa [Units.smul_def] using sixS_y b d hirr hK a
  have hdU : ∀ z ∈ P'.perp, (sixS b d hirr hK a : SixV K ≃ₗ[K] SixV K) z = z := by
    intro z hz
    rw [HypPair.mem_perp, hP'e, hP'f] at hz
    exact sixS_U b d hirr hK a
      ⟨z, HypPair.mem_perp.mpr (by simpa only [sixX, sixY] using hz.symm)⟩
  have hu : (u : SixV K) ∈ P'.perp := by
    rw [HypPair.mem_perp, hP'e, hP'f]
    simpa only [sixX, sixY] using (HypPair.mem_perp.mp u.2).symm
  have h := w183_root_conj (f := fun g => Multiplicative.toAdd (c g))
    (six_toAdd_mem_Z1A b d hc) P' (d := sixS b d hirr hK a)
    hd0 (c := ((a⁻¹ : Kˣ) : K)) hdx hdU (u := (u : SixV K)) hu
  rw [hP'e] at h
  simpa [sixR, w183El, sixY, Submodule.coe_smul, Units.smul_def] using h

private theorem sixEtaR_smul (b d : K)
    (hirr : ∀ s : K, s ^ 2 + b * s + d ≠ 0) (hK : 2 < Nat.card K)
    {c : ↥(elementaryGroup (sixQ b d)) → SixN K}
    (hc : IsCocycle (sixSigmaHom b d) c)
    (hcS : ∀ a : Kˣ, c (sixS b d hirr hK a) = 1) (a : Kˣ) (u : sixU b d) :
    sixEtaR b d c (a • u) = sixEtaR b d c u := by
  apply Subtype.ext
  have h := sixR_scaling_toAdd b d hirr hK hc hcS a⁻¹ u
  rw [inv_inv] at h
  rw [six_decomp_R b d c (a • u), six_decomp_R b d c u] at h
  rw [sixS_decomp_apply b d hirr hK a⁻¹ (sixAlphaR b d c u) (sixGammaR b d c u)
    (sixEtaR b d c u)] at h
  simp only [sixAlphaR_zero b d hc, zero_smul, zero_add, Units.smul_def] at h
  have hx := congrArg (sixProjLM b d) h
  simp only [map_add, map_smul] at hx
  simp only [sixProjLM_apply, sixProj_x, sixProj_y, sixProj_of_mem_U_subtype] at hx
  simpa [sixEtaR, Units.smul_def] using hx

private theorem sixGammaR_smul (b d : K)
    (hirr : ∀ s : K, s ^ 2 + b * s + d ≠ 0) (hK : 2 < Nat.card K)
    {c : ↥(elementaryGroup (sixQ b d)) → SixN K}
    (hc : IsCocycle (sixSigmaHom b d) c)
    (hcS : ∀ a : Kˣ, c (sixS b d hirr hK a) = 1) (a : Kˣ) (u : sixU b d) :
    sixGammaR b d c (a • u) = (a : K) * sixGammaR b d c u := by
  have h := sixR_scaling_toAdd b d hirr hK hc hcS a⁻¹ u
  rw [inv_inv] at h
  rw [six_decomp_R b d c (a • u), six_decomp_R b d c u] at h
  rw [sixS_decomp_apply b d hirr hK a⁻¹ (sixAlphaR b d c u) (sixGammaR b d c u)
    (sixEtaR b d c u)] at h
  simp only [sixAlphaR_zero b d hc, zero_smul, zero_add, Units.smul_def, Units.val_inv_eq_inv_val] at h
  have hx := congrArg (sixCoeffYLM b d) h
  simp only [map_add, map_smul] at hx
  simp only [sixCoeffYLM_apply, sixCoeffY_x, sixCoeffY_y, sixCoeffY_of_mem_U_subtype] at hx
  simpa [Units.val_inv_eq_inv_val, Units.smul_def] using hx

private theorem sixEtaR_zero (b d : K)
    (hirr : ∀ s : K, s ^ 2 + b * s + d ≠ 0) (hK : 2 < Nat.card K)
    {c : ↥(elementaryGroup (sixQ b d)) → SixN K}
    (hc : IsCocycle (sixSigmaHom b d) c)
    (hcS : ∀ a : Kˣ, c (sixS b d hirr hK a) = 1) :
    ∀ u : sixU b d, sixEtaR b d c u = 0 := by
  refine sixU_eta_zero b d hK (sixEtaR b d c) ?_ ?_
  · intro u v
    rw [sixEtaR_add b d hc u v, sixAlphaR_zero b d hc v, zero_smul, add_zero]
  · intro a u
    exact sixEtaR_smul b d hirr hK hc hcS a u

private theorem sixGammaR_add' (b d : K)
    (hirr : ∀ s : K, s ^ 2 + b * s + d ≠ 0) (hK : 2 < Nat.card K)
    {c : ↥(elementaryGroup (sixQ b d)) → SixN K}
    (hc : IsCocycle (sixSigmaHom b d) c)
    (hcS : ∀ a : Kˣ, c (sixS b d hirr hK a) = 1) (u v : sixU b d) :
    sixGammaR b d c (u + v) = sixGammaR b d c u + sixGammaR b d c v := by
  rw [sixGammaR_add b d hc u v, sixAlphaR_zero b d hc v,
    sixEtaR_zero b d hirr hK hc hcS v]
  simp

private noncomputable def sixGammaRLM (b d : K)
    (hirr : ∀ s : K, s ^ 2 + b * s + d ≠ 0) (hK : 2 < Nat.card K)
    {c : ↥(elementaryGroup (sixQ b d)) → SixN K}
    (hc : IsCocycle (sixSigmaHom b d) c)
    (hcS : ∀ a : Kˣ, c (sixS b d hirr hK a) = 1) :
    sixU b d →ₗ[K] K where
  toFun := sixGammaR b d c
  map_add' := sixGammaR_add' b d hirr hK hc hcS
  map_smul' := fun a u => by
    by_cases ha : a = 0
    · subst ha
      have hzero : sixGammaR b d c (0 : sixU b d) = 0 := by
        have h := sixGammaR_add' b d hirr hK hc hcS 0 0
        simp at h
        exact (add_left_cancel (a := sixGammaR b d c 0) (b := 0) (c := sixGammaR b d c 0)
          (by simpa using h)).symm
      simp [hzero]
    · simpa [Units.smul_def] using
        sixGammaR_smul b d hirr hK hc hcS (Units.mk0 a ha) u

omit [Finite K] in
private theorem sixT_mul_R_comm (b d : K) (u : sixU b d)
    (hu : sixQ b d (u : SixV K) = 0) :
    sixT b d u * sixR b d u = sixR b d u * sixT b d u := by
  let L : SixV K ≃ₗ[K] SixV K :=
    (sixT b d u : SixV K ≃ₗ[K] SixV K) * (sixR b d u : SixV K ≃ₗ[K] SixV K)
  let M : SixV K ≃ₗ[K] SixV K :=
    (sixR b d u : SixV K ≃ₗ[K] SixV K) * (sixT b d u : SixV K ≃ₗ[K] SixV K)
  have hLx : L (sixX b d) = M (sixX b d) := by
    change (sixT b d u : SixV K ≃ₗ[K] SixV K)
        ((sixR b d u : SixV K ≃ₗ[K] SixV K) (sixX b d)) =
      (sixR b d u : SixV K ≃ₗ[K] SixV K)
        ((sixT b d u : SixV K ≃ₗ[K] SixV K) (sixX b d))
    rw [sixT_x, sixR_x, hu, zero_smul, add_zero]
    rw [map_add, sixT_x, sixT_U, polar_self_eq_zero hu]
    simp
  have hLy : L (sixY b d) = M (sixY b d) := by
    change (sixT b d u : SixV K ≃ₗ[K] SixV K)
        ((sixR b d u : SixV K ≃ₗ[K] SixV K) (sixY b d)) =
      (sixR b d u : SixV K ≃ₗ[K] SixV K)
        ((sixT b d u : SixV K ≃ₗ[K] SixV K) (sixY b d))
    rw [sixR_y, sixT_y, hu, zero_smul, add_zero]
    rw [map_add, sixR_y, sixR_U, polar_self_eq_zero hu]
    simp
  have hLw : ∀ w : sixU b d, L (w : SixV K) = M (w : SixV K) := by
    intro w
    change (sixT b d u : SixV K ≃ₗ[K] SixV K)
        ((sixR b d u : SixV K ≃ₗ[K] SixV K) (w : SixV K)) =
      (sixR b d u : SixV K ≃ₗ[K] SixV K)
        ((sixT b d u : SixV K ≃ₗ[K] SixV K) (w : SixV K))
    rw [sixR_U, sixT_U, map_add, map_smul, map_add, map_smul,
      sixT_U, sixT_y, sixR_U, sixR_x, hu, zero_smul, add_zero]
    module
  apply Subtype.ext
  refine LinearEquiv.ext fun v => ?_
  change L v = M v
  let a := sixCoeffX b d v
  let c := sixCoeffY b d v
  let w : sixU b d := ⟨sixProj b d v, sixProj_mem_U b d v⟩
  have hv : v = a • sixX b d + c • sixY b d + (w : SixV K) := by
    have h := six_decomp b d v
    dsimp only [a, c, w]
    rw [show sixProj b d v = (w : SixV K) from rfl] at h
    exact h
  calc L v = L (a • sixX b d + c • sixY b d + (w : SixV K)) := by rw [hv]
    _ = a • L (sixX b d) + c • L (sixY b d) + L (w : SixV K) := by
      rw [map_add, map_add, map_smul, map_smul]
    _ = a • M (sixX b d) + c • M (sixY b d) + M (w : SixV K) := by
      rw [hLx, hLy, hLw w]
    _ = M (a • sixX b d + c • sixY b d + (w : SixV K)) := by
      rw [map_add, map_add, map_smul, map_smul]
    _ = M v := by rw [hv]

private theorem sixGammaR_zero (b d : K)
    (hirr : ∀ s : K, s ^ 2 + b * s + d ≠ 0) (hK : 2 < Nat.card K)
    {c : ↥(elementaryGroup (sixQ b d)) → SixN K}
    (hc : IsCocycle (sixSigmaHom b d) c)
    (hcS : ∀ a : Kˣ, c (sixS b d hirr hK a) = 1) :
    sixGammaR b d c (0 : sixU b d) = 0 := by
  have h := sixGammaR_add' b d hirr hK hc hcS (0 : sixU b d) (0 : sixU b d)
  simp only [add_zero] at h
  exact (add_left_cancel (a := sixGammaR b d c 0) (b := 0) (c := sixGammaR b d c 0)
    (by simpa using h)).symm

private theorem sixAlpha_eq_sixGammaR_of_singular (b d : K)
    (hirr : ∀ s : K, s ^ 2 + b * s + d ≠ 0) (hK : 2 < Nat.card K)
    {c : ↥(elementaryGroup (sixQ b d)) → SixN K}
    (hc : IsCocycle (sixSigmaHom b d) c)
    (hcS : ∀ a : Kˣ, c (sixS b d hirr hK a) = 1) {u : sixU b d}
    (hu : sixQ b d (u : SixV K) = 0) :
    sixAlpha b d c u = sixGammaR b d c u := by
  have hcomm := sixT_mul_R_comm b d u hu
  have h1 := six_toAdd_cocycle b d hc (sixT b d u) (sixR b d u)
  have h2 := six_toAdd_cocycle b d hc (sixR b d u) (sixT b d u)
  rw [hcomm] at h1
  have hT : Multiplicative.toAdd (c (sixT b d u)) = sixAlpha b d c u • sixX b d := by
    rw [six_decomp_T b d c u, sixGamma_zero b d hc,
      sixEta_zero b d hirr hK hc hcS]
    simp
  have hR : Multiplicative.toAdd (c (sixR b d u)) = sixGammaR b d c u • sixY b d := by
    rw [six_decomp_R b d c u, sixAlphaR_zero b d hc,
      sixEtaR_zero b d hirr hK hc hcS]
    simp
  rw [hT, hR] at h1 h2
  rw [map_smul, sixT_y] at h1
  rw [map_smul, sixR_x] at h2
  rw [hu, zero_smul, add_zero] at h1 h2
  have hEq := h1.symm.trans h2
  rw [smul_add, smul_add] at hEq
  have hU := congrArg (sixProjLM b d) hEq
  simp only [map_add, map_smul, sixProjLM_apply, sixProj_x, sixProj_y, sixProj_of_mem_U_subtype, smul_zero, zero_add] at hU
  by_cases hu0 : u = 0
  · subst hu0
    rw [sixAlpha_zero b d hirr hK hc hcS, sixGammaR_zero b d hirr hK hc hcS]
  · have hsubV : (sixGammaR b d c u - sixAlpha b d c u) • (u : SixV K) = 0 := by
      rw [sub_smul, hU, sub_self]
    have hsub : (sixGammaR b d c u - sixAlpha b d c u) • u = 0 := by
      apply Subtype.ext
      simpa [Submodule.coe_smul] using hsubV
    rcases smul_eq_zero.mp hsub with hz | hz
    · exact (sub_eq_zero.mp hz).symm
    · exact absurd hz hu0

private theorem sixAlpha_eq_sixGammaR (b d : K)
    (hirr : ∀ s : K, s ^ 2 + b * s + d ≠ 0) (hK : 2 < Nat.card K)
    {c : ↥(elementaryGroup (sixQ b d)) → SixN K}
    (hc : IsCocycle (sixSigmaHom b d) c)
    (hcS : ∀ a : Kˣ, c (sixS b d hirr hK a) = 1) :
    ∀ u : sixU b d, sixAlpha b d c u = sixGammaR b d c u := by
  let f : sixU b d →ₗ[K] K :=
    sixAlphaLM b d hirr hK hc hcS - sixGammaRLM b d hirr hK hc hcS
  have hsing : ∀ u : sixU b d, sixQ b d (u : SixV K) = 0 → f u = 0 := by
    intro u hu
    have h := sixAlpha_eq_sixGammaR_of_singular b d hirr hK hc hcS hu
    change sixAlpha b d c u - sixGammaR b d c u = 0
    rw [h, sub_self]
  have hspan := sixU_span_singular b d hirr
  have hker : Submodule.span K
      {v : sixU b d | (sixQ b d).restrict (sixU b d) v = 0} ≤ LinearMap.ker f := by
    rw [Submodule.span_le]
    rintro v hv
    exact hsing v hv
  have htop : LinearMap.ker f = ⊤ := by
    rw [eq_top_iff]
    rwa [← hspan]
  intro u
  have hu : f u = 0 := by
    have hmem : u ∈ LinearMap.ker f := by rw [htop]; exact Submodule.mem_top
    exact hmem
  have h := sub_eq_zero.mp hu
  exact h

private theorem six_isCoboundary_sigma (b d : K)
    (hirr : ∀ s : K, s ^ 2 + b * s + d ≠ 0) (hK : 2 < Nat.card K)
    {c : ↥(elementaryGroup (sixQ b d)) → SixN K}
    (hc : IsCocycle (sixSigmaHom b d) c) :
    IsCoboundary (sixSigmaHom b d) c := by
  obtain ⟨m, hm⟩ := six_torus_coboundary b d hirr hK hc
  let c1 : ↥(elementaryGroup (sixQ b d)) → SixN K :=
    fun g => c g * (sixSigmaHom b d g m * m⁻¹)⁻¹
  have hc1 : IsCocycle (sixSigmaHom b d) c1 := hc.div_cobdry m
  have hc1S : ∀ a : Kˣ, c1 (sixS b d hirr hK a) = 1 := by
    intro a
    dsimp only [c1]
    rw [hm a]
    exact mul_inv_cancel _
  obtain ⟨z, hz⟩ := sixAlpha_exists_z b d hirr hK hc1 hc1S
  let Z : SixN K := Multiplicative.ofAdd (z : SixV K)
  let c2 : ↥(elementaryGroup (sixQ b d)) → SixN K :=
    fun g => c1 g * (sixSigmaHom b d g Z * Z⁻¹)⁻¹
  have hc2 : IsCocycle (sixSigmaHom b d) c2 := hc1.div_cobdry Z
  have hc1T : ∀ u : sixU b d,
      Multiplicative.toAdd (c1 (sixT b d u)) = sixAlpha b d c1 u • sixX b d := by
    intro u
    rw [six_decomp_T b d c1 u, sixGamma_zero b d hc1,
      sixEta_zero b d hirr hK hc1 hc1S]
    simp
  have hc1R : ∀ u : sixU b d,
      Multiplicative.toAdd (c1 (sixR b d u)) = sixGammaR b d c1 u • sixY b d := by
    intro u
    rw [six_decomp_R b d c1 u, sixAlphaR_zero b d hc1,
      sixEtaR_zero b d hirr hK hc1 hc1S]
    simp
  have hinner : ∀ (g : ↥(elementaryGroup (sixQ b d))) (v : SixV K),
      Multiplicative.toAdd
        (sixSigmaHom b d g (Multiplicative.ofAdd v) * (Multiplicative.ofAdd v)⁻¹) =
        (g : SixV K ≃ₗ[K] SixV K) v - v := by
    intro g v
    rw [sixSigmaHom_apply, toAdd_mul, toAdd_ofAdd, toAdd_inv, toAdd_ofAdd]
    abel
  have hc2T : ∀ u : sixU b d, c2 (sixT b d u) = 1 := by
    intro u
    have hzT : (sixT b d u : SixV K ≃ₗ[K] SixV K) (z : SixV K) =
        (z : SixV K) + sixAlpha b d c1 u • sixX b d := by
      rw [sixT_U b d u z, hz u]
    apply Multiplicative.toAdd.injective
    dsimp only [c2]
    rw [toAdd_mul, toAdd_inv, hinner, hc1T u, hzT, toAdd_one]
    abel
  have hc2R : ∀ u : sixU b d, c2 (sixR b d u) = 1 := by
    intro u
    have hzR : (sixR b d u : SixV K ≃ₗ[K] SixV K) (z : SixV K) =
        (z : SixV K) + sixGammaR b d c1 u • sixY b d := by
      rw [sixR_U b d u z, ← hz u, sixAlpha_eq_sixGammaR b d hirr hK hc1 hc1S u]
    apply Multiplicative.toAdd.injective
    dsimp only [c2]
    rw [toAdd_mul, toAdd_inv, hinner, hc1R u, hzR, toAdd_one]
    abel
  let f : ↥(elementaryGroup (sixQ b d)) → SixV K :=
    fun g => Multiplicative.toAdd (c2 g)
  have hf : f ∈ CFSG.Quasithin.JonesParshall.Z1A (w183ElemAct (sixQ b d)) :=
    six_toAdd_mem_Z1A b d hc2
  have hT : ∀ u ∈ (sixPair b d).perp,
      f (w183El (sixQ b d) (sixPair b d).e u) = 0 := by
    intro u hu
    dsimp only [f]
    have h := hc2T ⟨u, hu⟩
    rw [show w183El (sixQ b d) (sixPair b d).e u = sixT b d ⟨u, hu⟩ from rfl,
      h, toAdd_one]
  have hR : ∀ u ∈ (sixPair b d).perp,
      f (w183El (sixQ b d) (sixPair b d).f u) = 0 := by
    intro u hu
    dsimp only [f]
    have h := hc2R ⟨u, hu⟩
    rw [show w183El (sixQ b d) (sixPair b d).f u = sixR b d ⟨u, hu⟩ from rfl,
      h, toAdd_one]
  have hzero : ∀ g : ↥(elementaryGroup (sixQ b d)), c2 g = 1 := fun g =>
    toAdd_eq_zero.mp
      (w183_zero_of_roots (sixQ_nondegenerate b d hirr) (sixPair b d) hf hT hR g)
  have hc2cob : IsCoboundary (sixSigmaHom b d) c2 := by
    refine ⟨1, fun g => ?_⟩
    rw [hzero g]
    simp
  have hc1cob : IsCoboundary (sixSigmaHom b d) c1 :=
    isCoboundary_of_div_cobdry (ρ := sixSigmaHom b d) Z hc2cob
  exact isCoboundary_of_div_cobdry (ρ := sixSigmaHom b d) m hc1cob

private theorem isCoboundary_of_isCoboundary_sigma (b d : K)
    (hirr : ∀ s : K, s ^ 2 + b * s + d ≠ 0) (hK : 2 < Nat.card K)
    {c : StatedOmega (StatedQuadMinus 3 K b d) → SixN K}
    (hc : IsCocycle
      ((s16gNatHom (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) K).comp
        (StatedOmega (StatedQuadMinus 3 K b d)).subtype) c) :
    IsCoboundary
      ((s16gNatHom (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) K).comp
        (StatedOmega (StatedQuadMinus 3 K b d)).subtype) c := by
  let e : StatedOmega (StatedQuadMinus 3 K b d) ≃*
      ↥(elementaryGroup (sixQ b d)) :=
    statedOmegaMinusEquiv (m := 3) (by norm_num) hirr
  let c' : ↥(elementaryGroup (sixQ b d)) → SixN K := fun g => c (e.symm g)
  have hact : ∀ (g : ↥(elementaryGroup (sixQ b d))) (m : SixN K),
      ((s16gNatHom (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) K).comp
          (StatedOmega (StatedQuadMinus 3 K b d)).subtype) (e.symm g) m =
        sixSigmaHom b d g m := by
    intro g m
    apply Multiplicative.toAdd.injective
    rw [MonoidHom.comp_apply, s16gNatHom_apply, sixSigmaHom_apply, toAdd_ofAdd, toAdd_ofAdd]
    have h := statedOmegaMinusEquiv_app (m := 3) (by norm_num) hirr (e.symm g)
      (Multiplicative.toAdd m)
    change Gom.app (e (e.symm g)) (Multiplicative.toAdd m) =
      (((e.symm g : StatedOmega (StatedQuadMinus 3 K b d)) : GL
        (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) K).val) *ᵥ
        Multiplicative.toAdd m at h
    rw [MulEquiv.apply_symm_apply] at h
    simpa [Gom.app] using h.symm
  have hc' : IsCocycle (sixSigmaHom b d) c' := by
    intro g h
    change c (e.symm (g * h)) = c (e.symm g) * sixSigmaHom b d g (c (e.symm h))
    rw [map_mul]
    have hcgh := hc (e.symm g) (e.symm h)
    rw [hact g (c (e.symm h))] at hcgh
    exact hcgh
  obtain ⟨m, hm⟩ := six_isCoboundary_sigma b d hirr hK hc'
  refine ⟨m, fun g => ?_⟩
  have h := hm (e g)
  dsimp only [c'] at h
  rw [MulEquiv.symm_apply_apply] at h
  have hactg : ((s16gNatHom (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) K).comp
      (StatedOmega (StatedQuadMinus 3 K b d)).subtype) g m =
      sixSigmaHom b d (e g) m := by
    simpa using hact (e g) m
  rw [← hactg] at h
  exact h

theorem isCoboundary_nat_omegaMinus_six {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK : 2 < Nat.card K) {b d : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + d ≠ 0)
    (c : StatedOmega (StatedQuadMinus 3 K b d) →
      Multiplicative ((Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) → K))
    (hc : IsCocycle
      ((s16gNatHom (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) K).comp
        (StatedOmega (StatedQuadMinus 3 K b d)).subtype) c) :
    IsCoboundary
      ((s16gNatHom (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) K).comp
        (StatedOmega (StatedQuadMinus 3 K b d)).subtype) c :=
  isCoboundary_of_isCoboundary_sigma b d hirr hK hc

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
