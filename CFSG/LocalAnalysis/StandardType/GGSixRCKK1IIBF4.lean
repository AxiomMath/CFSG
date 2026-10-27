module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKK1IIBPair
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2LongF4
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2OddCenter
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionOddCoreCover
public import CFSG.LieType.Steinberg.Adjoint.Group

public section

namespace CFSG.StandardType.RCKK1II

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.StandardType CFSG.StandardType.S2MathFi1035Pos CFSG.StandardType.RCKC1 CFSG.Open
  CFSG.LieType.Chevalley CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.HighestRoot CFSG.SeitzReduction CFSG.Blueprint.Chevalley
  CFSG.StandardType.LieKnownR2.Short CFSG.StandardType.LieKnownR2.OddCenter
  CFSG.LieType.Chevalley.RootOps
open scoped commutatorElement

private abbrev rckp4_theta : Fin (Tag.rank .F4) → ℤ := ![2, 3, 4, 2]

private abbrev rckp4_gamma : Fin (Tag.rank .F4) → ℤ := ![1, 3, 4, 2]

private abbrev rckp4_delta : Fin (Tag.rank .F4) → ℤ := ![-1, 0, 0, 0]

private theorem rckp4_theta_eq_highRoot : rckp4_theta = CFSG.SeitzReduction.highRoot .F4 := rfl

private theorem rckp4_delta_add_theta : rckp4_delta + rckp4_theta = rckp4_gamma := by
  decide +kernel

private theorem rckp4_theta_pos : ∀ j : Fin (Tag.rank .F4), 0 < rckp4_theta j := by
  decide +kernel

private theorem rckp4_gamma_pos : ∀ j : Fin (Tag.rank .F4), 0 < rckp4_gamma j := by
  decide +kernel

private theorem rckp4_theta_ne_zero : rckp4_theta ≠ 0 := by
  decide +kernel

private theorem rckp4_isRoot_theta : IsRoot .F4 rckp4_theta := by
  rw [rckp4_theta_eq_highRoot]
  exact CFSG.SeitzReduction.isRoot_highRoot .F4

private theorem rckp4_isRoot_gamma :
    IsRoot .F4 rckp4_gamma := by
  rw [← CFSG.LieType.Chevalley.RootOps.isRootB_iff]
  decide +kernel

private theorem rckp4_isRoot_delta :
    IsRoot .F4 rckp4_delta := by
  rw [← CFSG.LieType.Chevalley.RootOps.isRootB_iff]
  decide +kernel

private theorem rckp4_isRoot_gamma_add :
    IsRoot .F4 (rckp4_delta + rckp4_theta) := by
  rw [rckp4_delta_add_theta]
  exact rckp4_isRoot_gamma

private theorem rckp4_not_isRoot_theta_add_gamma :
    ¬ IsRoot .F4 (rckp4_theta + rckp4_gamma) := by
  have h : CFSG.LieType.Chevalley.RootOps.isRootB .F4 (rckp4_theta + rckp4_gamma) = false := by
    decide +kernel
  intro hr
  rw [← CFSG.LieType.Chevalley.RootOps.isRootB_iff] at hr
  rw [h] at hr
  exact Bool.noConfusion hr

private theorem rckp4_not_isRoot_theta_sub_delta :
    ¬ IsRoot .F4 (rckp4_theta - rckp4_delta) := by
  have h : CFSG.LieType.Chevalley.RootOps.isRootB .F4 (rckp4_theta - rckp4_delta) = false := by
    decide +kernel
  intro hr
  rw [← CFSG.LieType.Chevalley.RootOps.isRootB_iff] at hr
  rw [h] at hr
  exact Bool.noConfusion hr

private theorem rckp4_not_isRoot_delta_add_two_theta :
    ¬ IsRoot .F4 (rckp4_delta + 2 • rckp4_theta) := by
  have h : CFSG.LieType.Chevalley.RootOps.isRootB .F4
      (rckp4_delta + 2 • rckp4_theta) = false := by decide +kernel
  intro hr
  rw [← CFSG.LieType.Chevalley.RootOps.isRootB_iff] at hr
  rw [h] at hr
  exact Bool.noConfusion hr

private theorem rckp4_not_isRoot_two_delta_add_theta :
    ¬ IsRoot .F4 (2 • rckp4_delta + rckp4_theta) := by
  have h : CFSG.LieType.Chevalley.RootOps.isRootB .F4
      (2 • rckp4_delta + rckp4_theta) = false := by decide +kernel
  intro hr
  rw [← CFSG.LieType.Chevalley.RootOps.isRootB_iff] at hr
  rw [h] at hr
  exact Bool.noConfusion hr

private theorem rckp4_coeff11_natAbs
    (F : CFSG.LieType.Chevalley.RootOperatorFamily .F4)
    (hD : CFSG.LieType.Steinberg.Adjoint.f4Data.Valid) :
    (RootOperatorFamily'.coeff11 F hD ⟨rckp4_delta, rckp4_isRoot_delta⟩
        ⟨rckp4_theta, rckp4_isRoot_theta⟩).natAbs = 1 := by
  have hne : (⟨rckp4_theta, rckp4_isRoot_theta⟩ : Root .F4).1
      ≠ -(⟨rckp4_delta, rckp4_isRoot_delta⟩ : Root .F4).1 := by
    show rckp4_theta ≠ -rckp4_delta
    decide +kernel
  have hsum : IsRoot .F4 ((⟨rckp4_delta, rckp4_isRoot_delta⟩ : Root .F4).1
      + (⟨rckp4_theta, rckp4_isRoot_theta⟩ : Root .F4).1) := by
    simpa using rckp4_isRoot_gamma_add
  rw [RootOperatorFamily'.coeff11,
    RootOperatorFamily'.bracketCoeff_natAbs (F := F) (hD := hD)
      (β := ⟨rckp4_delta, rckp4_isRoot_delta⟩)
      (γ := ⟨rckp4_theta, rckp4_isRoot_theta⟩) hne hsum]
  exact stringNorm_of_not_isRoot rckp4_not_isRoot_theta_sub_delta

private theorem rckp4_commutator
    (F : CFSG.LieType.Chevalley.RootOperatorFamily .F4)
    (hD : CFSG.LieType.Steinberg.Adjoint.f4Data.Valid) :
    ⁅xPar F rckp4_delta (1 : GaloisField 2 1), xPar F rckp4_theta (1 : GaloisField 2 1)⁆
      = xPar F rckp4_gamma (1 : GaloisField 2 1) := by
  have h := commutator_xPar (F := F) (D := CFSG.LieType.Steinberg.Adjoint.f4Data)
    (K := GaloisField 2 1) hD noG2_F4
    rckp4_isRoot_delta rckp4_isRoot_theta
    (show rckp4_delta ≠ rckp4_theta by decide +kernel)
    (show rckp4_delta ≠ -rckp4_theta by decide +kernel) (1 : GaloisField 2 1) 1
  rw [rckp4_delta_add_theta] at h
  rw [xPar_of_not_isRoot rckp4_not_isRoot_delta_add_two_theta,
    xPar_of_not_isRoot rckp4_not_isRoot_two_delta_add_theta, mul_one, mul_one] at h
  have hcast : ((RootOperatorFamily'.coeff11 F hD ⟨rckp4_delta, rckp4_isRoot_delta⟩
      ⟨rckp4_theta, rckp4_isRoot_theta⟩ : ℤ) : GaloisField 2 1) = 1 := by
    rcases Int.natAbs_eq_iff.1 (rckp4_coeff11_natAbs F hD) with h1 | h1 <;>
      · rw [h1]; simp [CharTwo.neg_eq]
  rw [hcast, one_mul, one_mul] at h
  exact h

private theorem rckp4_pair
    (n : ℕ) (hadm : StatedLieAdmissible .F4 n 2 1) :
    ∃ (β : Fin (Tag.rank .F4) → ℤ)
      (x : ↥(adjointGroup .F4 (GaloisField 2 1)))
      (V : Subgroup ↥(adjointGroup .F4 (GaloisField 2 1))),
      β ∈ (f4Datum (GaloisField 2 1)).roots ∧
        GGLongRoot (f4Datum (GaloisField 2 1)) β ∧
        (f4Datum (GaloisField 2 1)).rootGroup β = Subgroup.zpowers x ∧
        x * x = 1 ∧ x ≠ 1 ∧ x ∈ V ∧ IsElemAbelian 2 V ∧ Nat.card V = 4 ∧
        V ≤ pCoreOf 2 (Subgroup.normalizer
          (((f4Datum (GaloisField 2 1)).rootGroup β :
            Subgroup ↥(adjointGroup .F4 (GaloisField 2 1))) : Set _)) ∧
        ∀ v ∈ V, v ≠ 1 → ∃ j, v = j * x * j⁻¹ := by
  haveI : Finite ↥(adjointGroup .F4 (GaloisField 2 1)) :=
    CFSG.StandardType.LieKnownR2.OddCenter.finite_ggU (n := 0) (by decide)
      (show StatedLieAdmissible .F4 0 2 1 from ⟨Nat.prime_two, le_refl 1, rfl⟩)
  let F : CFSG.LieType.Chevalley.RootOperatorFamily .F4 :=
    CFSG.LieType.Chevalley.rootOperatorFamily .F4
  let x : ↥(adjointGroup .F4 (GaloisField 2 1)) := xPar F rckp4_theta 1
  let y : ↥(adjointGroup .F4 (GaloisField 2 1)) := xPar F rckp4_gamma 1
  let z : ↥(adjointGroup .F4 (GaloisField 2 1)) := xPar F rckp4_delta 1
  let V : Subgroup ↥(adjointGroup .F4 (GaloisField 2 1)) :=
    Subgroup.zpowers x ⊔ Subgroup.zpowers y
  have hθmem : rckp4_theta ∈ (f4Datum (GaloisField 2 1)).roots := by
    rw [rckp4_theta_eq_highRoot]
    exact (mem_adjDatum_roots (F := CFSG.LieType.Chevalley.rootOperatorFamily .F4)
      (K := GaloisField 2 1)).2 (CFSG.SeitzReduction.isRoot_highRoot .F4)
  have hθlong : GGLongRoot (f4Datum (GaloisField 2 1)) rckp4_theta := by
    rw [rckp4_theta_eq_highRoot]
    refine ⟨1, CFSG.SeitzReduction.highRoot .F4,
      (mem_adjDatum_roots (F := CFSG.LieType.Chevalley.rootOperatorFamily .F4)
        (K := GaloisField 2 1)).2 (CFSG.SeitzReduction.isRoot_highRoot .F4), ?_, ?_⟩
    · intro δ hδ
      have hthis := CFSG.SeitzReduction.height_le_height_highRoot
        ((mem_adjDatum_roots (F := CFSG.LieType.Chevalley.rootOperatorFamily .F4)
          (K := GaloisField 2 1)).1 hδ)
      simp only [CFSG.Blueprint.Chevalley.height] at hthis
      exact hthis
    · simp only [map_one, Module.End.one_apply]
  have hγmem : rckp4_gamma ∈ (f4Datum (GaloisField 2 1)).roots :=
    (mem_adjDatum_roots (F := CFSG.LieType.Chevalley.rootOperatorFamily .F4)
      (K := GaloisField 2 1)).2 rckp4_isRoot_gamma
  have hx2 : x * x = 1 := by
    change xPar F rckp4_theta (1 : GaloisField 2 1) * xPar F rckp4_theta 1 = 1
    have h := xPar_add (F := F) (K := GaloisField 2 1) rckp4_theta (1 : GaloisField 2 1) 1
    rw [CharTwo.add_self_eq_zero, xPar_zero] at h
    exact h.symm
  have hy2 : y * y = 1 := by
    change xPar F rckp4_gamma (1 : GaloisField 2 1) * xPar F rckp4_gamma 1 = 1
    have h := xPar_add (F := F) (K := GaloisField 2 1) rckp4_gamma (1 : GaloisField 2 1) 1
    rw [CharTwo.add_self_eq_zero, xPar_zero] at h
    exact h.symm
  have hx1 : x ≠ 1 := by
    change xPar F rckp4_theta (1 : GaloisField 2 1) ≠ 1
    intro hx
    exact one_ne_zero (xPar_injective (F := F) (K := GaloisField 2 1) rckp4_isRoot_theta
      (hx.trans (xPar_zero (F := F) rckp4_theta).symm))
  have hy1 : y ≠ 1 := by
    change xPar F rckp4_gamma (1 : GaloisField 2 1) ≠ 1
    intro hy
    exact one_ne_zero (xPar_injective (F := F) (K := GaloisField 2 1) rckp4_isRoot_gamma
      (hy.trans (xPar_zero (F := F) rckp4_gamma).symm))
  have hxy : Commute x y :=
    commute_xPar (F := F) (K := GaloisField 2 1) f4Data_valid_exact noG2_F4
      rckp4_isRoot_theta rckp4_isRoot_gamma (by decide +kernel)
      rckp4_not_isRoot_theta_add_gamma 1 1
  have hz : ⁅z, x⁆ = y := by
    change ⁅xPar F rckp4_delta (1 : GaloisField 2 1),
      xPar F rckp4_theta (1 : GaloisField 2 1)⁆ = xPar F rckp4_gamma (1 : GaloisField 2 1)
    exact rckp4_commutator F f4Data_valid_exact
  have hzx : z * x * z⁻¹ = x * y := by
    have h1 : z * x * z⁻¹ = ⁅z, x⁆ * x := by
      rw [commutatorElement_def]; group
    rw [h1, hz]
    exact (hxy.eq).symm
  have hx_ne_y : x ≠ y := by
    intro heq
    have h1 : z * x * z⁻¹ = 1 := by rw [hzx, heq, hy2]
    have h2 : z⁻¹ * (z * x * z⁻¹) * z = x := by group
    have hx1' : x = 1 := by
      calc x = z⁻¹ * (z * x * z⁻¹) * z := h2.symm
        _ = z⁻¹ * 1 * z := by rw [h1]
        _ = 1 := by group
    exact hx1 hx1'
  have hxord : orderOf x = 2 := orderOf_eq_prime (by rw [pow_two]; exact hx2) hx1
  have hyord : orderOf y = 2 := orderOf_eq_prime (by rw [pow_two]; exact hy2) hy1
  obtain ⟨hVabel, hVcard, hVenum⟩ :=
    CFSG.ProperTwoGeneratedCore.commuting_distinct_involutions_four_group
      hxord hyord hxy (Ne.symm hx_ne_y)
  have hdom : IsDominant (f4Datum (GaloisField 2 1)).isFiniteType rckp4_theta := by
    rw [rckp4_theta_eq_highRoot]
    exact (isHighestRoot_F4 (K := GaloisField 2 1)).dominant
  have hθ0 : rckp4_theta ≠ 0 := rckp4_theta_ne_zero
  have hposθ : 0 < rootForm (f4Datum (GaloisField 2 1)) rckp4_theta rckp4_theta := by
    have := form_pos_of_pos (f4Datum (GaloisField 2 1)).isFiniteType
      (r := rckp4_theta) hdom hθ0 rckp4_theta_pos
    simpa only [rootForm] using this
  have hposγ : 0 < rootForm (f4Datum (GaloisField 2 1)) rckp4_gamma rckp4_theta := by
    have := form_pos_of_pos (f4Datum (GaloisField 2 1)).isFiniteType
      (r := rckp4_theta) (β := rckp4_gamma) hdom hθ0 rckp4_gamma_pos
    simpa only [rootForm] using this
  have hxRad : x ∈ highestRootRadical (f4Datum (GaloisField 2 1)) rckp4_theta := by
    have hmem : x ∈ (f4Datum (GaloisField 2 1)).rootGroup rckp4_theta := by
      change xPar F rckp4_theta (1 : GaloisField 2 1) ∈
        (f4Datum (GaloisField 2 1)).rootGroup rckp4_theta
      exact xPar_mem (F := F) (K := GaloisField 2 1) rckp4_isRoot_theta 1
    exact Subgroup.mem_iSup_of_mem rckp4_theta
      (Subgroup.mem_iSup_of_mem ⟨hθmem, hposθ⟩ hmem)
  have hyRad : y ∈ highestRootRadical (f4Datum (GaloisField 2 1)) rckp4_theta := by
    have hmem : y ∈ (f4Datum (GaloisField 2 1)).rootGroup rckp4_gamma := by
      change xPar F rckp4_gamma 1 ∈ (f4Datum (GaloisField 2 1)).rootGroup rckp4_gamma
      exact xPar_mem (F := F) (K := GaloisField 2 1) rckp4_isRoot_gamma 1
    exact Subgroup.mem_iSup_of_mem rckp4_gamma
      (Subgroup.mem_iSup_of_mem ⟨hγmem, hposγ⟩ hmem)
  have hpcore : pCoreOf 2 (Subgroup.normalizer
      (((f4Datum (GaloisField 2 1)).rootGroup rckp4_theta :
        Subgroup ↥(adjointGroup .F4 (GaloisField 2 1))) : Set _)) =
      highestRootRadical (f4Datum (GaloisField 2 1)) rckp4_theta :=
    CFSG.StandardType.LieKnownR2.Short.pCoreOf_normalizer_rootGroup_highRoot_F4
      (GaloisField 2 1)
  have hVcore : V ≤ pCoreOf 2 (Subgroup.normalizer
      (((f4Datum (GaloisField 2 1)).rootGroup rckp4_theta :
        Subgroup ↥(adjointGroup .F4 (GaloisField 2 1))) : Set _)) := by
    rw [hpcore]
    refine sup_le ?_ ?_
    · rw [Subgroup.zpowers_le]; exact hxRad
    · rw [Subgroup.zpowers_le]; exact hyRad
  have hcard_group : Nat.card ((f4Datum (GaloisField 2 1)).rootGroup rckp4_theta) = 2 := by
    have hbij : Function.Bijective
        (fun c : GaloisField 2 1 =>
          (⟨xPar F rckp4_theta c, xPar_mem (F := F) (K := GaloisField 2 1)
            rckp4_isRoot_theta c⟩ :
            (f4Datum (GaloisField 2 1)).rootGroup rckp4_theta)) := by
      constructor
      · intro a b hab
        exact xPar_injective (F := F) (K := GaloisField 2 1) rckp4_isRoot_theta
          (Subtype.ext_iff.mp hab)
      · intro g
        obtain ⟨c, hc⟩ := (mem_rootGroup_iff (F := F) (K := GaloisField 2 1)
          rckp4_isRoot_theta g.1).1 g.2
        exact ⟨c, Subtype.ext hc⟩
    calc Nat.card ((f4Datum (GaloisField 2 1)).rootGroup rckp4_theta)
        = Nat.card (GaloisField 2 1) := (Nat.card_congr (Equiv.ofBijective _ hbij)).symm
      _ = 2 := by rw [GaloisField.card]; norm_num; norm_num
  have hroot : (f4Datum (GaloisField 2 1)).rootGroup rckp4_theta = Subgroup.zpowers x := by
    have hle : Subgroup.zpowers x ≤ (f4Datum (GaloisField 2 1)).rootGroup rckp4_theta := by
      rw [Subgroup.zpowers_le]
      change xPar F rckp4_theta 1 ∈ (f4Datum (GaloisField 2 1)).rootGroup rckp4_theta
      exact xPar_mem (F := F) (K := GaloisField 2 1) rckp4_isRoot_theta 1
    have hcard_z : Nat.card (Subgroup.zpowers x) = 2 := (Nat.card_zpowers x).trans hxord
    have hcard_le : Nat.card ((f4Datum (GaloisField 2 1)).rootGroup rckp4_theta) ≤
        Nat.card (Subgroup.zpowers x) := by
      rw [hcard_group, hcard_z]
    exact (Subgroup.eq_of_le_of_card_ge hle hcard_le).symm
  have hWeyl : ∃ j : ↥(adjointGroup .F4 (GaloisField 2 1)), y = j * x * j⁻¹ := by
    obtain ⟨ε, hε, hconj⟩ :=
      weylElement_xPar_conj (F := F) (K := GaloisField 2 1) (i := ⟨0, by decide⟩)
        rckp4_isRoot_theta
    refine ⟨weylElement (xPar F) ⟨0, by decide⟩ (1 : (GaloisField 2 1)ˣ), ?_⟩
    have h := hconj (1 : (GaloisField 2 1)ˣ) 1
    have href : (reflection (Tag.cartan .F4) ⟨0, by decide⟩) rckp4_theta = rckp4_gamma := by
      rw [reflection_apply_coroot, coroot_apply]
      decide +kernel
    rw [href] at h
    have hεK : (ε : GaloisField 2 1) = 1 := by
      rcases hε with h1 | h1 <;> rw [h1] <;> simp [CharTwo.neg_eq]
    simp only [one_zpow, Units.val_one, mul_one, hεK] at h
    exact h.symm
  refine ⟨rckp4_theta, x, V, hθmem, hθlong, hroot, hx2, hx1,
    Subgroup.mem_sup_left (Subgroup.mem_zpowers x), hVabel, hVcard, hVcore, ?_⟩
  intro v hv hv1
  rcases hVenum v hv with h | h | h | h
  · exact (hv1 h).elim
  · exact ⟨1, by rw [h]; group⟩
  · obtain ⟨j, hj⟩ := hWeyl
    exact ⟨j, by rw [h]; exact hj⟩
  · exact ⟨z, by rw [h]; exact hzx.symm⟩

theorem rckIIPair_F4
    (n : ℕ) (hadm : StatedLieAdmissible .F4 n 2 1) : RCKIIPair .F4 n := by
  unfold RCKIIPair
  exact rckp4_pair n hadm

end CFSG.StandardType.RCKK1II
