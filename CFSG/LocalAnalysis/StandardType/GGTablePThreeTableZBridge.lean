module

public import CFSG.LocalAnalysis.StandardType.GGTablePThreeTableZDefs
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeE6RatLabel
public import CFSG.LocalAnalysis.StandardType.GGNbrTableForms
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.E6ThreeScLift
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompSUStd
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcInnerLang.TwE6
import CFSG.LocalAnalysis.SeitzReduction.F4PilotCTGraphTwisted
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompSUAut
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.PlanesSetup
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.RigidCriterion
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.RigidNorm
public import CFSG.RankThree.PartOne.KE.E7FiveBlock
import CFSG.LocalAnalysis.SeitzReduction.E6PilotAlignField

public section

namespace CFSG.StandardType.TablePThreeKG

open CFSG CFSG.Assembly CFSG.RankThree.PerfectCover CFSG.Blueprint.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LieType.Chevalley CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped MatrixGroups

open CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Isogeny CFSG.HardMathSupport.Timmesfeld.CrossChar in
theorem tableZ_bridge
    (K : Type) [Field K] [Finite K] (σ : K ≃+* K) {n : ℕ} (hn : 1 ≤ n)
    (hK : Nat.card K = (2 ^ n) ^ 2) (hσ : ∀ c, σ c = c ^ (2 ^ n))
    (δ : MulAut ↥(TwistedE6.fixedGroup K σ.toRingHom)) (hδ3 : δ ^ 3 = 1) (hδ1 : δ ≠ 1)
    (h₀ : ModGL TwistTag.E6.tag K) (hh₀ : h₀ ∈ twistedE6InndiagGL K σ)
    (hδh : ∀ x, e6IsogenyFixed σ.toRingHom (δ x) = h₀ * e6IsogenyFixed σ.toRingHom x * h₀⁻¹)
    (J : Subgroup ↥(TwistedE6.fixedGroup K σ.toRingHom)) (hJ : IsComponentOf J (ggAutFixedSubgroup δ)) :
    ∃ (π₀ : ↥(TwistedE6.fixedGroup K σ.toRingHom) →* ↥(twistedE6RootGroup K σ))
      (h : ↥(twistedE6InndiagGL K σ)),
      (∀ x, ((π₀ x : ↥(twistedE6RootGroup K σ)) : ModGL TwistTag.E6.tag K) =
        e6IsogenyFixed σ.toRingHom x) ∧
      Function.Surjective π₀ ∧ π₀.ker ≤ Subgroup.center ↥(TwistedE6.fixedGroup K σ.toRingHom) ∧
      h ^ 3 = 1 ∧ h ≠ 1 ∧
      CFSG.Open.IsComponentOf (J.map π₀)
        (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup (twistedE6InndiagConj K σ h)) := by
  classical
  let U := ↥(TwistedE6.fixedGroup K σ.toRingHom)
  let C₀ := ↥(twistedE6RootGroup K σ)
  have hθθ : ∀ c, σ.toRingHom (σ.toRingHom c) = c :=
    CFSG.SeitzReduction.F4Pilot.involutive_of_natCard_eq hK hσ
  have hk4 : 4 ≤ Nat.card K :=
    CFSG.SeitzReduction.F4Pilot.four_le_natCard_of_eq hn hK
  let π₀ : U →* C₀ := CFSG.SeitzReduction.F4Pilot.twistedIsogenyC hn hK σ.toRingHom hσ
  have hπ₀coe : ∀ x : U, ((π₀ x : C₀) : ModGL TwistTag.E6.tag K) =
      e6IsogenyFixed σ.toRingHom x :=
    fun x => CFSG.SeitzReduction.F4Pilot.coe_twistedIsogenyC hn hK σ.toRingHom hσ x
  have hπ₀surj : Function.Surjective π₀ :=
    CFSG.SeitzReduction.F4Pilot.twistedIsogenyC_surjective hn hK σ.toRingHom hσ
  have hπ₀ker_le : π₀.ker ≤ Subgroup.center U := by
    intro x hx
    rw [Subgroup.mem_center_iff]
    intro y
    have hx1 : e6IsogenyT K (x : U) = 1 := by
      apply Subtype.ext
      have h : e6IsogenyFixed σ.toRingHom x = 1 := by
        rw [← hπ₀coe x, hx]
        rfl
      exact h
    have hxc := CFSG.LieType.Steinberg.Isogeny.ker_e6IsogenyT_le_center K
      (MonoidHom.mem_ker.mpr hx1)
    exact Subtype.ext (Subgroup.mem_center_iff.mp hxc (y : U))
  have hπ₀ker_ge : Subgroup.center U ≤ π₀.ker := by
    intro z hz
    rw [MonoidHom.mem_ker]
    have hzc : π₀ z ∈ Subgroup.center C₀ := by
      rw [Subgroup.mem_center_iff]
      intro y
      obtain ⟨x, rfl⟩ := hπ₀surj y
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hz x]
    rw [CFSG.LieType.Chevalley.exceptional_fixed_center_trivial TwistTag.E6 K σ,
      Subgroup.mem_bot] at hzc
    exact hzc
  have hπ₀ker_eq : π₀.ker = Subgroup.center U := le_antisymm hπ₀ker_le hπ₀ker_ge
  let θ : U ⧸ Subgroup.center U ≃* C₀ :=
    (QuotientGroup.quotientMulEquivOfEq hπ₀ker_eq.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective π₀ hπ₀surj)
  have hθmk : ∀ x : U, θ (x : U ⧸ Subgroup.center U) = π₀ x := by
    intro x
    change (QuotientGroup.quotientKerEquivOfSurjective π₀ hπ₀surj)
      ((QuotientGroup.quotientMulEquivOfEq hπ₀ker_eq.symm)
        (x : U ⧸ Subgroup.center U)) = π₀ x
    rw [QuotientGroup.quotientMulEquivOfEq_mk]
    rfl
  let h : ↥(twistedE6InndiagGL K σ) := ⟨h₀, hh₀⟩
  have hconj_eq : ggInducedAut θ δ = twistedE6InndiagConj K σ h := by
    refine MulEquiv.ext fun y => ?_
    obtain ⟨x, rfl⟩ := hπ₀surj y
    rw [← hθmk x, ggInducedAut_apply, hθmk (δ x)]
    apply Subtype.ext
    rw [twistedE6InndiagConj_apply, hθmk x, hπ₀coe x, hπ₀coe (δ x)]
    exact hδh x
  have hφπ : ∀ x : U, twistedE6InndiagConj K σ h (π₀ x) = π₀ (δ x) := by
    intro x
    rw [← hconj_eq, ← hθmk x, ggInducedAut_apply, hθmk (δ x)]
  have hδ3x : ∀ x : U, δ (δ (δ x)) = x := by
    intro x
    have h := congrArg (fun e : MulAut U => e x) hδ3
    rw [show (δ ^ 3) x = δ (δ (δ x)) by
      rw [pow_succ, pow_succ, pow_one, MulAut.mul_apply, MulAut.mul_apply]] at h
    simpa only [MulAut.one_apply] using h
  have hφ3 : (twistedE6InndiagConj K σ h) ^ 3 = 1 := by
    refine MulEquiv.ext fun y => ?_
    obtain ⟨x, rfl⟩ := hπ₀surj y
    have hpow : ((twistedE6InndiagConj K σ h) ^ 3) (π₀ x) =
        twistedE6InndiagConj K σ h (twistedE6InndiagConj K σ h
          (twistedE6InndiagConj K σ h (π₀ x))) := by
      rw [pow_succ, pow_succ, pow_one, MulAut.mul_apply, MulAut.mul_apply]
    rw [hpow, hφπ x, hφπ (δ x), hφπ (δ (δ x)), hδ3x, MulAut.one_apply]
  have h3 : h ^ 3 = 1 :=
    CFSG.HardMathSupport.Timmesfeld.CrossChar.twistedE6InndiagConj_injective
      Nat.prime_two hn hK σ hσ (by rw [map_pow, hφ3, map_one])
  have hUperf : Group.IsPerfect U :=
    CFSG.LieType.Steinberg.TwistedE6.fixedGroup_isPerfect_of_four_le_card σ.toRingHom hθθ hk4
  have hUcom : commutator U = ⊤ := hUperf.commutator_eq_top
  have hne : h ≠ 1 := by
    intro hh
    have hg1 : ggInducedAut θ δ = 1 := by rw [hconj_eq, hh, map_one]
    exact hδ1 (CFSG.StandardType.ggInducedAut_injective_of_perfect hUcom θ
      (by rw [hg1, map_one]))
  refine ⟨π₀, h, hπ₀coe, hπ₀surj, hπ₀ker_le, h3, hne, ?_⟩
  have hcomp : (θ : U ⧸ Subgroup.center U →* C₀).comp
      (QuotientGroup.mk' (Subgroup.center U)) = π₀ :=
    MonoidHom.ext fun x => hθmk x
  have hJbar := CFSG.StandardType.ggTorsion_isComponentOf_image θ hJ
  rw [hcomp, hconj_eq] at hJbar
  have hfix : CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup (twistedE6InndiagConj K σ h) =
      ggAutFixedSubgroup (twistedE6InndiagConj K σ h) := Subgroup.ext fun _ => Iff.rfl
  rw [hfix]
  exact isComponentOf_iff_open.mp hJbar

end CFSG.StandardType.TablePThreeKG

end
