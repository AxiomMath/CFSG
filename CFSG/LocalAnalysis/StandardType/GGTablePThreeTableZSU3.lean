module

public import CFSG.LocalAnalysis.StandardType.GGTablePThreeTableZDefs
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeE6RatLabel
public import CFSG.LocalAnalysis.StandardType.GGNbrTableForms
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.E6ThreeScLift
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompSUStd
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcInnerLang.TwE6
import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.InnExcSuNHom
import CFSG.LieType.Steinberg.CentralExt.SUOddClosed
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompSUAut
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.PlanesSetup
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.RigidCriterion
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.RigidNorm
public import CFSG.RankThree.PartOne.KE.E7FiveBlock
import CFSG.HardMathSupport.Timmesfeld.LangTorus.CentralizerTrivialPoly
import CFSG.HardMathSupport.Timmesfeld.LangTorus.OuterField
import CFSG.HardMathSupport.Timmesfeld.LangTorus.RigidField

public section

namespace CFSG.StandardType.TablePThreeKG

open CFSG CFSG.Assembly CFSG.RankThree.PerfectCover CFSG.Blueprint.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LieType.Chevalley CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped MatrixGroups

open CFSG.HardMathSupport.Timmesfeld.CrossChar in
theorem tableZ_exists_lift_su3
    {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {f : ℕ} (hf : 2 ≤ f)
    (σQ : L ≃+* L) (hσQ : ∀ c, σQ c = c ^ (2 ^ f))
    {G C : Type} [Group G] [Group C] [Finite G] {π : G →* C} (hπ : Function.Surjective π)
    (hker : π.ker ≤ Subgroup.center G)
    (ρ₀ : ↥(CFSG.RankThree.Classical2.fixSubgroup (stdUnitaryEquiv (ν := 3) σQ)) →* C) :
    ∃ ρ : ↥(CFSG.RankThree.Classical2.fixSubgroup (stdUnitaryEquiv (ν := 3) σQ)) →* G,
      π.comp ρ = ρ₀ := by
  have hf1 : 1 ≤ f := by omega
  have h2f : (2 : ℕ) ^ f ≠ 2 := by
    intro h
    have h4 : 4 ≤ 2 ^ f := by
      calc (4 : ℕ) = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
    omega
  have hq : (3, 2 ^ f) ≠ (3, 2) := fun hh => h2f (Prod.mk.inj hh).2
  obtain ⟨F, hFcard, ⟨eC⟩⟩ :=
    CFSG.HardMathSupport.Dickson.Sec6.Up34Exc.two_suN_exists_equiv (ν := 3)
      Nat.prime_two hf1 σQ hσQ le_rfl
  haveI : Finite F := Nat.finite_of_card_ne_zero (by
    rw [hFcard]
    exact (pow_pos (pow_pos (by norm_num : (0 : ℕ) < 2) f) 2).ne')
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP F 2 := RingHom.charP (algebraMap F L) Subtype.coe_injective 2
  let ρ₀' : CFSG.Open.StatedSU 3 (2 ^ f) F →* C := ρ₀.comp eC.toMonoidHom
  obtain ⟨s, hs⟩ :=
    CFSG.LieType.Steinberg.CentralExt.SUOdd.statedSU_odd_exists_section_of_central
      (p := 2) (f := f) (F := F) hFcard hf1 (n := 3) le_rfl (by norm_num) hq
      (π := CFSG.LieType.Steinberg.pullbackFst ρ₀' π)
      (CFSG.LieType.Steinberg.pullbackFst_surjective (β := ρ₀') (η := π) hπ)
      (CFSG.LieType.Steinberg.ker_pullbackFst_le_center (β := ρ₀') (η := π) hker)
  refine ⟨((MonoidHom.snd (CFSG.Open.StatedSU 3 (2 ^ f) F) G).comp
    ((CFSG.LieType.Steinberg.pullback ρ₀' π).subtype.comp s)).comp eC.symm.toMonoidHom, ?_⟩
  ext x
  have h1 : ((s (eC.symm x) : CFSG.LieType.Steinberg.pullback ρ₀' π) :
      CFSG.Open.StatedSU 3 (2 ^ f) F × G).1 = eC.symm x := hs (eC.symm x)
  have h2' := CFSG.LieType.Steinberg.mem_pullback.1 (s (eC.symm x)).2
  rw [h1] at h2'
  show π (((s (eC.symm x) : CFSG.LieType.Steinberg.pullback ρ₀' π) :
    CFSG.Open.StatedSU 3 (2 ^ f) F × G).2) = ρ₀ x
  rw [← h2']
  show ρ₀ (eC (eC.symm x)) = ρ₀ x
  rw [MulEquiv.apply_symm_apply]

end CFSG.StandardType.TablePThreeKG

end
