module

public import CFSG.LocalAnalysis.StandardType.GGFamLabelAssembly
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4RLangLabel
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4RFam
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeE6KernelExit
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeExcInnerD4FixMain
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265CDynE
public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.InnExcLang
public import CFSG.HardMathSupport.Dickson.Sec6.Up34OddAux.SsTwAux.RatLayer
public import CFSG.HardMathSupport.Dickson.Sec6.Up34OddAux.SsTwAux.ExcD4Layer
public import CFSG.LocalAnalysis.StandardType.GGFamAssembly

public section

namespace CFSG.StandardType

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.Torality
  CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.ComponentClassification.PerfectAutomorphisms (centerQuotientHom)
open CFSG.GroupActions (subgroupStabAut subgroupStabRestrict)
open CFSG.LocalAnalysis.GLTheoremA.S265C.DynE (IsADETag)
open CFSG.StandardType.TableCRes
open CFSG.HardMathSupport.Dickson.Sec6 (ssTw_exists_f)
open CFSG.Assembly (LargeEvenLabel)

private theorem langComp_ade_of_componentLabel (r N n : ℕ) (k : TwistKind) :
    IsADETag (markTag (componentLabel r N k n)) ∨
      markTag (componentLabel r N k n) = .trialityD4 := by
  cases k <;> simp only [componentLabel] <;> (try split_ifs) <;>
    simp only [markTag] <;> (try split_ifs) <;> simp [IsADETag]

private theorem langComp_d4_of_componentLabel {r N n : ℕ} {k : TwistKind}
    (ht : markTag (componentLabel r N k n) = .POmegaPlus)
    (hn : markRank (componentLabel r N k n) = 4) :
    k = .inner ∧ r = 4 ∧ N = 24 := by
  cases k <;> simp only [componentLabel] at ht hn <;> (try split_ifs at ht hn) <;>
    simp only [markTag, markRank] at ht hn <;> (try split_ifs at ht hn) <;> simp_all

theorem langComp_lieModel_alternative
    {τ : Tag} (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {L : Type} [Field L] [IsAlgClosed L]
    [CharP L 2] {p₀ p : ℕ} (S : LangSetup τ L p₀) (hp : p.Prime) (hp2 : p ≠ 2)
    {a : Fin τ.rank → Lˣ} (hT : rootDiagUnit τ a ∈ S.D.torus) (hap : ∀ j, a j ^ p = 1)
    (i : KernelComponent (rootCharHom a))
    (hQS : CFSG.IsQuasisimple ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i))
    {y : ModGL τ L}
    (hyZ : y ∈ torusGroup τ L ⊔ rootSpan τ L (kernelRoots (rootCharHom a)))
    (hyF : S.D.step y = y)
    (hyStab : MulAut.conj y ∈ subgroupStabAut (rationalComponent S.ρ S.Γ (rootCharHom a) i)) :
    ∃ (t : StatedLieTag) (n f : ℕ),
      CFSG.Blueprint.LieModel (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
        Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) t n 2 f ∧
      (IsADETag t ∨ t = .trialityD4) ∧
      (¬ (t = .POmegaPlus ∧ n = 4) ∨
        centerQuotientHom ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)
            (subgroupStabRestrict (rationalComponent S.ρ S.Γ (rootCharHom a) i)
              ⟨MulAut.conj y, hyStab⟩) ∈
          CFSG.ComponentClassification.OuterAutomorphisms.inner
            (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
              Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i))) := by
  classical
  let a' : PUnit.{1} → Fin τ.rank → Lˣ := fun _ => a
  have hT' : ∀ u, rootDiagUnit τ (a' u) ∈ S.D.torus := fun _ => hT
  have hap' : ∀ u j, a' u j ^ p = 1 := fun _ j => hap j
  have hK : CFSG.Open.IsComponentOf (rationalComponent S.ρ S.Γ (rootCharHom a) i)
      (S.Γ ⊓ Subgroup.centralizer (Set.range fun u : PUnit.{1} => rootDiagUnit τ (a' u))) := by
    have hrange : (Set.range fun u : PUnit.{1} => rootDiagUnit τ (a' u)) = {rootDiagUnit τ a} := by
      ext z
      simp only [Set.mem_range, Set.mem_singleton_iff]
      constructor
      · rintro ⟨u, rfl⟩
        rfl
      · intro hz
        exact ⟨PUnit.unit, hz.symm⟩
    rw [hrange]
    exact CFSG.HardMathSupport.Dickson.Sec6.Up34Exc.isComponentOf_rationalComponent S hT i hQS
  obtain ⟨i', hi'⟩ := exists_componentRoots_eq (kernelRoots_famChar_punit_eq a).symm i
  have hspan : rationalComponent S.ρ S.Γ (rootCharHom a) i ≤
      rootSpan τ L (famOrbit S.ρ a' i') := by
    have hforb : famOrbit S.ρ a' i' = rationalRoots S.ρ (rootCharHom a) i := by
      ext γ
      simp only [famOrbit, rationalRoots, Set.mem_setOf_eq]
      rw [hi']
    rw [hforb]
    exact (Subgroup.commutator_le_self _).trans inf_le_left
  obtain ⟨f, hf1, hfq⟩ := ssTw_exists_f S (ℓ := 2)
  let lab : LargeEvenLabel := LabAt S.ρ f (componentRoots (famCharHom a') i')
  have hlab' : GGCompLabelAt lab (rationalComponent S.ρ S.Γ (rootCharHom a) i) := by
    obtain ⟨n, hn, hlabn⟩ := langFamilyCompLabel_exc hτ S hp hp2 a' hT' hap' hK i' hspan
    have h2 : (2 : ℕ) ^ n =
        2 ^ (componentOrbitLength S.ρ (componentRoots (famCharHom a') i') * f) := by
      rw [hn, hfq, ← pow_mul, mul_comm]
    have hnf := Nat.pow_right_injective (le_refl 2) h2
    change GGCompLabelAt (LabAt S.ρ f (componentRoots (famCharHom a') i')) _
    unfold LabAt
    rw [← hnf]
    exact hlabn
  obtain ⟨-, hc, -, R, instR, hR, ⟨θ⟩⟩ := hlab'
  letI : Group R := instR
  have hR2 : CFSG.Blueprint.LieModel R (markTag lab) (markRank lab) 2 (markDeg lab) := by
    unfold MarkedModel at hR
    rwa [hc] at hR
  have hLM : CFSG.Blueprint.LieModel
      (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
        Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i))
      (markTag lab) (markRank lab) 2 (markDeg lab) :=
    CFSG.LieType.CurtisTits.lieModel_of_mulEquiv θ.symm hR2
  refine ⟨markTag lab, markRank lab, markDeg lab, hLM, ?_, ?_⟩
  ·
    exact langComp_ade_of_componentLabel (compRank (componentRoots (famCharHom a') i'))
      (componentRoots (famCharHom a') i').ncard
      (componentOrbitLength S.ρ (componentRoots (famCharHom a') i') * f)
      (twistKindOf S.ρ (componentRoots (famCharHom a') i'))
  ·
    by_cases hD : markTag lab = .POmegaPlus ∧ markRank lab = 4
    · right
      have hD' : markTag (componentLabel (compRank (componentRoots (famCharHom a') i'))
            (componentRoots (famCharHom a') i').ncard
            (twistKindOf S.ρ (componentRoots (famCharHom a') i'))
            (componentOrbitLength S.ρ (componentRoots (famCharHom a') i') * f)) = .POmegaPlus ∧
          markRank (componentLabel (compRank (componentRoots (famCharHom a') i'))
            (componentRoots (famCharHom a') i').ncard
            (twistKindOf S.ρ (componentRoots (famCharHom a') i'))
            (componentOrbitLength S.ρ (componentRoots (famCharHom a') i') * f)) = 4 := hD
      obtain ⟨hk, hr, hN⟩ := langComp_d4_of_componentLabel hD'.1 hD'.2
      have hkind : twistKind S.ρ (rootCharHom a) i = .inner := by
        show twistKindOf S.ρ (componentRoots (rootCharHom a) i) = .inner
        rw [hi']
        exact hk
      have hr' : compRank (componentRoots (rootCharHom a) i) = 4 := by rw [hi']; exact hr
      have hN' : (componentRoots (rootCharHom a) i).ncard = 24 := by rw [hi']; exact hN
      have hspec := outer_componentOrbitLength_spec S hT i
      haveI : NeZero (componentOrbitLength S.ρ (componentRoots (rootCharHom a) i)) :=
        ⟨Nat.pos_iff_ne_zero.mp hspec.1⟩
      have hZ := CFSG.LocalAnalysis.GLTheoremA.T171Sh.center_eq_bot_of_compRank_four_ncard_24
        (L := L) i hr' hN'
      exact CFSG.LocalAnalysis.GLTheoremA.T171Sh.centerQuotientHom_mem_inner_twoDExcRankFour
        S hT i hspec.2.1 hspec.2.2 hZ
        (CFSG.LocalAnalysis.GLTheoremA.T171Sh.innerD4FixedPointsPerfect_holds
          S hT i hkind hr' hN') hyZ hyF hyStab
    · left
      exact hD

end CFSG.StandardType

end
