module

public import CFSG.LocalAnalysis.StandardType.GGFamLabelAssembly
public import CFSG.LocalAnalysis.StandardType.GGNbrTableForms
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4Inputs2
public import CFSG.LocalAnalysis.StandardType.GGFinModelRat
import CFSG.LocalAnalysis.StandardType.GGLabelRigid
import CFSG.LocalAnalysis.StandardType.GGSecFiveNonWeylOfKnown
import CFSG.LocalAnalysis.StandardType.GGSixTCWP4RFam
import CFSG.LocalAnalysis.StandardType.GGSixRCKU33Transport
import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.InnExcLang
import CFSG.HardMathSupport.Curtis.Coordinator.SeitzTower.Rest
import CFSG.HardMathSupport.Lang.Coordinator.OuterFixedOrderE6Order
import CFSG.LocalAnalysis.ComponentInitial.SteinbergBUProjectivePlaneFieldRoot
import CFSG.LocalAnalysis.GLTheoremA.CatA.HG2InnMain
import CFSG.LocalAnalysis.RankThreeTheoremC.RelativePairInputs
import CFSG.RankThree.PartOne.KF.F128Count
import CFSG.RankThree.PartOne.S11b.OuterPrimeTwoSporadicOpen
public import CFSG.LocalAnalysis.StandardType.GGFamAssembly

public section

namespace CFSG.StandardType.LangComponentLabel

open CFSG CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Universal
  CFSG.LieType.Chevalley CFSG.LieType.RootSystem CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.StandardType.GGFinModel
  CFSG.LieType.AlgebraicGroups CFSG.StandardType.TableCRes


theorem exists_componentLabel_rationalComponent {τ : Tag} (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {p₀ p : ℕ} (S : LangSetup τ L p₀)
    (hp : p.Prime) (hp2 : p ≠ 2) {a : Fin τ.rank → Lˣ} (hT : rootDiagUnit τ a ∈ S.D.torus)
    (hap : ∀ j, a j ^ p = 1) (i : KernelComponent (rootCharHom a))
    (hq : CFSG.IsQuasisimple ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) :
    ∃ m : ℕ, 2 ^ m = S.D.q ^ componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) ∧
      GGCompLabelAt (componentLabel (compRank (componentRoots (rootCharHom a) i))
          (componentRoots (rootCharHom a) i).ncard
          (twistKindOf S.ρ (componentRoots (rootCharHom a) i)) m)
        (rationalComponent S.ρ S.Γ (rootCharHom a) i) := by
  classical
  let a' : PUnit.{1} → Fin τ.rank → Lˣ := fun _ => a
  have hT' : ∀ u, rootDiagUnit τ (a' u) ∈ S.D.torus := fun _ => hT
  have hap' : ∀ u j, a' u j ^ p = 1 := fun _ j => hap j
  have hrange : (Set.range fun u : PUnit.{1} => rootDiagUnit τ (a' u)) = {rootDiagUnit τ a} := by
    ext z
    constructor
    · rintro ⟨u, rfl⟩
      exact Set.mem_singleton _
    · rintro rfl
      exact ⟨PUnit.unit, rfl⟩
  have hK : CFSG.Open.IsComponentOf (rationalComponent S.ρ S.Γ (rootCharHom a) i)
      (S.Γ ⊓ Subgroup.centralizer (Set.range fun u : PUnit.{1} => rootDiagUnit τ (a' u))) := by
    rw [hrange]
    exact CFSG.HardMathSupport.Dickson.Sec6.Up34Exc.isComponentOf_rationalComponent S hT i hq
  obtain ⟨i', hi'⟩ := exists_componentRoots_eq (kernelRoots_famChar_punit_eq a).symm i
  have hspan : rationalComponent S.ρ S.Γ (rootCharHom a) i ≤
      rootSpan τ L (famOrbit S.ρ a' i') := by
    have hforb : famOrbit S.ρ a' i' = rationalRoots S.ρ (rootCharHom a) i := by
      ext γ
      simp only [famOrbit, rationalRoots, Set.mem_setOf_eq]
      rw [hi']
    rw [hforb]
    exact (Subgroup.commutator_le_self _).trans inf_le_left
  obtain ⟨m, hm, hlab⟩ := langFamilyCompLabel_exc hτ S hp hp2 a' hT' hap' hK i' hspan
  rw [← hi'] at hm hlab
  exact ⟨m, hm, hlab⟩

theorem compRank_eq_six_of_exc_of_ggHasLabel {τ : Tag} (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {p₀ : ℕ} (S : LangSetup τ GGL p₀) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {a : Fin τ.rank → GGLˣ} (hT : rootDiagUnit τ a ∈ S.D.torus) (hap : ∀ j, a j ^ p = 1)
    (i : KernelComponent (rootCharHom a))
    (hq : CFSG.IsQuasisimple ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i))
    {lab : LargeEvenLabel} (hl : LargeEvenInLambda2 lab) (htri : lab.tag ≠ .triD4)
    (hlab : GGHasLabel lab (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
      Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i))) :
    twistKindOf S.ρ (componentRoots (rootCharHom a) i) = .exc →
      compRank (componentRoots (rootCharHom a) i) = 6 := by
  intro hk
  obtain ⟨m, -, hΛ, -, hhas, -⟩ := exists_componentLabel_rationalComponent hτ S hp hp2 hT hap i hq
  have hi := ggLabelRigidInput_holds lab _ _ hl hΛ hlab hhas
  rw [hk] at hi
  by_contra h6
  simp only [componentLabel, if_neg h6] at hi
  unfold GGLabelIso at hi
  rcases hi with rfl | ⟨-, h, -⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨h, -⟩
  · exact htri rfl
  all_goals simp at h

theorem compRank_eq_six_of_exc_of_member {τ : Tag} (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {p₀ : ℕ} (S : LangSetup τ GGL p₀) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {a : Fin τ.rank → GGLˣ} (hT : rootDiagUnit τ a ∈ S.D.torus) (hap : ∀ j, a j ^ p = 1)
    (i : KernelComponent (rootCharHom a))
    (hq : CFSG.IsQuasisimple ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i))
    {K G N : Type} [Group K] [Group G] [Group N] {L : Subgroup G} {lab : LargeEvenLabel}
    (hl : LargeEvenInLambda2 lab) (hlab : GGHasLabel lab (↥L ⧸ Subgroup.center ↥L))
    (htri : lab.tag ≠ .triD4)
    (ψ : K →* G) (hψ : ψ.ker ≤ Subgroup.center K) (π : K →* N) (hπ : π.ker ≤ Subgroup.center K)
    (ι : N →* ModGL τ GGL) (hι : Function.Injective ι) {M : Subgroup K}
    (hM : commutator ↥M = ⊤) (hML : M.map ψ = L)
    (hposition : (M.map π).map ι = rationalComponent S.ρ S.Γ (rootCharHom a) i) :
    twistKindOf S.ρ (componentRoots (rootCharHom a) i) = .exc →
      compRank (componentRoots (rootCharHom a) i) = 6 := by
  subst hML
  have hιπ : (ι.comp π).ker ≤ Subgroup.center K := by
    intro k hk
    apply hπ
    rw [MonoidHom.mem_ker] at hk ⊢
    apply hι
    rw [map_one]
    exact hk
  have : Group.IsPerfect ↥M := ⟨hM⟩
  obtain ⟨e₁⟩ := CFSG.LocalAnalysis.GLTheoremA.I141F.nonempty_centerQuot_map ψ hψ (J := M) this
  obtain ⟨e₂⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.I141F.nonempty_centerQuot_map (ι.comp π) hιπ (J := M) this
  have hhas := ggHasLabel_of_mulEquiv (e₁.symm.trans e₂) hlab
  rw [← Subgroup.map_map, hposition] at hhas
  exact compRank_eq_six_of_exc_of_ggHasLabel hτ S hp hp2 hT hap i hq hl htri hhas

end CFSG.StandardType.LangComponentLabel

end
