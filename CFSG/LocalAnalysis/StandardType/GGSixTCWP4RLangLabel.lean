module

public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4RDefs
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4Inputs
public import CFSG.LocalAnalysis.StandardType.GGExcCompFieldInput
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4ULang

public section

namespace CFSG.StandardType.TableCRes

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.HardMathSupport.Timmesfeld.LangTorus
open CFSG.Assembly (LargeEvenLabel LargeEvenInLambda2 LargeEvenLieTag)
open CFSG.StandardType (GGLabelIso GGHasLabel)
open CFSG.Blueprint (LieModel)

section Labels

theorem tc_three_dvd_card
    {G : Type} [Group G] {K : Subgroup G} {m : ℕ}
    (h : GGCompFieldAtSL (2 ^ m) K) : 3 ∣ Nat.card ↥K := by
  have h3 : 2 ^ 2 - 1 ∣ (2 ^ m) ^ 2 - 1 := sq_sub_one_dvd_pow_sq_sub_one 2 m
  have h3' : 3 ∣ (2 ^ m) ^ 2 - 1 := by simpa using h3
  exact h3'.trans (ggCompFieldAt_dvd h.toAt)

theorem tc_langLabel
    (hR2 : LangFamilyCompLabel) {τ : Tag} (hτ : τ = .E6 ∨ τ = .E8) {Lf : Type} [Field Lf]
    [IsAlgClosed Lf] [CharP Lf 2] {p₀ p f : ℕ} (S : LangSetup τ Lf p₀) (hp : p.Prime)
    (hp2 : p ≠ 2) (hq : S.D.q = 2 ^ f) {ι : Type} (a : ι → Fin τ.rank → Lfˣ)
    (hT : ∀ u, rootDiagUnit τ (a u) ∈ S.D.torus) (hap : ∀ u j, a u j ^ p = 1)
    {K : Subgroup (ModGL τ Lf)}
    (hK : IsComponentOf K (S.Γ ⊓ Subgroup.centralizer (Set.range fun u => rootDiagUnit τ (a u))))
    (i : KernelComponent (famCharHom a))
    (hspan : K ≤ rootSpan τ Lf (famOrbit S.ρ a i)) :
    GGCompLabelAt (LabAt S.ρ f (componentRoots (famCharHom a) i)) K := by
  obtain ⟨n, hn, hlab⟩ := hR2 τ Lf p₀ p S hτ hp hp2 ι a hT hap K hK i hspan
  have h2 : (2 : ℕ) ^ n =
      2 ^ (componentOrbitLength S.ρ (componentRoots (famCharHom a) i) * f) := by
    rw [hn, hq, ← pow_mul, mul_comm]
  have hnf := Nat.pow_right_injective (le_refl 2) h2
  unfold LabAt
  rw [← hnf]
  exact hlab

theorem tc_labelIso_of_compLabel
    {G : Type} [Group G] {K : Subgroup G} {lab lab' : LargeEvenLabel}
    (h : GGCompLabelAt lab K) (h' : GGCompLabelAt lab' K) : GGLabelIso lab lab' := by
  obtain ⟨h1, -, h3, -⟩ := h
  obtain ⟨h1', -, h3', -⟩ := h'
  exact ggLabelRigidInput_holds lab lab' (↥K ⧸ Subgroup.center ↥K) h1 h1' h3 h3'

theorem tc_lieModel_of_labAt {G : Type} [Group G] {X : Subgroup G} {τ : Tag}
    {ρ : Equiv.Perm (Fin τ.rank → ℤ)} {Ψ : Set (Fin τ.rank → ℤ)} {r e f : ℕ}
    (hr : compRank Ψ = r) (hN : Ψ.ncard = r * (r + 1)) (hk : twistKindOf ρ Ψ = .inner)
    (he : componentOrbitLength ρ Ψ = e) (hlab : GGCompLabelAt (LabAt ρ f Ψ) X) :
    LieModel (↥X ⧸ Subgroup.center ↥X) .PSL (r + 1) 2 (e * f) := by
  have hLab : LabAt ρ f Ψ = ⟨LargeEvenLieTag.A, r, e * f⟩ := by
    unfold LabAt
    rw [hk, hr, hN, he]
    simp [componentLabel]
  unfold GGCompLabelAt at hlab
  rw [hLab] at hlab
  obtain ⟨-, -, -, R, _, hR, ⟨θ⟩⟩ := hlab
  have hR' : LieModel R .PSL (r + 1) 2 (e * f) := hR
  exact lieModel_of_mulEquiv' θ.symm hR'

end Labels

end CFSG.StandardType.TableCRes

end
