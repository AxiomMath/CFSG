module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeTriD4PinnedNative
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeTriD4NormalForm
import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeTriD4FrameE

public section

namespace CFSG.StandardType.RCKRP

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.StandardType.GGFinModel
  CFSG.RankThree.PartOne.KD4T CFSG.RankThree.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.Steinberg.Adjoint


theorem symmetrizedCartan_d4Id {τ : Tag} [E6Sub τ] (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    (k l : Fin Tag.D4.rank) :
    τ.symmetrizedCartan (d4Id k) (d4Id l) = Tag.D4.symmetrizedCartan k l := by
  have h1 : τ.symmetrizedCartan = τ.cartan := by
    rcases hτ with rfl | rfl | rfl <;> exact one_mul _
  have h2 : Tag.D4.symmetrizedCartan = Tag.D4.cartan := one_mul _
  rw [h1, h2, cartan_d4Id]

theorem rckTriD4PinnedFrame_of_nativeEquiv
    {τ : Tag} [E6Sub τ] (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {p₀ : ℕ} (S : LangSetup τ GGL p₀)
    (ε : ↥(adjointGroup Tag.D4 GGL) ≃* ↥(subsystemGroup τ GGL (d4Set τ)))
    (hεx : ∀ (k : Fin Tag.D4.rank) (c : GGL),
      (ε ⟨xUnit Tag.D4 GGL k c, xUnit_mem_adjointGroup k c⟩ : ModGL τ GGL) =
        xUnit τ GGL (d4Id k) c)
    (hεy : ∀ (k : Fin Tag.D4.rank) (c : GGL),
      (ε ⟨yUnit Tag.D4 GGL k c, yUnit_mem_adjointGroup k c⟩ : ModGL τ GGL) =
        yUnit τ GGL (d4Id k) c)
    {a : Fin τ.rank → GGLˣ} (hT : rootDiagUnit τ a ∈ S.D.torus) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hTp : rootDiagUnit τ a ^ p = 1) (i : KernelComponent (rootCharHom a))
    {h : ℕ} (hq : S.D.q = 2 ^ h)
    (hr : compRank (componentRoots (rootCharHom a) i) = 4)
    (hc : (componentRoots (rootCharHom a) i).ncard = 24)
    (h2 : ¬ twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin τ.rank → ℤ) → _)^[2 * componentOrbitLength S.ρ
        (componentRoots (rootCharHom a) i)])) :
    componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) = 1 ∧
      RCKTriD4PinnedFrame S (componentRoots (rootCharHom a) i) h := by
  have hpL : (p : GGL) ≠ 0 := fun h0 =>
    hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).1
      ((CharP.cast_eq_zero_iff GGL 2 p).1 h0)).symm
  obtain ⟨hs, v, Fr, hFr, hΨ, u, t, N, e, hu, he, hN, hNx, hNy, hstep⟩ :=
    exists_triD4_normalForm hτ S hT hp hpL hTp i hr hc h2
  have hFr2 : Fr = iterateFrobenius GGL 2 h := by
    ext c
    rw [hFr, hq, iterateFrobenius_def]
  subst hFr2
  have hqQ : canonicalRep (coxeterSystem τ) GGL u *
      (torusElt τ GGL (d4Id 0) (t 0) * torusElt τ GGL (d4Id 1) (t 1) *
        torusElt τ GGL (d4Id 2) (t 2) * torusElt τ GGL (d4Id 3) (t 3))⁻¹ ∈
      subsystemGroup τ GGL (d4Set τ) :=
    mul_mem (canonicalRep_mem_subsystemGroup hu) (inv_mem (d4TorusWord_mem_subsystemGroup t))
  exact ⟨hs, rckTriD4PinnedFrame_of_native S ε hεx hεy (symmetrizedCartan_d4Id hτ) v hΨ he hqQ
    (native_symm_mem_monomialSubgroup ε hεx hεy hu t rfl hqQ) hN hNx hNy (fun g _ => hstep g)⟩

theorem rckTriD4PinnedFrame_exc
    {τ : Tag} (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {p₀ : ℕ} (S : LangSetup τ GGL p₀)
    {a : Fin τ.rank → GGLˣ} (hT : rootDiagUnit τ a ∈ S.D.torus) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hTp : rootDiagUnit τ a ^ p = 1) (i : KernelComponent (rootCharHom a))
    {h : ℕ} (hq : S.D.q = 2 ^ h)
    (hr : compRank (componentRoots (rootCharHom a) i) = 4)
    (hc : (componentRoots (rootCharHom a) i).ncard = 24)
    (h2 : ¬ twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin τ.rank → ℤ) → _)^[2 * componentOrbitLength S.ρ
        (componentRoots (rootCharHom a) i)])) :
    componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) = 1 ∧
      RCKTriD4PinnedFrame S (componentRoots (rootCharHom a) i) h := by
  rcases hτ with rfl | rfl | rfl
  · obtain ⟨ε, hεx, hεy⟩ := rckTriD4_d4NativeEquiv (τ := .E6) (L := GGL)
    exact rckTriD4PinnedFrame_of_nativeEquiv (Or.inl rfl) S ε hεx hεy hT hp hp2 hTp i hq hr hc h2
  · obtain ⟨ε, hεx, hεy⟩ := rckTriD4_d4NativeEquiv (τ := .E7) (L := GGL)
    exact rckTriD4PinnedFrame_of_nativeEquiv (Or.inr (Or.inl rfl)) S ε hεx hεy hT hp hp2 hTp i
      hq hr hc h2
  · obtain ⟨ε, hεx, hεy⟩ := rckTriD4_d4NativeEquiv (τ := .E8) (L := GGL)
    exact rckTriD4PinnedFrame_of_nativeEquiv (Or.inr (Or.inr rfl)) S ε hεx hεy hT hp hp2 hTp i
      hq hr hc h2

end CFSG.StandardType.RCKRP
