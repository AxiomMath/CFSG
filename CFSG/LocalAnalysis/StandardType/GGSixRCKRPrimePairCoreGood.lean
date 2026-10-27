module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeIncidence

public section

namespace CFSG.StandardType.RCKRP

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis
  CFSG.StandardType.GGFinModel

theorem rckConj_mem_commutator {G : Type*} [Group G] {M : Subgroup G} {h : G} (hh : h ∈ M)
    {u : G} (hu : u ∈ ⁅M, M⁆) : h⁻¹ * u * h ∈ ⁅M, M⁆ := by
  have hle : ⁅M, M⁆ ≤ (⁅M, M⁆).comap (MulAut.conj h⁻¹).toMonoidHom := by
    rw [Subgroup.commutator_le]
    intro x hx y hy
    rw [Subgroup.mem_comap, map_commutatorElement]
    exact Subgroup.commutator_mem_commutator
      (by simpa using M.mul_mem (M.mul_mem (M.inv_mem hh) hx) hh)
      (by simpa using M.mul_mem (M.mul_mem (M.inv_mem hh) hy) hh)
  simpa using hle hu

theorem rckMem_normalizer_of_conjSub_eq {G : Type*} [Group G] {A B : Subgroup G} {g : G}
    (hAB : conjSub g A = B) {x : G} (hx : x ∈ Subgroup.normalizer (B : Set G)) :
    g⁻¹ * x * g ∈ Subgroup.normalizer (A : Set G) := by
  have hy : ∀ y : G, y ∈ A ↔ g * y * g⁻¹ ∈ B := fun y => by
    rw [← hAB, mem_conjSub_iff]
    simp [mul_assoc]
  rw [Subgroup.mem_normalizer_iff] at hx ⊢
  intro y
  have e : g * ((g⁻¹ * x * g) * y * (g⁻¹ * x * g)⁻¹) * g⁻¹ = x * (g * y * g⁻¹) * x⁻¹ := by group
  rw [hy y, hy ((g⁻¹ * x * g) * y * (g⁻¹ * x * g)⁻¹), e]
  exact hx (g * y * g⁻¹)


@[expose] def RCKPairCoreGood {τ : Tag} (S : LangSetup τ GGL 5) : Prop :=
  ∃ (γ : Fin τ.rank → ℤ) (z : ModGL τ GGL), IsRoot τ γ ∧ z ∈ adjointGroup τ GGL ∧
    ((rootSubgroup τ GGL γ).map (MulAut.conj z).toMonoidHom).map S.D.step =
        (rootSubgroup τ GGL γ).map (MulAut.conj z).toMonoidHom ∧
    ((rootSubgroup τ GGL (-γ)).map (MulAut.conj z).toMonoidHom).map S.D.step =
        (rootSubgroup τ GGL (-γ)).map (MulAut.conj z).toMonoidHom ∧
    ∀ r ∈ S.D.model, ∃ u ∈ S.Γ,
      u⁻¹ * r ∈ Subgroup.normalizer ((rootSubgroup τ GGL γ).map (MulAut.conj z).toMonoidHom) ∧
      u⁻¹ * r ∈ Subgroup.normalizer ((rootSubgroup τ GGL (-γ)).map (MulAut.conj z).toMonoidHom)

theorem rckFramePairCore_of_good
    (hgood : ∀ (τ : Tag), (τ = Tag.D4 ∨ τ = Tag.E6 ∨ τ = Tag.E7) → ∀ S : LangSetup τ GGL 5,
      RCKPairCoreGood S) : RCKFramePairCore := by
  intro τ hτ S γ hγ z hz h1 h2 r hr
  obtain ⟨γ0, z0, hγ0, hz0, h10, h20, hcore⟩ := hgood τ hτ S
  obtain ⟨h, hhM, hp, hm⟩ := rckPairFixedConj hτ S hγ hγ0 hz hz0 h1 h2 h10 h20
  have hr' : h * r * h⁻¹ ∈ S.D.model := mul_mem (mul_mem hhM hr) (inv_mem hhM)
  obtain ⟨u', hu', hn1, hn2⟩ := hcore _ hr'
  have key : h⁻¹ * (u'⁻¹ * (h * r * h⁻¹)) * h = (h⁻¹ * u' * h)⁻¹ * r := by group
  refine ⟨h⁻¹ * u' * h, rckConj_mem_commutator hhM hu', ?_, ?_⟩
  · rw [← key]
    exact rckMem_normalizer_of_conjSub_eq hp hn1
  · rw [← key]
    exact rckMem_normalizer_of_conjSub_eq hm hn2

end CFSG.StandardType.RCKRP
