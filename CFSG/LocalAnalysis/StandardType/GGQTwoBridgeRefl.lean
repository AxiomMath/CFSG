module

public import CFSG.LocalAnalysis.StandardType.GGQTwoLin

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Module QTwoLin

theorem ggQ2_transvectionFree {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {Bs : Subgroup G} {x y : G} {D L J K : Subgroup G}
    (M : GGQTwoModel p Bs x y D L J K) (hNT : GGNoTransvection p Bs) :
    TransvectionFree M.linGroup := by
  rintro g hg ⟨u, ψ, hu, hψ, hψu, hgv⟩
  rw [GGQTwoModel.linGroup] at hg
  obtain ⟨φ, hφ, rfl⟩ := hg
  have hφ' : φ ∈ ggInduced ⊤ Bs := by
    rw [ggAutomizer_eq] at hφ
    exact hφ
  exact hNT φ hφ' (ggIsTransvection_of_apply M.model hu hψ hψu hgv)

theorem ggQ2_reflGp_map {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {Bs : Subgroup G} {x y : G} {D L J K : Subgroup G}
    (M : GGQTwoModel p Bs x y D L J K) (hp2 : p ≠ 2) :
    (ggReflGp p Bs).map (ggLin (p := p) M.model) = reflGp M.linGroup := by
  haveI : Finite M.V := Finite.of_equiv (Additive ↥Bs) M.model.toEquiv
  have hST : ggLin (p := p) M.model '' {φ | φ ∈ ggAutomizer ⊤ Bs ∧ GGIsReflection p φ} =
      {t | t ∈ M.linGroup ∧ IsReflLin t} := by
    ext t
    constructor
    · rintro ⟨φ, ⟨hφA, hφr⟩, hφt⟩
      refine ⟨?_, ?_⟩
      · rw [GGQTwoModel.linGroup]
        exact Subgroup.mem_map.mpr ⟨φ, hφA, hφt⟩
      · obtain ⟨c, f, hcf, hφc⟩ := exists_of_ggIsReflection (p := p) M.model hφr
        exact ⟨c, f, hcf, hφt.symm.trans (ggLin_eq_reflection M.model hcf hφc)⟩
    · rintro ⟨htlin, ht⟩
      rw [GGQTwoModel.linGroup] at htlin
      obtain ⟨φ, hφA, hφt⟩ := htlin
      obtain ⟨c, g, hg, ht_eq⟩ := ht
      exact ⟨φ, ⟨hφA, ggIsReflection_of_eq_reflection hp2 M.model hg (hφt.trans ht_eq)⟩, hφt⟩
  rw [ggReflGp, reflGp, MonoidHom.map_closure, hST]

end CFSG.StandardType

end
