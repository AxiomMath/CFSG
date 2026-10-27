module

public import CFSG.RankThree.Coprime.PlaneCoreCentralizesComponent
public import CFSG.RankThree.GroupTheory.SteinbergBYSectionNineResidual
public import CFSG.RankThree.SteinbergR3EOrdinaryCoprimeCyclic
public import CFSG.RankThree.Chevalley.SteinbergCFExceptionalModelCover
public import CFSG.LocalAnalysis.ComponentInitial.Finkelstein1977StandardCyclic

public section

namespace CFSG.RankThree.GroupTheory.SteinbergBM

open Subgroup CFSG CFSG.RankThree.GroupTheory CFSG.RankThree.LocalRank
open CFSG.LocalAnalysis.ComponentInitial CFSG.Blueprint CFSG.Blueprint.Chevalley
open CFSG.RankThree.Automorphisms
open scoped Pointwise

variable {G : Type*} [Group G]

theorem card_ker_automizer_comp_inclusion {L E : Subgroup G} [Group.IsPerfect L]
    (hEL : E ≤ normalizer (L : Set G)) :
    Nat.card ((Finkelstein1977.automizer L).comp (inclusion hEL)).ker =
      Nat.card (E ⊓ centralizer (L : Set G) : Subgroup G) := by
  have h : ((Finkelstein1977.automizer L).comp (inclusion hEL)).ker.map E.subtype =
      E ⊓ centralizer (L : Set G) := by
    ext x
    constructor
    · rintro ⟨e, he, rfl⟩
      exact ⟨e.2, (Finkelstein1977.automizer_eq_one_iff L (inclusion hEL e)).mp
        (MonoidHom.mem_ker.mp he)⟩
    · rintro ⟨hxE, hxC⟩
      exact ⟨⟨x, hxE⟩, MonoidHom.mem_ker.mpr
        ((Finkelstein1977.automizer_eq_one_iff L (inclusion hEL ⟨x, hxE⟩)).mpr hxC), rfl⟩
  rw [← h, card_map_of_injective E.subtype_injective]

theorem plane_core_product_centralizes_of_le_card [Finite G] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {E : Subgroup G} (hE : IsElementaryAbelian p E) (hEcard : Nat.card E = p ^ 2)
    {t : G} (ht : t ∈ E) (ht1 : t ≠ 1) {L : Subgroup G} (hL : IsComponent L)
    (hXL : ⁅inSubgroup (aschbacherSolvableCore p) (centralizer ({t} : Set G)), E⁆ ≤
      normalizer (L : Set G))
    (hcard : p ≤ Nat.card (E ⊓ centralizer (L : Set G) : Subgroup G)) :
    ((⁅inSubgroup (aschbacherSolvableCore p) (centralizer ({t} : Set G)), E⁆ ⊔ thetaT p E :
        Subgroup G) : Set G) =
      ((⁅inSubgroup (aschbacherSolvableCore p) (centralizer ({t} : Set G)), E⁆ : Subgroup G) :
        Set G) * (thetaT p E : Set G) ∧
      ⁅⁅inSubgroup (aschbacherSolvableCore p) (centralizer ({t} : Set G)), E⁆, L⁆ = ⊥ ∧
      ⁅thetaT p E, L⁆ = ⊥ ∧
      ⁅inSubgroup (aschbacherSolvableCore p) (centralizer ({t} : Set G)), E⁆ ⊔ thetaT p E ≤
        centralizer (L : Set G) := by
  have hne : E ⊓ centralizer (L : Set G) ≠ ⊥ := by
    intro h
    rw [h, card_bot] at hcard
    exact absurd hcard (by have := hp.two_le; omega)
  obtain ⟨hX, hI, hW⟩ :=
    CFSG.RankThree.Coprime.nonfaithful_plane_local_core_product_centralizes_component
      hp hE hEcard ht ht1 hL hXL hne
  exact ⟨(SteinbergBY.section_nine_residual_to_intersection hp hp2 E).1 t ht ht1, hX, hI,
    commutator_eq_bot_iff_le_centralizer.mp hW⟩

theorem ordinary_exceptional_coprime_normalized_component_centralization {G : Type} [Group G]
    [Finite G] {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) {E : Subgroup G}
    (hE : IsElementaryAbelian p E) (hEcard : Nat.card E = p ^ 2) {t : G} (ht : t ∈ E)
    (ht1 : t ≠ 1) {L : Subgroup G} (hL : IsComponent L) (hpT : ¬ p ∣ Nat.card (L ⧸ center L))
    (hEL : E ≤ normalizer (L : Set G))
    (hXL : ⁅inSubgroup (aschbacherSolvableCore p) (centralizer ({t} : Set G)), E⁆ ≤
      normalizer (L : Set G))
    (hT : ∃ (τ : Assembly.LowTwoRank.StatedLieTag) (ℓ f : ℕ),
      (τ = .G2 ∨ τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) ∧
        ChevalleyExceptionalModel (L ⧸ center L) τ ℓ f) :
    p ≤ Nat.card (E ⊓ centralizer (L : Set G) : Subgroup G) ∧
      ((⁅inSubgroup (aschbacherSolvableCore p) (centralizer ({t} : Set G)), E⁆ ⊔ thetaT p E :
          Subgroup G) : Set G) =
        ((⁅inSubgroup (aschbacherSolvableCore p) (centralizer ({t} : Set G)), E⁆ : Subgroup G) :
          Set G) * (thetaT p E : Set G) ∧
      ⁅⁅inSubgroup (aschbacherSolvableCore p) (centralizer ({t} : Set G)), E⁆, L⁆ = ⊥ ∧
      ⁅thetaT p E, L⁆ = ⊥ ∧
      ⁅inSubgroup (aschbacherSolvableCore p) (centralizer ({t} : Set G)), E⁆ ⊔ thetaT p E ≤
        centralizer (L : Set G) := by
  have := hE
  have : Group.IsPerfect L := hL.1.1
  obtain ⟨τ', K, _, _, ⟨e⟩⟩ : ∃ (τ' : Tag) (K : Type) (_ : Field K) (_ : Finite K),
      Nonempty ((L ⧸ center L) ≃* adjointGroup τ' K) := by
    obtain ⟨τ, ℓ, f, hτ, -, hmodel⟩ := hT
    have key : ∀ τ' : Tag, UntwistedChevalleyModel (L ⧸ center L) τ' (ℓ ^ f) →
        ∃ (τ' : Tag) (K : Type) (_ : Field K) (_ : Finite K),
          Nonempty ((L ⧸ center L) ≃* adjointGroup τ' K) := by
      rintro τ' ⟨K, _, _, -, ⟨e⟩⟩
      exact ⟨τ', K, inferInstance, inferInstance,
        ⟨e.trans (CFSG.RankThree.Chevalley.adjointQuotientEquiv τ' K)⟩⟩
    rcases hτ with rfl | rfl | rfl | rfl | rfl
    · exact key _ hmodel
    · exact key _ hmodel
    · exact key _ hmodel
    · exact key _ hmodel
    · exact key _ hmodel
  have hpC : ¬ p ∣ Nat.card (adjointGroup τ' K) := by
    rwa [← Nat.card_congr e.toEquiv]
  set ψ := (Finkelstein1977.automizer L).comp (inclusion hEL) with hψ
  set α : E →* MulAut (adjointGroup τ' K) := (MulAut.congr e).toMonoidHom.comp ψ with hα
  have hker : α.ker = ψ.ker := by
    ext x
    simp only [hα, MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff]
  have hcard : p ≤ Nat.card (E ⊓ centralizer (L : Set G) : Subgroup G) := by
    have h := (ordinary_Chevalley_coprime_large_prime_automorphism_subgroups_cyclic τ' K hp hp3
      hpC).2 E hEcard α
    rwa [hker, hψ, card_ker_automizer_comp_inclusion hEL] at h
  exact ⟨hcard, plane_core_product_centralizes_of_le_card hp (by omega) hE hEcard ht ht1 hL hXL
    hcard⟩

end CFSG.RankThree.GroupTheory.SteinbergBM
