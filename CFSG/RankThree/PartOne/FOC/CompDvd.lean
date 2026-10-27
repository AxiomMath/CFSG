module

public import CFSG.RankThree.PartOne.FOCD.CompSimple
public import CFSG.RankThree.PartOne.FOCD.Bridge

public section

namespace CFSG.RankThree.PartOne.FOC

open Subgroup CFSG CFSG.RankThree.PartOne CFSG.RankThree.PartOne.FOCD
open scoped commutatorElement

@[expose] def CompDvdAt (p : ℕ) {T : Type} [Group T] (b : T) : Prop :=
  ∀ E : Subgroup T, IsComponentOf (Subgroup.centralizer ({b} : Set T)) E → p ∣ Nat.card E

theorem compDvdAt_of_mulEquiv {p : ℕ} {T T' : Type} [Group T] [Group T'] (φ : T ≃* T') {b : T}
    (h : CompDvdAt p (φ b)) : CompDvdAt p b := by
  intro E hE
  have hE' := isComponentOf_map_mulEquiv φ hE
  rw [map_centralizer_singleton_mulEquiv_good φ b] at hE'
  have := h _ hE'
  rwa [Subgroup.card_map_of_injective φ.injective] at this

theorem compDvdAt_conj {p : ℕ} {T : Type} [Group T] {b : T} (g : T)
    (h : CompDvdAt p (g * b * g⁻¹)) : CompDvdAt p b :=
  compDvdAt_of_mulEquiv (MulAut.conj g) (by simpa [MulAut.conj_apply] using h)

theorem compDvdAt_of_comm {T : Type} [Group T] {p : ℕ} {b : T}
    (h : ∀ x ∈ Subgroup.centralizer ({b} : Set T), ∀ y ∈ Subgroup.centralizer ({b} : Set T),
      x * y = y * x) : CompDvdAt p b :=
  fun E hE => (compGoodAt_of_comm h E hE).2

theorem component_eq_of_layer {G : Type} [Group G] [Finite G] {C N D : Subgroup G}
    (hNC : N ≤ C) (hCN : ⁅C, C⁆ ≤ N) (hN : CFSG.IsQuasisimple ↥N) (hD : IsComponentOf C D) :
    D = N := by
  obtain ⟨hDC, hDq, hDsn⟩ := hD
  have hD1 : D ≠ ⊥ :=
    (Subgroup.nontrivial_iff_ne_bot D).1 (CFSG.LocalCores.isQuasisimple_nontrivial hDq)
  have hDperf : ⁅D, D⁆ = D := Subgroup.isPerfect_iff.mp hDq.1
  have hDN : D ≤ N := by
    rw [← hDperf]
    exact (Subgroup.commutator_mono hDC hDC).trans hCN
  have hsn : (D.subgroupOf N).IsSubnormal := by
    have h1 := hDsn.comap (Subgroup.inclusion hNC)
    convert h1 using 1
    ext g
    simp [Subgroup.mem_subgroupOf]
  exact eq_of_isSubnormal_of_isPerfect_of_isQuasisimple hN hDN hDq.1 hD1 hsn

theorem compDvdAt_of_quasisimple_layer {G : Type} [Group G] [Finite G] {J : Subgroup G} {d : G}
    (hdJ : d ∈ J) {Q : Subgroup G} (hQ : CFSG.IsQuasisimple ↥Q)
    (hQD : Q ≤ J ⊓ Subgroup.centralizer ({d} : Set G))
    (hDQ : ⁅J ⊓ Subgroup.centralizer ({d} : Set G), J ⊓ Subgroup.centralizer ({d} : Set G)⁆ ≤ Q)
    {p : ℕ} (hpQ : p ∣ Nat.card Q) : CompDvdAt p (⟨d, hdJ⟩ : ↥J) := by
  intro E hE
  have hE' : IsComponentOf (J ⊓ Subgroup.centralizer ({d} : Set G)) (E.map J.subtype) :=
    isComponentOf_map_subtype hdJ hE.2.1 hE.1 hE.2.2
  have hEQ : E.map J.subtype = Q := component_eq_of_layer hQD hDQ hQ hE'
  let e : ↥E ≃* ↥Q := (Subgroup.equivMapOfInjective E J.subtype J.subtype_injective).trans
    (MulEquiv.subgroupCongr hEQ)
  rw [Nat.card_congr e.toEquiv]
  exact hpQ

end CFSG.RankThree.PartOne.FOC
