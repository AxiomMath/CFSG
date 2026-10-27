module

public import CFSG.RankThree.PartOne.FOCD.CompSimple

public section

namespace CFSG.RankThree.PartOne.FOCD

open Subgroup CFSG CFSG.RankThree.PartOne CFSG.RankThree.PartOne.FOC
open scoped commutatorElement

@[expose] def CompGoodZAt (p : ℕ) {T : Type} [Group T] (b : T) : Prop :=
  ∀ E : Subgroup T, IsComponentOf (Subgroup.centralizer ({b} : Set T)) E →
    (∀ z ∈ E ⊓ Subgroup.centralizer (E : Set T), z ^ p = 1 → z = 1) ∧ p ∣ Nat.card E

theorem CompGoodAt.toZ {p : ℕ} {T : Type} [Group T] {b : T} (h : CompGoodAt p b) :
    CompGoodZAt p b := fun E hE => by
  obtain ⟨h1, h2⟩ := h E hE
  refine ⟨fun z hz _ => ?_, h2⟩
  rw [h1] at hz
  exact Subgroup.mem_bot.1 hz

theorem compGoodZAt_of_mulEquiv {p : ℕ} {T T' : Type} [Group T] [Group T'] (φ : T ≃* T') {b : T}
    (h : CompGoodZAt p (φ b)) : CompGoodZAt p b := by
  intro E hE
  have hE' := isComponentOf_map_mulEquiv φ hE
  rw [map_centralizer_singleton_mulEquiv_good φ b] at hE'
  obtain ⟨hZ, hp⟩ := h _ hE'
  refine ⟨fun z hz hzp => ?_, ?_⟩
  · obtain ⟨hzE, hzC⟩ := Subgroup.mem_inf.1 hz
    have h1 : φ z ∈ E.map φ.toMonoidHom ⊓ Subgroup.centralizer (E.map φ.toMonoidHom : Set T') := by
      refine Subgroup.mem_inf.2 ⟨⟨z, hzE, rfl⟩, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      rintro _ ⟨y, hy, rfl⟩
      have := Subgroup.mem_centralizer_iff.1 hzC y hy
      change φ y * φ z = φ z * φ y
      rw [← map_mul, ← map_mul, this]
    have h2 : (φ z) ^ p = 1 := by rw [← map_pow, hzp, map_one]
    exact φ.injective ((hZ _ h1 h2).trans (map_one φ).symm)
  · rwa [Subgroup.card_map_of_injective φ.injective] at hp

theorem compGoodZAt_conj {p : ℕ} {T : Type} [Group T] {b : T} (g : T)
    (h : CompGoodZAt p (g * b * g⁻¹)) : CompGoodZAt p b :=
  compGoodZAt_of_mulEquiv (MulAut.conj g) (by simpa [MulAut.conj_apply] using h)

theorem compGoodZAt_of_comm {T : Type} [Group T] {p : ℕ} {b : T}
    (h : ∀ x ∈ Subgroup.centralizer ({b} : Set T), ∀ y ∈ Subgroup.centralizer ({b} : Set T),
      x * y = y * x) : CompGoodZAt p b :=
  (compGoodAt_of_comm h).toZ

theorem component_eq_of_quasisimple_layer {G : Type} [Group G] [Finite G] {C N D : Subgroup G}
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

theorem compGoodZAt_of_quasisimple_layer {G : Type} [Group G] [Finite G] {J : Subgroup G} {d : G}
    (hdJ : d ∈ J) {Q : Subgroup G} (hQ : CFSG.IsQuasisimple ↥Q)
    (hQD : Q ≤ J ⊓ Subgroup.centralizer ({d} : Set G))
    (hDQ : ⁅J ⊓ Subgroup.centralizer ({d} : Set G), J ⊓ Subgroup.centralizer ({d} : Set G)⁆ ≤ Q)
    {p : ℕ} (hpQ : p ∣ Nat.card Q)
    (hZ : ∀ z ∈ Q, (∀ q ∈ Q, z * q = q * z) → z ^ p = 1 → z = 1) :
    CompGoodZAt p (⟨d, hdJ⟩ : ↥J) := by
  intro E hE
  have hE' : IsComponentOf (J ⊓ Subgroup.centralizer ({d} : Set G)) (E.map J.subtype) :=
    isComponentOf_map_subtype hdJ hE.2.1 hE.1 hE.2.2
  have hEQ : E.map J.subtype = Q := component_eq_of_quasisimple_layer hQD hDQ hQ hE'
  let e : ↥E ≃* ↥Q := (Subgroup.equivMapOfInjective E J.subtype J.subtype_injective).trans
    (MulEquiv.subgroupCongr hEQ)
  refine ⟨fun z hz hzp => ?_, ?_⟩
  · obtain ⟨hzE, hzC⟩ := Subgroup.mem_inf.1 hz
    have hzQ : (z : G) ∈ Q := hEQ ▸ ⟨z, hzE, rfl⟩
    have hcomm : ∀ q ∈ Q, (z : G) * q = q * (z : G) := by
      intro q hq
      rw [← hEQ] at hq
      obtain ⟨y, hy, rfl⟩ := hq
      have := Subgroup.mem_centralizer_iff.1 hzC y hy
      exact congrArg Subtype.val this.symm
    have hzp' : (z : G) ^ p = 1 := by
      have := congrArg Subtype.val hzp
      simpa using this
    exact Subtype.ext (hZ _ hzQ hcomm hzp')
  · rw [Nat.card_congr e.toEquiv]
    exact hpQ

end CFSG.RankThree.PartOne.FOCD
