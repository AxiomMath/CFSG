module

public import CFSG.RankThree.PartOne.S12.PushingUp
public import CFSG.Quasithin.Background.BlueprintB2Thompson

public section

namespace CFSG.RankThree.PartOne.KF1514B

open CFSG CFSG.Quasithin.BlueprintB2

variable {G : Type} [Group G]

theorem elemCenter_le {T R : Subgroup G} [Finite ↥T]
    (hfam : ∀ A ∈ elemThompsonFamily ↥T 2, A.map T.subtype ≤ R) :
    (elemThompsonCenterTorsion ↥T 2).map T.subtype ≤ R := by
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨A₀, hA₀⟩ := elemThompsonFamily_nonempty ↥T 2
  exact hfam A₀ hA₀ ⟨x, mem_elemThompsonCenterTorsion_iff_forall.1 hx A₀ hA₀, rfl⟩

theorem conj_mem_elemCenter {T R : Subgroup G} [Finite ↥T] (hRT : R ≤ T)
    (hfam : ∀ A ∈ elemThompsonFamily ↥T 2, A.map T.subtype ≤ R) {n : G}
    (hn : n ∈ Subgroup.normalizer (R : Set G)) {x : G}
    (hx : x ∈ (elemThompsonCenterTorsion ↥T 2).map T.subtype) :
    n * x * n⁻¹ ∈ (elemThompsonCenterTorsion ↥T 2).map T.subtype := by
  obtain ⟨x', hx', rfl⟩ := hx
  have hxR : (x' : G) ∈ R := elemCenter_le hfam ⟨x', hx', rfl⟩
  have hyR : n * (x' : G) * n⁻¹ ∈ R := (Subgroup.mem_normalizer_iff.1 hn _).1 hxR
  have hx'' : x' ∈ elemThompsonCenterTorsion ↥T 2 := hx'
  refine ⟨⟨n * (x' : G) * n⁻¹, hRT hyR⟩, ?_, rfl⟩
  show (⟨n * (x' : G) * n⁻¹, hRT hyR⟩ : ↥T) ∈ elemThompsonCenterTorsion ↥T 2
  rw [mem_elemThompsonCenterTorsion_iff_forall]
  intro A hA
  set AG : Subgroup G := A.map T.subtype with hAG
  set AG' : Subgroup G := AG.map (MulAut.conj n⁻¹).toMonoidHom with hAG'
  have hAGR : AG ≤ R := hfam A hA
  have hAG'R : AG' ≤ R := by
    rintro _ ⟨a, ha, rfl⟩
    have := (Subgroup.mem_normalizer_iff.1 (inv_mem hn) a).1 (hAGR ha)
    simpa [MulAut.conj_apply] using this
  set A' : Subgroup ↥T := AG'.subgroupOf T with hA'
  have hA'el : IsElementaryAbelian 2 A' :=
    isElementaryAbelian_subgroupOf (isElementaryAbelian_map (isElementaryAbelian_map hA.1 _) _)
  have hcard : Nat.card A' = Nat.card A := by
    rw [card_subgroupOf_eq (hAG'R.trans hRT), hAG',
      Subgroup.card_map_of_injective (MulAut.conj n⁻¹).injective, hAG,
      Subgroup.card_map_of_injective T.subtype_injective]
  have hA'mem : A' ∈ elemThompsonFamily ↥T 2 := by
    refine mem_elemThompsonFamily_iff.2 ⟨hA'el, fun B hB => ?_⟩
    rw [hcard]
    exact (mem_elemThompsonFamily_iff.1 hA).2 B hB
  have hx'A' := mem_elemThompsonCenterTorsion_iff_forall.1 hx'' A' hA'mem
  obtain ⟨a, ha, hax⟩ := (Subgroup.mem_subgroupOf.1 hx'A' : (x' : G) ∈ AG')
  obtain ⟨a', ha', rfl⟩ := ha
  have h1 : n⁻¹ * (a' : G) * n⁻¹⁻¹ = (x' : G) := hax
  have h2 : n * (x' : G) * n⁻¹ = (a' : G) := by
    rw [← h1]
    group
  show (⟨n * (x' : G) * n⁻¹, hRT hyR⟩ : ↥T) ∈ A
  have : (⟨n * (x' : G) * n⁻¹, hRT hyR⟩ : ↥T) = a' := Subtype.ext h2
  rw [this]
  exact ha'

theorem normalizer_le_normalizer_pushingUpS {T R : Subgroup G} [Finite ↥T] (hRT : R ≤ T)
    (hfam : ∀ A ∈ elemThompsonFamily ↥T 2, A.map T.subtype ≤ R) (hS : pushingUpS T ≤ R) :
    Subgroup.normalizer (R : Set G) ≤ Subgroup.normalizer (pushingUpS T : Set G) := by
  have key : ∀ n ∈ Subgroup.normalizer (R : Set G), ∀ s ∈ pushingUpS T,
      n * s * n⁻¹ ∈ pushingUpS T := by
    intro n hn s hs
    have hsR : s ∈ R := hS hs
    have hsC : s ∈ Subgroup.centralizer
        (((elemThompsonCenterTorsion ↥T 2).map T.subtype : Subgroup G) : Set G) := hs.2
    have hsR' : n * s * n⁻¹ ∈ R := (Subgroup.mem_normalizer_iff.1 hn _).1 hsR
    refine Subgroup.mem_inf.2 ⟨hRT hsR', ?_⟩
    show n * s * n⁻¹ ∈ Subgroup.centralizer
        (((elemThompsonCenterTorsion ↥T 2).map T.subtype : Subgroup G) : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have hx' := conj_mem_elemCenter hRT hfam (inv_mem hn) hx
    have h3 := Subgroup.mem_centralizer_iff.1 hsC _ hx'
    calc x * (n * s * n⁻¹) = n * ((n⁻¹ * x * n⁻¹⁻¹) * s) * n⁻¹ := by group
      _ = n * (s * (n⁻¹ * x * n⁻¹⁻¹)) * n⁻¹ := by rw [h3]
      _ = (n * s * n⁻¹) * x := by group
  intro n hn
  rw [Subgroup.mem_normalizer_iff]
  intro h
  refine ⟨key n hn h, fun hh => ?_⟩
  have := key n⁻¹ (inv_mem hn) _ hh
  simpa [mul_assoc] using this

end CFSG.RankThree.PartOne.KF1514B
