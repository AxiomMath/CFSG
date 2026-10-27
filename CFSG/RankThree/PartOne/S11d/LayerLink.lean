module

public import CFSG.RankThree.PartOne.S11d.Facts5
public import CFSG.RankThree.PartOne.S11d.FourClaimAux
public import CFSG.GroupTheory.LocalCores.Layer

public section

namespace CFSG.RankThree.PartOne

open Subgroup CFSG CFSG.RankThree CFSG.RankThree.GroupTheory CFSG.RankThree.LocalRank

variable {G : Type} [Group G]

theorem isComponent_subgroupOf_of_isComponentOf {X E : Subgroup G} (hE : IsComponentOf X E) :
    CFSG.IsComponent (E.subgroupOf X) :=
  ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hE.1).symm hE.2.1,
    hE.2.2⟩

theorem isComponentOf_map_subtype_of_isComponent {X : Subgroup G} {K : Subgroup ↥X}
    (hK : CFSG.IsComponent K) : IsComponentOf X (K.map X.subtype) := by
  refine ⟨Subgroup.map_subtype_le K, ?_, ?_⟩
  · exact CFSG.LocalCores.isQuasisimple_of_mulEquiv
      (Subgroup.equivMapOfInjective K X.subtype X.subtype_injective) hK.1
  · have h : (K.map X.subtype).subgroupOf X = K :=
      Subgroup.comap_map_eq_self_of_injective X.subtype_injective K
    rw [h]
    exact hK.2

theorem coe_mem_normalizer_map_subtype {X : Subgroup G} {K : Subgroup ↥X} {x : ↥X}
    (hx : x ∈ Subgroup.normalizer (K : Set ↥X)) :
    (x : G) ∈ Subgroup.normalizer ((K.map X.subtype : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  have hx' : x⁻¹ ∈ Subgroup.normalizer (K : Set ↥X) := Subgroup.inv_mem _ hx
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact ⟨x * k * x⁻¹, (Subgroup.mem_normalizer_iff.mp hx k).mp hk, rfl⟩
  · rintro ⟨k, hk, hkh⟩
    have hy : x⁻¹ * k * x ∈ K := by
      have := (Subgroup.mem_normalizer_iff.mp hx' k).mp hk
      simpa using this
    refine ⟨x⁻¹ * k * x, hy, ?_⟩
    have hkh' : (k : G) = (x : G) * h * (x : G)⁻¹ := hkh
    change (x : G)⁻¹ * (k : G) * (x : G) = h
    rw [hkh']
    group

variable [Finite G]

theorem exists_component_le_theta {p : ℕ} (hp : p.Prime) {d : G} {X D ID : Subgroup G}
    (hID : ID ∈ thetaComponentsAt p d) (hDI : D ≤ ID)
    (hXd : X ≤ Subgroup.centralizer ({d} : Set G))
    (hex : ∀ E : Subgroup G, IsComponentOf X E → ∃ I ∈ thetaComponentsAt p d, E ≤ I)
    {t₁ t₂ : G} (ht₁D : t₁ ∈ D) (ht₁ : t₁ ∈ inSubgroup layer X) (ht₂ : t₂ ∈ inSubgroup layer X)
    (hnc : t₁ * t₂ ≠ t₂ * t₁) :
    ∃ E : Subgroup G, IsComponentOf X E ∧ E ≤ ID := by
  by_contra hno
  push Not at hno
  obtain ⟨t₁', ht₁', rfl⟩ := ht₁
  obtain ⟨t₂', ht₂', rfl⟩ := ht₂
  have hcomp : ∀ K : Subgroup ↥X, CFSG.IsComponent K →
      K ≤ Subgroup.centralizer ({t₁'} : Set ↥X) := by
    intro K hK k hk
    set E : Subgroup G := K.map X.subtype with hEdef
    have hE : IsComponentOf X E := isComponentOf_map_subtype_of_isComponent hK
    obtain ⟨I, hI, hEI⟩ := hex E hE
    have hne : ID ≠ I := fun h => hno E hE (by rw [h]; exact hEI)
    have hEd : E ≤ Subgroup.centralizer ({d} : Set G) := hE.1.trans hXd
    have hxN : (t₁' : G) ∈ Subgroup.normalizer (E : Set G) :=
      coe_mem_normalizer_map_subtype (CFSG.LocalCores.layer_le_normalizer hK ht₁')
    have hcommE : ∀ e ∈ E, (t₁' : G) * e * (t₁' : G)⁻¹ * e⁻¹ ∈
        inSubgroup (aschbacherSolvableCore p) (Subgroup.centralizer ({d} : Set G)) := fun e he =>
      S11d.commutator_mem_theta_of_ne hp hID hI hne _ (hDI ht₁D) e (hEI he)
    have hcent := centralizes_of_commutators_mem_theta hp hE.2.1 hEd hxN hcommE
    have hkE : (k : G) ∈ E := ⟨k, hk, rfl⟩
    have h1 := hcent _ hkE
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply Subtype.ext
    change (k : G) * t₁' = t₁' * k
    calc (k : G) * t₁' = ((t₁' : G) * k * (t₁' : G)⁻¹) * t₁' := by rw [h1]
      _ = t₁' * k := by group
  have hlayer : CFSG.layer ↥X ≤ Subgroup.centralizer ({t₁'} : Set ↥X) :=
    sSup_le fun K hK => hcomp K hK
  have h2 := Subgroup.mem_centralizer_singleton_iff.mp (hlayer ht₂')
  exact hnc (congrArg Subtype.val h2).symm

end CFSG.RankThree.PartOne
