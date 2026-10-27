module

public import CFSG.SignalizerFunctorTheorem.Nonsolvable.SolComponent.Bijection

public section

open scoped commutatorElement

namespace CFSG.SignalizerFunctorTheorem.Nonsolvable

variable {G : Type*} [Group G]

theorem commutator_le_of_le_normalizer {K S : Subgroup G}
    (h : S ≤ Subgroup.normalizer (K : Set G)) : ⁅K, S⁆ ≤ K := by
  refine Subgroup.commutator_le.mpr fun k hk s hs => ?_
  have h1 : s * k⁻¹ * s⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp (h hs) k⁻¹).mp (inv_mem hk)
  have : ⁅k, s⁆ = k * (s * k⁻¹ * s⁻¹) := by rw [commutatorElement_def]; group
  rw [this]
  exact mul_mem hk h1

theorem commutator_le_inf_of_le_normalizer {K S : Subgroup G}
    (hSK : S ≤ Subgroup.normalizer (K : Set G)) (hKS : K ≤ Subgroup.normalizer (S : Set G)) :
    ⁅K, S⁆ ≤ K ⊓ S :=
  le_inf (commutator_le_of_le_normalizer hSK)
    (by rw [Subgroup.commutator_comm]; exact commutator_le_of_le_normalizer hKS)

theorem commutator_map_eq_bot_iff (K S : Subgroup G) :
    ⁅K.map (QuotientGroup.mk' (CFSG.solvableRadical G)),
        S.map (QuotientGroup.mk' (CFSG.solvableRadical G))⁆ = ⊥ ↔
      ⁅K, S⁆ ≤ CFSG.solvableRadical G := by
  rw [← Subgroup.map_commutator, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']

variable [Finite G]

namespace IsSolComponent

variable {K L : Subgroup G}

theorem le_or_commutator_le_solvableRadical (hK : IsSolComponent K) {S : Subgroup G}
    (hS : S.IsSubnormal) : K ≤ S ∨ ⁅K, S⁆ ≤ CFSG.solvableRadical G := by
  rcases CFSG.LocalCores.component_subnormal_subgroup hK.isComponent_map
      (hS.map (QuotientGroup.mk'_surjective _)) with h | h
  · exact Or.inl (hK.le_of_map_le_map hS h)
  · exact Or.inr ((commutator_map_eq_bot_iff K S).mp h)

theorem le_normalizer_of_commutator_le (hK : IsSolComponent K) {S : Subgroup G}
    (h : ⁅K, S⁆ ≤ CFSG.solvableRadical G) : S ≤ Subgroup.normalizer (K : Set G) := by
  have hRs : Group.IsSolvable (CFSG.solvableRadical G) := isSolvable_solvableRadical
  refine le_trans ?_ (normalizer_sup_le_normalizer hK.isPerfect hK.isSubnormal
    (inferInstance : (CFSG.solvableRadical G).Normal) hRs)
  have key : ∀ t ∈ S, ∀ y ∈ K ⊔ CFSG.solvableRadical G,
      t * y * t⁻¹ ∈ K ⊔ CFSG.solvableRadical G := by
    intro t ht y hy
    obtain ⟨k, hk, r, hr, rfl⟩ :=
      (Subgroup.mem_sup_of_normal_right (s := K) (t := CFSG.solvableRadical G)).mp hy
    have hc : k * t * k⁻¹ * t⁻¹ ∈ CFSG.solvableRadical G := by
      have := h (Subgroup.commutator_mem_commutator hk ht)
      rwa [commutatorElement_def] at this
    have h1 : t * k * t⁻¹ ∈ K ⊔ CFSG.solvableRadical G := by
      have e : t * k * t⁻¹ = (k * t * k⁻¹ * t⁻¹)⁻¹ * k := by group
      rw [e, sup_comm]
      exact Subgroup.mul_mem_sup (inv_mem hc) hk
    have h2 : t * r * t⁻¹ ∈ K ⊔ CFSG.solvableRadical G :=
      Subgroup.mem_sup_right ((inferInstance : (CFSG.solvableRadical G).Normal).conj_mem r hr t)
    have e : t * (k * r) * t⁻¹ = (t * k * t⁻¹) * (t * r * t⁻¹) := by group
    rw [e]
    exact mul_mem h1 h2
  intro s hs
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨key s hs y, fun hy => ?_⟩
  have h3 := key s⁻¹ (inv_mem hs) _ hy
  have e : s⁻¹ * (s * y * s⁻¹) * s⁻¹⁻¹ = y := by group
  rwa [e] at h3

theorem inf_le_solvableRadical_of_commutator_le (hK : IsSolComponent K) {S : Subgroup G}
    (hS : S.IsSubnormal) (h : ⁅K, S⁆ ≤ CFSG.solvableRadical G) :
    K ⊓ S ≤ CFSG.solvableRadical G := by
  have hc := (commutator_map_eq_bot_iff K S).mpr h
  have hXs : (K.map (QuotientGroup.mk' (CFSG.solvableRadical G)) ⊓
      S.map (QuotientGroup.mk' (CFSG.solvableRadical G))).IsSubnormal :=
    hK.isComponent_map.2.inf (hS.map (QuotientGroup.mk'_surjective _))
  have hcomm : IsMulCommutative ↥(K.map (QuotientGroup.mk' (CFSG.solvableRadical G)) ⊓
      S.map (QuotientGroup.mk' (CFSG.solvableRadical G))) :=
    ⟨⟨fun a b => Subtype.ext (Subgroup.mem_centralizer_iff.mp
      (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hc (Subgroup.mem_inf.mp a.2).1)
      (b : G ⧸ CFSG.solvableRadical G) (Subgroup.mem_inf.mp b.2).2).symm⟩⟩
  have hle := le_solvableRadical_of_isSubnormal hXs inferInstance
  rw [solvableRadical_quotient] at hle
  intro x hx
  obtain ⟨hxK, hxS⟩ := Subgroup.mem_inf.mp hx
  have hx1 := hle (Subgroup.mem_inf.mpr
    ⟨Subgroup.mem_map_of_mem _ hxK, Subgroup.mem_map_of_mem _ hxS⟩)
  rw [Subgroup.mem_bot] at hx1
  exact (QuotientGroup.eq_one_iff x).mp hx1

theorem le_or_normalizes (hK : IsSolComponent K) {S : Subgroup G} (hS : S.IsSubnormal) :
    K ≤ S ∨ (S ≤ Subgroup.normalizer (K : Set G) ∧
      ⁅K, S⁆ ≤ (CFSG.solvableRadical K).map K.subtype ∧
      K ⊓ S ≤ (CFSG.solvableRadical K).map K.subtype) := by
  rcases hK.le_or_commutator_le_solvableRadical hS with h | h
  · exact Or.inl h
  · right
    have hN := hK.le_normalizer_of_commutator_le h
    rw [map_subtype_solvableRadical_eq_inf hK.isSubnormal]
    exact ⟨hN, le_inf (commutator_le_of_le_normalizer hN) h,
      le_inf inf_le_left (hK.inf_le_solvableRadical_of_commutator_le hS h)⟩

theorem isSolvable_inf_of_commutator_le (hK : IsSolComponent K) {S : Subgroup G}
    (hS : S.IsSubnormal) (h : ⁅K, S⁆ ≤ CFSG.solvableRadical G) :
    Group.IsSolvable ↥(K ⊓ S) := by
  have hRs : Group.IsSolvable (CFSG.solvableRadical G) := isSolvable_solvableRadical
  exact Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective
    (hK.inf_le_solvableRadical_of_commutator_le hS h))

theorem solvableRadical_le_normalizer (hK : IsSolComponent K) :
    CFSG.solvableRadical G ≤ Subgroup.normalizer (K : Set G) :=
  le_sup_right.trans (sup_le_normalizer (R := CFSG.solvableRadical G) hK.isPerfect
    hK.isSubnormal inferInstance isSolvable_solvableRadical)

theorem commutator_le_solvableRadical_of_ne (hK : IsSolComponent K) (hL : IsSolComponent L)
    (hne : K ≠ L) : ⁅K, L⁆ ≤ CFSG.solvableRadical G := by
  have hne' : K.map (QuotientGroup.mk' (CFSG.solvableRadical G)) ≠
      L.map (QuotientGroup.mk' (CFSG.solvableRadical G)) := fun h => hne (hK.eq_of_map_eq hL h)
  exact (commutator_map_eq_bot_iff K L).mp
    ((CFSG.LocalCores.distinct_components_commute hK.isComponent_map
      hL.isComponent_map).resolve_left hne')

theorem normalizes_of_ne (hK : IsSolComponent K) (hL : IsSolComponent L) (hne : K ≠ L) :
    K ≤ Subgroup.normalizer (L : Set G) ∧ L ≤ Subgroup.normalizer (K : Set G) ∧
      ⁅K, L⁆ ≤ K ⊓ L ∧ ⁅K, L⁆ ≤ CFSG.solvableRadical G ∧
      K ⊓ L ≤ CFSG.solvableRadical G := by
  have h := hK.commutator_le_solvableRadical_of_ne hL hne
  have h' : ⁅L, K⁆ ≤ CFSG.solvableRadical G := by rw [Subgroup.commutator_comm]; exact h
  have hLK := hK.le_normalizer_of_commutator_le h
  have hKL := hL.le_normalizer_of_commutator_le h'
  exact ⟨hKL, hLK, commutator_le_inf_of_le_normalizer hLK hKL, h,
    hK.inf_le_solvableRadical_of_commutator_le hL.isSubnormal h⟩

end IsSolComponent

end CFSG.SignalizerFunctorTheorem.Nonsolvable
