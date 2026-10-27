module

public import CFSG.GroupTheory.ExtraspecialInvolutionIndexTwo

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG CFSG.Open Subgroup
open CFSG.LargeExtraspecial.Timmesfeld (IsExtraspecial2)

variable {G : Type} [Group G]

theorem mem_inSubgroup_pCore_centralizer_self {z : G} (hz : orderOf z = 2) :
    z ∈ inSubgroup (pCore 2) (centralizer ({z} : Set G)) := by
  have hzM : z ∈ centralizer ({z} : Set G) := mem_centralizer_singleton_iff.mpr rfl
  set M : Subgroup G := centralizer ({z} : Set G) with hM
  set x : M := ⟨z, hzM⟩ with hx
  have hxc : ∀ m : M, Commute m x := fun m =>
    Subtype.ext (mem_centralizer_singleton_iff.mp m.2)
  have hord : orderOf x = 2 := by
    rw [← orderOf_injective M.subtype M.subtype_injective x]
    exact hz
  have hK : (zpowers x).Normal := by
    refine ⟨fun n hn g => ?_⟩
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hn
    have hc : Commute g (x ^ k) := (hxc g).zpow_right k
    rw [hc.eq, mul_inv_cancel_right]
    exact zpow_mem_zpowers x k
  have hP : IsPGroup 2 (zpowers x) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hord, pow_one])
  have hle : zpowers x ≤ pCore 2 M := le_sSup ⟨hK, hP⟩
  exact ⟨x, hle (mem_zpowers x), rfl⟩

theorem centralizer_le_normalizer_inSubgroup_pCore (z : G) :
    centralizer ({z} : Set G) ≤
      normalizer (inSubgroup (pCore 2) (centralizer ({z} : Set G)) : Set G) := by
  intro h hh
  rw [mem_normalizer_iff]
  intro j
  have key : ∀ (h : G) (hh : h ∈ centralizer ({z} : Set G)) (j : G),
      j ∈ inSubgroup (pCore 2) (centralizer ({z} : Set G)) →
      h * j * h⁻¹ ∈ inSubgroup (pCore 2) (centralizer ({z} : Set G)) := by
    rintro h hh j ⟨j', hj', rfl⟩
    refine ⟨⟨h, hh⟩ * j' * ⟨h, hh⟩⁻¹, (pCore_normal (p := 2)).conj_mem _ hj' _, ?_⟩
    simp
  exact ⟨fun hj => key h hh j hj, fun hj => by
    have := key h⁻¹ (inv_mem hh) _ hj
    simpa [mul_assoc] using this⟩

theorem parrott77_lemma6 [Finite G] (z : G) (J : Subgroup G) (hz : orderOf z = 2)
    (hJdef : J = inSubgroup (pCore 2) (centralizer ({z} : Set G))) (hJ : IsExtraspecial2 J)
    (hCH : centralizer ({z} : Set G) ⊓ centralizer (J : Set G) = zpowers z)
    {x : G} (hxH : x ∈ centralizer ({z} : Set G)) (hxJ : x ∉ J)
    (hidx : (centralizer ({x} : Set G)).relIndex J = 2) : x ^ 2 ∉ zpowers z := by
  intro hx2
  have hzJ : z ∈ J := hJdef ▸ mem_inSubgroup_pCore_centralizer_self hz
  have hzC : z ∈ centralizer (J : Set G) := by
    have : z ∈ centralizer ({z} : Set G) ⊓ centralizer (J : Set G) := by
      rw [hCH]; exact mem_zpowers z
    exact this.2
  have hx2' : x ^ 2 ∈ centralizer (J : Set G) := (zpowers_le.mpr hzC) hx2
  have hC : centralizer ({z} : Set G) ⊓ centralizer (J : Set G) ≤ J := by
    rw [hCH]; exact zpowers_le.mpr hzJ
  have hJH : J ≤ centralizer ({z} : Set G) := hJdef ▸ Subgroup.map_subtype_le _
  have hN : centralizer ({z} : Set G) ≤ normalizer (J : Set G) :=
    hJdef ▸ centralizer_le_normalizer_inSubgroup_pCore z
  exact CFSG.GroupTheory.relIndex_centralizer_ne_two_of_sq_mem_centralizer hJ hJH hN hC hxH
    hxJ hx2' hidx

end CFSG.RankThree.GF2n.Parrott
