module

public import CFSG.Timmesfeld.Bridge.Asc72Defs

public section

namespace CFSG.OddTranspositions

open CFSG.Timmesfeld.Bridge.Asc72

variable {H K : Type} [Group H] [Group K]

theorem IsMinimalNormal.comap_mulEquiv (e : H ≃* K) {M : Subgroup K}
    (hM : IsMinimalNormal M) : IsMinimalNormal (M.comap (e : H →* K)) := by
  refine ⟨hM.1.comap (e : H →* K), ?_, ?_⟩
  · intro hbot
    apply hM.2.1
    rw [eq_bot_iff]
    intro m hm
    obtain ⟨h, rfl⟩ := e.surjective m
    have hh : h ∈ M.comap (e : H →* K) := hm
    rw [hbot] at hh
    simpa using congrArg e (by simpa using hh : h = 1)
  · intro N hN hNle
    have hmap : (N.map (e : H →* K)).Normal := hN.map _ e.surjective
    have hle : N.map (e : H →* K) ≤ M := by
      rintro _ ⟨n, hn, rfl⟩
      exact hNle hn
    rcases hM.2.2 _ hmap hle with h | h
    · left
      rw [eq_bot_iff]
      intro n hn
      have hn' : e n ∈ N.map (e : H →* K) := ⟨n, hn, rfl⟩
      rw [h] at hn'
      simpa using e.injective (by simpa using hn')
    · right
      refine le_antisymm hNle ?_
      intro x hx
      have hxM : e x ∈ M := hx
      rw [← h] at hxM
      obtain ⟨n, hn, hne⟩ := hxM
      rwa [← e.injective hne]

theorem not_isSimpleGroup_comap_mulEquiv (e : H ≃* K) {M : Subgroup K}
    (h : ¬ IsSimpleGroup M) : ¬ IsSimpleGroup (M.comap (e : H →* K)) := by
  intro hc
  apply h
  have hmap : (M.comap (e : H →* K)).map (e : H →* K) = M := by
    rw [Subgroup.map_comap_eq_self]
    simp
  have hequiv : (M.comap (e : H →* K)) ≃* M := by
    have := Subgroup.equivMapOfInjective (M.comap (e : H →* K)) (e : H →* K) e.injective
    rwa [hmap] at this
  exact (MulEquiv.isSimpleGroup_congr hequiv).mp hc

end CFSG.OddTranspositions
