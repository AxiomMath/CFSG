module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5P518B2Orb3

public section

namespace CFSG.Quasithin.Fan86

namespace P518

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}
variable {F : FanTree Γ G} {L : ZLab Γ G} {T : Track Γ G} {a : ℤ}

theorem subFixer_le_edge (T : Track Γ G) (a : ℤ) :
    T.subFixer (a + 2) (a + 5) ≤
      MulAction.stabilizer G (xv T a 3) ⊓ MulAction.stabilizer G (xv T a 4) := fun g hg =>
  ⟨MulAction.mem_stabilizer_iff.2 ((mem_subFixer_iff T a g).1 hg 3 (by norm_num) (by norm_num)),
    MulAction.mem_stabilizer_iff.2 ((mem_subFixer_iff T a g).1 hg 4 (by norm_num) (by norm_num))⟩

theorem nOrb_le_four (S : B2Set F L T a) : nOrb T a ≤ 4 := by
  have hv4 : valence Γ (xv T a 4) = 5 := by simpa using S.val_even 2
  have hsub : {w : V | ∃ g ∈ T.subFixer (a + 2) (a + 5), w = g • xv T a 5} ⊆
      Γ.neighborSet (xv T a 4) \ {xv T a 3} := by
    rintro w ⟨g, hg, rfl⟩
    have h4 : g • xv T a 4 = xv T a 4 := (mem_subFixer_iff T a g).1 hg 4 (by norm_num) le_rfl
    have h3 : g • xv T a 3 = xv T a 3 :=
      (mem_subFixer_iff T a g).1 hg 3 (by norm_num) (by norm_num)
    refine ⟨?_, ?_⟩
    · have := (F.adj_smul g (xv T a 4) (xv T a 5)).2 (xv_adj T a 4)
      rwa [h4] at this
    · intro hw
      rw [Set.mem_singleton_iff] at hw
      have hg35 : g • xv T a 5 = g • xv T a 3 := by rw [hw, h3]
      have := xv_inj F T a (MulAction.injective g hg35)
      omega
  have hcard : (Γ.neighborSet (xv T a 4)).ncard = 5 := by
    rw [← Nat.card_coe_set_eq]
    exact hv4
  have hfin : (Γ.neighborSet (xv T a 4)).Finite := Set.finite_of_ncard_pos (by omega)
  calc nOrb T a ≤ (Γ.neighborSet (xv T a 4) \ {xv T a 3}).ncard :=
        Set.ncard_le_ncard hsub (hfin.sdiff)
    _ = 4 := by
        rw [Set.ncard_sdiff_singleton_of_mem
          (show xv T a 3 ∈ Γ.neighborSet (xv T a 4) from xv_adj' T a 3), hcard]

theorem nOrb_pow_two (_S : B2Set F L T a) : ∃ k : ℕ, nOrb T a = 2 ^ k := by
  have hle := subFixer_le_edge T a
  have h2 : IsPGroup 2 ↥(T.subFixer (a + 2) (a + 5)) :=
    (F.edge_two (xv T a 3) (xv T a 4) (xv_adj T a 3)).of_injective (Subgroup.inclusion hle)
      (Subgroup.inclusion_injective hle)
  have hfin : Finite ↥(T.subFixer (a + 2) (a + 5)) := by
    have := F.loc_finite (xv T a 4)
    exact Finite.of_injective (Subgroup.inclusion (hle.trans inf_le_right))
      (Subgroup.inclusion_injective _)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := h2.index ((nbrStab Γ G (xv T a 4)).subgroupOf (T.subFixer (a + 2) (a + 5)))
  exact ⟨k, by rw [nOrb_eq_relIndex F T a]; exact hk⟩

theorem nOrb_eq_four_of_lowerBound (S : B2Set F L T a) {x : G}
    (hx : x ∈ MulAction.stabilizer G (xv T a 6)) (hxo : orderOf x = 5)
    (hlow : 2 ^ 12 ≤ cIdx Γ x (xv T a 6)) : nOrb T a = 4 := by
  have h3 : 2 ^ 12 ≤ (2 * nOrb T a * 2 * nOrb T a * 2) ^ 2 :=
    hlow.trans ((cIdx_le_sq S hx hxo).trans (Nat.pow_le_pow_left (orbit_chain S) 2))
  have h4 := nOrb_le_four S
  obtain ⟨k, hk⟩ := nOrb_pow_two S
  have hn : nOrb T a = 1 ∨ nOrb T a = 2 ∨ nOrb T a = 4 := by
    rcases k with _ | _ | _ | k
    · left
      simpa using hk
    · right; left
      simpa using hk
    · right; right
      simpa using hk
    · exfalso
      have h8 : 2 ^ (k + 1 + 1 + 1) = 8 * 2 ^ k := by ring
      have hpos : 0 < 2 ^ k := Nat.two_pow_pos k
      omega
  rcases hn with h | h | h
  · rw [h] at h3
    norm_num at h3
  · rw [h] at h3
    norm_num at h3
  · exact h

end P518

end CFSG.Quasithin.Fan86
