module

public import CFSG.Quasithin.Background.A4Defs

public section

namespace CFSG.Quasithin.C58

open CFSG.Open CFSG.QuasithinUnique Subgroup

variable {G : Type*} [Group G]

theorem le_of_isPGroup_of_normal [Finite G] {S N P : Subgroup G} (hS : IsSylowTwoOf S N)
    (hSn : N ≤ normalizer (S : Set G)) (hPN : P ≤ N) (hP : IsPGroup 2 P) : P ≤ S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hPS : IsPGroup 2 ↥(P ⊔ S) := hP.to_sup_of_normal_right' hS.2.1 (hPN.trans hSn)
  have hmax := (A4.isSylowTwoOf_iff_maximal.mp hS).2.2 (P ⊔ S) (sup_le hPN hS.1) hPS le_sup_right
  exact le_sup_left.trans hmax

theorem exists_index_two [Finite G] {Y T T₁ : Subgroup G} (hTY : IsSylowTwoOf T Y)
    (hT₁T : T₁ ≤ T) (hidx : T₁.relIndex T = 2) (hYN : Y ≤ normalizer (T₁ : Set G)) :
    ∃ N₁ : Subgroup G, N₁ ≤ Y ∧ Y ≤ normalizer (N₁ : Set G) ∧ T₁ ≤ N₁ ∧
      N₁.relIndex Y = 2 ∧ IsSylowTwoOf T₁ N₁ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hT₁Y : T₁ ≤ Y := hT₁T.trans hTY.1
  set K : Subgroup Y := T₁.subgroupOf Y with hKdef
  have hKn : K.Normal := (normal_subgroupOf_iff_le_normalizer hT₁Y).mpr hYN
  set X := ↥Y ⧸ K
  set π : ↥Y →* X := QuotientGroup.mk' K
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective K
  have hYT : T₁.relIndex Y = 2 * T.relIndex Y := by
    rw [← Subgroup.relIndex_mul_relIndex T₁ T Y hT₁T hTY.1, hidx]
  have hcardX : Nat.card X = 2 * T.relIndex Y := by
    have : Nat.card X = K.index := (Subgroup.index_eq_card K).symm
    rw [this, hKdef, ← Subgroup.relIndex, hYT]
  have hodd : ¬ 2 ∣ T.relIndex Y := hTY.2.2
  have hminFac : (Nat.card X).minFac = 2 := by
    rw [Nat.minFac_eq_two_iff, hcardX]; exact dvd_mul_right 2 _
  obtain ⟨P⟩ : Nonempty (Sylow 2 X) := inferInstance
  have hP2 : Nat.card P = 2 := by
    obtain ⟨k, hk⟩ := P.2.exists_card_eq
    have hmul := Subgroup.card_mul_index (P : Subgroup X)
    rw [hk, hcardX] at hmul
    have hnd : ¬ 2 ∣ (P : Subgroup X).index := P.not_dvd_index
    rcases k with _ | _ | k
    · exfalso; apply hnd; rw [pow_zero, one_mul] at hmul; rw [hmul]; exact dvd_mul_right 2 _
    · rw [hk]; norm_num
    · exfalso; apply hodd
      have e : 2 ^ (k + 1 + 1) * (P : Subgroup X).index =
          2 * (2 * (2 ^ k * (P : Subgroup X).index)) := by ring
      rw [e] at hmul
      have h1 := Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 2) hmul
      exact ⟨_, h1.symm⟩
  have hPc : IsCyclic P := by
    have : Fact (Nat.card P).Prime := ⟨by rw [hP2]; exact Nat.prime_two⟩
    exact isCyclic_of_prime_card rfl
  have hcompl := hPc.isComplement' hminFac
  set Nb := (MonoidHom.transferSylow P (hPc.normalizer_le_centralizer hminFac)).ker with hNb
  have hcardNb : Nat.card Nb = T.relIndex Y := by
    have := hcompl.card_mul_card
    rw [hP2, hcardX] at this
    omega
  set N₁' : Subgroup Y := Nb.comap π with hN₁'
  have hN₁'n : N₁'.Normal := Subgroup.Normal.comap inferInstance π
  have hidxN₁' : N₁'.index = 2 := by
    rw [hN₁', Subgroup.index_comap_of_surjective Nb hπ]
    have h1 := Subgroup.card_mul_index Nb
    rw [hcardNb, hcardX] at h1
    have hpos : 0 < T.relIndex Y := Nat.pos_of_ne_zero (fun h => hodd (by rw [h]; exact dvd_zero 2))
    have : T.relIndex Y * Nb.index = T.relIndex Y * 2 := by rw [h1]; ring
    exact Nat.eq_of_mul_eq_mul_left hpos this
  refine ⟨N₁'.map Y.subtype, map_subtype_le _, ?_, ?_, ?_, ?_⟩
  · have h1 := Subgroup.le_normalizer_map (H := N₁') Y.subtype
    rw [(Subgroup.normalizer_eq_top_iff).mpr hN₁'n, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype] at h1
    exact h1
  · intro t ht
    refine ⟨⟨t, hT₁Y ht⟩, ?_, rfl⟩
    show π ⟨t, hT₁Y ht⟩ ∈ Nb
    have : π ⟨t, hT₁Y ht⟩ = 1 := (QuotientGroup.eq_one_iff _).mpr (by
      rw [hKdef, mem_subgroupOf]; exact ht)
    rw [this]; exact one_mem _
  · rw [Subgroup.relIndex]
    have : (N₁'.map Y.subtype).subgroupOf Y = N₁' := by
      ext y; simp [mem_subgroupOf]
    rw [this, hidxN₁']
  · have hT₁N : T₁ ≤ N₁'.map Y.subtype := by
      intro t ht
      refine ⟨⟨t, hT₁Y ht⟩, ?_, rfl⟩
      show π ⟨t, hT₁Y ht⟩ ∈ Nb
      have : π ⟨t, hT₁Y ht⟩ = 1 := (QuotientGroup.eq_one_iff _).mpr (by
        rw [hKdef, mem_subgroupOf]; exact ht)
      rw [this]; exact one_mem _
    have hN₁Y : N₁'.map Y.subtype ≤ Y := map_subtype_le _
    have hrel : (N₁'.map Y.subtype).relIndex Y = 2 := by
      rw [Subgroup.relIndex]
      have : (N₁'.map Y.subtype).subgroupOf Y = N₁' := by
        ext y; simp [mem_subgroupOf]
      rw [this, hidxN₁']
    refine ⟨hT₁N, hTY.2.1.to_le hT₁T, ?_⟩
    show ¬ 2 ∣ T₁.relIndex (N₁'.map Y.subtype)
    have h1 := Subgroup.relIndex_mul_relIndex T₁ (N₁'.map Y.subtype) Y hT₁N hN₁Y
    rw [hrel, hYT] at h1
    have h2 : T₁.relIndex (N₁'.map Y.subtype) = T.relIndex Y := by omega
    rw [h2]; exact hodd

end CFSG.Quasithin.C58
