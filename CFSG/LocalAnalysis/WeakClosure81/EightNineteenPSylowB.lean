module

public import CFSG.Quasithin.Background.A1bBasic

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin Subgroup

variable {G : Type} [Group G] [Finite G]

private theorem wc819sb_isSylowIn_subgroupOf {p : ℕ} [Fact p.Prime] {H K P : Subgroup G}
    (hKH : K ≤ H) (hP : IsSylowIn p P K) :
    IsSylowIn p (P.subgroupOf H) (K.subgroupOf H) := by
  refine isSylowIn_of_card_eq (Subgroup.subgroupOf_mono H hP.le) ?_
  rw [show Nat.card (P.subgroupOf H) = Nat.card P from
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hP.le.trans hKH)).toEquiv,
      show Nat.card (K.subgroupOf H) = Nat.card K from
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKH).toEquiv,
      hP.card_eq]

private theorem wc819sb_le_sup_of_map_mk'_eq {X : Type*} [Group X] [Finite X]
    {p : ℕ} [Fact p.Prime] {K M : Subgroup X} (hK : K.Normal) (hKM : K ⊔ M = ⊤)
    (S : Sylow p M) (T : Sylow p X)
    (hST : (S : Subgroup M).map M.subtype ≤ (T : Subgroup X)) :
    (T : Subgroup X) ≤ K ⊔ (S : Subgroup M).map M.subtype := by
  haveI : K.Normal := hK
  let π : X →* X ⧸ K := QuotientGroup.mk' K
  have hsurj : Function.Surjective (π.comp M.subtype) := by
    intro y
    obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective K y
    obtain ⟨k, hk, m, hm, hkm⟩ :=
      (Subgroup.mem_sup_of_normal_left (s := K) (t := M)).1 (hKM ▸ Subgroup.mem_top x)
    refine ⟨⟨m, hm⟩, ?_⟩
    rw [← hx, ← hkm, map_mul]
    rw [show π k = 1 from (QuotientGroup.eq_one_iff (N := K) k).2 hk, one_mul]
    rfl
  let hSM : Sylow p (X ⧸ K) := S.mapSurjective hsurj
  let hTX : Sylow p (X ⧸ K) := T.mapSurjective (QuotientGroup.mk'_surjective K)
  have hle : (hSM : Subgroup (X ⧸ K)) ≤ (hTX : Subgroup (X ⧸ K)) := by
    change (S : Subgroup ↥M).map (π.comp M.subtype) ≤ (T : Subgroup X).map π
    rw [← Subgroup.map_map]
    exact Subgroup.map_mono hST
  have heq : (hTX : Subgroup (X ⧸ K)) = (hSM : Subgroup (X ⧸ K)) := by
    refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
    rw [hSM.card_eq_multiplicity, hTX.card_eq_multiplicity]
  have hmap : (T : Subgroup X).map π = ((S : Subgroup ↥M).map M.subtype).map π := by
    rw [Subgroup.map_map]
    exact heq
  calc (T : Subgroup X) ≤ Subgroup.comap π ((T : Subgroup X).map π) :=
        Subgroup.le_comap_map (f := π) (T : Subgroup X)
    _ = Subgroup.comap π (((S : Subgroup M).map M.subtype).map π) := by rw [hmap]
    _ = K ⊔ (S : Subgroup M).map M.subtype := by rw [QuotientGroup.comap_map_mk']

theorem eq_inf_mul_inf_of_isSylowIn {J D N T : Subgroup G} (hJD : J ≤ D)
    (hDJ : D ≤ normalizer (J : Set G)) (hND : N ≤ D) (hDN : D = J ⊔ N)
    (hT : IsSylowIn 2 T D) (hTN : IsSylowIn 2 (T ⊓ N) N) :
    ∀ t ∈ T, ∃ n ∈ T ⊓ N, ∃ j ∈ T ⊓ J, t = n * j := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let J' : Subgroup D := J.subgroupOf D
  let N' : Subgroup D := N.subgroupOf D
  let S' : Subgroup D := (T ⊓ N).subgroupOf D
  have hJ'norm : J'.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hJD).mpr hDJ
  have hS' : IsSylowIn 2 S' N' := wc819sb_isSylowIn_subgroupOf hND hTN
  have htop : J' ⊔ N' = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hJD hND, ← hDN, Subgroup.subgroupOf_self]
  have hST' : (hS'.toSylow : Subgroup N').map N'.subtype ≤ (hT.toSylow : Subgroup D) := by
    rw [IsSylowIn.coe_toSylow, IsSylowIn.coe_toSylow,
      Subgroup.map_subgroupOf_eq_of_le hS'.le]
    exact Subgroup.subgroupOf_mono D inf_le_left
  have hsup : T.subgroupOf D ≤ J' ⊔ S' := by
    have h := wc819sb_le_sup_of_map_mk'_eq hJ'norm htop hS'.toSylow hT.toSylow hST'
    rw [IsSylowIn.coe_toSylow, IsSylowIn.coe_toSylow,
      Subgroup.map_subgroupOf_eq_of_le hS'.le] at h
    exact h
  intro t ht
  have htD : (⟨t, hT.le ht⟩ : D) ∈ T.subgroupOf D := ht
  have hmem : (⟨t, hT.le ht⟩ : D) ∈ S' ⊔ J' := by
    have h1 := hsup htD
    rwa [sup_comm] at h1
  haveI : J'.Normal := hJ'norm
  obtain ⟨n, hn, j, hj, hnj⟩ :=
    (Subgroup.mem_sup_of_normal_right (s := S') (t := J')).1 hmem
  obtain ⟨hnT, hnN⟩ := Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hn)
  refine ⟨(n : G), Subgroup.mem_inf.mpr ⟨hnT, hnN⟩, (j : G), ?_, ?_⟩
  · refine Subgroup.mem_inf.mpr ⟨?_, Subgroup.mem_subgroupOf.mp hj⟩
    have hjn : (j : G) = (n : G)⁻¹ * t := by
      have hnj' : (n : G) * (j : G) = t := congrArg Subtype.val hnj
      rw [← hnj']
      group
    rw [hjn]
    exact T.mul_mem (T.inv_mem hnT) ht
  · exact (congrArg Subtype.val hnj).symm

end CFSG.LocalAnalysis.WeakClosure81

end
