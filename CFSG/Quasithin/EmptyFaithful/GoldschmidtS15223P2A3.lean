module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS15223P2Main

public section

namespace CFSG.Quasithin.S15223

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

variable {G : Type} [Group G]

theorem false_of_alt3_block [Finite G] {I S K P Zs X : Subgroup G}
    (hC19 : DistinctBlocksCommuteStatement (G := G)) (hchar : CharTwo I)
    (hrank : CFSG.Open.pRank 3 (⊤ : Subgroup ↥I) ≤ 2) (hS : IsSylowTwoOf S I) (hKI : K ≤ I)
    (hPK : P ≤ K) (hP : IsElemAbelian 3 P) (hP9 : Nat.card P = 9)
    (hKZ : ∀ k ∈ K, ∀ z ∈ Zs, k * z = z * k)
    (hZS : ∀ z ∈ Zs, z ∈ S ∧ z ^ 2 = 1 ∧ ∀ s ∈ S, z * s = s * z)
    (hZmax : ∀ w ∈ S, w ^ 2 = 1 → (∀ s ∈ S, w * s = s * w) → w ∈ Zs)
    (hX : IsBlock2 I X) (halt : IsAltType X 3) : False := by
  obtain ⟨c, hA⟩ := S14110.A4Data.of_isShort2 hX.1 halt
  have hXc := commute_block_of_central hC19 hchar hrank hS hKI hPK hP hP9 hKZ hZS hX (Or.inl halt)
  have h3 : 3 ∣ Nat.card X := three_dvd_card_of_type (Or.inl halt)
  have hWX : blockU X ≤ X := hA.le
  have hW2 : IsPGroup 2 ↥(blockU X) := C1.isPGroup_blockU hX.1
  have hW1 : blockU X ≠ ⊥ := by
    intro h
    have := hA.card_W
    rw [h, Subgroup.card_bot] at this
    omega
  have hSyl : IsSylowIn 2 (S ⊓ X) X := isSylowIn_inf_of_block hC19 hchar hrank hS hX h3
  have hWn : ((blockU X).subgroupOf X).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hWX).mpr (C1.le_normalizer_blockU X)
  have hWS : blockU X ≤ S ⊓ X := hSyl.le_of_normal hWX hWn hW2
  have hfpf : ∀ a ∈ blockU X, a ≠ 1 → c * a ≠ a * c := fun a ha ha1 h => by
    apply hA.fpf a ha ha1
    calc c * a * c⁻¹ = a * c * c⁻¹ := by rw [h]
      _ = a := by group
  by_cases hSN : S ≤ Subgroup.normalizer (X : Set G)
  ·
    have hSW : S ≤ Subgroup.normalizer (blockU X : Set G) := fun s hs =>
      C1.mem_normalizer_blockU (hSN hs)
    obtain ⟨w, hw, hw1, hwc⟩ := exists_centralized_ne_one hS.2.1 hW2 hSW hW1
    have hwZ : w ∈ Zs := hZmax w (hWS hw).1 (hA.sq_eq_one w hw) fun s hs => (hwc s hs).symm
    exact hfpf w hw hw1 (hXc w hwZ c hA.mem_X)
  ·
    obtain ⟨s, hsS, hsn⟩ : ∃ s ∈ S, s ∉ Subgroup.normalizer (X : Set G) := by
      by_contra hcon
      push Not at hcon
      exact hSN fun s hs => hcon s hs
    have hsI : s ∈ I := hS.1 hsS
    have hidx := index_normalizer_le_two hC19 hchar hrank hX h3
    have hNn := normal_normalizer_inf hC19 hchar hrank hX h3
    set N' : Subgroup ↥I := (Subgroup.normalizer (X : Set G) ⊓ I).subgroupOf I with hN'
    have hmemN : ∀ g : ↥I, g ∈ N' ↔ (g : G) ∈ Subgroup.normalizer (X : Set G) := fun g => by
      rw [hN', Subgroup.mem_subgroupOf, Subgroup.mem_inf]
      exact ⟨fun h => h.1, fun h => ⟨h, g.2⟩⟩
    let s' : ↥I := ⟨s, hsI⟩
    have hs'N : s' ∉ N' := fun h => hsn ((hmemN s').mp h)
    have hconjN : ∀ t ∈ S, t ∈ Subgroup.normalizer (X : Set G) →
        s⁻¹ * t * s ∈ Subgroup.normalizer (X : Set G) := by
      intro t ht htn
      have h1 : (⟨t, hS.1 ht⟩ : ↥I) ∈ N' := (hmemN _).mpr htn
      have h2 := (hmemN _).mp (hNn.conj_mem _ h1 s'⁻¹)
      simpa using h2
    have hsq : s * s ∈ Subgroup.normalizer (X : Set G) := by
      rcases mem_of_index_le_two hidx 1 s' (s' * s') with h | h | h
      · exact absurd (by simpa using h) hs'N
      · exact (hmemN _).mp (by simpa using h)
      · exact absurd (by simpa using h) hs'N
    have hcoset : ∀ t ∈ S, t ∉ Subgroup.normalizer (X : Set G) →
        s⁻¹ * t ∈ Subgroup.normalizer (X : Set G) := by
      intro t ht htn
      have ht' : (⟨t, hS.1 ht⟩ : ↥I) ∉ N' := fun h => htn ((hmemN _).mp h)
      rcases mem_of_index_le_two hidx 1 s' ⟨t, hS.1 ht⟩ with h | h | h
      · exact absurd (by simpa using h) hs'N
      · exact absurd (by simpa using h) ht'
      · exact (hmemN _).mp h
    set S₁ : Subgroup G := S ⊓ Subgroup.normalizer (X : Set G) with hS₁
    have hS₁W : S₁ ≤ Subgroup.normalizer (blockU X : Set G) := fun t ht =>
      C1.mem_normalizer_blockU ht.2
    obtain ⟨a, ha, ha1, hac⟩ := exists_centralized_ne_one (hS.2.1.to_le inf_le_left) hW2 hS₁W hW1
    have hX' : IsBlock2 I (conjByElt s X) := IsBlock2.conjByElt_of_mem hX hsI
    have hne : X ≠ conjByElt s X := fun h =>
      hsn (Subgroup.mem_normalizer_iff_map_conj_eq.mpr h.symm)
    have hcm := mul_comm_of_commutator_bot (hC19 I X (conjByElt s X) hchar hX hX' hne)
    have haX : a ∈ X := hWX ha
    have ha' : s * a * s⁻¹ ∈ conjByElt s X := by
      rw [mem_conjByElt]
      have : s⁻¹ * (s * a * s⁻¹) * s = a := by group
      rw [this]
      exact haX
    have haa' : a * (s * a * s⁻¹) = (s * a * s⁻¹) * a := hcm a haX _ ha'
    have ha2 : a ^ 2 = 1 := hA.sq_eq_one a ha
    have ha'2 : (s * a * s⁻¹) ^ 2 = 1 := by
      rw [conj_pow, ha2]
      group
    have haS : a ∈ S := (hWS ha).1
    have hw0S : a * (s * a * s⁻¹) ∈ S :=
      mul_mem haS (mul_mem (mul_mem hsS haS) (S.inv_mem hsS))
    have hw02 : (a * (s * a * s⁻¹)) ^ 2 = 1 := by
      have hc : Commute a (s * a * s⁻¹) := haa'
      rw [hc.mul_pow, ha2, ha'2, one_mul]
    have hS₁c : ∀ t ∈ S₁, t * (a * (s * a * s⁻¹)) = (a * (s * a * s⁻¹)) * t := by
      intro t ht
      have h1 : t * a = a * t := hac t ht
      have h2 : t * (s * a * s⁻¹) = (s * a * s⁻¹) * t := by
        have htn : s⁻¹ * t * s ∈ S₁ := ⟨mul_mem (mul_mem (S.inv_mem hsS) ht.1) hsS,
          hconjN t ht.1 ht.2⟩
        have h3 := hac _ htn
        calc t * (s * a * s⁻¹) = s * ((s⁻¹ * t * s) * a) * s⁻¹ := by group
          _ = s * (a * (s⁻¹ * t * s)) * s⁻¹ := by rw [h3]
          _ = (s * a * s⁻¹) * t := by group
      calc t * (a * (s * a * s⁻¹)) = (t * a) * (s * a * s⁻¹) := by group
        _ = a * (t * (s * a * s⁻¹)) := by rw [h1]; group
        _ = a * ((s * a * s⁻¹) * t) := by rw [h2]
        _ = (a * (s * a * s⁻¹)) * t := by group
    have hsc : s * (a * (s * a * s⁻¹)) = (a * (s * a * s⁻¹)) * s := by
      have hs2 : (s * s) * a = a * (s * s) := hac _ ⟨mul_mem hsS hsS, hsq⟩
      have h4 : s * s * a * s⁻¹ * s⁻¹ = a := by
        calc s * s * a * s⁻¹ * s⁻¹ = (a * (s * s)) * s⁻¹ * s⁻¹ := by rw [hs2]
          _ = a := by group
      calc s * (a * (s * a * s⁻¹)) = (s * a * s⁻¹) * (s * s * a * s⁻¹ * s⁻¹) * s := by group
        _ = (s * a * s⁻¹) * a * s := by rw [h4]
        _ = (a * (s * a * s⁻¹)) * s := by rw [← haa']
    have hSc : ∀ t ∈ S, (a * (s * a * s⁻¹)) * t = t * (a * (s * a * s⁻¹)) := by
      intro t ht
      by_cases htn : t ∈ Subgroup.normalizer (X : Set G)
      · exact (hS₁c t ⟨ht, htn⟩).symm
      · have hu : s⁻¹ * t ∈ S₁ := ⟨mul_mem (S.inv_mem hsS) ht, hcoset t ht htn⟩
        have h1 := hS₁c _ hu
        calc (a * (s * a * s⁻¹)) * t = (a * (s * a * s⁻¹)) * s * (s⁻¹ * t) := by group
          _ = (s * (a * (s * a * s⁻¹))) * (s⁻¹ * t) := by rw [hsc]
          _ = s * ((a * (s * a * s⁻¹)) * (s⁻¹ * t)) := by group
          _ = s * ((s⁻¹ * t) * (a * (s * a * s⁻¹))) := by rw [← h1]
          _ = t * (a * (s * a * s⁻¹)) := by group
    have hw0Z : a * (s * a * s⁻¹) ∈ Zs := hZmax _ hw0S hw02 hSc
    have hcw := hXc _ hw0Z c hA.mem_X
    have hca' := hcm c hA.mem_X _ ha'
    have hmul : (c * a) * (s * a * s⁻¹) = (a * c) * (s * a * s⁻¹) := by
      calc (c * a) * (s * a * s⁻¹) = c * (a * (s * a * s⁻¹)) := by group
        _ = (a * (s * a * s⁻¹)) * c := hcw
        _ = a * ((s * a * s⁻¹) * c) := by group
        _ = a * (c * (s * a * s⁻¹)) := by rw [hca']
        _ = (a * c) * (s * a * s⁻¹) := by group
    exact hfpf a ha ha1 (mul_right_cancel hmul)

end CFSG.Quasithin.S15223
