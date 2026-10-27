module

public import CFSG.RankThree.PartTwo.Sec21.FF79Vocab

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF79.L13b

open CFSG CFSG.RankThree.PartTwo.Sec21

variable {G : Type} [Group G] [Finite G]

theorem isSylowOf_card {H P : Subgroup G} (h : IsSylowOf 3 P H) :
    Nat.card P = 3 ^ (Nat.card H).factorization 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hle, hp, hcop⟩ := h
  obtain ⟨a, ha⟩ := hp.exists_card_eq
  have h1 := Subgroup.relIndex_mul_card P H
  rw [inf_of_le_left hle, ha] at h1
  have hne : P.relIndex H ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at h1
    exact Nat.card_pos.ne' h1.symm
  have hf : (P.relIndex H).factorization 3 = 0 :=
    Nat.factorization_eq_zero_of_not_dvd ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp hcop)
  rw [← h1, Nat.factorization_mul hne (by positivity), Finsupp.add_apply, hf,
    Nat.Prime.factorization_pow Nat.prime_three, Finsupp.single_eq_same, zero_add, ha]

theorem isSylowOf_of_card {H P : Subgroup G} (hle : P ≤ H)
    (hc : Nat.card P = 3 ^ (Nat.card H).factorization 3) : IsSylowOf 3 P H := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine ⟨hle, IsPGroup.of_card hc, ?_⟩
  have h1 := Subgroup.relIndex_mul_card P H
  rw [inf_of_le_left hle, hc] at h1
  have hne : P.relIndex H ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at h1
    exact Nat.card_pos.ne' h1.symm
  rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_three]
  intro hdvd
  have hpos : 0 < (P.relIndex H).factorization 3 :=
    Nat.Prime.factorization_pos_of_dvd Nat.prime_three hne hdvd
  have h2 : (P.relIndex H * 3 ^ (Nat.card H).factorization 3).factorization 3 =
      (Nat.card H).factorization 3 := by rw [h1]
  rw [Nat.factorization_mul hne (by positivity), Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_three, Finsupp.single_eq_same] at h2
  omega

theorem exists_sylowOf (H : Subgroup G) : ∃ P : Subgroup G, IsSylowOf 3 P H := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨P⟩ : Nonempty (Sylow 3 H) := inferInstance
  refine ⟨(P : Subgroup H).map H.subtype, ?_, ?_, ?_⟩
  · rintro _ ⟨x, -, rfl⟩
    exact x.2
  · exact P.isPGroup'.map H.subtype
  · rw [Subgroup.relIndex, Subgroup.subgroupOf,
      Subgroup.comap_map_eq_self_of_injective H.subtype_injective]
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr (P.not_dvd_index)

theorem exists_conj_le_sylowOf {H P Q : Subgroup G} (hP : IsSylowOf 3 P H) (hQH : Q ≤ H)
    (hQ : IsPGroup 3 Q) : ∃ k ∈ H, ∀ x ∈ Q, k * x * k⁻¹ ∈ P := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hPH, hPp, hPi⟩ := hP
  let A : Subgroup ↥H := P.subgroupOf H
  let Q' : Subgroup ↥H := Q.subgroupOf H
  have hAp : IsPGroup 3 A := hPp.of_equiv (Subgroup.subgroupOfEquivOfLe hPH).symm
  have hQ'p : IsPGroup 3 Q' := hQ.of_equiv (Subgroup.subgroupOfEquivOfLe hQH).symm
  have hAi : ¬ 3 ∣ A.index := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp hPi
  obtain ⟨S, hS⟩ := hQ'p.exists_le_sylow
  obtain ⟨k, hk⟩ := MulAction.exists_smul_eq ↥H (hAp.toSylow hAi) S
  refine ⟨((k : ↥H) : G)⁻¹, H.inv_mem k.2, fun x hx => ?_⟩
  have hxS : (⟨x, hQH hx⟩ : ↥H) ∈ ((k • hAp.toSylow hAi : Sylow 3 ↥H) : Subgroup ↥H) := by
    rw [hk]
    exact hS (show (⟨x, hQH hx⟩ : ↥H) ∈ Q' from hx)
  rw [Sylow.coe_subgroup_smul, IsPGroup.toSylow_coe,
    Subgroup.mem_smul_pointwise_iff_exists] at hxS
  obtain ⟨s, hs, hseq⟩ := hxS
  have h1 := congrArg Subtype.val hseq
  have hsP : (s : G) ∈ P := hs
  have h2 : ((k : ↥H) : G) * (s : G) * ((k : ↥H) : G)⁻¹ = x := by
    simpa [MulAut.smul_def, MulAut.conj_apply] using h1
  have h3 : ((k : ↥H) : G)⁻¹ * x * ((k : ↥H) : G) = s := by
    rw [← h2]; group
  have : ((k : ↥H) : G)⁻¹ * x * ((k : ↥H) : G)⁻¹⁻¹ = s := by rw [inv_inv]; exact h3
  rw [this]
  exact hsP

theorem isSylowOf_inf_normal {H B N : Subgroup G} (hB : IsSylowOf 3 B H) (hNH : N ≤ H)
    (hnorm : ∀ g ∈ H, ∀ n ∈ N, g * n * g⁻¹ ∈ N) : IsSylowOf 3 (B ⊓ N) N := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨Q, hQ⟩ := exists_sylowOf (G := G) N
  obtain ⟨k, hkH, hk⟩ := exists_conj_le_sylowOf hB (hQ.1.trans hNH) hQ.2.1
  let Q' : Subgroup G := Q.map (MulAut.conj k).toMonoidHom
  have hQ'le : Q' ≤ B ⊓ N := by
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨hk x hx, hnorm k hkH x (hQ.1 hx)⟩
  have hQ'card : Nat.card Q' = 3 ^ (Nat.card N).factorization 3 := by
    rw [Subgroup.card_map_of_injective (MulAut.conj k).injective]
    exact isSylowOf_card hQ
  have hQ'syl : IsSylowOf 3 Q' N := isSylowOf_of_card (hQ'le.trans inf_le_right) hQ'card
  refine ⟨inf_le_right, hB.2.1.to_le inf_le_left, ?_⟩
  have h1 := Subgroup.relIndex_mul_relIndex Q' (B ⊓ N) N hQ'le inf_le_right
  have h2 : Nat.Coprime 3 (Q'.relIndex N) := hQ'syl.2.2
  rw [← h1] at h2
  exact Nat.Coprime.coprime_dvd_right (Dvd.intro_left _ rfl) h2

theorem mem_nor_of_forall {B : Subgroup G} {n : G} (h : ∀ y ∈ B, n * y * n⁻¹ ∈ B) :
    n ∈ Nor B := by
  have hle : B.map (MulAut.conj n).toMonoidHom ≤ B := by
    rintro _ ⟨y, hy, rfl⟩
    exact h y hy
  have heq : B.map (MulAut.conj n).toMonoidHom = B :=
    Subgroup.eq_of_le_of_card_ge hle
      (by rw [Subgroup.card_map_of_injective (MulAut.conj n).injective])
  refine Subgroup.mem_set_normalizer_iff.mpr (fun y => ⟨h y, fun hy => ?_⟩)
  have : n * y * n⁻¹ ∈ B.map (MulAut.conj n).toMonoidHom := by rw [heq]; exact hy
  obtain ⟨z, hz, hzy⟩ := this
  have : z = y := by
    have := congrArg (fun t => n⁻¹ * t * n) hzy
    simpa [MulAut.conj_apply, mul_assoc] using this
  rwa [← this]

end CFSG.RankThree.PartTwo.Sec21.FF79.L13b
