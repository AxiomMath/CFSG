module

public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148V

theorem a5n_conj_mem_zpowers {Q : Type} [Group Q] {Jq Zq : Subgroup Q} {f x : Q}
    (hJZ : ∀ u ∈ Jq, ∀ v ∈ Zq, u * v = v * u) (hint : Jq ⊓ Zq = ⊥)
    (hfZ : f ∈ Zq) (hxJ : x ∈ Jq)
    (hN : Zq ≤ Subgroup.normalizer (Subgroup.zpowers (f * x) : Set Q)) :
    ∀ z ∈ Zq, z * f * z⁻¹ ∈ Subgroup.zpowers f := by
  intro z hz
  have hcomm : Commute f x := (hJZ x hxJ f hfZ).symm
  have hxz : Commute x z := hJZ x hxJ z hz
  have hxzinv : x * z⁻¹ = z⁻¹ * x := hxz.inv_right.eq
  have hmem : f * x ∈ (Subgroup.zpowers (f * x) : Set Q) :=
    SetLike.mem_coe.2 (Subgroup.mem_zpowers (f * x))
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1
    (SetLike.mem_coe.1 ((Subgroup.mem_set_normalizer_iff.1 (hN hz) (f * x)).1 hmem))
  rw [hcomm.mul_zpow] at hm
  have hsplit : z * (f * x) * z⁻¹ = z * f * z⁻¹ * x := by
    calc z * (f * x) * z⁻¹ = z * f * (x * z⁻¹) := by group
      _ = z * f * (z⁻¹ * x) := by rw [hxzinv]
      _ = z * f * z⁻¹ * x := by group
  rw [hsplit] at hm
  have h2 : z * f * z⁻¹ = f ^ m * x ^ m * x⁻¹ := by
    rw [hm, mul_inv_cancel_right]
  have hconj : (f ^ m)⁻¹ * (z * f * z⁻¹) = x ^ m * x⁻¹ := by
    rw [h2]; group
  have hJmem : (f ^ m)⁻¹ * (z * f * z⁻¹) ∈ Jq := by
    rw [hconj]; exact Jq.mul_mem (Jq.zpow_mem hxJ m) (Jq.inv_mem hxJ)
  have hZmem : (f ^ m)⁻¹ * (z * f * z⁻¹) ∈ Zq :=
    Zq.mul_mem (Zq.inv_mem (Zq.zpow_mem hfZ m)) (Zq.mul_mem (Zq.mul_mem hz hfZ) (Zq.inv_mem hz))
  have h1 : (f ^ m)⁻¹ * (z * f * z⁻¹) = 1 := by
    have hinf : (f ^ m)⁻¹ * (z * f * z⁻¹) ∈ Jq ⊓ Zq := Subgroup.mem_inf.2 ⟨hJmem, hZmem⟩
    rwa [hint, Subgroup.mem_bot] at hinf
  have h3 : f ^ m = z * f * z⁻¹ := inv_mul_eq_one.1 h1
  rw [← h3]
  exact Subgroup.zpow_mem_zpowers f m

theorem a5n_zpowers_normal {Q : Type} [Group Q] {Zq : Subgroup Q} {f : Q}
    (hfZ : f ∈ Zq) (hconj : ∀ z ∈ Zq, z * f * z⁻¹ ∈ Subgroup.zpowers f) :
    ((Subgroup.zpowers f).subgroupOf Zq).Normal := by
  have hle : Subgroup.zpowers f ≤ Zq := Subgroup.zpowers_le.2 hfZ
  have fwd : ∀ z ∈ Zq, ∀ h ∈ Subgroup.zpowers f, z * h * z⁻¹ ∈ Subgroup.zpowers f := by
    intro z hz h hh
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hh
    rw [← conj_zpow]
    exact Subgroup.zpow_mem _ (hconj z hz) k
  refine (Subgroup.normal_subgroupOf_iff_le_normalizer hle).2 ?_
  intro g hg
  rw [Subgroup.mem_set_normalizer_iff]
  intro h
  constructor
  · intro hh
    exact fwd g hg h hh
  · intro hh
    have key := fwd g⁻¹ (Zq.inv_mem hg) (g * h * g⁻¹) hh
    have e : g⁻¹ * (g * h * g⁻¹) * g⁻¹⁻¹ = h := by group
    rw [e] at key
    exact key

theorem a5n_card_alt5 : Nat.card (alternatingGroup (Fin 5)) = 60 := by
  rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
  norm_num [Nat.factorial]

theorem a5n_false_of_zpowers_normal {Q : Type} [Group Q] [Finite Q] {Zq : Subgroup Q} {f : Q}
    (φ : ↥Zq ≃* alternatingGroup (Fin 5)) (hfZ : f ∈ Zq) (hf3 : f ^ 3 = 1) (hf1 : f ≠ 1)
    (hnorm : ((Subgroup.zpowers f).subgroupOf Zq).Normal) : False := by
  haveI : IsSimpleGroup (alternatingGroup (Fin 5)) :=
    alternatingGroup.isSimpleGroup (by simp)
  haveI : IsSimpleGroup ↥Zq := φ.isSimpleGroup
  rcases Subgroup.Normal.eq_bot_or_eq_top ((Subgroup.zpowers f).subgroupOf Zq) with hbot | htop
  · have hmem : (⟨f, hfZ⟩ : ↥Zq) ∈ (Subgroup.zpowers f).subgroupOf Zq :=
      Subgroup.mem_subgroupOf.2 (Subgroup.mem_zpowers f)
    rw [hbot, Subgroup.mem_bot] at hmem
    have hval := congrArg Subtype.val hmem
    simp only [ZeroMemClass.coe_zero, OneMemClass.coe_one] at hval
    exact hf1 hval
  · have hle : Zq ≤ Subgroup.zpowers f := by
      intro z hz
      have hzN : (⟨z, hz⟩ : ↥Zq) ∈ (Subgroup.zpowers f).subgroupOf Zq := by
        rw [htop]; exact Subgroup.mem_top _
      exact Subgroup.mem_subgroupOf.1 hzN
    have h1 : Nat.card Zq ≤ Nat.card (Subgroup.zpowers f) := Subgroup.card_le_of_le hle
    have h2 : Nat.card (Subgroup.zpowers f) = 3 := by
      rw [Nat.card_zpowers, orderOf_eq_prime hf3 hf1]
    have h3 : Nat.card Zq = 60 := by
      rw [Nat.card_congr φ.toEquiv, a5n_card_alt5]
    omega

theorem zpow_eq_one_of_normalizer_a5 {Q : Type} [Group Q] [Finite Q] {Jq Zq : Subgroup Q}
    {e x : Q} {l : ℤ}
    (hJZ : ∀ u ∈ Jq, ∀ v ∈ Zq, u * v = v * u) (hint : Jq ⊓ Zq = ⊥)
    (φ : ↥Zq ≃* alternatingGroup (Fin 5)) (heZ : e ∈ Zq) (he3 : e ^ 3 = 1) (hxJ : x ∈ Jq)
    (hN : Zq ≤ Subgroup.normalizer (Subgroup.zpowers (e ^ l * x) : Set Q)) : e ^ l = 1 := by
  by_contra hf1
  have hfZ : e ^ l ∈ Zq := Zq.zpow_mem heZ l
  have hf3 : (e ^ l) ^ 3 = 1 := by
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, he3, one_zpow]
  exact a5n_false_of_zpowers_normal φ hfZ hf3 hf1
    (a5n_zpowers_normal hfZ (a5n_conj_mem_zpowers hJZ hint hfZ hxJ hN))

end CFSG.RankThree.PartTwo.Sec14.Ronan148V
