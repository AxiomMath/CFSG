module

public import CFSG.RankThree.PartOne.SEITZ12.SuzukiTwo
public import CFSG.RankThree.PartOne.SEITZ7.SzRoot

public section

namespace CFSG.RankThree.PartOne.SEITZ12

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.LieType.Ree.ReeTag CFSG.LieType.Ree.LargeReeInvolution CFSG.LieType.Ree.LargeReeCover
  CFSG.RankThree.PartOne.SEITZ7
open scoped commutatorElement

set_option linter.unusedSectionVars false

variable {m : ℕ} {K : Type} [Field K] [Finite K] [CharP K F4.prime]

theorem U₂_le_rankOneGroupTwo :
    F4.reeFixedOrbitUnipotent K m ⟨1, by decide⟩ ≤ rankOneGroupTwo K m :=
  fun _ hg => Subgroup.subset_closure (Or.inl (Or.inl hg))

theorem weylTwo_mem_rankOneGroupTwo : weylTwo K ∈ rankOneGroupTwo K m :=
  Subgroup.subset_closure (Or.inr rfl)

theorem phi4_index_U₂ (hm : 1 ≤ m) (hK : Nat.card K = 2 ^ (2 * m + 1)) :
    ((F4.reeFixedOrbitUnipotent K m ⟨1, by decide⟩).subgroupOf (rankOneGroupTwo K m)).index =
      (2 ^ (2 * m + 1) - 1) * ((2 ^ (2 * m + 1)) ^ 2 + 1) := by
  have h1 := Subgroup.card_mul_index
    ((F4.reeFixedOrbitUnipotent K m ⟨1, by decide⟩).subgroupOf (rankOneGroupTwo K m))
  have h2 : Nat.card ((F4.reeFixedOrbitUnipotent K m ⟨1, by decide⟩).subgroupOf
      (rankOneGroupTwo K m)) = (2 ^ (2 * m + 1)) ^ 2 := by
    rw [← phi4s_card_U₂ hK]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe U₂_le_rankOneGroupTwo).toEquiv
  have h3 : Nat.card (rankOneGroupTwo K m) = (2 ^ (2 * m + 1)) ^ 2 * (2 ^ (2 * m + 1) - 1) *
      ((2 ^ (2 * m + 1)) ^ 2 + 1) := card_rankOneGroupTwo hm hK
  rw [Nat.card_congr (Equiv.refl _), h3, h2] at h1
  have hq : 0 < (2 ^ (2 * m + 1)) ^ 2 := by positivity
  refine Nat.eq_of_mul_eq_mul_left hq ?_
  rw [h1, mul_assoc]

theorem phi4_index_U₂_odd (hm : 1 ≤ m) (hK : Nat.card K = 2 ^ (2 * m + 1)) :
    ¬ 2 ∣
      ((F4.reeFixedOrbitUnipotent K m ⟨1, by decide⟩).subgroupOf (rankOneGroupTwo K m)).index := by
  rw [phi4_index_U₂ hm hK]
  have h2 : 2 ∣ 2 ^ (2 * m + 1) := dvd_pow_self 2 (by omega)
  have h1 : 1 ≤ 2 ^ (2 * m + 1) := Nat.one_le_two_pow
  intro h
  rcases (Nat.Prime.dvd_mul Nat.prime_two).1 h with h | h
  · omega
  · have : 2 ∣ (2 ^ (2 * m + 1)) ^ 2 := dvd_pow h2 two_ne_zero
    omega

theorem phi4_card_U₂_subgroupOf (hK : Nat.card K = 2 ^ (2 * m + 1)) :
    Nat.card ((F4.reeFixedOrbitUnipotent K m ⟨1, by decide⟩).subgroupOf (rankOneGroupTwo K m)) =
      2 ^ (2 * (2 * m + 1)) := by
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe U₂_le_rankOneGroupTwo).toEquiv,
    phi4s_card_U₂ hK]
  ring

@[expose] noncomputable def phi4Sylow (hm : 1 ≤ m) (hK : Nat.card K = 2 ^ (2 * m + 1)) :
    Sylow 2 (rankOneGroupTwo K m) :=
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  (IsPGroup.of_card (phi4_card_U₂_subgroupOf hK)).toSylow (phi4_index_U₂_odd hm hK)

theorem coe_phi4Sylow (hm : 1 ≤ m) (hK : Nat.card K = 2 ^ (2 * m + 1)) :
    (phi4Sylow hm hK : Subgroup (rankOneGroupTwo K m)) =
      (F4.reeFixedOrbitUnipotent K m ⟨1, by decide⟩).subgroupOf (rankOneGroupTwo K m) :=
  rfl

theorem phi4_U₂_max (hm : 1 ≤ m) (hK : Nat.card K = 2 ^ (2 * m + 1))
    (P : Subgroup (ModGL F4.tag K)) (hP : P ≤ rankOneGroupTwo K m) (hP2 : IsPGroup 2 P)
    (hU : F4.reeFixedOrbitUnipotent K m ⟨1, by decide⟩ ≤ P) :
    P = F4.reeFixedOrbitUnipotent K m ⟨1, by decide⟩ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 : IsPGroup 2 (P.subgroupOf (rankOneGroupTwo K m)) :=
    hP2.of_equiv (Subgroup.subgroupOfEquivOfLe hP).symm
  have h2 := (phi4Sylow hm hK).is_maximal' h1 (by
    rw [coe_phi4Sylow]
    exact fun x hx => hU hx)
  refine le_antisymm ?_ hU
  intro x hx
  have : (⟨x, hP hx⟩ : rankOneGroupTwo K m) ∈
      (F4.reeFixedOrbitUnipotent K m ⟨1, by decide⟩).subgroupOf (rankOneGroupTwo K m) := by
    rw [← coe_phi4Sylow hm hK, ← h2]
    exact hx
  exact this

theorem phi4_conj_into_U₂ (hm : 1 ≤ m) (hK : Nat.card K = 2 ^ (2 * m + 1))
    {x : ModGL F4.tag K} (hx : x ∈ rankOneGroupTwo K m) (hx2 : x * x = 1) :
    ∃ g ∈ rankOneGroupTwo K m, g * x * g⁻¹ ∈ F4.reeFixedOrbitUnipotent K m ⟨1, by decide⟩ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let y : rankOneGroupTwo K m := ⟨x, hx⟩
  have hy2 : y * y = 1 := Subtype.ext hx2
  have hord : orderOf y ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hy2)
  have hyp : IsPGroup 2 (Subgroup.zpowers y) := by
    rcases (Nat.dvd_prime Nat.prime_two).1 hord with h | h
    · exact IsPGroup.of_card (n := 0) (by rw [Nat.card_zpowers, h]; rfl)
    · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h]; rfl)
  obtain ⟨Q, hQ⟩ := hyp.exists_le_sylow
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq (rankOneGroupTwo K m) (phi4Sylow hm hK) Q
  have h1 : ((c • phi4Sylow hm hK : Sylow 2 (rankOneGroupTwo K m)) :
      Subgroup (rankOneGroupTwo K m)) = (Q : Subgroup (rankOneGroupTwo K m)) := by rw [hc]
  rw [Sylow.coe_subgroup_smul] at h1
  have hyQ : y ∈ (Q : Subgroup (rankOneGroupTwo K m)) := hQ (Subgroup.mem_zpowers y)
  rw [← h1, Subgroup.mem_pointwise_smul_iff_inv_smul_mem, coe_phi4Sylow] at hyQ
  refine ⟨((c⁻¹ : rankOneGroupTwo K m) : ModGL F4.tag K), (c⁻¹).2, ?_⟩
  have h3 : ((((MulAut.conj c)⁻¹ • y : rankOneGroupTwo K m)) : ModGL F4.tag K) =
      ((c⁻¹ : rankOneGroupTwo K m) : ModGL F4.tag K) * x *
        ((c⁻¹ : rankOneGroupTwo K m) : ModGL F4.tag K)⁻¹ := by
    simp [MulAut.smul_def, MulAut.inv_def, MulAut.conj_symm_apply, y]
  rw [← h3]
  exact hyQ

theorem phi4_sylowB_zero_zero : sylowB m K 0 0 = 1 := by
  simp [sylowB, sylowX, largeReeSigma_zero, pinnedX_zero]

theorem phi4_involution_conj (hm : 1 ≤ m) (hK : Nat.card K = 2 ^ (2 * m + 1))
    {x : ModGL F4.tag K} (hx : x ∈ rankOneGroupTwo K m) (hx2 : x * x = 1) (hx1 : x ≠ 1) :
    ∃ g ∈ rankOneGroupTwo K m, ∃ c : K, c ≠ 0 ∧ g * x * g⁻¹ = sylowB m K 0 c := by
  obtain ⟨g, hg, hgU⟩ := phi4_conj_into_U₂ hm hK hx hx2
  have hsq : (g * x * g⁻¹) * (g * x * g⁻¹) = 1 := by
    calc (g * x * g⁻¹) * (g * x * g⁻¹) = g * (x * x) * g⁻¹ := by group
      _ = 1 := by rw [hx2]; group
  have hz : g * x * g⁻¹ ∈ zTwo m K := (suzukiTwo_U₂ hm hK).eq_one_of_sq _ hgU hsq
  obtain ⟨c, hc⟩ := (mem_zTwo_iff _).1 hz
  refine ⟨g, hg, c, fun hc0 => hx1 ?_, hc⟩
  rw [hc0, phi4_sylowB_zero_zero] at hc
  have : x = g⁻¹ * (g * x * g⁻¹) * g := by group
  rw [this, hc]
  group

theorem rankOneGroupTwo_perfect (hm : 1 ≤ m) (hK : Nat.card K = 2 ^ (2 * m + 1)) :
    ⁅rankOneGroupTwo K m, rankOneGroupTwo K m⁆ = rankOneGroupTwo K m := by
  obtain ⟨hs, x, y, hxy⟩ := isSimpleGroup_rankOneGroupTwo hm hK
  rcases hs.eq_bot_or_eq_top_of_normal (commutator (rankOneGroupTwo K m)) with h | h
  · exfalso
    apply hxy
    have h1 : ⁅x, y⁆ ∈ commutator (rankOneGroupTwo K m) :=
      Subgroup.commutator_mem_commutator (Subgroup.mem_top x) (Subgroup.mem_top y)
    rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
    exact h1
  · rw [← Subgroup.map_subtype_commutator, h, Subgroup.map_top, Subgroup.range_subtype]

end CFSG.RankThree.PartOne.SEITZ12
