module

public import CFSG.Quasithin.H13.KG14726Corr
public import CFSG.Quasithin.H13.KG14726C27
public import CFSG.GH74.KGroups.U33
public import CFSG.Assembly.GL83LieDefs
public import CFSG.Quasithin.Background.A3StructureDefs

public section

namespace CFSG.Quasithin.H13.KG14726

open Subgroup CFSG.Quasithin CFSG.Assembly.LowTwoRank

theorem false_of_isPSU_three_three
    {X : Type} [Group X] (hqs : CFSG.IsQuasisimple X)
    (h : IsPSU 3 3 1 X) {A B : Subgroup (MulAut X)}
    (hA : (MulAut.conj : X →* MulAut X).range ≤ A) (hBA : B ≤ A)
    (hBi : ¬ 2 ∣ (B.subgroupOf A).index) (hB : ∃ a : ℕ, Nat.card B = 2 ^ a * 27) : False := by
  have hL : CFSG.Blueprint.LieModel X .PSU 3 3 1 := Or.inl ⟨by decide, h⟩
  obtain ⟨e⟩ := CFSG.GH74.KGroups.U33.equiv_of_lieModel hL
  have hAut : Nat.card (MulAut X) = 12096 := CFSG.GH74.KGroups.U33.card_mulAut e
  have : Finite X := CFSG.GH74.KGroups.U33.finite_K e
  have hX : Nat.card X = 6048 := by
    rw [Nat.card_congr e.toEquiv, CFSG.GH74.KGroups.card_group _ CFSG.GH74.KGroups.U33.QP_ok,
      CFSG.GH74.KGroups.U33.QP_valid.2]
  obtain ⟨-, K, _, _, hK, ⟨eT⟩⟩ := h
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : IsSimpleGroup (StatedProj (StatedSU 3 (3 ^ 1) K)) :=
    CFSG.ClassicalGroups.Unitary.isSimpleGroup_statedProj_statedSU K 3 1 hK 3 le_rfl (by decide)
  have hc : center X = ⊥ := center_eq_bot_of_mulEquiv_simple hqs eT
  set I := (MulAut.conj : X →* MulAut X).range with hIdef
  have eI : X ≃* ↥I := (quotientCenterEquivSelf hc).symm.trans quotientCenterEquivInn
  have hIcard : Nat.card I = 6048 := by rw [← Nat.card_congr eI.toEquiv, hX]
  have : Nontrivial X := eT.symm.injective.nontrivial
  have : IsSimpleGroup X :=
    IsSimpleGroup.isSimpleGroup_of_surjective eT.symm.toMonoidHom eT.symm.surjective
  have : Nontrivial ↥I := eI.injective.nontrivial
  have : IsSimpleGroup ↥I := IsSimpleGroup.isSimpleGroup_of_surjective eI.toMonoidHom eI.surjective
  have : I.Normal := inn_normal
  have hIidx : I.index = 2 := by
    have h2 := I.card_mul_index
    rw [hIcard, hAut] at h2
    omega
  have hin : ∀ b ∈ B, b ^ 27 = 1 → b ∈ I := by
    intro b _ hb27
    have h2 : b ^ 2 ∈ I := by
      have := I.pow_index_mem b
      rwa [hIidx] at this
    have hb : b = (b ^ 2) ^ 14 * (b ^ 27)⁻¹ := by
      rw [← pow_mul, ← zpow_natCast, ← zpow_natCast, ← zpow_neg, ← zpow_add]
      norm_num
    rw [hb, hb27, inv_one, mul_one]
    exact I.pow_mem h2 14
  have h27 := twentyseven_dvd_card_inf_inn hB hin
  have hodd : ¬ 2 ∣ B.relIndex I := odd_relIndex_inn hA hBA hBi
  have hrel := Subgroup.relIndex_mul_card B I
  rw [hIcard] at hrel
  obtain ⟨a, ha⟩ := hB
  have hcB : Nat.card ↥(B ⊓ I) ∣ 2 ^ a * 27 := by
    rw [← ha]
    exact card_dvd_of_le inf_le_left
  obtain ⟨c, hc⟩ := h27
  have hc2 : c ∣ 2 ^ a := by
    rw [hc, mul_comm] at hcB
    exact Nat.dvd_of_mul_dvd_mul_right (by norm_num) hcB
  obtain ⟨j, hj, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hc2
  rw [hc, show B.relIndex I * (27 * 2 ^ j) = (B.relIndex I * 2 ^ j) * 27 by ring] at hrel
  have hr : B.relIndex I * 2 ^ j = 224 := by omega
  have hj5 : j ≤ 5 := by
    by_contra hj5
    push Not at hj5
    have hdvd : 2 ^ j ∣ 224 := ⟨B.relIndex I, by rw [← hr]; ring⟩
    have h64 := (pow_dvd_pow 2 hj5).trans hdvd
    norm_num at h64
  have h7 : B.relIndex I = 7 := by
    interval_cases j <;> omega
  have hne : B.subgroupOf I ≠ ⊤ := by
    intro htop
    have : B.relIndex I = 1 := by
      rw [Subgroup.relIndex, htop, Subgroup.index_top]
    omega
  have : (B.subgroupOf I).FiniteIndex := Subgroup.finiteIndex_of_finite
  have hle := card_le_factorial_index hne
  rw [hIcard, ← Subgroup.relIndex, h7] at hle
  exact absurd hle (by decide)

end CFSG.Quasithin.H13.KG14726

end
