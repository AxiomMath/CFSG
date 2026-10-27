module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.HallSubgroups.Existence

public section

namespace CFSG.RankThree.PGroups

open Subgroup

theorem solvable_coprime_invariant_sylow_containment {A H : Type*} [Group A] [Group H]
    [Finite A] [Finite H] [Group.IsSolvable A] [Group.IsSolvable H]
    (hcop : Nat.Coprime (Nat.card A) (Nat.card H)) (ρ : A →* MulAut H) {q : ℕ} (hq : q.Prime) :
    (∀ U : Subgroup H, IsPGroup q U → (∀ a : A, ∀ u ∈ U, ρ a u ∈ U) →
      ∃ Q : Sylow q H, U ≤ (Q : Subgroup H) ∧
        ∀ a : A, (Q : Subgroup H).map (ρ a).toMonoidHom = Q) ∧
    ∃ Q : Sylow q H, ∀ a : A, (Q : Subgroup H).map (ρ a).toMonoidHom = Q := by
  have : Fact q.Prime := ⟨hq⟩
  let : MulDistribMulAction A H := MulDistribMulAction.compHom H ρ
  have hsmul : ∀ (a : A) (h : H), a • h = ρ a h := fun _ _ => rfl
  have main : ∀ U : Subgroup H, IsPGroup q U → (∀ a : A, ∀ u ∈ U, ρ a u ∈ U) →
      ∃ Q : Sylow q H, U ≤ (Q : Subgroup H) ∧
        ∀ a : A, (Q : Subgroup H).map (ρ a).toMonoidHom = Q := by
    intro U hU hUinv
    let π : Set Nat.Primes := {r | r.val = q}
    have hUπ : IsPiSubgroup π U := fun r hr => by
      obtain ⟨k, hk⟩ := hU.exists_card_eq
      rw [hk] at hr
      exact (Nat.prime_dvd_prime_iff_eq r.2 hq).1 (r.2.dvd_of_dvd_pow hr)
    have hUinv' : IsInvariant A H U := ⟨fun a g => ⟨fun hg => hUinv a g hg,
      fun hg => by
        have h := hUinv a⁻¹ _ hg
        rwa [hsmul, ← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one,
          MulAut.one_apply] at h⟩⟩
    obtain ⟨K, hK, hKinv, hUK⟩ :=
      exists_isHallSubgroup_isInvariant_of_isPiSubgroup inferInstance hcop π U hUπ hUinv'
    have hKq : IsPGroup q K := IsPGroup.of_card (Nat.eq_prime_pow_of_unique_prime_dvd
      Nat.card_pos.ne' fun {d} hd hdK => hK.p_in_pi_of_p_dvd_card ⟨d, hd⟩ hdK)
    have hKidx : ¬ q ∣ K.index := fun h => hK.p_in_pi_of_p_dvd_index ⟨q, hq⟩ h rfl
    refine ⟨hKq.toSylow hKidx, hUK, fun a => ?_⟩
    change K.map (ρ a).toMonoidHom = K
    have hle : ∀ b : A, K.map (ρ b).toMonoidHom ≤ K := by
      rintro b _ ⟨k, hk, rfl⟩
      exact (hKinv.invariant b k).1 hk
    refine eq_of_le_of_card_ge (hle a) ?_
    rw [card_map_of_injective (ρ a).injective]
  refine ⟨main, ?_⟩
  obtain ⟨Q, -, hQ⟩ := main ⊥ (IsPGroup.of_card (n := 0) (by rw [card_bot, pow_zero]))
    fun a u hu => by rw [mem_bot.1 hu, map_one]; exact one_mem _
  exact ⟨Q, hQ⟩

end CFSG.RankThree.PGroups
