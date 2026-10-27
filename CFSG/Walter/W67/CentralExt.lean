module

public import Mathlib.GroupTheory.Transfer
public import Mathlib.GroupTheory.Abelianization.Defs

public section

namespace CFSG.Walter.W67

variable {E : Type*} [Group E] [Finite E]

open scoped IsMulCommutative in
theorem inf_commutator_eq_bot_of_isPGroup {p : ℕ} [Fact p.Prime] (P : Sylow p E)
    (hP : IsMulCommutative (P : Subgroup E)) {Z : Subgroup E} (hZc : Z ≤ Subgroup.center E)
    (hZp : IsPGroup p Z) : Z ⊓ commutator E = ⊥ := by
  have : IsMulCommutative (P : Subgroup E) := hP
  have hZn : Z.Normal := Subgroup.normal_of_le_center hZc
  have hZP : Z ≤ (P : Subgroup E) := hZp.le_sylow_of_normal P
  let τ : E →* P := MonoidHom.transfer (MonoidHom.id P)
  rw [eq_bot_iff]
  intro z hz
  obtain ⟨hzZ, hzD⟩ := Subgroup.mem_inf.mp hz
  have hτ1 : τ z = 1 := by
    have hker : commutator E ≤ τ.ker := by
      exact Abelianization.commutator_subset_ker τ
    exact hker hzD
  have hzc : z ∈ Subgroup.center E := hZc hzZ
  have hτ2 := MonoidHom.transfer_eq_pow (MonoidHom.id P) z (fun k g₀ _ => by
    have hk : z ^ k ∈ Subgroup.center E := Subgroup.pow_mem _ hzc k
    rw [Subgroup.mem_center_iff] at hk
    rw [mul_assoc, ← hk g₀, ← mul_assoc, inv_mul_cancel, one_mul])
  have hpow : z ^ (P : Subgroup E).index = 1 := by
    have h := hτ2.symm.trans hτ1
    have := congrArg Subtype.val h
    simpa using this
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hZp) ⟨z, hzZ⟩
  rw [Subgroup.orderOf_mk] at hk
  have hdvd : orderOf z ∣ (P : Subgroup E).index := orderOf_dvd_of_pow_eq_one hpow
  have hcop : Nat.Coprime (p ^ k) (P : Subgroup E).index :=
    Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr P.not_dvd_index)
  rw [hk] at hdvd
  have h1 : p ^ k = 1 := Nat.Coprime.eq_one_of_dvd hcop hdvd
  rw [Subgroup.mem_bot, ← orderOf_eq_one_iff, hk, h1]

theorem inf_commutator_eq_bot {Z : Subgroup E} (hZc : Z ≤ Subgroup.center E)
    (hab : ∀ p : ℕ, p.Prime → p ∣ Nat.card Z →
      ∃ (_ : Fact p.Prime) (P : Sylow p E), IsMulCommutative (P : Subgroup E)) :
    Z ⊓ commutator E = ⊥ := by
  by_contra hne
  obtain ⟨z, hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  have hzZ : (z : E) ∈ Z := (Subgroup.mem_inf.mp z.2).1
  have hzD : (z : E) ∈ commutator E := (Subgroup.mem_inf.mp z.2).2
  obtain ⟨p, hp, hpz⟩ : ∃ p, p.Prime ∧ p ∣ orderOf (z : E) := by
    refine Nat.exists_prime_and_dvd ?_
    intro h1
    rw [orderOf_eq_one_iff] at h1
    exact hz1 (Subtype.ext h1)
  have : Fact p.Prime := ⟨hp⟩
  set w : E := (z : E) ^ (orderOf (z : E) / p) with hw
  have hwo : orderOf w = p := by
    rw [hw, orderOf_pow_orderOf_div (orderOf_pos (z : E)).ne' hpz]
  have hwZ : w ∈ Z := Subgroup.pow_mem _ hzZ _
  have hwD : w ∈ commutator E := Subgroup.pow_mem _ hzD _
  have hpZ : p ∣ Nat.card Z := by
    rw [← hwo, ← Subgroup.orderOf_mk w hwZ]
    exact orderOf_dvd_natCard _
  obtain ⟨_, P, hP⟩ := hab p hp hpZ
  have hWc : Subgroup.zpowers w ≤ Subgroup.center E :=
    (Subgroup.zpowers_le).mpr (hZc hwZ)
  have hWp : IsPGroup p (Subgroup.zpowers w) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hwo, pow_one])
  have h := inf_commutator_eq_bot_of_isPGroup P hP hWc hWp
  have hw1 : w = 1 := by
    have : w ∈ Subgroup.zpowers w ⊓ commutator E :=
      Subgroup.mem_inf.mpr ⟨Subgroup.mem_zpowers w, hwD⟩
    rw [h] at this
    exact Subgroup.mem_bot.mp this
  rw [hw1, orderOf_one] at hwo
  exact hp.one_lt.ne hwo

omit [Finite E] in
theorem commutator_sup_eq_top_and_inf_eq_bot {Z : Subgroup E}
    (hZD : Z ⊓ commutator E = ⊥) (hEZ : commutator E ⊔ Z = ⊤) :
    commutator E ⊔ Z = ⊤ ∧ commutator E ⊓ Z = ⊥ :=
  ⟨hEZ, by rw [inf_comm]; exact hZD⟩

end CFSG.Walter.W67
