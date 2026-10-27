module

public import CFSG.Quasithin.Background.A3Structure316

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

namespace SBd8

section NS

variable {Γ : Type} [Group Γ]

theorem normalizer_le_normalizer_oPrimeResidualOf' (p : ℕ) (X : Subgroup Γ) :
    Subgroup.normalizer (X : Set Γ) ≤ Subgroup.normalizer (oPrimeResidualOf p X : Set Γ) := by
  have key : ∀ g ∈ Subgroup.normalizer (X : Set Γ), ∀ y ∈ oPrimeResidualOf p X,
      g * y * g⁻¹ ∈ oPrimeResidualOf p X := by
    intro g hg y hy
    induction hy using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨hxX, k, hk⟩ := hx
      refine Subgroup.subset_closure ⟨(Subgroup.mem_normalizer_iff.mp hg x).mp hxX, k, ?_⟩
      rw [← MulAut.conj_apply, MulEquiv.orderOf_eq]
      exact hk
    | one => simp
    | mul x y _ _ ihx ihy => simpa [mul_assoc] using (oPrimeResidualOf p X).mul_mem ihx ihy
    | inv x _ ihx => simpa [mul_assoc] using (oPrimeResidualOf p X).inv_mem ihx
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => key g hg x hx, fun hx => ?_⟩
  have := key g⁻¹ ((Subgroup.normalizer (X : Set Γ)).inv_mem hg) _ hx
  simpa [mul_assoc] using this

theorem normal_solvable_eq_bot_of_simple {Λ : Type} [Group Λ] (hs : IsSimpleGroup Λ)
    (hns : ¬ Group.IsSolvable Λ) :
    ∀ M : Subgroup Λ, M.Normal → Group.IsSolvable ↥M → M = ⊥ := by
  intro M hM hMs
  rcases hs.eq_bot_or_eq_top_of_normal M with h | h
  · exact h
  · exfalso
    apply hns
    rw [h] at hMs
    exact Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.topEquiv (G := Λ)).symm.toMonoidHom) (MulEquiv.injective _)

theorem false_of_surjective_of_solvable_oPrime {K N : Subgroup Γ} (hNK : N ≤ K)
    (hY : Group.IsSolvable ↥(oPrimeResidualOf 3 K)) {Λ : Type} [Group Λ] (π : ↥N →* Λ)
    (hπ : Function.Surjective π)
    (hΛ : ∀ M : Subgroup Λ, M.Normal → Group.IsSolvable ↥M → M = ⊥) (h3 : 3 ∣ Nat.card Λ) [Finite Γ] :
    False := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hfinΛ : Finite Λ := Finite.of_surjective π hπ
  obtain ⟨x₀, hx₀⟩ := exists_prime_orderOf_dvd_card' 3 h3
  obtain ⟨n₀, hn₀⟩ := hπ x₀
  set Y := oPrimeResidualOf 3 K with hYdef
  have hKN : K ≤ Subgroup.normalizer (Y : Set Γ) :=
    (Subgroup.le_normalizer).trans (normalizer_le_normalizer_oPrimeResidualOf' 3 K)
  set W : Subgroup ↥N := Y.subgroupOf N with hW
  have hWn : W.Normal := by
    refine ⟨fun w hw n => ?_⟩
    have hwY : (w : Γ) ∈ Y := hw
    have h1 := (Subgroup.mem_normalizer_iff.mp (hKN (hNK n.2)) (w : Γ)).1 hwY
    exact h1
  have hMn : (W.map π).Normal := hWn.map π hπ
  have hWs : Group.IsSolvable ↥W := by
    refine Group.isSolvable_of_isSolvable_injective
      (f := ((N.subtype.comp W.subtype).codRestrict Y (fun x => x.2)))  (fun a b hab => ?_)
    have h1 : (((a : ↥N)) : Γ) = (((b : ↥N)) : Γ) := congrArg (fun y : ↥Y => (y : Γ)) hab
    exact Subtype.ext (Subtype.ext h1)
  have hMs : Group.IsSolvable ↥(W.map π) :=
    Group.isSolvable_of_surjective (f := π.subgroupMap W) (MonoidHom.subgroupMap_surjective π W)
  have hM := hΛ _ hMn hMs
  have hord : 0 < orderOf n₀ := orderOf_pos n₀
  obtain ⟨a, b, hb, hab⟩ := Nat.exists_eq_pow_mul_and_not_dvd hord.ne' 3 Nat.prime_three.ne_one
  set n : ↥N := n₀ ^ b with hn
  have hn3 : ∃ k : ℕ, orderOf (n : Γ) = 3 ^ k := by
    have h1 : n ^ (3 ^ a) = 1 := by
      rw [hn, ← pow_mul, mul_comm, ← hab, pow_orderOf_eq_one]
    have h2 : orderOf n ∣ 3 ^ a := orderOf_dvd_of_pow_eq_one h1
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 h2
    exact ⟨k, by rw [Subgroup.orderOf_coe]; exact hk⟩
  have hnY : (n : Γ) ∈ Y := by
    obtain ⟨k, hk⟩ := hn3
    exact Subgroup.subset_closure ⟨hNK n.2, k, hk⟩
  have hnW : n ∈ W := hnY
  have hπn : π n ≠ 1 := by
    intro h
    rw [hn, map_pow, hn₀] at h
    have := orderOf_dvd_of_pow_eq_one h
    rw [hx₀] at this
    exact hb this
  have : π n ∈ W.map π := Subgroup.mem_map_of_mem π hnW
  rw [hM] at this
  exact hπn (Subgroup.mem_bot.1 this)

end NS

end SBd8

end CFSG.Quasithin
