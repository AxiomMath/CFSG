module

public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.GroupTheory.Subgroup.Simple
public import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.NoTransv

theorem eq_bot_of_pow_four {S : Type*} [Group S] [Finite S] [IsSimpleGroup S]
    (hS : ∃ a b : S, a * b ≠ b * a) {N : Subgroup S} (hN : N.Normal) (h4 : ∀ x ∈ N, x ^ 4 = 1) :
    N = ⊥ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : N.Normal := hN
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with hNbot | hNtop
  · exact hNbot
  · exfalso
    have h2 : IsPGroup 2 S := by
      rw [IsPGroup.iff_orderOf]
      intro x
      have hx4 : x ^ 4 = 1 := h4 x (by rw [hNtop]; exact Subgroup.mem_top x)
      have hdvd : orderOf x ∣ 2 ^ 2 := by
        simpa using orderOf_dvd_of_pow_eq_one hx4
      obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
      exact ⟨k, hk⟩
    have hZnt : Nontrivial (Subgroup.center S) := h2.center_nontrivial
    have hZ : Subgroup.center S = ⊥ := by
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center S) with hc | hc
      · exact hc
      · obtain ⟨a, b, hne⟩ := hS
        exact absurd ((Subgroup.mem_center_iff.mp (by rw [hc]; exact Subgroup.mem_top b)) a) hne
    exact (Subgroup.nontrivial_iff_ne_bot (Subgroup.center S)).mp hZnt hZ

theorem center_eq_bot_of_isSimpleGroup {T : Type*} [Group T] [IsSimpleGroup T]
    (hT : ∃ a b : T, a * b ≠ b * a) : Subgroup.center T = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center T) with h | h
  · exact h
  · obtain ⟨a, b, hne⟩ := hT
    exact absurd ((Subgroup.mem_center_iff.mp (by rw [h]; exact Subgroup.mem_top b)) a) hne

theorem ker_eq_ker {H S T : Type*} [Group H] [Group S] [Group T] {f : H →* S}
    (hf : Function.Surjective f) (hfk : f.ker ≤ Subgroup.center H)
    (hS : ∀ N : Subgroup S, N.Normal → (∀ x ∈ N, x ^ 4 = 1) → N = ⊥) {ψ : H →* T}
    (hψ : Function.Surjective ψ) (hT : Subgroup.center T = ⊥) (hψk : ∀ h ∈ ψ.ker, h ^ 4 = 1) :
    f.ker = ψ.ker := by
  have h1 : f.ker ≤ ψ.ker := by
    intro x hx
    have hxc : x ∈ Subgroup.center H := hfk hx
    rw [MonoidHom.mem_ker]
    have hmem : ψ x ∈ Subgroup.center T := by
      rw [Subgroup.mem_center_iff]
      intro t
      obtain ⟨y, rfl⟩ := hψ t
      calc ψ y * ψ x = ψ (y * x) := (map_mul ψ y x).symm
        _ = ψ (x * y) := by rw [(Subgroup.mem_center_iff.mp hxc) y]
        _ = ψ x * ψ y := map_mul ψ x y
    rw [hT, Subgroup.mem_bot] at hmem
    exact hmem
  have h2 : ψ.ker ≤ f.ker := by
    have hK : ψ.ker.map f = ⊥ := by
      refine hS (ψ.ker.map f) ((MonoidHom.normal_ker ψ).map f hf) ?_
      intro y hy
      obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
      rw [← map_pow, hψk x hx, map_one]
    rwa [Subgroup.map_eq_bot_iff] at hK
  exact le_antisymm h1 h2

theorem nonempty_mulEquiv_of_ker {H S T : Type*} [Group H] [Group S] [Group T] {f : H →* S}
    (hf : Function.Surjective f) (hfk : f.ker ≤ Subgroup.center H)
    (hS : ∀ N : Subgroup S, N.Normal → (∀ x ∈ N, x ^ 4 = 1) → N = ⊥) {ψ : H →* T}
    (hψ : Function.Surjective ψ) (hT : Subgroup.center T = ⊥) (hψk : ∀ h ∈ ψ.ker, h ^ 4 = 1) :
    Nonempty (S ≃* T) := by
  exact ⟨(QuotientGroup.quotientKerEquivOfSurjective f hf).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq (ker_eq_ker hf hfk hS hψ hT hψk)).trans
      (QuotientGroup.quotientKerEquivOfSurjective ψ hψ))⟩

theorem quotient_center_simple_and_card {X : Type*} [Group X] [IsSimpleGroup X]
    (hZ : Subgroup.center X = ⊥) {n : ℕ} (hcard : Nat.card X = n) :
    IsSimpleGroup (X ⧸ Subgroup.center X) ∧ Nat.card (X ⧸ Subgroup.center X) = n := by
  let e : X ⧸ Subgroup.center X ≃* X :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  exact ⟨e.isSimpleGroup, by rw [Nat.card_congr e.toEquiv, hcard]⟩

end CFSG.LocalAnalysis.UniquenessCase.UC22.NoTransv
