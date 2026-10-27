module

public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF79

open MulAction Pointwise

theorem aut_cube_apply {H : Type} [Group H] {β : MulAut H} (h3 : β ^ 3 = 1) (h : H) :
    β (β (β h)) = h := by
  have := congrArg (fun f : MulAut H => f h) h3
  simpa [pow_succ] using this

@[expose] def restrAut {H : Type} [Group H] (β : MulAut H) (L : Subgroup H) (h3 : β ^ 3 = 1)
    (hm : ∀ x ∈ L, β x ∈ L) : MulAut ↥L where
  toFun l := ⟨β l.1, hm l.1 l.2⟩
  invFun l := ⟨β (β l.1), hm _ (hm _ l.2)⟩
  left_inv l := Subtype.ext (aut_cube_apply h3 (l : H))
  right_inv l := Subtype.ext (aut_cube_apply h3 (l : H))
  map_mul' a b := Subtype.ext (map_mul β (a : H) (b : H))

theorem exists_invariant_sylow3 {L : Type} [Group L] [Finite L] (x : MulAut L) (hx : x ^ 3 = 1) :
    ∃ P : Sylow 3 L, ∀ s ∈ (P : Subgroup L), x s ∈ (P : Subgroup L) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hord : orderOf x ∣ 3 ^ 1 := by simpa using orderOf_dvd_of_pow_eq_one hx
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hord
  have hp : IsPGroup 3 (Subgroup.zpowers x) :=
    IsPGroup.of_card (n := k) (by rw [Nat.card_zpowers, hk])
  haveI : Finite (Sylow 3 L) := inferInstance
  have h1 := hp.card_modEq_card_fixedPoints (Sylow 3 L)
  have h2 := card_sylow_modEq_one 3 L
  have h3 : Nat.card (fixedPoints (Subgroup.zpowers x) (Sylow 3 L)) ≡ 1 [MOD 3] :=
    h1.symm.trans h2
  have hne : (fixedPoints (Subgroup.zpowers x) (Sylow 3 L)).Nonempty := by
    by_contra hemp
    rw [Set.not_nonempty_iff_eq_empty] at hemp
    rw [hemp] at h3
    exact absurd h3 (by simp [Nat.ModEq])
  obtain ⟨P, hP⟩ := hne
  refine ⟨P, fun s hs => ?_⟩
  have h4 := hP ⟨x, Subgroup.mem_zpowers x⟩
  have h5 : x • (P : Subgroup L) = (P : Subgroup L) := congrArg Sylow.toSubgroup h4
  have h6 : x s ∈ x • (P : Subgroup L) := Subgroup.smul_mem_pointwise_smul s x _ hs
  rwa [h5] at h6

end CFSG.RankThree.PartTwo.Sec21.FF79
