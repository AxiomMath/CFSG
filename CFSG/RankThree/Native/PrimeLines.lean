module

public import CFSG.Certificates.PrimeCyclicRepresentatives

public section

namespace CFSG.RankThree.Native

open CFSG.Certificates.PrimeCyclicRepresentatives

variable {G : Type*} [Group G]

theorem prime_subgroups_eq_range {p : ℕ} [hp : Fact p.Prime] {Q : Subgroup G} {r : ℕ}
    (xs : Fin r → G) (hxsQ : ∀ j, xs j ∈ Q) (hxs1 : ∀ j, xs j ≠ 1) (hxsp : ∀ j, xs j ^ p = 1)
    (hcover : ∀ g ∈ Q, g ≠ 1 → ∃ j, ∃ k : ℕ, g = xs j ^ k)
    (hdist : ∀ j j', ∀ k < p, xs j = xs j' ^ k → j = j') :
    {H : Subgroup G | H ≤ Q ∧ Nat.card H = p} = Set.range (fun j => Subgroup.zpowers (xs j)) ∧
      Function.Injective (fun j => Subgroup.zpowers (xs j)) := by
  have horder : ∀ j, orderOf (xs j) = p := fun j => orderOf_eq_prime (hxsp j) (hxs1 j)
  have hcardj : ∀ j, Nat.card (Subgroup.zpowers (xs j)) = p := fun j => by
    rw [Nat.card_zpowers, horder j]
  refine ⟨Set.ext fun H => ⟨?_, ?_⟩, ?_⟩
  · rintro ⟨hHQ, hH⟩
    have : Finite H := Nat.finite_of_card_ne_zero (by rw [hH]; exact hp.out.ne_zero)
    have : Nontrivial H :=
      Finite.one_lt_card_iff_nontrivial.mp (by rw [hH]; exact hp.out.one_lt)
    obtain ⟨h, hh1⟩ := exists_ne (1 : H)
    have hh1' : (h : G) ≠ 1 := fun e => hh1 (Subtype.ext e)
    obtain ⟨j, k, hk⟩ := hcover h (hHQ h.2) hh1'
    obtain ⟨-, hzp⟩ := orderOf_and_zpowers_eq_of_mem_prime_subgroup p hp.out H hH h.2 hh1'
    refine ⟨j, ?_⟩
    show Subgroup.zpowers (xs j) = H
    have : Finite (Subgroup.zpowers (xs j)) :=
      Nat.finite_of_card_ne_zero (by rw [hcardj]; exact hp.out.ne_zero)
    rw [← hzp]
    symm
    apply Subgroup.eq_of_le_of_card_ge
    · rw [Subgroup.zpowers_le, hk]
      exact Subgroup.npow_mem_zpowers _ _
    · rw [hcardj, hzp, hH]
  · rintro ⟨j, rfl⟩
    exact ⟨(Subgroup.zpowers_le).2 (hxsQ j), hcardj j⟩
  · intro j j' hjj'
    have hmem : xs j ∈ Subgroup.zpowers (xs j') := by
      rw [← show Subgroup.zpowers (xs j) = Subgroup.zpowers (xs j') from hjj']
      exact Subgroup.mem_zpowers _
    have hfin : IsOfFinOrder (xs j') := orderOf_pos_iff.mp (by rw [horder]; exact hp.out.pos)
    classical
    obtain ⟨k, hk, he⟩ := Finset.mem_image.mp (hfin.mem_zpowers_iff_mem_range_orderOf.mp hmem)
    rw [Finset.mem_range, horder] at hk
    exact hdist j j' k hk he.symm

end CFSG.RankThree.Native
