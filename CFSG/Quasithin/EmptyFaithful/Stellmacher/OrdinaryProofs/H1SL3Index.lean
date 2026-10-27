module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.OrdinaryProofs.H1SL3Avg

public section

namespace CFSG.Quasithin.EmptyFaithful.Stellmacher.OrdinaryProofs.H1SL3

variable {G : Type*} [Group G] {M : Type*} [AddCommGroup M] [Module (ZMod 2) M]

theorem crossedHom_principal_of_odd_index [Finite G] (H : Subgroup G)
    (hodd : Odd (Nat.card (G ⧸ H)))
    (act : G →* AddMonoid.End M)
    (f : G → M) (hf : ∀ g h, f (g * h) = f g + act g (f h))
    (hH : ∀ k ∈ H, f k = 0) :
    ∃ w : M, ∀ g : G, f g = w - act g w := by
  classical
  have : Fintype G := Fintype.ofFinite G
  have : Fintype (G ⧸ H) := Fintype.ofFinite (G ⧸ H)
  have hodd' : Odd (Fintype.card (G ⧸ H)) := by
    rwa [← Nat.card_eq_fintype_card]
  have hcoset : ∀ a k : G, k ∈ H → f (a * k) = f a := by
    intro a k hk
    rw [hf, hH k hk, map_zero, add_zero]
  have hrep : ∀ (h : G) (q : G ⧸ H),
      f (Quotient.out (h • q)) = f h + act h (f (Quotient.out q)) := by
    intro h q
    obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul H (h * Quotient.out q)
    have hq : h • q = (QuotientGroup.mk (h * Quotient.out q) : G ⧸ H) := by
      conv_lhs => rw [← Quotient.out_eq q]
      rfl
    rw [hq, hk, hcoset _ _ k.2, hf]
  set S : M := ∑ q : G ⧸ H, f (Quotient.out q) with hS
  have hsum : ∀ h : G, S = Fintype.card (G ⧸ H) • f h + act h S := by
    intro h
    have h1 : ∑ q : G ⧸ H, f (Quotient.out (h • q)) = S := by
      simpa only [MulAction.toPerm_apply] using
        Equiv.sum_comp (MulAction.toPerm h) (fun q : G ⧸ H => f (Quotient.out q))
    have h2 : ∑ q : G ⧸ H, f (Quotient.out (h • q)) =
        ∑ q : G ⧸ H, (f h + act h (f (Quotient.out q))) :=
      Finset.sum_congr rfl (fun q _ => hrep h q)
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, ← map_sum] at h2
    rw [h1] at h2
    exact h2
  refine ⟨S, fun g => ?_⟩
  have h3 := eq_sub_of_add_eq (hsum g).symm
  rw [odd_nsmul_eq_self hodd'] at h3
  exact h3

end CFSG.Quasithin.EmptyFaithful.Stellmacher.OrdinaryProofs.H1SL3
