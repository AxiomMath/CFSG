module

public import CFSG.RankThree.PartTwo.Census.TripleCoverLift
public import CFSG.RankThree.PartOne.K159.CoverLift

public section

namespace CFSG.RankThree.PartOne.N143

open CFSG.RankThree.PartTwo.Sec4.Census
open CFSG.Assembly.RankThreeEven (localRank)

theorem succ_le_localRank_of_torus {G X : Type} [Group G] [Finite G] [Group X] {φ : G →* X}
    (hφ : Function.Surjective φ) (hker : φ.ker ≤ Subgroup.center G) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hpk : p ∣ Nat.card φ.ker) {r : ℕ}
    (θ : Multiplicative (Fin r → ZMod p) →* X) (hθ : Function.Injective θ)
    (hswap : ∀ j k : Fin r, j ≠ k → ∃ w : X,
      w * θ (.ofAdd (Pi.single j 1)) * w⁻¹ = θ (.ofAdd (Pi.single k 1)) ∧
        w * θ (.ofAdd (Pi.single k 1)) * w⁻¹ = θ (.ofAdd (Pi.single j 1)))
    (hinv : ∀ j : Fin r, ∃ w : X,
      w * θ (.ofAdd (Pi.single j 1)) * w⁻¹ = (θ (.ofAdd (Pi.single j 1)))⁻¹)
    {t : X} (ht1 : t ≠ 1) (ht2 : t ^ 2 = 1) (htE : ∀ a, Commute t (θ a)) :
    r + 1 ≤ localRank p G := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : NeZero p := ⟨hp.ne_zero⟩
  have hodd : Odd p := hp.odd_of_ne_two hp2
  set g : Fin r → X := fun j => θ (.ofAdd (Pi.single j 1)) with hg
  set S : Set X := Set.range g with hSdef
  have hclosure : Subgroup.closure S = θ.range := by
    have h1 : (Subgroup.closure (Set.range fun j : Fin r =>
        (Multiplicative.ofAdd (Pi.single j (1 : ZMod p)) :
          Multiplicative (Fin r → ZMod p)))).map θ = Subgroup.closure S := by
      rw [MonoidHom.map_closure, hSdef, ← Set.range_comp]
      rfl
    rw [← h1, CFSG.RankThree.PartOne.K159.closure_range_ofAdd_single, ← MonoidHom.range_eq_map]
  have hgp : ∀ j, g j ^ p = 1 := by
    intro j
    rw [hg]
    simp only
    rw [← map_pow]
    have : (Multiplicative.ofAdd (Pi.single j (1 : ZMod p)) : Multiplicative (Fin r → ZMod p)) ^ p
        = 1 := by
      apply Multiplicative.toAdd.injective
      funext i
      rw [toAdd_pow, toAdd_one, Pi.smul_apply, nsmul_eq_mul, ZMod.natCast_self, zero_mul,
        Pi.zero_apply]
    rw [this, map_one]
  have hcommg : ∀ j k, Commute (g j) (g k) := fun j k => (Commute.all _ _).map θ
  have hS : ∀ x y : G, φ x ∈ S → φ y ∈ S → φ x ≠ φ y → x * y = y * x := by
    rintro x y ⟨j, hj⟩ ⟨k, hk⟩ hne
    have hjk : j ≠ k := fun h => hne (by rw [← hj, ← hk, h])
    obtain ⟨w, hw1, hw2⟩ := hswap j k hjk
    exact TripleCoverLift.commute_of_conj hφ hker hodd (x := x) (y := y)
      (by rw [← hj, ← hk]; exact hcommg j k) (by rw [← hk]; exact hgp k) (n := w)
      (Or.inr ⟨by rw [← hj, ← hk]; exact hw1, by rw [← hj, ← hk]; exact hw2⟩)
  have hcomm : ∀ x ∈ θ.range.comap φ, ∀ y ∈ θ.range.comap φ, x * y = y * x := fun x hx y hy =>
    TripleCoverLift.commute_of_mem_closure hφ hker hS (x := x) (y := y) (by rw [hclosure]; exact hx)
      (by rw [hclosure]; exact hy)
  have hSE : S ⊆ (θ.range : Set X) := by
    rintro _ ⟨j, rfl⟩
    exact ⟨_, rfl⟩
  have hgen : ∀ s ∈ S, ∃ y : G, φ y = s ∧ y ^ p = 1 := by
    rintro _ ⟨j, rfl⟩
    obtain ⟨w, hw⟩ := hinv j
    exact TripleCoverLift.exists_lift_pow_eq_one_of_conj_eq_inv hφ hker hodd (hgp j) hw
  have hlift : ∀ e ∈ θ.range, ∃ y : G, φ y = e ∧ y ^ p = 1 := fun e he =>
    TripleCoverLift.exists_lift_pow_eq_one_of_mem_closure hcomm hSE hgen (by rw [hclosure]; exact he)
  have hcard : p ^ r ≤ Nat.card θ.range := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hθ).toEquiv, Nat.card_congr Multiplicative.toAdd,
      Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card, Fintype.card_fin]
  exact TripleCoverLift.succ_le_localRank_of_lift hφ hker hp hp2 hpk hcomm hlift ht1 ht2
    (fun e he => by obtain ⟨a, rfl⟩ := he; exact htE a) hcard

end CFSG.RankThree.PartOne.N143
