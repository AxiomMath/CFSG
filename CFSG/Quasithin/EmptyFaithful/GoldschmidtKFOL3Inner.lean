module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtKFOL3Model

public section

namespace CFSG.Quasithin.SBd19F

open CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.RankThree.SubgroupLists

theorem no_mul_sq_sub_one_eq_168 {p : ℕ} (h : p * (p ^ 2 - 1) = 168) : False := by
  have h2 : p ≤ 6 := by
    by_contra hlt
    push Not at hlt
    have : 7 * (7 ^ 2 - 1) ≤ p * (p ^ 2 - 1) := Nat.mul_le_mul hlt
      (Nat.sub_le_sub_right (Nat.pow_le_pow_left hlt 2) 1)
    omega
  interval_cases p <;> omega

theorem false_of_perfect_card_168_centralizer {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) {g : projectiveSL 3 (ZMod p)} (hg2 : g ^ 2 = 1) (hg1 : g ≠ 1)
    {K : Subgroup (projectiveSL 3 (ZMod p))} [Group.IsPerfect K] (hcard : Nat.card K = 168)
    (hK : ∀ x ∈ K, x * g = g * x) : False := by
  obtain ⟨H, hdet, hZ, ⟨τ⟩⟩ := exists_equiv_quotient_center p
  have hLp : Group.IsPerfect (K.map τ.toMonoidHom) := Group.IsPerfect.map _
  have hLcard : Nat.card (K.map τ.toMonoidHom) = 168 := by
    rw [← hcard]
    exact Nat.card_congr (K.equivMapOfInjective τ.toMonoidHom τ.injective).toEquiv.symm
  have hL0 : K.map τ.toMonoidHom ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hLcard
    omega
  have hLt : ∀ x ∈ K.map τ.toMonoidHom, x * τ g = τ g * x := by
    rintro _ ⟨y, hy, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, ← map_mul, hK y hy]
  have h := card_perfect_of_le_centralizer hp2 hdet hZ (t := τ g)
    (by rw [← map_pow, hg2, map_one]) (fun h => hg1 (τ.injective (by rw [h, map_one])))
    (K.map τ.toMonoidHom) hL0 hLt
  rw [hLcard] at h
  rcases h with h | h | h
  · omega
  · omega
  · exact no_mul_sq_sub_one_eq_168 h.symm

end CFSG.Quasithin.SBd19F
