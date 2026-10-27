module

public import CFSG.Quasithin.EmptyFaithful.S151cOne
public import CFSG.Quasithin.EmptyFaithful.S151cOm4
public import CFSG.Quasithin.EmptyFaithful.S151cCases

public section

namespace CFSG.Quasithin

open CFSG.Open

section ShapeOmega151c

variable {V : Type} [CommGroup V] [Finite V] {X Tb Xc J : Subgroup (MulAut V)} {r : ℚ}

theorem shape_Omega (B : OneBlock151c X Tb Xc J r) (hΩ : IsOmegaFourPlus J) (hr : r = 3 / 2)
    (hrk : rk V = 4) : ACase3 X J := by
  have hcard : Nat.card V = 16 := by
    rw [card_eq_two_pow_rk B.sq, hrk]
    norm_num
  have hXJ : X = J := by
    by_contra hne
    obtain ⟨τ, hτX, hτ1, hτ2, hτrk⟩ := exists_transvection_of_ne hΩ B.le B.normalizes
      (fun e => hne e.symm)
    have hmem := zpowers_mem_kRle_three B.sq hτX hτ1 hτ2
      (by rw [hτrk]; norm_num : (rk (commV (Subgroup.zpowers τ)) : ℚ) ≤ 1)
    have hA2 : IsA2 X (Subgroup.zpowers τ) := hmem.1.1
    have hrA : rAV (Subgroup.zpowers τ) ≤ 1 := hmem.1.2
    have hq := (kq_eq_coe_iff.mp B.qhat).2 (Subgroup.zpowers τ) hA2 hmem.2
    rw [hr] at hq
    have : (3 / 2 : ℚ) ≤ 1 := hq.trans hrA
    norm_num at this
  exact ⟨hcard, hXJ, hXJ ▸ hΩ⟩

end ShapeOmega151c

end CFSG.Quasithin
