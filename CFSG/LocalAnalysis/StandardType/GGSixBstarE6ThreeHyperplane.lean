module

public import CFSG.LocalAnalysis.StandardType.GGSixBstarE6ThreeDiag

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.CentralCover
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

namespace NoOffE6Three

section Hyperplane

variable {K : Type} [Field K]

theorem diag3_ofAdd_add (ζ : Kˣ) (hζ : ζ ^ 3 = 1) (x y : Fin Tag.E6.rank → ZMod 3) :
    diag3 (K := K) ζ hζ (Multiplicative.ofAdd (x + y)) =
      diag3 ζ hζ (Multiplicative.ofAdd x) * diag3 ζ hζ (Multiplicative.ofAdd y) := by
  rw [ofAdd_add, map_mul]

theorem diag3_ofAdd_nsmul (ζ : Kˣ) (hζ : ζ ^ 3 = 1) (n : ℕ) (x : Fin Tag.E6.rank → ZMod 3) :
    diag3 (K := K) ζ hζ (Multiplicative.ofAdd (n • x)) =
      diag3 ζ hζ (Multiplicative.ofAdd x) ^ n := by
  rw [ofAdd_nsmul, map_pow]

theorem mem_hypE6_of_diag3_mem_innerAut (ζ : Kˣ) (hζ : ζ ^ 3 = 1)
    (hnot : ¬ vAd (K := K) ζ hζ ≤
      (MulAut.conj : adjointGroup .E6 K →* MulAut (adjointGroup .E6 K)).range)
    {x : Fin Tag.E6.rank → ZMod 3}
    (hx : diag3 ζ hζ (Multiplicative.ofAdd x) ∈
      (MulAut.conj : adjointGroup .E6 K →* MulAut (adjointGroup .E6 K)).range) :
    x ∈ NoOffRest.hypE6 := by
  by_contra hxh
  apply hnot
  rintro _ ⟨y, rfl⟩
  have hm : NoOffRest.kDotP 3 x ≠ 0 := hxh
  obtain ⟨c, hc⟩ : ∃ c : ZMod 3, c * NoOffRest.kDotP 3 x = NoOffRest.kDotP 3 (Multiplicative.toAdd y) := by
    have key : ∀ m t : ZMod 3, m ≠ 0 → ∃ c : ZMod 3, c * m = t := by decide
    exact key _ _ hm
  have hyc : Multiplicative.toAdd y - c • x ∈ NoOffRest.hypE6 := by
    rw [NoOffRest.mem_hypE6, NoOffRest.kDotP_sub, NoOffRest.kDotP_smul, hc, sub_self]
  have h1 := diag3_mem_innerAut_of_mem_hyp (K := K) ζ hζ hyc
  have h2 : diag3 (K := K) ζ hζ (Multiplicative.ofAdd (c • x)) ∈
      (MulAut.conj : adjointGroup .E6 K →* MulAut (adjointGroup .E6 K)).range := by
    have e : c • x = c.val • x := by
      rw [← ZMod.natCast_zmod_val c, Nat.cast_smul_eq_nsmul]
      simp
    rw [e, diag3_ofAdd_nsmul]
    exact Subgroup.pow_mem _ hx _
  have h3 := mul_mem h1 h2
  rw [← diag3_ofAdd_add, sub_add_cancel] at h3
  exact h3

end Hyperplane

end NoOffE6Three

end CFSG.StandardType
