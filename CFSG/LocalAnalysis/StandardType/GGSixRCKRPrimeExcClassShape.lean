module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeExcRelOneAt
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeExcClassHalf
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeExcClassLagr
import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeExcOrbit

public section

namespace CFSG.StandardType.RCKRP

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.LieType.SeitzGeneration CFSG.StandardType.ExcMaxToral CFSG.RankThree.E6
  CFSG.StandardType CFSG.StandardType.GGFinModel
open CFSG.Open (StatedLieTag IsElemAbelian)
open scoped Matrix

theorem rck_dvd_of_orderOf_one {p f : ℕ} (h : orderOf ((2 ^ f : ℕ) : ZMod p) = 1) :
    p ∣ 2 ^ f - 1 := by
  have h1 : ((2 ^ f : ℕ) : ZMod p) = 1 := orderOf_eq_one_iff.1 h
  have hpos : 1 ≤ 2 ^ f := Nat.one_le_two_pow
  have h0 : ((2 ^ f - 1 : ℕ) : ZMod p) = 0 := by
    rw [Nat.cast_sub hpos, h1, Nat.cast_one, sub_self]
  exact (ZMod.natCast_eq_zero_iff _ _).1 h0

theorem rck_cast_eq_neg_one {p f : ℕ} (hp : p.Prime) (h : orderOf ((2 ^ f : ℕ) : ZMod p) = 2) :
    ((2 ^ f : ℕ) : ZMod p) = -1 := by
  have h0 : ((2 ^ f + 1 : ℕ) : ZMod p) = 0 :=
    (ZMod.natCast_eq_zero_iff _ _).2 (rck_dvd_of_orderOf_two hp h)
  rw [Nat.cast_add, Nat.cast_one] at h0
  exact eq_neg_of_add_eq_zero_left h0

theorem rckExcClassShape_of_weyl
    {τ : Tag} (hτ : τ = .F4 ∨ τ = .E7 ∨ τ = .E8) {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {ρ : Equiv.Perm (Fin τ.rank → ℤ)} {w : WeylGroup τ}
    (hw : ∀ γ, IsRoot τ γ → ρ γ = w • γ) {N : ℕ}
    (hN : N ≤ Nat.card {z : Fin τ.rank → ZMod p //
      (modMat p (weylMatrix w))ᵀ *ᵥ z = ((2 ^ f : ℕ) : ZMod p) • z})
    (h1 : orderOf ((2 ^ f : ℕ) : ZMod p) = 1 → p ^ τ.rank ≤ N)
    (h2 : orderOf ((2 ^ f : ℕ) : ZMod p) = 2 → p ^ (τ.rank - 1) ≤ N)
    (hF4 : τ = .F4 → p ^ τ.rank ≤ N) (h4 : p ^ 4 ≤ N)
    (hdeg : 4 ≤ excDegCount τ (orderOf ((2 ^ f : ℕ) : ZMod p))) :
    RCKExcClassShape τ (orderOf ((2 ^ f : ℕ) : ZMod p)) ρ := by
  refine ⟨fun hd1 γ hγ => ?_, fun hd2 => ?_, fun ⟨hE8, hd⟩ γ hγ => ?_, fun hd1 hd2 => ?_⟩
  · have hq1 : ((2 ^ f : ℕ) : ZMod p) = 1 := orderOf_eq_one_iff.1 hd1
    have hc : p ^ τ.rank ≤ Nat.card {z : Fin τ.rank → ZMod p //
        (modMat p (weylMatrix w))ᵀ *ᵥ z = ((1 : ℤ) : ZMod p) • z} := by
      have := (h1 hd1).trans hN
      simpa [hq1] using this
    have htop := weyl_eq_sign_of_eigenspace_top hp hp2 w (ε := 1) (Or.inl rfl) hc
    rw [hw γ hγ, htop γ, one_smul]
  · have hqm : ((2 ^ f : ℕ) : ZMod p) = -1 := rck_cast_eq_neg_one hp hd2
    rcases hτ with hF | h78
    · left
      intro γ hγ
      have hc : p ^ τ.rank ≤ Nat.card {z : Fin τ.rank → ZMod p //
          (modMat p (weylMatrix w))ᵀ *ᵥ z = ((-1 : ℤ) : ZMod p) • z} := by
        have := (hF4 hF).trans hN
        simpa [hqm] using this
      have htop := weyl_eq_sign_of_eigenspace_top hp hp2 w (ε := -1) (Or.inr rfl) hc
      rw [hw γ hγ, htop γ]
      simp
    · have hc : p ^ (τ.rank - 1) ≤ Nat.card {z : Fin τ.rank → ZMod p //
          (modMat p (weylMatrix w))ᵀ *ᵥ z = (-1 : ZMod p) • z} := by
        have := (h2 hd2).trans hN
        simpa [hqm] using this
      rcases rckExc_weyl_half_class h78 hp hp2 w hc with hneg | ⟨β, hβ, hβw⟩
      · left
        intro γ hγ
        rw [hw γ hγ, hneg γ]
      · right
        refine ⟨β, hβ, fun γ hγ => ?_⟩
        rw [hw γ hγ, hβw γ]
  · subst hE8
    have hlag := rckExc_weyl_lagrangian hp hp2 w (orderOf ((2 ^ f : ℕ) : ZMod p)) hd _ rfl
      (h4.trans hN)
    have h1 : ρ γ = w • γ := hw γ hγ
    have h2 : ρ (ρ γ) = w • (w • γ) := by
      rw [hw (ρ γ) (h1 ▸ IsRoot.smul hγ w), h1]
    rw [h2, h1]
    exact hlag γ
  · rcases excDegCount_ge_four hdeg with ⟨-, hd12, -⟩ | ⟨hτ8, hd346, -⟩
    · rcases hd12 with h | h
      · exact absurd h hd1
      · exact absurd h hd2
    · exact ⟨hτ8, hd346⟩

end CFSG.StandardType.RCKRP
