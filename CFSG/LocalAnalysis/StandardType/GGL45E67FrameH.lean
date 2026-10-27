module

public import CFSG.LocalAnalysis.StandardType.GGL45E67Frame
public import CFSG.LocalAnalysis.StandardType.GGL45NtDefs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem ggL45TorusH123_of_hOne_of_frame {R : Type} [Group R] (D : E6ThreeModel.FrameData R)
    (hD : D.Good) {I : Set (MulAut R)} (hI : ∃ J : Subgroup (MulAut R), (J : Set (MulAut R)) = I)
    (hTI : ∀ t ∈ D.Tor, MulAut.conj t ∈ I)
    {K : Type} [Group K] [Finite K] (θ : K ⧸ Subgroup.center K ≃* R) (hK : commutator K = ⊤)
    (hZ : Nat.card (Subgroup.center K) ∣ 3) {ψ : MulAut K} (hψ : ψ ^ 3 = 1)
    {E : Subgroup (MulAut K)} (hE : IsElemAbelian 3 E) (hEI : ∀ e ∈ E, GGL45InducesIn θ I e)
    (hC : ∀ u ∈ I, (∀ e ∈ E, u * ggInducedAut θ e = ggInducedAut θ e * u) → ∀ t ∈ D.Tor, u t = t)
    (h3' : ∀ u ∈ I, (∀ e ∈ E, u * ggInducedAut θ e = ggInducedAut θ e * u) →
      Nat.Coprime 3 (orderOf u) → ∃ t ∈ D.Tor, u = MulAut.conj t)
    (hCR : ∀ r : R, (∀ e ∈ E, ggInducedAut θ e r = r) → r ∈ D.Tor)
    {s : ℕ} (hs : 2 ≤ s) {c : ℤ} {k : ℕ} (hk : ¬ 3 ∣ k)
    (hc : c ≡ 1 + 3 ^ (s - 1) * k [ZMOD 3 ^ s]) (hH1 : GGL45HOne 3 I θ E (ggInducedAut θ ψ) s c)
    (hH3 : ∃ t₁ ∈ D.Tor, ∃ t₂ ∈ D.Tor, t₁ ^ 3 ^ s = 1 ∧ t₂ ^ 3 ^ s = 1 ∧
      ∀ i j : ℕ, (t₁ ^ 3 ^ (s - 1)) ^ i * (t₂ ^ 3 ^ (s - 1)) ^ j = 1 → 3 ∣ i ∧ 3 ∣ j) :
    GGL45TorusH123 3 I θ ψ E := by
  have hc1 : c ≡ 1 [ZMOD 3] := by
    have hs1 : 1 ≤ s := by omega
    have hs2 : 1 ≤ s - 1 := by omega
    have h3s : (3 : ℤ) ∣ 3 ^ s := by simpa using pow_dvd_pow (3 : ℤ) hs1
    have hdiv : (3 : ℤ) ∣ 3 ^ (s - 1) * (k : ℤ) := by
      have h : (3 : ℤ) ∣ 3 ^ (s - 1) := by simpa using pow_dvd_pow (3 : ℤ) hs2
      exact h.mul_right (k : ℤ)
    refine (Int.ModEq.of_dvd h3s hc).trans ?_
    rw [Int.modEq_iff_dvd]
    have h1 : (1 : ℤ) - (1 + 3 ^ (s - 1) * (k : ℤ)) = -(3 ^ (s - 1) * (k : ℤ)) := by ring
    rw [h1]
    exact dvd_neg.mpr hdiv
  have hpair := ggL45HTwo_HThree_of_frame D hD hI hTI θ hK hZ ψ hψ E hE hEI hC h3' hCR hc1 hH1 hH3
  have hcast : (((3 : ℕ) : ℤ)) = 3 := by norm_num
  refine ⟨s, hs, c, k, hk, ?_, hH1, hpair.1, hpair.2⟩
  simpa only [hcast] using hc

end CFSG.StandardType
