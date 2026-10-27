module

public import CFSG.LocalAnalysis.StandardType.GGHdRo7DSmallDefs
import CFSG.LocalAnalysis.StandardType.GGHdRo7DSmallBasic
import CFSG.LocalAnalysis.StandardType.GGHdRo7DSmallClassAux

public section

namespace CFSG.StandardType.HdRo7D.Small

open CFSG.StandardType.HdRo7C CFSG.StandardType.HdRo7SU

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private lemma hdRo7DSmRulesAux_dIsD_neg {n : ℕ} {h : DV n} : dIsD (-h) ↔ dIsD h := by
  unfold dIsD
  constructor
  · rintro ⟨i, j, hij, hi, hj, hk⟩
    exact ⟨i, j, hij, by simpa using hi, by simpa using hj,
      fun k hki hkj => by simpa using hk k hki hkj⟩
  · rintro ⟨i, j, hij, hi, hj, hk⟩
    exact ⟨i, j, hij, by simpa using hi, by simpa using hj,
      fun k hki hkj => by simpa using hk k hki hkj⟩

private lemma hdRo7DSmRulesAux_dIsO_neg {n : ℕ} {h : DV n} : dIsO (-h) ↔ dIsO h := by
  unfold dIsO
  constructor
  · rintro ⟨i, hi, hk⟩
    exact ⟨i, by simpa using hi, fun k hki => by simpa using hk k hki⟩
  · rintro ⟨i, hi, hk⟩
    exact ⟨i, by simpa using hi, fun k hki => by simpa using hk k hki⟩

private lemma hdRo7DSmRulesAux_dE_zero {n : ℕ} : (dE n 0) 0 = 1 := by
  simp [dE]

theorem dSmRules_of_leaves : DSmNormLeaf → DSmCommonLeaf → DSmExistLeaf → (DNormalizerLeaf →
    DReflFixLeaf → ∀ (n : ℕ) (H A : Subgroup (DGL n)), DLinData 3 n (DV n) (dStd n) H A → (∃ r ∈ H,
    GGLinRefl r ∧ ¬ ggLinMove r ≤ LinearMap.ker ((dStd n).coord 0)) → ∃ ρ : ZMod 3, ρ ≠ 0 ∧ (∀ r ∈
    H, GGLinRefl r → ∃ h, DRefl ρ r h) ∧ DRCl ρ (dRoots ρ H)) := by
  intro hN hC hE hNorm hFix n H A hD hext
  obtain ⟨r₁, hr₁H, ρ, hρ, h₁, h₁0, h₁supp, hr₁⟩ := hE hN hNorm hFix n H A hD hext
  have horth : ∀ r ∈ H, GGLinRefl r → ∃ h, DRefl ρ r h := by
    intro r hrH hrRefl
    rcases hN hNorm hFix n H A hD r hrH hrRefl with
      ⟨h, _h0, _hshape, hrefl⟩ | haxis | ⟨ρ', hρ', h, h0, hsupp, hrefl⟩
    · exact ⟨h, hrefl ρ hρ⟩
    · exact ⟨dE n 0, haxis ρ hρ⟩
    · have h0ne : h 0 ≠ 0 := by rw [h0]; decide
      have hρeq : ρ' = ρ :=
        hC n H A hD ρ' ρ r r₁ h h₁ hrH hr₁H hρ' hρ h0ne (by rw [h₁0]; decide) hsupp h₁supp
          hrefl hr₁
      exact ⟨h, hρeq ▸ hrefl⟩
  refine ⟨ρ, hρ, horth, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro h ⟨r, _hrH, hr⟩
    exact hr.1
  · rintro h ⟨r, hrH, hr⟩
    exact ⟨r, hrH, dRefl_neg_iff.mpr hr⟩
  · rintro h ⟨r, hrH, hr⟩ g ⟨s, hsH, hs⟩
    exact ⟨r * s * r⁻¹, H.mul_mem (H.mul_mem hrH hsH) (H.inv_mem hrH), dRefl_conj hr hs⟩
  · rintro h ⟨r, hrH, hr⟩ σ c hd
    have haH : dActL σ c hd.2.2.1 ∈ H := hD.hPH _ (dsp_dActL hd)
    exact ⟨dActL σ c hd.2.2.1 * r * (dActL σ c hd.2.2.1)⁻¹,
      H.mul_mem (H.mul_mem haH hrH) (H.inv_mem haH), dRefl_conj_dActL hd.1 hd.2.2.1 hr⟩
  · intro h h0 hDshape
    have hsupp : dSupp h = 2 := by
      rcases (dIsD_iff h).mp hDshape with ⟨_, hs⟩ | ⟨hne, _⟩
      · exact hs
      · exact absurd h0 hne
    have hb : dB ρ h h ≠ 0 := by
      rw [dB_self_of_eq ρ h0, hsupp]
      decide
    obtain ⟨r, hr⟩ := exists_dRefl hb
    exact ⟨r, hD.hPH r (dsp_of_dRefl_int hr h0 hDshape), hr⟩
  · rintro h ⟨r, hrH, hr⟩ h0
    have hrRefl : GGLinRefl r := ggLinRefl_of_dRefl hr
    rcases hN hNorm hFix n H A hD r hrH hrRefl with
      ⟨h', _h'0, h'shape, hrefl⟩ | haxis | ⟨ρ', _hρ', h', h'0, _hsupp, hrefl⟩
    · rcases dRefl_root_unique hr (hrefl ρ hρ) with h'eq | h'eq
      · rw [h'eq] at h'shape
        exact h'shape
      · rw [h'eq] at h'shape
        rcases h'shape with hD' | hO'
        · exact Or.inl (hdRo7DSmRulesAux_dIsD_neg.mp hD')
        · exact Or.inr (hdRo7DSmRulesAux_dIsO_neg.mp hO')
    · have hDrefl : DRefl ρ r (dE n 0) := haxis ρ hρ
      rcases dRefl_root_unique hr hDrefl with h'eq | h'eq
      · have h1 : (1 : ZMod 3) = 0 := by
          rw [← h'eq] at h0
          rw [hdRo7DSmRulesAux_dE_zero] at h0
          exact h0
        exact absurd h1 (by decide)
      · have h1 : (1 : ZMod 3) = 0 := by
          have hc := congrArg (fun x : DV n => x 0) h'eq
          simp only [dE, Pi.single_eq_same, Pi.neg_apply] at hc
          rwa [h0, neg_zero] at hc
        exact absurd h1 (by decide)
    · rcases dRefl_root_unique hr hrefl with h'eq | h'eq
      · have h1 : (0 : ZMod 3) = 1 := by
          rw [← h'eq] at h0
          rw [h0] at h'0
          exact h'0
        exact absurd h1 (by decide)
      · have h1 : (1 : ZMod 3) = 0 := by
          have hc := congrArg (fun x : DV n => x 0) h'eq
          simp only [Pi.neg_apply] at hc
          rw [h'0, h0, neg_zero] at hc
          exact hc
        exact absurd h1 (by decide)
  · exact ⟨h₁, ⟨r₁, hr₁H, hr₁⟩, by rw [h₁0]; decide, h₁supp⟩

end CFSG.StandardType.HdRo7D.Small
