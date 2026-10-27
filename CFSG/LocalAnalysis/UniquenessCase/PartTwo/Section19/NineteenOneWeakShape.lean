module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenNineBTrans
public import CFSG.GroupTheory.FixedPointFreeFiveTwist
public import CFSG.GroupTheory.CommVFixOrderTwentyFive
public import CFSG.RankThree.PartTwo.Sec15.F153A10KWit
public import CFSG.GH74.Generic.S45.LEvSporGen
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19

open CFSG.Quasithin
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase
open CFSG.GH74.Generic.S45 (a5_eq_one_of_forall_comm a5_exists_five)

variable {W : Type} [CommGroup W]

@[expose] def Shape19_1W (X Lb Kb : Subgroup (MulAut W)) : Prop :=
  Lb ≤ X ∧ Kb ≤ X ∧ IsAlt ↥Lb 5 ∧ IsAlt ↥Kb 5 ∧
    (∀ x ∈ Lb, ∀ y ∈ Kb, x * y = y * x) ∧
  (∀ φ ∈ X,
      ((∀ x ∈ Lb, φ * x * φ⁻¹ ∈ Lb) ∧ (∀ x ∈ Kb, φ * x * φ⁻¹ ∈ Kb)) ∨
      ((∀ x ∈ Lb, φ * x * φ⁻¹ ∈ Kb) ∧ (∀ x ∈ Kb, φ * x * φ⁻¹ ∈ Lb))) ∧
  16 ≤ rk W ∧
  (∃ f ∈ X, orderOf f = 5 ∧ fixV (Subgroup.zpowers f) = ⊥ ∧
    (∀ φ ∈ X, φ * f * φ⁻¹ ∈ Subgroup.zpowers f) ∧
    ∀ x ∈ Lb ⊔ Kb, x * f = f * x) ∧
  (∀ φ ∈ X, rkIdx (fixV (Subgroup.zpowers φ)) ≤ 7 →
    (∀ x ∈ Lb, φ * x * φ⁻¹ ∈ Lb) → (∀ x ∈ Kb, φ * x * φ⁻¹ ∈ Kb) →
    (∀ x ∈ Lb, φ * x = x * φ) ∨ (∀ x ∈ Kb, φ * x = x * φ))

theorem invFix_of_shape_W [Finite W] (hW : ∀ w : W, w ^ 2 = 1)
    {X Lb Kb : Subgroup (MulAut W)} (hsh : Shape19_1W X Lb Kb) :
    s16n9bInvFix X 5 7 := by
  obtain ⟨hLX, hKX, hAltL, hAltK, hcommLK, hact, h16, hf, hMC⟩ := hsh
  obtain ⟨f, hfX, hford, hffix, hfnorm, hfcent⟩ := hf
  intro φ hφX _hφ2 hd z hz _hz1
  have hE25 : ∀ y0 : MulAut W, y0 ∈ Lb ⊔ Kb → orderOf y0 = 5 → y0 * φ = φ * y0 →
      (∀ k : ℕ, k < 5 → y0 ≠ f ^ k) → ∃ ψ ∈ X, orderOf ψ = 5 ∧ ψ z = z := by
    intro y0 hy0mem hy0ord hy0comm hfpow
    have hfcommφ : φ * f = f * φ :=
      CFSG.GroupTheory.commute_of_rkIdx_fixV_le hW (by norm_num : Nat.Prime 5) hford hffix
        (hfnorm φ hφX) (by omega) hd
    have hf5 : f ^ 5 = 1 := by
      rw [← hford]
      exact pow_orderOf_eq_one f
    have hf1 : f ≠ 1 := by
      intro h
      rw [h, orderOf_one] at hford
      omega
    have hy05 : y0 ^ 5 = 1 := by
      rw [← hy0ord]
      exact pow_orderOf_eq_one y0
    have hcommfy : f * y0 = y0 * f := (hfcent y0 hy0mem).symm
    have hPcard : Nat.card ↥(Subgroup.zpowers f ⊔ Subgroup.zpowers y0) = 25 :=
      CFSG.RankThree.PartTwo.Sec15.F153A10K.card_sup_zpowers_eq_25
        hcommfy hf5 hf1 hy05 hfpow
    have hy0X : y0 ∈ X := (sup_le hLX hKX) hy0mem
    have hPX : Subgroup.zpowers f ⊔ Subgroup.zpowers y0 ≤ X :=
      sup_le (Subgroup.zpowers_le.mpr hfX) (Subgroup.zpowers_le.mpr hy0X)
    have hPφ : ∀ ψ ∈ Subgroup.zpowers f ⊔ Subgroup.zpowers y0, ψ * φ = φ * ψ := by
      have hfC : f ∈ Subgroup.centralizer ({φ} : Set (MulAut W)) := by
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact hfcommφ.symm
      have hy0C : y0 ∈ Subgroup.centralizer ({φ} : Set (MulAut W)) := by
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact hy0comm
      have hPle : Subgroup.zpowers f ⊔ Subgroup.zpowers y0 ≤
          Subgroup.centralizer ({φ} : Set (MulAut W)) :=
        sup_le (Subgroup.zpowers_le.mpr hfC) (Subgroup.zpowers_le.mpr hy0C)
      intro ψ hψ
      exact Subgroup.mem_centralizer_singleton_iff.mp (hPle hψ)
    obtain ⟨ψ, hψP, hψord, hψfix⟩ :=
      CFSG.GroupTheory.exists_orderOf_five_fix_commV hW hd hPcard hPφ
    exact ⟨ψ, hPX hψP, hψord, hψfix z hz⟩
  have hfk : ∀ k : ℕ, ∀ y ∈ Lb ⊔ Kb, f ^ k * y = y * f ^ k := by
    intro k y hy
    have hc : Commute y f := hfcent y hy
    exact (hc.pow_right k).symm.eq
  have hnotL : ∀ x0 ∈ Lb, x0 ≠ 1 → ∀ z0 ∈ Kb, ∀ k : ℕ, x0 * z0 ≠ f ^ k := by
    intro x0 hx0 hx01 z0 hz0 k hk
    apply hx01
    refine a5_eq_one_of_forall_comm (Classical.choice hAltL) hx0 (fun y hy => Eq.symm ?_)
    have hfy := hfk k y (Subgroup.mem_sup_left hy)
    rw [← hk] at hfy
    have hzy : z0 * y = y * z0 := (hcommLK y hy z0 hz0).symm
    have h1 : x0 * y * z0 = y * x0 * z0 := by
      calc x0 * y * z0 = x0 * (y * z0) := by rw [mul_assoc]
        _ = x0 * (z0 * y) := by rw [hzy]
        _ = x0 * z0 * y := by rw [mul_assoc]
        _ = y * (x0 * z0) := hfy
        _ = y * x0 * z0 := by rw [mul_assoc]
    exact mul_right_cancel h1
  have hnotK : ∀ w0 ∈ Kb, w0 ≠ 1 → ∀ k : ℕ, w0 ≠ f ^ k := by
    intro w0 hw0 hw01 k hk
    apply hw01
    refine a5_eq_one_of_forall_comm (Classical.choice hAltK) hw0 (fun y hy => Eq.symm ?_)
    have hfy := hfk k y (Subgroup.mem_sup_right hy)
    rw [← hk] at hfy
    exact hfy
  obtain ⟨x0, hx0L, hx0ord⟩ := a5_exists_five (Classical.choice hAltL)
  have hx01 : x0 ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hx0ord
    omega
  rcases hact φ hφX with ⟨hnL, hnK⟩ | ⟨hLK, hKL⟩
  · rcases hMC φ hφX hd hnL hnK with hcL | hcK
    · refine hE25 x0 (Subgroup.mem_sup_left hx0L) hx0ord (hcL x0 hx0L).symm ?_
      intro k _ hk
      exact hnotL x0 hx0L hx01 1 Kb.one_mem k (by rw [mul_one]; exact hk)
    · obtain ⟨w0, hw0K, hw0ord⟩ := a5_exists_five (Classical.choice hAltK)
      have hw01 : w0 ≠ 1 := by
        intro h
        rw [h, orderOf_one] at hw0ord
        omega
      exact hE25 w0 (Subgroup.mem_sup_right hw0K) hw0ord (hcK w0 hw0K).symm
        (fun k _ => hnotK w0 hw0K hw01 k)
  ·
    have hφ2X : φ ^ 2 ∈ X := X.pow_mem hφX 2
    have hpow : ∀ x : MulAut W, φ ^ 2 * x * (φ ^ 2)⁻¹ = φ * (φ * x * φ⁻¹) * φ⁻¹ := by
      intro x
      simp only [pow_two]
      group
    have hnorm2L : ∀ x ∈ Lb, φ ^ 2 * x * (φ ^ 2)⁻¹ ∈ Lb := by
      intro x hx
      rw [hpow]
      exact hKL _ (hLK x hx)
    have hnorm2K : ∀ x ∈ Kb, φ ^ 2 * x * (φ ^ 2)⁻¹ ∈ Kb := by
      intro x hx
      rw [hpow]
      exact hLK _ (hKL x hx)
    have hd2 : rkIdx (fixV (Subgroup.zpowers (φ ^ 2))) ≤ 7 := by
      have hfixle : fixV (Subgroup.zpowers φ) ≤ fixV (Subgroup.zpowers (φ ^ 2)) := by
        intro v hv
        rw [mem_fixV] at hv ⊢
        intro ψ hψ
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hψ
        have hk : (φ ^ (2 : ℕ) : MulAut W) ^ k = φ ^ (2 * k) := by
          rw [← zpow_natCast φ 2, ← zpow_mul]
          norm_num
        rw [hk]
        exact hv _ (Subgroup.zpow_mem _ (Subgroup.mem_zpowers φ) (2 * k))
      exact (rkIdx_anti hfixle).trans hd
    have hcent2 : ∀ x ∈ Lb, φ ^ 2 * x = x * φ ^ 2 := by
      rcases hMC (φ ^ 2) hφ2X hd2 hnorm2L hnorm2K with hc | hc
      · exact hc
      · intro x hx
        have hz : φ ^ 2 * (φ * x * φ⁻¹) = (φ * x * φ⁻¹) * φ ^ 2 := hc _ (hLK x hx)
        calc φ ^ 2 * x = φ⁻¹ * (φ ^ 2 * (φ * x * φ⁻¹)) * φ := by
              simp only [pow_two]
              group
          _ = φ⁻¹ * ((φ * x * φ⁻¹) * φ ^ 2) * φ := by rw [hz]
          _ = x * φ ^ 2 := by
              simp only [pow_two]
              group
    let z0 : MulAut W := φ * x0 * φ⁻¹
    have hz0K : z0 ∈ Kb := hLK x0 hx0L
    have hz0ord : orderOf z0 = 5 := by
      rw [show z0 = (MulAut.conj φ) x0 by rw [MulAut.conj_apply]]
      exact (orderOf_injective (MulAut.conj φ).toMonoidHom
        (MulAut.conj φ).injective x0).trans hx0ord
    have hcomm_xz : x0 * z0 = z0 * x0 := hcommLK x0 hx0L z0 hz0K
    let y0 : MulAut W := x0 * z0
    have hx05 : x0 ^ 5 = 1 := by
      rw [← hx0ord]
      exact pow_orderOf_eq_one _
    have hz05 : z0 ^ 5 = 1 := by
      rw [← hz0ord]
      exact pow_orderOf_eq_one _
    have hy05 : y0 ^ 5 = 1 := by
      rw [show y0 = x0 * z0 from rfl, Commute.mul_pow (show Commute x0 z0 from hcomm_xz) 5,
        hx05, hz05, mul_one]
    have hy0ne : y0 ≠ 1 := by
      have h := hnotL x0 hx0L hx01 z0 hz0K 0
      rwa [pow_zero] at h
    have hy0ord : orderOf y0 = 5 := by
      have hdvd : orderOf y0 ∣ 5 := orderOf_dvd_iff_pow_eq_one.mpr hy05
      rcases Nat.prime_five.eq_one_or_self_of_dvd _ hdvd with h | h
      · exact absurd (orderOf_eq_one_iff.mp h) hy0ne
      · exact h
    have hφz : φ * z0 * φ⁻¹ = x0 := by
      have hc2 : φ ^ 2 * x0 = x0 * φ ^ 2 := hcent2 x0 hx0L
      calc φ * z0 * φ⁻¹ = φ * (φ * x0 * φ⁻¹) * φ⁻¹ := rfl
        _ = φ ^ 2 * x0 * (φ ^ 2)⁻¹ := (hpow x0).symm
        _ = x0 * φ ^ 2 * (φ ^ 2)⁻¹ := by rw [hc2]
        _ = x0 := by group
    have hy0conj : φ * y0 * φ⁻¹ = y0 := by
      calc φ * y0 * φ⁻¹ = (φ * x0 * φ⁻¹) * (φ * z0 * φ⁻¹) := by
            rw [show y0 = x0 * z0 from rfl]
            group
        _ = z0 * x0 := by rw [hφz]
        _ = y0 := hcomm_xz.symm
    have hy0comm : y0 * φ = φ * y0 := by
      have h := congrArg (fun t : MulAut W => t * φ) hy0conj
      simpa [mul_assoc] using h.symm
    exact hE25 y0 (Subgroup.mul_mem_sup hx0L hz0K) hy0ord hy0comm
      (fun k _ => hnotL x0 hx0L hx01 z0 hz0K k)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19
