module

public import CFSG.LocalAnalysis.StandardType.GGTwE6DD2Recipe
public import CFSG.LocalAnalysis.StandardType.GGTwE6DD2Cover

public section

namespace CFSG.StandardType.TwE6R4

open CFSG.Open


theorem card_ker_dvd_three {n : ℕ} (hn : 1 ≤ n) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ n) ^ 2) {L' : Type} [Group L'] [Finite L']
    {ψ : L' →* TwE6Delta.RecipeR K n} (hψ : Function.Surjective ψ)
    (hker : ψ.ker ≤ Subgroup.center L') (hperf : commutator L' = ⊤)
    (hodd : Odd (Nat.card ψ.ker)) : Nat.card ψ.ker ∣ 3 := by
  have hZR := TwE6Delta.center_recipeR_eq_bot hn hK
  have hkc : ψ.ker = Subgroup.center L' := BstarDesc.ker_eq_center hψ hker hZR
  obtain ⟨hcf1, hcf2⟩ := TwE6DD2.center_facts hn hK hψ hker hperf
  have hoddZ : Odd (Nat.card (Subgroup.center L')) := by rw [← hkc]; exact hodd
  haveI : Finite (Subgroup.center L') := inferInstance
  let M : ℕ := 4 ^ Nat.card L'
  let f : Subgroup.center L' → Subgroup.center L' := fun z => z ^ M
  have hf_inj : Function.Injective f := by
    intro z w hzw
    have hzf : (z : L') ^ M = (w : L') ^ M := by
      have := congrArg (fun t : Subgroup.center L' => (t : L')) hzw
      simpa [f] using this
    let g : L' := (z : L') * (w : L')⁻¹
    have hgZ : g ∈ Subgroup.center L' := mul_mem z.2 (inv_mem w.2)
    have hgM : g ^ M = 1 := by
      have hcomm : Commute (z : L') (w : L') :=
        (Subgroup.mem_center_iff.1 z.2 (w : L')).symm
      change ((z : L') * (w : L')⁻¹) ^ M = 1
      rw [hcomm.inv_right.mul_pow, inv_pow, hzf, mul_inv_cancel]
    have hdvdK : orderOf g ∣ M := orderOf_dvd_iff_pow_eq_one.2 hgM
    have hdvdZ : orderOf g ∣ Nat.card (Subgroup.center L') :=
      Subgroup.orderOf_dvd_natCard _ hgZ
    have hoddg : Odd (orderOf g) := hoddZ.of_dvd_nat hdvdZ
    have hfour : M = 2 ^ (2 * Nat.card L') := by
      dsimp only [M]
      rw [show (4 : ℕ) = 2 ^ 2 by norm_num, pow_mul]
    have hdvd2 : orderOf g ∣ 2 ^ (2 * Nat.card L') := by rw [← hfour]; exact hdvdK
    have hone : orderOf g = 1 :=
      (Nat.Coprime.pow_right _ (Nat.coprime_two_right.mpr hoddg)).eq_one_of_dvd hdvd2
    have hg1 : g = 1 := orderOf_eq_one_iff.1 hone
    exact Subtype.ext (mul_inv_eq_one.1 hg1)
  have hf_surj : Function.Surjective f := (Finite.injective_iff_surjective (f := f)).1 hf_inj
  have hZcore : ∀ z : Subgroup.center L', (z : L') ^ 3 = 1 := by
    intro z
    obtain ⟨w, hw⟩ := hf_surj z
    have hw' : (w : L') ^ M = (z : L') := by
      have := congrArg (fun t : Subgroup.center L' => (t : L')) hw
      simpa [f] using this
    rw [show (z : L') = (w : L') ^ M from hw'.symm]
    exact hcf1 (w : L') w.2
  by_cases h3ex : ∃ z₀ ∈ Subgroup.center L', orderOf z₀ = 3
  ·
    obtain ⟨z₀, hz₀, ho₀⟩ := h3ex
    have hle : Subgroup.center L' ≤ Subgroup.zpowers z₀ := by
      intro z hz
      exact hcf2 z₀ hz₀ z hz ho₀ (hZcore ⟨z, hz⟩)
    have hdvd : Nat.card (Subgroup.center L') ∣ 3 := by
      have h := Subgroup.card_dvd_of_le hle
      rwa [Nat.card_zpowers, ho₀] at h
    rw [hkc]
    exact hdvd
  ·
    have hbot : Subgroup.center L' = ⊥ := by
      rw [Subgroup.eq_bot_iff_forall]
      intro z hz
      have hdvd3 : orderOf z ∣ 3 := orderOf_dvd_iff_pow_eq_one.2 (hZcore ⟨z, hz⟩)
      rcases (Nat.dvd_prime Nat.prime_three).1 hdvd3 with h1 | h3
      · exact orderOf_eq_one_iff.1 h1
      · exact absurd ⟨z, hz, h3⟩ h3ex
    rw [hkc, hbot, Subgroup.card_bot]
    exact one_dvd 3

theorem cover_commute_of_nine {n : ℕ} (hn : 1 ≤ n) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ n) ^ 2) (h9 : 9 ∣ 2 ^ n + 1)
    {L' : Type} [Group L'] [Finite L'] {ψ : L' →* TwE6Delta.RecipeR K n}
    (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center L') (hperf : commutator L' = ⊤)
    {Y : Subgroup (MulAut (TwE6Delta.RecipeR K n))}
    (hYI : ∀ φ ∈ Y, φ ∈ TwE6Delta.RecipeI K n)
    (hY : IsElemAbelian 3 Y) (hY6 : Nat.card Y = 3 ^ 6) :
    (∀ l₁ l₂ : L', MulAut.conj (ψ l₁) ∈ Y → MulAut.conj (ψ l₂) ∈ Y → l₁ * l₂ = l₂ * l₁) ∧
      Y ≤ (MulAut.conj : TwE6Delta.RecipeR K n →* MulAut (TwE6Delta.RecipeR K n)).range := by
  have h3 : 3 ∣ 2 ^ n + 1 := dvd_trans (by norm_num) h9
  have h5 : 3 ^ 5 ≤ Nat.card Y := by rw [hY6]; norm_num
  obtain ⟨Y', hYY', -, -, -, h9'⟩ :=
    TwE6DD2.exists_cubeTorus_recipe hn hK h3 hY (fun φ hφ => hYI φ hφ) h5
  obtain ⟨hY'inn, W, hW, hW9, hYW⟩ := h9' h9
  refine ⟨fun l₁ l₂ h₁ h₂ => ?_, hYY'.trans hY'inn⟩
  exact TwE6DD2.commute_of_cube_mem hn hK hψ hker hperf hW hW9
    (fun y hy => hYW y (hYY' hy)) h₁ h₂

end CFSG.StandardType.TwE6R4

