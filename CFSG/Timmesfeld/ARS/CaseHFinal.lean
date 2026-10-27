module

public import CFSG.Timmesfeld.ARS.CaseHD4Frame
public import CFSG.Timmesfeld.ARS.CaseHInput

public section

namespace CFSG.Timmesfeld.ARS

open scoped commutatorElement
open CFSG.LieType.Universal CFSG.Timmesfeld.RankOne Matrix NaturalModule FrameSL3 Sec8Field
open CFSG.Timmesfeld.RankTwo CFSG.Timmesfeld.GradedPresentation CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Adjoint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.TwistedD4

namespace CaseH

theorem exists_setup {G : Type*} [Group G] {R : Set (Subgroup G)} (h : Hyp G R)
    (hH : SigmaEqLambda R) (hT : MTransitive R) {A : Subgroup G} (hA : A ∈ R)
    (h3 : 3 ≤ (linesThrough R A).ncard) : ∃ A₀ P P', Setup R A A₀ P P' := by
  have := h.finite
  have hR := h.root
  have hiso := h.noIsolated
  obtain ⟨B, hB, hAB⟩ := hiso A hA
  have hA₀ : B ∈ omegaSet R A := ⟨hB, hAB⟩
  have hpt : ∀ V ∈ linesThrough R A, ∃ P ∈ lambdaStar R A B, A ⊔ P = V := by
    intro V hV
    obtain ⟨D, hD, rfl⟩ := (mem_linesThrough_iff h hA).1 hV
    obtain ⟨P, ⟨hPR, hPle, hPψ⟩, -⟩ := existsUnique_mem_psiSet_of_le hR hiso hA hB hAB hD
    have hAP : A ≠ P := by
      rintro rfl
      exact Special.not_opposite hR hB hPψ.2 hAB.symm
    obtain ⟨hPΛ, hsup⟩ := mem_lambdaSet_of_le_sup hR hiso hA hD hA le_sup_left hPR hPle hAP
    exact ⟨P, ⟨hPΛ, hPψ⟩, hsup⟩
  obtain ⟨V₁, V₂, hV₁, hV₂, hne⟩ :=
    (Set.one_lt_ncard_iff (Set.toFinite _)).1 (by omega : 1 < (linesThrough R A).ncard)
  obtain ⟨P, hP, rfl⟩ := hpt V₁ hV₁
  obtain ⟨P', hP', rfl⟩ := hpt V₂ hV₂
  exact ⟨B, P, P', ⟨h, hH, hT, hA, h3, hA₀, hP, hP', fun e => hne (by rw [e])⟩⟩

namespace Coords

variable {G : Type} [Group G] {R : Set (Subgroup G)} {A A₀ P P' : Subgroup G}
  {S : Setup R A A₀ P P'} {F E : Type} [Field F] [Field E] (c : Coords S F E) [CharP E 2]
  [CharP F 2] [Finite F] [Finite E] (e : F →+* E) (he : ∀ s u, c.c5 s u = c.c5 (e u * s) 1)
  {τ : F} (hτ0 : τ ≠ 0) (hτ : ∀ u, c.m * c.x6 u * c.m⁻¹ = c.x2 (τ * u))
include he hτ0 hτ

theorem g2Frame (hsq : ∀ s, c.sharp s = s ^ 2) (hEF : Nat.card E = Nat.card F) {n : ℕ}
    (hF : Nat.card F = 2 ^ n) (hn : 2 ≤ n) : G2Frame G n := by
  have hβ := c.beta_eq e he (c.T_nondeg_G2 e he hτ0 hτ hsq)
  obtain ⟨l, hl0, hl1⟩ : ∃ l : E, l ≠ 0 ∧ l ≠ 1 := by
    by_contra hcon
    simp only [not_exists, not_and, not_not] at hcon
    have hsurj : Function.Surjective fun b : Bool => if b then (1 : E) else 0 := fun l => by
      by_cases hl : l = 0
      · exact ⟨false, by simp [hl]⟩
      · exact ⟨true, by simp [hcon l hl]⟩
    have h1 := Nat.card_le_card_of_surjective _ hsurj
    rw [Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool, hEF, hF] at h1
    have h2 : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    omega
  have hNt := c.Nt_eq e he hτ0 hτ hβ (c.not_additive_N_G2 e he hτ0 hτ hsq hl0 hl1)
  have hesurj : Function.Surjective e :=
    (e.injective.bijective_of_nat_card_le hEF.le).2
  refine ⟨F, inferInstance, inferInstance, hF, g2PhiOf (c.g2Psi e τ),
    g2_coneCompatible_of (c.g2Psi e τ) (fun w hw => ?_) c.g2Weyl (c.g2_hW e hτ0 hτ hβ)
      (c.g2_hrank e), c.g2_hgen e hτ0 hesurj, c.g2_hnt e⟩
  have hfun : (fun g : Σ _ : Fin 6, F => c.g2Psi e τ (hexRoot g.1) g.2) =
      fun g => c.g2Pos e τ g.1 g.2 := funext fun g => c.g2Psi_pos e τ g.1 g.2
  exact (congrArg (fun φ => FreeGroup.lift φ w) hfun).trans
    (c.g2_rels e he hτ0 hτ hsq hβ hNt w hw)

theorem d4Frame {n : ℕ} (hsq : ∀ s, c.sharp s = s ^ (2 ^ n + 2 ^ (2 * n)))
    (hF : Nat.card F = 2 ^ n) (hE : Nat.card E = 2 ^ (3 * n)) (hn : 1 ≤ n) :
    TwistedD4Frame G n := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set σ : E →+* E := iterateFrobenius E 2 n with hσdef
  have hσ : ∀ x, σ x = x ^ 2 ^ n := fun x => iterateFrobenius_def 2 n x
  have hE' : Nat.card E = (2 ^ n) ^ 3 := by rw [hE, ← pow_mul, mul_comm]
  have hσ3 : ∀ x, σ (σ (σ x)) = x := sigma_three_of_card hE' hσ
  have hsq' : ∀ s, c.sharp s = σ s * σ (σ s) := fun s => by
    rw [hsq, hσ, hσ, ← pow_mul, ← pow_add]
    congr 1
    rw [two_mul, pow_add]
  have hq : 1 < 2 ^ n := Nat.one_lt_two_pow (by omega)
  have hβ := c.beta_eq e he (c.T_nondeg_D4 e he hτ0 hτ σ hσ3 hsq')
  have hna : ¬ ∀ x y : E, c.N (x + y) = c.N x + c.N y := fun hadd => by
    have h1 := c.card_le_of_additive_N hτ0 hτ hadd
    rw [hE, hF] at h1
    have h2 : 2 ^ n < 2 ^ (3 * n) := Nat.pow_lt_pow_right (by norm_num) (by omega)
    omega
  have hNt := c.Nt_eq e he hτ0 hτ hβ hna
  set ι := fixedInv e hF hσ hq with hιdef
  have heι : ∀ t, e (ι t) = t := e_fixedInv e hF hσ hq
  have hιs : Function.Surjective ι := fixedInv_surjective e hF hσ hq
  refine ⟨E, inferInstance, inferInstance, hE', σ, hσ, d43PhiOf hσ3 c.d4PsiS (c.d4PsiL ι τ),
    d43_coneCompatible_of hσ3 c.d4PsiS (c.d4PsiL ι τ) (fun w hw => ?_) c.g2Weyl (c.d4_hWS hβ)
      (c.d4_hWL ι hτ0 hτ) (c.d4_hrank ι hσ3), c.d4_hgen ι hτ0 hσ3 hιs, c.d4_hnt ι hσ3⟩
  exact (congrArg (fun φ => FreeGroup.lift φ w) (c.d43PsiPos_eq ι τ)).trans
    (c.d4_rels e he hτ0 hτ hσ3 hsq' hβ hNt ι heι w hw)

end Coords

end CaseH

theorem caseHFrameInput : CaseHFrameInput := by
  intro G _ R h hH hT A hA h3 h23
  obtain ⟨A₀, P, P', S⟩ := CaseH.exists_setup h hH hT hA h3
  obtain ⟨n, m, hn, hm, hq, hL, ⟨c⟩⟩ := S.exists_coords
  obtain ⟨e, he⟩ := c.exists_ringHom
  obtain ⟨τ, hτ0, hτ⟩ := c.exists_tau
  have hF : Nat.card (GaloisField 2 n) = 2 ^ n := GaloisField.card 2 n (by omega)
  have hE : Nat.card (GaloisField 2 m) = 2 ^ m := GaloisField.card 2 m (by omega)
  rcases c.classify e he hτ0 hτ hn hF hE with ⟨rfl, hsq⟩ | ⟨rfl, hsq⟩ | ⟨rfl, rfl⟩
  · have h2 : 2 ≤ m := by
      by_contra hlt
      have hm1 : m = 1 := by omega
      subst hm1
      exact h23 ⟨by rw [hq]; norm_num, by rw [hL]; norm_num⟩
    exact Or.inl ⟨m, h2, hq, c.g2Frame e he hτ0 hτ hsq (hE.trans hF.symm) hF h2⟩
  · exact Or.inr ⟨n, hn, hq, c.d4Frame e he hτ0 hτ hsq hF hE hn⟩
  · exact absurd (by rw [hL]; norm_num)
      (CaseH.ncard_linesThrough_ne_five h hH hA (by rw [hq]; norm_num))

end CFSG.Timmesfeld.ARS
