module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeE6Weyl
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeExcFloorsPF
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeExcFloorsE6
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeExcTw
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeExcCaseV
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeExcEigen
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeExcEigenTw
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeExcE6Shape
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeExcRelOneAt
public import CFSG.RankThree.PartOne.KE.CTLang

public section

namespace CFSG.StandardType.RCKRP

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Universal
  CFSG.LieType.RootSystem CFSG.StandardType CFSG.StandardType.S2MathFi1035Pos
  CFSG.StandardType.RCKC1 CFSG.StandardType.GGFinModel CFSG.StandardType.LieCore
open CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LieType.SeitzGeneration CFSG.RankThree.E6 CFSG.RankThree.PartOne.KE
open CFSG.Open (StatedLieTag StatedLieAdmissible)
open CFSG.StandardType.ExcFramesHalf (IsToralSubgroup)
open scoped Matrix
open CFSG.StandardType.RCKBand (CaseEightV StepZeroRankFloor BandRankFloor)

theorem rckExc_dvd_pred_of_cast_eq_one {p f : ℕ} (h : ((2 ^ f : ℕ) : ZMod p) = 1) :
    p ∣ 2 ^ f - 1 := by
  have h' : ((2 ^ f : ℕ) : ZMod p) = ((1 : ℕ) : ZMod p) := by simpa using h
  have h1 := (ZMod.natCast_eq_natCast_iff _ _ _).1 h'
  exact (Nat.modEq_iff_dvd' Nat.one_le_two_pow).1 h1.symm

theorem rckExc_dvd_succ_of_cast_eq_neg_one {p f : ℕ} (h : ((2 ^ f : ℕ) : ZMod p) = -1) :
    p ∣ 2 ^ f + 1 := by
  have h1 : ((2 ^ f + 1 : ℕ) : ZMod p) = 0 := by
    rw [Nat.cast_succ, h]
    ring
  exact (ZMod.natCast_eq_zero_iff _ _).1 h1

theorem rckExc_even_of_cast_eq_one_three {f : ℕ} (h : ((2 ^ f : ℕ) : ZMod 3) = 1) : Even f := by
  rcases Nat.even_or_odd f with he | ho
  · exact he
  · exfalso
    have h3 := rckExc_three_dvd_two_pow_succ_of_odd ho
    have h1 : ((2 ^ f + 1 : ℕ) : ZMod 3) = 0 := (ZMod.natCast_eq_zero_iff _ _).2 h3
    rw [Nat.cast_succ, h] at h1
    exact absurd h1 (by decide)

theorem rckExc_odd_of_cast_eq_neg_one_three {f : ℕ} (h : ((2 ^ f : ℕ) : ZMod 3) = -1) : Odd f := by
  rcases Nat.even_or_odd f with he | ho
  · exfalso
    have h3 := rckExc_three_dvd_two_pow_pred_of_even he
    have h1 : ((2 ^ f : ℕ) : ZMod 3) = 1 := by
      have := (Nat.modEq_iff_dvd' Nat.one_le_two_pow).2 h3
      simpa using ((ZMod.natCast_eq_natCast_iff _ _ _).2 this).symm
    rw [h1] at h
    exact absurd h (by decide)
  · exact ho

theorem rckExc_five_le_of_ne {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) : 5 ≤ p := by
  have h2 := hp.two_le
  have h4 : p ≠ 4 := by
    rintro rfl
    exact absurd hp (by norm_num)
  omega

theorem rckExc_E6_floor_of_cast_one
    {X : Type} [Group X] [Finite X] {n f : ℕ} {ψ : (ggU .E6 n f).K →* X} {p : ℕ}
    {G₀ A B₁ D J L R Rm K : Subgroup X} {e : X}
    (h : RCKRPConfig .E6 n f ψ p G₀ A B₁ D J L R Rm K e) (hc : ((2 ^ f : ℕ) : ZMod p) = 1) :
    p ^ 5 ≤ Nat.card A := by
  have hpp : p.Prime ∧ p ≠ 2 := by
    have h' := h
    unfold RCKRPConfig at h'
    exact ⟨h'.2.2.1, h'.2.2.2.1⟩
  by_cases hp3 : p = 3
  · subst hp3
    exact rckExc_E6_floor h rfl (rckExc_even_of_cast_eq_one_three hc)
  · exact rckExc_E6_floor_pf h (rckExc_five_le_of_ne hpp.1 hpp.2 hp3)
      (rckExc_dvd_pred_of_cast_eq_one hc)

theorem rckExc_twE6_three_floor_of_toral
    (hFl : RCKExcFloors)
    {X : Type} [Group X] [Finite X] {n f : ℕ} {ψ : (ggU .twistedE6 n f).K →* X}
    {G₀ A B₁ D J L R Rm K : Subgroup X} {e : X}
    (h : RCKRPConfig .twistedE6 n f ψ 3 G₀ A B₁ D J L R Rm K e) (hodd : Odd f)
    {θ : ↥G₀ →* ModGL (langTag .twistedE6) GGL}
    {A' : Subgroup (ModGL (langTag .twistedE6) GGL)}
    (hfr : RCKBridgeFrame .twistedE6 f 3 G₀ A θ A')
    (hT : IsToralSubgroup (langTag .twistedE6) GGL A') :
    3 ^ 5 ≤ Nat.card A := by
  by_contra hlt
  have ht : GGExcFive .twistedE6 := Or.inr (Or.inr (Or.inr (Or.inr rfl)))
  have hfl : StepZeroRankFloor .twistedE6 f 3 A' :=
    hFl X .twistedE6 n f ψ 3 G₀ A B₁ D J L R Rm K e ht h θ A' hfr
  obtain ⟨-, -, h9f, hout⟩ := hfl.1 rfl
  have hlt5 : ¬ 3 ^ 5 ≤ Nat.card A' := by
    rw [hfr.2.2.2.2.1]
    exact hlt
  have h3 : 3 ∣ 2 ^ f + 1 := rckExc_three_dvd_two_pow_succ_of_odd hodd
  by_cases h9 : 9 ∣ 2 ^ f + 1
  · exact hlt5 (h9f rfl h9)
  by_cases hR : A' ≤ ⁅ggFixGp .twistedE6 f, ggFixGp .twistedE6 f⁆
  · have hV := rckExcCaseVData_of_caseEightV ht h hfr ⟨rfl, rfl, h3, h9, hR⟩ hlt5
    exact rckExcCaseV_not_toral h hV ⟨θ, A', hfr, hT⟩
  · exact hlt5 (hout rfl hodd hR)

theorem rckExc_twE6_floor_of_cast_neg_one
    (hFl : RCKExcFloors)
    {X : Type} [Group X] [Finite X] {n f : ℕ} {ψ : (ggU .twistedE6 n f).K →* X} {p : ℕ}
    {G₀ A B₁ D J L R Rm K : Subgroup X} {e : X}
    (h : RCKRPConfig .twistedE6 n f ψ p G₀ A B₁ D J L R Rm K e)
    {θ : ↥G₀ →* ModGL (langTag .twistedE6) GGL}
    {A' : Subgroup (ModGL (langTag .twistedE6) GGL)}
    (hfr : RCKBridgeFrame .twistedE6 f p G₀ A θ A')
    (hT : IsToralSubgroup (langTag .twistedE6) GGL A') (hc : ((2 ^ f : ℕ) : ZMod p) = -1) :
    p ^ 5 ≤ Nat.card A := by
  have hpp : p.Prime ∧ p ≠ 2 := by
    have h' := h
    unfold RCKRPConfig at h'
    exact ⟨h'.2.2.1, h'.2.2.2.1⟩
  by_cases hp3 : p = 3
  · subst hp3
    exact rckExc_twE6_three_floor_of_toral hFl h (rckExc_odd_of_cast_eq_neg_one_three hc) hfr hT
  · exact rckExc_twE6_floor_pf h (rckExc_five_le_of_ne hpp.1 hpp.2 hp3)
      (rckExc_dvd_succ_of_cast_eq_neg_one hc)

theorem rckExc_E6_rho_sq
    {X : Type} [Group X] [Finite X] {n f : ℕ} {ψ : (ggU .E6 n f).K →* X} {p : ℕ}
    {G₀ A B₁ D J L R Rm K : Subgroup X} {e : X}
    (h : RCKRPConfig .E6 n f ψ p G₀ A B₁ D J L R Rm K e)
    {θ : ↥G₀ →* ModGL (langTag .E6) GGL} {A' : Subgroup (ModGL (langTag .E6) GGL)}
    (hfr : RCKBridgeFrame .E6 f p G₀ A θ A')
    (Dl : LangDatum (langTag .E6) GGL) (ρ : Equiv.Perm (Fin (langTag .E6).rank → ℤ))
    (hΦ : Dl.Φ = ggPhi .E6 f) (hρ : FrobRootMap Dl ρ)
    (hconj : ∀ x ∈ A', Dl.g0⁻¹ * x * Dl.g0 ∈ Dl.torus) :
    ∀ γ, IsRoot (langTag .E6) γ → ρ (ρ γ) = γ := by
  have h' := h
  unfold RCKRPConfig at h'
  obtain ⟨hGG, -, hp, hp2, -, hB1A, -, -, -, -, -, -, hp4, -⟩ := h'
  have hf : 1 ≤ f := hGG.1.1.2.1
  obtain ⟨w, hρw, hcard⟩ := rckExc_torus_eigen_untwisted (t := .E6) (by decide) hf hp hp2 Dl ρ
    hΦ hρ A' hfr.2.2.2.1 hconj
  have hm4 : p ^ 4 ≤ Nat.card A' := by
    rw [hfr.2.2.2.2.1]
    exact hp4.trans (Subgroup.card_le_of_le hB1A)
  have hm5 : ((2 ^ f : ℕ) : ZMod p) = ((1 : ℤ) : ZMod p) → p ^ 5 ≤ Nat.card A' := fun hc => by
    rw [hfr.2.2.2.2.1]
    exact rckExc_E6_floor_of_cast_one h (by simpa using hc)
  exact rckE6_rho_sq_core hp hp2 (weylMatrix w) 1 (Or.inl rfl) (rckE6_weyl_matrixCheck w).1
    (rckE6_weylMatrix_pres_form w) (fun γ hγ => (hρw γ hγ).trans (weylMatrix_mulVec w γ).symm)
    (fun γ hγ => (hρ.isRoot_iff γ).2 hγ) hm4 hcard hm5

theorem rckExc_twE6_rho_sq
    (hFl : RCKExcFloors)
    {X : Type} [Group X] [Finite X] {n f : ℕ} {ψ : (ggU .twistedE6 n f).K →* X} {p : ℕ}
    {G₀ A B₁ D J L R Rm K : Subgroup X} {e : X}
    (h : RCKRPConfig .twistedE6 n f ψ p G₀ A B₁ D J L R Rm K e)
    {θ : ↥G₀ →* ModGL (langTag .twistedE6) GGL}
    {A' : Subgroup (ModGL (langTag .twistedE6) GGL)}
    (hfr : RCKBridgeFrame .twistedE6 f p G₀ A θ A')
    (hT : IsToralSubgroup (langTag .twistedE6) GGL A')
    (Dl : LangDatum (langTag .twistedE6) GGL)
    (ρ : Equiv.Perm (Fin (langTag .twistedE6).rank → ℤ))
    (hΦ : Dl.Φ = ggPhi .twistedE6 f) (hρ : FrobRootMap Dl ρ)
    (hconj : ∀ x ∈ A', Dl.g0⁻¹ * x * Dl.g0 ∈ Dl.torus) :
    ∀ γ, IsRoot (langTag .twistedE6) γ → ρ (ρ γ) = γ := by
  have h' := h
  unfold RCKRPConfig at h'
  obtain ⟨-, -, hp, hp2, -, hB1A, -, -, -, -, -, -, hp4, -⟩ := h'
  obtain ⟨w, hw⟩ := rckExc_rho_twisted (f := f) Dl ρ hΦ hρ
  have hq : Dl.q = 2 ^ f := rckExc_langDatum_q_eq Dl hΦ
  have hcard := rckExc_torus_eigen_of_rho hp hp2 Dl ρ hρ (weylMatrix w * rhoMatrix)
    (fun i => hw _ (isRoot_single _ i)) A' hfr.2.2.2.1 hconj
  rw [hq] at hcard
  have hm4 : p ^ 4 ≤ Nat.card A' := by
    rw [hfr.2.2.2.2.1]
    exact hp4.trans (Subgroup.card_le_of_le hB1A)
  have hm5 : ((2 ^ f : ℕ) : ZMod p) = ((-1 : ℤ) : ZMod p) → p ^ 5 ≤ Nat.card A' := fun hc => by
    rw [hfr.2.2.2.2.1]
    exact rckExc_twE6_floor_of_cast_neg_one hFl h hfr hT (by simpa using hc)
  exact rckE6_rho_sq_core hp hp2 (weylMatrix w * rhoMatrix) (-1) (Or.inr rfl)
    (rckE6_weyl_matrixCheck w).2 (rckE6_twistMatrix_pres_form w) hw
    (fun γ hγ => (hρ.isRoot_iff γ).2 hγ) hm4 hcard hm5

theorem rckExcRelOneAt_E6
    : RCKExcRelOneAt (fun t => t = .E6) := by
  intro X _ _ t n f ψ p G₀ A B₁ D J L R Rm K e hP h hKJ θ A' hfr hT Dl ρ hΦ hρ hconj S₁ S₂ h21 h1A
    hS1 hS2 iJ iK hsub hShape
  subst hP
  have hρ2 := rckExc_E6_rho_sq h hfr Dl ρ hΦ hρ hconj
  have h' := h
  unfold RCKRPConfig at h'
  obtain ⟨-, -, hp, hp2, -⟩ := h'
  exact absurd hShape (rckE6_famClass_not_excShape hp hp2 S₂ hS2
    (fun x hx => (mem_twistedTorusOf.1 (hconj x (h1A (h21 hx)))).1) hρ2 iK)

theorem rckExcRelOneAt_twE6
    : RCKExcRelOneAt (fun t => t = .twistedE6) := by
  intro X _ _ t n f ψ p G₀ A B₁ D J L R Rm K e hP h hKJ θ A' hfr hT Dl ρ hΦ hρ hconj S₁ S₂ h21 h1A
    hS1 hS2 iJ iK hsub hShape
  subst hP
  have hρ2 := rckExc_twE6_rho_sq rckExcFloors_holds h hfr hT Dl ρ hΦ hρ hconj
  have h' := h
  unfold RCKRPConfig at h'
  obtain ⟨-, -, hp, hp2, -⟩ := h'
  exact absurd hShape (rckE6_famClass_not_excShape hp hp2 S₂ hS2
    (fun x hx => (mem_twistedTorusOf.1 (hconj x (h1A (h21 hx)))).1) hρ2 iK)

theorem rckExcRelOneAt_E6_twE6
    : RCKExcRelOneAt (fun t => t = .E6 ∨ t = .twistedE6) := by
  intro X _ _ t n f ψ p G₀ A B₁ D J L R Rm K e hP
  rcases hP with hP | hP
  · exact rckExcRelOneAt_E6 X t n f ψ p G₀ A B₁ D J L R Rm K e hP
  · exact rckExcRelOneAt_twE6 X t n f ψ p G₀ A B₁ D J L R Rm K e hP

end CFSG.StandardType.RCKRP

end
