module

public import CFSG.RankThree.PartOne.K159.BorelBlock
public import CFSG.RankThree.PartOne.S15K.Row1Layer
import CFSG.RankThree.PartOne.S15K.BlockFacts
import CFSG.RankThree.PartOne.KC.LinearCommutantSetting
import CFSG.RankThree.PartOne.KC.LinearCommutantFactors
import CFSG.RankThree.PartOne.S15K.ProjSLBridge
public import CFSG.RankThree.PartOne.K159.BorelL0c
import CFSG.RankThree.PartOne.S15K.LayerTransport

public section

namespace CFSG.RankThree.PartOne.K159

open CFSG CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.RankThree.PartOne CFSG.RankThree.PartOne.S15K CFSG.RankThree.PartOne.KCLinComm
  CFSG.RankThree.PartOne.KCPrimary Matrix
open scoped _root_.Classical
open Polynomial

section Transport

variable {G : Type} [Group G] {Γ : Type*} [Group Γ]

theorem nonempty_mulEquiv_of_transport {I : Subgroup G} (ψ : ↥I →* Γ) (hψ : Function.Injective ψ)
    {U : Type*} [Group U] (ρ : U →* Γ) {F : Subgroup U} {Q : Subgroup G}
    (hQ : ∀ x : G, x ∈ Q ↔ ∃ hx : x ∈ I, ψ ⟨x, hx⟩ ∈ F.map ρ) (hFB : F.map ρ ≤ ψ.range)
    (hρ : ∀ u ∈ F, ρ u = 1 → u = 1) : Nonempty (↥F ≃* ↥Q) := by
  let ρF : ↥F →* Γ := ρ.comp F.subtype
  have hρF : ∀ u : ↥F, ρF u ∈ ψ.range := fun u => hFB ⟨u, u.2, rfl⟩
  let θ : ↥F →* ↥ψ.range := ρF.codRestrict ψ.range hρF
  let ψe : ↥I ≃* ↥ψ.range := MonoidHom.ofInjective hψ
  let Θ : ↥F →* G := I.subtype.comp (ψe.symm.toMonoidHom.comp θ)
  have hθ : Function.Injective θ := by
    rw [injective_iff_map_eq_one]
    intro u hu
    have h1 : ρ (u : U) = 1 := congrArg Subtype.val hu
    exact Subtype.ext (hρ _ u.2 h1)
  have hΘ : Function.Injective Θ := Subtype.val_injective.comp (ψe.symm.injective.comp hθ)
  have hrange : Θ.range = Q := by
    ext x
    rw [hQ x]
    constructor
    · rintro ⟨u, rfl⟩
      refine ⟨(ψe.symm (θ u)).2, ?_⟩
      have h1 : ψ (ψe.symm (θ u)) = ρ (u : U) := by
        have := congrArg Subtype.val (ψe.apply_symm_apply (θ u))
        exact this
      show ψ (ψe.symm (θ u)) ∈ F.map ρ
      rw [h1]
      exact ⟨u, u.2, rfl⟩
    · rintro ⟨hx, u, hu, hux⟩
      refine ⟨⟨u, hu⟩, ?_⟩
      have h1 : θ ⟨u, hu⟩ = ψe ⟨x, hx⟩ := Subtype.ext hux
      show ((ψe.symm (θ ⟨u, hu⟩) : ↥I) : G) = x
      rw [h1, ψe.symm_apply_apply]
  exact ⟨(MonoidHom.ofInjective hΘ).trans (MulEquiv.subgroupCongr hrange)⟩

theorem borelFacts_of_transport [Finite G] {p : ℕ} {I : Subgroup G} (ψ : ↥I →* Γ)
    (hψ : Function.Injective ψ) {U : Type*} [Group U] (ρ : U →* Γ) {F : Subgroup U}
    {Q : Subgroup G} (hQ : ∀ x : G, x ∈ Q ↔ ∃ hx : x ∈ I, ψ ⟨x, hx⟩ ∈ F.map ρ)
    (hFB : F.map ρ ≤ ψ.range) (hρ : ∀ u ∈ F, ρ u = 1 → u = 1) (h : BorelFactsGrp p ↥F) :
    BorelFacts p Q := by
  obtain ⟨e⟩ := nonempty_mulEquiv_of_transport ψ hψ ρ hQ hFB hρ
  have : Finite ↥F := Finite.of_equiv _ e.symm.toEquiv
  exact BorelFactsGrp.of_mulEquiv e h

end Transport

section Block

variable {K : Type} [Field K] {n : ℕ} {x : Module.End K (Fin n → K)}

theorem borelFactsGrp_blockImage [CharP K 2] [Finite K] {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hpK : p ∣ Nat.card K - 1) (hsq : Squarefree (minpoly K x)) (c : primaryFactors x)
    (h2 : 2 ≤ mult x c) (h4 : mult x c ≤ 4) : BorelFactsGrp p (blockImage hsq c) := by
  have : CharP (Efac x c) 2 := charP_of_injective_algebraMap (algebraMap K (Efac x c)).injective 2
  have : Module.Finite K (Efac x c) := inferInstance
  have : Finite (Efac x c) := Module.finite_of_finite K
  have hpE : p ∣ Nat.card (Efac x c) - 1 := by
    rw [Module.natCard_eq_pow_finrank (K := K) (V := Efac x c)]
    have h1 := Nat.sub_dvd_pow_sub_pow (Nat.card K) 1 (Module.finrank K (Efac x c))
    rw [one_pow] at h1
    exact hpK.trans h1
  have hSL := borelFactsGrp_specialLinear (K := Efac x c) (m := mult x c) hp hpE h2 (by omega)
  let Θ := (blockTheta hsq).comp (blockEmbed (Efac x) (mult x) c)
  have hΘ : Function.Injective Θ := (blockTheta_injective hsq).comp (blockEmbed_injective c)
  have heq : Θ.range = blockImage hsq c := by
    ext g
    rw [mem_blockImage]
    constructor
    · rintro ⟨s, rfl⟩
      exact ⟨s, rfl⟩
    · rintro ⟨s, rfl⟩
      exact ⟨s, rfl⟩
  exact BorelFactsGrp.of_mulEquiv ((MonoidHom.ofInjective hΘ).trans (MulEquiv.subgroupCongr heq)) hSL

end Block

section Row

variable {G : Type} [Group G] [Finite G]

@[expose] def LayerBorelData (p : ℕ) (E I : Subgroup G) : Prop :=
  ∀ b ∈ E, b ≠ 1 → ∃ (ι : Type) (Q : ι → Subgroup G),
    (∀ i, Q i ≤ I ⊓ Subgroup.centralizer ({b} : Set G)) ∧
    (∀ i, IsComponent ((Q i).subgroupOf (I ⊓ Subgroup.centralizer ({b} : Set G)))) ∧
    ⁅I ⊓ Subgroup.centralizer ({b} : Set G), I ⊓ Subgroup.centralizer ({b} : Set G)⁆ = ⨆ i, Q i ∧
    ∀ i, BorelFacts p (Q i)

theorem layerBorel_of_lifts {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) {E I : Subgroup G}
    {K : Type} [Field K] [Finite K] [CharP K 2] (hK4 : 4 ≤ Nat.card K) (hpK : p ∣ Nat.card K - 1)
    (hEI : E ≤ Subgroup.normalizer (I : Set G)) (φ : ↥I ≃* projectiveSL 4 K)
    (B : ↥E → GL (Fin 4) K) (hBdet : ∀ e, (B e : Matrix (Fin 4) (Fin 4) K).det = 1)
    (hBp : ∀ e, B e ^ p = 1)
    (hBact : ∀ e : ↥E, actP φ ⟨(e : G), hEI e.2⟩ = LinearFlag.conjAut 4 K (B e)) :
    LayerBorelData p E I := by
  have hp2 : p ≠ 2 := by omega
  let ψ : ↥I →* MulAut (projectiveSL 4 K) :=
    (MulAut.conj : projectiveSL 4 K →* MulAut (projectiveSL 4 K)).comp φ.toMonoidHom
  have hψ : Function.Injective ψ :=
    (CFSG.RankThree.RegularUnipotent.conj_injective_projectiveSL (by norm_num)).comp φ.injective
  have hψrange : ψ.range = (MulAut.conj : projectiveSL 4 K →* MulAut (projectiveSL 4 K)).range := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨φ x, rfl⟩
    · rintro ⟨p0, rfl⟩
      exact ⟨φ.symm p0, by simp [ψ]⟩
  have hInnB : (MulAut.conj : projectiveSL 4 K →* MulAut (projectiveSL 4 K)).range ≤ ψ.range :=
    hψrange.ge
  have hBD : ψ.range ≤ (LinearFlag.conjAut 4 K).range := by
    rw [hψrange, ← KCLinComm.map_toGL_range_eq_conj_range (n := 4) (K := K)]
    rintro _ ⟨g, -, rfl⟩
    exact ⟨g, rfl⟩
  intro b hb hb1
  set bE : ↥E := ⟨b, hb⟩ with hbE
  set a : GL (Fin 4) K := B bE with ha
  have hap : a ^ p = 1 := hBp bE
  have hadet : (a : Matrix (Fin 4) (Fin 4) K).det = 1 := hBdet bE
  have hpK0 : (p : K) ≠ 0 := by
    intro h0
    exact hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).1
      ((CharP.cast_eq_zero_iff K 2 p).1 h0)).symm
  have hsq : Squarefree (minpoly K (Matrix.toLin' (a : Matrix (Fin 4) (Fin 4) K))) := by
    refine squarefree_minpoly_of_pow_eq_one hpK0 ?_
    rw [← Matrix.toLin'_pow, ← Units.val_pow_eq_pow_val, hap, Units.val_one, Matrix.toLin'_one]
    rfl
  have hZp : ∀ c : Kˣ, c ^ p = 1 → c ^ 4 = 1 → c = 1 := fun c _ h4 =>
    Units.ext (eq_one_of_pow_four_eq_one (by simpa using congrArg Units.val h4))
  have hDn : (LinearFlag.conjAut 4 K).range.Normal := conjAut_range_normal (by norm_num)
  have S := projSetting (n := 4) (by norm_num) hK4 hZp hDn ψ.range hInnB a hap hadet hsq
  have hbI : b ∈ Subgroup.normalizer (I : Set G) := hEI hb
  have hcompb : ∀ x : ↥I, ψ (I.normalizerMonoidHom ⟨b, hbI⟩ x) =
      LinearFlag.conjAut 4 K a * ψ x * (LinearFlag.conjAut 4 K a)⁻¹ := compat_of_actP φ (hBact bE)
  obtain ⟨Q, hQH, hQc, hder, hmem⟩ := layer_of_projSetting ψ hψ hbI hcompb hBD S
  have hFB : ∀ i : {c : primaryFactors (Matrix.toLin' (a : Matrix (Fin 4) (Fin 4) K)) //
      2 ≤ mult (Matrix.toLin' (a : Matrix (Fin 4) (Fin 4) K)) c},
      (blockImage hsq i.1).map (LinearFlag.conjAut 4 K) ≤ ψ.range := fun i => S.map_le_B i
  have hmultle : ∀ c : primaryFactors (Matrix.toLin' (a : Matrix (Fin 4) (Fin 4) K)),
      mult (Matrix.toLin' (a : Matrix (Fin 4) (Fin 4) K)) c ≤ 4 := fun c => by
    have := primaryMultiplicity_le_finrank hsq c
    simpa using this
  have hmult : ∀ i : {c : primaryFactors (Matrix.toLin' (a : Matrix (Fin 4) (Fin 4) K)) //
      2 ≤ mult (Matrix.toLin' (a : Matrix (Fin 4) (Fin 4) K)) c},
      ¬ p ∣ mult (Matrix.toLin' (a : Matrix (Fin 4) (Fin 4) K)) i.1 := fun i =>
    Nat.not_dvd_of_pos_of_lt (by have := i.2; omega) (by have := hmultle i.1; omega)
  have hρ : ∀ i : {c : primaryFactors (Matrix.toLin' (a : Matrix (Fin 4) (Fin 4) K)) //
      2 ≤ mult (Matrix.toLin' (a : Matrix (Fin 4) (Fin 4) K)) c},
      ∀ u ∈ blockImage hsq i.1, LinearFlag.conjAut 4 K u = 1 → u = 1 := by
    intro i u hu hu1
    have hdetu : (u : Matrix (Fin 4) (Fin 4) K).det = 1 := by
      have := blockImage_le_range_toGL hsq hK4 i.1 i.2 hu
      rw [SpecialLinearGroup.range_toGL_eq_ker_det, MonoidHom.mem_ker] at this
      rw [← Matrix.GeneralLinearGroup.val_det_apply, this, Units.val_one]
    obtain ⟨c', hc'⟩ := (conjAut_eq_one_iff (by norm_num) u).1 hu1
    exact eq_one_of_scalar_det_one hdetu c' hc'.symm
  refine ⟨_, Q, hQH, hQc, hder, fun i => ?_⟩
  exact borelFacts_of_transport ψ hψ (LinearFlag.conjAut 4 K) (hmem i) (hFB i) (hρ i)
    (borelFactsGrp_blockImage hp h5 hpK hsq i.1 i.2 (hmultle i.1))

theorem layerBorel_rowOne {p : ℕ} {A : Subgroup G} {c : G} {L E : Subgroup G}
    (h15 : Sec15Hyp G p A c L E) (h13 : Sec13Facts G p A c L E)
    (hout : Outcome152One p E A (lieGenerated p E)) : LayerBorelData p E (lieGenerated p E) := by
  obtain ⟨f, hf, hpq, ⟨φ₀⟩, -, hEA, -⟩ := hout
  have h := h15.h12
  have hp := h.prime
  have h5 := Sec12Three.five_le h
  have hK : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  have hK4 : 4 ≤ Nat.card (GaloisField 2 f) := by
    have hpos : 0 < 2 ^ f - 1 := Nat.sub_pos_of_lt (Nat.one_lt_two_pow (by omega))
    have := Nat.le_of_dvd hpos hpq
    rw [hK]
    omega
  obtain ⟨φ, -⟩ : ∃ φ : ↥(lieGenerated p E) ≃* projectiveSL 4 (GaloisField 2 f), True :=
    ⟨φ₀.trans (projSLEquivProjectiveSL 4 (GaloisField 2 f)), trivial⟩
  have hpK : p ∣ Nat.card (GaloisField 2 f) - 1 := by rw [hK]; exact hpq
  exact (row1_lifts h h13 hEA hf φ).elim fun B hB =>
    layerBorel_of_lifts hp h5 hK4 hpK (E_le_normalizer_lieGenerated hp) φ B hB.1 hB.2.1 hB.2.2.1

theorem kf158BlocksBorel_of_sec13 (hS13 : Sec13Avail) : KF158BlocksBorel := by
  intro G _ _ p A c L E h15 hF hout b hb hb1 Y hY0 hYb hYI
  rcases hout with h1 | h2 | h3
  · have hnot5 : ¬ Outcome152Five p E A (lieGenerated p E) := by
      obtain ⟨-, -, -, -, -, hEA, -⟩ := h1
      rintro ⟨-, -, -, -, -, -, hne, -⟩
      exact hne hEA
    have h13 := hS13 G p A c L E h15.h12 hnot5
    obtain ⟨ι, Q, hQH, hQc, hder, hB⟩ := layerBorel_rowOne h15 h13 h1 b hb hb1
    have hYC : Y ≤ Subgroup.centralizer ({b} : Set G) := (mem_thetaComponentsAt_iff.mp hYb).1
    obtain ⟨i, rfl⟩ := eq_component_of_mem_thetaComponentsAt h15.h12.prime inf_le_right Q hQH hQc
      hder hYb (le_inf hYI hYC)
    exact hB i
  · exact kf158BlocksBorel_two_three hS13 h15 (Or.inl h2) hb hb1 hYb hYI
  · exact kf158BlocksBorel_two_three hS13 h15 (Or.inr h3) hb hb1 hYb hYI

end Row

end CFSG.RankThree.PartOne.K159
