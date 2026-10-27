module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight91D4Model
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight91D4SU32
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight91D4Bridge
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.ExtraspecialTransport
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.SmallD4Par

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.RankThreeUC.SmallClassTwoGroups (IsExtraspecialExpP)
open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.UC22.F08
open CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4

@[expose] def R891AutConcl {X : Type} [Group X] [Finite X] (n : ℕ) (α : MulAut X) : Prop :=
  (2 ≤ n → ⁅DerInf8 (R891Fix α), DerInf8 (R891Fix α)⁆ = DerInf8 (R891Fix α) ∧
      (IsG2 ↥(DerInf8 (R891Fix α)) n ∨ R891SL3Two ↥(DerInf8 (R891Fix α)) n ∨
        R891L3Pi ↥(DerInf8 (R891Fix α)) n)) ∧
    (n = 1 → ⁅R891Odd (Opp 2 (R891Fix α)), Opp 2 (R891Fix α)⁆ = R891Odd (Opp 2 (R891Fix α)) ∧
      (IsExtraspecialExpP 3 1 ↥(R891Odd (Opp 2 (R891Fix α))) ∨
        R891E9 ↥(R891Odd (Opp 2 (R891Fix α)))) ∧
      ∀ W : Subgroup X, W ≤ R891Odd (Opp 2 (R891Fix α)) →
        W.relIndex (R891Odd (Opp 2 (R891Fix α))) = 3 →
          ¬ ∀ k ∈ Opp 2 (R891Fix α), W.map (MulAut.conj k).toMonoidHom = W)

private lemma r891_dvd_pow_six_sub_one {n p : ℕ}
    (h3n : (2 : ℤ) ^ (3 * n) ≡ -R891Pi n [ZMOD p]) : p ∣ (2 ^ n) ^ 6 - 1 := by
  have hpi2 : (-R891Pi n) ^ 2 = 1 := by
    rw [R891Pi, neg_sq, ← pow_mul]
    exact Even.neg_one_pow ⟨n, by ring⟩
  have h3n' : ((2 : ℤ) ^ n) ^ 3 ≡ -R891Pi n [ZMOD p] := by
    rw [show 3 * n = n * 3 by omega, pow_mul] at h3n
    exact h3n
  have hsq : (((2 : ℤ) ^ n) ^ 3) ^ 2 ≡ 1 [ZMOD p] := by
    simpa [hpi2] using Int.ModEq.pow 2 h3n'
  have hdvdz : (p : ℤ) ∣ (((2 : ℤ) ^ n) ^ 3) ^ 2 - 1 := by
    have h := Int.modEq_iff_dvd.mp hsq
    have h' : (p : ℤ) ∣ -(1 - (((2 : ℤ) ^ n) ^ 3) ^ 2) := dvd_neg.mpr h
    simpa [neg_sub] using h'
  have hpos : 1 ≤ ((2 ^ n) ^ 3) ^ 2 := by
    have : 0 < ((2 ^ n) ^ 3) ^ 2 := by positivity
    omega
  have hcast : ((((2 ^ n) ^ 3) ^ 2 - 1 : ℕ) : ℤ) = (((2 : ℤ) ^ n) ^ 3) ^ 2 - 1 := by
    rw [Nat.cast_sub hpos]
    push_cast
    ring
  have hnat : p ∣ ((2 ^ n) ^ 3) ^ 2 - 1 := by
    rw [← Int.natCast_dvd_natCast]
    rw [hcast]
    exact hdvdz
  rw [show (2 ^ n) ^ 6 = ((2 ^ n) ^ 3) ^ 2 by ring]
  exact hnat

private lemma r891AutConcl_conj_odd_one {X : Type} [Group X] [Finite X] {n : ℕ} (hX : Is3D4 X n)
    {p : ℕ} (h3n : (2 : ℤ) ^ (3 * n) ≡ -R891Pi n [ZMOD p]) {x : X} (_hx3 : x ^ 3 = 1) (_hx1 : x ≠ 1)
    (_hpx : ¬ p ∣ Nat.card (R891Fix (MulAut.conj x))) (hn1 : n = 1)
    (R : Subgroup X) (_hxR : x ∈ R) (hRle : R ≤ R891Fix (MulAut.conj x))
    (hcomm : ∀ a ∈ R891Fix (MulAut.conj x), ∀ b ∈ R891Fix (MulAut.conj x),
      a * b * a⁻¹ * b⁻¹ ∈ R)
    (hOdd : Odd n) (Ω : Type) [hField : Field Ω] [hAlg : IsAlgClosed Ω] [hChar : CharP Ω 2]
    (U : Subgroup (GL (Fin 3) Ω))
    (hU : (U : Set (GL (Fin 3) Ω)) = CFSG.RankThree.Classical2.unitarySet (2 ^ n) 3)
    (eU : ↥R ≃* ↥U)
    (hUinfo : 2 ≤ n → CFSG.IsQuasisimple ↥R ∧
      ∀ y : ↥R, y ∈ center ↥R ↔ ∃ μ : Ω,
        (((eU y : ↥U) : GL (Fin 3) Ω) : Matrix (Fin 3) (Fin 3) Ω) = Matrix.scalar (Fin 3) μ) :
    ⁅R891Odd (Opp 2 (R891Fix (MulAut.conj x))), Opp 2 (R891Fix (MulAut.conj x))⁆ =
        R891Odd (Opp 2 (R891Fix (MulAut.conj x))) ∧
      (IsExtraspecialExpP 3 1 ↥(R891Odd (Opp 2 (R891Fix (MulAut.conj x)))) ∨
        R891E9 ↥(R891Odd (Opp 2 (R891Fix (MulAut.conj x))))) ∧
      ∀ W : Subgroup X, W ≤ R891Odd (Opp 2 (R891Fix (MulAut.conj x))) →
        W.relIndex (R891Odd (Opp 2 (R891Fix (MulAut.conj x)))) = 3 →
          ¬ ∀ k ∈ Opp 2 (R891Fix (MulAut.conj x)), W.map (MulAut.conj k).toMonoidHom = W := by
  subst hn1
  have hU' : (U : Set (GL (Fin 3) Ω)) = CFSG.RankThree.Classical2.unitarySet (2 ^ 1) 3 := hU
  obtain ⟨F, hField, hFinite, hF4, ⟨eS⟩⟩ := exists_mulEquiv_statedSU_two hU'
  let e : ↥R ≃* ↥(StatedSU 3 2 F) := eU.trans eS
  obtain ⟨E₀, hcore₀, hE₀⟩ := exists_oddCore_statedSU_two hF4
  let E : Subgroup X := (E₀.comap e.toMonoidHom).map R.subtype
  have htop : (⊤ : Subgroup ↥R).map R.subtype = R := by
    rw [Subgroup.map_top, Subgroup.range_subtype]
  have hcore : R891OddCore R E := by
    have h := R891OddCore.comap_map e hcore₀
    rw [Subgroup.comap_top, htop] at h
    simpa [E] using h
  have hmain := r891Odd_opp_eq_of_oddCore hRle hcomm hcore
  rcases hmain with ⟨hodd, hcomm', hnorm⟩
  obtain ⟨φ⟩ := nonempty_mulEquiv_comap_map e E₀
  have hE : IsExtraspecialExpP 3 1 ↥E := isExtraspecialExpP_of_mulEquiv φ hE₀
  constructor
  · rw [hodd]
    exact hcomm'
  · constructor
    · rw [hodd]
      exact Or.inl hE
    · intro W hW hrel
      rw [hodd] at hW hrel
      exact hnorm W hW hrel

private lemma r891AutConcl_outer_one {X : Type} [Group X] [Finite X] {n : ℕ} (hX : Is3D4 X n)
    {p : ℕ} (h3n : (2 : ℤ) ^ (3 * n) ≡ -R891Pi n [ZMOD p]) {α : MulAut X} (_hα3 : α ^ 3 = 1)
    (_hout : α ∉ (MulAut.conj : X →* MulAut X).range) (_hpα : ¬ p ∣ Nat.card (R891Fix α))
    (hn1 : n = 1) (π : Bool) (F : Type) [hField : Field F] [hFinite : Finite F]
    (hPi : Sec4.PiField π 2 n F)
    (hc : cond π (Even n) (Odd n))
    (ePGL : ↥(R891Fix α) ≃* ↥(CFSG.PGLModel.projImage (Sec4.glPi π 3 (2 ^ n) F))) :
    ⁅R891Odd (Opp 2 (R891Fix α)), Opp 2 (R891Fix α)⁆ = R891Odd (Opp 2 (R891Fix α)) ∧
      (IsExtraspecialExpP 3 1 ↥(R891Odd (Opp 2 (R891Fix α))) ∨
        R891E9 ↥(R891Odd (Opp 2 (R891Fix α)))) ∧
      ∀ W : Subgroup X, W ≤ R891Odd (Opp 2 (R891Fix α)) →
        W.relIndex (R891Odd (Opp 2 (R891Fix α))) = 3 →
          ¬ ∀ k ∈ Opp 2 (R891Fix α), W.map (MulAut.conj k).toMonoidHom = W := by
  subst hn1
  have hπ : π = false := by
    cases π
    · rfl
    · exfalso
      simp [Nat.not_even_one] at hc
  subst hπ
  have hpow : 2 ^ 1 = 2 := by norm_num
  have ePGL' : ↥(R891Fix α) ≃* ↥(CFSG.PGLModel.projImage (Sec4.glPi false 3 2 F)) := by
    simpa [hpow] using ePGL
  have hF4 : Nat.card F = 4 := by
    rw [hPi.card]
    simp [piCard, pow_one]
  obtain ⟨R₀, E₀, hc₀, hcore₀, hE₀⟩ := exists_oddCore_pgu_two hF4
  let R : Subgroup X := (R₀.comap ePGL'.toMonoidHom).map (R891Fix α).subtype
  let E : Subgroup X := (E₀.comap ePGL'.toMonoidHom).map (R891Fix α).subtype
  have hcore : R891OddCore R E := by
    simpa [R, E] using R891OddCore.comap_map ePGL' hcore₀
  have hRle : R ≤ R891Fix α := Subgroup.map_subtype_le _
  have hcomm : ∀ a ∈ R891Fix α, ∀ b ∈ R891Fix α, a * b * a⁻¹ * b⁻¹ ∈ R := by
    intro a ha b hb
    let a' : ↥(R891Fix α) := ⟨a, ha⟩
    let b' : ↥(R891Fix α) := ⟨b, hb⟩
    have hcomm' : a' * b' * a'⁻¹ * b'⁻¹ ∈ R₀.comap ePGL'.toMonoidHom := by
      rw [Subgroup.mem_comap]
      simpa [map_mul, map_inv] using hc₀ (ePGL' a') (ePGL' b')
    rw [Subgroup.mem_map]
    refine ⟨a' * b' * a'⁻¹ * b'⁻¹, hcomm', ?_⟩
    simp [a', b', Subgroup.subtype_apply]
  have hmain := r891Odd_opp_eq_of_oddCore hRle hcomm hcore
  rcases hmain with ⟨hodd, hcomm', hnorm⟩
  obtain ⟨φ⟩ := nonempty_mulEquiv_comap_map ePGL' E₀
  have hE : R891E9 ↥E := R891E9.of_mulEquiv φ.symm hE₀
  constructor
  · rw [hodd]
    exact hcomm'
  · constructor
    · rw [hodd]
      exact Or.inr hE
    · intro W hW hrel
      rw [hodd] at hW hrel
      exact hnorm W hW hrel


theorem r891AutConcl_conj {X : Type} [Group X] [Finite X] {n : ℕ} (hX : Is3D4 X n) {p : ℕ}
    (h3n : (2 : ℤ) ^ (3 * n) ≡ -R891Pi n [ZMOD p]) {x : X} (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1)
    (hpx : ¬ p ∣ Nat.card (R891Fix (MulAut.conj x))) : R891AutConcl n (MulAut.conj x) := by
  have hFix : R891Fix (MulAut.conj x) = Subgroup.centralizer ({x} : Set X) := by
    ext y
    simp only [R891Fix, MonoidHom.eqLocus]
    rw [Subgroup.mem_centralizer_singleton_iff]
    rw [eq_comm]
    exact mul_inv_eq_iff_eq_mul
  have hp6 : p ∣ (2 ^ n) ^ 6 - 1 := r891_dvd_pow_six_sub_one h3n
  rcases r891_three_classes hX hx3 hx1 with ⟨S, hSle, hScard⟩ | ⟨R, hxR, hRle, hcomm, hRtype⟩
  ·
    have hSleFix : S ≤ R891Fix (MulAut.conj x) := by rwa [hFix]
    have hdiv : Nat.card S ∣ Nat.card (R891Fix (MulAut.conj x)) := Subgroup.card_dvd_of_le hSleFix
    have hpS : p ∣ Nat.card S := by
      rw [hScard, show ((2 ^ n) ^ 3) ^ 2 = (2 ^ n) ^ 6 by ring, mul_comm]
      exact dvd_mul_of_dvd_left hp6 _
    exact (hpx (dvd_trans hpS hdiv)).elim
  ·
    have hRleFix : R ≤ R891Fix (MulAut.conj x) := by rwa [hFix]
    have hcommFix : ∀ a ∈ R891Fix (MulAut.conj x), ∀ b ∈ R891Fix (MulAut.conj x),
        a * b * a⁻¹ * b⁻¹ ∈ R := by rwa [← hFix] at hcomm
    rcases hRtype with ⟨hEven, hRq, F, hField, hFinite, hFcard, ⟨eSL⟩⟩ |
      ⟨hOdd, Ω, hField, hAlg, hChar, U, hU, eU, hUinfo⟩
    ·
      constructor
      · intro hn2
        have hRperfect : ⁅R, R⁆ = R := Subgroup.isPerfect_iff.mp hRq.1
        have hDer : DerInf8 (R891Fix (MulAut.conj x)) = R :=
          derInf8_eq_of_perfect hRleFix hRperfect hcommFix
        constructor
        · rw [hDer]
          exact hRperfect
        · rw [hDer]
          right; left; right; left
          exact ⟨hn2, hEven, threeCover_psl3_of_mulEquiv hn2 hEven hFcard hRq eSL⟩
      · intro hn1
        rw [hn1] at hEven
        norm_num at hEven
    ·
      constructor
      · intro hn2
        have hRq' : CFSG.IsQuasisimple ↥R := (hUinfo hn2).1
        have hRperfect : ⁅R, R⁆ = R := Subgroup.isPerfect_iff.mp hRq'.1
        have hDer : DerInf8 (R891Fix (MulAut.conj x)) = R :=
          derInf8_eq_of_perfect hRleFix hRperfect hcommFix
        constructor
        · rw [hDer]
          exact hRperfect
        · rw [hDer]
          right; left; right; right
          exact ⟨hn2, hOdd, threeCover_psu3_of_mulEquiv hn2 hOdd hU hRq' eU⟩
      · intro hn1
        exact r891AutConcl_conj_odd_one (hField := hField) (hAlg := hAlg) (hChar := hChar)
          hX h3n hx3 hx1 hpx hn1 R hxR hRleFix hcommFix hOdd Ω U hU eU hUinfo

theorem r891AutConcl_outer {X : Type} [Group X] [Finite X] {n : ℕ} (hX : Is3D4 X n) {p : ℕ}
    (h3n : (2 : ℤ) ^ (3 * n) ≡ -R891Pi n [ZMOD p]) {α : MulAut X} (hα3 : α ^ 3 = 1)
    (hout : α ∉ (MulAut.conj : X →* MulAut X).range) (hpα : ¬ p ∣ Nat.card (R891Fix α)) :
    R891AutConcl n α := by
  have hp6 : p ∣ (2 ^ n) ^ 6 - 1 := r891_dvd_pow_six_sub_one h3n
  rcases r891_outer_cases hX hα3 hout with hG2 | ⟨π, F, hField, hFinite, hPi, hc, ⟨ePGL⟩⟩
  ·
    have hpG2 : p ∣ ordG2 (2 ^ n) := by
      rw [show ordG2 (2 ^ n) = ((2 ^ n) ^ 6 - 1) * ((2 ^ n) ^ 6) * ((2 ^ n) ^ 2 - 1) by
        unfold ordG2; ring]
      exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left hp6 _) _
    rw [hG2] at hpα
    exact (hpα hpG2).elim
  ·
    constructor
    · intro hn2
      let P := CFSG.PGLModel.projImage (Sec4.glPi π 3 (2 ^ n) F)
      have hL3Pi : R891L3Pi ↥⁅P, P⁆ n :=
        (r891L3Pi_commutator_projImage hn2 hPi hc).2
      have hPerf : ⁅⁅P, P⁆, ⁅P, P⁆⁆ = ⁅P, P⁆ :=
        (r891L3Pi_commutator_projImage hn2 hPi hc).1
      have hDerP : DerInf8 P = ⁅P, P⁆ :=
        derInf8_eq_of_perfect (Subgroup.commutator_le.2 (fun a ha b hb => by
          have h1 : a * b ∈ P := Subgroup.mul_mem P ha hb
          have h2 : a * b * a⁻¹ ∈ P := Subgroup.mul_mem P h1 (Subgroup.inv_mem P ha)
          exact Subgroup.mul_mem P h2 (Subgroup.inv_mem P hb))) hPerf
          (fun a ha b hb => Subgroup.commutator_mem_commutator ha hb)
      have hL3Pi' : R891L3Pi ↥(DerInf8 P) n := by
        rwa [hDerP]
      have eDer : ↥(DerInf8 P) ≃* ↥(DerInf8 (R891Fix α)) :=
        (nonempty_derInf8_mulEquiv ePGL).some.symm
      have hL3Pi'' : R891L3Pi ↥(DerInf8 (R891Fix α)) n := R891L3Pi.of_mulEquiv eDer hL3Pi'
      constructor
      · exact commutator_derInf8_self (R891Fix α)
      · right; right
        exact hL3Pi''
    · intro hn1
      exact r891AutConcl_outer_one (hField := hField) (hFinite := hFinite)
        hX h3n hα3 hout hpα hn1 π F hPi hc ePGL

theorem r891AutCore_holds :
    ∀ (X : Type) [Group X] [Finite X] (n : ℕ), Is3D4 X n → ∀ p : ℕ, p.Prime → 5 ≤ p →
      ((2 : ℤ) ^ (3 * n) ≡ -R891Pi n [ZMOD p]) → ¬ ((2 : ℤ) ^ n ≡ -R891Pi n [ZMOD p]) →
      ∀ α : MulAut X, orderOf α = 3 → ¬ p ∣ Nat.card (R891Fix α) →
        (2 ≤ n → ⁅DerInf8 (R891Fix α), DerInf8 (R891Fix α)⁆ = DerInf8 (R891Fix α) ∧
          (IsG2 ↥(DerInf8 (R891Fix α)) n ∨ R891SL3Two ↥(DerInf8 (R891Fix α)) n ∨
            R891L3Pi ↥(DerInf8 (R891Fix α)) n)) ∧
        (n = 1 → ⁅R891Odd (Opp 2 (R891Fix α)), Opp 2 (R891Fix α)⁆ = R891Odd (Opp 2 (R891Fix α)) ∧
          (IsExtraspecialExpP 3 1 ↥(R891Odd (Opp 2 (R891Fix α))) ∨
            R891E9 ↥(R891Odd (Opp 2 (R891Fix α)))) ∧
          ∀ W : Subgroup X, W ≤ R891Odd (Opp 2 (R891Fix α)) →
            W.relIndex (R891Odd (Opp 2 (R891Fix α))) = 3 →
              ¬ ∀ k ∈ Opp 2 (R891Fix α), W.map (MulAut.conj k).toMonoidHom = W) := by
  intro X _ _ n hX p hp hp5 h3n hn3 α hα3 hpα
  by_cases hout : α ∈ (MulAut.conj : X →* MulAut X).range
  ·
    rcases hout with ⟨x, rfl⟩
    have hx3 : x ^ 3 = 1 := by
      have h : MulAut.conj (x ^ 3) = 1 := by
        rw [map_pow, ← hα3]
        exact pow_orderOf_eq_one (MulAut.conj x)
      have hcenter : x ^ 3 ∈ Subgroup.center X := by
        rw [Subgroup.mem_center_iff]
        intro g
        have hconj : MulAut.conj (x ^ 3) g = g := by rw [h]; rfl
        exact (mul_inv_eq_iff_eq_mul.mp hconj).symm
      rw [PartTwo.Inputs1719.Thm14_5.center_eq_bot_of_is3D4 hX] at hcenter
      simpa using hcenter
    have hx1 : x ≠ 1 := by
      intro hx
      rw [hx] at hα3
      simp at hα3
    exact r891AutConcl_conj hX h3n hx3 hx1 hpα
  ·
    have hα3' : α ^ 3 = 1 := by
      rw [← hα3]
      exact pow_orderOf_eq_one α
    exact r891AutConcl_outer hX h3n hα3' hout hpα

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
