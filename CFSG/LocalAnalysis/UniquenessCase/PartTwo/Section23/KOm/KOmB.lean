module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.StatementsOmegaK
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KOm.MinusModel
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KOm.MinusCore
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KOm.RootGroupFix
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KOm.MinusSylow
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KOm.MinusInvol
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KOm.MinusWeyl
public import CFSG.GroupTheory.GL52.Basic
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.StatementsComponents
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.StatementsSL3
public import CFSG.LocalAnalysis.UniquenessCase.UC22S21b
public import CFSG.LocalAnalysis.UniquenessCase.UCFront07

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Matrix
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22.KOm
open CFSG.LieType.Universal.Spin
open CFSG.ClassicalGroups.Orthogonal (rootGroupGL)

local notation "ιM" => Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2

variable {K : Type} [Field K]

private theorem exists_model {W : Type} [CommGroup W] {e : W ≃* Multiplicative (ιM → K)}
    {T : Subgroup (GL ιM K)} {E : Subgroup (MulAut W)} (hE : E ≤ T.map (glPull e))
    (hEab : IsElemAbelian 2 E) :
    ∃ E' : Subgroup (GL ιM K), E' ≤ T ∧ E = E'.map (glPull e) ∧
      Nat.card ↥E = Nat.card ↥E' ∧
      Nat.card ↥(CFSG.Quasithin.fixV E) =
        Nat.card {v : ιM → K // ∀ g ∈ E', (g : Matrix ιM ιM K) *ᵥ v = v} ∧
      (∀ g ∈ E', g ^ 2 = 1) ∧ IsPGroup 2 ↥E' := by
  classical
  obtain ⟨E', hE'T, hEE'⟩ := exists_eq_map_glPull_of_le e hE
  have hcard : Nat.card ↥E = Nat.card ↥E' := by
    rw [hEE', Subgroup.card_map_of_injective (glPull_injective e)]
  have hfix : Nat.card ↥(CFSG.Quasithin.fixV E) =
      Nat.card {v : ιM → K // ∀ g ∈ E', (g : Matrix ιM ιM K) *ᵥ v = v} := by
    rw [hEE', card_fixV_map_glPull]
  have hexp : ∀ g ∈ E', g ^ 2 = 1 := by
    intro g hg
    have hmem : glPull e g ∈ E := by
      rw [hEE']
      exact Subgroup.mem_map_of_mem (glPull e) hg
    have h1 : glPull e (g ^ 2) = 1 := by
      rw [map_pow, hEab.2 (glPull e g) hmem]
    exact glPull_injective e (by simpa using h1)
  have h2 : IsPGroup 2 ↥E' := by
    intro g
    refine ⟨1, ?_⟩
    rw [pow_one]
    exact Subtype.ext
      (by simpa [Subgroup.coe_pow, Subgroup.coe_one] using hexp (g : GL ιM K) g.2)
  exact ⟨E', hE'T, hEE', hcard, hfix, hexp, h2⟩

private theorem not_le_rootGroupGL_of_weak [Finite K] {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {F : Subgroup (GL ιM K)} (hF1 : F ≠ ⊥)
    (hq : 4 ≤ Nat.card K)
    (hcard : Nat.card K ^ 4 ≤ 2 * (Nat.card ↥F *
      Nat.card {v : ιM → K // ∀ g ∈ F, (g : Matrix ιM ιM K) *ᵥ v = v})) :
    ¬ F ≤ rootGroupGL (quadMinus 2 K b c) (KTabC.e1M K) := by
  intro hFU
  have hQ : (QuadraticMap.polarBilin (quadMinus 2 K b c)).Nondegenerate :=
    nondegenerate_polarBilin_quadMinus_of_finite 2 K hirr
  have hle := card_mul_card_fix_le_of_le_rootGroupGL (ι := ιM) hQ (quadMinus_e1M b c)
    (e1M_ne_zero (K := K)) hFU hF1
  have hcardι : Fintype.card ιM = 4 := by simp
  have hle3 : Nat.card ↥F *
      Nat.card {v : ιM → K // ∀ g ∈ F, (g : Matrix ιM ιM K) *ᵥ v = v} ≤
        Nat.card K ^ 3 := by
    simpa [hcardι] using hle
  have hlt : 2 * Nat.card K ^ 3 < Nat.card K ^ 4 := by
    have h2 : 2 < Nat.card K := by omega
    calc 2 * Nat.card K ^ 3 < Nat.card K * Nat.card K ^ 3 :=
          Nat.mul_lt_mul_of_pos_right h2 (pow_pos (by omega) 3)
      _ = Nat.card K ^ 4 := by ring
  have hle2 : Nat.card K ^ 4 ≤ 2 * Nat.card K ^ 3 :=
    hcard.trans (Nat.mul_le_mul_left 2 hle3)
  exact (not_lt_of_ge hle2) hlt

theorem kOmB_holds : KOmB := by
  intro W _ _ H n S Tstar hF E hET hE hEne hcard
  obtain ⟨K, hKfield, hKfin, hKchar, b, c, hKcard, hirr, e, T, hH, hTstar, hTfix, hT2, -, hℓ⟩ :=
    exists_minusModel hF
  letI : Field K := hKfield
  letI : Finite K := hKfin
  letI : CharP K 2 := hKchar
  classical
  have hι : Nat.card ιM = 4 := by simp [Nat.card_eq_fintype_card, Fintype.card_sum]
  have hq : 4 ≤ Nat.card K := by
    rw [hKcard]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hF.1
  have hW : Nat.card W = Nat.card K ^ 4 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_congr Multiplicative.toAdd, Nat.card_fun, hι]
  have hEmap : E ≤ T.map (glPull e) := by rw [← hTstar]; exact hET
  obtain ⟨E', hE'T, hEE', hE'card, hE'fixcard, -, hE'2⟩ := exists_model (e := e) hEmap hE
  have hE'fix : E' ≤ isoFix (StatedQuadMinus 2 K b c) (KTabC.e1M K) := hE'T.trans hTfix
  have hE'ne : E' ≠ ⊥ := by
    intro hbot
    apply hEne
    refine Subgroup.eq_bot_of_card_eq E ?_
    rw [hE'card, show Nat.card ↥E' = 1 by rw [hbot, Subgroup.card_bot]]
  have hEweak : Nat.card K ^ 4 ≤ 2 * (Nat.card ↥E' *
      Nat.card {v : ιM → K // ∀ g ∈ E', (g : Matrix ιM ιM K) *ᵥ v = v}) := by
    calc Nat.card K ^ 4 = Nat.card W := hW.symm
      _ ≤ 2 * (Nat.card ↥E * Nat.card ↥(CFSG.Quasithin.fixV E)) := hcard
      _ = 2 * (Nat.card ↥E' *
            Nat.card {v : ιM → K // ∀ g ∈ E', (g : Matrix ιM ιM K) *ᵥ v = v}) := by
          rw [hE'card, hE'fixcard]
  have hE'U : ¬ E' ≤ rootGroupGL (quadMinus 2 K b c) (KTabC.e1M K) :=
    not_le_rootGroupGL_of_weak hirr hE'ne hq hEweak
  obtain ⟨t₀, ht₀E', ht₀U⟩ := SetLike.not_le_iff_exists.mp hE'U
  have hq4le : Nat.card K ^ 4 ≤ 4 * Nat.card K ^ 3 := by
    have hbound := card_mul_card_fix_le_two_mul (K := K) hirr hE'fix hE'2 hE'ne
    calc Nat.card K ^ 4 = Nat.card W := hW.symm
      _ ≤ 2 * (Nat.card ↥E * Nat.card ↥(CFSG.Quasithin.fixV E)) := hcard
      _ = 2 * (Nat.card ↥E' *
            Nat.card {v : ιM → K // ∀ g ∈ E', (g : Matrix ιM ιM K) *ᵥ v = v}) := by
          rw [hE'card, hE'fixcard]
      _ ≤ 2 * (2 * Nat.card K ^ 3) := Nat.mul_le_mul_left 2 hbound
      _ = 4 * Nat.card K ^ 3 := by ring
  have hK4 : Nat.card K = 4 := by
    have hKle : Nat.card K ≤ 4 := by
      have h' : Nat.card K ^ 3 * Nat.card K ≤ Nat.card K ^ 3 * 4 := by
        calc Nat.card K ^ 3 * Nat.card K = Nat.card K ^ 4 := by ring
          _ ≤ 4 * Nat.card K ^ 3 := hq4le
          _ = Nat.card K ^ 3 * 4 := by ring
      exact Nat.le_of_mul_le_mul_left h' (pow_pos Nat.card_pos 3)
    exact le_antisymm hKle hq
  have hn2 : n = 2 := by
    apply Nat.pow_right_injective (le_refl 2)
    show 2 ^ n = 2 ^ 2
    rw [← hKcard, hK4]
  have hTH : ¬ Tstar ≤ H := by
    intro hle
    have h1 : T.map (glPull e) ≤ (StatedOmega (StatedQuadMinus 2 K b c)).map (glPull e) := by
      rw [← hTstar, ← hH]
      exact hle
    have hTΩ : T ≤ StatedOmega (StatedQuadMinus 2 K b c) :=
      (Subgroup.map_le_map_iff_of_injective (glPull_injective e)).mp h1
    have hTU : T ≤ rootGroupGL (quadMinus 2 K b c) (KTabC.e1M K) :=
      le_rootGroupGL_of_le_statedOmega hirr hTΩ
        (fun g hg => (mem_isoFix.mp (hTfix hg)).2) hT2
    exact ht₀U (hTU (hE'T ht₀E'))
  obtain ⟨k, hk⟩ := hE'2 ⟨t₀, ht₀E'⟩
  have hk' : t₀ ^ 2 ^ k = 1 := by
    simpa [Subgroup.coe_pow, Subgroup.coe_one] using congrArg (fun x : ↥E' => (x : GL ιM K)) hk
  obtain ⟨a, ha0, ha⟩ := exists_planeBlock_mulVec_eq_self (hE'fix ht₀E') hk'
  have hpa0 : planeVec a ≠ 0 := by
    intro h0
    apply ha0
    funext i
    have h1 := congrFun h0 (Sum.inr (Sum.inr i))
    rw [planeVec_inr_inr] at h1
    simpa using h1
  set A₀ : Subgroup W := linePull e (planeVec a) with hA₀def
  have hA₀card : Nat.card ↥A₀ = 4 := by
    rw [hA₀def, card_linePull e hpa0, hK4]
  have hcentral : ∀ E₂ : Subgroup (MulAut W), E₂ ≤ Tstar → IsElemAbelian 2 E₂ →
      Nat.card W ≤ 2 * (Nat.card ↥E₂ * Nat.card ↥(CFSG.Quasithin.fixV E₂)) →
      A₀ ≤ CFSG.Quasithin.fixV E₂ := by
    intro E₂ hE₂T hE₂ab hE₂card
    obtain ⟨E₂', hE₂'T, hE₂E, hE₂'card, hE₂'fixcard, hE₂'exp, -⟩ :=
      exists_model (e := e) (by rw [← hTstar]; exact hE₂T) hE₂ab
    have hE₂weak : Nat.card K ^ 4 ≤ 2 * (Nat.card ↥E₂' *
        Nat.card {v : ιM → K // ∀ g ∈ E₂', (g : Matrix ιM ιM K) *ᵥ v = v}) := by
      calc Nat.card K ^ 4 = Nat.card W := hW.symm
        _ ≤ 2 * (Nat.card ↥E₂ * Nat.card ↥(CFSG.Quasithin.fixV E₂)) := hE₂card
        _ = 2 * (Nat.card ↥E₂' *
              Nat.card {v : ιM → K // ∀ g ∈ E₂', (g : Matrix ιM ιM K) *ᵥ v = v}) := by
            rw [hE₂'card, hE₂'fixcard]
    by_cases hbot : E₂' = ⊥
    · have hE₂bot : E₂ = ⊥ := by rw [hE₂E, hbot, Subgroup.map_bot]
      rw [hE₂bot]
      intro x _
      simp [CFSG.Quasithin.mem_fixV]
    · have hEU : ¬ E₂' ≤ rootGroupGL (quadMinus 2 K b c) (KTabC.e1M K) :=
        not_le_rootGroupGL_of_weak hirr hbot hq hE₂weak
      have hfixvec := mulVec_planeVec_eq_of_exponent_two hirr hTfix hT2 (hE'T ht₀E') ht₀U ha0 ha
        hE₂'T hE₂'exp hEU
      rw [hE₂E, hA₀def]
      exact linePull_le_fixV_map_glPull e hfixvec
  obtain ⟨h', hh'Ω, hh'fix, hh'move⟩ := exists_mem_statedOmega_fix_planeVec hirr ha0
  refine ⟨hn2, hTH, A₀, hA₀card, hcentral, glPull e h', ?_, ?_, ?_⟩
  · rw [hH]
    exact Subgroup.mem_map_of_mem (glPull e) hh'Ω
  · rw [hA₀def]
    exact map_glPull_linePull_of_mulVec_eq e hh'fix
  · rw [hℓ]
    exact map_glPull_linePull_ne e hh'move

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
