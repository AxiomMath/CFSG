module

public import CFSG.RankThree.PartTwo.Sec15.Y4CoreProofTools
public import CFSG.RankThree.PartTwo.Sec16.Item165StepsProofThree
public import CFSG.RankThree.PartTwo.Sec15.Item1513StepsProofMax
public import CFSG.RankThree.PartTwo.Sec15.Item1520StepsProofDefs
public import CFSG.RankThree.PartTwo.Sec15.Item158Res2Proof159
import CFSG.RankThree.PartTwo.Sec14.Item147

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS

variable {G : Type} [Group G] [Finite G]

namespace Y4Core

omit [Finite G] in
theorem nonempty_of_le_sSup {Z : Subgroup G} (hO : oPrimeResidualOf 3 Z ≤ sSup (comp3In Z))
    (hne : oPrimeResidualOf 3 Z ≠ ⊥) : (comp3In Z).Nonempty := by
  by_contra hemp
  rw [Set.not_nonempty_iff_eq_empty] at hemp
  rw [hemp, sSup_empty] at hO
  exact hne (le_bot_iff.mp hO)

theorem exists_mem_scriptY0_normalizer (hRead : Y4CoreReadR) (hMem : Y4CoreMemR)
    {A L : Subgroup G} {c : G} (h : Sec15R G A c L) (hbot : ∃ B, IsHyperplane A B ∧ lB A B = ⊥)
    {Y : Subgroup G} (hY : Y ∈ scriptY3 A (lB A)) (hO : oPrimeResidualOf 3 Y ≠ ⊥) {w : G}
    (hwA : w ∈ Subgroup.normalizer (A : Set G)) (hwY : w ∈ Subgroup.normalizer (Y : Set G))
    {n : ℕ} (hn : Odd n) (hwn : w ^ n = 1) :
    ∃ J ∈ scriptY0 A (lB A), w ∈ Subgroup.normalizer (J : Set G) := by
  obtain ⟨hM2, hF, hYM⟩ := twoLocal_facts h.toSec14Std hY.1
  set M := Subgroup.normalizer (CFSG.Open.pCoreOf 2 Y : Set G) with hM
  have hwM : w ∈ Subgroup.normalizer (M : Set G) :=
    Subgroup.le_normalizer (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 Y hwY)
  have hwZ : w ∈ Subgroup.normalizer ((delta A (lB A) M : Subgroup G) : Set G) :=
    Proof159.mem_normalizer_delta hwA hwM
  obtain ⟨⟨J₁, J₂, hS⟩, hJ, hOle, -⟩ := exists_mem_scriptY0 hRead hMem h hbot hM2 hF
  have hne : oPrimeResidualOf 3 (delta A (lB A) M) ≠ ⊥ := fun h0 =>
    hO (le_bot_iff.mp (h0 ▸ oPrimeResidualOf_mono 3 (hY.2.le.trans (delta_mono hYM))))
  obtain ⟨J, hJ'⟩ := nonempty_of_le_sSup hOle hne
  exact ⟨J, (hJ J hJ').2, mem_normalizer_of_odd hS hwZ hn hwn hJ'⟩

end Y4Core

open Y4Core

theorem step1513MaxJ_of_core (hRead : Y4CoreReadR) (hMem : Y4CoreMemR) (hbot : Item145BotS14) :
    Step1513MaxJ := by
  intro G _ _ A c L a K hctx w hwKA hw3 _ T hT hI
  have h := hctx.toSec15R
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hTQ, hT1, hwT⟩ := hT.prop
  have hT2 : IsPGroup 2 T := isPGroup_of_mem_scriptQPi Nat.prime_two hTQ
  obtain ⟨hY3, -⟩ := Proof159Res2.delta_normalizer_mem_scriptY3 h.isSimpleGroup
    h.toSec13Data.card_eq hTQ.1.1 hT2 hT1
  have hwY := Proof159.mem_normalizer_delta hwKA.2 (Subgroup.le_normalizer hwT)
  exact exists_mem_scriptY0_normalizer hRead hMem h (hbot G A c L h.toSec14Std) hY3 hI hwKA.2
    hwY (by decide : Odd 3) hw3

@[expose] noncomputable def Step159ClaimKY0 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Ctx159 G A c L → ∀ w : G, IsW159 A L w → ∀ J ∈ scriptY0 A (lB A),
      w ∈ Subgroup.normalizer (J : Set G) →
        ∃ K ∈ scriptY0Star A (lB A), w ∈ Subgroup.normalizer (K : Set G) ∧
          ∃ F ∈ omegaA A, (F : Set G) = Late.sectionCentralizer A K (CFSG.Open.pCoreOf 2 K)

theorem step1520CoreComp_of_core (hRead : Y4CoreReadR) (hMem : Y4CoreMemR)
    (hbot : Item145BotS14) : Step1520CoreComp := by
  intro G _ _ A c L h Y _ p P hdata _ X hX hPX hPD hPO
  have hp : p.Prime := hdata.1
  have hp3 : 3 < p := hdata.2.1
  have hPp : IsPGroup p P := fun g => ⟨1, Subtype.ext (by
    simpa using hdata.2.2.2.1.2 g g.2)⟩
  have hbot' := hbot G A c L h.toSec14Std
  obtain ⟨hM2, hF, hXM⟩ := twoLocal_facts h.toSec14Std hX
  set M := Subgroup.normalizer (CFSG.Open.pCoreOf 2 X : Set G) with hM
  set Z := delta A (lB A) M with hZ
  obtain ⟨⟨J₁, J₂, hS⟩, hJ, -, hDZ⟩ := exists_mem_scriptY0 hRead hMem h hbot' hM2 hF
  have hZY : Z ∈ scriptY A := delta_mem_scriptY hM2.1
  have hΔXZ : delta A (lB A) X ≤ Z := delta_mono hXM
  have hPZ : P ≤ Z := hPD.trans ((deltaZero_le_delta X).trans hΔXZ)
  have hPD0 : P ≤ deltaZero A (lB A) Z :=
    hPD.trans ((deltaZero_mono hXM).trans (deltaZero_le_deltaZero_delta M))
  have hPR : ¬ P ≤ pPrimeCoreOf 3 Z := by
    intro hle
    apply hPO
    refine le_trans (le_inf hle (hPD.trans (deltaZero_le_delta X))) ?_
    refine le_pPrimeCoreOf inf_le_right ?_ ?_
    · exact (le_inf (hΔXZ.trans (le_normalizer_pPrimeCoreOf 3 Z)) Subgroup.le_normalizer).trans
        Subgroup.inf_normalizer_le_normalizer_inf
    · exact Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_left)
        (coprime_card_pPrimeCoreOf 3 Z)
  have hPN : ∀ J ∈ comp3In Z, P ≤ Subgroup.normalizer (J : Set G) := fun J hJ' =>
    le_normalizer_of_isPGroup hS hp (by omega) hPp (hPZ.trans Subgroup.le_normalizer) hJ'
  by_contra hne
  push Not at hne
  apply hPR
  have hZD : Z ≤ Subgroup.normalizer (deltaZero A (lB A) Z : Set G) := by
    have h145 := (rank3II_14_5_lB h.toSec14Std.isE27 hbot' hZY.2).2.2
    rw [show delta A (lB A) Z = Z from delta_delta M] at h145
    exact h145
  refine le_pPrimeCoreOf_of_commute (deltaZero_le Z) hZD hPD0 hp (by omega) hPp ?_
  intro x hx
  have hxZ : x ∈ Z := hPZ hx
  set R := pPrimeCoreOf 3 Z with hR
  have hRN : Z ≤ Subgroup.normalizer (R : Set G) := le_normalizer_pPrimeCoreOf 3 Z
  have hRZ : R ≤ Z := pPrimeCoreOf_le 3 Z
  let C : Subgroup G :=
    { carrier := {d | d ∈ Z ∧ x * d * x⁻¹ * d⁻¹ ∈ R}
      one_mem' := ⟨Z.one_mem, by simp⟩
      mul_mem' := by
        rintro d₁ d₂ ⟨hd₁, h₁⟩ ⟨hd₂, h₂⟩
        refine ⟨Z.mul_mem hd₁ hd₂, ?_⟩
        have h₂' : d₁ * (x * d₂ * x⁻¹ * d₂⁻¹) * d₁⁻¹ ∈ R :=
          (Subgroup.mem_normalizer_iff.mp (hRN hd₁) _).mp h₂
        have := R.mul_mem h₁ h₂'
        rwa [show x * d₁ * x⁻¹ * d₁⁻¹ * (d₁ * (x * d₂ * x⁻¹ * d₂⁻¹) * d₁⁻¹) =
          x * (d₁ * d₂) * x⁻¹ * (d₁ * d₂)⁻¹ by group] at this
      inv_mem' := by
        rintro d ⟨hd, h₁⟩
        refine ⟨Z.inv_mem hd, ?_⟩
        have := (Subgroup.mem_normalizer_iff.mp (hRN (Z.inv_mem hd)) _).mp (R.inv_mem h₁)
        rwa [show d⁻¹ * (x * d * x⁻¹ * d⁻¹)⁻¹ * d⁻¹⁻¹ = x * d⁻¹ * x⁻¹ * d⁻¹⁻¹ by group] at this }
  have hJC : ∀ J ∈ comp3In Z, J ≤ C := by
    intro J hJ' y hy
    refine ⟨le_of_mem_comp3In hJ' hy, ?_⟩
    have hsec := hne J (hJ J hJ').2 (hPN J hJ') hx
    exact open_pCoreOf_two_le_pPrimeCoreOf hJ'.1 (hsec.2 y hy)
  have hRC : R ≤ C := by
    intro r hr
    refine ⟨hRZ hr, ?_⟩
    exact R.mul_mem ((Subgroup.mem_normalizer_iff.mp (hRN hxZ) r).mp hr) (R.inv_mem hr)
  intro d hd
  exact (sup_le (sSup_le hJC) hRC (hDZ hd)).2

end CFSG.RankThree.PartTwo.Sec15

namespace CFSG.RankThree.PartTwo.Sec16

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15 CFSG.RankThree.PartTwo.Sec17
  CFSG.RankThree.LocalRank CFSG.GH74.GLS
open CFSG.RankThree.PartTwo.Sec15.Y4Core

variable {G : Type} [Group G] [Finite G]

theorem item1610_of_core (hRead : Y4CoreReadR) (hMem : Y4CoreMemR) {A : Subgroup G} {c : G}
    {L : Subgroup G} (h : Sec15R G A c L) (hbot : ∃ B, IsHyperplane A B ∧ lB A B = ⊥) :
    Item1610 A (lB A) := by
  intro h0
  ext Y
  refine ⟨fun hY => ⟨hY, ?_⟩, fun hY => hY.1⟩
  by_contra hO
  obtain ⟨J, hJ, -⟩ := exists_mem_scriptY0_normalizer hRead hMem h hbot hY hO
    (Subgroup.one_mem _) (Subgroup.one_mem _) (by decide : Odd 1) (one_pow 1)
  rw [h0] at hJ
  exact hJ

theorem res165R_of_core (hRead : Y4CoreReadR) (hMem : Y4CoreMemR) (hbot : Item145BotS14) :
    Res165R := by
  intro G _ _ A c L Y₀ h _ X hX _ _
  have hR := h.toSec15R
  have hX3 : X ∈ scriptY3 A (lB A) := hX.prop
  obtain ⟨hM2, hF, hXM⟩ := twoLocal_facts hR.toSec14Std hX3.1
  obtain ⟨-, hJ, hOle, -⟩ := exists_mem_scriptY0 hRead hMem hR (hbot G A c L hR.toSec14Std) hM2 hF
  refine (oPrimeResidualOf_mono 3 (hX3.2.le.trans (delta_mono hXM))).trans (hOle.trans ?_)
  refine sSup_le fun J hJ' => ?_
  obtain ⟨Y', hJY', hY'⟩ := Finite.exists_le_maximal (p := (· ∈ scriptY0 A (lB A))) (hJ J hJ').2
  rw [← h.eq_of_mem_y0Star hY']
  exact hJY'

end CFSG.RankThree.PartTwo.Sec16
