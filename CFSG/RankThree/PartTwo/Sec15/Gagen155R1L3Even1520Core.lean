module

public import CFSG.RankThree.PartTwo.Sec15.Ronan154BigMem
import CFSG.RankThree.PartTwo.Sec14.Item147

public section

namespace CFSG.RankThree.PartTwo.Sec15.Res1Cover

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS
open Y4Core

theorem step1520CoreComp_of_at (hRead : Y4CoreReadR) (hbot : Item145BotS14)
    (hMem : ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
      Sec15R G A c L → ∀ Y, Ctx1514 A (lB A) c L Y → Ronan154Big.Y4CoreMemAt A) :
    Step1520CoreComp := by
  intro G _ _ A c L h Y ctx p P hdata _ X hX hPX hPD hPO
  have hp : p.Prime := hdata.1
  have hp3 : 3 < p := hdata.2.1
  have hPp : IsPGroup p P := fun g => ⟨1, Subtype.ext (by
    simpa using hdata.2.2.2.1.2 g g.2)⟩
  have hbot' := hbot G A c L h.toSec14Std
  obtain ⟨hM2, hF, hXM⟩ := twoLocal_facts h.toSec14Std hX
  set M := Subgroup.normalizer (CFSG.Open.pCoreOf 2 X : Set G) with hM
  set Z := delta A (lB A) M with hZ
  obtain ⟨⟨J₁, J₂, hS⟩, hJ, -, hDZ⟩ :=
    Ronan154Big.exists_mem_scriptY0_of_at hRead (hMem G A c L h Y ctx) h hbot' hM2 hF
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

end CFSG.RankThree.PartTwo.Sec15.Res1Cover
