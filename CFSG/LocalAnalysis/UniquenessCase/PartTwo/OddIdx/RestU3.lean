module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.OddIdx.RestBase
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.OddIdx.RestU3Conj
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.I811.U3.RestEven
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.OddIdx.RestSl2
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9.R920OddQ7U3Levi
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9.R920OddQ7U3Iso
import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.OddIndex.U3OddModel
public import CFSG.StronglyEmbedded.BenderUnitaryBorel

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.OddIdx

open Subgroup
open CFSG.Blueprint (LieModel)
open Matrix CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits CFSG.LieType.Steinberg
open CFSG.AGLEmbeddingD2.McLaughlin.OddIndex

set_option linter.unusedSectionVars false

theorem oddIdxNone_su3_even {F : Type} [Field F] [Finite F] {f : ℕ} [CharP F 2]
    (hF : Nat.card F = (2 ^ f) ^ 2) (hq3 : 2 ^ f % 3 = 1)
    (hB : CFSG.Open.fusionBenderBorel (SU (unitaryInvolution F 2 f) 3) (2 ^ f) 3) :
    OddIdxNone (SU (unitaryInvolution F 2 f) 3) := by
  intro N Y D hN hodd hD hDY hYN hnorm hY hNK
  have hf0 : f ≠ 0 := by
    have := CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.I811.U3.one_le_f hF
    omega
  obtain ⟨ω, g, hω, hNW⟩ := oddIdxRest_su3_conj hF hq3 hf0 hD hnorm
  let W : Subgroup (SU (unitaryInvolution F 2 f) 3) := N.map (MulAut.conj g).toMonoidHom
  have hWodd : ¬ 2 ∣ W.index := by
    rw [show W = N.map (MulAut.conj g).toMonoidHom from rfl]
    rw [Subgroup.index_map_of_bijective (f := (MulAut.conj g).toMonoidHom)
      (MulAut.conj g).bijective N]
    obtain ⟨k, hk⟩ := hodd
    rintro ⟨m, hm⟩
    omega
  have hns : ¬ Group.IsSolvable ↥W := by
    intro hsol
    haveI : Group.IsSolvable ↥W := hsol
    haveI : Group.IsSolvable ↥N :=
      Group.isSolvable_of_isSolvable_injective
        (f := (N.equivMapOfInjective (MulAut.conj g).toMonoidHom
          (MulAut.conj g).injective).toMonoidHom) (MulEquiv.injective _)
    exact oddIdx_not_isSolvable hYN hY ‹Group.IsSolvable ↥N›
  have hWtop : W = ⊤ :=
    CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.I811.U3.eq_top_of_not_two_dvd_index
      hF hq3 hB hω hNW hWodd hns
  apply hN
  have hmap_top : N.map (MulAut.conj g).toMonoidHom = ⊤ := hWtop
  have hc := Subgroup.comap_map_eq_self_of_injective
    (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).injective N
  rw [hmap_top, Subgroup.comap_top] at hc
  exact hc.symm

theorem oddIdxNone_su3_odd {F : Type} [Field F] [Finite F]
    {p f : ℕ} [Fact p.Prime] [CharP F p] (hF : Nat.card F = (p ^ f) ^ 2) (hp2 : p ≠ 2)
    (hq3 : (p ^ f) % 3 = 1) (hf : 2 ≤ f) :
    OddIdxNone (SU (unitaryInvolution F p f) 3) := by
  intro N Y D hN hodd hD hDY hYN hnorm hY hNK
  have hf0 : f ≠ 0 := by omega
  obtain ⟨ω, g, hω, hNW⟩ := oddIdxRest_su3_conj hF hq3 hf0 hD hnorm
  let W : Subgroup (SU (unitaryInvolution F p f) 3) := N.map (MulAut.conj g).toMonoidHom
  have hNW' : normA0 hF ω ≤ W := hNW
  have hns : ¬ Group.IsSolvable ↥W := by
    intro hsol
    haveI : Group.IsSolvable ↥W := hsol
    haveI : Group.IsSolvable ↥N :=
      Group.isSolvable_of_isSolvable_injective
        (f := (N.equivMapOfInjective (MulAut.conj g).toMonoidHom
          (MulAut.conj g).injective).toMonoidHom) (MulEquiv.injective _)
    exact oddIdx_not_isSolvable hYN hY ‹Group.IsSolvable ↥N›
  have hKW : CFSG.KCore.KGroupNonab (DvdOrThreeFree 51840) ↥W :=
    CFSG.KCore.KGroupNonab.of_mulEquiv (isoInvariant_dvdOrThreeFree 51840) hNK
      (N.equivMapOfInjective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective).symm
  have hq13 : 13 ≤ p ^ f := by
    have hp3 : p ≠ 3 := by
      rintro rfl
      rw [Nat.pow_mod, Nat.mod_self, zero_pow (by omega : f ≠ 0)] at hq3
      norm_num at hq3
    have hp5 : 5 ≤ p := by
      obtain ⟨k, hk⟩ := (Fact.out : p.Prime).eq_two_or_odd'.resolve_left hp2
      have h2le : 2 ≤ p := (Fact.out : p.Prime).two_le
      have hk1 : k ≠ 1 := by
        intro h1
        exact hp3 (by omega)
      omega
    calc 13 ≤ 5 ^ 2 := by norm_num
      _ ≤ 5 ^ f := Nat.pow_le_pow_right (by norm_num) hf
      _ ≤ p ^ f := Nat.pow_le_pow_left hp5 f
  by_cases hbad : ∀ x ∈ W, x * zSU hF = zSU hF * x → x ∈ normA0 hF ω
  · exact hns
      (CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9.Q7U3.isSolvable_of_centralizer_le
        hF hp2 hω hq3 hNW' hbad)
  · push Not at hbad
    obtain ⟨x, hxW, hxz, hxN⟩ := hbad
    have hL :=
      CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9.Q7U3.range_embSU_le_of_not_bad
        hF hp2 hq3 hq13 hω hNW' hxW hxz hxN
    obtain ⟨ζ, hζ0, hζ⟩ := exists_unitaryInvolution_eq_neg hF
    have hW₁ : (levi hζ0 hζ).range ≤ W := by
      rw [range_levi hζ0 hζ]
      exact hL
    let φ : ↥((levi hζ0 hζ).range) →*
        Matrix.SpecialLinearGroup (Fin 2) (fixedSubfield F p f) :=
      (MonoidHom.ofInjective (levi_injective hζ0 hζ)).symm.toMonoidHom
    have hφ : Function.Surjective φ :=
      (MonoidHom.ofInjective (levi_injective hζ0 hζ)).symm.surjective
    have h4 : 4 ≤ Nat.card (fixedSubfield F p f) := by
      rw [CFSG.LieType.Steinberg.card_fixedSubfield hF]
      omega
    have h3 : ¬ 3 ∣ Nat.card (fixedSubfield F p f) := by
      rw [CFSG.LieType.Steinberg.card_fixedSubfield hF]
      intro hd
      have := Nat.mod_eq_zero_of_dvd hd
      omega
    have h45 := oddIdxRest_card_of_sl2_section hW₁ h4 h3 φ hφ hKW
    rw [CFSG.LieType.Steinberg.card_fixedSubfield hF] at h45
    omega

theorem oddIdxProp_psu3_rest {K : Type} [Group K] [Finite K]
    {p f : ℕ} (hrest : 2 ≤ f ∨ p = 2) (hq : p ^ f % 3 = 1) (hU : LieModel K .PSU 3 p f) :
    OddIdxProp K := by
  apply oddIdxProp_of_none
  have hmodel := hU.statedClassicalModel (by decide)
  haveI : Fact p.Prime := ⟨hmodel.1.1⟩
  obtain ⟨F, _, _, _, _, hF, ⟨e⟩⟩ := exists_mulEquiv_SU3 hmodel hq
  apply oddIdxNone_of_mulEquiv e
  by_cases hp2 : p = 2
  · subst p
    have hf2 : 2 ≤ f :=
      CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.I811.U3.two_le_f hF hq
    obtain ⟨eP⟩ :=
      CFSG.ComponentClassification.GMS78.nonempty_mulEquiv_psu3_of_stated hf2 hmodel
    haveI : Finite (CFSG.Open.PSU3 2 f) := Finite.of_equiv K eP.toEquiv
    have hB0 := CFSG.Open.bender_psu3_borel_full f hf2
    have hB := hB0.map_mulEquiv (eP.symm.trans e)
    exact oddIdxNone_su3_even hF hq hB
  · have hf : 2 ≤ f := by
      rcases hrest with hf | hp_eq
      · exact hf
      · exact absurd hp_eq hp2
    exact oddIdxNone_su3_odd hF hp2 hq hf

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.OddIdx
