module

public import CFSG.LocalAnalysis.StandardType.GGNbrLangS1JInputs
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117
public import Certificates.Certificate2264
public import Certificates.Certificate2267
public import Certificates.Certificate8033
public import Certificates.Certificate8064
import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerMoreCl
import CFSG.LocalAnalysis.StandardType.MarkingClassical
import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotCatTypeDet
import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotCatTypeDet
import CFSG.LocalAnalysis.GLTheoremA.CatA.I91T5
import CFSG.LocalAnalysis.StandardType.GGTableBUnitarySixThreeCases

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

private theorem ggStdSubUnitaryAux_label_arith {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) {m d : ℕ}
    (h1 : markTag lab = .PSU) (h2 : markRank lab = d) (h3 : markDeg lab = m)
    (hc : markChar lab = 2) (hd4 : d ≠ 4) :
    lab.tag = .twA ∧ lab.rank = d - 1 ∧ lab.n = m := by
  obtain ⟨t, l, n⟩ := lab
  cases t
  case twA =>
    refine ⟨rfl, ?_, ?_⟩
    · have h := h2
      simp [markRank] at h
      change l = d - 1
      omega
    · have h := h3
      simp [markDeg] at h
      change n = m
      exact h
  case twD =>
    by_cases hl2 : l = 2
    · exact absurd h1 (by simp [markTag, hl2])
    · by_cases hl3 : l = 3
      · have h := h2
        simp [markRank, hl2, hl3] at h
        exact absurd h.symm hd4
      · exact absurd h1 (by simp [markTag, hl2, hl3])
  case G2der => exact absurd hc (by simp [markChar])
  case A => exact absurd h1 (by simp [markTag])
  case B => exact absurd h1 (by simp [markTag])
  case C => exact absurd h1 (by simp [markTag])
  case D =>
    by_cases h3l : l = 3
    · have h := h2
      simp [markRank, h3l] at h
      exact absurd h.symm hd4
    · exact absurd h1 (by simp [markTag, h3l])
  case E6 => exact absurd h1 (by simp [markTag])
  case E7 => exact absurd h1 (by simp [markTag])
  case E8 => exact absurd h1 (by simp [markTag])
  case F4 => exact absurd h1 (by simp [markTag])
  case twE6 => exact absurd h1 (by simp [markTag])
  case triD4 => exact absurd h1 (by simp [markTag])
  case G2 => exact absurd h1 (by simp [markTag])
  case twB2 => exact absurd h1 (by simp [markTag])
  case twF4 => exact absurd h1 (by simp [markTag])
  case B2der => exact absurd h1 (by simp [markTag])
  case twF4der => exact absurd h1 (by simp [markTag])

private theorem ggStdSubUnitaryAux_label
    {R_J : Type} [Group R_J] {lab_J : LargeEvenLabel} (hlab_J : LargeEvenInLambda2 lab_J)
    {m : ℕ} {d : ℕ} (hd : d = 3 ∨ d = 5 ∨ d = 6) (hd4 : d ≠ 4)
    (hdm : ¬ (d = 3 ∧ m = 1))
    (hMarked : MarkedModel lab_J R_J) (hPSU : CFSG.Blueprint.LieModel R_J .PSU d 2 m) :
    lab_J.tag = .twA ∧ lab_J.rank = d - 1 ∧ lab_J.n = m := by
  rcases hd with rfl | rfl | rfl
  · by_cases hc : markChar lab_J = 2
    · have hM' := NbrInnerMore.lieModel_of_markedModel_two hc hMarked
      obtain ⟨h1, h2, h3⟩ :=
        CFSG.LocalAnalysis.EvenBN.GMSK.su3EvenTypeDet R_J m (markTag lab_J) (markRank lab_J)
          (markDeg lab_J) hPSU
          (CFSG.SeitzReduction.F4Pilot.statedLieAdmissible_of_lieModel hM') hM'
      exact ggStdSubUnitaryAux_label_arith hlab_J h1 h2 h3 hc (by omega)
    · exact absurd hMarked
        (NbrInnerMore.not_markedModel_of_char_ne_two hPSU
          (by rintro ⟨-, h, -⟩; omega) (by rintro ⟨-, -, h⟩; exact hdm ⟨rfl, h⟩)
          (by rintro ⟨-, h, -⟩; omega) hc)
  · by_cases hc : markChar lab_J = 2
    · have hM' := NbrInnerMore.lieModel_of_markedModel_two hc hMarked
      obtain ⟨h1, h2, h3⟩ :=
        CFSG.SeitzReduction.UnitaryPilot.lieModel_PSU_two_unique_of_card_eq (m := 5)
          (by norm_num) hPSU hM' rfl
      exact ggStdSubUnitaryAux_label_arith hlab_J h1 h2 h3 hc (by omega)
    · exact absurd hMarked
        (NbrInnerMore.not_markedModel_of_char_ne_two hPSU
          (by rintro ⟨-, h, -⟩; omega) (by rintro ⟨-, h, -⟩; omega)
          (by rintro ⟨-, h, -⟩; omega) hc)
  · by_cases hc : markChar lab_J = 2
    · have hM' := NbrInnerMore.lieModel_of_markedModel_two hc hMarked
      obtain ⟨h1, h2, h3⟩ :=
        CFSG.SeitzReduction.TwistedE6Pilot.lieModel_PSU_six_two_unique hPSU hM'
      exact ggStdSubUnitaryAux_label_arith hlab_J h1 h2 h3 hc (by omega)
    · exact absurd hMarked
        (NbrInnerMore.not_markedModel_of_char_ne_two hPSU
          (by rintro ⟨-, h, -⟩; omega) (by rintro ⟨-, h, -⟩; omega)
          (by rintro ⟨-, h, -⟩; omega) hc)

private theorem ggStdSubUnitaryAux_mem_unitGroup_of_primeFormUnitary
    {K : Type} [Field K] {n d : ℕ}
    (h : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 n K)
    {P : GL (Fin d) K}
    (hP : P ∈ CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormUnitary h
      (CFSG.RankThree.PartOne.KCUnitaryModel.idGram K d)) :
    P ∈ TableB.unitGroup (ι := Fin d) h.bar := by
  rw [TableB.mem_unitGroup]
  rw [CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.mem_primeFormUnitary] at hP
  simpa [CFSG.RankThree.PartOne.KCUnitaryModel.idGram] using hP

theorem ggConfig_exists_abelianPreimage_psu {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} (hcfg : GGConfig p B Bs x L D J)
    (hID : GGInnerDiagOn Bs L) (hQ2U : GGBstarAbelianPreimageJUniS1Input)
    (hIDJ : GGInnerDiagOn Bs J) {d : ℕ} (hpd : (p = 3 ∧ (d = 3 ∨ d = 6)) ∨ (p = 5 ∧ d = 5))
    {E : Type} [Field E] {m : ℕ} (hE : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 m E)
    (hpm : p ∣ 2 ^ m + 1) (hdm : ¬ (d = 3 ∧ m = 1))
    (σ : ↥J ⧸ Subgroup.center ↥J ≃* LargeEvenProj (LargeEvenSUGroup (Fin d) E (2 ^ m))) :
    ∃ (E' : Type) (_ : Field E') (m' : ℕ)
      (hE' : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 m' E')
      (θJ : ↥J ⧸ Subgroup.center ↥J ≃* LargeEvenProj (LargeEvenSUGroup (Fin d) E' (2 ^ m')))
      (At : Subgroup ↥(TableB.unitGroup (ι := Fin d) hE'.bar)), IsMulCommutative At ∧
        ∀ b ∈ Bs, ∃ g ∈ At, ∀ j : ↥J, ∃ j' : ↥J, (j' : G) = b * (j : G) * b⁻¹ ∧
          θJ (QuotientGroup.mk j') =
            CFSG.HardMathSupport.C14Cl.uniConj hE' d g (θJ (QuotientGroup.mk j)) := by
  obtain ⟨hJperf, lab_J, hlab_J, hraw_J⟩ := hIDJ
  have hraw_marked := largeEvenRawDatum_markedModel hlab_J
    (Q := fun R _ I F => IsSimpleGroup R ∧ (∃ a b : R, a * b ≠ b * a) ∧
      ∃ θ : (↥J ⧸ Subgroup.center ↥J) ≃* R,
        Bs ≤ Subgroup.normalizer (J : Set G) ∧
          ∀ b ∈ Bs, ∃ φ ∈ I,
            LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ)
    (fun R _ I F hQ => hQ.2.1) hraw_J
  obtain ⟨R', _, I', F', hQ', hMM'⟩ := largeEvenRawDatum_exists hraw_marked
  obtain ⟨hs', hna', θ', hNJ', hhall'⟩ := hQ'
  have hMarkedCenter : MarkedModel lab_J (↥J ⧸ Subgroup.center ↥J) :=
    MarkedModel.of_mulEquiv θ'.symm hMM'
  have hd3 : 3 ≤ d := by
    rcases hpd with ⟨-, h | h⟩ | ⟨-, h⟩ <;> omega
  have hd : d = 3 ∨ d = 5 ∨ d = 6 := by
    rcases hpd with ⟨-, h | h⟩ | ⟨-, h⟩
    · exact Or.inl h
    · exact Or.inr (Or.inr h)
    · exact Or.inr (Or.inl h)
  have hne : (d, 2 ^ m) ≠ (3, 2) := by
    intro h
    have hd3' : d = 3 := congrArg Prod.fst h
    have h2m : 2 ^ m = 2 := congrArg Prod.snd h
    have hm1 : m = 1 :=
      Nat.pow_right_injective (le_refl 2) (h2m.trans (by norm_num : (2 : ℕ) = 2 ^ 1))
    exact hdm ⟨hd3', hm1⟩
  have hEadm : CFSG.Open.StatedLieAdmissible .PSU d 2 m :=
    ⟨Nat.prime_two, hE.one_le, hd3, hne⟩
  haveI : Finite E := hE.finite
  have hcardE : Nat.card E = (2 ^ m) ^ 2 := by
    rw [hE.card, ← pow_mul, Nat.mul_comm]
  have hSCM : CFSG.Open.StatedClassicalModel
      (LargeEvenProj (LargeEvenSUGroup (Fin d) E (2 ^ m))) .PSU d 2 m :=
    statedClassicalModel_unitary d m hcardE hEadm
  have hPSL0 : CFSG.Blueprint.LieModel
      (LargeEvenProj (LargeEvenSUGroup (Fin d) E (2 ^ m))) .PSU d 2 m :=
    Or.inl ⟨by decide, hSCM⟩
  have hPSLJ : CFSG.Blueprint.LieModel (↥J ⧸ Subgroup.center ↥J) .PSU d 2 m :=
    lieModel_of_mulEquiv' σ.symm hPSL0
  obtain ⟨hAtag, hArank, hAn⟩ :=
    ggStdSubUnitaryAux_label hlab_J hd (by omega) hdm hMarkedCenter hPSLJ
  have hlab_eq : lab_J = ⟨.twA, d - 1, m⟩ := by
    obtain ⟨t, l, n⟩ := lab_J
    dsimp only at hAtag hArank hAn
    subst hAtag
    subst hArank
    subst hAn
    rfl
  subst hlab_eq
  have hd1 : d - 1 + 1 = d := by omega
  dsimp only [CFSG.Assembly.LargeEvenRawDatumLegacy] at hraw_J
  rw [hd1] at hraw_J
  obtain ⟨K0, hK0field, hK0fin, hK0card, hQK⟩ := hraw_J
  obtain ⟨hs_J, hna_J, θ_J, hNJ, hhall_J⟩ := hQK
  have hE' : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 m K0 :=
    unitaryFieldData_of_card hE.one_le hK0card
  let At : Subgroup ↥(TableB.unitGroup (ι := Fin d) hE'.bar) :=
    (((ggBsAut hNJ).range).map (kgInducedAut θ_J)).comap (CFSG.HardMathSupport.C14Cl.uniConj hE' d)
  have hAt_comm : IsMulCommutative At :=
    hQ2U G p B Bs x L D J hcfg hID hNJ d m hpd hpm K0 hE' θ_J
  refine ⟨K0, hK0field, m, hE', θ_J, At, hAt_comm, ?_⟩
  intro b hb
  have hmem : ggLAut J θ_J ⟨b, hNJ hb⟩ ∈
      LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin d) K0 (2 ^ m)))
        (LargeEvenGUSet (Fin d) K0 (2 ^ m)) :=
    ggLAut_mem_of_induces J θ_J hNJ hhall_J hb
  obtain ⟨A, hAgu, hAeq⟩ :=
    TableB.exists_eq_projConj (TableBUE.gu_subset_normalizer (d := d) hE') hmem
  obtain ⟨u, hu⟩ := TableBU63.exists_unitary_of_gu hE' hAgu
  have huU : Matrix.GeneralLinearGroup.scalar (Fin d) u * A ∈
      TableB.unitGroup (ι := Fin d) hE'.bar :=
    ggStdSubUnitaryAux_mem_unitGroup_of_primeFormUnitary hE' hu
  let g : ↥(TableB.unitGroup (ι := Fin d) hE'.bar) :=
    ⟨Matrix.GeneralLinearGroup.scalar (Fin d) u * A, huU⟩
  have hgeq : CFSG.HardMathSupport.C14Cl.uniConj hE' d g =
      TableB.projConj (LargeEvenSUGroup (Fin d) K0 (2 ^ m))
        ⟨A, TableBUE.gu_subset_normalizer (d := d) hE' hAgu⟩ := by
    change TableB.projConj (LargeEvenSUGroup (Fin d) K0 (2 ^ m))
      ((Subgroup.inclusion (CFSG.HardMathSupport.C14Cl.uniGroup_le_normalizer hE')) g) = _
    have hz : Matrix.GeneralLinearGroup.scalar (Fin d) u ∈ LargeEvenScalars (Fin d) K0 := ⟨u, rfl⟩
    have hzN : Matrix.GeneralLinearGroup.scalar (Fin d) u ∈
        Subgroup.normalizer (LargeEvenSUGroup (Fin d) K0 (2 ^ m) : Set (GL (Fin d) K0)) :=
      TableB.scalar_mem_normalizer _ hz
    have hprod : ((Subgroup.inclusion (CFSG.HardMathSupport.C14Cl.uniGroup_le_normalizer hE')) g :
        Subgroup.normalizer (LargeEvenSUGroup (Fin d) K0 (2 ^ m) : Set (GL (Fin d) K0))) =
        ⟨Matrix.GeneralLinearGroup.scalar (Fin d) u, hzN⟩ *
        ⟨A, TableBUE.gu_subset_normalizer (d := d) hE' hAgu⟩ := by
      apply Subtype.ext
      rfl
    rw [hprod, map_mul, TableB.projConj_of_scalar _ hz, one_mul]
  refine ⟨g, ?_, ?_⟩
  · rw [Subgroup.mem_comap]
    rw [hgeq, ← hAeq]
    exact Subgroup.mem_map.mpr
      ⟨ggBsAut hNJ ⟨b, hb⟩, ⟨⟨b, hb⟩, rfl⟩, rfl⟩
  · intro j
    refine ⟨ggBsAut hNJ ⟨b, hb⟩ j, normalizerMonoidHom_coe J ⟨b, hNJ hb⟩ j, ?_⟩
    rw [hgeq, ← hAeq]
    exact (ggLAut_apply J θ_J ⟨b, hNJ hb⟩ j).symm

end CFSG.StandardType
