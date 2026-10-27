module

public import CFSG.LocalAnalysis.StandardType.GGLinCentBlock
public import CFSG.LocalAnalysis.StandardType.GGTableBLinear
public import CFSG.LocalAnalysis.StandardType.GGTriD4KnownInputs
public import CFSG.LocalAnalysis.StandardType.GGCentInnerDiagConcl
public import CFSG.LocalAnalysis.StandardType.GGNbrLangQ1CentLin
public import CFSG.LocalAnalysis.StandardType.GGNbrLangQ1TorLinLift
public import CFSG.LocalAnalysis.StandardType.GGTypeANbrKappaCard
public import CFSG.LocalAnalysis.StandardType.Marking
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnLinDict

public section

namespace CFSG.StandardType

open CFSG.Assembly

private theorem linCentCompLabel_card_eq_two_pow {K E : Type} [Field K] [Field E] [Algebra K E]
    [Finite K] [Finite E] [CharP K 2] : ∃ m : ℕ, Nat.card E = 2 ^ m := by
  have : CharP E 2 := (Algebra.charP_iff K E 2).mp inferInstance
  obtain ⟨m, -, hm⟩ := @FiniteField.card E _ (Fintype.ofFinite E) 2 _
  exact ⟨(m : ℕ), by rw [@Nat.card_eq_fintype_card E (Fintype.ofFinite E), hm]⟩

theorem exists_labelA_of_isComponentOf_centralizer_linear {d : ℕ} (hd : 2 ≤ d) {K : Type}
    [Field K] [Finite K] {n : ℕ} (hK : Nat.card K = 2 ^ n)
    {s : LargeEvenProj (LargeEvenSLGroup (Fin d) K)} (hs : Odd (orderOf s))
    {J : Subgroup (LargeEvenProj (LargeEvenSLGroup (Fin d) K))}
    (hJ : IsComponentOf J (Subgroup.centralizer {s})) :
    ∃ lab : LargeEvenLabel, lab.tag = .A ∧ LargeEvenInLambda2 lab ∧
      GGHasLabel lab (↥J ⧸ Subgroup.center ↥J) := by
  classical
  have : CharP K 2 := charP_two_of_card hK
  obtain ⟨a, ha⟩ := QuotientGroup.mk'_surjective
    (N := (LargeEvenScalars (Fin d) K).subgroupOf (LargeEvenSLGroup (Fin d) K)) s
  let A : GL (Fin d) K := (a : GL (Fin d) K)
  have hAmem : A ∈ LargeEvenSLGroup (Fin d) K := a.2
  have hlin : TableB.linConjAut (Fin d) K A = MulAut.conj s := by
    have h := TableB.linConjAut_of_mem (ι := Fin d) (K := K) A hAmem
    have hcoe : ((⟨A, hAmem⟩ : LargeEvenSLGroup (Fin d) K) :
        LargeEvenProj (LargeEvenSLGroup (Fin d) K)) = s := by
      simpa [LargeEvenProjMk] using ha
    rwa [hcoe] at h
  have hcentral : ggAutFixedSubgroup (MulAut.conj s) =
      Subgroup.centralizer ({s} : Set (LargeEvenProj (LargeEvenSLGroup (Fin d) K))) :=
    ggAutFixedSubgroup_mulAut_conj s
  have hJopen : CFSG.Open.IsComponentOf J
      (ggAutFixedSubgroup (TableB.linConjAut (Fin d) K A)) := by
    rw [hlin, hcentral]
    exact (CFSG.Assembly.isComponentOf_iff_open).1 hJ
  have hodd : Odd (orderOf (TableB.linConjAut (Fin d) K A)) := by
    rw [hlin]
    exact hs.of_dvd_nat (orderOf_map_dvd (MulAut.conj :
      LargeEvenProj (LargeEvenSLGroup (Fin d) K) →*
        MulAut (LargeEvenProj (LargeEvenSLGroup (Fin d) K))) s)
  have hAodd : Odd (orderOf A) := q1CentLin_odd_orderOf A hodd
  obtain ⟨C, hC, hCSL, hJeq⟩ := q1TorLin_component_lift hd A J hJopen
  obtain ⟨b, E, hEf, hEalg, hEfin, hb, ⟨φ⟩⟩ :=
    linCentComp_block A hAodd C hC hCSL J hJeq
  let : Field E := hEf
  let : Finite E := hEfin
  let : Algebra K E := hEalg
  obtain ⟨m, hm⟩ := linCentCompLabel_card_eq_two_pow (K := K) (E := E)
  have : IsSimpleGroup (↥J ⧸ Subgroup.center ↥J) := hJ.2.2.2
  have hmodel : CFSG.Open.StatedClassicalModel (↥J ⧸ Subgroup.center ↥J) .PSL b 2 m :=
    CFSG.LocalAnalysis.GLTheoremA.Y10GInnLin.statedClassicalModel_psl_of_isSimpleGroup hb hm φ
  have hmodel' : CFSG.Open.StatedClassicalModel (↥J ⧸ Subgroup.center ↥J) .PSL
      ((b - 1) + 1) 2 m := by
    simpa [Nat.sub_add_cancel (by omega : 1 ≤ b)] using hmodel
  exact ⟨⟨.A, b - 1, m⟩, rfl, largeEvenInLambda2_typeA hmodel', ggHasLabel_typeA hmodel'⟩

end CFSG.StandardType

end
