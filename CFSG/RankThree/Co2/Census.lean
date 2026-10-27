module

public import CFSG.RankThree.Co2.Classes
public import CFSG.RankThree.Co2.Syl
public import CFSG.RankThree.Co2.CensusCert
public import CFSG.RankThree.Co2.CrMat
public import Certificates.Certificate8101
public import Certificates.Certificate8102
public import Certificates.Certificate8108
public import Certificates.Certificate3014
public import Certificates.Certificate3017
public import Certificates.Certificate3019
public import Certificates.Certificate3025
public import Certificates.Certificate3026
public import Certificates.Certificate3028
public import Certificates.Certificate3054
public import Certificates.Certificate3055
public import Certificates.Certificate16022
public import Certificates.Certificate3114
public import Certificates.Certificate3115
public import Certificates.Certificate3116
public import Certificates.Certificate3117
public import Certificates.Certificate3138

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.RankThree.Co2

open CFSG.Monster CFSG.Monster.B.Co2 CFSG.Monster.B.Short CFSG.Monster.B.TwoA
  CFSG.Monster.B.TwoA.Census CFSG.Monster.B.TwoA.Co2Inv

theorem exists_isConj_rep (x : Cr) (hx : x * x = 1) (hx1 : x ≠ 1) :
    ∃ i < 10, IsConj x (rep i) := by
  obtain ⟨g, hg⟩ := exists_conj_mem_sylT x hx hx1
  set y := g * x * g⁻¹
  have hy : y * y = 1 := by
    calc y * y = g * (x * x) * g⁻¹ := by simp only [y]; group
      _ = 1 := by rw [hx]; group
  have hy1 : y ≠ 1 := by
    intro e
    apply hx1
    calc x = g⁻¹ * y * g := by simp only [y]; group
      _ = 1 := by rw [e]; group
  have hc : Nat.card (matGrp sylWords) ≤ 2 ^ 18 :=
    (card_matGrp_le sylWords_letters).trans (le_of_eq (by rw [card_sylT]; norm_num))
  have hm : crMat y ∈ matGrp sylWords := map_subW_le sylWords_letters ⟨y, hg, rfl⟩
  have hsq : crMat y * crMat y = 1 := by rw [← map_mul, hy, map_one]
  have hne : crMat y ≠ 1 := fun e => hy1 (crMat_injective (by rw [e, map_one]))
  obtain ⟨i, hi, h, hh, e⟩ := tInvFacts_cert hc _ hm hsq hne
  obtain ⟨h', rfl⟩ := MonoidHom.mem_mrange.1 (Cm_le_mrange hh)
  have e' : h' * rep i = y * h' := by
    apply crMat_injective
    simp only [map_mul]
    rw [crMat_rep hi]
    exact e
  refine ⟨i, hi, ?_⟩
  exact (isConj_iff.2 ⟨g, rfl⟩).trans (isConj_iff.2 ⟨h', by rw [e', mul_inv_cancel_right]⟩).symm

end CFSG.RankThree.Co2
