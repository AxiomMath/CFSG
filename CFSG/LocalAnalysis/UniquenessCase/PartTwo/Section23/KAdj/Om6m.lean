module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KAdj.Concl
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23d.Defs
public import CFSG.LocalAnalysis.UniquenessCase.UC22S20
public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockOrthMinusCuts
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalTailModelCoordinates
public import CFSG.Open.StatedDefs

import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KAdj.ConjBack
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KAdj.SUOHinf
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KAdj.Om6mBorel
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KAdj.Om6mChar
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KAdj.Om6mAct
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KAdj.Om6mRoot
import CFSG.LocalAnalysis.UniquenessCase.UC22P21c
import CFSG.LocalAnalysis.UniquenessCase.UC22P22m
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ParabolicTransfer
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasFive
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalStandardFormsRegular
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalTailPolar
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalTailWeylLift
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.Monster.Code.Weights
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.Quasithin.Background.A4Defs
public import CFSG.Quasithin.Background.B1Restrict
public import CFSG.Quasithin.Background.B4Statement
public import CFSG.Quasithin.EmptyFaithful.Setting
public import CFSG.Sporadic.J4.Simple
public import CFSG.Sporadic.J4Base
public import CFSG.Sporadic.Mathieu.M12
public import CFSG.Sporadic.Mathieu.M24
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.ComplementTransfer
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public import Certificates.Certificate43

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.KAdjE

open CFSG.Open
open CFSG.AGLEmbedding.LeviBlock (orthParab)
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail
open KTabD (lineStab)

theorem om6m_odd_of_hr {n r : ℕ}
    (hr : (∃ s : ℕ, s ∣ n ∧ Odd s ∧ 1 < s ∧ r ∣ 2 ^ s - 1) ∨ (∃ k : ℕ, n = 2 ^ k ∧ r = 3)) :
    Odd r := by
  rcases hr with ⟨s, -, -, hs1, hrdvd⟩ | ⟨k, -, hr3⟩
  · have hEven : Even (2 ^ s) := even_two.pow_of_ne_zero (by omega)
    have h1le : 1 ≤ 2 ^ s := by have := Nat.two_pow_pos s; omega
    have hodd : Odd (2 ^ s - 1) :=
      (Nat.odd_sub' h1le).mpr ⟨fun _ => hEven, fun _ => odd_one⟩
    have h2 : ¬ 2 ∣ r := fun h => hodd.not_two_dvd_nat (dvd_trans h hrdvd)
    exact Nat.not_even_iff_odd.mp fun he => h2 (even_iff_two_dvd.mp he)
  · rw [hr3]
    exact ⟨1, rfl⟩

private lemma kAdj_model_om6m_diag_D11 {K : Type} [Field K] [Finite K] [CharP K 2] {b c : K}
    {n : ℕ} (hK : Nat.card K = 2 ^ n) (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {s : Kˣ}
    {g : ↥(orthElementaryGroup (quadTail 2 (minusTailForm K b c)))}
    (hg : (g : ((Fin 2 ⊕ Fin 2 → K) × (Fin 2 → K)) ≃ₗ[K]
      ((Fin 2 ⊕ Fin 2 → K) × (Fin 2 → K))) = tailDiag 2 ![s, s⁻¹] 1) :
    KAdjConcl (Hinf (orthParab 2 (minusTailForm K b c) ![0, 1])) g (orderOf s) (2 * n) := by
  refine ⟨om6mX b c, om6mX b c, om6mX_le_hinf_orthParab hirr, om6mX_le_hinf_orthParab hirr,
    ?_, ?_⟩
  · intro N hN hnorm h₁ _
    exact om6m_normal_closure_om6mX hirr N hN hnorm h₁
  · rintro X (rfl | rfl)
    · obtain ⟨d, hdX, hdord, hdconj⟩ := om6m_exists_root_of_tailDiag hirr hg
      exact ⟨om6m_isSLn_om6mX hK hirr, om6m_mem_normalizer_om6mX hg, d, hdX, hdord, hdconj⟩
    · obtain ⟨d, hdX, hdord, hdconj⟩ := om6m_exists_root_of_tailDiag hirr hg
      exact ⟨om6m_isSLn_om6mX hK hirr, om6m_mem_normalizer_om6mX hg, d, hdX, hdord, hdconj⟩

theorem kAdj_model_om6m_tail {K : Type} [Field K] [Finite K] [CharP K 2] {b c : K} {n : ℕ}
    (hK : Nat.card K = 2 ^ n) (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {r : ℕ} (hr : Odd r)
    {t : ↥(orthElementaryGroup (quadTail 2 (minusTailForm K b c)))}
    (ht : t ∈ Hinf (orthParab 2 (minusTailForm K b c) ![0, 2]) ⊓
      orthParab 2 (minusTailForm K b c) ![0, 1])
    (hord : orderOf t = r) :
    KAdjConcl (Hinf (orthParab 2 (minusTailForm K b c) ![0, 1])) t r (2 * n) := by
  obtain ⟨htα, htQ⟩ := Subgroup.mem_inf.mp ht
  have htαQ : t ∈ orthParab 2 (minusTailForm K b c) ![0, 2] := uc22p21c_Hinf_le _ htα
  have htB : t ∈ (tailBorel 2 (minusTailForm K b c)).subgroupOf
      (orthElementaryGroup (quadTail 2 (minusTailForm K b c))) := by
    rw [← om6m_orthParab_inf_eq_tailBorel]
    exact Subgroup.mem_inf.mpr ⟨htQ, htαQ⟩
  have hodd : ¬ 2 ∣ orderOf t := by
    rw [hord]
    exact hr.not_two_dvd_nat
  obtain ⟨e, he, hconj⟩ := om6m_exists_conj_mem_tailTorus hirr htB hodd
  have heP : e ∈ orthParab 2 (minusTailForm K b c) ![0, 1] ⊓
      orthParab 2 (minusTailForm K b c) ![0, 2] := om6m_tailUnipotent_le_orthParab hirr he
  have ht'α : e * t * e⁻¹ ∈ Hinf (orthParab 2 (minusTailForm K b c) ![0, 2]) :=
    suo_conj_mem_hinf heP.2 htα
  obtain ⟨-, τ, k, -, hτk⟩ := mem_tailTorus.mp (Subgroup.mem_subgroupOf.mp hconj)
  obtain ⟨hprod, hk⟩ := om6m_tailDiag_of_mem_hinf hirr ht'α hτk.symm
  have hτ1 : τ 1 = (τ 0)⁻¹ := by
    have hmul : τ 0 * τ 1 = 1 := by
      apply Units.ext
      simpa using hprod
    exact eq_inv_of_mul_eq_one_right hmul
  have hτeq : τ = ![τ 0, (τ 0)⁻¹] := by
    funext i
    fin_cases i <;> simp [hτ1]
  have hg' : ((e * t * e⁻¹ : ↥(orthElementaryGroup (quadTail 2 (minusTailForm K b c)))) :
      ((Fin 2 ⊕ Fin 2 → K) × (Fin 2 → K)) ≃ₗ[K] ((Fin 2 ⊕ Fin 2 → K) × (Fin 2 → K))) =
      tailDiag 2 ![τ 0, (τ 0)⁻¹] 1 := by
    rw [← hτk, hk]
    exact congrArg (fun u => tailDiag 2 u 1) hτeq
  have ht'ord : orderOf (e * t * e⁻¹ : ↥(orthElementaryGroup
      (quadTail 2 (minusTailForm K b c)))) = orderOf t := by
    simpa [MulAut.conj_apply] using MulEquiv.orderOf_eq (MulAut.conj e) t
  have hs : orderOf (τ 0) = r :=
    (om6m_orderOf_eq_of_tailDiag hg').symm.trans (ht'ord.trans hord)
  have hmain : KAdjConcl (Hinf (orthParab 2 (minusTailForm K b c) ![0, 1]))
      (e * t * e⁻¹) r (2 * n) := by
    rw [← hs]
    exact kAdj_model_om6m_diag_D11 hK hirr hg'
  exact kAdjConcl_conj e
    (uc22p22m_le_normalizer_Hinf (orthParab 2 (minusTailForm K b c) ![0, 1]) heP.1) hmain

end CFSG.LocalAnalysis.UniquenessCase.UC22.KAdjE
