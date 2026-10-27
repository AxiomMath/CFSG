module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KAdj.Concl
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23d.Defs
public import CFSG.LocalAnalysis.UniquenessCase.UC22S20
public import CFSG.Quasithin.H13.U4ParPoint
public import CFSG.ClassicalGroups.UnitaryFlag.ModelTransport
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherParabolicData
public import CFSG.Open.StatedDefs

import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KAdj.ConjBack
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KAdj.SUOHinf
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KAdj.SU4Borel
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KAdj.SU4Char
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KAdj.SU4Act
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KAdj.SU4Root
import CFSG.LocalAnalysis.UniquenessCase.UC22P21c
import CFSG.LocalAnalysis.UniquenessCase.UC22P22m
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ParabolicTransfer
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23d.UnitaryTransport
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
import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockUniMap

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.KAdjE

open Matrix CFSG.Open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.Quasithin.H13.U4Par
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (flagStabilizer)
open KTabD (lineStab)

theorem su4_dvd_two_pow_sub_one {n m r : ℕ} (hn : n = 2 * m) (h3 : 3 ≤ n)
    (hr : (∃ s : ℕ, s ∣ n ∧ Odd s ∧ 1 < s ∧ r ∣ 2 ^ s - 1) ∨ (∃ k : ℕ, n = 2 ^ k ∧ r = 3)) :
    r ∣ 2 ^ m - 1 := by
  rcases hr with ⟨s, hs_dvd, hs_odd, -, hr_s⟩ | ⟨k, hk, hr3⟩
  · have hs_dvd_m : s ∣ m := by
      have hcop : s.Coprime 2 := hs_odd.coprime_two_right
      have h2 : s ∣ 2 * m := by rw [← hn]; exact hs_dvd
      exact hcop.dvd_of_dvd_mul_left h2
    exact hr_s.trans (Nat.pow_sub_one_dvd_pow_sub_one 2 hs_dvd_m)
  · have hk2 : 2 ≤ k := by
      by_contra h
      have hk1 : k ≤ 1 := by omega
      interval_cases k
      · simp at hk; omega
      · simp at hk; omega
    have hm_eq : m = 2 ^ (k - 1) := by
      have h2m : 2 * m = 2 ^ k := hn.symm.trans hk
      have hpow : 2 ^ k = 2 * 2 ^ (k - 1) := by
        conv_lhs => rw [← Nat.sub_add_cancel (show 1 ≤ k by omega)]
        rw [pow_succ']
      exact Nat.mul_left_cancel (by norm_num) (h2m.trans hpow)
    have hm2 : 2 ∣ m := by
      rw [hm_eq]
      obtain ⟨j, hj⟩ : ∃ j, k - 1 = j + 1 := ⟨k - 2, by omega⟩
      rw [hj, pow_succ]
      exact ⟨2 ^ j, mul_comm _ _⟩
    rw [hr3]
    have h : 2 ^ 2 - 1 ∣ 2 ^ m - 1 := Nat.pow_sub_one_dvd_pow_sub_one 2 hm2
    norm_num at h
    exact h

private lemma su4_not_two_dvd_two_pow_sub_one_D06 {a : ℕ} (ha : 2 ≤ a) : ¬ 2 ∣ 2 ^ a - 1 := by
  obtain ⟨b, rfl⟩ : ∃ b, a = b + 1 := ⟨a - 1, by omega⟩
  rw [pow_succ]
  have hpos : 0 < 2 ^ b := Nat.two_pow_pos b
  intro hdvd
  obtain ⟨c, hc⟩ := hdvd
  omega

private theorem su4_coroot_kAdjConcl_D06 {a : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 a K)
    (ha : 2 ≤ a) {c : Kˣ} {c' : h.fixedFieldˣ}
    (hc' : ((c' : h.fixedField) : K) = (c : K)) {r : ℕ} (horder_c : orderOf c = r) :
    KAdjConcl (Hinf (parP h)) (su4Coroot h c) r a := by
  refine ⟨(levHom h).range, (levHom h).range, su4_levHom_range_le_hinf_parP h ha,
    su4_levHom_range_le_hinf_parP h ha, ?_, ?_⟩
  · intro N hN hnorm hX₁ _
    exact su4_normal_closure_levHom_range h ha N hN hnorm hX₁
  · intro X hX
    have hXr : X = (levHom h).range := hX.elim id id
    rw [hXr]
    refine ⟨su4_isSLn_levHom_range h, su4Coroot_mem_normalizer_levHom_range h hc', ?_⟩
    refine ⟨levHom h (su4Diag2 h c'), ?_, ?_, ?_⟩
    · exact ⟨su4Diag2 h c', rfl⟩
    · rw [orderOf_levHom_su4Diag2 h hc', horder_c]
    · intro x hx
      exact su4Coroot_conj_eq_of_mem_levHom_range h hc' hx

theorem kAdj_model_su4_hyp {a : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 a K)
    (ha : 2 ≤ a) {r : ℕ} (hr : r ∣ 2 ^ a - 1) {t : ↥(hypSU h 2 0)}
    (ht : t ∈ Hinf (flagStabilizer h 2 0 {2}) ⊓ parP h) (hord : orderOf t = r) :
    KAdjConcl (Hinf (parP h)) t r a := by
  haveI := h.finite
  haveI : Finite ↥(hypSU h 2 0) := CFSG.ClassicalGroups.UnitaryFlag.finite_hypSU h
  obtain ⟨htQα, htQ₀⟩ := Subgroup.mem_inf.mp ht
  have htQα' : t ∈ flagStabilizer h 2 0 {2} := uc22p21c_Hinf_le _ htQα
  have htB : t ∈ hypBorel h 2 0 := by
    rw [← su4_parP_inf_flagStabilizer_eq_hypBorel h]
    exact ⟨htQ₀, htQα'⟩
  have hodd : ¬ 2 ∣ orderOf t := by
    rw [hord]
    exact fun h2r => su4_not_two_dvd_two_pow_sub_one_D06 ha (h2r.trans hr)
  obtain ⟨e, heU, hetor⟩ := su4_exists_conj_mem_hypTorus h htB hodd
  have heB : e ∈ hypBorel h 2 0 := hypUnitriangular_le_hypBorel h heU
  have he_mem : e ∈ parP h ⊓ flagStabilizer h 2 0 {2} := by
    rw [su4_parP_inf_flagStabilizer_eq_hypBorel h]
    exact heB
  have hconjHinf : e * t * e⁻¹ ∈ Hinf (flagStabilizer h 2 0 {2}) :=
    suo_conj_mem_hinf he_mem.2 htQα
  have hgB : e * t * e⁻¹ ∈ hypBorel h 2 0 := hypTorus_le_hypBorel h hetor
  have hdiag := su4_diag_mul_eq_one_of_mem_hinf h hconjHinf hgB
  obtain ⟨c, hc⟩ := su4_exists_eq_coroot_of_mem_hypTorus h hetor hdiag
  have hconjorder : orderOf (e * t * e⁻¹) = orderOf t := by
    have := orderOf_injective (MulAut.conj e).toMonoidHom (MulAut.conj e).injective t
    simpa [MulAut.conj_apply] using this
  have horder_c : orderOf c = r := by
    rw [← orderOf_su4Coroot h c, ← hc, hconjorder, hord]
  obtain ⟨c', hc'⟩ := su4_exists_fixedField_unit_of_orderOf_dvd h c (by rw [horder_c]; exact hr)
  have hmain := su4_coroot_kAdjConcl_D06 h ha hc' horder_c
  have he_norm : e ∈ Subgroup.normalizer (Hinf (parP h) : Set ↥(hypSU h 2 0)) :=
    uc22p22m_le_normalizer_Hinf (parP h) he_mem.1
  exact kAdjConcl_conj e he_norm (hc.symm ▸ hmain)

end CFSG.LocalAnalysis.UniquenessCase.UC22.KAdjE
