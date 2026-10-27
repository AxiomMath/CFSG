module

public import Certificates.Certificate946016Base

public import Certificates.Data.ParrottPSp43
public import Certificates.Kernel.Parrott946.Glue16
public import Certificates.Kernel.Parrott946.Alg
public import Certificates.Certificate2012

public section

public section

namespace Certificates

open Certificates CFSG.RankThree.GF2n.Parrott CFSG.GH74.KGroups Subgroup CFSG.Certificates.Kernel.PkCV
  CFSG.ComponentClassification.CatFactsSmall.PSp43 CertificateChecks.Parrott946
  CertificateChecks.KernelA45

open CFSG.ComponentClassification.CatFactsSmall.PSp43
open CFSG.GH74.KGroups

open Certificates CFSG.RankThree.GF2n.Parrott CFSG.GH74.KGroups Subgroup
  CFSG.ComponentClassification.CatFactsSmall.PSp43 CertificateChecks.Parrott946
  CertificateChecks.KernelA45

theorem v_conj_sigma1 : v * sigma1 * v⁻¹ = sigma1 * sigma1 := by
  rw [Alg.sigma1_conj_v]
  refine (eq_inv_of_mul_eq_one_right ?_).symm
  rw [CFSG.KC.OrbFind.pow_three', Alg.sigma1_cube]

theorem certificate946016 : CFSG.RankThree.GF2n.Parrott.ParrottO3Facts := {
    o3_nodup := by
      rw [O3_eq, nodup_map_ev]
      exact o3c_facts.1
    o3_length := by
      rw [O3_eq, List.length_map]
      exact o3c_facts.2.1
    o3_one_mem := o3_one
    o3_mul_closed := List.all_eq_true.2 fun _ hx => List.all_eq_true.2 fun _ hy =>
      decide_eq_true (o3_mul hx hy)
    o3_inv_closed := List.all_eq_true.2 fun _ hx => decide_eq_true (o3_inv hx)
    o3_fixed := o3_fixed'
    o3a_mem := s1_mem_O3
    o3b_mem := o3b_mem_O3
    o3c_mem := o3c_mem_O3
    o3a_cube := Alg.sigma1_cube
    o3b_cube := o3_pow o3b_mem_O3
    o3c_cube := o3_pow o3c_mem_O3
    O3_le_QA45 := List.all_eq_true.2 fun x hx => (mem_iff_sift QA45 QA45_ok x).1 (O3_le_A x hx)
    isHeisenberg_O3 := by
      refine ⟨List.all_eq_true.2 fun _ hx => decide_eq_true (o3_pow hx), ?_⟩
      obtain ⟨x, hx, y, hy, h⟩ := o3_noncomm
      exact List.any_eq_true.2 ⟨x, hx, List.any_eq_true.2 ⟨y, hy, decide_eq_true h⟩⟩
    center_O3 := by
      ext x
      simp only [List.mem_toFinset, List.mem_filter, List.all_eq_true, decide_eq_true_eq,
        Finset.mem_insert, Finset.mem_singleton]
      exact center_O3'
    sigma1_mem_O3 := s1_mem_O3
    sigma2inv_not_mem_O3 := s12i_not_mem_O3
    O3_le_centralizer_sigma1 := List.all_eq_true.2 fun _ hx => decide_eq_true (o3_comm_s1 hx)
    O3_normal_in_centralizer := by
      refine ⟨?_, List.all_eq_true.2 fun c hc => List.all_eq_true.2 fun x hx =>
        decide_eq_true (O3_normal' ?_ hx)⟩
      · have e : centralizerSigma1 =
            (elemsT QA45).filter (fun c => decide (c * sigma1 = sigma1 * c)) := rfl
        rw [e, filter_cent, card_cent_s1]
      · obtain ⟨hc, hs⟩ := List.mem_filter.1 hc
        exact mem_inf.2 ⟨(mem_elemsT QA45 QA45_ok c).1 hc,
          mem_centralizer_singleton_iff.2 (beq_iff_eq.1 hs)⟩
    class_of_sigma1sigma2inv := by
      have hs : classCentralizerSize (sigma1 * sigma2⁻¹) () = 108 := by
        have e : classCentralizerSize (sigma1 * sigma2⁻¹) () = ((elemsT QA45).filter
            (fun c => decide (c * (sigma1 * sigma2⁻¹) = (sigma1 * sigma2⁻¹) * c))).length := by
          unfold classCentralizerSize
          refine congrArg List.length (List.filter_congr fun c _ => ?_)
          rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff, mul_inv_eq_iff_eq_mul]
        rw [e, filter_cent, card_cent_s12i]
      refine ⟨hs, by rw [hs], ?_⟩
      ext x
      simp only [classInO3, o3CenterComplement, List.mem_toFinset, List.mem_filter, List.mem_map,
        decide_eq_true_eq, Finset.mem_insert, Finset.mem_singleton]
      have h := class_O3' v_conj_sigma1 (x := x)
      constructor
      · rintro ⟨⟨c, hc, e⟩, hx⟩
        exact h.1 ⟨hx, c, (mem_elemsT QA45 QA45_ok c).1 hc, e.symm⟩
      · rintro hx
        obtain ⟨hx, c, hc, e⟩ := h.2 hx
        exact ⟨⟨c, (mem_elemsT QA45 QA45_ok c).2 hc, e.symm⟩, hx⟩ }

end Certificates
