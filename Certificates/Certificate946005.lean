module

public import Certificates.Data.ParrottPSp43
public import Certificates.Kernel.Parrott946.Glue
public import Certificates.Kernel.Parrott946.Alg
public import Certificates.Certificate2012

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG.ComponentClassification.CatFactsSmall.PSp43
open CFSG.GH74.KGroups

structure ParrottFacts : Prop where
  u_mem_Q : QP45.sift u 0 = true
  sigma1_mem_Q : QP45.sift sigma1 0 = true
  sigma2_mem_Q : QP45.sift sigma2 0 = true
  alpha1_mem_Q : QP45.sift alpha1 0 = true
  beta1_mem_Q : QP45.sift beta1 0 = true
  alpha2_mem_Q : QP45.sift alpha2 0 = true
  beta2_mem_Q : QP45.sift beta2 0 = true
  beta_mem_Q : QP45.sift beta 0 = true
  u_mem_A : QA45.sift u 0 = true
  v_mem_A : QA45.sift v 0 = true
  sigma1_mem_A : QA45.sift sigma1 0 = true
  sigma2_mem_A : QA45.sift sigma2 0 = true
  alpha1_mem_A : QA45.sift alpha1 0 = true
  beta1_mem_A : QA45.sift beta1 0 = true
  alpha2_mem_A : QA45.sift alpha2 0 = true
  beta2_mem_A : QA45.sift beta2 0 = true
  beta_mem_A : QA45.sift beta 0 = true
  v_not_mem_Q : ¬ (QP45.sift v 0 = true)
  t_sq : t * t = 1
  t_ne_one : t ≠ 1
  u_sq : u * u = 1
  u_ne_one : u ≠ 1
  v_sq : v * v = 1
  v_ne_one : v ≠ 1
  sigma1_cube : sigma1 ^ 3 = 1
  sigma1_ne_one : sigma1 ≠ 1
  sigma2_cube : sigma2 ^ 3 = 1
  sigma2_ne_one : sigma2 ≠ 1
  alpha1_sq : alpha1 * alpha1 = t
  alpha1_ne_one : alpha1 ≠ 1
  alpha1_pow_four : alpha1 ^ 4 = 1
  alpha1_sq_ne_one : alpha1 * alpha1 ≠ 1
  beta1_sq : beta1 * beta1 = t
  beta1_ne_one : beta1 ≠ 1
  beta1_pow_four : beta1 ^ 4 = 1
  beta1_sq_ne_one : beta1 * beta1 ≠ 1
  alpha2_sq : alpha2 * alpha2 = t
  alpha2_ne_one : alpha2 ≠ 1
  alpha2_pow_four : alpha2 ^ 4 = 1
  alpha2_sq_ne_one : alpha2 * alpha2 ≠ 1
  beta2_sq : beta2 * beta2 = t
  beta2_ne_one : beta2 ≠ 1
  beta2_pow_four : beta2 ^ 4 = 1
  beta2_sq_ne_one : beta2 * beta2 ≠ 1
  beta_sq : beta * beta = u * t
  beta_ne_one : beta ≠ 1
  beta_pow_four : beta ^ 4 = 1
  beta_sq_ne_one : beta * beta ≠ 1
  sigma1_conj_u : u * sigma1 * u⁻¹ = sigma2
  alpha1_conj_u : u * alpha1 * u⁻¹ = alpha2
  beta1_conj_u : u * beta1 * u⁻¹ = beta2
  sigma1_mul_u : sigma1 * u = u * sigma2
  alpha1_mul_u : alpha1 * u = u * alpha2
  beta1_mul_u : beta1 * u = u * beta2
  sigma1_conj_v : v * sigma1 * v⁻¹ = sigma1⁻¹
  sigma2_conj_v : v * sigma2 * v⁻¹ = sigma2⁻¹
  alpha1_conj_v : v * alpha1 * v⁻¹ = alpha1⁻¹
  alpha2_conj_v : v * alpha2 * v⁻¹ = alpha2⁻¹
  beta1_conj_v : v * beta1 * v⁻¹ = alpha1 * beta1
  beta2_conj_v : v * beta2 * v⁻¹ = alpha2 * beta2
  u_commute_v : u * v = v * u
  t_commute_u : t * u = u * t
  t_commute_v : t * v = v * t
  t_commute_sigma1 : t * sigma1 = sigma1 * t
  t_commute_sigma2 : t * sigma2 = sigma2 * t
  t_commute_alpha1 : t * alpha1 = alpha1 * t
  t_commute_beta1 : t * beta1 = beta1 * t
  t_commute_alpha2 : t * alpha2 = alpha2 * t
  t_commute_beta2 : t * beta2 = beta2 * t
  sigma1_commute_sigma2 : sigma1 * sigma2 = sigma2 * sigma1
  alpha1_commute_alpha2 : alpha1 * alpha2 = alpha2 * alpha1
  beta1_commute_beta2 : beta1 * beta2 = beta2 * beta1
  alpha1_beta1_alpha1 : alpha1 * beta1 * alpha1 = beta1
  alpha1_beta1_eq : alpha1 * beta1 = beta1 * alpha1 * t
  alpha1_beta1_sq : alpha1 * beta1 * (alpha1 * beta1) = t
  alpha1_beta1_ne_one : alpha1 * beta1 ≠ 1
  alpha2_beta2_alpha2 : alpha2 * beta2 * alpha2 = beta2
  alpha2_beta2_eq : alpha2 * beta2 = beta2 * alpha2 * t
  alpha2_beta2_sq : alpha2 * beta2 * (alpha2 * beta2) = t
  alpha2_beta2_ne_one : alpha2 * beta2 ≠ 1
  beta_mul_u : beta * u = t * beta
  u_mul_beta : u * beta = beta * t
  beta_mul_t_mul_beta : beta * t * beta = t
  beta_mul_u_mul_beta : beta * u * beta = u
  centralizer_sigma1 : ((elemsT QA45).filter (fun g => g * sigma1 = sigma1 * g)).length = 648
  centralizer_sigma2 : ((elemsT QA45).filter (fun g => g * sigma2 = sigma2 * g)).length = 648
  centralizer_sigma1sigma2 : ((elemsT QA45).filter (fun g => g * (sigma1 * sigma2) = (sigma1 * sigma2) * g)).length = 216
  centralizer_sigma1sigma2inv : ((elemsT QA45).filter (fun g => g * (sigma1 * sigma2⁻¹) = (sigma1 * sigma2⁻¹) * g)).length = 108
  centralizer_t : ((elemsT QA45).filter (fun g => g * t = t * g)).length = 1152
  centralizer_u : ((elemsT QA45).filter (fun g => g * u = u * g)).length = 1152
  centralizer_v : ((elemsT QA45).filter (fun g => g * v = v * g)).length = 96
end CFSG.RankThree.GF2n.Parrott

public section

namespace Certificates

open Certificates CFSG.RankThree.GF2n.Parrott CFSG.GH74.KGroups
  CFSG.ComponentClassification.CatFactsSmall.PSp43 CertificateChecks.Parrott946

open CFSG.ComponentClassification.CatFactsSmall.PSp43 in
open CFSG.GH74.KGroups in
theorem certificate946005 : CFSG.RankThree.GF2n.Parrott.ParrottFacts := {
    u_mem_Q := (mem_iff_sift QP45 QP45_ok u).1 u_memP
    sigma1_mem_Q := (mem_iff_sift QP45 QP45_ok sigma1).1 sigma1_memP
    sigma2_mem_Q := (mem_iff_sift QP45 QP45_ok sigma2).1 sigma2_memP
    alpha1_mem_Q := (mem_iff_sift QP45 QP45_ok alpha1).1 alpha1_memP
    beta1_mem_Q := (mem_iff_sift QP45 QP45_ok beta1).1 beta1_memP
    alpha2_mem_Q := (mem_iff_sift QP45 QP45_ok alpha2).1 alpha2_memP
    beta2_mem_Q := (mem_iff_sift QP45 QP45_ok beta2).1 beta2_memP
    beta_mem_Q := (mem_iff_sift QP45 QP45_ok beta).1 beta_memP
    u_mem_A := (mem_iff_sift QA45 QA45_ok u).1 u_memA
    v_mem_A := (mem_iff_sift QA45 QA45_ok v).1 v_memA
    sigma1_mem_A := (mem_iff_sift QA45 QA45_ok sigma1).1 sigma1_memA
    sigma2_mem_A := (mem_iff_sift QA45 QA45_ok sigma2).1 sigma2_memA
    alpha1_mem_A := (mem_iff_sift QA45 QA45_ok alpha1).1 alpha1_memA
    beta1_mem_A := (mem_iff_sift QA45 QA45_ok beta1).1 beta1_memA
    alpha2_mem_A := (mem_iff_sift QA45 QA45_ok alpha2).1 alpha2_memA
    beta2_mem_A := (mem_iff_sift QA45 QA45_ok beta2).1 beta2_memA
    beta_mem_A := (mem_iff_sift QA45 QA45_ok beta).1 beta_memA
    v_not_mem_Q := fun h => v_not_mem_P ((mem_iff_sift QP45 QP45_ok v).2 h)
    t_sq := Alg.t_sq
    t_ne_one := Alg.t_ne_one
    u_sq := Alg.u_sq
    u_ne_one := Alg.u_ne_one
    v_sq := Alg.v_sq
    v_ne_one := Alg.v_ne_one
    sigma1_cube := Alg.sigma1_cube
    sigma1_ne_one := Alg.sigma1_ne_one
    sigma2_cube := Alg.sigma2_cube
    sigma2_ne_one := Alg.sigma2_ne_one
    alpha1_sq := Alg.alpha1_sq
    alpha1_ne_one := Alg.alpha1_ne_one
    alpha1_pow_four := Alg.alpha1_pow_four
    alpha1_sq_ne_one := Alg.alpha1_sq_ne_one
    beta1_sq := Alg.beta1_sq
    beta1_ne_one := Alg.beta1_ne_one
    beta1_pow_four := Alg.beta1_pow_four
    beta1_sq_ne_one := Alg.beta1_sq_ne_one
    alpha2_sq := Alg.alpha2_sq
    alpha2_ne_one := Alg.alpha2_ne_one
    alpha2_pow_four := Alg.alpha2_pow_four
    alpha2_sq_ne_one := Alg.alpha2_sq_ne_one
    beta2_sq := Alg.beta2_sq
    beta2_ne_one := Alg.beta2_ne_one
    beta2_pow_four := Alg.beta2_pow_four
    beta2_sq_ne_one := Alg.beta2_sq_ne_one
    beta_sq := Alg.beta_sq
    beta_ne_one := Alg.beta_ne_one
    beta_pow_four := Alg.beta_pow_four
    beta_sq_ne_one := Alg.beta_sq_ne_one
    sigma1_conj_u := Alg.sigma1_conj_u
    alpha1_conj_u := Alg.alpha1_conj_u
    beta1_conj_u := Alg.beta1_conj_u
    sigma1_mul_u := Alg.sigma1_mul_u
    alpha1_mul_u := Alg.alpha1_mul_u
    beta1_mul_u := Alg.beta1_mul_u
    sigma1_conj_v := Alg.sigma1_conj_v
    sigma2_conj_v := Alg.sigma2_conj_v
    alpha1_conj_v := Alg.alpha1_conj_v
    alpha2_conj_v := Alg.alpha2_conj_v
    beta1_conj_v := Alg.beta1_conj_v
    beta2_conj_v := Alg.beta2_conj_v
    u_commute_v := Alg.u_commute_v
    t_commute_u := Alg.t_commute_u
    t_commute_v := Alg.t_commute_v
    t_commute_sigma1 := Alg.t_commute_sigma1
    t_commute_sigma2 := Alg.t_commute_sigma2
    t_commute_alpha1 := Alg.t_commute_alpha1
    t_commute_beta1 := Alg.t_commute_beta1
    t_commute_alpha2 := Alg.t_commute_alpha2
    t_commute_beta2 := Alg.t_commute_beta2
    sigma1_commute_sigma2 := Alg.sigma1_commute_sigma2
    alpha1_commute_alpha2 := Alg.alpha1_commute_alpha2
    beta1_commute_beta2 := Alg.beta1_commute_beta2
    alpha1_beta1_alpha1 := Alg.alpha1_beta1_alpha1
    alpha1_beta1_eq := Alg.alpha1_beta1_eq
    alpha1_beta1_sq := Alg.alpha1_beta1_sq
    alpha1_beta1_ne_one := Alg.alpha1_beta1_ne_one
    alpha2_beta2_alpha2 := Alg.alpha2_beta2_alpha2
    alpha2_beta2_eq := Alg.alpha2_beta2_eq
    alpha2_beta2_sq := Alg.alpha2_beta2_sq
    alpha2_beta2_ne_one := Alg.alpha2_beta2_ne_one
    beta_mul_u := Alg.beta_mul_u
    u_mul_beta := Alg.u_mul_beta
    beta_mul_t_mul_beta := Alg.beta_mul_t_mul_beta
    beta_mul_u_mul_beta := Alg.beta_mul_u_mul_beta
    centralizer_sigma1 := (filter_cent sigma1).trans card_cent_s1
    centralizer_sigma2 := (filter_cent sigma2).trans (card_cent_s2 Alg.sigma1_conj_u)
    centralizer_sigma1sigma2 := (filter_cent (sigma1 * sigma2)).trans card_cent_s12
    centralizer_sigma1sigma2inv := (filter_cent (sigma1 * sigma2⁻¹)).trans card_cent_s12i
    centralizer_t := (filter_cent t).trans (card_cent_t Alg.t_sq Alg.t_ne_one)
    centralizer_u := (filter_cent u).trans (card_cent_u Alg.u_sq Alg.u_ne_one)
    centralizer_v := (filter_cent v).trans (card_cent_v Alg.v_sq Alg.v_ne_one) }

end Certificates
