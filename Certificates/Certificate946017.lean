
module

public import Certificates.Certificate946017Base

public import Certificates.Data.ParrottPSp43L1
public import Certificates.Kernel.Parrott946.Glue17m
public import Certificates.Kernel.Parrott946.Glue17p
public import Certificates.Certificate2012

public section

set_option maxRecDepth 400000

public section

namespace Certificates

open CFSG.GH74.KGroups CFSG.ComponentClassification.CatFactsSmall.PSp43
  CFSG.RankThree.GF2n.Parrott CertificateChecks.KernelA45 CertificateChecks.Parrott946

open CFSG.ComponentClassification.CatFactsSmall.PSp43 in
open CFSG.GH74.KGroups in
open CFSG.Sporadic.Schreier (tab) in
local notation "P45" => Equiv.Perm (Fin 45)

structure _root_.CFSG.RankThree.GF2n.Parrott.QA45L1Facts : Prop where
  centralizer_ut : commCount (u * t) = 192
  centralizer_uv : commCount (u * v) = 1440
  card_involutions : involutionCount () = 891
  card_order_three : orderThreeCount () = 800
  t0_group : ListGroupFacts (T0list ()) T0gens
  t0_normalizer : t0NormalizerCheck () = true
  b5_mem_A : QA45.sift b5 0 = true
  b5_pow_five : b5 ^ 5 = 1
  b5_ne_one : b5 ≠ 1
  b5_commutes : b5 * (u * v) = (u * v) * b5
  b5_normalizer : b5NormalizerCount () = 40
  b5_centralizer : commCount b5 = 10
  s_group : ListGroupFacts (Slist ()) Sgens
  e3_group : ListGroupFacts (E3list ()) E3gens
  e1_group : ListGroupFacts (E1list ()) E1gens
  e2_group : ListGroupFacts (E2list ()) E2gens
  e16_in_t0 : e16Check () = true
  e16_centralizer : e16CentralizerCheck () = true
  e16_meet_s : e16MeetCheck () = true
  s_normalizer_card : (NSlist ()).length = 1920
  s_centralizer : centralizerSCheck () = true
  s_orbits : sOrbitCheck (NSlist ()) = true
  q8_group : ListGroupFacts (Q8list ()) Q8gens
  q8_conj : beta2 * alpha2 * beta2⁻¹ = alpha2⁻¹
  a2_commutes_sigma1 : alpha2 * sigma1 = sigma1 * alpha2
  b2_commutes_sigma1 : beta2 * sigma1 = sigma1 * beta2
  uv_commutes_sigma1_sigma2_inv : (u * v) * (sigma1 * sigma2⁻¹) = (sigma1 * sigma2⁻¹) * (u * v)
  d8_group : ListGroupFacts (D8list ()) D8gens
  vbeta_sq : (v * beta) * (v * beta) = 1
  tvbeta_sq : (t * (v * beta)) * (t * (v * beta)) = u * t
  vbeta_commutes_ut : (u * t) * (v * beta) = (v * beta) * (u * t)
  vbeta_commutes_sigma1_sigma2 : (v * beta) * (sigma1 * sigma2) = (sigma1 * sigma2) * (v * beta)
  d8_center : d8CenterCheck () = true

theorem certificate946017 : CFSG.RankThree.GF2n.Parrott.QA45L1Facts := {
    centralizer_ut := centralizer_ut
    centralizer_uv := centralizer_uv
    card_involutions := card_involutions
    card_order_three := card_order_three
    t0_group := t0_group
    t0_normalizer := t0_normalizer
    b5_mem_A := (mem_iff_sift QA45 QA45_ok b5).1 b5_memA
    b5_pow_five := b5_pow_five
    b5_ne_one := b5_ne_one
    b5_commutes := b5_commutes
    b5_normalizer := b5_normalizer
    b5_centralizer := b5_centralizer
    s_group := s_group
    e3_group := e3_group
    e1_group := e1_group
    e2_group := e2_group
    e16_in_t0 := e16_in_t0
    e16_centralizer := e16_centralizer
    e16_meet_s := e16_meet_s
    s_normalizer_card := s_normalizer_card
    s_centralizer := s_centralizer
    s_orbits := s_orbits
    q8_group := q8_group
    q8_conj := q8_conj
    a2_commutes_sigma1 := rels17.2.1
    b2_commutes_sigma1 := rels17.2.2.1
    uv_commutes_sigma1_sigma2_inv := uv_commutes_s12i
    d8_group := d8_group
    vbeta_sq := vbeta_sq
    tvbeta_sq := tvbeta_sq
    vbeta_commutes_ut := rels17.2.2.2.2.2.2.2.1
    vbeta_commutes_sigma1_sigma2 := rels17.2.2.2.2.2.2.2.2
    d8_center := d8_center }

end Certificates

end
