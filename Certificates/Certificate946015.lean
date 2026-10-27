module

public import Certificates.Data.ParrottE9

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG.ComponentClassification.CatFactsSmall.PSp43
open CFSG.GH74.KGroups

structure ParrottE9Facts : Prop where
  e9_mem_A : QA45.sift e9 0 = true
  e9_pow_nine : e9 ^ 9 = 1
  e9_cube : e9 ^ 3 = sigma1
  e9_cube_ne_one : e9 ^ 3 ≠ 1

end CFSG.RankThree.GF2n.Parrott

public section

namespace Certificates

open Certificates

set_option maxHeartbeats 0 in
open CFSG.ComponentClassification.CatFactsSmall.PSp43 in
open CFSG.GH74.KGroups in
open CFSG.RankThree.GF2n.Parrott in
theorem certificate946015 : ParrottE9Facts := {
    e9_mem_A := by decide +kernel
    e9_pow_nine := by decide +kernel
    e9_cube := by decide +kernel
    e9_cube_ne_one := by decide +kernel
  }

end Certificates
