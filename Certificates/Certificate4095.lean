module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporRuFinInputs
import Certificates.Kernel.LocalQT.Small.C4095

public section

namespace Certificates

open CFSG.KD.LQT.C4095 in
open CFSG CFSG.QuasithinUnique CFSG.QuasithinUnique.Vol2Native CFSG.QuasithinUnique.Vol2Native.L239 CFSG.QuasithinUnique.Vol2Native.L239.RuPairs in
open Equiv in
theorem certificate4095 : (∀ g ∈ [blockPerm0, blockPerm1], ∀ x ∈ blockHList,
          g * x ∈ blockHList ∧ g⁻¹ * x ∈ blockHList)
    ∧ (∀ g ∈ [blockTau2, blockTau3], ∀ x ∈ blockTList,
          g * x ∈ blockTList ∧ g⁻¹ * x ∈ blockTList)
    ∧ (∀ x ∈ blockHList,
          (∀ t ∈ [blockTau2, blockTau3], x * t * x⁻¹ ∈ blockTList) → x ∈ blockTList) :=
  CFSG.KC.LQT.S.s4095 _ _ _ _ hG hH hU hT hk

end Certificates
