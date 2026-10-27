module

public import CFSG.LocalAnalysis.StandardType.GGTriD4TwoRow.Model
public import Certificates.Certificate707012

public section

namespace CFSG.RankThree.PartTwo.Sec4.Item434D42

open Subgroup CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
  CFSG.Monster.B.Fischer CFSG.RankThree.Native CFSG.RankThree.PartOne
  CFSG.StandardType.TriD4TwoRow

@[expose] noncomputable def d4F0 : Equiv.Perm (Fin 2457) := permOfArr 2457 (f0Arr ())

@[expose] noncomputable def d4S0 : Subgroup (Equiv.Perm (Fin 2457)) :=
  closure (permsA 2457 (s0Gens ()))

theorem d4S0_facts :
    (s0Cert ()).pts.size = 243 ∧
      (∀ i < 243, Rep 2457 (s0Cert ()).pts[i]! (permOfArr 2457 (s0Cert ()).pts[i]!) ∧
        permOfArr 2457 (s0Cert ()).pts[i]! ∈ d4S0) ∧
      (∀ x ∈ d4S0, ∃ i < 243, Rep 2457 (s0Cert ()).pts[i]! x) ∧ Nat.card d4S0 = 243 ∧
      (d4F0 * d4Phi⁻¹ ∈ d4P) ∧
      
        ∀ y ∈ d4G, y ∉ d4P → y ^ 3 = 1 → ∃ t ∈ d4P, t ≠ 1 ∧ t ^ 2 = 1 ∧ y * t = t * y :=
  Certificates.certificate707012

end CFSG.RankThree.PartTwo.Sec4.Item434D42
