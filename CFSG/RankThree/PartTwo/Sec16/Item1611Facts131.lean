module

public import CFSG.RankThree.PartTwo.Sec13.Item131a
import CFSG.RankThree.PartTwo.Sec13.Item13SLTwo
import CFSG.RankThree.PartTwo.Sec13.Item131Facts
import CFSG.RankThree.PartTwo.Sec13.Item13Sporadic
import CFSG.RankThree.PartTwo.Sec14.Concl142NHJInner
import CFSG.RankThree.PartTwo.KFacts.KS14Orders
import CFSG.RankThree.PartTwo.Sec16.Item1613StepsProofTrans

public section

namespace CFSG.RankThree.PartTwo.Sec16.Proof1611Res

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.GH74.GLS
open Matrix CFSG.RankThree.PartTwo.Sec4

variable {G : Type} [Group G] [Finite G] {A L : Subgroup G} {c : G}

theorem facts131_odd
    (h131a : Item131a) (hD : Sec13Data G A c L) (hcL : c ∉ L)
    (hL3 : IsLThreePi (↥L ⧸ aschbacherSolvableCore 3 ↥L))
    (hprod : Nonempty (lBarA c L A ≃* Multiplicative (ZMod 3) × Sec12.lBar c L)) :
    Nonempty (Sec4.autIn L A ≃* QuaternionGroup 2) ∨
      Nonempty (Sec4.autIn L A ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 3)) := by
  obtain ⟨φ₀⟩ := hprod
  have h9 := Sec13.card_inf_eq_nine hD (Sec13.isPerfect_lBar hD) φ₀
  obtain ⟨⟨hM22p, hM22z⟩, ⟨hM12p, hM12z⟩, ⟨hJ2p, hJ2z⟩⟩ :=
    (sporadicModels131 : SporadicModels131)
  rcases h131a G A c L hD with ⟨-, hQ⟩ | ⟨hPGL, -, -⟩ | ⟨⟨φ⟩, -⟩ | ⟨⟨φ⟩, -⟩ | ⟨⟨φ⟩, -⟩ |
      ⟨⟨φ⟩, -⟩ | hSL | ⟨hHeis, -⟩
  · exact hQ
  · have h3 := Sec16.Proof1614Trans.card_inf_eq_three_of_pgl hD hPGL
    omega
  · obtain ⟨hS, hZ⟩ := isPerfect_center_alt7
    obtain ⟨-, -, -, ⟨ψ⟩⟩ := Sec13.facts_of_prod hD hS hZ φ
    exact absurd hL3 (not_isLThreePi_of_mulEquiv ψ not_isoLThreePi_alternating_seven)
  · obtain ⟨-, -, -, ⟨ψ⟩⟩ := Sec13.facts_of_prod hD hM22p hM22z φ
    exact absurd hL3 (not_isLThreePi_of_mulEquiv ψ KFacts.KS14.not_isoLThreePi_M22)
  · obtain ⟨-, -, -, ⟨ψ⟩⟩ := Sec13.facts_of_prod hD hM12p hM12z φ
    exact absurd hL3 (not_isLThreePi_of_mulEquiv ψ KFacts.KS14.not_isoLThreePi_M12)
  · obtain ⟨-, -, -, ⟨ψ⟩⟩ := Sec13.facts_of_prod hD hJ2p hJ2z φ
    exact absurd hL3 (not_isLThreePi_of_mulEquiv ψ KFacts.KS14.ks17J2NotList.1)
  · exact absurd (mem_of_isSLThreePiTwo slTwoCenter hD hSL) hcL
  · exact absurd (mem_of_isHeisCentral hD hHeis) hcL

end CFSG.RankThree.PartTwo.Sec16.Proof1611Res
