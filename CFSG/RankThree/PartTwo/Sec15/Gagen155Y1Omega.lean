module

public import CFSG.RankThree.PartTwo.Sec15.HypR
public import CFSG.RankThree.PartTwo.Sec13.Statements
import CFSG.RankThree.PartTwo.Sec14.Concl142HJPoint
import CFSG.RankThree.PartTwo.Sec14.Item1417
import CFSG.RankThree.PartTwo.Sec14.Item143DescProofOne
import CFSG.RankThree.PartTwo.Sec15.Item15Res11ProofQ
import CFSG.RankThree.PartTwo.Sec15.Ronan152SL25Conf
import CFSG.RankThree.PartTwo.Sec4.Sporadic.Item415

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank

variable {G : Type} [Group G] [Finite G]

namespace Gagen155Y1

theorem omegaA_eq_singleton_of_j2_of_ncard_lt
    (h134 : Item134) (h48 : Sec4.Item4_8) {A L : Subgroup G} {c : G} (hR : Sec15R G A c L)
    (hJ : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2))
    (h3 : (omegaA A).ncard < 3) : omegaA A = {Subgroup.zpowers c} := by
  have h := hR.toSec14Std
  have hD := hR.toSec13Data
  have hA := h.isE27'
  obtain ⟨d, hdA, hd1, hdZ⟩ : ∃ d ∈ A, d ≠ 1 ∧ IsZCentral L d := by
    obtain ⟨d, hdA, hd1, hdL, S, hdS, hSd⟩ := exists_three_central_of_j2 hD hJ
    obtain ⟨-, -, hθ3, -⟩ :=
      solvable_prime_complement_core_characterization (H := ↥L) Nat.prime_three
    obtain ⟨hS, hZ⟩ :=
      center_sylow_eq_zpowers_of_quot_j2 Sec4.Sporadic.rank3II_4_15 hθ3 hJ hdL hd1 S hdS hSd
    exact ⟨d, hdA, hd1, _, hS, hZ⟩
  have hcd : IsLBConfig A (Subgroup.closure {c, d}) c d L :=
    Proof15Res11.isLBConfig_of hR hJ hdZ
  obtain ⟨hdL, -⟩ := hcd.2.2.2.2
  have hBcd : IsHyperplane A (Subgroup.closure {c, d}) :=
    Proof15Res11.isHyperplane_of hR hJ hdA hd1 hdL
  obtain ⟨-, -, -, -, -, -, -, -, -, hdc⟩ := Ronan152SL25.lbConfig_facts hA hBcd hcd
  have hdB' : d ∈ Subgroup.closure {c, d} :=
    Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  obtain ⟨K, hK, hLK⟩ := Desc143X.exists_mem_le_residual h48 h hBcd hcd hdB' hd1 hdc
  rcases h134 G A c L hD hJ d hdA hd1 hdZ K hK hLK with
    ⟨-, -, hΩ1⟩ | ⟨-, -, -, -, -, -, hΩ⟩ | ⟨-, -, -, h12⟩
  · exact hΩ1
  · rcases hΩ with ⟨-, h3'⟩ | ⟨-, -, -, -, -, -, -, -, h6, -, -, -⟩
    · omega
    · omega
  · omega

end Gagen155Y1

end CFSG.RankThree.PartTwo.Sec15
