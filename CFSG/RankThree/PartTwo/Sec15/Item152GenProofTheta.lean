module

public import CFSG.RankThree.PartTwo.Sec15.Item152StepsGen
import CFSG.RankThree.PartTwo.Sec14.Concl142HJ
import CFSG.RankThree.PartTwo.Sec14.Item147
import CFSG.RankThree.PartTwo.Sec6.Item612Core
import CFSG.RankThree.PartTwo.Sec14.Item1411HJ
import CFSG.RankThree.PartTwo.Sec12.Gap128OTwoHJ
import CFSG.RankThree.PartTwo.Sec13.Item13Basic
public import CFSG.RankThree.PartTwo.Sec14.Item1446

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS

namespace Proof152Gen

variable {G : Type} [Group G] [Finite G]

theorem isPGroup_theta_of_j2
    {A L : Subgroup G} {c : G} (h : Sec14Std G A c L)
    (hJ : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2)) :
    IsPGroup 2 (aschbacherSolvableCore 3 ↥L) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hD := h.toSec13Data
  have hLc : L ≤ Subgroup.centralizer {c} := hD.le_centralizer
  have hLtop : L ≠ ⊤ := fun htop =>
    Sec6.centralizer_ne_top_of_ne_one h.toTheoremFourHyp hD.ne_one (top_le_iff.mp (htop ▸ hLc))
  obtain ⟨e₂⟩ := Sec12.gap128OTwoHJ ↥L (h.toTheoremFourHyp.sectionFourHyp hLtop)
    (Sec6.isPerfect_of_mem_thetaComponentsAt hD.mem_thetaComponentsAt) hJ
  obtain ⟨eθ⟩ := hJ
  obtain ⟨-, -, -, -, -, -, hθO⟩ :=
    solvable_prime_complement_core_characterization (H := ↥L) Nat.prime_three
  have hle : CFSG.pCore 2 ↥L ≤ aschbacherSolvableCore 3 ↥L := hθO 2 Nat.prime_two (by norm_num)
  have hidx : (aschbacherSolvableCore 3 ↥L).index = (CFSG.pCore 2 ↥L).index := by
    rw [Subgroup.index, Subgroup.index, Nat.card_congr eθ.toEquiv, Nat.card_congr e₂.toEquiv]
  have hcard : Nat.card (aschbacherSolvableCore 3 ↥L) ≤ Nat.card (CFSG.pCore 2 ↥L) := by
    have h1 := Subgroup.card_mul_index (aschbacherSolvableCore 3 ↥L)
    have h2 := Subgroup.card_mul_index (CFSG.pCore 2 ↥L)
    have hpos : 0 < (CFSG.pCore 2 ↥L).index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
    rw [hidx] at h1
    exact (Nat.eq_of_mul_eq_mul_right hpos (h1.trans h2.symm)).le
  have heq : CFSG.pCore 2 ↥L = aschbacherSolvableCore 3 ↥L :=
    Subgroup.eq_of_le_of_card_ge hle hcard
  rw [← heq]
  exact CFSG.pCore_isPGroup

theorem theta_le_of_mem_scriptQPiStar
    {A L : Subgroup G} {c : G}
    (h : Sec14Std G A c L)
    (hJ : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2))
    {U : Subgroup G}
    (hU : U ∈ scriptQPiStar A (lB A) (Subgroup.normalizer (Subgroup.zpowers c : Set G))
      (piOf 2)) :
    inSubgroup (aschbacherSolvableCore 3) L ≤ U := by
  have hD := h.toSec13Data
  set H := Subgroup.normalizer (Subgroup.zpowers c : Set G) with hHdef
  set θ := inSubgroup (aschbacherSolvableCore 3) L with hθdef
  have hUmem := hU.prop
  have hU2 : IsPGroup 2 U := isPGroup_of_mem_scriptQPi Nat.prime_two hUmem
  have hAU : A ≤ Subgroup.normalizer (U : Set G) := hUmem.1.1.1.2.2
  have hUinv : U ∈ invariantPiSubgroups H A (piCompl 3) :=
    ⟨hUmem.1.2, isPiSubgroup_piCompl_three_of_piOf_two hUmem.2, hAU⟩
  have hUc : U ≤ Subgroup.centralizer ({c} : Set G) :=
    le_centralizer_of_mem_invariantPiSubgroups hD.mem_A hD.orderOf_eq hUinv
  have hUθ : U ≤ Subgroup.normalizer (θ : Set G) :=
    (hUc.trans (centralizer_le_normalizer_of_j2 h hJ)).trans
      (Sec6.normalizer_le_normalizer_theta L)
  have hAθ : A ≤ Subgroup.normalizer (θ : Set G) :=
    hD.le_normalizer.trans (Sec6.normalizer_le_normalizer_theta L)
  have hθ2 : IsPGroup 2 θ :=
    (isPGroup_theta_of_j2 h hJ).map L.subtype
  have hθH : θ ≤ H :=
    (Sec6.theta_le L).trans
      (hD.le_centralizer.trans (centralizer_singleton_le_normalizer_zpowers c))
  have hUθ2 : IsPGroup 2 (U ⊔ θ : Subgroup G) := hU2.to_sup_of_normal_right' hθ2 hUθ
  have hinv : U ⊔ θ ∈ invariantPiSubgroups H A (piCompl 3) :=
    ⟨sup_le hUmem.1.2 hθH,
      isPiSubgroup_piCompl_three_of_piOf_two ((isPiSubgroup_piOf_iff Nat.prime_two _).mpr hUθ2),
      le_normalizer_sup hAU hAθ⟩
  have hmem : U ⊔ θ ∈ scriptQPi A (lB A) H (piOf 2) :=
    ⟨⟨(mem_scriptQ_of_hj_point h hJ hinv).1, hinv.1⟩,
      (isPiSubgroup_piOf_iff Nat.prime_two _).mpr hUθ2⟩
  exact le_sup_right.trans (hU.2 hmem le_sup_left)

end Proof152Gen

open Proof152Gen

theorem step152GenTheta_holds :
    Step152GenTheta := by
  intro G _ _ A c L h Y M X _ d p P T K S hD hSH
  exact (theta_le_of_mem_scriptQPiStar h hD.hj hSH).trans le_sup_left

end CFSG.RankThree.PartTwo.Sec15
