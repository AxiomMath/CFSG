module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.NormalCThreeCentral
public import CFSG.RankThree.PartOne.S9.Sylow.GlobalBridge
public import CFSG.GroupTheory.PGroup.OmegaComm
public import CFSG.RankThree.PartOne.Assembly

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.RankThree.PartOne

theorem omegaOne_le_center_of_normal_cyclic
    {G : Type} [Group G] [Finite G] (hG : IsPGroup 3 G) {C : Subgroup G}
    (hCnorm : C.Normal) (hCcyc : IsCyclic C) :
    CFSG.RankThree.PartOne.omegaOne 3 C ≤ Subgroup.center G := by
  classical
  haveI : C.Normal := hCnorm
  haveI : IsCyclic C := hCcyc
  have htop : (CFSG.omega₁ (G := C) (p := 3)) = omegaOne 3 (⊤ : Subgroup C) := by
    ext x
    simp [CFSG.omega₁, CFSG.omega, omegaOne]
  have hmap : (omegaOne 3 (⊤ : Subgroup C)).map C.subtype = omegaOne 3 C := by
    have h := CFSG.RankThree.PartOne.Sec9B.map_omegaOne (f := C.subtype) C.subtype_injective 3
      (⊤ : Subgroup C)
    simpa [Subgroup.map_top, Subgroup.range_subtype] using h
  have hΩeq : omegaOne 3 C = (CFSG.omega₁ (G := C) (p := 3)).map C.subtype := by
    rw [htop]
    exact hmap.symm
  have hΩnorm : (omegaOne 3 C).Normal := by
    rw [hΩeq]
    haveI : (CFSG.omega₁ (G := C) (p := 3)).Characteristic := CFSG.omega₁_characteristic C
    infer_instance
  have hcard : Nat.card (omegaOne 3 C) = (Nat.card C).gcd 3 := by
    rw [hΩeq, Subgroup.card_subtype]
    exact CFSG.card_omega₁_of_isCyclic (X := C) (p := 3)
  have hdvd : Nat.card (omegaOne 3 C) ∣ 3 := by
    rw [hcard]
    exact Nat.gcd_dvd_right (Nat.card C) 3
  rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
  · have hbot : omegaOne 3 C = ⊥ :=
      Subgroup.eq_bot_of_card_eq (omegaOne 3 C) h1
    rw [hbot]
    exact bot_le
  · exact normal_card_three_le_center_of_isPGroup_three hG hΩnorm h3

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
