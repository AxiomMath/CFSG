module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.BorelLocal
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.SEFive.CoverLift
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.KInputs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.SEFive

open Subgroup

theorem coverActsTriviallyOnSmall_of_d2Heis {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p)
    {i : TauCeti.CFSGIndex} (hH : CFSG.AGLEmbeddingD2.D2HeisLocalAt i fun q => q = p)
    {L : Type} [Group L] [Finite L] [IsSimpleGroup L] (e : L ≃* i.Group) :
    CoverActsTriviallyOnSmall p L := by
  rcases Subgroup.Normal.eq_bot_or_eq_top (Subgroup.center L) with hZ | hZ
  ·
    obtain ⟨R⟩ := Sylow.nonempty (p := p) (G := L)
    have hC : Subgroup.centralizer ((⊤ : Subgroup L) : Set L) = ⊥ := by
      rw [Subgroup.coe_top, Subgroup.centralizer_univ, hZ]
    obtain ⟨-, -, -, -, hZcard, hcomm, -⟩ :=
      hH L ⊤ inferInstance hC ⟨Subgroup.topEquiv.trans e⟩ p rfl R
    have hnc : ∃ a ∈ (R : Subgroup L), ∃ b ∈ (R : Subgroup L), a * b ≠ b * a := by
      by_contra h
      push Not at h
      have hle : (R : Subgroup L) ≤ Subgroup.centralizer ((R : Subgroup L) : Set L) := by
        intro a ha
        rw [Subgroup.mem_centralizer_iff]
        exact fun b hb => h b hb a ha
      have hbot : ⁅(R : Subgroup L), (R : Subgroup L)⁆ = ⊥ :=
        (Subgroup.commutator_eq_bot_iff_le_centralizer (H₁ := (R : Subgroup L))
          (H₂ := (R : Subgroup L))).mpr hle
      rw [hcomm] at hbot
      rw [hbot, Subgroup.card_bot] at hZcard
      exact (Fact.out : p.Prime).ne_one hZcard.symm
    exact coverActsTriviallyOnSmall_of_nonabelian Fact.out hp5 R.isPGroup' hnc
  ·
    intro J _ _ hJ φ hφ
    exfalso
    haveI : Group.IsPerfect J := hJ
    haveI : Group.IsPerfect L := Group.IsPerfect.ofSurjective (f := φ) hφ
    have hcommL : ∀ a b : L, a * b = b * a :=
      isMulCommutative_iff.mp (Subgroup.center_eq_top_iff.mp hZ)
    exact Group.IsPerfect.not_isSolvable L ((IsSimpleGroup.comm_iff_isSolvable).mp hcommL)

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.SEFive
