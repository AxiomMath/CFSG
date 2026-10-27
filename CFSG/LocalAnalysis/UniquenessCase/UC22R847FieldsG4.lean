module

public import CFSG.LocalAnalysis.UniquenessCase.UC22R847Fields
public import CFSG.LocalAnalysis.UniquenessCase.UC22R847G4
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ProofsThirtySevenPrelim
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section21.ProofsNine
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section21.ProofsNineteenN

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup

variable {G : Type} [Group G] [Finite G]

theorem r847ThinCZ_of_r847G4 {D : Data G} (h : R847G4 D) (hsig : D.sig.Nonempty) :
    R847ThinCZ D := by
  intro Y hY hthin X hXY hXp hX2 hO2
  obtain ⟨p, hp⟩ := hsig
  rcases h Y hY X hXY _ hXp hX2 rfl p hp (Or.inl hthin) with
    h1 | ⟨n, hSU, hn6, -⟩ | ⟨ℓ, f, -, -, hbot, -⟩
  · exact h1
  · exact absurd hthin (not_thin8_of_isSU3 hSU (Nat.odd_iff.2 (by omega)))
  · exact absurd hbot hO2

theorem r847ThinPair_of_r847G4 {D : Data G} (h : R847G4 D) (hsig : D.sig.Nonempty) :
    R847ThinPair D := by
  intro Y hY _ hthin _ K hK hKY _ X hXY hXp hX2
  obtain ⟨p, hp⟩ := hsig
  rcases h Y hY X hXY _ hXp hX2 rfl p hp (Or.inl hthin) with
    h1 | ⟨n, hSU, hn6, -⟩ | ⟨ℓ, f, -, -, -, -, A', hGrpA, hLieA, hnf⟩
  · exact h1
  · exact absurd hthin (not_thin8_of_isSU3 hSU (Nat.odd_iff.2 (by omega)))
  · let : Group A' := hGrpA
    let : IsSimpleGroup A' :=
      CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (t := .PSL) (by decide) hLieA
    exact (not_nonempty_mulEquiv_fstar_of_ne D hY hK hKY.symm (A := A')
      (B := Multiplicative (ZMod 3) × Multiplicative (ZMod 3)) (fun a b => mul_comm a b) hnf).elim

theorem r847SU3G4_of_r847G4 {D : Data G} (h : R847G4 D) : R847SU3G4 D := by
  intro Y hY _ n hSU X hXY q hq hq2 hqn hXq p hp
  have hmod : 2 ^ (2 * n) ≡ 1 [MOD q] := by
    have hsq : q ∣ 2 ^ (2 * n) - 1 := by
      rw [show 2 ^ (2 * n) = (2 ^ n) ^ 2 by rw [mul_comm, pow_mul]]
      exact hqn.trans (Nat.sub_one_dvd_pow_sub_one (2 ^ n) 2)
    exact ((Nat.modEq_iff_dvd' Nat.one_le_two_pow).mpr hsq).symm
  rcases h Y hY X hXY q hq hq2 hXq p hp (Or.inr ⟨n, hSU, hmod⟩) with
    h1 | ⟨n', hSU', hn6, -, hp3, he, -⟩ | ⟨ℓ, f, hlie, -⟩
  · exact Or.inl h1
  · have hnn : n = n' := PartTwo.S17.uc2_17_36b_isSU3_param_eq hSU hSU'
    subst hnn
    exact Or.inr ⟨hp3, hn6, he⟩
  · exact absurd hlie (not_lieModel_psl2_of_isSU3 hSU)

end CFSG.LocalAnalysis.UniquenessCase.UC22
