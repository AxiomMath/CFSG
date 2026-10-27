module

public import CFSG.LocalAnalysis.UniquenessCase.K340.Vocab

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.InS3.Campbell340

open CFSG.QuasithinUnique.Setup.Campbell

variable {G : Type} [Group G] [Finite G] {H : Subgroup G}

private theorem omegaOneCenterIn_eq_centerTorsion (T : Subgroup G) :
    CFSG.RankThree.PartOne.omegaOneCenterIn T =
      CFSG.Quasithin.BlueprintB2.centerTorsion 2 T := by
  rw [CFSG.RankThree.PartOne.omegaOneCenterIn, CFSG.RankThree.PartOne.omegaOne,
    ← CFSG.Quasithin.BlueprintB2.centerTorsion_eq_closure]

private theorem map_Kodd : (Kodd ↥H).map H.subtype = CFSG.Quasithin.opResidual 2 H := by
  have hset : (H.subtype '' {x : ↥H | x ∈ (⊤ : Subgroup ↥H) ∧ (orderOf x).Coprime 2}) =
      {x : G | x ∈ H ∧ (orderOf x).Coprime 2} := by
    ext y
    constructor
    · rintro ⟨x, ⟨-, hx⟩, rfl⟩
      exact ⟨x.2, by simpa using hx⟩
    · rintro ⟨hy, hx⟩
      refine ⟨⟨y, hy⟩, ⟨trivial, ?_⟩, rfl⟩
      simpa using hx
  rw [Kodd, CFSG.Quasithin.BlueprintB2.pPrimeGen,
    CFSG.Quasithin.opResidual, MonoidHom.map_closure, hset]

theorem map_Fcore :
    (CFSG.QuasithinUnique.Setup.Campbell.Fcore ↥H).map H.subtype =
      omegaOneZJ (CFSG.Open.pCoreOf 2 H) := by
  rw [CFSG.QuasithinUnique.Setup.Campbell.Fcore,
    CFSG.Quasithin.BlueprintB2.map_centerTorsion H.subtype H.subtype_injective,
    ← CFSG.Quasithin.thompsonJ_map_of_injective' H.subtype_injective,
    omegaOneZJ_eq_quasithin, CFSG.Quasithin.BlueprintB2.omegaOneCenterOf_eq_centerTorsion]
  rfl

theorem map_Ecore :
    (CFSG.QuasithinUnique.Setup.Campbell.Ecore ↥H).map H.subtype =
      CFSG.RankThree.PartOne.omegaOneCenterIn (CFSG.Open.pCoreOf 2 H) := by
  rw [CFSG.QuasithinUnique.Setup.Campbell.Ecore,
    CFSG.Quasithin.BlueprintB2.map_centerTorsion H.subtype H.subtype_injective,
    omegaOneCenterIn_eq_centerTorsion]
  rfl

theorem map_Vmod :
    (CFSG.QuasithinUnique.Setup.Campbell.Vmod ↥H).map H.subtype =
      ⁅CFSG.Quasithin.opResidual 2 H,
        CFSG.RankThree.PartOne.omegaOneCenterIn (CFSG.Open.pCoreOf 2 H)⁆ := by
  rw [CFSG.QuasithinUnique.Setup.Campbell.Vmod, Subgroup.map_commutator, map_Ecore, map_Kodd,
    Subgroup.commutator_comm]

section Sylow

variable {T : Subgroup G} (P : Sylow 2 ↥H)
  (hP : (P : Subgroup ↥H).map H.subtype = T)

include hP

theorem hnc_of_not_le_center
    (hZ : ¬ CFSG.RankThree.PartOne.omegaOneCenterIn T ≤
      (Subgroup.center ↥H).map H.subtype) :
    ⁅(⊤ : Subgroup ↥H), CFSG.Open.quasithinOmegaOneCenter (P : Subgroup ↥H)⁆ ≠ ⊥ := by
  intro hbot
  apply hZ
  have hle : CFSG.Open.quasithinOmegaOneCenter (P : Subgroup ↥H) ≤
      Subgroup.center ↥H := by
    rw [Subgroup.commutator_comm, Subgroup.commutator_eq_bot_iff_le_centralizer] at hbot
    simpa [Subgroup.centralizer_univ] using hbot
  have hL : (CFSG.Open.quasithinOmegaOneCenter (P : Subgroup ↥H)).map H.subtype =
      CFSG.RankThree.PartOne.omegaOneCenterIn T := by
    rw [← CFSG.Quasithin.omegaOneCenterOf_eq,
      CFSG.Quasithin.BlueprintB2.omegaOneCenterOf_eq_centerTorsion,
      CFSG.Quasithin.BlueprintB2.map_centerTorsion H.subtype H.subtype_injective, hP,
      ← omegaOneCenterIn_eq_centerTorsion]
  rw [← hL]
  exact Subgroup.map_mono hle

end Sylow

end CFSG.LocalAnalysis.UniquenessCase.UC22.InS3.Campbell340

end
