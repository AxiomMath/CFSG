module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P22sl
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22sk
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22sc
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22sa
import CFSG.LocalAnalysis.UniquenessCase.UC22P22si
import CFSG.LocalAnalysis.UniquenessCase.UC22P22sj
import CFSG.LocalAnalysis.UniquenessCase.UC22P22e
import CFSG.RankThree.PartOne.S12.Sec15Final
import CFSG.LocalAnalysis.QuasithinUnique.CharTwoInheritance
import CFSG.Quasithin.Background.A4V
import CFSG.Quasithin.EmptyFaithful.SBd5Perf
import CFSG.Quasithin.Background.C118NoOuterAct

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open Subgroup CFSG.Open CFSG.LocalAnalysis.RankThreeUC
open CFSG.Quasithin (MinParabolic IsTwoReducedIn VZ thompsonJ baum)
open CFSG.RankThree.PartOne (InClassG tripleE tripleV InClassX oResidualTwo omegaOne omegaOneCenterIn)
open CFSG.LocalAnalysis.UniquenessCase.UC22.F12 (jOf)
open scoped commutatorElement
open P22x P22s

variable {G : Type} [Group G] [Finite G]

namespace P22s

theorem charTwo_of_isSubnormal' {H K : Subgroup G} (hK : CFSG.QuasithinUnique.CharTwo K)
    (h : CFSG.Open.IsSubnormal H K) : CFSG.QuasithinUnique.CharTwo H := by
  induction h with
  | refl => exact hK
  | step hle hN _ ih => exact CFSG.QuasithinUnique.CharTwo.of_normal (ih hK) hle hN

theorem mem_tripleE_iff {S H : Subgroup G} (hSH : S ≤ H) (s : ↥S) :
    Subgroup.inclusion hSH s ∈ tripleE ↥H ↔ (s : G) ∈ omegaZJ22 (pCoreOf 2 H) := by
  rw [← map_tripleE H]
  constructor
  · intro h
    exact ⟨_, h, rfl⟩
  · rintro ⟨y, hy, hys⟩
    have : y = Subgroup.inclusion hSH s := Subtype.ext hys
    rwa [← this]

theorem omegaZJ22_le_of_inClassG {S H : Subgroup G} (hSH : S ≤ H)
    (hG : InClassG ↥S ↥H (Subgroup.inclusion hSH)) : omegaZJ22 (pCoreOf 2 H) ≤ S := by
  rw [← map_tripleE H]
  rintro _ ⟨y, hy, rfl⟩
  obtain ⟨s, hs⟩ := tripleE_le_range hG hy
  rw [← hs]
  exact s.2

theorem omegaZJ22_eq_of_comap_eq {S H₁ H₂ : Subgroup G} (h₁ : S ≤ H₁) (h₂ : S ≤ H₂)
    (hG₁ : InClassG ↥S ↥H₁ (Subgroup.inclusion h₁)) (hG₂ : InClassG ↥S ↥H₂ (Subgroup.inclusion h₂))
    (h : (tripleE ↥H₁).comap (Subgroup.inclusion h₁) = (tripleE ↥H₂).comap (Subgroup.inclusion h₂)) :
    omegaZJ22 (pCoreOf 2 H₁) = omegaZJ22 (pCoreOf 2 H₂) := by
  have key : ∀ y : G, y ∈ omegaZJ22 (pCoreOf 2 H₁) → y ∈ S → y ∈ omegaZJ22 (pCoreOf 2 H₂) := by
    intro y hy hyS
    have hmem : (⟨y, hyS⟩ : ↥S) ∈ (tripleE ↥H₁).comap (Subgroup.inclusion h₁) := (mem_tripleE_iff h₁ _).2 hy
    rw [h] at hmem
    exact (mem_tripleE_iff h₂ _).1 hmem
  have key' : ∀ y : G, y ∈ omegaZJ22 (pCoreOf 2 H₂) → y ∈ S → y ∈ omegaZJ22 (pCoreOf 2 H₁) := by
    intro y hy hyS
    have hmem : (⟨y, hyS⟩ : ↥S) ∈ (tripleE ↥H₂).comap (Subgroup.inclusion h₂) := (mem_tripleE_iff h₂ _).2 hy
    rw [← h] at hmem
    exact (mem_tripleE_iff h₁ _).1 hmem
  exact le_antisymm (fun y hy => key y hy (omegaZJ22_le_of_inClassG h₁ hG₁ hy))
    (fun y hy => key' y hy (omegaZJ22_le_of_inClassG h₂ hG₂ hy))

theorem Z_le_omegaOneCenterIn (D : Data G) : D.Z ≤ omegaOneCenterIn (proofS D) := by
  intro z hz
  obtain ⟨hzT, hzc, hz2⟩ := CFSG.RankThree.PartOne.Sec15Final.mem_omegaOneCenterIn_iff.1 hz
  have hzS : z ∈ proofS D := ⟨hzT, Subgroup.mem_centralizer_iff.2 fun e he =>
    hzc e (uc22p22e_mem_omegaZJ'.1 he).1⟩
  exact CFSG.RankThree.PartOne.Sec15Final.mem_omegaOneCenterIn_iff.2
    ⟨hzS, fun k hk => hzc k hk.1, hz2⟩

end P22s

end CFSG.LocalAnalysis.UniquenessCase.UC22
