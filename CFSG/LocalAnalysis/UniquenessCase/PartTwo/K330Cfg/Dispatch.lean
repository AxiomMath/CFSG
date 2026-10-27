module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.K330Cfg.FamAssembly
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.K330Cfg.ArithGroups
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.K330Cfg.Big27Exc
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.K330Cfg.Big27L3
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.K330Cfg.Big27Spor
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.K330Cfg.FamM23Aut
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.K330Cfg.FamPSL3Heis
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.K330Cfg.FamPSU3Heis
public import CFSG.LocalAnalysis.UniquenessCase.UCKInputs2

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.K330Cfg

open CFSG.Open Subgroup
open scoped commutatorElement
open CFSG.Blueprint (LieModel)
open CFSG.LocalAnalysis.UniquenessCase.UC22 (IsAlt IsSpor)
open CFSG.LocalAnalysis.UniquenessCase.UCK (ThreeCover)

theorem k33_hyps_of_sit {J : Type} [Group J] [Finite J] (hs : Sit J) :
    CFSG.Open.IsQuasisimple J ∧ CFSG.Open.IsCatalogGroup (J ⧸ Subgroup.center J) ∧
      IsPGroup 3 (Subgroup.center J) ∧ CFSG.Open.pRank 3 (⊤ : Subgroup J) = 2 := by
  have hcen := center_eq_bot_of_sit hs
  obtain ⟨hsimple, ⟨a, b, hab⟩, hcat, hrank, -⟩ := hs
  haveI := hsimple
  have e : (J ⧸ Subgroup.center J) ≃* J :=
    (QuotientGroup.quotientMulEquivOfEq hcen).trans QuotientGroup.quotientBot
  refine ⟨⟨?_, e.isSimpleGroup⟩, ?_, ?_, hrank⟩
  · rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator J) with h | h
    · exfalso
      apply hab
      have h1 : ⁅a, b⁆ ∈ commutator J := commutator_mem_commutator (Subgroup.mem_top a)
        (Subgroup.mem_top b)
      rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
      exact h1
    · exact h
  · exact CFSG.AGLEmbedding.IsCatalogGroup.of_mulEquiv e hcat
  · rw [hcen]; exact IsPGroup.of_card (n := 0) (by simp)


theorem excl_of_k33 (hK33 : CFSG.LocalAnalysis.UniquenessCase.UCK.K33) {J : Type} [Group J]
    [Finite J] (hs : Sit J) : Excl J := by
  obtain ⟨hq, hcat, hZ, hr⟩ := k33_hyps_of_sit hs
  have hcen := center_eq_bot_of_sit hs
  have hno : ∀ {S : ∀ (Y : Type) [Group Y], Prop}, ThreeCover S J → False := by
    intro S h
    have h3 := h.2.1
    rw [hcen, Subgroup.card_bot] at h3
    omega
  rcases hK33 J hq hcat hZ hr with
    (h | h | h | ⟨p, f, -, h⟩ | ⟨p, f, -, h⟩) | (h | h) | (h | h) |
    (⟨p, f, hq3, e⟩ | ⟨p, f, hq3, e⟩ | ⟨p, f, e⟩ | ⟨p, f, e⟩ | ⟨p, f, e⟩ | ⟨f, e⟩ | e |
      ⟨p, f, hq3, e⟩ | ⟨p, f, hq3, e⟩ | ⟨p, f, hq3, e⟩ | ⟨p, f, hq3, e⟩) |
    ⟨s, hsl, e⟩
  · exact (hno h).elim
  · exact (hno h).elim
  · exact (hno h).elim
  · exact (hno h).elim
  · exact (hno h).elim
  · exact excl_alt_seven h
  · exact excl_alt_six h
  · exact excl_L3_three h
  · exact excl_U3_three h
  · exact Or.inr (Or.inr (Or.inl (automizerBig_of_heis (hasHeis_PSL3 e hq3))))
  · exact Or.inr (Or.inr (Or.inl (automizerBig_of_heis (hasHeis_PSU3 e hq3))))
  · exact excl_PSp4 hs e
  · exact excl_G2 e
  · exact excl_3D4 e
  · exact excl_2F4 e
  · exact excl_Tits e
  · exact excl_PSL 4 (Or.inl rfl) hs e hq3
  · exact excl_PSU 4 (Or.inl rfl) hs e hq3
  · exact excl_PSL 5 (Or.inr rfl) hs e hq3
  · exact excl_PSU 5 (Or.inr rfl) hs e hq3
  · rcases hsl with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact excl_M11 e
    · exact excl_M12 e
    · exact excl_M22 e
    · exact Or.inr (Or.inr (Or.inl (automizerBig_M23 e)))
    · exact excl_M24 e
    · exact excl_J2 e
    · exact excl_HS e
    · exact excl_He e
    · exact excl_Ru e
    · exact excl_J4 e

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.K330Cfg
