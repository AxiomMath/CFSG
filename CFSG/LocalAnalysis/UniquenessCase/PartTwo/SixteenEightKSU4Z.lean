module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKSU4ZPre
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKSU4ZCase
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC4V1Main

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G] {D : Data G} {V₀ V L : Subgroup G}
  {hV : IsElemAbelian 2 V}

theorem s16k_false_of_su4_z (h : S16gRowCtx D V₀ V L hV)
    (hGA : CFSG.Open.GriessAllModelsStatement)
    (hSU : IsSUn ↥(lBar V₀ V hV L) 4 1)
    (hN : NatSUn (lBar V₀ V hV L) (commSub ⊤ (lBar V₀ V hV L))
      (commSub ⊤ (lBar V₀ V hV L) ⊓ fixV (lBar V₀ V hV L)) 4 1)
    (hσ : 3 ∈ D.sig) (hrk : 4 ≤ CFSG.Open.pRank 3 (Mbar D.M V₀ V hV))
    (hZ : fixV (lBar V₀ V hV L) ≠ ⊥) : False := by
  have hV0 : V₀ = ⊥ := s16k_su4z_v0 h hZ
  have hstd : s16c4v1_Std D := ⟨h.std.hx, h.std.hSg, h.std.h1219, h.std.h61, h.std.h126,
    h.std.h111, r129_1_of_r127 D h.std.h127, h.std.h1217, h.std.h4⟩
  have hne : barSub V₀ V hV L ≠ ⊥ := fun hb => by
    haveI := h.quasi.2.toNontrivial
    haveI : Nontrivial ↥(lBar V₀ V hV L) :=
      (QuotientGroup.mk'_surjective (Subgroup.center ↥(lBar V₀ V hV L))).nontrivial
    exact (Subgroup.nontrivial_iff_ne_bot _).1 ‹_› hb
  have h4 : Case167_4 D V₀ V hV L := s16k_su4z_case4 h hGA hSU hN hσ hV0
  have hV1 := s16c4v1_holds D hstd V₀ V L hV ⟨h.setting, hne, h.conc⟩ h4 hV0
  exact s16k_su4z_v1_ne_bot h hV0 hZ (hV1.trans hV0)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
