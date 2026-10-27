module

public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenTools
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
variable {G : Type} [Group G] [Finite G]

theorem s16h_e3_CycThreeCent_fix_of_centSub
    (D : Data G) {V₀ V L : Subgroup G} (hV : IsElemAbelian 2 V) (h : Setting16 D V₀ V L)
    {X Y : Subgroup G} (hX : X ∈ wConj D.M V₀ V hV L) (hY : Y ∈ wConj D.M V₀ V hV L)
    {φ : MulAut (Vtil V₀ V hV)} (hφX : φ ∈ centSub (imgTil V₀ V hV X))
    (hφY : φ ∈ centSub (imgTil V₀ V hV Y)) {u : G} (hu : u ∈ X ⊔ Y) (huV : u ∈ V) :
    φ (mkTil V₀ V hV (IntMod.mk hV ⟨u, huV⟩)) = mkTil V₀ V hV (IntMod.mk hV ⟨u, huV⟩) := by
  have hXV : X ≤ V := by
    rcases hX with ⟨m, hm, rfl⟩
    exact s15_Tools_conj_wSub_le D h.hyp151.hyp125 hV hm
  have hYV : Y ≤ V := by
    rcases hY with ⟨m, hm, rfl⟩
    exact s15_Tools_conj_wSub_le D h.hyp151.hyp125 hV hm
  have hmem : IntMod.mk hV ⟨u, huV⟩ ∈ X.subgroupOf V ⊔ Y.subgroupOf V := by
    rw [← Subgroup.subgroupOf_sup hXV hYV]
    exact (mem_intSub V hV (X ⊔ Y) _).2 hu
  obtain ⟨y, hy, z, hz, hyz⟩ := Subgroup.mem_sup.1 hmem
  have hyX : y.val ∈ X := (mem_intSub V hV X y).1 hy
  have hzY : z.val ∈ Y := (mem_intSub V hV Y z).1 hz
  have hfixy : φ (mkTil V₀ V hV y) = mkTil V₀ V hV y :=
    (mem_centSub.1 hφX) _ ((mem_imgTil V₀ V hV X _).2 ⟨y, hyX, rfl⟩)
  have hfixz : φ (mkTil V₀ V hV z) = mkTil V₀ V hV z :=
    (mem_centSub.1 hφY) _ ((mem_imgTil V₀ V hV Y _).2 ⟨z, hzY, rfl⟩)
  calc
    φ (mkTil V₀ V hV (IntMod.mk hV ⟨u, huV⟩))
        = φ (mkTil V₀ V hV (y * z)) := by rw [← hyz]
    _ = φ (mkTil V₀ V hV y * mkTil V₀ V hV z) := by rw [map_mul]
    _ = φ (mkTil V₀ V hV y) * φ (mkTil V₀ V hV z) := by rw [map_mul]
    _ = mkTil V₀ V hV y * mkTil V₀ V hV z := by rw [hfixy, hfixz]
    _ = mkTil V₀ V hV (y * z) := by rw [map_mul]
    _ = mkTil V₀ V hV (IntMod.mk hV ⟨u, huV⟩) := by rw [hyz]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
