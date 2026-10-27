module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1G43Rank
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1G43TI
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1G43Lift
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1G43GeomA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1G43GeomB
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1G43Hyp
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1G43Asm

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.WeakClosure81

variable {G : Type} [Group G] [Finite G]

theorem s16c1G43_pack {D : Data G} (h42 : R16_42 D) (h431 : R16_43_1 D) (hkitB : OmegaKitB)
    (hkitC : OmegaKitC) (hkitE : OmegaKitE16) {V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (hS : Sect16 D ⊥ V L hV) (hc : Case167_1 D ⊥ V hV L) {i : ℕ} {A : Subgroup G} {g : G}
    (hy : Hyp1643 D ⊥ V i A g) (hnot : ¬ V ≤ conjSubgroup D.M g) :
    ¬ conjSubgroup V g ≤ D.M ∧ PrimGeom D.M V g := by
  obtain ⟨hVgM, hm, hB16⟩ := s16c1G43_prim h42 hkitB hkitC hS hc hy hnot
  have hBM : conjSubgroup V g ⊓ D.M ≤ D.M := inf_le_right
  have hBg : conjSubgroup V g ⊓ D.M ≤ conjSubgroup V g := inf_le_left
  have hyB : Hyp1643 D ⊥ V 1 (conjSubgroup V g ⊓ D.M) g :=
    ⟨Or.inr ⟨rfl, rfl⟩, ⟨hBM, g, hBg, hm⟩, hBg⟩
  have hBL := h431 ⊥ V L hV hS hc 1 _ g hyB
  obtain ⟨z, P, hE⟩ := s16c1G43_lift hkitE hS hc hBM hBg hBL hB16
  have hker := s16c1G43_relIndex_cent hS hBM hB16
  refine ⟨hVgM, ?_⟩
  exact s16c1G43_primGeom hV hS.setting.hyp151.hyp125.normalizer_eq (s16c1G43_card_V hc) hnot hm
    hker hE (fun b hb hbV v hv hbv => s16c1G43_fixed_mem h42 hS hc hBM hBg hm hB16 hb hbV hv hbv)

theorem r16_43_4_of {D : Data G} (h22 : R1622 D) (h41 : R16_41 D) (h42 : R16_42 D)
    (h431 : R16_43_1 D) (hkitB : OmegaKitB) (hkitC : OmegaKitC) (hkitE : OmegaKitE16) :
    R16_43_4 D := by
  intro V₀ V L hV hS hc i A g hy hV₀
  subst hV₀
  by_cases hnot : V ≤ conjSubgroup D.M g
  · exact Or.inl hnot
  right
  obtain ⟨hVgM, hG⟩ := s16c1G43_pack h42 h431 hkitB hkitC hkitE hS hc hy hnot
  have hy' := s16c1G43_hyp1643_inv (D := D) (V := V) hG.relIndex_U
  have hnot' := s16c1G43_not_le_inv (M := D.M) (V := V) hVgM
  obtain ⟨hVgM', hG'⟩ := s16c1G43_pack h42 h431 hkitB hkitC hkitE hS hc hy' hnot'
  have hM := hS.setting.hyp151.hyp125.normalizer_eq
  have hV64 := s16c1G43_card_V hc
  have hlt := s16c1G43_lt_rStar h22 h41 hS hc
  have hH := s16c1G43_hyp612Sym hV hM hV64 hlt hVgM hnot hG hG'.half
  have hTI : ∀ x : G, conjSubgroup V x ≠ V → Nat.card ↥(V ⊓ conjSubgroup V x) ≤ 4 := by
    intro x hx
    refine s16c1G43_card_inf_le h22 h41 hS hc ?_
    intro hxM
    apply hx
    rw [conjSubgroup_eq_iff_mem_normalizer, hM]
    exact hxM
  obtain ⟨h1, h2⟩ := s16c1G43_asm hH hV64 hG.card_U hG.card_B hG.card_N hTI
  exact ⟨⟨g, rfl, h1⟩, h2⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
