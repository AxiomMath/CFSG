module

public import CFSG.Quasithin.Background.C2PushA3
public import CFSG.Quasithin.Background.C129Used
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L238FourConj
public import CFSG.Quasithin.Background.C2PushBlocks

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

namespace S1421

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem isChi0Block_conjByElt {X B : Subgroup G} (hB : IsChi0Block X B) {s : G} (hs : s ∈ X) :
    IsChi0Block X (conjByElt s B) := by
  obtain ⟨hblock, htype⟩ := hB
  refine ⟨IsBlock2.conjByElt_of_mem hblock hs, ?_⟩
  rcases htype with ⟨n, hn, hlin⟩ | h3 | h5
  · exact Or.inl ⟨n, hn, Lin2.IsLin2Type.map_equiv hlin (MulAut.conj s)⟩
  · exact Or.inr (Or.inl (L238.IsAltType.map_equiv h3 (MulAut.conj s)))
  · exact Or.inr (Or.inr (L238.IsAltType.map_equiv h5 (MulAut.conj s)))

theorem le_or_isChi0Block_of_asc129_used (h129 : ASC129StatementUsed G) {M R H L : Subgroup G}
    (hMc : CharTwo M) (hMs : IsSQTKIn M) (hR : IsTwoRadicalIn M R) (hcgs : cgsIn M R ≤ H)
    (hL : L ∈ cComp M) (hLq : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L))
    (hsyl : IsSylowTwoOf (R ⊓ L) L) :
    L ≤ H ∨ IsChi0Block (conjClosure L R ⊔ R) L := by
  set Y : Subgroup G := conjClosure L R ⊔ R with hY
  have hRM : R ≤ M := hR.1
  have hLM : L ≤ M := le_of_mem_cComp hL
  have hYM : Y ≤ M := C2Push.conjClosure_sup_le hRM hLM
  have hRY : R ≤ Y := le_sup_right
  have hRH : R ≤ H := fun x hx =>
    hcgs (inf_normalizer_le_cgsIn hR.2.1 ⟨hRM hx, Subgroup.le_normalizer hx⟩)
  have hYsyl : IsSylowTwoOf R Y := C2Push.isSylowTwoOf_conjClosure_sup hR hL hLq hsyl
  have hYc : CharTwo Y :=
    C2Push.charTwo_of_pCoreOf_le hMc ((c2_1_pCore_le hR).trans hRY) hYM
  have hYs : IsSQTKIn Y := hMs.mono hYM
  have hcgsY : cgsIn Y R ≤ Y ⊓ H :=
    le_inf (cgsIn_le Y R) ((C2Nine.cgsIn_mono_left hYM R).trans hcgs)
  obtain ⟨r, Lb, -, hLb, hprod⟩ := h129 Y R (Y ⊓ H) hYs hYc hYsyl hcgsY inf_le_left
  by_cases hq : ∃ i, ¬ Nat.card (↥(Lb i) ⧸ CFSG.pCore 2 ↥(Lb i)) = 3
  · right
    obtain ⟨i, hi⟩ := hq
    have hBq : CFSG.IsQuasisimple (↥(Lb i) ⧸ CFSG.pCore 2 ↥(Lb i)) :=
      ((hLb i).1.1.1.2.2.2.1).resolve_right hi
    obtain ⟨s, hs, hBs⟩ := C2Push.exists_eq_conjByElt_of_isBlock2 hR hL hLq (hLb i).1.1 hBq
    have hsY : s⁻¹ ∈ Y := Y.inv_mem (Subgroup.mem_sup_right hs)
    have h1 : IsChi0Block Y (conjByElt s⁻¹ (Lb i)) := isChi0Block_conjByElt (hLb i).1 hsY
    have h2 : conjByElt s⁻¹ (Lb i) = L := by
      ext x
      rw [hBs, mem_conjByElt, mem_conjByElt]
      simp [mul_assoc]
    rwa [h2] at h1
  · left
    push Not at hq
    exact C2Push.le_of_isBlock2_card_three hL hLq hRM hYsyl hRH Lb
      (fun i => ⟨(hLb i).1.1, hq i⟩) hprod

end S1421

end CFSG.Quasithin
