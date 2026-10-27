module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.G3CompBasic
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.Defs
public import CFSG.LocalAnalysis.QuasithinUnique.GammaFamilies
public import CFSG.Quasithin.Background.C2PushA3
public import CFSG.Quasithin.Background.C2PushBlocks
public import CFSG.Quasithin.Background.F1Models

public section

namespace CFSG.Quasithin.S146zV

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.C2Push
open CFSG.QuasithinUnique.Lin2 (IsLin2Type.map_equiv)

variable {G : Type} [Group G] [Finite G]

theorem isBorelOfBlock_map_conj {L B : Subgroup G} (h : IsBorelOfBlock L B) (s : G) :
    IsBorelOfBlock (L.map (MulAut.conj s).toMonoidHom) (B.map (MulAut.conj s).toMonoidHom) := by
  set f : G ≃* G := MulAut.conj s with hf
  have hQ : pCoreOf 2 (L.map f.toMonoidHom) = (pCoreOf 2 L).map f.toMonoidHom :=
    pCoreOf_map_equiv 2 f L
  let φ : L ≃* (L.map f.toMonoidHom : Subgroup G) :=
    Subgroup.equivMapOfInjective L f.toMonoidHom f.injective
  have e : (↥L ⧸ CFSG.pCore 2 ↥L) ≃*
      ((L.map f.toMonoidHom : Subgroup G) ⧸ CFSG.pCore 2 (L.map f.toMonoidHom : Subgroup G)) :=
    QuotientGroup.congr _ _ φ (CFSG.pCore_map_iso 2 φ)
  have hcard : Nat.card ((L.map f.toMonoidHom : Subgroup G) ⧸
      CFSG.pCore 2 (L.map f.toMonoidHom : Subgroup G)) = Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) :=
    (Nat.card_congr e.toEquiv).symm
  unfold IsBorelOfBlock at h ⊢
  rw [hcard]
  split_ifs at h ⊢
  · rw [hQ]
    exact Subgroup.map_mono h
  · obtain ⟨S, hS, hSB⟩ := h
    refine ⟨S.map f.toMonoidHom, hS.map_equiv f, ?_⟩
    rw [hQ, ← Subgroup.map_sup, hSB, map_equiv_inf, normalizer_map_equiv]

theorem exists_block_data_of_asc129 (h129 : ASC129Statement G) {M R H L : Subgroup G}
    (hMc : CharTwo M) (hMs : IsSQTKIn M) (hR : IsTwoRadicalIn M R) (hcgs : cgsIn M R ≤ H)
    (hL : L ∈ cComp M) (hLq : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L))
    (hsyl : IsSylowTwoOf (R ⊓ L) L) (hLH : ¬ L ≤ H) :
    IsShort2 L ∧ ((∃ n : ℕ, 1 < n ∧ IsLin2Type L n) ∨ IsAltType L 5) ∧
      IsBorelOfBlock L (L ⊓ H) := by
  set Y : Subgroup G := conjClosure L R ⊔ R with hY
  have hRM : R ≤ M := hR.1
  have hLM : L ≤ M := le_of_mem_cComp hL
  have hYM : Y ≤ M := conjClosure_sup_le hRM hLM
  have hRY : R ≤ Y := le_sup_right
  have hLY : L ≤ Y := (le_conjClosure L R).trans le_sup_left
  have hRH : R ≤ H := fun x hx =>
    hcgs (inf_normalizer_le_cgsIn hR.2.1 ⟨hRM hx, Subgroup.le_normalizer hx⟩)
  have hYsyl : IsSylowTwoOf R Y := isSylowTwoOf_conjClosure_sup hR hL hLq hsyl
  have hYc : CharTwo Y := charTwo_of_pCoreOf_le hMc ((c2_1_pCore_le hR).trans hRY) hYM
  have hYs : IsSQTKIn Y := hMs.mono hYM
  have hcgsY : cgsIn Y R ≤ Y ⊓ H :=
    le_inf (cgsIn_le Y R) ((C2Nine.cgsIn_mono_left hYM R).trans hcgs)
  obtain ⟨r, Lb, -, hLb, hprod⟩ := h129 Y R (Y ⊓ H) hYs hYc hYsyl hcgsY inf_le_left
  by_cases hq : ∃ i, ¬ Nat.card (↥(Lb i) ⧸ CFSG.pCore 2 ↥(Lb i)) = 3
  · obtain ⟨i, hi⟩ := hq
    have hBq : CFSG.IsQuasisimple (↥(Lb i) ⧸ CFSG.pCore 2 ↥(Lb i)) :=
      ((hLb i).1.1.1.2.2.2.1).resolve_right hi
    obtain ⟨ρ, hρ, hBρ⟩ := exists_eq_conjByElt_of_isBlock2 hR hL hLq (hLb i).1.1 hBq
    have hρY : ρ⁻¹ ∈ Y := Y.inv_mem (Subgroup.mem_sup_right hρ)
    set c : G ≃* G := MulAut.conj ρ⁻¹ with hc
    have hBL : (Lb i).map c.toMonoidHom = L := by
      rw [hBρ]
      unfold conjByElt
      rw [Subgroup.map_map]
      have : c.toMonoidHom.comp (MulAut.conj ρ).toMonoidHom = MonoidHom.id G := by
        ext x
        simp [hc, MulAut.conj_apply, mul_assoc]
      rw [this, Subgroup.map_id]
    have hYc' : Y.map c.toMonoidHom = Y :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer hρY)
    have hHc : H.map c.toMonoidHom = H :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer (H.inv_mem (hRH hρ)))
    obtain ⟨hchi, hBor, -⟩ := hLb i
    refine ⟨?_, ?_, ?_⟩
    · have := (A5.G3.isChi0Block_conj hchi hρY).1.1
      rwa [hBL] at this
    · rcases hchi.2 with ⟨n, hn, hlin⟩ | h3 | h5
      · left
        refine ⟨n, hn, ?_⟩
        have := IsLin2Type.map_equiv hlin c
        rwa [hBL] at this
      · exact absurd (C2Six.natCard_pCore_quotient_of_isAltType_three h3) hi
      · right
        have := L238.IsAltType.map_equiv h5 c
        rwa [hBL] at this
    · have h1 := isBorelOfBlock_map_conj hBor ρ⁻¹
      have h2 : (Lb i ⊓ (Y ⊓ H)).map (MulAut.conj ρ⁻¹).toMonoidHom = L ⊓ H := by
        rw [← hc, map_equiv_inf, map_equiv_inf, hBL, hYc', hHc]
        ext x
        exact ⟨fun hx => ⟨hx.1, hx.2.2⟩, fun hx => ⟨hx.1, hLY hx.1, hx.2⟩⟩
      rw [← hc] at h1
      rw [h2, hBL] at h1
      exact h1
  · push Not at hq
    exact absurd (le_of_isBlock2_card_three hL hLq hRM hYsyl hRH Lb
      (fun i => ⟨(hLb i).1.1, hq i⟩) hprod) hLH

end CFSG.Quasithin.S146zV
