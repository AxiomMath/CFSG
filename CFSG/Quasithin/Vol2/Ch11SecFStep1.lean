module

public import CFSG.Quasithin.Vol2.Ch11SecFBasic
public import CFSG.Quasithin.Vol2.Ch11SecD556B
public import CFSG.Quasithin.Vol2.Ch11SecFFacts

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecF

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.H13

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G} {n : ℕ} {V₁ : Subgroup G}

theorem commutator_fsuV_le (hF : Sp4Facts) (h1102 : Stmt11_0_2) (h1141 : Stmt11_4_1)
    (h1154 : Stmt11_5_4) (h1156 : Stmt11_5_6) (h : Hyp11 G T L I n) (hV₁ : IsVi T L I n 1 V₁)
    (hk : KindSp4 L (fsuV T I) n) :
    ⁅fsuV T I, KOf L V₁ V₁ ⊔ (Subgroup.centralizer (V₁ : Set G) ⊓
        sectionCentralizer (KOf L V₁ V₁) (pCoreOf 2 (KOf L V₁ V₁)))⁆ ≤
      pCoreOf 2 (KOf L V₁ V₁ ⊔ (Subgroup.centralizer (V₁ : Set G) ⊓
        sectionCentralizer (KOf L V₁ V₁) (pCoreOf 2 (KOf L V₁ V₁)))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨X, hX⟩ := SecD.exists_isCartanX h
  set K := KOf L V₁ V₁ with hKdef
  set Y := Subgroup.centralizer (V₁ : Set G) ⊓ sectionCentralizer K (pCoreOf 2 K) with hYdef
  obtain ⟨-, -, -, -, h64, h65, -⟩ := h1156 G T L I n V₁ X (Subgroup.normalizer (V₁ : Set G))
    h hV₁ hX (inH_normalizer_V₁ h hV₁) (normalizer_V₁_not_le h1154 h hV₁) le_rfl
  have hVX : ⁅fsuV T I, X⁆ = fsuV T I :=
    hF.cartanFree G T L I n X (SecD.natSetting11_of h1102 h1141 h hV₁) hk hX
  have hVY : ⁅fsuV T I, Y⁆ ≤ pCoreOf 2 Y := by
    refine h64 (fsuV T I) hVX.symm (SecA.fsuV_le_T h) ?_
    rw [frattini_map_eq_bot (SecA.isElemAbelian_fsuV h)]
    exact bot_le
  have hVKT : fsuV T I ≤ pCoreOf 2 (K ⊔ T) := by
    calc fsuV T I = ⁅fsuV T I, X⁆ := hVX.symm
      _ ≤ ⁅pCoreOf 2 (L ⊔ T), X⁆ := Subgroup.commutator_mono (fsuV_le_pCoreOf_sup h) le_rfl
      _ ≤ pCoreOf 2 (K ⊔ T) := h65
  have hG₁K : Subgroup.normalizer (V₁ : Set G) ≤ Subgroup.normalizer (K : Set G) :=
    SecD.normalizer_le_normalizer_kOf L V₁ V₁
  have hG₁Y : Subgroup.normalizer (V₁ : Set G) ≤ Subgroup.normalizer (Y : Set G) :=
    SecD.normalizer_le_normalizer_Y L V₁
  have hVK : ⁅fsuV T I, K⁆ ≤ pCoreOf 2 K :=
    commutator_le_pCoreOf_of_le ((SecA.IsVi.le_normalizer hV₁).trans hG₁K) hVKT
  have hKY : K ⊔ Y ≤ Subgroup.normalizer (V₁ : Set G) :=
    sup_le (kOf_le_normalizer_V₁ L V₁) (Y_le_normalizer_V₁ L V₁)
  have hKYO : K ⊔ Y ≤ Subgroup.normalizer (pCoreOf 2 (K ⊔ Y) : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _
  have hOK : pCoreOf 2 K ≤ pCoreOf 2 (K ⊔ Y) :=
    pCoreOf_le_pCoreOf_of_le_normalizer le_sup_left (hKY.trans hG₁K)
  have hOY : pCoreOf 2 Y ≤ pCoreOf 2 (K ⊔ Y) :=
    pCoreOf_le_pCoreOf_of_le_normalizer le_sup_right (hKY.trans hG₁Y)
  exact commutator_sup_right_le (le_sup_left.trans hKYO) (le_sup_right.trans hKYO)
    (hVK.trans hOK) (hVY.trans hOY)

theorem fsuV_le_pCoreOf_normalizer (hF : Sp4Facts) (h1102 : Stmt11_0_2) (h1103 : Stmt11_0_3)
    (h1141 : Stmt11_4_1) (h1143 : Stmt11_4_3) (h1154 : Stmt11_5_4) (h1156 : Stmt11_5_6)
    (h : Hyp11 G T L I n) (hV₁ : IsVi T L I n 1 V₁) (hk : KindSp4 L (fsuV T I) n) :
    fsuV T I ≤ pCoreOf 2 (Subgroup.normalizer (V₁ : Set G)) := by
  have hKY : KOf L V₁ V₁ ⊔ (Subgroup.centralizer (V₁ : Set G) ⊓
      sectionCentralizer (KOf L V₁ V₁) (pCoreOf 2 (KOf L V₁ V₁))) ≤
      Subgroup.normalizer (V₁ : Set G) :=
    sup_le (kOf_le_normalizer_V₁ L V₁) (Y_le_normalizer_V₁ L V₁)
  refine le_pCoreOf_of_commutator_le hKY (fun g hg => SecD.le_normalizer_sup
      (SecD.normalizer_le_normalizer_kOf L V₁ V₁) (SecD.normalizer_le_normalizer_Y L V₁) hg)
    ((SecA.fsuV_le_T h).trans (SecA.IsVi.le_normalizer hV₁)) (SecA.isPGroup_fsuV h)
    (inf_normalizer_V₁_le_normalizer_fsuV h1103 h hV₁) inf_le_right
    (exists_decomp h1143 h hV₁) ?_
  exact commutator_fsuV_le hF h1102 h1141 h1154 h1156 h hV₁ hk

end CFSG.Quasithin.Vol2.Ch11.SecF
