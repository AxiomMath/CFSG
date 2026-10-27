module

public import CFSG.Quasithin.Vol2.Ch11SecD557T
public import CFSG.Quasithin.Vol2.Ch11SecDObl557C
public import CFSG.Quasithin.Vol2.Ch11SecD557P

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecD

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13
open CFSG.Quasithin.SL3Model
open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G} {n : ℕ}

theorem config_big (hG2 : SecA.FactG2DerivedOrder) (hNat : NatV3Fact) (h1102 : Stmt11_0_2)
    (h1110 : Stmt11_1_0) (h1141 : Stmt11_4_1) (h1154 : Stmt11_5_4) (h1155 : Stmt11_5_5)
    {V₁ : Subgroup G} {x y : G} (hconf : Config11_5_7SL3 G T L I n V₁ x y)
    (hK : KOf L V₁ V₁ = LOf L V₁) :
    conjClosure (fsuV T I) (Subgroup.normalizer (V₁ : Set G)) ≤ L ∧
      pCoreOf 2 (L ⊔ conjClosure (fsuV T I) (Subgroup.normalizer (V₁ : Set G))) = fsuV T I ∧
      Nat.card ↥(conjClosure (fsuV T I) (Subgroup.normalizer (V₁ : Set G))) = 2 ^ (5 * n) ∧
      pCoreOf 2 L = fsuV T I := by
  have hbot := inf_centralizer_eq_bot_of_kOf_eq hG2 hNat h1102 h1110 h1141 h1154 h1155 hconf hK
  obtain ⟨h, hV₁, hSL3, hU, hx, hy, hV, -, hS, hSc, -, hSV, hUL, hCS⟩ := hconf
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hyp := almostSpecialL3Hyp_of_kindSL3 hG2 hNat h1102 h1110 h1141 h hV₁ hSL3 hU
  obtain ⟨D⟩ := hyp.natural.nonempty_data
  let St : L3Setting n (fsuV T I) V₁ L T (Subgroup.normalizer (V₁ : Set G)) := ⟨hyp, D⟩
  set U := conjClosure (fsuV T I) (Subgroup.normalizer (V₁ : Set G)) with hUdef
  have hUL' : U ≤ L := by
    rw [hbot, sup_bot_eq] at hUL
    exact hUL.trans inf_le_right
  have hVS : fsuV T I ≤ pCoreOf 2 (L ⊔ U) :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((le_conjClosure _ _).trans le_sup_right) St.LU_le_normV St.isPGroup_V
  have hSeq : pCoreOf 2 (L ⊔ U) = fsuV T I := by
    refine le_antisymm (fun z hz => ?_) hVS
    have h1 : pCoreOf 2 (L ⊔ U) ⊓ Subgroup.centralizer (L : Set G) = ⊥ := by
      rw [eq_bot_iff, ← hbot]
      exact fun c hc => ⟨(hS hc.1).1.1, hc.2⟩
    have h2 := hSV hz
    rwa [h1, sup_bot_eq] at h2
  have hcard := card_U St hx hy hV hS hSc hSV hCS
  rw [hbot, Subgroup.card_bot, mul_one] at hcard
  have hLU : L ⊔ U ≤ Subgroup.normalizer (L : Set G) :=
    sup_le Subgroup.le_normalizer fun u hu => St.U_le_normL hu
  have hO2L : pCoreOf 2 L ≤ pCoreOf 2 (L ⊔ U) :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 L).trans le_sup_left)
      (fun z hz => CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L (hLU hz))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L)
  refine ⟨hUL', hSeq, hcard, le_antisymm (hO2L.trans hSeq.le) ?_⟩
  exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
    ((le_conjClosure _ _).trans hUL') St.D.hnorm St.isPGroup_V

theorem obl11_5_7SL3Big_of (hCore : Obl11_5_7SL3BigCore) (hG2 : SecA.FactG2DerivedOrder)
    (hNat : NatV3Fact) (h1102 : Stmt11_0_2) (h1110 : Stmt11_1_0) (h1141 : Stmt11_4_1)
    (h1154 : Stmt11_5_4) (h1155 : Stmt11_5_5) : Obl11_5_7SL3Big := by
  intro G _ _ T L I n V₁ x y hconf hK
  obtain ⟨h1, h2, h3, h4⟩ := config_big hG2 hNat h1102 h1110 h1141 h1154 h1155 hconf hK
  exact hCore G T L I n V₁ x y hconf hK h1 h2 h3 h4

end CFSG.Quasithin.Vol2.Ch11.SecD
