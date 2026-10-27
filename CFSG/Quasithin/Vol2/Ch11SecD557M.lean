module

public import CFSG.Quasithin.Vol2.Ch11SecD557L
public import CFSG.Quasithin.Vol2.Ch11SecDObl557B
public import CFSG.Quasithin.Vol2.Ch11SecD557H
public import CFSG.Quasithin.Vol2.Ch11SecDObl557

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecD

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13
open CFSG.Quasithin.SL3Model
open scoped MatrixGroups commutatorElement

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G} {n : ℕ}

theorem stmt11_5_5_normalizer (h1110 : Stmt11_1_0) (h1154 : Stmt11_5_4) (h1155 : Stmt11_5_5)
    (h : Hyp11 G T L I n) {V₁ : Subgroup G} (hV₁ : IsVi T L I n 1 V₁)
    (hSL3 : KindSL3 L (fsuV T I) n) :
    conjClosure (fsuV T I) (Subgroup.normalizer (V₁ : Set G)) ≤
        pCoreOf 2 (Subgroup.normalizer (V₁ : Set G)) ∧
      ⁅conjClosure (fsuV T I) (Subgroup.normalizer (V₁ : Set G)),
        pCoreOf 2 (Subgroup.normalizer (V₁ : Set G))⁆ ≤ V₁ ∧
      (frattini ↥(conjClosure (fsuV T I) (Subgroup.normalizer (V₁ : Set G)))).map
        (conjClosure (fsuV T I) (Subgroup.normalizer (V₁ : Set G))).subtype ≤ V₁ := by
  have hTG₁ : T ≤ Subgroup.normalizer (V₁ : Set G) := SecA.IsVi.le_normalizer hV₁
  have hV₁O : V₁ ≤ pCoreOf 2 (Subgroup.normalizer (V₁ : Set G)) :=
    CFSG.LieType.BorelTits.le_pCoreOf 2 (Subgroup.le_normalizer)
      ((Subgroup.normal_subgroupOf_iff_le_normalizer Subgroup.le_normalizer).mpr le_rfl)
      (h.fsu.sylow.1.to_le ((SecA.IsVi.le_fsuV hV₁).trans (SecA.fsuV_le_T h)))
  have hO2ne : pCoreOf 2 (Subgroup.normalizer (V₁ : Set G)) ≠ ⊥ := fun hb =>
    SecA.IsVi.ne_bot h hV₁ le_rfl (le_bot_iff.mp (hb ▸ hV₁O))
  have hH₁ : InH (LOf L V₁ ⊔ T) (Subgroup.normalizer (V₁ : Set G)) :=
    ⟨sup_le (lOf_le_normalizer L V₁) hTG₁, hO2ne⟩
  have hH₁M : ¬ Subgroup.normalizer (V₁ : Set G) ≤ Subgroup.normalizer (L : Set G) := fun hle =>
    (h1154 G T L I n V₁ h hV₁).1 ((Subgroup.centralizer_le_normalizer _).trans hle)
  obtain ⟨V₃, hV₃, -⟩ := (h1110 G T L I n h).1 3 (by norm_num) le_rfl
  have hV₃eq : V₃ = fsuV T I := ((h1110 G T L I n h).2.2 V₁ V₃ hV₁ hV₃).1 hSL3
  obtain ⟨h5one, h5two, h5three, -⟩ := h1155 G T L I n V₁ V₃ _ h hV₁ hV₃ hH₁ hH₁M le_rfl
  subst hV₃eq
  exact ⟨h5one, h5two, h5three⟩

theorem obl11_5_7SL3End_of (hSmall : Obl11_5_7SL3Small) (hBig : Obl11_5_7SL3Big)
    (hI16 : ASInputs.AS_I_1_6) (hG2 : SecA.FactG2DerivedOrder) (hComm : CommLOneSL3Fact)
    (hNat : NatV3Fact) (h1102 : Stmt11_0_2) (h1110 : Stmt11_1_0) (h1141 : Stmt11_4_1)
    (h1154 : Stmt11_5_4) (h1155 : Stmt11_5_5) : Obl11_5_7SL3End := by
  intro G _ _ T L I n V₁ x y h hV₁ hSL3 hU hx hy hV hxy hS
  have hyp := almostSpecialL3Hyp_of_kindSL3 hG2 hNat h1102 h1110 h1141 h hV₁ hSL3 hU
  obtain ⟨D⟩ := hyp.natural.nonempty_data
  let St : L3Setting n (fsuV T I) V₁ L T (Subgroup.normalizer (V₁ : Set G)) := ⟨hyp, D⟩
  obtain ⟨h5one, h5two, h5three⟩ := stmt11_5_5_normalizer h1110 h1154 h1155 h hV₁ hSL3
  have hUcomm : ∀ a ∈ conjClosure (fsuV T I) (Subgroup.normalizer (V₁ : Set G)),
      ∀ b ∈ conjClosure (fsuV T I) (Subgroup.normalizer (V₁ : Set G)),
        a * b * a⁻¹ * b⁻¹ ∈ V₁ := fun a ha b hb =>
    h5two (Subgroup.commutator_mem_commutator ha (h5one hb))
  have hUsq : ∀ a ∈ conjClosure (fsuV T I) (Subgroup.normalizer (V₁ : Set G)), a ^ 2 ∈ V₁ :=
    fun a ha => h5three (sq_mem_frattini St.isPGroup_U ha)
  obtain ⟨h1, h2, h3, h4, h5⟩ :=
    config_structure hI16 hComm h1102 h1141 h hV₁ hSL3 St hx hy hV hxy hS hUcomm hUsq
  have hconf : Config11_5_7SL3 G T L I n V₁ x y :=
    ⟨h, hV₁, hSL3, hU, hx, hy, hV, hxy, hS, h1, h2, h3, h4, h5⟩
  by_cases hK : KOf L V₁ V₁ = LOf L V₁
  · exact hBig G T L I n V₁ x y hconf hK
  · exact hSmall G T L I n V₁ x y hconf hK

end CFSG.Quasithin.Vol2.Ch11.SecD
