module

public import CFSG.Quasithin.EmptyFaithful.S1565H
public import CFSG.Quasithin.Background.F918P5

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
open scoped Pointwise commutatorElement

section Layer

attribute [local instance] commGroupOfFact

variable {G : Type} [Group G] [Finite G] {T V L V₁ Vp H K : Subgroup G}

@[expose] def NoFixedLayer15365 (hF : HypF918 T V L V₁ Vp H K) (M I : Subgroup G) : Prop :=
  haveI := factElem hF (le_conjClosure Vp H)
  S1565.NoFixedOn (actH hF.H_le_normalizer_V₁ (le_normalizer_conjClosure Vp H))
    ((H ⊓ M).subgroupOf H)
    (subM V₁ (conjClosure Vp H) ⁅conjClosure Vp H, conjClosure K T⁆ ⊓
      S1565.fixModSub (actH hF.H_le_normalizer_V₁ (le_normalizer_conjClosure Vp H))
        ((conjClosure K T).subgroupOf H) (subM V₁ (conjClosure Vp H) (conjClosure I H)))
    (subM V₁ (conjClosure Vp H) ⁅conjClosure Vp H, conjClosure K T⁆)

theorem actH_comm_mem_commutator (hF : HypF918 T V L V₁ Vp H K) {k : G}
    (hk : k ∈ conjClosure K T) (w : ↥(tildeOf V₁ (conjClosure Vp H))) :
    haveI := factElem hF (le_conjClosure Vp H)
    actH hF.H_le_normalizer_V₁ (le_normalizer_conjClosure Vp H) ⟨k, hF.K₀_le_H hk⟩ w * w⁻¹ ∈
      subM V₁ (conjClosure Vp H) ⁅conjClosure Vp H, conjClosure K T⁆ := by
  have := factElem hF (le_conjClosure Vp H)
  set hUN := hF.conjClosure_le_normalizer_V₁ (le_conjClosure Vp H) with hUN_def
  obtain ⟨a, haU, hau⟩ := exists_mk_of_mem_tilde w
  have hw : w = modMk hUN (a : G) haU := Subtype.ext hau.symm
  have hkH : k ∈ H := hF.K₀_le_H hk
  have hkaU : k * (a : G) * k⁻¹ ∈ conjClosure Vp H :=
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_conjClosure Vp H hkH) (a : G)).mp haU
  rw [hw, actH_modMk hF.H_le_normalizer_V₁ hUN (le_normalizer_conjClosure Vp H) ⟨k, hkH⟩ haU,
    ← modMk_inv hUN haU, ← modMk_mul hUN hkaU ((conjClosure Vp H).inv_mem haU)]
  rw [mem_subM_iff]
  show secMk _ _ ⟨k * (a : G) * k⁻¹ * (a : G)⁻¹, _⟩ ∈ tildeOf V₁ ⁅conjClosure Vp H, conjClosure K T⁆
  refine secMk_mem_secImg (x := ⟨k * (a : G) * k⁻¹ * (a : G)⁻¹, _⟩) ?_
  rw [← Subgroup.commutator_comm]
  exact Subgroup.commutator_mem_commutator hk haU

theorem invSub_subM_conjClosure (hF : HypF918 T V L V₁ Vp H K) {I : Subgroup G}
    (hV₁I : V₁ ≤ I) (hIU : I ≤ conjClosure Vp H) :
    haveI := factElem hF (le_conjClosure Vp H)
    S1565.InvSub (actH hF.H_le_normalizer_V₁ (le_normalizer_conjClosure Vp H))
      (subM V₁ (conjClosure Vp H) (conjClosure I H)) := by
  have := factElem hF (le_conjClosure Vp H)
  have hIU' : conjClosure I H ≤ conjClosure Vp H := conjClosure_le_conjClosure_U hIU le_rfl
  intro x w hw
  have hst := (actH_mem_stabSub_subM_iff hF.H_le_normalizer_V₁
    (hF.conjClosure_le_normalizer_V₁ (le_conjClosure Vp H)) (le_normalizer_conjClosure Vp H)
    (hV₁I.trans (le_conjClosure I H)) hIU' x).mpr (le_normalizer_conjClosure I H x.2)
  exact (hst w).2 hw

theorem invSub_subM_commutator (hF : HypF918 T V L V₁ Vp H K) :
    haveI := factElem hF (le_conjClosure Vp H)
    S1565.InvSub (actH hF.H_le_normalizer_V₁ (le_normalizer_conjClosure Vp H))
      (subM V₁ (conjClosure Vp H) ⁅conjClosure Vp H, conjClosure K T⁆) := by
  have := factElem hF (le_conjClosure Vp H)
  have hHU := le_normalizer_conjClosure Vp H
  have hUN := hF.conjClosure_le_normalizer_V₁ (le_conjClosure Vp H)
  have hV₁U : V₁ ≤ conjClosure Vp H := hF.toHypF98.toHypF91.V₁_le_Vp.trans (le_conjClosure Vp H)
  have hCU : ⁅conjClosure Vp H, conjClosure K T⁆ ≤ conjClosure Vp H := by
    rw [Subgroup.commutator_comm]
    exact Subgroup.le_normalizer_iff_commutator_le_right.mp (hF.K₀_le_H.trans hHU)
  have hCN : ⁅conjClosure Vp H, conjClosure K T⁆ ≤ Subgroup.normalizer (V₁ : Set G) := hCU.trans hUN
  have hsup : subM V₁ (conjClosure Vp H) ⁅conjClosure Vp H, conjClosure K T⁆ =
      subM V₁ (conjClosure Vp H) (⁅conjClosure Vp H, conjClosure K T⁆ ⊔ V₁) := by
    unfold subM
    rw [tildeOf_sup_self hCN]
  rw [hsup]
  intro x w hw
  have hHC : H ≤ Subgroup.normalizer ((⁅conjClosure Vp H, conjClosure K T⁆ : Subgroup G) : Set G) :=
    F9.le_normalizer_commutator_of_le hHU hF.K₀_normal
  have hHJ : H ≤ Subgroup.normalizer
      ((⁅conjClosure Vp H, conjClosure K T⁆ ⊔ V₁ : Subgroup G) : Set G) :=
    (le_inf hHC hF.H_le_normalizer_V₁).trans (Subgroup.inf_normalizer_le_normalizer_sup _ _)
  have hst := (actH_mem_stabSub_subM_iff hF.H_le_normalizer_V₁ hUN hHU le_sup_right
    (sup_le hCU hV₁U) x).mpr (hHJ x.2)
  exact (hst w).2 hw

theorem noFixedLayer_of_eq (hF : HypF918 T V L V₁ Vp H K) (M I : Subgroup G)
    (ha : tildeOf V₁ (conjClosure I H) = tildeOf V₁ ⁅conjClosure Vp H, conjClosure K T⁆) :
    NoFixedLayer15365 hF M I := by
  have := factElem hF (le_conjClosure Vp H)
  have hJ : subM V₁ (conjClosure Vp H) (conjClosure I H) =
      subM V₁ (conjClosure Vp H) ⁅conjClosure Vp H, conjClosure K T⁆ := by
    unfold subM
    rw [ha]
  show S1565.NoFixedOn _ _ _ _
  intro u hu _
  refine ⟨hu, fun s hs => ?_⟩
  rw [hJ]
  exact actH_comm_mem_commutator hF (Subgroup.mem_subgroupOf.mp hs) u

end Layer

end CFSG.Quasithin
