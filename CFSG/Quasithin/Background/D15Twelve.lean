module

public import CFSG.Quasithin.Background.B2FactorizationBaumannAux
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Quasithin.Background.B6Basic
public import CFSG.Quasithin.Background.D1Statement
public import CFSG.Quasithin.Background.F6Basic

public section

namespace CFSG.Quasithin.D15Proof

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits B2F

variable {G : Type*} [Group G] [Finite G]

theorem card_mul_lt_of_not_isFFInt {G₁ V A : Subgroup G} (hV : IsElemAbelian 2 V)
    (hG₁V : G₁ ≤ Subgroup.normalizer (V : Set G)) (hnff : ¬ IsFFInt G₁ V hV) (hAG₁ : A ≤ G₁)
    (hA : IsElemAbelian 2 A) (hAV : ¬ A ≤ Subgroup.centralizer (V : Set G)) :
    Nat.card A * Nat.card (V ⊓ Subgroup.centralizer (A : Set G) : Subgroup G) <
      Nat.card V * Nat.card (A ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) := by
  by_contra hle
  push Not at hle
  apply hnff
  have hAn : A ≤ Subgroup.normalizer (V : Set G) := hAG₁.trans hG₁V
  refine ⟨autOn A V, autOn_le_autOn V hAG₁, autOn_ne_bot_of_not_le_centralizer hAn hAV,
    isElemAbelian2_autOn hV hA hAn, ?_⟩
  rw [card_autOn_eq_relIndex hAn, card_fixV_autOn_eq hV hAn]
  have e := Subgroup.relIndex_mul_card (A ⊓ Subgroup.centralizer (V : Set G)) A
  rw [inf_eq_left.mpr inf_le_left] at e
  have hpos : 0 < Nat.card (A ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) := Nat.card_pos
  refine Nat.le_of_mul_le_mul_right ?_ hpos
  calc Nat.card V * Nat.card (A ⊓ Subgroup.centralizer (V : Set G) : Subgroup G)
      ≤ Nat.card A * Nat.card (V ⊓ Subgroup.centralizer (A : Set G) : Subgroup G) := hle
    _ = (A ⊓ Subgroup.centralizer (V : Set G)).relIndex A *
          Nat.card (V ⊓ Subgroup.centralizer (A : Set G) : Subgroup G) *
          Nat.card (A ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) := by
      rw [← e]
      ring

variable {G₁ G₂ T V M₂ : Subgroup G}

theorem le_centralizer_cjSub (h : D11Hyp G₁ G₂ T V M₂) (hnff : ¬ IsFFInt G₁ V h.reduced.2.2.1)
    (hVR₂ : V ≤ pCoreOf 2 G₂) {g : G} (hg : g ∈ G₂) :
    V ≤ Subgroup.centralizer (cjSub g V : Set G) := by
  have hV := h.reduced.2.2.1
  have hG₁V := h.reduced.2.1
  have hR₂G₁ : pCoreOf 2 G₂ ≤ G₁ :=
    (B6.pCoreOf_two_le_of_isSylowTwoOf h.sylow₂).trans h.sylow₁.1
  have hA : ∀ k ∈ G₂, cjSub k V ≤ G₁ := fun k hk =>
    (cjSub_le (le_normalizer_pCoreOf 2 G₂ hk) hVR₂).trans hR₂G₁
  by_contra hnot
  have h1 : ¬ cjSub g V ≤ Subgroup.centralizer (V : Set G) := fun hle =>
    hnot (Subgroup.le_centralizer_iff.mp hle)
  have h2 : ¬ cjSub g⁻¹ V ≤ Subgroup.centralizer (V : Set G) := by
    intro hle
    apply h1
    have := cjSub_mono (g := g) hle
    rw [cjSub_cjSub_inv, cjSub_centralizer] at this
    exact Subgroup.le_centralizer_iff.mp this
  have i1 := card_mul_lt_of_not_isFFInt hV hG₁V hnff (hA g hg) (isElemAbelian_cjSub hV) h1
  have i2 := card_mul_lt_of_not_isFFInt hV hG₁V hnff (hA g⁻¹ (G₂.inv_mem hg))
    (isElemAbelian_cjSub hV) h2
  rw [card_cjSub] at i1 i2
  have c1 : Nat.card (V ⊓ Subgroup.centralizer (cjSub g⁻¹ V : Set G) : Subgroup G) =
      Nat.card (cjSub g V ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) := by
    rw [← card_cjSub g, cjSub_inf, cjSub_centralizer, cjSub_cjSub_inv]
  have c2 : Nat.card (cjSub g⁻¹ V ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) =
      Nat.card (V ⊓ Subgroup.centralizer (cjSub g V : Set G) : Subgroup G) := by
    rw [← card_cjSub g, cjSub_inf, cjSub_centralizer, cjSub_cjSub_inv]
  rw [c1, c2] at i2
  exact lt_asymm i1 i2

theorem isElemAbelian_conjClosure (h : D11Hyp G₁ G₂ T V M₂)
    (hnff : ¬ IsFFInt G₁ V h.reduced.2.2.1) (hVR₂ : V ≤ pCoreOf 2 G₂) :
    IsElemAbelian 2 (conjClosure V G₂) := by
  have hV := h.reduced.2.2.1
  refine B2F.isElemAbelian_closure ?_ ?_
  · rintro _ ⟨k, hk, z, hz, rfl⟩ _ ⟨k', hk', z', hz', rfl⟩
    have hm : k'⁻¹ * k ∈ G₂ := G₂.mul_mem (G₂.inv_mem hk') hk
    have hmem : (k'⁻¹ * k) * z * (k'⁻¹ * k)⁻¹ ∈ cjSub (k'⁻¹ * k) V := by
      rw [mem_cjSub]
      convert hz using 1
      group
    have hc := Subgroup.mem_centralizer_iff.mp (le_centralizer_cjSub h hnff hVR₂ hm hz') _ hmem
    calc k * z * k⁻¹ * (k' * z' * k'⁻¹)
        = k' * (((k'⁻¹ * k) * z * (k'⁻¹ * k)⁻¹) * z') * k'⁻¹ := by group
      _ = k' * (z' * ((k'⁻¹ * k) * z * (k'⁻¹ * k)⁻¹)) * k'⁻¹ := by rw [hc]
      _ = k' * z' * k'⁻¹ * (k * z * k⁻¹) := by group
  · rintro _ ⟨k, hk, z, hz, rfl⟩
    rw [conj_pow, hV.2 z hz]
    group

theorem commutator_ne_bot (h : D11Hyp G₁ G₂ T V M₂) :
    ⁅conjClosure V G₂, oTwoUpper G₂⁆ ≠ ⊥ := by
  intro hbot
  have hTP : T ⊔ oTwoUpper G₂ = G₂ := by
    rw [← F6.twoResidual_eq_oTwoUpper]
    exact sup_twoResidual_eq h.sylow₂
  have hTV : T ≤ Subgroup.normalizer (V : Set G) := h.sylow₁.1.trans h.reduced.2.1
  have hPC : oTwoUpper G₂ ≤ Subgroup.centralizer (conjClosure V G₂ : Set G) := by
    rw [Subgroup.commutator_comm, Subgroup.commutator_eq_bot_iff_le_centralizer] at hbot
    exact hbot
  have hPV : oTwoUpper G₂ ≤ Subgroup.normalizer (V : Set G) :=
    (hPC.trans (Subgroup.centralizer_le fun x hx => le_conjClosure V G₂ hx)).trans
      (Subgroup.centralizer_le_normalizer _)
  have hG₂V : G₂ ≤ Subgroup.normalizer (V : Set G) := hTP ▸ sup_le hTV hPV
  have hVR : V ≤ pCoreOf 2 G₁ :=
    le_pCoreOf_of_le_normalizer 2 h.reduced.1 h.reduced.2.1
      (B6.isPGroup_of_isElemAbelian h.reduced.2.2.1)
  exact h.nontrivial (h.no_normal V hVR
    ((Subgroup.normal_subgroupOf_iff_le_normalizer (h.reduced.1.trans le_sup_left)).mpr
      (sup_le h.reduced.2.1 hG₂V)))

end CFSG.Quasithin.D15Proof
