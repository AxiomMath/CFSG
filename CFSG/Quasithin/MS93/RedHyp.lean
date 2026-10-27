module

public import CFSG.Quasithin.MS93.SkHyp
public import CFSG.Quasithin.MS93.ASGroup
public import CFSG.Quasithin.MS93.Sec2Gen
public import CFSG.Quasithin.Background.B5NonB
public import CFSG.Quasithin.Background.C1GNNotation

public section

namespace CFSG.Quasithin.MS93

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin

variable {G : Type} [Group G]

theorem le_normalizer_of_characteristic {T C : Subgroup G} (hCT : C ≤ T)
    (hc : (C.subgroupOf T).Characteristic) : T ≤ Subgroup.normalizer (C : Set G) := by
  have key : ∀ s ∈ T, ∀ y ∈ C, s * y * s⁻¹ ∈ C := by
    intro s hs y hy
    have h1 := Subgroup.characteristic_iff_map_le.mp hc (MulAut.conj (⟨s, hs⟩ : ↥T))
    have h2 : (MulAut.conj (⟨s, hs⟩ : ↥T)) ⟨y, hCT hy⟩ ∈ C.subgroupOf T :=
      h1 ⟨⟨y, hCT hy⟩, Subgroup.mem_subgroupOf.mpr hy, rfl⟩
    rw [Subgroup.mem_subgroupOf] at h2
    simpa using h2
  intro t ht
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨key t ht x, fun hx => ?_⟩
  have := key t⁻¹ (inv_mem ht) _ hx
  simpa [mul_assoc] using this

variable [Finite G] {M T L T₁ : Subgroup G}

theorem PUHyp.le_normalizer_reduce (h : PUHyp M T L) (hT₁ : T₁ ≤ T)
    (hc : (T₁.subgroupOf T).Characteristic) :
    M ≤ Subgroup.normalizer ((L ⊔ T₁ : Subgroup G) : Set G) := by
  rw [h.eq_sup]
  exact sup_le (le_sup_left.trans Subgroup.le_normalizer)
    (le_normalizer_sup (h.le.trans h.le_normalizer) (le_normalizer_of_characteristic hT₁ hc))

theorem PUHyp.reduce_le (h : PUHyp M T L) (hT₁ : T₁ ≤ T) : L ⊔ T₁ ≤ M :=
  sup_le h.L_le (hT₁.trans h.le)

theorem PUHyp.pCoreOf_reduce_le (h : PUHyp M T L) (hT₁ : T₁ ≤ T)
    (hc : (T₁.subgroupOf T).Characteristic) (hO : (L ⊔ T₁) ⊓ pCoreOf 2 M ≤ T₁) :
    pCoreOf 2 (L ⊔ T₁) ≤ T₁ :=
  (le_inf (pCoreOf_le' _) (pCoreOf_le_pCoreOf_of_le_normalizer (h.reduce_le hT₁)
    (h.le_normalizer_reduce hT₁ hc))).trans hO

theorem PUHyp.reduce (h : PUHyp M T L) (hT₁ : T₁ ≤ T) (hc : (T₁.subgroupOf T).Characteristic)
    (hO : (L ⊔ T₁) ⊓ pCoreOf 2 M ≤ T₁) (hne : T₁ ≠ ⊥) : PUHyp (L ⊔ T₁) T₁ L where
  le := le_sup_right
  isPGroup := h.isPGroup.to_le hT₁
  ne_bot := hne
  noChar := by
    intro C hCT₁ hCne hCc hN
    have hCc' : (C.subgroupOf T).Characteristic :=
      C1GN.characteristic_subgroupOf_trans hT₁ hCT₁ hc hCc
    apply h.noChar C (hCT₁.trans hT₁) hCne hCc'
    rw [h.eq_sup]
    exact sup_le (le_sup_left.trans hN) (le_normalizer_of_characteristic (hCT₁.trans hT₁) hCc')
  pCore_le := h.pCoreOf_reduce_le hT₁ hc hO
  charTwo := CharTwo.of_normal h.charTwo (h.reduce_le hT₁)
    ((Subgroup.normal_subgroupOf_iff_le_normalizer (h.reduce_le hT₁)).2
      (h.le_normalizer_reduce hT₁ hc))
  L_le := le_sup_left
  le_normalizer := sup_le Subgroup.le_normalizer ((hT₁.trans h.le).trans h.le_normalizer)
  eq_sup := rfl
  perfect := h.perfect
  quasisimple := h.quasisimple
  rankTwo := h.rankTwo
  sqtk := B5.sqtk_of_le h.sqtk (h.reduce_le hT₁)

theorem PUHyp.vq_eq_blockU (h : PUHyp M T L) : Vq M L = blockU L :=
  commutator_eq_blockU h.L_le h.le_normalizer h.perfect

theorem PUHyp.vq_eq_vq {M₁ : Subgroup G} (h : PUHyp M T L) (h₁ : PUHyp M₁ T₁ L) :
    Vq M₁ L = Vq M L := by
  rw [h₁.vq_eq_blockU, h.vq_eq_blockU]

theorem PUHyp.vq_reduce (h : PUHyp M T L) (hT₁ : T₁ ≤ T) (hc : (T₁.subgroupOf T).Characteristic)
    (hO : (L ⊔ T₁) ⊓ pCoreOf 2 M ≤ T₁) (hne : T₁ ≠ ⊥) : Vq (L ⊔ T₁) L = Vq M L :=
  h.vq_eq_vq (h.reduce hT₁ hc hO hne)

end CFSG.Quasithin.MS93
