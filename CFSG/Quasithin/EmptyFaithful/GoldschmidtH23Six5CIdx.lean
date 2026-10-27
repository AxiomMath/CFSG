module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtH23Six5B

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace Six5Data

variable {T M V : Subgroup G} {hV : IsElemAbelian 2 V} (d : Six5Data T M V hV)
include d

theorem mem_normalizer_of_maps_into {m : G} (hm : m ∈ M) (h : ∀ v ∈ d.V₁, m * v * m⁻¹ ∈ d.V₁) :
    m ∈ Subgroup.normalizer (d.V₁ : Set G) := by
  rcases d.m_cases hm with ⟨h1, -⟩ | ⟨h1, -⟩
  · exact h1
  · exfalso
    have hb : d.V₁ = ⊥ := by
      refine (Subgroup.eq_bot_iff_forall _).2 fun v hv => ?_
      have h2 : m * v * m⁻¹ ∈ d.V₁ ⊓ d.V₂ := ⟨h v hv, h1 v hv⟩
      rw [d.V₁_inf_V₂, Subgroup.mem_bot] at h2
      calc v = m⁻¹ * (m * v * m⁻¹) * m := by group
        _ = 1 := by rw [h2]; group
    have h16 := d.card_V₁
    rw [hb, Subgroup.card_bot] at h16
    omega

theorem swap_of_not_mem_normalizer {m : G} (hm : m ∈ M)
    (h : m ∉ Subgroup.normalizer (d.V₁ : Set G)) :
    (∀ v ∈ d.V₁, m * v * m⁻¹ ∈ d.V₂) ∧ ∀ v ∈ d.V₂, m * v * m⁻¹ ∈ d.V₁ := by
  rcases d.m_cases hm with ⟨h1, -⟩ | h1
  · exact absurd h1 h
  · exact h1

theorem mem_normalizer_V₂ {m : G} (hm : m ∈ M) (h : m ∈ Subgroup.normalizer (d.V₁ : Set G)) :
    m ∈ Subgroup.normalizer (d.V₂ : Set G) := by
  rcases d.m_cases hm with ⟨-, h2⟩ | h1
  · exact h2
  · exact absurd h (d.not_mem_normalizer_of_swap h1.1)

theorem mem_normalizer_mul_swap {t b : G} (hbM : b ∈ M) (htM : t ∈ M)
    (hts : ∀ v ∈ d.V₁, t * v * t⁻¹ ∈ d.V₂)
    (hb : b ∉ Subgroup.normalizer (d.V₁ : Set G)) :
    b * t ∈ Subgroup.normalizer (d.V₁ : Set G) := by
  obtain ⟨-, hb2⟩ := d.swap_of_not_mem_normalizer hbM hb
  refine d.mem_normalizer_of_maps_into (M.mul_mem hbM htM) fun v hv => ?_
  have h1 : t * v * t⁻¹ ∈ d.V₂ := hts v hv
  have h2 := hb2 _ h1
  have : b * t * v * (b * t)⁻¹ = b * (t * v * t⁻¹) * b⁻¹ := by group
  rw [this]
  exact h2

theorem relIndex_N : (M ⊓ Subgroup.normalizer (d.V₁ : Set G)).relIndex M = 2 := by
  obtain ⟨t, htT, hts, -⟩ := d.exists_swap
  have htM : t ∈ M := d.hTM htT
  have htn : t ∉ Subgroup.normalizer (d.V₁ : Set G) := d.not_mem_normalizer_of_swap hts
  rw [Subgroup.relIndex, Subgroup.index_eq_two_iff]
  refine ⟨⟨t, htM⟩, fun b => ?_⟩
  simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.mem_inf]
  by_cases hbn : (b : G) ∈ Subgroup.normalizer (d.V₁ : Set G)
  · have hbt : (b : G) * t ∉ Subgroup.normalizer (d.V₁ : Set G) := by
      intro h
      apply htn
      have h2 : (b : G)⁻¹ * ((b : G) * t) ∈ Subgroup.normalizer (d.V₁ : Set G) :=
        Subgroup.mul_mem _ (Subgroup.inv_mem _ hbn) h
      simpa using h2
    exact Or.inr ⟨⟨b.2, hbn⟩, fun h => hbt h.2⟩
  · exact Or.inl ⟨⟨M.mul_mem b.2 htM, d.mem_normalizer_mul_swap b.2 htM hts hbn⟩,
      fun h => hbn h.2⟩

theorem relIndex_Sg : d.Sg.relIndex T = 2 := by
  obtain ⟨t, htT, hts, -⟩ := d.exists_swap
  have htM : t ∈ M := d.hTM htT
  have htn : t ∉ Subgroup.normalizer (d.V₁ : Set G) := d.not_mem_normalizer_of_swap hts
  rw [Subgroup.relIndex, Subgroup.index_eq_two_iff]
  refine ⟨⟨t, htT⟩, fun b => ?_⟩
  simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Sg, Subgroup.mem_inf]
  by_cases hbn : (b : G) ∈ Subgroup.normalizer (d.V₁ : Set G)
  · have hbt : (b : G) * t ∉ Subgroup.normalizer (d.V₁ : Set G) := by
      intro h
      apply htn
      have h2 : (b : G)⁻¹ * ((b : G) * t) ∈ Subgroup.normalizer (d.V₁ : Set G) :=
        Subgroup.mul_mem _ (Subgroup.inv_mem _ hbn) h
      simpa using h2
    exact Or.inr ⟨⟨b.2, hbn⟩, fun h => hbt h.2⟩
  · exact Or.inl ⟨⟨T.mul_mem b.2 htT, d.mem_normalizer_mul_swap (d.hTM b.2) htM hts hbn⟩,
      fun h => hbn h.2⟩

theorem relIndex_Sg_N :
    ¬ 2 ∣ d.Sg.relIndex (M ⊓ Subgroup.normalizer (d.V₁ : Set G)) := by
  have hSgT : d.Sg ≤ T := inf_le_left
  have hSgN : d.Sg ≤ M ⊓ Subgroup.normalizer (d.V₁ : Set G) :=
    le_inf (hSgT.trans d.hTM) inf_le_right
  have h1 := Subgroup.relIndex_mul_relIndex d.Sg T M hSgT d.hTM
  have h2 := Subgroup.relIndex_mul_relIndex d.Sg (M ⊓ Subgroup.normalizer (d.V₁ : Set G)) M hSgN
    inf_le_left
  rw [d.relIndex_Sg] at h1
  rw [d.relIndex_N] at h2
  have h3 : d.Sg.relIndex (M ⊓ Subgroup.normalizer (d.V₁ : Set G)) = T.relIndex M := by
    have := h1.trans h2.symm
    omega
  rw [h3]
  exact d.hsyl.2.2

end Six5Data

end CFSG.Quasithin
