module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.L3YC.Row20Center
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.L3YC.L3YCClassIIRows
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.L3YC.L3YCLemmaUBar

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.S153D
open scoped commutatorElement

namespace Stellmacher.L3YC

section Row20

variable {G : Type} [Group G] [Finite G]

theorem row20_false
    {T Mc M V₁ V₂ Yp I L : Subgroup G} {t : G}
    (c : Ctx15316 T Mc M V₁ V₂ Yp I L t) (hq : IsLnTwoQuot L 3)
    (hSL : Sgp153 T V₁ ≤ Subgroup.normalizer (L : Set G))
    (h4 : MS93.IsC134Case4Corr (L ⊔ Sgp153 T V₁) (Sgp153 T V₁) L)
    {c₀ : G} (hc₀ : c₀ ∈ c134CQ (L ⊔ Sgp153 T V₁) L)
    {H : Subgroup G} (hH : H = Subgroup.centralizer ({c₀} : Set G))
    (hSyl : IsSylowTwoOf (Sgp153 T V₁) H) {L₁ : Subgroup G} (hLL₁ : L ≤ L₁)
    (hN : (L₁.subgroupOf H).Normal)
    (hrow : Nat.card (CFSG.pCore 2 ↥(modO2Image H L)) = 2 ^ 11 ∧
      IsSporadic .Ru ↥(modO2Image H L₁)) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hperf : ⁅L, L⁆ = L := by
    obtain ⟨h, -⟩ := c.conc
    exact perfect_of_mem_cComp h
  have hLH : L ≤ H := by
    rw [hH]
    intro l hl
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hc₀).2 l hl
  have hLG : L ≤ L ⊔ Sgp153 T V₁ := le_sup_left
  have hGL : L ⊔ Sgp153 T V₁ ≤ Subgroup.normalizer (L : Set G) :=
    sup_le Subgroup.le_normalizer hSL
  let mk : ↥H →* ↥H ⧸ CFSG.pCore 2 ↥H := QuotientGroup.mk' (CFSG.pCore 2 ↥H)
  set N : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H) := modO2Image H L₁ with hNdef
  set Lb : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H) := modO2Image H L with hLbdef
  have hNn : N.Normal := Subgroup.Normal.map hN _ (QuotientGroup.mk'_surjective _)
  have hLbN : Lb ≤ N := Subgroup.map_mono fun _ hx => hLL₁ hx
  have hN' : Nonempty (↥N ≃* CFSG.Blueprint.NativeSporadic.Carrier .Ru) := hrow.2
  have h3 : IsPSL 3 2 1 (ModO2 Lb) := CD.L3YC.isPSL_modO2_modO2Image hLH hq
  have hLbc : Nat.card Lb = 2 ^ 14 * 21 := by
    have h2 : Nat.card Lb = Nat.card (ModO2 Lb) * Nat.card (CFSG.pCore 2 ↥Lb) :=
      Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 ↥Lb)
    rw [PU.L3YC.card_L32 h3, hrow.1] at h2
    rw [h2]
    norm_num
  have hNc : Nat.card ↥N = 2 ^ 14 * 8906625 := card_of_equiv_Ru hN'
  set Sb : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H) := ((Sgp153 T V₁).subgroupOf H).map mk with hSbdef
  have hSb : IsSylowTwoOf Sb ⊤ :=
    isSylowTwoOf_top_map_of_surjective (isSylowTwoOf_top_subgroupOf hSyl) mk
      (QuotientGroup.mk'_surjective _)
  have hSbL : Sb ≤ Subgroup.normalizer (Lb : Set (↥H ⧸ CFSG.pCore 2 ↥H)) :=
    Row18.bar_le_normalizer hSL
  have hS₀ : IsSylowTwoOf (Sb ⊓ N) N :=
    B6.isSylowTwoOf_inf_normal hSb le_top (by rw [Subgroup.normalizer_eq_top (H := N)])
  have hS₀c : Nat.card ↥(Sb ⊓ N) = 2 ^ 14 :=
    Row18.card_eq_pow_of_isSylowTwoOf hS₀ hNc (by omega)
  have hS₀L : Sb ⊓ N ≤ Lb :=
    Row18.le_of_normalizes_of_card_dvd hS₀ hLbN (inf_le_left.trans hSbL)
      (by rw [hS₀c, hLbc]; exact dvd_mul_right _ _)
  obtain ⟨hKc, hKle⟩ := PU.L3YC.card_pCore_modO2Image_le (H := H) hLH hLG hGL hq hperf h4
  rw [hrow.1] at hKc
  have hQ_le : Nat.card ↥(PU.L3YC.Qbar H (L ⊔ Sgp153 T V₁) L) ≤ 2 ^ 11 := by
    refine (Subgroup.card_le_of_le hKle).trans ?_
    rw [Subgroup.card_map_of_injective (modO2Image H L).subtype_injective]
    exact hrow.1.le
  obtain ⟨hCc, -, -⟩ := PU.L3YC.lemmaU_bar_U1 (H := H) hLH hLG hGL hq h4
  have hCQ : PU.L3YC.Cbar H (L ⊔ Sgp153 T V₁) L ≤ PU.L3YC.Qbar H (L ⊔ Sgp153 T V₁) L :=
    Subgroup.map_mono fun x hx => (Subgroup.mem_inf.mp hx).1
  have hCbot : PU.L3YC.Cbar H (L ⊔ Sgp153 T V₁) L = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    have hxL : x ∈ Lb := by
      obtain ⟨w, -, rfl⟩ := hKle (hCQ hx)
      exact w.2
    exact row20_center_trivial hN' hS₀ hLbN hS₀L hLbc hxL fun b hb =>
      ((Subgroup.mem_centralizer_iff.mp (hCc hx) b hb).symm)
  have hU2 := PU.L3YC.lemmaU_bar_U2 (H := H) hLH hLG hGL hq h4
    (D' := PU.L3YC.Cbar H (L ⊔ Sgp153 T V₁) L)
    (fun b hb y hy => by
      have := Subgroup.mem_centralizer_iff.mp (hCc hy) b hb
      rw [show b * y * b⁻¹ = y by rw [this, mul_assoc, mul_inv_cancel, mul_one]]
      exact hy) le_rfl hCQ
  obtain ⟨j, hj⟩ := hU2
  rw [hCbot, Subgroup.card_bot, one_mul] at hj
  rw [hj] at hQ_le
  have hQ_ge : 2 ^ 10 ≤ 8 ^ j := by
    have : 2 ^ 11 ≤ 2 * Nat.card ↥(PU.L3YC.Qbar H (L ⊔ Sgp153 T V₁) L) := hKc
    omega
  rcases Nat.lt_or_ge j 4 with h | h
  · have : 8 ^ j ≤ 8 ^ 3 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  · have : 8 ^ 4 ≤ 8 ^ j := Nat.pow_le_pow_right (by norm_num) h
    omega

end Row20

end Stellmacher.L3YC

end CFSG.Quasithin
