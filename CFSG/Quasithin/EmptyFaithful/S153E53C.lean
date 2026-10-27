module

public import CFSG.Quasithin.EmptyFaithful.S153E53A

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.S1417 CFSG.LieType.BorelTits
open scoped commutatorElement Pointwise

namespace S153E

section Preimage

variable {G : Type} [Group G]

theorem mem_preAut153 {V A : Subgroup G} {N : Subgroup (MulAut ↥V)} {g : G} :
    g ∈ preAut153 V A N ↔
      g ∈ A ∧ ∃ hg : g ∈ Subgroup.normalizer (V : Set G), conjAct V ⟨g, hg⟩ ∈ N := by
  unfold preAut153
  rw [Subgroup.mem_inf]
  refine and_congr_right fun _ => ?_
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x.2, hx⟩
  · rintro ⟨hg, h⟩
    exact ⟨⟨g, hg⟩, h, rfl⟩

omit [Group G] in
theorem preAut153_le {G : Type} [Group G] {V A : Subgroup G} {N : Subgroup (MulAut ↥V)} :
    preAut153 V A N ≤ A := inf_le_left

omit [Group G] in
theorem autI_preAut153 {G : Type} [Group G] {V A : Subgroup G} (hV : IsElemAbelian 2 V)
    (N : Subgroup (MulAut (IntMod V hV))) :
    autI hV (preAut153 V A N) = autI hV A ⊓ N := by
  ext φ
  constructor
  · intro hφ
    obtain ⟨g, hg, rfl⟩ := (mem_autI hV).1 hφ
    obtain ⟨hgA, hgN, hN⟩ := mem_preAut153.1 hg
    exact ⟨convI_mem_autI hV hgA g.2, hN⟩
  · rintro ⟨hφA, hφN⟩
    obtain ⟨g, hgA, rfl⟩ := (mem_autI hV).1 hφA
    refine (mem_autI hV).2 ⟨g, mem_preAut153.2 ⟨hgA, g.2, hφN⟩, rfl⟩

end Preimage

section OddOmega

variable {X : Type*} [Group X]

theorem mem_of_odd_of_index_two {Ω : Subgroup X} (hidx : Ω.index = 2) {g : X}
    (hodd : Odd (orderOf g)) : g ∈ Ω := by
  have hsq : g * g ∈ Ω := Subgroup.mul_self_mem_of_index_two hidx g
  obtain ⟨m, hm⟩ := hodd
  have h1 : g ^ orderOf g = 1 := pow_orderOf_eq_one g
  have e : g = (g * g) ^ (m + 1) := by
    calc g = g ^ (orderOf g + 1) := by rw [pow_succ, h1, one_mul]
      _ = (g * g) ^ (m + 1) := by rw [hm, ← pow_two, ← pow_mul]; ring_nf
  rw [e]
  exact Subgroup.pow_mem _ hsq _

end OddOmega

section One53

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ : Subgroup G} {t : G}

theorem lemma_15_3_53_one (h113 : StageLemma14113) (cx : Ctx15350 T Mc M V₁ V₂ t)
    (h51 : Concl15351 cx) (h52 : Concl15352 cx) :
    ∃ N₁ N₂ : Subgroup (MulAut ↥(VZ T M)), Concl15353One cx N₁ N₂ := by
  have hV := cx.c.hyp.elemAbelian
  have hT := cx.c.hyp.isSylowTwoOf_autI
  obtain ⟨L₁, L₂, tb, s₁, s₂, τ, a₁, a₂, hS, hF, hV₁, -⟩ := exists_bar_model cx
  obtain ⟨-, hK4, -, -, Ω₀, hΩ₀, hsyl⟩ : IsNonabelian153 (UH153 T M V₁ Mc) ∧
      IsKleinFour153 (autOn (UH153 T M V₁ Mc) (VZ T M)) ∧
      autOn (UH153 T M V₁ Mc) (VZ T M) ≤ autOn T (VZ T M) ∧
      autOn (UH153 T M V₁ Mc) (VZ T M) ≠ autOn (Sgp153 T V₁) (VZ T M) ∧
      ∃ Ω : Subgroup (MulAut ↥(VZ T M)), IsOmega4PlusOfM153 T M cx.c.hyp.elemAbelian Ω ∧
        IsSylowTwoOf (autOn (UH153 T M V₁ Mc) (VZ T M)) Ω := by
    rcases h51.two with h | ⟨hab, -, -, -⟩
    · exact h
    · exfalso
      obtain ⟨a, ha, b, hb, hne⟩ := h52
      exact hne (B2F.isElemAbelian_comm hab ha hb)
  have hcard16 : Nat.card (IntMod (VZ T M) hV) = 16 := cx.c.hyp.card_VZ
  obtain ⟨N₁, N₂, hΩ, h36, hinf, hcomm, hiso₁, hiso₂, hc₁, hc₂⟩ :=
    exists_omegaFourPlus_split hcard16 (qW_spec cx).1 (qW_spec cx).2.1 (qW_spec cx).2.2.1
  have hOmega : IsOmega4PlusOfM153 T M hV (N₁ ⊔ N₂) := by
    intro g
    refine (hΩ g).trans ?_
    have hXg : g ∈ autOn M (VZ T M) ↔ g ∈ orthogonalGroupOf (qW cx) := by
      have : autOn M (VZ T M) = orthogonalGroupOf (qW cx) := (qW_spec cx).2.2.2
      rw [this]
      exact Iff.rfl
    exact and_congr hXg.symm Iff.rfl
  have hΩeq : Ω₀ = N₁ ⊔ N₂ := by
    ext g
    exact (hΩ₀ g).trans (hOmega g).symm
  rw [hΩeq] at hsyl
  have hYbar : autI hV (Y153 Mc M) = oTwoUpper (autI hV M) := cx.c.hyp.autOn_Y153 h113
  have hY9 : Nat.card ↥(autI hV (Y153 Mc M)) = 9 := by
    rw [hYbar]
    exact hS.card_oTwoUpper hT
  have hM72 : Nat.card ↥(autI hV M) = 72 := hS.card_X
  have hΩM : N₁ ⊔ N₂ ≤ autI hV M := by
    intro g hg
    have := ((hOmega g).1 hg).1
    exact this
  have hidx : ((N₁ ⊔ N₂).subgroupOf (autI hV M)).index = 2 := by
    have hmul := Subgroup.card_mul_index ((N₁ ⊔ N₂).subgroupOf (autI hV M))
    have hc : Nat.card ↥((N₁ ⊔ N₂).subgroupOf (autI hV M)) = 36 := by
      rw [← h36]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hΩM).toEquiv
    rw [hc, hM72] at hmul
    omega
  have hYΩ : autI hV (Y153 Mc M) ≤ N₁ ⊔ N₂ := by
    rw [hYbar, oTwoUpper]
    refine (Subgroup.closure_le _).mpr ?_
    rintro y ⟨hyX, hyodd⟩
    exact mem_of_odd_of_index_two (X := ↥(autI hV M)) hidx (g := ⟨y, hyX⟩) (by
      rw [Subgroup.orderOf_mk]
      exact hyodd) |> fun h => by simpa [Subgroup.mem_subgroupOf] using h
  have hUΩ : autI hV (UH153 T M V₁ Mc) ≤ N₁ ⊔ N₂ := hsyl.1
  have hU4 : Nat.card ↥(autI hV (UH153 T M V₁ Mc)) = 4 := hK4.1
  have hsupΩ : autI hV (UH153 T M V₁ Mc) ⊔ autI hV (Y153 Mc M) = N₁ ⊔ N₂ := by
    apply le_antisymm (sup_le hUΩ hYΩ)
    have hd1 : 4 ∣ Nat.card ↥(autI hV (UH153 T M V₁ Mc) ⊔ autI hV (Y153 Mc M)) := by
      rw [← hU4]
      exact Subgroup.card_dvd_of_le le_sup_left
    have hd2 : 9 ∣ Nat.card ↥(autI hV (UH153 T M V₁ Mc) ⊔ autI hV (Y153 Mc M)) := by
      rw [← hY9]
      exact Subgroup.card_dvd_of_le le_sup_right
    have hd3 : Nat.card ↥(autI hV (UH153 T M V₁ Mc) ⊔ autI hV (Y153 Mc M)) ≤ 36 := by
      rw [← h36]
      exact Subgroup.card_le_of_le (sup_le hUΩ hYΩ)
    have hd4 : 0 < Nat.card ↥(autI hV (UH153 T M V₁ Mc) ⊔ autI hV (Y153 Mc M)) := Nat.card_pos
    exact (Subgroup.eq_of_le_of_card_ge (sup_le hUΩ hYΩ) (by omega)).ge
  have hYUN : Y153 Mc M ⊔ UH153 T M V₁ Mc ≤ Subgroup.normalizer (VZ T M : Set G) :=
    sup_le ((Y153_le Mc M).trans cx.c.hyp.le_normalizer) (U_le_N cx)
  have hautYU : autI hV (Y153 Mc M ⊔ UH153 T M V₁ Mc) = N₁ ⊔ N₂ := by
    rw [autI_sup hV ((Y153_le Mc M).trans cx.c.hyp.le_normalizer) (U_le_N cx), sup_comm]
    exact hsupΩ
  have hcommN : ∀ N : Subgroup (MulAut (IntMod (VZ T M) hV)), N ≤ N₁ ⊔ N₂ → commV N = ⊤ →
      ⁅VZ T M, Ni153 T Mc M V₁ N⁆ = VZ T M := by
    intro N hN hcN
    have hNi : Ni153 T Mc M V₁ N ≤ Subgroup.normalizer (VZ T M : Set G) :=
      preAut153_le.trans hYUN
    rw [commutator_eq_map_commV hV hNi]
    have : autI hV (Ni153 T Mc M V₁ N) = N := by
      show autI hV (preAut153 (VZ T M) (Y153 Mc M ⊔ UH153 T M V₁ Mc) N) = N
      rw [autI_preAut153, hautYU]
      exact inf_eq_right.2 hN
    rw [this, hcN]
    exact map_inclMod_top hV
  refine ⟨N₁, N₂, ⟨⟨N₁ ⊔ N₂, hOmega, hsupΩ, rfl⟩, hinf, hcomm, hiso₁, hiso₂,
    hcommN N₁ le_sup_left hc₁, hcommN N₂ le_sup_right hc₂⟩⟩

end One53

end S153E

end CFSG.Quasithin
