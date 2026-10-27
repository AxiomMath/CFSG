module

public import CFSG.Quasithin.EmptyFaithful.S14110AuxCommuteCrux
public import CFSG.Quasithin.EmptyFaithful.S14110AuxCommuteSub

public section

namespace CFSG.Quasithin.S14110

open Subgroup

namespace Commute

variable {G : Type*} [Group G]

theorem a4Data_subgroupOf {M X W : Subgroup G} {c : G} (hXM : X ≤ M) (h : A4Data X W c) :
    A4Data (X.subgroupOf M) (W.subgroupOf M) (⟨c, hXM h.mem_X⟩ : M) where
  le := fun x hx => (Subgroup.mem_subgroupOf).2 (h.le ((Subgroup.mem_subgroupOf).1 hx))
  card_W := (Nat.card_congr (Subgroup.subgroupOfEquivOfLe (h.le.trans hXM)).toEquiv).trans
    h.card_W
  sq_eq_one := fun w hw => Subtype.ext (by
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    exact h.sq_eq_one w ((Subgroup.mem_subgroupOf).1 hw))
  comm := fun u hu v hv => Subtype.ext
    (h.comm u ((Subgroup.mem_subgroupOf).1 hu) v ((Subgroup.mem_subgroupOf).1 hv))
  mem_X := (Subgroup.mem_subgroupOf).2 h.mem_X
  order_c := by rw [Subgroup.orderOf_mk]; exact h.order_c
  mem_normalizer := by
    rw [mem_normalizer_iff]
    intro x
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    exact mem_normalizer_iff.1 h.mem_normalizer (x : G)
  fpf := by
    intro w hw hw1 hfix
    apply h.fpf (w : G) ((Subgroup.mem_subgroupOf).1 hw) (fun h1 => hw1 (Subtype.ext h1))
    exact congrArg Subtype.val hfix
  eq_sup := by
    have hWM : W ≤ M := h.le.trans hXM
    have hcM : c ∈ M := hXM h.mem_X
    have hz : (zpowers c).subgroupOf M = zpowers (⟨c, hcM⟩ : M) := by
      ext x
      rw [Subgroup.mem_subgroupOf, mem_zpowers_iff, mem_zpowers_iff]
      constructor
      · rintro ⟨k, hk⟩
        exact ⟨k, Subtype.ext (by rw [Subgroup.coe_zpow]; exact hk)⟩
      · rintro ⟨k, hk⟩
        exact ⟨k, by rw [← hk, Subgroup.coe_zpow]⟩
    conv_lhs => rw [h.eq_sup]
    rw [Subgroup.subgroupOf_sup hWM (zpowers_le.2 hcM), hz]
  card_X := (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXM).toEquiv).trans h.card_X
  center := by
    intro g hg hcen
    apply Subtype.ext
    rw [Subgroup.coe_one]
    refine h.center g ((Subgroup.mem_subgroupOf).1 hg) (fun l hl => ?_)
    exact congrArg Subtype.val (hcen ⟨l, hXM hl⟩ ((Subgroup.mem_subgroupOf).2 hl))

theorem commute_or_eq_top {Γ : Type*} [Group Γ] [Finite Γ]
    (hΓ : ∀ g : Γ, (∀ q ∈ CFSG.Open.pCore 2 Γ, g * q = q * g) → g ∈ CFSG.Open.pCore 2 Γ)
    {X Y W W' : Subgroup Γ} {c c' : Γ} (hXs : X.IsSubnormal) (hYs : Y.IsSubnormal)
    (hX : A4Data X W c) (hY : A4Data Y W' c') :
    X = Y ∨ ∀ x ∈ X, ∀ y ∈ Y, x * y = y * x := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQn : (CFSG.Open.pCore 2 Γ).Normal := CFSG.LieType.BorelTits.pCore_normal 2
  have hQ2 : ∀ q ∈ CFSG.Open.pCore 2 Γ, ∃ m : ℕ, q ^ 2 ^ m = 1 := fun q hq => by
    obtain ⟨m, hm⟩ := CFSG.LieType.BorelTits.pCore_isPGroup 2 (G := Γ) ⟨q, hq⟩
    exact ⟨m, congrArg Subtype.val hm⟩
  have hWQ : W ≤ CFSG.Open.pCore 2 Γ :=
    le_pCore_of_isSubnormal 2 hXs hX.le
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hX.le).2 hX.le_normalizer)
      (IsPGroup.of_card (n := 2) (by rw [hX.card_W]; norm_num))
  have hW'Q : W' ≤ CFSG.Open.pCore 2 Γ :=
    le_pCore_of_isSubnormal 2 hYs hY.le
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hY.le).2 hY.le_normalizer)
      (IsPGroup.of_card (n := 2) (by rw [hY.card_W]; norm_num))
  have hbX : BlockData (CFSG.Open.pCore 2 Γ) X W c :=
    BlockData.of_comm_mem hX hWQ hQ2 (comm_mem_of_isSubnormal hQ2 hX hXs)
  have hbY : BlockData (CFSG.Open.pCore 2 Γ) Y W' c' :=
    BlockData.of_comm_mem hY hW'Q hQ2 (comm_mem_of_isSubnormal hQ2 hY hYs)
  obtain ⟨R, hcR, hc'R, hR⟩ := exists_pow_mem_of_isSubnormal hX hY hXs hYs hWQ hW'Q
  have hcc := commutator_mem hΓ hbX hbY hcR hc'R hR
  obtain ⟨w₀, hw₀, hw₀c⟩ := exists_conj_commute hQ2 hbX hbY hcc
  exact commute_or_eq_of_commute hQ2 hΓ (hbX.conj hw₀) hbY hw₀c.symm


end Commute

theorem commute_or_eq_of_isSubnormal {G : Type} [Group G] [Finite G]
    {M X Y W W' : Subgroup G} {c c' : G}
    (hM : CFSG.QuasithinUnique.CharTwo M) (hXM : X ≤ M) (hYM : Y ≤ M)
    (hXs : (X.subgroupOf M).IsSubnormal) (hYs : (Y.subgroupOf M).IsSubnormal)
    (hX : A4Data X W c) (hY : A4Data Y W' c') :
    X = Y ∨ ∀ x ∈ X, ∀ y ∈ Y, x * y = y * x := by
  have hΓ : ∀ g : M, (∀ q ∈ CFSG.Open.pCore 2 M, g * q = q * g) → g ∈ CFSG.Open.pCore 2 M := by
    intro g hg
    have hgM : (g : G) ∈ M ⊓ Subgroup.centralizer (CFSG.Open.pCoreOf 2 M : Set G) := by
      refine Subgroup.mem_inf.2 ⟨g.2, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      rintro _ ⟨q, hq, rfl⟩
      exact (congrArg Subtype.val (hg q hq)).symm
    obtain ⟨q, hq, hqg⟩ := hM hgM
    have : q = g := Subtype.ext hqg
    rw [← this]; exact hq
  rcases Commute.commute_or_eq_top hΓ hXs hYs (Commute.a4Data_subgroupOf hXM hX)
    (Commute.a4Data_subgroupOf hYM hY) with h | h
  · left
    have := Subgroup.subgroupOf_inj.1 h
    rwa [inf_of_le_left hXM, inf_of_le_left hYM] at this
  · right
    intro x hx y hy
    have := h ⟨x, hXM hx⟩ ((Subgroup.mem_subgroupOf).2 hx) ⟨y, hYM hy⟩
      ((Subgroup.mem_subgroupOf).2 hy)
    exact congrArg Subtype.val this

end CFSG.Quasithin.S14110
