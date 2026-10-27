module

public import CFSG.Quasithin.Background.HPair
public import CFSG.Quasithin.Background.HSL
public import CFSG.Quasithin.Background.InternalSecIso
public import CFSG.Quasithin.Vol2.Ch11SecA03Basic

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.H
open scoped IsMulCommutative Matrix

namespace Sec121

theorem eq_zero_or_eq_one_of_card_two {F : Type} [Field F] [Finite F] (hF : Nat.card F = 2)
    (c : F) : c = 0 ∨ c = 1 := by
  have := Fintype.ofFinite F
  have h := FiniteField.pow_card c
  rw [← Nat.card_eq_fintype_card, hF] at h
  have h2 : c * (c - 1) = 0 := by linear_combination h
  rcases mul_eq_zero.mp h2 with h3 | h3
  · exact Or.inl h3
  · exact Or.inr (sub_eq_zero.mp h3)

theorem endo_natural {X : Type*} [CommGroup X] {K : Subgroup (MulAut X)} {n : ℕ} (hn : 2 ≤ n)
    (hnat : BinaryNaturalSL K ⊤ ⊥ n 1) (f : X →* X)
    (hf : ∀ k ∈ K, ∀ x, f ((k : MulAut X) x) = (k : MulAut X) (f x)) :
    (∀ x, f x = 1) ∨ ∀ x, f x = x := by
  obtain ⟨F, _, _, hF, π, hπ⟩ := hnat
  obtain ⟨e, he⟩ := exists_mulEquiv_of_realizesVia (StatedSL n F) hπ
  let g : (Fin n → F) →+ (Fin n → F) :=
    { toFun := fun v => Multiplicative.toAdd (e (f (e.symm (Multiplicative.ofAdd v))))
      map_zero' := by
        change Multiplicative.toAdd (e (f (e.symm 1))) = 0
        rw [map_one, map_one, map_one]
        rfl
      map_add' := fun v w => by
        change Multiplicative.toAdd (e (f (e.symm (Multiplicative.ofAdd v *
          Multiplicative.ofAdd w)))) = _
        rw [map_mul, map_mul, map_mul, toAdd_mul] }
  have hg0 : ∀ x : X, g (Multiplicative.toAdd (e x)) = Multiplicative.toAdd (e (f x)) := by
    intro x
    change Multiplicative.toAdd (e (f (e.symm (Multiplicative.ofAdd
      (Multiplicative.toAdd (e x)))))) = _
    rw [ofAdd_toAdd, MulEquiv.symm_apply_apply]
  have hg : ∀ γ ∈ StatedSL n F, ∀ v, g ((γ : Matrix (Fin n) (Fin n) F) *ᵥ v) =
      (γ : Matrix (Fin n) (Fin n) F) *ᵥ g v := by
    intro γ hγ v
    let γ' : (FFModel.nat (StatedSL n F)).Gam := ⟨γ, hγ⟩
    obtain ⟨x, rfl⟩ : ∃ x : X, Multiplicative.toAdd (e x) = v :=
      ⟨e.symm (Multiplicative.ofAdd v), by rw [MulEquiv.apply_symm_apply, toAdd_ofAdd]⟩
    have h1 : ∀ y : X, Multiplicative.toAdd (e (((π γ' : ↥K) : MulAut X) y)) =
        (γ : Matrix (Fin n) (Fin n) F) *ᵥ Multiplicative.toAdd (e y) := fun y =>
      congrArg Multiplicative.toAdd (he γ' y)
    rw [← h1, hg0, hf _ (π γ').2, h1, hg0]
  obtain ⟨c, hc⟩ := hasScalarCommutant_statedSL (K := F) hn g hg
  rcases eq_zero_or_eq_one_of_card_two (by rw [hF, pow_one]) c with rfl | rfl
  · left
    intro x
    have h1 := hc (Multiplicative.toAdd (e x))
    rw [hg0, zero_smul] at h1
    have h2 : e (f x) = 1 := by
      rw [← ofAdd_toAdd (e (f x)), h1]
      rfl
    exact (map_eq_one_iff e e.injective).mp h2
  · right
    intro x
    have h1 := hc (Multiplicative.toAdd (e x))
    rw [hg0, one_smul] at h1
    exact e.injective (by rw [← ofAdd_toAdd (e (f x)), h1, ofAdd_toAdd])

variable {G : Type} [Group G]

theorem isXSectionIso₂_of_isoMod {L V V₁ V₂ : Subgroup G} [IsMulCommutative ↥V]
    (hV₁ : V₁ ≤ V) (hV₂ : V₂ ≤ V) (hLV : L ≤ Subgroup.normalizer (V : Set G))
    (h : Pair.IsoMod (autOn L V) (V₁.subgroupOf V) (V₂.subgroupOf V)) :
    IsXSectionIso₂ L V₁ ⊥ V₂ ⊥ := by
  obtain ⟨e, he⟩ := h
  let j₁ := Subgroup.subgroupOfEquivOfLe hV₁
  let j₂ := Subgroup.subgroupOfEquivOfLe hV₂
  refine CFSG.Quasithin.Vol2.Ch11.SecA.isXSectionIso₂_of_equiv ((j₁.symm.trans e).trans j₂)
    fun x hx a ha => ?_
  have hlΛ : conjAct V ⟨x, hLV hx⟩ ∈ autOn L V :=
    Setup.mem_autOn_iff.mpr ⟨⟨x, hLV hx⟩, hx, rfl⟩
  have hlw : conjAct V ⟨x, hLV hx⟩ (j₁.symm a : ↥V) ∈ V₁.subgroupOf V := by
    rw [Subgroup.mem_subgroupOf, Setup.coe_conjAct_apply]
    exact ha
  have h1 : j₁.symm ⟨x * (a : G) * x⁻¹, ha⟩ = ⟨conjAct V ⟨x, hLV hx⟩ (j₁.symm a : ↥V), hlw⟩ := by
    apply Subtype.ext
    apply Subtype.ext
    rw [Setup.coe_conjAct_apply]
    rfl
  have h2 := he _ hlΛ (j₁.symm a) hlw
  change ((e (j₁.symm ⟨x * (a : G) * x⁻¹, ha⟩) : ↥V) : G) =
    x * ((e (j₁.symm a) : ↥V) : G) * x⁻¹
  rw [h1, h2, Setup.coe_conjAct_apply]

theorem eq_self_of_map_eq {L V W : Subgroup G} [IsMulCommutative ↥V] [IsMulCommutative ↥W]
    {n : ℕ} (hn : 2 ≤ n) (hWV : W ≤ V) (hLV : L ≤ Subgroup.normalizer (V : Set G))
    (hne : W ≠ ⊥) (hnat : BinaryNaturalSL (V := ↥W) (autOn L W) ⊤ ⊥ n 1) {c : MulAut ↥V}
    (hc : ∀ y ∈ autOn L V, c * y = y * c)
    (hmap : (W.subgroupOf V).map c.toMonoidHom = W.subgroupOf V) :
    ∀ v : ↥V, (v : G) ∈ W → c v = v := by
  have hmem : ∀ w : ↥W, ((c ⟨w, hWV w.2⟩ : ↥V) : G) ∈ W := fun w => by
    have : c ⟨w, hWV w.2⟩ ∈ (W.subgroupOf V).map c.toMonoidHom :=
      ⟨⟨w, hWV w.2⟩, Subgroup.mem_subgroupOf.mpr w.2, rfl⟩
    rw [hmap] at this
    exact this
  let f : ↥W →* ↥W :=
    { toFun := fun w => ⟨(c ⟨w, hWV w.2⟩ : G), hmem w⟩
      map_one' := by
        apply Subtype.ext
        change ((c 1 : ↥V) : G) = 1
        rw [map_one]
        rfl
      map_mul' := fun a b => by
        apply Subtype.ext
        change ((c (⟨a, hWV a.2⟩ * ⟨b, hWV b.2⟩) : ↥V) : G) = _
        rw [map_mul]
        rfl }
  have hf : ∀ k ∈ autOn L W, ∀ w, f ((k : MulAut ↥W) w) = (k : MulAut ↥W) (f w) := by
    intro k hk w
    obtain ⟨g, hgL, rfl⟩ := Setup.mem_autOn_iff.mp hk
    have hgΛ : conjAct V ⟨g, hLV hgL⟩ ∈ autOn L V :=
      Setup.mem_autOn_iff.mpr ⟨⟨g, hLV hgL⟩, hgL, rfl⟩
    have h1 : (⟨((conjAct W g w : ↥W) : G), hWV (conjAct W g w).2⟩ : ↥V) =
        conjAct V ⟨g, hLV hgL⟩ ⟨w, hWV w.2⟩ := by
      apply Subtype.ext
      rw [Setup.coe_conjAct_apply, Setup.coe_conjAct_apply]
    apply Subtype.ext
    change ((c ⟨_, hWV (conjAct W g w).2⟩ : ↥V) : G) = _
    rw [h1, ← MulAut.mul_apply, hc _ hgΛ, MulAut.mul_apply, Setup.coe_conjAct_apply,
      Setup.coe_conjAct_apply]
    rfl
  rcases endo_natural hn hnat f hf with h | h
  · exfalso
    obtain ⟨⟨w, hw⟩, hw1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hne
    apply hw1
    have h2 := congrArg Subtype.val (h ⟨w, hw⟩)
    change ((c ⟨w, hWV hw⟩ : ↥V) : G) = 1 at h2
    have h3 : c ⟨w, hWV hw⟩ = 1 := Subtype.ext h2
    rw [map_eq_one_iff c c.injective] at h3
    have h4 : (w : G) = 1 := congrArg Subtype.val h3
    exact Subtype.ext h4
  · intro v hv
    have h2 := congrArg Subtype.val (h ⟨v, hv⟩)
    exact Subtype.ext h2

theorem eq_one_of_commute_autOn {L V V₁ V₂ : Subgroup G} [IsMulCommutative ↥V]
    [IsMulCommutative ↥V₁] [IsMulCommutative ↥V₂] {n : ℕ} (hn : 2 ≤ n)
    (hV₁ : V₁ ≤ V) (hV₂ : V₂ ≤ V) (hsum : V₁ ⊔ V₂ = V) (hinf : V₁ ⊓ V₂ = ⊥)
    (hLV : L ≤ Subgroup.normalizer (V : Set G)) (hL₁ : L ≤ Subgroup.normalizer (V₁ : Set G))
    (hL₂ : L ≤ Subgroup.normalizer (V₂ : Set G)) (hne₁ : V₁ ≠ ⊥) (hne₂ : V₂ ≠ ⊥)
    (hirr₁ : ∀ J : Subgroup G, J ≤ V₁ → L ≤ Subgroup.normalizer (J : Set G) → J = ⊥ ∨ J = V₁)
    (hirr₂ : ∀ J : Subgroup G, J ≤ V₂ → L ≤ Subgroup.normalizer (J : Set G) → J = ⊥ ∨ J = V₂)
    (hnat₁ : BinaryNaturalSL (V := ↥V₁) (autOn L V₁) ⊤ ⊥ n 1)
    (hnat₂ : BinaryNaturalSL (V := ↥V₂) (autOn L V₂) ⊤ ⊥ n 1)
    (hniso : ¬ IsXSectionIso₂ L V₁ ⊥ V₂ ⊥) {c : MulAut ↥V}
    (hc : ∀ y ∈ autOn L V, c * y = y * c) : c = 1 := by
  set Λ := autOn L V with hΛ
  set W₁ := V₁.subgroupOf V with hW₁
  set W₂ := V₂.subgroupOf V with hW₂
  have hinf' : W₁ ⊓ W₂ = ⊥ := InternalSec.inf_subgroupOf_eq_bot hinf
  have hsup' : W₁ ⊔ W₂ = ⊤ := InternalSec.sup_subgroupOf_eq_top hV₁ hV₂ hsum
  have hinf'' : W₂ ⊓ W₁ = ⊥ := by rw [inf_comm]; exact hinf'
  have hsup'' : W₂ ⊔ W₁ = ⊤ := by rw [sup_comm]; exact hsup'
  have hI₁ : Pair.IsInv Λ W₁ := InternalSec.autOn_inv_subgroupOf hL₁
  have hI₂ : Pair.IsInv Λ W₂ := InternalSec.autOn_inv_subgroupOf hL₂
  have hne : ∀ {X : Subgroup G}, X ≤ V → X ≠ ⊥ → X.subgroupOf V ≠ ⊥ := fun hX hX0 h =>
    hX0 (by
      have h1 := disjoint_iff.mp (Subgroup.subgroupOf_eq_bot.mp h)
      rwa [inf_eq_left.mpr hX] at h1)
  have hIrr₁ : Pair.IsIrr Λ W₁ :=
    ⟨hne hV₁ hne₁, fun U hU hUi => InternalSec.irr_subgroupOf hLV (fun J hJ hLJ => hirr₁ J hJ hLJ)
      U hU hUi⟩
  have hIrr₂ : Pair.IsIrr Λ W₂ :=
    ⟨hne hV₂ hne₂, fun U hU hUi => InternalSec.irr_subgroupOf hLV (fun J hJ hLJ => hirr₂ J hJ hLJ)
      U hU hUi⟩
  have hniso₁ : ¬ Pair.IsoMod Λ W₁ W₂ := fun h => hniso (isXSectionIso₂_of_isoMod hV₁ hV₂ hLV h)
  have hniso₂ : ¬ Pair.IsoMod Λ W₂ W₁ := fun h => hniso₁ (h.symm hI₂)
  have hcN : c ∈ Subgroup.normalizer (Λ : Set (MulAut ↥V)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      rw [hc y hy, mul_inv_cancel_right]
      exact hy
    · intro hy
      have h1 := hc _ hy
      have h2 : y = c * y * c⁻¹ :=
        calc y = c⁻¹ * ((c * y * c⁻¹) * c) := by group
          _ = c⁻¹ * (c * (c * y * c⁻¹)) := by rw [← h1]
          _ = c * y * c⁻¹ := by group
      rw [h2]
      exact hy
  have hmap : ∀ {A B : Subgroup ↥V}, A ⊓ B = ⊥ → A ⊔ B = ⊤ → Pair.IsInv Λ A → Pair.IsInv Λ B →
      Pair.IsIrr Λ A → Pair.IsIrr Λ B → ¬ Pair.IsoMod Λ A B → A.map c.toMonoidHom = A := by
    intro A B hAB hAB' hA hB hAi hBi hni
    rcases Pair.map_eq_or_map_eq hAB hAB' hA hB hAi hBi hni hcN with h | h
    · exact h
    · exfalso
      apply hni
      refine ⟨(c.subgroupMap A).trans (MulEquiv.subgroupCongr h), fun l hl w hw => ?_⟩
      change c (l w) = l (c w)
      rw [← MulAut.mul_apply, hc l hl, MulAut.mul_apply]
  have hmap₁ := hmap hinf' hsup' hI₁ hI₂ hIrr₁ hIrr₂ hniso₁
  have hmap₂ := hmap hinf'' hsup'' hI₂ hI₁ hIrr₂ hIrr₁ hniso₂
  have hfix₁ := eq_self_of_map_eq hn hV₁ hLV hne₁ hnat₁ hc hmap₁
  have hfix₂ := eq_self_of_map_eq hn hV₂ hLV hne₂ hnat₂ hc hmap₂
  apply MulEquiv.ext
  intro v
  obtain ⟨a, ha, b, hb, rfl⟩ := Pair.exists_decomp hsup' v
  rw [map_mul, hfix₁ a (Subgroup.mem_subgroupOf.mp ha), hfix₂ b (Subgroup.mem_subgroupOf.mp hb)]
  rfl

end Sec121

end CFSG.Quasithin.H13
