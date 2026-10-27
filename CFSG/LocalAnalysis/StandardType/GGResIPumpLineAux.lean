module

public import CFSG.LocalAnalysis.StandardType.GGResIBasic

public section

namespace CFSG.StandardType

open CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {G : Type} [Group G] {p : ℕ} [Fact p.Prime] {Bs X : Subgroup G} {V : Type}
  [AddCommGroup V] [Module (ZMod p) V]

theorem ggCoroot_mem (hp2 : p ≠ 2) (hBsN : Bs ≤ Subgroup.normalizer (X : Set G))
    (ι : Additive ↥Bs ≃+ V) {φ : MulAut ↥Bs} {hv : V} {αv : Module.Dual (ZMod p) V}
    (hφ : ∀ w, ggLin (p := p) ι φ w = w - αv w • hv) (h2 : αv hv = 2)
    (hφX : φ ∈ ggAutomizer X Bs) : ((Additive.toMul (ι.symm hv) : ↥Bs) : G) ∈ X := by
  obtain ⟨n, hnX, hnN, hn⟩ := mem_ggAutomizer_iff.mp hφX
  set c : ↥Bs := Additive.toMul (ι.symm hv) with hc
  have hιc : ι (Additive.ofMul c) = hv := by simp [hc]
  set d : ↥Bs := φ c * c⁻¹ with hd
  have hdX : (d : G) ∈ X := by
    have hcN : (c : G) ∈ Subgroup.normalizer (X : Set G) := hBsN c.2
    have h1 : (c : G) * n⁻¹ * (c : G)⁻¹ ∈ X :=
      (Subgroup.mem_normalizer_iff.mp hcN n⁻¹).mp (X.inv_mem hnX)
    have h2' : (d : G) = n * ((c : G) * n⁻¹ * (c : G)⁻¹) := by
      rw [hd, Subgroup.coe_mul, hn c, Subgroup.coe_inv]
      group
    rw [h2']
    exact X.mul_mem hnX h1
  have hιd : ι (Additive.ofMul d) = (-2 : ZMod p) • hv := by
    rw [hd, ofMul_mul, map_add, ofMul_inv, map_neg, ← ggLin_apply_ofMul (p := p) ι φ c, hιc, hφ, h2]
    module
  have h20 : (-2 : ZMod p) ≠ 0 := by
    rw [neg_ne_zero]
    exact zmod_two_ne_zero hp2
  set k : ℕ := ((-2 : ZMod p)⁻¹).val with hk
  have hdk : d ^ k = c := by
    apply Additive.ofMul.injective
    apply ι.injective
    rw [ofMul_pow, map_nsmul, hιd, hιc, ← Nat.cast_smul_eq_nsmul (ZMod p), smul_smul, hk,
      ZMod.natCast_zmod_val, inv_mul_cancel₀ h20, one_smul]
  rw [← hdk, Subgroup.coe_pow]
  exact X.pow_mem hdX k

@[expose] def ggSpanSub (ι : Additive ↥Bs ≃+ V) (W : Submodule (ZMod p) V) : Subgroup G where
  carrier := {g | ∃ v ∈ W, ((Additive.toMul (ι.symm v) : ↥Bs) : G) = g}
  one_mem' := ⟨0, W.zero_mem, by simp⟩
  mul_mem' := by
    rintro _ _ ⟨v, hv, rfl⟩ ⟨w, hw, rfl⟩
    exact ⟨v + w, W.add_mem hv hw, by rw [map_add, toMul_add, Subgroup.coe_mul]⟩
  inv_mem' := by
    rintro _ ⟨v, hv, rfl⟩
    exact ⟨-v, W.neg_mem hv, by rw [map_neg, toMul_neg, Subgroup.coe_inv]⟩

theorem mem_ggSpanSub {ι : Additive ↥Bs ≃+ V} {W : Submodule (ZMod p) V} {g : G} :
    g ∈ ggSpanSub ι W ↔ ∃ v ∈ W, ((Additive.toMul (ι.symm v) : ↥Bs) : G) = g :=
  Iff.rfl

theorem ggSpanSub_le_bs (ι : Additive ↥Bs ≃+ V) (W : Submodule (ZMod p) V) :
    ggSpanSub ι W ≤ Bs := by
  rintro _ ⟨v, -, rfl⟩
  exact (Additive.toMul (ι.symm v)).2

theorem coe_mem_ggSpanSub_iff {ι : Additive ↥Bs ≃+ V} {W : Submodule (ZMod p) V} {c : ↥Bs} :
    (c : G) ∈ ggSpanSub ι W ↔ ι (Additive.ofMul c) ∈ W := by
  constructor
  · rintro ⟨v, hv, hvc⟩
    have h1 : Additive.toMul (ι.symm v) = c := Subtype.ext hvc
    rw [← h1, ofMul_toMul, AddEquiv.apply_symm_apply]
    exact hv
  · intro hc
    exact ⟨_, hc, by rw [AddEquiv.symm_apply_apply, toMul_ofMul]⟩

theorem card_ggSpanSub (ι : Additive ↥Bs ≃+ V) (W : Submodule (ZMod p) V) :
    Nat.card (ggSpanSub ι W) = Nat.card W := by
  symm
  refine Nat.card_congr (Equiv.ofBijective
    (fun v : W => (⟨_, v.1, v.2, rfl⟩ : ggSpanSub ι W)) ⟨fun v w hvw => ?_, ?_⟩)
  · have h0 := congrArg Subtype.val hvw
    have h1 : (Additive.toMul (ι.symm v.1) : ↥Bs) = Additive.toMul (ι.symm w.1) := Subtype.ext h0
    exact Subtype.ext (ι.symm.injective (Additive.toMul.injective h1))
  · rintro ⟨_, v, hv, rfl⟩
    exact ⟨⟨v, hv⟩, rfl⟩

theorem isElemAbelian_ggSpanSub {G : Type} [Group G] {p : ℕ} [Fact p.Prime] {Bs : Subgroup G}
    {V : Type} [AddCommGroup V] [Module (ZMod p) V] (ι : Additive ↥Bs ≃+ V)
    (W : Submodule (ZMod p) V) : IsElemAbelian p (ggSpanSub ι W) := by
  have hcommB : ∀ v w : V, (Additive.toMul (ι.symm v)) * (Additive.toMul (ι.symm w)) =
      (Additive.toMul (ι.symm w)) * (Additive.toMul (ι.symm v)) := by
    intro v w
    apply Additive.ofMul.injective
    rw [ofMul_mul, ofMul_mul, ofMul_toMul, ofMul_toMul]
    apply ι.injective
    rw [map_add, map_add, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]
    exact add_comm v w
  have hpowB : ∀ v : V, (Additive.toMul (ι.symm v)) ^ p = 1 := by
    intro v
    apply Additive.ofMul.injective
    rw [ofMul_pow, ofMul_one, ofMul_toMul]
    apply ι.injective
    rw [map_nsmul, map_zero, AddEquiv.apply_symm_apply]
    rw [← Nat.cast_smul_eq_nsmul (ZMod p) p v, ZMod.natCast_self p, zero_smul]
  refine ⟨IsMulCommutative.of_comm ?_, ?_⟩
  · intro a b
    apply Subtype.ext
    obtain ⟨v, -, hv⟩ := mem_ggSpanSub.mp a.2
    obtain ⟨w, -, hw⟩ := mem_ggSpanSub.mp b.2
    rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hv, ← hw]
    have h := congrArg (fun t : ↥Bs => (t : G)) (hcommB v w)
    simpa only [Subgroup.coe_mul] using h
  · intro e he
    obtain ⟨v, -, rfl⟩ := mem_ggSpanSub.mp he
    have h := congrArg (fun t : ↥Bs => (t : G)) (hpowB v)
    simpa only [Subgroup.coe_pow, Subgroup.coe_one] using h

theorem ggSpanSub_le {r : ℕ} (ι : Additive ↥Bs ≃+ V) {hv : Fin r → V}
    (hmem : ∀ j, ((Additive.toMul (ι.symm (hv j)) : ↥Bs) : G) ∈ X) :
    ggSpanSub ι (Submodule.span (ZMod p) (Set.range hv)) ≤ X := by
  rintro _ ⟨v, hv', rfl⟩
  induction hv' using Submodule.span_induction with
  | mem v hv0 =>
    obtain ⟨j, rfl⟩ := hv0
    exact hmem j
  | zero => simp
  | add v w _ _ hv1 hw1 =>
    rw [map_add, toMul_add, Subgroup.coe_mul]
    exact X.mul_mem hv1 hw1
  | smul c v _ hv1 =>
    have hcv : c • v = c.val • v := by
      rw [← Nat.cast_smul_eq_nsmul (ZMod p), ZMod.natCast_zmod_val]
    rw [hcv, map_nsmul, toMul_nsmul, Subgroup.coe_pow]
    exact X.pow_mem hv1 _

theorem ggCoroots_card_le [Finite G] {r : ℕ} (ι : Additive ↥Bs ≃+ V) {hv : Fin r → V}
    (hind : LinearIndependent (ZMod p) hv)
    (hmem : ∀ j, ((Additive.toMul (ι.symm (hv j)) : ↥Bs) : G) ∈ X) :
    p ^ r ≤ Nat.card (Bs ⊓ X : Subgroup G) := by
  have : Finite V := Finite.of_equiv _ ι.toEquiv
  set W := Submodule.span (ZMod p) (Set.range hv) with hWdef
  have hW : ∀ v ∈ W, ((Additive.toMul (ι.symm v) : ↥Bs) : G) ∈ X := by
    intro v hv'
    induction hv' using Submodule.span_induction with
    | mem v hv0 =>
      obtain ⟨j, rfl⟩ := hv0
      exact hmem j
    | zero => simp
    | add v w _ _ hv1 hw1 =>
      rw [map_add, toMul_add, Subgroup.coe_mul]
      exact X.mul_mem hv1 hw1
    | smul c v _ hv1 =>
      have hcv : c • v = c.val • v := by
        rw [← Nat.cast_smul_eq_nsmul (ZMod p), ZMod.natCast_zmod_val]
      rw [hcv, map_nsmul, toMul_nsmul, Subgroup.coe_pow]
      exact X.pow_mem hv1 _
  have hcardW : Nat.card W = p ^ r := by
    rw [← FiniteField.pow_finrank_eq_natCard p W, finrank_span_eq_card hind, Fintype.card_fin]
  let f : W → (Bs ⊓ X : Subgroup G) := fun v =>
    ⟨((Additive.toMul (ι.symm v.1) : ↥Bs) : G), (Additive.toMul (ι.symm v.1)).2, hW v.1 v.2⟩
  have hf : Function.Injective f := by
    intro v w hvw
    have h0 : ((f v : (Bs ⊓ X : Subgroup G)) : G) = ((f w : (Bs ⊓ X : Subgroup G)) : G) :=
      congrArg Subtype.val hvw
    have h1 : (Additive.toMul (ι.symm v.1) : ↥Bs) = Additive.toMul (ι.symm w.1) := Subtype.ext h0
    exact Subtype.ext (ι.symm.injective (Additive.toMul.injective h1))
  rw [← hcardW]
  exact Nat.card_le_card_of_injective f hf

end CFSG.StandardType
