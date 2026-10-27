module

public import CFSG.Foundations.Basic
import CFSG.LocalAnalysis.ComponentInitial.SelfCentralizingCoreAutomorphisms

public section

namespace CFSG.RankThree.GroupTheory.SteinbergBK

open Subgroup CFSG
open scoped commutatorElement

universe u v

theorem two_stage_automorphism_kernel {Q : Type*} [Group Q] [Finite Q] {p : ℕ} [Fact p.Prime]
    (W : Subgroup Q) [W.Normal] (hW : IsPGroup p W) (A : Subgroup (MulAut Q))
    (hAW : ∀ α ∈ A, ∀ w ∈ W, α w = w) (hAQ : ∀ α ∈ A, ∀ x : Q, x⁻¹ * α x ∈ W) :
    IsPGroup p A ∧ ∀ α ∈ A, ∀ β ∈ A, α * β = β * α := by
  classical
  have hcen : ∀ α ∈ A, ∀ x : Q, ∃ h : x⁻¹ * α x ∈ W, (⟨x⁻¹ * α x, h⟩ : W) ∈ center W := by
    intro α hα x
    have hc := CFSG.LocalAnalysis.ComponentInitial.inv_mul_apply_mem_centralizer
      (Q := W) (CFSG.LocalAnalysis.ComponentInitial.mem_pointwiseFixingAut.mpr (hAW α hα)) x
    refine ⟨hAQ α hα x, mem_center_iff.mpr fun w => Subtype.ext ?_⟩
    exact mem_centralizer_iff.mp hc w w.2
  let d : A →* (Q → center W) :=
    { toFun := fun α x => ⟨⟨x⁻¹ * (α : MulAut Q) x, (hcen α α.2 x).1⟩, (hcen α α.2 x).2⟩
      map_one' := funext fun x => Subtype.ext (Subtype.ext (by simp))
      map_mul' := fun α β => funext fun x => Subtype.ext (Subtype.ext (by
        change x⁻¹ * ((α : MulAut Q) ((β : MulAut Q) x)) =
          (x⁻¹ * (α : MulAut Q) x) * (x⁻¹ * (β : MulAut Q) x)
        have hfix : (α : MulAut Q) (x⁻¹ * (β : MulAut Q) x) = x⁻¹ * (β : MulAut Q) x :=
          hAW α α.2 _ (hAQ β β.2 x)
        rw [map_mul, map_inv] at hfix
        calc x⁻¹ * (α : MulAut Q) ((β : MulAut Q) x) =
              (x⁻¹ * (α : MulAut Q) x) *
                (((α : MulAut Q) x)⁻¹ * (α : MulAut Q) ((β : MulAut Q) x)) := by group
          _ = (x⁻¹ * (α : MulAut Q) x) * (x⁻¹ * (β : MulAut Q) x) := by rw [hfix])) }
  have hinj : Function.Injective d := by
    rw [injective_iff_map_eq_one]
    intro α hα
    refine Subtype.ext (MulEquiv.ext fun x => ?_)
    have h := congrArg (fun f => ((f x : center W) : W)) hα
    have h' := congrArg Subtype.val h
    change x⁻¹ * (α : MulAut Q) x = 1 at h'
    rw [inv_mul_eq_one] at h'
    exact h'.symm
  have hZ : IsPGroup p (center W) := hW.to_subgroup _
  have hmap : IsPGroup p (Q → center W) := by
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 hZ
    exact IsPGroup.of_card (n := n * Nat.card Q) (by rw [Nat.card_fun, hn, ← pow_mul])
  refine ⟨hmap.of_injective d hinj, fun α hα β hβ => ?_⟩
  have h := hinj (a₁ := ⟨α, hα⟩ * ⟨β, hβ⟩) (a₂ := ⟨β, hβ⟩ * ⟨α, hα⟩) (by
    rw [map_mul, map_mul]
    funext x
    change d ⟨α, hα⟩ x * d ⟨β, hβ⟩ x = d ⟨β, hβ⟩ x * d ⟨α, hα⟩ x
    exact Subtype.ext (mem_center_iff.mp (d ⟨β, hβ⟩ x).2 (d ⟨α, hα⟩ x)))
  exact congrArg Subtype.val h

theorem two_stage_kernel_le_pCore {H : Type*} [Group H] [Finite H] {p : ℕ} [Fact p.Prime]
    (hchar : IsCharacteristicP p H) (W : Subgroup H) [W.Normal] {h : H}
    (hhW : h ∈ centralizer (W : Set H)) (hhQ : ∀ x ∈ pCore p H, ⁅x, h⁆ ∈ W) :
    h ∈ pCore p H := by
  classical
  set Q := pCore p H with hQ
  have : Q.Normal := pCore_normal
  have hWn : W.Normal := inferInstance
  let C : Subgroup H :=
    { carrier := {g | g ∈ centralizer (W : Set H) ∧ ∀ x ∈ Q, ⁅x, g⁆ ∈ W}
      mul_mem' := fun {a b} ha hb => ⟨mul_mem ha.1 hb.1, fun x hx => by
        have e : ⁅x, a * b⁆ = ⁅x, a⁆ * (a * ⁅x, b⁆ * a⁻¹) := by
          simp only [commutatorElement_def]; group
        rw [e]
        exact mul_mem (ha.2 x hx) (hWn.conj_mem _ (hb.2 x hx) a)⟩
      one_mem' := ⟨one_mem _, fun x _ => by
        rw [commutatorElement_one_right]; exact one_mem W⟩
      inv_mem' := fun {a} ha => ⟨inv_mem ha.1, fun x hx => by
        have e : ⁅x, a⁻¹⁆ = a⁻¹ * ⁅x, a⁆⁻¹ * a := by
          simp only [commutatorElement_def]; group
        rw [e]
        have := hWn.conj_mem _ (inv_mem (ha.2 x hx)) a⁻¹
        rwa [inv_inv] at this⟩ }
  have hhC : h ∈ C := ⟨hhW, hhQ⟩
  have hCn : C.Normal := by
    constructor
    intro g hg k
    refine ⟨?_, fun x hx => ?_⟩
    · have : (centralizer (W : Set H)).Normal := inferInstance
      exact this.conj_mem g hg.1 k
    · have hxk : k⁻¹ * x * k ∈ Q := by
        have := (inferInstance : Q.Normal).conj_mem x hx k⁻¹
        rwa [inv_inv] at this
      have e : ⁅x, k * g * k⁻¹⁆ = k * ⁅k⁻¹ * x * k, g⁆ * k⁻¹ := by
        simp only [commutatorElement_def]; group
      rw [e]
      exact hWn.conj_mem _ (hg.2 _ hxk) k
  have hQp : IsPGroup p Q := pCore_isPGroup
  have hW'n : (W.subgroupOf Q).Normal := hWn.subgroupOf Q
  have hW'p : IsPGroup p (W.subgroupOf Q) := hQp.to_subgroup _
  let φ : C →* MulAut Q := (MulAut.conjNormal : H →* MulAut Q).comp C.subtype
  have hrange : IsPGroup p φ.range := by
    refine (two_stage_automorphism_kernel (W.subgroupOf Q) hW'p φ.range ?_ ?_).1
    · rintro _ ⟨c, rfl⟩ w hw
      apply Subtype.ext
      change (c : H) * w * (c : H)⁻¹ = w
      rw [mem_subgroupOf] at hw
      rw [← mem_centralizer_iff.mp c.2.1 w hw, mul_inv_cancel_right]
    · rintro _ ⟨c, rfl⟩ x
      rw [mem_subgroupOf]
      change (x : H)⁻¹ * ((c : H) * x * (c : H)⁻¹) ∈ W
      have := c.2.2 _ (inv_mem x.2)
      rw [commutatorElement_def, inv_inv] at this
      simpa [mul_assoc] using this
  have hker : IsPGroup p φ.ker := by
    intro k
    have hkQ : ((k : C) : H) ∈ Q := by
      apply hchar
      rw [mem_centralizer_iff]
      intro x hx
      have h1 := congrArg (fun f : MulAut Q => ((f ⟨x, hx⟩ : Q) : H)) k.2
      change ((k : C) : H) * x * ((k : C) : H)⁻¹ = x at h1
      rw [mul_inv_eq_iff_eq_mul] at h1
      exact h1.symm
    obtain ⟨n, hn⟩ := hQp ⟨_, hkQ⟩
    refine ⟨n, Subtype.ext (Subtype.ext ?_)⟩
    have := congrArg Subtype.val hn
    simpa using this
  have hCp : IsPGroup p C := by
    obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp hker
    obtain ⟨b, hb⟩ := IsPGroup.iff_card.mp hrange
    refine IsPGroup.of_card (n := a + b) ?_
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv, ha, hb, pow_add, mul_comm]
  exact (le_sSup ⟨hCn, hCp⟩ : C ≤ pCore p H) hhC

theorem two_stage_pointwise_automorphism_kernel_is_a_prime_group (p : ℕ) [Fact p.Prime] :
    (∀ (Q : Type u) [Group Q] [Finite Q] (W : Subgroup Q) [W.Normal], IsPGroup p W →
      ∀ A : Subgroup (MulAut Q), (∀ α ∈ A, ∀ w ∈ W, α w = w) →
        (∀ α ∈ A, ∀ x : Q, x⁻¹ * α x ∈ W) →
        IsPGroup p A ∧ ∀ α ∈ A, ∀ β ∈ A, α * β = β * α) ∧
    ∀ (H : Type v) [Group H] [Finite H], IsCharacteristicP p H →
      ∀ (W : Subgroup H) [W.Normal], W ≤ pCore p H → ∀ h ∈ centralizer (W : Set H),
        (∀ x ∈ pCore p H, ⁅x, h⁆ ∈ W) → h ∈ pCore p H :=
  ⟨fun _ _ _ W _ hW A hAW hAQ => two_stage_automorphism_kernel W hW A hAW hAQ,
    fun _ _ _ hchar W _ _ _ hhW hhQ => two_stage_kernel_le_pCore hchar W hhW hhQ⟩

end CFSG.RankThree.GroupTheory.SteinbergBK
