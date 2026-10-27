module

public import CFSG.Quasithin.MS93.S45Br
public import CFSG.Quasithin.MS93.S46LastAbs

public section

namespace CFSG.Quasithin.MS93.S45

open CFSG.Quasithin CFSG.Assembly.LowTwoRank Matrix
open scoped commutatorElement

section Pairing

variable {F : Type} [Field F] {A : Type*} [Group A]

theorem pairing_eq_one (f : (Fin 3 → F) → (Fin 3 → F) → A)
    (hadd₁ : ∀ a a' b, f (a + a') b = f a b * f a' b)
    (hadd₂ : ∀ a b b', f a (b + b') = f a b * f a b')
    (hinv : ∀ (h : SL3 F) a b, f (((h : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ a)
      (((h : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ b) = f a b) :
    ∀ a b, f a b = 1 := by
  have hzero₁ : ∀ b, f 0 b = 1 := fun b => by
    have := hadd₁ 0 0 b
    rw [add_zero] at this
    exact (mul_eq_left.mp this.symm)
  have hzero₂ : ∀ a, f a 0 = 1 := fun a => by
    have := hadd₂ a 0 0
    rw [add_zero] at this
    exact (mul_eq_left.mp this.symm)
  have h01 : f ![1, 0, 0] ![0, 1, 0] = 1 := by
    have h1 := hinv (rootElt 1 2 1) ![1, 0, 0] ![0, 0, 1]
    have e0 : ((rootElt 1 2 (1 : F) : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ ![1, 0, 0] =
        ![1, 0, 0] := by
      rw [coe_rootElt (by decide)]
      funext k
      fin_cases k <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, Matrix.single_apply,
        Matrix.one_apply]
    have e2 : ((rootElt 1 2 (1 : F) : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ ![0, 0, 1] =
        ![0, 1, 0] + ![0, 0, 1] := by
      rw [coe_rootElt (by decide)]
      funext k
      fin_cases k <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, Matrix.single_apply,
        Matrix.one_apply]
    rw [e0, e2, hadd₂] at h1
    exact mul_eq_right.mp h1
  have hind : ∀ u w : Fin 3 → F, u ≠ 0 → (∀ t : F, w ≠ t • u) → f u w = 1 := by
    intro u w hu hw
    obtain ⟨x, hx0, hx1⟩ := exists_mulVec_e0_e1 hu hw
    rw [← hx0, ← hx1, hinv x]
    exact h01
  intro a b
  by_cases ha : a = 0
  · rw [ha, hzero₁]
  by_cases hb : ∀ t : F, b ≠ t • a
  · exact hind a b ha hb
  push Not at hb
  obtain ⟨t, rfl⟩ := hb
  obtain ⟨w, hw⟩ : ∃ w : Fin 3 → F, ∀ s : F, w ≠ s • a := by
    by_contra hcon
    push Not at hcon
    have hle : (⊤ : Submodule F (Fin 3 → F)) ≤ Submodule.span F {a} := by
      intro v _
      obtain ⟨s, rfl⟩ := hcon v
      exact Submodule.smul_mem _ s (Submodule.mem_span_singleton_self a)
    have h1 := Submodule.finrank_mono hle
    rw [finrank_top, Module.finrank_fin_fun, finrank_span_singleton ha] at h1
    omega
  have hw' : ∀ s : F, t • a + w ≠ s • a := fun s heq => hw (s - t) (by
    rw [sub_smul, ← heq]; abel)
  have hneg : ∀ s : F, -w ≠ s • a := fun s heq => hw (-s) (by
    rw [neg_smul, ← heq, neg_neg])
  have e : t • a = (t • a + w) + -w := by abel
  rw [e, hadd₂, hind a _ ha hw', hind a _ ha hneg, one_mul]

end Pairing

section Sections

variable {𝔾 : Type} [Group 𝔾] {F : Type} [Field F]

theorem commutator_eq_bot_of_isSum {K V₁ Z₁ V₂ Z₂ : Subgroup 𝔾}
    {ψ : ↥K →* ↥(StatedSL 3 F)} (hψ : Function.Surjective ψ) {dual : Bool}
    (h₁ : IsSumOfNaturalModulesVia K V₁ Z₁ ψ dual 1)
    (h₂ : IsSumOfNaturalModulesVia K V₂ Z₂ ψ dual 1)
    (hc : ∀ x ∈ V₁, ∀ v ∈ V₂, ∀ g ∈ K ⊔ V₁ ⊔ V₂, g * ⁅x, v⁆ = ⁅x, v⁆ * g)
    (hZ₁ : ∀ z ∈ Z₁, ∀ v ∈ V₂, ⁅z, v⁆ = 1) (hZ₂ : ∀ x ∈ V₁, ∀ z ∈ Z₂, ⁅x, z⁆ = 1) :
    ⁅V₁, V₂⁆ = ⊥ := by
  classical
  set N₁ := NatSec.ofIsSum h₁ with hN₁
  set N₂ := NatSec.ofIsSum h₂ with hN₂
  have hK1 : K ≤ K ⊔ V₁ ⊔ V₂ := le_sup_left.trans le_sup_left
  have hV1 : V₁ ≤ K ⊔ V₁ ⊔ V₂ := le_sup_right.trans le_sup_left
  have hV2 : V₂ ≤ K ⊔ V₁ ⊔ V₂ := le_sup_right
  choose x hx hxc using fun a : Fin 3 → F => N₁.exists_coord_eq a
  choose v hv hvc using fun b : Fin 3 → F => N₂.exists_coord_eq b
  have hwd : ∀ x' ∈ V₁, ∀ v' ∈ V₂, ⁅x', v'⁆ = ⁅x (N₁.coord x'), v (N₂.coord v')⁆ := by
    intro x' hx' v' hv'
    obtain hz₁ := N₁.inv_mul_mem_of_coord_eq (hx (N₁.coord x')) hx' (hxc _)
    obtain hz₂ := N₂.inv_mul_mem_of_coord_eq (hv (N₂.coord v')) hv' (hvc _)
    set y := x (N₁.coord x')
    set w := v (N₂.coord v')
    have ex : x' = y * (y⁻¹ * x') := by group
    have ev : v' = w * (w⁻¹ * v') := by group
    have hz₁' := hZ₁ _ hz₁
    have hz₂' := hZ₂ y (hx _) _ hz₂
    have e1 : ⁅y * (y⁻¹ * x'), v'⁆ = ⁅y, v'⁆ := by
      rw [S46.commutatorElement_mul_left_conj, hz₁' v' hv', mul_one, mul_inv_cancel, one_mul]
    have e2 : ⁅y, w * (w⁻¹ * v')⁆ = ⁅y, w⁆ := by
      rw [S46.commutatorElement_mul_right_conj, hz₂', mul_one, mul_inv_cancel, mul_one]
    rw [ex, e1, ev, e2]
  set f : (Fin 3 → F) → (Fin 3 → F) → 𝔾 := fun a b => ⁅x a, v b⁆ with hf
  have hcen : ∀ a b, ∀ g ∈ K ⊔ V₁ ⊔ V₂, g * f a b = f a b * g := fun a b g hg =>
    hc _ (hx a) _ (hv b) g hg
  have hadd₁ : ∀ a a' b, f (a + a') b = f a b * f a' b := by
    intro a a' b
    have hxx : x a * x a' ∈ V₁ := V₁.mul_mem (hx a) (hx a')
    have := hwd _ hxx _ (hv b)
    rw [N₁.coord_mul (hx a) (hx a'), hxc, hxc, hvc] at this
    show ⁅x (a + a'), v b⁆ = ⁅x a, v b⁆ * ⁅x a', v b⁆
    rw [← this, S46.commutatorElement_mul_left_conj]
    have h1 : x a * ⁅x a', v b⁆ * (x a)⁻¹ = ⁅x a', v b⁆ := by
      rw [hcen a' b _ (hV1 (hx a)), mul_inv_cancel_right]
    rw [h1]
    have hm : ⁅x a', v b⁆ ∈ K ⊔ V₁ ⊔ V₂ := by
      rw [commutatorElement_def]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ (hV1 (hx a'))
        (hV2 (hv b))) (Subgroup.inv_mem _ (hV1 (hx a')))) (Subgroup.inv_mem _ (hV2 (hv b)))
    exact hcen a b _ hm
  have hadd₂ : ∀ a b b', f a (b + b') = f a b * f a b' := by
    intro a b b'
    have hvv : v b * v b' ∈ V₂ := V₂.mul_mem (hv b) (hv b')
    have := hwd _ (hx a) _ hvv
    rw [N₂.coord_mul (hv b) (hv b'), hxc, hvc, hvc] at this
    show ⁅x a, v (b + b')⁆ = ⁅x a, v b⁆ * ⁅x a, v b'⁆
    rw [← this, S46.commutatorElement_mul_right_conj]
    have h1 : v b * ⁅x a, v b'⁆ * (v b)⁻¹ = ⁅x a, v b'⁆ := by
      rw [hcen a b' _ (hV2 (hv b)), mul_inv_cancel_right]
    rw [h1]
  have hinv : ∀ (h : SL3 F) a b, f (((h : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ a)
      (((h : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ b) = f a b := by
    intro h a b
    obtain ⟨k, hk⟩ : ∃ k : ↥K, natAct dual (toSL3 ψ k) = ((h : SL3 F) : Matrix _ _ F) := by
      cases dual
      · obtain ⟨k, hk⟩ := toSL3_surjective hψ h
        exact ⟨k, by rw [natAct_false, hk]⟩
      · obtain ⟨k, hk⟩ := toSL3_surjective hψ (transposeInv h)
        refine ⟨k, ?_⟩
        rw [natAct_true, hk, ← coe_transposeInv, transposeInv_transposeInv]
    have hxk := N₁.conj_mem k (hx a)
    have hvk := N₂.conj_mem k (hv b)
    have e := hwd _ hxk _ hvk
    rw [N₁.coord_conj k (hx a), N₂.coord_conj k (hv b), hxc, hvc, hk] at e
    show ⁅x (((h : SL3 F) : Matrix _ _ F) *ᵥ a), v (((h : SL3 F) : Matrix _ _ F) *ᵥ b)⁆ =
      ⁅x a, v b⁆
    rw [← e]
    have e2 : ⁅(k : 𝔾) * x a * (k : 𝔾)⁻¹, (k : 𝔾) * v b * (k : 𝔾)⁻¹⁆ =
        (k : 𝔾) * ⁅x a, v b⁆ * (k : 𝔾)⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [e2, hcen a b _ (hK1 k.2), mul_inv_cancel_right]
  have hall := pairing_eq_one f hadd₁ hadd₂ hinv
  rw [eq_bot_iff, Subgroup.commutator_le]
  intro x' hx' v' hv'
  rw [hwd x' hx' v' hv', Subgroup.mem_bot]
  exact hall _ _

end Sections

end CFSG.Quasithin.MS93.S45
