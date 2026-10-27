module

public import CFSG.Quasithin.Background.P3Sp44K
public import CFSG.Quasithin.Background.P3Sp44Comm
public import CFSG.LocalAnalysis.ComponentClassification.PresentationLocalSymplecticSix
public import TauCeti.LinearAlgebra.BilinearForm.SymplecticBasis

public section

namespace CFSG.Quasithin

namespace G11

namespace G118

open Matrix CFSG.Assembly.LowTwoRank CFSG.ClassicalGroups.Symplectic
open CFSG.ComponentClassification.PresentationLocal

variable {K : Type} [Field K]

@[expose, reducible] def sp44Fix (a' : (Fin 2 ⊕ Fin 2 → K) →+ (Fin 2 ⊕ Fin 2 → K)) :
    AddSubgroup (Fin 2 ⊕ Fin 2 → K) :=
  AddMonoidHom.eqLocus a' (AddMonoidHom.id _)

theorem sp44_descent_surj [Finite K] (hK : Nat.card K = 4)
    (a' : (Fin 2 ⊕ Fin 2 → K) →+ (Fin 2 ⊕ Fin 2 → K))
    (hinv : ∀ v, a' (a' v) = v) (hsq : ∀ (t : K) (w : Fin 2 ⊕ Fin 2 → K), a' (t • w) = t ^ 2 • a' w)
    {ω : K} (hω : ω ^ 2 + ω + 1 = 0) (v : Fin 2 ⊕ Fin 2 → K) :
    ∃ x y, x ∈ sp44Fix a' ∧ y ∈ sp44Fix a' ∧ v = x + ω • y := by
  have hc : CharP K 2 := sp44_charTwo hK
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hω4 : (ω ^ 2) ^ 2 = ω := by rw [← pow_mul]; exact sp44_pow_four hK ω
  set t : Fin 2 ⊕ Fin 2 → K := v + a' v with ht
  set s : Fin 2 ⊕ Fin 2 → K := ω • v + ω ^ 2 • a' v with hs
  have hta : a' t = t := by
    rw [ht, map_add, hinv, add_comm]
  have hsa : a' s = s := by
    rw [hs, map_add, hsq, hsq, hinv, hω4]
    rw [add_comm]
  refine ⟨s + t, t, ?_, hta, ?_⟩
  · show a' (s + t) = s + t
    rw [map_add, hsa, hta]
  · have e : s + t + ω • t = (ω + 1 + ω) • v + (ω ^ 2 + 1 + ω) • a' v := by
      rw [hs, ht]
      module
    have e1 : ω + 1 + ω = 1 := by linear_combination ω * h2
    have e2 : ω ^ 2 + 1 + ω = 0 := by linear_combination hω
    rw [e1, e2, zero_smul, add_zero, one_smul] at e
    exact e.symm

theorem sp44_descent_inj [Finite K] (hK : Nat.card K = 4)
    (a' : (Fin 2 ⊕ Fin 2 → K) →+ (Fin 2 ⊕ Fin 2 → K))
    (hsq : ∀ (t : K) (w : Fin 2 ⊕ Fin 2 → K), a' (t • w) = t ^ 2 • a' w)
    {ω : K} (hω : ω ^ 2 + ω + 1 = 0) (x y : Fin 2 ⊕ Fin 2 → K) (hx : x ∈ sp44Fix a')
    (hy : y ∈ sp44Fix a') (h : x + ω • y = 0) : x = 0 ∧ y = 0 := by
  have hc : CharP K 2 := sp44_charTwo hK
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hx' : a' x = x := hx
  have hy' : a' y = y := hy
  have h' : x + ω ^ 2 • y = 0 := by
    have := congrArg a' h
    rw [map_add, hsq, hx', hy', map_zero] at this
    exact this
  have hy0 : y = 0 := by
    have : (ω - ω ^ 2) • y = 0 := by
      rw [sub_smul]
      have := sub_eq_zero.2 (h.trans h'.symm)
      simpa [add_sub_add_left_eq_sub] using this
    have e : ω - ω ^ 2 = 1 := by linear_combination (-1 : K) * hω + ω * h2
    rw [e, one_smul] at this
    exact this
  refine ⟨?_, hy0⟩
  rw [hy0, smul_zero, add_zero] at h
  exact h

theorem sp44_card_fix [Finite K] (hK : Nat.card K = 4)
    (a' : (Fin 2 ⊕ Fin 2 → K) →+ (Fin 2 ⊕ Fin 2 → K))
    (hinv : ∀ v, a' (a' v) = v)
    (hsq : ∀ (t : K) (w : Fin 2 ⊕ Fin 2 → K), a' (t • w) = t ^ 2 • a' w)
    {ω : K} (hω : ω ^ 2 + ω + 1 = 0) : Nat.card (sp44Fix a') = 16 := by
  let Φ : (sp44Fix a') × (sp44Fix a') → (Fin 2 ⊕ Fin 2 → K) := fun p => p.1 + ω • p.2
  have hbij : Function.Bijective Φ := by
    constructor
    · intro p q h
      have h' : (p.1 - q.1 : Fin 2 ⊕ Fin 2 → K) + ω • (p.2 - q.2 : Fin 2 ⊕ Fin 2 → K) = 0 := by
        have : (p.1 : Fin 2 ⊕ Fin 2 → K) + ω • p.2 = q.1 + ω • q.2 := h
        rw [smul_sub]
        calc (p.1 - q.1 : Fin 2 ⊕ Fin 2 → K) + (ω • p.2 - ω • q.2)
            = (p.1 + ω • p.2) - (q.1 + ω • q.2) := by abel
          _ = 0 := by rw [this, sub_self]
      have := sp44_descent_inj hK a' hsq hω _ _ (sub_mem p.1.2 q.1.2) (sub_mem p.2.2 q.2.2) h'
      exact Prod.ext (Subtype.ext (sub_eq_zero.1 this.1)) (Subtype.ext (sub_eq_zero.1 this.2))
    · intro v
      obtain ⟨x, y, hx, hy, rfl⟩ := sp44_descent_surj hK a' hinv hsq hω v
      exact ⟨(⟨x, hx⟩, ⟨y, hy⟩), rfl⟩
  have hcard : Nat.card (Fin 2 ⊕ Fin 2 → K) = Nat.card (sp44Fix a') * Nat.card (sp44Fix a') := by
    rw [← Nat.card_prod]
    exact (Nat.card_eq_of_bijective Φ hbij).symm
  have h256 : Nat.card (Fin 2 ⊕ Fin 2 → K) = 256 := by
    rw [Nat.card_fun, hK]
    simp
  rw [h256] at hcard
  have : Nat.card (sp44Fix a') * Nat.card (sp44Fix a') = 16 * 16 := by omega
  exact Nat.mul_self_inj.1 this

theorem sp44ω_self (v : Fin 2 ⊕ Fin 2 → K) : sp44ω v v = 0 := by
  simp only [sp44ω, Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Fin.sum_univ_two]
  simp
  ring

theorem sp44ω_eq_zero_left (v : Fin 2 ⊕ Fin 2 → K) (h : ∀ w, sp44ω v w = 0) : v = 0 := by
  ext a
  rcases a with i | i
  · have := h (Pi.single (Sum.inr i) 1)
    simpa [sp44ω, Matrix.mulVec, dotProduct, Fintype.sum_sum_type, fromBlocks, Pi.single_apply,
      Matrix.one_apply] using this
  · have := h (Pi.single (Sum.inl i) 1)
    simpa [sp44ω, Matrix.mulVec, dotProduct, Fintype.sum_sum_type, fromBlocks, Pi.single_apply,
      Matrix.one_apply] using this

theorem sp44ω_eq_zero_right (w : Fin 2 ⊕ Fin 2 → K) (h : ∀ v, sp44ω v w = 0) : w = 0 := by
  ext a
  rcases a with i | i
  · have := h (Pi.single (Sum.inr i) 1)
    fin_cases i <;> simpa [sp44ω, Matrix.mulVec, dotProduct, Fintype.sum_sum_type, fromBlocks,
      Pi.single_apply, Matrix.one_apply] using this
  · have := h (Pi.single (Sum.inl i) 1)
    fin_cases i <;> simpa [sp44ω, Matrix.mulVec, dotProduct, Fintype.sum_sum_type, fromBlocks,
      Pi.single_apply, Matrix.one_apply] using this

section Embed

variable [Finite K]

theorem sp44_embed (hK : Nat.card K = 4)
    (a' : (Fin 2 ⊕ Fin 2 → K) →+ (Fin 2 ⊕ Fin 2 → K))
    (hinv : ∀ v, a' (a' v) = v)
    (hsq : ∀ (t : K) (w : Fin 2 ⊕ Fin 2 → K), a' (t • w) = t ^ 2 • a' w)
    (hform : ∀ v w, sp44ω (a' v) (a' w) = sp44ω v w ^ 2)
    (C : Subgroup (Equiv.Perm (Fin 2 ⊕ Fin 2 → K)))
    (hC : ∀ c : Equiv.Perm (Fin 2 ⊕ Fin 2 → K), c ∈ C → (∀ v w, c (v + w) = c v + c w) ∧
      (∀ (t : K) v, c (t • v) = t • c v) ∧
      c * c = 1 ∧ (∀ v, c (a' v) = a' (c v)) ∧ (∀ v w, sp44ω (c v) (c w) = sp44ω v w)) :
    ∃ φ : C →* sympFour, Function.Injective φ := by
  have hchar : CharP K 2 := sp44_charTwo hK
  obtain ⟨w₀, -, -, hw₀⟩ := sp44_exists_omega hK
  have h2V : ∀ x : Fin 2 ⊕ Fin 2 → K, (2 : ℕ) • x = 0 := by
    intro x
    ext i
    simp only [Pi.smul_apply, Pi.zero_apply, nsmul_eq_mul, Nat.cast_ofNat]
    rw [CharTwo.two_eq_zero, zero_mul]
  let _ : Module (ZMod 2) (Fin 2 ⊕ Fin 2 → K) := AddCommGroup.zmodModule h2V
  let V₀ : Submodule (ZMod 2) (Fin 2 ⊕ Fin 2 → K) := AddSubgroup.toZModSubmodule 2 (sp44Fix a')
  have hV₀ : ∀ x : Fin 2 ⊕ Fin 2 → K, x ∈ V₀ ↔ a' x = x := fun x => Iff.rfl
  have hval : ∀ x y : V₀, ∃ z : ZMod 2, ZMod.castHom (dvd_refl 2) K z =
      sp44ω (x : Fin 2 ⊕ Fin 2 → K) (y : Fin 2 ⊕ Fin 2 → K) := by
    intro x y
    have h1 : a' (x : Fin 2 ⊕ Fin 2 → K) = x := (hV₀ _).1 x.2
    have h2 : a' (y : Fin 2 ⊕ Fin 2 → K) = y := (hV₀ _).1 y.2
    have h := hform (x : Fin 2 ⊕ Fin 2 → K) y
    rw [h1, h2] at h
    have h3 : sp44ω (x : Fin 2 ⊕ Fin 2 → K) y * (sp44ω (x : Fin 2 ⊕ Fin 2 → K) y - 1) = 0 := by
      linear_combination -h
    rcases mul_eq_zero.1 h3 with h0 | h0
    · exact ⟨0, by rw [h0]; simp⟩
    · exact ⟨1, by rw [sub_eq_zero.1 h0]; simp⟩
  choose f hf using hval
  have hcinj : Function.Injective (ZMod.castHom (dvd_refl 2) K) :=
    (ZMod.castHom (dvd_refl 2) K).injective
  have hf_al : ∀ x x' y : V₀, f (x + x') y = f x y + f x' y := by
    intro x x' y
    apply hcinj
    rw [hf, map_add, hf, hf]
    exact sp44ω_add_left _ _ _
  have hf_ar : ∀ x y y' : V₀, f x (y + y') = f x y + f x y' := by
    intro x y y'
    apply hcinj
    rw [hf, map_add, hf, hf]
    exact sp44ω_add_right _ _ _
  have hc01 : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
  have hf0l : ∀ y : V₀, f 0 y = 0 := by
    intro y
    apply hcinj
    rw [hf, map_zero]
    simp [sp44ω, Matrix.mulVec, dotProduct]
  have hf0r : ∀ x : V₀, f x 0 = 0 := by
    intro x
    apply hcinj
    rw [hf, map_zero]
    simp [sp44ω, Matrix.mulVec, dotProduct]
  have hsl : ∀ (c : ZMod 2) (x y : V₀), f (c • x) y = c * f x y := by
    intro c x y
    rcases hc01 c with rfl | rfl
    · rw [zero_smul, hf0l, zero_mul]
    · rw [one_smul, one_mul]
  have hsr : ∀ (c : ZMod 2) (x y : V₀), f x (c • y) = c * f x y := by
    intro c x y
    rcases hc01 c with rfl | rfl
    · rw [zero_smul, hf0r, zero_mul]
    · rw [one_smul, one_mul]
  let B : LinearMap.BilinForm (ZMod 2) V₀ := LinearMap.mk₂ (ZMod 2) f hf_al hsl hf_ar hsr
  have hB : ∀ x y, B x y = f x y := fun x y => rfl
  have hBcast : ∀ x y, ZMod.castHom (dvd_refl 2) K (B x y) =
      sp44ω (x : Fin 2 ⊕ Fin 2 → K) (y : Fin 2 ⊕ Fin 2 → K) := fun x y => by rw [hB, hf]
  have hBalt : B.IsAlt := by
    intro x
    apply hcinj
    rw [hBcast, sp44ω_self, map_zero]
  have hωzero : ∀ (x : V₀), (∀ y : V₀, sp44ω (x : Fin 2 ⊕ Fin 2 → K) (y : Fin 2 ⊕ Fin 2 → K) = 0) →
      (∀ w : Fin 2 ⊕ Fin 2 → K, sp44ω (x : Fin 2 ⊕ Fin 2 → K) w = 0) := by
    intro x hx w
    obtain ⟨u, z, hu, hz, rfl⟩ := sp44_descent_surj hK a' hinv hsq hw₀ w
    rw [sp44ω_add_right, sp44ω_smul_right, hx ⟨u, hu⟩, hx ⟨z, hz⟩]
    simp
  have hωzero' : ∀ (y : V₀), (∀ x : V₀, sp44ω (x : Fin 2 ⊕ Fin 2 → K) (y : Fin 2 ⊕ Fin 2 → K) = 0) →
      (∀ v : Fin 2 ⊕ Fin 2 → K, sp44ω v (y : Fin 2 ⊕ Fin 2 → K) = 0) := by
    intro y hy v
    obtain ⟨u, z, hu, hz, rfl⟩ := sp44_descent_surj hK a' hinv hsq hw₀ v
    rw [sp44ω_add_left, sp44ω_smul_left, hy ⟨u, hu⟩, hy ⟨z, hz⟩]
    simp
  have hBnd : B.Nondegenerate := by
    constructor
    · intro x hx
      apply Subtype.ext
      apply sp44ω_eq_zero_left
      apply hωzero
      intro y
      rw [← hBcast, hx y, map_zero]
    · intro y hy
      apply Subtype.ext
      apply sp44ω_eq_zero_right
      apply hωzero'
      intro x
      rw [← hBcast, hy x, map_zero]
  have hcardV₀ : Nat.card V₀ = 16 := by
    rw [← sp44_card_fix hK a' hinv hsq hw₀]
    exact Nat.card_congr (Equiv.refl _)
  have hfin : Module.finrank (ZMod 2) V₀ = 4 := by
    have h := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := V₀)
    rw [hcardV₀, Nat.card_zmod] at h
    have h4 : (16 : ℕ) = 2 ^ 4 := by norm_num
    rw [h4] at h
    exact (Nat.pow_right_injective (le_refl 2) h).symm
  obtain ⟨m, b, hb⟩ := hBalt.exists_basis_toMatrix_eq_J hBnd
  have hm : m = 2 := by
    have := Module.finrank_eq_card_basis b
    rw [hfin, Fintype.card_sum, Fintype.card_fin] at this
    omega
  subst hm
  let e4 : Fin 2 ⊕ Fin 2 ≃ Fin 4 :=
    { toFun := fun x =>
        if x = Sum.inl 0 then 0 else if x = Sum.inl 1 then 1 else if x = Sum.inr 1 then 2 else 3
      invFun := fun i =>
        if i = 0 then Sum.inl 0 else if i = 1 then Sum.inl 1 else if i = 2 then Sum.inr 1
          else Sum.inr 0
      left_inv := by decide
      right_inv := by decide }
  let b4 : Module.Basis (Fin 4) (ZMod 2) V₀ := b.reindex e4
  have hJ : ∀ i j : Fin 4, Matrix.J (Fin 2) (ZMod 2) (e4.symm i) (e4.symm j) =
      antidiagGram i j := by
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.J, antidiagGram, e4, Matrix.fromBlocks]
  have hG : ∀ i j, B (b4 i) (b4 j) = antidiagGram i j := by
    intro i j
    have h := congrFun (congrFun hb (e4.symm i)) (e4.symm j)
    rw [LinearMap.BilinForm.toMatrix_apply] at h
    have h' : B (b4 i) (b4 j) = B (b (e4.symm i)) (b (e4.symm j)) := by
      simp [b4]
    rw [h', h, hJ]
  have hGmat : LinearMap.BilinForm.toMatrix b4 B = antidiagGram := by
    ext i j
    rw [LinearMap.BilinForm.toMatrix_apply]
    exact hG i j
  have hres : ∀ c : C, ∀ x : Fin 2 ⊕ Fin 2 → K, x ∈ V₀ → c.1 x ∈ V₀ := by
    intro c x hx
    rw [hV₀] at hx ⊢
    rw [← (hC c.1 c.2).2.2.2.1 x, hx]
  let cRes : C → (V₀ →ₗ[ZMod 2] V₀) := fun c =>
    ((AddMonoidHom.mk' c.1 (hC c.1 c.2).1).toZModLinearMap 2).restrict (hres c)
  have hcRes : ∀ (c : C) (x : V₀), ((cRes c x : V₀) : Fin 2 ⊕ Fin 2 → K) = c.1 (x : _) :=
    fun c x => rfl
  have hcRes_mul : ∀ c d : C, cRes (c * d) = cRes c * cRes d := by
    intro c d
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    rfl
  have hcRes_one : cRes 1 = 1 := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    rfl
  let Mc : C → Matrix (Fin 4) (Fin 4) (ZMod 2) := fun c => LinearMap.toMatrix b4 b4 (cRes c)
  have hMmul : ∀ c d, Mc (c * d) = Mc c * Mc d := by
    intro c d
    simp only [Mc, hcRes_mul, LinearMap.toMatrix_mul]
  have hMone : Mc 1 = 1 := by
    simp only [Mc, hcRes_one, LinearMap.toMatrix_one]
  have hM2 : ∀ c, Mc c * Mc c = 1 := by
    intro c
    rw [← hMmul]
    have : c * c = 1 := Subtype.ext (hC c.1 c.2).2.2.1
    rw [this, hMone]
  have hiso : ∀ c : C, ∀ x y : V₀, B (cRes c x) (cRes c y) = B x y := by
    intro c x y
    apply hcinj
    rw [hBcast, hBcast, hcRes, hcRes]
    exact (hC c.1 c.2).2.2.2.2 _ _
  have hMsymp : ∀ c, (Mc c)ᵀ * antidiagGram * Mc c = antidiagGram := by
    intro c
    have hcomp : B.comp (cRes c) (cRes c) = B := by
      apply LinearMap.ext
      intro x
      apply LinearMap.ext
      intro y
      exact hiso c x y
    have := LinearMap.BilinForm.toMatrix_comp b4 b4 B (cRes c) (cRes c)
    rw [hcomp, hGmat] at this
    exact this.symm
  let φ : C →* sympFour :=
    { toFun := fun c => ⟨⟨Mc c, Mc c, hM2 c, hM2 c⟩, hMsymp c⟩
      map_one' := Subtype.ext (Units.ext hMone)
      map_mul' := fun c d => Subtype.ext (Units.ext (hMmul c d)) }
  refine ⟨φ, ?_⟩
  intro c d hcd
  have h1 : Mc c = Mc d := congrArg (fun g : sympFour => ((g : GL (Fin 4) (ZMod 2)) :
    Matrix (Fin 4) (Fin 4) (ZMod 2))) hcd
  have h2 : cRes c = cRes d := (LinearMap.toMatrix b4 b4).injective h1
  have h3 : ∀ x : Fin 2 ⊕ Fin 2 → K, x ∈ V₀ → c.1 x = d.1 x := by
    intro x hx
    have := congrArg (fun g : V₀ →ₗ[ZMod 2] V₀ => ((g ⟨x, hx⟩ : V₀) : Fin 2 ⊕ Fin 2 → K)) h2
    exact this
  apply Subtype.ext
  apply Equiv.ext
  intro v
  obtain ⟨u, z, hu, hz, rfl⟩ := sp44_descent_surj hK a' hinv hsq hw₀ v
  rw [(hC c.1 c.2).1, (hC d.1 d.2).1, (hC c.1 c.2).2.1, (hC d.1 d.2).2.1, h3 u hu, h3 z hz]

end Embed

end G118

end G11

end CFSG.Quasithin
