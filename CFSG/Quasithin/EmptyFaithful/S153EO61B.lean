module

public import CFSG.Quasithin.EmptyFaithful.S153EO61A
public import CFSG.Quasithin.EmptyFaithful.S153E58D
public import Certificates.Data.ExceptionalSL3

public section

namespace CFSG.Quasithin

open CFSG.Assembly.LowTwoRank
open Matrix

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace S153EO61

section Abstract

variable {W : Type} [CommGroup W]

theorem exists_commuting_order_three {K : Subgroup (MulAut W)} {W₁ W₂ : Subgroup W}
    (bil : W → W → ZMod 2)
    (bil_right : ∀ a b c, bil a (b * c) = bil a b + bil a c)
    (bil_symm : ∀ a b, bil a b = bil b a)
    (bil_nondeg : ∀ a, (∀ b, bil a b = 0) → a = 1)
    (hbilK : ∀ k ∈ K, ∀ a b, bil (k a) (k b) = bil a b)
    (dir : IsIntDirect W₁ W₂ ⊤) {π : ↥(StatedSL 3 (ZMod 2)) →* ↥K}
    (hπ : (FFModel.nat (StatedSL 3 (ZMod 2))).RealizesVia K W₁ ⊥ π)
    (hKW₂ : ∀ k ∈ K, ∀ u ∈ W₂, k u ∈ W₂)
    {τ : MulAut W} (hτ2 : τ * τ = 1) (hτbil : ∀ a b, bil (τ a) (τ b) = bil a b)
    (hτ₁ : ∀ x ∈ W₁, τ x ∈ W₂) (hτ₂ : ∀ x ∈ W₂, τ x ∈ W₁) :
    ∃ d ∈ K, orderOf d = 3 ∧ d * τ = τ * d := by
  classical
  obtain ⟨e, hT, he⟩ := S153E58.exists_coords_of_realizes hπ
  have hKW₁ : ∀ k ∈ K, ∀ u ∈ W₁, (k : MulAut W) u ∈ W₁ := fun k hk u hu => hπ.2.2.2.1 ⟨k, hk⟩ u hu
  have bil_left : ∀ a b c, bil (a * b) c = bil a c + bil b c := fun a b c => by
    rw [bil_symm, bil_right, bil_symm c a, bil_symm c b]
  have bil_one : ∀ a, bil a 1 = 0 := fun a => by
    have := bil_right a 1 1
    rw [mul_one] at this
    have h2 : bil a 1 + bil a 1 = bil a 1 + 0 := by rw [← this, add_zero]
    exact add_left_cancel h2
  have bil_inv : ∀ a c, bil a c⁻¹ = bil a c := fun a c => by
    have := bil_right a c c⁻¹
    rw [mul_inv_cancel, bil_one] at this
    have key : ∀ x y : ZMod 2, 0 = x + y → y = x := by decide
    exact key _ _ this
  have h0 : ∀ a ∈ W₁, ∀ b ∈ W₁, bil a b = 0 :=
    S153E58.form_zero_of_transv hT hKW₁ bil bil_right (fun k hk a _ b _ => hbilK k hk a b)
  have hττ : ∀ a, τ (τ a) = a := fun a => by
    have := congrArg (fun f : MulAut W => f a) hτ2
    simpa using this
  have h0' : ∀ a ∈ W₂, ∀ b ∈ W₂, bil a b = 0 := by
    intro a ha b hb
    have := hτbil (τ a) (τ b)
    rw [hττ, hττ] at this
    rw [this]
    exact h0 _ (hτ₂ a ha) _ (hτ₂ b hb)
  have hdec : ∀ w : W, ∃ x ∈ W₁, ∃ u ∈ W₂, x * u = w := by
    intro w
    have hw : w ∈ W₁ ⊔ W₂ := dir.1 ▸ Subgroup.mem_top w
    exact Subgroup.mem_sup.1 hw
  have hperp : ∀ a, (∀ x ∈ W₁, bil a x = 0) → (∀ u ∈ W₂, bil a u = 0) → a = 1 := by
    intro a h1 h2
    apply bil_nondeg a
    intro b
    obtain ⟨x, hx, u, hu, rfl⟩ := hdec b
    rw [bil_right, h1 x hx, h2 u hu, add_zero]
  have hperp₁ : ∀ a ∈ W₁, (∀ u ∈ W₂, bil a u = 0) → a = 1 := fun a ha h =>
    hperp a (fun x hx => h0 a ha x hx) h
  have hperp₂ : ∀ a ∈ W₂, (∀ x ∈ W₁, bil x a = 0) → a = 1 := fun a ha h =>
    hperp a (fun x hx => by rw [bil_symm]; exact h x hx) (fun u hu => h0' a ha u hu)
  let emb : (Fin 3 → ZMod 2) → W := fun u => ((e.symm (Multiplicative.ofAdd u) : ↥W₁) : W)
  have emb_mem : ∀ u, emb u ∈ W₁ := fun u => (e.symm _).2
  have emb_add : ∀ u v, emb (u + v) = emb u * emb v := by
    intro u v
    simp only [emb]
    rw [show Multiplicative.ofAdd (u + v) = Multiplicative.ofAdd u * Multiplicative.ofAdd v from rfl,
      map_mul]
    rfl
  have emb_inj : ∀ u v, emb u = emb v → u = v := by
    intro u v h
    have h1 : e.symm (Multiplicative.ofAdd u) = e.symm (Multiplicative.ofAdd v) := Subtype.ext h
    exact Multiplicative.ofAdd.injective (e.symm.injective h1)
  have emb_one : emb 0 = 1 := by
    simp only [emb]
    rw [show Multiplicative.ofAdd (0 : Fin 3 → ZMod 2) = 1 from rfl, map_one]
    rfl
  have emb_surj : ∀ x ∈ W₁, ∃ ξ, emb ξ = x := by
    intro x hx
    refine ⟨Multiplicative.toAdd (e ⟨x, hx⟩), ?_⟩
    simp [emb]
  let β : (Fin 3 → ZMod 2) → (Fin 3 → ZMod 2) → ZMod 2 := fun u v => bil (emb u) (τ (emb v))
  have hβ₁ : ∀ x x' y, β (x + x') y = β x y + β x' y := by
    intro x x' y
    simp only [β, emb_add, bil_left]
  have hβ₂ : ∀ x y y', β x (y + y') = β x y + β x y' := by
    intro x y y'
    simp only [β, emb_add, map_mul, bil_right]
  have hβsymm : ∀ u v, β u v = β v u := by
    intro u v
    simp only [β]
    have := hτbil (emb u) (τ (emb v))
    rw [hττ] at this
    rw [← this, bil_symm]
  set A : Matrix (Fin 3) (Fin 3) (ZMod 2) := Matrix.of fun i j => β (Pi.single i 1) (Pi.single j 1) with hA
  have hAβ : ∀ x y, β x y = x ⬝ᵥ (A *ᵥ y) := fun x y => biadd_eq_dot β hβ₁ hβ₂ x y
  have hAsymm : Aᵀ = A := by
    ext i j
    simp only [hA, Matrix.transpose_apply, Matrix.of_apply]
    exact hβsymm _ _
  have hAnd : ∀ v : Fin 3 → ZMod 2, (∀ w : Fin 3 → ZMod 2, v ⬝ᵥ (A *ᵥ w) = 0) → v = 0 := by
    intro v hv
    have h1 : emb v = 1 := by
      apply hperp₁ _ (emb_mem v)
      intro u hu
      obtain ⟨ξ, hξ⟩ := emb_surj _ (hτ₂ u hu)
      have : u = τ (emb ξ) := by rw [hξ, hττ]
      rw [this]
      have := hAβ v ξ
      simp only [β] at this
      rw [this]
      exact hv ξ
    exact emb_inj _ _ (h1.trans emb_one.symm)
  obtain ⟨γ, hγ3, hγ1, hγ⟩ := finite_check A hAsymm hAnd
  let gl : GL (Fin 3) (ZMod 2) := ⟨γ, γ * γ, by rw [← mul_assoc]; exact hγ3, hγ3⟩
  let g : ↥(StatedSL 3 (ZMod 2)) := ⟨gl, S153E58.mem_statedSL_three_two gl⟩
  have hgval : (((g : ↥(StatedSL 3 (ZMod 2))) : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) = γ :=
    rfl
  have hggval : ((((g * g : ↥(StatedSL 3 (ZMod 2))) : GL (Fin 3) (ZMod 2)) :
      Matrix (Fin 3) (Fin 3) (ZMod 2))) = γ * γ := rfl
  have hg3 : g * g * g = 1 := by
    apply Subtype.ext
    apply Units.ext
    exact hγ3
  have hact : ∀ (h : ↥(StatedSL 3 (ZMod 2))) (ξ : Fin 3 → ZMod 2),
      (π h : MulAut W) (emb ξ) =
        emb ((((h : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2))) *ᵥ ξ) := by
    intro h ξ
    have hu : (π h : MulAut W) (emb ξ) ∈ W₁ := hKW₁ _ (π h).2 _ (emb_mem ξ)
    have h1 := he h (e.symm (Multiplicative.ofAdd ξ)) hu
    have h2 : e ⟨(π h : MulAut W) (emb ξ), hu⟩ =
        Multiplicative.ofAdd (((h : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ ξ) := by
      rw [h1]
      simp [natAct]
    have h3 := congrArg (fun z => ((e.symm z : ↥W₁) : W)) h2
    simpa using h3
  have hdg : ∀ ξ, (π g : MulAut W) (emb ξ) = emb (γ *ᵥ ξ) := fun ξ => by rw [hact, hgval]
  have hddg : ∀ ξ, (π (g * g) : MulAut W) (emb ξ) = emb ((γ * γ) *ᵥ ξ) := fun ξ => by
    rw [hact, hggval]
  have hd1 : (π g : MulAut W) ≠ 1 := by
    intro h1
    apply hγ1
    ext i j
    have h2 := hdg (Pi.single j 1)
    rw [h1, MulAut.one_apply] at h2
    have h3 := congrFun (emb_inj _ _ h2) i
    have h4 : γ i j = (Pi.single j (1 : ZMod 2) : Fin 3 → ZMod 2) i := by simpa [Matrix.mulVec_single_one] using h3.symm
    rw [h4, Matrix.one_apply, Pi.single_apply]
  have hd3 : (π g : MulAut W) ^ 3 = 1 := by
    have : (π g : MulAut W) ^ 3 = ((π (g * g * g) : ↥K) : MulAut W) := by
      rw [map_mul, map_mul]
      simp [pow_succ, mul_assoc]
    rw [this, hg3, map_one]
    rfl
  have hdinv : ∀ ξ, (π g : MulAut W) ((π (g * g) : MulAut W) (emb ξ)) = emb ξ := by
    intro ξ
    rw [hddg, hdg, Matrix.mulVec_mulVec]
    congr 1
    rw [show γ * (γ * γ) = γ * γ * γ by rw [mul_assoc], hγ3, Matrix.one_mulVec]
  have hcomm : ∀ x ∈ W₁, (π g : MulAut W) (τ x) = τ ((π g : MulAut W) x) := by
    intro x hx
    obtain ⟨η, rfl⟩ := emb_surj x hx
    have hp : (π g : MulAut W) (τ (emb η)) ∈ W₂ := hKW₂ _ (π g).2 _ (hτ₁ _ (emb_mem η))
    have hq : τ ((π g : MulAut W) (emb η)) ∈ W₂ := hτ₁ _ (hKW₁ _ (π g).2 _ (emb_mem η))
    have hpq : (π g : MulAut W) (τ (emb η)) * (τ ((π g : MulAut W) (emb η)))⁻¹ = 1 := by
      apply hperp₂ _ (W₂.mul_mem hp (W₂.inv_mem hq))
      intro x' hx'
      obtain ⟨ξ, rfl⟩ := emb_surj x' hx'
      rw [bil_right, bil_inv]
      have e1 : bil (emb ξ) ((π g : MulAut W) (τ (emb η))) =
          bil (emb ((γ * γ) *ᵥ ξ)) (τ (emb η)) := by
        have := hbilK _ (π g).2 ((π (g * g) : MulAut W) (emb ξ)) (τ (emb η))
        rw [hdinv] at this
        rw [this, hddg]
      have e2 : bil (emb ξ) (τ ((π g : MulAut W) (emb η))) = bil (emb ξ) (τ (emb (γ *ᵥ η))) := by
        rw [hdg]
      rw [e1, e2]
      have e3 := hγ ξ η
      have e4 := hAβ ((γ * γ) *ᵥ ξ) η
      have e5 := hAβ ξ (γ *ᵥ η)
      simp only [β] at e4 e5
      rw [e4, e5, e3]
      generalize ξ ⬝ᵥ (A *ᵥ (γ *ᵥ η)) = z
      revert z
      decide
    exact mul_inv_eq_one.1 hpq
  refine ⟨(π g : MulAut W), (π g).2, orderOf_eq_prime hd3 hd1, ?_⟩
  ext w
  obtain ⟨x, hx, u, hu, rfl⟩ := hdec w
  simp only [MulAut.mul_apply, map_mul]
  rw [hcomm x hx]
  congr 1
  have h1 := hcomm (τ u) (hτ₂ u hu)
  rw [hττ] at h1
  have h2 := congrArg τ h1
  rw [hττ] at h2
  exact h2.symm

end Abstract

end S153EO61

end CFSG.Quasithin
