module

public import CFSG.RankThree.PartOne.K1214.PActFin

public section

namespace CFSG.RankThree.PartOne.K1214

variable {p r e : ℕ}

@[expose] def addEndHom (p r e : ℕ) :
    MulAut (Fin r → Multiplicative (ZMod (p ^ e))) →* AddMonoid.End (Fin r → ZMod (p ^ e)) where
  toFun θ :=
    { toFun := fun v i => Multiplicative.toAdd (θ (fun j => Multiplicative.ofAdd (v j)) i)
      map_zero' := by
        funext i
        have h : (fun j : Fin r => Multiplicative.ofAdd ((0 : Fin r → ZMod (p ^ e)) j)) = 1 := rfl
        rw [h, map_one]
        rfl
      map_add' := fun v w => by
        funext i
        have h : (fun j : Fin r => Multiplicative.ofAdd ((v + w) j)) =
            (fun j => Multiplicative.ofAdd (v j)) * (fun j => Multiplicative.ofAdd (w j)) := rfl
        rw [h, map_mul]
        rfl }
  map_one' := by
    apply AddMonoidHom.ext
    intro v
    rfl
  map_mul' := fun θ₁ θ₂ => by
    apply AddMonoidHom.ext
    intro v
    rfl

theorem addEndHom_apply (θ : MulAut (Fin r → Multiplicative (ZMod (p ^ e)))) (v : Fin r → ZMod (p ^ e))
    (i : Fin r) : addEndHom p r e θ v i = Multiplicative.toAdd (θ (fun j => Multiplicative.ofAdd (v j)) i) :=
  rfl

theorem act_lemma_mul [Fact p.Prime] (hp5 : 5 ≤ p) (hr : r = 1 ∨ r = 2) (he1 : 1 ≤ e)
    (he : r = 1 ∨ 2 ≤ e) {R : Type*} [Group R]
    (φ : R ≃* (Fin r → Multiplicative (ZMod (p ^ e)))) (σ : MulAut R) (hσ : σ ^ p = 1) :
    (∀ x : R, (σ x * x⁻¹) ^ p = 1) ∧ (∀ x : R, x ^ p = 1 → σ x = x) := by
  set θ : MulAut (Fin r → Multiplicative (ZMod (p ^ e))) := MulAut.congr φ σ with hθ
  have hθp : θ ^ p = 1 := by
    rw [hθ, ← map_pow, hσ, map_one]
  set α := addEndHom p r e θ with hα
  have hαp : α ^ p = 1 := by
    rw [hα, ← map_pow, hθp, map_one]
  set δ : AddMonoid.End (Fin r → ZMod (p ^ e)) := α - 1 with hδ
  have hg : (1 + δ) ^ p = 1 := by
    rw [hδ, add_sub_cancel]
    exact hαp
  obtain ⟨hA, hB⟩ := act_lemma_add hp5 hr he1 he hg
  have hθx : ∀ x : R, θ (φ x) = φ (σ x) := fun x => by
    rw [hθ]
    simp [MulAut.congr_apply]
  have hvec : ∀ x : R, (fun j => Multiplicative.ofAdd ((fun i => Multiplicative.toAdd (φ x i)) j)) = φ x :=
    fun x => rfl
  constructor
  · intro x
    obtain ⟨w, hw⟩ := hA (fun i => Multiplicative.toAdd (φ x i))
    apply φ.injective
    rw [map_pow, map_mul, map_inv, ← hθx x, map_one]
    funext i
    have h1 := congrFun hw i
    have h2 : δ (fun i => Multiplicative.toAdd (φ x i)) i =
        Multiplicative.toAdd (θ (φ x) i) - Multiplicative.toAdd (φ x i) := by
      rw [hδ]
      show (α (fun i => Multiplicative.toAdd (φ x i)) - (fun i => Multiplicative.toAdd (φ x i))) i = _
      rw [Pi.sub_apply, hα, addEndHom_apply, hvec x]
    show ((θ (φ x) * (φ x)⁻¹) ^ p) i = 1
    rw [Pi.pow_apply, Pi.mul_apply, Pi.inv_apply]
    apply Multiplicative.toAdd.injective
    rw [toAdd_pow, toAdd_mul, toAdd_inv]
    have h3 : Multiplicative.toAdd (θ (φ x) i) + -Multiplicative.toAdd (φ x i) = (p ^ (e - 1)) • w i := by
      rw [← sub_eq_add_neg, ← h2, h1]
      rfl
    rw [h3, ← mul_nsmul', ← pow_succ']
    have : p ^ (e - 1 + 1) = p ^ e := by
      congr 1
      omega
    rw [this]
    show (p ^ e) • w i = 0
    simp [nsmul_eq_mul]
  · intro x hx
    have hu : p • (fun i => Multiplicative.toAdd (φ x i)) = 0 := by
      funext i
      have := congrFun (congrArg φ hx) i
      rw [map_pow, map_one] at this
      show p • Multiplicative.toAdd (φ x i) = 0
      rw [← toAdd_pow, ← Pi.pow_apply, this]
      rfl
    have h0 := hB _ hu
    apply φ.injective
    rw [← hθx x]
    funext i
    have h1 := congrFun h0 i
    have h2 : δ (fun i => Multiplicative.toAdd (φ x i)) i =
        Multiplicative.toAdd (θ (φ x) i) - Multiplicative.toAdd (φ x i) := by
      rw [hδ]
      show (α (fun i => Multiplicative.toAdd (φ x i)) - (fun i => Multiplicative.toAdd (φ x i))) i = _
      rw [Pi.sub_apply, hα, addEndHom_apply, hvec x]
    rw [h2] at h1
    have h3 : Multiplicative.toAdd (θ (φ x) i) = Multiplicative.toAdd (φ x i) := sub_eq_zero.1 h1
    exact Multiplicative.toAdd.injective h3

end CFSG.RankThree.PartOne.K1214
