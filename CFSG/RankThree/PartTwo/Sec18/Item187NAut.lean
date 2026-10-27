module

public import Mathlib.Algebra.Group.End
public import Mathlib.Algebra.Group.Subgroup.Map

public section

namespace CFSG.RankThree.PartTwo.Sec18.Item187Proof

section Aut

@[expose] def restrictAut {Y : Type*} [Group Y] (σ : MulAut Y) (K : Subgroup Y)
    (hK : K.map σ.toMonoidHom = K) : MulAut ↥K where
  toFun k := ⟨σ k, by
    have h := Subgroup.mem_map_of_mem σ.toMonoidHom k.2
    rwa [hK] at h⟩
  invFun k := ⟨σ.symm k, by
    have h : (k : Y) ∈ K.map σ.toMonoidHom := by rw [hK]; exact k.2
    obtain ⟨k', hk', hkk'⟩ := h
    have e : σ.symm k = k' := by
      rw [← hkk']
      exact σ.symm_apply_apply k'
    rw [e]
    exact hk'⟩
  left_inv k := Subtype.ext (σ.symm_apply_apply k)
  right_inv k := Subtype.ext (σ.apply_symm_apply k)
  map_mul' a b := Subtype.ext (map_mul σ (a : Y) (b : Y))

theorem coe_restrictAut {Y : Type*} [Group Y] (σ : MulAut Y) (K : Subgroup Y)
    (hK : K.map σ.toMonoidHom = K) (k : ↥K) :
    ((restrictAut σ K hK k : ↥K) : Y) = σ k := rfl

theorem coe_pow_restrictAut {Y : Type*} [Group Y] (σ : MulAut Y) (K : Subgroup Y)
    (hK : K.map σ.toMonoidHom = K) (n : ℕ) (k : ↥K) :
    ((((restrictAut σ K hK) ^ n) k : ↥K) : Y) = (σ ^ n) k := by
  induction n generalizing k with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, pow_succ, MulAut.mul_apply, MulAut.mul_apply, ih]
    rfl

theorem restrictAut_pow_three {Y : Type*} [Group Y] (σ : MulAut Y) (K : Subgroup Y)
    (hK : K.map σ.toMonoidHom = K) (hσ : σ ^ 3 = 1) : restrictAut σ K hK ^ 3 = 1 := by
  ext k
  rw [coe_pow_restrictAut, hσ]
  rfl

theorem restrictAut_ne_one {Y : Type*} [Group Y] (σ : MulAut Y) (K : Subgroup Y)
    (hK : K.map σ.toMonoidHom = K) (h : ∃ z ∈ K, σ z ≠ z) : restrictAut σ K hK ≠ 1 := by
  obtain ⟨z, hz, hne⟩ := h
  intro h1
  apply hne
  have := congrArg (fun f : MulAut ↥K => ((f ⟨z, hz⟩ : ↥K) : Y)) h1
  simpa [coe_restrictAut] using this

end Aut

end CFSG.RankThree.PartTwo.Sec18.Item187Proof
