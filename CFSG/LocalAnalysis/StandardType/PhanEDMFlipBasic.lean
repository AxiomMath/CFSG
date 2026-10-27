module

public import CFSG.LocalAnalysis.StandardType.PhanEReduction
public import CFSG.LocalAnalysis.StandardType.PhanEDMCoxeterW0

public section

namespace CFSG.ClassicalInvolution.Phan.PhanE.DM

open CFSG.Monster.B.Geometry CFSG.LieType.Chevalley.CosetBuilding
  CFSG.ClassicalInvolution.Phan.PhanE

variable {ι : Type} {M : CoxeterMatrix ι} {W : Type} [Group W] {cs : CoxeterSystem M W}
  {C : Type} {δ : C → C → W}

@[expose] def dstar (δ : C → C → W) (w₀ : W) (t : C → C) (x : C) : W := δ x (t x) * w₀

theorem mul_simple_left (hB : IsWeylDistanceBuilding cs δ) {x y z : C} {i : ι}
    (h : δ x y = cs.simple i) :
    (δ y z = δ x z ∨ δ y z = cs.simple i * δ x z) ∧
      (cs.length (cs.simple i * δ x z) = cs.length (δ x z) + 1 →
        δ y z = cs.simple i * δ x z) := by
  have hzy := hB.mul_simple z x y i h
  have hyz : δ y z = (δ z y)⁻¹ := dist_inv hB z y
  have hxz : δ x z = (δ z x)⁻¹ := dist_inv hB z x
  constructor
  · rcases hzy.1 with h' | h'
    · left
      rw [hyz, hxz, h']
    · right
      rw [hyz, hxz, h', mul_inv_rev, cs.inv_simple]
  · intro hlen
    have hlen' : cs.length (δ z x * cs.simple i) = cs.length (δ z x) + 1 := by
      have h1 : (δ z x * cs.simple i)⁻¹ = cs.simple i * δ x z := by
        rw [mul_inv_rev, cs.inv_simple, hxz]
      calc cs.length (δ z x * cs.simple i)
          = cs.length ((δ z x * cs.simple i)⁻¹) := (cs.length_inv _).symm
        _ = cs.length (cs.simple i * δ x z) := by rw [h1]
        _ = cs.length (δ x z) + 1 := hlen
        _ = cs.length ((δ z x)⁻¹) + 1 := by rw [hxz]
        _ = cs.length (δ z x) + 1 := by rw [cs.length_inv]
    have h' := hzy.2 hlen'
    rw [hyz, h', mul_inv_rev, cs.inv_simple, hxz]

variable {w₀ : W} {t : C → C}

theorem dist_inv_flip (hB : IsWeylDistanceBuilding cs δ)
    (hw : ∀ w, cs.length (w * w₀) + cs.length w = cs.length w₀)
    (ht : IsSphericalFlip cs δ w₀ t) (x : C) :
    (δ x (t x))⁻¹ = w₀ * δ x (t x) * w₀ := by
  have hw0 : w₀ * w₀ = 1 := CoxeterSystem.w0_mul_self cs w₀ hw
  have h1 : δ x (t x) = w₀ * (δ x (t x))⁻¹ * w₀ := by
    have h := ht.dist (t x) x
    rw [ht.invol x, dist_inv hB x (t x)] at h
    exact h
  calc (δ x (t x))⁻¹
      = w₀ * w₀ * (δ x (t x))⁻¹ * w₀ * w₀ := by
        rw [hw0, one_mul, mul_assoc, hw0, mul_one]
    _ = w₀ * (w₀ * (δ x (t x))⁻¹ * w₀) * w₀ := by group
    _ = w₀ * δ x (t x) * w₀ := by rw [← h1]

theorem dstar_mul_self (hB : IsWeylDistanceBuilding cs δ)
    (hw : ∀ w, cs.length (w * w₀) + cs.length w = cs.length w₀)
    (ht : IsSphericalFlip cs δ w₀ t) (x : C) :
    dstar δ w₀ t x * dstar δ w₀ t x = 1 := by
  have h := dist_inv_flip hB hw ht x
  calc dstar δ w₀ t x * dstar δ w₀ t x
      = δ x (t x) * w₀ * (δ x (t x) * w₀) := rfl
    _ = δ x (t x) * (w₀ * δ x (t x) * w₀) := by group
    _ = δ x (t x) * (δ x (t x))⁻¹ := by rw [← h]
    _ = 1 := mul_inv_cancel _

theorem length_dstar_add (hw : ∀ w, cs.length (w * w₀) + cs.length w = cs.length w₀) (x : C) :
    cs.length (δ x (t x)) + cs.length (dstar δ w₀ t x) = cs.length w₀ := by
  rw [dstar, add_comm]
  exact hw (δ x (t x))

theorem dstar_step (hB : IsWeylDistanceBuilding cs δ)
    (hw : ∀ w, cs.length (w * w₀) + cs.length w = cs.length w₀)
    (ht : IsSphericalFlip cs δ w₀ t) {x y : C} {j : ι} (hxy : δ x y = cs.simple j) :
    dstar δ w₀ t y = dstar δ w₀ t x ∨ dstar δ w₀ t y = cs.simple j * dstar δ w₀ t x ∨
      dstar δ w₀ t y = dstar δ w₀ t x * cs.simple j ∨
      dstar δ w₀ t y = cs.simple j * dstar δ w₀ t x * cs.simple j := by
  obtain ⟨j', hj'⟩ := CoxeterSystem.exists_simple_conj_w0 cs w₀ hw j
  have hw0 : w₀ * w₀ = 1 := CoxeterSystem.w0_mul_self cs w₀ hw
  have hsj' : cs.simple j' * w₀ = w₀ * cs.simple j := by
    rw [← hj', mul_assoc, hw0, mul_one]
  have hstep : δ (t x) (t y) = cs.simple j' := by
    rw [ht.dist x y, hxy, hj']
  have h1 := (mul_simple_left hB hxy (z := t x)).1
  have h2 := (hB.mul_simple y (t x) (t y) j' hstep).1
  simp only [dstar]
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
  · left
    rw [h2, h1]
  · right; right; left
    rw [h2, h1, mul_assoc, hsj', ← mul_assoc]
  · right; left
    rw [h2, h1, mul_assoc]
  · right; right; right
    rw [h2, h1, mul_assoc, hsj']
    group

theorem dstar_mem_doubleCoset (hB : IsWeylDistanceBuilding cs δ)
    (hw : ∀ w, cs.length (w * w₀) + cs.length w = cs.length w₀)
    (ht : IsSphericalFlip cs δ w₀ t) {J : Set ι} {x y : C} (hy : y ∈ residue cs δ J x) :
    dstar δ w₀ t y ∈
      DoubleCoset.doubleCoset (dstar δ w₀ t x) (cs.parabolic J) (cs.parabolic J) := by
  induction hy with
  | refl => exact DoubleCoset.mem_doubleCoset_self _ _ _
  | @tail b c _ hbc ih =>
    obtain ⟨i, hi, hδi⟩ := hbc
    have hmem : dstar δ w₀ t c ∈
        DoubleCoset.doubleCoset (dstar δ w₀ t b) (cs.parabolic J) (cs.parabolic J) := by
      rcases dstar_step hB hw ht hδi with h | h | h | h
      · rw [h]
        exact DoubleCoset.mem_doubleCoset_self _ _ _
      · exact DoubleCoset.mem_doubleCoset.mpr
          ⟨cs.simple i, cs.simple_mem_parabolic hi, 1, Subgroup.one_mem _,
            by rw [h, mul_one]⟩
      · exact DoubleCoset.mem_doubleCoset.mpr
          ⟨1, Subgroup.one_mem _, cs.simple i, cs.simple_mem_parabolic hi,
            by rw [h, one_mul]⟩
      · exact DoubleCoset.mem_doubleCoset.mpr
          ⟨cs.simple i, cs.simple_mem_parabolic hi, cs.simple i,
            cs.simple_mem_parabolic hi, h⟩
    rwa [DoubleCoset.doubleCoset_eq_of_mem ih] at hmem

end CFSG.ClassicalInvolution.Phan.PhanE.DM
