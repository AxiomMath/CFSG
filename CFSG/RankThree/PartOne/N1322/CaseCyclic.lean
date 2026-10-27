module

public import CFSG.RankThree.PartOne.N1322.CaseBasic
public import CFSG.RankThree.PartOne.N1322.CoreData

public section

namespace CFSG.RankThree.PartOne.N1322

open scoped Matrix
open CFSG.RepresentationTheory

variable {K : Type*} [Field K]

theorem eq_one_of_fixed {H : Subgroup (GL (Fin 3) K)} (hirr : IsIrreducibleMatrixRep H.subtype)
    (hcomm : ∀ a b : GL (Fin 3) K, a ∈ H → b ∈ H → a * b = b * a) {y : GL (Fin 3) K} (hy : y ∈ H)
    {x : Fin 3 → K} (hx0 : x ≠ 0) (hx : (y : Matrix (Fin 3) (Fin 3) K) *ᵥ x = x) : y = 1 := by
  let W : Submodule K (Fin 3 → K) := LinearMap.ker ((y : Matrix (Fin 3) (Fin 3) K) - 1).mulVecLin
  have hW : ∀ g : H, ∀ w ∈ W, ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ w ∈ W := by
    intro g w hw
    have hw' : ((y : Matrix (Fin 3) (Fin 3) K) - 1) *ᵥ w = 0 := hw
    have hc : ((y : Matrix (Fin 3) (Fin 3) K)) * ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
        ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * y := by
      rw [← Units.val_mul, ← Units.val_mul, hcomm y g hy g.2]
    show ((y : Matrix (Fin 3) (Fin 3) K) - 1) *ᵥ
      (((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ w) = 0
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.mulVec_mulVec, hc, ← Matrix.mulVec_mulVec]
    have : (y : Matrix (Fin 3) (Fin 3) K) *ᵥ w = w := by
      have := hw'
      rw [Matrix.sub_mulVec, Matrix.one_mulVec] at this
      exact sub_eq_zero.mp this
    rw [this, sub_self]
  rcases hirr W hW with h | h
  · exfalso
    have : x ∈ W := by
      show ((y : Matrix (Fin 3) (Fin 3) K) - 1) *ᵥ x = 0
      rw [Matrix.sub_mulVec, Matrix.one_mulVec, hx, sub_self]
    rw [h, Submodule.mem_bot] at this
    exact hx0 this
  · apply Units.ext
    ext i j
    have h1 : Pi.single j (1 : K) ∈ W := by rw [h]; trivial
    have h2 : ((y : Matrix (Fin 3) (Fin 3) K) - 1) *ᵥ Pi.single j 1 = 0 := h1
    have := congrFun h2 i
    rw [Matrix.mulVec_single_one] at this
    simp only [Pi.zero_apply] at this
    simp only [Units.val_one, Matrix.one_apply]
    exact sub_eq_zero.mp this

theorem no_refl_normalizing_cyclic (h4 : (4 : K) ≠ 0) {H : Subgroup (GL (Fin 3) K)}
    (hirr : IsIrreducibleMatrixRep H.subtype) (hcyc : IsCyclic H) {t : GL (Fin 3) K}
    (ht : IsRefl t) (hnorm : ∀ x ∈ H, t * x * t⁻¹ ∈ H) : False := by
  obtain ⟨g, hg⟩ := hcyc.exists_generator
  have hHg : ∀ x ∈ H, ∃ k : ℤ, (g : GL (Fin 3) K) ^ k = x := by
    intro x hx
    obtain ⟨k, hk⟩ := hg ⟨x, hx⟩
    exact ⟨k, congrArg Subtype.val hk⟩
  have hcomm : ∀ a b : GL (Fin 3) K, a ∈ H → b ∈ H → a * b = b * a := by
    intro a b ha hb
    obtain ⟨i, rfl⟩ := hHg a ha
    obtain ⟨j, rfl⟩ := hHg b hb
    rw [← zpow_add, ← zpow_add, add_comm]
  have hgH : (g : GL (Fin 3) K) ∈ H := g.2
  obtain ⟨k, hk⟩ := hHg _ (hnorm _ hgH)
  have ht' := ht
  obtain ⟨r, φ, hr, hφ, htm⟩ := ht
  have ht2 : t * t = 1 := IsRefl.sq ht'
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  rw [htinv] at hk
  have hx : ∃ x : Fin 3 → K, x ≠ 0 ∧ φ ⬝ᵥ x = 0 ∧
      φ ⬝ᵥ (((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ x) = 0 := by
    let F : (Fin 3 → K) →ₗ[K] K × K :=
      LinearMap.prod
        { toFun := fun x => φ ⬝ᵥ x
          map_add' := fun a b => dotProduct_add φ a b
          map_smul' := fun c a => by simp [dotProduct_smul] }
        { toFun := fun x => φ ⬝ᵥ (((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ x)
          map_add' := fun a b => by simp [Matrix.mulVec_add, dotProduct_add]
          map_smul' := fun c a => by simp [Matrix.mulVec_smul, dotProduct_smul] }
    have hlt : Module.finrank K (K × K) < Module.finrank K (Fin 3 → K) := by
      simp [Module.finrank_prod]
    obtain ⟨x, hxk, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
      (LinearMap.ker_ne_bot_of_finrank_lt hlt (f := F))
    have hFx : F x = 0 := hxk
    exact ⟨x, hx0, congrArg Prod.fst hFx, congrArg Prod.snd hFx⟩
  obtain ⟨x, hx0, hφx, hφgx⟩ := hx
  have htx : (t : Matrix (Fin 3) (Fin 3) K) *ᵥ x = x := by
    rw [IsRefl.mulVec_apply htm, hφx, zero_smul, sub_zero]
  obtain ⟨w, hw⟩ : ∃ w : Fin 3 → K, w = ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ x :=
    ⟨_, rfl⟩
  have htw : (t : Matrix (Fin 3) (Fin 3) K) *ᵥ w = w := by
    rw [IsRefl.mulVec_apply htm, hw, hφgx, zero_smul, sub_zero]
  have hw0 : w ≠ 0 := by
    intro h0
    apply hx0
    have := mulVec_inv_mulVec (g : GL (Fin 3) K) x
    rw [← hw, h0, Matrix.mulVec_zero] at this
    exact this.symm
  have hgkx : (((g : GL (Fin 3) K) ^ k : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ x = w := by
    rw [hk, Units.val_mul, Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, htx,
      ← hw]
    exact htw
  have hfix : (((g : GL (Fin 3) K) ^ (k - 1) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ w =
      w := by
    have h1 : (g : GL (Fin 3) K) ^ (k - 1) * g = (g : GL (Fin 3) K) ^ k := by
      rw [zpow_sub_one, inv_mul_cancel_right]
    rw [hw, Matrix.mulVec_mulVec, ← Units.val_mul, h1, hgkx, hw]
  have hone : (g : GL (Fin 3) K) ^ (k - 1) = 1 :=
    eq_one_of_fixed hirr hcomm (H.zpow_mem hgH _) hw0 hfix
  have hgk : (g : GL (Fin 3) K) ^ k = g := by
    have h1 : (g : GL (Fin 3) K) ^ (k - 1) * g = (g : GL (Fin 3) K) ^ k := by
      rw [zpow_sub_one, inv_mul_cancel_right]
    rw [← h1, hone, one_mul]
  have hcg : t * (g : GL (Fin 3) K) = g * t := by
    calc t * (g : GL (Fin 3) K) = (t * g * t) * t := by rw [mul_assoc (t * (g : GL (Fin 3) K)) t t, ht2, mul_one]
      _ = g * t := by rw [← hk, hgk]
  have hcH : ∀ y ∈ H, t * y = y * t := by
    intro y hy
    obtain ⟨m, rfl⟩ := hHg y hy
    exact ((Commute.zpow_right (show Commute t (g : GL (Fin 3) K) from hcg) m)).eq
  let W : Submodule K (Fin 3 → K) := LinearMap.ker ((t : Matrix (Fin 3) (Fin 3) K) + 1).mulVecLin
  have hW : ∀ y : H, ∀ v ∈ W, ((y : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ v ∈ W := by
    intro y v hv
    have hv' : ((t : Matrix (Fin 3) (Fin 3) K) + 1) *ᵥ v = 0 := hv
    have hc : (t : Matrix (Fin 3) (Fin 3) K) * ((y : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
        ((y : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * t := by
      rw [← Units.val_mul, ← Units.val_mul, hcH y y.2]
    show ((t : Matrix (Fin 3) (Fin 3) K) + 1) *ᵥ (((y : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ v) = 0
    have e1 : (t : Matrix (Fin 3) (Fin 3) K) *ᵥ (((y : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ v) =
        ((y : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ ((t : Matrix (Fin 3) (Fin 3) K) *ᵥ v) := by
      rw [Matrix.mulVec_mulVec, hc, ← Matrix.mulVec_mulVec]
    have e2 : (t : Matrix (Fin 3) (Fin 3) K) *ᵥ v + v = 0 := by
      have := hv'
      rwa [Matrix.add_mulVec, Matrix.one_mulVec] at this
    rw [Matrix.add_mulVec, Matrix.one_mulVec, e1, ← Matrix.mulVec_add, e2, Matrix.mulVec_zero]
  rcases hirr W hW with h | h
  · have hrW : r ∈ W := by
      show ((t : Matrix (Fin 3) (Fin 3) K) + 1) *ᵥ r = 0
      rw [Matrix.add_mulVec, Matrix.one_mulVec, IsRefl.mulVec_root hφ htm, neg_add_cancel]
    rw [h, Submodule.mem_bot] at hrW
    exact hr hrW
  · apply IsRefl.ne_neg_one h4 ht'
    ext i j
    have h1 : Pi.single j (1 : K) ∈ W := by rw [h]; trivial
    have h2 : ((t : Matrix (Fin 3) (Fin 3) K) + 1) *ᵥ Pi.single j 1 = 0 := h1
    have h3 := congrFun h2 i
    rw [Matrix.mulVec_single_one] at h3
    simp only [Pi.zero_apply] at h3
    simp only [Matrix.neg_apply, Matrix.one_apply]
    exact eq_neg_of_add_eq_zero_left h3

end CFSG.RankThree.PartOne.N1322
