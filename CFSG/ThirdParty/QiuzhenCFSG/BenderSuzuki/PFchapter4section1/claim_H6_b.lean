module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter4section1.claim_H6_a

namespace CFSG
end CFSG
open CFSG

namespace CFSG.BenderSuzuki
namespace PFchapter4section1

open PFchapter1section1 PFAppendixIII

/-! # Peterfalvi, Part II, Chapter IV, Section 1, (H6)(b) -/

private theorem h6b_hy_t_inv_rightConj
    {L : Type*} [Group L] {hy t : L}
    (htinv : t⁻¹ = t) (ht2 : t * t = 1) :
    hy * t * (rightConjugateElem hy t)⁻¹ = t := by
  rw [rightConjugateElem]
  simp only [mul_inv_rev, inv_inv]
  rw [htinv]
  rw [mul_assoc hy t (t * (hy⁻¹ * t))]
  rw [← mul_assoc t t (hy⁻¹ * t)]
  rw [ht2]
  simp

private theorem h6b_conj_transport
    {L : Type*} [Group L] {fz hy t : L}
    (htinv : t⁻¹ = t) (ht2 : t * t = 1) :
    hy * t * rightConjugateElem fz (rightConjugateElem hy t) =
      t * fz * rightConjugateElem hy t := by
  have hcancel := h6b_hy_t_inv_rightConj (hy := hy) (t := t) htinv ht2
  calc
    hy * t * rightConjugateElem fz (rightConjugateElem hy t)
        = hy * t * ((rightConjugateElem hy t)⁻¹ * fz * rightConjugateElem hy t) := by
          rw [rightConjugateElem]
    _ = (hy * t * (rightConjugateElem hy t)⁻¹) * fz * rightConjugateElem hy t := by
          simp [mul_assoc]
    _ = t * fz * rightConjugateElem hy t := by
          rw [hcancel]

private theorem h6b_reassoc_left
    {L : Type*} [Group L] {gx hx gz hz fz hy fy t : L} :
    gx * hx * (gz * hz * t * fz) * rightConjugateElem hy t * fy =
      gx * hx * gz * hz * (t * fz * rightConjugateElem hy t) * fy := by
  simp [mul_assoc]

private theorem h6b_twist_mul
    {L : Type*} [Group L] {a b t : L} (ht2 : t * t = 1) :
    t * (a * b) * t = (t * a * t) * (t * b * t) := by
  calc
    t * (a * b) * t = t * a * b * t := by
      simp [mul_assoc]
    _ = t * a * 1 * b * t := by
      simp
    _ = t * a * (t * t) * b * t := by
      rw [ht2]
    _ = (t * a * t) * (t * b * t) := by
      simp [mul_assoc]

private theorem h6b_insert_rightConj
    {L : Type*} [Group L] {a b z hy fy t : L}
    (htinv : t⁻¹ = t) (ht2 : t * t = 1) :
    a * b * t * z * hy * t * fy =
      a * b * (t * z * t) * rightConjugateElem hy t * fy := by
  rw [rightConjugateElem, htinv]
  calc
    a * b * t * z * hy * t * fy = a * b * t * z * 1 * hy * t * fy := by
      simp
    _ = a * b * t * z * (t * t) * hy * t * fy := by
      rw [ht2]
    _ = a * b * (t * z * t) * (t * hy * t) * fy := by
      simp [mul_assoc]

private theorem h6b_right_repack
    {L : Type*} [Group L] {a b c d e u v w : L} :
    a * b * c * d * (e * u * v) * w =
      (a * rightConjugateElem c (b⁻¹)) * (b * d * e) * u * (v * w) := by
  rw [rightConjugateElem]
  simp only [inv_inv]
  symm
  calc
    (a * (b * c * b⁻¹)) * (b * d * e) * u * (v * w)
        = a * b * c * (b⁻¹ * b) * d * e * u * v * w := by
          repeat rw [mul_assoc]
    _ = a * b * c * d * e * u * v * w := by
          rw [inv_mul_cancel]
          simp only [mul_one]
    _ = a * b * c * d * (e * u * v) * w := by
          repeat rw [mul_assoc]

public theorem h6_qd_t_q_comparison
    {L X : Type*} [Group L] [Finite L] [MulAction L X] [Finite X]
    (M Q D : Subgroup L) (t : L) (f g h : L → L)
    (htwo_transitive : MulAction.IsMultiplyPretransitive L X 2)
    (hpoint_stabilizer : ∃ x : X, M = MulAction.stabilizer L x)
    (ht_involution : IsInvolution t) (ht_not_mem_M : t ∉ M)
    (hD_eq : D = M ⊓ rightConjugate M t)
    (hQ_normal_in_M : (Q.subgroupOf M).Normal)
    (hQ_disjoint_D : Disjoint Q D) (hQ_sup_D : Q ⊔ D = M)
    (hf_mem : ∀ x : L, x ∈ Q → x ≠ 1 → f x ∈ Q ∧ f x ≠ 1)
    (hg_mem : ∀ x : L, x ∈ Q → x ≠ 1 → g x ∈ Q ∧ g x ≠ 1)
    (hh_mem : ∀ x : L, x ∈ Q → x ≠ 1 → h x ∈ D)
    (hcanonical_eq : ∀ x : L, x ∈ Q → x ≠ 1 → t * x * t = g x * h x * t * f x) :
    ∀ x y : L, x ∈ Q → y ∈ Q → x ≠ 1 → y ≠ 1 → x * y ≠ 1 →
      g x * rightConjugateElem (g (f x * g y)) (h x)⁻¹ ∈ Q ∧
      h x * h (f x * g y) * h y ∈ D ∧
      rightConjugateElem (f (f x * g y)) (rightConjugateElem (h y) t) * f y ∈ Q ∧
      g (x * y) * h (x * y) * t * f (x * y) =
        (g x * rightConjugateElem (g (f x * g y)) (h x)⁻¹) *
          (h x * h (f x * g y) * h y) * t *
          (rightConjugateElem (f (f x * g y)) (rightConjugateElem (h y) t) *
            f y) := by
  intro x y hxQ hyQ hx1 hy1 hxy1
  have htinv : t⁻¹ = t := ht_involution.inv_eq_self
  have ht2 : t * t = 1 := by
    calc
      t * t = t⁻¹ * t := by rw [htinv]
      _ = 1 := inv_mul_cancel t
  have hxyQ : x * y ∈ Q := Q.mul_mem hxQ hyQ
  have hfx := hf_mem x hxQ hx1
  have hgx := hg_mem x hxQ hx1
  have hhx := hh_mem x hxQ hx1
  have hfy := hf_mem y hyQ hy1
  have hgy := hg_mem y hyQ hy1
  have hhy := hh_mem y hyQ hy1
  let z : L := f x * g y
  have hzQ : z ∈ Q := Q.mul_mem hfx.1 hgy.1
  have hz1 : z ≠ 1 :=
    claim_H6_a M Q D t f g h htwo_transitive hpoint_stabilizer ht_involution ht_not_mem_M hD_eq hQ_normal_in_M hQ_disjoint_D hQ_sup_D hf_mem hg_mem hh_mem hcanonical_eq x y hxQ hyQ hx1 hy1 hxy1
  have hfz := hf_mem z hzQ hz1
  have hgz := hg_mem z hzQ hz1
  have hhz := hh_mem z hzQ hz1
  have hhyt : rightConjugateElem (h y) t ∈ D :=
    rightConjugateElem_mem_D (M := M) (D := D) htinv hD_eq hhy
  have hgz_conjQ :
      rightConjugateElem (g z) (h x)⁻¹ ∈ Q :=
    h6_rightConjugateElem_mem_Q_of_mem_M (rankOneSplit_Q_le_M hQ_sup_D) hQ_normal_in_M
      hgz.1 ((rankOneSplit_D_le_M hD_eq) (D.inv_mem hhx))
  have hfz_conjQ :
      rightConjugateElem (f z) (rightConjugateElem (h y) t) ∈ Q :=
    h6_rightConjugateElem_mem_Q_of_mem_M (rankOneSplit_Q_le_M hQ_sup_D) hQ_normal_in_M
      hfz.1 ((rankOneSplit_D_le_M hD_eq) hhyt)
  refine ⟨Q.mul_mem hgx.1 hgz_conjQ, ?_, ?_, ?_⟩
  · exact D.mul_mem (D.mul_mem hhx hhz) hhy
  · exact Q.mul_mem hfz_conjQ hfy.1
  · have hcan_x := hcanonical_eq x hxQ hx1
    have hcan_y := hcanonical_eq y hyQ hy1
    have hcan_z := hcanonical_eq z hzQ hz1
    have hcan_xy := hcanonical_eq (x * y) hxyQ hxy1
    have hprod :
        t * (x * y) * t =
          (g x * rightConjugateElem (g z) (h x)⁻¹) *
            (h x * h z * h y) * t *
            (rightConjugateElem (f z) (rightConjugateElem (h y) t) * f y) := by
      calc
        t * (x * y) * t = (t * x * t) * (t * y * t) := by
          exact h6b_twist_mul ht2
        _ = (g x * h x * t * f x) * (g y * h y * t * f y) := by
          rw [hcan_x, hcan_y]
        _ = g x * h x * t * z * h y * t * f y := by
          simp [z, mul_assoc]
        _ = g x * h x * (t * z * t) * rightConjugateElem (h y) t * f y := by
          exact h6b_insert_rightConj htinv ht2
        _ = g x * h x * (g z * h z * t * f z) *
              rightConjugateElem (h y) t * f y := by
          rw [hcan_z]
        _ = (g x * rightConjugateElem (g z) (h x)⁻¹) *
              (h x * h z * h y) * t *
              (rightConjugateElem (f z) (rightConjugateElem (h y) t) * f y) := by
          calc
            g x * h x * (g z * h z * t * f z) *
                rightConjugateElem (h y) t * f y =
              g x * h x * g z * h z *
                (t * f z * rightConjugateElem (h y) t) * f y := by
                exact h6b_reassoc_left
            _ = g x * h x * g z * h z *
                (h y * t *
                  rightConjugateElem (f z) (rightConjugateElem (h y) t)) * f y := by
                rw [← h6b_conj_transport (fz := f z) (hy := h y) (t := t) htinv ht2]
            _ = (g x * rightConjugateElem (g z) (h x)⁻¹) *
                (h x * h z * h y) * t *
                (rightConjugateElem (f z) (rightConjugateElem (h y) t) * f y) := by
                exact h6b_right_repack
    exact hcan_xy.symm.trans hprod

public theorem claim_H6_b
    {L X : Type*} [Group L] [Finite L] [MulAction L X] [Finite X]
    (M Q D : Subgroup L) (t : L) (f g h : L → L)
    (htwo_transitive : MulAction.IsMultiplyPretransitive L X 2)
    (hpoint_stabilizer : ∃ x : X, M = MulAction.stabilizer L x)
    (ht_involution : IsInvolution t) (ht_not_mem_M : t ∉ M)
    (hD_eq : D = M ⊓ rightConjugate M t)
    (hQ_normal_in_M : (Q.subgroupOf M).Normal)
    (hQ_disjoint_D : Disjoint Q D) (hQ_sup_D : Q ⊔ D = M)
    (hf_mem : ∀ x : L, x ∈ Q → x ≠ 1 → f x ∈ Q ∧ f x ≠ 1)
    (hg_mem : ∀ x : L, x ∈ Q → x ≠ 1 → g x ∈ Q ∧ g x ≠ 1)
    (hh_mem : ∀ x : L, x ∈ Q → x ≠ 1 → h x ∈ D)
    (hcanonical_eq : ∀ x : L, x ∈ Q → x ≠ 1 → t * x * t = g x * h x * t * f x) :
    ∀ x y : L, x ∈ Q → y ∈ Q → x ≠ 1 → y ≠ 1 → x * y ≠ 1 →
      f (x * y) =
        rightConjugateElem (f (f x * g y)) (rightConjugateElem (h y) t) * f y := by
  intro x y hxQ hyQ hx1 hy1 hxy1
  have htinv : t⁻¹ = t := ht_involution.inv_eq_self
  have hxyQ : x * y ∈ Q := Q.mul_mem hxQ hyQ
  have hcmp := h6_qd_t_q_comparison M Q D t f g h htwo_transitive hpoint_stabilizer ht_involution ht_not_mem_M hD_eq hQ_normal_in_M hQ_disjoint_D hQ_sup_D hf_mem hg_mem hh_mem hcanonical_eq x y hxQ hyQ hx1 hy1 hxy1
  exact qd_t_q_right_unique (M := M) (Q := Q) (D := D) (t := t)
    (q₁ := g (x * y)) (d₁ := h (x * y)) (r₁ := f (x * y))
    (q₂ := g x * rightConjugateElem (g (f x * g y)) (h x)⁻¹)
    (d₂ := h x * h (f x * g y) * h y)
    (r₂ := rightConjugateElem (f (f x * g y)) (rightConjugateElem (h y) t) * f y)
    htinv hD_eq (rankOneSplit_Q_le_M hQ_sup_D) (rankOneSplit_D_le_M hD_eq) hQ_disjoint_D
    (hg_mem (x * y) hxyQ hxy1).1
    (hh_mem (x * y) hxyQ hxy1)
    (hf_mem (x * y) hxyQ hxy1).1
    hcmp.1 hcmp.2.1 hcmp.2.2.1 hcmp.2.2.2

end PFchapter4section1
end CFSG.BenderSuzuki

