module

public import CFSG.LocalAnalysis.StandardType.GGWitOrthClassR53Aux3
public import CFSG.LocalAnalysis.StandardType.GGWitOrthClassR53Data
import CFSG.LocalAnalysis.StandardType.GGWitOrthCoord
import CFSG.LocalAnalysis.StandardType.GGWitOrthTypeA

public section

namespace CFSG.StandardType.ZS
open Subgroup
open scoped BigOperators

noncomputable def owR53_alphaY (w : Fin 3 → ZMod 5) (c : ZMod 5) (y : Fin 3 → ZMod 5) :
    (Fin 3 → ZMod 5) →ₗ[ZMod 5] ZMod 5 :=
  (2 * c⁻¹) • ∑ k, (w k * y k) • LinearMap.proj (R := ZMod 5) k

theorem owR53_alphaY_apply (w : Fin 3 → ZMod 5) (c : ZMod 5) (y : Fin 3 → ZMod 5)
    (v : Fin 3 → ZMod 5) :
    owR53_alphaY w c y v = (2 * c⁻¹) * ∑ k, w k * (v k * y k) := by
  simp only [owR53_alphaY, LinearMap.smul_apply, LinearMap.sum_apply, LinearMap.add_apply,
    LinearMap.proj_apply, smul_eq_mul, Fin.sum_univ_three]
  ring

theorem owR53_alphaY_self (w : Fin 3 → ZMod 5) (c : ZMod 5) (hc : c ≠ 0)
    (y : Fin 3 → ZMod 5) (hy : (∑ k, w k * (y k * y k)) = c) :
    owR53_alphaY w c y y = 2 := by
  rw [owR53_alphaY_apply, hy, show (2 * c⁻¹) * c = 2 * (c⁻¹ * c) by ring,
    owR53D_c_inv c hc, mul_one]

noncomputable def owR53_rOf (w : Fin 3 → ZMod 5) (c : ZMod 5) (hc : c ≠ 0)
    (y : Fin 3 → ZMod 5) (hy : (∑ k, w k * (y k * y k)) = c) :
    (Fin 3 → ZMod 5) ≃ₗ[ZMod 5] (Fin 3 → ZMod 5) :=
  Module.reflection (f := owR53_alphaY w c y) (x := y) (owR53_alphaY_self w c hc y hy)

theorem owR53_r_congr (w : Fin 3 → ZMod 5) (c : ZMod 5) (hc : c ≠ 0)
    (x y : Fin 3 → ZMod 5)
    (hx : (∑ k, w k * (x k * x k)) = c) (hy : (∑ k, w k * (y k * y k)) = c) (h : x = y) :
    owR53_rOf w c hc x hx = owR53_rOf w c hc y hy := by
  subst h
  rfl

noncomputable def owR53_formY (w : Fin 3 → ZMod 5) (c : ZMod 5) (b v : Fin 3 → ZMod 5) : Fin 3 → ZMod 5 :=
  v - (owR53_alphaY w c b v) • b

theorem owR53_rOf_apply (w : Fin 3 → ZMod 5) (c : ZMod 5) (hc : c ≠ 0)
    (y : Fin 3 → ZMod 5) (hy : (∑ k, w k * (y k * y k)) = c) (v : Fin 3 → ZMod 5) :
    owR53_rOf w c hc y hy v = owR53_formY w c y v :=
  Module.reflection_apply (f := owR53_alphaY w c y) (x := y) (h := owR53_alphaY_self w c hc y hy) (y := v)

theorem owR53_formY_norm (w : Fin 3 → ZMod 5) (c : ZMod 5) (hc : c ≠ 0)
    (y z : Fin 3 → ZMod 5) (hy : (∑ k, w k * (y k * y k)) = c)
    (hz : (∑ k, w k * (z k * z k)) = c) :
    ∑ k, w k * (owR53_formY w c y z k * owR53_formY w c y z k) = c := by
  set A : ZMod 5 := owR53_alphaY w c y z with hA
  have hAval : A = (2 * c⁻¹) * ∑ k, w k * (z k * y k) := by rw [hA, owR53_alphaY_apply]
  have hform : ∀ k, owR53_formY w c y z k = z k - A * y k := by
    intro k; simp only [owR53_formY, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hA]
  calc ∑ k, w k * (owR53_formY w c y z k * owR53_formY w c y z k)
      = ∑ k, w k * ((z k - A * y k) * (z k - A * y k)) := by
        apply Finset.sum_congr rfl; intro k _; rw [hform k]
    _ = ∑ k, (w k * (z k * z k) - (2 * A) * (w k * (z k * y k))
          + (A * A) * (w k * (y k * y k))) := by
        apply Finset.sum_congr rfl; intro k _; ring
    _ = (∑ k, w k * (z k * z k)) - (2 * A) * (∑ k, w k * (z k * y k))
          + (A * A) * (∑ k, w k * (y k * y k)) := by
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.mul_sum, Finset.mul_sum]
    _ = c := by
        rw [hz, hy, hAval]
        simp only [Fin.sum_univ_three]
        linear_combination (4 * c⁻¹ * (w 0 * (z 0 * y 0) + w 1 * (z 1 * y 1) + w 2 * (z 2 * y 2))
          * (w 0 * (z 0 * y 0) + w 1 * (z 1 * y 1) + w 2 * (z 2 * y 2))) * (owR53D_c_inv c hc)

theorem owR53_bilin (w : Fin 3 → ZMod 5) (c : ZMod 5) (hc : c ≠ 0)
    (b : Fin 3 → ZMod 5) (hb : (∑ k, w k * (b k * b k)) = c) (v x : Fin 3 → ZMod 5) :
    ∑ k, w k * (owR53_formY w c b v k * x k) = ∑ k, w k * (v k * owR53_formY w c b x k) := by
  simp only [owR53_formY, owR53_alphaY_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
    Fin.sum_univ_three]
  ring

theorem owR53_alpha_conj (w : Fin 3 → ZMod 5) (c : ZMod 5) (hc : c ≠ 0)
    (b : Fin 3 → ZMod 5) (hb : (∑ k, w k * (b k * b k)) = c) (v x : Fin 3 → ZMod 5) :
    owR53_alphaY w c (owR53_formY w c b x) v = owR53_alphaY w c x (owR53_formY w c b v) := by
  rw [owR53_alphaY_apply, owR53_alphaY_apply, owR53_bilin w c hc b hb v x]

theorem owR53_reflP_conj (w : Fin 3 → ZMod 5) (c : ZMod 5) (hc : c ≠ 0)
    (b x : Fin 3 → ZMod 5) (hb : (∑ k, w k * (b k * b k)) = c)
    (hx : (∑ k, w k * (x k * x k)) = c) :
    owR53_rOf w c hc b hb * owR53_rOf w c hc x hx * (owR53_rOf w c hc b hb)⁻¹
      = owR53_rOf w c hc (owR53_formY w c b x)
          (owR53_formY_norm w c hc b x hb hx) := by
  unfold owR53_rOf
  ext v
  rw [Module.reflection_apply (x := owR53_formY w c b x)
    (f := owR53_alphaY w c (owR53_formY w c b x))
    (h := owR53_alphaY_self w c hc (owR53_formY w c b x) (owR53_formY_norm w c hc b x hb hx)) (y := v)]
  simp only [LinearEquiv.mul_apply, Module.reflection_inv]
  rw [owR53_alpha_conj w c hc b hb v x]
  have h1 : Module.reflection (f := owR53_alphaY w c x) (x := x) (owR53_alphaY_self w c hc x hx)
        (Module.reflection (f := owR53_alphaY w c b) (x := b) (owR53_alphaY_self w c hc b hb) v)
      = Module.reflection (f := owR53_alphaY w c b) (x := b) (owR53_alphaY_self w c hc b hb) v
        - owR53_alphaY w c x
            (Module.reflection (f := owR53_alphaY w c b) (x := b)
              (owR53_alphaY_self w c hc b hb) v) • x :=
    Module.reflection_apply (x := x) (f := owR53_alphaY w c x)
      (h := owR53_alphaY_self w c hc x hx)
      (y := Module.reflection (f := owR53_alphaY w c b) (x := b) (owR53_alphaY_self w c hc b hb) v)
  have h2 : Module.reflection (f := owR53_alphaY w c b) (x := b) (owR53_alphaY_self w c hc b hb)
        (Module.reflection (f := owR53_alphaY w c b) (x := b)
          (owR53_alphaY_self w c hc b hb) v) = v :=
    Module.involutive_reflection (owR53_alphaY_self w c hc b hb) v
  rw [h1, map_sub, map_smul, h2]
  simp only [owR53_formY, Module.reflection_apply]

theorem owR53_alphaY_neg (w : Fin 3 → ZMod 5) (c : ZMod 5) (y : Fin 3 → ZMod 5) :
    owR53_alphaY w c (-y) = -owR53_alphaY w c y := by
  apply LinearMap.ext; intro v
  rw [owR53_alphaY_apply, LinearMap.neg_apply, owR53_alphaY_apply]
  simp only [Pi.neg_apply, Fin.sum_univ_three]
  ring

theorem owR53_refl_neg (w : Fin 3 → ZMod 5) (c : ZMod 5) (hc : c ≠ 0)
    (y : Fin 3 → ZMod 5) (hy : (∑ k, w k * (y k * y k)) = c)
    (hy' : (∑ k, w k * (-y k * -y k)) = c) :
    owR53_rOf w c hc (-y) hy' = owR53_rOf w c hc y hy := by
  have hα := owR53_alphaY_neg w c y
  unfold owR53_rOf
  ext v
  simp only [Module.reflection_apply]
  rw [show owR53_alphaY w c (-y) v = -owR53_alphaY w c y v from by rw [hα]; rfl]
  simp only [neg_smul, smul_neg, neg_neg]

theorem owR53_rOf_mem_class (w : Fin 3 → ZMod 5) (c : ZMod 5) (hc : c ≠ 0)
    (y : Fin 3 → ZMod 5) (hy : (∑ k, w k * (y k * y k)) = c) :
    owR53_rOf w c hc y hy ∈ ClassRefl 5 (QuadraticMap.weightedSumSquares (ZMod 5) w) c := by
  rw [wit_coord_classRefl_iff (by norm_num) (by norm_num) w c hc]
  refine ⟨y, hy, fun v => ?_⟩
  rw [owR53_rOf_apply]
  unfold owR53_formY
  rw [owR53_alphaY_apply]

theorem owR53_xs_mem (w : Fin 3 → ZMod 5) (c : ZMod 5) (hc : c ≠ 0) (hg : owR53D_guard w c)
    (H : Subgroup ((Fin 3 → ZMod 5) ≃ₗ[ZMod 5] (Fin 3 → ZMod 5)))
    (hroot : ∀ i : Fin 4, owR53_rOf w c hc (owR53D_root w c i) (owR53D_norms w c hg i) ∈ H) :
    ∀ k, (hk : k < owR53D_len w c) →
      owR53_rOf w c hc (owR53D_xs w c k) (owR53D_xs_norm w c hg k hk) ∈ H := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    by_cases hk4 : k < 4
    · rw [owR53_r_congr w c hc (owR53D_xs w c k) (owR53D_root w c (Fin.ofNat 4 k))
        (owR53D_xs_norm w c hg k hk) (owR53D_norms w c hg _) (owR53D_base w c hg k hk4)]
      exact hroot _
    · have hk4' : 4 ≤ k := not_lt.mp hk4
      have hpar := owR53D_par_lt w c hg k hk4' hk
      have hch := owR53D_chain w c hg k hk4' hk
      have hbn := owR53D_norms w c hg (owR53D_gen w c k)
      have hxpn := owR53D_xs_norm w c hg (owR53D_par w c k) (lt_trans hpar hk)
      have hform : owR53D_xs w c k = owR53_formY w c (owR53D_root w c (owR53D_gen w c k))
          (owR53D_xs w c (owR53D_par w c k)) := by
        rw [hch]
        funext i
        simp only [owR53D_rf, owR53_formY, owR53_alphaY_apply, Pi.sub_apply, Pi.smul_apply,
          smul_eq_mul]
      rw [owR53_r_congr w c hc (owR53D_xs w c k)
        (owR53_formY w c (owR53D_root w c (owR53D_gen w c k)) (owR53D_xs w c (owR53D_par w c k)))
        (owR53D_xs_norm w c hg k hk)
        (owR53_formY_norm w c hc _ _ hbn hxpn) hform,
        ← owR53_reflP_conj w c hc _ _ hbn hxpn]
      exact H.mul_mem (H.mul_mem (hroot _) (ih _ hpar (lt_trans hpar hk))) (H.inv_mem (hroot _))

theorem owR53_weyl_half_core (w : Fin 3 → ZMod 5) (c : ZMod 5) (hg : owR53D_guard w c) :
    LinWeyl 5 (closure (ClassRefl 5 (QuadraticMap.weightedSumSquares (ZMod 5) w) c)) := by
  classical
  have hc : c ≠ 0 := hg.2.2.2.1
  have hnorm := owR53D_norms w c hg
  have hne : ∀ i, owR53D_lam w c i ≠ 0 := by
    intro i h0
    have h1 := owR53D_lam_mul_self w c hg i
    rw [h0] at h1
    exact absurd h1 (by decide)
  let r : Fin 4 → (Fin 3 → ZMod 5) ≃ₗ[ZMod 5] (Fin 3 → ZMod 5) :=
    fun i => owR53_rOf w c hc (owR53D_root w c i) (hnorm i)
  let h : Fin 4 → (Fin 3 → ZMod 5) := fun i => owR53D_lam w c i • owR53D_root w c i
  let α : Fin 4 → (Fin 3 → ZMod 5) →ₗ[ZMod 5] ZMod 5 :=
    fun i => (owR53D_lam w c i)⁻¹ • owR53_alphaY w c (owR53D_root w c i)
  have hP : ∀ i j, α i (h j) = (CartanMatrix.A 4 i j : ZMod 5) := by
    intro i j
    rw [← owR53D_cartan w c hg i j]
    simp only [α, h, LinearMap.smul_apply, smul_eq_mul, owR53_alphaY_apply, Pi.smul_apply,
      Fin.sum_univ_three]
    ring
  have hs : ∀ i v, r i v = v - α i v • h i := by
    intro i v
    simp only [r]
    rw [owR53_rOf_apply]
    unfold owR53_formY
    simp only [α, h, LinearMap.smul_apply, smul_eq_mul, smul_smul]
    have hl := owR53D_c_inv (owR53D_lam w c i) (hne i)
    have : (owR53D_lam w c i)⁻¹ * owR53_alphaY w c (owR53D_root w c i) v * owR53D_lam w c i
        = owR53_alphaY w c (owR53D_root w c i) v := by
      linear_combination (owR53_alphaY w c (owR53D_root w c i) v) * hl
    rw [this]
  have hs_mem : ∀ i, r i ∈ ClassRefl 5 (QuadraticMap.weightedSumSquares (ZMod 5) w) c :=
    fun i => owR53_rOf_mem_class w c hc _ _
  have hgen : closure (Set.range r) = closure (ClassRefl 5 (QuadraticMap.weightedSumSquares (ZMod 5) w) c) := by
    apply le_antisymm
    · rw [Subgroup.closure_le]
      rintro _ ⟨i, rfl⟩
      exact Subgroup.subset_closure (hs_mem i)
    · rw [Subgroup.closure_le]
      intro t ht
      rw [wit_coord_classRefl_iff (by norm_num) (by norm_num) w c hc] at ht
      obtain ⟨a, ha, hta⟩ := ht
      have hra : t = owR53_rOf w c hc a ha := by
        ext v
        rw [hta v, owR53_rOf_apply]
        unfold owR53_formY
        rw [owR53_alphaY_apply]
      have hroot : ∀ i : Fin 4, owR53_rOf w c hc (owR53D_root w c i) (hnorm i) ∈
          closure (Set.range r) := fun i => Subgroup.subset_closure ⟨i, rfl⟩
      have hxmem := owR53_xs_mem w c hc hg (closure (Set.range r)) hroot
      obtain ⟨k, hk | hk⟩ := owR53D_cover w c hg a ha
      · rw [hra, owR53_r_congr w c hc a (owR53D_xs w c k.val) ha
          (owR53D_xs_norm w c hg k.val k.isLt) hk]
        exact hxmem k.val k.isLt
      · have hneg : (∑ j, w j * (-a j * -a j)) = c := by
          simpa only [neg_mul, mul_neg, neg_neg] using ha
        have hneg' : (-a) = owR53D_xs w c k.val := by
          rw [← hk]; rfl
        rw [hra, ← owR53_refl_neg w c hc a ha hneg,
          owR53_r_congr w c hc (-a) (owR53D_xs w c k.val) hneg
            (owR53D_xs_norm w c hg k.val k.isLt) hneg']
        exact hxmem k.val k.isLt
  exact owTA_linWeyl_of_typeA (p := 5) (by norm_num) (by norm_num)
    (QuadraticMap.weightedSumSquares (ZMod 5) w) c (by norm_num : 3 ≤ 4) h α hP r hs hs_mem hgen

end CFSG.StandardType.ZS

end

