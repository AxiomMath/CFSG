module

public import CFSG.LocalAnalysis.StandardType.GGWitOrthCoord
public import CFSG.LocalAnalysis.StandardType.GGCoxeterFaithfulE6Three
public import CFSG.LocalAnalysis.StandardType.GGWitOrthNormal
public import CFSG.LocalAnalysis.StandardType.GGWitOrthTransport

public section

namespace CFSG.StandardType.ZS

open Subgroup

attribute [-instance] Nat.fact_prime_three instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def owR35g_alphaLinP (p : ℕ) (W : Fin 5 → ZMod p) (a : Fin 5 → ZMod p) :
    (Fin 5 → ZMod p) →ₗ[ZMod p] ZMod p where
  toFun v := 2 * ∑ k, W k * (v k * a k)
  map_add' x y := by
    simp only [Pi.add_apply]
    rw [show (∑ k, W k * ((x k + y k) * a k))
          = (∑ k, W k * (x k * a k)) + (∑ k, W k * (y k * a k)) by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun k _ => by ring]
    ring
  map_smul' r x := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [show (∑ k, W k * ((r * x k) * a k)) = r * ∑ k, W k * (x k * a k) by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun k _ => by ring]
    ring

@[expose] def owR35g_formP (p : ℕ) (W : Fin 5 → ZMod p) (b v : Fin 5 → ZMod p) : Fin 5 → ZMod p :=
  v - (owR35g_alphaLinP p W b v) • b

theorem owR35g_alpha_self {p : ℕ} (W : Fin 5 → ZMod p) (y : Fin 5 → ZMod p)
    (hy : (∑ k, W k * (y k * y k)) = 1) :
    owR35g_alphaLinP p W y y = 2 := by
  show 2 * ∑ k, W k * (y k * y k) = 2
  rw [hy, mul_one]

theorem owR35g_formP_norm {p : ℕ} (W : Fin 5 → ZMod p) (y z : Fin 5 → ZMod p)
    (hy : (∑ k, W k * (y k * y k)) = 1)
    (hz : (∑ k, W k * (z k * z k)) = 1) :
    ∑ k, W k * (owR35g_formP p W y z k * owR35g_formP p W y z k) = 1 := by
  set A : ZMod p := owR35g_alphaLinP p W y z with hA
  have hAval : A = 2 * ∑ k, W k * (z k * y k) := by
    rw [hA]; rfl
  have hform : ∀ k, owR35g_formP p W y z k = z k - A * y k := by
    intro k
    simp only [owR35g_formP, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hA]
  calc ∑ k, W k * (owR35g_formP p W y z k * owR35g_formP p W y z k)
      = ∑ k, W k * ((z k - A * y k) * (z k - A * y k)) := by
        apply Finset.sum_congr rfl; intro k _; rw [hform k]
    _ = ∑ k, (W k * (z k * z k) - (2 * A) * (W k * (z k * y k))
          + (A * A) * (W k * (y k * y k))) := by
        apply Finset.sum_congr rfl; intro k _; ring
    _ = (∑ k, W k * (z k * z k)) - (2 * A) * (∑ k, W k * (z k * y k))
          + (A * A) * (∑ k, W k * (y k * y k)) := by
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.mul_sum, Finset.mul_sum]
    _ = 1 := by
        rw [hz, hy, hAval]
        ring

theorem owR35g_bilin {p : ℕ} (W : Fin 5 → ZMod p) (b : Fin 5 → ZMod p) (v x : Fin 5 → ZMod p) :
    ∑ k, W k * (owR35g_formP p W b v k * x k)
      = ∑ k, W k * (v k * owR35g_formP p W b x k) := by
  simp only [owR35g_formP, owR35g_alphaLinP, LinearMap.coe_mk, AddHom.coe_mk, Pi.sub_apply,
    Pi.smul_apply, smul_eq_mul]
  simp only [Fin.sum_univ_five]
  ring

theorem owR35g_alpha_conj {p : ℕ} (W : Fin 5 → ZMod p) (b : Fin 5 → ZMod p) (v x : Fin 5 → ZMod p) :
    owR35g_alphaLinP p W (owR35g_formP p W b x) v
      = owR35g_alphaLinP p W x (owR35g_formP p W b v) := by
  simp only [owR35g_alphaLinP, LinearMap.coe_mk, AddHom.coe_mk]
  rw [owR35g_bilin W b v x]

theorem owR35g_r_congr {p : ℕ} (W : Fin 5 → ZMod p) (x y : Fin 5 → ZMod p)
    (hx : (∑ k, W k * (x k * x k)) = 1) (hy : (∑ k, W k * (y k * y k)) = 1) (h : x = y) :
    Module.reflection (f := owR35g_alphaLinP p W x) (x := x) (owR35g_alpha_self W x hx)
      = Module.reflection (f := owR35g_alphaLinP p W y) (x := y) (owR35g_alpha_self W y hy) := by
  subst h
  rfl

theorem owR35g_reflP_conj {p : ℕ} (W : Fin 5 → ZMod p) (b x : Fin 5 → ZMod p)
    (hb : (∑ k, W k * (b k * b k)) = 1) (hx : (∑ k, W k * (x k * x k)) = 1) :
    Module.reflection (f := owR35g_alphaLinP p W b) (x := b) (owR35g_alpha_self W b hb)
      * Module.reflection (f := owR35g_alphaLinP p W x) (x := x) (owR35g_alpha_self W x hx)
      * (Module.reflection (f := owR35g_alphaLinP p W b) (x := b) (owR35g_alpha_self W b hb))⁻¹
    = Module.reflection (f := owR35g_alphaLinP p W (owR35g_formP p W b x))
        (x := owR35g_formP p W b x)
        (owR35g_alpha_self W (owR35g_formP p W b x) (owR35g_formP_norm W b x hb hx)) := by
  ext v
  rw [Module.reflection_apply (x := owR35g_formP p W b x)
    (f := owR35g_alphaLinP p W (owR35g_formP p W b x))
    (h := owR35g_alpha_self W (owR35g_formP p W b x) (owR35g_formP_norm W b x hb hx)) (y := v)]
  simp only [LinearEquiv.mul_apply, Module.reflection_inv]
  rw [owR35g_alpha_conj W b v x]
  have h1 : Module.reflection (f := owR35g_alphaLinP p W x) (x := x) (owR35g_alpha_self W x hx)
        (Module.reflection (f := owR35g_alphaLinP p W b) (x := b) (owR35g_alpha_self W b hb) v)
      = Module.reflection (f := owR35g_alphaLinP p W b) (x := b) (owR35g_alpha_self W b hb) v
        - owR35g_alphaLinP p W x
            (Module.reflection (f := owR35g_alphaLinP p W b) (x := b) (owR35g_alpha_self W b hb) v)
          • x :=
    Module.reflection_apply (x := x) (f := owR35g_alphaLinP p W x)
      (h := owR35g_alpha_self W x hx)
      (y := Module.reflection (f := owR35g_alphaLinP p W b) (x := b) (owR35g_alpha_self W b hb) v)
  have h2 : Module.reflection (f := owR35g_alphaLinP p W b) (x := b) (owR35g_alpha_self W b hb)
        (Module.reflection (f := owR35g_alphaLinP p W b) (x := b) (owR35g_alpha_self W b hb) v) = v :=
    Module.involutive_reflection (owR35g_alpha_self W b hb) v
  rw [h1, map_sub, map_smul, h2]
  simp only [owR35g_formP, Module.reflection_apply]

theorem owR35g_e6_bridge {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p = 3) (W : Fin 5 → ZMod p)
    (roots : Fin 6 → Fin 5 → ZMod p) (ord : Fin 72 → Fin 5 → ZMod p) (par : Fin 72 → Fin 72)
    (gen : Fin 72 → Fin 6)
    (hnorm : ∀ i, ∑ k, W k * (roots i k * roots i k) = 1)
    (hP : ∀ i j, owR35g_alphaLinP p W (roots i) (roots j) = (CartanMatrix.E 6 i j : ZMod p))
    (hfirst : ∀ i : Fin 6, ord (Fin.castLE (by norm_num) i) = roots i)
    (hstep : ∀ j : Fin 72, 6 ≤ j.val → ord j = owR35g_formP p W (roots (gen j)) (ord (par j)))
    (hlt : ∀ j : Fin 72, 6 ≤ j.val → (par j).val < j.val)
    (hcov : ∀ a : Fin 5 → ZMod p, (∑ k, W k * (a k * a k)) = 1 → ∃ j, a = ord j) :
    LinWeyl p (closure (ClassRefl p (QuadraticMap.weightedSumSquares (ZMod p) W) 1)) := by
  classical
  have hone : (1 : ZMod p) ≠ 0 := by
    intro h
    exact hp.not_dvd_one ((ZMod.natCast_eq_zero_iff 1 p).mp (by simpa using h))
  let s : Fin 6 → (Fin 5 → ZMod p) ≃ₗ[ZMod p] (Fin 5 → ZMod p) :=
    fun i => Module.reflection (f := owR35g_alphaLinP p W (roots i)) (x := roots i)
      (owR35g_alpha_self W (roots i) (hnorm i))
  have hs : ∀ i v, s i v = v - owR35g_alphaLinP p W (roots i) v • roots i := by
    intro i v
    exact Module.reflection_apply (x := roots i) (f := owR35g_alphaLinP p W (roots i))
      (h := owR35g_alpha_self W (roots i) (hnorm i)) (y := v)
  have hs_mem : ∀ i, s i ∈ ClassRefl p (QuadraticMap.weightedSumSquares (ZMod p) W) 1 := by
    intro i
    rw [wit_coord_classRefl_iff hp hp2 W 1 hone]
    refine ⟨roots i, hnorm i, fun v => ?_⟩
    rw [hs i v]
    simp only [owR35g_alphaLinP, LinearMap.coe_mk, AddHom.coe_mk, ZMod.inv_one, mul_one]
  let H : Subgroup ((Fin 5 → ZMod p) ≃ₗ[ZMod p] (Fin 5 → ZMod p)) := closure (Set.range s)
  have hsH : ∀ i, s i ∈ H := fun i => Subgroup.subset_closure ⟨i, rfl⟩
  have hord : ∀ n : ℕ, ∀ j : Fin 72, j.val = n →
      ∃ hn : (∑ k, W k * (ord j k * ord j k)) = 1,
        Module.reflection (f := owR35g_alphaLinP p W (ord j)) (x := ord j)
          (owR35g_alpha_self W (ord j) hn) ∈ H := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro j hjn
      by_cases hj6 : j.val < 6
      · have hjroot : ord j = roots ⟨j.val, hj6⟩ := by
          rw [← hfirst ⟨j.val, hj6⟩]
          rfl
        have hn : (∑ k, W k * (ord j k * ord j k)) = 1 := by
          rw [hjroot]; exact hnorm _
        refine ⟨hn, ?_⟩
        rw [owR35g_r_congr W (ord j) (roots ⟨j.val, hj6⟩) hn (hnorm _) hjroot]
        exact hsH _
      · have hj6' : 6 ≤ j.val := not_lt.mp hj6
        have hpar := hlt j hj6'
        obtain ⟨hnp, hmp⟩ := ih (par j).val (by omega) (par j) rfl
        have hbn := hnorm (gen j)
        have hn : (∑ k, W k * (ord j k * ord j k)) = 1 := by
          rw [hstep j hj6']
          exact owR35g_formP_norm W (roots (gen j)) (ord (par j)) hbn hnp
        refine ⟨hn, ?_⟩
        rw [owR35g_r_congr W (ord j) (owR35g_formP p W (roots (gen j)) (ord (par j))) hn
            (owR35g_formP_norm W _ _ hbn hnp) (hstep j hj6'),
          ← owR35g_reflP_conj W (roots (gen j)) (ord (par j)) hbn hnp]
        exact H.mul_mem (H.mul_mem (hsH _) hmp) (H.inv_mem (hsH _))
  have hgen : closure (Set.range s) =
      closure (ClassRefl p (QuadraticMap.weightedSumSquares (ZMod p) W) 1) := by
    apply le_antisymm
    · rw [Subgroup.closure_le]
      rintro _ ⟨i, rfl⟩
      exact Subgroup.subset_closure (hs_mem i)
    · rw [Subgroup.closure_le]
      intro t ht
      rw [wit_coord_classRefl_iff hp hp2 W 1 hone] at ht
      obtain ⟨a, ha, hta⟩ := ht
      have hra : t = Module.reflection (f := owR35g_alphaLinP p W a) (x := a)
          (owR35g_alpha_self W a ha) := by
        ext v
        rw [hta v, Module.reflection_apply]
        simp only [owR35g_alphaLinP, LinearMap.coe_mk, AddHom.coe_mk, ZMod.inv_one, mul_one]
      obtain ⟨j, hj⟩ := hcov a ha
      obtain ⟨hn, hm⟩ := hord j.val j rfl
      rw [hra, owR35g_r_congr W a (ord j) ha hn hj]
      exact hm
  subst hp3
  obtain ⟨f, hf⟩ := ggCoxeterIso_of_E6_three_reindex (Equiv.refl (Fin 6))
    (by ext i j; simp [CoxeterMatrix.reindex_apply]) ggIntCartan_E₆ roots
    (fun i => owR35g_alphaLinP 3 W (roots i)) hP s hs
  refine ⟨Fin 6, CoxeterMatrix.E₆, ?_, ?_⟩
  · exact Or.inr (Or.inl ⟨Equiv.refl (Fin 6), by ext i j; simp [CoxeterMatrix.reindex_apply]⟩)
  · refine ⟨f.trans (MulEquiv.subgroupCongr hgen), ?_⟩
    intro i
    rw [MulEquiv.trans_apply, MulEquiv.subgroupCongr_apply, hf i]
    exact (hs_mem i).1

theorem owR35g_e6_canon {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p = 3) {U : Type}
    [AddCommGroup U] [Module (ZMod p) U] (Q : QuadraticForm (ZMod p) U)
    (e : U ≃ₗ[ZMod p] (Fin 5 → ZMod p)) (W : Fin 5 → ZMod p)
    (he : ∀ v, Q v = ∑ i, W i * (e v i) ^ 2)
    (roots : Fin 6 → Fin 5 → ZMod p) (ord : Fin 72 → Fin 5 → ZMod p) (par : Fin 72 → Fin 72)
    (gen : Fin 72 → Fin 6)
    (hnorm : ∀ i, ∑ k, W k * (roots i k * roots i k) = 1)
    (hP : ∀ i j, owR35g_alphaLinP p W (roots i) (roots j) = (CartanMatrix.E 6 i j : ZMod p))
    (hfirst : ∀ i : Fin 6, ord (Fin.castLE (by norm_num) i) = roots i)
    (hstep : ∀ j : Fin 72, 6 ≤ j.val → ord j = owR35g_formP p W (roots (gen j)) (ord (par j)))
    (hlt : ∀ j : Fin 72, 6 ≤ j.val → (par j).val < j.val)
    (hcov : ∀ a : Fin 5 → ZMod p, (∑ k, W k * (a k * a k)) = 1 → ∃ j, a = ord j) :
    LinWeyl p (closure (ClassRefl p Q 1)) := by
  have he' : ∀ v : U, QuadraticMap.weightedSumSquares (ZMod p) W (e v) = Q v := by
    intro v
    simpa only [QuadraticMap.weightedSumSquares_apply, smul_eq_mul, pow_two] using (he v).symm
  obtain ⟨φ, hφ⟩ := wit_classRefl_transport hp hp2 Q (QuadraticMap.weightedSumSquares (ZMod p) W)
    e he' 1 (A := closure (ClassRefl p Q 1))
    (A' := closure (ClassRefl p (QuadraticMap.weightedSumSquares (ZMod p) W) 1)) rfl rfl
  exact wit_linWeyl_transport e φ hφ
    (owR35g_e6_bridge hp hp2 hp3 W roots ord par gen hnorm hP hfirst hstep hlt hcov)

end CFSG.StandardType.ZS

end
