module

public import CFSG.LocalAnalysis.StandardType.GGOmegaMinusRootGenDefs
public import CFSG.ClassicalGroups.Orthogonal.StatedOmegaElementary
public import CFSG.LieType.Universal.Spin.Generation.Eichler
public import CFSG.ClassicalGroups.Orthogonal.Omega7ThreeLocalRoot
public import CFSG.ClassicalGroups.Orthogonal.RootGroupFixedCard

public section

namespace CFSG.StandardType

open CFSG.Open CFSG.ClassicalGroups.Orthogonal CFSG.SeitzReduction.OmegaPilot
  CFSG.SeitzReduction.SymplecticPilot QuadraticMap
open scoped Matrix

section Generic

variable {K : Type} [Field K] {ι : Type} [DecidableEq ι] {m : ℕ}
  {Q : QuadraticForm K (ι → K)} {a b : Fin m → ι}

private def coordFrameGen (a b : Fin m → ι) (k : Fin m) (s : Bool) : ι → K :=
  cond s (Pi.single (a k) 1) (Pi.single (b k) 1)

private theorem polar_coordFrameGen (h : IsHypFrame Q a b) (k : Fin m) (s : Bool) (v : ι → K) :
    polar Q (coordFrameGen a b k s) v = cond s (v (b k)) (v (a k)) := by
  cases s
  · exact (h.hyp k).polar_right v
  · exact (h.hyp k).polar_left v

private theorem coordFrameGen_apply_left (h : IsHypFrame Q a b) (k l : Fin m) (s : Bool) :
    coordFrameGen a b k s (a l) = if s ∧ k = l then (1 : K) else 0 := by
  cases s
  · simp [coordFrameGen, Ne.symm (h.left_ne_right l k)]
  · by_cases hkl : k = l
    · subst hkl
      simp [coordFrameGen]
    · have hne : a l ≠ a k := fun e => hkl (h.left_injective e).symm
      simp [coordFrameGen, hne, hkl]

private theorem coordFrameGen_apply_right (h : IsHypFrame Q a b) (k l : Fin m) (s : Bool) :
    coordFrameGen a b k s (b l) = if s = false ∧ k = l then (1 : K) else 0 := by
  cases s
  · by_cases hkl : k = l
    · subst hkl
      simp [coordFrameGen]
    · have hne : b l ≠ b k := fun e => hkl (h.right_injective e).symm
      simp [coordFrameGen, hne, hkl]
  · simp [coordFrameGen, h.left_ne_right k l]

private theorem apply_eq_zero_of_polarGen (h : IsHypFrame Q a b) {v : ι → K}
    (hv : ∀ k r, polar Q v (coordFrameGen a b k r) = 0) (k : Fin m) :
    v (a k) = 0 ∧ v (b k) = 0 := by
  have h1 := hv k false
  have h2 := hv k true
  rw [polar_comm, polar_coordFrameGen h] at h1 h2
  exact ⟨h1, h2⟩

private noncomputable def toHypFrameGen (h : IsHypFrame Q a b) (z : ι → K)
    (hz : IsUnit (Q z)) (hza : ∀ k, z (a k) = 0) (hzb : ∀ k, z (b k) = 0) :
    CFSG.LieType.Universal.Spin.HypFrame Q m where
  vec := coordFrameGen a b
  map_vec k s := by
    cases s
    · exact (h.hyp k).map_right
    · exact (h.hyp k).map_left
  polar_vec_of_ne i j hij s t := by
    rw [polar_coordFrameGen h]
    cases s
    · simp [coordFrameGen_apply_left h, Ne.symm hij]
    · simp [coordFrameGen_apply_right h, Ne.symm hij]
  polar_vec_not i s := by
    rw [polar_coordFrameGen h]
    cases s
    · simp [coordFrameGen_apply_left h]
    · simp [coordFrameGen_apply_right h]
  exists_aux i j := ⟨z, hz, fun s => by
    rw [polar_coordFrameGen h, polar_coordFrameGen h]
    cases s <;> simp [hza, hzb]⟩

private theorem toHypFrameGen_vec (h : IsHypFrame Q a b) (z : ι → K)
    (hz : IsUnit (Q z)) (hza : ∀ k, z (a k) = 0) (hzb : ∀ k, z (b k) = 0) :
    (toHypFrameGen h z hz hza hzb).vec = coordFrameGen a b := rfl

private noncomputable def frameRootGen (Q : QuadraticForm K (ι → K)) (a b : Fin m → ι)
    (p q : Fin m) (c : K) : (ι → K) ≃ₗ[K] (ι → K) :=
  eichler Q (Pi.single (a p) 1) (c • Pi.single (b q) 1)

private theorem pairDisjointGen (h : IsHypFrame Q a b) {p p' : Fin m} (hpp : p ≠ p') :
    PairDisjoint (a p) (b p) (a p') (b p') :=
  ⟨fun e => hpp (h.left_injective e).symm, h.left_ne_right p' p, (h.left_ne_right p p').symm,
    fun e => hpp (h.right_injective e).symm⟩

private theorem frameRootGen_apply (h : IsHypFrame Q a b) {p q : Fin m} (hpq : p ≠ q) (c : K)
    (x : ι → K) :
    frameRootGen Q a b p q c x =
      x + (c * x (b p)) • Pi.single (b q) 1 - (c * x (a q)) • Pi.single (a p) 1 := by
  have hpol : polar Q (Pi.single (a p) 1) (c • Pi.single (b q) 1) = 0 := by
    rw [(h.hyp p).polar_left, Pi.smul_apply,
      Pi.single_eq_of_ne (fun e => hpq (h.right_injective e)), smul_zero]
  rw [frameRootGen, eichler_apply (h.hyp p).map_left hpol, polar_comm, (h.hyp p).polar_left,
    polar_smul_right, polar_comm, (h.hyp q).polar_right, QuadraticMap.map_smul,
    (h.hyp q).map_right, smul_zero, zero_mul, add_zero, smul_smul, smul_eq_mul, mul_comm (x (b p))]

private theorem frameRootGen_apply_coord (h : IsHypFrame Q a b) {p q : Fin m} (hpq : p ≠ q)
    (c : K) (x : ι → K) (j : ι) :
    frameRootGen Q a b p q c x j =
      if j = a p then x (a p) - c * x (a q)
        else if j = b q then x (b q) + c * x (b p) else x j := by
  rw [frameRootGen_apply h hpq]
  have hne : a p ≠ b q := h.left_ne_right p q
  by_cases h1 : j = a p
  · subst h1
    simp [hne]
  · by_cases h2 : j = b q
    · subst h2
      simp [Ne.symm hne]
    · simp [h1, h2]

private noncomputable def pairSwapGen (Q : QuadraticForm K (ι → K)) (x y x' y' : ι) :
    (ι → K) ≃ₗ[K] (ι → K) :=
  eichler Q (Pi.single x 1 + Pi.single x' 1) (Pi.single y 1 + Pi.single y' 1)

private theorem pairSwapGen_comm (Q : QuadraticForm K (ι → K)) (x y x' y' : ι) :
    pairSwapGen Q x y x' y' = pairSwapGen Q x' y' x y := by
  unfold pairSwapGen
  congr 1 <;> exact add_comm _ _

private theorem pairSwapGen_hyp [CharP K 2] {x y x' y' : ι} (h : IsHypCoord Q x y)
    (h' : IsHypCoord Q x' y') (hd : PairDisjoint x y x' y') :
    Q (Pi.single x 1 + Pi.single x' 1) = 0 ∧
      polar Q (Pi.single x 1 + Pi.single x' 1) (Pi.single y 1 + Pi.single y' 1) = 0 := by
  have htwo : (2 : K) = 0 := CharTwo.two_eq_zero
  refine ⟨?_, ?_⟩
  · rw [QuadraticMap.map_add Q, h.map_left, h'.map_left, h.polar_left,
      Pi.single_eq_of_ne hd.left_ne_right.symm]
    simp
  · rw [polar_add_left, polar_add_right, polar_add_right, h.polar_left, h.polar_left,
      h'.polar_left, h'.polar_left, Pi.single_eq_same, Pi.single_eq_same,
      Pi.single_eq_of_ne hd.right_ne_right.symm, Pi.single_eq_of_ne hd.right_ne_right]
    linear_combination htwo

private theorem pairSwapGen_hyp_right {x y x' y' : ι} (h : IsHypCoord Q x y)
    (h' : IsHypCoord Q x' y') (hd : PairDisjoint x y x' y') :
    Q (Pi.single y 1 + Pi.single y' 1) = 0 := by
  rw [QuadraticMap.map_add Q, h.map_right, h'.map_right, h.polar_right,
    Pi.single_eq_of_ne hd.right_ne_left.symm]
  simp

private theorem pairSwapGen_apply_left [CharP K 2] {x y x' y' : ι} (h : IsHypCoord Q x y)
    (h' : IsHypCoord Q x' y') (hd : PairDisjoint x y x' y') :
    pairSwapGen Q x y x' y' (Pi.single x 1) = Pi.single x' 1 ∧
      pairSwapGen Q x y x' y' (Pi.single y 1) = Pi.single y' 1 := by
  obtain ⟨hu, hw⟩ := pairSwapGen_hyp h h' hd
  have hQw := pairSwapGen_hyp_right h h' hd
  have htwo : (2 : K) = 0 := CharTwo.two_eq_zero
  refine ⟨?_, ?_⟩
  · have hub : (Pi.single x (1 : K) + Pi.single x' 1 : ι → K) y = 0 := by
      rw [Pi.add_apply, Pi.single_eq_of_ne h.ne.symm, Pi.single_eq_of_ne hd.left_ne_right.symm,
        add_zero]
    have hwb : (Pi.single y (1 : K) + Pi.single y' 1 : ι → K) y = 1 := by
      rw [Pi.add_apply, Pi.single_eq_same, Pi.single_eq_of_ne hd.right_ne_right.symm, add_zero]
    rw [pairSwapGen, eichler_apply hu hw, h.polar_left, h.polar_left, hub, hwb, hQw]
    ext i
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    linear_combination (-(Pi.single x' (1 : K) : ι → K) i) * htwo
  · have hua : (Pi.single x (1 : K) + Pi.single x' 1 : ι → K) x = 1 := by
      rw [Pi.add_apply, Pi.single_eq_same, Pi.single_eq_of_ne hd.left_ne_left.symm, add_zero]
    have hwa : (Pi.single y (1 : K) + Pi.single y' 1 : ι → K) x = 0 := by
      rw [Pi.add_apply, Pi.single_eq_of_ne h.ne, Pi.single_eq_of_ne hd.right_ne_left.symm,
        add_zero]
    rw [pairSwapGen, eichler_apply hu hw, h.polar_right, h.polar_right, hua, hwa, hQw]
    ext i
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    linear_combination ((Pi.single y (1 : K) : ι → K) i) * htwo

private theorem pairSwapGen_apply_coord [CharP K 2] (h : IsHypFrame Q a b) {p q : Fin m}
    (hpq : p ≠ q) (x : ι → K) (j : ι) :
    pairSwapGen Q (a p) (b p) (a q) (b q) x j =
      if j = a p then x (a q) else if j = a q then x (a p) else if j = b p then x (b q)
        else if j = b q then x (b p) else x j := by
  have hd := pairDisjointGen h hpq
  obtain ⟨hu, hw⟩ := pairSwapGen_hyp (h.hyp p) (h.hyp q) hd
  have hQw := pairSwapGen_hyp_right (h.hyp p) (h.hyp q) hd
  have htwo : (2 : K) = 0 := CharTwo.two_eq_zero
  rw [pairSwapGen, eichler_apply hu hw, hQw, zero_mul, add_zero, polar_comm, polar_add_left,
    (h.hyp p).polar_left, (h.hyp q).polar_left, polar_comm, polar_add_left, (h.hyp p).polar_right,
    (h.hyp q).polar_right]
  have e1 : a p ≠ a q := fun e => hpq (h.left_injective e)
  have e2 : b p ≠ b q := fun e => hpq (h.right_injective e)
  have e3 : ∀ k l, a k ≠ b l := h.left_ne_right
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  by_cases j1 : j = a p
  · subst j1
    simp [e1, e3]
    linear_combination (-x (a q)) * htwo
  by_cases j2 : j = a q
  · subst j2
    simp [Ne.symm e1, e3]
    linear_combination (-x (a p)) * htwo
  by_cases j3 : j = b p
  · subst j3
    simp [e2, fun k => Ne.symm (e3 k p)]
    linear_combination x (b p) * htwo
  by_cases j4 : j = b q
  · subst j4
    simp [Ne.symm e2, fun k => Ne.symm (e3 k q)]
    linear_combination x (b q) * htwo
  · simp [j1, j2, j3, j4]

private theorem pairSwapGen_eq_frameRootGen [CharP K 2] (h : IsHypFrame Q a b) {p q : Fin m}
    (hpq : p ≠ q) :
    pairSwapGen Q (a p) (b p) (a q) (b q) =
      frameRootGen Q a b q p 1 * frameRootGen Q a b p q 1 * frameRootGen Q a b q p 1 := by
  have htwo : (2 : K) = 0 := CharTwo.two_eq_zero
  have e1 : a p ≠ a q := fun e => hpq (h.left_injective e)
  have e2 : b p ≠ b q := fun e => hpq (h.right_injective e)
  have e3 : ∀ k l, a k ≠ b l := h.left_ne_right
  refine LinearEquiv.ext fun x => funext fun j => ?_
  simp only [LinearEquiv.mul_apply, frameRootGen_apply_coord h hpq,
    frameRootGen_apply_coord h (Ne.symm hpq), pairSwapGen_apply_coord h hpq, one_mul]
  have e4 : ∀ k l, b l ≠ a k := fun k l => Ne.symm (e3 k l)
  simp only [e1, Ne.symm e1, e2, Ne.symm e2, e3, e4, ite_false, ite_true]
  by_cases j1 : j = a p
  · subst j1
    simp only [e1, e3, ite_true, ite_false]
    linear_combination (x (a q) - x (a p)) * htwo
  by_cases j2 : j = a q
  · subst j2
    simp only [Ne.symm e1, e3, ite_true, ite_false]
    linear_combination (2 * x (a p) - x (a q)) * htwo
  by_cases j3 : j = b p
  · subst j3
    simp only [e2, e4, ite_true, ite_false]
    linear_combination (-x (b p) - x (b q)) * htwo
  by_cases j4 : j = b q
  · subst j4
    simp only [Ne.symm e2, e4, ite_true, ite_false]
    linear_combination (-x (b q)) * htwo
  · simp only [j1, j2, j3, j4, ite_false]

private theorem pairSwapGen_coordFrame [CharP K 2] (h : IsHypFrame Q a b) {p p' : Fin m}
    (hpp : p ≠ p') (k : Fin m) (r : Bool) :
    pairSwapGen Q (a p) (b p) (a p') (b p') (coordFrameGen a b k r) =
      coordFrameGen a b (Equiv.swap p p' k) r := by
  have hd := pairDisjointGen h hpp
  by_cases hkp : k = p
  · subst hkp
    rw [Equiv.swap_apply_left]
    obtain ⟨h1, h2⟩ := pairSwapGen_apply_left (h.hyp k) (h.hyp p') hd
    cases r
    · exact h2
    · exact h1
  by_cases hkp' : k = p'
  · subst hkp'
    rw [Equiv.swap_apply_right, pairSwapGen_comm]
    obtain ⟨h1, h2⟩ := pairSwapGen_apply_left (h.hyp k) (h.hyp p) hd.symm
    cases r
    · exact h2
    · exact h1
  rw [Equiv.swap_apply_of_ne_of_ne hkp hkp']
  have h1 : a k ≠ a p := fun e => hkp (h.left_injective e)
  have h2 : a k ≠ a p' := fun e => hkp' (h.left_injective e)
  have h3 : b k ≠ b p := fun e => hkp (h.right_injective e)
  have h4 : b k ≠ b p' := fun e => hkp' (h.right_injective e)
  have h5 : ∀ l, a k ≠ b l := fun l => h.left_ne_right k l
  have h6 : ∀ l, b k ≠ a l := fun l e => h.left_ne_right l k e.symm
  refine eichler_apply_of_polar_eq_zero ?_ ?_
  · rw [polar_add_right, polar_coordFrameGen h, polar_coordFrameGen h]
    cases r
    · simp [Pi.single_apply, h1, h2]
    · simp [Pi.single_apply, h6]
  · rw [polar_add_right, polar_coordFrameGen h, polar_coordFrameGen h]
    cases r
    · simp [Pi.single_apply, h5]
    · simp [Pi.single_apply, h3, h4]

private theorem pairSwapGen_apply_of_vanish (h : IsHypFrame Q a b) {p p' : Fin m} {v : ι → K}
    (hap : v (a p) = 0) (hbp : v (b p) = 0) (hap' : v (a p') = 0) (hbp' : v (b p') = 0) :
    pairSwapGen Q (a p) (b p) (a p') (b p') v = v := by
  refine eichler_apply_of_polar_eq_zero ?_ ?_
  · rw [polar_comm, polar_add_left, (h.hyp p).polar_left, (h.hyp p').polar_left, hbp, hbp',
      add_zero]
  · rw [polar_comm, polar_add_left, (h.hyp p).polar_right, (h.hyp p').polar_right, hap, hap',
      add_zero]

private theorem coordFrameGen_vanish (h : IsHypFrame Q a b) {k l : Fin m} (hkl : k ≠ l)
    (r : Bool) : coordFrameGen a b k r (a l) = (0 : K) ∧ coordFrameGen a b k r (b l) = (0 : K) := by
  rw [coordFrameGen_apply_left h, coordFrameGen_apply_right h]
  simp [hkl]

private theorem eichler_right_leftGen [CharP K 2] (h : IsHypFrame Q a b) {i j : Fin m}
    (hij : i ≠ j) (c : K) :
    eichler Q (Pi.single (b j) 1) (c • Pi.single (a i) 1) = frameRootGen Q a b i j (-c) := by
  have hpol : polar Q (Pi.single (b j) 1) (c • Pi.single (a i) 1) = 0 := by
    rw [(h.hyp j).polar_right, Pi.smul_apply,
      Pi.single_eq_of_ne (fun e => hij (h.left_injective e).symm), smul_zero]
  have hQ : Q (c • Pi.single (a i) 1) = 0 := by
    rw [QuadraticMap.map_smul, (h.hyp i).map_left, smul_zero]
  have hanti := CFSG.ClassicalGroups.Orthogonal.Omega7ThreeLocal.eichler_eq_eichler_neg_of_singular
    (K := K) (V := ι → K) (Q := Q) (u := Pi.single (b j) 1)
    (w := c • Pi.single (a i) 1) (h.hyp j).map_right hQ hpol
  rw [hanti, eichler_smul_left, frameRootGen, smul_neg, ← neg_smul]

private theorem eichler_flip_applyGen [CharP K 2] (h : IsHypFrame Q a b) {z : ι → K}
    (hz : Q z = 1) (hza : ∀ k, z (a k) = 0) (hzb : ∀ k, z (b k) = 0) (i : Fin m) :
    Q (coordFrameGen a b i true + coordFrameGen a b i false + z) = 0 ∧
      polar Q (coordFrameGen a b i true + coordFrameGen a b i false + z) z = 0 ∧
      (∀ r, eichler Q (coordFrameGen a b i true + coordFrameGen a b i false + z) z
        (coordFrameGen a b i r) = coordFrameGen a b i (!r)) ∧
      ∀ j, j ≠ i → ∀ r, eichler Q (coordFrameGen a b i true + coordFrameGen a b i false + z) z
        (coordFrameGen a b j r) = coordFrameGen a b j r := by
  have htwo : (2 : K) = 0 := CharTwo.two_eq_zero
  have hneg : ∀ v : ι → K, -v = v := fun v => by
    funext j
    simp [CharTwo.neg_eq]
  set e := coordFrameGen (K := K) a b i true with he
  set f := coordFrameGen (K := K) a b i false with hf
  have hef : polar Q e f = 1 := by
    rw [he, hf, polar_coordFrameGen h]
    simp [coordFrameGen]
  have hez : polar Q e z = 0 := by rw [he, polar_coordFrameGen h]; exact hzb i
  have hfz : polar Q f z = 0 := by rw [hf, polar_coordFrameGen h]; exact hza i
  have hQe : Q e = 0 := (h.hyp i).map_left
  have hQf : Q f = 0 := (h.hyp i).map_right
  have hzz : polar Q z z = 0 := by rw [polar_self, hz, two_smul, CharTwo.add_self_eq_zero]
  have hu : Q (e + f + z) = 0 := by
    rw [QuadraticMap.map_add Q, QuadraticMap.map_add Q, hQe, hQf, hz, polar_add_left, hef, hez, hfz]
    linear_combination htwo
  have huz : polar Q (e + f + z) z = 0 := by
    rw [polar_add_left, polar_add_left, hez, hfz, hzz, add_zero, add_zero]
  refine ⟨hu, huz, fun r => ?_, fun j hji r => ?_⟩
  · rw [eichler_apply hu huz, hz]
    cases r
    · have h1 : polar Q f (e + f + z) = 1 := by
        rw [polar_add_right, polar_add_right, polar_comm, hef, polar_self, hQf, smul_zero, hfz,
          add_zero, add_zero]
      change f + polar Q f (e + f + z) • z - (polar Q f z + 1 * polar Q f (e + f + z)) •
        (e + f + z) = e
      rw [h1, hfz, one_smul, zero_add, one_mul, one_smul]
      rw [show f + z - (e + f + z) = -e by abel, hneg]
    · have h1 : polar Q e (e + f + z) = 1 := by
        rw [polar_add_right, polar_add_right, hef, polar_self, hQe, smul_zero, hez, zero_add,
          add_zero]
      change e + polar Q e (e + f + z) • z - (polar Q e z + 1 * polar Q e (e + f + z)) •
        (e + f + z) = f
      rw [h1, hez, one_smul, zero_add, one_mul, one_smul]
      rw [show e + z - (e + f + z) = -f by abel, hneg]
  · have hv := coordFrameGen_vanish h (k := i) (l := j) (Ne.symm hji)
    refine eichler_apply_of_polar_eq_zero ?_ ?_
    · rw [polar_coordFrameGen h]
      cases r
      · simp only [Bool.cond_false, Pi.add_apply, he, hf, (hv true).1, (hv false).1, hza j,
          add_zero]
      · simp only [Bool.cond_true, Pi.add_apply, he, hf, (hv true).2, (hv false).2, hzb j,
          add_zero]
    · rw [polar_coordFrameGen h]
      cases r
      · exact hza j
      · exact hzb j

private theorem pairSwapGen_conj_frameRootGen [CharP K 2] (h : IsHypFrame Q a b) {p p' : Fin m}
    (hpp : p ≠ p') (r s : Fin m) (c : K) :
    pairSwapGen Q (a p) (b p) (a p') (b p') * frameRootGen Q a b r s c *
        (pairSwapGen Q (a p) (b p) (a p') (b p'))⁻¹ =
      frameRootGen Q a b (Equiv.swap p p' r) (Equiv.swap p p' s) c := by
  rw [frameRootGen, eichler_conj (show pairSwapGen Q (a p) (b p) (a p') (b p') ∈
      TauCeti.QuadraticMap.orthogonalGroup Q from eichler_mem_orthogonalGroup Q _ _), map_smul,
    show (Pi.single (a r) 1 : ι → K) = coordFrameGen a b r true from rfl,
    show (Pi.single (b s) 1 : ι → K) = coordFrameGen a b s false from rfl,
    pairSwapGen_coordFrame h hpp, pairSwapGen_coordFrame h hpp]
  rfl

private theorem elementaryGroupGen_le_of_rootElt [CharP K 2] (h : IsHypFrame Q a b) {z : ι → K}
    (hz : Q z = 1) (hza : ∀ k, z (a k) = 0) (hzb : ∀ k, z (b k) = 0)
    (hrest : ∀ v : ι → K, (∀ k, v (a k) = 0 ∧ v (b k) = 0) → Q v = 0 → v = 0)
    {H : Subgroup ((ι → K) ≃ₗ[K] (ι → K))}
    (hroot : ∀ p q : Fin m, p ≠ q → ∀ c : K, frameRootGen Q a b p q c ∈ H) (k₀ : Fin m)
    (hplane : ∀ u w : ι → K, (∀ k, k ≠ k₀ → u (a k) = 0 ∧ u (b k) = 0) →
      (∀ k, k ≠ k₀ → w (a k) = 0 ∧ w (b k) = 0) → eichler Q u w ∈ H) :
    elementaryGroup Q ≤ H := by
  have hconj : ∀ g ∈ H, g ∈ TauCeti.QuadraticMap.orthogonalGroup Q → ∀ u w,
      eichler Q u w ∈ H → eichler Q (g u) (g w) ∈ H := fun g hg hgO u w huw => by
    rw [← eichler_conj hgO]
    exact mul_mem (mul_mem hg huw) (inv_mem hg)
  have hswap : ∀ p q : Fin m, p ≠ q → pairSwapGen Q (a p) (b p) (a q) (b q) ∈ H := fun p q hpq => by
    rw [pairSwapGen_eq_frameRootGen h hpq]
    exact mul_mem (mul_mem (hroot q p (Ne.symm hpq) 1) (hroot p q hpq 1))
      (hroot q p (Ne.symm hpq) 1)
  have hswapO : ∀ p q : Fin m, pairSwapGen Q (a p) (b p) (a q) (b q) ∈
      TauCeti.QuadraticMap.orthogonalGroup Q := fun p q => eichler_mem_orthogonalGroup Q _ _
  have hvan : ∀ r : Bool, ∀ k, k ≠ k₀ →
      coordFrameGen a b k₀ r (a k) = (0 : K) ∧ coordFrameGen a b k₀ r (b k) = (0 : K) :=
    fun r k hk => coordFrameGen_vanish h (Ne.symm hk) r
  have hza' : ∀ k, z (a k) = 0 := hza
  have hzb' : ∀ k, z (b k) = 0 := hzb
  have hflip : ∀ i : Fin m,
      eichler Q (coordFrameGen a b i true + coordFrameGen a b i false + z) z ∈ H := by
    have h0 : eichler Q (coordFrameGen a b k₀ true + coordFrameGen a b k₀ false + z) z ∈ H := by
      refine hplane _ _ (fun k hk => ?_) (fun k hk => ⟨hza k, hzb k⟩)
      simp only [Pi.add_apply, (hvan true k hk).1, (hvan false k hk).1, (hvan true k hk).2,
        (hvan false k hk).2, hza k, hzb k, add_zero, and_self]
    intro i
    by_cases hi : i = k₀
    · rw [hi]
      exact h0
    have h1 := hconj _ (hswap k₀ i (Ne.symm hi)) (hswapO k₀ i) _ _ h0
    have hz' : pairSwapGen Q (a k₀) (b k₀) (a i) (b i) z = z :=
      pairSwapGen_apply_of_vanish h (hza k₀) (hzb k₀) (hza i) (hzb i)
    rwa [map_add, map_add, pairSwapGen_coordFrame h (Ne.symm hi),
      pairSwapGen_coordFrame h (Ne.symm hi), Equiv.swap_apply_left, hz'] at h1
  have hflipO : ∀ i : Fin m, eichler Q (coordFrameGen a b i true + coordFrameGen a b i false + z)
      z ∈ TauCeti.QuadraticMap.orthogonalGroup Q := fun i => eichler_mem_orthogonalGroup Q _ _
  set F := toHypFrameGen h z (by rw [hz]; exact isUnit_one) hza hzb
  refine F.elementaryGroup_le (fun {i j} hij s t c => ?_) (fun i s v hv => ?_)
    (fun v hv hv0 => hrest v (apply_eq_zero_of_polarGen h hv) hv0)
  · simp only [F, toHypFrameGen_vec]
    have hmixed : ∀ t : Bool, ∀ c : K,
        eichler Q (coordFrameGen a b j t) (c • coordFrameGen a b i (!t)) ∈ H := by
      intro t c
      cases t
      · exact (eichler_right_leftGen h hij c).symm ▸ hroot i j hij (-c)
      · exact hroot j i (Ne.symm hij) c
    by_cases hst : s = !t
    · rw [hst]
      exact hmixed t c
    · have hs : s = t := by
        revert hst
        cases s <;> cases t <;> decide
      obtain ⟨-, -, hwi, hwj⟩ := eichler_flip_applyGen h hz hza hzb i
      have h1 := hconj _ (hflip i) (hflipO i) _ _ (hmixed t c)
      rw [hs]
      rwa [map_smul, hwi, Bool.not_not, hwj j (Ne.symm hij)] at h1
  · simp only [F, toHypFrameGen_vec] at hv ⊢
    have hv' := apply_eq_zero_of_polarGen h hv
    have h0 : eichler Q (coordFrameGen a b k₀ s) v ∈ H :=
      hplane _ _ (hvan s) (fun k _ => hv' k)
    by_cases hi : i = k₀
    · rw [hi]
      exact h0
    have h1 := hconj _ (hswap k₀ i (Ne.symm hi)) (hswapO k₀ i) _ _ h0
    rwa [pairSwapGen_coordFrame h (Ne.symm hi), Equiv.swap_apply_left,
      pairSwapGen_apply_of_vanish h (hv' k₀).1 (hv' k₀).2 (hv' i).1 (hv' i).2] at h1

end Generic

section Main

variable {K : Type} [Field K] [Finite K] [CharP K 2] {m : ℕ} {b c : K}

private abbrev ι (m : ℕ) : Type := Fin (m + 1 - 1) ⊕ Fin (m + 1 - 1) ⊕ Fin 2

private abbrev frameLeft (m : ℕ) : Fin m → ι m := fun i => Sum.inl i

private abbrev frameRight (m : ℕ) : Fin m → ι m := fun i => Sum.inr (Sum.inl i)

private abbrev anisoVec (m : ℕ) : ι m → K := Pi.single (Sum.inr (Sum.inr 0)) 1

private theorem eq_zero_of_frame_vanish_quadMinus {v : ι m → K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (hv : ∀ k : Fin m, v (Sum.inl k) = 0 ∧ v (Sum.inr (Sum.inl k)) = 0)
    (hQ : CFSG.LieType.Universal.Spin.quadMinus (m + 1) K b c v = 0) : v = 0 := by
  have hsum : ∑ i : Fin (m + 1 - 1),
      v (Sum.inl i) * v (Sum.inr (Sum.inl i)) = 0 :=
    Finset.sum_eq_zero fun i _ => by rw [(hv i).1, zero_mul]
  rw [CFSG.LieType.Universal.Spin.quadMinus_apply, hsum, zero_add] at hQ
  set x := v (Sum.inr (Sum.inr 0)) with hx
  set y := v (Sum.inr (Sum.inr 1)) with hy
  have hy0 : y = 0 := by
    by_contra hyne
    apply hirr (x / y)
    field_simp
    linear_combination hQ
  have hx0 : x = 0 := by
    rw [hy0] at hQ
    simpa using hQ
  funext j
  rcases j with i | i | t
  · exact (hv i).1
  · exact (hv i).2
  · fin_cases t
    · simpa [hx] using hx0
    · simpa [hy] using hy0

theorem statedOmega_quadMinus_le_of_eichler (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (hm : 2 ≤ m) {H : Subgroup (GL ((Fin (m + 1 - 1) ⊕ Fin (m + 1 - 1) ⊕ Fin 2)) K)}
    (hroot : ∀ i j : Fin m, i ≠ j → ∀ t : K,
      (toLinEquiv ((Fin (m + 1 - 1) ⊕ Fin (m + 1 - 1) ⊕ Fin 2)) K).symm
        (eichler (CFSG.LieType.Universal.Spin.quadMinus (m + 1) K b c)
          (Pi.single (Sum.inl i) 1) (t • Pi.single (Sum.inr (Sum.inl j)) 1)) ∈ H)
    (k₀ : Fin m)
    (hplane : ∀ u w : (Fin (m + 1 - 1) ⊕ Fin (m + 1 - 1) ⊕ Fin 2) → K,
      (∀ k : Fin m, k ≠ k₀ → u (Sum.inl k) = 0 ∧ u (Sum.inr (Sum.inl k)) = 0) →
      (∀ k : Fin m, k ≠ k₀ → w (Sum.inl k) = 0 ∧ w (Sum.inr (Sum.inl k)) = 0) →
      (toLinEquiv ((Fin (m + 1 - 1) ⊕ Fin (m + 1 - 1) ⊕ Fin 2)) K).symm
        (eichler (CFSG.LieType.Universal.Spin.quadMinus (m + 1) K b c) u w) ∈ H) :
    StatedOmega (StatedQuadMinus (m + 1) K b c) ≤ H := by
  have hQ : ⇑(CFSG.LieType.Universal.Spin.quadMinus (m + 1) K b c) =
      StatedQuadMinus (m + 1) K b c := CFSG.LieType.Universal.Spin.coe_quadMinus (m + 1) K b c
  have hE : ⁅TauCeti.QuadraticMap.orthogonalGroup
        (CFSG.LieType.Universal.Spin.quadMinus (m + 1) K b c),
      TauCeti.QuadraticMap.orthogonalGroup
        (CFSG.LieType.Universal.Spin.quadMinus (m + 1) K b c)⁆ =
      elementaryGroup (CFSG.LieType.Universal.Spin.quadMinus (m + 1) K b c) :=
    commutator_orthogonalGroup_quadMinus_of_two_le (by omega) hirr
  set H' : Subgroup ((ι m → K) ≃ₗ[K] (ι m → K)) :=
    H.comap (toLinEquiv (ι m) K).symm.toMonoidHom with hH'
  have hroot' : ∀ i j : Fin m, i ≠ j → ∀ t : K,
      frameRootGen (CFSG.LieType.Universal.Spin.quadMinus (m + 1) K b c)
        (frameLeft m) (frameRight m) i j t ∈ H' := by
    intro i j hij t
    exact hroot i j hij t
  have hplane' : ∀ u w : ι m → K,
      (∀ k : Fin m, k ≠ k₀ → u (Sum.inl k) = 0 ∧ u (Sum.inr (Sum.inl k)) = 0) →
      (∀ k : Fin m, k ≠ k₀ → w (Sum.inl k) = 0 ∧ w (Sum.inr (Sum.inl k)) = 0) →
      eichler (CFSG.LieType.Universal.Spin.quadMinus (m + 1) K b c) u w ∈ H' := by
    intro u w hu hw
    exact hplane u w hu hw
  have hz : CFSG.LieType.Universal.Spin.quadMinus (m + 1) K b c (anisoVec m) = 1 := by
    rw [hQ]
    exact kOmM_statedQuadMinus_vec K b c
  have hza : ∀ k : Fin m, anisoVec m (Sum.inl k) = (0 : K) :=
    fun k => kOmMVec_kOmMEmb K (Sum.inl k)
  have hzb : ∀ k : Fin m, anisoVec m (Sum.inr (Sum.inl k)) = (0 : K) :=
    fun k => kOmMVec_kOmMEmb K (Sum.inr k)
  have hgen : elementaryGroup (CFSG.LieType.Universal.Spin.quadMinus (m + 1) K b c) ≤ H' :=
    elementaryGroupGen_le_of_rootElt (kOmM_isHypFrame (k := K) (r := m) b c) hz hza hzb
      (fun v hv h0 => eq_zero_of_frame_vanish_quadMinus hirr hv h0) hroot' k₀ hplane'
  rw [statedOmega_eq_map_elementaryGroup hQ hE]
  rintro x ⟨g, hg, rfl⟩
  exact hgen hg

theorem statedOmega_quadMinus_le_of_eichler_avoid (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (hm : 3 ≤ m) {H : Subgroup (GL ((Fin (m + 1 - 1) ⊕ Fin (m + 1 - 1) ⊕ Fin 2)) K)}
    {i₀ j₀ : Fin m} (hij₀ : i₀ ≠ j₀)
    (hroot : ∀ i j : Fin m, i ≠ j → ({i, j} : Finset (Fin m)) ≠ {i₀, j₀} → ∀ t : K,
      (toLinEquiv ((Fin (m + 1 - 1) ⊕ Fin (m + 1 - 1) ⊕ Fin 2)) K).symm
        (eichler (CFSG.LieType.Universal.Spin.quadMinus (m + 1) K b c)
          (Pi.single (Sum.inl i) 1) (t • Pi.single (Sum.inr (Sum.inl j)) 1)) ∈ H)
    (k₀ : Fin m)
    (hplane : ∀ u w : (Fin (m + 1 - 1) ⊕ Fin (m + 1 - 1) ⊕ Fin 2) → K,
      (∀ k : Fin m, k ≠ k₀ → u (Sum.inl k) = 0 ∧ u (Sum.inr (Sum.inl k)) = 0) →
      (∀ k : Fin m, k ≠ k₀ → w (Sum.inl k) = 0 ∧ w (Sum.inr (Sum.inl k)) = 0) →
      (toLinEquiv ((Fin (m + 1 - 1) ⊕ Fin (m + 1 - 1) ⊕ Fin 2)) K).symm
        (eichler (CFSG.LieType.Universal.Spin.quadMinus (m + 1) K b c) u w) ∈ H) :
    StatedOmega (StatedQuadMinus (m + 1) K b c) ≤ H := by
  have hex : ∀ i j : Fin m, i ≠ j → ({i, j} : Finset (Fin m)) = {i₀, j₀} → ∀ t : K,
      (toLinEquiv (ι m) K).symm
        (eichler (CFSG.LieType.Universal.Spin.quadMinus (m + 1) K b c)
          (Pi.single (Sum.inl i) 1) (t • Pi.single (Sum.inr (Sum.inl j)) 1)) ∈ H := by
    intro i j hij hp t
    obtain ⟨k, hki, hkj⟩ := CFSG.SeitzReduction.SymplecticPilot.exists_ne_ne_of_three_le hm i₀ j₀
    have hmemk : k ∉ ({i₀, j₀} : Finset (Fin m)) := by
      simp [hki, hkj]
    have hnotk : ∀ y : Fin m, ({k, y} : Finset (Fin m)) ≠ {i₀, j₀} := by
      intro y h
      exact hmemk (by rw [← h]; simp)
    have hnotk' : ∀ y : Fin m, ({y, k} : Finset (Fin m)) ≠ {i₀, j₀} := by
      intro y h
      exact hmemk (by rw [← h]; simp)
    set s := pairSwapGen (CFSG.LieType.Universal.Spin.quadMinus (m + 1) K b c)
      (frameLeft m k) (frameRight m k) (frameLeft m j₀) (frameRight m j₀) with hs
    have hframe := kOmM_isHypFrame (k := K) (r := m) b c
    have hsH : (toLinEquiv (ι m) K).symm s ∈ H := by
      rw [hs, pairSwapGen_eq_frameRootGen hframe hkj]
      simp only [map_mul]
      exact mul_mem (mul_mem (hroot j₀ k (Ne.symm hkj) (hnotk' j₀) 1)
        (hroot k j₀ hkj (hnotk j₀) 1)) (hroot j₀ k (Ne.symm hkj) (hnotk' j₀) 1)
    have hconj₁ : frameRootGen (CFSG.LieType.Universal.Spin.quadMinus (m + 1) K b c)
        (frameLeft m) (frameRight m) i₀ j₀ t =
        s * frameRootGen (CFSG.LieType.Universal.Spin.quadMinus (m + 1) K b c)
          (frameLeft m) (frameRight m) i₀ k t * s⁻¹ := by
      have h := pairSwapGen_conj_frameRootGen hframe hkj i₀ k t
      rw [Equiv.swap_apply_of_ne_of_ne (Ne.symm hki) hij₀, Equiv.swap_apply_left] at h
      exact h.symm
    have hconj₂ : frameRootGen (CFSG.LieType.Universal.Spin.quadMinus (m + 1) K b c)
        (frameLeft m) (frameRight m) j₀ i₀ t =
        s * frameRootGen (CFSG.LieType.Universal.Spin.quadMinus (m + 1) K b c)
          (frameLeft m) (frameRight m) k i₀ t * s⁻¹ := by
      have h := pairSwapGen_conj_frameRootGen hframe hkj k i₀ t
      rw [Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne (Ne.symm hki) hij₀] at h
      exact h.symm
    have hx₀ : (toLinEquiv (ι m) K).symm
        (frameRootGen (CFSG.LieType.Universal.Spin.quadMinus (m + 1) K b c)
          (frameLeft m) (frameRight m) i₀ j₀ t) ∈ H := by
      rw [hconj₁]
      simp only [map_mul, map_inv]
      exact mul_mem (mul_mem hsH (hroot i₀ k (Ne.symm hki) (hnotk' i₀) t)) (inv_mem hsH)
    have hx : (toLinEquiv (ι m) K).symm
        (eichler (CFSG.LieType.Universal.Spin.quadMinus (m + 1) K b c)
          (Pi.single (Sum.inl i₀) 1) (t • Pi.single (Sum.inr (Sum.inl j₀)) 1)) ∈ H := hx₀
    have hx'₀ : (toLinEquiv (ι m) K).symm
        (frameRootGen (CFSG.LieType.Universal.Spin.quadMinus (m + 1) K b c)
          (frameLeft m) (frameRight m) j₀ i₀ t) ∈ H := by
      rw [hconj₂]
      simp only [map_mul, map_inv]
      exact mul_mem (mul_mem hsH (hroot k i₀ hki (hnotk i₀) t)) (inv_mem hsH)
    have hx' : (toLinEquiv (ι m) K).symm
        (eichler (CFSG.LieType.Universal.Spin.quadMinus (m + 1) K b c)
          (Pi.single (Sum.inl j₀) 1) (t • Pi.single (Sum.inr (Sum.inl i₀)) 1)) ∈ H := hx'₀
    have hi : i = i₀ ∨ i = j₀ := by
      have : i ∈ ({i₀, j₀} : Finset (Fin m)) := by rw [← hp]; simp
      simpa using this
    have hj : j = i₀ ∨ j = j₀ := by
      have : j ∈ ({i₀, j₀} : Finset (Fin m)) := by rw [← hp]; simp
      simpa using this
    rcases hi with rfl | rfl
    · have hj' : j = j₀ := by
        rcases hj with h | h
        · exact absurd h.symm hij
        · exact h
      subst hj'
      exact hx
    · have hj' : j = i₀ := by
        rcases hj with h | h
        · exact h
        · exact absurd h.symm hij
      subst hj'
      exact hx'
  refine statedOmega_quadMinus_le_of_eichler hirr (by omega) ?_ k₀ hplane
  intro i j hij t
  by_cases hp : ({i, j} : Finset (Fin m)) = {i₀, j₀}
  · exact hex i j hij hp t
  · exact hroot i j hij hp t

end Main

end CFSG.StandardType
