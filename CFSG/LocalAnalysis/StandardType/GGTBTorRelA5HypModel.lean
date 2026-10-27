module

public import CFSG.LocalAnalysis.StandardType.GGTBTorRelA5Coord
public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerUnitaryHypTorus
public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerUnitaryHypEigen

@[expose] public section

namespace CFSG.StandardType.RelA5

open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial Matrix Multiplicative

variable {n : ℕ} {K : Type} [Field K]

variable (n K) in
abbrev muSplit : Subgroup Kˣ := rootsOfUnity (2 ^ n - 1) K

theorem bar_eq_of_mem_muSplit (h : UnitaryFieldData 2 n K) {x : Kˣ} (hx : x ∈ muSplit n K) :
    h.bar (x : K) = x := by
  have hx1 : x ^ (2 ^ n - 1) = 1 := by
    rw [muSplit, mem_rootsOfUnity] at hx
    exact hx
  have hxK : (x : K) ^ (2 ^ n - 1) = 1 := by
    have := congrArg (fun u : Kˣ => (u : K)) hx1
    simpa [Units.val_pow_eq_pow_val] using this
  have hpow : (x : K) ^ (2 ^ n) = (x : K) := by
    rw [← Nat.sub_add_cancel (Nat.one_le_two_pow), pow_add, hxK, one_mul, pow_one]
  rw [h.bar_apply, hpow]

private theorem torusRatio_muSplit (h : UnitaryFieldData 2 n K) {r : ℕ}
    (a : Fin r → muSplit n K) :
    torusRatio h (fun i => ((a i : muSplit n K) : Kˣ)) (Fin.elim0) = 1 := by
  have hprod : (∏ i, (((a i : muSplit n K) : Kˣ) : K) /
      h.bar (((a i : muSplit n K) : Kˣ) : K)) = 1 := by
    refine Finset.prod_eq_one fun i _ => ?_
    rw [bar_eq_of_mem_muSplit h (a i).2]
    exact div_self (Units.ne_zero _)
  rw [torusRatio, hprod, Finset.prod_eq_one (fun k _ => k.elim0), mul_one]

theorem exists_hypSmall (h : UnitaryFieldData 2 n K) :
    ∃ F : (Fin 3 → muSplit n K) →* hypSU h 3 0, ∀ z,
      (((F z : hypSU h 3 0) : GL (HypIndex 3 0) K) : Matrix (HypIndex 3 0) (HypIndex 3 0) K) =
        diagonal (torusEntries h (fun i => ((z i : muSplit n K) : Kˣ)) (Fin.elim0)) := by
  classical
  let d0 : Fin 0 → Kˣ := Fin.elim0
  have hd : ∀ k : Fin 0, h.norm (d0 k : K) = 1 := fun k => k.elim0
  have hex : ∀ z : Fin 3 → muSplit n K, ∃ g : hypSU h 3 0,
      (((g : GL (HypIndex 3 0) K) : Matrix (HypIndex 3 0) (HypIndex 3 0) K) =
        diagonal (torusEntries h (fun i => ((z i : muSplit n K) : Kˣ)) (Fin.elim0))) := by
    intro z
    obtain ⟨g, -, hg⟩ := torusMat_mem_hypSU (d := Fin.elim0) h
      (fun i => ((z i : muSplit n K) : Kˣ)) hd (torusRatio_muSplit h z)
    exact ⟨g, hg⟩
  let F0 : (Fin 3 → muSplit n K) → hypSU h 3 0 := fun z => Classical.choose (hex z)
  have hF0 : ∀ z : Fin 3 → muSplit n K,
      (((F0 z : hypSU h 3 0) : GL (HypIndex 3 0) K) :
        Matrix (HypIndex 3 0) (HypIndex 3 0) K) =
        diagonal (torusEntries h (fun i => ((z i : muSplit n K) : Kˣ)) (Fin.elim0)) :=
    fun z => Classical.choose_spec (hex z)
  have hmul : ∀ z w, F0 (z * w) = F0 z * F0 w := by
    intro z w
    apply Subtype.ext
    apply Units.ext
    rw [Subgroup.coe_mul, Units.val_mul, hF0, hF0, hF0, diagonal_mul_diagonal]
    congr 1
    funext x
    rcases x with i | k | i
    · simp [torusEntries]
    · exact k.elim0
    · simp only [torusEntries, Pi.mul_apply, Subgroup.coe_mul, Units.val_mul, map_mul, mul_inv]
  exact ⟨MonoidHom.mk' F0 hmul, hF0⟩

private theorem symm_weylPerm_of_sq_one {w : Equiv.Perm (Fin 3 ⊕ Fin 3)}
    (hww : weylPerm (ε := 0) w * weylPerm (ε := 0) w = 1) (x : HypIndex 3 0) :
    (weylPerm (ε := 0) w).symm x = weylPerm (ε := 0) w x := by
  have h2 : weylPerm (ε := 0) w (weylPerm (ε := 0) w x) = x := by
    have h := congrFun (congrArg DFunLike.coe hww) x
    simpa using h
  rw [Equiv.symm_apply_eq]
  exact h2.symm

private theorem weylElt_conj_hypSmall (h : UnitaryFieldData 2 n K)
    {F : (Fin 3 → muSplit n K) →* hypSU h 3 0}
    (hF : ∀ z, (((F z : hypSU h 3 0) : GL (HypIndex 3 0) K) :
      Matrix (HypIndex 3 0) (HypIndex 3 0) K) =
        diagonal (torusEntries h (fun i => ((z i : muSplit n K) : Kˣ)) (Fin.elim0)))
    {c : K} (hc : c ∈ h.traceZero) (hc0 : c ≠ 0)
    {w₀ : Equiv.Perm (Fin 3 ⊕ Fin 3)} (hw₀ : w₀ ∈ hypWeyl 3)
    (hinv : ∀ x : HypIndex 3 0,
      (weylPerm (ε := 0) w₀).symm x = weylPerm (ε := 0) w₀ x)
    (z z' : Fin 3 → muSplit n K)
    (hzz : ∀ x : HypIndex 3 0,
      torusEntries h (fun i => ((z i : muSplit n K) : Kˣ)) (Fin.elim0)
        (weylPerm (ε := 0) w₀ x) =
      torusEntries h (fun i => ((z' i : muSplit n K) : Kˣ)) (Fin.elim0) x) :
    weylElt (r := 3) (ε := 0) h hc hc0 hw₀ * F z *
      (weylElt (r := 3) (ε := 0) h hc hc0 hw₀)⁻¹ = F z' := by
  have hgl : weylElt (r := 3) (ε := 0) h hc hc0 hw₀ * F z =
      F z' * weylElt (r := 3) (ε := 0) h hc hc0 hw₀ := by
    apply Subtype.ext
    apply Units.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul, hF z, hF z',
      coe_weylElt, weylMat_mul_diagonal]
    have hfun : (fun a => torusEntries h (fun i => ((z i : muSplit n K) : Kˣ)) (Fin.elim0)
        ((weylPerm (ε := 0) w₀).symm a)) =
        torusEntries h (fun i => ((z' i : muSplit n K) : Kˣ)) (Fin.elim0) := by
      funext a
      rw [hinv a]
      exact hzz a
    rw [hfun]
  rw [hgl, mul_assoc, mul_inv_cancel, mul_one]

section Model

variable (h : UnitaryFieldData 2 n K) (F : (Fin 3 → muSplit n K) →* hypSU h 3 0)
  (hF : ∀ z, (((F z : hypSU h 3 0) : GL (HypIndex 3 0) K) :
    Matrix (HypIndex 3 0) (HypIndex 3 0) K) =
      diagonal (torusEntries h (fun i => ((z i : muSplit n K) : Kˣ)) (Fin.elim0)))
include hF

theorem hypSmall_injective : Function.Injective F := by
  intro z w hzw
  have hm : diagonal (torusEntries h (fun i => ((z i : muSplit n K) : Kˣ)) (Fin.elim0)) =
      diagonal (torusEntries h (fun i => ((w i : muSplit n K) : Kˣ)) (Fin.elim0)) := by
    rw [← hF z, ← hF w, hzw]
  funext i
  have h := congrFun (congrFun hm (.inl i)) (.inl i)
  simp only [diagonal_apply_eq, torusEntries] at h
  exact Subtype.ext (Units.ext h)

theorem hypSmall_mem_hypTorus (z : Fin 3 → muSplit n K) : F z ∈ hypTorus h 3 0 :=
  ⟨fun i => ((z i : muSplit n K) : Kˣ), Fin.elim0, fun k => k.elim0,
    torusRatio_muSplit h z, hF z⟩

theorem exists_eq_hypSmall_of_pow {t : hypSU h 3 0} (ht : t ∈ hypTorus h 3 0)
    (htm : t ^ (2 ^ n - 1) = 1) : ∃ z, F z = t := by
  obtain ⟨a, d, hd, hratio, hmat⟩ := ht
  have hD : ∀ x : HypIndex 3 0, torusEntries h a d x ^ (2 ^ n - 1) = 1 := by
    have hpow : (((t : GL (HypIndex 3 0) K)) :
        Matrix (HypIndex 3 0) (HypIndex 3 0) K) ^ (2 ^ n - 1) = 1 := by
      have := congrArg (fun u : hypSU h 3 0 =>
        ((u : GL (HypIndex 3 0) K) : Matrix (HypIndex 3 0) (HypIndex 3 0) K)) htm
      simpa using this
    rw [hmat, diagonal_pow] at hpow
    intro x
    have := congrFun (congrFun hpow x) x
    simpa using this
  have haK : ∀ i : Fin 3, ((a i : K)) ^ (2 ^ n - 1) = 1 := by
    intro i
    have := hD (.inl i)
    simpa [torusEntries] using this
  have ha : ∀ i : Fin 3, a i ^ (2 ^ n - 1) = 1 := fun i => Units.ext (by
    rw [Units.val_pow_eq_pow_val]
    exact haK i)
  refine ⟨fun i => ⟨a i, (mem_rootsOfUnity (2 ^ n - 1) (a i)).mpr (ha i)⟩, ?_⟩
  apply Subtype.ext
  apply Units.ext
  rw [hF, hmat]
  congr 1
  funext x
  rcases x with i | k | i
  · rfl
  · exact k.elim0
  · rfl

theorem exists_hypWeyl :
    ∃ w : Fin 3 → hypSU h 3 0, ∀ k z, w k * F z * (w k)⁻¹ = F (refl k z) := by
  obtain ⟨c, hc, hc0⟩ := exists_mem_traceZero_ne_zero' h
  have hw0 : Equiv.sumCongr (Equiv.swap (0 : Fin 3) 1) (Equiv.swap 0 1) ∈ hypWeyl 3 :=
    sumCongr_mem_hypWeyl _
  have hw1 : Equiv.sumCongr (Equiv.swap (1 : Fin 3) 2) (Equiv.swap 1 2) ∈ hypWeyl 3 :=
    sumCongr_mem_hypWeyl _
  have hw2 : swapSet ({2} : Finset (Fin 3)) ∈ hypWeyl 3 := swapSet_mem_hypWeyl _
  refine ⟨![weylElt (r := 3) (ε := 0) h hc hc0 hw0,
    weylElt (r := 3) (ε := 0) h hc hc0 hw1,
    weylElt (r := 3) (ε := 0) h hc hc0 hw2], ?_⟩
  intro k z
  fin_cases k
  · refine weylElt_conj_hypSmall (h := h) (F := F) (hF := hF) (c := c) (hc := hc)
      (hc0 := hc0) (w₀ := Equiv.sumCongr (Equiv.swap (0 : Fin 3) 1) (Equiv.swap 0 1))
      (hw₀ := hw0)
      (hinv := fun x => symm_weylPerm_of_sq_one (w := Equiv.sumCongr (Equiv.swap (0 : Fin 3) 1)
        (Equiv.swap 0 1)) (by decide) x) (z := z) (z' := refl 0 z) ?_
    · intro x
      have hσl : ∀ i : Fin 3, weylPerm (ε := 0) (Equiv.sumCongr (Equiv.swap (0 : Fin 3) 1)
          (Equiv.swap 0 1)) (.inl i) = .inl (Equiv.swap 0 1 i) := by
        intro i
        rw [weylPerm_inl]
        rfl
      have hσr : ∀ i : Fin 3, weylPerm (ε := 0) (Equiv.sumCongr (Equiv.swap (0 : Fin 3) 1)
          (Equiv.swap 0 1)) (.inr (.inr i)) = .inr (.inr (Equiv.swap 0 1 i)) := by
        intro i
        rw [weylPerm_inr_inr]
        rfl
      have hzf : ∀ i : Fin 3, (refl 0 z) i = z (Equiv.swap 0 1 i) := by
        intro i
        fin_cases i <;> rfl
      rcases x with i | kk | i
      · rw [hσl]
        simp only [torusEntries]
        rw [hzf i]
      · exact kk.elim0
      · rw [hσr]
        simp only [torusEntries]
        rw [hzf i]
  · refine weylElt_conj_hypSmall (h := h) (F := F) (hF := hF) (c := c) (hc := hc)
      (hc0 := hc0) (w₀ := Equiv.sumCongr (Equiv.swap (1 : Fin 3) 2) (Equiv.swap 1 2))
      (hw₀ := hw1)
      (hinv := fun x => symm_weylPerm_of_sq_one (w := Equiv.sumCongr (Equiv.swap (1 : Fin 3) 2)
        (Equiv.swap 1 2)) (by decide) x) (z := z) (z' := refl 1 z) ?_
    · intro x
      have hσl : ∀ i : Fin 3, weylPerm (ε := 0) (Equiv.sumCongr (Equiv.swap (1 : Fin 3) 2)
          (Equiv.swap 1 2)) (.inl i) = .inl (Equiv.swap 1 2 i) := by
        intro i
        rw [weylPerm_inl]
        rfl
      have hσr : ∀ i : Fin 3, weylPerm (ε := 0) (Equiv.sumCongr (Equiv.swap (1 : Fin 3) 2)
          (Equiv.swap 1 2)) (.inr (.inr i)) = .inr (.inr (Equiv.swap 1 2 i)) := by
        intro i
        rw [weylPerm_inr_inr]
        rfl
      have hzf : ∀ i : Fin 3, (refl 1 z) i = z (Equiv.swap 1 2 i) := by
        intro i
        fin_cases i <;> rfl
      rcases x with i | kk | i
      · rw [hσl]
        simp only [torusEntries]
        rw [hzf i]
      · exact kk.elim0
      · rw [hσr]
        simp only [torusEntries]
        rw [hzf i]
  · refine weylElt_conj_hypSmall (h := h) (F := F) (hF := hF) (c := c) (hc := hc)
      (hc0 := hc0) (w₀ := swapSet ({2} : Finset (Fin 3))) (hw₀ := hw2)
      (hinv := fun x => symm_weylPerm_of_sq_one (w := swapSet ({2} : Finset (Fin 3)))
        (by decide) x) (z := z) (z' := refl 2 z) ?_
    · intro x
      have hzf : ∀ i : Fin 3, (refl 2 z) i = if i = 2 then (z 2)⁻¹ else z i := by
        intro i
        fin_cases i <;> simp [refl]
      have hσl : ∀ i : Fin 3, weylPerm (ε := 0) (swapSet ({2} : Finset (Fin 3))) (.inl i) =
          if i = 2 then .inr (.inr 2) else .inl i := by
        intro i
        rw [weylPerm_inl]
        by_cases hi : i = 2
        · subst hi
          rfl
        · rw [if_neg hi]
          simp [swapSet, hi, lineCoord]
      have hσr : ∀ i : Fin 3, weylPerm (ε := 0) (swapSet ({2} : Finset (Fin 3))) (.inr (.inr i)) =
          if i = 2 then .inl 2 else .inr (.inr i) := by
        intro i
        rw [weylPerm_inr_inr]
        by_cases hi : i = 2
        · subst hi
          rfl
        · rw [if_neg hi]
          simp [swapSet, hi, lineCoord]
      rcases x with i | kk | i
      · fin_cases i <;> simp [torusEntries, hσl, hzf, bar_eq_of_mem_muSplit h (z 2).2]
      · exact kk.elim0
      · fin_cases i <;> simp [torusEntries, hσr, hzf, map_inv₀, bar_eq_of_mem_muSplit h (z 2).2]

theorem mem_hypTorus_of_commute {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ 2 ^ n - 1)
    (g : hypSU h 3 0) (hg : ∀ z : Fin 3 → muSplit n K, (∀ i, z i ^ p = 1) → Commute g (F z)) :
    g ∈ hypTorus h 3 0 := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Finite K := h.finite
  obtain ⟨ζ₀, hζ₀⟩ := exists_primitiveRoot_of_dvd_two_pow_sub_one h hp hpq
  have hmem : Units.mk0 ζ₀ (hζ₀.ne_zero hp.ne_zero) ∈ muSplit n K := by
    rw [muSplit, mem_rootsOfUnity]
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_one, Units.val_mk0]
    exact (hζ₀.pow_eq_one_iff_dvd (2 ^ n - 1)).mpr hpq
  let ζ : Kˣ := Units.mk0 ζ₀ (hζ₀.ne_zero hp.ne_zero)
  have hζ : IsPrimitiveRoot ζ p :=
    IsPrimitiveRoot.coe_units_iff.mp (by simpa [ζ] using hζ₀)
  let ζm : muSplit n K := ⟨ζ, hmem⟩
  have hζm_pow : ζm ^ p = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    exact hζ.pow_eq_one
  have hζ1 : (ζ : K) ≠ 1 := by
    intro hc1
    exact hζ.ne_one (by have := hp.two_le; omega) (Units.ext hc1)
  have hζinv1 : ((ζ : K))⁻¹ ≠ 1 := by
    intro hc1
    exact hζ1 ((inv_eq_one).mp hc1)
  have hζ_inv : ζ ≠ ζ⁻¹ := by
    intro hc1
    have h2 : ζ ^ 2 = 1 := by
      rw [pow_two]
      exact eq_inv_iff_mul_eq_one.mp hc1
    have hdvd : p ∣ 2 := (hζ.pow_eq_one_iff_dvd 2).mp h2
    have hp_le : p ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
    have hp_ge : 2 ≤ p := hp.two_le
    omega
  have hζ_invK : (ζ : K) ≠ ((ζ : K))⁻¹ := fun hc1 => hζ_inv (Units.ext hc1)
  let G : Matrix (HypIndex 3 0) (HypIndex 3 0) K :=
    ((g : GL (HypIndex 3 0) K) : Matrix (HypIndex 3 0) (HypIndex 3 0) K)
  let zt : Fin 3 → Fin 3 → muSplit n K := fun i j => if j = i then ζm else 1
  have hztj : ∀ (i j : Fin 3), ((zt i j : muSplit n K) : Kˣ) = if j = i then ζ else 1 := by
    intro i j
    show (((if j = i then ζm else 1 : muSplit n K)) : Kˣ) = _
    by_cases hj : j = i
    · rw [if_pos hj, if_pos hj]
    · simp [hj]
  have hzt : ∀ (i : Fin 3), ∀ j : Fin 3, zt i j ^ p = 1 := by
    intro i j
    show (if j = i then ζm else 1 : muSplit n K) ^ p = 1
    by_cases hj : j = i <;> simp [hj, hζm_pow]
  have hcomm : ∀ i, G * diagonal (torusEntries h (fun j => ((zt i j : muSplit n K) : Kˣ))
      Fin.elim0) = diagonal (torusEntries h (fun j => ((zt i j : muSplit n K) : Kˣ))
      Fin.elim0) * G := by
    intro i
    have hci : g * F (zt i) = F (zt i) * g := hg (zt i) (hzt i)
    have h2 := congrArg (fun u : hypSU h 3 0 =>
      ((u : GL (HypIndex 3 0) K) : Matrix (HypIndex 3 0) (HypIndex 3 0) K)) hci
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul] at h2
    rw [hF (zt i)] at h2
    exact h2
  have hDval_inl : ∀ (i j : Fin 3),
      torusEntries h (fun j => ((zt i j : muSplit n K) : Kˣ)) Fin.elim0 (.inl j) =
        if j = i then (ζ : K) else 1 := by
    intro i j
    rw [torusEntries, hztj i j]
    by_cases hj : j = i <;> simp [hj]
  have hDval_inr : ∀ (i j : Fin 3),
      torusEntries h (fun j => ((zt i j : muSplit n K) : Kˣ)) Fin.elim0 (.inr (.inr j)) =
        if j = i then ((ζ : K))⁻¹ else 1 := by
    intro i j
    have hbarj : h.bar ((((zt i j : muSplit n K)) : Kˣ) : K) =
        ((if j = i then ζ else 1 : Kˣ) : K) := by
      rw [hztj i j, ← hztj i j]
      exact bar_eq_of_mem_muSplit h (zt i j).2
    rw [torusEntries, hbarj]
    by_cases hj : j = i <;> simp [hj]
  have hsep : ∀ a b : HypIndex 3 0, a ≠ b → G a b = 0 := by
    intro a b hab
    have key : ∀ (i : Fin 3),
        torusEntries h (fun j => ((zt i j : muSplit n K) : Kˣ)) Fin.elim0 a ≠
        torusEntries h (fun j => ((zt i j : muSplit n K) : Kˣ)) Fin.elim0 b → G a b = 0 := by
      intro i hi
      by_contra h0
      have hm := congrFun (congrFun (hcomm i) a) b
      rw [Matrix.mul_diagonal, Matrix.diagonal_mul] at hm
      have h1 : G a b * (torusEntries h (fun j => ((zt i j : muSplit n K) : Kˣ)) Fin.elim0 b -
          torusEntries h (fun j => ((zt i j : muSplit n K) : Kˣ)) Fin.elim0 a) = 0 := by
        rw [mul_sub, hm]
        ring
      exact (mul_ne_zero h0 (sub_ne_zero.mpr (Ne.symm hi))) h1
    rcases a with i | kk | i
    · rcases b with j | ll | j
      · have hij : i ≠ j := fun hh => hab (by rw [hh])
        refine key i ?_
        rw [hDval_inl i i, hDval_inl i j, if_pos rfl, if_neg (Ne.symm hij)]
        exact hζ1
      · exact ll.elim0
      · refine key i ?_
        rw [hDval_inl i i, hDval_inr i j, if_pos rfl]
        by_cases hj : j = i
        · rw [if_pos hj]
          exact hζ_invK
        · rw [if_neg hj]
          exact hζ1
    · exact kk.elim0
    · rcases b with j | ll | j
      · refine key i ?_
        rw [hDval_inr i i, hDval_inl i j, if_pos rfl]
        by_cases hj : j = i
        · rw [if_pos hj]
          exact fun hh => hζ_invK hh.symm
        · rw [if_neg hj]
          exact hζinv1
      · exact ll.elim0
      · have hij : i ≠ j := fun hh => hab (by rw [hh])
        refine key i ?_
        rw [hDval_inr i i, hDval_inr i j, if_pos rfl, if_neg (Ne.symm hij)]
        exact hζinv1
  let gv : HypIndex 3 0 → K := fun a => G a a
  have hdiagmat : G = diagonal gv := by
    ext a b
    by_cases hab : a = b
    · subst hab
      rw [Matrix.diagonal_apply_eq]
    · rw [hsep a b hab, Matrix.diagonal_apply_ne _ hab]
  have hdet_ne : G.det ≠ 0 := Matrix.GeneralLinearGroup.det_ne_zero (g : GL (HypIndex 3 0) K)
  have hprod : ∀ a : HypIndex 3 0, gv a ≠ 0 := by
    have hd : (∏ a : HypIndex 3 0, gv a) ≠ 0 := by
      rw [← Matrix.det_diagonal, ← hdiagmat]
      exact hdet_ne
    intro a
    exact (Finset.prod_ne_zero_iff.mp hd) a (Finset.mem_univ a)
  let A : Fin 3 → Kˣ := fun i => Units.mk0 (gv (.inl i)) (hprod (.inl i))
  have hdetg : ((g : GL (HypIndex 3 0) K) : Matrix (HypIndex 3 0) (HypIndex 3 0) K).det = 1 :=
    (mem_hypSU.mp g.2).2
  have hiso := (mem_hypSU.mp g.2).1
  have hgmat : ((g : GL (HypIndex 3 0) K) : Matrix (HypIndex 3 0) (HypIndex 3 0) K) = G := rfl
  have hiso_entry : ∀ i : Fin 3,
      h.bar (gv (.inl i)) * gv (.inr (.inr i)) = 1 := by
    intro i
    have hmapT : ((G.map h.bar))ᵀ = diagonal (fun a => h.bar (gv a)) := by
      conv_lhs => rw [hdiagmat]
      rw [Matrix.diagonal_map (map_zero h.bar), Matrix.diagonal_transpose]
    have hentry := congrFun (congrFun hiso (.inl i)) (.inr (.inr i))
    rw [hgmat, show ((G.map h.bar))ᵀ = diagonal (fun a => h.bar (gv a)) from hmapT,
      hdiagmat] at hentry
    have hL : (diagonal (fun a => h.bar (gv a)) * hypGram 3 0 K *
        diagonal gv) (.inl i) (.inr (.inr i)) =
        h.bar (gv (.inl i)) * gv (.inr (.inr i)) := by
      rw [Matrix.mul_assoc, Matrix.diagonal_mul, Matrix.mul_diagonal, hypGram_apply]
      simp
    rw [hL, hypGram_apply] at hentry
    simpa using hentry
  have hAmat : ((g : GL (HypIndex 3 0) K) : Matrix (HypIndex 3 0) (HypIndex 3 0) K) =
      diagonal (torusEntries h A Fin.elim0) := by
    rw [hgmat, hdiagmat]
    congr 1
    funext x
    rcases x with i | kk | i
    · rfl
    · exact kk.elim0
    · show gv (.inr (.inr i)) = (h.bar (gv (.inl i)))⁻¹
      exact eq_inv_of_mul_eq_one_right (hiso_entry i)
  refine ⟨A, Fin.elim0, fun k => k.elim0, ?_, ?_⟩
  · rw [← det_diagonal_torusEntries h A Fin.elim0, ← hAmat]
    exact hdetg
  · exact hAmat

end Model

theorem hypTorus_commute (h : UnitaryFieldData 2 n K) {x y : hypSU h 3 0}
    (hx : x ∈ hypTorus h 3 0) (hy : y ∈ hypTorus h 3 0) : Commute x y := by
  obtain ⟨a, d, hd, hp, hxmat⟩ := hx
  obtain ⟨a', d', hd', hp', hymat⟩ := hy
  show x * y = y * x
  apply Subtype.ext
  apply Units.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul, hxmat, hymat,
    diagonal_mul_diagonal, diagonal_mul_diagonal]
  congr 1
  funext i
  exact mul_comm _ _

theorem mem_hypTorus_of_scalar (h : UnitaryFieldData 2 n K) (g : hypSU h 3 0) {c : K}
    (hg : ((g : GL (HypIndex 3 0) K) : Matrix (HypIndex 3 0) (HypIndex 3 0) K) =
      diagonal (fun _ => c)) : g ∈ hypTorus h 3 0 := by
  have hiso := (mem_hypSU.mp g.2).1
  have hdet := (mem_hypSU.mp g.2).2
  have hbc : h.bar c * c = 1 := by
    have h := congrFun (congrFun hiso (.inl 0)) (.inr (.inr 0))
    rw [hg] at h
    simpa [Matrix.mul_diagonal, Matrix.diagonal_mul, hypGram_apply] using h
  have hc0 : c ≠ 0 := by
    rintro rfl
    simp at hbc
  have hbar : h.bar c = c⁻¹ := by
    refine mul_right_cancel₀ hc0 ?_
    rw [hbc, inv_mul_cancel₀ hc0]
  have hdet6 : c ^ 6 = 1 := by
    have h := hdet
    rw [hg, Matrix.det_diagonal, Finset.prod_const, Finset.card_univ] at h
    have hc : Fintype.card (HypIndex 3 0) = 6 := by
      simp only [HypIndex, Fintype.card_sum, Fintype.card_fin]
    rw [hc] at h
    exact h
  refine ⟨fun _ => Units.mk0 c hc0, Fin.elim0, fun k => k.elim0, ?_, ?_⟩
  · rw [torusRatio]
    have hp1 : (∏ _i : Fin 3,
        (↑(Units.mk0 c hc0) : K) / h.bar (↑(Units.mk0 c hc0) : K)) = 1 := by
      simp only [Units.val_mk0, hbar, div_inv_eq_mul, Finset.prod_const, Finset.card_fin]
      rw [show (c * c) ^ 3 = c ^ 6 by ring, hdet6]
    have hp0 : (∏ k : Fin 0, ((Fin.elim0 k : Kˣ) : K)) = 1 :=
      Finset.prod_eq_one fun k _ => k.elim0
    rw [hp1, hp0, mul_one]
  · rw [hg]
    congr 1
    funext x
    rcases x with i | k | i
    · rfl
    · exact k.elim0
    · simp only [torusEntries, Units.val_mk0, hbar, inv_inv]

section PTorsion

variable {p : ℕ} [Fact p.Prime]

theorem card_muSplit [Finite K] (hK : Nat.card K = (2 ^ n) ^ 2) :
    Nat.card (muSplit n K) = 2 ^ n - 1 := by
  have : Fintype K := Fintype.ofFinite K
  have hK2 : 1 < Nat.card K := by
    rw [Nat.card_eq_fintype_card]
    exact Fintype.one_lt_card
  have hn : n ≠ 0 := by
    rintro rfl
    rw [hK] at hK2
    norm_num at hK2
  have hne : 2 ^ n - 1 ≠ 0 := by
    have h1 : 1 < 2 ^ n := by
      calc 1 = 2 ^ 0 := by norm_num
        _ < 2 ^ n := Nat.pow_lt_pow_right (by norm_num) (Nat.pos_of_ne_zero hn)
    omega
  have : NeZero (2 ^ n - 1) := ⟨hne⟩
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Kˣ)
  have hgprim : IsPrimitiveRoot g (Nat.card Kˣ) := IsPrimitiveRoot.iff_orderOf.mpr hg
  have hcard : Nat.card Kˣ = (2 ^ n + 1) * (2 ^ n - 1) := by
    rw [Nat.card_units, hK]
    simpa using Nat.sq_sub_sq (2 ^ n) 1
  have hprim : IsPrimitiveRoot (g ^ (2 ^ n + 1)) (2 ^ n - 1) :=
    hgprim.pow Nat.card_pos hcard
  exact IsPrimitiveRoot.card_rootsOfUnity' hprim

theorem exists_zeta_muSplit [Finite K] (hK : Nat.card K = (2 ^ n) ^ 2) (hpq : p ∣ 2 ^ n - 1) :
    ∃ ζ : muSplit n K, IsPrimitiveRoot ζ p := by
  have : Fintype K := Fintype.ofFinite K
  have hcard := card_muSplit (n := n) (K := K) hK
  obtain ⟨ζ, hζ⟩ := exists_prime_orderOf_dvd_card' (G := muSplit n K) p (by rw [hcard]; exact hpq)
  exact ⟨ζ, IsPrimitiveRoot.iff_orderOf.mpr hζ⟩

def embP (ζ : muSplit n K) (hζ : ζ ^ p = 1) :
    (Fin 3 → Multiplicative (ZMod p)) →* (Fin 3 → muSplit n K) where
  toFun f i := ζ ^ (toAdd (f i)).val
  map_one' := by
    funext i
    simp
  map_mul' f g := by
    funext i
    have hmod : ∀ x : ℕ, ζ ^ (x % p) = ζ ^ x := fun x => by
      conv_rhs => rw [← Nat.mod_add_div x p, pow_add, pow_mul, hζ, one_pow, mul_one]
    simp only [Pi.mul_apply, toAdd_mul]
    rw [ZMod.val_add, hmod, pow_add]

omit [Fact p.Prime] in
theorem isPrimitiveRoot_coe {ζ : muSplit n K} (hζ : IsPrimitiveRoot ζ p) :
    IsPrimitiveRoot ((ζ : Kˣ) : K) p := by
  rw [IsPrimitiveRoot.coe_units_iff]
  exact hζ.map_of_injective (Subgroup.subtype_injective _)

theorem mem_range_embP_iff {ζ : muSplit n K} (hζ : IsPrimitiveRoot ζ p)
    (z : Fin 3 → muSplit n K) :
    z ∈ (embP ζ hζ.pow_eq_one).range ↔ ∀ i, z i ^ p = 1 := by
  have : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  constructor
  · rintro ⟨f, rfl⟩ i
    show (ζ ^ (toAdd (f i)).val) ^ p = 1
    rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
  · intro h
    have hζK : IsPrimitiveRoot (((ζ : Kˣ) : K)) p := isPrimitiveRoot_coe hζ
    have hex : ∀ i : Fin 3, ∃ k : ℕ, k < p ∧ ((ζ : Kˣ) : K) ^ k = (((z i : muSplit n K) : Kˣ) : K) := by
      intro i
      refine hζK.eq_pow_of_pow_eq_one ?_
      have hi := congrArg (fun u : muSplit n K => ((u : Kˣ) : K)) (h i)
      simpa [Units.val_pow_eq_pow_val] using hi
    refine MonoidHom.mem_range.mpr
      ⟨fun i => Multiplicative.ofAdd (((Classical.choose (hex i) : ℕ)) : ZMod p), ?_⟩
    funext i
    have hspec := Classical.choose_spec (hex i)
    have hk : (Classical.choose (hex i) : ℕ) < p := hspec.1
    have hzk : ((ζ : Kˣ) : K) ^ (Classical.choose (hex i) : ℕ) =
        (((z i : muSplit n K) : Kˣ) : K) := hspec.2
    have hcoe : ∀ m : ℕ,
        (((((ζ : muSplit n K) ^ m : muSplit n K) : Kˣ) : K)) = ((ζ : Kˣ) : K) ^ m := by
      intro m
      rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val]
    apply Subtype.ext
    apply Units.ext
    show ((((((ζ : muSplit n K) ^ (((Classical.choose (hex i) : ℕ) : ZMod p)).val :
      muSplit n K) : Kˣ) : K))) = (((z i : muSplit n K) : Kˣ) : K)
    rw [ZMod.val_natCast_of_lt hk, hcoe (Classical.choose (hex i))]
    exact hzk

theorem hypSmall_embP (h : UnitaryFieldData 2 n K) {F : (Fin 3 → muSplit n K) →* hypSU h 3 0}
    (hF : ∀ z, (((F z : hypSU h 3 0) : GL (HypIndex 3 0) K) :
      Matrix (HypIndex 3 0) (HypIndex 3 0) K) =
        diagonal (torusEntries h (fun i => ((z i : muSplit n K) : Kˣ)) (Fin.elim0)))
    {ζ : muSplit n K} (hζp : ζ ^ p = 1) (f : Fin 3 → Multiplicative (ZMod p)) :
    (((F (embP ζ hζp f) : hypSU h 3 0) : GL (HypIndex 3 0) K) :
      Matrix (HypIndex 3 0) (HypIndex 3 0) K) =
        diagonal (hypEntries ((ζ : Kˣ) : K) (fun i => toAdd (f i))) := by
  have hcoe : ∀ m : ℕ,
      (((((ζ : muSplit n K) ^ m : muSplit n K) : Kˣ) : K)) = ((ζ : Kˣ) : K) ^ m := by
    intro m
    rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val]
  have hbar_pow : ∀ m : ℕ,
      h.bar (((((ζ : muSplit n K) ^ m : muSplit n K) : Kˣ) : K)) = ((ζ : Kˣ) : K) ^ m := by
    intro m
    rw [hcoe m, map_pow, bar_eq_of_mem_muSplit h ζ.2]
  rw [hF]
  congr 1
  funext x
  rcases x with i | k | i
  · show ((((((ζ : muSplit n K) ^ (toAdd (f i)).val : muSplit n K) : Kˣ) : K))) =
      ((ζ : Kˣ) : K) ^ (toAdd (f i)).val
    rw [hcoe]
  · exact k.elim0
  · show (h.bar (((((ζ : muSplit n K) ^ (toAdd (f i)).val : muSplit n K) : Kˣ) : K)))⁻¹ =
      (((ζ : Kˣ) : K) ^ (toAdd (f i)).val)⁻¹
    rw [hbar_pow]

end PTorsion

end CFSG.StandardType.RelA5
