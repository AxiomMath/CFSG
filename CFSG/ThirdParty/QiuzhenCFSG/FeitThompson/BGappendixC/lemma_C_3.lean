module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGappendixC.lemma_C_2

namespace CFSG
end CFSG
open CFSG

open scoped Pointwise

noncomputable section

universe u v

variable (p q : ℕ) [Fact p.Prime]

/-- The first norm equation for inversion stability is automatic: if `a ∈ E`,
then `Norm(a⁻¹)=1`. -/
public theorem CFSG.appendixCE_inv_norm_one
    {a : appendixCField p q} (ha : a ∈ appendixCE p q) :
    (Algebra.norm (ZMod p) (S := appendixCField p q)) a⁻¹ = 1 := by
  simp [Algebra.norm_inv, ha.1]

/-- To prove `a⁻¹ ∈ E`, it remains only to prove the second defining norm
equation for `2-a⁻¹`. -/
public theorem CFSG.appendixCE_inv_mem_of_norm_two_sub_inv
    {a : appendixCField p q} (ha : a ∈ appendixCE p q)
    (h2 : (Algebra.norm (ZMod p) (S := appendixCField p q))
      ((2 : appendixCField p q) - a⁻¹) = 1) :
    a⁻¹ ∈ appendixCE p q :=
  ⟨appendixCE_inv_norm_one (p := p) (q := q) ha, h2⟩

/-- Appendix C C.3 Step 4 endpoint induction. If a self-map `T` has odd
order `p`, preserves inversion, and the source calculation proves
`T x⁻¹ ∈ S` for every nontrivial `x ∈ S`, then every nontrivial member of
`S` has its inverse in `S`.

This isolates the final source sentence: from
`(a⁻¹)^{t^3} ∈ E`, iterate the same assertion and use that `t` has order
`p`. -/
public theorem CFSG.appendixC_twisted_inv_mem_of_odd_order
    {F : Type u} [GroupWithZero F] {S : Set F} (T : F → F) {p : ℕ}
    (hTinj : Function.Injective T) (hTone : T 1 = 1)
    (hTinv : ∀ x : F, T x⁻¹ = (T x)⁻¹)
    (hTpow : ∀ x : F, T^[p] x = x)
    (hstep : ∀ {x : F}, x ∈ S → x ≠ 1 → T x⁻¹ ∈ S)
    (hpodd : Odd p) {a : F} (ha : a ∈ S) (ha1 : a ≠ 1) :
    a⁻¹ ∈ S := by
  rcases hpodd with ⟨m, rfl⟩
  have hT_ne_one : ∀ {x : F}, x ≠ 1 → T x ≠ 1 := by
    intro x hx hTx
    apply hx
    exact hTinj (by simpa [hTone] using hTx)
  have hTiter_inv : ∀ n x, T^[n] x⁻¹ = (T^[n] x)⁻¹ := by
    intro n
    induction n with
    | zero =>
        intro x
        simp
    | succ n ih =>
        intro x
        rw [Function.iterate_succ_apply']
        rw [Function.iterate_succ_apply']
        rw [ih]
        exact hTinv ((T^[n]) x)
  have hTiter_ne_one : ∀ n {x : F}, x ≠ 1 → T^[n] x ≠ 1 := by
    intro n
    induction n with
    | zero =>
        intro x hx
        simpa using hx
    | succ n ih =>
        intro x hx
        rw [Function.iterate_succ_apply']
        exact hT_ne_one (ih hx)
  have h_even_odd : ∀ n : ℕ,
      (T^[2 * n]) a ∈ S ∧ (T^[2 * n + 1]) a⁻¹ ∈ S := by
    intro n
    induction n with
    | zero =>
        constructor
        · simpa using ha
        · simpa using hstep ha ha1
    | succ n ih =>
        rcases ih with ⟨h_even, h_odd⟩
        have h_even_next : (T^[2 * (n + 1)]) a ∈ S := by
          have hne_odd : (T^[2 * n + 1]) a⁻¹ ≠ 1 := by
            have hainv_ne : a⁻¹ ≠ 1 := by
              intro h
              apply ha1
              simpa using congrArg Inv.inv h
            exact hTiter_ne_one (2 * n + 1) hainv_ne
          have hnext := hstep h_odd hne_odd
          have hrewrite :
              T ((T^[2 * n + 1]) a⁻¹)⁻¹ = (T^[2 * (n + 1)]) a := by
            calc
              T ((T^[2 * n + 1]) a⁻¹)⁻¹
                  = T (((T^[2 * n + 1]) a)⁻¹)⁻¹ := by
                    rw [hTiter_inv (2 * n + 1) a]
              _ = T ((T^[2 * n + 1]) a) := by
                    rw [inv_inv]
              _ = (T^[(2 * n + 1).succ]) a := by
                    exact (Function.iterate_succ_apply' T (2 * n + 1) a).symm
              _ = (T^[2 * (n + 1)]) a := by
                    have hnat : (2 * n + 1).succ = 2 * (n + 1) := by omega
                    rw [hnat]
          rw [hrewrite] at hnext
          exact hnext
        have h_odd_next : (T^[2 * (n + 1) + 1]) a⁻¹ ∈ S := by
          have hne_even : (T^[2 * (n + 1)]) a ≠ 1 :=
            hTiter_ne_one (2 * (n + 1)) ha1
          have hnext := hstep h_even_next hne_even
          have hrewrite :
              T ((T^[2 * (n + 1)]) a)⁻¹ =
                (T^[2 * (n + 1) + 1]) a⁻¹ := by
            calc
              T ((T^[2 * (n + 1)]) a)⁻¹
                  = T ((T^[2 * (n + 1)]) a⁻¹) := by
                    rw [hTiter_inv (2 * (n + 1)) a]
              _ = (T^[(2 * (n + 1)).succ]) a⁻¹ := by
                    exact (Function.iterate_succ_apply' T (2 * (n + 1)) a⁻¹).symm
              _ = (T^[2 * (n + 1) + 1]) a⁻¹ := by
                    have hnat :
                        (2 * (n + 1)).succ = 2 * (n + 1) + 1 := by omega
                    rw [hnat]
          rw [hrewrite] at hnext
          exact hnext
        exact ⟨h_even_next, h_odd_next⟩
  have hodd_mem := (h_even_odd m).2
  have hpow : T^[2 * m + 1] a⁻¹ = a⁻¹ := hTpow a⁻¹
  rw [hpow] at hodd_mem
  exact hodd_mem

/-- The remaining data needed from Appendix C Lemma C.3, Step 4 after the
long product calculation. The map `T` is the action induced by conjugation by
the source element `t^3`; the product calculation proves the one-step closure
`T x⁻¹ ∈ E`, and the already-proved odd-order induction turns this into
ordinary inverse-closure. -/
@[expose] public def CFSG.appendixC_lemma_C_3_twisted_step_data : Prop :=
  ∃ T : appendixCField p q → appendixCField p q,
    Function.Injective T ∧
      T 1 = 1 ∧
      (∀ x : appendixCField p q, T x⁻¹ = (T x)⁻¹) ∧
      (∀ x : appendixCField p q, T^[p] x = x) ∧
      ∀ {x : appendixCField p q}, x ∈ appendixCE p q → x ≠ 1 →
        T x⁻¹ ∈ appendixCE p q

/-- The map-theoretic part of the C.3 Step 4 twisted action. This separates
the formal properties of the conjugation-induced map from the hard product
calculation proving one-step closure of `E`. -/
@[expose] public def CFSG.appendixC_lemma_C_3_twisted_map_data
    (T : appendixCField p q → appendixCField p q) : Prop :=
  Function.Injective T ∧
    T 1 = 1 ∧
    (∀ x : appendixCField p q, T x⁻¹ = (T x)⁻¹) ∧
    ∀ x : appendixCField p q, T^[p] x = x

/-- The product-calculation part of the C.3 Step 4 twisted action. -/
@[expose] public def CFSG.appendixC_lemma_C_3_twisted_closure
    (T : appendixCField p q → appendixCField p q) : Prop :=
  ∀ {x : appendixCField p q}, x ∈ appendixCE p q → x ≠ 1 →
    T x⁻¹ ∈ appendixCE p q

/-- Assemble the C.3 Step 4 data from the map action and the one-step closure
proved by the source product calculation. -/
public theorem CFSG.appendixC_lemma_C_3_twisted_step_data_of_map_data
    {T : appendixCField p q → appendixCField p q}
    (hT : appendixC_lemma_C_3_twisted_map_data (p := p) (q := q) T)
    (hclosure : appendixC_lemma_C_3_twisted_closure (p := p) (q := q) T) :
    appendixC_lemma_C_3_twisted_step_data p q := by
  rcases hT with ⟨hTinj, hTone, hTinv, hTpow⟩
  exact ⟨T, hTinj, hTone, hTinv, hTpow, hclosure⟩


/-- Extend a multiplicative equivalence of the norm-one subgroup `U` to the
field by using it on nonzero elements of `U`, fixing `0`, and fixing nonzero
elements outside `U`. This is tailored to the C.3 action induced by
conjugation on the embedded copy of `U`. -/
@[expose] public def CFSG.appendixCFieldMapOfNormOneUnitsMulEquiv
    (T : appendixCNormOneUnits p q ≃* appendixCNormOneUnits p q) :
    appendixCField p q → appendixCField p q := by
  classical
  exact fun x => if hx : x = 0 then 0 else
    if hU : Units.mk0 x hx ∈ appendixCNormOneUnits p q then
      (((T ⟨Units.mk0 x hx, hU⟩ : appendixCNormOneUnits p q) :
        (appendixCField p q)ˣ) : appendixCField p q)
    else x

/-- The norm-one extension sends `0` to `0`. -/
public theorem CFSG.appendixCFieldMapOfNormOneUnitsMulEquiv_zero
    (T : appendixCNormOneUnits p q ≃* appendixCNormOneUnits p q) :
    appendixCFieldMapOfNormOneUnitsMulEquiv (p := p) (q := q) T 0 = 0 := by
  classical
  simp [appendixCFieldMapOfNormOneUnitsMulEquiv]

/-- On elements whose associated unit lies in `U`, the norm-one extension is
the underlying value of the supplied equivalence. -/
public theorem CFSG.appendixCFieldMapOfNormOneUnitsMulEquiv_apply_mem
    (T : appendixCNormOneUnits p q ≃* appendixCNormOneUnits p q)
    {x : appendixCField p q} (hx : x ≠ 0)
    (hU : Units.mk0 x hx ∈ appendixCNormOneUnits p q) :
    appendixCFieldMapOfNormOneUnitsMulEquiv (p := p) (q := q) T x =
      (((T ⟨Units.mk0 x hx, hU⟩ : appendixCNormOneUnits p q) :
        (appendixCField p q)ˣ) : appendixCField p q) := by
  classical
  simp [appendixCFieldMapOfNormOneUnitsMulEquiv, hx, hU]

/-- On nonzero elements outside `U`, the norm-one extension is the identity. -/
public theorem CFSG.appendixCFieldMapOfNormOneUnitsMulEquiv_apply_not_mem
    (T : appendixCNormOneUnits p q ≃* appendixCNormOneUnits p q)
    {x : appendixCField p q} (hx : x ≠ 0)
    (hU : ¬ Units.mk0 x hx ∈ appendixCNormOneUnits p q) :
    appendixCFieldMapOfNormOneUnitsMulEquiv (p := p) (q := q) T x = x := by
  classical
  simp [appendixCFieldMapOfNormOneUnitsMulEquiv, hx, hU]

/-- The norm-one extension is injective. -/
public theorem CFSG.appendixCFieldMapOfNormOneUnitsMulEquiv_injective
    (T : appendixCNormOneUnits p q ≃* appendixCNormOneUnits p q) :
    Function.Injective (appendixCFieldMapOfNormOneUnitsMulEquiv
      (p := p) (q := q) T) := by
  classical
  intro x y hxy
  by_cases hx0 : x = 0
  · subst x
    by_cases hy0 : y = 0
    · exact hy0.symm
    · have hyT_nonzero :
        appendixCFieldMapOfNormOneUnitsMulEquiv (p := p) (q := q) T y ≠ 0 := by
        by_cases hyU : Units.mk0 y hy0 ∈ appendixCNormOneUnits p q
        · rw [appendixCFieldMapOfNormOneUnitsMulEquiv_apply_mem
            (p := p) (q := q) T hy0 hyU]
          exact Units.ne_zero _
        · rw [appendixCFieldMapOfNormOneUnitsMulEquiv_apply_not_mem
            (p := p) (q := q) T hy0 hyU]
          exact hy0
      exact False.elim (hyT_nonzero (by
        simpa [appendixCFieldMapOfNormOneUnitsMulEquiv_zero] using hxy.symm))
  · by_cases hy0 : y = 0
    · subst y
      have hxT_nonzero :
        appendixCFieldMapOfNormOneUnitsMulEquiv (p := p) (q := q) T x ≠ 0 := by
        by_cases hxU : Units.mk0 x hx0 ∈ appendixCNormOneUnits p q
        · rw [appendixCFieldMapOfNormOneUnitsMulEquiv_apply_mem
            (p := p) (q := q) T hx0 hxU]
          exact Units.ne_zero _
        · rw [appendixCFieldMapOfNormOneUnitsMulEquiv_apply_not_mem
            (p := p) (q := q) T hx0 hxU]
          exact hx0
      exact False.elim (hxT_nonzero (by
        simpa [appendixCFieldMapOfNormOneUnitsMulEquiv_zero] using hxy))
    · by_cases hxU : Units.mk0 x hx0 ∈ appendixCNormOneUnits p q
      · by_cases hyU : Units.mk0 y hy0 ∈ appendixCNormOneUnits p q
        · rw [appendixCFieldMapOfNormOneUnitsMulEquiv_apply_mem
            (p := p) (q := q) T hx0 hxU] at hxy
          rw [appendixCFieldMapOfNormOneUnitsMulEquiv_apply_mem
            (p := p) (q := q) T hy0 hyU] at hxy
          have hunit :
              T ⟨Units.mk0 x hx0, hxU⟩ = T ⟨Units.mk0 y hy0, hyU⟩ := by
            apply Subtype.ext
            apply Units.ext
            exact hxy
          have hpre := T.injective hunit
          have hval := congrArg (fun u : appendixCNormOneUnits p q =>
            ((u : (appendixCField p q)ˣ) : appendixCField p q)) hpre
          simpa using hval
        · rw [appendixCFieldMapOfNormOneUnitsMulEquiv_apply_mem
            (p := p) (q := q) T hx0 hxU] at hxy
          rw [appendixCFieldMapOfNormOneUnitsMulEquiv_apply_not_mem
            (p := p) (q := q) T hy0 hyU] at hxy
          have hyU' : Units.mk0 y hy0 ∈ appendixCNormOneUnits p q := by
            have hunit : Units.mk0 y hy0 =
                ((T ⟨Units.mk0 x hx0, hxU⟩ : appendixCNormOneUnits p q) :
                  (appendixCField p q)ˣ) := by
              apply Units.ext
              exact hxy.symm
            rw [hunit]
            exact (T ⟨Units.mk0 x hx0, hxU⟩).property
          exact False.elim (hyU hyU')
      · by_cases hyU : Units.mk0 y hy0 ∈ appendixCNormOneUnits p q
        · rw [appendixCFieldMapOfNormOneUnitsMulEquiv_apply_not_mem
            (p := p) (q := q) T hx0 hxU] at hxy
          rw [appendixCFieldMapOfNormOneUnitsMulEquiv_apply_mem
            (p := p) (q := q) T hy0 hyU] at hxy
          have hxU' : Units.mk0 x hx0 ∈ appendixCNormOneUnits p q := by
            have hunit : Units.mk0 x hx0 =
                ((T ⟨Units.mk0 y hy0, hyU⟩ : appendixCNormOneUnits p q) :
                  (appendixCField p q)ˣ) := by
              apply Units.ext
              exact hxy
            rw [hunit]
            exact (T ⟨Units.mk0 y hy0, hyU⟩).property
          exact False.elim (hxU hxU')
        · rw [appendixCFieldMapOfNormOneUnitsMulEquiv_apply_not_mem
            (p := p) (q := q) T hx0 hxU] at hxy
          rw [appendixCFieldMapOfNormOneUnitsMulEquiv_apply_not_mem
            (p := p) (q := q) T hy0 hyU] at hxy
          exact hxy

/-- The norm-one extension fixes `1`. -/
public theorem CFSG.appendixCFieldMapOfNormOneUnitsMulEquiv_one
    (T : appendixCNormOneUnits p q ≃* appendixCNormOneUnits p q) :
    appendixCFieldMapOfNormOneUnitsMulEquiv (p := p) (q := q) T 1 = 1 := by
  have hU : Units.mk0 (1 : appendixCField p q) one_ne_zero ∈
      appendixCNormOneUnits p q := by
    simp
  rw [appendixCFieldMapOfNormOneUnitsMulEquiv_apply_mem
    (p := p) (q := q) T one_ne_zero hU]
  simp

/-- The norm-one extension commutes with inversion. -/
public theorem CFSG.appendixCFieldMapOfNormOneUnitsMulEquiv_inv
    (T : appendixCNormOneUnits p q ≃* appendixCNormOneUnits p q)
    (x : appendixCField p q) :
    appendixCFieldMapOfNormOneUnitsMulEquiv (p := p) (q := q) T x⁻¹ =
      (appendixCFieldMapOfNormOneUnitsMulEquiv (p := p) (q := q) T x)⁻¹ := by
  by_cases hx0 : x = 0
  · subst x
    simp [appendixCFieldMapOfNormOneUnitsMulEquiv_zero]
  · have hxinv0 : x⁻¹ ≠ 0 := inv_ne_zero hx0
    by_cases hxU : Units.mk0 x hx0 ∈ appendixCNormOneUnits p q
    · have hxinvU : Units.mk0 x⁻¹ hxinv0 ∈ appendixCNormOneUnits p q := by
        have hunit : Units.mk0 x⁻¹ hxinv0 = (Units.mk0 x hx0)⁻¹ := by
          ext
          simp
        rw [hunit]
        exact (appendixCNormOneUnits p q).inv_mem hxU
      rw [appendixCFieldMapOfNormOneUnitsMulEquiv_apply_mem
        (p := p) (q := q) T hx0 hxU]
      rw [appendixCFieldMapOfNormOneUnitsMulEquiv_apply_mem
        (p := p) (q := q) T hxinv0 hxinvU]
      have hunit : Units.mk0 x⁻¹ hxinv0 = (Units.mk0 x hx0)⁻¹ := by
        ext
        simp
      have hsub : (⟨Units.mk0 x⁻¹ hxinv0, hxinvU⟩ :
          appendixCNormOneUnits p q) =
          (⟨Units.mk0 x hx0, hxU⟩ : appendixCNormOneUnits p q)⁻¹ := by
        apply Subtype.ext
        exact hunit
      rw [hsub, map_inv]
      simp
    · have hxinvU : ¬ Units.mk0 x⁻¹ hxinv0 ∈ appendixCNormOneUnits p q := by
        intro h
        apply hxU
        have hunit : Units.mk0 x hx0 = (Units.mk0 x⁻¹ hxinv0)⁻¹ := by
          ext
          simp
        rw [hunit]
        exact (appendixCNormOneUnits p q).inv_mem h
      rw [appendixCFieldMapOfNormOneUnitsMulEquiv_apply_not_mem
        (p := p) (q := q) T hx0 hxU]
      rw [appendixCFieldMapOfNormOneUnitsMulEquiv_apply_not_mem
        (p := p) (q := q) T hxinv0 hxinvU]

/-- Iterates of the norm-one extension on a point of `U` are the corresponding
iterates of the subgroup equivalence. -/
public theorem CFSG.appendixCFieldMapOfNormOneUnitsMulEquiv_iterate_mem
    (T : appendixCNormOneUnits p q ≃* appendixCNormOneUnits p q)
    {x : appendixCField p q} (hx : x ≠ 0)
    (hU : Units.mk0 x hx ∈ appendixCNormOneUnits p q) :
    ∀ n : ℕ,
      (appendixCFieldMapOfNormOneUnitsMulEquiv (p := p) (q := q) T)^[n] x =
        ((((T : appendixCNormOneUnits p q → appendixCNormOneUnits p q)^[n])
          ⟨Units.mk0 x hx, hU⟩ : appendixCNormOneUnits p q) :
            (appendixCField p q)ˣ) := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      rw [ih]
      let un : appendixCNormOneUnits p q :=
        (((T : appendixCNormOneUnits p q → appendixCNormOneUnits p q)^[n])
          ⟨Units.mk0 x hx, hU⟩)
      have hne :
          (((un : (appendixCField p q)ˣ) : appendixCField p q)) ≠ 0 :=
        Units.ne_zero _
      have hmem : Units.mk0
          (((un : (appendixCField p q)ˣ) : appendixCField p q)) hne ∈
            appendixCNormOneUnits p q := by
        have hunit : Units.mk0
            (((un : (appendixCField p q)ˣ) : appendixCField p q)) hne =
              (un : (appendixCField p q)ˣ) := by
          ext
          simp
        rw [hunit]
        exact un.property
      rw [appendixCFieldMapOfNormOneUnitsMulEquiv_apply_mem
        (p := p) (q := q) T hne hmem]
      have hunit : (⟨Units.mk0
          (((un : (appendixCField p q)ˣ) : appendixCField p q)) hne, hmem⟩ :
            appendixCNormOneUnits p q) = un := by
        apply Subtype.ext
        ext
        simp
      rw [hunit]
      exact congrArg (fun u : appendixCNormOneUnits p q =>
          ((u : (appendixCField p q)ˣ) : appendixCField p q))
        (Function.iterate_succ_apply'
          (T : appendixCNormOneUnits p q → appendixCNormOneUnits p q) n
          ⟨Units.mk0 x hx, hU⟩).symm

/-- Iterates of the norm-one extension are the identity on nonzero points
outside `U`. -/
public theorem CFSG.appendixCFieldMapOfNormOneUnitsMulEquiv_iterate_not_mem
    (T : appendixCNormOneUnits p q ≃* appendixCNormOneUnits p q)
    {x : appendixCField p q} (hx : x ≠ 0)
    (hU : ¬ Units.mk0 x hx ∈ appendixCNormOneUnits p q) :
    ∀ n : ℕ,
      (appendixCFieldMapOfNormOneUnitsMulEquiv (p := p) (q := q) T)^[n] x =
        x := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      rw [ih]
      rw [appendixCFieldMapOfNormOneUnitsMulEquiv_apply_not_mem
        (p := p) (q := q) T hx hU]

/-- If the norm-one equivalence has `p`th iterate equal to the identity, so
does its field extension. -/
public theorem CFSG.appendixCFieldMapOfNormOneUnitsMulEquiv_pow
    (T : appendixCNormOneUnits p q ≃* appendixCNormOneUnits p q)
    (hpow : ∀ u : appendixCNormOneUnits p q,
      (T : appendixCNormOneUnits p q → appendixCNormOneUnits p q)^[p] u = u)
    (x : appendixCField p q) :
    (appendixCFieldMapOfNormOneUnitsMulEquiv (p := p) (q := q) T)^[p] x =
      x := by
  by_cases hx0 : x = 0
  · subst x
    have hiter_zero : ∀ n : ℕ,
        (appendixCFieldMapOfNormOneUnitsMulEquiv (p := p) (q := q) T)^[n]
          (0 : appendixCField p q) = 0 := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
          rw [Function.iterate_succ_apply']
          simp [ih, appendixCFieldMapOfNormOneUnitsMulEquiv_zero]
    simpa using hiter_zero p
  · by_cases hU : Units.mk0 x hx0 ∈ appendixCNormOneUnits p q
    · rw [appendixCFieldMapOfNormOneUnitsMulEquiv_iterate_mem
        (p := p) (q := q) T hx0 hU]
      simpa using congrArg (fun u : appendixCNormOneUnits p q =>
          ((u : (appendixCField p q)ˣ) : appendixCField p q))
        (hpow ⟨Units.mk0 x hx0, hU⟩)
    · exact appendixCFieldMapOfNormOneUnitsMulEquiv_iterate_not_mem
        (p := p) (q := q) T hx0 hU p

/-- A norm-one subgroup equivalence of order dividing `p`, extended to the
field, supplies the formal map-action half of Appendix C C.3, Step 4. -/
public theorem CFSG.appendixC_lemma_C_3_twisted_map_data_of_normOneUnitsMulEquiv
    (T : appendixCNormOneUnits p q ≃* appendixCNormOneUnits p q)
    (hpow : ∀ u : appendixCNormOneUnits p q,
      (T : appendixCNormOneUnits p q → appendixCNormOneUnits p q)^[p] u = u) :
    appendixC_lemma_C_3_twisted_map_data (p := p) (q := q)
      (appendixCFieldMapOfNormOneUnitsMulEquiv (p := p) (q := q) T) := by
  exact ⟨appendixCFieldMapOfNormOneUnitsMulEquiv_injective
      (p := p) (q := q) T,
    appendixCFieldMapOfNormOneUnitsMulEquiv_one (p := p) (q := q) T,
    appendixCFieldMapOfNormOneUnitsMulEquiv_inv (p := p) (q := q) T,
    appendixCFieldMapOfNormOneUnitsMulEquiv_pow (p := p) (q := q) T hpow⟩

/-- Closure for the zero-extension of a norm-one subgroup equivalence can be
proved directly on the norm-one unit attached to `x⁻¹`. This keeps the source
Step 4 product calculation inside `U`, where the conjugation action actually
lives. -/
public theorem CFSG.appendixC_lemma_C_3_twisted_closure_of_normOneUnitsMulEquiv
    (T : appendixCNormOneUnits p q ≃* appendixCNormOneUnits p q)
    (hclosure : ∀ {x : appendixCField p q} (hx : x ∈ appendixCE p q),
      x ≠ 1 →
      (((T ⟨Units.mk0 x⁻¹
          (inv_ne_zero (appendixCE_ne_zero (p := p) (q := q) hx)),
        appendixCE_inv_unit_mem_normOneUnits (p := p) (q := q) hx⟩ :
        appendixCNormOneUnits p q) : (appendixCField p q)ˣ) :
        appendixCField p q) ∈ appendixCE p q) :
    appendixC_lemma_C_3_twisted_closure (p := p) (q := q)
      (appendixCFieldMapOfNormOneUnitsMulEquiv (p := p) (q := q) T) := by
  intro x hx hx1
  have hx0 : x ≠ 0 := appendixCE_ne_zero (p := p) (q := q) hx
  have hxinv0 : x⁻¹ ≠ 0 := inv_ne_zero hx0
  have hxinvU : Units.mk0 x⁻¹ hxinv0 ∈ appendixCNormOneUnits p q :=
    appendixCE_inv_unit_mem_normOneUnits (p := p) (q := q) hx
  rw [appendixCFieldMapOfNormOneUnitsMulEquiv_apply_mem
    (p := p) (q := q) T hxinv0 hxinvU]
  simpa using hclosure hx hx1

/-- If `v ∈ U` satisfies `v + z = 2` in the field, then the companion
`2 - z` is the same norm-one unit. This is the final field-level conversion
used after the Step 4 product calculation identifies `v_1 = 2 - z`. -/
public theorem CFSG.appendixCNormOneUnits_two_sub_mem_of_add_eq
    {z : appendixCField p q} (v : appendixCNormOneUnits p q)
    (hadd : (((v : appendixCNormOneUnits p q) : (appendixCField p q)ˣ) :
      appendixCField p q) + z = 2) :
    ∃ h2z : (2 : appendixCField p q) - z ≠ 0,
      Units.mk0 ((2 : appendixCField p q) - z) h2z ∈
        appendixCNormOneUnits p q := by
  have htwo_sub :
      (2 : appendixCField p q) - z =
        (((v : appendixCNormOneUnits p q) : (appendixCField p q)ˣ) :
          appendixCField p q) := by
    rw [← hadd]
    ring
  have h2z : (2 : appendixCField p q) - z ≠ 0 := by
    rw [htwo_sub]
    exact Units.ne_zero ((v : appendixCNormOneUnits p q) :
      (appendixCField p q)ˣ)
  refine ⟨h2z, ?_⟩
  have hunit : Units.mk0 ((2 : appendixCField p q) - z) h2z =
      ((v : appendixCNormOneUnits p q) : (appendixCField p q)ˣ) := by
    ext
    simp [htwo_sub]
  simp [hunit]

/-- Endpoint form of the C.3 Step 4 induction using a fixed twisted action. -/
public theorem CFSG.appendixC_lemma_C_3_inv_mem_of_twisted_map_data
    {T : appendixCField p q → appendixCField p q}
    (hT : appendixC_lemma_C_3_twisted_map_data (p := p) (q := q) T)
    (hclosure : appendixC_lemma_C_3_twisted_closure (p := p) (q := q) T)
    (hoddp : Odd p)
    {a : appendixCField p q} (ha : a ∈ appendixCE p q) (ha1 : a ≠ 1) :
    a⁻¹ ∈ appendixCE p q := by
  rcases hT with ⟨hTinj, hTone, hTinv, hTpow⟩
  exact appendixC_twisted_inv_mem_of_odd_order
    (S := appendixCE p q) T hTinj hTone hTinv hTpow hclosure hoddp ha ha1

/-- The odd-order endpoint of Appendix C Lemma C.3, Step 4: once the source
product calculation has supplied the twisted one-step closure, every
nontrivial element of `E` has its inverse in `E`. -/
public theorem CFSG.appendixC_lemma_C_3_inv_mem_of_twisted_step_data
    (hTdata : appendixC_lemma_C_3_twisted_step_data p q)
    (hoddp : Odd p)
    {a : appendixCField p q} (ha : a ∈ appendixCE p q) (ha1 : a ≠ 1) :
    a⁻¹ ∈ appendixCE p q := by
  rcases hTdata with ⟨T, hTinj, hTone, hTinv, hTpow, hstep⟩
  exact appendixC_lemma_C_3_inv_mem_of_twisted_map_data
    (p := p) (q := q) (T := T) ⟨hTinj, hTone, hTinv, hTpow⟩ hstep
    hoddp ha ha1

/-- A pointwise proof of `Norm(2-a⁻¹)=1` for every `a ∈ E` implies the full
inversion-stability statement `E = E⁻¹`. -/
public theorem CFSG.appendixCInversionStable_of_norm_two_sub_inv
    (h : ∀ a : appendixCField p q, a ∈ appendixCE p q →
      (Algebra.norm (ZMod p) (S := appendixCField p q))
        ((2 : appendixCField p q) - a⁻¹) = 1) :
    appendixCInversionStable p q (appendixCE p q) := by
  intro a
  constructor
  · intro ha
    exact appendixCE_inv_mem_of_norm_two_sub_inv (p := p) (q := q) ha (h a ha)
  · intro ha
    have hback : (a⁻¹)⁻¹ ∈ appendixCE p q :=
      appendixCE_inv_mem_of_norm_two_sub_inv (p := p) (q := q) ha (h a⁻¹ ha)
    simpa using hback


set_option maxHeartbeats 800000 in
/-- Right-route value form of the remaining source product calculation in
Appendix C Lemma C.3, Step 4. For the inverse normalizer-induced action, the
source equations C2--C10 produce a norm-one unit `v` with
`v + (T^{-3}(2 - x))⁻¹ = 2`. The companion-unit theorem below applies this
with `t⁻¹` and `2 - x` to recover the forward-action endpoint. -/
public theorem CFSG.appendixC_lemma_C_3_twisted_companion_value_of_conditionB_action
    [Fact q.Prime]
    (hA : appendixCConditionA p q) (hoddp : Odd p) (_hoddq : Odd q)
    (_hp3 : p ≠ 3)
    {G : Type u} [Group G] (σ : appendixCH p q →* G)
    (hσ : Function.Injective σ)
    (Q : Subgroup G) [Finite Q] [IsMulCommutative Q]
    (hcop : Nat.Coprime p (Nat.card Q))
    {y t : G} (hy : y ∈ Q)
    (hP0Q : appendixCNormalizes (Subgroup.map σ (appendixCP0InH p q)) Q)
    (hfixed :
      let P0img : Subgroup G := Subgroup.map σ (appendixCP0InH p q)
      let φ : P0img →* MulAut Q :=
        Q.normalizerMonoidHom.comp (Subgroup.inclusion hP0Q)
      letI : MulDistribMulAction P0img Q := MulDistribMulAction.compHom Q φ
      fixedPointSubgroup P0img Q ⊓ commutatorAction (A := P0img) (G := Q) = ⊥)
    (hycomm :
      let P0img : Subgroup G := Subgroup.map σ (appendixCP0InH p q)
      let φ : P0img →* MulAut Q :=
        Q.normalizerMonoidHom.comp (Subgroup.inclusion hP0Q)
      letI : MulDistribMulAction P0img Q := MulDistribMulAction.compHom Q φ
      (⟨y, hy⟩ : Q) ∈ commutatorAction (A := P0img) (G := Q))
    (hP1U :
      appendixCNormalizes
        (appendixCRightConjugate (Subgroup.map σ (appendixCP0InH p q)) y)
        (Subgroup.map σ (appendixCUInH p q)))
    (ht : t ∈ appendixCRightConjugate
      (Subgroup.map σ (appendixCP0InH p q)) y)
    (htne : t ≠ 1) :
    let TunitInv : appendixCNormOneUnits p q ≃* appendixCNormOneUnits p q :=
      appendixCEmbedding_conjNormOneUnitsMulEquiv (p := p) (q := q)
        σ hσ
        ((Subgroup.normalizer
          (Subgroup.map σ (appendixCUInH p q) : Set G)).inv_mem (hP1U ht))
    ∀ {x : appendixCField p q} (hx : x ∈ appendixCE p q), x ≠ 1 →
      ∃ v : appendixCNormOneUnits p q,
        (((v : appendixCNormOneUnits p q) : (appendixCField p q)ˣ) :
          appendixCField p q) +
          ((((((TunitInv : appendixCNormOneUnits p q →
                    appendixCNormOneUnits p q)^[3])
              ⟨Units.mk0 ((2 : appendixCField p q) - x)
                (appendixCE_two_sub_ne_zero (p := p) (q := q) hx),
                appendixCE_two_sub_unit_mem_normOneUnits
                  (p := p) (q := q) hx⟩)⁻¹ :
            appendixCNormOneUnits p q) : (appendixCField p q)ˣ) :
            appendixCField p q) = 2 := by
  dsimp only
  intro x hx hx1
  let P0img : Subgroup G := Subgroup.map σ (appendixCP0InH p q)
  let Uimg : Subgroup G := Subgroup.map σ (appendixCUInH p q)
  let Himg : Subgroup G := Subgroup.map σ (⊤ : Subgroup (appendixCH p q))
  rcases (appendixCRightConjugate_mem_iff P0img y t).1 (by
      simpa [P0img] using ht) with
    ⟨s, hs, ht_eq⟩
  have hsne : s ≠ 1 := by
    intro hs1
    apply htne
    simp [ht_eq, hs1]
  have hs_norm_Q : s ∈ Subgroup.normalizer (Q : Set G) := by
    simpa [P0img] using hP0Q hs
  have q_comm {a b : G} (ha : a ∈ Q) (hb : b ∈ Q) : a * b = b * a := by
    simpa using congrArg Subtype.val
      ((IsMulCommutative.is_comm (M := Q)).comm (⟨a, ha⟩ : Q) (⟨b, hb⟩ : Q))
  have hq_sinv_t : s⁻¹ * t ∈ Q := by
    rw [ht_eq]
    have hsinv_norm_Q :
        s⁻¹ ∈ Subgroup.normalizer (Q : Set G) :=
      (Subgroup.normalizer (Q : Set G)).inv_mem hs_norm_Q
    have hq : s⁻¹ * y⁻¹ * s ∈ Q := by
      have hq_raw : s⁻¹ * y⁻¹ * (s⁻¹)⁻¹ ∈ Q :=
        (Subgroup.mem_normalizer_iff.mp hsinv_norm_Q y⁻¹).1 (Q.inv_mem hy)
      simpa using hq_raw
    simpa [mul_assoc] using Q.mul_mem hq hy
  have hq_sinv2_t2 : s ^ (-2 : ℤ) * t ^ 2 ∈ Q := by
    have hconj : s⁻¹ * (s⁻¹ * t) * s ∈ Q := by
      have hconj_raw : s⁻¹ * (s⁻¹ * t) * (s⁻¹)⁻¹ ∈ Q :=
        (Subgroup.mem_normalizer_iff.mp
          ((Subgroup.normalizer (Q : Set G)).inv_mem hs_norm_Q) (s⁻¹ * t)).1
          hq_sinv_t
      simpa using hconj_raw
    have hmem : s⁻¹ * (s⁻¹ * t) * s * (s⁻¹ * t) ∈ Q :=
      Q.mul_mem hconj hq_sinv_t
    convert hmem using 1
    rw [pow_two]
    group
  have hq_sinv3_t3 : s ^ (-3 : ℤ) * t ^ 3 ∈ Q := by
    have hconj : s⁻¹ * (s ^ (-2 : ℤ) * t ^ 2) * s ∈ Q := by
      have hconj_raw : s⁻¹ * (s ^ (-2 : ℤ) * t ^ 2) * (s⁻¹)⁻¹ ∈ Q :=
        (Subgroup.mem_normalizer_iff.mp
          ((Subgroup.normalizer (Q : Set G)).inv_mem hs_norm_Q)
          (s ^ (-2 : ℤ) * t ^ 2)).1 hq_sinv2_t2
      simpa using hconj_raw
    have hmem : s⁻¹ * (s ^ (-2 : ℤ) * t ^ 2) * s * (s⁻¹ * t) ∈ Q :=
      Q.mul_mem hconj hq_sinv_t
    convert hmem using 1
    rw [pow_succ, pow_two]
    group
  have hq_tinv_s : t⁻¹ * s ∈ Q := by
    simpa using Q.inv_mem hq_sinv_t
  have hq_tinv2_s2 : (t ^ 2)⁻¹ * s ^ 2 ∈ Q := by
    simpa [inv_zpow, zpow_ofNat] using Q.inv_mem hq_sinv2_t2
  have hq_tinv3_s3 : (t ^ 3)⁻¹ * s ^ 3 ∈ Q := by
    simpa [inv_zpow, zpow_ofNat] using Q.inv_mem hq_sinv3_t3
  obtain ⟨sc, hsc_img⟩ :
      ∃ c : ZMod p, s = σ (SemidirectProduct.inl (Multiplicative.ofAdd
        (algebraMap (ZMod p) (appendixCField p q) c) : appendixCP p q)) := by
    rcases hs with ⟨sH, hsH, rfl⟩
    rcases (appendixCP0InH_mem_iff (p := p) (q := q) sH).1 hsH with
      ⟨c, rfl⟩
    exact ⟨c, rfl⟩
  have hsc_ne : sc ≠ 0 := by
    intro hsc0
    apply hsne
    simp [hsc_img, hsc0]
  let Tunit : appendixCNormOneUnits p q ≃* appendixCNormOneUnits p q :=
    appendixCEmbedding_conjNormOneUnitsMulEquiv (p := p) (q := q)
      σ hσ
      ((Subgroup.normalizer
        (Subgroup.map σ (appendixCUInH p q) : Set G)).pow_mem
          (hP1U ht) 3)
  let uinv : appendixCNormOneUnits p q :=
    ⟨Units.mk0 x⁻¹
      (inv_ne_zero (appendixCE_ne_zero (p := p) (q := q) hx)),
      appendixCE_inv_unit_mem_normOneUnits (p := p) (q := q) hx⟩
  let aunit : appendixCNormOneUnits p q :=
    ⟨Units.mk0 x (appendixCE_ne_zero (p := p) (q := q) hx),
      appendixCE_unit_mem_normOneUnits (p := p) (q := q) hx⟩
  let bunit : appendixCNormOneUnits p q :=
    ⟨Units.mk0 ((2 : appendixCField p q) - x)
      (appendixCE_two_sub_ne_zero (p := p) (q := q) hx),
      appendixCE_two_sub_unit_mem_normOneUnits (p := p) (q := q) hx⟩
  let abinv : appendixCNormOneUnits p q :=
    ⟨Units.mk0 (x * ((2 : appendixCField p q) - x)⁻¹)
      (mul_ne_zero (appendixCE_ne_zero (p := p) (q := q) hx)
        (inv_ne_zero (appendixCE_two_sub_ne_zero (p := p) (q := q) hx))),
      appendixCE_mul_inv_two_sub_unit_mem_normOneUnits (p := p) (q := q) hx⟩
  let z : appendixCField p q :=
    (((Tunit uinv : appendixCNormOneUnits p q) : (appendixCField p q)ˣ) :
      appendixCField p q)
  have ha_b_add :
      (((aunit : appendixCNormOneUnits p q) : (appendixCField p q)ˣ) :
          appendixCField p q) +
        (((bunit : appendixCNormOneUnits p q) : (appendixCField p q)ˣ) :
          appendixCField p q) = 2 := by
    dsimp [aunit, bunit]
    ring
  have hC2_sq :
      s ^ 2 =
        (σ (SemidirectProduct.inr aunit) * s *
            (σ (SemidirectProduct.inr aunit))⁻¹) *
          (σ (SemidirectProduct.inr bunit) * s *
            (σ (SemidirectProduct.inr bunit))⁻¹) := by
    simpa [hsc_img] using
      appendixCEmbedding_CP0_conj_normOneUnits_sq_eq_mul_of_add_eq_two
        (p := p) (q := q) σ (c := sc) aunit bunit ha_b_add
  have haunit_inv_eq_uinv : aunit⁻¹ = uinv := by
    ext
    simp [aunit, uinv]
  have hbunit_inv_mul_aunit_eq_abinv : bunit⁻¹ * aunit = abinv := by
    ext
    simp [aunit, bunit, abinv, mul_comm]
  have hC2_cyclic :
      s * σ (SemidirectProduct.inr uinv) * s ^ (-2 : ℤ) *
          σ (SemidirectProduct.inr bunit) * s *
          σ (SemidirectProduct.inr abinv) = 1 := by
    have hba_add :
        (((bunit : appendixCNormOneUnits p q) : (appendixCField p q)ˣ) :
            appendixCField p q) +
          (((aunit : appendixCNormOneUnits p q) : (appendixCField p q)ˣ) :
            appendixCField p q) = 2 := by
      simpa [add_comm] using ha_b_add
    simpa [hsc_img, haunit_inv_eq_uinv, hbunit_inv_mul_aunit_eq_abinv,
      mul_assoc] using
      appendixCEmbedding_CP0_conj_normOneUnits_C2_cyclic_product_of_add_eq_two
        (p := p) (q := q) σ (c := sc) bunit aunit hba_add
  have hC4_right_conj_source :
      t ^ 2 *
          (s * (t ^ (-3 : ℤ) * σ (SemidirectProduct.inr bunit) * t ^ 3) *
            s ^ (-2 : ℤ)) *
        t⁻¹ *
          (s ^ 3 *
            (t ^ (-2 : ℤ) * σ (SemidirectProduct.inr (bunit⁻¹ * aunit)) *
              t ^ 2) *
            s ^ (-1 : ℤ)) *
        t⁻¹ *
          (s ^ 2 * (t⁻¹ * σ (SemidirectProduct.inr aunit⁻¹) * t) *
            s ^ (-3 : ℤ)) = 1 := by
    have hba_add :
        (((bunit : appendixCNormOneUnits p q) : (appendixCField p q)ˣ) :
            appendixCField p q) +
          (((aunit : appendixCNormOneUnits p q) : (appendixCField p q)ˣ) :
            appendixCField p q) = 2 := by
      simpa [add_comm] using ha_b_add
    exact appendixCEmbedding_CP0_conj_normOneUnits_C4_right_conj_of_add_eq_two
      (p := p) (q := q) σ (s := s) (t := t) (c := sc) hsc_img
      bunit aunit hba_add
      (q_comm hq_sinv_t hq_sinv2_t2)
      (q_comm hq_sinv_t hq_sinv3_t3)
      (q_comm hq_sinv2_t2 hq_sinv3_t3)
  have hC4_right_conj_source_pow :
      t ^ 2 *
          (s * (t ^ (-3 : ℤ) * σ (SemidirectProduct.inr (bunit ^ p)) * t ^ 3) *
            s ^ (-2 : ℤ)) *
        t⁻¹ *
          (s ^ 3 *
            (t ^ (-2 : ℤ) * σ (SemidirectProduct.inr (abinv ^ p)) *
              t ^ 2) *
            s ^ (-1 : ℤ)) *
        t⁻¹ *
          (s ^ 2 * (t⁻¹ * σ (SemidirectProduct.inr (uinv ^ p)) * t) *
            s ^ (-3 : ℤ)) = 1 := by
    have hba_add :
        (((bunit : appendixCNormOneUnits p q) : (appendixCField p q)ˣ) :
            appendixCField p q) +
          (((aunit : appendixCNormOneUnits p q) : (appendixCField p q)ˣ) :
            appendixCField p q) = 2 := by
      simpa [add_comm] using ha_b_add
    have hpow :=
      appendixCEmbedding_CP0_conj_normOneUnits_C4_right_conj_pow_of_add_eq_two
        (p := p) (q := q) σ (s := s) (t := t) (c := sc) hsc_img
        bunit aunit hba_add
        (q_comm hq_sinv_t hq_sinv2_t2)
        (q_comm hq_sinv_t hq_sinv3_t3)
        (q_comm hq_sinv2_t2 hq_sinv3_t3)
    simpa [haunit_inv_eq_uinv, ← hbunit_inv_mul_aunit_eq_abinv, mul_pow]
      using hpow
  have hz_conj :
      σ (SemidirectProduct.inr (Tunit uinv)) =
        t ^ 3 * σ (SemidirectProduct.inr uinv) * (t ^ 3)⁻¹ := by
    simpa [Tunit, Uimg, uinv] using
      appendixCEmbedding_conjNormOneUnitsMulEquiv_apply
        (p := p) (q := q) σ hσ
      ((Subgroup.normalizer
        (Subgroup.map σ (appendixCUInH p q) : Set G)).pow_mem
          (hP1U ht) 3)
      uinv
  have hStep3_t2 :
      Himg ⊓ Himg.conjBy (t ^ 2) = Uimg := by
    simpa [Himg, Uimg, P0img] using
      appendixCEmbedding_H_inf_conjBy_sq_eq_CUInH_of_mem_rightConjugate_ne_one
        (p := p) (q := q) hA hoddp σ hσ Q hcop hy hP0Q hP1U hx hx1 ht htne
  have huinv_img : σ (SemidirectProduct.inr uinv) ∈ Uimg := by
    exact ⟨SemidirectProduct.inr uinv,
      (appendixCUInH_mem_iff (p := p) (q := q) _).2 ⟨uinv, rfl⟩, rfl⟩
  have hbunit_img : σ (SemidirectProduct.inr bunit) ∈ Uimg := by
    exact ⟨SemidirectProduct.inr bunit,
      (appendixCUInH_mem_iff (p := p) (q := q) _).2 ⟨bunit, rfl⟩, rfl⟩
  have habinv_img : σ (SemidirectProduct.inr abinv) ∈ Uimg := by
    exact ⟨SemidirectProduct.inr abinv,
      (appendixCUInH_mem_iff (p := p) (q := q) _).2 ⟨abinv, rfl⟩, rfl⟩
  have ht_inv_right :
      t⁻¹ ∈ appendixCRightConjugate
        (Subgroup.map σ (appendixCP0InH p q)) y :=
    (appendixCRightConjugate
      (Subgroup.map σ (appendixCP0InH p q)) y).inv_mem ht
  rcases appendixC_lemma_C_3_step4_C5_decompositions
      (p := p) (q := q) hA σ hP1U ht_inv_right hs
        hbunit_img habinv_img huinv_img 3 with
    ⟨ru1, rhu1, rs1, rhs1, rv1img, rhv1img,
      ru2, rhu2, rs2, rhs2, rv2img, rhv2img,
      ru3, rhu3, rs3, rhs3, rv3img, rhv3img,
      hC5r_1_raw, hC5r_2_raw, hC5r_3_raw⟩
  have hC5r_1 :
      s * (t ^ (-3 : ℤ) * σ (SemidirectProduct.inr bunit) * t ^ 3) *
          s ^ (-2 : ℤ) =
        ru1 * rs1 * rv1img := by
    convert hC5r_1_raw using 1
    group
  have hC5r_2 :
      s ^ 3 * (t ^ (-2 : ℤ) * σ (SemidirectProduct.inr abinv) * t ^ 2) *
          s ^ (-1 : ℤ) =
        ru2 * rs2 * rv2img := by
    convert hC5r_2_raw using 1
    group
  have hC5r_3 :
      s ^ 2 * (t⁻¹ * σ (SemidirectProduct.inr uinv) * t) *
          s ^ (-3 : ℤ) =
        ru3 * rs3 * rv3img := by
    convert hC5r_3_raw using 1
    group
  have hprod_right_conj :
      t ^ 2 * (ru1 * rs1 * rv1img) * t⁻¹ * (ru2 * rs2 * rv2img) *
          t⁻¹ * (ru3 * rs3 * rv3img) = 1 := by
    calc
      t ^ 2 * (ru1 * rs1 * rv1img) * t⁻¹ * (ru2 * rs2 * rv2img) *
          t⁻¹ * (ru3 * rs3 * rv3img)
          = t ^ 2 *
              (s * (t ^ (-3 : ℤ) * σ (SemidirectProduct.inr bunit) * t ^ 3) *
                s ^ (-2 : ℤ)) *
            t⁻¹ *
              (s ^ 3 *
                (t ^ (-2 : ℤ) * σ (SemidirectProduct.inr abinv) * t ^ 2) *
                s ^ (-1 : ℤ)) *
            t⁻¹ *
              (s ^ 2 * (t⁻¹ * σ (SemidirectProduct.inr uinv) * t) *
                s ^ (-3 : ℤ)) := by
            rw [← hC5r_1, ← hC5r_2, ← hC5r_3]
      _ = 1 := by
            simpa [haunit_inv_eq_uinv, hbunit_inv_mul_aunit_eq_abinv] using
              hC4_right_conj_source
  have hC7_right_conj_ambient :
      t⁻¹ * rs2 * t⁻¹ =
        ((t * rv2img * t⁻¹ * ru3) * rs3 *
          (rv3img * (t ^ 2 * ru1 * (t ^ 2)⁻¹)) *
          t ^ 2 * rs1 *
          (rv1img * (t⁻¹ * ru2 * (t⁻¹)⁻¹)))⁻¹ := by
    exact appendixC_lemma_C_3_step4_C7_of_product
      (t := t) (u1 := ru1) (s1 := rs1) (v1 := rv1img)
      (u2 := ru2) (s2 := rs2) (v2 := rv2img)
      (u3 := ru3) (s3 := rs3) (v3 := rv3img)
      (w1 := t * rv2img * t⁻¹ * ru3)
      (w2 := rv3img * (t ^ 2 * ru1 * (t ^ 2)⁻¹))
      (w3 := rv1img * (t⁻¹ * ru2 * (t⁻¹)⁻¹))
      rfl rfl rfl hprod_right_conj
  let ru1Unit : appendixCNormOneUnits p q :=
    (appendixCEmbedding_CUInHEquiv (p := p) (q := q) σ hσ).symm ⟨ru1, rhu1⟩
  let rv1Unit : appendixCNormOneUnits p q :=
    (appendixCEmbedding_CUInHEquiv (p := p) (q := q) σ hσ).symm
      ⟨rv1img, rhv1img⟩
  let ru2Unit : appendixCNormOneUnits p q :=
    (appendixCEmbedding_CUInHEquiv (p := p) (q := q) σ hσ).symm ⟨ru2, rhu2⟩
  let rv2Unit : appendixCNormOneUnits p q :=
    (appendixCEmbedding_CUInHEquiv (p := p) (q := q) σ hσ).symm
      ⟨rv2img, rhv2img⟩
  let ru3Unit : appendixCNormOneUnits p q :=
    (appendixCEmbedding_CUInHEquiv (p := p) (q := q) σ hσ).symm ⟨ru3, rhu3⟩
  let rv3Unit : appendixCNormOneUnits p q :=
    (appendixCEmbedding_CUInHEquiv (p := p) (q := q) σ hσ).symm
      ⟨rv3img, rhv3img⟩
  have hru1Unit_img : σ (SemidirectProduct.inr ru1Unit) = ru1 :=
    appendixCEmbedding_CUInHEquiv_symm_apply (p := p) (q := q) σ hσ rhu1
  have hrv1Unit_img : σ (SemidirectProduct.inr rv1Unit) = rv1img :=
    appendixCEmbedding_CUInHEquiv_symm_apply (p := p) (q := q) σ hσ rhv1img
  have hru2Unit_img : σ (SemidirectProduct.inr ru2Unit) = ru2 :=
    appendixCEmbedding_CUInHEquiv_symm_apply (p := p) (q := q) σ hσ rhu2
  have hrv2Unit_img : σ (SemidirectProduct.inr rv2Unit) = rv2img :=
    appendixCEmbedding_CUInHEquiv_symm_apply (p := p) (q := q) σ hσ rhv2img
  have hru3Unit_img : σ (SemidirectProduct.inr ru3Unit) = ru3 :=
    appendixCEmbedding_CUInHEquiv_symm_apply (p := p) (q := q) σ hσ rhu3
  have hrv3Unit_img : σ (SemidirectProduct.inr rv3Unit) = rv3img :=
    appendixCEmbedding_CUInHEquiv_symm_apply (p := p) (q := q) σ hσ rhv3img
  have rhtnorm : t ∈ Subgroup.normalizer (Uimg : Set G) := by
    simpa [Uimg, P0img] using hP1U ht
  have rhtnorm_inv : t⁻¹ ∈ Subgroup.normalizer (Uimg : Set G) :=
    (Subgroup.normalizer (Uimg : Set G)).inv_mem rhtnorm
  have rhtnorm_sq : t ^ 2 ∈ Subgroup.normalizer (Uimg : Set G) :=
    (Subgroup.normalizer (Uimg : Set G)).pow_mem rhtnorm 2
  have rhtnorm_raw :
      t ∈ Subgroup.normalizer
        (Subgroup.map σ (appendixCUInH p q) : Set G) := by
    simpa [Uimg] using rhtnorm
  have rhtnorm_inv_raw :
      t⁻¹ ∈ Subgroup.normalizer
        (Subgroup.map σ (appendixCUInH p q) : Set G) := by
    simpa [Uimg] using rhtnorm_inv
  have rhtnorm_sq_raw :
      t ^ 2 ∈ Subgroup.normalizer
        (Subgroup.map σ (appendixCUInH p q) : Set G) := by
    simpa [Uimg] using rhtnorm_sq
  let rTt : appendixCNormOneUnits p q ≃* appendixCNormOneUnits p q :=
    appendixCEmbedding_conjNormOneUnitsMulEquiv (p := p) (q := q) σ hσ rhtnorm_raw
  let rTtInv : appendixCNormOneUnits p q ≃* appendixCNormOneUnits p q :=
    appendixCEmbedding_conjNormOneUnitsMulEquiv (p := p) (q := q) σ hσ rhtnorm_inv_raw
  let rTtSq : appendixCNormOneUnits p q ≃* appendixCNormOneUnits p q :=
    appendixCEmbedding_conjNormOneUnitsMulEquiv (p := p) (q := q) σ hσ rhtnorm_sq_raw
  have hrTtInv_eq_symm : rTtInv = rTt.symm := by
    simpa [rTt, rTtInv] using
      appendixCEmbedding_conjNormOneUnitsMulEquiv_inv_eq_symm
        (p := p) (q := q) σ hσ rhtnorm_raw rhtnorm_inv_raw
  let rw1 : appendixCNormOneUnits p q := rTt rv2Unit * ru3Unit
  let rw2 : appendixCNormOneUnits p q := rv3Unit * rTtSq ru1Unit
  let rw3 : appendixCNormOneUnits p q := rv1Unit * rTtInv ru2Unit
  have hrw1_img :
      σ (SemidirectProduct.inr rw1) = (t * rv2img * t⁻¹) * ru3 := by
    have hconj_rv2 :
        σ (SemidirectProduct.inr (rTt rv2Unit)) =
          t * rv2img * t⁻¹ := by
      exact
        appendixCEmbedding_conjNormOneUnitsMulEquiv_apply_of_mem
          (p := p) (q := q) σ hσ (t := t) (u0 := rv2img)
          rhtnorm_raw rhv2img
    calc
      σ (SemidirectProduct.inr rw1)
          = σ (SemidirectProduct.inr (rTt rv2Unit)) *
              σ (SemidirectProduct.inr ru3Unit) := by
            simp [rw1, map_mul]
      _ = (t * rv2img * t⁻¹) * ru3 := by
            rw [hconj_rv2, hru3Unit_img]
  have hrw2_img :
      σ (SemidirectProduct.inr rw2) =
        rv3img * (t ^ 2 * ru1 * (t ^ 2)⁻¹) := by
    have hconj_ru1 :
        σ (SemidirectProduct.inr (rTtSq ru1Unit)) =
          t ^ 2 * ru1 * (t ^ 2)⁻¹ := by
      exact
        appendixCEmbedding_conjNormOneUnitsMulEquiv_apply_of_mem
          (p := p) (q := q) σ hσ (t := t ^ 2) (u0 := ru1)
          rhtnorm_sq_raw rhu1
    calc
      σ (SemidirectProduct.inr rw2)
          = σ (SemidirectProduct.inr rv3Unit) *
              σ (SemidirectProduct.inr (rTtSq ru1Unit)) := by
            simp [rw2, map_mul]
      _ = rv3img * (t ^ 2 * ru1 * (t ^ 2)⁻¹) := by
            rw [hrv3Unit_img, hconj_ru1]
  have hrw3_img :
      σ (SemidirectProduct.inr rw3) = rv1img * (t⁻¹ * ru2 * (t⁻¹)⁻¹) := by
    have hconj_ru2 :
        σ (SemidirectProduct.inr (rTtInv ru2Unit)) =
          t⁻¹ * ru2 * (t⁻¹)⁻¹ := by
      exact
        appendixCEmbedding_conjNormOneUnitsMulEquiv_apply_of_mem
          (p := p) (q := q) σ hσ (t := t⁻¹) (u0 := ru2)
          rhtnorm_inv_raw rhu2
    calc
      σ (SemidirectProduct.inr rw3)
          = σ (SemidirectProduct.inr rv1Unit) *
              σ (SemidirectProduct.inr (rTtInv ru2Unit)) := by
            simp [rw3, map_mul]
      _ = rv1img * (t⁻¹ * ru2 * (t⁻¹)⁻¹) := by
            rw [hrv1Unit_img, hconj_ru2]
  have hC7_right_conj :
      t⁻¹ * rs2 * t⁻¹ =
        (σ (SemidirectProduct.inr rw1) * rs3 * σ (SemidirectProduct.inr rw2) *
          t ^ 2 * rs1 * σ (SemidirectProduct.inr rw3))⁻¹ :=
    appendixC_lemma_C_3_step4_C7_of_image_product
      (p := p) (q := q) hrw1_img hrw2_img hrw3_img hprod_right_conj
  have hC9r_eq_of_power_product
      (hpowprod :
        σ (SemidirectProduct.inr rw1) * rs3 * σ (SemidirectProduct.inr rw2) *
            t ^ 2 * rs1 * σ (SemidirectProduct.inr rw3) =
          σ (SemidirectProduct.inr (rw1 ^ p)) * rs3 *
            σ (SemidirectProduct.inr (rw2 ^ p)) *
            t ^ 2 * rs1 * σ (SemidirectProduct.inr (rw3 ^ p))) :
      (t ^ 2)⁻¹ * (σ (SemidirectProduct.inr (rw2 ^ p)))⁻¹ * rs3⁻¹ *
          σ (SemidirectProduct.inr (rw1⁻¹ ^ (p - 1))) * rs3 *
          σ (SemidirectProduct.inr rw2) * t ^ 2 =
        rs1 * σ (SemidirectProduct.inr (rw3 ^ (p - 1))) * rs1⁻¹ :=
    appendixC_lemma_C_3_step4_C9_eq_of_power_product
      (p := p) (q := q) (σ := σ) (t := t) (s1 := rs1) (s3 := rs3)
      rw1 rw2 rw3 hpowprod
  let rTtInv3bunit : appendixCNormOneUnits p q :=
    ((rTtInv : appendixCNormOneUnits p q → appendixCNormOneUnits p q)^[3]) bunit
  let rTtInv2abinv : appendixCNormOneUnits p q :=
    ((rTtInv : appendixCNormOneUnits p q → appendixCNormOneUnits p q)^[2]) abinv
  have hrTtInv3bunit_img :
      σ (SemidirectProduct.inr rTtInv3bunit) =
        t ^ (-3 : ℤ) * σ (SemidirectProduct.inr bunit) * t ^ 3 := by
    have hiter := appendixCEmbedding_conjNormOneUnitsMulEquiv_iterate_apply
      (p := p) (q := q) σ hσ rhtnorm_inv_raw bunit 3
    simpa [rTtInv, rTtInv3bunit, zpow_ofNat, inv_pow] using hiter
  have hrTtInv2abinv_img :
      σ (SemidirectProduct.inr rTtInv2abinv) =
        t ^ (-2 : ℤ) * σ (SemidirectProduct.inr abinv) * t ^ 2 := by
    have hiter := appendixCEmbedding_conjNormOneUnitsMulEquiv_iterate_apply
      (p := p) (q := q) σ hσ rhtnorm_inv_raw abinv 2
    simpa [rTtInv, rTtInv2abinv, zpow_ofNat, inv_pow] using hiter
  have hrTtInv_uinv_img :
      σ (SemidirectProduct.inr (rTtInv uinv)) =
        t⁻¹ * σ (SemidirectProduct.inr uinv) * t := by
    simpa [rTtInv] using
      appendixCEmbedding_conjNormOneUnitsMulEquiv_apply
        (p := p) (q := q) σ hσ rhtnorm_inv_raw uinv
  have hC5r_1_unit_product :
      rTtInv3bunit = ru1Unit * rv1Unit := by
    exact appendixCEmbedding_P0_U_P0_eq_U_P0_U_right_component
      (p := p) (q := q) σ hσ
      (sL := s) (sR := s ^ (-2 : ℤ)) (s0 := rs1)
      (z := rTtInv3bunit) (u := ru1Unit) (v := rv1Unit)
      (by simpa [P0img] using hs)
      (by simpa [P0img] using P0img.zpow_mem hs (-2 : ℤ))
      (by simpa [P0img] using rhs1)
      (by simpa [hrTtInv3bunit_img, hru1Unit_img, hrv1Unit_img, mul_assoc] using hC5r_1)
  have hC5r_2_unit_product :
      rTtInv2abinv = ru2Unit * rv2Unit := by
    exact appendixCEmbedding_P0_U_P0_eq_U_P0_U_right_component
      (p := p) (q := q) σ hσ
      (sL := s ^ 3) (sR := s ^ (-1 : ℤ)) (s0 := rs2)
      (z := rTtInv2abinv) (u := ru2Unit) (v := rv2Unit)
      (by simpa [P0img] using P0img.pow_mem hs 3)
      (by simpa [P0img] using P0img.zpow_mem hs (-1 : ℤ))
      (by simpa [P0img] using rhs2)
      (by simpa [hrTtInv2abinv_img, hru2Unit_img, hrv2Unit_img, mul_assoc] using hC5r_2)
  have hC5r_3_unit_product :
      rTtInv uinv = ru3Unit * rv3Unit := by
    exact appendixCEmbedding_P0_U_P0_eq_U_P0_U_right_component
      (p := p) (q := q) σ hσ
      (sL := s ^ 2) (sR := s ^ (-3 : ℤ)) (s0 := rs3)
      (z := rTtInv uinv) (u := ru3Unit) (v := rv3Unit)
      (by simpa [P0img] using P0img.pow_mem hs 2)
      (by simpa [P0img] using P0img.zpow_mem hs (-3 : ℤ))
      (by simpa [P0img] using rhs3)
      (by simpa [hrTtInv_uinv_img, hru3Unit_img, hrv3Unit_img, mul_assoc] using hC5r_3)
  have hC5r_1_pow :
      s * σ (SemidirectProduct.inr (rTtInv3bunit ^ p)) * s ^ (-2 : ℤ) =
        σ (SemidirectProduct.inr (ru1Unit ^ p)) * rs1 *
          σ (SemidirectProduct.inr (rv1Unit ^ p)) := by
    exact appendixCEmbedding_P0_U_P0_eq_U_P0_U_pow
      (p := p) (q := q) σ hσ
      (sL := s) (sR := s ^ (-2 : ℤ)) (s0 := rs1)
      (z := rTtInv3bunit) (u := ru1Unit) (v := rv1Unit)
      (by simpa [P0img] using hs)
      (by simpa [P0img] using P0img.zpow_mem hs (-2 : ℤ))
      (by simpa [P0img] using rhs1)
      (by simpa [hrTtInv3bunit_img, hru1Unit_img, hrv1Unit_img, mul_assoc] using hC5r_1)
  have hC5r_2_pow :
      s ^ 3 * σ (SemidirectProduct.inr (rTtInv2abinv ^ p)) * s ^ (-1 : ℤ) =
        σ (SemidirectProduct.inr (ru2Unit ^ p)) * rs2 *
          σ (SemidirectProduct.inr (rv2Unit ^ p)) := by
    exact appendixCEmbedding_P0_U_P0_eq_U_P0_U_pow
      (p := p) (q := q) σ hσ
      (sL := s ^ 3) (sR := s ^ (-1 : ℤ)) (s0 := rs2)
      (z := rTtInv2abinv) (u := ru2Unit) (v := rv2Unit)
      (by simpa [P0img] using P0img.pow_mem hs 3)
      (by simpa [P0img] using P0img.zpow_mem hs (-1 : ℤ))
      (by simpa [P0img] using rhs2)
      (by simpa [hrTtInv2abinv_img, hru2Unit_img, hrv2Unit_img, mul_assoc] using hC5r_2)
  have hC5r_3_pow :
      s ^ 2 * σ (SemidirectProduct.inr ((rTtInv uinv) ^ p)) *
          s ^ (-3 : ℤ) =
        σ (SemidirectProduct.inr (ru3Unit ^ p)) * rs3 *
          σ (SemidirectProduct.inr (rv3Unit ^ p)) := by
    exact appendixCEmbedding_P0_U_P0_eq_U_P0_U_pow
      (p := p) (q := q) σ hσ
      (sL := s ^ 2) (sR := s ^ (-3 : ℤ)) (s0 := rs3)
      (z := rTtInv uinv) (u := ru3Unit) (v := rv3Unit)
      (by simpa [P0img] using P0img.pow_mem hs 2)
      (by simpa [P0img] using P0img.zpow_mem hs (-3 : ℤ))
      (by simpa [P0img] using rhs3)
      (by simpa [hrTtInv_uinv_img, hru3Unit_img, hrv3Unit_img, mul_assoc] using hC5r_3)
  have hrTtInv3bunit_pow_img :
      σ (SemidirectProduct.inr (rTtInv3bunit ^ p)) =
        t ^ (-3 : ℤ) * σ (SemidirectProduct.inr (bunit ^ p)) * t ^ 3 := by
    have hiter := appendixCEmbedding_conjNormOneUnitsMulEquiv_iterate_apply
      (p := p) (q := q) σ hσ rhtnorm_inv_raw (bunit ^ p) 3
    simpa [rTtInv, rTtInv3bunit, map_pow, zpow_ofNat, inv_pow] using hiter
  have hrTtInv2abinv_pow_img :
      σ (SemidirectProduct.inr (rTtInv2abinv ^ p)) =
        t ^ (-2 : ℤ) * σ (SemidirectProduct.inr (abinv ^ p)) * t ^ 2 := by
    have hiter := appendixCEmbedding_conjNormOneUnitsMulEquiv_iterate_apply
      (p := p) (q := q) σ hσ rhtnorm_inv_raw (abinv ^ p) 2
    simpa [rTtInv, rTtInv2abinv, map_pow, zpow_ofNat, inv_pow] using hiter
  have hrTtInv_uinv_pow_img :
      σ (SemidirectProduct.inr ((rTtInv uinv) ^ p)) =
        t⁻¹ * σ (SemidirectProduct.inr (uinv ^ p)) * t := by
    have hconj := appendixCEmbedding_conjNormOneUnitsMulEquiv_apply
      (p := p) (q := q) σ hσ rhtnorm_inv_raw (uinv ^ p)
    simpa [rTtInv, map_pow] using hconj
  have hprod_right_conj_pow :
      t ^ 2 *
          (σ (SemidirectProduct.inr (ru1Unit ^ p)) * rs1 *
            σ (SemidirectProduct.inr (rv1Unit ^ p))) *
        t⁻¹ *
          (σ (SemidirectProduct.inr (ru2Unit ^ p)) * rs2 *
            σ (SemidirectProduct.inr (rv2Unit ^ p))) *
        t⁻¹ *
          (σ (SemidirectProduct.inr (ru3Unit ^ p)) * rs3 *
            σ (SemidirectProduct.inr (rv3Unit ^ p))) = 1 := by
    calc
      t ^ 2 *
          (σ (SemidirectProduct.inr (ru1Unit ^ p)) * rs1 *
            σ (SemidirectProduct.inr (rv1Unit ^ p))) *
        t⁻¹ *
          (σ (SemidirectProduct.inr (ru2Unit ^ p)) * rs2 *
            σ (SemidirectProduct.inr (rv2Unit ^ p))) *
        t⁻¹ *
          (σ (SemidirectProduct.inr (ru3Unit ^ p)) * rs3 *
            σ (SemidirectProduct.inr (rv3Unit ^ p)))
          = t ^ 2 *
              (s * σ (SemidirectProduct.inr (rTtInv3bunit ^ p)) *
                s ^ (-2 : ℤ)) *
            t⁻¹ *
              (s ^ 3 * σ (SemidirectProduct.inr (rTtInv2abinv ^ p)) *
                s ^ (-1 : ℤ)) *
            t⁻¹ *
              (s ^ 2 * σ (SemidirectProduct.inr ((rTtInv uinv) ^ p)) *
                s ^ (-3 : ℤ)) := by
            rw [← hC5r_1_pow, ← hC5r_2_pow, ← hC5r_3_pow]
      _ = t ^ 2 *
              (s * (t ^ (-3 : ℤ) * σ (SemidirectProduct.inr (bunit ^ p)) *
                t ^ 3) * s ^ (-2 : ℤ)) *
            t⁻¹ *
              (s ^ 3 * (t ^ (-2 : ℤ) * σ (SemidirectProduct.inr (abinv ^ p)) *
                t ^ 2) * s ^ (-1 : ℤ)) *
            t⁻¹ *
              (s ^ 2 * (t⁻¹ * σ (SemidirectProduct.inr (uinv ^ p)) * t) *
                s ^ (-3 : ℤ)) := by
            rw [hrTtInv3bunit_pow_img, hrTtInv2abinv_pow_img,
              hrTtInv_uinv_pow_img]
      _ = 1 := hC4_right_conj_source_pow
  have hrw1_pow_img :
      σ (SemidirectProduct.inr (rw1 ^ p)) =
        (t * σ (SemidirectProduct.inr (rv2Unit ^ p)) * t⁻¹) *
          σ (SemidirectProduct.inr (ru3Unit ^ p)) := by
    have hconj_rv2 :
        σ (SemidirectProduct.inr (rTt (rv2Unit ^ p))) =
          t * σ (SemidirectProduct.inr (rv2Unit ^ p)) * t⁻¹ := by
      exact appendixCEmbedding_conjNormOneUnitsMulEquiv_apply
        (p := p) (q := q) σ hσ rhtnorm_raw (rv2Unit ^ p)
    calc
      σ (SemidirectProduct.inr (rw1 ^ p))
          = σ (SemidirectProduct.inr (rTt (rv2Unit ^ p) * ru3Unit ^ p)) := by
            congr
            simp [rw1, mul_pow, map_pow]
      _ = σ (SemidirectProduct.inr (rTt (rv2Unit ^ p))) *
            σ (SemidirectProduct.inr (ru3Unit ^ p)) := by
            simp [map_mul]
      _ = (t * σ (SemidirectProduct.inr (rv2Unit ^ p)) * t⁻¹) *
            σ (SemidirectProduct.inr (ru3Unit ^ p)) := by
            rw [hconj_rv2]
  have hrw2_pow_img :
      σ (SemidirectProduct.inr (rw2 ^ p)) =
        σ (SemidirectProduct.inr (rv3Unit ^ p)) *
          (t ^ 2 * σ (SemidirectProduct.inr (ru1Unit ^ p)) * (t ^ 2)⁻¹) := by
    have hconj_ru1 :
        σ (SemidirectProduct.inr (rTtSq (ru1Unit ^ p))) =
          t ^ 2 * σ (SemidirectProduct.inr (ru1Unit ^ p)) * (t ^ 2)⁻¹ := by
      exact appendixCEmbedding_conjNormOneUnitsMulEquiv_apply
        (p := p) (q := q) σ hσ rhtnorm_sq_raw (ru1Unit ^ p)
    calc
      σ (SemidirectProduct.inr (rw2 ^ p))
          = σ (SemidirectProduct.inr (rv3Unit ^ p * rTtSq (ru1Unit ^ p))) := by
            congr
            simp [rw2, mul_pow, map_pow]
      _ = σ (SemidirectProduct.inr (rv3Unit ^ p)) *
            σ (SemidirectProduct.inr (rTtSq (ru1Unit ^ p))) := by
            simp [map_mul]
      _ = σ (SemidirectProduct.inr (rv3Unit ^ p)) *
            (t ^ 2 * σ (SemidirectProduct.inr (ru1Unit ^ p)) * (t ^ 2)⁻¹) := by
            rw [hconj_ru1]
  have hrw3_pow_img :
      σ (SemidirectProduct.inr (rw3 ^ p)) =
        σ (SemidirectProduct.inr (rv1Unit ^ p)) *
          (t⁻¹ * σ (SemidirectProduct.inr (ru2Unit ^ p)) * (t⁻¹)⁻¹) := by
    have hconj_ru2 :
        σ (SemidirectProduct.inr (rTtInv (ru2Unit ^ p))) =
          t⁻¹ * σ (SemidirectProduct.inr (ru2Unit ^ p)) * (t⁻¹)⁻¹ := by
      exact appendixCEmbedding_conjNormOneUnitsMulEquiv_apply
        (p := p) (q := q) σ hσ rhtnorm_inv_raw (ru2Unit ^ p)
    calc
      σ (SemidirectProduct.inr (rw3 ^ p))
          = σ (SemidirectProduct.inr (rv1Unit ^ p * rTtInv (ru2Unit ^ p))) := by
            congr
            simp [rw3, mul_pow, map_pow]
      _ = σ (SemidirectProduct.inr (rv1Unit ^ p)) *
            σ (SemidirectProduct.inr (rTtInv (ru2Unit ^ p))) := by
            simp [map_mul]
      _ = σ (SemidirectProduct.inr (rv1Unit ^ p)) *
            (t⁻¹ * σ (SemidirectProduct.inr (ru2Unit ^ p)) * (t⁻¹)⁻¹) := by
            rw [hconj_ru2]
  have hC7_right_conj_power :
      t⁻¹ * rs2 * t⁻¹ =
        (σ (SemidirectProduct.inr (rw1 ^ p)) * rs3 *
          σ (SemidirectProduct.inr (rw2 ^ p)) *
          t ^ 2 * rs1 * σ (SemidirectProduct.inr (rw3 ^ p)))⁻¹ :=
    appendixC_lemma_C_3_step4_C7_of_image_product
      (p := p) (q := q) hrw1_pow_img hrw2_pow_img hrw3_pow_img
      hprod_right_conj_pow
  have hpowprod_right_conj :
      σ (SemidirectProduct.inr rw1) * rs3 * σ (SemidirectProduct.inr rw2) *
          t ^ 2 * rs1 * σ (SemidirectProduct.inr rw3) =
        σ (SemidirectProduct.inr (rw1 ^ p)) * rs3 *
          σ (SemidirectProduct.inr (rw2 ^ p)) *
          t ^ 2 * rs1 * σ (SemidirectProduct.inr (rw3 ^ p)) := by
    apply inv_injective
    exact hC7_right_conj.symm.trans hC7_right_conj_power
  have rUimg (w : appendixCNormOneUnits p q) :
      σ (SemidirectProduct.inr w) ∈ Uimg := by
    exact ⟨SemidirectProduct.inr w,
      (appendixCUInH_mem_iff (p := p) (q := q) _).2 ⟨w, rfl⟩, rfl⟩
  have hrC5_1_u_img :
      t ^ (-3 : ℤ) * σ (SemidirectProduct.inr bunit) * t ^ 3 ∈ Uimg := by
    rw [← hrTtInv3bunit_img]
    exact rUimg rTtInv3bunit
  have hrC5_2_u_img :
      t ^ (-2 : ℤ) * σ (SemidirectProduct.inr abinv) * t ^ 2 ∈ Uimg := by
    rw [← hrTtInv2abinv_img]
    exact rUimg rTtInv2abinv
  have hrC5_3_u_img :
      t⁻¹ * σ (SemidirectProduct.inr uinv) * t ∈ Uimg := by
    rw [← hrTtInv_uinv_img]
    exact rUimg (rTtInv uinv)
  have rhs_sq_ne : s ^ 2 ≠ 1 :=
    appendixCEmbedding_CP0InH_sq_ne_one_of_mem_ne_one
      (p := p) (q := q) hoddp σ hσ (by simpa [P0img] using hs) hsne
  have hrs1_ne : rs1 ≠ 1 := by
    intro hrs1_one
    have hmem :
        s * (t ^ (-3 : ℤ) * σ (SemidirectProduct.inr bunit) * t ^ 3) *
            s ^ (-2 : ℤ) ∈ Uimg := by
      rw [hC5r_1]
      simpa [hrs1_one, mul_assoc] using Uimg.mul_mem rhu1 rhv1img
    rcases appendixCEmbedding_P0_mul_U_mul_P0_mem_U_cases
        (p := p) (q := q) hA σ hσ
        (s1 := s) (s2 := s ^ (-2 : ℤ))
        (u := t ^ (-3 : ℤ) * σ (SemidirectProduct.inr bunit) * t ^ 3)
        (by simpa [P0img] using hs)
        (by simpa [P0img] using P0img.zpow_mem hs (-2 : ℤ))
        (by simpa [Uimg] using hrC5_1_u_img)
        (by simpa [Uimg] using hmem) with
      htrivial | hunit
    · exact hsne htrivial.1
    · have hs_one : s = 1 := by
        have h := hunit.2
        group at h
        have hinv := congrArg Inv.inv h
        simpa using hinv
      exact hsne hs_one
  have hrs2_ne : rs2 ≠ 1 := by
    intro hrs2_one
    have hmem :
        s ^ 3 * (t ^ (-2 : ℤ) * σ (SemidirectProduct.inr abinv) * t ^ 2) *
            s ^ (-1 : ℤ) ∈ Uimg := by
      rw [hC5r_2]
      simpa [hrs2_one, mul_assoc] using Uimg.mul_mem rhu2 rhv2img
    rcases appendixCEmbedding_P0_mul_U_mul_P0_mem_U_cases
        (p := p) (q := q) hA σ hσ
        (s1 := s ^ 3) (s2 := s ^ (-1 : ℤ))
        (u := t ^ (-2 : ℤ) * σ (SemidirectProduct.inr abinv) * t ^ 2)
        (by simpa [P0img] using P0img.pow_mem hs 3)
        (by simpa [P0img] using P0img.zpow_mem hs (-1 : ℤ))
        (by simpa [Uimg] using hrC5_2_u_img)
        (by simpa [Uimg] using hmem) with
      htrivial | hunit
    · have hs_one : s = 1 := by
        have hinv := congrArg Inv.inv htrivial.2
        simpa using hinv
      exact hsne hs_one
    · have hs2_one : s ^ 2 = 1 := by
        have h := hunit.2
        group at h
        simpa [zpow_ofNat] using h
      exact rhs_sq_ne hs2_one
  have hrs3_ne : rs3 ≠ 1 := by
    intro hrs3_one
    have hmem :
        s ^ 2 * (t⁻¹ * σ (SemidirectProduct.inr uinv) * t) *
            s ^ (-3 : ℤ) ∈ Uimg := by
      rw [hC5r_3]
      simpa [hrs3_one, mul_assoc] using Uimg.mul_mem rhu3 rhv3img
    rcases appendixCEmbedding_P0_mul_U_mul_P0_mem_U_cases
        (p := p) (q := q) hA σ hσ
        (s1 := s ^ 2) (s2 := s ^ (-3 : ℤ))
        (u := t⁻¹ * σ (SemidirectProduct.inr uinv) * t)
        (by simpa [P0img] using P0img.pow_mem hs 2)
        (by simpa [P0img] using P0img.zpow_mem hs (-3 : ℤ))
        (by simpa [Uimg] using hrC5_3_u_img)
        (by simpa [Uimg] using hmem) with
      htrivial | hunit
    · exact rhs_sq_ne htrivial.1
    · have hs_one : s = 1 := by
        have h := hunit.2
        group at h
        have hinv := congrArg Inv.inv h
        simpa using hinv
      exact hsne hs_one
  have rht_sq_ne : t ^ 2 ≠ 1 :=
    appendixCEmbedding_rightConjugate_sq_ne_one_of_mem_ne_one
      (p := p) (q := q) hoddp σ hσ ht htne
  have rStep3_t2_inv :
      Himg ⊓ Himg.conjBy ((t ^ 2)⁻¹) = Uimg := by
    simpa [Himg, Uimg, P0img] using
      appendixCEmbedding_H_inf_conjBy_eq_CUInH_of_mem_rightConjugate_ne_one
        (p := p) (q := q) hA σ hσ Q hcop hy hP0Q hP1U hx hx1
        ((appendixCRightConjugate
          (Subgroup.map σ (appendixCP0InH p q)) y).inv_mem
            ((appendixCRightConjugate
              (Subgroup.map σ (appendixCP0InH p q)) y).pow_mem ht 2))
        (by
          intro h
          exact rht_sq_ne (inv_eq_one.mp h))
  have hC9r_collapse_of_power_product
      (hpowprod :
        σ (SemidirectProduct.inr rw1) * rs3 * σ (SemidirectProduct.inr rw2) *
            t ^ 2 * rs1 * σ (SemidirectProduct.inr rw3) =
          σ (SemidirectProduct.inr (rw1 ^ p)) * rs3 *
            σ (SemidirectProduct.inr (rw2 ^ p)) *
            t ^ 2 * rs1 * σ (SemidirectProduct.inr (rw3 ^ p))) :
      rw1 = 1 ∧ rw2 = 1 ∧ rw3 = 1 :=
    appendixC_lemma_C_3_step4_C9_collapse_of_eq
      (p := p) (q := q) hA σ hσ rStep3_t2_inv
      (by simpa [P0img] using rhs1) hrs1_ne
      (by simpa [P0img] using rhs3) hrs3_ne
      rw1 rw2 rw3 (hC9r_eq_of_power_product hpowprod)
  have hC10r_of_power_product
      (hpowprod :
        σ (SemidirectProduct.inr rw1) * rs3 * σ (SemidirectProduct.inr rw2) *
            t ^ 2 * rs1 * σ (SemidirectProduct.inr rw3) =
          σ (SemidirectProduct.inr (rw1 ^ p)) * rs3 *
            σ (SemidirectProduct.inr (rw2 ^ p)) *
            t ^ 2 * rs1 * σ (SemidirectProduct.inr (rw3 ^ p))) :
      t ^ 2 * rs1 * t⁻¹ * rs2 * t⁻¹ * rs3 = 1 := by
    rcases hC9r_collapse_of_power_product hpowprod with ⟨hrw1, hrw2, hrw3⟩
    exact appendixC_lemma_C_3_step4_C10_of_C7
      (t := t) (s1 := rs1) (s2 := rs2) (s3 := rs3)
      (w1 := σ (SemidirectProduct.inr rw1))
      (w2 := σ (SemidirectProduct.inr rw2))
      (w3 := σ (SemidirectProduct.inr rw3))
      hC7_right_conj
      (by simp [hrw1]) (by simp [hrw2]) (by simp [hrw3])
  have hC10r : t ^ 2 * rs1 * t⁻¹ * rs2 * t⁻¹ * rs3 = 1 :=
    hC10r_of_power_product hpowprod_right_conj
  have hC10r_P0_part :
      s ^ 2 * rs1 * s⁻¹ * rs2 * s⁻¹ * rs3 = rs1 * rs2 * rs3 :=
    appendixCEmbedding_CP0InH_C10_P0_part
      (p := p) (q := q) σ
      (by simpa [P0img] using hs)
      (by simpa [P0img] using rhs1)
      (by simpa [P0img] using rhs2)
  have hC10r_prod_mem_Q : rs1 * rs2 * rs3 ∈ Q := by
    have hnorm_s2 : s ^ 2 ∈ Subgroup.normalizer (Q : Set G) :=
      (Subgroup.normalizer (Q : Set G)).pow_mem hs_norm_Q 2
    have hnorm_sinv : s⁻¹ ∈ Subgroup.normalizer (Q : Set G) :=
      (Subgroup.normalizer (Q : Set G)).inv_mem hs_norm_Q
    have hnorm_rs1 : rs1 ∈ Subgroup.normalizer (Q : Set G) := by
      simpa [P0img] using hP0Q rhs1
    have hnorm_rs2 : rs2 ∈ Subgroup.normalizer (Q : Set G) := by
      simpa [P0img] using hP0Q rhs2
    have hnorm_rs3 : rs3 ∈ Subgroup.normalizer (Q : Set G) := by
      simpa [P0img] using hP0Q rhs3
    have hmod_t2_s2 : t ^ 2 * (s ^ 2)⁻¹ ∈ Q := by
      have hconj :
          s ^ 2 * (s ^ (-2 : ℤ) * t ^ 2) * (s ^ 2)⁻¹ ∈ Q :=
        (Subgroup.mem_normalizer_iff.mp hnorm_s2
          (s ^ (-2 : ℤ) * t ^ 2)).1 hq_sinv2_t2
      convert hconj using 1
      group
    have hmod_tinv_sinv : t⁻¹ * (s⁻¹)⁻¹ ∈ Q := by
      simpa using hq_tinv_s
    have hmod_rs1 : rs1 * rs1⁻¹ ∈ Q := by simp
    have hmod_rs2 : rs2 * rs2⁻¹ ∈ Q := by simp
    have hmod_rs3 : rs3 * rs3⁻¹ ∈ Q := by simp
    have hmod1 :
        (t ^ 2 * rs1) * (s ^ 2 * rs1)⁻¹ ∈ Q :=
      appendixC_modRight_mul_mem hmod_t2_s2 hmod_rs1 hnorm_s2
    have hnorm_pref1 :
        s ^ 2 * rs1 ∈ Subgroup.normalizer (Q : Set G) :=
      (Subgroup.normalizer (Q : Set G)).mul_mem hnorm_s2 hnorm_rs1
    have hmod2 :
        ((t ^ 2 * rs1) * t⁻¹) * ((s ^ 2 * rs1) * s⁻¹)⁻¹ ∈ Q :=
      appendixC_modRight_mul_mem hmod1 hmod_tinv_sinv hnorm_pref1
    have hnorm_pref2 :
        (s ^ 2 * rs1) * s⁻¹ ∈ Subgroup.normalizer (Q : Set G) :=
      (Subgroup.normalizer (Q : Set G)).mul_mem hnorm_pref1 hnorm_sinv
    have hmod3 :
        (((t ^ 2 * rs1) * t⁻¹) * rs2) *
            (((s ^ 2 * rs1) * s⁻¹) * rs2)⁻¹ ∈ Q :=
      appendixC_modRight_mul_mem hmod2 hmod_rs2 hnorm_pref2
    have hnorm_pref3 :
        ((s ^ 2 * rs1) * s⁻¹) * rs2 ∈ Subgroup.normalizer (Q : Set G) :=
      (Subgroup.normalizer (Q : Set G)).mul_mem hnorm_pref2 hnorm_rs2
    have hmod4 :
        ((((t ^ 2 * rs1) * t⁻¹) * rs2) * t⁻¹) *
            ((((s ^ 2 * rs1) * s⁻¹) * rs2) * s⁻¹)⁻¹ ∈ Q :=
      appendixC_modRight_mul_mem hmod3 hmod_tinv_sinv hnorm_pref3
    have hnorm_pref4 :
        (((s ^ 2 * rs1) * s⁻¹) * rs2) * s⁻¹ ∈
          Subgroup.normalizer (Q : Set G) :=
      (Subgroup.normalizer (Q : Set G)).mul_mem hnorm_pref3 hnorm_sinv
    have hmod5 :
        (((((t ^ 2 * rs1) * t⁻¹) * rs2) * t⁻¹) * rs3) *
            (((((s ^ 2 * rs1) * s⁻¹) * rs2) * s⁻¹) * rs3)⁻¹ ∈ Q :=
      appendixC_modRight_mul_mem hmod4 hmod_rs3 hnorm_pref4
    have hmod :
        (t ^ 2 * rs1 * t⁻¹ * rs2 * t⁻¹ * rs3) *
            (s ^ 2 * rs1 * s⁻¹ * rs2 * s⁻¹ * rs3)⁻¹ ∈ Q := by
      simpa [mul_assoc] using hmod5
    have hP0part_inv : (s ^ 2 * rs1 * s⁻¹ * rs2 * s⁻¹ * rs3)⁻¹ ∈ Q := by
      simpa [hC10r] using hmod
    have hP0part : s ^ 2 * rs1 * s⁻¹ * rs2 * s⁻¹ * rs3 ∈ Q := by
      simpa using Q.inv_mem hP0part_inv
    simpa [hC10r_P0_part] using hP0part
  have hC10r_prod_eq_one : rs1 * rs2 * rs3 = 1 := by
    have hprodP0 : rs1 * rs2 * rs3 ∈ P0img :=
      P0img.mul_mem (P0img.mul_mem (by simpa [P0img] using rhs1)
        (by simpa [P0img] using rhs2)) (by simpa [P0img] using rhs3)
    have hprodP : rs1 * rs2 * rs3 ∈ Subgroup.map σ (appendixCPInH p q) :=
      Subgroup.map_mono (appendixCP0InH_le_appendixCPInH (p := p) (q := q))
        hprodP0
    have hbot : Subgroup.map σ (appendixCPInH p q) ⊓ Q = ⊥ :=
      appendixCEmbedding_CPInH_inf_Q_eq_bot_of_coprime_card
        (p := p) (q := q) σ Q hcop
    have hmem : rs1 * rs2 * rs3 ∈ (⊥ : Subgroup G) := by
      have hInf : rs1 * rs2 * rs3 ∈ Subgroup.map σ (appendixCPInH p q) ⊓ Q :=
        ⟨hprodP, hC10r_prod_mem_Q⟩
      simpa [hbot] using hInf
    simpa using hmem
  let c10FixedTerm : G :=
    rs3⁻¹ * y⁻¹ * rs3 * s * y * s⁻¹ * s * rs1 * y⁻¹ * rs1⁻¹ * s⁻¹ * y
  have hC10r_fixedTerm_mem_Q : c10FixedTerm ∈ Q := by
    have hnorm_rs1 : rs1 ∈ Subgroup.normalizer (Q : Set G) := by
      simpa [P0img] using hP0Q rhs1
    have hnorm_rs3 : rs3 ∈ Subgroup.normalizer (Q : Set G) := by
      simpa [P0img] using hP0Q rhs3
    have hq1 : rs3⁻¹ * y⁻¹ * rs3 ∈ Q := by
      have hnorm_rs3_inv :
          rs3⁻¹ ∈ Subgroup.normalizer (Q : Set G) :=
        (Subgroup.normalizer (Q : Set G)).inv_mem hnorm_rs3
      have hqraw : rs3⁻¹ * y⁻¹ * (rs3⁻¹)⁻¹ ∈ Q :=
        (Subgroup.mem_normalizer_iff.mp hnorm_rs3_inv y⁻¹).1 (Q.inv_mem hy)
      simpa using hqraw
    have hq2 : s * y * s⁻¹ ∈ Q :=
      (Subgroup.mem_normalizer_iff.mp hs_norm_Q y).1 hy
    have hq3 : s * rs1 * y⁻¹ * rs1⁻¹ * s⁻¹ ∈ Q := by
      have hnorm_s_rs1 :
          s * rs1 ∈ Subgroup.normalizer (Q : Set G) :=
        (Subgroup.normalizer (Q : Set G)).mul_mem hs_norm_Q hnorm_rs1
      have hqraw : (s * rs1) * y⁻¹ * (s * rs1)⁻¹ ∈ Q :=
        (Subgroup.mem_normalizer_iff.mp hnorm_s_rs1 y⁻¹).1 (Q.inv_mem hy)
      convert hqraw using 1
      group
    have hq12 : (rs3⁻¹ * y⁻¹ * rs3) * (s * y * s⁻¹) ∈ Q :=
      Q.mul_mem hq1 hq2
    have hq123 :
        (rs3⁻¹ * y⁻¹ * rs3) * (s * y * s⁻¹) *
            (s * rs1 * y⁻¹ * rs1⁻¹ * s⁻¹) ∈ Q :=
      Q.mul_mem hq12 hq3
    have hq1234 :
        (rs3⁻¹ * y⁻¹ * rs3) * (s * y * s⁻¹) *
            (s * rs1 * y⁻¹ * rs1⁻¹ * s⁻¹) * y ∈ Q :=
      Q.mul_mem hq123 hy
    simpa [c10FixedTerm, mul_assoc] using hq1234
  have hC10r_fixedTerm_mem_comm :
      let φ : P0img →* MulAut Q :=
        Q.normalizerMonoidHom.comp (Subgroup.inclusion hP0Q)
      letI : MulDistribMulAction P0img Q := MulDistribMulAction.compHom Q φ
      (⟨c10FixedTerm, hC10r_fixedTerm_mem_Q⟩ : Q) ∈
        commutatorAction (A := P0img) (G := Q) := by
    classical
    let φ : P0img →* MulAut Q :=
      Q.normalizerMonoidHom.comp (Subgroup.inclusion hP0Q)
    letI : MulDistribMulAction P0img Q := MulDistribMulAction.compHom Q φ
    let C : Subgroup Q := commutatorAction (A := P0img) (G := Q)
    haveI : IsInvariant P0img Q C := by
      simpa [C] using (commutatorAction_isInvariant (G := Q) (A := P0img))
    have hyC : (⟨y, hy⟩ : Q) ∈ C := by
      simpa [P0img, φ, C] using hycomm
    have hyinvC : (⟨y⁻¹, Q.inv_mem hy⟩ : Q) ∈ C := by
      have hyinvC0 : (⟨y, hy⟩ : Q)⁻¹ ∈ C := C.inv_mem hyC
      rw [show (⟨y⁻¹, Q.inv_mem hy⟩ : Q) = (⟨y, hy⟩ : Q)⁻¹ from
        Subtype.ext (by rfl)]
      exact hyinvC0
    have action_mem {a z : G} (ha : a ∈ P0img) (hz : z ∈ Q)
        (hzC : (⟨z, hz⟩ : Q) ∈ C) :
        (⟨a * z * a⁻¹,
          (Subgroup.mem_normalizer_iff.mp (by simpa [P0img] using hP0Q ha) z).1 hz⟩ :
            Q) ∈ C := by
      let a0 : P0img := ⟨a, ha⟩
      have hsmul :
          a0 • (⟨z, hz⟩ : Q) ∈ C :=
        (IsInvariant.invariant (A := P0img) (G := Q) (H := C) a0
          (⟨z, hz⟩ : Q)).1 hzC
      have hsmul' :
          (Subgroup.inclusion hP0Q ⟨a, ha⟩) • (⟨z, hz⟩ : Q) ∈ C := by
        simpa [a0, φ, C, MulAction.compHom_smul_def,
          Subgroup.normalizerMonoidHom] using hsmul
      rw [show (⟨a * z * a⁻¹,
          (Subgroup.mem_normalizer_iff.mp (by simpa [P0img] using hP0Q ha) z).1 hz⟩ :
            Q) = (Subgroup.inclusion hP0Q ⟨a, ha⟩) • (⟨z, hz⟩ : Q) from
        Subtype.ext (by rfl)]
      exact hsmul'
    have hnorm_rs1 : rs1 ∈ Subgroup.normalizer (Q : Set G) := by
      simpa [P0img] using hP0Q rhs1
    have hnorm_rs3 : rs3 ∈ Subgroup.normalizer (Q : Set G) := by
      simpa [P0img] using hP0Q rhs3
    have hq1 : rs3⁻¹ * y⁻¹ * rs3 ∈ Q := by
      have hnorm_rs3_inv :
          rs3⁻¹ ∈ Subgroup.normalizer (Q : Set G) :=
        (Subgroup.normalizer (Q : Set G)).inv_mem hnorm_rs3
      have hqraw : rs3⁻¹ * y⁻¹ * (rs3⁻¹)⁻¹ ∈ Q :=
        (Subgroup.mem_normalizer_iff.mp hnorm_rs3_inv y⁻¹).1 (Q.inv_mem hy)
      simpa using hqraw
    have hq2 : s * y * s⁻¹ ∈ Q :=
      (Subgroup.mem_normalizer_iff.mp hs_norm_Q y).1 hy
    have hq3 : s * rs1 * y⁻¹ * rs1⁻¹ * s⁻¹ ∈ Q := by
      have hnorm_s_rs1 :
          s * rs1 ∈ Subgroup.normalizer (Q : Set G) :=
        (Subgroup.normalizer (Q : Set G)).mul_mem hs_norm_Q hnorm_rs1
      have hqraw : (s * rs1) * y⁻¹ * (s * rs1)⁻¹ ∈ Q :=
        (Subgroup.mem_normalizer_iff.mp hnorm_s_rs1 y⁻¹).1 (Q.inv_mem hy)
      convert hqraw using 1
      group
    have hC1 : (⟨rs3⁻¹ * y⁻¹ * rs3, hq1⟩ : Q) ∈ C := by
      have h :=
        action_mem (a := rs3⁻¹) (z := y⁻¹)
          (by simpa [P0img] using P0img.inv_mem rhs3) (Q.inv_mem hy) hyinvC
      simpa using h
    have hC2 : (⟨s * y * s⁻¹, hq2⟩ : Q) ∈ C :=
      action_mem (a := s) (z := y) (by simpa [P0img] using hs) hy hyC
    have hC3 : (⟨s * rs1 * y⁻¹ * rs1⁻¹ * s⁻¹, hq3⟩ : Q) ∈ C := by
      have h :=
        action_mem (a := s * rs1) (z := y⁻¹)
          (P0img.mul_mem (by simpa [P0img] using hs) (by simpa [P0img] using rhs1))
          (Q.inv_mem hy) hyinvC
      convert h using 1
      group
    have hC12 :
        (⟨(rs3⁻¹ * y⁻¹ * rs3) * (s * y * s⁻¹), Q.mul_mem hq1 hq2⟩ :
          Q) ∈ C :=
      C.mul_mem hC1 hC2
    have hC123 :
        (⟨(rs3⁻¹ * y⁻¹ * rs3) * (s * y * s⁻¹) *
            (s * rs1 * y⁻¹ * rs1⁻¹ * s⁻¹),
          Q.mul_mem (Q.mul_mem hq1 hq2) hq3⟩ : Q) ∈ C :=
      C.mul_mem hC12 hC3
    have hC1234 :
        (⟨(rs3⁻¹ * y⁻¹ * rs3) * (s * y * s⁻¹) *
            (s * rs1 * y⁻¹ * rs1⁻¹ * s⁻¹) * y,
          Q.mul_mem (Q.mul_mem (Q.mul_mem hq1 hq2) hq3) hy⟩ : Q) ∈ C :=
      C.mul_mem hC123 hyC
    simpa [c10FixedTerm, φ, C, mul_assoc] using hC1234
  have hC10r_fixedTerm_eq_one_of_fixed
      (hfix : s * c10FixedTerm * s⁻¹ = c10FixedTerm) :
      c10FixedTerm = 1 := by
    exact appendixCEmbedding_commutatorAction_eq_one_of_fixed_by_P0
      (p := p) (q := q) σ hσ Q hP0Q hfixed
      (a := s) (x := c10FixedTerm)
      (by simpa [P0img] using hs) hsne hC10r_fixedTerm_mem_Q
      (by simpa [P0img] using hC10r_fixedTerm_mem_comm) hfix
  have hC10r_regrouped_eq_one :
      y⁻¹ * (s ^ 2 * y * s ^ (-2 : ℤ)) *
        (s ^ 2 * rs1 * y⁻¹ * rs1⁻¹ * s ^ (-2 : ℤ)) *
        (s * rs1 * y * rs1⁻¹ * s⁻¹) *
        (s * rs3⁻¹ * y⁻¹ * rs3 * s⁻¹) *
        (rs3⁻¹ * y * rs3) = 1 := by
    have hcomm1 : Commute s rs1 :=
      appendixCEmbedding_CP0InH_commute (p := p) (q := q) σ
        (by simpa [P0img] using hs) (by simpa [P0img] using rhs1)
    have hcomm3 : Commute s rs3 :=
      appendixCEmbedding_CP0InH_commute (p := p) (q := q) σ
        (by simpa [P0img] using hs) (by simpa [P0img] using rhs3)
    have hrs2_eq : rs2 = rs1⁻¹ * rs3⁻¹ := by
      have hprodQ :
          (⟨rs1, by simpa [P0img] using rhs1⟩ : P0img) *
              (⟨rs2, by simpa [P0img] using rhs2⟩ : P0img) *
              (⟨rs3, by simpa [P0img] using rhs3⟩ : P0img) = 1 := by
        ext
        simpa using hC10r_prod_eq_one
      have hrs2Q :
          (⟨rs2, by simpa [P0img] using rhs2⟩ : P0img) =
            (⟨rs1, by simpa [P0img] using rhs1⟩ : P0img)⁻¹ *
              (⟨rs3, by simpa [P0img] using rhs3⟩ : P0img)⁻¹ := by
        calc
          (⟨rs2, by simpa [P0img] using rhs2⟩ : P0img) =
              (⟨rs1, by simpa [P0img] using rhs1⟩ : P0img)⁻¹ *
                (((⟨rs1, by simpa [P0img] using rhs1⟩ : P0img) *
                    (⟨rs2, by simpa [P0img] using rhs2⟩ : P0img)) *
                  (⟨rs3, by simpa [P0img] using rhs3⟩ : P0img)) *
                (⟨rs3, by simpa [P0img] using rhs3⟩ : P0img)⁻¹ := by
                group
          _ = (⟨rs1, by simpa [P0img] using rhs1⟩ : P0img)⁻¹ *
                (1 : P0img) *
                (⟨rs3, by simpa [P0img] using rhs3⟩ : P0img)⁻¹ := by
                rw [hprodQ]
          _ = (⟨rs1, by simpa [P0img] using rhs1⟩ : P0img)⁻¹ *
                (⟨rs3, by simpa [P0img] using rhs3⟩ : P0img)⁻¹ := by
                simp
      simpa using congrArg Subtype.val hrs2Q
    have hsource_eq :
        y⁻¹ * (s ^ 2 * y * s ^ (-2 : ℤ)) *
          (s ^ 2 * rs1 * y⁻¹ * rs1⁻¹ * s ^ (-2 : ℤ)) *
          (s * rs1 * y * rs1⁻¹ * s⁻¹) *
          (s * rs3⁻¹ * y⁻¹ * rs3 * s⁻¹) *
          (rs3⁻¹ * y * rs3) =
        (y⁻¹ * s * y) ^ 2 * rs1 * (y⁻¹ * s * y)⁻¹ *
          (rs1⁻¹ * rs3⁻¹) * (y⁻¹ * s * y)⁻¹ * rs3 := by
      have h1 : rs1⁻¹ * s⁻¹ * rs1 = s⁻¹ := by
        rw [(hcomm1.symm.inv_left.inv_right).eq]
        group
      have h3 : rs3 * s⁻¹ * rs3⁻¹ = s⁻¹ := by
        rw [(hcomm3.symm.inv_right).eq]
        group
      rw [show y⁻¹ * (s ^ 2 * y * s ^ (-2 : ℤ)) *
          (s ^ 2 * rs1 * y⁻¹ * rs1⁻¹ * s ^ (-2 : ℤ)) *
          (s * rs1 * y * rs1⁻¹ * s⁻¹) *
          (s * rs3⁻¹ * y⁻¹ * rs3 * s⁻¹) *
          (rs3⁻¹ * y * rs3) =
          y⁻¹ * s ^ 2 * y * rs1 * y⁻¹ * (rs1⁻¹ * s⁻¹ * rs1) *
            y * rs1⁻¹ * rs3⁻¹ * y⁻¹ * (rs3 * s⁻¹ * rs3⁻¹) *
            y * rs3 by
            simp only [zpow_neg, zpow_ofNat]
            group]
      rw [h1, h3]
      simp only [pow_two]
      group
    exact hsource_eq.trans (by simpa [ht_eq, hrs2_eq] using hC10r)
  have hC10r_fixedTerm_fixed :
      s * c10FixedTerm * s⁻¹ = c10FixedTerm := by
    let A : G := rs3⁻¹ * y⁻¹ * rs3
    let B : G := s * y * s⁻¹
    let C : G := s * rs1 * y⁻¹ * rs1⁻¹ * s⁻¹
    let D : G := y
    have hnorm_rs1 : rs1 ∈ Subgroup.normalizer (Q : Set G) := by
      simpa [P0img] using hP0Q rhs1
    have hnorm_rs3 : rs3 ∈ Subgroup.normalizer (Q : Set G) := by
      simpa [P0img] using hP0Q rhs3
    have hAq : A ∈ Q := by
      have hnorm_rs3_inv :
          rs3⁻¹ ∈ Subgroup.normalizer (Q : Set G) :=
        (Subgroup.normalizer (Q : Set G)).inv_mem hnorm_rs3
      have hqraw : rs3⁻¹ * y⁻¹ * (rs3⁻¹)⁻¹ ∈ Q :=
        (Subgroup.mem_normalizer_iff.mp hnorm_rs3_inv y⁻¹).1 (Q.inv_mem hy)
      simpa [A] using hqraw
    have hBq : B ∈ Q := by
      simpa [B] using (Subgroup.mem_normalizer_iff.mp hs_norm_Q y).1 hy
    have hCq : C ∈ Q := by
      have hnorm_s_rs1 :
          s * rs1 ∈ Subgroup.normalizer (Q : Set G) :=
        (Subgroup.normalizer (Q : Set G)).mul_mem hs_norm_Q hnorm_rs1
      have hqraw : (s * rs1) * y⁻¹ * (s * rs1)⁻¹ ∈ Q :=
        (Subgroup.mem_normalizer_iff.mp hnorm_s_rs1 y⁻¹).1 (Q.inv_mem hy)
      convert hqraw using 1
      simp [C]
      group
    have hDq : D ∈ Q := by simpa [D] using hy
    have hsAq : s * A * s⁻¹ ∈ Q :=
      (Subgroup.mem_normalizer_iff.mp hs_norm_Q A).1 hAq
    have hsBq : s * B * s⁻¹ ∈ Q :=
      (Subgroup.mem_normalizer_iff.mp hs_norm_Q B).1 hBq
    have hsCq : s * C * s⁻¹ ∈ Q :=
      (Subgroup.mem_normalizer_iff.mp hs_norm_Q C).1 hCq
    have hc_def : c10FixedTerm = A * B * C * D := by
      simp [c10FixedTerm, A, B, C, D, mul_assoc]
    have hsource' :
        D⁻¹ * (s * B * s⁻¹) * (s * C * s⁻¹) * C⁻¹ *
          (s * A * s⁻¹) * A⁻¹ = 1 := by
      convert hC10r_regrouped_eq_one using 1
      simp [A, B, C, D, zpow_neg, zpow_ofNat, pow_two]
      group
    have hfix_aux : c10FixedTerm⁻¹ * (s * c10FixedTerm * s⁻¹) = 1 := by
      rw [hc_def]
      have hmul_conj :
          s * (A * B * C * D) * s⁻¹ =
            (s * A * s⁻¹) * (s * B * s⁻¹) * (s * C * s⁻¹) * B := by
        simp [A, B, C, D, mul_assoc]
      rw [hmul_conj]
      calc
        (A * B * C * D)⁻¹ * ((s * A * s⁻¹) * (s * B * s⁻¹) *
            (s * C * s⁻¹) * B)
            = B * B⁻¹ * (D⁻¹ * (s * B * s⁻¹) *
                (s * C * s⁻¹) * C⁻¹ * (s * A * s⁻¹) * A⁻¹) := by
              simpa using congrArg Subtype.val
                (show ((⟨A, hAq⟩ : Q) * (⟨B, hBq⟩ : Q) *
                      (⟨C, hCq⟩ : Q) * (⟨D, hDq⟩ : Q))⁻¹ *
                    ((⟨s * A * s⁻¹, hsAq⟩ : Q) *
                      (⟨s * B * s⁻¹, hsBq⟩ : Q) *
                      (⟨s * C * s⁻¹, hsCq⟩ : Q) *
                      (⟨B, hBq⟩ : Q)) =
                    (⟨B, hBq⟩ : Q) * (⟨B, hBq⟩ : Q)⁻¹ *
                      ((⟨D, hDq⟩ : Q)⁻¹ *
                        (⟨s * B * s⁻¹, hsBq⟩ : Q) *
                        (⟨s * C * s⁻¹, hsCq⟩ : Q) *
                        (⟨C, hCq⟩ : Q)⁻¹ *
                        (⟨s * A * s⁻¹, hsAq⟩ : Q) *
                        (⟨A, hAq⟩ : Q)⁻¹) by
                      simp only [mul_inv_rev]
                      ac_rfl)
        _ = D⁻¹ * (s * B * s⁻¹) * (s * C * s⁻¹) * C⁻¹ *
              (s * A * s⁻¹) * A⁻¹ := by simp
        _ = 1 := hsource'
    exact (inv_mul_eq_one.mp hfix_aux).symm
  have hC10r_source_endpoint_of_fixed
      (hfix : s * c10FixedTerm * s⁻¹ = c10FixedTerm) :
      rs1 * (y⁻¹ * rs1 * y)⁻¹ * t⁻¹ =
        t⁻¹ * (y⁻¹ * rs3 * y)⁻¹ * rs3 := by
    have hc10 : c10FixedTerm = 1 := hC10r_fixedTerm_eq_one_of_fixed hfix
    subst t
    have hc10' :
        (rs3⁻¹ * y⁻¹ * rs3 * s * y) *
            (rs1 * y⁻¹ * rs1⁻¹ * s⁻¹ * y) = 1 := by
      simpa [c10FixedTerm, mul_assoc] using hc10
    have htail :
        rs1 * y⁻¹ * rs1⁻¹ * s⁻¹ * y =
          (rs3⁻¹ * y⁻¹ * rs3 * s * y)⁻¹ := by
      exact eq_inv_of_mul_eq_one_right hc10'
    simpa [mul_assoc] using htail
  have hC10r_source_endpoint :
      rs1 * (y⁻¹ * rs1 * y)⁻¹ * t⁻¹ =
        t⁻¹ * (y⁻¹ * rs3 * y)⁻¹ * rs3 :=
    hC10r_source_endpoint_of_fixed hC10r_fixedTerm_fixed
  have hrs1_eq_sinv : rs1 = s⁻¹ := by
    let t1 : G := y⁻¹ * rs1 * y
    let t3 : G := y⁻¹ * rs3 * y
    have ht1_mem :
        t1 ∈ appendixCRightConjugate P0img y := by
      exact (appendixCRightConjugate_mem_iff P0img y t1).2
        ⟨rs1, by simpa [P0img] using rhs1, by simp [t1]⟩
    have ht3_mem :
        t3 ∈ appendixCRightConjugate P0img y := by
      exact (appendixCRightConjugate_mem_iff P0img y t3).2
        ⟨rs3, by simpa [P0img] using rhs3, by simp [t3]⟩
    have ht1_eq_tinv : t1 = t⁻¹ := by
      by_contra ht1_ne
      let g : G := t * t1
      have ht_mem' : t ∈ appendixCRightConjugate P0img y := by
        simpa [P0img] using ht
      have hg_mem :
          g ∈ appendixCRightConjugate P0img y := by
        exact (appendixCRightConjugate P0img y).mul_mem ht_mem' ht1_mem
      have hg_ne : g ≠ 1 := by
        intro hg
        apply ht1_ne
        have h := congrArg (fun z : G => t⁻¹ * z) hg
        simpa [g, mul_assoc] using h
      have hStep3_g :
          Himg ⊓ Himg.conjBy g = Uimg := by
        simpa [Himg, Uimg, P0img, g] using
          appendixCEmbedding_H_inf_conjBy_eq_CUInH_of_mem_rightConjugate_ne_one
            (p := p) (q := q) hA σ hσ Q hcop hy hP0Q hP1U hx hx1
            (by simpa [P0img] using hg_mem) hg_ne
      rcases appendixCE_exists_nontrivial_normOneUnit (p := p) (q := q) hx hx1 with
        ⟨u0, hu0_ne⟩
      let uimg : G := σ (SemidirectProduct.inr u0)
      let w : G := g * (rs1⁻¹ * uimg * rs1) * g⁻¹
      have hP0leH : P0img ≤ Himg := by
        intro a ha
        rcases ha with ⟨aH, _haH, rfl⟩
        exact ⟨aH, trivial, rfl⟩
      have hUleH : Uimg ≤ Himg := by
        intro a ha
        rcases ha with ⟨aH, _haH, rfl⟩
        exact ⟨aH, trivial, rfl⟩
      have huimg_mem : uimg ∈ Uimg := by
        exact ⟨SemidirectProduct.inr u0,
          (appendixCUInH_mem_iff (p := p) (q := q) _).2 ⟨u0, rfl⟩, rfl⟩
      have hrs1_H : rs1 ∈ Himg :=
        hP0leH (by simpa [P0img] using rhs1)
      have hrs3_H : rs3 ∈ Himg :=
        hP0leH (by simpa [P0img] using rhs3)
      have hinner_H : rs1⁻¹ * uimg * rs1 ∈ Himg :=
        Himg.mul_mem (Himg.mul_mem (Himg.inv_mem hrs1_H) (hUleH huimg_mem)) hrs1_H
      have hw_conj : w ∈ Himg.conjBy g := by
        change w ∈ Subgroup.map (MulAut.conj g).toMonoidHom Himg
        refine Subgroup.mem_map.mpr ⟨rs1⁻¹ * uimg * rs1, hinner_H, ?_⟩
        simp [w, MulAut.conj_apply, mul_assoc]
      have htnorm_U : t ∈ Subgroup.normalizer (Uimg : Set G) := by
        simpa [Uimg, P0img] using hP1U ht
      have ht3norm_U : t3 ∈ Subgroup.normalizer (Uimg : Set G) := by
        simpa [Uimg, P0img] using hP1U (by simpa [P0img] using ht3_mem)
      have htu_mem : t * uimg * t⁻¹ ∈ Uimg :=
        (Subgroup.mem_normalizer_iff.mp htnorm_U uimg).1 huimg_mem
      have ht3tu_mem : t3 * (t * uimg * t⁻¹) * t3⁻¹ ∈ Uimg :=
        (Subgroup.mem_normalizer_iff.mp ht3norm_U (t * uimg * t⁻¹)).1 htu_mem
      have hsource_endpoint' :
          rs1 * t1⁻¹ * t⁻¹ = t⁻¹ * t3⁻¹ * rs3 := by
        simpa [t1, t3, mul_assoc] using hC10r_source_endpoint
      have hw_eq_source :
          w = (t⁻¹ * t3⁻¹ * rs3)⁻¹ * uimg * (t⁻¹ * t3⁻¹ * rs3) := by
        have hg_eq : rs1 * g⁻¹ = t⁻¹ * t3⁻¹ * rs3 := by
          simpa [g, mul_assoc] using hsource_endpoint'
        calc
          w = (rs1 * g⁻¹)⁻¹ * uimg * (rs1 * g⁻¹) := by
                simp [w, mul_assoc]
          _ = (t⁻¹ * t3⁻¹ * rs3)⁻¹ * uimg * (t⁻¹ * t3⁻¹ * rs3) := by
                rw [hg_eq]
      have hw_H : w ∈ Himg := by
        rw [hw_eq_source]
        have hsource_H :
            (t⁻¹ * t3⁻¹ * rs3)⁻¹ * uimg * (t⁻¹ * t3⁻¹ * rs3) ∈ Himg := by
          have hcore_H : rs3⁻¹ * (t3 * (t * uimg * t⁻¹) * t3⁻¹) * rs3 ∈ Himg :=
            Himg.mul_mem
              (Himg.mul_mem (Himg.inv_mem hrs3_H) (hUleH ht3tu_mem)) hrs3_H
          convert hcore_H using 1
          group
        exact hsource_H
      have hw_U : w ∈ Uimg := by
        have hw_inf : w ∈ Himg ⊓ Himg.conjBy g := ⟨hw_H, hw_conj⟩
        simpa [hStep3_g] using hw_inf
      have hg_norm_U : g ∈ Subgroup.normalizer (Uimg : Set G) := by
        simpa [Uimg, P0img, g] using hP1U (by simpa [P0img] using hg_mem)
      have hinner_U : rs1⁻¹ * uimg * rs1 ∈ Uimg := by
        have hg_inv_norm_U :
            g⁻¹ ∈ Subgroup.normalizer (Uimg : Set G) :=
          (Subgroup.normalizer (Uimg : Set G)).inv_mem hg_norm_U
        have hmem := (Subgroup.mem_normalizer_iff.mp hg_inv_norm_U w).1 hw_U
        convert hmem using 1
        simp [w, mul_assoc]
      have hu0_eq_one :
          u0 = 1 :=
        appendixCEmbedding_normOneUnit_eq_one_of_P0_conj_mem_U
          (p := p) (q := q) hA σ hσ
          (s := rs1⁻¹)
          (by simpa [P0img] using P0img.inv_mem (by simpa [P0img] using rhs1))
          (by
            intro h
            exact hrs1_ne (inv_eq_one.mp h))
          u0 (by simpa [Uimg, uimg, mul_assoc] using hinner_U)
      exact hu0_ne hu0_eq_one
    have ht_inv_eq : t⁻¹ = y⁻¹ * s⁻¹ * y := by
      rw [ht_eq]
      group
    have hconj : y⁻¹ * rs1 * y = y⁻¹ * s⁻¹ * y := by
      rw [← ht_inv_eq]
      simpa [t1] using ht1_eq_tinv
    have h := congrArg (fun z : G => y * z * y⁻¹) hconj
    simpa [mul_assoc] using h
  have hC5r_endpoint_value :
      (((rv1Unit⁻¹ : appendixCNormOneUnits p q) :
          (appendixCField p q)ˣ) : appendixCField p q) +
        (((rTtInv3bunit⁻¹ : appendixCNormOneUnits p q) :
          (appendixCField p q)ˣ) : appendixCField p q) = 2 := by
    exact
      appendixCEmbedding_CP0_conj_normOneUnits_inv_add_inv_eq_two_of_C5
        (p := p) (q := q) σ hσ hsc_ne
        (s := s) (uimg := ru1) (vimg := rv1img)
        (z := rTtInv3bunit) (u0 := ru1Unit) (v0 := rv1Unit)
        hsc_img hru1Unit_img.symm hrv1Unit_img.symm
        (by
          simpa [hrTtInv3bunit_img, hrs1_eq_sinv, mul_assoc] using hC5r_1)
  change ∃ v : appendixCNormOneUnits p q,
    (((v : appendixCNormOneUnits p q) : (appendixCField p q)ˣ) :
      appendixCField p q) +
      ((((((rTtInv : appendixCNormOneUnits p q →
                appendixCNormOneUnits p q)^[3]) bunit)⁻¹ :
        appendixCNormOneUnits p q) : (appendixCField p q)ˣ) :
        appendixCField p q) = 2
  exact ⟨rv1Unit⁻¹, by simpa [rTtInv3bunit] using hC5r_endpoint_value⟩

/-- Companion-unit form of the remaining source product calculation in
Appendix C Lemma C.3, Step 4. The image of `x⁻¹` under the normalizer-induced
automorphism already lies in `U`; this statement isolates the source
calculation proving that its companion `2 - z` also lies in `U`. -/
public theorem CFSG.appendixC_lemma_C_3_twisted_companion_unit_of_conditionB_action
    [Fact q.Prime]
    (hA : appendixCConditionA p q) (hoddp : Odd p) (hoddq : Odd q)
    (hp3 : p ≠ 3)
    {G : Type u} [Group G] (σ : appendixCH p q →* G)
    (hσ : Function.Injective σ)
    (Q : Subgroup G) [Finite Q] [IsMulCommutative Q]
    (hcop : Nat.Coprime p (Nat.card Q))
    {y t : G} (hy : y ∈ Q)
    (hP0Q : appendixCNormalizes (Subgroup.map σ (appendixCP0InH p q)) Q)
    (hfixed :
      let P0img : Subgroup G := Subgroup.map σ (appendixCP0InH p q)
      let φ : P0img →* MulAut Q :=
        Q.normalizerMonoidHom.comp (Subgroup.inclusion hP0Q)
      letI : MulDistribMulAction P0img Q := MulDistribMulAction.compHom Q φ
      fixedPointSubgroup P0img Q ⊓ commutatorAction (A := P0img) (G := Q) = ⊥)
    (hycomm :
      let P0img : Subgroup G := Subgroup.map σ (appendixCP0InH p q)
      let φ : P0img →* MulAut Q :=
        Q.normalizerMonoidHom.comp (Subgroup.inclusion hP0Q)
      letI : MulDistribMulAction P0img Q := MulDistribMulAction.compHom Q φ
      (⟨y, hy⟩ : Q) ∈ commutatorAction (A := P0img) (G := Q))
    (hP1U :
      appendixCNormalizes
        (appendixCRightConjugate (Subgroup.map σ (appendixCP0InH p q)) y)
        (Subgroup.map σ (appendixCUInH p q)))
    (ht : t ∈ appendixCRightConjugate
      (Subgroup.map σ (appendixCP0InH p q)) y)
    (htne : t ≠ 1) :
    let Tunit : appendixCNormOneUnits p q ≃* appendixCNormOneUnits p q :=
      appendixCEmbedding_conjNormOneUnitsMulEquiv (p := p) (q := q)
        σ hσ
        ((Subgroup.normalizer
          (Subgroup.map σ (appendixCUInH p q) : Set G)).pow_mem
            (hP1U ht) 3)
    ∀ {x : appendixCField p q} (hx : x ∈ appendixCE p q), x ≠ 1 →
      ∃ h2z : (2 : appendixCField p q) -
          (((Tunit
            ⟨Units.mk0 x⁻¹
              (inv_ne_zero (appendixCE_ne_zero (p := p) (q := q) hx)),
              appendixCE_inv_unit_mem_normOneUnits (p := p) (q := q) hx⟩ :
            appendixCNormOneUnits p q) : (appendixCField p q)ˣ) :
            appendixCField p q) ≠ 0,
        Units.mk0
          ((2 : appendixCField p q) -
            (((Tunit
              ⟨Units.mk0 x⁻¹
                (inv_ne_zero (appendixCE_ne_zero (p := p) (q := q) hx)),
                appendixCE_inv_unit_mem_normOneUnits (p := p) (q := q) hx⟩ :
              appendixCNormOneUnits p q) : (appendixCField p q)ˣ) :
              appendixCField p q)) h2z ∈ appendixCNormOneUnits p q := by
  dsimp only
  intro x hx hx1
  let Tunit : appendixCNormOneUnits p q ≃* appendixCNormOneUnits p q :=
    appendixCEmbedding_conjNormOneUnitsMulEquiv (p := p) (q := q)
      σ hσ
      ((Subgroup.normalizer
        (Subgroup.map σ (appendixCUInH p q) : Set G)).pow_mem
          (hP1U ht) 3)
  let uinv : appendixCNormOneUnits p q :=
    ⟨Units.mk0 x⁻¹
      (inv_ne_zero (appendixCE_ne_zero (p := p) (q := q) hx)),
      appendixCE_inv_unit_mem_normOneUnits (p := p) (q := q) hx⟩
  let z : appendixCField p q :=
    (((Tunit uinv : appendixCNormOneUnits p q) : (appendixCField p q)ˣ) :
      appendixCField p q)
  let Uimg : Subgroup G := Subgroup.map σ (appendixCUInH p q)
  have ht_inv :
      t⁻¹ ∈ appendixCRightConjugate
        (Subgroup.map σ (appendixCP0InH p q)) y :=
    (appendixCRightConjugate
      (Subgroup.map σ (appendixCP0InH p q)) y).inv_mem ht
  have ht_inv_ne : t⁻¹ ≠ 1 := by
    intro h
    exact htne (inv_eq_one.mp h)
  let x' : appendixCField p q := (2 : appendixCField p q) - x
  have hx' : x' ∈ appendixCE p q := by
    simpa [x'] using appendixCE_two_sub_mem (p := p) (q := q) hx
  have hx'1 : x' ≠ 1 := by
    intro hx'one
    apply hx1
    have hxsub : (2 : appendixCField p q) - x = 1 := by
      simpa [x'] using hx'one
    calc
      x = (2 : appendixCField p q) - ((2 : appendixCField p q) - x) := by ring
      _ = (2 : appendixCField p q) - 1 := by rw [hxsub]
      _ = 1 := by ring
  let aunit : appendixCNormOneUnits p q :=
    ⟨Units.mk0 x (appendixCE_ne_zero (p := p) (q := q) hx),
      appendixCE_unit_mem_normOneUnits (p := p) (q := q) hx⟩
  let bunit' : appendixCNormOneUnits p q :=
    ⟨Units.mk0 ((2 : appendixCField p q) - x')
      (appendixCE_two_sub_ne_zero (p := p) (q := q) hx'),
      appendixCE_two_sub_unit_mem_normOneUnits (p := p) (q := q) hx'⟩
  have hbunit'_eq : bunit' = aunit := by
    apply Subtype.ext
    apply Units.ext
    simp [bunit', aunit, x']
  have htnorm_raw :
      t ∈ Subgroup.normalizer
        (Subgroup.map σ (appendixCUInH p q) : Set G) := by
    simpa using hP1U ht
  let Tt : appendixCNormOneUnits p q ≃* appendixCNormOneUnits p q :=
    appendixCEmbedding_conjNormOneUnitsMulEquiv (p := p) (q := q) σ hσ htnorm_raw
  let TtFromInv : appendixCNormOneUnits p q ≃* appendixCNormOneUnits p q :=
    appendixCEmbedding_conjNormOneUnitsMulEquiv (p := p) (q := q) σ hσ
      ((Subgroup.normalizer
        (Subgroup.map σ (appendixCUInH p q) : Set G)).inv_mem (hP1U ht_inv))
  have hunit_inj :
      Function.Injective
        (fun w : appendixCNormOneUnits p q => σ (SemidirectProduct.inr w)) := by
    intro a b hab
    have hpre : (SemidirectProduct.inr a : appendixCH p q) =
        SemidirectProduct.inr b := hσ hab
    have hright := congrArg (fun z : appendixCH p q => z.right) hpre
    simpa using hright
  have hTtFromInv_eq_Tt : TtFromInv = Tt := by
    apply MulEquiv.ext
    intro w
    apply hunit_inj
    calc
      σ (SemidirectProduct.inr (TtFromInv w))
          = t * σ (SemidirectProduct.inr w) * t⁻¹ := by
            have h :=
              appendixCEmbedding_conjNormOneUnitsMulEquiv_apply
                (p := p) (q := q) σ hσ
                ((Subgroup.normalizer
                  (Subgroup.map σ (appendixCUInH p q) : Set G)).inv_mem
                    (hP1U ht_inv)) w
            simpa [TtFromInv] using h
      _ = σ (SemidirectProduct.inr (Tt w)) := by
            exact (appendixCEmbedding_conjNormOneUnitsMulEquiv_apply
              (p := p) (q := q) σ hσ htnorm_raw w).symm
  have hTt_iter3_uinv_eq_Tunit :
      (((Tt : appendixCNormOneUnits p q → appendixCNormOneUnits p q)^[3]) uinv) =
        Tunit uinv := by
    apply hunit_inj
    have hiter := appendixCEmbedding_conjNormOneUnitsMulEquiv_iterate_apply
      (p := p) (q := q) σ hσ htnorm_raw uinv 3
    have happly := appendixCEmbedding_conjNormOneUnitsMulEquiv_apply
      (p := p) (q := q) σ hσ
      ((Subgroup.normalizer
        (Subgroup.map σ (appendixCUInH p q) : Set G)).pow_mem (hP1U ht) 3)
      uinv
    calc
      σ (SemidirectProduct.inr
          (((Tt : appendixCNormOneUnits p q → appendixCNormOneUnits p q)^[3])
            uinv))
          = t ^ 3 * σ (SemidirectProduct.inr uinv) * (t ^ 3)⁻¹ := by
            simpa [Tt] using hiter
      _ = σ (SemidirectProduct.inr (Tunit uinv)) := by
            have happly' :
                σ (SemidirectProduct.inr (Tunit uinv)) =
                  t ^ 3 * σ (SemidirectProduct.inr uinv) * (t ^ 3)⁻¹ := by
              simpa [Tunit] using happly
            exact happly'.symm
  have haunit_inv_eq_uinv : aunit⁻¹ = uinv := by
    ext
    simp [aunit, uinv]
  have hTt_iter3_inv :
      ((((Tt : appendixCNormOneUnits p q →
              appendixCNormOneUnits p q)^[3]) aunit)⁻¹) =
        (((Tt : appendixCNormOneUnits p q →
              appendixCNormOneUnits p q)^[3]) uinv) := by
    rw [show (((Tt : appendixCNormOneUnits p q →
              appendixCNormOneUnits p q)^[3]) aunit) =
        Tt (Tt (Tt aunit)) by rfl]
    rw [show (((Tt : appendixCNormOneUnits p q →
              appendixCNormOneUnits p q)^[3]) uinv) =
        Tt (Tt (Tt uinv)) by rfl]
    rw [← haunit_inv_eq_uinv]
    simp
  have hright_unit_eq :
      ((((TtFromInv : appendixCNormOneUnits p q →
              appendixCNormOneUnits p q)^[3]) bunit')⁻¹) =
        Tunit uinv := by
    rw [hTtFromInv_eq_Tt, hbunit'_eq]
    exact hTt_iter3_inv.trans hTt_iter3_uinv_eq_Tunit
  rcases appendixC_lemma_C_3_twisted_companion_value_of_conditionB_action
      (p := p) (q := q) hA hoddp hoddq hp3 σ hσ Q hcop hy hP0Q
      hfixed hycomm hP1U ht_inv ht_inv_ne (x := x') hx' hx'1 with
    ⟨v, hv⟩
  have hright_field_eq :
      ((((((TtFromInv : appendixCNormOneUnits p q →
                appendixCNormOneUnits p q)^[3]) bunit')⁻¹ :
        appendixCNormOneUnits p q) : (appendixCField p q)ˣ) :
        appendixCField p q) = z := by
    exact congrArg
      (fun w : appendixCNormOneUnits p q =>
        (((w : appendixCNormOneUnits p q) : (appendixCField p q)ˣ) :
          appendixCField p q))
      hright_unit_eq
  have hvz :
      (((v : appendixCNormOneUnits p q) : (appendixCField p q)ˣ) :
        appendixCField p q) + z = 2 := by
    rw [← hright_field_eq]
    simpa [TtFromInv, bunit', x'] using hv
  change ∃ h2z : (2 : appendixCField p q) - z ≠ 0,
    Units.mk0 ((2 : appendixCField p q) - z) h2z ∈ appendixCNormOneUnits p q
  exact appendixCNormOneUnits_two_sub_mem_of_add_eq (p := p) (q := q)
    (z := z) v hvz

/-- Unit-level form of the source product calculation in Appendix C Lemma C.3,
Step 4. The remaining work is to prove that the conjugation-induced
automorphism of `U` sends the unit attached to `x⁻¹` back to an element of
`E`. -/
public theorem CFSG.appendixC_lemma_C_3_twisted_unit_closure_of_conditionB_action
    [Fact q.Prime]
    (hA : appendixCConditionA p q) (hoddp : Odd p) (hoddq : Odd q)
    (hp3 : p ≠ 3)
    {G : Type u} [Group G] (σ : appendixCH p q →* G)
    (hσ : Function.Injective σ)
    (Q : Subgroup G) [Finite Q] [IsMulCommutative Q]
    (hcop : Nat.Coprime p (Nat.card Q))
    {y t : G} (hy : y ∈ Q)
    (hP0Q : appendixCNormalizes (Subgroup.map σ (appendixCP0InH p q)) Q)
    (hfixed :
      let P0img : Subgroup G := Subgroup.map σ (appendixCP0InH p q)
      let φ : P0img →* MulAut Q :=
        Q.normalizerMonoidHom.comp (Subgroup.inclusion hP0Q)
      letI : MulDistribMulAction P0img Q := MulDistribMulAction.compHom Q φ
      fixedPointSubgroup P0img Q ⊓ commutatorAction (A := P0img) (G := Q) = ⊥)
    (hycomm :
      let P0img : Subgroup G := Subgroup.map σ (appendixCP0InH p q)
      let φ : P0img →* MulAut Q :=
        Q.normalizerMonoidHom.comp (Subgroup.inclusion hP0Q)
      letI : MulDistribMulAction P0img Q := MulDistribMulAction.compHom Q φ
      (⟨y, hy⟩ : Q) ∈ commutatorAction (A := P0img) (G := Q))
    (hP1U :
      appendixCNormalizes
        (appendixCRightConjugate (Subgroup.map σ (appendixCP0InH p q)) y)
        (Subgroup.map σ (appendixCUInH p q)))
    (ht : t ∈ appendixCRightConjugate
      (Subgroup.map σ (appendixCP0InH p q)) y)
    (htne : t ≠ 1) :
    ∀ {x : appendixCField p q} (hx : x ∈ appendixCE p q), x ≠ 1 →
      (((appendixCEmbedding_conjNormOneUnitsMulEquiv (p := p) (q := q)
        σ hσ
        ((Subgroup.normalizer
          (Subgroup.map σ (appendixCUInH p q) : Set G)).pow_mem
            (hP1U ht) 3)
        ⟨Units.mk0 x⁻¹
          (inv_ne_zero (appendixCE_ne_zero (p := p) (q := q) hx)),
          appendixCE_inv_unit_mem_normOneUnits (p := p) (q := q) hx⟩ :
        appendixCNormOneUnits p q) : (appendixCField p q)ˣ) :
        appendixCField p q) ∈ appendixCE p q := by
  intro x hx hx1
  let Tunit : appendixCNormOneUnits p q ≃* appendixCNormOneUnits p q :=
    appendixCEmbedding_conjNormOneUnitsMulEquiv (p := p) (q := q)
      σ hσ
      ((Subgroup.normalizer
        (Subgroup.map σ (appendixCUInH p q) : Set G)).pow_mem
          (hP1U ht) 3)
  let uinv : appendixCNormOneUnits p q :=
    ⟨Units.mk0 x⁻¹
      (inv_ne_zero (appendixCE_ne_zero (p := p) (q := q) hx)),
      appendixCE_inv_unit_mem_normOneUnits (p := p) (q := q) hx⟩
  let z : appendixCField p q :=
    (((Tunit uinv : appendixCNormOneUnits p q) : (appendixCField p q)ˣ) :
      appendixCField p q)
  have hz : z ≠ 0 := by
    exact Units.ne_zero ((Tunit uinv : appendixCNormOneUnits p q) :
      (appendixCField p q)ˣ)
  have hzU : Units.mk0 z hz ∈ appendixCNormOneUnits p q := by
    have hunit : Units.mk0 z hz =
        ((Tunit uinv : appendixCNormOneUnits p q) : (appendixCField p q)ˣ) := by
      ext
      simp [z]
    rw [hunit]
    exact (Tunit uinv).property
  rcases appendixC_lemma_C_3_twisted_companion_unit_of_conditionB_action
      (p := p) (q := q) hA hoddp hoddq hp3 σ hσ Q hcop hy hP0Q
      hfixed hycomm hP1U ht htne (x := x) hx hx1 with
    ⟨h2z, h2zU⟩
  change z ∈ appendixCE p q
  exact appendixCE_of_units_mem_normOneUnits (p := p) (q := q) hz h2z hzU h2zU

/-- The source product calculation in Appendix C Lemma C.3, Step 4. Starting
from the condition-`(B)` action data, it proves the twisted one-step closure
`(a⁻¹)^{t^3} ∈ E` for every nontrivial `a ∈ E`. The surrounding theorem
constructs the actual normalizer-induced action `T`; this statement isolates
the remaining source product calculation. -/
public theorem CFSG.appendixC_lemma_C_3_twisted_closure_of_conditionB_action
    [Fact q.Prime]
    (hA : appendixCConditionA p q) (hoddp : Odd p) (hoddq : Odd q)
    (hp3 : p ≠ 3)
    {G : Type u} [Group G] (σ : appendixCH p q →* G)
    (hσ : Function.Injective σ)
    (Q : Subgroup G) [Finite Q] [IsMulCommutative Q]
    (hcop : Nat.Coprime p (Nat.card Q))
    {y t : G} (hy : y ∈ Q)
    (hP0Q : appendixCNormalizes (Subgroup.map σ (appendixCP0InH p q)) Q)
    (hfixed :
      let P0img : Subgroup G := Subgroup.map σ (appendixCP0InH p q)
      let φ : P0img →* MulAut Q :=
        Q.normalizerMonoidHom.comp (Subgroup.inclusion hP0Q)
      letI : MulDistribMulAction P0img Q := MulDistribMulAction.compHom Q φ
      fixedPointSubgroup P0img Q ⊓ commutatorAction (A := P0img) (G := Q) = ⊥)
    (hycomm :
      let P0img : Subgroup G := Subgroup.map σ (appendixCP0InH p q)
      let φ : P0img →* MulAut Q :=
        Q.normalizerMonoidHom.comp (Subgroup.inclusion hP0Q)
      letI : MulDistribMulAction P0img Q := MulDistribMulAction.compHom Q φ
      (⟨y, hy⟩ : Q) ∈ commutatorAction (A := P0img) (G := Q))
    (hP1U :
      appendixCNormalizes
        (appendixCRightConjugate (Subgroup.map σ (appendixCP0InH p q)) y)
        (Subgroup.map σ (appendixCUInH p q)))
    (ht : t ∈ appendixCRightConjugate
      (Subgroup.map σ (appendixCP0InH p q)) y)
    (htne : t ≠ 1) :
    appendixC_lemma_C_3_twisted_closure (p := p) (q := q)
      (appendixCFieldMapOfNormOneUnitsMulEquiv (p := p) (q := q)
        (appendixCEmbedding_conjNormOneUnitsMulEquiv (p := p) (q := q)
          σ hσ
      ((Subgroup.normalizer
        (Subgroup.map σ (appendixCUInH p q) : Set G)).pow_mem
          (hP1U ht) 3))) := by
  exact appendixC_lemma_C_3_twisted_closure_of_normOneUnitsMulEquiv
    (p := p) (q := q)
    (appendixCEmbedding_conjNormOneUnitsMulEquiv (p := p) (q := q)
      σ hσ
      ((Subgroup.normalizer
        (Subgroup.map σ (appendixCUInH p q) : Set G)).pow_mem
          (hP1U ht) 3))
    (appendixC_lemma_C_3_twisted_unit_closure_of_conditionB_action
      (p := p) (q := q) hA hoddp hoddq hp3 σ hσ Q hcop hy hP0Q
      hfixed hycomm hP1U ht htne)

/-- The source product calculation in Appendix C Lemma C.3, Step 4. Starting
from condition `(B)`, it constructs the conjugation action `T` and delegates
only the twisted one-step closure to the explicit product-calculation lemma. -/
public theorem CFSG.appendixC_lemma_C_3_twisted_step_data_of_conditionB
    [Fact q.Prime]
    (hA : appendixCConditionA p q) (hoddp : Odd p) (hoddq : Odd q)
    (hp3 : p ≠ 3) (hB : appendixCConditionB p q) :
    appendixC_lemma_C_3_twisted_step_data p q := by
  classical
  rcases appendixCConditionB_exists_commutatorAction_y (p := p) (q := q) hB with
    ⟨G, hG, σ, hσ, Q, hQfin, hQcomm, hcop, y, hy, hP0Q,
      hfixed, hycomm, hP1U⟩
  letI : Group G := hG
  letI : Finite Q := hQfin
  letI : IsMulCommutative Q := hQcomm
  let P0img : Subgroup G := Subgroup.map σ (appendixCP0InH p q)
  let Uimg : Subgroup G := Subgroup.map σ (appendixCUInH p q)
  let sH : appendixCH p q :=
    SemidirectProduct.inl (Multiplicative.ofAdd (1 : appendixCField p q))
  let s : G := σ sH
  have hsH : sH ∈ appendixCP0InH p q := by
    rw [appendixCP0InH_mem_iff]
    exact ⟨1, by simp [sH]⟩
  have hs : s ∈ P0img := by
    exact ⟨sH, hsH, rfl⟩
  have hsne : s ≠ 1 := by
    intro hs1
    have hpre : sH = 1 := by
      apply hσ
      simpa [s] using hs1
    have hleft := congrArg SemidirectProduct.left hpre
    have hadd := congrArg Multiplicative.toAdd hleft
    simp [sH] at hadd
  let t : G := y⁻¹ * s * y
  have ht : t ∈ appendixCRightConjugate
      (Subgroup.map σ (appendixCP0InH p q)) y := by
    change t ∈ Subgroup.map (MulAut.conj y⁻¹).toMonoidHom
      (Subgroup.map σ (appendixCP0InH p q))
    exact ⟨s, by simpa [P0img] using hs, by simp [t, mul_assoc]⟩
  have htne : t ≠ 1 := by
    intro ht1
    apply hsne
    have hconj := congrArg (fun z : G => y * z * y⁻¹) ht1
    simpa [t, mul_assoc] using hconj
  let Tunit : appendixCNormOneUnits p q ≃* appendixCNormOneUnits p q :=
    appendixCEmbedding_conjNormOneUnitsMulEquiv (p := p) (q := q) σ hσ
      ((Subgroup.normalizer (Uimg : Set G)).pow_mem (hP1U ht) 3)
  let Tfield : appendixCField p q → appendixCField p q :=
    appendixCFieldMapOfNormOneUnitsMulEquiv (p := p) (q := q) Tunit
  have hpow : ∀ u : appendixCNormOneUnits p q,
      (Tunit : appendixCNormOneUnits p q → appendixCNormOneUnits p q)^[p] u = u := by
    intro u
    simpa [Tunit, Uimg, P0img] using
      appendixCEmbedding_conjNormOneUnitsMulEquiv_pow_of_rightConjugate
        (p := p) (q := q) σ hσ (y := y) (t := t) hP1U ht u
  have hT : appendixC_lemma_C_3_twisted_map_data (p := p) (q := q) Tfield := by
    simpa [Tfield] using
      appendixC_lemma_C_3_twisted_map_data_of_normOneUnitsMulEquiv
        (p := p) (q := q) Tunit hpow
  have hclosure0 :
      appendixC_lemma_C_3_twisted_closure (p := p) (q := q)
        (appendixCFieldMapOfNormOneUnitsMulEquiv (p := p) (q := q)
          (appendixCEmbedding_conjNormOneUnitsMulEquiv (p := p) (q := q)
            σ hσ
            ((Subgroup.normalizer
              (Subgroup.map σ (appendixCUInH p q) : Set G)).pow_mem
                (hP1U ht) 3))) :=
    appendixC_lemma_C_3_twisted_closure_of_conditionB_action
      (p := p) (q := q) hA hoddp hoddq hp3 σ hσ Q hcop hy hP0Q
      hfixed hycomm hP1U ht htne
  have hclosure :
      appendixC_lemma_C_3_twisted_closure (p := p) (q := q) Tfield := by
    intro x hx hx1
    simpa [Tfield, Tunit, Uimg] using hclosure0 hx hx1
  exact appendixC_lemma_C_3_twisted_step_data_of_map_data
    (p := p) (q := q) (T := Tfield) hT hclosure

/-- The hard source group calculation in the non-`p = 3` branch of Lemma C.3:
for every nontrivial `a ∈ E`, it proves that `a⁻¹ ∈ E`. This is the source
calculation beginning with `a ∈ E#`, including the twisted-inverse closure and
the final odd-order iteration. -/
public theorem CFSG.appendixC_lemma_C_3_inv_mem_of_p_ne_three_ne_one
    [Fact q.Prime]
    (hA : appendixCConditionA p q) (hoddp : Odd p) (hoddq : Odd q)
    (hp3 : p ≠ 3) (hB : appendixCConditionB p q)
    {a : appendixCField p q} (ha : a ∈ appendixCE p q) (ha1 : a ≠ 1) :
    a⁻¹ ∈ appendixCE p q := by
  exact appendixC_lemma_C_3_inv_mem_of_twisted_step_data
    (p := p) (q := q)
    (appendixC_lemma_C_3_twisted_step_data_of_conditionB
      (p := p) (q := q) hA hoddp hoddq hp3 hB)
    hoddp ha ha1

/-- The hard source group calculation in the non-`p = 3` branch of Lemma C.3:
for every nontrivial `a ∈ E`, it proves the remaining norm equation for
`2-a⁻¹`. This is now only the field-norm projection of the sharper inverse
membership statement. -/
public theorem CFSG.appendixC_lemma_C_3_norm_two_sub_inv_of_p_ne_three_ne_one
    [Fact q.Prime]
    (hA : appendixCConditionA p q) (hoddp : Odd p) (hoddq : Odd q)
    (hp3 : p ≠ 3) (hB : appendixCConditionB p q)
    {a : appendixCField p q} (ha : a ∈ appendixCE p q) (ha1 : a ≠ 1) :
      (Algebra.norm (ZMod p) (S := appendixCField p q))
        ((2 : appendixCField p q) - a⁻¹) = 1 := by
  exact (appendixC_lemma_C_3_inv_mem_of_p_ne_three_ne_one
    (p := p) (q := q) hA hoddp hoddq hp3 hB ha ha1).2

/-- The hard source group calculation in the non-`p = 3` branch of Lemma C.3:
for every `a ∈ E`, it proves the remaining norm equation for `2-a⁻¹`. The
case `a = 1` is immediate, so the remaining proof is exactly the source's
`E#` calculation. -/
public theorem CFSG.appendixC_lemma_C_3_norm_two_sub_inv_of_p_ne_three
    [Fact q.Prime]
    (hA : appendixCConditionA p q) (hoddp : Odd p) (hoddq : Odd q)
    (hp3 : p ≠ 3) (hB : appendixCConditionB p q) :
    ∀ a : appendixCField p q, a ∈ appendixCE p q →
      (Algebra.norm (ZMod p) (S := appendixCField p q))
        ((2 : appendixCField p q) - a⁻¹) = 1 := by
  intro a ha
  by_cases ha1 : a = 1
  · subst a
    have h : (2 : appendixCField p q) - 1 = 1 := by ring
    simp [h]
  · exact appendixC_lemma_C_3_norm_two_sub_inv_of_p_ne_three_ne_one
      (p := p) (q := q) hA hoddp hoddq hp3 hB ha ha1

/-- The hard non-`p = 3` branch of Lemma C.3. The source proof is the main
Appendix C group calculation from hypothesis `(B)`, now isolated to the
second norm equation for inverses. -/
public theorem CFSG.appendixC_lemma_C_3_of_p_ne_three
    [Fact q.Prime]
    (hA : appendixCConditionA p q) (hoddp : Odd p) (hoddq : Odd q)
    (hp3 : p ≠ 3) (hB : appendixCConditionB p q) :
    appendixCInversionStable p q (appendixCE p q) := by
  exact appendixCInversionStable_of_norm_two_sub_inv (p := p) (q := q)
    (appendixC_lemma_C_3_norm_two_sub_inv_of_p_ne_three (p := p) (q := q)
      hA hoddp hoddq hp3 hB)


end
