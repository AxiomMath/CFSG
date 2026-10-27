module

public import Mathlib.GroupTheory.Coxeter.Matrix
public import CFSG.LocalAnalysis.StandardType.GGSecFiveOrthRefl
public import CFSG.LocalAnalysis.StandardType.GGSecFiveOrthTyGram
public import CFSG.LocalAnalysis.StandardType.GGSecFiveOrthSPermStab
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.Algebra.Group.Subgroup.Finite
public import Mathlib.Algebra.Group.Subgroup.Lattice

public section

namespace CFSG.StandardType.OrthF3

open TauCeti

private lemma ct_b1_eq_pm_one (x : ZMod 3) (hx : x ≠ 0) : x = 1 ∨ x = -1 := by
  revert x
  decide +kernel

private lemma ct_b1_sq_eq_one (x : ZMod 3) (hx : x ≠ 0) : x * x = 1 := by
  revert x
  decide +kernel

private lemma ct_b1_roots {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    {Q : QuadraticForm (ZMod 3) V} {r : Fin 5 → (V ≃ₗ[ZMod 3] V)}
    (hrefl : ∀ i, ∃ c : ZMod 3, c ≠ 0 ∧ OrthReflOfNorm Q c (r i)) :
    ∃ v : Fin 5 → V, (∀ i, Q (v i) ≠ 0) ∧
      (∀ i, r i * r i = 1) ∧
      (∀ i, ∀ w : V, r i w = w - (QuadraticMap.polar Q (v i) w / Q (v i)) • v i) := by
  classical
  choose c hc using hrefl
  choose v hv using fun i => (hc i).2
  refine ⟨v, ?_, ?_, ?_⟩
  · intro i
    obtain ⟨-, hQ, -⟩ := hv i
    rw [hQ]
    exact (hc i).1
  · intro i
    obtain ⟨hInv, hQ, hEq⟩ := hv i
    rw [← hEq, QuadraticMap.coe_reflectionOrthogonal, QuadraticMap.reflection_mul_self]
  · intro i w
    obtain ⟨hInv, hQ, hEq⟩ := hv i
    have : Invertible (Q (v i)) := hInv
    rw [← hEq, QuadraticMap.coe_reflectionOrthogonal,
      QuadraticMap.reflection_apply_eq_sub_div]

private lemma ct_b1_refl_eq_of_smul {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (Q : QuadraticForm (ZMod 3) V) {u v w : V} (hu : Q u ≠ 0) {c : ZMod 3} (hc : c ≠ 0)
    (hvu : v = c • u) :
    w - (QuadraticMap.polar Q u w / Q u) • u
      = w - (QuadraticMap.polar Q v w / Q v) • v := by
  have hu0 : u ≠ 0 := fun h => hu (by simp [h])
  subst hvu
  rw [QuadraticMap.map_smul, QuadraticMap.polar_smul_left, smul_smul]
  congr 1
  rw [smul_left_inj hu0]
  field_simp [hc, hu]
  ring

private lemma ct_b1_pair_linearIndependent {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (Q : QuadraticForm (ZMod 3) V) {u v : V} (hu : Q u ≠ 0) (hv : Q v ≠ 0)
    (hnot : ∀ c : ZMod 3, v ≠ c • u) : LinearIndependent (ZMod 3) ![u, v] := by
  rw [linearIndependent_fin2]
  change v ≠ 0 ∧ ∀ c : ZMod 3, c • v ≠ u
  constructor
  · intro hv0
    exact hv (by simp [hv0])
  · intro c hc
    have hc0 : c ≠ 0 := by
      intro h0
      apply hu
      rw [← hc, h0, zero_smul, map_zero]
    exact hnot c⁻¹ (by
      calc
        v = c⁻¹ • (c • v) := by rw [inv_smul_smul₀ hc0]
        _ = c⁻¹ • u := by rw [hc])

private lemma ct_b1_coeff_eq {V : Type} [AddCommGroup V] [Module (ZMod 3) V] {u v : V}
    (hli : LinearIndependent (ZMod 3) ![u, v]) {A B A' B' : ZMod 3}
    (h : A • u + B • v = A' • u + B' • v) : A = A' ∧ B = B' := by
  have h0 : (A - A') • u + (B - B') • v = 0 := by
    have hsub : (A - A') • u + (B - B') • v =
        (A • u + B • v) - (A' • u + B' • v) := by module
    rw [hsub, h, sub_self]
  have hz := (Fintype.linearIndependent_iff.mp hli) ![A - A', B - B'] (by
    simpa [Fin.sum_univ_two] using h0)
  constructor
  · exact sub_eq_zero.mp (by simpa using hz 0)
  · exact sub_eq_zero.mp (by simpa using hz 1)

private lemma ct_b1_label4_arith (a b t : ZMod 3) (ha : a ≠ 0) (hb : b ≠ 0) (ht : t ≠ 0)
    (h : let s := t * t / (a * b)
         let α := -1 + s
         let A := α * α - s
         let B := t / b * (1 - α)
         let C := t / a * (α - 1)
         let D := 1 - s
         A * A + B * C = 1 ∧ B * (A + D) = 0) :
    t * t = 2 * a * b := by
  revert a b t
  decide +kernel

private lemma ct_b1_label2 {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (Q : QuadraticForm (ZMod 3) V) {g h : V ≃ₗ[ZMod 3] V} {u v : V}
    (hu : Q u ≠ 0) (hv : Q v ≠ 0)
    (hg : ∀ w, g w = w - (QuadraticMap.polar Q u w / Q u) • u)
    (hh : ∀ w, h w = w - (QuadraticMap.polar Q v w / Q v) • v)
    (hg1 : g * g = 1) (hh1 : h * h = 1)
    (hne : g ≠ h) (hord : orderOf (g * h) = 2) :
    QuadraticMap.polar Q u v = 0 := by
  have h2 : (g * h) * (g * h) = 1 := by
    have h := pow_orderOf_eq_one (g * h)
    rw [hord, pow_two] at h
    exact h
  have hcomm : g * h = h * g := by
    calc
      g * h = (g * h)⁻¹ := (inv_eq_of_mul_eq_one_right h2).symm
      _ = h⁻¹ * g⁻¹ := mul_inv_rev g h
      _ = h * g := by rw [inv_eq_of_mul_eq_one_right hg1, inv_eq_of_mul_eq_one_right hh1]
  exact ((ggOrthGram_relations Q hu hv hg hh).1 hne).1 hcomm

private lemma ct_b1_label3 {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (Q : QuadraticForm (ZMod 3) V) {g h : V ≃ₗ[ZMod 3] V} {u v : V}
    (hu : Q u ≠ 0) (hv : Q v ≠ 0)
    (hg : ∀ w, g w = w - (QuadraticMap.polar Q u w / Q u) • u)
    (hh : ∀ w, h w = w - (QuadraticMap.polar Q v w / Q v) • v)
    (hg1 : g * g = 1) (hh1 : h * h = 1)
    (hord : orderOf (g * h) = 3) :
    QuadraticMap.polar Q u v ^ 2 = Q u * Q v ∧ QuadraticMap.polar Q u v ≠ 0 := by
  have h3 : (g * h) ^ 3 = 1 := by
    simpa [hord] using (pow_orderOf_eq_one (g * h) : (g * h) ^ orderOf (g * h) = 1)
  have hne : g * h ≠ h * g := by
    intro hcomm
    have h2 : (g * h) ^ 2 = 1 := by
      rw [pow_two]
      nth_rewrite 2 [hcomm]
      calc
        (g * h) * (h * g) = g * (h * h) * g := by group
        _ = 1 := by rw [hh1]; simp [hg1]
    have hdvd : orderOf (g * h) ∣ 2 := orderOf_dvd_of_pow_eq_one h2
    rw [hord] at hdvd
    norm_num at hdvd
  have hghne : g ≠ h := fun hgh => hne (by rw [hgh])
  have hne_root : QuadraticMap.polar Q u v ≠ 0 := by
    intro hp
    exact hne (((ggOrthGram_relations Q hu hv hg hh).1 hghne).2 hp)
  exact ⟨(ggOrthGram_relations Q hu hv hg hh).2 h3 hne, hne_root⟩

private lemma ct_b1_label4 {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (Q : QuadraticForm (ZMod 3) V) {g h : V ≃ₗ[ZMod 3] V} {u v : V}
    (hu : Q u ≠ 0) (hv : Q v ≠ 0)
    (hg : ∀ w, g w = w - (QuadraticMap.polar Q u w / Q u) • u)
    (hh : ∀ w, h w = w - (QuadraticMap.polar Q v w / Q v) • v)
    (hg1 : g * g = 1)
    (h4 : (g * h) ^ 4 = 1) (h2ne : (g * h) ^ 2 ≠ 1) :
    QuadraticMap.polar Q u v ^ 2 = 2 * Q u * Q v := by
  classical
  set a : ZMod 3 := Q u with ha
  set b : ZMod 3 := Q v with hb
  set t : ZMod 3 := QuadraticMap.polar Q u v with ht
  have ha0 : a ≠ 0 := by simpa [ha] using hu
  have hb0 : b ≠ 0 := by simpa [hb] using hv
  have hgne : g ≠ h := by
    intro hgh
    apply h2ne
    rw [← hgh, hg1]
    simp
  have hnot : ∀ c : ZMod 3, v ≠ c • u := by
    intro c hc
    apply hgne
    ext w
    have hc0 : c ≠ 0 := by
      intro h0
      apply hv
      rw [hb, hc, h0]
      simp
    have hEq := ct_b1_refl_eq_of_smul Q (w := w) (by rw [← ha]; exact hu) hc0 hc
    rw [hh w, hg w]
    simpa [← ha, ← hb] using hEq
  have hli : LinearIndependent (ZMod 3) ![u, v] :=
    ct_b1_pair_linearIndependent Q hu hv hnot
  set s : ZMod 3 := t * t / (a * b) with hs
  set α : ZMod 3 := -1 + s with hα
  set A : ZMod 3 := α * α - s with hA
  set B : ZMod 3 := t / b * (1 - α) with hB
  set C : ZMod 3 := t / a * (α - 1) with hC
  set D : ZMod 3 := 1 - s with hD
  have hgu : g u = -u := by
    rw [hg u, QuadraticMap.polar_self, ← ha]
    have h2 : (2 : ℕ) • a / a = 2 := by
      rw [nsmul_eq_mul]
      field_simp [ha0]
      norm_num
    rw [h2]
    module
  have hgv : g v = v - (t / a) • u := by
    rw [hg v, ← ht]
  have hhu : h u = u - (t / b) • v := by
    rw [hh u, QuadraticMap.polar_comm, ← ht]
  have hhv : h v = -v := by
    rw [hh v, QuadraticMap.polar_self, ← hb]
    have h2 : (2 : ℕ) • b / b = 2 := by
      rw [nsmul_eq_mul]
      field_simp [hb0]
      norm_num
    rw [h2]
    module
  have hGu : (g * h) u = α • u - (t / b) • v := by
    change g (h u) = _
    rw [hhu, map_sub, map_smul, hgu, hgv, smul_sub, smul_smul]
    rw [hα, hs]
    module
  have hGv : (g * h) v = (t / a) • u - v := by
    change g (h v) = _
    rw [hhv, map_neg, hgv]
    module
  have hEu : ((g * h) ^ 2) u = A • u + B • v := by
    rw [pow_two, LinearEquiv.mul_apply, hGu, map_sub, map_smul, map_smul, hGu, hGv]
    rw [hA, hB, hα, hs]
    module
  have hEv : ((g * h) ^ 2) v = C • u + D • v := by
    rw [pow_two, LinearEquiv.mul_apply, hGv, map_sub, map_smul, hGu, hGv]
    rw [hC, hD, hα, hs]
    module
  have hEEu : ((g * h) ^ 2) (((g * h) ^ 2) u) = (A * A + B * C) • u + (B * (A + D)) • v := by
    rw [hEu, map_add, map_smul, map_smul, hEu, hEv, smul_add, smul_add, smul_smul, smul_smul]
    module
  have hE2 : (g * h) ^ 2 * (g * h) ^ 2 = 1 := by
    rw [← pow_add, show (2 : ℕ) + 2 = 4 by norm_num]
    exact h4
  have hE2u : ((g * h) ^ 2) (((g * h) ^ 2) u) = u := by
    have := congrArg (fun e : V ≃ₗ[ZMod 3] V => e u) hE2
    simpa [LinearEquiv.mul_apply] using this
  have hcoeff : A * A + B * C = 1 ∧ B * (A + D) = 0 := by
    apply ct_b1_coeff_eq hli
    have h := hEEu.symm.trans hE2u
    simpa using h
  by_cases ht0 : t = 0
  · exfalso
    have hp0 : QuadraticMap.polar Q u v = 0 := by rw [← ht, ht0]
    have hGu0 : (g * h) u = -u := by
      rw [hGu]
      rw [show α = -1 by rw [hα, hs]; simp [ht0]]
      rw [show t / b = 0 by rw [ht0, zero_div]]
      module
    have hGv0 : (g * h) v = -v := by
      rw [hGv]
      rw [show t / a = 0 by rw [ht0, zero_div]]
      module
    have hGz : ∀ z, (g * h) z = z - (QuadraticMap.polar Q u z / a) • u
        - (QuadraticMap.polar Q v z / b) • v := by
      intro z
      change g (h z) = _
      rw [hh z, map_sub, map_smul, hg z, hgv, ht0, zero_div]
      module
    have hG2z : ∀ z, (g * h) ((g * h) z) = z := by
      intro z
      calc
        (g * h) ((g * h) z) =
            (g * h) (z - (QuadraticMap.polar Q u z / a) • u
              - (QuadraticMap.polar Q v z / b) • v) := by rw [hGz z]
        _ = (g * h) z - (QuadraticMap.polar Q u z / a) • ((g * h) u)
              - (QuadraticMap.polar Q v z / b) • ((g * h) v) := by
          rw [map_sub, map_sub, map_smul, map_smul]
        _ = (g * h) z - (QuadraticMap.polar Q u z / a) • (-u)
              - (QuadraticMap.polar Q v z / b) • (-v) := by rw [hGu0, hGv0]
        _ = z := by rw [hGz z]; module
    have hG2 : (g * h) ^ 2 = 1 := by
      ext z
      rw [pow_two, LinearEquiv.mul_apply]
      exact hG2z z
    exact h2ne hG2
  · have hrel := ct_b1_label4_arith a b t ha0 hb0 ht0 hcoeff
    simpa [ha, hb, ht, sq] using hrel

private lemma ct_b1_ne_of_order {G : Type} [Group G] {g h : G} {n : ℕ} (hg1 : g * g = 1)
    (hord : orderOf (g * h) = n) (hn : n ≠ 1) : g ≠ h := by
  intro hgh
  apply hn
  rw [← hord, ← hgh, hg1]
  exact orderOf_one

private lemma ct_b1_gram2 {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    {Q : QuadraticForm (ZMod 3) V} {v : Fin 5 → V} {r : Fin 5 → (V ≃ₗ[ZMod 3] V)}
    (hQv : ∀ i, Q (v i) ≠ 0) (hreflv : ∀ i, ∀ w, r i w = w - (QuadraticMap.polar Q (v i) w / Q (v i)) • v i)
    (hinv : ∀ i, r i * r i = 1)
    (hord : ∀ i j, i ≠ j → orderOf (r i * r j) = (CoxeterMatrix.B 5).M i j)
    {i j : Fin 5} (hij : i ≠ j) (hM : (CoxeterMatrix.B 5).M i j = 2) :
    QuadraticMap.polar Q (v i) (v j) = 0 := by
  have hordij : orderOf (r i * r j) = 2 := by rw [hord i j hij, hM]
  exact ct_b1_label2 Q (hQv i) (hQv j) (hreflv i) (hreflv j) (hinv i) (hinv j)
    (ct_b1_ne_of_order (hinv i) hordij (by norm_num)) hordij

private lemma ct_b1_gram3 {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    {Q : QuadraticForm (ZMod 3) V} {v : Fin 5 → V} {r : Fin 5 → (V ≃ₗ[ZMod 3] V)}
    (hQv : ∀ i, Q (v i) ≠ 0) (hreflv : ∀ i, ∀ w, r i w = w - (QuadraticMap.polar Q (v i) w / Q (v i)) • v i)
    (hinv : ∀ i, r i * r i = 1)
    (hord : ∀ i j, i ≠ j → orderOf (r i * r j) = (CoxeterMatrix.B 5).M i j)
    {i j : Fin 5} (hij : i ≠ j) (hM : (CoxeterMatrix.B 5).M i j = 3) :
    QuadraticMap.polar Q (v i) (v j) ^ 2 = Q (v i) * Q (v j) ∧
      QuadraticMap.polar Q (v i) (v j) ≠ 0 := by
  have hordij : orderOf (r i * r j) = 3 := by rw [hord i j hij, hM]
  exact ct_b1_label3 Q (hQv i) (hQv j) (hreflv i) (hreflv j) (hinv i) (hinv j) hordij

private lemma ct_b1_gram4 {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    {Q : QuadraticForm (ZMod 3) V} {v : Fin 5 → V} {r : Fin 5 → (V ≃ₗ[ZMod 3] V)}
    (hQv : ∀ i, Q (v i) ≠ 0) (hreflv : ∀ i, ∀ w, r i w = w - (QuadraticMap.polar Q (v i) w / Q (v i)) • v i)
    (hinv : ∀ i, r i * r i = 1)
    (hord : ∀ i j, i ≠ j → orderOf (r i * r j) = (CoxeterMatrix.B 5).M i j)
    {i j : Fin 5} (hij : i ≠ j) (hM : (CoxeterMatrix.B 5).M i j = 4) :
    QuadraticMap.polar Q (v i) (v j) ^ 2 = 2 * Q (v i) * Q (v j) := by
  have hordij : orderOf (r i * r j) = 4 := by rw [hord i j hij, hM]
  have h4 : (r i * r j) ^ 4 = 1 := by
    have h := pow_orderOf_eq_one (r i * r j)
    rw [hordij] at h
    exact h
  have h2ne : (r i * r j) ^ 2 ≠ 1 := by
    intro h2
    have hdvd : orderOf (r i * r j) ∣ 2 := orderOf_dvd_of_pow_eq_one h2
    rw [hordij] at hdvd
    norm_num at hdvd
  exact ct_b1_label4 Q (hQv i) (hQv j) (hreflv i) (hreflv j) (hinv i) h4 h2ne

private lemma ct_b1_step {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (Q : QuadraticForm (ZMod 3) V) {f v : V} {q : ZMod 3}
    (hq : q ≠ 0) (hfQ : Q f = q) (hvQ : Q v = -q)
    (hfv : QuadraticMap.polar Q f v ≠ 0) :
    let e : ZMod 3 := q * QuadraticMap.polar Q f v
    Q (f + e • v) = q ∧ (e = 1 ∨ e = -1) ∧
      QuadraticMap.polar Q (f + e • v) f = 0 ∧
      e * QuadraticMap.polar Q f v = q := by
  intro e
  set t : ZMod 3 := QuadraticMap.polar Q f v with ht
  have ht2 : t * t = 1 := ct_b1_sq_eq_one t hfv
  have hq2 : q * q = 1 := ct_b1_sq_eq_one q hq
  have he_ne : e ≠ 0 := by
    rw [show e = q * t from rfl]
    exact mul_ne_zero hq hfv
  have he_pm : e = 1 ∨ e = -1 := ct_b1_eq_pm_one e he_ne
  have het : e * t = q := by
    rw [show e = q * t from rfl]
    calc
      q * t * t = q * (t * t) := by ring
      _ = q * 1 := by rw [ht2]
      _ = q := by ring
  refine ⟨?_, he_pm, ?_, het⟩
  · rw [QuadraticMap.map_add Q, QuadraticMap.map_smul Q, hfQ, hvQ,
      QuadraticMap.polar_smul_right]
    have he2 : e * e = 1 := ct_b1_sq_eq_one e he_ne
    rw [show e * e = 1 from he2, one_smul]
    rw [show e • QuadraticMap.polar Q f v = e * QuadraticMap.polar Q f v by rw [smul_eq_mul]]
    rw [ht.symm, het]
    module
  · rw [QuadraticMap.polar_add_left, QuadraticMap.polar_smul_left,
      QuadraticMap.polar_comm Q v f, QuadraticMap.polar_self, hfQ]
    rw [ht.symm]
    rw [show e • t = e * t by rw [smul_eq_mul], het]
    rw [show (2 : ℕ) • q = (2 : ZMod 3) * q by rw [nsmul_eq_mul]; norm_num]
    rw [show (2 : ZMod 3) * q + q = 3 * q by ring]
    rw [show (3 : ZMod 3) = 0 by decide, zero_mul]

private lemma ct_b1_norm_eq_of_edge (qi qj t : ZMod 3) (hi : qi ≠ 0) (hj : qj ≠ 0)
    (ht : t ≠ 0) (h : t ^ 2 = qi * qj) : qi = qj := by
  revert qi qj t
  decide +kernel

private lemma ct_b1_norm_neg_of_edge (qi qj t : ZMod 3) (hi : qi ≠ 0) (hj : qj ≠ 0)
    (ht : t ≠ 0) (h : t ^ 2 = 2 * qi * qj) : qi = -qj := by
  revert qi qj t
  decide +kernel

private lemma ct_b1_ne_of_sq_eq_two_mul (qi qj t : ZMod 3) (hi : qi ≠ 0) (hj : qj ≠ 0)
    (h : t ^ 2 = 2 * qi * qj) : t ≠ 0 := by
  revert qi qj t
  decide +kernel

private lemma ct_b1_linearIndependent_of_orth {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (Q : QuadraticForm (ZMod 3) V) {n : ℕ} {f : Fin n → V}
    (hQ : ∀ i, Q (f i) ≠ 0)
    (horth : ∀ i j, i ≠ j → QuadraticMap.polar Q (f i) (f j) = 0) :
    LinearIndependent (ZMod 3) f := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro g hsum i
  have hmap : (QuadraticMap.polarBilin Q) (f i) (∑ j, g j • f j) = 0 := by
    rw [hsum]
    simp
  rw [map_sum] at hmap
  have hsingle : (QuadraticMap.polarBilin Q) (f i) (g i • f i) = 0 := by
    have h := Finset.sum_eq_single (s := Finset.univ)
      (f := fun j => ((QuadraticMap.polarBilin Q) (f i)) (g j • f j)) i ?_ ?_
    · rw [← hmap]
      exact h.symm
    · intro j _ hj
      rw [map_smul, QuadraticMap.polarBilin_apply_apply, horth i j hj.symm, smul_zero]
    · intro hi
      exact absurd (Finset.mem_univ i) hi
  have hps : QuadraticMap.polar Q (f i) (f i) ≠ 0 := by
    rw [QuadraticMap.polar_self,
      show (2 : ℕ) • Q (f i) = (2 : ZMod 3) * Q (f i) by rw [nsmul_eq_mul]; norm_num]
    exact mul_ne_zero (by decide) (hQ i)
  have : g i * QuadraticMap.polar Q (f i) (f i) = 0 := by
    simpa [QuadraticMap.polarBilin_apply_apply, smul_eq_mul] using hsingle
  exact (mul_eq_zero.mp this).resolve_right hps

private lemma ct_b1_gs {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (Q : QuadraticForm (ZMod 3) V) {v : Fin 5 → V}
    (hQv : ∀ i, Q (v i) ≠ 0)
    (ht01 : QuadraticMap.polar Q (v 0) (v 1) ^ 2 = Q (v 0) * Q (v 1) ∧
      QuadraticMap.polar Q (v 0) (v 1) ≠ 0)
    (ht12 : QuadraticMap.polar Q (v 1) (v 2) ^ 2 = Q (v 1) * Q (v 2) ∧
      QuadraticMap.polar Q (v 1) (v 2) ≠ 0)
    (ht23 : QuadraticMap.polar Q (v 2) (v 3) ^ 2 = Q (v 2) * Q (v 3) ∧
      QuadraticMap.polar Q (v 2) (v 3) ≠ 0)
    (ht34 : QuadraticMap.polar Q (v 3) (v 4) ^ 2 = 2 * Q (v 3) * Q (v 4))
    (h02 : QuadraticMap.polar Q (v 0) (v 2) = 0)
    (h03 : QuadraticMap.polar Q (v 0) (v 3) = 0)
    (h04 : QuadraticMap.polar Q (v 0) (v 4) = 0)
    (h13 : QuadraticMap.polar Q (v 1) (v 3) = 0)
    (h14 : QuadraticMap.polar Q (v 1) (v 4) = 0)
    (h24 : QuadraticMap.polar Q (v 2) (v 4) = 0)
    (hq01 : Q (v 0) = Q (v 1)) (hq12 : Q (v 1) = Q (v 2)) (hq23 : Q (v 2) = Q (v 3))
    (hq34 : Q (v 3) = -Q (v 4)) :
    ∃ f : Fin 5 → V, ∃ q : ZMod 3, q ≠ 0 ∧ (∀ i, Q (f i) = q) ∧
      (∀ i j, i ≠ j → QuadraticMap.polar Q (f i) (f j) = 0) ∧ v 4 = f 4 ∧
      (∀ i : Fin 4, ∃ ε : ZMod 3, (ε = 1 ∨ ε = -1) ∧
        v i.castSucc = ε • (f i.castSucc - f i.succ)) := by
  let q : ZMod 3 := Q (v 4)
  have hq4 : Q (v 4) = q := rfl
  have hq3 : Q (v 3) = -q := by rw [hq34]
  have hq2 : Q (v 2) = -q := by rw [hq23, hq3]
  have hq1 : Q (v 1) = -q := by rw [hq12, hq2]
  have hq0 : Q (v 0) = -q := by rw [hq01, hq1]
  have hq_ne : q ≠ 0 := by simpa [q] using hQv 4
  have ht34_ne : QuadraticMap.polar Q (v 3) (v 4) ≠ 0 :=
    ct_b1_ne_of_sq_eq_two_mul _ _ _ (hQv 3) (hQv 4) ht34
  let e3 : ZMod 3 := q * QuadraticMap.polar Q (v 4) (v 3)
  let f3 : V := v 4 + e3 • v 3
  let e2 : ZMod 3 := q * QuadraticMap.polar Q f3 (v 2)
  let f2 : V := f3 + e2 • v 2
  let e1 : ZMod 3 := q * QuadraticMap.polar Q f2 (v 1)
  let f1 : V := f2 + e1 • v 1
  let e0 : ZMod 3 := q * QuadraticMap.polar Q f1 (v 0)
  let f0 : V := f1 + e0 • v 0
  have ht3 : QuadraticMap.polar Q (v 4) (v 3) ≠ 0 := by
    rw [QuadraticMap.polar_comm]
    exact ht34_ne
  have hs3 := ct_b1_step Q hq_ne hq4 hq3 ht3
  dsimp only at hs3
  obtain ⟨hQf3, he3pm, hf3v4, he3t⟩ := hs3
  have he3_ne : e3 ≠ 0 := by
    dsimp [e3]
    exact mul_ne_zero hq_ne ht3
  have h42 : QuadraticMap.polar Q (v 4) (v 2) = 0 := by
    rw [QuadraticMap.polar_comm]; exact h24
  have h32 : QuadraticMap.polar Q (v 3) (v 2) ≠ 0 := by
    rw [QuadraticMap.polar_comm Q (v 3) (v 2)]; exact ht23.2
  have ht2eq : QuadraticMap.polar Q f3 (v 2) = e3 * QuadraticMap.polar Q (v 3) (v 2) := by
    dsimp [f3]
    rw [QuadraticMap.polar_add_left, QuadraticMap.polar_smul_left, h42, zero_add,
      smul_eq_mul]
  have ht2ne : QuadraticMap.polar Q f3 (v 2) ≠ 0 := by
    rw [ht2eq]; exact mul_ne_zero he3_ne h32
  have hs2 := ct_b1_step Q hq_ne hQf3 hq2 ht2ne
  dsimp only at hs2
  obtain ⟨hQf2, he2pm, hf2f3, he2t⟩ := hs2
  have he2_ne : e2 ≠ 0 := by
    dsimp [e2]
    exact mul_ne_zero hq_ne ht2ne
  have h41 : QuadraticMap.polar Q (v 4) (v 1) = 0 := by
    rw [QuadraticMap.polar_comm]; exact h14
  have h31 : QuadraticMap.polar Q (v 3) (v 1) = 0 := by
    rw [QuadraticMap.polar_comm]; exact h13
  have hf3v1 : QuadraticMap.polar Q f3 (v 1) = 0 := by
    dsimp [f3]
    rw [QuadraticMap.polar_add_left, QuadraticMap.polar_smul_left, h41, h31,
      zero_add, smul_zero]
  have ht1eq : QuadraticMap.polar Q f2 (v 1) = e2 * QuadraticMap.polar Q (v 2) (v 1) := by
    dsimp [f2]
    rw [QuadraticMap.polar_add_left, QuadraticMap.polar_smul_left, hf3v1, zero_add,
      smul_eq_mul]
  have h21 : QuadraticMap.polar Q (v 2) (v 1) ≠ 0 := by
    rw [QuadraticMap.polar_comm Q (v 2) (v 1)]; exact ht12.2
  have ht1ne : QuadraticMap.polar Q f2 (v 1) ≠ 0 := by
    rw [ht1eq]; exact mul_ne_zero he2_ne h21
  have hs1 := ct_b1_step Q hq_ne hQf2 hq1 ht1ne
  dsimp only at hs1
  obtain ⟨hQf1, he1pm, hf1f2, he1t⟩ := hs1
  have he1_ne : e1 ≠ 0 := by
    dsimp [e1]
    exact mul_ne_zero hq_ne ht1ne
  have h40 : QuadraticMap.polar Q (v 4) (v 0) = 0 := by
    rw [QuadraticMap.polar_comm]; exact h04
  have h30 : QuadraticMap.polar Q (v 3) (v 0) = 0 := by
    rw [QuadraticMap.polar_comm]; exact h03
  have h20 : QuadraticMap.polar Q (v 2) (v 0) = 0 := by
    rw [QuadraticMap.polar_comm]; exact h02
  have hf3v0 : QuadraticMap.polar Q f3 (v 0) = 0 := by
    dsimp [f3]
    rw [QuadraticMap.polar_add_left, QuadraticMap.polar_smul_left, h40, h30,
      zero_add, smul_zero]
  have hf2v0 : QuadraticMap.polar Q f2 (v 0) = 0 := by
    dsimp [f2]
    rw [QuadraticMap.polar_add_left, QuadraticMap.polar_smul_left, hf3v0, h20,
      zero_add, smul_zero]
  have ht0eq : QuadraticMap.polar Q f1 (v 0) = e1 * QuadraticMap.polar Q (v 1) (v 0) := by
    dsimp [f1]
    rw [QuadraticMap.polar_add_left, QuadraticMap.polar_smul_left, hf2v0, zero_add,
      smul_eq_mul]
  have h10 : QuadraticMap.polar Q (v 1) (v 0) ≠ 0 := by
    rw [QuadraticMap.polar_comm Q (v 1) (v 0)]; exact ht01.2
  have ht0ne : QuadraticMap.polar Q f1 (v 0) ≠ 0 := by
    rw [ht0eq]; exact mul_ne_zero he1_ne h10
  have hs0 := ct_b1_step Q hq_ne hQf1 hq0 ht0ne
  dsimp only at hs0
  obtain ⟨hQf0, he0pm, hf0f1, he0t⟩ := hs0
  have he0_ne : e0 ≠ 0 := by
    dsimp [e0]
    exact mul_ne_zero hq_ne ht0ne
  let f : Fin 5 → V := ![f0, f1, f2, f3, v 4]
  have hf0 : f 0 = f0 := rfl
  have hf1 : f 1 = f1 := rfl
  have hf2 : f 2 = f2 := rfl
  have hf3 : f 3 = f3 := rfl
  have hf4 : f 4 = v 4 := rfl
  have hfQ : ∀ i, Q (f i) = q := by
    intro i
    fin_cases i
    · simp only
      exact hQf0
    · simp only
      exact hQf1
    · simp only
      exact hQf2
    · simp only
      exact hQf3
    · simp only
      exact hq4
  have hp34 : QuadraticMap.polar Q f3 (v 4) = 0 := by
    dsimp [f3]; exact hf3v4
  have hp23 : QuadraticMap.polar Q f2 f3 = 0 := by
    dsimp [f2]; exact hf2f3
  have hp12 : QuadraticMap.polar Q f1 f2 = 0 := by
    dsimp [f1]; exact hf1f2
  have hp01 : QuadraticMap.polar Q f0 f1 = 0 := by
    dsimp [f0]; exact hf0f1
  have hp24 : QuadraticMap.polar Q f2 (v 4) = 0 := by
    dsimp [f2, f3]
    rw [QuadraticMap.polar_add_left, QuadraticMap.polar_smul_left, hf3v4, h24,
      smul_zero, zero_add]
  have hp14 : QuadraticMap.polar Q f1 (v 4) = 0 := by
    dsimp [f1]
    rw [QuadraticMap.polar_add_left, QuadraticMap.polar_smul_left, hp24, h14,
      smul_zero, zero_add]
  have hp13 : QuadraticMap.polar Q f1 f3 = 0 := by
    dsimp [f1, f3]
    rw [QuadraticMap.polar_add_left, QuadraticMap.polar_smul_left, hp23,
      QuadraticMap.polar_add_right, QuadraticMap.polar_smul_right, h14, h13]
    simp
  have hp04 : QuadraticMap.polar Q f0 (v 4) = 0 := by
    dsimp [f0]
    rw [QuadraticMap.polar_add_left, QuadraticMap.polar_smul_left, hp14, h04,
      smul_zero, zero_add]
  have hp03 : QuadraticMap.polar Q f0 f3 = 0 := by
    dsimp [f0, f3]
    rw [QuadraticMap.polar_add_left, QuadraticMap.polar_smul_left, hp13,
      QuadraticMap.polar_add_right, QuadraticMap.polar_smul_right, h04, h03]
    simp
  have hp02 : QuadraticMap.polar Q f0 f2 = 0 := by
    dsimp [f0, f2, f3]
    rw [QuadraticMap.polar_add_left, QuadraticMap.polar_smul_left, hp12,
      QuadraticMap.polar_add_right, QuadraticMap.polar_smul_right,
      QuadraticMap.polar_add_right, QuadraticMap.polar_smul_right, h04, h03, h02]
    simp
  have horth_lt : ∀ i j : Fin 5, i < j → QuadraticMap.polar Q (f i) (f j) = 0 := by
    intro i j hij
    fin_cases i <;> fin_cases j
    · exact absurd hij (by decide)
    · change QuadraticMap.polar Q f0 f1 = 0
      exact hp01
    · change QuadraticMap.polar Q f0 f2 = 0
      exact hp02
    · change QuadraticMap.polar Q f0 f3 = 0
      exact hp03
    · change QuadraticMap.polar Q f0 (v 4) = 0
      exact hp04
    · exact absurd hij (by decide)
    · exact absurd hij (by decide)
    · change QuadraticMap.polar Q f1 f2 = 0
      exact hp12
    · change QuadraticMap.polar Q f1 f3 = 0
      exact hp13
    · change QuadraticMap.polar Q f1 (v 4) = 0
      exact hp14
    · exact absurd hij (by decide)
    · exact absurd hij (by decide)
    · exact absurd hij (by decide)
    · change QuadraticMap.polar Q f2 f3 = 0
      exact hp23
    · change QuadraticMap.polar Q f2 (v 4) = 0
      exact hp24
    · exact absurd hij (by decide)
    · exact absurd hij (by decide)
    · exact absurd hij (by decide)
    · exact absurd hij (by decide)
    · change QuadraticMap.polar Q f3 (v 4) = 0
      exact hp34
    · exact absurd hij (by decide)
    · exact absurd hij (by decide)
    · exact absurd hij (by decide)
    · exact absurd hij (by decide)
    · exact absurd hij (by decide)
  have hf_orth : ∀ i j, i ≠ j → QuadraticMap.polar Q (f i) (f j) = 0 := by
    intro i j hij
    rcases lt_or_gt_of_ne hij with h | h
    · exact horth_lt i j h
    · rw [QuadraticMap.polar_comm]; exact horth_lt j i h
  refine ⟨f, q, hq_ne, hfQ, hf_orth, hf4.symm, ?_⟩
  intro i
  fin_cases i
  · refine ⟨e0, he0pm, ?_⟩
    change v 0 = e0 • (f0 - f1)
    have h : f0 - f1 = e0 • v 0 := by
      rw [show f0 = f1 + e0 • v 0 from rfl, add_sub_cancel_left]
    rw [h, ← smul_assoc, smul_eq_mul, ct_b1_sq_eq_one e0 he0_ne, one_smul]
  · refine ⟨e1, he1pm, ?_⟩
    change v 1 = e1 • (f1 - f2)
    have h : f1 - f2 = e1 • v 1 := by
      rw [show f1 = f2 + e1 • v 1 from rfl, add_sub_cancel_left]
    rw [h, ← smul_assoc, smul_eq_mul, ct_b1_sq_eq_one e1 he1_ne, one_smul]
  · refine ⟨e2, he2pm, ?_⟩
    change v 2 = e2 • (f2 - f3)
    have h : f2 - f3 = e2 • v 2 := by
      rw [show f2 = f3 + e2 • v 2 from rfl, add_sub_cancel_left]
    rw [h, ← smul_assoc, smul_eq_mul, ct_b1_sq_eq_one e2 he2_ne, one_smul]
  · refine ⟨e3, he3pm, ?_⟩
    change v 3 = e3 • (f3 - v 4)
    have h : f3 - v 4 = e3 • v 3 := by
      rw [show f3 = v 4 + e3 • v 3 from rfl, add_sub_cancel_left]
    rw [h, ← smul_assoc, smul_eq_mul, ct_b1_sq_eq_one e3 he3_ne, one_smul]

private lemma ct_b1_refl_neg {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    {Q : QuadraticForm (ZMod 3) V} {f : Fin 5 → V} {q : ZMod 3} (hq : q ≠ 0)
    (hfQ : ∀ i, Q (f i) = q)
    (horth : ∀ i j, i ≠ j → QuadraticMap.polar Q (f i) (f j) = 0)
    {c : Fin 5} {u : V} (hu : u = f c) {g : V ≃ₗ[ZMod 3] V}
    (hg : ∀ w, g w = w - (QuadraticMap.polar Q u w / Q u) • u) :
    g (f c) = -f c ∧ ∀ j, j ≠ c → g (f j) = f j := by
  constructor
  · rw [hg, hu]
    have hpol : QuadraticMap.polar Q (f c) (f c) = 2 * q := by
      rw [QuadraticMap.polar_self, hfQ c,
        show (2 : ℕ) • q = (2 : ZMod 3) * q by rw [nsmul_eq_mul]; norm_num]
    have hdiv : QuadraticMap.polar Q (f c) (f c) / Q (f c) = 2 := by
      rw [hpol, hfQ c, mul_div_assoc, div_self hq, mul_one]
    rw [hdiv]
    calc f c - (2 : ZMod 3) • f c
        = (1 : ZMod 3) • f c - (2 : ZMod 3) • f c := by rw [one_smul]
      _ = ((1 : ZMod 3) - 2) • f c := by rw [sub_smul]
      _ = -f c := by rw [show (1 : ZMod 3) - 2 = -1 by decide, neg_one_smul]
  · intro j hj
    rw [hg, hu, horth c j (Ne.symm hj)]
    simp

private lemma ct_b1_refl_swap {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    {Q : QuadraticForm (ZMod 3) V} {f : Fin 5 → V} {q : ZMod 3} (hq : q ≠ 0)
    (hfQ : ∀ i, Q (f i) = q)
    (horth : ∀ i j, i ≠ j → QuadraticMap.polar Q (f i) (f j) = 0)
    {a b : Fin 5} (hab : a ≠ b) {ε : ZMod 3} (hε : ε = 1 ∨ ε = -1) {u : V}
    (hu : u = ε • (f a - f b)) {g : V ≃ₗ[ZMod 3] V}
    (hg : ∀ w, g w = w - (QuadraticMap.polar Q u w / Q u) • u) :
    g (f a) = f b ∧ g (f b) = f a ∧ ∀ j, j ≠ a → j ≠ b → g (f j) = f j := by
  have hε2 : ε * ε = 1 := by rcases hε with h | h <;> rw [h] <;> decide
  have hεm : -ε * ε = -1 := by rw [neg_mul, hε2]
  have h2q : (2 : ZMod 3) * q ≠ 0 := mul_ne_zero (by decide) hq
  have hps : ∀ i : Fin 5, QuadraticMap.polar Q (f i) (f i) = 2 * q := by
    intro i
    rw [QuadraticMap.polar_self, hfQ i,
      show (2 : ℕ) • q = (2 : ZMod 3) * q by rw [nsmul_eq_mul]; norm_num]
  have hQsub : Q (f a - f b) = 2 * q := by
    rw [sub_eq_add_neg, QuadraticMap.map_add Q, QuadraticMap.map_neg,
      QuadraticMap.polar_neg_right, horth a b hab, hfQ a, hfQ b]
    ring
  have hQu : Q u = 2 * q := by
    rw [hu, QuadraticMap.map_smul, hQsub, hε2, one_smul]
  have hpolua : QuadraticMap.polar Q u (f a) = ε * 2 * q := by
    rw [hu, QuadraticMap.polar_smul_left, QuadraticMap.polar_sub_left, hps a,
      horth b a (Ne.symm hab), sub_zero, smul_eq_mul]
    ring
  have hpolub : QuadraticMap.polar Q u (f b) = -ε * 2 * q := by
    rw [hu, QuadraticMap.polar_smul_left, QuadraticMap.polar_sub_left, horth a b hab,
      hps b, zero_sub, smul_eq_mul]
    ring
  have hpoluj : ∀ j : Fin 5, j ≠ a → j ≠ b → QuadraticMap.polar Q u (f j) = 0 := by
    intro j hja hjb
    rw [hu, QuadraticMap.polar_smul_left, QuadraticMap.polar_sub_left,
      horth a j (Ne.symm hja), horth b j (Ne.symm hjb)]
    simp
  have hdiva : QuadraticMap.polar Q u (f a) / Q u = ε := by
    rw [hpolua, hQu, show ε * 2 * q = ε * (2 * q) by ring,
      mul_div_cancel_right₀ ε h2q]
  have hdivb : QuadraticMap.polar Q u (f b) / Q u = -ε := by
    rw [hpolub, hQu, show -ε * 2 * q = (-ε) * (2 * q) by ring,
      mul_div_cancel_right₀ (-ε) h2q]
  refine ⟨?_, ?_, ?_⟩
  · rw [hg, hdiva, hu, smul_smul, hε2, one_smul]
    abel
  · rw [hg, hdivb, hu, smul_smul, hεm, neg_one_smul]
    abel
  · intro j hja hjb
    rw [hg, hpoluj j hja hjb]
    simp

private lemma ct_b1_mem_swap {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    {Q : QuadraticForm (ZMod 3) V} (fB : Module.Basis (Fin 5) (ZMod 3) V) {q : ZMod 3}
    (hq : q ≠ 0) (hfQ : ∀ i, Q (fB i) = q)
    (horth : ∀ i j, i ≠ j → QuadraticMap.polar Q (fB i) (fB j) = 0)
    (a b : Fin 5) (hab : a ≠ b) {ε : ZMod 3} (hε : ε = 1 ∨ ε = -1) {u : V}
    (hu : u = ε • (fB a - fB b)) {g : V ≃ₗ[ZMod 3] V}
    (hg : ∀ w, g w = w - (QuadraticMap.polar Q u w / Q u) • u) :
    g ∈ ggOrthSignedPerms fB := by
  obtain ⟨ha, hb, hj⟩ := ct_b1_refl_swap hq hfQ horth hab hε hu hg
  refine ⟨Equiv.swap a b, fun _ => 1, fun _ => Or.inl rfl, fun k => ?_⟩
  by_cases hk : k = a
  · subst hk; rw [ha]; simp [Equiv.swap_apply_left]
  · by_cases hk' : k = b
    · subst hk'; rw [hb]; simp [Equiv.swap_apply_right]
    · rw [hj k hk hk']; simp [Equiv.swap_apply_of_ne_of_ne hk hk']

private lemma ct_b1_mem {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    {Q : QuadraticForm (ZMod 3) V} (fB : Module.Basis (Fin 5) (ZMod 3) V) {q : ZMod 3} (hq : q ≠ 0)
    (hfQ : ∀ i, Q (fB i) = q)
    (horth : ∀ i j, i ≠ j → QuadraticMap.polar Q (fB i) (fB j) = 0)
    {r : Fin 5 → (V ≃ₗ[ZMod 3] V)} {v : Fin 5 → V}
    (hreflv : ∀ i, ∀ w : V, r i w = w - (QuadraticMap.polar Q (v i) w / Q (v i)) • v i)
    (hv4 : v 4 = fB 4)
    (hstep : ∀ i : Fin 4, ∃ ε : ZMod 3, (ε = 1 ∨ ε = -1) ∧
      v i.castSucc = ε • (fB i.castSucc - fB i.succ)) (i : Fin 5) :
    r i ∈ ggOrthSignedPerms fB := by
  fin_cases i
  · obtain ⟨ε, hε, hv⟩ := hstep (0 : Fin 4)
    exact ct_b1_mem_swap fB hq hfQ horth 0 1 (by decide) hε hv (hreflv 0)
  · obtain ⟨ε, hε, hv⟩ := hstep (1 : Fin 4)
    exact ct_b1_mem_swap fB hq hfQ horth 1 2 (by decide) hε hv (hreflv 1)
  · obtain ⟨ε, hε, hv⟩ := hstep (2 : Fin 4)
    exact ct_b1_mem_swap fB hq hfQ horth 2 3 (by decide) hε hv (hreflv 2)
  · obtain ⟨ε, hε, hv⟩ := hstep (3 : Fin 4)
    exact ct_b1_mem_swap fB hq hfQ horth 3 4 (by decide) hε hv (hreflv 3)
  · obtain ⟨hneg, hfix⟩ := ct_b1_refl_neg (c := 4) hq hfQ horth (u := v 4) hv4 (hreflv 4)
    refine ⟨1, fun j => if j = 4 then -1 else 1, ?_, ?_⟩
    · intro j
      by_cases hj : j = 4 <;> simp [hj]
    · intro j
      by_cases hj : j = 4
      · subst hj
        change r 4 (fB 4) = (-1 : ZMod 3) • fB 4
        rw [hneg, neg_one_smul]
      · change r 4 (fB j) = (fun j => if j = 4 then -1 else 1) j • fB j
        rw [hfix j hj]
        simp [hj]

private lemma ct_b1_tail {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    {Q : QuadraticForm (ZMod 3) V} (hdim : Module.finrank (ZMod 3) V = 5)
    (r : Fin 5 → (V ≃ₗ[ZMod 3] V)) {v : Fin 5 → V}
    (hreflv : ∀ i, ∀ w : V, r i w = w - (QuadraticMap.polar Q (v i) w / Q (v i)) • v i)
    {f : Fin 5 → V} {q : ZMod 3} (hq_ne : q ≠ 0) (hfQ : ∀ i, Q (f i) = q)
    (hf_orth : ∀ i j, i ≠ j → QuadraticMap.polar Q (f i) (f j) = 0)
    (hv4 : v 4 = f 4)
    (hstep : ∀ i : Fin 4, ∃ ε : ZMod 3, (ε = 1 ∨ ε = -1) ∧
      v i.castSucc = ε • (f i.castSucc - f i.succ))
    (hcard : Nat.card ↥(Subgroup.closure (Set.range r)) = 3840) :
    ∃ fB : Module.Basis (Fin 5) (ZMod 3) V, Subgroup.closure (Set.range r) = ggOrthSignedPerms fB := by
  have hli := ct_b1_linearIndependent_of_orth Q (fun i => by rw [hfQ i]; exact hq_ne) hf_orth
  have hcard_eq : Fintype.card (Fin 5) = Module.finrank (ZMod 3) V := by simp [hdim]
  let fB := basisOfLinearIndependentOfCardEqFinrank (K := ZMod 3) hli hcard_eq
  have hfB : ⇑fB = f := coe_basisOfLinearIndependentOfCardEqFinrank hli hcard_eq
  have hfQ' : ∀ i, Q (fB i) = q := by intro i; rw [hfB]; exact hfQ i
  have horth' : ∀ i j, i ≠ j → QuadraticMap.polar Q (fB i) (fB j) = 0 := by
    intro i j hij; rw [hfB]; exact hf_orth i j hij
  have hv4' : v 4 = fB 4 := by rw [hv4, hfB]
  have hstep' : ∀ i : Fin 4, ∃ ε : ZMod 3, (ε = 1 ∨ ε = -1) ∧
      v i.castSucc = ε • (fB i.castSucc - fB i.succ) := by
    intro i
    obtain ⟨ε, hε, hv⟩ := hstep i
    exact ⟨ε, hε, by rw [hv, hfB]⟩
  have hmem : ∀ i, r i ∈ ggOrthSignedPerms fB :=
    fun i => ct_b1_mem fB hq_ne hfQ' horth' hreflv hv4' hstep' i
  have hle : Subgroup.closure (Set.range r) ≤ ggOrthSignedPerms fB :=
    (Subgroup.closure_le _).mpr (by rintro _ ⟨i, rfl⟩; exact hmem i)
  have : Finite ↥(ggOrthSignedPerms fB) :=
    Nat.finite_of_card_ne_zero (by rw [card_ggOrthSignedPerms fB]; decide)
  refine ⟨fB, Subgroup.eq_of_le_of_card_ge hle ?_⟩
  rw [card_ggOrthSignedPerms fB, hcard]
  norm_num [Nat.factorial]

theorem ggOrthB5_model {V : Type} [AddCommGroup V] [Module (ZMod 3) V] {Q : QuadraticForm (ZMod 3) V}
    (hdim : Module.finrank (ZMod 3) V = 5)
    (r : Fin 5 → (V ≃ₗ[ZMod 3] V)) (hrefl : ∀ i, ∃ c : ZMod 3, c ≠ 0 ∧ OrthReflOfNorm Q c (r i))
    (hord : ∀ i j, i ≠ j → orderOf (r i * r j) = (CoxeterMatrix.B 5).M i j)
    (hcard : Nat.card ↥(Subgroup.closure (Set.range r)) = 3840) :
    ∃ f : Module.Basis (Fin 5) (ZMod 3) V, Subgroup.closure (Set.range r) = ggOrthSignedPerms f := by
  classical
  obtain ⟨v, hQv, hinv, hreflv⟩ := ct_b1_roots hrefl
  have ht01 := ct_b1_gram3 (Q := Q) (v := v) (r := r) hQv hreflv hinv hord
    (i := 0) (j := 1) (by decide) (by decide)
  have ht12 := ct_b1_gram3 (Q := Q) (v := v) (r := r) hQv hreflv hinv hord
    (i := 1) (j := 2) (by decide) (by decide)
  have ht23 := ct_b1_gram3 (Q := Q) (v := v) (r := r) hQv hreflv hinv hord
    (i := 2) (j := 3) (by decide) (by decide)
  have ht34 := ct_b1_gram4 (Q := Q) (v := v) (r := r) hQv hreflv hinv hord
    (i := 3) (j := 4) (by decide) (by decide)
  have h02 := ct_b1_gram2 (Q := Q) (v := v) (r := r) hQv hreflv hinv hord
    (i := 0) (j := 2) (by decide) (by decide)
  have h03 := ct_b1_gram2 (Q := Q) (v := v) (r := r) hQv hreflv hinv hord
    (i := 0) (j := 3) (by decide) (by decide)
  have h04 := ct_b1_gram2 (Q := Q) (v := v) (r := r) hQv hreflv hinv hord
    (i := 0) (j := 4) (by decide) (by decide)
  have h13 := ct_b1_gram2 (Q := Q) (v := v) (r := r) hQv hreflv hinv hord
    (i := 1) (j := 3) (by decide) (by decide)
  have h14 := ct_b1_gram2 (Q := Q) (v := v) (r := r) hQv hreflv hinv hord
    (i := 1) (j := 4) (by decide) (by decide)
  have h24 := ct_b1_gram2 (Q := Q) (v := v) (r := r) hQv hreflv hinv hord
    (i := 2) (j := 4) (by decide) (by decide)
  have ht34_ne : QuadraticMap.polar Q (v 3) (v 4) ≠ 0 :=
    ct_b1_ne_of_sq_eq_two_mul _ _ _ (hQv 3) (hQv 4) ht34
  have hq01 : Q (v 0) = Q (v 1) :=
    ct_b1_norm_eq_of_edge _ _ _ (hQv 0) (hQv 1) ht01.2 ht01.1
  have hq12 : Q (v 1) = Q (v 2) :=
    ct_b1_norm_eq_of_edge _ _ _ (hQv 1) (hQv 2) ht12.2 ht12.1
  have hq23 : Q (v 2) = Q (v 3) :=
    ct_b1_norm_eq_of_edge _ _ _ (hQv 2) (hQv 3) ht23.2 ht23.1
  have hq34 : Q (v 3) = -Q (v 4) :=
    ct_b1_norm_neg_of_edge _ _ _ (hQv 3) (hQv 4) ht34_ne ht34
  obtain ⟨f, q, hq_ne, hfQ, hf_orth, hv4, hstep⟩ :=
    ct_b1_gs Q hQv ht01 ht12 ht23 ht34 h02 h03 h04 h13 h14 h24 hq01 hq12 hq23 hq34
  exact ct_b1_tail hdim r hreflv hq_ne hfQ hf_orth hv4 hstep hcard

end CFSG.StandardType.OrthF3

end
