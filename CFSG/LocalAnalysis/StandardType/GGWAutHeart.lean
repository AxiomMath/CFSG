module

public import CFSG.LocalAnalysis.StandardType.GGWAutOrthOdd
public import CFSG.LocalAnalysis.StandardType.GGWAutEngine
public import CFSG.LocalAnalysis.StandardType.GGQTwoLin
public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoTransfer
public import CFSG.LocalAnalysis.StandardType.GGRCAbsIrred
public import CFSG.LocalAnalysis.StandardType.GGRCMonomial
public import CFSG.LocalAnalysis.StandardType.GGQTwoQuandleE

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Module QTwoLin

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private lemma ggWAutH_hP (D : GGQ2Lin 3) (e : Fin 6 ≃ D.ι)
    (hE6 : D.coxeter = CoxeterMatrix.E₆.reindex e) :
    ∀ i j : Fin 6, D.root (e i) (D.coroot (e j)) = (CartanMatrix.E 6 i j : ZMod 3) := by
  intro i j
  rw [D.pairing, ggQ2xQ_cartan_E6 D e hE6 i j]

private lemma ggWAutH_conn {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (h : Fin 6 → V) (α : Fin 6 → Dual (ZMod 3) V)
    (hP : ∀ i j, α i (h j) = (CartanMatrix.E 6 i j : ZMod 3)) :
    ∀ i j : Fin 6, Relation.ReflTransGen (fun a b => α a (h b) ≠ 0 ∧ α b (h a) ≠ 0) i j := by
  let rel : Fin 6 → Fin 6 → Prop := fun a b => α a (h b) ≠ 0 ∧ α b (h a) ≠ 0
  have r02 : rel 0 2 := ⟨by rw [hP]; decide +kernel, by rw [hP]; decide +kernel⟩
  have r13 : rel 1 3 := ⟨by rw [hP]; decide +kernel, by rw [hP]; decide +kernel⟩
  have r23 : rel 2 3 := ⟨by rw [hP]; decide +kernel, by rw [hP]; decide +kernel⟩
  have r34 : rel 3 4 := ⟨by rw [hP]; decide +kernel, by rw [hP]; decide +kernel⟩
  have r45 : rel 4 5 := ⟨by rw [hP]; decide +kernel, by rw [hP]; decide +kernel⟩
  have hc : ∀ i : Fin 6, Relation.ReflTransGen rel i 3 := by
    intro i
    fin_cases i
    · exact (Relation.ReflTransGen.single r02).trans (Relation.ReflTransGen.single r23)
    · exact Relation.ReflTransGen.single r13
    · exact Relation.ReflTransGen.single r23
    · exact Relation.ReflTransGen.refl
    · exact Relation.ReflTransGen.single ⟨r34.2, r34.1⟩
    · exact (Relation.ReflTransGen.single ⟨r45.2, r45.1⟩).trans
        (Relation.ReflTransGen.single ⟨r34.2, r34.1⟩)
  have hc' : ∀ j : Fin 6, Relation.ReflTransGen rel 3 j := by
    intro j
    fin_cases j
    · exact (Relation.ReflTransGen.single ⟨r23.2, r23.1⟩).trans
        (Relation.ReflTransGen.single ⟨r02.2, r02.1⟩)
    · exact Relation.ReflTransGen.single ⟨r13.2, r13.1⟩
    · exact Relation.ReflTransGen.single ⟨r23.2, r23.1⟩
    · exact Relation.ReflTransGen.refl
    · exact Relation.ReflTransGen.single r34
    · exact (Relation.ReflTransGen.single r34).trans (Relation.ReflTransGen.single r45)
  intro i j
  exact (hc i).trans (hc' j)

private theorem ggWAutH_absIrred {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (h : Fin 6 → V) (α : Fin 6 → Dual (ZMod 3) V)
    (hα : ∀ i, α i (h i) = 2)
    (hspan : Submodule.span (ZMod 3) (Set.range h) = ⊤)
    (hker : ∀ w, (∀ i, α i w = 0) → w = 0)
    (hconn : ∀ i j, Relation.ReflTransGen (fun a b => α a (h b) ≠ 0 ∧ α b (h a) ≠ 0) i j) :
    ZS.AbsIrred 3 (E6QTwo.e6Weyl (h := h) (α := α) hα) := by
  refine ggRC_absIrred_of_connected (p := 3) (by norm_num)
    (fun i => Module.reflection (hα i)) h α ?_ hα hspan hker hconn
    (E6QTwo.e6Weyl (h := h) (α := α) hα) rfl
  intro i w
  exact reflection_apply w (hα i)

private lemma ggWAutH_weyl_eq (D : GGQ2Lin 3) (e : Fin 6 ≃ D.ι)
    (hα : ∀ i : Fin 6, D.root (e i) (D.coroot (e i)) = 2) :
    D.weyl = E6QTwo.e6Weyl (h := fun i => D.coroot (e i)) (α := fun i => D.root (e i)) hα := by
  have hrange : Set.range (fun i : Fin 6 => D.simpleRefl (e i)) = Set.range D.simpleRefl := by
    rw [show (fun i : Fin 6 => D.simpleRefl (e i)) = D.simpleRefl ∘ e from rfl,
      Set.range_comp, Equiv.range_eq_univ, Set.image_univ]
  have hfun : (fun i : Fin 6 => D.simpleRefl (e i)) =
      (fun i => Module.reflection (hα i)) := by
    funext i
    rw [GGQ2Lin.simpleRefl, Subsingleton.elim (D.root_coroot_self (e i)) (hα i)]
  rw [GGQ2Lin.weyl, GGQ2Lin.parab, Set.image_univ, ← hrange, hfun, E6QTwo.e6Weyl]

private lemma ggWAutH_B_sum_left {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    {h : Fin 6 → V} {α : Fin 6 → Dual (ZMod 3) V} {B : LinearMap.BilinForm (ZMod 3) V}
    (_hB : ∀ i v, B (h i) v = α i v) (c : Fin 6 → ZMod 3) (y : V) :
    B (∑ i, c i • h i) y = ∑ i, c i * B (h i) y := by
  rw [map_sum]
  simp only [LinearMap.sum_apply, map_smul, LinearMap.smul_apply, smul_eq_mul]

private lemma ggWAutH_B_expand {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    {h : Fin 6 → V} {α : Fin 6 → Dual (ZMod 3) V} {B : LinearMap.BilinForm (ZMod 3) V}
    (hP : ∀ i j, α i (h j) = (CartanMatrix.E 6 i j : ZMod 3))
    (hB : ∀ i v, B (h i) v = α i v) (c d : Fin 6 → ZMod 3) :
    B (∑ i, c i • h i) (∑ j, d j • h j) =
      ∑ i, ∑ j, c i * d j * (CartanMatrix.E 6 i j : ZMod 3) := by
  rw [ggWAutH_B_sum_left hB c]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_sum]
  simp only [map_smul, smul_eq_mul, hB, hP]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

private def ggWAutH_ccoef : Fin 6 → ZMod 3
  | 0 => 0 | 1 => 1 | 2 => 1 | 3 => 2 | 4 => 2 | 5 => 2

private def ggWAutH_v1coef : Fin 6 → ZMod 3
  | 0 => 0 | 1 => 1 | 2 => 0 | 3 => 0 | 4 => 0 | 5 => 0

private def ggWAutH_v2coef : Fin 6 → ZMod 3
  | 0 => 0 | 1 => 0 | 2 => 1 | 3 => 0 | 4 => 0 | 5 => 0

private def ggWAutH_v3coef : Fin 6 → ZMod 3
  | 0 => 0 | 1 => 0 | 2 => 0 | 3 => 0 | 4 => 1 | 5 => 0

private def ggWAutH_v4coef : Fin 6 → ZMod 3
  | 0 => 0 | 1 => 1 | 2 => 1 | 3 => 2 | 4 => 1 | 5 => 0

private lemma ggWAutH_span_of_orthogonal {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    [FiniteDimensional (ZMod 3) V] {B : LinearMap.BilinForm (ZMod 3) V}
    (hdim : Module.finrank (ZMod 3) V = 5) {w : Fin 5 → V}
    (horth : ∀ i j, i ≠ j → B (w i) (w j) = 0)
    (hnorm : ∀ i, B (w i) (w i) ≠ 0) :
    Submodule.span (ZMod 3) (Set.range w) = ⊤ := by
  have hli : LinearIndependent (ZMod 3) w := by
    rw [Fintype.linearIndependent_iff]
    intro g hg k
    have h := congrArg (fun x => B x (w k)) hg
    simp only [map_sum, map_smul, LinearMap.smul_apply, LinearMap.sum_apply,
      LinearMap.zero_apply, map_zero] at h
    rw [Finset.sum_eq_single k] at h
    · rcases smul_eq_zero.mp h with h1 | h1
      · exact h1
      · exact absurd h1 (hnorm k)
    · intro i _ hik
      rw [horth i k hik, smul_zero]
    · intro hk; exact absurd (Finset.mem_univ k) hk
  have hfin : Module.finrank (ZMod 3) (Submodule.span (ZMod 3) (Set.range w)) = 5 := by
    rw [finrank_span_eq_card hli, Fintype.card_fin]
  exact Submodule.eq_top_of_finrank_eq (by rw [hfin, hdim])

private theorem ggWAutH_neg_sRefl_mem {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    [FiniteDimensional (ZMod 3) V] [Finite V]
    {h : Fin 6 → V} {α : Fin 6 → Dual (ZMod 3) V} {B : LinearMap.BilinForm (ZMod 3) V}
    (hP : ∀ i j, α i (h j) = (CartanMatrix.E 6 i j : ZMod 3))
    (hV : Nat.card V = 3 ^ 5) (hB : ∀ i v, B (h i) v = α i v) (hα : ∀ i, α i (h i) = 2)
    (hdim : Module.finrank (ZMod 3) V = 5)
    {c : V} (hc : c ≠ 0) (hcc : B c c = 1) :
    ∃ g ∈ E6QTwo.e6Weyl (h := h) (α := α) hα, ∀ u, g u = -(u + B c u • c) := by
  classical
  let c0 : V := ∑ i, ggWAutH_ccoef i • h i
  let vcoef : Fin 4 → Fin 6 → ZMod 3
    | 0 => ggWAutH_v1coef
    | 1 => ggWAutH_v2coef
    | 2 => ggWAutH_v3coef
    | 3 => ggWAutH_v4coef
  let v : Fin 4 → V := fun k => ∑ i, vcoef k i • h i
  have hBc0c0 : B c0 c0 = 1 := by
    dsimp only [c0]; rw [ggWAutH_B_expand hP hB]; decide +kernel
  have hBv : ∀ k : Fin 4, B (v k) (v k) = 2 := by
    intro k
    fin_cases k <;> (dsimp only [v, vcoef]; rw [ggWAutH_B_expand hP hB]; decide +kernel)
  have hBc0v : ∀ k : Fin 4, B c0 (v k) = 0 := by
    intro k
    fin_cases k <;> (dsimp only [c0, v, vcoef]; rw [ggWAutH_B_expand hP hB]; decide +kernel)
  have hBvv : ∀ k l : Fin 4, k ≠ l → B (v k) (v l) = 0 := by
    intro k l hkl
    fin_cases k <;> fin_cases l <;>
      first
        | exact (hkl rfl).elim
        | (dsimp only [v, vcoef]; rw [ggWAutH_B_expand hP hB]; decide +kernel)
  have hBvc0 : ∀ k : Fin 4, B (v k) c0 = 0 := fun k => by
    rw [E6QTwo.bilinForm_symm hP hV hB (v k) c0, hBc0v k]
  choose s hsW hsform using fun k : Fin 4 =>
    E6QTwo.exists_mem_e6Weyl_reflection hP hV hB hα (hBv k)
  let p : V ≃ₗ[ZMod 3] V := s 0 * s 1 * s 2 * s 3
  have hpW : p ∈ E6QTwo.e6Weyl (h := h) (α := α) hα :=
    mul_mem (mul_mem (mul_mem (hsW 0) (hsW 1)) (hsW 2)) (hsW 3)
  have hs_c0 : ∀ j, s j c0 = c0 := by
    intro j
    rw [hsform j c0, hBvc0 j, zero_smul, sub_zero]
  have hp_c0 : p c0 = c0 := by
    dsimp only [p]
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, LinearEquiv.mul_apply,
      hs_c0 3, hs_c0 2, hs_c0 1, hs_c0 0]
  have hs_v_ne : ∀ j k : Fin 4, j ≠ k → s j (v k) = v k := by
    intro j k hjk
    rw [hsform j (v k), hBvv j k hjk, zero_smul, sub_zero]
  have hs_v_eq : ∀ k : Fin 4, s k (v k) = - v k := by
    intro k
    rw [hsform k (v k), hBv k]
    module
  have hp_v : ∀ k : Fin 4, p (v k) = - v k := by
    intro k
    fin_cases k
    · dsimp only [p]
      rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, LinearEquiv.mul_apply,
        hs_v_ne 3 0 (by decide), hs_v_ne 2 0 (by decide), hs_v_ne 1 0 (by decide), hs_v_eq 0]
    · dsimp only [p]
      rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, LinearEquiv.mul_apply,
        hs_v_ne 3 1 (by decide), hs_v_ne 2 1 (by decide), hs_v_eq 1, map_neg,
        hs_v_ne 0 1 (by decide)]
    · dsimp only [p]
      rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, LinearEquiv.mul_apply,
        hs_v_ne 3 2 (by decide), hs_v_eq 2, map_neg, hs_v_ne 1 2 (by decide), map_neg,
        hs_v_ne 0 2 (by decide)]
    · dsimp only [p]
      rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, LinearEquiv.mul_apply,
        hs_v_eq 3, map_neg, hs_v_ne 2 3 (by decide), map_neg, hs_v_ne 1 3 (by decide), map_neg,
        hs_v_ne 0 3 (by decide)]
  let w : Fin 5 → V
    | 0 => c0
    | 1 => v 0
    | 2 => v 1
    | 3 => v 2
    | 4 => v 3
  have hnorm : ∀ i : Fin 5, B (w i) (w i) ≠ 0 := by
    intro i
    fin_cases i <;> dsimp only [w]
    · rw [hBc0c0]; decide
    · rw [hBv 0]; decide
    · rw [hBv 1]; decide
    · rw [hBv 2]; decide
    · rw [hBv 3]; decide
  have horth : ∀ i j : Fin 5, i ≠ j → B (w i) (w j) = 0 := by
    intro i j hij
    fin_cases i <;> fin_cases j
    · exact (hij rfl).elim
    · exact hBc0v 0
    · exact hBc0v 1
    · exact hBc0v 2
    · exact hBc0v 3
    · exact hBvc0 0
    · exact (hij rfl).elim
    · exact hBvv 0 1 (by decide)
    · exact hBvv 0 2 (by decide)
    · exact hBvv 0 3 (by decide)
    · exact hBvc0 1
    · exact hBvv 1 0 (by decide)
    · exact (hij rfl).elim
    · exact hBvv 1 2 (by decide)
    · exact hBvv 1 3 (by decide)
    · exact hBvc0 2
    · exact hBvv 2 0 (by decide)
    · exact hBvv 2 1 (by decide)
    · exact (hij rfl).elim
    · exact hBvv 2 3 (by decide)
    · exact hBvc0 3
    · exact hBvv 3 0 (by decide)
    · exact hBvv 3 1 (by decide)
    · exact hBvv 3 2 (by decide)
    · exact (hij rfl).elim
  have hspan_w : Submodule.span (ZMod 3) (Set.range w) = ⊤ :=
    ggWAutH_span_of_orthogonal hdim horth hnorm
  let φ0 : Dual (ZMod 3) V := -B c0
  have hφ0 : φ0 c0 = 2 := by
    dsimp only [φ0]
    rw [LinearMap.neg_apply, hBc0c0]
    decide
  let sp : V ≃ₗ[ZMod 3] V := Module.reflection hφ0
  have hsp : ∀ u, sp u = u + B c0 u • c0 := by
    intro u
    rw [show sp = Module.reflection hφ0 from rfl, reflection_apply u hφ0]
    dsimp only [φ0]
    rw [LinearMap.neg_apply, neg_smul, sub_neg_eq_add]
  let negsp : V ≃ₗ[ZMod 3] V := LinearEquiv.neg (ZMod 3) * sp
  have hnegsp : ∀ u, negsp u = -(sp u) := by
    intro u
    rw [show negsp = LinearEquiv.neg (ZMod 3) * sp from rfl, LinearEquiv.mul_apply,
      LinearEquiv.neg_apply]
  have hp_form : ∀ u, p u = -(u + B c0 u • c0) := by
    have hfun : (p : V →ₗ[ZMod 3] V) = (negsp : V →ₗ[ZMod 3] V) := by
      refine LinearMap.ext_on_range hspan_w ?_
      intro i
      fin_cases i
      · change p (w 0) = negsp (w 0)
        rw [show w 0 = c0 from rfl, hp_c0, hnegsp c0, hsp c0, hBc0c0, one_smul]
        have hc : -(c0 + c0) = c0 := by
          rw [← two_smul (ZMod 3) c0]
          rw [show (2 : ZMod 3) = -1 from by decide, neg_smul, one_smul, neg_neg]
        rw [hc]
      · change p (w 1) = negsp (w 1)
        rw [show w 1 = v 0 from rfl, hp_v 0, hnegsp (v 0), hsp (v 0), hBc0v 0, zero_smul, add_zero]
      · change p (w 2) = negsp (w 2)
        rw [show w 2 = v 1 from rfl, hp_v 1, hnegsp (v 1), hsp (v 1), hBc0v 1, zero_smul, add_zero]
      · change p (w 3) = negsp (w 3)
        rw [show w 3 = v 2 from rfl, hp_v 2, hnegsp (v 2), hsp (v 2), hBc0v 2, zero_smul, add_zero]
      · change p (w 4) = negsp (w 4)
        rw [show w 4 = v 3 from rfl, hp_v 3, hnegsp (v 3), hsp (v 3), hBc0v 3, zero_smul, add_zero]
    intro u
    have h := LinearMap.congr_fun hfun u
    change p u = negsp u at h
    rw [hnegsp u, hsp u] at h
    exact h
  have hc0ne : c0 ≠ 0 := by
    intro h0
    have h1 : B c0 c0 = 0 := by rw [h0, map_zero]
    rw [hBc0c0] at h1
    exact absurd h1 (by decide)
  obtain ⟨g0, hg0W, hg0c⟩ :=
    E6QTwo.exists_mem_e6Weyl_apply_eq hP hV hB hα hc0ne hc (by rw [hBc0c0, hcc])
  refine ⟨g0 * p * g0.symm, mul_mem (mul_mem hg0W hpW) (inv_mem hg0W), fun u => ?_⟩
  have hg0iso : ∀ x y, B (g0 x) (g0 y) = B x y :=
    E6QTwo.bilinForm_apply_e6Weyl hP hV hB hα hg0W
  have hBc0 : B c0 (g0.symm u) = B c u := by
    have h := hg0iso c0 (g0.symm u)
    rw [hg0c] at h
    simpa using h.symm
  calc (g0 * p * g0.symm) u
      = g0 (p (g0.symm u)) := by rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply]
    _ = g0 (-(g0.symm u) - B c0 (g0.symm u) • c0) := by
          rw [hp_form (g0.symm u)]
          congr 1
          abel
    _ = -(g0 (g0.symm u)) - B c0 (g0.symm u) • g0 c0 := by rw [map_sub, map_neg, map_smul]
    _ = -u - B c0 (g0.symm u) • c := by
          rw [LinearEquiv.apply_symm_apply, hg0c]
    _ = -u - B c u • c := by rw [hBc0]
    _ = -(u + B c u • c) := by abel

private theorem ggWAutH_refl_mem_pmW {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    [FiniteDimensional (ZMod 3) V] [Finite V]
    {h : Fin 6 → V} {α : Fin 6 → Dual (ZMod 3) V} {B : LinearMap.BilinForm (ZMod 3) V}
    (hP : ∀ i j, α i (h j) = (CartanMatrix.E 6 i j : ZMod 3))
    (hV : Nat.card V = 3 ^ 5) (hB : ∀ i v, B (h i) v = α i v) (hα : ∀ i, α i (h i) = 2)
    (hdim : Module.finrank (ZMod 3) V = 5)
    (W : Subgroup (V ≃ₗ[ZMod 3] V)) (hWeq : W = E6QTwo.e6Weyl (h := h) (α := α) hα)
    {R : Subgroup (V ≃ₗ[ZMod 3] V)}
    (hpresB : ∀ g ∈ R, ∀ u v, B (g u) (g v) = B u v)
    {t : V ≃ₗ[ZMod 3] V} (ht : t ∈ R) (htRefl : IsReflLin t) :
    ∃ g ∈ W, (∀ v, t v = g v) ∨ (∀ v, t v = -(g v)) := by
  obtain ⟨c, φ, hφ, rfl⟩ := htRefl
  have hc : c ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hφ
    exact absurd hφ (by decide)
  have hsym : ∀ u w : V, B u w = B w u := E6QTwo.bilinForm_symm hP hV hB
  have hxx : ∀ x : ZMod 3, x + x = 2 * x := by decide
  have h2x : ∀ x : ZMod 3, (2 : ZMod 3) * x = -x := by decide
  have hkey : ∀ u : V, φ u * B c c = 2 * B c u := by
    intro u
    have h := hpresB (Module.reflection hφ) ht u c
    rw [reflection_apply u hφ, reflection_apply c hφ, hφ] at h
    have hv2 : c - (2 : ZMod 3) • c = -c := by module
    rw [hv2] at h
    have hexp : B (u - φ u • c) (-c) = -(B u c - φ u * B c c) := by
      simp only [LinearMap.BilinForm.neg_right, LinearMap.BilinForm.sub_left,
        LinearMap.BilinForm.smul_left]
    have h2 : -(B u c - φ u * B c c) = B u c := hexp.symm.trans h
    have h2' : φ u * B c c - B u c = B u c :=
      (neg_sub (B u c) (φ u * B c c)).symm.trans h2
    have h3 : φ u * B c c = B u c + B u c := sub_eq_iff_eq_add.mp h2'
    rw [show B c u = B u c from (hsym u c).symm, h3, hxx]
  rcases (by decide : ∀ x : ZMod 3, x = 0 ∨ x = 1 ∨ x = 2) (B c c) with h0 | h1 | h2
  · have hc0 : c = 0 := E6QTwo.bilinForm_nondegenerate hP hV hB (fun u => by
      have h := hkey u
      rw [h0, mul_zero] at h
      have h2 : (2 : ZMod 3) * B c u = 0 := h.symm
      exact (mul_eq_zero.mp h2).resolve_left (by decide))
    exact absurd hc0 hc
  · have hfe : ∀ u, φ u = -(B c u) := by
      intro u
      have h := hkey u
      rw [h1, mul_one] at h
      rw [h, h2x]
    have ht' : ∀ u, Module.reflection hφ u = u + B c u • c := by
      intro u
      rw [reflection_apply u hφ, hfe u,
        show (-(B c u)) • c = -(B c u • c) from neg_smul (B c u) c, sub_neg_eq_add]
    obtain ⟨g, hgW, hg⟩ := ggWAutH_neg_sRefl_mem hP hV hB hα hdim hc h1
    refine ⟨g, by rw [hWeq]; exact hgW, Or.inr ?_⟩
    intro u
    rw [ht' u, hg u, neg_neg]
  · have hfe : ∀ u, φ u = B c u := by
      intro u
      have h := hkey u
      rw [h2] at h
      have hcomm : (2 : ZMod 3) * B c u = B c u * 2 := mul_comm _ _
      rw [hcomm] at h
      exact mul_right_cancel₀ (by decide : (2 : ZMod 3) ≠ 0) h
    have ht' : ∀ u, Module.reflection hφ u = u - B c u • c := by
      intro u
      rw [reflection_apply u hφ, hfe u]
    obtain ⟨g, hgW, hg⟩ := E6QTwo.exists_mem_e6Weyl_reflection hP hV hB hα h2
    refine ⟨g, by rw [hWeq]; exact hgW, Or.inl ?_⟩
    intro u
    rw [ht' u, hg u]

private lemma ggWAutH_neg_comm {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (g : V ≃ₗ[ZMod 3] V) :
    LinearEquiv.neg (ZMod 3) * g = g * LinearEquiv.neg (ZMod 3) := by
  ext v
  simp only [LinearEquiv.mul_apply, LinearEquiv.neg_apply, map_neg]

private lemma ggWAutH_neg_inv {V : Type} [AddCommGroup V] [Module (ZMod 3) V] :
    (LinearEquiv.neg (ZMod 3) : V ≃ₗ[ZMod 3] V)⁻¹ = LinearEquiv.neg (ZMod 3) := by
  rw [inv_eq_iff_mul_eq_one]
  ext v
  simp

private lemma ggWAutH_neg_mul_self {V : Type} [AddCommGroup V] [Module (ZMod 3) V] :
    (LinearEquiv.neg (ZMod 3) : V ≃ₗ[ZMod 3] V) * LinearEquiv.neg (ZMod 3) = 1 := by
  ext v
  simp

private def ggWAutH_pm {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (W : Subgroup (V ≃ₗ[ZMod 3] V)) : Subgroup (V ≃ₗ[ZMod 3] V) where
  carrier := {x | ∃ g ∈ W, x = g ∨ x = LinearEquiv.neg (ZMod 3) * g}
  one_mem' := ⟨1, W.one_mem, Or.inl rfl⟩
  mul_mem' := by
    rintro x y ⟨g, hg, hxg | hxg⟩ ⟨k, hk, hyk | hyk⟩
    · exact ⟨g * k, W.mul_mem hg hk, Or.inl (by rw [hxg, hyk])⟩
    · refine ⟨g * k, W.mul_mem hg hk, Or.inr ?_⟩
      rw [hxg, hyk]
      calc g * (LinearEquiv.neg (ZMod 3) * k)
          = (g * LinearEquiv.neg (ZMod 3)) * k := by rw [mul_assoc]
        _ = (LinearEquiv.neg (ZMod 3) * g) * k := by rw [ggWAutH_neg_comm g]
        _ = LinearEquiv.neg (ZMod 3) * (g * k) := by rw [mul_assoc]
    · refine ⟨g * k, W.mul_mem hg hk, Or.inr ?_⟩
      rw [hxg, hyk, mul_assoc]
    · refine ⟨g * k, W.mul_mem hg hk, Or.inl ?_⟩
      rw [hxg, hyk]
      calc (LinearEquiv.neg (ZMod 3) * g) * (LinearEquiv.neg (ZMod 3) * k)
          = LinearEquiv.neg (ZMod 3) * (g * (LinearEquiv.neg (ZMod 3) * k)) := by
              rw [mul_assoc]
        _ = LinearEquiv.neg (ZMod 3) * ((g * LinearEquiv.neg (ZMod 3)) * k) := by
              rw [mul_assoc]
        _ = LinearEquiv.neg (ZMod 3) * ((LinearEquiv.neg (ZMod 3) * g) * k) := by
              rw [ggWAutH_neg_comm g]
        _ = LinearEquiv.neg (ZMod 3) * (LinearEquiv.neg (ZMod 3) * (g * k)) := by
              rw [mul_assoc]
        _ = (LinearEquiv.neg (ZMod 3) * LinearEquiv.neg (ZMod 3)) * (g * k) := by
              rw [mul_assoc]
        _ = g * k := by rw [ggWAutH_neg_mul_self, one_mul]
  inv_mem' := by
    rintro x ⟨g, hg, hxg | hxg⟩
    · exact ⟨g⁻¹, W.inv_mem hg, Or.inl (by rw [hxg])⟩
    · refine ⟨g⁻¹, W.inv_mem hg, Or.inr ?_⟩
      rw [hxg, mul_inv_rev, ggWAutH_neg_inv, ← ggWAutH_neg_comm g⁻¹]

private lemma ggWAutH_repr_monomial {n : ℕ} {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (b : Module.Basis (Fin n) (ZMod 3) V) {a : V ≃ₗ[ZMod 3] V}
    (σ : Equiv.Perm (Fin n)) (c : Fin n → ZMod 3)
    (ha : ∀ i, a (b i) = c i • b (σ i)) (x : V) (i : Fin n) :
    b.repr (a x) (σ i) = c i * b.repr x i := by
  have hx : a x = ∑ j, (b.repr x j * c j) • b (σ j) := by
    conv_lhs => rw [← b.sum_repr x]
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, ha j, smul_smul]
  rw [hx, map_sum, Finsupp.coe_finset_sum]
  simp only [Finset.sum_apply, map_smul, Finsupp.coe_smul, Pi.smul_apply, Basis.repr_self]
  rw [Finset.sum_eq_single i]
  · simp [Finsupp.single_eq_same, mul_comm]
  · intro j _ hj
    have hne : σ i ≠ σ j := fun h => hj (σ.injective h.symm)
    rw [Finsupp.single_eq_of_ne hne, smul_zero]
  · intro hi; exact absurd (Finset.mem_univ i) hi

private lemma ggWAutH_card_supp_monomial {n : ℕ} {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (b : Module.Basis (Fin n) (ZMod 3) V) {a : V ≃ₗ[ZMod 3] V}
    (σ : Equiv.Perm (Fin n)) (c : Fin n → ZMod 3) (hc : ∀ i, c i ≠ 0)
    (ha : ∀ i, a (b i) = c i • b (σ i)) (x : V) :
    (Finset.univ.filter (fun i => b.repr (a x) i ≠ 0)).card =
      (Finset.univ.filter (fun i => b.repr x i ≠ 0)).card := by
  have hkey : ∀ i, b.repr (a x) (σ i) = c i * b.repr x i :=
    fun i => ggWAutH_repr_monomial b σ c ha x i
  have hsupp : (Finset.univ.filter (fun i => b.repr (a x) i ≠ 0)) =
      (Finset.univ.filter (fun i => b.repr x i ≠ 0)).map σ.toEmbedding := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map,
      Equiv.toEmbedding_apply]
    constructor
    · intro hj
      refine ⟨σ.symm j, ?_, σ.apply_symm_apply j⟩
      have h := hkey (σ.symm j)
      rw [σ.apply_symm_apply] at h
      rw [h] at hj
      exact fun hx => hj (by rw [hx, mul_zero])
    · rintro ⟨i, hi, rfl⟩
      rw [hkey i]
      exact mul_ne_zero (hc i) hi
  rw [hsupp, Finset.card_map]

private theorem ggWAutH_not_imprimitive {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    [Module.Finite (ZMod 3) V] [Finite V]
    {h : Fin 6 → V} {α : Fin 6 → Dual (ZMod 3) V} {B : LinearMap.BilinForm (ZMod 3) V}
    (hP : ∀ i j, α i (h j) = (CartanMatrix.E 6 i j : ZMod 3))
    (hV : Nat.card V = 3 ^ 5) (hB : ∀ i v, B (h i) v = α i v) (hα : ∀ i, α i (h i) = 2)
    (W : Subgroup (V ≃ₗ[ZMod 3] V)) (hWeq : W = E6QTwo.e6Weyl (h := h) (α := α) hα)
    (R : Subgroup (V ≃ₗ[ZMod 3] V)) (hWR : W ≤ R) (habsR : ZS.AbsIrred 3 R)
    (hgenR : R = Subgroup.closure {r | r ∈ R ∧ GGLinRefl r})
    (hdim : Module.finrank (ZMod 3) V = 5) :
    ¬ CFSG.Quasithin.SimsG4.IsImprimitiveOnV R := by
  classical
  intro himp
  obtain ⟨b, hb⟩ := ggRC_monomial_of_imprimitive (p := 3) hdim R habsR hgenR himp
  have hweight : ∀ (a : V ≃ₗ[ZMod 3] V), a ∈ R → ∀ x : V,
      (Finset.univ.filter (fun i => b.repr (a x) i ≠ 0)).card =
        (Finset.univ.filter (fun i => b.repr x i ≠ 0)).card := by
    intro a ha x
    obtain ⟨σ, c, hc, hac⟩ := hb a ha
    exact ggWAutH_card_supp_monomial b σ c hc hac x
  let vk : Fin 5 → V := fun k =>
    (Finset.univ.filter (fun i : Fin 5 => i.val ≤ k.val)).sum (fun i => b i)
  have hrepr_vk : ∀ k : Fin 5, ∀ j : Fin 5,
      b.repr (vk k) j = if j.val ≤ k.val then 1 else 0 := by
    intro k j
    have h1 : b.repr (vk k) = (Finset.univ.filter (fun i : Fin 5 => i.val ≤ k.val)).sum
        (fun i => Finsupp.single i (1 : ZMod 3)) := by
      dsimp only [vk]
      rw [map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Basis.repr_self]
    rw [h1, Finsupp.coe_finset_sum]
    simp only [Finset.sum_apply, Finsupp.single_apply]
    rw [Finset.sum_ite_eq']
    simp
  have hcard_vk : ∀ k : Fin 5,
      (Finset.univ.filter (fun i => b.repr (vk k) i ≠ 0)).card = k.val + 1 := by
    intro k
    have hsupp : (Finset.univ.filter (fun i => b.repr (vk k) i ≠ 0)) =
        Finset.univ.filter (fun i : Fin 5 => i.val ≤ k.val) := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, hrepr_vk k j]
      by_cases h : j.val ≤ k.val <;> simp [h]
    rw [hsupp, ← Fintype.card_subtype (fun i : Fin 5 => i.val ≤ k.val)]
    refine (Fintype.card_congr ?_).trans
      (Fintype.card_fin_lt_of_le (n := 5) (m := k.val + 1) (by omega))
    exact
      { toFun := fun i => ⟨⟨i.val, by omega⟩, show i.val < k.val + 1 from by omega⟩
        invFun := fun i => ⟨⟨i.val, by omega⟩, show i.val ≤ k.val from by omega⟩
        left_inv := fun i => by ext; rfl
        right_inv := fun i => by ext; rfl }
  have hvk_ne : ∀ k : Fin 5, vk k ≠ 0 := by
    intro k h0
    have h := hcard_vk k
    rw [h0, map_zero] at h
    simp at h
  have hcard_lt : Fintype.card (ZMod 3) < Fintype.card (Fin 5) := by simp
  obtain ⟨k, l, hkl, hnormeq⟩ :=
    Fintype.exists_ne_map_eq_of_card_lt (fun k : Fin 5 => B (vk k) (vk k)) hcard_lt
  obtain ⟨g, hgW, hgkl⟩ :=
    E6QTwo.exists_mem_e6Weyl_apply_eq hP hV hB hα (hvk_ne k) (hvk_ne l) hnormeq
  have hgR : g ∈ R := hWR (by rw [hWeq]; exact hgW)
  have hw := hweight g hgR (vk k)
  rw [hgkl] at hw
  rw [hcard_vk l, hcard_vk k] at hw
  exact hkl (Fin.ext (by omega))

theorem ggWAut_heartE6 (hE : GGWAutEngine) (hK : GGReflClassOmegaInput)
    (D : GGQ2Lin 3) [FiniteDimensional (ZMod 3) D.V] (e : Fin 6 ≃ D.ι)
    (hE6 : D.coxeter = CoxeterMatrix.E₆.reindex e) (hdim : Module.finrank (ZMod 3) D.V = 5)
    (A : Subgroup (D.V ≃ₗ[ZMod 3] D.V)) (hW : D.weyl ≤ A) (hTF : TransvectionFree A) :
    ∀ a ∈ A, ∃ g ∈ D.weyl, (∀ v, a v = g v) ∨ (∀ v, a v = -(g v)) := by
  classical
  have : Finite D.V := Module.finite_of_finite (ZMod 3)
  let h : Fin 6 → D.V := fun i => D.coroot (e i)
  let α : Fin 6 → Dual (ZMod 3) D.V := fun i => D.root (e i)
  have hP : ∀ i j, α i (h j) = (CartanMatrix.E 6 i j : ZMod 3) :=
    fun i j => ggWAutH_hP D e hE6 i j
  have hα : ∀ i, α i (h i) = 2 := fun i => D.root_coroot_self (e i)
  have hV : Nat.card D.V = 3 ^ 5 := by
    have hcard := Module.natCard_eq_pow_finrank (K := ZMod 3) (V := D.V)
    rw [Nat.card_zmod, hdim] at hcard
    exact hcard
  let W : Subgroup (D.V ≃ₗ[ZMod 3] D.V) := E6QTwo.e6Weyl (h := h) (α := α) hα
  have hWeq : W = E6QTwo.e6Weyl (h := h) (α := α) hα := rfl
  have hweyl : D.weyl = W := ggWAutH_weyl_eq D e hα
  have habsW : ZS.AbsIrred 3 W :=
    ggWAutH_absIrred h α hα (E6QTwo.span_eq_top_of_card hP hV)
      (fun w hw => E6QTwo.eq_zero_of_forall_apply_eq_zero hP hV (v := w) hw)
      (ggWAutH_conn h α hP)
  have habsW' : ZS.AbsIrred 3 D.weyl := by rw [hweyl]; exact habsW
  let R : Subgroup (D.V ≃ₗ[ZMod 3] D.V) := reflGp A
  have hWR : W ≤ R := by
    rw [hWeq, E6QTwo.e6Weyl]
    refine (Subgroup.closure_le R).mpr ?_
    rintro g ⟨i, rfl⟩
    change D.simpleRefl (e i) ∈ R
    exact Subgroup.subset_closure ⟨hW (ggQ2xQ_simpleRefl_mem_weyl D (e i)),
      ggQ2xQ_simpleRefl_isReflLin D (e i)⟩
  have hWR' : D.weyl ≤ R := by rw [hweyl]; exact hWR
  have hRA : R ≤ A := ggWAut_reflGp_le A
  have habsR : ZS.AbsIrred 3 R := ggWAut_absIrred_of_le hWR' habsW'
  have hgenR : R = Subgroup.closure {r | r ∈ R ∧ GGLinRefl r} := ggWAut_reflGp_closure A
  obtain ⟨B, hB⟩ := E6QTwo.exists_bilinForm hP hV
  have hpmA : ∀ a ∈ A, ∃ r ∈ R, (∀ v, a v = r v) ∨ (∀ v, a v = -(r v)) := by
    rcases hE D.V 5 hdim (by norm_num) A hTF habsR with ⟨hEven, -⟩ | hpm
    · exact absurd hEven (by norm_num)
    · exact hpm
  have hnotImp : ¬ CFSG.Quasithin.SimsG4.IsImprimitiveOnV R :=
    ggWAutH_not_imprimitive hP hV hB hα W hWeq R hWR habsR hgenR hdim
  have hnotSL : ¬ (∀ g : D.V ≃ₗ[ZMod 3] D.V, LinearEquiv.det g = 1 → g ∈ R) := by
    intro hsl
    have hslA : ∀ g : D.V ≃ₗ[ZMod 3] D.V, LinearEquiv.det g = 1 → g ∈ A :=
      fun g hg => hRA (hsl g hg)
    have h2 : 2 ≤ Module.finrank (ZMod 3) D.V := by rw [hdim]; norm_num
    exact ggWAut_SL_has_transvection h2 A hslA hTF
  have hOorth : GGOrthType R := by
    rcases hK.2 D.V 5 hdim (by norm_num) (by norm_num) R habsR hgenR with
      himp | hsl | hO | h4 | h5 | h6 | h7
    · exact absurd himp hnotImp
    · exact absurd hsl.1 hnotSL
    · exact hO.1
    · exact absurd h4.1 (by norm_num)
    · exact absurd h5.1 (by norm_num)
    · exact absurd h6.1 (by norm_num)
    · exact absurd h7.1 (by norm_num)
  obtain ⟨Q', hQ'nd, hQ'R, -⟩ := hOorth
  let QB : QuadraticForm (ZMod 3) D.V := LinearMap.BilinMap.toQuadraticMap B
  have hQBapply : ∀ v, QB v = B v v := fun v => LinearMap.BilinMap.toQuadraticMap_apply B v
  have hpolar : ∀ x y : D.V, QuadraticMap.polar (⇑QB) x y = 2 * B x y := by
    intro x y
    rw [QuadraticMap.polar, hQBapply (x + y), hQBapply x, hQBapply y]
    simp only [LinearMap.BilinForm.add_left, LinearMap.BilinForm.add_right]
    rw [E6QTwo.bilinForm_symm hP hV hB y x]
    ring
  have hQBnd : (QuadraticMap.polarBilin QB).Nondegenerate := by
    refine (LinearMap.BilinForm.nondegenerate_iff_ker_eq_bot
      (B := QuadraticMap.polarBilin QB)).mpr ?_
    rw [Submodule.eq_bot_iff]
    intro x hx
    rw [LinearMap.mem_ker] at hx
    apply E6QTwo.bilinForm_nondegenerate hP hV hB
    intro y
    have h := congrArg (fun f : D.V →ₗ[ZMod 3] (ZMod 3) => f y) hx
    rw [QuadraticMap.polarBilin_apply_apply, hpolar x y] at h
    exact (mul_eq_zero.mp h).resolve_left (by decide)
  have hQBW : ∀ g ∈ W, ZS.IsIsom 3 QB g := by
    intro g hg v
    rw [hQBapply, hQBapply]
    exact E6QTwo.bilinForm_apply_e6Weyl hP hV hB hα hg v v
  have hQ'W : ∀ g ∈ W, ZS.IsIsom 3 Q' g := fun g hg => hQ'R g (hWR hg)
  obtain ⟨cst, -, hcst⟩ := ggWAut_form_unique W habsW Q' QB hQ'nd hQBnd hQ'W hQBW
  have hpresQB : ∀ g ∈ R, ∀ v, QB (g v) = QB v := by
    intro g hg v
    have h1 : Q' (g v) = Q' v := hQ'R g hg v
    have h2 : QB (g v) = cst * Q' (g v) := hcst (g v)
    have h3 : QB v = cst * Q' v := hcst v
    rw [h2, h3, h1]
  have hpresB : ∀ g ∈ R, ∀ u v, B (g u) (g v) = B u v := by
    intro g hg u v
    have hpu := hpresQB g hg (u + v)
    have hgu := hpresQB g hg u
    have hgv := hpresQB g hg v
    have hp : QuadraticMap.polar (⇑QB) (g u) (g v) = QuadraticMap.polar (⇑QB) u v := by
      rw [QuadraticMap.polar, QuadraticMap.polar]
      rw [← map_add g u v]
      rw [hpu, hgu, hgv]
    rw [hpolar (g u) (g v), hpolar u v] at hp
    exact mul_left_cancel₀ (by decide : (2 : ZMod 3) ≠ 0) hp
  have hRle : R ≤ ggWAutH_pm W := by
    rw [hgenR]
    refine (Subgroup.closure_le (ggWAutH_pm W)).mpr ?_
    rintro r ⟨hrR, hrRefl⟩
    obtain ⟨g, hgW, hpg | hpg⟩ :=
      ggWAutH_refl_mem_pmW hP hV hB hα hdim W hWeq hpresB hrR
        ((ggLinRefl_iff_isReflLin r).mp hrRefl)
    · exact ⟨g, hgW, Or.inl (LinearEquiv.ext hpg)⟩
    · refine ⟨g, hgW, Or.inr ?_⟩
      apply LinearEquiv.ext
      intro v
      rw [hpg v, LinearEquiv.mul_apply, LinearEquiv.neg_apply]
  intro a ha
  obtain ⟨r, hrR, har | har⟩ := hpmA a ha
  · obtain ⟨g, hgW, hrg | hrg⟩ := hRle hrR
    · exact ⟨g, by rw [hweyl]; exact hgW, Or.inl (fun v => by rw [har v, hrg])⟩
    · exact ⟨g, by rw [hweyl]; exact hgW, Or.inr (fun v => by
        rw [har v, hrg, LinearEquiv.mul_apply, LinearEquiv.neg_apply])⟩
  · obtain ⟨g, hgW, hrg | hrg⟩ := hRle hrR
    · exact ⟨g, by rw [hweyl]; exact hgW, Or.inr (fun v => by rw [har v, hrg])⟩
    · exact ⟨g, by rw [hweyl]; exact hgW, Or.inl (fun v => by
        rw [har v, hrg, LinearEquiv.mul_apply, LinearEquiv.neg_apply, neg_neg])⟩

end CFSG.StandardType

end
