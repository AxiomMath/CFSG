module

public import CFSG.LocalAnalysis.StandardType.ZS.ImpExtRankThree
import CFSG.LocalAnalysis.StandardType.ZS.Basic
import CFSG.LocalAnalysis.StandardType.ZS.RootMatrix
import CFSG.LocalAnalysis.StandardType.ZS.ReflFrame

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

public section

namespace CFSG.StandardType.ZS

variable {p : ℕ} [Fact p.Prime] {U : Type} [AddCommGroup U] [Module (ZMod p) U]

structure FourRefl (a b c d : U ≃ₗ[ZMod p] U) (A : Subgroup (U ≃ₗ[ZMod p] U)) : Prop where
  finrank_eq : Module.finrank (ZMod p) U = 4
  isRefl_a : IsRefl p a
  isRefl_b : IsRefl p b
  isRefl_c : IsRefl p c
  isRefl_d : IsRefl p d
  eq_closure : A = Subgroup.closure {a, b, c, d}
  transvectionFree : QTwoLin.TransvectionFree A
  dmax : DMax p A 4
  finrank_commutatorSpace :
    Module.finrank (ZMod p) (HardMathSupport.Kantor79.commutatorSpace A) = 4

private def Kz : Matrix (Fin 4) (Fin 4) ℤ :=
  !![2, -1, 0, 0; -1, 2, -1, -2; 0, -1, 2, 0; 0, -1, 0, 2]

private def Mz (i : Fin 4) : Matrix (Fin 4) (Fin 4) ℤ :=
  1 - Matrix.of (fun r c => if r = i then Kz i c else 0)

private def Mzp (i : Fin 4) : Matrix (Fin 4) (Fin 4) (ZMod p) :=
  1 - Matrix.of (fun r c => if r = i then (Kz i c : ZMod p) else 0)

private def Tz : Matrix (Fin 4) (Fin 4) ℤ :=
  1 + Matrix.of (fun i j => ![1, 2, 1, 1] i * ![0, -2, 4, 0] j)

private def wordZ : Matrix (Fin 4) (Fin 4) ℤ :=
  let a := Mz 0; let b := Mz 1; let c := Mz 2; let d := Mz 3
  let bdb := b * d * b
  let com := bdb * a * bdb * a
  c * (com * d) * c * (d * a * bdb * a * bdb)

private lemma wordZ_eq_Tz : wordZ = Tz := by
  decide +kernel

private lemma Mzp_eq_map (i : Fin 4) :
    Mzp (p := p) i = (Mz i).map (Int.castRingHom (ZMod p)) := by
  ext r c
  simp only [Mzp, Mz, Matrix.sub_apply, Matrix.one_apply, Matrix.map_apply]
  split_ifs <;> simp

private noncomputable def RW {e : Module.Basis (Fin 4) (ZMod p) U}
    {φ : Fin 4 → Module.Dual (ZMod p) U} (hφ : ∀ i, φ i (e i) = 2) (i : Fin 4) :
    U ≃ₗ[ZMod p] U := Module.reflection (hφ i)

private noncomputable def wordW {e : Module.Basis (Fin 4) (ZMod p) U}
    {φ : Fin 4 → Module.Dual (ZMod p) U} (hφ : ∀ i, φ i (e i) = 2) :
    U ≃ₗ[ZMod p] U :=
  let a := RW hφ 0; let b := RW hφ 1; let c := RW hφ 2; let d := RW hφ 3
  let bdb := b * d * b
  let com := bdb * a * bdb * a
  c * (com * d) * c * (d * a * bdb * a * bdb)

private lemma toMatrix_RW {e : Module.Basis (Fin 4) (ZMod p) U}
    {φ : Fin 4 → Module.Dual (ZMod p) U} (hφ : ∀ i, φ i (e i) = 2)
    (hK : ∀ i j, φ i (e j) = (Kz i j : ZMod p)) (i : Fin 4) :
    LinearMap.toMatrix e e (RW hφ i : U →ₗ[ZMod p] U) = Mzp (p := p) i := by
  ext r c
  rw [LinearMap.toMatrix_apply]
  change e.coord r ((Module.reflection (hφ i)) (e c)) = Mzp (p := p) i r c
  rw [Module.reflection_apply, map_sub, map_smul]
  rw [show e.coord r (e c) = (if r = c then (1 : ZMod p) else 0) by
    rw [Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]
    by_cases h : r = c
    · simp [h]
    · simp [h, show ¬ c = r from fun hc => h hc.symm]]
  rw [show e.coord r (e i) = (if r = i then (1 : ZMod p) else 0) by
    rw [Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]
    by_cases h : r = i
    · simp [h]
    · simp [h, show ¬ i = r from fun hi => h hi.symm]]
  rw [hK i c, smul_eq_mul]
  rw [show Mzp (p := p) i r c =
      (if r = c then (1 : ZMod p) else 0) -
        (if r = i then (Kz i c : ZMod p) else 0) by simp [Mzp, Matrix.one_apply]]
  by_cases hrc : r = c
  · simp only [if_pos hrc]
    by_cases hri : r = i
    · simp only [if_pos hri, mul_one]
    · simp only [if_neg hri, mul_zero]
  · simp only [if_neg hrc]
    by_cases hri : r = i
    · simp only [if_pos hri, mul_one]
    · simp only [if_neg hri, mul_zero]

private lemma toMatrix_wordW {e : Module.Basis (Fin 4) (ZMod p) U}
    {φ : Fin 4 → Module.Dual (ZMod p) U} (hφ : ∀ i, φ i (e i) = 2)
    (hK : ∀ i j, φ i (e j) = (Kz i j : ZMod p)) :
    LinearMap.toMatrix e e (wordW hφ : U →ₗ[ZMod p] U) =
      (wordZ.map (Int.castRingHom (ZMod p))) := by
  have hword : (wordW hφ : U →ₗ[ZMod p] U) =
      let a := (RW hφ 0 : U →ₗ[ZMod p] U); let b := (RW hφ 1 : U →ₗ[ZMod p] U)
      let c := (RW hφ 2 : U →ₗ[ZMod p] U); let d := (RW hφ 3 : U →ₗ[ZMod p] U)
      let bdb := b * d * b
      let com := bdb * a * bdb * a
      c * (com * d) * c * (d * a * bdb * a * bdb) := rfl
  rw [hword, wordZ]
  simp only [LinearMap.toMatrix_mul, toMatrix_RW hφ hK, Mzp_eq_map, Matrix.map_mul]

private noncomputable def uVec (e : Module.Basis (Fin 4) (ZMod p) U) : U :=
  e 0 + 2 • e 1 + e 2 + e 3

private noncomputable def psiVec (e : Module.Basis (Fin 4) (ZMod p) U) :
    Module.Dual (ZMod p) U :=
  -2 • e.coord 1 + 4 • e.coord 2

private lemma psiVec_uVec {e : Module.Basis (Fin 4) (ZMod p) U} :
    psiVec e (uVec e) = 0 := by
  simp only [psiVec, uVec, map_add]
  simp [Module.Basis.repr_self]
  ring_nf

private lemma uVec_ne_zero {e : Module.Basis (Fin 4) (ZMod p) U} : uVec e ≠ 0 := by
  intro h
  have h1 := congrArg (fun x => e.repr x 0) h
  simp only [uVec, map_add, Module.Basis.repr_self, Finsupp.add_apply, Finsupp.single_eq_same] at h1
  norm_num at h1

private lemma psiVec_ne_zero (hp : p ≠ 2) {e : Module.Basis (Fin 4) (ZMod p) U} :
    psiVec e ≠ 0 := by
  intro h
  have h1 : psiVec e (e 1) = 0 := by rw [h]; rfl
  have h2 : (2 : ZMod p) = 0 := by
    simpa [psiVec, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply] using h1
  have hdvd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp h2
  have hle : p ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
  have hge : 2 ≤ p := (Fact.out : p.Prime).two_le
  omega

private lemma repr_uVec {e : Module.Basis (Fin 4) (ZMod p) U} (i : Fin 4) :
    e.repr (uVec e) i = ((![1, 2, 1, 1] i : ℤ) : ZMod p) := by
  simp only [uVec, map_add, Module.Basis.repr_self, Finsupp.add_apply]
  fin_cases i <;> simp

private lemma psiVec_e {e : Module.Basis (Fin 4) (ZMod p) U} (j : Fin 4) :
    psiVec e (e j) = ((![0, -2, 4, 0] j : ℤ) : ZMod p) := by
  simp only [psiVec, LinearMap.add_apply, LinearMap.smul_apply,
    Module.Basis.coord_apply, Module.Basis.repr_self]
  fin_cases j <;> simp

private lemma Tz_map_eq {e : Module.Basis (Fin 4) (ZMod p) U} :
    (Tz.map (Int.castRingHom (ZMod p))) =
      1 + LinearMap.toMatrix e e ((psiVec e).smulRight (uVec e)) := by
  rw [LinearMap.toMatrix_smulRight]
  ext i j
  rw [Matrix.map_apply, Tz, Matrix.add_apply, Matrix.one_apply, Matrix.of_apply,
    Matrix.add_apply, Matrix.one_apply, Matrix.vecMulVec_apply, Function.comp_apply,
    map_add, map_mul]
  rw [repr_uVec i, psiVec_e j]
  by_cases hij : i = j <;> simp [hij]

private lemma wordW_eq {e : Module.Basis (Fin 4) (ZMod p) U}
    {φ : Fin 4 → Module.Dual (ZMod p) U} (hφ : ∀ i, φ i (e i) = 2)
    (hK : ∀ i j, φ i (e j) = (Kz i j : ZMod p)) :
    (wordW hφ : U →ₗ[ZMod p] U) = 1 + (psiVec e).smulRight (uVec e) := by
  rw [← Matrix.toLin_toMatrix (v₁ := e) (v₂ := e) (wordW hφ : U →ₗ[ZMod p] U),
    toMatrix_wordW (e := e) hφ hK, wordZ_eq_Tz, Tz_map_eq (e := e)]
  rw [map_add, Matrix.toLin_one, Matrix.toLin_toMatrix]
  rfl

private theorem isTransvection_wordW (hp : p ≠ 2) {e : Module.Basis (Fin 4) (ZMod p) U}
    {φ : Fin 4 → Module.Dual (ZMod p) U} (hφ : ∀ i, φ i (e i) = 2)
    (hK : ∀ i j, φ i (e j) = (Kz i j : ZMod p)) :
    QTwoLin.IsTransvectionLin (wordW hφ) := by
  have heq := wordW_eq hφ hK
  refine ⟨uVec e, psiVec e, uVec_ne_zero, psiVec_ne_zero hp, psiVec_uVec, fun v => ?_⟩
  change (wordW hφ : U →ₗ[ZMod p] U) v = v + psiVec e v • uVec e
  rw [heq, LinearMap.add_apply, LinearMap.smulRight_apply]
  rfl

private lemma movedSpace_reflection_eq_span (hp : p ≠ 2) {v : U}
    {φ : Module.Dual (ZMod p) U} (hφ : φ v = 2) :
    HardMathSupport.Kantor79.movedSpace (Module.reflection hφ) =
      Submodule.span (ZMod p) {v} := by
  have h2 : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp
  unfold HardMathSupport.Kantor79.movedSpace
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    change Module.reflection hφ x - x ∈ Submodule.span (ZMod p) {v}
    have hx : Module.reflection hφ x - x = -(φ x • v) := by
      rw [Module.reflection_apply]; abel
    rw [hx]
    exact Submodule.neg_mem _ (Submodule.smul_mem _ (φ x)
      (Submodule.subset_span (Set.mem_singleton v)))
  · rw [Submodule.span_singleton_le_iff_mem]
    have hmem : -v ∈ LinearMap.range
        ((Module.reflection hφ : U →ₗ[ZMod p] U) - LinearMap.id) := by
      refine ⟨(2 : ZMod p)⁻¹ • v, ?_⟩
      have hφv : φ ((2 : ZMod p)⁻¹ • v) = 1 := by
        rw [map_smul, hφ, smul_eq_mul, inv_mul_cancel₀ h2]
      change Module.reflection hφ ((2 : ZMod p)⁻¹ • v) - (2 : ZMod p)⁻¹ • v = -v
      rw [show Module.reflection hφ ((2 : ZMod p)⁻¹ • v) - (2 : ZMod p)⁻¹ • v =
          -(φ ((2 : ZMod p)⁻¹ • v) • v) by rw [Module.reflection_apply]; abel]
      rw [hφv, one_smul]
    simpa using Submodule.neg_mem _ hmem

private lemma span_range_eq_iSup_span {v : Fin 4 → U} :
    Submodule.span (ZMod p) (Set.range v) =
      ⨆ i, Submodule.span (ZMod p) ({v i} : Set U) := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro x ⟨i, rfl⟩
    exact Submodule.mem_iSup_of_mem i (Submodule.subset_span rfl)
  · refine iSup_le fun i => ?_
    exact Submodule.span_mono (by rintro x rfl; exact ⟨i, rfl⟩)

private lemma wordW_eq_prod {e : Module.Basis (Fin 4) (ZMod p) U}
    {φ : Fin 4 → Module.Dual (ZMod p) U} (hφ : ∀ i, φ i (e i) = 2) :
    wordW hφ = RW hφ 2 * ((RW hφ 1 * RW hφ 3 * RW hφ 1) * RW hφ 0 *
        (RW hφ 1 * RW hφ 3 * RW hφ 1) * RW hφ 0) * RW hφ 3 * RW hφ 2 *
      (RW hφ 3 * RW hφ 0 * (RW hφ 1 * RW hφ 3 * RW hφ 1) * RW hφ 0 *
        (RW hφ 1 * RW hφ 3 * RW hφ 1)) := rfl

private def Mmat : Matrix (Fin 4) (Fin 4) ℕ :=
  !![1, 3, 2, 2; 3, 1, 3, 4; 2, 3, 1, 2; 2, 4, 2, 1]

private structure FourReflRoots (a b c d : U ≃ₗ[ZMod p] U) where
  x : Fin 4 → U ≃ₗ[ZMod p] U
  hx_eq : x = ![a, b, c, d]
  v : Fin 4 → U
  φ : Fin 4 → Module.Dual (ZMod p) U
  hφ : ∀ i, φ i (v i) = 2
  hx : ∀ i, x i = Module.reflection (hφ i)

private noncomputable def fourRefl_roots [Module.Finite (ZMod p) U] (hp : p ≠ 2)
    {a b c d : U ≃ₗ[ZMod p] U} {A : Subgroup (U ≃ₗ[ZMod p] U)}
    (h : FourRefl a b c d A) : FourReflRoots a b c d := by
  let x : Fin 4 → U ≃ₗ[ZMod p] U := ![a, b, c, d]
  have hrefl : ∀ i : Fin 4, ∃ (v : U) (φ : Module.Dual (ZMod p) U) (hφ : φ v = 2),
      x i = Module.reflection hφ := by
    intro i
    fin_cases i
    · exact (isRefl_iff hp a).mp h.isRefl_a
    · exact (isRefl_iff hp b).mp h.isRefl_b
    · exact (isRefl_iff hp c).mp h.isRefl_c
    · exact (isRefl_iff hp d).mp h.isRefl_d
  choose v φ hφ hx using hrefl
  exact ⟨x, rfl, v, φ, hφ, hx⟩

private theorem fourRefl_hordM
    {a b c d : U ≃ₗ[ZMod p] U}
    (had : orderOf (a * d) = 2) (hac : orderOf (a * c) = 2)
    (hcd : orderOf (c * d) = 2) (hab : orderOf (a * b) = 3) (hbc : orderOf (b * c) = 3)
    (hbd : orderOf (b * d) = 4) (R : FourReflRoots a b c d) :
    ∀ i j, orderOf (Module.reflection (R.hφ i) * Module.reflection (R.hφ j)) = Mmat i j := by
  have hselford : ∀ i, orderOf (Module.reflection (R.hφ i) * Module.reflection (R.hφ i)) = 1 :=
    fun i => by
    rw [show Module.reflection (R.hφ i) * Module.reflection (R.hφ i) = 1 from
      mul_inv_cancel _, orderOf_one]
  have hrev : ∀ i j, orderOf (Module.reflection (R.hφ j) * Module.reflection (R.hφ i)) =
      orderOf (Module.reflection (R.hφ i) * Module.reflection (R.hφ j)) := by
    intro i j
    rw [show Module.reflection (R.hφ j) * Module.reflection (R.hφ i) =
        (Module.reflection (R.hφ i) * Module.reflection (R.hφ j))⁻¹ from by
      rw [mul_inv_rev, Module.reflection_inv, Module.reflection_inv]]
    rw [orderOf_inv]
  have ho01 : orderOf (Module.reflection (R.hφ 0) * Module.reflection (R.hφ 1)) = 3 := by
    rw [← R.hx 0, ← R.hx 1]; simpa [R.hx_eq] using hab
  have ho02 : orderOf (Module.reflection (R.hφ 0) * Module.reflection (R.hφ 2)) = 2 := by
    rw [← R.hx 0, ← R.hx 2]; simpa [R.hx_eq] using hac
  have ho03 : orderOf (Module.reflection (R.hφ 0) * Module.reflection (R.hφ 3)) = 2 := by
    rw [← R.hx 0, ← R.hx 3]; simpa [R.hx_eq] using had
  have ho12 : orderOf (Module.reflection (R.hφ 1) * Module.reflection (R.hφ 2)) = 3 := by
    rw [← R.hx 1, ← R.hx 2]; simpa [R.hx_eq] using hbc
  have ho13 : orderOf (Module.reflection (R.hφ 1) * Module.reflection (R.hφ 3)) = 4 := by
    rw [← R.hx 1, ← R.hx 3]; simpa [R.hx_eq] using hbd
  have ho23 : orderOf (Module.reflection (R.hφ 2) * Module.reflection (R.hφ 3)) = 2 := by
    rw [← R.hx 2, ← R.hx 3]; simpa [R.hx_eq] using hcd
  intro i j
  fin_cases i <;> fin_cases j <;> simp only [Mmat, Matrix.of_apply]
  · exact hselford 0
  · exact ho01
  · exact ho02
  · exact ho03
  · exact (hrev 0 1).trans ho01
  · exact hselford 1
  · exact ho12
  · exact ho13
  · exact (hrev 0 2).trans ho02
  · exact (hrev 1 2).trans ho12
  · exact hselford 2
  · exact ho23
  · exact (hrev 0 3).trans ho03
  · exact (hrev 1 3).trans ho13
  · exact (hrev 2 3).trans ho23
  · exact hselford 3

private theorem fourRefl_independence [Module.Finite (ZMod p) U] (hp : p ≠ 2)
    {a b c d : U ≃ₗ[ZMod p] U} {A : Subgroup (U ≃ₗ[ZMod p] U)}
    (h : FourRefl a b c d A) (R : FourReflRoots a b c d) :
    LinearIndependent (ZMod p) R.v ∧
      Module.finrank (ZMod p) (Submodule.span (ZMod p) (Set.range R.v)) = 4 := by
  have hrange : (Set.range R.x : Set (U ≃ₗ[ZMod p] U)) = {a, b, c, d} := by
    rw [R.hx_eq]
    ext y; constructor
    · rintro ⟨i, rfl⟩; fin_cases i <;> simp
    · intro hy
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with rfl | rfl | rfl | rfl
      · exact ⟨0, by simp⟩
      · exact ⟨1, by simp⟩
      · exact ⟨2, by simp⟩
      · exact ⟨3, by simp⟩
  have hcomm : HardMathSupport.Kantor79.commutatorSpace A =
      Submodule.span (ZMod p) (Set.range R.v) := by
    rw [h.eq_closure, ← hrange,
      HardMathSupport.Kantor79.commutatorSpace_closure_eq_iSup_movedSpace R.x,
      span_range_eq_iSup_span]
    exact iSup_congr fun i => by
      rw [R.hx i]; exact movedSpace_reflection_eq_span hp (R.hφ i)
  have hfr : Module.finrank (ZMod p) (Submodule.span (ZMod p) (Set.range R.v)) = 4 := by
    rw [← hcomm, h.finrank_commutatorSpace]
  refine ⟨?_, hfr⟩
  rw [linearIndependent_iff_card_eq_finrank_span]
  change Fintype.card (Fin 4) = Module.finrank (ZMod p)
    (Submodule.span (ZMod p) (Set.range R.v))
  rw [hfr]; rfl

private theorem fourRefl_hP0 (hp : p ≠ 2) {v : Fin 4 → U}
    {φ : Fin 4 → Module.Dual (ZMod p) U} (hφ : ∀ i, φ i (v i) = 2)
    (hordM : ∀ i j, orderOf (Module.reflection (hφ i) * Module.reflection (hφ j)) = Mmat i j) :
    ∀ i j, i ≠ j → Kz i j = 0 → φ i (v j) = 0 := by
  intro i j hij hK
  have hM : Mmat i j = 2 := by
    fin_cases i <;> fin_cases j <;>
      simp only [Kz, Matrix.of_apply] at hK
    all_goals first | exact absurd hK (by decide) | rfl
  exact (apply_eq_zero_of_orderOf_eq_two hp (hφ i) (hφ j) (by rw [hordM i j, hM])).1

private theorem fourRefl_hPP (hp : p ≠ 2) {v : Fin 4 → U}
    {φ : Fin 4 → Module.Dual (ZMod p) U} (hφ : ∀ i, φ i (v i) = 2)
    (hordM : ∀ i j, orderOf (Module.reflection (hφ i) * Module.reflection (hφ j)) = Mmat i j) :
    ∀ i j, i ≠ j → Kz i j ≠ 0 →
      φ i (v j) * φ j (v i) = (Kz i j : ZMod p) * (Kz j i : ZMod p) := by
  intro i j hij hK
  fin_cases i <;> fin_cases j <;>
    simp only [Kz, Matrix.of_apply] at hK
  all_goals
    simp only [Kz, Matrix.of_apply]
    first
    | exact absurd rfl hij
    | exact absurd hK (by decide)
    | simpa [Int.cast_neg, Int.cast_one, Int.cast_ofNat] using
        apply_mul_apply_eq_one_of_orderOf_eq_three hp (hφ 0) (hφ 1) (by rw [hordM 0 1]; rfl)
    | simpa [Int.cast_neg, Int.cast_one, Int.cast_ofNat] using
        apply_mul_apply_eq_one_of_orderOf_eq_three hp (hφ 1) (hφ 0) (by rw [hordM 1 0]; rfl)
    | simpa [Int.cast_neg, Int.cast_one, Int.cast_ofNat] using
        apply_mul_apply_eq_one_of_orderOf_eq_three hp (hφ 1) (hφ 2) (by rw [hordM 1 2]; rfl)
    | simpa [Int.cast_neg, Int.cast_one, Int.cast_ofNat] using
        apply_mul_apply_eq_one_of_orderOf_eq_three hp (hφ 2) (hφ 1) (by rw [hordM 2 1]; rfl)
    | simpa [Int.cast_neg, Int.cast_one, Int.cast_ofNat] using
        apply_mul_apply_eq_two_of_orderOf_eq_four hp (hφ 1) (hφ 3) (by rw [hordM 1 3]; rfl)
    | simpa [Int.cast_neg, Int.cast_one, Int.cast_ofNat] using
        apply_mul_apply_eq_two_of_orderOf_eq_four hp (hφ 3) (hφ 1) (by rw [hordM 3 1]; rfl)

private theorem fourRefl_hAK (hp : p ≠ 2) :
    ∀ i j, i ≠ j → Kz i j ≠ 0 → (Kz i j : ZMod p) ≠ 0 := by
  have h1 : ((-1 : ℤ) : ZMod p) ≠ 0 := by
    rw [Int.cast_neg, Int.cast_one]; exact neg_ne_zero.mpr one_ne_zero
  have h2 : ((-2 : ℤ) : ZMod p) ≠ 0 := by
    rw [Int.cast_neg, Int.cast_ofNat]
    exact neg_ne_zero.mpr (ZMod.prime_ne_zero p 2 hp)
  intro i j hij hK
  fin_cases i <;> fin_cases j
  all_goals
    first
    | exact absurd rfl hij
    | exact absurd hK (by decide)
    | exact h1
    | exact h2

private theorem fourRefl_gauge {v : Fin 4 → U}
    {φ : Fin 4 → Module.Dual (ZMod p) U} (hφ : ∀ i, φ i (v i) = 2)
    (hP0 : ∀ i j, i ≠ j → Kz i j = 0 → φ i (v j) = 0)
    (hPP : ∀ i j, i ≠ j → Kz i j ≠ 0 →
      φ i (v j) * φ j (v i) = (Kz i j : ZMod p) * (Kz j i : ZMod p))
    (hAK : ∀ i j, i ≠ j → Kz i j ≠ 0 → (Kz i j : ZMod p) ≠ 0) :
    ∃ c : Fin 4 → ZMod p, (∀ i, c i ≠ 0) ∧
      ∀ i j, (c i)⁻¹ * c j * φ i (v j) = (Kz i j : ZMod p) := by
  have hpar : ∀ i j, i ≠ j → (Kz i j ≠ 0 ↔
      ((i ≠ (1 : Fin 4) ∧ (fun _ : Fin 4 => (1 : Fin 4)) i = j) ∨
        (j ≠ (1 : Fin 4) ∧ (fun _ : Fin 4 => (1 : Fin 4)) j = i))) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp only [Kz, Matrix.of_apply]
    all_goals first | exact absurd rfl hij | decide
  have hdepth : ∀ i, i ≠ (1 : Fin 4) →
      (fun i : Fin 4 => if i = 1 then 0 else 1) ((fun _ : Fin 4 => (1 : Fin 4)) i) <
      (fun i : Fin 4 => if i = 1 then 0 else 1) i := by
    intro i hi
    fin_cases i <;> simp only []
    all_goals first | exact absurd rfl hi | decide
  obtain ⟨c, hc0, hc⟩ := SecFiveRootRefl.exists_gauge_of_tree (fun i j => Kz i j)
    (fun i j => φ i (v j)) (fun _ : Fin 4 => (1 : Fin 4)) (1 : Fin 4)
    (fun i : Fin 4 => if i = 1 then 0 else 1) hP0 hPP hAK hpar hdepth
  refine ⟨c, hc0, fun i j => ?_⟩
  by_cases hij : i = j
  · subst j
    rw [hφ i, inv_mul_cancel₀ (hc0 i), one_mul]
    fin_cases i <;> simp [Kz]
  · exact hc i j hij

private structure FourReflScaled (a b c d : U ≃ₗ[ZMod p] U)
    (R : FourReflRoots a b c d) where
  c : Fin 4 → ZMod p
  hc0 : ∀ i, c i ≠ 0
  e : Fin 4 → U
  ψ : Fin 4 → Module.Dual (ZMod p) U
  he : ∀ i, e i = c i • R.v i
  hψ : ∀ i, ψ i (e i) = 2
  hKz : ∀ i j, ψ i (e j) = (Kz i j : ZMod p)
  href : ∀ i, Module.reflection (hψ i) = Module.reflection (R.hφ i)

private noncomputable def fourRefl_scaled {a b c d : U ≃ₗ[ZMod p] U}
    (R : FourReflRoots a b c d) (cc : Fin 4 → ZMod p) (hc0 : ∀ i, cc i ≠ 0)
    (hc : ∀ i j, (cc i)⁻¹ * cc j * R.φ i (R.v j) = (Kz i j : ZMod p)) :
    FourReflScaled a b c d R := by
  let e : Fin 4 → U := fun i => cc i • R.v i
  let ψ : Fin 4 → Module.Dual (ZMod p) U := fun i => (cc i)⁻¹ • R.φ i
  have hψ : ∀ i, ψ i (e i) = 2 := by
    intro i
    simp only [ψ, e, map_smul, LinearMap.smul_apply, smul_eq_mul]
    rw [R.hφ i, ← mul_assoc, mul_inv_cancel₀ (hc0 i), one_mul]
  have hKz : ∀ i j, ψ i (e j) = (Kz i j : ZMod p) := by
    intro i j
    by_cases hij : i = j
    · subst j
      simp only [ψ, e, map_smul, LinearMap.smul_apply, smul_eq_mul]
      rw [R.hφ i, ← mul_assoc, mul_inv_cancel₀ (hc0 i), one_mul]
      fin_cases i <;> simp [Kz]
    · simp only [ψ, e, map_smul, LinearMap.smul_apply, smul_eq_mul]
      simpa only [mul_assoc, mul_comm, mul_left_comm] using hc i j
  have href : ∀ i, Module.reflection (hψ i) = Module.reflection (R.hφ i) := by
    intro i
    ext y
    change y - ((cc i)⁻¹ • R.φ i) y • (cc i • R.v i) = y - R.φ i y • R.v i
    rw [LinearMap.smul_apply, smul_eq_mul, smul_smul]
    congr 1
    rw [mul_assoc, mul_comm (R.φ i y) (cc i), ← mul_assoc, inv_mul_cancel₀ (hc0 i), one_mul]
  exact ⟨cc, hc0, e, ψ, fun i => rfl, hψ, hKz, href⟩

private structure FourReflBasis (a b c d : U ≃ₗ[ZMod p] U)
    (R : FourReflRoots a b c d) where
  eB : Module.Basis (Fin 4) (ZMod p) U
  ψ : Fin 4 → Module.Dual (ZMod p) U
  hψ : ∀ i, ψ i (eB i) = 2
  hKz : ∀ i j, ψ i (eB j) = (Kz i j : ZMod p)
  href : ∀ i, Module.reflection (hψ i) = R.x i

private noncomputable def fourRefl_basis [Module.Finite (ZMod p) U]
    {a b c d : U ≃ₗ[ZMod p] U} {A : Subgroup (U ≃ₗ[ZMod p] U)} (h : FourRefl a b c d A)
    (R : FourReflRoots a b c d)
    (hfr : Module.finrank (ZMod p) (Submodule.span (ZMod p) (Set.range R.v)) = 4)
    (S : FourReflScaled a b c d R) : FourReflBasis a b c d R := by
  have hspan_e : Submodule.span (ZMod p) (Set.range S.e) =
      Submodule.span (ZMod p) (Set.range R.v) := by
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro x ⟨i, rfl⟩
      rw [S.he i]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    · rw [Submodule.span_le]
      rintro x ⟨i, rfl⟩
      have hvi : R.v i = (S.c i)⁻¹ • S.e i := by
        rw [S.he i, smul_smul, inv_mul_cancel₀ (S.hc0 i), one_smul]
      rw [hvi]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hli_e : LinearIndependent (ZMod p) S.e := by
    rw [linearIndependent_iff_card_eq_finrank_span]
    change Fintype.card (Fin 4) =
      Module.finrank (ZMod p) (Submodule.span (ZMod p) (Set.range S.e))
    rw [hspan_e, hfr]; rfl
  have htop_e : Submodule.span (ZMod p) (Set.range S.e) = ⊤ := by
    rw [hspan_e]
    exact Submodule.eq_top_of_finrank_eq (by rw [hfr, h.finrank_eq])
  let eB : Module.Basis (Fin 4) (ZMod p) U := Module.Basis.mk hli_e (le_of_eq htop_e.symm)
  have heB : ∀ i, eB i = S.e i :=
    fun i => congrFun (Module.Basis.coe_mk hli_e (le_of_eq htop_e.symm)) i
  have hψB : ∀ i, S.ψ i (eB i) = 2 := fun i => by rw [heB i]; exact S.hψ i
  have hKzB : ∀ i j, S.ψ i (eB j) = (Kz i j : ZMod p) := fun i j => by
    rw [heB j]; exact S.hKz i j
  have hrefB : ∀ i, Module.reflection (hψB i) = R.x i := by
    intro i
    have h1 : Module.reflection (hψB i) = Module.reflection (S.hψ i) := by
      ext y
      rw [Module.reflection_apply, Module.reflection_apply, heB i]
    exact h1.trans ((S.href i).trans (R.hx i).symm)
  exact ⟨eB, S.ψ, hψB, hKzB, hrefB⟩

private theorem false_i_aux [Module.Finite (ZMod p) U] (hp : p ≠ 2)
    {a b c d : U ≃ₗ[ZMod p] U} {A : Subgroup (U ≃ₗ[ZMod p] U)} (h : FourRefl a b c d A)
    (had : orderOf (a * d) = 2) (hac : orderOf (a * c) = 2) (hcd : orderOf (c * d) = 2)
    (hab : orderOf (a * b) = 3) (hbc : orderOf (b * c) = 3) (hbd : orderOf (b * d) = 4) :
    False := by
  have R := fourRefl_roots hp h
  have hordM := fourRefl_hordM had hac hcd hab hbc hbd R
  obtain ⟨hli, hfr⟩ := fourRefl_independence hp h R
  obtain ⟨cc, hc0, hc⟩ := fourRefl_gauge R.hφ (fourRefl_hP0 hp R.hφ hordM)
    (fourRefl_hPP hp R.hφ hordM) (fourRefl_hAK hp)
  have S := fourRefl_scaled R cc hc0 hc
  have B := fourRefl_basis h R hfr S
  have htv := isTransvection_wordW hp B.hψ B.hKz
  have hxA : ∀ i, R.x i ∈ A := by
    intro i
    rw [h.eq_closure]
    exact Subgroup.subset_closure (by rw [R.hx_eq]; fin_cases i <;> simp)
  have hRW : ∀ i, RW B.hψ i = R.x i := by intro i; rw [RW]; exact B.href i
  have hmem : wordW B.hψ ∈ A := by
    rw [wordW_eq_prod B.hψ]
    simp only [hRW]
    repeat' apply Subgroup.mul_mem
    all_goals exact hxA _
  exact h.transvectionFree (wordW B.hψ) hmem htv

private theorem cycle_sq {R : Type*} [CommRing R] {k k' w w' : R} (hk : k + k' = 2)
    (hkk : k * k' = 2) (hw : w + w' = 1) :
    ((1 - k + k * w) * (1 - k' + k' * w') - 2 * (w * w')) ^ 2 = 4 * (w * w') - 1 := by
  have h1 : (1 - k + k * w) * (1 - k' + k' * w') - 2 * (w * w') = (1 - k) * (1 - 2 * w) := by
    linear_combination (w' - 1) * hk + (-w' ^ 2 + w') * hkk +
      (k * k' * w' - k * k' - k - 2 * w' + 2) * hw
  rw [h1]
  linear_combination (4 * k * w' ^ 2 - 4 * k * w' + k) * hk + (-4 * w' ^ 2 + 4 * w' - 1) * hkk +
    (4 * k ^ 2 * w - 4 * k ^ 2 * w' - 8 * k * w + 8 * k * w' + 4 * w - 8 * w') * hw

private theorem babc_sum {R : Type*} [CommRing R] {Cab Cba Cac Cca Cbc Ccb : R}
    (hab : Cab * Cba = 1) (hbc : Cbc * Ccb = 1) (hac : Cac * Cca = 2)
    (hbabc : (Cac - Cab * Cbc) * (Cca - Cba * Ccb) = 1) :
    Cac * Ccb * Cba + Cab * Cbc * Cca = 2 ∧ Cac * Ccb * Cba * (Cab * Cbc * Cca) = 2 := by
  constructor
  · linear_combination hab + (Cab * Cba) * hbc + hac - hbabc
  · linear_combination 2 * hab + (Cab * Cac * Cba * Cca) * hbc + (Cab * Cba) * hac

theorem ne_three_of_orderOf_babc [Module.Finite (ZMod p) U] (hp : p ≠ 2)
    {a b c : U ≃ₗ[ZMod p] U} (ha : IsRefl p a) (hb : IsRefl p b) (hc : IsRefl p c)
    (hab : orderOf (a * b) = 3) (hbc : orderOf (b * c) = 3) (hac : orderOf (a * c) = 4)
    (hbabc : orderOf (b * a * b * c) = 3) : p ≠ 3 ∧ p ≠ 7 := by
  obtain ⟨va, φa, hφa, rfl⟩ := (isRefl_iff hp a).mp ha
  obtain ⟨vb, φb, hφb, rfl⟩ := (isRefl_iff hp b).mp hb
  obtain ⟨vc, φc, hφc, rfl⟩ := (isRefl_iff hp c).mp hc
  have h1 := apply_mul_apply_eq_one_of_orderOf_eq_three hp hφa hφb hab
  have h2 := apply_mul_apply_eq_one_of_orderOf_eq_three hp hφb hφc hbc
  have h3 := apply_mul_apply_eq_two_of_orderOf_eq_four hp hφa hφc hac
  rw [reflection_conj_reflection hφb hφa] at hbabc
  have h4 := apply_mul_apply_eq_one_of_orderOf_eq_three hp _ hφc hbabc
  simp only [LinearMap.sub_apply, LinearMap.smul_apply, map_sub, map_smul, smul_eq_mul] at h4
  obtain ⟨hs, hkk⟩ := babc_sum h1 h2 h3 h4
  have hk : (φa vc * φc vb * φb va) ^ 2 + ((-2 : ℤ) : ZMod p) * (φa vc * φc vb * φb va) +
      ((2 : ℤ) : ZMod p) = 0 := by
    push_cast
    linear_combination (φa vc * φc vb * φb va) * hs - hkk
  exact ⟨ne_of_root_quadratic (-2) 2 hk (by decide), ne_of_root_quadratic (-2) 2 hk (by decide)⟩

private theorem bd_four_cases {K : Type*} [Field K] {k k' w w' : K} (hk : k + k' = 2)
    (hkk : k * k' = 2) (hw : w + w' = 2) (hww : w * w' = 2) :
    (2 + k * w - 2 * w = 0 ∧ 2 + k' * w' - 2 * w' = 0) ∨
      ((1 - k + k * w) * (1 - k' + k' * w') = 5 ∧
        (1 - k + k * w) + (1 - k' + k' * w') = 4) := by
  have h : (k - w') * (k + w' - 2) = 0 := by linear_combination k * hk - hkk - w' * hw + hww
  rcases mul_eq_zero.mp h with hb | hg
  · right
    constructor
    · linear_combination (-w' ^ 3 + 2 * w' ^ 2 - 1) * hk +
        (k' * w' ^ 2 + w' ^ 3 - k' * w' - 2 * w' ^ 2 - 2 * w') * hw +
        (-w' ^ 2 + 2 * w' + 3) * hww +
        (k' * w * w' + w' ^ 3 - k' * w - k' * w' - 2 * w' ^ 2 + k' + w) * hb
    · linear_combination (w' - 1) * hk + (-w') * hw + 2 * hww + (w - w') * hb
  · left
    constructor
    · linear_combination (k + w' - 2) * hw + (-1) * hww + (-w' + 2) * hg
    · linear_combination w' * hk + w' * hw + (-1) * hww + (-w') * hg

private theorem eta_cdbdc {R : Type*} [CommRing R] {Cab Cba Cac Cca Cbc Ccb Cbd Cdb Ccd Cdc : R}
    (hab : Cab * Cba = 1) (hbc : Cbc * Ccb = 1) :
    (Cab - Cac * Ccb + Cac * Ccd * Cdb) * (Cba - Cca * Cbc + Cca * Cdc * Cbd) =
      (1 - Cac * Ccb * Cba + Cac * Ccb * Cba * (Ccd * Cdb * Cbc)) *
        (1 - Cab * Cbc * Cca + Cab * Cbc * Cca * (Cbd * Cdc * Ccb)) := by
  have h1 : Cba * (Cab - Cac * Ccb + Cac * Ccd * Cdb) =
      1 - Cac * Ccb * Cba + Cac * Ccb * Cba * (Ccd * Cdb * Cbc) := by
    linear_combination hab + (-Cac * Cba * Ccd * Cdb) * hbc
  have h2 : Cab * (Cba - Cca * Cbc + Cca * Cdc * Cbd) =
      1 - Cab * Cbc * Cca + Cab * Cbc * Cca * (Cbd * Cdc * Ccb) := by
    linear_combination hab + (-Cab * Cbd * Cca * Cdc) * hbc
  rw [← h1, ← h2]
  linear_combination (-(Cab - Cac * Ccb + Cac * Ccd * Cdb) * (Cba - Cca * Cbc + Cca * Cdc * Cbd)) *
    hab

private theorem eta_cdbdc_eq {va vb vc vd : U} {φa φb φc φd : Module.Dual (ZMod p) U}
    (had : φa vd = 0) (hda : φd va = 0) (hab : φa vb * φb va = 1) (hbc : φb vc * φc vb = 1) :
    φa ((vb - φd vb • vd) - φc (vb - φd vb • vd) • vc) *
        (((φb - φb vd • φd) - (φb - φb vd • φd) vc • φc) va) =
      (1 - φa vc * φc vb * φb va + φa vc * φc vb * φb va * (φc vd * φd vb * φb vc)) *
        (1 - φa vb * φb vc * φc va + φa vb * φb vc * φc va * (φb vd * φd vc * φc vb)) := by
  have h := eta_cdbdc (Cac := φa vc) (Cca := φc va) (Cbd := φb vd) (Cdb := φd vb)
    (Ccd := φc vd) (Cdc := φd vc) hab hbc
  simp only [LinearMap.sub_apply, LinearMap.smul_apply, map_sub, map_smul, smul_eq_mul, had, hda]
  linear_combination h

theorem false_iii_core [Module.Finite (ZMod p) U] (hp : p ≠ 2) (hp3 : p ≠ 3)
    {va vb vc vd : U} {φa φb φc φd : Module.Dual (ZMod p) U} (hφa : φa va = 2)
    (hφb : φb vb = 2) (hφc : φc vc = 2) (hφd : φd vd = 2) (had : φa vd = 0) (hda : φd va = 0)
    (hab : φa vb * φb va = 1) (hbc : φb vc * φc vb = 1) (hbd : φb vd * φd vb = 1)
    (hcd : φc vd * φd vc = 1) (hac : φa vc * φc va = 2)
    (hbabc : (φa vc - φa vb * φb vc) * (φc va - φb va * φc vb) = 1)
    (hbcbd : (φc vd - φc vb * φb vd) * (φd vc - φb vc * φd vb) = 1)
    (hx : orderOf (Module.reflection hφa * (Module.reflection hφc *
      (Module.reflection hφd * Module.reflection hφb * Module.reflection hφd) *
        Module.reflection hφc)) ≤ 4) : False := by
  rw [reflection_conj_reflection hφd hφb, reflection_conj_reflection hφc] at hx
  have hcases := eta_mem_of_orderOf_le_four hp hφa _ hx
  rw [eta_cdbdc_eq had hda hab hbc] at hcases
  obtain ⟨hs, hkk⟩ := babc_sum hab hbc hac hbabc
  have hw : φc vd * φd vb * φb vc + φb vd * φd vc * φc vb = 1 := by
    linear_combination -hbcbd + hcd + (φb vd * φd vb) * hbc + hbd
  have hww : φc vd * φd vb * φb vc * (φb vd * φd vc * φc vb) = 1 := by
    linear_combination (φb vc * φc vb * φb vd * φd vb) * hcd + (φb vd * φd vb) * hbc + hbd
  have key := cycle_sq hs hkk hw
  rw [hww] at key
  have h2 : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp
  have h3 : (3 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 3 hp3
  rcases hcases with h | h | h | h <;> rw [h] at key
  · exact one_ne_zero (by linear_combination key)
  · exact h2 (by linear_combination -key)
  · exact h3 (by linear_combination -key)
  · exact one_ne_zero (by linear_combination key)

private theorem cdbdc_entries {va vb vc vd : U} {φa φb φc φd : Module.Dual (ZMod p) U}
    (had : φa vd = 0) (hda : φd va = 0) (hab : φa vb * φb va = 1) (hbc : φb vc * φc vb = 1) :
    φb va * φa ((vb - φd vb • vd) - φc (vb - φd vb • vd) • vc) =
        1 - φa vc * φc vb * φb va + φa vc * φc vb * φb va * (φc vd * φd vb * φb vc) ∧
      φa vb * (((φb - φb vd • φd) - (φb - φb vd • φd) vc • φc) va) =
        1 - φa vb * φb vc * φc va + φa vb * φb vc * φc va * (φb vd * φd vc * φc vb) := by
  simp only [LinearMap.sub_apply, LinearMap.smul_apply, map_sub, map_smul, smul_eq_mul, had, hda]
  constructor
  · linear_combination hab + (-(φa vc) * φb va * φc vd * φd vb) * hbc
  · linear_combination hab + (-(φa vb) * φb vd * φc va * φd vc) * hbc

private theorem dpp_entries {va vb vc vd : U} {φa φb φc φd : Module.Dual (ZMod p) U}
    (had : φa vd = 0) (hda : φd va = 0) (hbc : φb vc * φc vb = 1) (hac : φa vc * φc va = 2)
    (hbd : φb vd * φd vb = 2) :
    φd vb * φb (vd - (φa - φa vc • φc) vd • (va - φc va • vc)) =
        2 + φa vc * φc vb * φb va * (φc vd * φd vb * φb vc) - 2 * (φc vd * φd vb * φb vc) ∧
      φb vd * ((φd - φd (va - φc va • vc) • (φa - φa vc • φc)) vb) =
        2 + φa vb * φb vc * φc va * (φb vd * φd vc * φc vb) - 2 * (φb vd * φd vc * φc vb) := by
  simp only [LinearMap.sub_apply, LinearMap.smul_apply, map_sub, map_smul, smul_eq_mul, had, hda]
  constructor
  · linear_combination (-(φa vc) * φb va * φc vd * φd vb) * hbc +
      (-(φb vc) * φc vd * φd vb) * hac + hbd
  · linear_combination (-(φa vb) * φb vd * φc va * φd vc) * hbc +
      (-(φb vd) * φc vb * φd vc) * hac + hbd

private theorem ac_sq_conj_eq {G : Type*} [Group G] {a c d : G} (ha : a * a = 1) (hc : c * c = 1)
    (had : a * d = d * a) :
    (a * c) ^ 2 * (c * a * c * d * (c * a * c)) * ((a * c) ^ 2)⁻¹ = d := by
  have ha' : ∀ x, a * (a * x) = x := fun x => by rw [← mul_assoc, ha, one_mul]
  have hc' : ∀ x, c * (c * x) = x := fun x => by rw [← mul_assoc, hc, one_mul]
  rw [mul_inv_eq_iff_eq_mul]
  simp only [pow_two, mul_assoc, ha', hc']
  rw [← mul_assoc a d, had, mul_assoc]

private theorem mul_comm_conj_of_mul_comm {G : Type*} [Group G] {g b d e : G}
    (hd : g * e * g⁻¹ = d) (h : b * e = e * b) :
    g * b * g⁻¹ * d = d * (g * b * g⁻¹) := by
  subst hd
  simp only [mul_assoc, inv_mul_cancel_left]
  rw [← mul_assoc b, h, mul_assoc]

private theorem commute_of_bd_four_core_false [Module.Finite (ZMod p) U] (hp : p ≠ 2) (hp3 : p ≠ 3)
    {va vb vc vd : U} {φa φb φc φd : Module.Dual (ZMod p) U} (hφa : φa va = 2)
    (hφb : φb vb = 2) (hφc : φc vc = 2) (hφd : φd vd = 2) (had : φa vd = 0) (hda : φd va = 0)
    (hab : φa vb * φb va = 1) (hbc : φb vc * φc vb = 1)
    (hP : (1 - φa vc * φc vb * φb va + φa vc * φc vb * φb va * (φc vd * φd vb * φb vc)) *
      (1 - φa vb * φb vc * φc va + φa vb * φb vc * φc va * (φb vd * φd vc * φc vb)) = 5)
    (hS : (1 - φa vc * φc vb * φb va + φa vc * φc vb * φb va * (φc vd * φd vb * φb vc)) +
      (1 - φa vb * φb vc * φc va + φa vb * φb vc * φc va * (φb vd * φd vc * φc vb)) = 4)
    (hx : orderOf (Module.reflection hφa * (Module.reflection hφc *
      (Module.reflection hφd * Module.reflection hφb * Module.reflection hφd) *
        Module.reflection hφc)) ≤ 4) : False := by
  rw [reflection_conj_reflection hφd hφb, reflection_conj_reflection hφc] at hx
  obtain ⟨e1, e2⟩ := cdbdc_entries had hda hab hbc
  have hprod := eta_cdbdc_eq had hda hab hbc
  have h2 : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp
  have h3 : (3 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 3 hp3
  rcases eta_cases_of_orderOf_le_four hp hφa _ hx with ⟨z1, z2⟩ | h | h | ⟨-, h⟩
  · rw [z1, mul_zero] at e1
    rw [z2, mul_zero] at e2
    have h4 : (2 : ZMod p) * 2 = 0 := by linear_combination -hS - e1 - e2
    exact h2 (mul_self_eq_zero.mp h4)
  · have h4 : (2 : ZMod p) * 2 = 0 := by linear_combination -hP - hprod + h
    exact h2 (mul_self_eq_zero.mp h4)
  · exact h3 (by linear_combination -hP - hprod + h)
  · have h1 : (1 : ZMod p) = 0 := by linear_combination -hP - hprod + h
    exact one_ne_zero h1

theorem commute_of_bd_four_core [Module.Finite (ZMod p) U] (hp : p ≠ 2) (hp3 : p ≠ 3)
    {va vb vc vd : U} {φa φb φc φd : Module.Dual (ZMod p) U} (hφa : φa va = 2)
    (hφb : φb vb = 2) (hφc : φc vc = 2) (hφd : φd vd = 2) (had : φa vd = 0) (hda : φd va = 0)
    (hab : φa vb * φb va = 1) (hbc : φb vc * φc vb = 1) (hac : φa vc * φc va = 2)
    (hcd : φc vd * φd vc = 1) (hbd : φb vd * φd vb = 2)
    (hbabc : (φa vc - φa vb * φb vc) * (φc va - φb va * φc vb) = 1)
    (hcbcd : (φb vd - φb vc * φc vd) * (φd vb - φc vb * φd vc) = 1)
    (hx : orderOf (Module.reflection hφa * (Module.reflection hφc *
      (Module.reflection hφd * Module.reflection hφb * Module.reflection hφd) *
        Module.reflection hφc)) ≤ 4) :
    (Module.reflection hφa * Module.reflection hφc) ^ 2 * Module.reflection hφb *
        ((Module.reflection hφa * Module.reflection hφc) ^ 2)⁻¹ * Module.reflection hφd =
      Module.reflection hφd * ((Module.reflection hφa * Module.reflection hφc) ^ 2 *
        Module.reflection hφb * ((Module.reflection hφa * Module.reflection hφc) ^ 2)⁻¹) := by
  obtain ⟨hk, hkk⟩ := babc_sum hab hbc hac hbabc
  have hw : φc vd * φd vb * φb vc + φb vd * φd vc * φc vb = 2 := by
    linear_combination hbd + (φc vd * φd vc) * hbc + hcd - hcbcd
  have hww : φc vd * φd vb * φb vc * (φb vd * φd vc * φc vb) = 2 := by
    linear_combination (φc vd * φd vc * φb vd * φd vb) * hbc + (φb vd * φd vb) * hcd + hbd
  have h2 : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp
  rcases bd_four_cases hk hkk hw hww with ⟨g1, g2⟩ | ⟨hP, hS⟩
  · obtain ⟨d1, d2⟩ := dpp_entries had hda hbc hac hbd
    have hbd0 : φb vd ≠ 0 := left_ne_zero_of_mul (by rw [hbd]; exact h2)
    have hdb0 : φd vb ≠ 0 := right_ne_zero_of_mul (by rw [hbd]; exact h2)
    rw [g1] at d1
    rw [g2] at d2
    have hcomm := reflection_mul_comm_of_apply_eq_zero hφb
      (conj_pairing (conj_pairing hφc hφa) hφd)
      ((mul_eq_zero.mp d1).resolve_left hdb0) ((mul_eq_zero.mp d2).resolve_left hbd0)
    rw [← reflection_conj_reflection (conj_pairing hφc hφa) hφd,
      ← reflection_conj_reflection hφc hφa] at hcomm
    have hadc : Module.reflection hφa * Module.reflection hφd =
        Module.reflection hφd * Module.reflection hφa :=
      reflection_mul_comm_of_apply_eq_zero hφa hφd had hda
    exact mul_comm_conj_of_mul_comm
      (ac_sq_conj_eq (mul_eq_one_iff_eq_inv.mpr (Module.reflection_inv hφa).symm)
        (mul_eq_one_iff_eq_inv.mpr (Module.reflection_inv hφc).symm) hadc) hcomm
  · exact (commute_of_bd_four_core_false hp hp3 hφa hφb hφc hφd had hda hab hbc hP hS hx).elim

private theorem orderOf_bab_of_false_ii (hp : p ≠ 2) {va vb vc vd : U}
    {φa φb φc φd : Module.Dual (ZMod p) U} (hφa : φa va = 2) (hφb : φb vb = 2)
    (hφc : φc vc = 2) (hφd : φd vd = 2) (had1 : φa vd = 0) (had2 : φd va = 0)
    (hbd1 : φb vd = 0) (hbd2 : φd vb = 0) (h1 : φa vb * φb va = 2) (h2 : φa vc * φc va = 1)
    (h3 : φb vc * φc vb = 1) (h4 : (φa vb - φa vc * φc vb) * (φb va - φc va * φb vc) = 1) :
    φb va ≠ 0 ∧
      orderOf (Module.reflection hφa * Module.reflection (conj_pairing hφb hφa)) = 2 ∧
      orderOf (Module.reflection (conj_pairing hφb hφa) * Module.reflection hφd) = 2 ∧
      orderOf (Module.reflection hφc * Module.reflection (conj_pairing hφb hφa)) = 3 := by
  have hs : φa vb * φb vc * φc va + φa vc * φc vb * φb va = 2 := by
    linear_combination h1 + h2 + (φa vc * φc va) * h3 - h4
  have hkk : φa vb * φb vc * φc va * (φa vc * φc vb * φb va) = 2 := by
    linear_combination h1 + (φa vb * φb va) * h2 + (φa vb * φa vc * φb va * φc va) * h3
  have hp3 : p ≠ 3 := by
    have hq : (φa vb * φb vc * φc va) ^ 2 + ((-2 : ℤ) : ZMod p) * (φa vb * φb vc * φc va) +
        ((2 : ℤ) : ZMod p) = 0 := by
      push_cast
      linear_combination (φa vb * φb vc * φc va) * hs - hkk
    exact ne_of_root_quadratic (-2) 2 hq (by decide)
  refine ⟨fun h0 => ?_, ?_, ?_, ?_⟩
  · rw [h0, mul_zero] at h1
    exact ZMod.prime_ne_zero p 2 hp h1.symm
  · refine orderOf_reflection_mul_eq_two hp _ _ ?_ ?_ <;>
      simp only [LinearMap.sub_apply, LinearMap.smul_apply, map_sub, map_smul, smul_eq_mul,
        hφa] <;>
      linear_combination -h1
  · refine orderOf_reflection_mul_eq_two hp _ _ ?_ ?_ <;>
      simp only [LinearMap.sub_apply, LinearMap.smul_apply, map_sub, map_smul, smul_eq_mul,
        had1, had2, hbd1, hbd2] <;> ring
  · refine orderOf_reflection_mul_eq_three hp3 _ _ ?_
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, map_sub, map_smul, smul_eq_mul]
    linear_combination h4 + (φa vb * φb va - φa vc * φc va) * h3

theorem false_bd_four_cbcd_four_core [Module.Finite (ZMod p) U] (hp : p ≠ 2) (hp3 : p ≠ 3)
    (hp7 : p ≠ 7) {va vb vc vd : U} {φa φb φc φd : Module.Dual (ZMod p) U} (hφa : φa va = 2)
    (hφb : φb vb = 2) (hφc : φc vc = 2) (hφd : φd vd = 2) (had : φa vd = 0) (hda : φd va = 0)
    (hab : φa vb * φb va = 1) (hbc : φb vc * φc vb = 1) (hac : φa vc * φc va = 2)
    (hcd : φc vd * φd vc = 1) (hbd : φb vd * φd vb = 2)
    (hbabc : (φa vc - φa vb * φb vc) * (φc va - φb va * φc vb) = 1)
    (hcbcd : (φb vd - φb vc * φc vd) * (φd vb - φc vb * φd vc) = 2)
    (hx : orderOf (Module.reflection hφa * (Module.reflection hφc *
      (Module.reflection hφd * Module.reflection hφb * Module.reflection hφd) *
        Module.reflection hφc)) ≤ 4) : False := by
  rw [reflection_conj_reflection hφd hφb, reflection_conj_reflection hφc] at hx
  have hcases := eta_mem_of_orderOf_le_four hp hφa _ hx
  rw [eta_cdbdc_eq had hda hab hbc] at hcases
  obtain ⟨hs, hkk⟩ := babc_sum hab hbc hac hbabc
  have hw : φc vd * φd vb * φb vc + φb vd * φd vc * φc vb = 1 := by
    linear_combination hbd + (φc vd * φd vc) * hbc + hcd - hcbcd
  have hww : φc vd * φd vb * φb vc * (φb vd * φd vc * φc vb) = 2 := by
    linear_combination (φc vd * φd vc * φb vd * φd vb) * hbc + (φb vd * φd vb) * hcd + hbd
  have key := cycle_sq hs hkk hw
  rw [hww] at key
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have h2 : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp
  have h3 : (3 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 3 hp3
  have h7 : (7 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 7 hp7
  rcases hcases with h | h | h | h <;> rw [h] at key
  · exact h3 (mul_self_eq_zero.mp (by linear_combination key))
  · exact h2 (by linear_combination key)
  · exact h3 (by linear_combination -key)
  · exact h7 (by linear_combination -key)

theorem commute_of_bd_three_cbcd_four [Module.Finite (ZMod p) U] (hp : p ≠ 2) (hp3 : p ≠ 3)
    {va vb vc vd : U} {φa φb φc φd : Module.Dual (ZMod p) U} (hφa : φa va = 2)
    (hφb : φb vb = 2) (hφc : φc vc = 2) (hφd : φd vd = 2) (had : φa vd = 0) (hda : φd va = 0)
    (hab : φa vb * φb va = 1) (hbc : φb vc * φc vb = 1) (hac : φa vc * φc va = 2)
    (hcd : φc vd * φd vc = 1) (hbd : φb vd * φd vb = 1)
    (hbabc : (φa vc - φa vb * φb vc) * (φc va - φb va * φc vb) = 1)
    (hcbcd : (φb vd - φb vc * φc vd) * (φd vb - φc vb * φd vc) = 2)
    (hx : orderOf (Module.reflection hφa * (Module.reflection hφc *
      (Module.reflection hφd * Module.reflection (conj_pairing hφc hφb) *
        Module.reflection hφd) * Module.reflection hφc)) ≤ 4) :
    (Module.reflection hφa * Module.reflection hφc) ^ 2 * Module.reflection hφc *
        Module.reflection hφb *
        ((Module.reflection hφa * Module.reflection hφc) ^ 2 * Module.reflection hφc)⁻¹ *
          Module.reflection hφd =
      Module.reflection hφd * ((Module.reflection hφa * Module.reflection hφc) ^ 2 *
        Module.reflection hφc * Module.reflection hφb *
          ((Module.reflection hφa * Module.reflection hφc) ^ 2 * Module.reflection hφc)⁻¹) := by
  obtain ⟨hs, -⟩ := babc_sum hab hbc hac hbabc
  have e1 : φa (vb - φc vb • vc) * (φb - φb vc • φc) va = 1 := by
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, map_sub, map_smul, smul_eq_mul]
    linear_combination hab - hs + (φa vc * φc va) * hbc + hac
  have e2 : (φb - φb vc • φc) vc * φc (vb - φc vb • vc) = 1 := by
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, map_sub, map_smul, smul_eq_mul, hφc]
    linear_combination hbc
  have e3 : (φb - φb vc • φc) vd * φd (vb - φc vb • vc) = 2 := by
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, map_sub, map_smul, smul_eq_mul]
    linear_combination hcbcd
  have e4 : (φa vc - φa (vb - φc vb • vc) * (φb - φb vc • φc) vc) *
      (φc va - (φb - φb vc • φc) va * φc (vb - φc vb • vc)) = 1 := by
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, map_sub, map_smul, smul_eq_mul, hφc]
    linear_combination (φa vb * φb va - (φa vc * φc vb * φb va + φa vb * φb vc * φc va) +
      (φb vc * φc vb - 1) * (φa vc * φc va)) * hbc + hab
  have e5 : ((φb - φb vc • φc) vd - (φb - φb vc • φc) vc * φc vd) *
      (φd (vb - φc vb • vc) - φc (vb - φc vb • vc) * φd vc) = 1 := by
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, map_sub, map_smul, smul_eq_mul, hφc]
    linear_combination hbd
  have hcore := commute_of_bd_four_core hp hp3 hφa (conj_pairing hφc hφb) hφc hφd had hda e1
    e2 hac hcd e3 e4 e5 hx
  rw [← reflection_conj_reflection hφc hφb] at hcore
  rw [mul_inv_rev, Module.reflection_inv]
  simpa only [mul_assoc] using hcore

private theorem exists_commute_conj_of_cbcd_two (hp : p ≠ 2) {va vb vc vd : U}
    {φa φb φc φd : Module.Dual (ZMod p) U} (hφa : φa va = 2) (hφb : φb vb = 2)
    (hφc : φc vc = 2) (hφd : φd vd = 2)
    (hm : orderOf (Module.reflection (conj_pairing hφc hφb) * Module.reflection hφd) = 2) :
    ∃ g ∈ Subgroup.closure ({Module.reflection hφa, Module.reflection hφc} :
      Set (U ≃ₗ[ZMod p] U)), g * Module.reflection hφb * g⁻¹ * Module.reflection hφd =
        Module.reflection hφd * (g * Module.reflection hφb * g⁻¹) := by
  obtain ⟨z1, z2⟩ := apply_eq_zero_of_orderOf_eq_two hp _ hφd hm
  refine ⟨Module.reflection hφc, Subgroup.subset_closure (by simp), ?_⟩
  rw [Module.reflection_inv, reflection_conj_reflection hφc hφb]
  exact reflection_mul_comm_of_apply_eq_zero _ hφd z1 z2

namespace FourRefl

variable [Module.Finite (ZMod p) U] {a b c d : U ≃ₗ[ZMod p] U} {A : Subgroup (U ≃ₗ[ZMod p] U)}

omit [Module.Finite (ZMod p) U] in
private lemma finrank_movedSpace_of_isRefl {t : U ≃ₗ[ZMod p] U} (ht : IsRefl p t) :
    Module.finrank (ZMod p) (HardMathSupport.Kantor79.movedSpace t) = 1 := ht.2

private lemma finrank_sup_four_sub_three {M0 M1 M2 M3 : Submodule (ZMod p) U}
    (h0 : Module.finrank (ZMod p) ↥M0 = 1) (h1 : Module.finrank (ZMod p) ↥M1 = 1)
    (h2 : Module.finrank (ZMod p) ↥M2 = 1) (h3 : Module.finrank (ZMod p) ↥M3 = 1)
    (htop : Module.finrank (ZMod p) ↥(M0 ⊔ M1 ⊔ M2 ⊔ M3) = 4) :
    Module.finrank (ZMod p) ↥(M0 ⊔ M2 ⊔ M3) = 3 := by
  set S : Submodule (ZMod p) U := M0 ⊔ M2 ⊔ M3 with hS
  have htop' : S ⊔ M1 = M0 ⊔ M1 ⊔ M2 ⊔ M3 := by rw [hS]; ac_rfl
  have h02 : Module.finrank (ZMod p) ↥(M0 ⊔ M2) ≤ 2 := by
    have h := Submodule.finrank_add_le_finrank_add_finrank M0 M2
    omega
  have hSle : Module.finrank (ZMod p) ↥S ≤ 3 := by
    have h := Submodule.finrank_add_le_finrank_add_finrank (M0 ⊔ M2) M3
    rw [hS]
    omega
  have hmod := Submodule.finrank_sup_add_finrank_inf_eq S M1
  rw [htop', htop] at hmod
  have : Module.finrank (ZMod p) ↥(S ⊓ M1) = 0 ∧
      Module.finrank (ZMod p) ↥S + Module.finrank (ZMod p) ↥M1 = 4 := by omega
  omega

private lemma commutatorSpace_closure_four {a b c d : U ≃ₗ[ZMod p] U} :
    HardMathSupport.Kantor79.commutatorSpace
        (Subgroup.closure ({a, b, c, d} : Set (U ≃ₗ[ZMod p] U))) =
      HardMathSupport.Kantor79.movedSpace a ⊔ HardMathSupport.Kantor79.movedSpace b ⊔
        HardMathSupport.Kantor79.movedSpace c ⊔ HardMathSupport.Kantor79.movedSpace d := by
  have hrange : (Set.range ![a, b, c, d] : Set (U ≃ₗ[ZMod p] U)) = {a, b, c, d} := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      fin_cases y <;> simp
    · intro hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
      · exact ⟨2, rfl⟩
      · exact ⟨3, rfl⟩
  rw [← hrange, HardMathSupport.Kantor79.commutatorSpace_closure_eq_iSup_movedSpace
    (fun i : Fin 4 => ![a, b, c, d] i)]
  apply le_antisymm
  · refine iSup_le fun i => ?_
    fin_cases i
    · exact le_trans le_sup_left (le_trans le_sup_left le_sup_left)
    · exact le_trans le_sup_right (le_trans le_sup_left le_sup_left)
    · exact le_trans le_sup_right le_sup_left
    · exact le_sup_right
  · refine sup_le ?_ ?_
    · refine sup_le ?_ ?_
      · refine sup_le ?_ ?_
        · simpa using le_iSup (fun i : Fin 4 => HardMathSupport.Kantor79.movedSpace
            (![a,b,c,d] i)) 0
        · simpa using le_iSup (fun i : Fin 4 => HardMathSupport.Kantor79.movedSpace
            (![a,b,c,d] i)) 1
      · simpa using le_iSup (fun i : Fin 4 => HardMathSupport.Kantor79.movedSpace
          (![a,b,c,d] i)) 2
    · simpa using le_iSup (fun i : Fin 4 => HardMathSupport.Kantor79.movedSpace
        (![a,b,c,d] i)) 3

private lemma commutatorSpace_closure_three {a b c : U ≃ₗ[ZMod p] U} :
    HardMathSupport.Kantor79.commutatorSpace
        (Subgroup.closure ({a, b, c} : Set (U ≃ₗ[ZMod p] U))) =
      HardMathSupport.Kantor79.movedSpace a ⊔ HardMathSupport.Kantor79.movedSpace b ⊔
        HardMathSupport.Kantor79.movedSpace c := by
  have hrange : (Set.range ![a, b, c] : Set (U ≃ₗ[ZMod p] U)) = {a, b, c} := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      fin_cases y <;> simp
    · intro hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
      · exact ⟨2, rfl⟩
  rw [← hrange, HardMathSupport.Kantor79.commutatorSpace_closure_eq_iSup_movedSpace
    (fun i : Fin 3 => ![a, b, c] i)]
  apply le_antisymm
  · refine iSup_le fun i => ?_
    fin_cases i
    · exact le_trans le_sup_left le_sup_left
    · exact le_trans le_sup_right le_sup_left
    · exact le_sup_right
  · refine sup_le ?_ ?_
    · refine sup_le ?_ ?_
      · simpa using le_iSup (fun i : Fin 3 => HardMathSupport.Kantor79.movedSpace
          (![a,b,c] i)) 0
      · simpa using le_iSup (fun i : Fin 3 => HardMathSupport.Kantor79.movedSpace
          (![a,b,c] i)) 1
    · simp

omit [Module.Finite (ZMod p) U] in
theorem mem_a (h : FourRefl a b c d A) : a ∈ A := by
  rw [h.eq_closure]; exact Subgroup.subset_closure (by simp)

omit [Module.Finite (ZMod p) U] in
theorem mem_b (h : FourRefl a b c d A) : b ∈ A := by
  rw [h.eq_closure]; exact Subgroup.subset_closure (by simp)

omit [Module.Finite (ZMod p) U] in
theorem mem_c (h : FourRefl a b c d A) : c ∈ A := by
  rw [h.eq_closure]; exact Subgroup.subset_closure (by simp)

omit [Module.Finite (ZMod p) U] in
theorem mem_d (h : FourRefl a b c d A) : d ∈ A := by
  rw [h.eq_closure]; exact Subgroup.subset_closure (by simp)

theorem orderOf_mul_conj_le (hp : p ≠ 2) (h : FourRefl a b c d A) {x : U ≃ₗ[ZMod p] U}
    (hx : x ∈ A) (hrx : IsRefl p x) : orderOf (a * (c * (d * x * d) * c)) ≤ 4 := by
  refine h.dmax.1 _ h.mem_a _ (A.mul_mem (A.mul_mem h.mem_c
    (A.mul_mem (A.mul_mem h.mem_d hx) h.mem_d)) h.mem_c) h.isRefl_a ?_
  obtain ⟨vc, φc, hφc, rfl⟩ := (isRefl_iff hp c).mp h.isRefl_c
  obtain ⟨vd, φd, hφd, rfl⟩ := (isRefl_iff hp d).mp h.isRefl_d
  obtain ⟨vx, φx, hφx, rfl⟩ := (isRefl_iff hp x).mp hrx
  rw [reflection_conj_reflection hφd hφx, reflection_conj_reflection hφc]
  exact isRefl_reflection hp _

theorem not_mem_closure_three (h : FourRefl a b c d A) :
    d ∉ Subgroup.closure ({a, b, c} : Set (U ≃ₗ[ZMod p] U)) := by
  intro hd
  have hr : (Set.range ![a, b, c] : Set (U ≃ₗ[ZMod p] U)) = {a, b, c} := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      fin_cases y <;> simp
    · intro hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
      · exact ⟨2, rfl⟩
  have hA : A = Subgroup.closure (Set.range ![a, b, c]) := by
    rw [hr, h.eq_closure]
    refine le_antisymm ((Subgroup.closure_le _).mpr ?_) (Subgroup.closure_mono ?_)
    · intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact Subgroup.subset_closure (by simp)
      · exact Subgroup.subset_closure (by simp)
      · exact Subgroup.subset_closure (by simp)
      · exact hd
    · intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
      tauto
  have hle := HardMathSupport.Kantor79.finrank_commutatorSpace_le ![a, b, c] (r := 1)
    (fun i => by
      fin_cases i
      exacts [h.isRefl_a.2.le, h.isRefl_b.2.le, h.isRefl_c.2.le])
  rw [← hA, h.finrank_commutatorSpace] at hle
  norm_num at hle

theorem orderOf_mul_ne_one (h : FourRefl a b c d A) {x : U ≃ₗ[ZMod p] U}
    (hx : x ∈ Subgroup.closure ({a, b, c} : Set (U ≃ₗ[ZMod p] U))) :
    orderOf (x * d) ≠ 1 := by
  intro h1
  have hdx : d = x⁻¹ := eq_inv_of_mul_eq_one_right (orderOf_eq_one_iff.mp h1)
  exact not_mem_closure_three h (by rw [hdx]; exact Subgroup.inv_mem _ hx)

theorem eq_three_of_cd_four (hp : p ≠ 2) (h : FourRefl a b c d A) (had : orderOf (a * d) = 2)
    (hac : orderOf (a * c) = 4) (hcd : orderOf (c * d) = 4) : p = 3 := by
  have h0 : Module.finrank (ZMod p) ↥(HardMathSupport.Kantor79.movedSpace a) = 1 :=
    finrank_movedSpace_of_isRefl h.isRefl_a
  have h1 : Module.finrank (ZMod p) ↥(HardMathSupport.Kantor79.movedSpace b) = 1 :=
    finrank_movedSpace_of_isRefl h.isRefl_b
  have h2 : Module.finrank (ZMod p) ↥(HardMathSupport.Kantor79.movedSpace c) = 1 :=
    finrank_movedSpace_of_isRefl h.isRefl_c
  have h3 : Module.finrank (ZMod p) ↥(HardMathSupport.Kantor79.movedSpace d) = 1 :=
    finrank_movedSpace_of_isRefl h.isRefl_d
  have htop : Module.finrank (ZMod p)
      ↥(HardMathSupport.Kantor79.movedSpace a ⊔ HardMathSupport.Kantor79.movedSpace b ⊔
        HardMathSupport.Kantor79.movedSpace c ⊔ HardMathSupport.Kantor79.movedSpace d) = 4 := by
    rw [← h.finrank_commutatorSpace, h.eq_closure, commutatorSpace_closure_four]
  have hdim : Module.finrank (ZMod p)
      ↥(HardMathSupport.Kantor79.commutatorSpace (Subgroup.closure {a, c, d})) = 3 := by
    rw [commutatorSpace_closure_three (b := c)]
    exact finrank_sup_four_sub_three h0 h1 h2 h3 htop
  have hGA : Subgroup.closure ({a, c, d} : Set (U ≃ₗ[ZMod p] U)) ≤ A := by
    rw [h.eq_closure]
    refine Subgroup.closure_mono ?_
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
    tauto
  obtain ⟨x, hxG, y, hyG, hxr, hyr, hxy⟩ :=
    exists_orderOf_mul_eq_max_gammaP hp h.isRefl_a h.isRefl_c h.isRefl_d hac hcd had rfl hdim
  have hx4 : orderOf (x * y) ≤ 4 := h.dmax.1 x (hGA hxG) y (hGA hyG) hxr hyr
  have hp4 : p ≤ 4 := by
    have : max 4 p ≤ 4 := hxy ▸ hx4
    omega
  have hpp : p.Prime := Fact.out
  have hp3 : p = 3 := by
    have h2' : 2 ≤ p := hpp.two_le
    have hne4 : p ≠ 4 := by rintro rfl; norm_num at hpp
    omega
  exact hp3

private theorem cbc_facts (hp : p ≠ 2) {va vb vc vd : U}
    {φa φb φc φd : Module.Dual (ZMod p) U} (hφa : φa va = 2) (hφb : φb vb = 2)
    (hφc : φc vc = 2) (hφd : φd vd = 2)
    (h : FourRefl (Module.reflection hφa) (Module.reflection hφb) (Module.reflection hφc)
      (Module.reflection hφd) A) :
    Module.reflection (conj_pairing hφc hφb) ∈ A ∧
      Module.reflection (conj_pairing hφc hφb) ∈ Subgroup.closure
        ({Module.reflection hφa, Module.reflection hφb, Module.reflection hφc} :
          Set (U ≃ₗ[ZMod p] U)) ∧
      0 < orderOf (Module.reflection (conj_pairing hφc hφb) * Module.reflection hφd) ∧
      orderOf (Module.reflection (conj_pairing hφc hφb) * Module.reflection hφd) ≤ 4 := by
  have hA : Module.reflection (conj_pairing hφc hφb) ∈ A := by
    rw [← reflection_conj_reflection hφc hφb]; exact A.mul_mem (A.mul_mem h.mem_c h.mem_b) h.mem_c
  have : Finite U := Module.finite_of_finite (ZMod p)
  have : Finite (U ≃ₗ[ZMod p] U) :=
    Finite.of_injective (fun e : U ≃ₗ[ZMod p] U => (e : U → U)) DFunLike.coe_injective
  refine ⟨hA, ?_, orderOf_pos _, h.dmax.1 _ hA _ h.mem_d (isRefl_reflection hp _) h.isRefl_d⟩
  rw [← reflection_conj_reflection hφc hφb]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
    (Subgroup.subset_closure (by simp))) (Subgroup.subset_closure (by simp))

private theorem exists_commute_conj_bd_three (hp : p ≠ 2) (hp3 : p ≠ 3)
    {va vb vc vd : U} {φa φb φc φd : Module.Dual (ZMod p) U} (hφa : φa va = 2)
    (hφb : φb vb = 2) (hφc : φc vc = 2) (hφd : φd vd = 2)
    (h : FourRefl (Module.reflection hφa) (Module.reflection hφb) (Module.reflection hφc)
      (Module.reflection hφd) A) (had : φa vd = 0) (hda : φd va = 0)
    (hab : φa vb * φb va = 1) (hbc : φb vc * φc vb = 1) (hac : φa vc * φc va = 2)
    (hcd : φc vd * φd vc = 1) (hbabc : (φa vc - φa vb * φb vc) * (φc va - φb va * φc vb) = 1)
    (hbd : φb vd * φd vb = 1) :
    ∃ g ∈ Subgroup.closure ({Module.reflection hφa, Module.reflection hφc} :
      Set (U ≃ₗ[ZMod p] U)), g * Module.reflection hφb * g⁻¹ * Module.reflection hφd =
        Module.reflection hφd * (g * Module.reflection hφb * g⁻¹) := by
  obtain ⟨hcbc, hcbc3, hpos, hle⟩ := cbc_facts hp hφa hφb hφc hφd h
  interval_cases hm : orderOf (Module.reflection (conj_pairing hφc hφb) * Module.reflection hφd)
  · exact absurd hm (orderOf_mul_ne_one h hcbc3)
  · exact exists_commute_conj_of_cbcd_two hp hφa hφb hφc hφd hm
  · exfalso
    have hm3 := apply_mul_apply_eq_one_of_orderOf_eq_three hp _ hφd hm
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, map_sub, map_smul, smul_eq_mul] at hm3
    refine false_iii_core hp hp3 hφa hφb hφc hφd had hda hab hbc hbd hcd hac hbabc ?_
      (h.orderOf_mul_conj_le hp h.mem_b h.isRefl_b)
    linear_combination hm3 + (φb vd * φd vb - φc vd * φd vc) * hbc
  · have hm4 := apply_mul_apply_eq_two_of_orderOf_eq_four hp _ hφd hm
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, map_sub, map_smul, smul_eq_mul] at hm4
    refine ⟨(Module.reflection hφa * Module.reflection hφc) ^ 2 * Module.reflection hφc,
      Subgroup.mul_mem _ (Subgroup.pow_mem _ (Subgroup.mul_mem _
        (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp))) 2)
        (Subgroup.subset_closure (by simp)), ?_⟩
    exact commute_of_bd_three_cbcd_four hp hp3 hφa hφb hφc hφd had hda hab hbc hac hcd hbd hbabc
      hm4 (h.orderOf_mul_conj_le hp hcbc (isRefl_reflection hp _))

private theorem exists_commute_conj_bd_four (hp : p ≠ 2) (hp3 : p ≠ 3) (hp7 : p ≠ 7)
    {va vb vc vd : U} {φa φb φc φd : Module.Dual (ZMod p) U} (hφa : φa va = 2)
    (hφb : φb vb = 2) (hφc : φc vc = 2) (hφd : φd vd = 2)
    (h : FourRefl (Module.reflection hφa) (Module.reflection hφb) (Module.reflection hφc)
      (Module.reflection hφd) A) (had : φa vd = 0) (hda : φd va = 0)
    (hab : φa vb * φb va = 1) (hbc : φb vc * φc vb = 1) (hac : φa vc * φc va = 2)
    (hcd : φc vd * φd vc = 1) (hbabc : (φa vc - φa vb * φb vc) * (φc va - φb va * φc vb) = 1)
    (hbd : φb vd * φd vb = 2) :
    ∃ g ∈ Subgroup.closure ({Module.reflection hφa, Module.reflection hφc} :
      Set (U ≃ₗ[ZMod p] U)), g * Module.reflection hφb * g⁻¹ * Module.reflection hφd =
        Module.reflection hφd * (g * Module.reflection hφb * g⁻¹) := by
  obtain ⟨-, hcbc3, hpos, hle⟩ := cbc_facts hp hφa hφb hφc hφd h
  have hx := h.orderOf_mul_conj_le hp h.mem_b h.isRefl_b
  interval_cases hm : orderOf (Module.reflection (conj_pairing hφc hφb) * Module.reflection hφd)
  · exact absurd hm (orderOf_mul_ne_one h hcbc3)
  · exact exists_commute_conj_of_cbcd_two hp hφa hφb hφc hφd hm
  · have hm3 := apply_mul_apply_eq_one_of_orderOf_eq_three hp _ hφd hm
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, map_sub, map_smul, smul_eq_mul] at hm3
    exact ⟨(Module.reflection hφa * Module.reflection hφc) ^ 2,
      Subgroup.pow_mem _ (Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
        (Subgroup.subset_closure (by simp))) 2,
      commute_of_bd_four_core hp hp3 hφa hφb hφc hφd had hda hab hbc hac hcd hbd hbabc hm3 hx⟩
  · exfalso
    have hm4 := apply_mul_apply_eq_two_of_orderOf_eq_four hp _ hφd hm
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, map_sub, map_smul, smul_eq_mul] at hm4
    exact false_bd_four_cbcd_four_core hp hp3 hp7 hφa hφb hφc hφd had hda hab hbc hac hcd hbd
      hbabc hm4 hx

theorem false_i (hp : p ≠ 2) (h : FourRefl a b c d A) (had : orderOf (a * d) = 2)
    (hac : orderOf (a * c) = 2) (hcd : orderOf (c * d) = 2) (hab : orderOf (a * b) = 3)
    (hbc : orderOf (b * c) = 3) (hbd : orderOf (b * d) = 4) : False := by
  exact false_i_aux hp h had hac hcd hab hbc hbd

omit [Module.Finite (ZMod p) U] in
theorem of_le (h : FourRefl a b c d A) {a' b' c' d' : U ≃ₗ[ZMod p] U}
    (ha : IsRefl p a') (hb : IsRefl p b') (hc : IsRefl p c') (hd : IsRefl p d')
    (hle : Subgroup.closure ({a', b', c', d'} : Set (U ≃ₗ[ZMod p] U)) ≤ A)
    (hV : Module.finrank (ZMod p) (HardMathSupport.Kantor79.commutatorSpace
      (Subgroup.closure ({a', b', c', d'} : Set (U ≃ₗ[ZMod p] U)))) = 4)
    (h4 : ∃ x ∈ Subgroup.closure ({a', b', c', d'} : Set (U ≃ₗ[ZMod p] U)),
      ∃ y ∈ Subgroup.closure ({a', b', c', d'} : Set (U ≃ₗ[ZMod p] U)),
        IsRefl p x ∧ IsRefl p y ∧ orderOf (x * y) = 4) :
    FourRefl a' b' c' d' (Subgroup.closure {a', b', c', d'}) :=
  ⟨h.finrank_eq, ha, hb, hc, hd, rfl, fun g hg => h.transvectionFree g (hle hg),
    ⟨fun x hx y hy => h.dmax.1 x (hle hx) y (hle hy), h4⟩, hV⟩

theorem finrank_commutatorSpace_bab (hp : p ≠ 2) {va vb vc vd : U}
    {φa φb φc φd : Module.Dual (ZMod p) U} (hφa : φa va = 2) (hφb : φb vb = 2)
    (hφc : φc vc = 2) (hφd : φd vd = 2) {A' : Subgroup (U ≃ₗ[ZMod p] U)}
    (h : FourRefl (Module.reflection hφa) (Module.reflection hφb) (Module.reflection hφc)
      (Module.reflection hφd) A) (hba : φb va ≠ 0) (hle : A' ≤ A)
    (ha : Module.reflection hφa ∈ A') (hb : Module.reflection (conj_pairing hφb hφa) ∈ A')
    (hc : Module.reflection hφc ∈ A') (hd : Module.reflection hφd ∈ A') :
    Module.finrank (ZMod p) (HardMathSupport.Kantor79.commutatorSpace A') = 4 := by
  have hva := mem_commutatorSpace_of_reflection_mem hp hφa ha
  have hvb' := mem_commutatorSpace_of_reflection_mem hp (conj_pairing hφb hφa) hb
  have hvb : vb ∈ HardMathSupport.Kantor79.commutatorSpace A' := by
    have hv : vb = (φb va)⁻¹ • (va - (va - φb va • vb)) := by
      rw [sub_sub_cancel, inv_smul_smul₀ hba]
    rw [hv]
    exact Submodule.smul_mem _ _ (Submodule.sub_mem _ hva hvb')
  have hmono : HardMathSupport.Kantor79.commutatorSpace A' ≤
      HardMathSupport.Kantor79.commutatorSpace A := by
    unfold HardMathSupport.Kantor79.commutatorSpace
    exact Submodule.span_mono fun w ⟨g, hg, v, hw⟩ => ⟨g, hle hg, v, hw⟩
  have hge : HardMathSupport.Kantor79.commutatorSpace A ≤
      HardMathSupport.Kantor79.commutatorSpace A' := by
    rw [h.eq_closure, commutatorSpace_closure_four]
    refine sup_le (sup_le (sup_le ?_ ?_) ?_) ?_
    · exact HardMathSupport.Kantor79.movedSpace_le_commutatorSpace ha
    · show HardMathSupport.Kantor79.movedSpace (Module.reflection hφb) ≤ _
      unfold HardMathSupport.Kantor79.movedSpace
      rintro _ ⟨x, rfl⟩
      change Module.reflection hφb x - x ∈ _
      rw [Module.reflection_apply, sub_sub_cancel_left]
      exact Submodule.neg_mem _ (Submodule.smul_mem _ _ hvb)
    · exact HardMathSupport.Kantor79.movedSpace_le_commutatorSpace hc
    · exact HardMathSupport.Kantor79.movedSpace_le_commutatorSpace hd
  apply le_antisymm
  · exact (Submodule.finrank_mono hmono).trans h.finrank_commutatorSpace.le
  · exact h.finrank_commutatorSpace.symm.le.trans (Submodule.finrank_mono hge)

theorem of_bab (hp : p ≠ 2) {va vb vc vd : U} {φa φb φc φd : Module.Dual (ZMod p) U}
    (hφa : φa va = 2) (hφb : φb vb = 2) (hφc : φc vc = 2) (hφd : φd vd = 2)
    (h : FourRefl (Module.reflection hφa) (Module.reflection hφb) (Module.reflection hφc)
      (Module.reflection hφd) A) (hba : φb va ≠ 0)
    (hcd : orderOf (Module.reflection hφc * Module.reflection hφd) = 4) :
    FourRefl (Module.reflection hφa) (Module.reflection hφc)
      (Module.reflection (conj_pairing hφb hφa)) (Module.reflection hφd)
      (Subgroup.closure {Module.reflection hφa, Module.reflection hφc,
        Module.reflection (conj_pairing hφb hφa), Module.reflection hφd}) := by
  have hb3 : Module.reflection (conj_pairing hφb hφa) ∈ A := by
    rw [← reflection_conj_reflection hφb hφa]
    exact A.mul_mem (A.mul_mem h.mem_b h.mem_a) h.mem_b
  have hle : Subgroup.closure ({Module.reflection hφa, Module.reflection hφc,
      Module.reflection (conj_pairing hφb hφa), Module.reflection hφd} :
        Set (U ≃ₗ[ZMod p] U)) ≤ A := by
    rw [Subgroup.closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact h.mem_a
    · exact h.mem_c
    · exact hb3
    · exact h.mem_d
  exact of_le h h.isRefl_a h.isRefl_c (isRefl_reflection hp (conj_pairing hφb hφa))
    h.isRefl_d hle (finrank_commutatorSpace_bab hp hφa hφb hφc hφd h hba hle
      (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp))
      (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp)))
    ⟨Module.reflection hφc, Subgroup.subset_closure (by simp), Module.reflection hφd,
      Subgroup.subset_closure (by simp), h.isRefl_c, h.isRefl_d, hcd⟩

theorem false_ii (hp : p ≠ 2) (h : FourRefl a b c d A) (had : orderOf (a * d) = 2)
    (hbd : orderOf (b * d) = 2) (hac : orderOf (a * c) = 3) (hbc : orderOf (b * c) = 3)
    (hcacb : orderOf (c * a * c * b) = 3) (hcd : orderOf (c * d) = 4)
    (hab : orderOf (a * b) = 4) : False := by
  obtain ⟨va, φa, hφa, rfl⟩ := (isRefl_iff hp a).mp h.isRefl_a
  obtain ⟨vb, φb, hφb, rfl⟩ := (isRefl_iff hp b).mp h.isRefl_b
  obtain ⟨vc, φc, hφc, rfl⟩ := (isRefl_iff hp c).mp h.isRefl_c
  obtain ⟨vd, φd, hφd, rfl⟩ := (isRefl_iff hp d).mp h.isRefl_d
  obtain ⟨had1, had2⟩ := apply_eq_zero_of_orderOf_eq_two hp hφa hφd had
  obtain ⟨hbd1, hbd2⟩ := apply_eq_zero_of_orderOf_eq_two hp hφb hφd hbd
  have h1 := apply_mul_apply_eq_two_of_orderOf_eq_four hp hφa hφb hab
  have h2 := apply_mul_apply_eq_one_of_orderOf_eq_three hp hφa hφc hac
  have h3 := apply_mul_apply_eq_one_of_orderOf_eq_three hp hφb hφc hbc
  rw [reflection_conj_reflection hφc hφa] at hcacb
  have h4 := apply_mul_apply_eq_one_of_orderOf_eq_three hp _ hφb hcacb
  simp only [LinearMap.sub_apply, LinearMap.smul_apply, map_sub, map_smul, smul_eq_mul] at h4
  obtain ⟨hba, hx, hy, hz⟩ :=
    orderOf_bab_of_false_ii hp hφa hφb hφc hφd had1 had2 hbd1 hbd2 h1 h2 h3 h4
  exact false_i hp (of_bab hp hφa hφb hφc hφd h hba hcd) had hx hy hac hz hcd

theorem orderOf_cd_eq_three (hp : p ≠ 2) (h : FourRefl a b c d A)
    (_hJ : ∀ X ≤ A, ReflGen p X → SplitSupport X 3 →
      (∃ x ∈ X, ∃ y ∈ X, IsRefl p x ∧ IsRefl p y ∧ orderOf (x * y) = 4) → Nat.card X ≠ 336)
    (had : orderOf (a * d) = 2) (hac : orderOf (a * c) = 4) (hab : orderOf (a * b) = 3)
    (hbc : orderOf (b * c) = 3) (hbabc : orderOf (b * a * b * c) = 3)
    (hcd : orderOf (c * d) ≠ 2) : orderOf (c * d) = 3 := by
  have hle := h.dmax.1 c h.mem_c d h.mem_d h.isRefl_c h.isRefl_d
  have : Finite U := Module.finite_of_finite (ZMod p)
  have : Finite (U ≃ₗ[ZMod p] U) :=
    Finite.of_injective (fun e : U ≃ₗ[ZMod p] U => (e : U → U)) DFunLike.coe_injective
  have hpos := orderOf_pos (c * d)
  have hp3 := (ne_three_of_orderOf_babc hp h.isRefl_a h.isRefl_b h.isRefl_c hab hbc hac
    hbabc).1
  interval_cases hn : orderOf (c * d)
  · exact absurd hn (orderOf_mul_ne_one h (Subgroup.subset_closure (by simp)))
  · omega
  · omega
  · exact absurd (eq_three_of_cd_four hp h had hac hn) hp3

theorem exists_commute_conj (hp : p ≠ 2) (h : FourRefl a b c d A)
    (_hJ : ∀ X ≤ A, ReflGen p X → SplitSupport X 3 →
      (∃ x ∈ X, ∃ y ∈ X, IsRefl p x ∧ IsRefl p y ∧ orderOf (x * y) = 4) → Nat.card X ≠ 336)
    (had : orderOf (a * d) = 2) (hac : orderOf (a * c) = 4) (hab : orderOf (a * b) = 3)
    (hbc : orderOf (b * c) = 3) (hbabc : orderOf (b * a * b * c) = 3)
    (hcd : orderOf (c * d) = 3) :
    ∃ g ∈ Subgroup.closure ({a, c} : Set (U ≃ₗ[ZMod p] U)),
      g * b * g⁻¹ * d = d * (g * b * g⁻¹) := by
  obtain ⟨hp3, hp7⟩ := ne_three_of_orderOf_babc hp h.isRefl_a h.isRefl_b h.isRefl_c hab hbc hac
    hbabc
  have hbdle := h.dmax.1 b h.mem_b d h.mem_d h.isRefl_b h.isRefl_d
  have : Finite U := Module.finite_of_finite (ZMod p)
  have : Finite (U ≃ₗ[ZMod p] U) :=
    Finite.of_injective (fun e : U ≃ₗ[ZMod p] U => (e : U → U)) DFunLike.coe_injective
  have hbdpos := orderOf_pos (b * d)
  obtain ⟨va, φa, hφa, rfl⟩ := (isRefl_iff hp a).mp h.isRefl_a
  obtain ⟨vb, φb, hφb, rfl⟩ := (isRefl_iff hp b).mp h.isRefl_b
  obtain ⟨vc, φc, hφc, rfl⟩ := (isRefl_iff hp c).mp h.isRefl_c
  obtain ⟨vd, φd, hφd, rfl⟩ := (isRefl_iff hp d).mp h.isRefl_d
  obtain ⟨had1, had2⟩ := apply_eq_zero_of_orderOf_eq_two hp hφa hφd had
  have h1 := apply_mul_apply_eq_one_of_orderOf_eq_three hp hφa hφb hab
  have h2 := apply_mul_apply_eq_one_of_orderOf_eq_three hp hφb hφc hbc
  have h3 := apply_mul_apply_eq_two_of_orderOf_eq_four hp hφa hφc hac
  have h5 := apply_mul_apply_eq_one_of_orderOf_eq_three hp hφc hφd hcd
  rw [reflection_conj_reflection hφb hφa] at hbabc
  have h4 := apply_mul_apply_eq_one_of_orderOf_eq_three hp _ hφc hbabc
  simp only [LinearMap.sub_apply, LinearMap.smul_apply, map_sub, map_smul, smul_eq_mul] at h4
  interval_cases hn : orderOf (Module.reflection hφb * Module.reflection hφd)
  · exact absurd hn (orderOf_mul_ne_one h (Subgroup.subset_closure (by simp)))
  · obtain ⟨z1, z2⟩ := apply_eq_zero_of_orderOf_eq_two hp hφb hφd hn
    refine ⟨1, Subgroup.one_mem _, ?_⟩
    simp only [one_mul, inv_one, mul_one]
    exact reflection_mul_comm_of_apply_eq_zero hφb hφd z1 z2
  · exact exists_commute_conj_bd_three hp hp3 hφa hφb hφc hφd h had1 had2 h1 h2 h3 h5 h4
      (apply_mul_apply_eq_one_of_orderOf_eq_three hp hφb hφd hn)
  · exact exists_commute_conj_bd_four hp hp3 hp7 hφa hφb hφc hφd h had1 had2 h1 h2 h3 h5 h4
      (apply_mul_apply_eq_two_of_orderOf_eq_four hp hφb hφd hn)

end FourRefl

end CFSG.StandardType.ZS

end
