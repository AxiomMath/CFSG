module

public import CFSG.LocalAnalysis.StandardType.ZS.DThreeConfig
public import CFSG.Fischer.Classification.Orthogonal2.Reflect
public import CFSG.Open.GLADefs
public import CFSG.ClassicalGroups.Orthogonal.ProjectiveSimple
public import CFSG.Fischer.Classification.Defs
public import CFSG.Fischer.Uniq.CompTau
public import CFSG.GroupTheory.LocalCores.Fitting

public section

namespace CFSG.StandardType.ZS

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

open CFSG.Fischer.Classification.Orth2
open CFSG.ClassicalGroups.Orthogonal

private def frameVec {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    (x : V) (f : Fin 3 → V) (bits : Fin 8 → Fin 3 → ZMod 2) (i : Fin 8) : V :=
  x + bits i 0 • f 0 + bits i 1 • f 1 + bits i 2 • f 2

private noncomputable def frameTransvection {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    {Q : QuadraticForm (ZMod 2) V} (v : V) : TauCeti.QuadraticMap.orthogonalGroup Q :=
  ⟨reflect Q v, reflect_mem_orthogonalGroup Q v⟩

private theorem add_self_eq_zero_of_zmodTwo {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    (x : V) :
    x + x = 0 := by
  have htwo : (2 : ZMod 2) = 0 := by decide
  rw [← two_smul (ZMod 2) x, htwo, zero_smul]

private theorem quad_smul_eq_zero {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    {Q : QuadraticForm (ZMod 2) V} {v : V} (h : Q v = 0) (a : ZMod 2) :
    Q (a • v) = 0 := by
  rw [QuadraticMap.map_smul, h, smul_zero]

private theorem polar_smul_smul_eq_zero {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    {Q : QuadraticForm (ZMod 2) V} {v w : V} (a b : ZMod 2)
    (h : QuadraticMap.polar Q v w = 0) : QuadraticMap.polar Q (a • v) (b • w) = 0 := by
  rw [QuadraticMap.polar_smul_left, QuadraticMap.polar_smul_right, h, smul_zero, smul_zero]

private theorem quad_add_add_eq_zero {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    {Q : QuadraticForm (ZMod 2) V} {a b c : V} (ha : Q a = 0) (hb : Q b = 0) (hc : Q c = 0)
    (hab : QuadraticMap.polar Q a b = 0) (hac : QuadraticMap.polar Q a c = 0)
    (hbc : QuadraticMap.polar Q b c = 0) : Q (a + b + c) = 0 := by
  simp only [QuadraticMap.map_add]
  rw [ha, hb, hc, hab, QuadraticMap.polar_add_left, hac, hbc]
  ring

private theorem quad_add_add_add_eq_one {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    {Q : QuadraticForm (ZMod 2) V} {x a b c : V} (hx : Q x = 1) (ha : Q a = 0) (hb : Q b = 0)
    (hc : Q c = 0) (hxa : QuadraticMap.polar Q x a = 0)
    (hxb : QuadraticMap.polar Q x b = 0) (hxc : QuadraticMap.polar Q x c = 0)
    (hab : QuadraticMap.polar Q a b = 0) (hac : QuadraticMap.polar Q a c = 0)
    (hbc : QuadraticMap.polar Q b c = 0) : Q (((x + a) + b) + c) = 1 := by
  simp only [QuadraticMap.map_add]
  rw [hx, ha, hb, hc, hxa, QuadraticMap.polar_add_left, hxb, hab,
    QuadraticMap.polar_add_left, QuadraticMap.polar_add_left, hxc, hac, hbc]
  ring

private theorem polar_eq_zero_of_quad_add {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    {Q : QuadraticForm (ZMod 2) V} {u v : V} (hu : Q u = 1) (hv : Q v = 1)
    (huv : Q (u + v) = 0) : QuadraticMap.polar Q u v = 0 := by
  rw [QuadraticMap.polar, hu, hv, huv]
  decide

private theorem frameVec_add_frameVec {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    {x : V} {f : Fin 3 → V} (bits : Fin 8 → Fin 3 → ZMod 2) (i j : Fin 8) :
    frameVec x f bits i + frameVec x f bits j =
      (bits i 0 + bits j 0) • f 0 + (bits i 1 + bits j 1) • f 1 +
        (bits i 2 + bits j 2) • f 2 := by
  have hxx : x + x = 0 := add_self_eq_zero_of_zmodTwo x
  have h1 : frameVec x f bits i + frameVec x f bits j =
      (x + x) + ((bits i 0 • f 0 + bits j 0 • f 0) +
        (bits i 1 • f 1 + bits j 1 • f 1) +
        (bits i 2 • f 2 + bits j 2 • f 2)) := by
    simp only [frameVec]
    abel
  rw [h1, hxx, zero_add, ← add_smul, ← add_smul, ← add_smul]

private theorem quad_frameVec {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    {Q : QuadraticForm (ZMod 2) V} {f : Fin 3 → V} {x : V}
    (bits : Fin 8 → Fin 3 → ZMod 2) (hf : ∀ k, Q (f k) = 0)
    (hfpol : ∀ k l, k ≠ l → QuadraticMap.polar Q (f k) (f l) = 0)
    (hxf : ∀ k, QuadraticMap.polar Q x (f k) = 0) (hx : Q x = 1) (i : Fin 8) :
    Q (frameVec x f bits i) = 1 := by
  have h0 : Q (bits i 0 • f 0) = 0 := quad_smul_eq_zero (hf 0) (bits i 0)
  have h1 : Q (bits i 1 • f 1) = 0 := quad_smul_eq_zero (hf 1) (bits i 1)
  have h2 : Q (bits i 2 • f 2) = 0 := quad_smul_eq_zero (hf 2) (bits i 2)
  have hx0 : QuadraticMap.polar Q x (bits i 0 • f 0) = 0 := by
    rw [QuadraticMap.polar_smul_right, hxf 0, smul_zero]
  have hx1 : QuadraticMap.polar Q x (bits i 1 • f 1) = 0 := by
    rw [QuadraticMap.polar_smul_right, hxf 1, smul_zero]
  have hx2 : QuadraticMap.polar Q x (bits i 2 • f 2) = 0 := by
    rw [QuadraticMap.polar_smul_right, hxf 2, smul_zero]
  have h01 : QuadraticMap.polar Q (bits i 0 • f 0) (bits i 1 • f 1) = 0 :=
    polar_smul_smul_eq_zero (bits i 0) (bits i 1) (hfpol 0 1 (by decide))
  have h02 : QuadraticMap.polar Q (bits i 0 • f 0) (bits i 2 • f 2) = 0 :=
    polar_smul_smul_eq_zero (bits i 0) (bits i 2) (hfpol 0 2 (by decide))
  have h12 : QuadraticMap.polar Q (bits i 1 • f 1) (bits i 2 • f 2) = 0 :=
    polar_smul_smul_eq_zero (bits i 1) (bits i 2) (hfpol 1 2 (by decide))
  simpa only [frameVec] using quad_add_add_add_eq_one hx h0 h1 h2 hx0 hx1 hx2 h01 h02 h12

private theorem quad_frameVec_add_frameVec {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    {Q : QuadraticForm (ZMod 2) V} {f : Fin 3 → V} {x : V}
    (bits : Fin 8 → Fin 3 → ZMod 2) (hf : ∀ k, Q (f k) = 0)
    (hfpol : ∀ k l, k ≠ l → QuadraticMap.polar Q (f k) (f l) = 0) (i j : Fin 8) :
    Q (frameVec x f bits i + frameVec x f bits j) = 0 := by
  rw [frameVec_add_frameVec]
  exact quad_add_add_eq_zero
    (quad_smul_eq_zero (hf 0) (bits i 0 + bits j 0))
    (quad_smul_eq_zero (hf 1) (bits i 1 + bits j 1))
    (quad_smul_eq_zero (hf 2) (bits i 2 + bits j 2))
    (polar_smul_smul_eq_zero _ _ (hfpol 0 1 (by decide)))
    (polar_smul_smul_eq_zero _ _ (hfpol 0 2 (by decide)))
    (polar_smul_smul_eq_zero _ _ (hfpol 1 2 (by decide)))

private theorem polar_frameVec_frameVec {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    {Q : QuadraticForm (ZMod 2) V} {f : Fin 3 → V} {x : V}
    (bits : Fin 8 → Fin 3 → ZMod 2) (hf : ∀ k, Q (f k) = 0)
    (hfpol : ∀ k l, k ≠ l → QuadraticMap.polar Q (f k) (f l) = 0)
    (hxf : ∀ k, QuadraticMap.polar Q x (f k) = 0) (hx : Q x = 1) (i j : Fin 8) :
    QuadraticMap.polar Q (frameVec x f bits i) (frameVec x f bits j) = 0 :=
  polar_eq_zero_of_quad_add (quad_frameVec bits hf hfpol hxf hx i)
    (quad_frameVec bits hf hfpol hxf hx j) (quad_frameVec_add_frameVec bits hf hfpol i j)

private theorem polar_frameVec_right {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    {Q : QuadraticForm (ZMod 2) V} {f : Fin 3 → V} {x y : V}
    (bits : Fin 8 → Fin 3 → ZMod 2) (hyf : ∀ k, QuadraticMap.polar Q y (f k) = 0)
    (hxy : QuadraticMap.polar Q x y = 1) (i : Fin 8) :
    QuadraticMap.polar Q y (frameVec x f bits i) = 1 := by
  simp only [frameVec]
  rw [QuadraticMap.polar_add_right, QuadraticMap.polar_add_right, QuadraticMap.polar_add_right,
    QuadraticMap.polar_smul_right, QuadraticMap.polar_smul_right, QuadraticMap.polar_smul_right,
    hyf 0, hyf 1, hyf 2, QuadraticMap.polar_comm Q y x, hxy]
  simp

private theorem sum_frameVec {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    {x : V} {f : Fin 3 → V} (bits : Fin 8 → Fin 3 → ZMod 2)
    (hbits : ∀ k, ∑ i : Fin 8, bits i k = 0) :
    ∑ i : Fin 8, frameVec x f bits i = 0 := by
  simp only [frameVec]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  rw [← Finset.sum_smul, ← Finset.sum_smul, ← Finset.sum_smul]
  rw [hbits 0, hbits 1, hbits 2]
  simp only [zero_smul, add_zero]
  have h8 : ((8 : ℕ) : ZMod 2) = 0 := by decide
  rw [← Nat.cast_smul_eq_nsmul (ZMod 2) 8 x, h8, zero_smul]

private theorem polar_list_sum_right {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    {Q : QuadraticForm (ZMod 2) V} (l : List V) (v : V)
    (h : ∀ u ∈ l, QuadraticMap.polar Q u v = 0) :
    QuadraticMap.polar Q l.sum v = 0 := by
  induction l with
  | nil => simp
  | cons u l ih =>
    rw [List.sum_cons, QuadraticMap.polar_add_left, h u (by simp),
      ih (fun x hx => h x (by simp [hx])), zero_add]

private theorem list_prod_frameTransvection_apply {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    {Q : QuadraticForm (ZMod 2) V} (l : List V) (y : V) (hQ : ∀ v ∈ l, Q v = 1)
    (horth : ∀ u ∈ l, ∀ v ∈ l, u ≠ v → QuadraticMap.polar Q u v = 0)
    (hy : ∀ v ∈ l, QuadraticMap.polar Q y v = 1) (hnd : l.Nodup) :
    (((l.map (fun v => reflect Q v)).prod : V ≃ₗ[ZMod 2] V)) y = y + l.sum := by
  induction l with
  | nil => simp
  | cons v l ih =>
    rw [List.map_cons, List.prod_cons, LinearEquiv.mul_apply,
      reflect_apply_of_map_eq_one (hQ v (by simp))]
    have hvnot : v ∉ l := List.Nodup.notMem hnd
    have hndtail : l.Nodup := List.Nodup.of_cons hnd
    rw [ih (fun u hu => hQ u (by simp [hu]))
      (fun u hu u' hu' hne => horth u (by simp [hu]) u' (by simp [hu']) hne)
      (fun u hu => hy u (by simp [hu])) hndtail]
    have hp : QuadraticMap.polar Q (y + l.sum) v = 1 := by
      rw [QuadraticMap.polar_add_left, hy v (by simp)]
      have hzero : QuadraticMap.polar Q l.sum v = 0 :=
        polar_list_sum_right l v (fun u hu => horth u (by simp [hu]) v (by simp)
          (by intro h; exact hvnot (h ▸ hu)))
      rw [hzero, add_zero]
    rw [hp, one_smul, List.sum_cons]
    abel

private theorem frameTransvection_injective {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    {Q : QuadraticForm (ZMod 2) V} {w : Fin 8 → V} {y : V} (hQw : ∀ i, Q (w i) = 1)
    (hpy : ∀ i, QuadraticMap.polar Q y (w i) = 1) (hdistinct : Function.Injective w) :
    Function.Injective (fun i => frameTransvection (Q := Q) (w i)) := by
  intro i j hij
  have hcoe : ((frameTransvection (Q := Q) (w i) : TauCeti.QuadraticMap.orthogonalGroup Q) :
      V ≃ₗ[ZMod 2] V) = ((frameTransvection (Q := Q) (w j) :
      TauCeti.QuadraticMap.orthogonalGroup Q) : V ≃ₗ[ZMod 2] V) :=
    congrArg (fun g : TauCeti.QuadraticMap.orthogonalGroup Q => (g : V ≃ₗ[ZMod 2] V)) hij
  have hyi : ((frameTransvection (Q := Q) (w i) : TauCeti.QuadraticMap.orthogonalGroup Q) :
      V ≃ₗ[ZMod 2] V) y = y + w i := by
    change reflect Q (w i) y = y + w i
    rw [reflect_apply_of_map_eq_one (hQw i), hpy i, one_smul]
  have hyj : ((frameTransvection (Q := Q) (w j) : TauCeti.QuadraticMap.orthogonalGroup Q) :
      V ≃ₗ[ZMod 2] V) y = y + w j := by
    change reflect Q (w j) y = y + w j
    rw [reflect_apply_of_map_eq_one (hQw j), hpy j, one_smul]
  have hsum' : y + w i = y + w j := by rw [← hyi, ← hyj, hcoe]
  exact hdistinct (add_left_cancel hsum')

private theorem frameTransvection_not_commute {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    {Q : QuadraticForm (ZMod 2) V} {w : Fin 8 → V} {y : V} (hQw : ∀ i, Q (w i) = 1)
    (hy : Q y = 1) (hpy : ∀ i, QuadraticMap.polar Q y (w i) = 1) :
    ∀ i, ¬ Commute (frameTransvection (Q := Q) y) (frameTransvection (Q := Q) (w i)) := by
  intro i hc
  have heq : frameTransvection (Q := Q) y * frameTransvection (Q := Q) (w i) =
      frameTransvection (Q := Q) (w i) * frameTransvection (Q := Q) y := (commute_iff_eq _ _).mp hc
  have h0 : QuadraticMap.polar Q y (w i) = 0 :=
    (mul_comm_iff_polar_eq_zero hy (hQw i) rfl rfl).mp heq
  rw [hpy i] at h0
  exact one_ne_zero h0

private theorem frameTransvection_commute_prod {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    {Q : QuadraticForm (ZMod 2) V} {w : Fin 8 → V} {y : V} (hQw : ∀ i, Q (w i) = 1)
    (horth : ∀ i j, i ≠ j → QuadraticMap.polar Q (w i) (w j) = 0)
    (hpy : ∀ i, QuadraticMap.polar Q y (w i) = 1) (hdistinct : Function.Injective w)
    (hsum : ∑ i : Fin 8, w i = 0) :
    Commute (frameTransvection (Q := Q) y)
      (List.ofFn (fun i => frameTransvection (Q := Q) (w i))).prod := by
  let d : Fin 8 → TauCeti.QuadraticMap.orthogonalGroup Q :=
    fun i => frameTransvection (Q := Q) (w i)
  let e : TauCeti.QuadraticMap.orthogonalGroup Q := frameTransvection (Q := Q) y
  let z : TauCeti.QuadraticMap.orthogonalGroup Q := (List.ofFn d).prod
  have hzcoe : ((z : V ≃ₗ[ZMod 2] V)) =
      ((List.ofFn w).map (fun v => reflect Q v)).prod := by
    dsimp only [z]
    rw [Subgroup.val_list_prod]
    congr 1
  have hzy : ((z : V ≃ₗ[ZMod 2] V)) y = y := by
    rw [hzcoe, list_prod_frameTransvection_apply (List.ofFn w) y]
    · rw [List.sum_ofFn, hsum, add_zero]
    · intro v hv
      have hv' : v ∈ Set.range w := (List.mem_ofFn' w v).mp hv
      rw [Set.mem_range] at hv'
      obtain ⟨i, rfl⟩ := hv'
      exact hQw i
    · intro u hu v hv huv
      have hu' : u ∈ Set.range w := (List.mem_ofFn' w u).mp hu
      have hv' : v ∈ Set.range w := (List.mem_ofFn' w v).mp hv
      rw [Set.mem_range] at hu' hv'
      obtain ⟨i, rfl⟩ := hu'
      obtain ⟨j, rfl⟩ := hv'
      exact horth i j (by intro h; exact huv (by rw [h]))
    · intro v hv
      have hv' : v ∈ Set.range w := (List.mem_ofFn' w v).mp hv
      rw [Set.mem_range] at hv'
      obtain ⟨i, rfl⟩ := hv'
      exact hpy i
    · exact List.nodup_ofFn_ofInjective hdistinct
  have hconj : ((z : V ≃ₗ[ZMod 2] V) * reflect Q y * ((z : V ≃ₗ[ZMod 2] V))⁻¹) =
      reflect Q y := by
    rw [reflect_conj (g := (z : V ≃ₗ[ZMod 2] V)) z.2 y, hzy]
  have hzgroup : z * e * z⁻¹ = e := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact hconj
  have hze' : z * e = e * z := by
    calc z * e = (z * e * z⁻¹) * z := by group
      _ = e * z := by rw [hzgroup]
  exact (commute_iff_eq e z).mpr hze'.symm

private theorem scalarFrame_of_frameVec {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    {Q : QuadraticForm (ZMod 2) V} (w : Fin 8 → V) (y : V) (hQw : ∀ i, Q (w i) = 1)
    (horth : ∀ i j, i ≠ j → QuadraticMap.polar Q (w i) (w j) = 0)
    (hpy : ∀ i, QuadraticMap.polar Q y (w i) = 1) (hy : Q y = 1)
    (hdistinct : Function.Injective w) (hsum : ∑ i : Fin 8, w i = 0) :
    ∃ (d : Fin 8 → TauCeti.QuadraticMap.orthogonalGroup Q)
      (e : TauCeti.QuadraticMap.orthogonalGroup Q),
      ScalarFrame (reflClass Q) d e ∧ ∀ i, ¬ Commute e (d i) := by
  let d : Fin 8 → TauCeti.QuadraticMap.orthogonalGroup Q :=
    fun i => frameTransvection (Q := Q) (w i)
  let e : TauCeti.QuadraticMap.orthogonalGroup Q := frameTransvection (Q := Q) y
  have hdmem : ∀ i, d i ∈ reflClass Q := fun i => ⟨w i, hQw i, rfl⟩
  have hd_inj : Function.Injective d := frameTransvection_injective hQw hpy hdistinct
  have hpair : Pairwise fun i j => Commute (d i) (d j) := by
    intro i j hij
    refine (commute_iff_eq (d i) (d j)).mpr ?_
    exact (mul_comm_iff_polar_eq_zero (hQw i) (hQw j) rfl rfl).mpr (horth i j hij)
  have hedge : e ∈ reflClass Q := ⟨y, hy, rfl⟩
  have hne := frameTransvection_not_commute hQw hy hpy
  have hne' : ∀ i, e ≠ d i := by
    intro i h
    exact hne i ((commute_iff_eq e (d i)).mpr (by rw [h]))
  have hcomm : Commute e (List.ofFn d).prod :=
    frameTransvection_commute_prod hQw horth hpy hdistinct hsum
  refine ⟨d, e, ?_, hne⟩
  exact ⟨hdmem, hd_inj, hpair, hedge, hne', hcomm⟩

private theorem quad_basis_symm {ι : Type*} [Fintype ι] [DecidableEq ι]
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    {b : Module.Basis ι (ZMod 2) V} {G : (ι → ZMod 2) → ZMod 2}
    {Q : QuadraticForm (ZMod 2) V} (hb : ∀ v, Q v = G (b.equivFun v)) (c : ι → ZMod 2) :
    Q (b.equivFun.symm c) = G c := by
  rw [hb, LinearEquiv.apply_symm_apply]

private theorem polar_basis_symm {ι : Type*} [Fintype ι] [DecidableEq ι]
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    {b : Module.Basis ι (ZMod 2) V} {G : (ι → ZMod 2) → ZMod 2}
    {Q : QuadraticForm (ZMod 2) V} (hb : ∀ v, Q v = G (b.equivFun v))
    (c c' : ι → ZMod 2) :
    QuadraticMap.polar Q (b.equivFun.symm c) (b.equivFun.symm c') =
      G (c + c') - G c - G c' := by
  rw [QuadraticMap.polar, ← LinearEquiv.map_add, hb, hb, hb,
    LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]

private def frameBits (i : Fin 8) (k : Fin 3) : ZMod 2 :=
  if i.val / 2 ^ k.val % 2 = 1 then 1 else 0

private theorem frameBits_injective : Function.Injective frameBits := by
  decide

private theorem sum_frameBits (k : Fin 3) : ∑ i : Fin 8, frameBits i k = 0 := by
  fin_cases k <;> decide

private theorem plus_frameCoord_apply {m : ℕ} (hm3 : 3 ≤ m)
    {cx : Fin m ⊕ Fin m → ZMod 2} {cf : Fin 3 → Fin m ⊕ Fin m → ZMod 2}
    {bits : Fin 8 → Fin 3 → ZMod 2}
    (hcx : ∀ k : Fin 3, cx (Sum.inr (Fin.castLE hm3 k)) = 0)
    (hcf : ∀ l k : Fin 3, cf l (Sum.inr (Fin.castLE hm3 k)) = if l = k then 1 else 0)
    (i : Fin 8) (k : Fin 3) :
    (cx + bits i 0 • cf 0 + bits i 1 • cf 1 + bits i 2 • cf 2)
      (Sum.inr (Fin.castLE hm3 k)) = bits i k := by
  simp only [Pi.add_apply, Pi.smul_apply, hcx k, hcf 0 k, hcf 1 k, hcf 2 k, smul_eq_mul]
  fin_cases k <;> simp

private theorem qPlus_one_pair {m : ℕ} (i : Fin m) (a b : ZMod 2) :
    CFSG.Open.GLAQPlus (ZMod 2) m
      (a • Pi.single (Sum.inl i) 1 + b • Pi.single (Sum.inr i) 1) = a * b := by
  let c : Fin m ⊕ Fin m → ZMod 2 := a • Pi.single (Sum.inl i) 1 + b • Pi.single (Sum.inr i) 1
  change CFSG.Assembly.LargeEvenQPlus (ZMod 2) m c = a * b
  rw [CFSG.Assembly.largeEvenQPlus_def]
  beta_reduce
  rw [Finset.sum_eq_add_sum_sdiff_singleton_of_mem (Finset.mem_univ i)]
  have hzero : ∑ x ∈ Finset.univ \ {i}, c (Sum.inl x) * c (Sum.inr x) = 0 := by
    apply Finset.sum_eq_zero
    intro x hx
    rw [Finset.mem_sdiff, Finset.mem_singleton] at hx
    simp [c, hx.2]
  rw [hzero, add_zero]
  simp [c]

private theorem qPlus_two_pairs {m : ℕ} (i j : Fin m) (hij : i ≠ j) (a b c d : ZMod 2) :
    CFSG.Open.GLAQPlus (ZMod 2) m
      (a • Pi.single (Sum.inl i) 1 + b • Pi.single (Sum.inr i) 1 +
       c • Pi.single (Sum.inl j) 1 + d • Pi.single (Sum.inr j) 1) = a * b + c * d := by
  let w : Fin m ⊕ Fin m → ZMod 2 :=
    a • Pi.single (Sum.inl i) 1 + b • Pi.single (Sum.inr i) 1 +
      c • Pi.single (Sum.inl j) 1 + d • Pi.single (Sum.inr j) 1
  change CFSG.Assembly.LargeEvenQPlus (ZMod 2) m w = a * b + c * d
  rw [CFSG.Assembly.largeEvenQPlus_def]
  beta_reduce
  rw [Finset.sum_eq_add_sum_sdiff_singleton_of_mem (Finset.mem_univ i)]
  rw [Finset.sum_eq_add_sum_sdiff_singleton_of_mem (by
    rw [Finset.mem_sdiff, Finset.mem_singleton]
    exact ⟨Finset.mem_univ j, Ne.symm hij⟩)]
  have hzero : ∑ x ∈ (Finset.univ \ {i}) \ {j}, w (Sum.inl x) * w (Sum.inr x) = 0 := by
    apply Finset.sum_eq_zero
    intro x hx
    rw [Finset.mem_sdiff] at hx
    obtain ⟨hx1, hxj⟩ := hx
    rw [Finset.mem_sdiff, Finset.mem_singleton] at hx1
    obtain ⟨-, hxi⟩ := hx1
    rw [Finset.mem_singleton] at hxj
    simp [w, hxi, hxj]
  rw [hzero, add_zero]
  simp [w, hij]

private theorem qPlus_three_pairs {m : ℕ} (i j k : Fin m) (hij : i ≠ j) (hik : i ≠ k)
    (hjk : j ≠ k) (a b c d e f : ZMod 2) :
    CFSG.Open.GLAQPlus (ZMod 2) m
      (a • Pi.single (Sum.inl i) 1 + b • Pi.single (Sum.inr i) 1 +
       c • Pi.single (Sum.inl j) 1 + d • Pi.single (Sum.inr j) 1 +
       e • Pi.single (Sum.inl k) 1 + f • Pi.single (Sum.inr k) 1) =
      a * b + c * d + e * f := by
  let w : Fin m ⊕ Fin m → ZMod 2 :=
    a • Pi.single (Sum.inl i) 1 + b • Pi.single (Sum.inr i) 1 +
      c • Pi.single (Sum.inl j) 1 + d • Pi.single (Sum.inr j) 1 +
      e • Pi.single (Sum.inl k) 1 + f • Pi.single (Sum.inr k) 1
  change CFSG.Assembly.LargeEvenQPlus (ZMod 2) m w = a * b + c * d + e * f
  rw [CFSG.Assembly.largeEvenQPlus_def]
  beta_reduce
  rw [Finset.sum_eq_add_sum_sdiff_singleton_of_mem (Finset.mem_univ i)]
  rw [Finset.sum_eq_add_sum_sdiff_singleton_of_mem (by
    rw [Finset.mem_sdiff, Finset.mem_singleton]
    exact ⟨Finset.mem_univ j, Ne.symm hij⟩)]
  rw [Finset.sum_eq_add_sum_sdiff_singleton_of_mem (by
    rw [Finset.mem_sdiff, Finset.mem_singleton, Finset.mem_sdiff, Finset.mem_singleton]
    exact ⟨⟨Finset.mem_univ k, Ne.symm hik⟩, Ne.symm hjk⟩)]
  have hzero : ∑ x ∈ ((Finset.univ \ {i}) \ {j}) \ {k},
      w (Sum.inl x) * w (Sum.inr x) = 0 := by
    apply Finset.sum_eq_zero
    intro x hx
    rw [Finset.mem_sdiff] at hx
    obtain ⟨hx1, hxk⟩ := hx
    rw [Finset.mem_sdiff] at hx1
    obtain ⟨hx2, hxj⟩ := hx1
    rw [Finset.mem_sdiff, Finset.mem_singleton] at hx2
    obtain ⟨-, hxi⟩ := hx2
    rw [Finset.mem_singleton] at hxj hxk
    simp [w, hxi, hxj, hxk]
  rw [hzero, add_zero]
  simp [w, hij, hik, hjk]
  ring

private theorem qPlus_singles_plusCx_plusCy {m : ℕ} (i3 i4 : Fin m) (h34 : i3 ≠ i4) :
    CFSG.Open.GLAQPlus (ZMod 2) m
      ((Pi.single (Sum.inl i3) (1 : ZMod 2) : Fin m ⊕ Fin m → ZMod 2) +
       Pi.single (Sum.inr i3) (1 : ZMod 2) +
       (Pi.single (Sum.inl i3) 1 + Pi.single (Sum.inl i4) (1 : ZMod 2) +
         Pi.single (Sum.inr i4) 1)) = 1 := by
  let s3 : Fin m ⊕ Fin m → ZMod 2 := Pi.single (Sum.inl i3) 1
  let t3 : Fin m ⊕ Fin m → ZMod 2 := Pi.single (Sum.inr i3) 1
  let s4 : Fin m ⊕ Fin m → ZMod 2 := Pi.single (Sum.inl i4) 1
  let t4 : Fin m ⊕ Fin m → ZMod 2 := Pi.single (Sum.inr i4) 1
  have htwo : (2 : ZMod 2) = 0 := by decide
  have h2 : s3 + s3 = 0 := by
    rw [← two_smul (ZMod 2) s3, htwo, zero_smul]
  have hgroup : (s3 + t3) + (s3 + s4 + t4) = (s3 + s3) + (t3 + s4 + t4) := by abel
  have hc : (s3 + t3) + (s3 + s4 + t4) =
      (0 : ZMod 2) • s3 + 1 • t3 + 1 • s4 + 1 • t4 := by
    simp only [zero_smul, one_smul]
    rw [hgroup, h2]
    abel
  change CFSG.Open.GLAQPlus (ZMod 2) m ((s3 + t3) + (s3 + s4 + t4)) = 1
  rw [hc]
  simpa [s3, t3, s4, t4] using
    qPlus_two_pairs (i := i3) (j := i4) h34 (a := 0) (b := 1) (c := 1) (d := 1)

private theorem qMinus_one_pair {m : ℕ} (i : Fin m) (a b u v : ZMod 2) :
    CFSG.Open.GLAQMinus m 1 1
      (a • Pi.single (Sum.inl (Sum.inl i)) 1 + b • Pi.single (Sum.inl (Sum.inr i)) 1 +
       u • Pi.single (Sum.inr 0) 1 + v • Pi.single (Sum.inr 1) 1) =
      a * b + u ^ 2 + 1 * u * v + 1 * v ^ 2 := by
  let w : CFSG.Open.GLAMinusIdx m → ZMod 2 :=
    a • Pi.single (Sum.inl (Sum.inl i)) 1 + b • Pi.single (Sum.inl (Sum.inr i)) 1 +
      u • Pi.single (Sum.inr 0) 1 + v • Pi.single (Sum.inr 1) 1
  change CFSG.Assembly.LargeEvenQMinus (K := ZMod 2) m 1 1 w =
    a * b + u ^ 2 + 1 * u * v + 1 * v ^ 2
  simp only [CFSG.Assembly.LargeEvenQMinus]
  rw [Finset.sum_eq_add_sum_sdiff_singleton_of_mem (Finset.mem_univ i)]
  have hzero : ∑ x ∈ Finset.univ \ {i}, w (Sum.inl (Sum.inl x)) * w (Sum.inl (Sum.inr x)) = 0 := by
    apply Finset.sum_eq_zero
    intro x hx
    rw [Finset.mem_sdiff, Finset.mem_singleton] at hx
    simp [w, hx.2]
  rw [hzero, add_zero]
  simp [w]

private theorem qMinus_two_pairs {m : ℕ} (i j : Fin m) (hij : i ≠ j)
    (a b c d u v : ZMod 2) :
    CFSG.Open.GLAQMinus m 1 1
      (a • Pi.single (Sum.inl (Sum.inl i)) 1 + b • Pi.single (Sum.inl (Sum.inr i)) 1 +
       c • Pi.single (Sum.inl (Sum.inl j)) 1 + d • Pi.single (Sum.inl (Sum.inr j)) 1 +
       u • Pi.single (Sum.inr 0) 1 + v • Pi.single (Sum.inr 1) 1) =
      a * b + c * d + u ^ 2 + 1 * u * v + 1 * v ^ 2 := by
  let w : CFSG.Open.GLAMinusIdx m → ZMod 2 :=
    a • Pi.single (Sum.inl (Sum.inl i)) 1 + b • Pi.single (Sum.inl (Sum.inr i)) 1 +
      c • Pi.single (Sum.inl (Sum.inl j)) 1 + d • Pi.single (Sum.inl (Sum.inr j)) 1 +
      u • Pi.single (Sum.inr 0) 1 + v • Pi.single (Sum.inr 1) 1
  change CFSG.Assembly.LargeEvenQMinus (K := ZMod 2) m 1 1 w =
    a * b + c * d + u ^ 2 + 1 * u * v + 1 * v ^ 2
  simp only [CFSG.Assembly.LargeEvenQMinus]
  rw [Finset.sum_eq_add_sum_sdiff_singleton_of_mem (Finset.mem_univ i)]
  rw [Finset.sum_eq_add_sum_sdiff_singleton_of_mem (by
    rw [Finset.mem_sdiff, Finset.mem_singleton]
    exact ⟨Finset.mem_univ j, Ne.symm hij⟩)]
  have hzero : ∑ x ∈ (Finset.univ \ {i}) \ {j},
      w (Sum.inl (Sum.inl x)) * w (Sum.inl (Sum.inr x)) = 0 := by
    apply Finset.sum_eq_zero
    intro x hx
    rw [Finset.mem_sdiff] at hx
    obtain ⟨hx1, hxj⟩ := hx
    rw [Finset.mem_sdiff, Finset.mem_singleton] at hx1
    obtain ⟨-, hxi⟩ := hx1
    rw [Finset.mem_singleton] at hxj
    simp [w, hxi, hxj]
  rw [hzero, add_zero]
  simp [w, hij]

private theorem minus_frameCoord_apply {m : ℕ} (hm3 : 3 ≤ m)
    {cx : CFSG.Open.GLAMinusIdx m → ZMod 2}
    {cf : Fin 3 → CFSG.Open.GLAMinusIdx m → ZMod 2}
    {bits : Fin 8 → Fin 3 → ZMod 2}
    (hcx : ∀ k : Fin 3, cx (Sum.inl (Sum.inr (Fin.castLE hm3 k))) = 0)
    (hcf : ∀ l k : Fin 3,
      cf l (Sum.inl (Sum.inr (Fin.castLE hm3 k))) = if l = k then 1 else 0)
    (i : Fin 8) (k : Fin 3) :
    (cx + bits i 0 • cf 0 + bits i 1 • cf 1 + bits i 2 • cf 2)
      (Sum.inl (Sum.inr (Fin.castLE hm3 k))) = bits i k := by
  simp only [Pi.add_apply, Pi.smul_apply, hcx k, hcf 0 k, hcf 1 k, hcf 2 k, smul_eq_mul]
  fin_cases k <;> simp

private def plusIdxThree {m : ℕ} (hm3 : 3 < m) : Fin m := ⟨3, hm3⟩

private def plusIdxFour {m : ℕ} (hm4 : 4 < m) : Fin m := ⟨4, hm4⟩

private theorem ne_castLE_of_val_eq_three {m : ℕ} (hm3 : 3 ≤ m) {i : Fin m} (hi : i.val = 3)
    (k : Fin 3) :
    i ≠ Fin.castLE hm3 k := by
  intro h
  have hv := congrArg Fin.val h
  rw [Fin.val_castLE, hi] at hv
  omega

private theorem ne_castLE_of_val_eq_four {m : ℕ} (hm3 : 3 ≤ m) {i : Fin m} (hi : i.val = 4)
    (k : Fin 3) :
    i ≠ Fin.castLE hm3 k := by
  intro h
  have hv := congrArg Fin.val h
  rw [Fin.val_castLE, hi] at hv
  omega

private def plusCf {m : ℕ} (hm3 : 3 ≤ m) (k : Fin 3) : Fin m ⊕ Fin m → ZMod 2 :=
  Pi.single (Sum.inr (Fin.castLE hm3 k)) 1

private def plusCx {m : ℕ} (i3 : Fin m) : Fin m ⊕ Fin m → ZMod 2 :=
  Pi.single (Sum.inl i3) 1 + Pi.single (Sum.inr i3) 1

private def plusCy {m : ℕ} (i3 i4 : Fin m) : Fin m ⊕ Fin m → ZMod 2 :=
  Pi.single (Sum.inl i3) 1 + Pi.single (Sum.inl i4) 1 + Pi.single (Sum.inr i4) 1

private theorem qPlus_plusCf {m : ℕ} (hm3 : 3 ≤ m) (k : Fin 3) :
    CFSG.Open.GLAQPlus (ZMod 2) m (plusCf hm3 k) = 0 := by
  simpa [plusCf] using qPlus_one_pair (i := Fin.castLE hm3 k) (a := 0) (b := 1)

private theorem qPlus_plusCf_add_plusCf {m : ℕ} (hm3 : 3 ≤ m) {k l : Fin 3} (hkl : k ≠ l) :
    CFSG.Open.GLAQPlus (ZMod 2) m (plusCf hm3 k + plusCf hm3 l) = 0 := by
  have hkl' : Fin.castLE hm3 k ≠ Fin.castLE hm3 l := fun h =>
    hkl (Fin.castLE_injective hm3 h)
  simpa [plusCf] using qPlus_two_pairs (i := Fin.castLE hm3 k) (j := Fin.castLE hm3 l) hkl'
    (a := 0) (b := 1) (c := 0) (d := 1)

private theorem qPlus_plusCx {m : ℕ} (i3 : Fin m) :
    CFSG.Open.GLAQPlus (ZMod 2) m (plusCx i3) = 1 := by
  simpa [plusCx] using qPlus_one_pair (i := i3) (a := 1) (b := 1)

private theorem qPlus_plusCy {m : ℕ} (i3 i4 : Fin m) (h34 : i3 ≠ i4) :
    CFSG.Open.GLAQPlus (ZMod 2) m (plusCy i3 i4) = 1 := by
  simpa [plusCy] using qPlus_two_pairs (i := i3) (j := i4) h34 (a := 1) (b := 0)
    (c := 1) (d := 1)

private theorem qPlus_plusCx_add_plusCf {m : ℕ} (hm3 : 3 ≤ m) (i3 : Fin m) (k : Fin 3)
    (hik : i3 ≠ Fin.castLE hm3 k) :
    CFSG.Open.GLAQPlus (ZMod 2) m (plusCx i3 + plusCf hm3 k) = 1 := by
  simpa [plusCx, plusCf] using qPlus_two_pairs (i := i3) (j := Fin.castLE hm3 k) hik
    (a := 1) (b := 1) (c := 0) (d := 1)

private theorem qPlus_plusCy_add_plusCf {m : ℕ} (hm3 : 3 ≤ m) (i3 i4 : Fin m) (h34 : i3 ≠ i4)
    (k : Fin 3) (hik : i3 ≠ Fin.castLE hm3 k) (hjk : i4 ≠ Fin.castLE hm3 k) :
    CFSG.Open.GLAQPlus (ZMod 2) m (plusCy i3 i4 + plusCf hm3 k) = 1 := by
  have hcy : plusCy i3 i4 + plusCf hm3 k =
      (1 : ZMod 2) • Pi.single (Sum.inl i3) (1 : ZMod 2) +
      (0 : ZMod 2) • Pi.single (Sum.inr i3) 1 +
      (1 : ZMod 2) • Pi.single (Sum.inl i4) 1 +
      (1 : ZMod 2) • Pi.single (Sum.inr i4) 1 +
      (0 : ZMod 2) • Pi.single (Sum.inl (Fin.castLE hm3 k)) 1 +
      (1 : ZMod 2) • Pi.single (Sum.inr (Fin.castLE hm3 k)) 1 := by
    simp [plusCy, plusCf]
  rw [hcy]
  simpa using qPlus_three_pairs (i := i3) (j := i4) (k := Fin.castLE hm3 k) h34 hik hjk
    (a := 1) (b := 0) (c := 1) (d := 1) (e := 0) (f := 1)

private theorem qPlus_plusCx_add_plusCy {m : ℕ} (i3 i4 : Fin m) (h34 : i3 ≠ i4) :
    CFSG.Open.GLAQPlus (ZMod 2) m (plusCx i3 + plusCy i3 i4) = 1 := by
  simpa [plusCx, plusCy] using qPlus_singles_plusCx_plusCy i3 i4 h34

private theorem plus_frame_forms {m : ℕ} (hm3 : 3 ≤ m) (i3 i4 : Fin m) (h34 : i3 ≠ i4)
    (hi3 : i3.val = 3) (hi4 : i4.val = 4)
    {Q : QuadraticForm (ZMod 2) (Fin (2 * m) → ZMod 2)}
    (b : Module.Basis (Fin m ⊕ Fin m) (ZMod 2) (Fin (2 * m) → ZMod 2))
    (hb : ∀ v, Q v = CFSG.Open.GLAQPlus (ZMod 2) m (b.equivFun v)) :
    (∀ k, Q (b.equivFun.symm (plusCf hm3 k)) = 0) ∧
    (∀ k l, k ≠ l → QuadraticMap.polar Q (b.equivFun.symm (plusCf hm3 k))
      (b.equivFun.symm (plusCf hm3 l)) = 0) ∧
    (∀ k, QuadraticMap.polar Q (b.equivFun.symm (plusCx i3))
      (b.equivFun.symm (plusCf hm3 k)) = 0) ∧
    (∀ k, QuadraticMap.polar Q (b.equivFun.symm (plusCy i3 i4))
      (b.equivFun.symm (plusCf hm3 k)) = 0) ∧
    Q (b.equivFun.symm (plusCx i3)) = 1 ∧
    Q (b.equivFun.symm (plusCy i3 i4)) = 1 ∧
    QuadraticMap.polar Q (b.equivFun.symm (plusCx i3))
      (b.equivFun.symm (plusCy i3 i4)) = 1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro k
    rw [quad_basis_symm hb (plusCf hm3 k), qPlus_plusCf hm3 k]
  · intro k l hkl
    rw [polar_basis_symm hb, qPlus_plusCf_add_plusCf hm3 hkl, qPlus_plusCf hm3 k,
      qPlus_plusCf hm3 l]
    ring
  · intro k
    rw [polar_basis_symm hb, qPlus_plusCx_add_plusCf hm3 i3 k (ne_castLE_of_val_eq_three hm3 hi3 k),
      qPlus_plusCx i3, qPlus_plusCf hm3 k]
    ring
  · intro k
    rw [polar_basis_symm hb,
      qPlus_plusCy_add_plusCf hm3 i3 i4 h34 k (ne_castLE_of_val_eq_three hm3 hi3 k)
        (ne_castLE_of_val_eq_four hm3 hi4 k), qPlus_plusCy i3 i4 h34, qPlus_plusCf hm3 k]
    ring
  · rw [quad_basis_symm hb, qPlus_plusCx i3]
  · rw [quad_basis_symm hb, qPlus_plusCy i3 i4 h34]
  · rw [polar_basis_symm hb, qPlus_plusCx_add_plusCy i3 i4 h34, qPlus_plusCx i3,
      qPlus_plusCy i3 i4 h34]
    decide

private theorem exists_scalarFrame_plus_aux {m : ℕ} (hm : 5 ≤ m)
    {Q : QuadraticForm (ZMod 2) (Fin (2 * m) → ZMod 2)}
    (b : Module.Basis (Fin m ⊕ Fin m) (ZMod 2) (Fin (2 * m) → ZMod 2))
    (hb : ∀ v, Q v = CFSG.Open.GLAQPlus (ZMod 2) m (b.equivFun v)) :
    ∃ (d : Fin 8 → TauCeti.QuadraticMap.orthogonalGroup Q)
      (e : TauCeti.QuadraticMap.orthogonalGroup Q),
      ScalarFrame (reflClass Q) d e ∧ ∀ i, ¬ Commute e (d i) := by
  have hm3 : 3 ≤ m := by omega
  let i3 : Fin m := plusIdxThree (by omega)
  let i4 : Fin m := plusIdxFour (by omega)
  have h34 : i3 ≠ i4 := by
    intro h
    simpa [i3, i4, plusIdxThree, plusIdxFour] using congrArg Fin.val h
  obtain ⟨hQf, hfpol, hxf, hyf, hQx, hQy, hxy⟩ :=
    plus_frame_forms hm3 i3 i4 h34 rfl rfl b hb
  let cf : Fin 3 → Fin m ⊕ Fin m → ZMod 2 := plusCf hm3
  let cx : Fin m ⊕ Fin m → ZMod 2 := plusCx i3
  let cy : Fin m ⊕ Fin m → ZMod 2 := plusCy i3 i4
  let f : Fin 3 → Fin (2 * m) → ZMod 2 := fun k => b.equivFun.symm (cf k)
  let x : Fin (2 * m) → ZMod 2 := b.equivFun.symm cx
  let y : Fin (2 * m) → ZMod 2 := b.equivFun.symm cy
  let bits : Fin 8 → Fin 3 → ZMod 2 := frameBits
  let w : Fin 8 → Fin (2 * m) → ZMod 2 := fun i =>
    x + bits i 0 • f 0 + bits i 1 • f 1 + bits i 2 • f 2
  have hQw : ∀ i, Q (w i) = 1 := fun i => by
    dsimp only [w]; exact quad_frameVec bits hQf hfpol hxf hQx i
  have horth : ∀ i j, i ≠ j → QuadraticMap.polar Q (w i) (w j) = 0 := fun i j _ => by
    dsimp only [w]; exact polar_frameVec_frameVec bits hQf hfpol hxf hQx i j
  have hpy : ∀ i, QuadraticMap.polar Q y (w i) = 1 := fun i => by
    dsimp only [w, y]; exact polar_frameVec_right bits hyf hxy i
  have hwcoord : ∀ i, b.equivFun (w i) =
      cx + bits i 0 • cf 0 + bits i 1 • cf 1 + bits i 2 • cf 2 := by
    intro i; dsimp only [w, x, f]; simp only [map_add, map_smul, LinearEquiv.apply_symm_apply]
  have hcx0 : ∀ k : Fin 3, cx (Sum.inr (Fin.castLE hm3 k)) = 0 := by
    intro k
    have hk : Fin.castLE hm3 k ≠ i3 := Ne.symm (ne_castLE_of_val_eq_three hm3 rfl k)
    simp [cx, plusCx, hk]
  have hcf0 : ∀ l k : Fin 3, cf l (Sum.inr (Fin.castLE hm3 k)) = if l = k then 1 else 0 := by
    intro l k
    by_cases h : l = k
    · subst h; simp [cf, plusCf]
    · rw [if_neg h]
      have hne : Fin.castLE hm3 l ≠ Fin.castLE hm3 k := fun heq =>
        h (Fin.castLE_injective hm3 heq)
      simp [cf, plusCf, hne]
  have hdistinct : Function.Injective w := by
    intro i j hij
    have hcoord : b.equivFun (w i) = b.equivFun (w j) := by rw [hij]
    rw [hwcoord i, hwcoord j] at hcoord
    apply frameBits_injective
    funext k
    have hk := congrFun hcoord (Sum.inr (Fin.castLE hm3 k))
    rw [plus_frameCoord_apply hm3 hcx0 hcf0 i k,
      plus_frameCoord_apply hm3 hcx0 hcf0 j k] at hk
    exact hk
  exact scalarFrame_of_frameVec w y hQw horth hpy hQy hdistinct
    (by dsimp only [w]; exact sum_frameVec bits sum_frameBits)

theorem exists_scalarFrame_reflClass_plus {m : ℕ} (hm : 5 ≤ m)
    {Q : QuadraticForm (ZMod 2) (Fin (2 * m) → ZMod 2)}
    (b : Module.Basis (Fin m ⊕ Fin m) (ZMod 2) (Fin (2 * m) → ZMod 2))
    (hb : ∀ v, Q v = CFSG.Open.GLAQPlus (ZMod 2) m (b.equivFun v)) :
    ∃ (d : Fin 8 → TauCeti.QuadraticMap.orthogonalGroup Q)
      (e : TauCeti.QuadraticMap.orthogonalGroup Q),
      ScalarFrame (reflClass Q) d e ∧ ∀ i, ¬ Commute e (d i) :=
  exists_scalarFrame_plus_aux hm b hb

private def minusIdxZero {m : ℕ} (hm : 0 < m) : Fin m := ⟨0, hm⟩

private def minusCf {m : ℕ} (hm3 : 3 ≤ m) (k : Fin 3) :
    CFSG.Open.GLAMinusIdx m → ZMod 2 :=
  Pi.single (Sum.inl (Sum.inr (Fin.castLE hm3 k))) 1

private def minusCx {m : ℕ} : CFSG.Open.GLAMinusIdx m → ZMod 2 :=
  Pi.single (Sum.inr 0) 1

private def minusCy {m : ℕ} : CFSG.Open.GLAMinusIdx m → ZMod 2 :=
  Pi.single (Sum.inr 1) 1

private theorem qMinus_minusCf {m : ℕ} (hm3 : 3 ≤ m) (k : Fin 3) :
    CFSG.Open.GLAQMinus (m := m) 1 1 (minusCf hm3 k) = 0 := by
  simpa [minusCf] using qMinus_one_pair (m := m) (i := Fin.castLE hm3 k)
    (a := 0) (b := 1) (u := 0) (v := 0)

private theorem qMinus_minusCf_add_minusCf {m : ℕ} (hm3 : 3 ≤ m) {k l : Fin 3} (hkl : k ≠ l) :
    CFSG.Open.GLAQMinus (m := m) 1 1 (minusCf hm3 k + minusCf hm3 l) = 0 := by
  have hkl' : Fin.castLE hm3 k ≠ Fin.castLE hm3 l := fun h =>
    hkl (Fin.castLE_injective hm3 h)
  simpa [minusCf] using qMinus_two_pairs (m := m) (i := Fin.castLE hm3 k)
    (j := Fin.castLE hm3 l) hkl' (a := 0) (b := 1) (c := 0) (d := 1) (u := 0) (v := 0)

private theorem qMinus_minusCx {m : ℕ} (hm3 : 3 ≤ m) :
    CFSG.Open.GLAQMinus (m := m) 1 1 (minusCx (m := m)) = 1 := by
  simpa [minusCx] using qMinus_one_pair (m := m) (i := minusIdxZero (by omega))
    (a := 0) (b := 0) (u := 1) (v := 0)

private theorem qMinus_minusCy {m : ℕ} (hm3 : 3 ≤ m) :
    CFSG.Open.GLAQMinus (m := m) 1 1 (minusCy (m := m)) = 1 := by
  simpa [minusCy] using qMinus_one_pair (m := m) (i := minusIdxZero (by omega))
    (a := 0) (b := 0) (u := 0) (v := 1)

private theorem qMinus_minusCx_add_minusCy {m : ℕ} (hm3 : 3 ≤ m) :
    CFSG.Open.GLAQMinus (m := m) 1 1 (minusCx (m := m) + minusCy (m := m)) = 1 := by
  have h := qMinus_one_pair (m := m) (i := minusIdxZero (by omega))
    (a := 0) (b := 0) (u := 1) (v := 1)
  have hc : minusCx (m := m) + minusCy (m := m) =
      (0 : ZMod 2) • Pi.single (Sum.inl (Sum.inl (minusIdxZero (by omega)))) (1 : ZMod 2) +
      (0 : ZMod 2) • Pi.single (Sum.inl (Sum.inr (minusIdxZero (by omega)))) 1 +
      (1 : ZMod 2) • Pi.single (Sum.inr 0) 1 + (1 : ZMod 2) • Pi.single (Sum.inr 1) 1 := by
    simp [minusCx, minusCy]
  rw [hc, h]
  decide

private theorem qMinus_minusCx_add_minusCf {m : ℕ} (hm3 : 3 ≤ m) (k : Fin 3) :
    CFSG.Open.GLAQMinus (m := m) 1 1 (minusCx (m := m) + minusCf hm3 k) = 1 := by
  have h := qMinus_one_pair (m := m) (i := Fin.castLE hm3 k)
    (a := 0) (b := 1) (u := 1) (v := 0)
  have hc : minusCx (m := m) + minusCf hm3 k =
      (0 : ZMod 2) • Pi.single (Sum.inl (Sum.inl (Fin.castLE hm3 k))) (1 : ZMod 2) +
      (1 : ZMod 2) • Pi.single (Sum.inl (Sum.inr (Fin.castLE hm3 k))) 1 +
      (1 : ZMod 2) • Pi.single (Sum.inr 0) 1 + (0 : ZMod 2) • Pi.single (Sum.inr 1) 1 := by
    simp [minusCx, minusCf]
    abel
  rw [hc, h]
  decide

private theorem qMinus_minusCy_add_minusCf {m : ℕ} (hm3 : 3 ≤ m) (k : Fin 3) :
    CFSG.Open.GLAQMinus (m := m) 1 1 (minusCy (m := m) + minusCf hm3 k) = 1 := by
  have h := qMinus_one_pair (m := m) (i := Fin.castLE hm3 k)
    (a := 0) (b := 1) (u := 0) (v := 1)
  have hc : minusCy (m := m) + minusCf hm3 k =
      (0 : ZMod 2) • Pi.single (Sum.inl (Sum.inl (Fin.castLE hm3 k))) (1 : ZMod 2) +
      (1 : ZMod 2) • Pi.single (Sum.inl (Sum.inr (Fin.castLE hm3 k))) 1 +
      (0 : ZMod 2) • Pi.single (Sum.inr 0) 1 + (1 : ZMod 2) • Pi.single (Sum.inr 1) 1 := by
    simp [minusCy, minusCf]
    abel
  rw [hc, h]
  decide

private theorem minus_frame_forms {m : ℕ} (hm : 4 ≤ m)
    {Q : QuadraticForm (ZMod 2) (Fin (2 * m) → ZMod 2)}
    (b : Module.Basis (CFSG.Open.GLAMinusIdx (m - 1)) (ZMod 2) (Fin (2 * m) → ZMod 2))
    (hb : ∀ v, Q v = CFSG.Open.GLAQMinus (m - 1) (1 : ZMod 2) 1 (b.equivFun v)) :
    (∀ k, Q (b.equivFun.symm (minusCf (by omega : 3 ≤ m - 1) k)) = 0) ∧
    (∀ k l, k ≠ l → QuadraticMap.polar Q
      (b.equivFun.symm (minusCf (by omega : 3 ≤ m - 1) k))
      (b.equivFun.symm (minusCf (by omega : 3 ≤ m - 1) l)) = 0) ∧
    (∀ k, QuadraticMap.polar Q (b.equivFun.symm (minusCx (m := m - 1)))
      (b.equivFun.symm (minusCf (by omega : 3 ≤ m - 1) k)) = 0) ∧
    (∀ k, QuadraticMap.polar Q (b.equivFun.symm (minusCy (m := m - 1)))
      (b.equivFun.symm (minusCf (by omega : 3 ≤ m - 1) k)) = 0) ∧
    Q (b.equivFun.symm (minusCx (m := m - 1))) = 1 ∧
    Q (b.equivFun.symm (minusCy (m := m - 1))) = 1 ∧
    QuadraticMap.polar Q (b.equivFun.symm (minusCx (m := m - 1)))
      (b.equivFun.symm (minusCy (m := m - 1))) = 1 := by
  have hm3 : 3 ≤ m - 1 := by omega
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro k
    rw [quad_basis_symm hb (minusCf hm3 k), qMinus_minusCf hm3 k]
  · intro k l hkl
    rw [polar_basis_symm hb, qMinus_minusCf_add_minusCf hm3 hkl, qMinus_minusCf hm3 k,
      qMinus_minusCf hm3 l]
    ring
  · intro k
    rw [polar_basis_symm hb, qMinus_minusCx_add_minusCf hm3 k, qMinus_minusCx hm3,
      qMinus_minusCf hm3 k]
    ring
  · intro k
    rw [polar_basis_symm hb, qMinus_minusCy_add_minusCf hm3 k, qMinus_minusCy hm3,
      qMinus_minusCf hm3 k]
    ring
  · rw [quad_basis_symm hb, qMinus_minusCx hm3]
  · rw [quad_basis_symm hb, qMinus_minusCy hm3]
  · rw [polar_basis_symm hb, qMinus_minusCx_add_minusCy hm3, qMinus_minusCx hm3,
      qMinus_minusCy hm3]
    decide

private theorem exists_scalarFrame_minus_aux {m : ℕ} (hm : 4 ≤ m)
    {Q : QuadraticForm (ZMod 2) (Fin (2 * m) → ZMod 2)}
    (b : Module.Basis (CFSG.Open.GLAMinusIdx (m - 1)) (ZMod 2) (Fin (2 * m) → ZMod 2))
    (hb : ∀ v, Q v = CFSG.Open.GLAQMinus (m - 1) (1 : ZMod 2) 1 (b.equivFun v)) :
    ∃ (d : Fin 8 → TauCeti.QuadraticMap.orthogonalGroup Q)
      (e : TauCeti.QuadraticMap.orthogonalGroup Q),
      ScalarFrame (reflClass Q) d e ∧ ∀ i, ¬ Commute e (d i) := by
  have hm3 : 3 ≤ m - 1 := by omega
  let cf : Fin 3 → CFSG.Open.GLAMinusIdx (m - 1) → ZMod 2 := minusCf hm3
  let cx : CFSG.Open.GLAMinusIdx (m - 1) → ZMod 2 := minusCx
  let cy : CFSG.Open.GLAMinusIdx (m - 1) → ZMod 2 := minusCy
  let f : Fin 3 → Fin (2 * m) → ZMod 2 := fun k => b.equivFun.symm (cf k)
  let x : Fin (2 * m) → ZMod 2 := b.equivFun.symm cx
  let y : Fin (2 * m) → ZMod 2 := b.equivFun.symm cy
  let bits : Fin 8 → Fin 3 → ZMod 2 := frameBits
  let w : Fin 8 → Fin (2 * m) → ZMod 2 := fun i =>
    x + bits i 0 • f 0 + bits i 1 • f 1 + bits i 2 • f 2
  obtain ⟨hQf, hfpol, hxf, hyf, hQx, hQy, hxy⟩ := minus_frame_forms hm b hb
  have hQw : ∀ i, Q (w i) = 1 := fun i => by
    dsimp only [w]; exact quad_frameVec bits hQf hfpol hxf hQx i
  have horth : ∀ i j, i ≠ j → QuadraticMap.polar Q (w i) (w j) = 0 := fun i j _ => by
    dsimp only [w]; exact polar_frameVec_frameVec bits hQf hfpol hxf hQx i j
  have hpy : ∀ i, QuadraticMap.polar Q y (w i) = 1 := fun i => by
    dsimp only [w, y]; exact polar_frameVec_right bits hyf hxy i
  have hwcoord : ∀ i, b.equivFun (w i) =
      cx + bits i 0 • cf 0 + bits i 1 • cf 1 + bits i 2 • cf 2 := by
    intro i; dsimp only [w, x, f]; simp only [map_add, map_smul, LinearEquiv.apply_symm_apply]
  have hcx0 : ∀ k : Fin 3, cx (Sum.inl (Sum.inr (Fin.castLE hm3 k))) = 0 := by
    intro k; simp [cx, minusCx]
  have hcf0 : ∀ l k : Fin 3,
      cf l (Sum.inl (Sum.inr (Fin.castLE hm3 k))) = if l = k then 1 else 0 := by
    intro l k
    by_cases h : l = k
    · subst h; simp [cf, minusCf]
    · rw [if_neg h]
      have hne : (Sum.inl (Sum.inr (Fin.castLE hm3 l)) : CFSG.Open.GLAMinusIdx (m - 1)) ≠
          (Sum.inl (Sum.inr (Fin.castLE hm3 k)) : CFSG.Open.GLAMinusIdx (m - 1)) := by
        intro heq
        have hcast : Fin.castLE hm3 l = Fin.castLE hm3 k := by simpa using heq
        exact h (Fin.castLE_injective hm3 hcast)
      simp [cf, minusCf, hne]
  have hdistinct : Function.Injective w := by
    intro i j hij
    have hcoord : b.equivFun (w i) = b.equivFun (w j) := by rw [hij]
    rw [hwcoord i, hwcoord j] at hcoord
    apply frameBits_injective
    funext k
    have hk := congrFun hcoord (Sum.inl (Sum.inr (Fin.castLE hm3 k)))
    rw [minus_frameCoord_apply hm3 hcx0 hcf0 i k,
      minus_frameCoord_apply hm3 hcx0 hcf0 j k] at hk
    exact hk
  exact scalarFrame_of_frameVec w y hQw horth hpy hQy hdistinct
    (by dsimp only [w]; exact sum_frameVec bits sum_frameBits)

theorem exists_scalarFrame_reflClass_minus {m : ℕ} (hm : 4 ≤ m)
    {Q : QuadraticForm (ZMod 2) (Fin (2 * m) → ZMod 2)}
    (b : Module.Basis (CFSG.Open.GLAMinusIdx (m - 1)) (ZMod 2) (Fin (2 * m) → ZMod 2))
    (hb : ∀ v, Q v = CFSG.Open.GLAQMinus (m - 1) (1 : ZMod 2) 1 (b.equivFun v)) :
    ∃ (d : Fin 8 → TauCeti.QuadraticMap.orthogonalGroup Q)
      (e : TauCeti.QuadraticMap.orthogonalGroup Q),
      ScalarFrame (reflClass Q) d e ∧ ∀ i, ¬ Commute e (d i) :=
  exists_scalarFrame_minus_aux hm b hb

end CFSG.StandardType.ZS
