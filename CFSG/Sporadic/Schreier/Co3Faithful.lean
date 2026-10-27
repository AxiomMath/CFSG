module

public import CFSG.Sporadic.Schreier.Co3FormsSpec
public import CFSG.Sporadic.Schreier.Co3FaithfulCheck
public import CFSG.Certificates.InvariantFunctionAction
public import CFSG.Blueprint.MatrixSeedIdentification
public import CFSG.Sporadic.Schreier.Co3Restrict
import all CFSG.Blueprint.NativeSporadic

public noncomputable section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Sporadic.Schreier.Co3

open CFSG.Sporadic.Schreier.Co3.Native CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native
  CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates Matrix

theorem co3FormWord_lt
    {r : ℕ} (hr : r < 276) : co3FormWord r < 2 ^ 253 :=
  co3Layout_check.2.2.2.2.2.2.2 r hr

theorem co3Form_injective
    {r r' : ℕ} (hr : r < 276) (hr' : r' < 276)
    (h : co3Form r = co3Form r') : r = r' := by
  have hw := co3Quad_injective (co3FormWord_lt hr) (co3FormWord_lt hr') h
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · exact co3Faithful_check.1 r' hr' r hlt hw.symm
  · exact co3Faithful_check.1 r hr r' hlt hw

@[expose] def co3DiffCoef (r : ℕ) (i : Fin 22) : ZMod 2 :=
  co3Coef (co3FormWord r) i i - co3Coef (co3FormWord 0) i i

@[expose] def co3DiffFun (r : ℕ) : Module.Dual (ZMod 2) Co3V :=
  ∑ i : Fin 22, co3DiffCoef r i • LinearMap.proj i

theorem co3DiffFun_apply (r : ℕ) (v : Co3V) :
    co3DiffFun r v = ∑ i : Fin 22, co3DiffCoef r i * v i := by
  simp [co3DiffFun, LinearMap.sum_apply]

theorem co3Form_sub {r : ℕ} (hr : r < 276) (v : Co3V) :
    co3DiffFun r v = co3Form r v - co3Form 0 v := by
  rw [co3DiffFun_apply, co3Form, co3Form, co3Quad_sub_of_offDiagOK (co3Faithful_check.2.1 r hr)]
  rfl

@[expose] def co3DiffIdxAt (k : Fin 22) : ℕ := co3DiffIdx.getD k 0

theorem co3DiffIdxAt_lt (k : Fin 22) : co3DiffIdxAt k < 276 := by
  revert k
  decide

theorem getD_map_toArray (l : List ℕ) (f : ℕ → ℕ) {j : ℕ} (hj : j < l.length) :
    (l.map f).toArray[j]?.getD 0 = f (l.getD j 0) := by
  rw [List.getD_eq_getElem _ _ hj, List.getElem?_toArray, List.getElem?_map,
    List.getElem?_eq_getElem hj, Option.map_some, Option.getD_some]

theorem diagVec_xor_testBit (w w' : ℕ) (i : Fin 22) :
    (diagVec w ^^^ diagVec w').testBit i =
      (w.testBit (pairIdx22 i i) ^^ w'.testBit (pairIdx22 i i)) := by
  rw [Nat.testBit_xor, diagVec, diagVec, ofBits_testBit, ofBits_testBit]
  simp only [i.2, decide_true, Bool.true_and]

theorem bool_xor_cast_sub (a b : Bool) :
    (if (a ^^ b) = true then (1 : ZMod 2) else 0) =
      (if a = true then 1 else 0) - (if b = true then 1 else 0) := by
  cases a <;> cases b <;> decide

theorem co3DiffIdx_length : co3DiffIdx.length = 22 := rfl

theorem co3DiffRows_get (j : Fin 22) (i : Fin 22) :
    rowsMatrix 22 co3DiffRows j i = co3DiffCoef (co3DiffIdxAt j) i := by
  have hj : (j : ℕ) < co3DiffIdx.length := by rw [co3DiffIdx_length]; exact j.2
  rw [rowsMatrix_apply', co3DiffRows, getD_map_toArray _ _ hj, diagVec_xor_testBit,
    bool_xor_cast_sub]
  rfl

theorem co3Span_mul :
    rowsMatrix 22 co3SpanCoeffs * rowsMatrix 22 co3DiffRows = 1 := by
  rw [← rowsMatrix_mulRows, co3Faithful_check.2.2.2.2, rowsMatrix_idRows]

theorem proj_mem_span (k : Fin 22) :
    (LinearMap.proj k : Module.Dual (ZMod 2) Co3V) ∈
      Submodule.span (ZMod 2) (Set.range fun j : Fin 22 => co3DiffFun (co3DiffIdxAt j)) := by
  have e : (LinearMap.proj k : Module.Dual (ZMod 2) Co3V) =
      ∑ j : Fin 22, rowsMatrix 22 co3SpanCoeffs k j • co3DiffFun (co3DiffIdxAt j) := by
    refine LinearMap.ext fun v => ?_
    rw [LinearMap.sum_apply]
    simp only [LinearMap.smul_apply, co3DiffFun_apply, smul_eq_mul, LinearMap.coe_proj,
      Function.eval]
    have h1 := congrFun (congrFun co3Span_mul k)
    simp only [Matrix.mul_apply, co3DiffRows_get] at h1
    calc v k = ∑ i : Fin 22, (1 : Matrix (Fin 22) (Fin 22) (ZMod 2)) k i * v i := by
          simp [Matrix.one_apply]
      _ = ∑ i : Fin 22, (∑ j : Fin 22, rowsMatrix 22 co3SpanCoeffs k j *
            co3DiffCoef (co3DiffIdxAt j) i) * v i := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [h1 i]
      _ = ∑ j : Fin 22, rowsMatrix 22 co3SpanCoeffs k j *
            ∑ i : Fin 22, co3DiffCoef (co3DiffIdxAt j) i * v i := by
          simp only [Finset.mul_sum, Finset.sum_mul]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
          ring
  rw [e]
  exact Submodule.sum_mem _ fun j _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

theorem co3Diff_span :
    ⊤ ≤ Submodule.span (ZMod 2) (Set.range fun j : Fin 22 => co3DiffFun (co3DiffIdxAt j)) := by
  intro ψ _
  rw [dual_eq_sum_proj ψ]
  exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (proj_mem_span k)

theorem co3_finrank_dual : Module.finrank (ZMod 2) (Module.Dual (ZMod 2) Co3V) = 22 := by
  rw [Subspace.dual_finrank_eq, Module.finrank_fin_fun]

@[expose] def co3DiffBasis :
    Module.Basis (Fin 22) (ZMod 2) (Module.Dual (ZMod 2) Co3V) :=
  Module.Basis.mk (linearIndependent_of_top_le_span_of_card_eq_finrank co3Diff_span
    (by rw [Fintype.card_fin, co3_finrank_dual])) co3Diff_span

theorem co3DiffBasis_apply (k : Fin 22) (v : Co3V) :
    co3DiffBasis k v = co3Form (co3DiffIdxAt k) v - co3Form 0 v := by
  rw [co3DiffBasis, Module.Basis.mk_apply, co3Form_sub (co3DiffIdxAt_lt k)]

abbrev co3A1 : Matrix (Fin 22) (Fin 22) (ZMod 2) :=
  Blueprint.NativeSporadic.decode 2 22 1 Blueprint.NativeSporadic.Co3Seed1

abbrev co3A2 : Matrix (Fin 22) (Fin 22) (ZMod 2) :=
  Blueprint.NativeSporadic.decode 2 22 1 Blueprint.NativeSporadic.Co3Seed2

theorem rowsMatrix_co3RowsA : rowsMatrix 22 CFSG.Sporadic.Co3.Native.co3Data.rowsA = co3A1 :=
  rowsMatrix_rowsOfPayload 22 _

theorem rowsMatrix_co3RowsB : rowsMatrix 22 CFSG.Sporadic.Co3.Native.co3Data.rowsB = co3A2 :=
  rowsMatrix_rowsOfPayload 22 _

theorem co3A1_pow : co3A1 ^ 3 = 1 := by
  have h := congrArg (rowsMatrix 22) co3Seed_check.1
  rwa [rowsMatrix_powRows, rowsMatrix_idRows, rowsMatrix_co3RowsA] at h

theorem co3A2_pow : co3A2 ^ 4 = 1 := by
  have h := congrArg (rowsMatrix 22) co3Seed_check.2
  rwa [rowsMatrix_powRows, rowsMatrix_idRows, rowsMatrix_co3RowsB] at h

theorem det_ne_zero_of_pow_eq_one {M : Matrix (Fin 22) (Fin 22) (ZMod 2)} {e : ℕ} (he : e ≠ 0)
    (h : M ^ e = 1) : M.det ≠ 0 := by
  intro h0
  have h1 := congrArg Matrix.det h
  rw [Matrix.det_pow, h0, zero_pow he, Matrix.det_one] at h1
  exact zero_ne_one h1

theorem det_co3A1 :
    co3A1.det ≠ 0 := det_ne_zero_of_pow_eq_one (by norm_num) co3A1_pow

theorem det_co3A2 :
    co3A2.det ≠ 0 := det_ne_zero_of_pow_eq_one (by norm_num) co3A2_pow

@[expose] def co3SeedGL (k : ℕ) : GL (Fin 22) (ZMod 2) :=
  if k = 0 then Matrix.GeneralLinearGroup.mkOfDetNeZero co3A1 det_co3A1
  else Matrix.GeneralLinearGroup.mkOfDetNeZero co3A2 det_co3A2

theorem co3SeedGL_val (k : ℕ) :
    ((co3SeedGL k : GL (Fin 22) (ZMod 2)) : Matrix (Fin 22) (Fin 22) (ZMod 2)) =
      if k = 0 then co3A1 else co3A2 := by
  unfold co3SeedGL
  split_ifs <;> rfl

theorem rep_co3GenPerm
    {k : ℕ} (hk : k < 2) : Rep 276 co3ChainArrs[k]! (co3GenPerm k) :=
  rep_co3StrongPerm (by omega)

theorem co3Form_seed
    {k : ℕ} (hk : k < 2) (r : Fin 276) (v : Co3V) :
    co3Form r v = co3Form (co3GenPerm k r) ((if k = 0 then co3A1 else co3A2) *ᵥ v) := by
  have e : (co3ChainArrs[k]!)[(r : ℕ)]! = (co3GenPerm k r : ℕ) := rep_co3GenPerm hk r
  rcases (by omega : k = 0 ∨ k = 1) with rfl | rfl
  · rw [ite_eq_left rfl, ← rowsMatrix_co3RowsA, co3Form, co3Form, ← e]
    exact pullOK_spec (co3Faithful_check.2.2.1 r r.2).2 v
  · rw [ite_eq_right one_ne_zero, ← rowsMatrix_co3RowsB, co3Form, co3Form, ← e]
    exact pullOK_spec (co3Faithful_check.2.2.2.1 r r.2).2 v

theorem co3SeedGL_mulVec_inv (k : ℕ) (v : Co3V) :
    ((co3SeedGL k : Matrix (Fin 22) (Fin 22) (ZMod 2))) *ᵥ
      (((co3SeedGL k)⁻¹ : GL (Fin 22) (ZMod 2)) : Matrix (Fin 22) (Fin 22) (ZMod 2)) *ᵥ v = v := by
  rw [mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec]

theorem co3Form_seed_inv
    {k : ℕ} (hk : k < 2) (r : Fin 276) (v : Co3V) :
    co3Form r ((((co3SeedGL k)⁻¹ : GL (Fin 22) (ZMod 2)) : Matrix (Fin 22) (Fin 22) (ZMod 2)) *ᵥ
      v) = co3Form (co3GenPerm k r) v := by
  rw [co3Form_seed hk, ← co3SeedGL_val, co3SeedGL_mulVec_inv]

abbrev Co3GL : Type := LinearMap.GeneralLinearGroup (ZMod 2) Co3V

@[expose] def co3SeedLin
    (k : Fin 2) : Co3GL := Matrix.GeneralLinearGroup.toLin (co3SeedGL k)

@[expose] def co3G :
    Subgroup Co3GL := Subgroup.closure (Set.range co3SeedLin)

theorem co3X_finite : co3X.Finite := by
  have : co3X = co3Form '' {r | r < 276} := by
    ext q
    simp only [co3X, Set.mem_ofPred_eq, Set.mem_image]
  rw [this]
  exact (Set.finite_lt_nat 276).image _

theorem co3SeedLin_inv_apply (k : Fin 2) (v : Co3V) :
    (((co3SeedLin k)⁻¹ : Co3GL) : Co3V →ₗ[ZMod 2] Co3V) v =
      (((co3SeedGL k)⁻¹ : GL (Fin 22) (ZMod 2)) : Matrix _ _ (ZMod 2)) *ᵥ v := by
  rw [co3SeedLin, ← map_inv]
  exact Matrix.GeneralLinearGroup.toLin_apply _ v

theorem funAct_co3Form
    (k : Fin 2) (r : Fin 276) :
    funAct (co3SeedLin k) (co3Form r) = co3Form (co3GenPerm k r) := by
  funext v
  rw [funAct, co3SeedLin_inv_apply, co3Form_seed_inv k.2]

theorem co3Seed_mapsTo
    (k : Fin 2) : ∀ q ∈ co3X, funAct (co3SeedLin k) q ∈ co3X := by
  rintro _ ⟨r, hr, rfl⟩
  refine ⟨co3GenPerm k ⟨r, hr⟩, (co3GenPerm k ⟨r, hr⟩).2, ?_⟩
  rw [← funAct_co3Form k ⟨r, hr⟩]

theorem co3Form_mem (r : ℕ) (hr : r < 276) : co3Form r ∈ co3X := ⟨r, hr, rfl⟩

theorem co3_faithful :
    ∃ ρ : co3G →* Equiv.Perm co3X,
      (∀ g q, ((ρ g q : co3X) : Co3V → ZMod 2) = funAct (g : Co3GL) q) ∧
      Function.Injective ρ ∧
      ρ.range = Subgroup.closure (Set.range fun i =>
        ρ ⟨co3SeedLin i, Subgroup.subset_closure (Set.mem_range_self i)⟩) := by
  refine invariant_function_differences_faithful_action co3X co3X_finite (co3Form 0)
    (co3Form_mem 0 (by norm_num)) ?_ ?_ co3SeedLin co3Seed_mapsTo
  · rintro _ ⟨r, hr, rfl⟩
    exact ⟨co3DiffFun r, co3Form_sub hr⟩
  · refine eq_top_iff.2 (le_trans co3Diff_span (Submodule.span_mono ?_))
    rintro _ ⟨j, rfl⟩
    exact ⟨co3Form (co3DiffIdxAt j), co3Form_mem _ (co3DiffIdxAt_lt j),
      co3Form_sub (co3DiffIdxAt_lt j)⟩

@[expose] def co3RhoX :
    co3G →* Equiv.Perm co3X := co3_faithful.choose

theorem co3RhoX_apply
    (g : co3G) (q : co3X) :
    ((co3RhoX g q : co3X) : Co3V → ZMod 2) = funAct (g : Co3GL) q :=
  co3_faithful.choose_spec.1 g q

theorem co3RhoX_injective :
    Function.Injective co3RhoX := co3_faithful.choose_spec.2.1

theorem co3RhoX_range :
    co3RhoX.range = Subgroup.closure (Set.range fun i =>
    co3RhoX ⟨co3SeedLin i, Subgroup.subset_closure (Set.mem_range_self i)⟩) :=
  co3_faithful.choose_spec.2.2

@[expose] def co3XMk (r : Fin 276) : co3X := ⟨co3Form r, co3Form_mem r r.2⟩

theorem co3XMk_val (r : Fin 276) : (co3XMk r : Co3V → ZMod 2) = co3Form r := rfl

theorem co3XMk_bijective :
    Function.Bijective co3XMk := by
  refine ⟨fun r r' h => Fin.ext (co3Form_injective r.2 r'.2 ?_), fun q => ?_⟩
  · rw [← co3XMk_val, ← co3XMk_val, h]
  · obtain ⟨r, hr, hq⟩ := q.2
    exact ⟨⟨r, hr⟩, Subtype.ext ((co3XMk_val _).trans hq)⟩

@[expose] def co3XEquiv :
    Fin 276 ≃ co3X := Equiv.ofBijective co3XMk co3XMk_bijective

theorem co3XEquiv_apply
    (r : Fin 276) : (co3XEquiv r : Co3V → ZMod 2) = co3Form r :=
  co3XMk_val r

@[expose] def co3Rho :
    co3G →* Equiv.Perm (Fin 276) :=
  co3XEquiv.symm.permCongrHom.toMonoidHom.comp co3RhoX

theorem co3XEquiv_rho
    (g : co3G) (r : Fin 276) :
    co3XEquiv (co3Rho g r) = co3RhoX g (co3XEquiv r) := by
  change co3XEquiv (co3XEquiv.symm (co3RhoX g (co3XEquiv.symm.symm r))) = _
  rw [Equiv.apply_symm_apply, Equiv.symm_symm]

theorem co3Form_rho
    (g : co3G) (r : Fin 276) :
    co3Form (co3Rho g r) = funAct (g : Co3GL) (co3Form r) := by
  have h := congrArg Subtype.val (co3XEquiv_rho g r)
  rw [co3XEquiv_apply, co3RhoX_apply, co3XEquiv_apply] at h
  exact h

theorem co3Rho_injective :
    Function.Injective co3Rho :=
  co3XEquiv.symm.permCongrHom.injective.comp co3RhoX_injective

theorem co3Rho_seed (k : Fin 2) :
    co3Rho ⟨co3SeedLin k, Subgroup.subset_closure ⟨k, rfl⟩⟩ = co3GenPerm k := by
  refine Equiv.ext fun r => Fin.ext (co3Form_injective (Fin.isLt _) (Fin.isLt _) ?_)
  rw [co3Form_rho]
  exact funAct_co3Form k r

theorem co3Chain_original_toList : co3Chain.original.toList = [co3GenPerm 0, co3GenPerm 1] := by
  change (Vector.ofFn fun i : Fin 2 => permOfArr 276 co3ChainArrs[(i : ℕ)]!).toList = _
  rw [Vector.toList_ofFn]
  rfl

theorem co3P_eq : co3P = Subgroup.closure (Set.range fun k : Fin 2 => co3GenPerm k) := by
  rw [co3P, RawSchreierDatum.originalSubgroup, co3Chain_original_toList]
  congr 1
  ext g
  simp only [Set.mem_ofPred_eq, List.mem_cons, List.not_mem_nil, or_false, Set.mem_range,
    Fin.exists_fin_two]
  constructor
  · rintro (rfl | rfl)
    · exact Or.inl rfl
    · exact Or.inr rfl
  · rintro (h | h)
    · exact Or.inl h.symm
    · exact Or.inr h.symm

theorem co3Rho_range :
    co3Rho.range = co3P := by
  rw [co3Rho, MonoidHom.range_comp, co3RhoX_range, MonoidHom.map_closure, co3P_eq]
  congr 1
  ext σ
  simp only [Set.mem_image, Set.mem_range]
  constructor
  · rintro ⟨_, ⟨k, rfl⟩, rfl⟩
    exact ⟨k, (co3Rho_seed k).symm⟩
  · rintro ⟨k, rfl⟩
    exact ⟨_, ⟨k, rfl⟩, co3Rho_seed k⟩

@[expose] def co3ToLin : GL (Fin 22) (ZMod 2) →* Co3GL :=
  Matrix.GeneralLinearGroup.toLin.toMonoidHom

theorem co3ToLin_injective : Function.Injective co3ToLin :=
  Matrix.GeneralLinearGroup.toLin.injective

theorem co3SeedLin_eq
    (k : Fin 2) : co3SeedLin k = co3ToLin (co3SeedGL k) := rfl

abbrev co3J : Subgroup (GL (Fin 22) (ZMod 2)) :=
  Subgroup.closure {Matrix.GeneralLinearGroup.mkOfDetNeZero co3A1 det_co3A1,
    Matrix.GeneralLinearGroup.mkOfDetNeZero co3A2 det_co3A2}

theorem co3SeedGL_mem (k : ℕ) : co3SeedGL k ∈ co3J := by
  unfold co3SeedGL
  split_ifs
  · exact Subgroup.subset_closure (Set.mem_insert _ _)
  · exact Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)

theorem co3ToLin_mem (g : co3J) : co3ToLin g ∈ co3G := by
  obtain ⟨g, hg⟩ := g
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with rfl | rfl
    · exact Subgroup.subset_closure ⟨0, by rw [co3SeedLin_eq]; rfl⟩
    · exact Subgroup.subset_closure ⟨1, by rw [co3SeedLin_eq]; rfl⟩
  | one => rw [map_one]; exact co3G.one_mem
  | mul x y _ _ hx hy => rw [map_mul]; exact co3G.mul_mem hx hy
  | inv x _ hx => rw [map_inv]; exact co3G.inv_mem hx

@[expose] def co3JHom : co3J →* co3G :=
  (co3ToLin.comp co3J.subtype).codRestrict co3G co3ToLin_mem

theorem co3JHom_val (g : co3J) :
    ((co3JHom g : co3G) : Co3GL) = co3ToLin (g : GL (Fin 22) (ZMod 2)) := rfl

theorem co3JHom_bijective : Function.Bijective co3JHom := by
  refine ⟨fun g h e => ?_, ?_⟩
  · have e' := congrArg Subtype.val e
    rw [co3JHom_val, co3JHom_val] at e'
    exact Subtype.ext (co3ToLin_injective e')
  rintro ⟨h, hh⟩
  induction hh using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨k, rfl⟩ := hx
    exact ⟨⟨co3SeedGL k, co3SeedGL_mem k⟩, Subtype.ext (co3SeedLin_eq k).symm⟩
  | one => exact ⟨1, map_one _⟩
  | mul x y _ _ hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    exact ⟨a * b, by rw [map_mul, ha, hb]; rfl⟩
  | inv x _ hx =>
    obtain ⟨a, ha⟩ := hx
    exact ⟨a⁻¹, by rw [map_inv, ha]; rfl⟩

@[expose] def co3JEquivG :
    co3J ≃* co3G := MulEquiv.ofBijective co3JHom co3JHom_bijective

@[expose] def co3MatEquiv : Blueprint.NativeSporadic.Co3 ≃* co3J :=
  Blueprint.NativeSporadic.matrixSeedEquiv 2 22 (by norm_num) co3A1 co3A2 det_co3A1 det_co3A2

theorem co3MatEquiv_val (u : Blueprint.NativeSporadic.Co3) :
    (((co3MatEquiv u : co3J) : GL (Fin 22) (ZMod 2)) : Matrix (Fin 22) (Fin 22) (ZMod 2)) =
      u.val.val :=
  Blueprint.NativeSporadic.matrixSeedEquiv_val 2 22 _ co3A1 co3A2 _ _ u

@[expose] def co3EquivG :
    Blueprint.NativeSporadic.Co3 ≃* co3G := co3MatEquiv.trans co3JEquivG

@[expose] def co3PermHom :
    Blueprint.NativeSporadic.Co3 →* Equiv.Perm (Fin 276) where
  toFun u := co3Rho (co3EquivG u)
  map_one' := by rw [map_one, map_one]
  map_mul' u w := by rw [map_mul, map_mul]

theorem co3PermHom_apply
    (u : Blueprint.NativeSporadic.Co3) :
    co3PermHom u = co3Rho (co3EquivG u) := rfl

theorem co3PermHom_injective :
    Function.Injective co3PermHom :=
  co3Rho_injective.comp co3EquivG.injective

theorem co3PermHom_range :
    co3PermHom.range = co3P := by
  rw [← co3Rho_range]
  ext σ
  constructor
  · rintro ⟨u, rfl⟩
    exact ⟨_, rfl⟩
  · rintro ⟨g, rfl⟩
    exact ⟨co3EquivG.symm g, by simp [co3PermHom]⟩

@[expose] def co3PermEquiv :
    Blueprint.NativeSporadic.Co3 ≃* co3P :=
  (MonoidHom.ofInjective co3PermHom_injective).trans (MulEquiv.subgroupCongr co3PermHom_range)

theorem co3PermEquiv_apply
    (u : Blueprint.NativeSporadic.Co3) :
    (co3PermEquiv u : Equiv.Perm (Fin 276)) = co3PermHom u := rfl

@[expose] def co3SeedA : Blueprint.NativeSporadic.Co3 :=
  co3MatEquiv.symm ⟨co3SeedGL 0, co3SeedGL_mem 0⟩

@[expose] def co3SeedB : Blueprint.NativeSporadic.Co3 :=
  co3MatEquiv.symm ⟨co3SeedGL 1, co3SeedGL_mem 1⟩

theorem co3SeedA_val : co3SeedA.val.val = co3A1 := by
  rw [← co3MatEquiv_val, co3SeedA, MulEquiv.apply_symm_apply, co3SeedGL_val]
  rfl

theorem co3SeedB_val : co3SeedB.val.val = co3A2 := by
  rw [← co3MatEquiv_val, co3SeedB, MulEquiv.apply_symm_apply, co3SeedGL_val]
  rfl

theorem co3EquivG_seed (k : Fin 2) :
    co3EquivG (co3MatEquiv.symm ⟨co3SeedGL k, co3SeedGL_mem k⟩) =
      ⟨co3SeedLin k, Subgroup.subset_closure ⟨k, rfl⟩⟩ := by
  apply Subtype.ext
  show ((co3JEquivG (co3MatEquiv (co3MatEquiv.symm ⟨co3SeedGL k, co3SeedGL_mem k⟩)) : co3G) :
    Co3GL) = co3SeedLin k
  rw [MulEquiv.apply_symm_apply]
  rfl

theorem co3PermEquiv_seedA :
    (co3PermEquiv co3SeedA : Equiv.Perm (Fin 276)) = co3GenPerm 0 := by
  rw [co3PermEquiv_apply, co3PermHom_apply]
  exact (congrArg co3Rho (co3EquivG_seed 0)).trans (co3Rho_seed 0)

theorem co3PermEquiv_seedB :
    (co3PermEquiv co3SeedB : Equiv.Perm (Fin 276)) = co3GenPerm 1 := by
  rw [co3PermEquiv_apply, co3PermHom_apply]
  exact (congrArg co3Rho (co3EquivG_seed 1)).trans (co3Rho_seed 1)

theorem co3EquivG_inv_apply
    (u : Blueprint.NativeSporadic.Co3) (v : Co3V) :
    ((((co3EquivG u)⁻¹ : co3G) : Co3GL) : Co3V →ₗ[ZMod 2] Co3V) v =
      (u⁻¹ : Blueprint.NativeSporadic.Co3).val.val *ᵥ v := by
  rw [← map_inv, ← co3MatEquiv_val]
  have e : ((co3EquivG u⁻¹ : co3G) : Co3GL) =
      co3ToLin ((co3MatEquiv u⁻¹ : co3J) : GL (Fin 22) (ZMod 2)) := rfl
  rw [e]
  exact Matrix.GeneralLinearGroup.toLin_apply _ v

theorem co3Form_permEquiv
    (u : Blueprint.NativeSporadic.Co3) (r : Fin 276) (v : Co3V) :
    co3Form ((co3PermEquiv u : Equiv.Perm (Fin 276)) r) v =
      co3Form r ((u⁻¹ : Blueprint.NativeSporadic.Co3).val.val *ᵥ v) := by
  rw [co3PermEquiv_apply, co3PermHom_apply, co3Form_rho, funAct, ← co3EquivG_inv_apply]
  rfl

theorem Co3_faithful_permutation_action :
    (∀ r < 276, ∀ r' < 276, co3Form r = co3Form r' → r = r') ∧
    (∀ r < 276, ∃ φ : Module.Dual (ZMod 2) Co3V, ∀ v, φ v = co3Form r v - co3Form 0 v) ∧
    (∃ b : Module.Basis (Fin 22) (ZMod 2) (Module.Dual (ZMod 2) Co3V), ∀ (k : Fin 22) v,
      b k v = co3Form (co3DiffIdx.getD k 0) v - co3Form 0 v) ∧
    (∀ (r : Fin 276) (v : Co3V), co3Form r (co3A1⁻¹ *ᵥ v) = co3Form (co3GenPerm 0 r) v) ∧
    (∀ (r : Fin 276) (v : Co3V), co3Form r (co3A2⁻¹ *ᵥ v) = co3Form (co3GenPerm 1 r) v) ∧
    (∀ (u : Blueprint.NativeSporadic.Co3) (r : Fin 276) (v : Co3V),
      co3Form ((co3PermEquiv u : Equiv.Perm (Fin 276)) r) v =
        co3Form r ((u⁻¹ : Blueprint.NativeSporadic.Co3).val.val *ᵥ v)) ∧
    co3SeedA.val.val = co3A1 ∧ co3SeedB.val.val = co3A2 ∧
    (co3PermEquiv co3SeedA : Equiv.Perm (Fin 276)) = co3GenPerm 0 ∧
    (co3PermEquiv co3SeedB : Equiv.Perm (Fin 276)) = co3GenPerm 1 := by
  have hA : (((co3SeedGL 0)⁻¹ : GL (Fin 22) (ZMod 2)) : Matrix (Fin 22) (Fin 22) (ZMod 2)) =
      co3A1⁻¹ := by
    rw [Matrix.coe_units_inv, co3SeedGL_val, ite_eq_left rfl]
  have hB : (((co3SeedGL 1)⁻¹ : GL (Fin 22) (ZMod 2)) : Matrix (Fin 22) (Fin 22) (ZMod 2)) =
      co3A2⁻¹ := by
    rw [Matrix.coe_units_inv, co3SeedGL_val, ite_eq_right one_ne_zero]
  refine ⟨fun r hr r' hr' h => co3Form_injective hr hr' h,
    fun r hr => ⟨co3DiffFun r, co3Form_sub hr⟩, ⟨co3DiffBasis, fun k v => co3DiffBasis_apply k v⟩,
    fun r v => ?_, fun r v => ?_, co3Form_permEquiv, co3SeedA_val, co3SeedB_val,
    co3PermEquiv_seedA, co3PermEquiv_seedB⟩
  · rw [← hA]
    exact co3Form_seed_inv (by norm_num) r v
  · rw [← hB]
    exact co3Form_seed_inv (by norm_num) r v

end CFSG.Sporadic.Schreier.Co3
