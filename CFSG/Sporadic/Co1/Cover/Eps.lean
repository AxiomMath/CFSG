module

public import CFSG.Sporadic.Co1.Cover.Checks
public import Certificates.Certificate10062

public section

namespace CFSG.Sporadic.Co1.Cover

open CFSG.Blueprint CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native
  CFSG.Sporadic.Co1.CoverNative CFSG.Sporadic.Co1.Module Matrix

attribute [local irreducible] eps0 ga gb regCov rrCov epsRows

theorem zmod2_cases (k : ZMod 2) : k = 0 ∨ k = 1 := by
  revert k
  decide

theorem matHom_regCov
    (i : ℕ) : matHom (regCov i) = rowsMatrix 24 (rrCov i) := mat_regCov i

theorem epsRows_get (i : ℕ) (hi : i < 11) : epsRows[i]! = rrCov (8 + i) := by
  unfold epsRows
  simp [hi]

theorem matHom_eps0
    (i : Fin 11) : matHom (eps0 i) = rowsMatrix 24 epsRows[i.val]! := by
  rw [epsRows_get i.val i.isLt, eps0_eq]
  exact matHom_regCov _

theorem matHom_ga : matHom ga = rowsMatrix 24 (rrCov 4) := by
  rw [ga_eq]
  exact matHom_regCov 4

theorem matHom_gb : matHom gb = rowsMatrix 24 (rrCov 5) := by
  rw [gb_eq]
  exact matHom_regCov 5

theorem eps0_sq
    (i : Fin 11) : eps0 i * eps0 i = 1 := by
  have h := cov_basic
  simp only [epsBasicOK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range] at h
  have h2 := (h.2 i.val i.isLt).1.2
  apply matHom_injective
  rw [map_mul, matHom_eps0, ← rowsMatrix_mulRows, h2, rowsMatrix_idRows, map_one]

theorem eps0_comm
    (i j : Fin 11) : eps0 i * eps0 j = eps0 j * eps0 i := by
  have h := cov_basic
  simp only [epsBasicOK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range] at h
  have h2 := (h.2 i.val i.isLt).2 j.val j.isLt
  apply matHom_injective
  rw [map_mul, map_mul, matHom_eps0, matHom_eps0, ← rowsMatrix_mulRows, ← rowsMatrix_mulRows, h2]

@[expose] noncomputable def epsFactor
    (i : Fin 11) :
    Multiplicative (ZMod 2) →* NativeSporadic.Co1 where
  toFun y := if Multiplicative.toAdd y = 0 then 1 else eps0 i
  map_one' := by simp
  map_mul' y z := by
    rcases zmod2_cases (Multiplicative.toAdd y) with hy | hy <;>
      rcases zmod2_cases (Multiplicative.toAdd z) with hz | hz
    · simp [toAdd_mul, hy, hz]
    · simp [toAdd_mul, hy, hz]
    · simp [toAdd_mul, hy, hz]
    · have h11 : (1 : ZMod 2) + 1 = 0 := by decide
      simp [toAdd_mul, hy, hz, h11, eps0_sq]

theorem epsFactor_one
    (i : Fin 11) : epsFactor i (Multiplicative.ofAdd 1) = eps0 i := by
  show (if Multiplicative.toAdd (Multiplicative.ofAdd (1 : ZMod 2)) = 0 then 1 else eps0 i) = _
  simp

theorem epsFactor_commute
    (i j : Fin 11) (x y : Multiplicative (ZMod 2)) :
    Commute (epsFactor i x) (epsFactor j y) := by
  show Commute (if Multiplicative.toAdd x = 0 then 1 else eps0 i)
    (if Multiplicative.toAdd y = 0 then 1 else eps0 j)
  by_cases hx : Multiplicative.toAdd x = 0
  · simp only [hx, ite_true]
    exact Commute.one_left _
  · by_cases hy : Multiplicative.toAdd y = 0
    · simp only [hy, ite_true]
      exact Commute.one_right _
    · simp only [hx, hy, ite_false]
      exact eps0_comm i j

theorem epsFactor_pairwise :
    Pairwise fun i j : Fin 11 => ∀ (x : Multiplicative (ZMod 2)) (y : Multiplicative (ZMod 2)),
      Commute (epsFactor i x) (epsFactor j y) :=
  fun i j _ x y => epsFactor_commute i j x y

@[expose] noncomputable def epsHom :
    Multiplicative (Fin 11 → ZMod 2) →* NativeSporadic.Co1 :=
  (MonoidHom.noncommPiCoprod epsFactor epsFactor_pairwise).comp
    (MulEquiv.piMultiplicative (fun _ : Fin 11 => ZMod 2)).toMonoidHom

theorem piMultiplicative_single (i : Fin 11) :
    (MulEquiv.piMultiplicative (fun _ : Fin 11 => ZMod 2))
      (Multiplicative.ofAdd (Pi.single i 1)) =
        Pi.mulSingle i (Multiplicative.ofAdd (1 : ZMod 2)) := by
  funext j
  by_cases hj : j = i
  · subst hj
    simp [MulEquiv.piMultiplicative]
  · simp [MulEquiv.piMultiplicative, hj]

theorem epsHom_single (i : Fin 11) :
    epsHom (Multiplicative.ofAdd (Pi.single i 1)) = eps0 i := by
  rw [epsHom, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, piMultiplicative_single]
  exact (MonoidHom.noncommPiCoprod_mulSingle (ϕ := epsFactor) (hcomm := epsFactor_pairwise) i
    (Multiplicative.ofAdd (1 : ZMod 2))).trans (epsFactor_one i)

theorem hom_ext_basis {G : Type*} [Group G] {n : ℕ} (f g : Multiplicative (Fin n → ZMod 2) →* G)
    (h : ∀ i, f (Multiplicative.ofAdd (Pi.single i 1)) =
      g (Multiplicative.ofAdd (Pi.single i 1))) : f = g := by
  refine MonoidHom.ext fun x => ?_
  obtain ⟨v, rfl⟩ := Multiplicative.ofAdd.surjective x
  have hs : ∀ s : Finset (Fin n), f (Multiplicative.ofAdd (∑ i ∈ s, Pi.single i (v i))) =
      g (Multiplicative.ofAdd (∑ i ∈ s, Pi.single i (v i))) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert j s hj ih =>
      rw [Finset.sum_insert hj, ofAdd_add, map_mul, map_mul, ih]
      congr 1
      rcases zmod2_cases (v j) with h0 | h1
      · rw [h0]
        simp
      · rw [h1]
        exact h j
  have := hs Finset.univ
  rwa [Finset.univ_sum_single] at this

@[expose] def matAct {n : ℕ} (M : Matrix (Fin n) (Fin n) (ZMod 2)) :
    Multiplicative (Fin n → ZMod 2) →* Multiplicative (Fin n → ZMod 2) where
  toFun x := Multiplicative.ofAdd (M *ᵥ Multiplicative.toAdd x)
  map_one' := by simp
  map_mul' x y := by
    show Multiplicative.ofAdd (M *ᵥ (Multiplicative.toAdd x + Multiplicative.toAdd y)) = _
    rw [Matrix.mulVec_add]
    rfl

theorem conj_of_basis
    {g : NativeSporadic.Co1} (A : Matrix (Fin 11) (Fin 11) (ZMod 2))
    (hbasis : ∀ i : Fin 11, g * eps0 i * g⁻¹ =
      epsHom (Multiplicative.ofAdd (A *ᵥ Pi.single i 1))) (x : Multiplicative (Fin 11 → ZMod 2)) :
    g * epsHom x * g⁻¹ = epsHom (Multiplicative.ofAdd (A *ᵥ Multiplicative.toAdd x)) := by
  have h := hom_ext_basis ((MulAut.conj g).toMonoidHom.comp epsHom) (epsHom.comp (matAct A))
    (fun i => by
      rw [MonoidHom.comp_apply, MonoidHom.comp_apply, epsHom_single]
      exact hbasis i)
  have := DFunLike.congr_fun h x
  rw [MonoidHom.comp_apply, MonoidHom.comp_apply] at this
  exact this

@[expose] def prefixVec (k m : ℕ) : Fin 11 → ZMod 2 :=
  fun j => if j.val < k ∧ m.testBit j.val then 1 else 0

theorem prefixVec_zero (m : ℕ) : prefixVec 0 m = 0 := by
  funext j
  simp [prefixVec]

theorem prefixVec_eleven (m : ℕ) : prefixVec 11 m = toVecD 11 m := by
  funext j
  simp [prefixVec, toVecD, j.isLt]

theorem prefixVec_succ (k m : ℕ) (hk : k < 11) :
    prefixVec (k + 1) m =
      prefixVec k m + (if m.testBit k then Pi.single ⟨k, hk⟩ 1 else 0) := by
  funext j
  by_cases hjk : j.val < k
  · have hne : j ≠ ⟨k, hk⟩ := fun e => by simp [Fin.ext_iff] at e; omega
    by_cases hb : m.testBit k <;>
      simp [prefixVec, hb, hjk, hne, show j.val < k + 1 by omega]
  · by_cases hjk' : j.val = k
    · have : j = ⟨k, hk⟩ := Fin.ext hjk'
      subst this
      by_cases hb : m.testBit k <;> simp [prefixVec, hb]
    · have hne : j ≠ ⟨k, hk⟩ := fun e => by simp [Fin.ext_iff] at e; omega
      by_cases hb : m.testBit k <;>
        simp [prefixVec, hb, hne, hjk, show ¬ j.val < k + 1 by omega]

theorem matHom_epsHom_prefix
    (m : ℕ) :
    ∀ k, k ≤ 11 → matHom (epsHom (Multiplicative.ofAdd (prefixVec k m))) =
      rowsMatrix 24 ((List.range k).foldl
        (fun acc i => if m.testBit i then mulRows 24 acc epsRows[i]! else acc) (idRows 24))
  | 0, _ => by
    simp [prefixVec_zero, rowsMatrix_idRows]
  | k + 1, hk => by
    have ih := matHom_epsHom_prefix m k (by omega)
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
      prefixVec_succ k m (by omega)]
    by_cases hb : m.testBit k
    · simp only [hb, ite_true, ofAdd_add, map_mul, ih, epsHom_single, matHom_eps0,
        rowsMatrix_mulRows]
    · simp [hb, ih]

theorem matHom_epsHom_toVecD
    (m : ℕ) :
    matHom (epsHom (Multiplicative.ofAdd (toVecD 11 m))) = rowsMatrix 24 (eprodRows epsRows m) := by
  rw [← prefixVec_eleven, matHom_epsHom_prefix m 11 le_rfl]
  rfl

theorem getElem!_eq_getD' (R : Array ℕ) (i : ℕ) : R[i]! = R[i]?.getD 0 := by
  cases h : R[i]? <;> simp [getElem!_def, h]

theorem exists_toVecD (v : Fin 11 → ZMod 2) : ∃ m, m < 2 ^ 11 ∧ toVecD 11 m = v := by
  refine ⟨ofBits 11 (fun j => if h : j < 11 then decide (v ⟨j, h⟩ = 1) else false),
    ofBits_lt _ _, ?_⟩
  funext j
  rw [toVecD_ofBits]
  simp only [j.isLt, dite_true]
  rcases zmod2_cases (v j) with h | h <;> simp [h]

theorem validRows_idRows :
    CFSG.Sporadic.Co1.InvNative.validRows (idRows 24) = true :=
  Certificates.certificate10062

theorem epsHom_injective :
    Function.Injective epsHom := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_bot]
  obtain ⟨v, rfl⟩ := Multiplicative.ofAdd.surjective x
  obtain ⟨m, hm, rfl⟩ := exists_toVecD v
  rw [MonoidHom.mem_ker] at hx
  by_cases hm0 : m = 0
  · subst hm0
    rw [toVecD_zero]
    rfl
  · exfalso
    obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    have h := cov_inj
    simp only [epsInjOK, List.all_eq_true, List.mem_range, Bool.and_eq_true, bne_iff_ne,
      ne_eq] at h
    obtain ⟨hvalid, hne⟩ := h k (by omega)
    have hmat : rowsMatrix 24 (eprodRows epsRows (k + 1)) = rowsMatrix 24 (idRows 24) := by
      rw [← matHom_epsHom_toVecD, hx, map_one, rowsMatrix_idRows]
    exact hne (rowsMatrix_injective_of_valid hvalid validRows_idRows hmat)

theorem basis_conj
    {g : NativeSporadic.Co1} {R M : Array ℕ} (hg : matHom g = rowsMatrix 24 R)
    (h : normOK epsRows R (transposeRows 11 M) = true) (i : Fin 11) :
    g * eps0 i * g⁻¹ = epsHom (Multiplicative.ofAdd (rowsMatrix 11 M *ᵥ Pi.single i 1)) := by
  simp only [normOK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range] at h
  have hi := h.2 i.val i.isLt
  have hcol : toVecD 11 ((transposeRows 11 M)[i.val]!) = rowsMatrix 11 M *ᵥ Pi.single i 1 := by
    funext j
    rw [Matrix.mulVec_single_one, Matrix.col_apply]
    have h2 := congrFun (congrFun (rowsMatrix_transposeRows 11 M) i) j
    rw [rowsMatrix_apply, Matrix.transpose_apply] at h2
    rw [getElem!_eq_getD']
    exact h2
  rw [← hcol]
  have h1 : g * eps0 i =
      epsHom (Multiplicative.ofAdd (toVecD 11 ((transposeRows 11 M)[i.val]!))) * g := by
    apply matHom_injective
    rw [map_mul, map_mul, matHom_epsHom_toVecD, matHom_eps0, hg, ← rowsMatrix_mulRows,
      ← rowsMatrix_mulRows, hi]
  rw [h1, mul_assoc, mul_inv_cancel, mul_one]

end CFSG.Sporadic.Co1.Cover
