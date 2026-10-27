module

public import CFSG.Assembly.GL83LieDefs
public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerUnitaryHypCount
public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotBlocksBasic
public import CFSG.Mathlib.LinearAlgebra.Matrix.DiagGLConj
public import CFSG.Open.StatedAPI
public import TauCeti.GroupTheory.FixedSubgroup
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Diagonal.Basic
public import CFSG.LieType.BorelTits.CompleteFlag

public section

namespace CFSG.StandardType.FrameRoute.UnitaryModel

open CFSG.Assembly CFSG.SeitzReduction.UnitaryPilot CFSG.LocalAnalysis.ComponentInitial

variable {K : Type} [Field K] {d : ℕ}

private lemma pow_eq_pow_iff_zmod3 {k : Type} [Group k] {ζ : k} (hζ : orderOf ζ = 3)
    {m n : ℕ} : ζ ^ m = ζ ^ n ↔ (m : ZMod 3) = (n : ZMod 3) := by
  rw [pow_eq_pow_iff_modEq, hζ]
  exact (ZMod.natCast_eq_natCast_iff m n 3).symm

private lemma diagGL_conj_det (e : Fin d → Kˣ) {A : GL (Fin d) K}
    (hA : (A : Matrix (Fin d) (Fin d) K).det = 1) :
    (((TauCeti.diagGL e * A * (TauCeti.diagGL e)⁻¹ : GL (Fin d) K) :
      Matrix (Fin d) (Fin d) K)).det = 1 := by
  have hAd : Matrix.GeneralLinearGroup.det A = 1 := by
    apply Units.ext
    rw [Matrix.GeneralLinearGroup.val_det_apply, hA, Units.val_one]
  have hB : Matrix.GeneralLinearGroup.det
      (TauCeti.diagGL e * A * (TauCeti.diagGL e)⁻¹) = 1 := by
    rw [map_mul, map_mul, map_inv, hAd]
    simp
  rw [← Matrix.GeneralLinearGroup.val_det_apply, hB, Units.val_one]

private lemma diagGL_conj_unitary_term {q : ℕ} {e : Fin d → Kˣ}
    (hpow : ∀ i, (e i : K) ^ q * (e i : K) = 1) (A : GL (Fin d) K) (i j k : Fin d) :
    ((e k : K) * (A : Matrix (Fin d) (Fin d) K) k i * ((e i : K))⁻¹) ^ q *
        ((e k : K) * (A : Matrix (Fin d) (Fin d) K) k j * ((e j : K))⁻¹) =
      ((A : Matrix (Fin d) (Fin d) K) k i) ^ q * (A : Matrix (Fin d) (Fin d) K) k j *
        ((((e i : K))⁻¹) ^ q * ((e j : K))⁻¹) := by
  rw [mul_pow, mul_pow]
  calc ((e k : K) ^ q * (A : Matrix (Fin d) (Fin d) K) k i ^ q *
        (((e i : K))⁻¹) ^ q) *
        ((e k : K) * (A : Matrix (Fin d) (Fin d) K) k j * ((e j : K))⁻¹) =
      ((e k : K) ^ q * (e k : K)) *
        ((A : Matrix (Fin d) (Fin d) K) k i ^ q *
          (A : Matrix (Fin d) (Fin d) K) k j) *
        ((((e i : K))⁻¹) ^ q * ((e j : K))⁻¹) := by ring
    _ = _ := by rw [hpow k, one_mul]

private lemma diagGL_conj_unitary {q : ℕ} {e : Fin d → Kˣ}
    (he : ∀ i, e i ^ (q + 1) = 1) {A : GL (Fin d) K}
    (hA : Matrix.transpose ((A : Matrix (Fin d) (Fin d) K).map (· ^ q)) *
      (A : Matrix (Fin d) (Fin d) K) = 1) :
    Matrix.transpose (((TauCeti.diagGL e * A * (TauCeti.diagGL e)⁻¹ : GL (Fin d) K) :
      Matrix (Fin d) (Fin d) K).map (· ^ q)) *
      ((TauCeti.diagGL e * A * (TauCeti.diagGL e)⁻¹ : GL (Fin d) K) :
        Matrix (Fin d) (Fin d) K) = 1 := by
  have hpow : ∀ i, (e i : K) ^ q * (e i : K) = 1 := by
    intro i
    have h := congrArg (fun u : Kˣ => (u : K)) (he i)
    rw [Units.val_pow_eq_pow_val, Units.val_one] at h
    rwa [pow_succ] at h
  have hq1 : ∀ i, (e i : K) ^ (q + 1) = 1 := by
    intro i
    rw [pow_succ]
    exact hpow i
  ext i j
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply]
  have hM : ∀ k l, (((TauCeti.diagGL e * A * (TauCeti.diagGL e)⁻¹ : GL (Fin d) K) :
      Matrix (Fin d) (Fin d) K)) k l =
      (e k : K) * (A : Matrix (Fin d) (Fin d) K) k l * ((e l : K))⁻¹ :=
    fun k l => diagGL_mul_mul_inv_apply e A k l
  simp only [hM]
  rw [Finset.sum_congr rfl (fun k _ => diagGL_conj_unitary_term hpow A i j k),
    ← Finset.sum_mul]
  have hsum : (∑ k, ((A : Matrix (Fin d) (Fin d) K) k i) ^ q *
      (A : Matrix (Fin d) (Fin d) K) k j) =
      (1 : Matrix (Fin d) (Fin d) K) i j := by
    have h := congrFun (congrFun hA i) j
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply] at h
    exact h
  rw [hsum]
  by_cases hij : i = j
  · subst hij
    rw [Matrix.one_apply_eq, one_mul, ← pow_succ, inv_pow, hq1 i, inv_one]
  · rw [Matrix.one_apply_ne hij]
    ring

@[expose] def suBlock (hK : Nat.card K = 4) (I : Finset (Fin d)) :
    Subgroup (LargeEvenProj (LargeEvenSUGroup (Fin d) K 2)) :=
  (unitaryBlock (⟨Nat.prime_two, le_rfl, hK⟩ : UnitaryFieldData 2 1 K) I).map
    (LargeEvenProjMk (LargeEvenSUGroup (Fin d) K 2))

theorem diagGL_mul_mul_inv_mem_largeEvenSUGroup {q : ℕ} {e : Fin d → Kˣ}
    (he : ∀ i, e i ^ (q + 1) = 1) {g : GL (Fin d) K} (hg : g ∈ LargeEvenSUGroup (Fin d) K q) :
    TauCeti.diagGL e * g * (TauCeti.diagGL e)⁻¹ ∈ LargeEvenSUGroup (Fin d) K q := by
  have hSU : LargeEvenSUGroup (Fin d) K q = Subgroup.closure {A : GL (Fin d) K |
      (A : Matrix (Fin d) (Fin d) K).det = 1 ∧
        Matrix.transpose ((A : Matrix (Fin d) (Fin d) K).map (· ^ q)) *
          (A : Matrix (Fin d) (Fin d) K) = 1} := rfl
  rw [hSU] at hg ⊢
  refine Subgroup.closure_induction (p := fun x _ =>
    TauCeti.diagGL e * x * (TauCeti.diagGL e)⁻¹ ∈ Subgroup.closure {A : GL (Fin d) K |
      (A : Matrix (Fin d) (Fin d) K).det = 1 ∧
        Matrix.transpose ((A : Matrix (Fin d) (Fin d) K).map (· ^ q)) *
          (A : Matrix (Fin d) (Fin d) K) = 1}) ?_ ?_ ?_ ?_ hg
  · rintro A hA
    exact Subgroup.subset_closure ⟨diagGL_conj_det e hA.1, diagGL_conj_unitary he hA.2⟩
  · rw [mul_one, mul_inv_cancel]
    exact Subgroup.one_mem _
  · intro x y hx hy hpx hpy
    rw [show TauCeti.diagGL e * (x * y) * (TauCeti.diagGL e)⁻¹ =
      (TauCeti.diagGL e * x * (TauCeti.diagGL e)⁻¹) *
        (TauCeti.diagGL e * y * (TauCeti.diagGL e)⁻¹) by group]
    exact Subgroup.mul_mem _ hpx hpy
  · intro x hx hpx
    rw [show TauCeti.diagGL e * x⁻¹ * (TauCeti.diagGL e)⁻¹ =
      (TauCeti.diagGL e * x * (TauCeti.diagGL e)⁻¹)⁻¹ by group]
    exact Subgroup.inv_mem _ hpx

private lemma exists_smul_eq_conj_of_fixed {ζ : Kˣ} (hζ : orderOf ζ = 3)
    {a : Fin d → ZMod 3}
    {φ : MulAut (LargeEvenProj (LargeEvenSUGroup (Fin d) K 2))}
    (hφ : LargeEvenGraphAut (LargeEvenProjMk (LargeEvenSUGroup (Fin d) K 2))
      (fun h h' => (h' : GL (Fin d) K) =
        TauCeti.diagGL (fun i => ζ ^ (a i).val) * (h : GL (Fin d) K) *
          (TauCeti.diagGL (fun i => ζ ^ (a i).val))⁻¹) φ)
    {g : ↥(LargeEvenSUGroup (Fin d) K 2)}
    (hfix : LargeEvenProjMk _ g ∈ TauCeti.fixedSubgroup φ.toMonoidHom) :
    ∃ u : Kˣ, (((TauCeti.diagGL (fun i => ζ ^ (a i).val) * (g : GL (Fin d) K) *
        (TauCeti.diagGL (fun i => ζ ^ (a i).val))⁻¹ : GL (Fin d) K)) :
      Matrix (Fin d) (Fin d) K) = ((g : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *
        ((u : K) • (1 : Matrix (Fin d) (Fin d) K)) := by
  have he : ∀ i, (fun i => ζ ^ (a i).val) i ^ (2 + 1) = 1 := by
    intro i
    show (ζ ^ (a i).val) ^ 3 = 1
    rw [← pow_mul, mul_comm (a i).val 3, pow_mul, (hζ ▸ pow_orderOf_eq_one ζ : ζ ^ 3 = 1), one_pow]
  have hmem := diagGL_mul_mul_inv_mem_largeEvenSUGroup he g.2
  let h' : ↥(LargeEvenSUGroup (Fin d) K 2) := ⟨_, hmem⟩
  have hphi : φ (LargeEvenProjMk _ g) = LargeEvenProjMk _ h' := hφ g h' rfl
  have hmk : LargeEvenProjMk _ h' = LargeEvenProjMk _ g := by
    rw [← hphi]
    exact TauCeti.mem_fixedSubgroup.mp hfix
  let N : Subgroup ↥(LargeEvenSUGroup (Fin d) K 2) :=
    (LargeEvenScalars (Fin d) K).subgroupOf (LargeEvenSUGroup (Fin d) K 2)
  have hmk_q : QuotientGroup.mk (s := N) h' = QuotientGroup.mk (s := N) g := by
    simpa only [LargeEvenProjMk, QuotientGroup.mk'_apply] using hmk
  obtain ⟨u, hu⟩ := (CFSG.Open.StatedAPI.statedProj_mk_eq_iff
    (LargeEvenSUGroup (Fin d) K 2) g h').mp hmk_q.symm
  exact ⟨u, hu⟩

private lemma scalar_eq_of_conj_eq {ζ : Kˣ}
    {a : Fin d → ZMod 3} {g : ↥(LargeEvenSUGroup (Fin d) K 2)} {u : Kˣ}
    {σ : Equiv.Perm (Fin d)}
    (hσ : ∀ i, ((g : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) (σ i) i ≠ 0)
    (hconj : (((TauCeti.diagGL (fun i => ζ ^ (a i).val) * (g : GL (Fin d) K) *
        (TauCeti.diagGL (fun i => ζ ^ (a i).val))⁻¹ : GL (Fin d) K)) :
      Matrix (Fin d) (Fin d) K) = ((g : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *
        ((u : K) • (1 : Matrix (Fin d) (Fin d) K))) :
    ∀ i, u = (fun i => ζ ^ (a i).val) (σ i) * ((fun i => ζ ^ (a i).val) i)⁻¹ := by
  let e : Fin d → Kˣ := fun i => ζ ^ (a i).val
  change (((TauCeti.diagGL e * (g : GL (Fin d) K) * (TauCeti.diagGL e)⁻¹ :
      GL (Fin d) K)) : Matrix (Fin d) (Fin d) K) = ((g : GL (Fin d) K) :
        Matrix (Fin d) (Fin d) K) * ((u : K) • (1 : Matrix (Fin d) (Fin d) K)) at hconj
  have hc : ∀ i, u = e (σ i) * (e i)⁻¹ := by
    intro i
    have h := congrFun (congrFun hconj (σ i)) i
    rw [diagGL_mul_mul_inv_apply] at h
    simp only [Matrix.mul_smul, Matrix.mul_one, Matrix.smul_apply, smul_eq_mul] at h
    have h2 : ((e (σ i) : K) * ((e i : K))⁻¹) *
        ((g : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) (σ i) i =
        (u : K) * ((g : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) (σ i) i := by
      linear_combination h
    apply Units.ext
    rw [Units.val_mul, Units.val_inv_eq_inv_val]
    exact (mul_right_cancel₀ (hσ i) h2).symm
  exact hc

private lemma pair_of_scalar {ζ : Kˣ} (hζ : orderOf ζ = 3) {a : Fin d → ZMod 3} {u : Kˣ}
    {σ : Equiv.Perm (Fin d)}
    (hc : ∀ i, u = (fun i => ζ ^ (a i).val) (σ i) * ((fun i => ζ ^ (a i).val) i)⁻¹) :
    ∀ i j, a (σ i) + a j = a (σ j) + a i := by
  let e : Fin d → Kˣ := fun i => ζ ^ (a i).val
  change ∀ i, u = e (σ i) * (e i)⁻¹ at hc
  have heq_unit : ∀ i, e (σ i) = u * e i := by
    intro i
    rw [hc i, mul_assoc, inv_mul_cancel, mul_one]
  intro i j
  have hpow : ζ ^ ((a (σ i)).val + (a j).val) = ζ ^ ((a (σ j)).val + (a i).val) := by
    rw [pow_add, pow_add]
    have h2 : e (σ i) * e j = e (σ j) * e i := by
      rw [heq_unit i, heq_unit j, mul_right_comm]
    simpa only [e] using h2
  have h := (pow_eq_pow_iff_zmod3 hζ).mp hpow
  rw [Nat.cast_add, Nat.cast_add, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val,
    ZMod.natCast_zmod_val, ZMod.natCast_zmod_val] at h
  exact h

private lemma a_comp_perm_eq_of_pair {a : Fin d → ZMod 3} {t : ZMod 3} {I : Finset (Fin d)}
    (hI : ∀ i, i ∈ I ↔ a i = t) (hd : d < 2 * I.card) {σ : Equiv.Perm (Fin d)}
    (hpair : ∀ i j, a (σ i) + a j = a (σ j) + a i) :
    ∀ i, a (σ i) = a i := by
  have hIpos : 0 < I.card := by
    have hle : I.card ≤ d := by simpa using Finset.card_le_univ I
    omega
  obtain ⟨i0, hi0⟩ := Finset.card_pos.mp hIpos
  let s : ZMod 3 := a (σ i0) - a i0
  have hs : ∀ i, a (σ i) = a i + s := by
    intro i
    have h := hpair i i0
    dsimp only [s]
    linear_combination h
  by_cases hs0 : s = 0
  · intro i
    rw [hs i, hs0, add_zero]
  · exfalso
    let J : Finset (Fin d) := Finset.univ.filter (fun i => a i = t + s)
    have hJ : ∀ i, i ∈ J ↔ a i = t + s := fun i => by simp [J]
    have hIJ : I.card ≤ J.card := by
      refine Finset.card_le_card_of_injOn σ ?_ ?_
      · intro i hi
        change σ i ∈ J
        rw [hJ, hs i, (hI i).1 hi]
      · intro i _ j _ hij
        exact σ.injective hij
    have hdisj : Disjoint I J := by
      rw [Finset.disjoint_left]
      intro i hi hiJ
      apply hs0
      have h1 : a i = t := (hI i).1 hi
      have h2 : a i = t + s := (hJ i).1 hiJ
      have hts : t + s = t := by rw [← h2, h1]
      simpa using (add_left_cancel (show t + s = t + 0 by simpa using hts))
    have hunion : (I ∪ J).card = I.card + J.card := Finset.card_union_of_disjoint hdisj
    have hle : (I ∪ J).card ≤ d := by
      simpa using Finset.card_le_univ (I ∪ J)
    have h2 : 2 * I.card ≤ d := by omega
    omega

private lemma offdiag_zero_of_conj_eq_one {ζ : Kˣ} (hζ : orderOf ζ = 3)
    {a : Fin d → ZMod 3} {g : ↥(LargeEvenSUGroup (Fin d) K 2)} {u : Kˣ}
    {σ : Equiv.Perm (Fin d)} (i0 : Fin d)
    (hsa : ∀ i, a (σ i) = a i)
    (hc : ∀ i, u = (fun i => ζ ^ (a i).val) (σ i) * ((fun i => ζ ^ (a i).val) i)⁻¹)
    (hconj : (((TauCeti.diagGL (fun i => ζ ^ (a i).val) * (g : GL (Fin d) K) *
        (TauCeti.diagGL (fun i => ζ ^ (a i).val))⁻¹ : GL (Fin d) K)) :
      Matrix (Fin d) (Fin d) K) = ((g : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *
        ((u : K) • (1 : Matrix (Fin d) (Fin d) K))) :
    ∀ i j, a i ≠ a j → ((g : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) i j = 0 := by
  let e : Fin d → Kˣ := fun i => ζ ^ (a i).val
  change ∀ i, u = e (σ i) * (e i)⁻¹ at hc
  change (((TauCeti.diagGL e * (g : GL (Fin d) K) * (TauCeti.diagGL e)⁻¹ : GL (Fin d) K)) :
      Matrix (Fin d) (Fin d) K) = ((g : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *
        ((u : K) • (1 : Matrix (Fin d) (Fin d) K)) at hconj
  have hu1 : u = 1 := by
    have h := hc i0
    simp only [e] at h
    rw [hsa i0, mul_inv_cancel] at h
    exact h
  have hconj1 : (((TauCeti.diagGL e * (g : GL (Fin d) K) * (TauCeti.diagGL e)⁻¹ :
      GL (Fin d) K)) : Matrix (Fin d) (Fin d) K) =
      ((g : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) := by
    have h := hconj
    rw [hu1] at h
    simpa using h
  intro i j hab
  have hene : e i ≠ e j := by
    intro heq
    apply hab
    change ζ ^ (a i).val = ζ ^ (a j).val at heq
    have h := (pow_eq_pow_iff_zmod3 hζ).mp heq
    rwa [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val] at h
  have hentry := congrFun (congrFun hconj1 i) j
  rw [diagGL_mul_mul_inv_apply] at hentry
  have hcoef : (e i : K) * ((e j : K))⁻¹ - 1 ≠ 0 := by
    intro hcoef0
    apply hene
    apply Units.ext
    have h1 : (e i : K) * ((e j : K))⁻¹ = 1 := sub_eq_zero.mp hcoef0
    have h2 : (e i : K) = (e j : K) := by
      calc (e i : K) = (e i : K) * ((e j : K))⁻¹ * (e j : K) := by
            rw [mul_assoc, inv_mul_cancel₀ (Units.ne_zero (e j)), mul_one]
        _ = (e j : K) := by rw [h1, one_mul]
    exact h2
  have hmul : ((e i : K) * ((e j : K))⁻¹ - 1) *
      ((g : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) i j = 0 := by
    linear_combination hentry
  exact (mul_eq_zero.mp hmul).resolve_left hcoef

private lemma fixed_of_offdiag_zero {ζ : Kˣ} (hζ : orderOf ζ = 3)
    {a : Fin d → ZMod 3}
    {φ : MulAut (LargeEvenProj (LargeEvenSUGroup (Fin d) K 2))}
    (hφ : LargeEvenGraphAut (LargeEvenProjMk (LargeEvenSUGroup (Fin d) K 2))
      (fun h h' => (h' : GL (Fin d) K) =
        TauCeti.diagGL (fun i => ζ ^ (a i).val) * (h : GL (Fin d) K) *
          (TauCeti.diagGL (fun i => ζ ^ (a i).val))⁻¹) φ)
    {g : ↥(LargeEvenSUGroup (Fin d) K 2)}
    (hg : ∀ i j, a i ≠ a j → ((g : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) i j = 0) :
    LargeEvenProjMk _ g ∈ TauCeti.fixedSubgroup φ.toMonoidHom := by
  let e : Fin d → Kˣ := fun i => ζ ^ (a i).val
  have he : ∀ i, e i ^ (2 + 1) = 1 := by
    intro i
    show (ζ ^ (a i).val) ^ 3 = 1
    rw [← pow_mul, mul_comm (a i).val 3, pow_mul, (hζ ▸ pow_orderOf_eq_one ζ : ζ ^ 3 = 1), one_pow]
  have hmem : TauCeti.diagGL e * (g : GL (Fin d) K) * (TauCeti.diagGL e)⁻¹ ∈
      LargeEvenSUGroup (Fin d) K 2 := diagGL_mul_mul_inv_mem_largeEvenSUGroup he g.2
  let h' : ↥(LargeEvenSUGroup (Fin d) K 2) := ⟨_, hmem⟩
  have hsub : h' = g := by
    apply Subtype.ext
    apply Units.ext
    ext i j
    change (((TauCeti.diagGL e * (g : GL (Fin d) K) * (TauCeti.diagGL e)⁻¹ : GL (Fin d) K) :
      Matrix (Fin d) (Fin d) K)) i j = ((g : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) i j
    by_cases hij : a i = a j
    · have heij : e i = e j := by simp only [e, hij]
      rw [diagGL_mul_mul_inv_apply, heij, mul_assoc, mul_comm _ ((e j : K))⁻¹, ← mul_assoc,
        mul_inv_cancel₀ (Units.ne_zero (e j)), one_mul]
    · rw [diagGL_mul_mul_inv_apply, hg i j hij]
      simp
  calc φ (LargeEvenProjMk _ g) = LargeEvenProjMk _ h' := hφ g h' rfl
    _ = LargeEvenProjMk _ g := by rw [hsub]

theorem mkProj_mem_fixedSubgroup_iff {ζ : Kˣ} (hζ : orderOf ζ = 3)
    {a : Fin d → ZMod 3} {t : ZMod 3} {I : Finset (Fin d)} (hI : ∀ i, i ∈ I ↔ a i = t)
    (hd : d < 2 * I.card)
    {φ : MulAut (LargeEvenProj (LargeEvenSUGroup (Fin d) K 2))}
    (hφ : LargeEvenGraphAut (LargeEvenProjMk (LargeEvenSUGroup (Fin d) K 2))
      (fun h h' => (h' : GL (Fin d) K) =
        TauCeti.diagGL (fun i => ζ ^ (a i).val) * (h : GL (Fin d) K) *
          (TauCeti.diagGL (fun i => ζ ^ (a i).val))⁻¹) φ)
    (g : ↥(LargeEvenSUGroup (Fin d) K 2)) :
    LargeEvenProjMk _ g ∈ TauCeti.fixedSubgroup φ.toMonoidHom ↔
      ∀ i j, a i ≠ a j → ((g : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) i j = 0 := by
  classical
  constructor
  · intro hfix
    obtain ⟨u, hconj⟩ := exists_smul_eq_conj_of_fixed hζ hφ hfix
    have hdetne : ((g : GL (Fin d) K) : Matrix (Fin d) (Fin d) K).det ≠ 0 :=
      Matrix.GeneralLinearGroup.det_ne_zero (g : GL (Fin d) K)
    obtain ⟨σ, hσ⟩ := exists_perm_ne_zero_of_det_ne_zero hdetne
    have hc := scalar_eq_of_conj_eq hσ hconj
    have hsa := a_comp_perm_eq_of_pair hI hd (pair_of_scalar hζ hc)
    have hIpos : 0 < I.card := by
      have hle : I.card ≤ d := by simpa using Finset.card_le_univ I
      omega
    obtain ⟨i0, -⟩ := Finset.card_pos.mp hIpos
    exact offdiag_zero_of_conj_eq_one hζ i0 hsa hc hconj
  · intro hg0
    exact fixed_of_offdiag_zero hζ hφ hg0

theorem suBlock_le_fixedSubgroup (hK : Nat.card K = 4) {ζ : Kˣ} (hζ : orderOf ζ = 3)
    {a : Fin d → ZMod 3} {t : ZMod 3} {I : Finset (Fin d)} (hI : ∀ i, i ∈ I ↔ a i = t)
    {φ : MulAut (LargeEvenProj (LargeEvenSUGroup (Fin d) K 2))}
    (hφ : LargeEvenGraphAut (LargeEvenProjMk (LargeEvenSUGroup (Fin d) K 2))
      (fun h h' => (h' : GL (Fin d) K) =
        TauCeti.diagGL (fun i => ζ ^ (a i).val) * (h : GL (Fin d) K) *
          (TauCeti.diagGL (fun i => ζ ^ (a i).val))⁻¹) φ) :
    suBlock hK I ≤ TauCeti.fixedSubgroup φ.toMonoidHom := by
  intro x hx
  obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp hx
  have hg0 : ∀ i j, a i ≠ a j → ((g : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) i j = 0 := by
    intro i j hab
    have hij : i ≠ j := fun h => hab (by rw [h])
    have hnot : i ∉ I ∨ j ∉ I := by
      by_cases hi : i ∈ I
      · right
        intro hj
        exact hab ((hI i).1 hi |>.trans ((hI j).1 hj).symm)
      · exact Or.inl hi
    have h := (mem_unitaryBlock (h := (⟨Nat.prime_two, le_rfl, hK⟩ :
      UnitaryFieldData 2 1 K))).1 hg i j hnot
    rwa [Matrix.one_apply_ne hij] at h
  exact fixed_of_offdiag_zero hζ hφ hg0

end CFSG.StandardType.FrameRoute.UnitaryModel
