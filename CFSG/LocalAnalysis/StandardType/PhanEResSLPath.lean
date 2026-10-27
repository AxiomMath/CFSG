module

public import CFSG.LocalAnalysis.StandardType.PhanEResChart
public import CFSG.LocalAnalysis.StandardType.PhanEResPanel
public import CFSG.LocalAnalysis.StandardType.PhanEResSLFlag
public import CFSG.LocalAnalysis.StandardType.PhanEChevConj
public import CFSG.LocalAnalysis.StandardType.PhanEFlagCox
public import CFSG.LieType.Steinberg.CentralExt.SLCentrallyClosed
public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagData
public import CFSG.Monster.B.Geometry.InitialIsometryParabolic
public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanEDefs
public import CFSG.LocalAnalysis.StandardType.PhanEChamberIsoOps
public import CFSG.LocalAnalysis.StandardType.PhanEFlagOpp
public import CFSG.LocalAnalysis.StandardType.PhanEFlagPart
public import CFSG.LocalAnalysis.StandardType.PhanELocalProd
public import CFSG.Monster.B.Geometry.ResidueAdj

public section

namespace CFSG.ClassicalInvolution.Phan.PhanE.Res

open Matrix CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.LieType.RootSystem
  CFSG.LieType.Steinberg CFSG.LieType.Chevalley.CosetBuilding CFSG.Monster.B.Geometry
  CFSG.ClassicalInvolution.Phan.PhanE CFSG.ClassicalInvolution.Phan.PhanE.Flag
  CFSG.LieType.Steinberg.CentralExt.SLClosed CFSG.LocalAnalysis.ComponentInitial

@[expose] def pathRoot {r m : ℕ} (e : Fin m → Fin r) (p q : Fin (m + 1)) : Fin r → ℤ :=
  if p < q then ∑ k : Fin m, if p.val ≤ k.val ∧ k.val < q.val then Pi.single (e k) 1 else 0
  else -∑ k : Fin m, if q.val ≤ k.val ∧ k.val < p.val then Pi.single (e k) 1 else 0

variable {K : Type} [Group K] {D : UniversalRootDatum K} {n : Fin D.rank → K}
  {H : Fin D.rank → Subgroup K} {Fld : Type} [Field Fld]

set_option hygiene false in
local notation "W" => (coxeterMatrix D.isFiniteType).Group
set_option hygiene false in
local notation "cs" => (coxeterMatrix D.isFiniteType).toCoxeterSystem

structure SLPath (M : ChevModel2 D n H Fld) (m : ℕ) where
  e : Fin m → Fin D.rank
  inj : Function.Injective e
  cartan : ∀ k l : Fin m, D.cartan (e k) (e l) =
    if k = l then 2 else if k.val + 1 = l.val ∨ l.val + 1 = k.val then -1 else 0
  ε : SpecialLinearGroup (Fin (m + 1)) Fld →* K
  tv_eq : ∀ p q : Fin (m + 1), p ≠ q → ∀ c : Fld, ε (tv Fld p q c) = M.x (pathRoot e p q) c

namespace SLPath

variable {M : ChevModel2 D n H Fld} {m : ℕ}

noncomputable def hmbSL_revMat (m : ℕ) (Fld : Type) [Field Fld] :
    SpecialLinearGroup (Fin (m + 1)) Fld :=
  LinearFlag.signedPermutation (m + 1) Fld (Fin.revPerm)

private lemma hmbSL_revMat_coe (m : ℕ) (Fld : Type) [Field Fld] [CharP Fld 2] :
    ((hmbSL_revMat m Fld : SpecialLinearGroup (Fin (m + 1)) Fld) :
      Matrix (Fin (m + 1)) (Fin (m + 1)) Fld) =
      CFSG.LieType.Universal.SpecialLinear.signedPerm (Fin.revPerm : Equiv.Perm (Fin (m+1)))
        (fun _ => 1) := by
  rw [hmbSL_revMat, LinearFlag.coe_signedPermutation, LinearFlag.signedPermMatrix]
  have hdiag : (diagonal (fun a : Fin (m+1) => if (a : ℕ) = 0 then
      ((Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin (m+1))) : ℤ) : Fld) else 1)) =
      (1 : Matrix (Fin (m+1)) (Fin (m+1)) Fld) := by
    rw [diagonal_eq_one]
    funext a
    split_ifs with ha
    · rcases Int.units_eq_one_or
        (Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin (m+1)))) with h | h <;>
        simp [h, CharTwo.neg_eq]
    · rfl
  rw [hdiag, one_mul]
  ext a b
  rw [LinearFlag.permMatrix_apply,
    CFSG.LieType.Universal.SpecialLinear.signedPerm_apply]

private lemma hmbSL_transpose_tv [CharP Fld 2] (i j : Fin (m+1)) (hij : i ≠ j) (c : Fld) :
    SpecialLinearGroup.transpose (tv Fld i j c) = tv Fld j i c := by
  apply Subtype.ext
  rw [tv_of_ne hij, tv_of_ne hij.symm]
  simp only [SpecialLinearGroup.coe_transpose, SpecialLinearGroup.transvection_coe]
  ext a b
  simp [Matrix.transpose_apply, Matrix.single, Matrix.one_apply, and_comm, eq_comm]

private lemma hmbSL_conj_rev [CharP Fld 2] (i j : Fin (m+1)) (hij : i ≠ j) (c : Fld) :
    hmbSL_revMat m Fld * (SpecialLinearGroup.transpose (tv Fld i j c))⁻¹ *
      (hmbSL_revMat m Fld)⁻¹ = tv Fld (Fin.rev j) (Fin.rev i) c := by
  have hinv : (tv Fld j i c)⁻¹ = tv Fld j i (-c) := by
    rw [tv_of_ne hij.symm, tv_of_ne hij.symm, SpecialLinearGroup.transvection_inv]
  have hsig : (SpecialLinearGroup.transpose (tv Fld i j c))⁻¹ = tv Fld j i c := by
    rw [hmbSL_transpose_tv (m := m) (i := i) (j := j) (hij := hij) (c := c), hinv]
    congr 1
    exact CharTwo.neg_eq c
  rw [hsig, tv_of_ne hij.symm, tv_of_ne (Fin.rev_injective.ne hij).symm]
  have h := CFSG.LieType.Universal.SpecialLinear.conj_transvection_of_coe_eq_signedPerm
    (hmbSL_revMat_coe m Fld) (fun _ => by simp) hij.symm c
  rw [h]
  apply Subtype.ext
  simp [SpecialLinearGroup.transvection_coe]

private lemma hmbSL_transpose_mul (A B : SpecialLinearGroup (Fin (m+1)) Fld) :
    SpecialLinearGroup.transpose (A * B) =
      SpecialLinearGroup.transpose B * SpecialLinearGroup.transpose A := by
  apply Subtype.ext
  simp [SpecialLinearGroup.coe_transpose, Matrix.transpose_mul]

private lemma hmbSL_transpose_one :
    SpecialLinearGroup.transpose (1 : SpecialLinearGroup (Fin (m+1)) Fld) = 1 := by
  apply Subtype.ext
  simp [SpecialLinearGroup.transpose]

noncomputable def hmbSL_rho (m : ℕ) [CharP Fld 2] :
    SpecialLinearGroup (Fin (m + 1)) Fld →* SpecialLinearGroup (Fin (m + 1)) Fld where
  toFun A := hmbSL_revMat m Fld * (SpecialLinearGroup.transpose A)⁻¹ *
    (hmbSL_revMat m Fld)⁻¹
  map_one' := by simp [hmbSL_transpose_one]
  map_mul' A B := by
    simp only [hmbSL_transpose_mul, _root_.mul_inv_rev]
    group

@[simp] private lemma hmbSL_rho_apply [CharP Fld 2]
    (A : SpecialLinearGroup (Fin (m + 1)) Fld) :
    hmbSL_rho m A = hmbSL_revMat m Fld * (SpecialLinearGroup.transpose A)⁻¹ *
      (hmbSL_revMat m Fld)⁻¹ := rfl

private lemma hmbSL_rev_adj {n : ℕ} {k l : Fin n} :
    (k.rev.val + 1 = l.rev.val ∨ l.rev.val + 1 = k.rev.val) ↔
      (k.val + 1 = l.val ∨ l.val + 1 = k.val) := by
  rw [Fin.val_rev, Fin.val_rev]
  omega

private lemma hmbSL_rev_interval (m : ℕ) (a b : Fin (m+1)) (k : Fin m) :
    (a.rev.val ≤ k.val ∧ k.val < b.rev.val) ↔
      (b.val ≤ (k.rev).val ∧ (k.rev).val < a.val) := by
  rw [Fin.val_rev, Fin.val_rev, Fin.val_rev]
  omega

private lemma hmbSL_pathRoot_rev {r m : ℕ} (e : Fin m → Fin r) (p q : Fin (m + 1)) :
    pathRoot e q.rev p.rev = pathRoot (fun k => e k.rev) p q := by
  unfold pathRoot
  by_cases hpq : p < q
  · have hrev : q.rev < p.rev := by rwa [Fin.rev_lt_rev]
    rw [if_pos hrev, if_pos hpq]
    rw [← Equiv.sum_comp (Fin.revPerm (n := m))]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [Fin.rev_rev, Fin.revPerm_apply]
    by_cases h : q.rev.val ≤ k.rev.val ∧ k.rev.val < p.rev.val
    · have h2 : p.val ≤ k.val ∧ k.val < q.val := by
        simpa only [Fin.rev_rev] using (hmbSL_rev_interval m q p k.rev).mp h
      rw [if_pos h, if_pos h2]
    · have h2 : ¬ (p.val ≤ k.val ∧ k.val < q.val) := by
        intro hh
        have hh' : p.val ≤ (k.rev).rev.val ∧ (k.rev).rev.val < q.val := by
          simpa only [Fin.rev_rev] using hh
        exact h ((hmbSL_rev_interval m q p k.rev).mpr hh')
      rw [if_neg h, if_neg h2]
  · have hpq' : ¬ q.rev < p.rev := by
      rw [Fin.rev_lt_rev]
      exact hpq
    rw [if_neg hpq', if_neg hpq, neg_inj]
    rw [← Equiv.sum_comp (Fin.revPerm (n := m))]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [Fin.rev_rev, Fin.revPerm_apply]
    by_cases h : p.rev.val ≤ k.rev.val ∧ k.rev.val < q.rev.val
    · have h2 : q.val ≤ k.val ∧ k.val < p.val := by
        simpa only [Fin.rev_rev] using (hmbSL_rev_interval m p q k.rev).mp h
      rw [if_pos h, if_pos h2]
    · have h2 : ¬ (q.val ≤ k.val ∧ k.val < p.val) := by
        intro hh
        have hh' : q.val ≤ (k.rev).rev.val ∧ (k.rev).rev.val < p.val := by
          simpa only [Fin.rev_rev] using hh
        exact h ((hmbSL_rev_interval m p q k.rev).mpr hh')
      rw [if_neg h, if_neg h2]

@[expose] noncomputable def reverse [CharP Fld 2] (L : SLPath M m) : SLPath M m where
  e k := L.e k.rev
  inj a b h := Fin.rev_injective (L.inj h)
  cartan k l := by
    rw [L.cartan]
    by_cases h : k = l
    · rw [if_pos h, if_pos (by rw [h])]
    · have hrev : k.rev ≠ l.rev := fun hh => h (Fin.rev_injective hh)
      rw [if_neg h, if_neg hrev]
      by_cases hc : k.val + 1 = l.val ∨ l.val + 1 = k.val
      · have hc' : k.rev.val + 1 = l.rev.val ∨ l.rev.val + 1 = k.rev.val :=
          (hmbSL_rev_adj (k := k) (l := l)).mpr hc
        rw [if_pos hc, if_pos hc']
      · have hc' : ¬ (k.rev.val + 1 = l.rev.val ∨ l.rev.val + 1 = k.rev.val) :=
          fun hh => hc ((hmbSL_rev_adj (k := k) (l := l)).mp hh)
        rw [if_neg hc, if_neg hc']
  ε := L.ε.comp (hmbSL_rho (Fld := Fld) m)
  tv_eq p q hpq c := by
    rw [MonoidHom.comp_apply, hmbSL_rho_apply, hmbSL_conj_rev p q hpq c,
      L.tv_eq q.rev p.rev (fun h => hpq (Fin.rev_injective h).symm) c,
      hmbSL_pathRoot_rev]

theorem reverse_e [CharP Fld 2] (L : SLPath M m) (k : Fin m) : L.reverse.e k = L.e k.rev :=
  rfl

end SLPath

private lemma hmbSL_A_apply {m : ℕ} (i j : Fin m) :
    (CoxeterMatrix.A m) i j =
      if i = j then 1 else if i.val + 1 = j.val ∨ j.val + 1 = i.val then 3 else 2 := by
  simp only [CoxeterMatrix.A, Matrix.of_apply]
  by_cases h : i = j
  · simp [h]
  · by_cases ha : i.val + 1 = j.val ∨ j.val + 1 = i.val
    · simp [h, ha, or_comm]
    · simp [h, ha]
      tauto

private lemma hmbSL_coxeter_apply (i j : Fin D.rank) :
    (coxeterMatrix D.isFiniteType) i j =
      TauCeti.coxeterOrder (D.cartan i j * D.cartan j i) := by
  simp only [CFSG.LieType.RootSystem.coxeterMatrix,
    TauCeti.coxeterMatrixOfCartanMatrix_apply]

private lemma hmbSL_coxeter_eq_A {M : ChevModel2 D n H Fld} {m : ℕ} (L : SLPath M m)
    (k l : Fin m) :
    (coxeterMatrix D.isFiniteType) (L.e k) (L.e l) = (CoxeterMatrix.A m) k l := by
  by_cases hkl : k = l
  · subst hkl
    simp [hmbSL_A_apply, hmbSL_coxeter_apply, L.cartan k k]
  · by_cases hadj : k.val + 1 = l.val ∨ l.val + 1 = k.val
    · have h2 : l.val + 1 = k.val ∨ k.val + 1 = l.val := Or.symm hadj
      simp [hmbSL_A_apply, hmbSL_coxeter_apply, L.cartan k l, L.cartan l k, hkl,
        Ne.symm hkl, hadj, h2]
    · have h2 : ¬ (l.val + 1 = k.val ∨ k.val + 1 = l.val) := fun h => hadj (Or.symm h)
      simp [hmbSL_A_apply, hmbSL_coxeter_apply, L.cartan k l, L.cartan l k, hkl,
        Ne.symm hkl, hadj, h2]

private theorem hmbSL_pathLiftable {M : ChevModel2 D n H Fld} {m : ℕ} (L : SLPath M m) :
    (CoxeterMatrix.A m).IsLiftable (fun k => (cs).simple (L.e k)) := by
  intro k l
  by_cases hkl : k = l
  · subst hkl
    rw [hmbSL_A_apply, if_pos rfl]
    exact (cs).simple_mul_simple_self (L.e k)
  · rw [hmbSL_A_apply, if_neg hkl]
    by_cases hadj : k.val + 1 = l.val ∨ l.val + 1 = k.val
    · have hM : (coxeterMatrix D.isFiniteType) (L.e k) (L.e l) = 3 := by
        rw [hmbSL_coxeter_eq_A L k l, hmbSL_A_apply, if_neg hkl, if_pos hadj]
      rw [if_pos hadj, ← hM]
      exact (cs).simple_mul_simple_pow (L.e k) (L.e l)
    · have hM : (coxeterMatrix D.isFiniteType) (L.e k) (L.e l) = 2 := by
        rw [hmbSL_coxeter_eq_A L k l, hmbSL_A_apply, if_neg hkl, if_neg hadj]
      rw [if_neg hadj, ← hM]
      exact (cs).simple_mul_simple_pow (L.e k) (L.e l)

variable (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
  (weylAction D.isFiniteType) D.roots D.rootGroup n H) (hext : SteinbergExtras D n H)
  {M : ChevModel2 D n H Fld} {m : ℕ}

noncomputable def pathWeyl (L : SLPath M m) : Equiv.Perm (Fin (m + 1)) →* W :=
  (symCox m).lift ⟨fun k => (cs).simple (L.e k), hmbSL_pathLiftable L⟩

theorem pathWeyl_simple (L : SLPath M m) (k : Fin m) :
    pathWeyl L ((symCox m).simple k) = (cs).simple (L.e k) := by
  rw [pathWeyl, CoxeterSystem.lift_apply_simple]

theorem pathWeyl_injective (L : SLPath M m) : Function.Injective (pathWeyl L) := by
  classical
  let J : Set (Fin D.rank) := Set.range L.e
  let eL : Fin m ≃ J := Equiv.ofInjective L.e L.inj
  let csJ : CoxeterSystem (parMatrix (coxeterMatrix D.isFiniteType) J)
      (parMatrix (coxeterMatrix D.isFiniteType) J).Group :=
    (parMatrix (coxeterMatrix D.isFiniteType) J).toCoxeterSystem
  let f : Fin m → (parMatrix (coxeterMatrix D.isFiniteType) J).Group :=
    fun k => csJ.simple ⟨L.e k, k, rfl⟩
  have hf : (CoxeterMatrix.A m).IsLiftable f := by
    intro k l
    show (f k * f l) ^ (CoxeterMatrix.A m) k l = 1
    rw [← hmbSL_coxeter_eq_A L k l]
    exact csJ.simple_mul_simple_pow ⟨L.e k, k, rfl⟩ ⟨L.e l, l, rfl⟩
  let φ : Equiv.Perm (Fin (m + 1)) →* (parMatrix (coxeterMatrix D.isFiniteType) J).Group :=
    (symCox m).lift ⟨f, hf⟩
  let g : J → Equiv.Perm (Fin (m + 1)) := fun j => (symCox m).simple (eL.symm j)
  have hgl : (parMatrix (coxeterMatrix D.isFiniteType) J).IsLiftable g := by
    intro j j'
    show (g j * g j') ^ (parMatrix (coxeterMatrix D.isFiniteType) J) j j' = 1
    have hexp : (parMatrix (coxeterMatrix D.isFiniteType) J) j j' =
        (CoxeterMatrix.A m) (eL.symm j) (eL.symm j') := by
      rw [parMatrix_apply]
      rw [show ((j : J) : Fin D.rank) = L.e (eL.symm j) from
        (Equiv.apply_ofInjective_symm L.inj j).symm]
      rw [show ((j' : J) : Fin D.rank) = L.e (eL.symm j') from
        (Equiv.apply_ofInjective_symm L.inj j').symm]
      exact hmbSL_coxeter_eq_A L (eL.symm j) (eL.symm j')
    rw [hexp]
    exact (symCox m).simple_mul_simple_pow (eL.symm j) (eL.symm j')
  let ψ : (parMatrix (coxeterMatrix D.isFiniteType) J).Group →*
      Equiv.Perm (Fin (m + 1)) := csJ.lift ⟨g, hgl⟩
  have hψφ : ψ.comp φ = MonoidHom.id (Equiv.Perm (Fin (m + 1))) := by
    apply (symCox m).ext_simple
    intro k
    show ψ (φ ((symCox m).simple k)) = (symCox m).simple k
    rw [show φ ((symCox m).simple k) = f k from
      CoxeterSystem.lift_apply_simple (symCox m) hf k]
    show ψ (csJ.simple ⟨L.e k, k, rfl⟩) = (symCox m).simple k
    rw [show ψ (csJ.simple ⟨L.e k, k, rfl⟩) = g ⟨L.e k, k, rfl⟩ from
      CoxeterSystem.lift_apply_simple csJ hgl ⟨L.e k, k, rfl⟩]
    show (symCox m).simple (eL.symm ⟨L.e k, k, rfl⟩) = (symCox m).simple k
    rw [show eL.symm ⟨L.e k, k, rfl⟩ = k from Equiv.ofInjective_symm_apply L.inj k]
  have hφinj : Function.Injective φ := by
    have hleft : ∀ x : Equiv.Perm (Fin (m + 1)), ψ (φ x) = x := fun x => by
      simpa using congrArg (fun F : Equiv.Perm (Fin (m + 1)) →*
        Equiv.Perm (Fin (m + 1)) => F x) hψφ
    intro x y hxy
    rw [← hleft x, ← hleft y, hxy]
  have hpath : pathWeyl L =
      (parToGroup (coxeterMatrix D.isFiniteType).toCoxeterSystem J).comp φ := by
    apply (symCox m).ext_simple
    intro k
    rw [pathWeyl_simple L k]
    show (coxeterMatrix D.isFiniteType).toCoxeterSystem.simple (L.e k) =
      parToGroup (coxeterMatrix D.isFiniteType).toCoxeterSystem J
        (φ ((symCox m).simple k))
    rw [show φ ((symCox m).simple k) = f k from
      CoxeterSystem.lift_apply_simple (symCox m) hf k]
    show (coxeterMatrix D.isFiniteType).toCoxeterSystem.simple (L.e k) =
      parToGroup (coxeterMatrix D.isFiniteType).toCoxeterSystem J
        (csJ.simple ⟨L.e k, k, rfl⟩)
    rw [show parToGroup (coxeterMatrix D.isFiniteType).toCoxeterSystem J
        (csJ.simple ⟨L.e k, k, rfl⟩) =
        (coxeterMatrix D.isFiniteType).toCoxeterSystem.simple (L.e k) from by
      rw [show csJ.simple ⟨L.e k, k, rfl⟩ =
        (parMatrix (coxeterMatrix D.isFiniteType) J).simple ⟨L.e k, k, rfl⟩ from rfl]
      rw [parToGroup_simple]]
  rw [hpath]
  exact (parToGroup_injective (coxeterMatrix D.isFiniteType).toCoxeterSystem J).comp hφinj

theorem pathWeyl_mem_parabolic (L : SLPath M m) (w : Equiv.Perm (Fin (m + 1))) :
    pathWeyl L w ∈ (cs).parabolic (Set.range L.e) := by
  obtain ⟨ω, rfl⟩ := (symCox m).wordProd_surjective w
  induction ω with
  | nil => simp
  | cons k ω ih =>
    rw [CoxeterSystem.wordProd_cons, map_mul, pathWeyl_simple]
    exact Subgroup.mul_mem _ ((cs).simple_mem_parabolic ⟨k, rfl⟩) ih

end CFSG.ClassicalInvolution.Phan.PhanE.Res

end
