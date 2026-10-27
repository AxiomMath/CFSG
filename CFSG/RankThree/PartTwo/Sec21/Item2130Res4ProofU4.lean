module

public import CFSG.RankThree.PartTwo.Sec21.Item2130Res4ProofU4Cent
import CFSG.RankThree.PartTwo.Sec9.Item95
public import CFSG.RankThree.GroupTheory.SteinbergBYHyperplaneResidual
public import CFSG.RankThree.PartTwo.Census.Classical.Bridges
public import CFSG.RankThree.PartTwo.Sec21.Item2130Res4ProofU4Wt

public section

namespace CFSG.RankThree.PartTwo.Sec21

open Matrix CFSG CFSG.RankThree CFSG.LieType.BorelTits CFSG.ClassicalGroups.UnitaryFlag
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.RankThree.PartTwo.Sec21.Item224Res6Proof
open CFSG.Assembly.LowTwoRank (StatedSU StatedScalars)
open CFSG.Assembly.RankThreeEven (projSU)

namespace Item2130Res4Proof

section Transport

variable {G : Type} [Group G]

theorem map_conj_centralizer_singleton (P a : G) :
    (Subgroup.centralizer ({a} : Set G)).map (MulAut.conj P).toMonoidHom =
      Subgroup.centralizer ({P * a * P⁻¹} : Set G) := by
  ext y
  rw [Subgroup.mem_map_equiv, Subgroup.mem_centralizer_singleton_iff,
    Subgroup.mem_centralizer_singleton_iff, MulAut.conj_symm_apply]
  constructor
  · intro hy
    calc y * (P * a * P⁻¹) = P * ((P⁻¹ * y * P) * a) * P⁻¹ := by group
      _ = P * (a * (P⁻¹ * y * P)) * P⁻¹ := by rw [hy]
      _ = P * a * P⁻¹ * y := by group
  · intro hy
    calc P⁻¹ * y * P * a = P⁻¹ * (y * (P * a * P⁻¹)) * P := by group
      _ = P⁻¹ * (P * a * P⁻¹ * y) * P := by rw [hy]
      _ = a * (P⁻¹ * y * P) := by group

theorem perfectResidual_centralizer_of_mulEquiv {X Y : Type} [Group X] [Group Y] [Finite X]
    [Finite Y] (e : X ≃* Y) (x : X) {q : ℕ}
    (h1 : e x ∈ inSubgroup perfectResidual (Subgroup.centralizer ({e x} : Set Y)))
    (h2 : Sec4.IsSLThreePiAt
      (inSubgroup perfectResidual (Subgroup.centralizer ({e x} : Set Y))) q) :
    x ∈ inSubgroup perfectResidual (Subgroup.centralizer ({x} : Set X)) ∧
      Sec4.IsSLThreePiAt (inSubgroup perfectResidual (Subgroup.centralizer ({x} : Set X))) q := by
  have hC : (Subgroup.centralizer ({x} : Set X)).map e.toMonoidHom =
      Subgroup.centralizer ({e x} : Set Y) := by
    ext y
    rw [Subgroup.mem_map_equiv, Subgroup.mem_centralizer_singleton_iff,
      Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro hy
      have := congrArg e hy
      simpa using this
    · intro hy
      apply e.injective
      simpa using hy
  have hR : (inSubgroup perfectResidual (Subgroup.centralizer ({x} : Set X))).map e.toMonoidHom =
      inSubgroup perfectResidual (Subgroup.centralizer ({e x} : Set Y)) := by
    rw [GroupTheory.SteinbergBY.map_inSubgroup_perfectResidual_of_injective _ e.injective, hC]
  refine ⟨?_, ?_⟩
  · rw [← hR] at h1
    obtain ⟨z, hz, hzx⟩ := h1
    rwa [show z = x from e.injective hzx] at hz
  · exact Sec9.isSLThreePiAt_of_mulEquiv
      (((Subgroup.equivMapOfInjective _ e.toMonoidHom e.injective).trans
        (MulEquiv.subgroupCongr hR)).symm) h2

theorem perfectResidual_centralizer_of_subtype [Finite G] (S : Subgroup G) (x : S) {q : ℕ}
    (h1 : (x : G) ∈ inSubgroup perfectResidual (S ⊓ Subgroup.centralizer ({(x : G)} : Set G)))
    (h2 : Sec4.IsSLThreePiAt
      (inSubgroup perfectResidual (S ⊓ Subgroup.centralizer ({(x : G)} : Set G))) q) :
    x ∈ inSubgroup perfectResidual (Subgroup.centralizer ({x} : Set S)) ∧
      Sec4.IsSLThreePiAt (inSubgroup perfectResidual (Subgroup.centralizer ({x} : Set S))) q := by
  have hR : (inSubgroup perfectResidual (Subgroup.centralizer ({x} : Set S))).map S.subtype =
      inSubgroup perfectResidual (S ⊓ Subgroup.centralizer ({(x : G)} : Set G)) := by
    rw [GroupTheory.SteinbergBY.map_inSubgroup_perfectResidual_of_injective _
      S.subtype_injective, GroupTheory.SteinbergBY.map_subtype_centralizer_singleton]
  refine ⟨?_, ?_⟩
  · rw [← hR] at h1
    obtain ⟨z, hz, hzx⟩ := h1
    rwa [show z = x from S.subtype_injective hzx] at hz
  · exact Sec9.isSLThreePiAt_of_mulEquiv
      (((Subgroup.equivMapOfInjective _ S.subtype S.subtype_injective).trans
        (MulEquiv.subgroupCongr hR)).symm) h2

end Transport

section Frame

variable {f : ℕ} {K : Type} [Field K] [Finite K] [Fact (Nat.Prime 2)] [CharP K 2]
variable (h : UnitaryFieldData 2 f K)

@[expose] def frameMat (v : Fin 4 → Fin 4 → K) : Matrix (Fin 4) (Fin 4) K :=
  Matrix.of fun r i => v i r

theorem gram_frameMat (v : Fin 4 → Fin 4 → K) :
    ((frameMat v).map h.bar)ᵀ * frameMat v = Matrix.of fun i j => (uF h 4).β (v i) (v j) := by
  ext i j
  rw [Matrix.of_apply, uF_β, Matrix.mul_apply]
  simp only [frameMat, Matrix.transpose_apply, Matrix.map_apply, Matrix.of_apply,
    UnitaryFieldData.bar_apply]

theorem gram_frameMat_eq_one {v : Fin 4 → Fin 4 → K}
    (hv : ∀ i j, (uF h 4).β (v i) (v j) = if i = j then 1 else 0) :
    ((frameMat v).map h.bar)ᵀ * frameMat v = 1 := by
  rw [gram_frameMat]
  ext i j
  rw [Matrix.of_apply, hv, Matrix.one_apply]

@[expose] noncomputable def frameGL {v : Fin 4 → Fin 4 → K}
    (hv : ∀ i j, (uF h 4).β (v i) (v j) = if i = j then 1 else 0) : GL (Fin 4) K where
  val := frameMat v
  inv := ((frameMat v).map h.bar)ᵀ
  val_inv := mul_eq_one_comm.mp (gram_frameMat_eq_one h hv)
  inv_val := gram_frameMat_eq_one h hv

theorem frameGL_mem_uU {v : Fin 4 → Fin 4 → K}
    (hv : ∀ i j, (uF h 4).β (v i) (v j) = if i = j then 1 else 0) : frameGL h hv ∈ uU h 4 := by
  rw [UnitaryHigher.mem_primeFormUnitary, Units.val_one, Matrix.mul_one]
  exact gram_frameMat_eq_one h hv

omit [Finite K] [Fact (Nat.Prime 2)] [CharP K 2] in
theorem conj_mem_uS_iff {P : GL (Fin 4) K} (hP : P ∈ uU h 4) (g : GL (Fin 4) K) :
    g ∈ uS h 4 ↔ P * g * P⁻¹ ∈ uS h 4 := by
  have hdet : ((P * g * P⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).det =
      (g : Matrix (Fin 4) (Fin 4) K).det := by
    rw [Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul, mul_comm, ← mul_assoc,
      ← Matrix.det_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.det_one, one_mul]
  constructor
  · intro hg
    rw [UnitaryHigher.mem_gramSU_iff_unitary] at hg ⊢
    exact ⟨(uU h 4).mul_mem ((uU h 4).mul_mem hP hg.1) ((uU h 4).inv_mem hP),
      hdet.trans hg.2⟩
  · intro hg
    rw [UnitaryHigher.mem_gramSU_iff_unitary] at hg ⊢
    have h1 : P⁻¹ * (P * g * P⁻¹) * P = g := by group
    refine ⟨?_, hdet.symm.trans hg.2⟩
    rw [← h1]
    exact (uU h 4).mul_mem ((uU h 4).mul_mem ((uU h 4).inv_mem hP) hg.1) hP

omit [Finite K] [Fact (Nat.Prime 2)] [CharP K 2] in
theorem map_conj_uS {P : GL (Fin 4) K} (hP : P ∈ uU h 4) :
    (uS h 4).map (MulAut.conj P).toMonoidHom = uS h 4 := by
  apply GroupTheory.SteinbergBY.map_conj_eq_of_mem_normalizer
  rw [Subgroup.mem_normalizer_iff]
  intro g
  rw [conj_mem_uS_iff h hP g]

end Frame

theorem card_galoisField_two_mul' (n : ℕ) (hn : 0 < n) :
    Nat.card (GaloisField 2 (2 * n)) = (2 ^ n) ^ 2 := by
  rw [GaloisField.card 2 (2 * n) (by omega), ← pow_mul, mul_comm]

theorem nonempty_projSU_mulEquiv_uS (n : ℕ) (hn : 0 < n)
    (h : UnitaryFieldData 2 n (GaloisField 2 (2 * n))) :
    Nonempty (projSU 4 2 n ≃* uS h 4) := by
  have hF := card_galoisField_two_mul' n hn
  have hbot : (StatedScalars (Fin 4) (GaloisField 2 (2 * n))).subgroupOf
      (StatedSU 4 (2 ^ n) (GaloisField 2 (2 * n))) = ⊥ := by
    rw [← Subgroup.card_eq_one, (CFSG.LinearGroups.unitary_scalar_kernel Nat.prime_two hF
      (by norm_num)).2.2]
    have hodd : Odd (2 ^ n + 1) := (Nat.even_pow.mpr ⟨even_two, hn.ne'⟩).add_one
    exact Nat.Coprime.pow_left 2 (Nat.coprime_two_left.mpr hodd)
  exact ⟨(MulEquiv.subgroupCongr (Census.projImage_statedSU 4 2 n).symm).trans
    ((Census.statedProjEquivProjImage _).symm.trans
      ((QuotientGroup.quotientMulEquivOfEq hbot).trans
        (QuotientGroup.quotientBot.trans (MulEquiv.subgroupCongr (statedSU_eq_uS h 4)))))⟩

end Item2130Res4Proof

open Item2130Res4Proof

end CFSG.RankThree.PartTwo.Sec21
