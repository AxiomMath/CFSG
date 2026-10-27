module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKZ3Def
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.LinearAlgebra.Matrix.CharP
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.Algebra.Polynomial.SpecificDegree
public import TauCeti.LinearAlgebra.Matrix.Commute

public section

open scoped Polynomial

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

private def s16kR2 : Matrix (Fin 2) (Fin 2) (ZMod 2) := !![0, 1; 1, 1]

private def s16kOmegaMat : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  s16kBlockMat 0 * s16kBlockMat 1 * s16kBlockMat 2

private lemma s16kR2_sq : s16kR2 * s16kR2 = s16kR2 + 1 := by
  decide

private lemma s16kR2_notScalar : s16kR2 ∉ Set.range (Matrix.scalar (Fin 2)) := by
  rw [TauCeti.mem_range_scalar_fin_two_iff]
  decide

private lemma s16kBlockMat_cube (i : Fin 3) :
    s16kBlockMat i * s16kBlockMat i * s16kBlockMat i = 1 := by
  fin_cases i <;> decide

private lemma s16kBlockMat_isUnit (i : Fin 3) : IsUnit (s16kBlockMat i) := by
  refine ⟨⟨s16kBlockMat i, s16kBlockMat i * s16kBlockMat i, ?_, ?_⟩, rfl⟩
  · rw [← mul_assoc, s16kBlockMat_cube]
  · rw [s16kBlockMat_cube]

private lemma s16kOmegaMat_isUnit : IsUnit s16kOmegaMat := by
  unfold s16kOmegaMat
  exact ((s16kBlockMat_isUnit 0).mul (s16kBlockMat_isUnit 1)).mul (s16kBlockMat_isUnit 2)

private noncomputable def s16kOmegaUnit : S16kGL6 := s16kOmegaMat_isUnit.unit

private lemma s16kOmegaUnit_spec :
    (s16kOmegaUnit : Matrix (Fin 6) (Fin 6) (ZMod 2)) = s16kOmegaMat :=
  IsUnit.unit_spec _

private lemma s16kOmegaUnit_mem : s16kOmegaUnit ∈ s16kScal :=
  Subgroup.subset_closure s16kOmegaUnit_spec

private abbrev s16kC : Subgroup S16kGL6 :=
  Subgroup.centralizer (s16kScal : Set S16kGL6)

private lemma s16k_comm_of_mem (g : S16kGL6) (hg : g ∈ s16kC) :
    (g : Matrix (Fin 6) (Fin 6) (ZMod 2)) * s16kOmegaMat =
      s16kOmegaMat * (g : Matrix (Fin 6) (Fin 6) (ZMod 2)) := by
  have hmem : s16kOmegaUnit * g = g * s16kOmegaUnit :=
    (Subgroup.mem_centralizer_iff.mp hg) s16kOmegaUnit s16kOmegaUnit_mem
  have hmat : s16kOmegaMat * (g : Matrix (Fin 6) (Fin 6) (ZMod 2)) =
      (g : Matrix (Fin 6) (Fin 6) (ZMod 2)) * s16kOmegaMat := by
    have := congrArg (fun u : S16kGL6 => (u : Matrix (Fin 6) (Fin 6) (ZMod 2))) hmem
    simpa [s16kOmegaUnit_spec] using this
  exact hmat.symm

private noncomputable def s16kE :
    Matrix (Fin 3) (Fin 3) (Matrix (Fin 2) (Fin 2) (ZMod 2)) ≃+*
      Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  (Matrix.compRingEquiv (Fin 3) (Fin 2) (ZMod 2)).trans
    (Matrix.reindexRingEquiv (ZMod 2) finProdFinEquiv)

private lemma s16kOmega_block :
    s16kE.symm s16kOmegaMat = Matrix.diagonal (fun _ : Fin 3 => s16kR2) := by
  have hd : s16kE (Matrix.diagonal (fun _ : Fin 3 => s16kR2)) = s16kOmegaMat := by
    decide
  rw [← hd]
  simp

private noncomputable def s16kPoly : (ZMod 2)[X] := Polynomial.X ^ 2 + Polynomial.X + 1

private lemma s16kPoly_natDegree : s16kPoly.natDegree = 2 := by
  unfold s16kPoly
  compute_degree!

private lemma s16kPoly_monic : s16kPoly.Monic := by
  unfold s16kPoly
  monicity!

private lemma s16kPoly_irreducible : Irreducible s16kPoly := by
  refine Polynomial.irreducible_of_degree_le_three_of_not_isRoot (K := ZMod 2) (p := s16kPoly) ?_ ?_
  · rw [s16kPoly_natDegree]
    norm_num
  · intro x
    have hx : x = 0 ∨ x = 1 := by revert x; decide
    rcases hx with rfl | rfl <;> simp [Polynomial.IsRoot, s16kPoly] <;> decide

private instance s16kFact : Fact (Irreducible s16kPoly) := ⟨s16kPoly_irreducible⟩

private abbrev s16kF : Type := AdjoinRoot s16kPoly

private noncomputable instance s16kFintype : Fintype s16kF :=
  Fintype.ofEquiv (Fin (AdjoinRoot.powerBasis' s16kPoly_monic).dim →₀ ZMod 2)
    (AdjoinRoot.powerBasis' s16kPoly_monic).basis.repr.toEquiv.symm

private lemma s16k_natCard_F : Nat.card s16kF = 4 := by
  rw [Nat.card_congr (AdjoinRoot.powerBasis' s16kPoly_monic).basis.repr.toEquiv,
    Nat.card_eq_fintype_card, Fintype.card_finsupp, Fintype.card_fin, ZMod.card,
    AdjoinRoot.powerBasis'_dim, s16kPoly_natDegree]
  norm_num

private lemma s16k_card_F : Fintype.card s16kF = 4 := by
  rw [← Nat.card_eq_fintype_card]
  exact s16k_natCard_F

private def s16kComm : Subalgebra (ZMod 2) (Matrix (Fin 2) (Fin 2) (ZMod 2)) :=
  Subalgebra.centralizer (ZMod 2) {s16kR2}

private def s16kCommVal : s16kComm →+* Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  Subalgebra.val s16kComm

private lemma s16kCommVal_injective : Function.Injective s16kCommVal :=
  Subtype.val_injective

private lemma s16k_mem_comm_iff (z : Matrix (Fin 2) (Fin 2) (ZMod 2)) :
    z ∈ s16kComm ↔ ∀ g ∈ ({s16kR2} : Set (Matrix (Fin 2) (Fin 2) (ZMod 2))),
      g * z = z * g := by
  rw [s16kComm]
  exact Subalgebra.mem_centralizer_iff (ZMod 2)

private lemma s16k_commute_of_mem (z : s16kComm) :
    Commute s16kR2 (z : Matrix (Fin 2) (Fin 2) (ZMod 2)) :=
  (s16k_mem_comm_iff (z : Matrix (Fin 2) (Fin 2) (ZMod 2))).mp z.2 s16kR2
    (Set.mem_singleton s16kR2)

private instance s16kCommNontrivial : Nontrivial s16kComm :=
  ⟨0, 1, fun h => zero_ne_one (α := Matrix (Fin 2) (Fin 2) (ZMod 2))
    (congrArg (fun z : s16kComm => (z : Matrix (Fin 2) (Fin 2) (ZMod 2))) h)⟩

private instance s16kCommIsMulCommutative : IsMulCommutative s16kComm :=
  IsMulCommutative.of_comm fun a b => by
    apply s16kCommVal_injective
    rw [map_mul, map_mul]
    exact TauCeti.commute_of_commute_fin_two s16kR2_notScalar
      (s16k_commute_of_mem a) (s16k_commute_of_mem b)

open scoped IsMulCommutative in
private noncomputable instance s16kCommCommRing : CommRing s16kComm := inferInstance

private lemma s16kR2_mem : s16kR2 ∈ s16kComm := by
  rw [s16k_mem_comm_iff]
  intro g hg
  rw [Set.mem_singleton_iff] at hg
  subst hg
  rfl

private lemma s16kPoly_eval₂_R2 :
    s16kPoly.eval₂ (algebraMap (ZMod 2) (Matrix (Fin 2) (Fin 2) (ZMod 2))) s16kR2 = 0 := by
  simp only [s16kPoly, Polynomial.eval₂_add, Polynomial.eval₂_X_pow, Polynomial.eval₂_X,
    Polynomial.eval₂_one]
  rw [pow_two, s16kR2_sq]
  have h : (s16kR2 + 1) + s16kR2 + 1 = (s16kR2 + 1) + (s16kR2 + 1) := by abel
  rw [h, CharTwo.add_self_eq_zero]

private lemma s16k_val_eval₂ (p : (ZMod 2)[X]) (x : s16kComm) :
    ((p.eval₂ (algebraMap (ZMod 2) s16kComm) x : s16kComm) :
        Matrix (Fin 2) (Fin 2) (ZMod 2)) =
      p.eval₂ (algebraMap (ZMod 2) (Matrix (Fin 2) (Fin 2) (ZMod 2)))
        (x : Matrix (Fin 2) (Fin 2) (ZMod 2)) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [Polynomial.eval₂_add, Subalgebra.coe_add, hp, hq]
  | monomial n a =>
      simp only [Polynomial.eval₂_monomial, Subalgebra.coe_mul, Subalgebra.coe_pow,
        Subalgebra.coe_algebraMap]

private lemma s16kR2_eval :
    s16kPoly.eval₂ (algebraMap (ZMod 2) s16kComm)
      (⟨s16kR2, s16kR2_mem⟩ : s16kComm) = 0 := by
  apply Subtype.ext
  rw [s16k_val_eval₂, Subalgebra.coe_zero]
  simpa using s16kPoly_eval₂_R2

private noncomputable def s16kPsi : s16kF →+* s16kComm :=
  AdjoinRoot.lift (f := s16kPoly) (algebraMap (ZMod 2) s16kComm)
    (⟨s16kR2, s16kR2_mem⟩ : s16kComm) s16kR2_eval

private lemma s16kPsi_injective : Function.Injective s16kPsi :=
  RingHom.injective s16kPsi

private lemma s16kPsi_of (a : ZMod 2) :
    s16kPsi ((AdjoinRoot.of s16kPoly) a) = algebraMap (ZMod 2) s16kComm a := by
  unfold s16kPsi
  exact AdjoinRoot.lift_of s16kR2_eval

private lemma s16kPsi_root :
    s16kPsi (AdjoinRoot.root s16kPoly) = (⟨s16kR2, s16kR2_mem⟩ : s16kComm) := by
  show AdjoinRoot.lift (f := s16kPoly) (algebraMap (ZMod 2) s16kComm)
    (⟨s16kR2, s16kR2_mem⟩ : s16kComm) s16kR2_eval (AdjoinRoot.root s16kPoly) =
      (⟨s16kR2, s16kR2_mem⟩ : s16kComm)
  exact AdjoinRoot.lift_root (f := s16kPoly) (i := algebraMap (ZMod 2) s16kComm)
    (a := (⟨s16kR2, s16kR2_mem⟩ : s16kComm)) (h := s16kR2_eval)

private lemma s16kPsi_surjective : Function.Surjective s16kPsi := by
  intro B
  have hB : Commute s16kR2 (B : Matrix (Fin 2) (Fin 2) (ZMod 2)) :=
    (s16k_mem_comm_iff (B : Matrix (Fin 2) (Fin 2) (ZMod 2))).mp B.2 s16kR2
      (Set.mem_singleton s16kR2)
  obtain ⟨a, b, hab⟩ := (TauCeti.commute_fin_two_iff s16kR2_notScalar).mp hB
  have hab' : (B : Matrix (Fin 2) (Fin 2) (ZMod 2)) =
      a • (1 : Matrix (Fin 2) (Fin 2) (ZMod 2)) + b • s16kR2 := by
    rw [hab, Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal]
  refine ⟨(AdjoinRoot.of s16kPoly) a + (AdjoinRoot.of s16kPoly) b *
    AdjoinRoot.root s16kPoly, ?_⟩
  apply Subtype.ext
  rw [map_add, map_mul, s16kPsi_of, s16kPsi_of, s16kPsi_root]
  change algebraMap (ZMod 2) (Matrix (Fin 2) (Fin 2) (ZMod 2)) a +
      algebraMap (ZMod 2) (Matrix (Fin 2) (Fin 2) (ZMod 2)) b * s16kR2 =
    (B : Matrix (Fin 2) (Fin 2) (ZMod 2))
  rw [hab', Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, Matrix.smul_mul,
    Matrix.one_mul]

private noncomputable def s16kPsiEquiv : s16kF ≃+* s16kComm :=
  RingEquiv.ofBijective s16kPsi ⟨s16kPsi_injective, s16kPsi_surjective⟩

private noncomputable def s16kToF : s16kComm →+* s16kF :=
  s16kPsiEquiv.symm.toRingHom

private lemma s16kToF_injective : Function.Injective s16kToF :=
  s16kPsiEquiv.symm.injective

private noncomputable def s16kBlocks (g : S16kGL6)
    (hg : (g : Matrix (Fin 6) (Fin 6) (ZMod 2)) * s16kOmegaMat =
      s16kOmegaMat * (g : Matrix (Fin 6) (Fin 6) (ZMod 2))) :
    Matrix (Fin 3) (Fin 3) s16kComm :=
  Matrix.of fun i j => ⟨(s16kE.symm (g : Matrix (Fin 6) (Fin 6) (ZMod 2))) i j, by
    rw [s16k_mem_comm_iff]
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    have h1 : s16kE.symm ((g : Matrix (Fin 6) (Fin 6) (ZMod 2)) * s16kOmegaMat) =
        s16kE.symm (s16kOmegaMat * (g : Matrix (Fin 6) (Fin 6) (ZMod 2))) := by
      rw [hg]
    rw [map_mul, map_mul, s16kOmega_block] at h1
    have hij := congrFun (congrFun h1 i) j
    simp only [Matrix.mul_diagonal, Matrix.diagonal_mul] at hij
    exact hij.symm⟩

private lemma s16kBlocks_val (g : S16kGL6)
    (hg : (g : Matrix (Fin 6) (Fin 6) (ZMod 2)) * s16kOmegaMat =
      s16kOmegaMat * (g : Matrix (Fin 6) (Fin 6) (ZMod 2))) :
    (s16kBlocks g hg).map s16kCommVal =
      s16kE.symm (g : Matrix (Fin 6) (Fin 6) (ZMod 2)) := by
  ext i j
  rfl

private lemma s16kBlocks_mul (g h : S16kGL6)
    (hg : (g : Matrix (Fin 6) (Fin 6) (ZMod 2)) * s16kOmegaMat =
      s16kOmegaMat * (g : Matrix (Fin 6) (Fin 6) (ZMod 2)))
    (hh : (h : Matrix (Fin 6) (Fin 6) (ZMod 2)) * s16kOmegaMat =
      s16kOmegaMat * (h : Matrix (Fin 6) (Fin 6) (ZMod 2)))
    (hgh : ((g * h : S16kGL6) : Matrix (Fin 6) (Fin 6) (ZMod 2)) * s16kOmegaMat =
      s16kOmegaMat * ((g * h : S16kGL6) : Matrix (Fin 6) (Fin 6) (ZMod 2))) :
    s16kBlocks (g * h) hgh = s16kBlocks g hg * s16kBlocks h hh := by
  apply Matrix.map_injective (f := s16kCommVal) s16kCommVal_injective
  change (s16kBlocks (g * h) hgh).map s16kCommVal =
    (s16kBlocks g hg * s16kBlocks h hh).map s16kCommVal
  rw [Matrix.map_mul, s16kBlocks_val, s16kBlocks_val, s16kBlocks_val, Units.val_mul, map_mul]

private noncomputable def s16kBM (g : s16kC) : Matrix (Fin 3) (Fin 3) s16kF :=
  RingHom.mapMatrix s16kToF
    (s16kBlocks (g : S16kGL6) (s16k_comm_of_mem (g : S16kGL6) g.2))

private lemma s16kBM_one : s16kBM (1 : s16kC) = 1 := by
  simp only [s16kBM]
  have hb : s16kBlocks (1 : S16kGL6) (s16k_comm_of_mem 1 (Subgroup.one_mem s16kC)) = 1 := by
    apply Matrix.ext
    intro i j
    apply Subtype.ext
    ext a b
    fin_cases i <;> fin_cases j <;>
      simp [s16kBlocks, Matrix.one_apply, Subalgebra.coe_one, Subalgebra.coe_zero]
  change RingHom.mapMatrix s16kToF (s16kBlocks (1 : S16kGL6) _) = 1
  rw [hb, map_one]

private lemma s16kBM_mul (g h : s16kC) : s16kBM (g * h) = s16kBM g * s16kBM h := by
  simp only [s16kBM]
  change RingHom.mapMatrix s16kToF
      (s16kBlocks ((g : S16kGL6) * (h : S16kGL6)) _) =
    RingHom.mapMatrix s16kToF (s16kBlocks (g : S16kGL6) _) *
      RingHom.mapMatrix s16kToF (s16kBlocks (h : S16kGL6) _)
  rw [s16kBlocks_mul, map_mul]

private noncomputable def s16kBMHom : s16kC →* Matrix (Fin 3) (Fin 3) s16kF where
  toFun := s16kBM
  map_one' := s16kBM_one
  map_mul' := s16kBM_mul

private lemma s16kBMHom_injective : Function.Injective s16kBMHom := by
  intro g h hgh
  change s16kBM g = s16kBM h at hgh
  have hblocks : s16kBlocks (g : S16kGL6) (s16k_comm_of_mem (g : S16kGL6) g.2) =
      s16kBlocks (h : S16kGL6) (s16k_comm_of_mem (h : S16kGL6) h.2) := by
    apply Matrix.map_injective (f := s16kToF) s16kToF_injective
    change (s16kBlocks (g : S16kGL6) _).map s16kToF =
      (s16kBlocks (h : S16kGL6) _).map s16kToF
    simpa only [s16kBM, RingHom.mapMatrix_apply] using hgh
  apply Subtype.ext
  apply Units.ext
  have h1 := congrArg (fun M => M.map s16kCommVal) hblocks
  rw [s16kBlocks_val, s16kBlocks_val] at h1
  exact s16kE.symm.injective h1

private lemma s16kBMHom_toHomUnits_injective :
    Function.Injective s16kBMHom.toHomUnits := by
  intro g h hgh
  apply s16kBMHom_injective
  have := congrArg (fun u : (Matrix (Fin 3) (Fin 3) s16kF)ˣ =>
    (u : Matrix (Fin 3) (Fin 3) s16kF)) hgh
  simpa only [MonoidHom.coe_toHomUnits] using this

private lemma s16k_card_GL :
    Nat.card (Matrix.GeneralLinearGroup (Fin 3) s16kF) = 181440 := by
  have h := Matrix.card_GL_field (𝔽 := s16kF) (n := 3)
  rw [h, s16k_card_F]
  norm_num [Fin.prod_univ_three]

theorem s16k_z3_cent_card_dvd :
    Nat.card ↥(Subgroup.centralizer (s16kScal : Set S16kGL6)) ∣ 181440 := by
  have hdvd := Subgroup.card_dvd_of_injective s16kBMHom.toHomUnits
    s16kBMHom_toHomUnits_injective
  rwa [s16k_card_GL] at hdvd

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
