module

public import CFSG.LocalAnalysis.WeakClosure81.W183CF
public import CFSG.LocalAnalysis.WeakClosure81.EightFiveDefs
public import CFSG.Quasithin.Background.A3StructureDefs
import CFSG.OddTranspositions.PartFour.ThirteenCompFactor
import CFSG.LocalAnalysis.WeakClosure81.W18ASNineOrthPlus
import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotResidualHigherSLTwo
import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltIb.OmegaPlusTop2
import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltIb.OmegaMinusSmall
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.KGroupProofsC
public import CFSG.LieType.Simplicity.Suzuki
public import CFSG.Quasithin.Vol2.Ch8Sec2L829LN1

public section

namespace CFSG.OddTranspositions.PartFour

open CFSG.Open CFSG.LocalAnalysis.WeakClosure81 CFSG.Quasithin CFSG.Quasithin.H13.L829N
open CFSG.Blueprint (LieModel)
open CFSG.LieType.BorelTits
open CFSG.LieType.Universal.Spin (quadPlus coe_quadPlus quadMinus
  nondegenerate_polarBilin_quadMinus_of_finite)
open CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltIb
open CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltIb.OmegaMinus
  (finrank_minusSpace_small exists_quadMinus_ne_zero_small nonempty_range_equiv_statedOmega)
open CFSG.SeitzReduction.F4Pilot (charP_two_of_natCard_eq_two_pow)

theorem oddTranspFactor_of_mulEquiv {T T' : Type} [Group T] [Group T'] (e : T ≃* T')
    (h : OddTranspFactor T) : OddTranspFactor T' := by
  have hL : ∀ {t : StatedLieTag} {n p f : ℕ}, LieModel T t n p f → LieModel T' t n p f :=
    fun h => h.of_mulEquiv e
  rcases h with ⟨n, hn, ⟨e'⟩⟩ | ⟨n, f, h⟩ | ⟨q, n, f, hq, hf, h⟩ | h | h | h
  · exact Or.inl ⟨n, hn, ⟨e.symm.trans e'⟩⟩
  · exact Or.inr (Or.inl ⟨n, f, h.imp hL (Or.imp hL (Or.imp hL (Or.imp hL (Or.imp hL
      (Or.imp hL hL)))))⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨q, n, f, hq, hf, h.imp hL (Or.imp hL (Or.imp hL (Or.imp hL
      (Or.imp hL (Or.imp hL hL)))))⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (Nonempty.map e.symm.trans h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Nonempty.map e.symm.trans h)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Nonempty.map e.symm.trans h)))))

@[expose] def OddTranspFactors (Y : Type) [Group Y] : Prop :=
  ∀ (T : Type) [Group T], E1.IsCompositionFactor Y T → (∃ a b : T, a * b ≠ b * a) →
    OddTranspFactor T

private noncomputable def kerFstEquiv (A B : Type) [Group A] [Group B] :
    ↥(MonoidHom.fst A B).ker ≃* B :=
  MulEquiv.ofBijective
    ({ toFun := fun x => (x : A × B).2
       map_one' := rfl
       map_mul' := fun _ _ => rfl } : ↥(MonoidHom.fst A B).ker →* B)
    ⟨fun x y hxy => Subtype.ext (Prod.ext ((show (x : A × B).1 = 1 from x.2).trans
      (show (y : A × B).1 = 1 from y.2).symm) hxy), fun b => ⟨⟨(1, b), rfl⟩, rfl⟩⟩

namespace OddTranspFactors

theorem of_mulEquiv {Y Y' : Type} [Group Y] [Group Y'] (e : Y ≃* Y') (h : OddTranspFactors Y) :
    OddTranspFactors Y' :=
  fun T _ hT hnab => h T ((isCompositionFactor_congr e).2 hT) hnab

theorem of_surjective {X Y : Type} [Group X] [Group Y] (f : X →* Y) (hf : Function.Surjective f)
    (h : OddTranspFactors X) : OddTranspFactors Y :=
  fun T _ hT hnab => h T (isCompositionFactor_of_surjective f hf hT) hnab

theorem of_normal {Y : Type} [Group Y] (A : Subgroup Y) [A.Normal] (hA : OddTranspFactors ↥A)
    (hQ : OddTranspFactors (Y ⧸ A)) : OddTranspFactors Y :=
  fun T _ hT hnab => (isCompositionFactor_of_normal A hT).elim (hA T · hnab) (hQ T · hnab)

theorem of_commute {Y : Type} [Group Y] (h : ∀ a b : Y, a * b = b * a) : OddTranspFactors Y :=
  fun _ _ hT ⟨a, b, hab⟩ => absurd (isCompositionFactor_commute h hT a b) hab

theorem of_commutator {Y : Type} [Group Y] (h : OddTranspFactors ↥(commutator Y)) :
    OddTranspFactors Y :=
  of_normal (commutator Y) h (of_commute fun a b => mul_comm (G := Abelianization Y) a b)

theorem of_index_two {Y : Type} [Group Y] [Finite Y] (A : Subgroup Y) (hidx : A.index = 2)
    (hA : OddTranspFactors ↥A) : OddTranspFactors Y := by
  haveI : A.Normal := Subgroup.normal_of_index_eq_two hidx
  refine of_normal A hA (of_commute ?_)
  haveI : Fact (Nat.card (Y ⧸ A)).Prime :=
    ⟨by rw [← Subgroup.index_eq_card, hidx]; exact Nat.prime_two⟩
  haveI : IsCyclic (Y ⧸ A) := isCyclic_of_prime_card rfl
  exact fun a b => (IsCyclic.commGroup (α := Y ⧸ A)).mul_comm a b

theorem prod {A B : Type} [Group A] [Group B] (hA : OddTranspFactors A)
    (hB : OddTranspFactors B) : OddTranspFactors (A × B) :=
  of_normal (MonoidHom.fst A B).ker (hB.of_mulEquiv (kerFstEquiv A B).symm)
    (hA.of_mulEquiv (QuotientGroup.quotientKerEquivOfSurjective (MonoidHom.fst A B)
      fun a => ⟨(a, 1), rfl⟩).symm)

theorem pi {L : Type} [Group L] (hL : OddTranspFactors L) (r : ℕ) :
    OddTranspFactors (Fin r → L) := by
  induction r with
  | zero => exact of_commute fun a b => Subsingleton.elim _ _
  | succ r ih =>
    exact of_normal (Pi.evalMonoidHom (fun _ : Fin (r + 1) => L) 0).ker
      (ih.of_mulEquiv (evalZeroKerEquiv L r).symm)
      (hL.of_mulEquiv (QuotientGroup.quotientKerEquivOfSurjective _
        fun l => ⟨fun _ => l, rfl⟩).symm)

theorem semidirectProduct {N H : Type} [Group N] [Group H] {φ : H →* MulAut N}
    (hN : OddTranspFactors N) (hH : OddTranspFactors H) : OddTranspFactors (N ⋊[φ] H) :=
  of_normal (SemidirectProduct.rightHom : N ⋊[φ] H →* H).ker
    (hN.of_mulEquiv ((MonoidHom.ofInjective SemidirectProduct.inl_injective).trans
      (MulEquiv.subgroupCongr SemidirectProduct.range_inl_eq_ker_rightHom)))
    (hH.of_mulEquiv (QuotientGroup.quotientKerEquivOfSurjective _
      SemidirectProduct.rightHom_surjective).symm)

theorem of_statedProj {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]
    (H : Subgroup (GL ι K)) (h : OddTranspFactors (StatedProj H)) : OddTranspFactors ↥H := by
  refine of_normal ((StatedScalars ι K).subgroupOf H) (of_commute fun a b => ?_) h
  have hc : StatedScalars ι K = Subgroup.center (GL ι K) := by
    rw [StatedScalars, ← Matrix.GeneralLinearGroup.center_eq_range_scalar]
  have ha : a.1.1 ∈ Subgroup.center (GL ι K) := hc ▸ a.2
  exact Subtype.ext (Subtype.ext (Subgroup.mem_center_iff.mp ha b.1.1).symm)

theorem of_isSimpleGroup {Y : Type} [Group Y] [IsSimpleGroup Y] (h : OddTranspFactor Y) :
    OddTranspFactors Y :=
  fun _ _ hT _ =>
    oddTranspFactor_of_mulEquiv (isCompositionFactor_mulEquiv_of_isSimpleGroup hT).some h

theorem of_statedClassicalModel {Y : Type} [Group Y] {t : StatedLieTag} {n p f : ℕ}
    (hY : StatedClassicalModel Y t n p f) (h : OddTranspFactor Y) : OddTranspFactors Y := by
  haveI := (CFSG.LieType.Simplicity.fam_classical_converse Y ⟨t, n, p, f, hY⟩).2.2
  exact of_isSimpleGroup h

end OddTranspFactors

private theorem four_le_two_pow {f : ℕ} (hf : 2 ≤ f) : 4 ≤ 2 ^ f :=
  calc 4 = 2 ^ 2 := by norm_num
    _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf

section Classical

variable {F : Type} [Field F] [Finite F] {f : ℕ}

theorem oddTranspFactors_statedSL_two (hF : Nat.card F = 2 ^ f) (hf : 2 ≤ f) :
    OddTranspFactors ↥(StatedSL 2 F) := by
  have h4 := four_le_two_pow hf
  have hM : StatedClassicalModel (StatedProj (StatedSL 2 F)) .PSL 2 2 f :=
    ⟨⟨Nat.prime_two, by omega, le_rfl, fun h => by have := (Prod.mk.inj h).2; omega,
      fun h => by have := (Prod.mk.inj h).2; omega⟩, F, inferInstance, inferInstance, hF,
      ⟨MulEquiv.refl _⟩⟩
  exact OddTranspFactors.of_statedProj _ (OddTranspFactors.of_statedClassicalModel hM
    (Or.inr (Or.inl ⟨0, f, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Or.inl ⟨by decide, hM⟩)))))⟩)))

theorem oddTranspFactors_sl2 (hF : Nat.card F = 2 ^ f) (hf : 2 ≤ f) :
    OddTranspFactors (Matrix.SpecialLinearGroup (Fin 2) F) :=
  (oddTranspFactors_statedSL_two hF hf).of_mulEquiv
    (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 F).symm

theorem oddTranspFactors_statedSL_four (hF : Nat.card F = 2 ^ f) (hf : 1 ≤ f) :
    OddTranspFactors ↥(StatedSL 4 F) := by
  have hM : StatedClassicalModel (StatedProj (StatedSL 4 F)) .PSL 4 2 f :=
    ⟨⟨Nat.prime_two, hf, by norm_num, fun h => absurd (Prod.mk.inj h).1 (by norm_num),
      fun h => absurd (Prod.mk.inj h).1 (by norm_num)⟩, F, inferInstance, inferInstance, hF,
      ⟨MulEquiv.refl _⟩⟩
  exact OddTranspFactors.of_statedProj _ (OddTranspFactors.of_statedClassicalModel hM
    (Or.inr (Or.inl ⟨0, f, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      (Or.inl ⟨by decide, hM⟩))))))⟩)))

theorem oddTranspFactors_statedSp (k : ℕ) (hF : Nat.card F = 2 ^ f) (hf : 2 ≤ f) :
    OddTranspFactors ↥(StatedSp k F) := by
  haveI : CharP F 2 := charP_two_of_natCard_eq_two_pow hF
  have h4 := four_le_two_pow hf
  rcases (by omega : k = 0 ∨ k = 1 ∨ 2 ≤ k) with rfl | rfl | hk
  · exact OddTranspFactors.of_commute fun a b =>
      Subtype.ext (Units.ext (Matrix.ext fun i => isEmptyElim i))
  · exact (oddTranspFactors_sl2 hF hf).of_mulEquiv
      ((CFSG.SeitzReduction.OmegaPilot.spProjEquivCharTwo F 1).symm.trans
        (CFSG.SeitzReduction.OmegaPilot.spOneEquiv F)).symm
  · have hM : StatedClassicalModel (StatedProj (StatedSp k F)) .PSp k 2 f :=
      ⟨⟨Nat.prime_two, by omega, hk, fun h => by have := (Prod.mk.inj h).2; omega⟩, F,
        inferInstance, inferInstance, hF, ⟨MulEquiv.refl _⟩⟩
    exact OddTranspFactors.of_statedProj _ (OddTranspFactors.of_statedClassicalModel hM
      (Or.inr (Or.inl ⟨k, f, Or.inl (Or.inl ⟨by decide, hM⟩)⟩)))

theorem oddTranspFactors_statedProj_statedSU {m : ℕ} (hm : 3 ≤ m)
    (hF : Nat.card F = (2 ^ f) ^ 2) (hf : 2 ≤ f) :
    OddTranspFactors (StatedProj (StatedSU m (2 ^ f) F)) := by
  have h4 := four_le_two_pow hf
  have hM : StatedClassicalModel (StatedProj (StatedSU m (2 ^ f) F)) .PSU m 2 f :=
    ⟨⟨Nat.prime_two, by omega, hm, fun h => by have := (Prod.mk.inj h).2; omega⟩, F,
      inferInstance, inferInstance, hF, ⟨MulEquiv.refl _⟩⟩
  exact OddTranspFactors.of_statedClassicalModel hM
    (Or.inr (Or.inl ⟨m, f, Or.inr (Or.inl (Or.inl ⟨by decide, hM⟩))⟩))

end Classical

section Orthogonal

variable {F : Type} [Field F] [Finite F] {f : ℕ}

theorem oddTranspFactors_orthogonalPlus {k : ℕ} (hk : 2 ≤ k) (hF : Nat.card F = 2 ^ f)
    (hf : 2 ≤ f) : OddTranspFactors ↥(CFSG.PGLModel.orthogonalPlus k F) := by
  haveI : CharP F 2 := charP_two_of_natCard_eq_two_pow hF
  rcases (by omega : k = 2 ∨ k = 3 ∨ 4 ≤ k) with rfl | rfl | hk4
  · have hle : (OmegaPlusCell.jProd (F := F)).range ≤ orthGroup (StatedQuadPlus 2 F) := by
      rintro _ ⟨x, rfl⟩
      exact OmegaPlusCell.jProd_mem_orthGroup x
    show OddTranspFactors ↥(orthGroup (StatedQuadPlus 2 F))
    refine OddTranspFactors.of_index_two
      ((OmegaPlusCell.jProd (F := F)).range.subgroupOf (orthGroup (StatedQuadPlus 2 F)))
      OmegaPlusCell.relIndex_jProd_range ?_
    exact ((oddTranspFactors_sl2 hF hf).prod (oddTranspFactors_sl2 hF hf)).of_mulEquiv
      ((MonoidHom.ofInjective OmegaPlusCell.jProd_injective).trans
        (Subgroup.subgroupOfEquivOfLe hle).symm)
  · refine OddTranspFactors.of_commutator
      ((?_ : OddTranspFactors ↥(StatedOmega (StatedQuadPlus 3 F))).of_mulEquiv
        (commutatorOrthogonalPlusEquiv 3 F).symm)
    obtain ⟨hnd, hts⟩ := CFSG.ClassicalGroups.Orthogonal.regular_quadPlus (K := F) (n := 3) le_rfl
    obtain ⟨eK⟩ := kleinCommutatorOrthogonalSix (quadPlus 3 F) hnd (by simp) hts
    exact (oddTranspFactors_statedSL_four hF (by omega)).of_mulEquiv
      ((statedOmegaEquivCommutator (coe_quadPlus 3 F)).trans eK).symm
  · refine OddTranspFactors.of_commutator
      ((?_ : OddTranspFactors ↥(StatedOmega (StatedQuadPlus k F))).of_mulEquiv
        (commutatorOrthogonalPlusEquiv k F).symm)
    have hM : StatedClassicalModel (StatedProj (StatedOmega (StatedQuadPlus k F)))
        .POmegaPlus k 2 f :=
      ⟨⟨Nat.prime_two, by omega, hk4⟩, F, inferInstance, inferInstance, hF, ⟨MulEquiv.refl _⟩⟩
    exact OddTranspFactors.of_statedProj _ (OddTranspFactors.of_statedClassicalModel hM
      (Or.inr (Or.inl ⟨k, f, Or.inr (Or.inr (Or.inl (Or.inl ⟨by decide, hM⟩)))⟩)))

theorem oddTranspFactors_orthogonalMinus {k : ℕ} (hk : 1 ≤ k) (hF : Nat.card F = 2 ^ f)
    (hf : 2 ≤ f) {b c : F} (hbc : ∀ s : F, s ^ 2 + b * s + c ≠ 0) :
    OddTranspFactors ↥(CFSG.PGLModel.orthogonalMinus k F b c) := by
  haveI : CharP F 2 := charP_two_of_natCard_eq_two_pow hF
  refine OddTranspFactors.of_commutator
    ((?_ : OddTranspFactors ↥(StatedOmega (StatedQuadMinus (k + 1) F b c))).of_mulEquiv
      (commutatorOrthogonalMinusEquiv k F b c).symm)
  rcases (by omega : k = 1 ∨ k = 2 ∨ 3 ≤ k) with rfl | rfl | hk3
  · obtain ⟨E, _, _, D, -, ρ, -, -, hinj, -, hcomm, -⟩ :=
      CFSG.RankThree.PartOne.even_minus_four_actual_derived_extraction (quadMinus 2 F b c)
        (nondegenerate_polarBilin_quadMinus_of_finite 2 F hbc)
        (finrank_minusSpace_small (n := 2) (by norm_num))
        (fun U hU => exists_quadMinus_ne_zero_small hbc (by norm_num) U hU)
    obtain ⟨e⟩ := nonempty_range_equiv_statedOmega ρ hcomm
    haveI := D.finite_E
    have hE : Nat.card E = 2 ^ (2 * f) := by rw [D.card_E, hF, ← pow_mul, mul_comm]
    exact (oddTranspFactors_sl2 hE (by omega)).of_mulEquiv
      ((MonoidHom.ofInjective hinj).trans e)
  · have hL : LieModel (StatedProj (StatedOmega (StatedQuadMinus 3 F b c))) .PSU 4 2 f :=
      CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.kOmega6MinusU4_holds _ f F b c hF hbc
        ⟨MulEquiv.refl _⟩
    exact OddTranspFactors.of_statedProj _ (OddTranspFactors.of_statedClassicalModel
      (hL.statedClassicalModel (by decide)) (Or.inr (Or.inl ⟨4, f, Or.inr (Or.inl hL)⟩)))
  · have hM : StatedClassicalModel (StatedProj (StatedOmega (StatedQuadMinus (k + 1) F b c)))
        .POmegaMinus (k + 1) 2 f :=
      ⟨⟨Nat.prime_two, by omega, by omega⟩, F, inferInstance, inferInstance, hF, b, c, hbc,
        ⟨MulEquiv.refl _⟩⟩
    exact OddTranspFactors.of_statedProj _ (OddTranspFactors.of_statedClassicalModel hM
      (Or.inr (Or.inl ⟨k + 1, f, Or.inr (Or.inr (Or.inr (Or.inl (Or.inl ⟨by decide, hM⟩))))⟩)))

end Orthogonal

theorem oddTranspFactors_perm (m : ℕ) : OddTranspFactors (Equiv.Perm (Fin m)) :=
  fun _ _ hT hnab => by
    obtain ⟨hm, ⟨e⟩⟩ := isCompositionFactor_perm hT hnab
    exact Or.inl ⟨m, hm, ⟨e⟩⟩

theorem oddTranspFactors_wreathSym_sl2 {F : Type} [Field F] [Finite F] {f : ℕ}
    (hF : Nat.card F = 2 ^ f) (hf : 2 ≤ f) (m : ℕ) :
    OddTranspFactors (WreathSym (Matrix.SpecialLinearGroup (Fin 2) F) m) :=
  OddTranspFactors.semidirectProduct ((oddTranspFactors_sl2 hF hf).pi m) (oddTranspFactors_perm m)

theorem oddTranspFactors_of_isSz {Y : Type} [Group Y] {f : ℕ} (h : IsSz f Y) :
    OddTranspFactors Y := by
  haveI := (CFSG.LieType.Simplicity.fam_2b2_simplicity Y 2 f h).2
  exact OddTranspFactors.of_isSimpleGroup (Or.inr (Or.inl ⟨0, f, Or.inr (Or.inr (Or.inr (Or.inr
    (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl, h⟩))))))))⟩))

end CFSG.OddTranspositions.PartFour
