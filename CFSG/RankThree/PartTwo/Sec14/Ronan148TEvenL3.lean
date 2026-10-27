module

public import CFSG.RankThree.PartTwo.Sec14.Ronan148TEvenU3
public import CFSG.RankThree.SubgroupLists.SchurCommutant
public import CFSG.RankThree.SubgroupLists.CliffordPrime
import CFSG.RankThree.PartTwo.Sec14.Ronan148TOddModel
import CFSG.RankThree.SubgroupLists.CentralThreeLift
import CFSG.RankThree.SubgroupLists.CentralizerPerfect
import CFSG.RankThree.SubgroupLists.QuasisimpleLayer
import CFSG.GH74.GLS.IVK.Lifted.SL2KGroup
import CFSG.GH74.Uniqueness.Bender.Dickson
import CFSG.RankThree.SteinbergR3ELargeEvenLinearTwoCover
import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Alt
import CFSG.Adapters.ProjectiveSpecialLinear
import CFSG.Open.StatedAPI
import CFSG.CharacterTheory.Burnside
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2Center
import CFSG.GroupTheory.ABGLocalTools.PStabilityQDickson
import CFSG.Quasithin.EmptyFaithful.S152He9A5
import CFSG.CGT.Timmesfeld75.L2Pair
import CFSG.CGT.Timmesfeld75.ListWCBasic
import CFSG.CharacterTheory.CyclicBlocks.Family
import CFSG.CharacterTheory.PSL2Table.BlocksProduct
import CFSG.CharacterTheory.Semidihedral.Principal.LargePrimeTorusSylowCentralizers
import CFSG.CharacterTheory.Semidihedral.Principal.PrimeTorusBlockAlignment
import CFSG.CharacterTheory.Wreathed.FourPointInvolutionHexagon
import CFSG.CharacterTheory.Wreathed.OrderThirtyTwoWreathFusion
import CFSG.ClassicalGroups
import CFSG.Combinatorics.AperiodicCentralInvolution
import CFSG.Combinatorics.AperiodicFiveOfSix
import CFSG.Combinatorics.AperiodicOppositeComponents
import CFSG.Combinatorics.AperiodicSixteenGraphDistances
import CFSG.Combinatorics.OuterLayerPredecessors
import CFSG.Dihedral.GorensteinWalter.GLSemilinearDescent
import CFSG.GH74.GLS.Defs
import CFSG.GH74.GLS.IVK.L2.Hilbert90Core
import CFSG.GH74.GLS.IVK.L2.Lemma13
import CFSG.GH74.GLS.IVK.Lifted.GroupAux
import CFSG.GH74.GLS.IVK.Lifted.Outer14
import CFSG.GH74.GLS.IVK.Lifted.SolvAut
import CFSG.GH74.GLS.IVK.Lifted.Strong
import CFSG.GH74.GLS.IVK.Prod.Basic
import CFSG.GH74.GLS.Stage1.Thm3.Sec4.Prop41
import CFSG.GH74.GLS.Stage1.Thm3.Sec5.Statements
import CFSG.GH74.GLS.Stage1.Thm6.Sec12.Defs
import CFSG.GH74.GLS.Stage1.Thm6.Sec12.Ext
import CFSG.GH74.GLS.TwoThin.KGroupCore
import CFSG.GH74.L5U5.ModelsBridge
import CFSG.GH74.Statements
import CFSG.GH74.Uniqueness.SU.KInputs2
import CFSG.GH74.Uniqueness.SU.SU13TA1Class
import CFSG.GH74.Uniqueness.SU.SU8Stmts
import CFSG.LinearAlgebra.LinearGroups.UnitaryThreeOverNine
import CFSG.LinearAlgebra.LinearGroups.UnitaryThreeOverNineInvolutions
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBAlternatingTransport
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBLinearDescentFixedBasis
import CFSG.LocalAnalysis.ComponentClassification.PrimeComplementQuotientComponents
import CFSG.LocalAnalysis.ComponentInitial.BlockOvergroupDichotomy
import CFSG.LocalAnalysis.ComponentInitial.GeneralizedFittingProduct
import CFSG.LocalAnalysis.ComponentInitial.SymplecticSmallFieldPerfect
import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionDenominatorNontrivial
import CFSG.LocalAnalysis.QuasithinUnique.Ch1.InnerCoverBase
import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Reduce
import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureTwoCoreGrowthLinearFrobenius
import CFSG.Permutation.UnitaryThreeRecognition.Model
import CFSG.StronglyEmbedded.MatrixGroups.PSL2
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_5_4
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82Orbit
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section11Lemma115Torus
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.ConjugatedInvertedSubgroup
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2NormalizedRootSylowCount
import CFSG.Walter.J1.Inv

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148T

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4 Matrix
open CFSG.Assembly.LowTwoRank (StatedClassicalModel StatedScalars StatedProj StatedLieAdmissible
  projectiveSpecialLinearGroupEquivStatedProj)
open CFSG.BenderSuzuki.MatrixGroups (PSL2MatrixGroup)
open scoped MatrixGroups commutatorElement

@[expose] def EvenSL3Irred : Prop :=
  ∀ (F : Type) [Field F] [Finite F] (e : ℕ), 1 ≤ e → Nat.card F = 2 ^ e → 2 ^ e % 3 = 1 →
    ∀ D : Subgroup (GL (Fin 3) F), (∀ x ∈ D, (x : Matrix (Fin 3) (Fin 3) F).det = 1) →
      IsQuasisimple D → (∀ z ∈ Subgroup.center D, z ^ 3 = 1) →
      SubgroupLists.IsIrreducibleOn D →
      (∀ M : Matrix (Fin 3) (Fin 3) F, (∀ g ∈ D, (g : Matrix (Fin 3) (Fin 3) F) * M = M * g) →
        ∃ c : F, M = Matrix.scalar (Fin 3) c) →
      ¬ SubgroupLists.IsTransitiveMonomial D →
      StatedClassicalModel (D ⧸ Subgroup.center D) .PSL 2 3 2 ∨
        ∃ f : ℕ, 1 ≤ f ∧ f ∣ e ∧ (haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩;
          IsLThreeEpsAt (D ⧸ Subgroup.center D) 2 f)

theorem eq_one_of_finrank_eq_one {F : Type*} [Field F] {E : Type*} [AddCommGroup E] [Module F E]
    (hE : Module.finrank F E = 1) {Y : Type*} [Group Y] [Group.IsPerfect Y]
    (χ : Y →* (Module.End F E)ˣ) (y : Y) : χ y = 1 := by
  have hcomm : ∀ a b : (Module.End F E)ˣ, a * b = b * a := by
    intro a b
    apply Units.ext
    obtain ⟨c, hc, -⟩ :=
      LinearMap.existsUnique_eq_smul_id_of_finrank_eq_one hE (a : Module.End F E)
    obtain ⟨d, hd, -⟩ :=
      LinearMap.existsUnique_eq_smul_id_of_finrank_eq_one hE (b : Module.End F E)
    rw [Units.val_mul, Units.val_mul, hc, hd]
    ext v
    simp [smul_smul, mul_comm]
  have hle : commutator Y ≤ χ.ker := by
    rw [commutator_def, Subgroup.commutator_le]
    intro a _ b _
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact hcomm _ _
  have hy : y ∈ commutator Y := by
    rw [Group.IsPerfect.commutator_eq_top]
    exact Subgroup.mem_top y
  exact (MonoidHom.mem_ker).mp (hle hy)

theorem isPerfect_of_simple {G : Type*} [Group G] (hs : IsSimpleGroup G)
    (hnab : ∃ a b : G, a * b ≠ b * a) : Group.IsPerfect G := by
  refine ⟨?_⟩
  rcases hs.eq_bot_or_eq_top_of_normal (commutator G) with h | h
  · exfalso
    obtain ⟨a, b, hab⟩ := hnab
    apply hab
    have hm : ⁅a, b⁆ ∈ commutator G := by
      rw [commutator_def]
      exact Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
    rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hm
    exact hm
  · exact h

theorem center_eq_bot_of_simple {G : Type*} [Group G] (hs : IsSimpleGroup G)
    (hnab : ∃ a b : G, a * b ≠ b * a) : Subgroup.center G = ⊥ := by
  rcases hs.eq_bot_or_eq_top_of_normal (Subgroup.center G) with h | h
  · exact h
  · exfalso
    obtain ⟨a, b, hab⟩ := hnab
    exact hab (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top b) a)

theorem exists_sl2_of_reducible {F : Type} [Field F] [Finite F] [CharP F 2]
    {D : Subgroup (GL (Fin 3) F)} (hDq : IsQuasisimple D)
    (hZ3 : ∀ z ∈ Subgroup.center D, z ^ 3 = 1) (W : Submodule F (Fin 3 → F))
    (hW : ∀ g ∈ D, ∀ v ∈ W, (g : Matrix (Fin 3) (Fin 3) F) *ᵥ v ∈ W) (hW0 : W ≠ ⊥)
    (hWt : W ≠ ⊤) : ∃ P : Subgroup SL(2, F), Nonempty (D ≃* P) := by
  haveI : Group.IsPerfect D := hDq.1
  have hinv : ∀ g ∈ D, ∀ v ∈ W, Matrix.toLin' (g : Matrix (Fin 3) (Fin 3) F) v ∈ W :=
    fun g hg v hv => by rw [Matrix.toLin'_apply]; exact hW g hg v hv
  let baseW : D →* Module.End F W :=
    { toFun := fun g => (Matrix.toLin' ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)).restrict
        (hinv g g.2)
      map_one' := by
        ext v
        simp
      map_mul' := fun a b => by
        ext v
        simp [Matrix.mulVec_mulVec] }
  let baseQ : D →* Module.End F ((Fin 3 → F) ⧸ W) :=
    { toFun := fun g => W.mapQ W (Matrix.toLin' ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F))
        (fun v hv => hinv g g.2 v hv)
      map_one' := by
        ext v
        simp
      map_mul' := fun a b => by
        ext v
        simp }
  have hdim := Submodule.finrank_quotient_add_finrank W
  rw [Module.finrank_fin_fun] at hdim
  have hW1 : Module.finrank F W ≠ 0 := fun h => hW0 (Submodule.finrank_eq_zero.mp h)
  have hW3 : Module.finrank F W < 3 := by
    have := Submodule.finrank_lt hWt
    rwa [Module.finrank_fin_fun] at this
  have hsq : ∀ g : D, baseW.toHomUnits g = 1 → baseQ.toHomUnits g = 1 → g * g = 1 := by
    intro g h1 h2
    set gm : Matrix (Fin 3) (Fin 3) F := ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) with hgm
    have hfixW : ∀ v ∈ W, gm *ᵥ v = v := by
      intro v hv
      have h3 := congrArg (fun u : (Module.End F W)ˣ => ((u : Module.End F W) ⟨v, hv⟩ : Fin 3 → F))
        h1
      simpa [baseW] using h3
    have hfixQ : ∀ v : Fin 3 → F, gm *ᵥ v - v ∈ W := by
      intro v
      have h3 := congrArg (fun u : (Module.End F ((Fin 3 → F) ⧸ W))ˣ =>
        ((u : Module.End F ((Fin 3 → F) ⧸ W)) (W.mkQ v))) h2
      simp only [MonoidHom.toHomUnits, baseQ, Units.val_one, Module.End.one_apply] at h3
      change W.mkQ (Matrix.toLin' gm v) = W.mkQ v at h3
      rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq,
        Matrix.toLin'_apply] at h3
      exact h3
    apply Subtype.ext
    apply Units.ext
    apply Matrix.toLin'.injective
    apply LinearMap.ext
    intro v
    have h1 := hfixW _ (hfixQ v)
    have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
    rw [Matrix.mulVec_sub] at h1
    have h3 : gm *ᵥ (gm *ᵥ v) = (2 : F) • (gm *ᵥ v) - v := by
      rw [sub_eq_iff_eq_add] at h1
      rw [h1, two_smul]
      abel
    change Matrix.toLin' (gm * gm) v = Matrix.toLin' (1 : Matrix (Fin 3) (Fin 3) F) v
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply, ← Matrix.mulVec_mulVec, h3, h2, zero_smul,
      zero_sub, Matrix.one_mulVec]
    funext i
    exact CharTwo.neg_eq _
  have hnorm : ∀ N : Subgroup D, N.Normal → (∀ g ∈ N, g * g = 1) → N = ⊥ := by
    intro N hN hN2
    have hs : IsSimpleGroup (D ⧸ Subgroup.center D) := hDq.2.1
    have hNi : (N.map (QuotientGroup.mk' (Subgroup.center D))).Normal :=
      Subgroup.Normal.map hN _ (QuotientGroup.mk'_surjective _)
    rcases hs.eq_bot_or_eq_top_of_normal (N.map (QuotientGroup.mk' (Subgroup.center D))) with h | h
    · rw [eq_bot_iff]
      intro g hg
      have hgZ : g ∈ Subgroup.center D := by
        have : QuotientGroup.mk' (Subgroup.center D) g ∈
            N.map (QuotientGroup.mk' (Subgroup.center D)) := ⟨g, hg, rfl⟩
        rw [h, Subgroup.mem_bot] at this
        exact (QuotientGroup.eq_one_iff g).mp this
      have h3 := hZ3 g hgZ
      have h2 := hN2 g hg
      rw [Subgroup.mem_bot]
      calc g = g ^ 3 * (g * g)⁻¹ := by group
        _ = 1 := by rw [h3, h2, inv_one, mul_one]
    · exfalso
      obtain ⟨a, b, hab⟩ := hDq.2.2
      apply hab
      have hexp : ∀ x : D ⧸ Subgroup.center D, x * x = 1 := by
        intro x
        obtain ⟨g, hg, rfl⟩ : x ∈ N.map (QuotientGroup.mk' (Subgroup.center D)) :=
          h ▸ Subgroup.mem_top x
        rw [← map_mul, hN2 g hg, map_one]
      calc a * b = a * (a * b * (a * b)) * b := by rw [hexp (a * b)]; group
        _ = (a * a) * b * a * (b * b) := by group
        _ = b * a := by rw [hexp a, hexp b]; group
  have hrep : ∀ (E : Type) [AddCommGroup E] [Module F E], Module.finrank F E = 2 →
      ∀ ρ : D →* (Module.End F E)ˣ, (∀ g : D, ρ g = 1 → g * g = 1) →
      ∃ P : Subgroup SL(2, F), Nonempty (D ≃* P) := by
    intro E _ _ hE ρ hρ
    have : FiniteDimensional F E := Module.finite_of_finrank_eq_succ hE
    have hker : ρ.ker = ⊥ := hnorm ρ.ker inferInstance fun g hg => hρ g hg
    have hinj : Function.Injective ρ := (MonoidHom.ker_eq_bot_iff ρ).mp hker
    let b := Module.finBasisOfFinrankEq F E hE
    let τ : (Module.End F E)ˣ ≃* GL (Fin 2) F :=
      Units.mapEquiv (LinearMap.toMatrixAlgEquiv b).toMulEquiv
    exact SubgroupLists.exists_sl2_copy_of_perfect (τ.toMonoidHom.comp ρ)
      (τ.injective.comp hinj)
  rcases (by omega : Module.finrank F W = 1 ∨ Module.finrank F W = 2) with h1 | h2
  ·
    have hWt : ∀ g : D, baseW.toHomUnits g = 1 := eq_one_of_finrank_eq_one h1 _
    exact hrep _ (by omega) baseQ.toHomUnits fun g hg => hsq g (hWt g) hg
  ·
    have hQt : ∀ g : D, baseQ.toHomUnits g = 1 :=
      eq_one_of_finrank_eq_one (by omega) _
    exact hrep _ h2 baseW.toHomUnits fun g hg => hsq g hg (hQt g)

theorem statedClassicalModel_of_sl2_copy {F : Type} [Field F]
    [Finite F] [CharP F 2] {e : ℕ} (hF : Nat.card F = 2 ^ e) (he : 1 ≤ e) {D : Type} [Group D]
    (hDq : IsQuasisimple D) {P : Subgroup SL(2, F)} (φ : D ≃* P) :
    Subgroup.center D = ⊥ ∧ ∃ j : ℕ, 2 ≤ j ∧ StatedClassicalModel D .PSL 2 2 j := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Group.IsPerfect D := hDq.1
  have hnt : Nontrivial D := CFSG.LocalCores.isQuasisimple_nontrivial hDq
  have hns : ¬ Group.IsSolvable D := fun h => Group.IsPerfect.not_isSolvable D h
  let σ : SL(2, F) ≃* PSL2MatrixGroup F :=
    (CFSG.RankThree.projectiveSpecialLinearTwoEquivSLOfCharTwo F).symm
  set Q : Subgroup (PSL2MatrixGroup F) := P.map σ.toMonoidHom with hQ
  let ψ : D ≃* Q := φ.trans (Subgroup.equivMapOfInjective P σ.toMonoidHom σ.injective)
  have hcase : ∀ m : ℕ, 1 ≤ m → Nonempty (D ≃* PSL2MatrixGroup (GaloisField 2 m)) →
      Subgroup.center D = ⊥ ∧ ∃ j : ℕ, 2 ≤ j ∧ StatedClassicalModel D .PSL 2 2 j := by
    rintro m hm ⟨χ⟩
    have hZ : Subgroup.center D = ⊥ := CFSG.GorensteinWalter.center_eq_bot_of_mulEquiv χ
      (CFSG.GorensteinWalter.psl2_center_eq_bot _)
    have hm2 : 2 ≤ m := by
      by_contra hm2
      have hm1 : m = 1 := by omega
      subst hm1
      apply hns
      have hc := CFSG.GH74.Uniqueness.Bender.card_psl2_even 1 le_rfl
      have := Fintype.ofFinite (PSL2MatrixGroup (GaloisField 2 1))
      have hsolv : Group.IsSolvable (PSL2MatrixGroup (GaloisField 2 1)) :=
        CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow (a := 1) (b := 1)
          Nat.prime_two Nat.prime_three (by norm_num)
          (by rw [← Nat.card_eq_fintype_card, hc]; norm_num)
      exact Group.isSolvable_of_surjective (f := χ.symm.toMonoidHom) χ.symm.surjective
    refine ⟨hZ, m, hm2, ⟨Nat.prime_two, hm, le_rfl, ?_, ?_⟩, GaloisField 2 m, inferInstance,
      inferInstance, GaloisField.card 2 m (by omega),
      ⟨χ.trans (projectiveSpecialLinearGroupEquivStatedProj 2 (GaloisField 2 m))⟩⟩
    · intro h
      have h2 : 2 ^ m = 2 ^ 1 := by simpa using congrArg Prod.snd h
      have := Nat.pow_right_injective (le_refl 2) h2
      omega
    · intro h
      have h2 : 2 ^ m = 3 := by simpa using congrArg Prod.snd h
      have : 2 ∣ 3 := h2 ▸ dvd_pow_self 2 (by omega)
      omega
  rcases CFSG.GH74.GLS.IVK.Lifted.psl2_subgroup_dichotomy hF Q with hsol | hA5 | ⟨m, hm, ⟨χ⟩⟩ |
      ⟨m, hm, ⟨χ⟩⟩
  · exact absurd (Group.isSolvable_of_surjective (f := ψ.symm.toMonoidHom) ψ.symm.surjective) hns
  · obtain ⟨χ⟩ := hA5
    obtain ⟨ε⟩ := CFSG.Quasithin.He9.nonempty_psl2_gf4_mulEquiv_alternating
    exact hcase 2 (by norm_num) ⟨(ψ.trans χ).trans ε.symm⟩
  · have hm1 : 1 ≤ m := by
      rcases Nat.eq_zero_or_pos m with h | h
      · subst h
        have := Nat.eq_zero_of_zero_dvd hm
        omega
      · exact h
    exact hcase m hm1 ⟨ψ.trans χ⟩
  · have hm1 : 1 ≤ m := by
      rcases Nat.eq_zero_or_pos m with h | h
      · subst h
        rw [mul_zero] at hm
        have := Nat.eq_zero_of_zero_dvd hm
        omega
      · exact h
    obtain ⟨ε⟩ := CFSG.GH74.Uniqueness.Bender.nonempty_pgl2_mulEquiv_psl2 m hm1
    exact hcase m hm1 ⟨(ψ.trans χ).trans ε⟩

theorem map_center_mulEquiv {A B : Type*} [Group A] [Group B] (χ : A ≃* B) :
    (Subgroup.center A).map χ.toMonoidHom = Subgroup.center B :=
  Subgroup.map_center_eq χ

theorem evenSimpleListL3_of_irred (hIrr : EvenSL3Irred) :
    EvenSimpleListL3 := by
  intro X _ _ e he hq hφX K hKs hnab
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨π, F, _, hF, hqF, ⟨φ⟩⟩ :=
    exists_slPi_quotient he (Or.inl ⟨hq, hφX⟩ : Sec4.IsoLThreePi X 2 e)
  cases π with
  | false =>
    exfalso
    change (2 ^ e) % 3 = 2 at hqF
    omega
  | true =>
  have := hF.finite
  have := charP_of_piField hF
  have hFc : Nat.card F = 2 ^ e := hF.card
  set H := slPi true 3 (2 ^ e) F with hH
  set N := Subgroup.center H with hN
  haveI : Group.IsPerfect K := isPerfect_of_simple hKs hnab
  have hKZ : Subgroup.center K = ⊥ := center_eq_bot_of_simple hKs hnab
  set K₁ : Subgroup (H ⧸ N) := K.map φ.toMonoidHom with hK₁
  let κ : K ≃* K₁ := Subgroup.equivMapOfInjective K φ.toMonoidHom φ.injective
  haveI : Group.IsPerfect K₁ := Group.IsPerfect.map φ.toMonoidHom
  have hK₁Z : Subgroup.center K₁ = ⊥ := by
    rw [← map_center_mulEquiv κ, hKZ, Subgroup.map_bot]
  set M : Subgroup H := K₁.comap (QuotientGroup.mk' N) with hM
  set D : Subgroup H := ⁅M, M⁆ with hD
  haveI hDp : Group.IsPerfect D := SubgroupLists.isPerfect_commutator_comap le_rfl K₁
  have hDK : D.map (QuotientGroup.mk' N) = K₁ := SubgroupLists.map_commutator_comap K₁
  have hmemK : ∀ d ∈ D, QuotientGroup.mk' N d ∈ K₁ := fun d hd => hDK ▸ ⟨d, hd, rfl⟩
  let f : D →* K₁ :=
    { toFun := fun d => ⟨QuotientGroup.mk' N d, hmemK d d.2⟩
      map_one' := Subtype.ext (map_one _)
      map_mul' := fun a b => Subtype.ext (map_mul _ _ _) }
  have hf : Function.Surjective f := by
    rintro ⟨k, hk⟩
    rw [← hDK] at hk
    obtain ⟨d, hd, rfl⟩ := hk
    exact ⟨⟨d, hd⟩, rfl⟩
  have hker : Subgroup.center D = f.ker := by
    ext d
    rw [MonoidHom.mem_ker]
    constructor
    · intro hd
      have h1 : f d ∈ Subgroup.center K₁ := by
        rw [Subgroup.mem_center_iff]
        intro k
        obtain ⟨d', rfl⟩ := hf k
        rw [← map_mul, ← map_mul, (Subgroup.mem_center_iff.mp hd) d']
      rw [hK₁Z, Subgroup.mem_bot] at h1
      exact h1
    · intro hd
      have h1 : (d : H) ∈ N := by
        have h2 := congrArg Subtype.val hd
        exact (QuotientGroup.eq_one_iff (N := N) (d : H)).mp h2
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (Subgroup.mem_center_iff.mp h1 (g : H))
  let ψ₀ : D ⧸ Subgroup.center D ≃* K :=
    ((QuotientGroup.quotientMulEquivOfEq hker).trans
      (QuotientGroup.quotientKerEquivOfSurjective f hf)).trans κ.symm
  set D' : Subgroup (GL (Fin 3) F) := D.map H.subtype with hD'
  let χ : D ≃* D' := Subgroup.equivMapOfInjective D H.subtype H.subtype_injective
  have hcenter : (Subgroup.center D).map χ.toMonoidHom = Subgroup.center D' :=
    map_center_mulEquiv χ
  let ψ : D' ⧸ Subgroup.center D' ≃* K :=
    (QuotientGroup.congr (Subgroup.center D) (Subgroup.center D') χ hcenter).symm.trans ψ₀
  haveI : Group.IsPerfect D' := Group.IsPerfect.ofSurjective (f := χ.toMonoidHom) χ.surjective
  have hD'q : IsQuasisimple D' := by
    haveI := hKs
    refine ⟨inferInstance, MulEquiv.isSimpleGroup ψ, ?_⟩
    obtain ⟨a, b, hab⟩ := hnab
    exact ⟨ψ.symm a, ψ.symm b, fun h => hab (ψ.symm.injective (by rw [map_mul, map_mul, h]))⟩
  have hD'det : ∀ x ∈ D', (x : Matrix (Fin 3) (Fin 3) F).det = 1 := by
    rintro _ ⟨x, -, rfl⟩
    exact det_eq_one_of_mem_slPi hF x.2
  have hD'Z3 : ∀ z ∈ Subgroup.center D', z ^ 3 = 1 := by
    intro z hz
    rw [← hcenter] at hz
    obtain ⟨d, hd, rfl⟩ := hz
    have hd' : d ∈ f.ker := hker ▸ hd
    rw [MonoidHom.mem_ker] at hd'
    have hd := hd'
    have h1 : (d : H) ∈ N := by
      have h2 := congrArg Subtype.val hd
      exact (QuotientGroup.eq_one_iff (N := N) (d : H)).mp h2
    have h3 := pow_three_eq_one_of_mem_center_slPi hF hqF h1
    apply Subtype.ext
    change ((d : H) : GL (Fin 3) F) ^ 3 = 1
    rw [← Subgroup.coe_pow, h3, Subgroup.coe_one]
  by_cases hirr : SubgroupLists.IsIrreducibleOn D'
  ·
    have hcomm : ∀ M : Matrix (Fin 3) (Fin 3) F,
        (∀ g ∈ D', (g : Matrix (Fin 3) (Fin 3) F) * M = M * g) →
        ∃ c : F, M = Matrix.scalar (Fin 3) c := by
      rcases SubgroupLists.scalar_commutant_or_cyclic Nat.prime_three
          (SubgroupLists.isIrreducibleOn_iff.mp hirr) with h | ⟨hcyc, -, -⟩
      · intro M hM
        exact h M fun g hg => (hM g hg)
      · exfalso
        obtain ⟨a, b, hab⟩ := hD'q.2.2
        apply hab
        induction a using QuotientGroup.induction_on with
        | H a =>
          induction b using QuotientGroup.induction_on with
          | H b =>
            obtain ⟨g, hg⟩ := hcyc.exists_generator
            obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hg a)
            obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hg b)
            rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, (Commute.zpow_zpow_self g i j).eq]
    have hprim : ¬ SubgroupLists.IsTransitiveMonomial D' :=
      SubgroupLists.not_isTransitiveMonomial_of_perfect
    rcases hIrr F e he hFc hq D' hD'det hD'q hD'Z3 hirr hcomm hprim with h | ⟨f', hf', hf'e, h⟩
    · exact Or.inr (Or.inl (CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv ψ h))
    · exact Or.inr (Or.inr ⟨f', hf', hf'e, Ronan148K.isLThreeEpsAt_of_mulEquiv ψ h⟩)
  ·
    unfold SubgroupLists.IsIrreducibleOn at hirr
    push Not at hirr
    obtain ⟨W, hW, hW0, hWt⟩ := hirr
    obtain ⟨P, ⟨θ⟩⟩ := exists_sl2_of_reducible hD'q hD'Z3 W hW hW0 hWt
    obtain ⟨hZ, j, hj, hM⟩ := statedClassicalModel_of_sl2_copy hFc he hD'q θ
    let ε : D' ≃* K :=
      ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm.trans ψ
    exact Or.inl ⟨j, hj, CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv ε hM⟩

end CFSG.RankThree.PartTwo.Sec14.Ronan148T
