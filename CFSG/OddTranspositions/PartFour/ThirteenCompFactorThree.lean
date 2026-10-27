module

public import CFSG.OddTranspositions.PartFour.ThirteenCompFactorModels
public import CFSG.LocalAnalysis.WeakClosure81.OddTranspCompFactorDerivedCases
import CFSG.OddTranspositions.PartFour.ThirteenList
import CFSG.OddTranspositions.PartFour.ThirteenThreeSimple
import CFSG.OddTranspositions.PartFour.ThirteenThreeTwo
import CFSG.OddTranspositions.PartFour.ThirteenThreeRefl
import CFSG.Milestones.CL_LIT_Fischer_three_transposition_theorem
public import CFSG.Quasithin.Vol2.Ch9L34Gam

public section

namespace CFSG.OddTranspositions.PartFour

open CFSG.Blueprint.Fischer CFSG.Open CFSG.LocalAnalysis.WeakClosure81 Matrix
open scoped commutatorElement


theorem oddTranspFactors_fischerSU {m : ℕ} (hm : 4 ≤ m) :
    OddTranspFactors ↥(fischerMatrixGroup fun A : Matrix (Fin m) (Fin m) (GaloisField 2 2) =>
      A.det = 1 ∧ ∀ x y, fischerHermitianF4 m (A *ᵥ x) (A *ᵥ y) = fischerHermitianF4 m x y) := by
  have hSU : (fischerMatrixGroup fun A : Matrix (Fin m) (Fin m) (GaloisField 2 2) =>
      A.det = 1 ∧ ∀ x y, fischerHermitianF4 m (A *ᵥ x) (A *ᵥ y) = fischerHermitianF4 m x y) =
      StatedSU m (2 ^ 1) (GaloisField 2 2) :=
    (CFSG.Fischer.Classification.Unitary.SUm_eq m).trans
      (CFSG.LieType.Universal.Unitary.SUid_eq_statedSU CFSG.Fischer.Classification.Unitary.card_K m)
  have hM : StatedClassicalModel (StatedProj (StatedSU m (2 ^ 1) (GaloisField 2 2))) .PSU m 2 1 :=
    ⟨⟨Nat.prime_two, le_rfl, by omega, fun h => by have := (Prod.mk.inj h).1; omega⟩,
      GaloisField 2 2, inferInstance, inferInstance, CFSG.Fischer.Classification.Unitary.card_K,
      ⟨MulEquiv.refl _⟩⟩
  exact (OddTranspFactors.of_statedProj _ (OddTranspFactors.of_statedClassicalModel hM
    (Or.inr (Or.inl ⟨m, 1, Or.inr (Or.inl (Or.inl ⟨by decide, hM⟩))⟩)))).of_mulEquiv
    (MulEquiv.subgroupCongr hSU).symm

private noncomputable def fi22CarrierEquiv :
    CFSG.Blueprint.NativeSporadic.Fi22 ≃* CFSG.Blueprint.NativeSporadic.Carrier .Fi22 :=
  MulEquiv.refl _

private noncomputable def fi23CarrierEquiv :
    CFSG.Blueprint.NativeSporadic.Fi23 ≃* CFSG.Blueprint.NativeSporadic.Carrier .Fi23 :=
  MulEquiv.refl _

private noncomputable def fi24CarrierEquiv :
    CFSG.Blueprint.NativeSporadic.Fi24prime ≃* CFSG.Blueprint.NativeSporadic.Carrier .Fi24Prime :=
  MulEquiv.refl _

section Simple


private theorem not_isMulCommutative_of_not_prime {S : Type} [Group S] [IsSimpleGroup S]
    (h : ¬ (Nat.card S).Prime) : ¬ IsMulCommutative S := fun hc => by
  have := hc
  exact h ((Group.is_simple_iff_prime_card (α := S)).mp inferInstance)

private theorem center_eq_bot_of_not_prime {S : Type} [Group S] [IsSimpleGroup S]
    (h : ¬ (Nat.card S).Prime) : Subgroup.center S = ⊥ := by
  rcases Subgroup.Normal.eq_bot_or_eq_top (Subgroup.center S) with hc | hc
  · exact hc
  · exact absurd ⟨⟨fun a b => Subgroup.mem_center_iff.mp (hc ▸ Subgroup.mem_top b) a⟩⟩
      (not_isMulCommutative_of_not_prime h)

private theorem isPerfect_of_not_prime {S : Type} [Group S] [IsSimpleGroup S]
    (h : ¬ (Nat.card S).Prime) : Group.IsPerfect S := by
  refine ⟨?_⟩
  rcases Subgroup.Normal.eq_bot_or_eq_top (commutator S) with hc | hc
  · refine absurd ⟨⟨fun a b => ?_⟩⟩ (not_isMulCommutative_of_not_prime h)
    have hm : ⁅a, b⁆ ∈ commutator S := by
      rw [commutator_def]
      exact Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
    rw [hc, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hm
    exact hm
  · exact hc

private theorem conj_range_normal (S : Type) [Group S] :
    (MulAut.conj : S →* MulAut S).range.Normal := by
  refine ⟨fun a ha σ => ?_⟩
  obtain ⟨g, rfl⟩ := ha
  refine ⟨σ g, MulEquiv.ext fun x => ?_⟩
  show σ g * x * (σ g)⁻¹ = σ (g * σ.symm x * g⁻¹)
  rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]

theorem eq_commutator_of_isPerfect {X : Type} [Group X] (hS : IsSimpleGroup (commutator X))
    {N : Subgroup X} (hN : N.Normal) (hperf : Group.IsPerfect N) (hne : N ≠ ⊥) :
    N = commutator X := by
  have hle : N ≤ commutator X := by
    intro n hn
    have hmem : (⟨n, hn⟩ : N) ∈ commutator N := by
      rw [hperf.commutator_eq_top]
      exact Subgroup.mem_top _
    have h1 : n ∈ (commutator N).map N.subtype := ⟨⟨n, hn⟩, hmem, rfl⟩
    rw [Subgroup.map_subtype_commutator] at h1
    exact Subgroup.commutator_mono le_top le_top h1
  have : (N.subgroupOf (commutator X)).Normal := Subgroup.normal_subgroupOf
  rcases hS.eq_bot_or_eq_top_of_normal (N.subgroupOf (commutator X)) with h | h
  · exfalso
    apply hne
    rw [Subgroup.subgroupOf_eq_bot] at h
    exact (inf_eq_left.mpr hle).symm.trans (disjoint_iff.mp h)
  · exact le_antisymm hle (Subgroup.subgroupOf_eq_top.mp h)

end Simple

section Fi24


theorem oddTranspFactors_of_mulEquiv_mulAut_fi24 {X : Type} [Group X]
    (hS : IsSimpleGroup (commutator X))
    (φ : X ≃* MulAut CFSG.Blueprint.NativeSporadic.Fi24prime) : OddTranspFactors X := by
  have := CFSG.Sporadic.Fi24.isSimpleGroup_Fi24prime
  have hnp : ¬ (Nat.card CFSG.Blueprint.NativeSporadic.Fi24prime).Prime := by
    rw [CFSG.Sporadic.Fi24.card_Fi24prime]
    norm_num
  have hZ := center_eq_bot_of_not_prime hnp
  have hinj : Function.Injective
      (MulAut.conj : CFSG.Blueprint.NativeSporadic.Fi24prime →* MulAut _) := by
    rw [injective_iff_map_eq_one]
    intro g hg
    have hgc : g ∈ Subgroup.center CFSG.Blueprint.NativeSporadic.Fi24prime :=
      Subgroup.mem_center_iff.mpr fun h => by
        have h1 := DFunLike.congr_fun hg h
        change g * h * g⁻¹ = h at h1
        calc h * g = g * h * g⁻¹ * g := by rw [h1]
          _ = g * h := by group
    rw [hZ, Subgroup.mem_bot] at hgc
    exact hgc
  set N : Subgroup X := (MulAut.conj : CFSG.Blueprint.NativeSporadic.Fi24prime →*
    MulAut _).range.comap φ.toMonoidHom with hN
  have hNn : N.Normal :=
    (conj_range_normal CFSG.Blueprint.NativeSporadic.Fi24prime).comap φ.toMonoidHom
  obtain ⟨eN⟩ : Nonempty (↥N ≃* CFSG.Blueprint.NativeSporadic.Fi24prime) :=
    ⟨((N.equivMapOfInjective φ.toMonoidHom φ.injective).trans
      (MulEquiv.subgroupCongr (Subgroup.map_comap_eq_self_of_surjective φ.surjective _))).trans
      (MonoidHom.ofInjective hinj).symm⟩
  have : IsSimpleGroup ↥N :=
    @MulEquiv.isSimpleGroup _ _ _ _ CFSG.Sporadic.Fi24.isSimpleGroup_Fi24prime eN
  have hperf : Group.IsPerfect ↥N :=
    isPerfect_of_not_prime (by rw [Nat.card_congr eN.toEquiv]; exact hnp)
  have hne : N ≠ ⊥ := by
    intro h
    obtain ⟨a, ha⟩ := exists_ne (1 : CFSG.Blueprint.NativeSporadic.Fi24prime)
    have h1 : eN.symm a = 1 :=
      Subtype.ext ((Subgroup.eq_bot_iff_forall N).mp h _ (eN.symm a).2)
    exact ha (by simpa using congrArg eN h1)
  have hNX := eq_commutator_of_isPerfect hS hNn hperf hne
  have := hS
  exact OddTranspFactors.of_commutator (OddTranspFactors.of_isSimpleGroup
    (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      ⟨((MulEquiv.subgroupCongr hNX).symm.trans eN).trans fi24CarrierEquiv⟩))))))

end Fi24

theorem oddTranspFactors_of_pair {X : Type} [Group X] {D : Set X} (hP : Pair X D)
    (hZ : Subgroup.center X = ⊥) (hS : IsSimpleGroup (commutator X)) : OddTranspFactors X := by
  have : Finite X := hP.1
  rcases CFSG.Milestones.cl_lit_fischer_three_transposition_theorem_pinned X D hP.2.1 hP.2.2.1
      hP.2.2.2.1 hP.2.2.2.2 hZ hS with
    ⟨m, -, φ, -⟩ | ⟨m, hm, b, halt, hnd, hM⟩ | ⟨m, hm, Q, hnd, hex, hM⟩ | ⟨m, hm, hM⟩ |
      ⟨m, hm, f, hsym, hnd, hM⟩ | ⟨φ, -, -⟩ | ⟨φ, -, -⟩ | ⟨φ, -, -⟩
  · exact (oddTranspFactors_perm m).of_mulEquiv φ.symm
  · obtain ⟨φ, -⟩ := hM
    obtain ⟨e, -⟩ := exists_fischerSp_equiv_statedSp b halt hnd
    exact ((oddTranspFactors_statedSp_zmod_two hm).of_mulEquiv e.symm).of_mulEquiv φ.symm
  · obtain ⟨φ, -⟩ := hM
    exact (oddTranspFactors_fischerOrth hm Q hnd hex).of_mulEquiv φ.symm
  · obtain ⟨φ, -⟩ := hM
    exact ((oddTranspFactors_fischerSU hm).of_surjective _
      (QuotientGroup.mk'_surjective _)).of_mulEquiv φ.symm
  · obtain ⟨φ, -⟩ := hM
    exact ((oddTranspFactors_f3ReflectionGroup hm hsym hnd).of_surjective _
      (QuotientGroup.mk'_surjective _)).of_mulEquiv φ.symm
  · have : IsSimpleGroup X :=
      @MulEquiv.isSimpleGroup _ _ _ _ CFSG.Sporadic.Fi22.isSimpleGroup_Fi22 φ
    exact OddTranspFactors.of_isSimpleGroup
      (Or.inr (Or.inr (Or.inr (Or.inl ⟨φ.trans fi22CarrierEquiv⟩))))
  · have : IsSimpleGroup X :=
      @MulEquiv.isSimpleGroup _ _ _ _ CFSG.Sporadic.Fi23.isSimpleGroup_Fi23 φ
    exact OddTranspFactors.of_isSimpleGroup
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨φ.trans fi23CarrierEquiv⟩)))))
  · exact oddTranspFactors_of_mulEquiv_mulAut_fi24 hS φ

theorem oddTranspCompFactorThreeTransp_of_models : OddTranspCompFactorThreeTransp := by
  intro X _ _ s hs _ hncl hsolv hder hprod T _ hT hnab
  have hinv : ∀ d ∈ {x : X | IsConj s x}, orderOf d = 2 := fun d hd => by
    obtain ⟨c, hc⟩ := hd
    exact (SemiconjBy.orderOf_eq _ hc).symm.trans hs
  have hgen : Subgroup.closure {x : X | IsConj s x} = ⊤ := by
    rw [closure_setOf_isConj_eq_normalClosure]
    exact hncl
  have hP : Pair X {x : X | IsConj s x} := ⟨inferInstance, ⟨s, rfl⟩, hinv, hprod, hgen⟩
  exact oddTranspFactors_of_pair hP (hsolv _ inferInstance inferInstance)
    (isSimpleGroup_commutator_of_derivedSeries hP hsolv hder) T hT hnab

end CFSG.OddTranspositions.PartFour
