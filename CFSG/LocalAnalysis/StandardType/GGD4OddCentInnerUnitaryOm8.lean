module

public import CFSG.LocalAnalysis.StandardType.GGD4OddCentInnerUnitaryRep

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.StandardType.Triality
open Polynomial Module
open CFSG.RankThree.Classical2 (orthDerived ProjOrthDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData (coordinateQuadPlus)
open CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCOrthogonal
open CFSG.RankThree.OrthogonalInvolutions CFSG.RankThree.PartOne.KCOrthComm
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.HardMathSupport.Dickson.Bal207.OrthFix CFSG.HardMathSupport.Dickson.Bal207.FirstClaim
open CFSG.RankThree.PartTwo.KFacts (unitaryIsom3 mem_unitaryIsom3)

namespace D4Inner

section Om8

variable {K : Type} [Field K] [Finite K] [CharP K 2]

omit [Finite K] [CharP K 2] in
theorem omLift_mem_omCent {s y : Om8 K} (hy : y ∈ Subgroup.centralizer ({s} : Set (Om8 K))) :
    ((omLift y : orthDerived (coordinateQuadPlus 4 K)) :
      (Fin (2 * 4) → K) ≃ₗ[K] (Fin (2 * 4) → K)) ∈
      isometryCentralizer (coordinateQuadPlus 4 K)
          (omLift s : (Fin (2 * 4) → K) ≃ₗ[K] (Fin (2 * 4) → K)) ⊓
        orthDerived (coordinateQuadPlus 4 K) := by
  refine Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr
    ⟨orthDerived_le_orthogonalGroup (omLift y).2, ?_⟩, (omLift y).2⟩
  rw [Subgroup.mem_centralizer_singleton_iff] at hy ⊢
  have := congrArg (fun z => ((omLift z : orthDerived (coordinateQuadPlus 4 K)) :
    (Fin (2 * 4) → K) ≃ₗ[K] (Fin (2 * 4) → K))) hy
  simpa only [map_mul, Subgroup.coe_mul] using this

@[expose] noncomputable def centHom (s : Om8 K) :
    ↥(Subgroup.centralizer ({s} : Set (Om8 K))) →*
      ↥(isometryCentralizer (coordinateQuadPlus 4 K)
          (omLift s : (Fin (2 * 4) → K) ≃ₗ[K] (Fin (2 * 4) → K)) ⊓
        orthDerived (coordinateQuadPlus 4 K)) where
  toFun y := ⟨(omLift y.1 : (Fin (2 * 4) → K) ≃ₗ[K] (Fin (2 * 4) → K)), omLift_mem_omCent y.2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' y y' := Subtype.ext (by simp)

omit [Finite K] [CharP K 2] in
theorem centHom_bijective (s : Om8 K) : Function.Bijective (centHom s) := by
  constructor
  · intro y y' h
    have h' := congrArg (fun g : ↥(isometryCentralizer (coordinateQuadPlus 4 K)
        (omLift s : (Fin (2 * 4) → K) ≃ₗ[K] (Fin (2 * 4) → K)) ⊓
        orthDerived (coordinateQuadPlus 4 K)) =>
          (g.1 : (Fin (2 * 4) → K) ≃ₗ[K] (Fin (2 * 4) → K))) h
    exact Subtype.ext ((CFSG.RankThree.PartOne.KCOrthComm.matrixDerivedEquiv
      (coordinateQuadPlus 4 K)).injective (Subtype.ext h'))
  · intro g
    have hgc := Subgroup.mem_centralizer_singleton_iff.mp
      (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp g.2).1).2
    refine ⟨⟨(CFSG.RankThree.PartOne.KCOrthComm.matrixDerivedEquiv (coordinateQuadPlus 4 K)).symm
      ⟨g.1, (Subgroup.mem_inf.mp g.2).2⟩, ?_⟩, ?_⟩
    · rw [Subgroup.mem_centralizer_singleton_iff]
      apply (CFSG.RankThree.PartOne.KCOrthComm.matrixDerivedEquiv
        (coordinateQuadPlus 4 K)).injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
      exact Subtype.ext hgc
    · apply Subtype.ext
      change (((CFSG.RankThree.PartOne.KCOrthComm.matrixDerivedEquiv (coordinateQuadPlus 4 K))
        ((CFSG.RankThree.PartOne.KCOrthComm.matrixDerivedEquiv (coordinateQuadPlus 4 K)).symm
          ⟨g.1, (Subgroup.mem_inf.mp g.2).2⟩) : orthDerived (coordinateQuadPlus 4 K)) :
            (Fin (2 * 4) → K) ≃ₗ[K] (Fin (2 * 4) → K)) = g.1
      rw [MulEquiv.apply_symm_apply]

@[expose] noncomputable def centEquiv (s : Om8 K) :
    ↥(Subgroup.centralizer ({s} : Set (Om8 K))) ≃*
      ↥(isometryCentralizer (coordinateQuadPlus 4 K)
          (omLift s : (Fin (2 * 4) → K) ≃ₗ[K] (Fin (2 * 4) → K)) ⊓
        orthDerived (coordinateQuadPlus 4 K)) :=
  MulEquiv.ofBijective (centHom s) (centHom_bijective s)

theorem mem_centDer_iff_mem_specialBlock {n : ℕ} (hK : Nat.card K = 2 ^ n) (hn : Odd n)
    (hn3 : 3 ≤ n) {s : Om8 K} (hs3 : s ^ 3 = 1) (hd : D4Rank.omFixDim s = 2) (y : Om8 K) :
    y ∈ centDer s ↔ ((omLift y : orthDerived (coordinateQuadPlus 4 K)) :
      (Fin (2 * 4) → K) ≃ₗ[K] (Fin (2 * 4) → K)) ∈ specialBlock (coordinateQuadPlus 4 K)
        (omLift s : (Fin (2 * 4) → K) ≃ₗ[K] (Fin (2 * 4) → K)) (X ^ 2 + X + 1) := by
  have h := map_centDer_eq_componentImage_phi hK hn hn3 hs3 hd
  have hQ := (CFSG.ComponentClassification.CatalogueBOrthogonalPointData.regular_coordinateQuadPlus
    4 K (by norm_num)).1
  constructor
  · intro hy
    have h1 : omBridge y ∈ (centDer s).map (omBridge (K := K)).toMonoidHom := ⟨y, hy, rfl⟩
    rw [h] at h1
    obtain ⟨z, hz, hzy⟩ := h1
    rw [omBridge_apply] at hzy
    have hz' : z = omLift y := CFSG.RankThree.PartOne.piOrth_injective hQ hzy
    rw [← hz']
    exact Subgroup.mem_subgroupOf.mp hz
  · intro hy
    have h1 : omBridge y ∈ componentImage (coordinateQuadPlus 4 K)
        (omLift s : (Fin (2 * 4) → K) ≃ₗ[K] (Fin (2 * 4) → K)) (X ^ 2 + X + 1) := by
      rw [omBridge_apply]
      exact ⟨omLift y, Subgroup.mem_subgroupOf.mpr hy, rfl⟩
    rw [← h] at h1
    obtain ⟨z, hz, hzy⟩ := h1
    rwa [omBridge.injective hzy] at hz

theorem exists_d2Model {n : ℕ} (hK : Nat.card K = 2 ^ n) (hn : Odd n) (hn3 : 3 ≤ n)
    {s : Om8 K} (hs3 : s ^ 3 = 1) (hd : D4Rank.omFixDim s = 2) :
    ∃ (E : Type) (_ : Field E) (hU : UnitaryFieldData 2 n E) (R : Type) (_ : Group R)
      (Ψ : ↥(Subgroup.centralizer ({s} : Set (Om8 K))) ≃* R × ↥(unitaryIsom3 hU)) (ω : Eˣ),
      (∀ a b : R, a * b = b * a) ∧ Nat.card R = 2 ^ n + 1 ∧
      Nat.card {r : R // r ^ 3 = 1} = 3 ∧ IsPrimitiveRoot (ω : E) 3 ∧
      (∀ y : ↥(Subgroup.centralizer ({s} : Set (Om8 K))), (y : Om8 K) ∈ centDer s ↔
        (Ψ y).1 = 1 ∧ (((Ψ y).2 : GL (Fin 3) E) : Matrix (Fin 3) (Fin 3) E).det = 1) ∧
      (Ψ ⟨s, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩).1 = 1 ∧
      ((Ψ ⟨s, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩).2 : GL (Fin 3) E) =
        Matrix.GeneralLinearGroup.scalar (Fin 3) ω := by
  classical
  have hQ := (CFSG.ComponentClassification.CatalogueBOrthogonalPointData.regular_coordinateQuadPlus
    4 K (by norm_num)).1
  have hT := (CFSG.ComponentClassification.CatalogueBOrthogonalPointData.regular_coordinateQuadPlus
    4 K (by norm_num)).2
  have hx := oddOrderIsometry_omLift hs3 hd
  have hpq := three_dvd_card_add_one hK hn
  have hmem := phi_mem_primaryFactors_omLift hK hn hs3 hd
  have : Fact (Irreducible (X ^ 2 + X + 1 : K[X])) := ⟨irreducible_of_mem_primaryFactors hmem⟩
  have hm := primaryMultiplicity_phi_omLift hK hn hs3 hd
  have hn1 : 1 ≤ n := by
    obtain ⟨k, rfl⟩ := hn
    omega
  have hmq : ¬(3 = 3 ∧ 2 ^ n = 2) := by
    rintro ⟨-, h⟩
    have h8 : 2 ^ 3 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn3
    omega
  obtain ⟨hU, H, b, -, hb, hrange, hspec⟩ := exists_phiFrame hK hn1 hx rfl hmem hm le_rfl hmq
  have := hU.charP
  have h2 := finrank_fixedSpace_omLift hd
  have hQW := hx.polarBilin_fixed_nondegenerate
  have hnp : ¬ CFSG.GroupTheory.WeirSylow.IsPlusType ((coordinateQuadPlus 4 K).comp
      (fixedSpace (omLift s : (Fin (2 * 4) → K) ≃ₗ[K] (Fin (2 * 4) → K))).subtype) := by
    obtain ⟨s', k, hs', -, -, htype⟩ := fixed_type hx Nat.prime_three (by norm_num) hpq (n := 4)
      (by rw [finrank_fin_fun])
      ⟨fun _ => ⟨2, rfl⟩, fun _ => (CFSG.GroupTheory.WeirSylow.isPlusType_congr
        (CFSG.ComponentClassification.CatalogueBOrthogonalPointData.coordinatePlusIsometry
          4 K)).1 (CFSG.GroupTheory.WeirSylow.isPlusType_quadPlus K 4)⟩
    have hs1 : s' = 1 := by omega
    subst hs1
    rw [htype le_rfl]
    exact Nat.not_even_one
  have hani : ∀ w : fixedSpace (omLift s : (Fin (2 * 4) → K) ≃ₗ[K] (Fin (2 * 4) → K)),
      w ≠ 0 → ((coordinateQuadPlus 4 K).comp
        (fixedSpace (omLift s : (Fin (2 * 4) → K) ≃ₗ[K] (Fin (2 * 4) → K))).subtype) w ≠ 0 := by
    intro w hw hQw
    refine hnp ⟨Submodule.span K {w}, ?_, fun u hu => ?_⟩
    · rw [finrank_span_singleton hw, h2]
    · obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hu
      rw [QuadraticMap.map_smul, hQw, smul_zero]
  have hirr : ∀ μ : K, μ ^ 2 + μ + 1 ≠ 0 := by
    intro μ hμ
    have hroot : (X ^ 2 + X + 1 : K[X]).IsRoot μ := by
      simp [Polynomial.IsRoot.def, hμ]
    have h1 := Polynomial.natDegree_eq_of_degree_eq_some
      (Polynomial.degree_eq_one_of_irreducible_of_root
        (Fact.out : Irreducible (X ^ 2 + X + 1 : K[X])) hroot)
    have h2' := (monic_phi (K := K)).2
    exact absurd (h1.symm.trans h2') (by norm_num)
  have hω3 : (AdjoinRoot.root (X ^ 2 + X + 1 : K[X])) ^ 3 = 1 :=
    root_pow_eq_one (hx.dvd_X_pow_sub_one hmem)
  have hω1 : AdjoinRoot.root (X ^ 2 + X + 1 : K[X]) ≠ 1 := by
    intro h1
    have h0 : (AdjoinRoot.root (X ^ 2 + X + 1 : K[X])) ^ 2 +
        AdjoinRoot.root (X ^ 2 + X + 1 : K[X]) + 1 = 0 := by
      have := AdjoinRoot.eval₂_root (X ^ 2 + X + 1 : K[X])
      simpa [Polynomial.eval₂_add, Polynomial.eval₂_pow, Polynomial.eval₂_X,
        Polynomial.eval₂_one] using this
    rw [h1, one_pow, CharTwo.add_self_eq_zero, zero_add] at h0
    exact one_ne_zero h0
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨Θ, hΘ⟩ : ∃ Θ, Θ = blockEquiv rfl hx hpq hmem hQ hT hU b hb hrange hspec := ⟨_, rfl⟩
  have hΘ1 := coe_blockEquiv_fst rfl hx hpq hmem hQ hT hU b hb hrange hspec
  have hΘ2 := coe_blockEquiv_snd rfl hx hpq hmem hQ hT hU b hb hrange hspec
  rw [← hΘ] at hΘ1 hΘ2
  have hyc : ∀ y : ↥(Subgroup.centralizer ({s} : Set (Om8 K))),
      (omLift y.1 : (Fin (2 * 4) → K) ≃ₗ[K] (Fin (2 * 4) → K)) ∈
        isometryCentralizer (coordinateQuadPlus 4 K)
          (omLift s : (Fin (2 * 4) → K) ≃ₗ[K] (Fin (2 * 4) → K)) := fun y =>
    (Subgroup.mem_inf.mp (omLift_mem_omCent y.2)).1
  have e1 : ∀ y : ↥(Subgroup.centralizer ({s} : Set (Om8 K))),
      ((((centEquiv s).trans Θ y).1 : ↥(rotGroup ((coordinateQuadPlus 4 K).comp
        (fixedSpace (omLift s : (Fin (2 * 4) → K) ≃ₗ[K] (Fin (2 * 4) → K))).subtype) hQW)) :
          ↥(fixedSpace (omLift s : (Fin (2 * 4) → K) ≃ₗ[K] (Fin (2 * 4) → K))) ≃ₗ[K]
            ↥(fixedSpace (omLift s : (Fin (2 * 4) → K) ≃ₗ[K] (Fin (2 * 4) → K)))) =
        isometryRestrictFixed (coordinateQuadPlus 4 K)
          (omLift s : (Fin (2 * 4) → K) ≃ₗ[K] (Fin (2 * 4) → K)) ⟨_, hyc y⟩ := fun y => by
    rw [MulEquiv.trans_apply, hΘ1]
    rfl
  have e2 : ∀ y : ↥(Subgroup.centralizer ({s} : Set (Om8 K))),
      ((((centEquiv s).trans Θ y).2 : ↥(unitaryIsom3 hU)) :
        GL (Fin 3) (AdjoinRoot (X ^ 2 + X + 1 : K[X]))) =
        phiRep b ⟨_, isometryCentralizer_le_centralizer (hyc y)⟩ := fun y => by
    rw [MulEquiv.trans_apply, hΘ2]
    rfl
  refine ⟨AdjoinRoot (X ^ 2 + X + 1 : K[X]), inferInstance, hU,
    ↥(rotGroup ((coordinateQuadPlus 4 K).comp
      (fixedSpace (omLift s : (Fin (2 * 4) → K) ≃ₗ[K] (Fin (2 * 4) → K))).subtype) hQW),
    inferInstance, (centEquiv s).trans Θ, phiRoot hx hmem,
    fun a b' => Subtype.ext (commute_of_mem_rotGroup h2 a.2 b'.2), ?_,
    card_rotGroup_pow_three_eq_one hQW h2 hani hpq hirr,
    IsPrimitiveRoot.iff_orderOf.mpr (orderOf_eq_prime hω3 hω1), fun y => ?_, ?_, ?_⟩
  · rw [card_rotGroup_of_anisotropic hQW h2 hani, hK]
  · have i1 := mem_centDer_iff_mem_specialBlock hK hn hn3 hs3 hd y.1
    have i2 := mem_specialBlock_iff_phiRep (Q := coordinateQuadPlus 4 K)
      (x := (omLift s : (Fin (2 * 4) → K) ≃ₗ[K] (Fin (2 * 4) → K))) (φ := X ^ 2 + X + 1) rfl hx hpq
      b (hyc y)
    have i3 : (((centEquiv s).trans Θ) y).1 = 1 ↔ (isometryRestrictFixed (coordinateQuadPlus 4 K)
        (omLift s : (Fin (2 * 4) → K) ≃ₗ[K] (Fin (2 * 4) → K))) ⟨_, hyc y⟩ = 1 := by
      rw [← e1 y, ← Subtype.coe_inj]
      rfl
    refine i1.trans (i2.trans (and_congr i3.symm ?_))
    rw [e2]
  · rw [← Subtype.coe_inj, e1]
    refine LinearEquiv.ext fun w => Subtype.ext ?_
    change (omLift s : (Fin (2 * 4) → K) ≃ₗ[K] (Fin (2 * 4) → K)) w = w
    exact mem_fixedSpace.mp w.2
  · rw [e2]
    exact phiRep_self hx hmem b

end Om8

end D4Inner

end CFSG.StandardType

end
