module

import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.GroupAction.Cardinalities
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.GroupAction.Quotient
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection8.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection5.PFsection5_2
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection5.PFsection5_3

namespace CFSG
end CFSG
open CFSG

/-!
# Peterfalvi, Section 9: basic notation

This file records book-facing vocabulary for Peterfalvi, Section 9,
`On the Maximal Subgroups of G of Types II, III and IV`.
-/

noncomputable section

open scoped BigOperators commutatorElement

attribute [local instance] Fintype.ofFinite

namespace CFSG.Section9

universe u

/-- The ambient action package in PF `(9.1)`. -/
@[expose] public def frobeniusActionData
    {G : Type u} [Group G] [Finite G]
    (UE U E H : Subgroup G) : Prop :=
  section12ComplementIn UE U E ∧
    section12FrobeniusJoinWithKernel U E ∧
    UE ≤ Subgroup.normalizer (H : Set G) ∧
    IsSolvable H ∧
    Nat.Coprime (Nat.card H) (Nat.card UE)

/-- PF Hypothesis `(9.2)`.

`MF` is the subgroup denoted `H = M_F` in the book.  The fields
`typePDefinitionData`, `typeIIToIVSourceCondition`, and the three branch
source implications record that `H`, `U`, `W1`, and `W2` have the meaning fixed
in Definition `(8.4)` and the following Type II/III/IV source definitions.
The ambient minimal-counterexample assumption is intentionally not a field of
this structure; proofs that need it should require `[IsMinCE G]` explicitly.
-/
public structure hypothesis_9_2_statement
    {G : Type u} [Group G] [Finite G]
    (M MF U W1 W2 : Subgroup G)
    (q : ℕ) : Prop where
  maximal : M ∈ section9MaximalSubgroups G
  mf : section16MFSubgroup M MF
  typeP : Section8.typePData M MF U W1 W2
  typePDefinitionData : Section8.typePDefinitionData M MF U W1 W2
  typeIIToIVSourceCondition : Section8.typeIIToIVSourceCondition M U W1
  typeIISource :
    section16TypeII M MF →
      IsMulCommutative U ∧
        ¬ Subgroup.normalizer (U : Set G) ≤ M ∧
        ∃ U1 U0 : Subgroup G,
          Section8.typeFData (ambientDerivedSubgroup M) MF U U1 U0
  typeIIISource :
    section16TypeIII M MF →
      IsMulCommutative U ∧ Subgroup.normalizer (U : Set G) ≤ M
  typeIVSource :
    section16TypeIV M MF →
      ¬ IsMulCommutative U ∧ Subgroup.normalizer (U : Set G) ≤ M
  typeCases : section16TypeII M MF ∨ section16TypeIII M MF ∨ section16TypeIV M MF
  q_eq : Nat.card W1 = q

public theorem hypothesis_9_2_with_card_W1_sec9
    {G : Type u} [Group G] [Finite G]
    {M MF U W1 W2 : Subgroup G}
    {q : ℕ} :
    hypothesis_9_2_statement M MF U W1 W2 q →
      hypothesis_9_2_statement M MF U W1 W2 (Nat.card W1) := by
  intro h92
  exact { h92 with q_eq := rfl }

/--
`A` centralizes the quotient `MF/H0`, expressed through commutators so that
PF Section 9 can record the book statement before a full quotient-action API is
introduced.
-/
@[expose] public def quotientCentralizedBy
    {G : Type u} [Group G]
    (MF H0 A : Subgroup G) : Prop :=
  ∀ a : G, a ∈ A → ∀ h : G, h ∈ MF → ⁅a, h⁆ ∈ H0

public theorem quotientCentralizedBy_iff_commutator_le_sec9
    {G : Type u} [Group G]
    {MF H0 A : Subgroup G} :
    quotientCentralizedBy MF H0 A ↔ ⁅A, MF⁆ ≤ H0 := by
  rw [Subgroup.commutator_le]
  constructor
  · intro hcent a ha h hh
    exact hcent a ha h hh
  · intro hcomm a ha h hh
    exact hcomm a ha h hh

/-- The exact quotient centralizer `C = C_U(MF/H0)` from PF `(9.5)`. -/
@[expose] public def quotientCentralizerIn
    {G : Type u} [Group G]
    (MF H0 U C : Subgroup G) : Prop :=
  C ≤ U ∧
    ∀ x : G, x ∈ U →
      (x ∈ C ↔ ∀ h : G, h ∈ MF → ⁅x, h⁆ ∈ H0)

public theorem quotientCentralizedBy_of_eq_quotientCentralizerIn_sec9
    {G : Type u} [Group G]
    {MF H0 U C : Subgroup G} :
    quotientCentralizerIn MF H0 U C →
      U = C →
        quotientCentralizedBy MF H0 U := by
  intro hC hUC x hxU h hhMF
  have hxC : x ∈ C := by
    simpa [hUC] using hxU
  exact (hC.2 x hxU).mp hxC h hhMF

public theorem ne_of_not_quotientCentralizedBy_quotientCentralizerIn_sec9
    {G : Type u} [Group G]
    {MF H0 U C : Subgroup G} :
    quotientCentralizerIn MF H0 U C →
      ¬ quotientCentralizedBy MF H0 U →
        U ≠ C := by
  intro hC hnon hUC
  exact hnon (quotientCentralizedBy_of_eq_quotientCentralizerIn_sec9 hC hUC)

/-- Construct the exact quotient centralizer `C_U(MF/H0)` as the kernel of the
induced conjugation action of `U` on `MF/H0`, retaining its normality in `U`. -/
public theorem exists_quotientCentralizerIn_normal_of_invariant_sec9
    {G : Type u} [Group G] [Finite G]
    {MF H0 U : Subgroup G}
    [Subgroup.Normalizes U MF]
    (hnormal : (H0.subgroupOf MF).Normal)
    (hH0_inv_U : IsInvariant U MF (H0.subgroupOf MF)) :
    ∃ C : Subgroup G,
      quotientCentralizerIn MF H0 U C ∧ (C.subgroupOf U).Normal := by
  classical
  let H0MF : Subgroup MF := H0.subgroupOf MF
  haveI : H0MF.Normal := hnormal
  letI : MulDistribMulAction U (MF ⧸ H0MF) :=
    quotientMulDistribMulAction (A := U) (G := MF) H0MF hH0_inv_U
  let ρ : U →* MulAut (MF ⧸ H0MF) := MulDistribMulAction.toMulAut U (MF ⧸ H0MF)
  let C : Subgroup G := ρ.ker.map U.subtype
  refine ⟨C, ⟨?_, ?_⟩, ?_⟩
  · intro x hxC
    rcases Subgroup.mem_map.mp hxC with ⟨u, _hu, rfl⟩
    exact u.property
  · intro x hxU
    constructor
    · intro hxC h hhMF
      rcases Subgroup.mem_map.mp hxC with ⟨u, huKer, hux⟩
      subst x
      let hMF : MF := ⟨h, hhMF⟩
      have hρ : ρ u = 1 := by
        simpa [ρ] using (MonoidHom.mem_ker.mp huKer)
      have hfix :
          u • QuotientGroup.mk' H0MF hMF = QuotientGroup.mk' H0MF hMF := by
        have hfun :=
          congrArg
            (fun f : MulAut (MF ⧸ H0MF) => f (QuotientGroup.mk' H0MF hMF)) hρ
        simpa [ρ] using hfun
      have hfix' :
          QuotientGroup.mk' H0MF (u • hMF) = QuotientGroup.mk' H0MF hMF := by
        simpa using hfix
      have hdiv : ((u • hMF : MF) / hMF) ∈ H0MF :=
        (QuotientGroup.eq_iff_div_mem (N := H0MF)).mp hfix'
      have hval : (((u • hMF : MF) / hMF : MF) : G) = ⁅(u : G), h⁆ := by
        simp [hMF, div_eq_mul_inv, commutatorElement_def,
          Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe, mul_assoc]
      simpa [H0MF, Subgroup.mem_subgroupOf, hval] using hdiv
    · intro hcent
      let u : U := ⟨x, hxU⟩
      refine Subgroup.mem_map.mpr ⟨u, ?_, rfl⟩
      rw [MonoidHom.mem_ker]
      ext q
      rcases QuotientGroup.mk'_surjective H0MF q with ⟨hMF, rfl⟩
      have hfix' :
          QuotientGroup.mk' H0MF (u • hMF) = QuotientGroup.mk' H0MF hMF := by
        apply (QuotientGroup.eq_iff_div_mem (N := H0MF)).mpr
        have hcommH0 : ⁅x, (hMF : G)⁆ ∈ H0 := hcent (hMF : G) hMF.property
        have hdiv : ((u • hMF : MF) / hMF) ∈ H0MF := by
          have hval :
              (((u • hMF : MF) / hMF : MF) : G) = ⁅x, (hMF : G)⁆ := by
            simp [u, div_eq_mul_inv, commutatorElement_def,
              Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe, mul_assoc]
          simpa [H0MF, Subgroup.mem_subgroupOf, hval] using hcommH0
        simpa [div_eq_mul_inv] using hdiv
      change
        (ρ u) (QuotientGroup.mk' H0MF hMF) =
          (1 : MulAut (MF ⧸ H0MF)) (QuotientGroup.mk' H0MF hMF)
      simpa [ρ] using hfix'
  · have hCsub : C.subgroupOf U = ρ.ker := by
      ext u
      constructor
      · intro hu
        rcases Subgroup.mem_map.mp hu with ⟨v, hv, hvu⟩
        have hvu' : v = u := Subtype.ext hvu
        simpa [hvu'] using hv
      · intro hu
        exact Subgroup.mem_map.mpr ⟨u, hu, rfl⟩
    rw [hCsub]
    infer_instance

/-- Construct the exact quotient centralizer `C_U(MF/H0)`. -/
public theorem exists_quotientCentralizerIn_of_invariant_sec9
    {G : Type u} [Group G] [Finite G]
    {MF H0 U : Subgroup G}
    [Subgroup.Normalizes U MF]
    (hnormal : (H0.subgroupOf MF).Normal)
    (hH0_inv_U : IsInvariant U MF (H0.subgroupOf MF)) :
    ∃ C : Subgroup G, quotientCentralizerIn MF H0 U C := by
  rcases exists_quotientCentralizerIn_normal_of_invariant_sec9
      hnormal hH0_inv_U with ⟨C, hC, _hCnormal⟩
  exact ⟨C, hC⟩

/-- The Dade isometry relative to `(A(M), M, G)` from PF `(9.5)`. -/
@[expose] public def dadeIsometryRelativeToASet
    {G : Type u} [Group G] [Finite G]
    (M U : Subgroup G)
    (T : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G) : Prop :=
  ∃ H : G → Subgroup G,
    ∃ hAMG : Section2.Hypothesis2 (section16ASet M U) M H,
      ∀ α : Section1.ClassFunction M,
        Section2.CFOn M (section16ASet M U) α →
          T α = Section2.dadeTransform H hAMG.subset_L α

/-- Cardinality data for the quotient `\overline U = U/C`. -/
@[expose] public def quotientBarUCardinality
    {G : Type u} [Group G] [Finite G]
    (U C : Subgroup G)
    (u : ℕ) : Prop :=
  C ≤ U ∧
    ∃ hnormal : (C.subgroupOf U).Normal,
      letI : (C.subgroupOf U).Normal := hnormal
      Nat.card (U ⧸ C.subgroupOf U) = u

public theorem quotientBarUCardinality_relIndex_sec9
    {G : Type u} [Group G] [Finite G]
    (U C : Subgroup G)
    (u : ℕ) :
    quotientBarUCardinality U C u →
      C.relIndex U = u := by
  intro hBarU
  rcases hBarU with ⟨_hCU, hnormal, hcard⟩
  letI : (C.subgroupOf U).Normal := hnormal
  rw [Subgroup.relIndex, Subgroup.index_eq_card (C.subgroupOf U), hcard]

public theorem quotientBarUCardinality_card_pos_sec9
    {G : Type u} [Group G] [Finite G]
    (U C : Subgroup G)
    (u : ℕ) :
    quotientBarUCardinality U C u →
      0 < u := by
  intro hBarU
  rcases hBarU with ⟨_hCU, hnormal, hcard⟩
  letI : (C.subgroupOf U).Normal := hnormal
  rw [← hcard]
  exact Nat.card_pos (α := U ⧸ C.subgroupOf U)

public theorem quotientBarUCardinality_odd_of_odd_U_sec9
    {G : Type u} [Group G] [Finite G]
    (U C : Subgroup G)
    (u : ℕ) :
    quotientBarUCardinality U C u →
      Odd (Nat.card U) →
        Odd u := by
  intro hBarU hUodd
  rcases hBarU with ⟨_hCU, hnormal, hcard⟩
  letI : (C.subgroupOf U).Normal := hnormal
  have hquot_dvd : Nat.card (U ⧸ C.subgroupOf U) ∣ Nat.card U :=
    Subgroup.card_quotient_dvd_card (C.subgroupOf U)
  have hquot_odd : Odd (Nat.card (U ⧸ C.subgroupOf U)) :=
    odd_of_card_dvd hUodd hquot_dvd
  exact hcard ▸ hquot_odd

/-- Cyclic quotient data for `\overline U = U/C`. -/
@[expose] public def quotientBarUCyclicData
    {G : Type u} [Group G] [Finite G]
    (U C : Subgroup G)
    (u : ℕ) : Prop :=
  C ≤ U ∧
    ∃ hnormal : (C.subgroupOf U).Normal,
      letI : (C.subgroupOf U).Normal := hnormal
      IsCyclic (U ⧸ C.subgroupOf U) ∧
        Nat.card (U ⧸ C.subgroupOf U) = u

/-- A quotient subgroup transported by conjugation with an ambient element. -/
@[expose] public def quotientSubgroupConjugateByElement
    {G : Type u} [Group G] [Finite G]
    (MF H0 : Subgroup G)
    [hnormal : (H0.subgroupOf MF).Normal]
    (Q R : Subgroup (MF ⧸ H0.subgroupOf MF))
    (g : G) : Prop :=
  ∃ hconjMF : ∀ h : MF, g⁻¹ * (h : G) * g ∈ MF,
    ∃ action : MulAut (MF ⧸ H0.subgroupOf MF),
      (∀ h : MF,
        action (QuotientGroup.mk' (H0.subgroupOf MF) h) =
          QuotientGroup.mk' (H0.subgroupOf MF)
            ⟨g⁻¹ * (h : G) * g, hconjMF h⟩) ∧
        R = Q.map action.toMonoidHom

/-- A subgroup of `MF/H0` is normalized by the image of `A`. -/
@[expose] public def quotientSubgroupNormalizedBy
    {G : Type u} [Group G] [Finite G]
    (MF H0 A : Subgroup G)
    [hnormal : (H0.subgroupOf MF).Normal]
    (Q : Subgroup (MF ⧸ H0.subgroupOf MF)) : Prop :=
  ∀ a : A, quotientSubgroupConjugateByElement MF H0 Q Q (a : G)

/-- An ambient element centralizes a quotient subgroup of `MF/H0`. -/
@[expose] public def quotientSubgroupCentralizedByElement
    {G : Type u} [Group G] [Finite G]
    (MF H0 : Subgroup G)
    [hnormal : (H0.subgroupOf MF).Normal]
    (Q : Subgroup (MF ⧸ H0.subgroupOf MF))
    (g : G) : Prop :=
  ∃ hconjMF : ∀ h : MF, g⁻¹ * (h : G) * g ∈ MF,
    ∃ action : MulAut (MF ⧸ H0.subgroupOf MF),
      (∀ h : MF,
        action (QuotientGroup.mk' (H0.subgroupOf MF) h) =
          QuotientGroup.mk' (H0.subgroupOf MF)
            ⟨g⁻¹ * (h : G) * g, hconjMF h⟩) ∧
        ∀ x : MF ⧸ H0.subgroupOf MF, x ∈ Q → action x = x

/--
The cyclic quotient `\overline U/C_{\overline U}(Q)` of order `a`, expressed
through the induced action of `\overline U` on the quotient factor `Q`; the
kernel is exactly the elements centralizing `Q`.
-/
@[expose] public def quotientFactorActionCentralizerData
    {G : Type u} [Group G] [Finite G]
    (MF H0 U C : Subgroup G)
    [hnormalH0 : (H0.subgroupOf MF).Normal]
    (Q : Subgroup (MF ⧸ H0.subgroupOf MF))
    (a : ℕ) : Prop :=
  ∃ hnormal : (C.subgroupOf U).Normal,
    letI : (C.subgroupOf U).Normal := hnormal
    ∃ ρ : (U ⧸ C.subgroupOf U) →* MulAut Q,
      IsCyclic ρ.range ∧
        Nat.card ρ.range = a ∧
        (∀ x : U ⧸ C.subgroupOf U,
          ∀ u : U, QuotientGroup.mk' (C.subgroupOf U) u = x →
            ∃ hconjMF : ∀ h : MF, (u : G)⁻¹ * (h : G) * (u : G) ∈ MF,
              ∀ h : MF, ∀ hhQ : QuotientGroup.mk' (H0.subgroupOf MF) h ∈ Q,
                (ρ x ⟨QuotientGroup.mk' (H0.subgroupOf MF) h, hhQ⟩ :
                    MF ⧸ H0.subgroupOf MF) =
                  QuotientGroup.mk' (H0.subgroupOf MF)
                    ⟨(u : G)⁻¹ * (h : G) * (u : G), hconjMF h⟩) ∧
        ∀ x : U ⧸ C.subgroupOf U,
          ρ x = 1 ↔
            ∀ u : U, QuotientGroup.mk' (C.subgroupOf U) u = x →
              quotientSubgroupCentralizedByElement MF H0 Q (u : G)

/-- The subgroup `H_0` and prime `p` chosen in PF `(9.4)`. -/
@[expose] public def hoReductionData
    {G : Type u} [Group G] [Finite G]
    (M MF U W2 H0 : Subgroup G)
    (p : Nat.Primes) : Prop :=
  H0 ≤ MF ∧
    MF ≤ M ∧
    (H0.subgroupOf M).Normal ∧
    (H0.subgroupOf MF).Normal ∧
    H0 < MF ∧
    (∃ hnormal : (H0.subgroupOf MF).Normal,
      letI : (H0.subgroupOf MF).Normal := hnormal
      IsElementaryAbelian p.val (MF ⧸ H0.subgroupOf MF)) ∧
    ((section16TypeIII M MF ∨ section16TypeIV M MF) →
      Nat.card W2 = p.val ∧
        IsChiefFactor (H0.subgroupOf M) (MF.subgroupOf M) ∧
          ¬ quotientCentralizedBy MF H0 U)

public theorem subgroupOf_MF_isInvariant_of_subgroupOf_M_normal_sec9
    {G : Type u} [Group G] [Finite G]
    (M MF A H0 : Subgroup G) [Subgroup.Normalizes A MF] :
    MF ≤ M →
      A ≤ M →
        (H0.subgroupOf M).Normal →
          A ≤ Subgroup.normalizer (MF : Set G) →
            IsInvariant A MF (H0.subgroupOf MF) := by
  classical
  intro hMF_le_M hA_le_M hH0_normal_M hA_norm_MF
  let H0MF : Subgroup MF := H0.subgroupOf MF
  change IsInvariant A MF H0MF
  have hforward : ∀ (a : A) (x : MF), x ∈ H0MF → a • x ∈ H0MF := by
    intro a x hx
    have haM : (a : G) ∈ M := hA_le_M a.property
    have hxH0 : (x : G) ∈ H0 := by
      simpa [H0MF, Subgroup.mem_subgroupOf] using hx
    have hxM : (x : G) ∈ M := hMF_le_M x.property
    let aM : M := ⟨(a : G), haM⟩
    let xM : M := ⟨(x : G), hxM⟩
    have hxH0M : xM ∈ H0.subgroupOf M := by
      simpa [xM, Subgroup.mem_subgroupOf] using hxH0
    have hconjM : aM * xM * aM⁻¹ ∈ H0.subgroupOf M :=
      hH0_normal_M.conj_mem xM hxH0M aM
    have hconjH0 : (a : G) * (x : G) * (a : G)⁻¹ ∈ H0 := by
      simpa [aM, xM, Subgroup.mem_subgroupOf] using hconjM
    simpa [H0MF, Subgroup.mem_subgroupOf,
      Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe, hA_norm_MF] using hconjH0
  constructor
  intro a x
  constructor
  · exact hforward a x
  · intro hx
    have hx' : (a⁻¹ : A) • (a • x) ∈ H0MF := hforward a⁻¹ (a • x) hx
    simpa using hx'

-- (6.1) S(A) = {Ind_K^L θ | θ ∈ Irr K, A ⊆ ker θ, θ ≠ 1_K }                      A ⊆ K, A ◁ L
-- (9.5) S(Y) = {Ind_{HU}^M χ | χ ∈ X(Y)} = {Ind_{HU}^M χ | χ ∈ X, Y ⊆ ker χ}
--            = {Ind_{HU}^M χ | χ ∈ Irr HU, H ⊄ ker χ, Y ⊆ ker χ}                 Y ⊆ HU

/-- A book-facing family `S(Y)` of characters induced from `M'`. -/
@[expose] public def kernelInducedFamily
    {G : Type u} [Group G] [Finite G]
    (M N H Y : Subgroup G)
    (S : Finset (Section1.ClassFunction M)) : Prop :=
  Y ≤ N ∧
    H ≤ N ∧
    ∀ χ : Section1.ClassFunction M,
      χ ∈ S ↔
        ∃ θ : Section1.ClassFunction (N.subgroupOf M),
          Section1.IsIrreducibleCharacterOnGroup θ ∧
            ¬ Section1.subgroupInKernel' θ ((H.subgroupOf M).subgroupOf (N.subgroupOf M)) ∧
            Section1.subgroupInKernel' θ ((Y.subgroupOf M).subgroupOf (N.subgroupOf M)) ∧
            χ = Section1.inducedCF (N.subgroupOf M) θ

public theorem subgroupInKernel'_mono_sec9
    {H : Type u} [Group H]
    {A B : Subgroup H}
    (hAB : A ≤ B)
    {χ : Section1.ClassFunction H} :
    Section1.subgroupInKernel' χ B →
      Section1.subgroupInKernel' χ A := by
  intro hB a
  exact hB ⟨a.1, hAB a.2⟩

public theorem principalCharacter_subgroupInKernel'_sec9
    {H : Type u} [Group H]
    (A : Subgroup H) :
    Section1.subgroupInKernel' (Section1.principalCharacter H) A := by
  intro a
  simp [Section1.principalCharacter, Section1.degree]

public theorem ne_principalCharacter_of_not_subgroupInKernel'_sec9
    {H : Type u} [Group H]
    {A : Subgroup H}
    {χ : Section1.ClassFunction H} :
    ¬ Section1.subgroupInKernel' χ A →
      χ ≠ Section1.principalCharacter H := by
  intro hnot hχ
  exact hnot (by
    rw [hχ]
    exact principalCharacter_subgroupInKernel'_sec9 A)

public theorem inducedFromNonkernelFamily_of_kernelInducedFamily_sec9
    {G : Type u} [Group G] [Finite G]
    (M N H Y : Subgroup G)
    (S : Finset (Section1.ClassFunction M)) :
    kernelInducedFamily M N H Y S →
      Section5.inducedFromNonkernelFamily_statement
        (N.subgroupOf M) (H.subgroupOf M) S := by
  intro hS χ hχ
  rcases hS with ⟨_hYN, _hHN, hmem⟩
  rcases (hmem χ).mp hχ with ⟨θ, hθirr, hθne, _hθker, hχeq⟩
  exact ⟨θ, hθirr, hθne, hχeq⟩

public theorem kernelInducedFamily_subset_of_le_sec9
    {G : Type u} [Group G] [Finite G]
    (M N H Y1 Y2 : Subgroup G)
    (S1 S2 : Finset (Section1.ClassFunction M)) :
    Y1 ≤ Y2 →
      kernelInducedFamily M N H Y1 S1 →
        kernelInducedFamily M N H Y2 S2 →
          S2 ⊆ S1 := by
  intro hY hS1 hS2 χ hχ
  rcases hS1 with ⟨_hY1N, _hHN1, hmem1⟩
  rcases hS2 with ⟨_hY2N, _hHN2, hmem2⟩
  rcases (hmem2 χ).mp hχ with ⟨θ, hθirr, hθne, hθker, hχeq⟩
  rw [hmem1 χ]
  refine ⟨θ, hθirr, hθne, ?_, hχeq⟩
  refine subgroupInKernel'_mono_sec9 ?_ hθker
  intro a ha
  rw [Subgroup.mem_subgroupOf] at ha ⊢
  exact hY ha

public noncomputable def kernelInducedSubfamily_sec9
    {G : Type u} [Group G] [Finite G]
    (M N H Y : Subgroup G)
    (S : Finset (Section1.ClassFunction M)) : Finset (Section1.ClassFunction M) := by
  classical
  exact S.filter fun χ =>
    ∃ θ : Section1.ClassFunction (N.subgroupOf M),
      Section1.IsIrreducibleCharacterOnGroup θ ∧
        ¬ Section1.subgroupInKernel' θ ((H.subgroupOf M).subgroupOf (N.subgroupOf M)) ∧
        Section1.subgroupInKernel' θ ((Y.subgroupOf M).subgroupOf (N.subgroupOf M)) ∧
        χ = Section1.inducedCF (N.subgroupOf M) θ

public theorem kernelInducedSubfamily_subset_sec9
    {G : Type u} [Group G] [Finite G]
    (M N H Y : Subgroup G)
    (S : Finset (Section1.ClassFunction M)) :
    kernelInducedSubfamily_sec9 M N H Y S ⊆ S := by
  classical
  intro χ hχ
  rw [kernelInducedSubfamily_sec9] at hχ
  exact (Finset.mem_filter.mp hχ).1

public theorem kernelInducedFamily_subfamily_of_le_sec9
    {G : Type u} [Group G] [Finite G]
    (M N H Y0 Y : Subgroup G)
    (S : Finset (Section1.ClassFunction M)) :
    Y ≤ N →
      Y0 ≤ Y →
        kernelInducedFamily M N H Y0 S →
          kernelInducedFamily M N H Y (kernelInducedSubfamily_sec9 M N H Y S) := by
  classical
  intro hYN hY0Y hS
  rcases hS with ⟨_hY0N, hHN, hmemS⟩
  constructor
  · exact hYN
  constructor
  · exact hHN
  · intro χ
    constructor
    · intro hχ
      exact (Finset.mem_filter.mp hχ).2
    · intro hχ
      rw [kernelInducedSubfamily_sec9, Finset.mem_filter]
      refine ⟨?_, hχ⟩
      rw [hmemS χ]
      rcases hχ with ⟨θ, hθirr, hθne, hθker, hχeq⟩
      refine ⟨θ, hθirr, hθne, ?_, hχeq⟩
      refine subgroupInKernel'_mono_sec9 ?_ hθker
      intro a ha
      rw [Subgroup.mem_subgroupOf] at ha ⊢
      exact hY0Y ha

public theorem conjugateCharacter_inducedCF_sec9
    {G : Type u} [Group G] [Finite G]
    (H : Subgroup G) [Finite H]
    (theta : Section1.ClassFunction H) :
    Section1.conjugateCharacter (Section1.inducedCF H theta) =
      Section1.inducedCF H (Section1.conjugateCharacter theta) := by
  classical
  letI := Fintype.ofFinite G
  funext g
  unfold Section1.conjugateCharacter Section1.inducedCF Section1.inducedClassFunction
  calc
    star ((Nat.card H : ℂ)⁻¹ *
        ∑ x : G, (if hx : x * g * x⁻¹ ∈ H then theta ⟨x * g * x⁻¹, hx⟩ else 0)) =
      (Nat.card H : ℂ)⁻¹ *
        star (∑ x : G,
          (if hx : x * g * x⁻¹ ∈ H then theta ⟨x * g * x⁻¹, hx⟩ else 0)) := by
          simp
    _ = (Nat.card H : ℂ)⁻¹ *
        ∑ x : G, star
          (if hx : x * g * x⁻¹ ∈ H then theta ⟨x * g * x⁻¹, hx⟩ else 0) := by
          rw [star_sum]
    _ = (Nat.card H : ℂ)⁻¹ *
        ∑ x : G,
          (if hx : x * g * x⁻¹ ∈ H then
            (Section1.conjugateCharacter theta) ⟨x * g * x⁻¹, hx⟩ else 0) := by
          congr 1
          refine Finset.sum_congr rfl ?_
          intro x _hx
          by_cases hmem : x * g * x⁻¹ ∈ H
          · simp [hmem]
            rfl
          · simp [hmem]

public theorem subgroupInKernel'_conjugateCharacter_iff_sec9
    {H : Type u} [Group H]
    (phi : Section1.ClassFunction H) (A : Subgroup H) :
    Section1.subgroupInKernel' (Section1.conjugateCharacter phi) A ↔
      Section1.subgroupInKernel' phi A := by
  constructor
  · intro h a
    have ha := h a
    simpa [Section1.subgroupInKernel', Section1.conjugateCharacter, Section1.degree]
      using congrArg star ha
  · intro h a
    have ha := h a
    simpa [Section1.subgroupInKernel', Section1.conjugateCharacter, Section1.degree]
      using congrArg star ha

public theorem isIrreducibleCharacterOnGroup_conjugateCharacter_sec9
    {G : Type u} [Group G] [Finite G]
    {χ : Section1.ClassFunction G} :
    Section1.IsIrreducibleCharacterOnGroup χ →
      Section1.IsIrreducibleCharacterOnGroup (Section1.conjugateCharacter χ) := by
  rintro ⟨n, ρ, hρirr, hχchar⟩
  have hdualirr : Representation.IsIrreducible ρ.dual :=
    Section1.representation_dual_irreducible_of ρ hρirr
  have hdualchar : Section1.conjugateCharacter ρ.character = ρ.dual.character := by
    ext g
    calc
      Section1.conjugateCharacter ρ.character g = star (ρ.character g) := by
        simp [Section1.conjugateCharacter]
      _ = ρ.character g⁻¹ := by
        exact (Section1.representation_character_inv_eq_star_character ρ g).symm
      _ = ρ.dual.character g := by
        rw [Representation.char_dual]
  rw [hχchar, hdualchar]
  exact Section1.isIrreducibleCharacterOnGroup_of_representation ρ.dual hdualirr

public theorem kernelInducedFamily_conjugate_mem_of_irreducible_conj_sec9
    {G : Type u} [Group G] [Finite G]
    (M N H Y : Subgroup G)
    (S : Finset (Section1.ClassFunction M)) :
    (∀ θ : Section1.ClassFunction (N.subgroupOf M),
      Section1.IsIrreducibleCharacterOnGroup θ →
        Section1.IsIrreducibleCharacterOnGroup (Section1.conjugateCharacter θ)) →
      kernelInducedFamily M N H Y S →
        ∀ χ : Section1.ClassFunction M,
          χ ∈ S → Section1.conjugateCharacter χ ∈ S := by
  intro hirrConj hS χ hχ
  rcases hS with ⟨_hYN, _hHN, hmem⟩
  rcases (hmem χ).mp hχ with ⟨θ, hθirr, hθne, hθker, hχeq⟩
  rw [hmem (Section1.conjugateCharacter χ)]
  refine ⟨Section1.conjugateCharacter θ, hirrConj θ hθirr, ?_, ?_, ?_⟩
  · intro hker
    exact hθne ((subgroupInKernel'_conjugateCharacter_iff_sec9 θ
      ((H.subgroupOf M).subgroupOf (N.subgroupOf M))).mp hker)
  · exact (subgroupInKernel'_conjugateCharacter_iff_sec9 θ
      ((Y.subgroupOf M).subgroupOf (N.subgroupOf M))).mpr hθker
  · rw [hχeq]
    exact conjugateCharacter_inducedCF_sec9 (N.subgroupOf M) θ

public theorem kernelInducedFamily_conjugationClosed_sec9
    {G : Type u} [Group G] [Finite G]
    (M N H Y : Subgroup G)
    (S : Finset (Section1.ClassFunction M)) :
    kernelInducedFamily M N H Y S →
      ∀ χ : Section1.ClassFunction M,
        χ ∈ S → Section1.conjugateCharacter χ ∈ S := by
  exact kernelInducedFamily_conjugate_mem_of_irreducible_conj_sec9
    M N H Y S (fun θ hθ => isIrreducibleCharacterOnGroup_conjugateCharacter_sec9 hθ)

public theorem msChoice_of_hypothesis_9_2_sec9
    {G : Type u} [Group G] [Finite G]
    (M MF U W1 W2 : Subgroup G) :
  hypothesis_9_2_statement M MF U W1 W2 (Nat.card W1) →
      ∃ Ms : Subgroup G, Section8.msChoice M MF Ms := by
  intro h92
  rcases h92.typeCases with hII | hIII | hIV
  · exact ⟨MF, Or.inl ⟨Or.inr (Or.inl hII), rfl⟩⟩
  · exact ⟨ambientDerivedSubgroup M, Or.inr ⟨Or.inl hIII, rfl⟩⟩
  · exact ⟨ambientDerivedSubgroup M, Or.inr ⟨Or.inr hIV, rfl⟩⟩

public theorem mf_le_msChoice_of_hypothesis_9_2_sec9
    {G : Type u} [Group G] [Finite G]
    (M MF U W1 W2 Ms : Subgroup G) :
    hypothesis_9_2_statement M MF U W1 W2 (Nat.card W1) →
      Section8.msChoice M MF Ms →
        MF ≤ Ms := by
  intro h92 hMs
  rcases h92.typeP with ⟨_hMFtype, hcommon⟩
  rcases hcommon with
    ⟨_hhall, hMFleDer, _hcomp, _hnil, _hW1norm, _hW1cyc, _hW1card,
      _hMFnotcyc, _hsecond, _hfitting, _hfittingDer, _hW2le, _hW2ne, _hW2cyc,
      _hcentralizer, _hhat, _hprimeCentralizer⟩
  rcases hMs with hMs | hMs
  · rcases hMs with ⟨_htype, rfl⟩
    exact le_rfl
  · rcases hMs with ⟨_htype, rfl⟩
    exact hMFleDer

public theorem W1_le_M_of_hypothesis_9_2_sec9
    {G : Type u} [Group G] [Finite G]
    (M MF U W1 W2 : Subgroup G)
    (q : ℕ) :
    hypothesis_9_2_statement M MF U W1 W2 q →
      W1 ≤ M := by
  intro h92
  rcases h92.typePDefinitionData with
    ⟨_hMFsource, _hW1cyc, _hW1ne, _hW1hall, hcompMW1, _hrest⟩
  exact hcompMW1.2.1

public theorem MF_le_ambientDerived_of_hypothesis_9_2_sec9
    {G : Type u} [Group G] [Finite G]
    (M MF U W1 W2 : Subgroup G)
    (q : ℕ) :
    hypothesis_9_2_statement M MF U W1 W2 q →
      MF ≤ ambientDerivedSubgroup M := by
  intro h92
  rcases h92.typeP with ⟨_hMFtype, hcommon⟩
  rcases hcommon with
    ⟨_hhall, hMFleDer, _hcomp, _hnil, _hW1norm, _hW1cyc, _hW1card,
      _hMFnotcyc, _hsecond, _hfitting, _hfittingDer, _hW2le, _hW2ne, _hW2cyc,
      _hcentralizer, _hhat, _hprimeCentralizer⟩
  exact hMFleDer

public theorem section8InducedNonkernelFamily_of_kernelInducedFamily_le_sec9
    {G : Type u} [Group G] [Finite G]
    (M H Ms Y : Subgroup G)
    (S : Finset (Section1.ClassFunction M)) :
    H ≤ Ms →
      kernelInducedFamily M (ambientDerivedSubgroup M) H Y S →
        S.Nonempty →
          (∀ χ : Section1.ClassFunction M,
            χ ∈ S → Section1.conjugateCharacter χ ∈ S) →
            Section8.section8InducedNonkernelFamily M Ms S := by
  intro hHMs hS hne hclosed
  refine ⟨hne, hclosed, ?_⟩
  intro χ hχ
  have hχ_ambient :
      ∃ θ : Section1.ClassFunction ((ambientDerivedSubgroup M).subgroupOf M),
        Section1.IsIrreducibleCharacterOnGroup θ ∧
          (¬ ∀ m : ((ambientDerivedSubgroup M).subgroupOf M),
            ((m : M) : G) ∈ Ms → θ m = θ 1) ∧
            χ = Section1.inducedCF ((ambientDerivedSubgroup M).subgroupOf M) θ := by
    rcases hS with ⟨_hY, _hH, hmem⟩
    rcases (hmem χ).mp hχ with ⟨θ, hθirr, hθne, _hθker, hχeq⟩
    refine ⟨θ, hθirr, ?_, hχeq⟩
    intro hsec
    apply hθne
    intro a
    have haH :
        (((a : (H.subgroupOf M).subgroupOf
            ((ambientDerivedSubgroup M).subgroupOf M)) :
            ((ambientDerivedSubgroup M).subgroupOf M)) : M) ∈ H.subgroupOf M :=
      a.property
    exact hsec a.1 (hHMs (by simpa [Subgroup.mem_subgroupOf] using haH))
  let P : Subgroup M → Prop := fun N =>
    ∃ θ : Section1.ClassFunction N,
      Section1.IsIrreducibleCharacterOnGroup θ ∧
        (∃ x ∈ Ms, ∃ (xM : x ∈ M) (xN : (⟨x, xM⟩ : M) ∈ N),
          ¬ θ ⟨⟨x, xM⟩, xN⟩ = θ 1) ∧
          χ = Section1.inducedCF N θ
  have hP : P (derivedSubgroup M) := by
    have hambient : P ((ambientDerivedSubgroup M).subgroupOf M) := by
      simpa [P] using hχ_ambient
    have hEq : ((ambientDerivedSubgroup M).subgroupOf M) = derivedSubgroup M :=
      section12_ambientDerivedSubgroup_subgroupOf_eq (E := M)
    exact hEq ▸ hambient
  rcases hP with ⟨θ, hθirr, hθnonker, hχeq⟩
  refine ⟨θ, hθirr, ?_, hχeq⟩
  intro hker
  rcases hθnonker with ⟨x, hxMs, xM, xN, hxne⟩
  exact hxne (hker ⟨⟨x, xM⟩, xN⟩ hxMs)


public theorem section8InducedNonkernelFamily_of_kernelInducedFamily_le_nonempty_sec9
    {G : Type u} [Group G] [Finite G]
    (M H Ms Y : Subgroup G)
    (S : Finset (Section1.ClassFunction M)) :
    H ≤ Ms →
      kernelInducedFamily M (ambientDerivedSubgroup M) H Y S →
        S.Nonempty →
          Section8.section8InducedNonkernelFamily M Ms S := by
  intro hHMs hS hne
  exact section8InducedNonkernelFamily_of_kernelInducedFamily_le_sec9
    M H Ms Y S hHMs hS hne
    (kernelInducedFamily_conjugationClosed_sec9 M (ambientDerivedSubgroup M) H Y S hS)

public theorem section8InducedNonkernelFamily_of_kernelInducedFamily_msChoice_nonempty_sec9
    {G : Type u} [Group G] [Finite G]
    (M MF U W1 W2 Ms Y : Subgroup G)
    (S : Finset (Section1.ClassFunction M)) :
    hypothesis_9_2_statement M MF U W1 W2 (Nat.card W1) →
      Section8.msChoice M MF Ms →
        kernelInducedFamily M (ambientDerivedSubgroup M) MF Y S →
          S.Nonempty →
            Section8.section8InducedNonkernelFamily M Ms S := by
  intro h92 hMs hS hne
  exact section8InducedNonkernelFamily_of_kernelInducedFamily_le_nonempty_sec9
    M MF Ms Y S (mf_le_msChoice_of_hypothesis_9_2_sec9 M MF U W1 W2 Ms h92 hMs)
    hS hne


public theorem theorem_8_15_data_and_family_of_hypothesis_9_2_kernelInducedFamily_sec9
    {G : Type u} [Group G] [Finite G]
    (M MF U W1 W2 Y : Subgroup G)
    (S : Finset (Section1.ClassFunction M)) :
    hypothesis_9_2_statement M MF U W1 W2 (Nat.card W1) →
      kernelInducedFamily M (ambientDerivedSubgroup M) MF Y S →
        S.Nonempty →
          ∃ K U8 Ms : Subgroup G, ∃ A : Set G, ∃ R : G → Subgroup G,
            Section8.theorem_8_15_data M MF K U8 Ms A R S ∧
              Section8.section8InducedNonkernelFamily M Ms S := by
  intro h92 hS hne
  rcases msChoice_of_hypothesis_9_2_sec9 M MF U W1 W2 h92 with ⟨Ms, hMs⟩
  refine ⟨⊥, U, Ms, section16ASet M U, fun _ => ⊥, ?_, ?_⟩
  · exact ⟨⟨hMs, Or.inl rfl, Or.inr rfl⟩, (by intro x hx; exact Or.inr rfl), hne⟩
  · exact section8InducedNonkernelFamily_of_kernelInducedFamily_msChoice_nonempty_sec9
      M MF U W1 W2 Ms Y S h92 hMs hS hne


public theorem not_typeIII_or_typeIV_of_hypothesis_9_2_typeII_sec9
    {G : Type u} [Group G] [Finite G]
    (M MF U W1 W2 : Subgroup G)
    (q : ℕ) :
    hypothesis_9_2_statement M MF U W1 W2 q →
      section16TypeII M MF →
        ¬ (section16TypeIII M MF ∨ section16TypeIV M MF) := by
  intro h92 hII hIIIIV
  have hIIsource := h92.typeIISource
  have hIIIsource := h92.typeIIISource
  have hIVsource := h92.typeIVSource
  have hnotNorm : ¬ Subgroup.normalizer (U : Set G) ≤ M := by
    exact (hIIsource hII).2.1
  rcases hIIIIV with hIII | hIV
  · exact hnotNorm (hIIIsource hIII).2
  · exact hnotNorm (hIVsource hIV).2


public theorem nat_card_W1_prime_of_hypothesis_9_2_sec9
    {G : Type u} [Group G] [Finite G]
    (M MF U W1 W2 : Subgroup G) :
  hypothesis_9_2_statement M MF U W1 W2 (Nat.card W1) →
      Nat.Prime (Nat.card W1) := by
  intro h92
  rcases h92.typeP with ⟨_hMFtype, hcommon⟩
  rcases hcommon with
    ⟨_hhall, _hMFder, _hcomp, _hnil, _hW1norm, _hW1cyc, hW1card,
      _hMFnotcyc, _hsecond, _hfitting, _hfittingDer, _hW2le, _hW2ne, _hW2cyc,
      _hcentralizer, _hhat, _hprimeCentralizer⟩
  have from_common_extra :
      ∀ {V W1' W2' : Subgroup G},
        section16TypeCommon M MF V W1' W2' →
          section16TypeIIToIVExtra M W1' →
            Nat.Prime (Nat.card W1) := by
    intro V W1' W2' hcommon' hextra
    rcases hcommon' with
      ⟨_hhall', _hMFder', _hcomp', _hnil', _hW1norm', _hW1cyc', hW1card',
        _hMFnotcyc', _hsecond', _hfitting', _hfittingDer', _hW2le', _hW2ne',
        _hW2cyc', _hcentralizer', _hhat', _hprimeCentralizer'⟩
    rcases hextra with ⟨hprimeOrder, _hTI⟩
    rcases hprimeOrder with ⟨q, hqcard⟩
    have hcard : Nat.card W1 = q.val := by
      rw [hW1card, ← hW1card', hqcard]
    rw [hcard]
    exact q.2
  rcases h92.typeCases with hII | hIII | hIV
  · rcases hII with ⟨V, W1', W2', hcommon', hextra, _hrest⟩
    exact from_common_extra hcommon' hextra
  · rcases hIII with ⟨V, W1', W2', hcommon', hextra, _hrest⟩
    exact from_common_extra hcommon' hextra
  · rcases hIV with ⟨V, W1', W2', hcommon', hextra, _hrest⟩
    exact from_common_extra hcommon' hextra

public theorem q_prime_of_hypothesis_9_2_sec9
    {G : Type u} [Group G] [Finite G]
    (M MF U W1 W2 : Subgroup G)
    (q : ℕ) :
    hypothesis_9_2_statement M MF U W1 W2 q →
      Nat.Prime q := by
  intro h92
  have hW1prime : Nat.Prime (Nat.card W1) := by
    have h92W1 : hypothesis_9_2_statement M MF U W1 W2 (Nat.card W1) :=
      hypothesis_9_2_with_card_W1_sec9 h92
    exact nat_card_W1_prime_of_hypothesis_9_2_sec9 M MF U W1 W2 h92W1
  rwa [h92.q_eq] at hW1prime

public theorem complement_le_right_sec9
    {G : Type u} [Group G] [Finite G]
    {H K L : Subgroup G} :
    section12ComplementIn H K L → L ≤ H := by
  intro h
  exact h.2.1

public theorem section12ComplementIn_left_isComplement'_subgroupOf_sec9
    {G : Type u} [Group G] [Finite G]
    {M H K : Subgroup G}
    (hcomp : section12ComplementIn M H K)
    [hHnormal : (H.subgroupOf M).Normal] :
    (H.subgroupOf M).IsComplement' (K.subgroupOf M) := by
  rcases hcomp with ⟨hHM, hKM, hsup, hdisj⟩
  have hdisjSub : Disjoint (H.subgroupOf M) (K.subgroupOf M) := by
    rw [disjoint_iff] at hdisj ⊢
    apply le_antisymm
    · intro x hx
      have hxAmb : (x : G) ∈ H ⊓ K := by
        exact ⟨by simpa [Subgroup.mem_subgroupOf] using hx.1,
          by simpa [Subgroup.mem_subgroupOf] using hx.2⟩
      have hxBot : (x : G) ∈ (⊥ : Subgroup G) := by
        simpa [hdisj] using hxAmb
      ext
      simpa using hxBot
    · exact bot_le
  have hsupTop : H.subgroupOf M ⊔ K.subgroupOf M = ⊤ := by
    rw [← Subgroup.subgroupOf_sup (A := H) (A' := K) (B := M) hHM hKM]
    apply Subgroup.subgroupOf_eq_top.2
    intro x hxM
    change x ∈ H ⊔ K
    simpa [← hsup] using hxM
  letI : (H.subgroupOf M).Normal := hHnormal
  exact isComplement'_of_disjoint_sup_eq_top_of_normal
    (H.subgroupOf M) (K.subgroupOf M) hdisjSub hsupTop

public theorem internalSemidirectProduct_top_of_normal_isComplement'_sec9
    {L : Type u} [Group L]
    {H K : Subgroup L} [H.Normal]
    (hcomp : H.IsComplement' K) :
    Section2.IsInternalSemidirectProduct (⊤ : Subgroup L) H K := by
  refine ⟨by intro _ _; trivial, by intro _ _; trivial, ?_, ?_, ?_⟩
  · intro k _ h hh
    simpa [Section2.conjBy] using
      (inferInstance : H.Normal).conj_mem h hh k
  · apply le_antisymm
    · intro x hx
      exact (Subgroup.disjoint_def.mp hcomp.disjoint) hx.1 hx.2
    · exact bot_le
  · intro c _hc
    rcases hcomp.2 c with ⟨⟨⟨h, hhH⟩, ⟨k, hkK⟩⟩, hck⟩
    exact ⟨h, hhH, k, hkK, hck.symm⟩

public theorem solvable_of_normal_and_quotient_sec9
    {L : Type u} [Group L]
    (N : Subgroup L) [N.Normal] :
    Group.IsSolvable N →
      Group.IsSolvable (L ⧸ N) →
        Group.IsSolvable L := by
  intro hN hQ
  let : Group.IsSolvable N := hN
  let : Group.IsSolvable (L ⧸ N) := hQ
  exact
    Group.isSolvable_of_ker_le_range
      N.subtype
      (QuotientGroup.mk' N)
      (by
        intro x hx
        refine ⟨⟨x, ?_⟩, rfl⟩
        exact (QuotientGroup.eq_one_iff (N := N) (x := x)).1 hx)

public theorem typePDefinitionData_ambientDerived_solvable_sec9
    {G : Type u} [Group G] [Finite G]
    {M MF U W1 W2 : Subgroup G}
    (hP : Section8.typePDefinitionData M MF U W1 W2) :
    IsSolvable (ambientDerivedSubgroup M) := by
  classical
  let D : Subgroup G := ambientDerivedSubgroup M
  rcases hP with
    ⟨hMF, _hW1cyc, _hW1ne, _hW1hall, _hcompMW1, _hUleD, hUnil,
      _hW1normU, hcompDU, _hMFnotCyc, _hSecond, _hFitEq, _hFitLeD,
      _hW2le, _hW2cyc, _hW2ne, _hCent, _hHatW⟩
  rcases hMF with ⟨hMFhall, _hMFmax⟩
  rcases hMFhall with ⟨hMFleM, hMFnormM, hMFnil, _hMFhall⟩
  have hDleM : D ≤ M := by
    simpa [D] using (section12_ambientDerivedSubgroup_le (G := G) (E := M))
  have hM_norm_MF : M ≤ Subgroup.normalizer (MF : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hMFleM).1 hMFnormM
  have hD_norm_MF : D ≤ Subgroup.normalizer (MF : Set G) :=
    hDleM.trans hM_norm_MF
  have hMFnormD : (MF.subgroupOf D).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer
      (by simpa [D] using hcompDU.1)).2 hD_norm_MF
  have hMFUdisjSub : Disjoint (MF.subgroupOf D) (U.subgroupOf D) := by
    have hdisj : Disjoint MF U := hcompDU.2.2.2
    rw [disjoint_iff] at hdisj ⊢
    apply le_antisymm
    · intro x hx
      have hxAmb : (x : G) ∈ MF ⊓ U := by
        exact ⟨by simpa [Subgroup.mem_subgroupOf, D] using hx.1,
          by simpa [Subgroup.mem_subgroupOf, D] using hx.2⟩
      have hxBot : (x : G) ∈ (⊥ : Subgroup G) := by
        simpa [hdisj] using hxAmb
      ext
      simpa using hxBot
    · exact bot_le
  have hMFUsupTop : MF.subgroupOf D ⊔ U.subgroupOf D = ⊤ := by
    rw [← Subgroup.subgroupOf_sup (A := MF) (A' := U) (B := D)
      (by simpa [D] using hcompDU.1) hcompDU.2.1]
    apply Subgroup.subgroupOf_eq_top.2
    intro x hxD
    change x ∈ D at hxD
    simpa [D, hcompDU.2.2.1] using hxD
  have hcompMFU : (MF.subgroupOf D).IsComplement' (U.subgroupOf D) := by
    letI : (MF.subgroupOf D).Normal := hMFnormD
    exact isComplement'_of_disjoint_sup_eq_top_of_normal
      (MF.subgroupOf D) (U.subgroupOf D) hMFUdisjSub hMFUsupTop
  have hMFsub_solv : Group.IsSolvable (MF.subgroupOf D) := by
    have hMFsub_nil : Group.IsNilpotent (MF.subgroupOf D) := by
      haveI : Group.IsNilpotent MF := hMFnil
      exact Group.nilpotent_of_mulEquiv
        (Subgroup.subgroupOfEquivOfLe (by simpa [D] using hcompDU.1)).symm
    haveI : Group.IsNilpotent (MF.subgroupOf D) := hMFsub_nil
    infer_instance
  have hquot_solv : Group.IsSolvable (D ⧸ MF.subgroupOf D) := by
    have hUsub_nil : Group.IsNilpotent (U.subgroupOf D) := by
      haveI : Group.IsNilpotent U := hUnil
      exact Group.nilpotent_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hcompDU.2.1).symm
    haveI : Group.IsNilpotent (U.subgroupOf D) := hUsub_nil
    let : Group.IsSolvable (U.subgroupOf D) := by infer_instance
    exact Group.isSolvable_of_isSolvable_injective
      (f := hcompMFU.symm.QuotientMulEquiv.toMonoidHom)
      hcompMFU.symm.QuotientMulEquiv.injective
  letI : (MF.subgroupOf D).Normal := hMFnormD
  exact solvable_of_normal_and_quotient_sec9 (MF.subgroupOf D)
    hMFsub_solv hquot_solv

public theorem typePDefinitionData_W1_card_coprime_ambientDerived_sec9
    {G : Type u} [Group G] [Finite G]
    {M MF U W1 W2 : Subgroup G}
    (hP : Section8.typePDefinitionData M MF U W1 W2) :
    Nat.Coprime (Nat.card W1) (Nat.card (ambientDerivedSubgroup M)) := by
  classical
  rcases hP with
    ⟨_hMF, _hW1cyc, _hW1ne, hW1hall, hcompMW1, _hUleD, _hUnil,
      _hW1normU, _hcompDU, _hMFnotCyc, _hM2le, _hFitEq, _hFitLeD,
      _hW2le, _hW2cyc, _hW2ne, _hCent, _hHatW⟩
  let D : Subgroup G := ambientDerivedSubgroup M
  have hDnormalM : (D.subgroupOf M).Normal := by
    simpa [D] using (section12_normalIn_ambientDerivedSubgroup (G := G) (E := M)).2
  letI : (D.subgroupOf M).Normal := hDnormalM
  have hcompLocal : (D.subgroupOf M).IsComplement' (W1.subgroupOf M) :=
    section12ComplementIn_left_isComplement'_subgroupOf_sec9 hcompMW1
  rcases hW1hall with ⟨hW1M, hHallW1⟩
  have hW1card : Nat.card (W1.subgroupOf M) = Nat.card W1 :=
    natCard_subgroupOf_eq W1 M hW1M
  have hDcard : Nat.card (D.subgroupOf M) = Nat.card D :=
    natCard_subgroupOf_eq D M hcompMW1.1
  have hindex : (W1.subgroupOf M).index = Nat.card (D.subgroupOf M) :=
    hcompLocal.index_eq_card
  have hcopSub :
      Nat.Coprime (Nat.card (W1.subgroupOf M)) (Nat.card (D.subgroupOf M)) := by
    rw [← hindex]
    exact hHallW1.card_coprime_index
  rw [hW1card, hDcard] at hcopSub
  simpa [D] using hcopSub

public theorem isHallSubgroup_map_of_surjective_sec9
    {G G' : Type*} [Group G] [Finite G] [Group G'] [Finite G']
    {π : Set Nat.Primes} {H : Subgroup G}
    (hHall : IsHallSubgroup π H)
    (f : G →* G') (hf : Function.Surjective f) :
    IsHallSubgroup π (H.map f) := by
  refine isHallSubgroup_of (G := G') (π := π) (H := H.map f)
    (hcard := ?_) (hindex := ?_)
  · intro q hq_dvd
    exact hHall.p_in_pi_of_p_dvd_card q
      (hq_dvd.trans (Subgroup.card_map_dvd (H := H) f))
  · intro q hq_mem hq_dvd_idx
    have hidx_dvd : (H.map f).index ∣ H.index :=
      Subgroup.index_map_dvd (H := H) hf
    exact (hHall.p_in_pi_of_p_dvd_index q
      (hq_dvd_idx.trans hidx_dvd)) hq_mem

public theorem ambientDerived_W1_isComplement'_subgroupOf_M_of_hypothesis_9_2_sec9
    {G : Type u} [Group G] [Finite G]
    (M MF U W1 W2 : Subgroup G)
    (q : ℕ) :
    hypothesis_9_2_statement M MF U W1 W2 q →
      ((ambientDerivedSubgroup M).subgroupOf M).IsComplement' (W1.subgroupOf M) := by
  intro h92
  rcases h92.typePDefinitionData with
    ⟨_hMFsource, _hW1cyc, _hW1ne, _hW1hall, hcompMW1, _hrest⟩
  have hDnormal : ((ambientDerivedSubgroup M).subgroupOf M).Normal := by
    simpa using (section12_normalIn_ambientDerivedSubgroup (G := G) (E := M)).2
  letI : ((ambientDerivedSubgroup M).subgroupOf M).Normal := hDnormal
  exact section12ComplementIn_left_isComplement'_subgroupOf_sec9 hcompMW1

public theorem W2_le_M_of_hypothesis_9_2_sec9
    {G : Type u} [Group G] [Finite G]
    (M MF U W1 W2 : Subgroup G)
    (q : ℕ) :
    hypothesis_9_2_statement M MF U W1 W2 q →
      W2 ≤ M := by
  intro h92
  rcases h92.typePDefinitionData with
    ⟨hMFsource, _hW1cyc, _hW1ne, _hW1hall, _hcompMW1, _hUleD,
      _hUnil, _hW1normU, _hcompDU, _hMFnotCyc, _hSecondLe, _hFittingEq,
      _hFittingLeD, hW2le, _hW2cyc, _hW2ne, _hCent, _hHatW⟩
  intro x hx
  exact hMFsource.1.1 ((hW2le hx).1)

/-- Natural divisibility of the degree of a class function. -/
@[expose] public def characterDegreeDivisibleBy
    {G : Type u} [Group G]
    (n : ℕ)
    (χ : Section1.ClassFunction G) : Prop :=
  ∃ d : ℕ, Section1.degree χ = (d : ℂ) ∧ n ∣ d

public theorem characterDegreeDivisibleBy_inducedCF_of_constituent_sec9
    {G : Type u} [Group G] [Finite G]
    (N : Subgroup G) (n : ℕ)
    (χ : Section1.ClassFunction G) (θ : Section1.ClassFunction N) :
    characterDegreeDivisibleBy n θ →
      χ = Section1.inducedCF N θ →
        characterDegreeDivisibleBy n χ := by
  intro hθ hχ
  rcases hθ with ⟨d, hdeg, hdiv⟩
  refine ⟨N.index * d, ?_, ?_⟩
  · rw [hχ, Section1.degree_inducedClassFunction, hdeg]
    norm_num
  · exact Nat.dvd_mul_left_of_dvd hdiv N.index

public theorem characterDegreeDivisibleBy_inducedCF_of_index_dvd_sec9
    {G : Type u} [Group G] [Finite G]
    (N : Subgroup G) (n : ℕ)
    (χ : Section1.ClassFunction G) (θ : Section1.ClassFunction N) :
    Section1.IsIrreducibleCharacterOnGroup θ →
      χ = Section1.inducedCF N θ →
        n ∣ N.index →
          characterDegreeDivisibleBy n χ := by
  intro hθirr hχ hidx
  rcases hθirr with ⟨V, ρ, _hρirr, hθeq⟩
  refine ⟨N.index * V, ?_, ?_⟩
  · rw [hχ, Section1.degree_inducedClassFunction, hθeq,
      Section1.degree_representation_character]
    simp [Nat.cast_mul]
  · exact Nat.dvd_mul_right_of_dvd hidx V

/-- PF Notation `(9.5)`: the quotient notation together with the Dade map.

This is the source-facing package. It deliberately does not include
Hypothesis `(5.2)(b)`, which is obtained later from `(8.15)` in the source
proof rather than assumed as part of the notation.
-/
public structure notation_9_5_data
    {G : Type u} [Group G] [Finite G]
    (M MF U W1 W2 H0 C Cprime : Subgroup G)
    (T : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G)
    (S : Finset (Section1.ClassFunction M)) : Prop where
  hypothesis92 : hypothesis_9_2_statement M MF U W1 W2 (Nat.card W1)
  hoReduction : ∃ p : Nat.Primes, hoReductionData M MF U W2 H0 p
  quotientCentralizer : quotientCentralizerIn MF H0 U C
  quotientBarU : ∃ u : ℕ, quotientBarUCardinality U C u
  Cprime_le_C : Cprime ≤ C
  Cprime_eq_commutator : Cprime = (_root_.commutator C).map C.subtype
  dade : dadeIsometryRelativeToASet M U T
  kernelInduced : kernelInducedFamily M (ambientDerivedSubgroup M) MF H0 S

/-- Proof-support strengthening of PF `(9.5)`.

The extra `hypothesis52b` field is not part of the printed `(9.5)` notation;
it records the Section `(5.2)(b)` input that downstream Lean proofs currently
use and that the source obtains later from `(8.15)`.
-/
public structure Hypothesis_9_5
    {G : Type u} [Group G] [Finite G]
    (M MF U W1 W2 H0 C Cprime : Subgroup G)
    (T : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G)
    (S : Finset (Section1.ClassFunction M)) : Prop where
  hypothesis92 : hypothesis_9_2_statement M MF U W1 W2 (Nat.card W1)
  hoReduction : ∃ p : Nat.Primes, hoReductionData M MF U W2 H0 p
  quotientCentralizer : quotientCentralizerIn MF H0 U C
  quotientBarU : ∃ u : ℕ, quotientBarUCardinality U C u
  Cprime_le_C : Cprime ≤ C
  Cprime_eq_commutator : Cprime = (_root_.commutator C).map C.subtype
  dade : dadeIsometryRelativeToASet M U T
  kernelInduced : kernelInducedFamily M (ambientDerivedSubgroup M) MF H0 S
  hypothesis52b : Section5.hypothesis_5_2_b_statement S T

public theorem Hypothesis_9_5.to_notation_9_5_data
    {G : Type u} [Group G] [Finite G]
    {M MF U W1 W2 H0 C Cprime : Subgroup G}
    {T : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    {S : Finset (Section1.ClassFunction M)}
    (h : Hypothesis_9_5 M MF U W1 W2 H0 C Cprime T S) :
    notation_9_5_data M MF U W1 W2 H0 C Cprime T S where
  hypothesis92 := h.hypothesis92
  hoReduction := h.hoReduction
  quotientCentralizer := h.quotientCentralizer
  quotientBarU := h.quotientBarU
  Cprime_le_C := h.Cprime_le_C
  Cprime_eq_commutator := h.Cprime_eq_commutator
  dade := h.dade
  kernelInduced := h.kernelInduced

public instance instCoeOutHypothesis_9_5Notation_9_5_data
    {G : Type u} [Group G] [Finite G]
    {M MF U W1 W2 H0 C Cprime : Subgroup G}
    {T : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    {S : Finset (Section1.ClassFunction M)} :
    CoeOut (Hypothesis_9_5 M MF U W1 W2 H0 C Cprime T S)
      (notation_9_5_data M MF U W1 W2 H0 C Cprime T S) where
  coe h := h.to_notation_9_5_data

/-- The quotient/chief-factor conclusion of PF `(9.6)` for `H = MF / H0`. -/
@[expose] public def quotientChiefFactorData_9_6
    {G : Type u} [Group G] [Finite G]
    (M MF H0 W1 : Subgroup G)
    (p : Nat.Primes) : Prop :=
  H0 ≤ MF ∧
    MF ≤ M ∧
    (H0.subgroupOf MF).Normal ∧
    IsChiefFactor (H0.subgroupOf M) (MF.subgroupOf M) ∧
    (∃ hnormal : (H0.subgroupOf MF).Normal,
      letI : (H0.subgroupOf MF).Normal := hnormal
      Nat.card {x : MF ⧸ H0.subgroupOf MF //
        ∀ h : MF, QuotientGroup.mk' (H0.subgroupOf MF) h = x →
          ∀ w : G, w ∈ W1 → ⁅w, (h : G)⁆ ∈ H0} = p.val) ∧
    Nat.card (MF ⧸ H0.subgroupOf MF) = p.val ^ Nat.card W1

/-- Linear induction from a subgroup, used in PF `(9.8)`--`(9.10)`. -/
@[expose] public def inducedFromLinearCharacter
    {G : Type u} [Group G] [Finite G]
    (M N : Subgroup G)
    (χ : Section1.ClassFunction M) : Prop :=
  ∃ θ : Section1.ClassFunction (N.subgroupOf M),
    Section1.IsIrreducibleCharacterOnGroup θ ∧
    Section1.degree θ = (1 : ℂ) ∧
      χ = Section1.inducedCF (N.subgroupOf M) θ

/-- Linear induction from `HC`, with `H = MF`, used in PF `(9.8)`--`(9.10)`. -/
@[expose] public def inducedFromLinearCharacterOfHC
    {G : Type u} [Group G] [Finite G]
    (M MF C : Subgroup G)
    (χ : Section1.ClassFunction M) : Prop :=
  inducedFromLinearCharacter M (MF ⊔ C) χ

public theorem inducedFromLinearCharacter_of_inducedCF_trans_sec9
    {G : Type u} [Group G] [Finite G]
    (M D N : Subgroup G)
    (χ : Section1.ClassFunction M)
    (θD : Section1.ClassFunction (D.subgroupOf M))
    (ψ : Section1.ClassFunction (N.subgroupOf M)) :
    N ≤ D →
      Section1.IsIrreducibleCharacterOnGroup ψ →
        Section1.degree ψ = (1 : ℂ) →
          θD = Section1.inducedCF
            ((N.subgroupOf M).subgroupOf (D.subgroupOf M))
              (Section1.subgroupOfClassFunction ψ) →
            χ = Section1.inducedCF (D.subgroupOf M) θD →
              inducedFromLinearCharacter M N χ := by
  intro hND hψirr hψdeg hθD hχ
  let Nm : Subgroup M := N.subgroupOf M
  let Dm : Subgroup M := D.subgroupOf M
  have hNm_le_Dm : Nm ≤ Dm := by
    intro x hx
    exact hND hx
  refine ⟨ψ, hψirr, hψdeg, ?_⟩
  calc
    χ = Section1.inducedCF Dm θD := hχ
    _ = Section1.inducedCF Dm
        (Section1.inducedCF (Nm.subgroupOf Dm)
          (Section1.subgroupOfClassFunction ψ)) := by
          rw [hθD]
    _ = Section1.inducedCF Nm ψ :=
          Section1.inducedCF_trans Nm Dm hNm_le_Dm ψ

public theorem HMK_index_eq_q_mul_relIndex_of_hypothesis_9_2_sec9
    {G : Type u} [Group G] [Finite G]
    (M MF U W1 W2 K : Subgroup G)
    (q : ℕ) :
    hypothesis_9_2_statement M MF U W1 W2 q →
      K ≤ U →
        Subgroup.index ((MF ⊔ K).subgroupOf M) = q * K.relIndex U := by
  classical
  intro h92 hK_le_U
  let D : Subgroup G := ambientDerivedSubgroup M
  let HK : Subgroup G := MF ⊔ K
  rcases h92.typeP with ⟨hMFtype, hcommon⟩
  rcases hcommon with
    ⟨_hDhall, hMFleD, hcompD, _hnil, _hW1norm, _hW1cyc, hW1card,
      _hMFnotcyc, _hsecond, _hfitting, _hfittingDer, _hW2le, _hW2ne,
      _hW2cyc, _hcentralizer, _hhat, _hprimeCentralizer, _hW2der⟩
  rcases hcompD with ⟨hMFleD', hUleD, hD_eq, hMFUdisj⟩
  have hDleM : D ≤ M := by
    dsimp [D]
    exact section12_ambientDerivedSubgroup_le (E := M)
  rcases hMFtype.1 with ⟨hMFleM, hMFnormalM, _hMFnil, _hMFhall⟩
  have hM_le_norm_MF : M ≤ Subgroup.normalizer (MF : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hMFleM).1 hMFnormalM
  have hD_le_norm_MF : D ≤ Subgroup.normalizer (MF : Set G) :=
    hDleM.trans hM_le_norm_MF
  have hMFnormalD : (MF.subgroupOf D).Normal := by
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer hMFleD).2
      hD_le_norm_MF
  have hMFUdisjSub : Disjoint (MF.subgroupOf D) (U.subgroupOf D) := by
    rw [disjoint_iff] at hMFUdisj ⊢
    apply le_antisymm
    · intro x hx
      have hxAmb : (x : G) ∈ MF ⊓ U := by
        exact ⟨by simpa [Subgroup.mem_subgroupOf] using hx.1,
          by simpa [Subgroup.mem_subgroupOf] using hx.2⟩
      have hxBot : (x : G) ∈ (⊥ : Subgroup G) := by
        simpa [hMFUdisj] using hxAmb
      ext
      simpa using hxBot
    · exact bot_le
  have hMFUsupTop : MF.subgroupOf D ⊔ U.subgroupOf D = ⊤ := by
    rw [← Subgroup.subgroupOf_sup (A := MF) (A' := U) (B := D)
      hMFleD hUleD]
    apply Subgroup.subgroupOf_eq_top.2
    intro x hxD
    change x ∈ D at hxD
    simpa [D, hD_eq] using hxD
  have hcompMFU : (MF.subgroupOf D).IsComplement' (U.subgroupOf D) := by
    letI : (MF.subgroupOf D).Normal := hMFnormalD
    exact isComplement'_of_disjoint_sup_eq_top_of_normal
      (MF.subgroupOf D) (U.subgroupOf D) hMFUdisjSub hMFUsupTop
  have hcardD : Nat.card D = Nat.card MF * Nat.card U := by
    have h := hcompMFU.card_mul
    rw [natCard_subgroupOf_eq MF D hMFleD,
      natCard_subgroupOf_eq U D hUleD] at h
    exact h.symm
  have hHK_le_D : HK ≤ D := by
    dsimp [HK]
    exact sup_le hMFleD (hK_le_U.trans hUleD)
  have hMFnormalHK : (MF.subgroupOf HK).Normal := by
    have hHK_le_norm_MF : HK ≤ Subgroup.normalizer (MF : Set G) :=
      hHK_le_D.trans hD_le_norm_MF
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer
      (show MF ≤ HK from le_sup_left)).2 hHK_le_norm_MF
  have hdisjMFK : Disjoint MF K := by
    rw [disjoint_iff] at hMFUdisj ⊢
    apply le_antisymm
    · intro x hx
      have hxAmb : x ∈ MF ⊓ U := ⟨hx.1, hK_le_U hx.2⟩
      simpa [hMFUdisj] using hxAmb
    · exact bot_le
  have hdisjMFK_sub : Disjoint (MF.subgroupOf HK) (K.subgroupOf HK) := by
    rw [disjoint_iff] at hdisjMFK ⊢
    apply le_antisymm
    · intro x hx
      have hxAmb : (x : G) ∈ MF ⊓ K := by
        exact ⟨by simpa [Subgroup.mem_subgroupOf] using hx.1,
          by simpa [Subgroup.mem_subgroupOf] using hx.2⟩
      have hxBot : (x : G) ∈ (⊥ : Subgroup G) := by
        simpa [hdisjMFK] using hxAmb
      ext
      simpa using hxBot
    · exact bot_le
  have hMF_K_supTop : MF.subgroupOf HK ⊔ K.subgroupOf HK = ⊤ := by
    dsimp [HK]
    rw [← Subgroup.subgroupOf_sup (A := MF) (A' := K) (B := MF ⊔ K)
      le_sup_left le_sup_right]
    exact Subgroup.subgroupOf_eq_top.2 le_rfl
  have hcompMFK : (MF.subgroupOf HK).IsComplement' (K.subgroupOf HK) := by
    letI : (MF.subgroupOf HK).Normal := hMFnormalHK
    exact isComplement'_of_disjoint_sup_eq_top_of_normal
      (MF.subgroupOf HK) (K.subgroupOf HK) hdisjMFK_sub hMF_K_supTop
  have hcardHK : Nat.card HK = Nat.card MF * Nat.card K := by
    have h := hcompMFK.card_mul
    rw [natCard_subgroupOf_eq MF HK le_sup_left,
      natCard_subgroupOf_eq K HK le_sup_right] at h
    exact h.symm
  have hcardHKsub : Nat.card (HK.subgroupOf D) = Nat.card HK :=
    natCard_subgroupOf_eq HK D hHK_le_D
  have hmulIndex : Nat.card HK * HK.relIndex D = Nat.card D := by
    rw [Subgroup.relIndex, ← hcardHKsub]
    exact (HK.subgroupOf D).card_mul_index
  have hcardKsub : Nat.card (K.subgroupOf U) = Nat.card K :=
    natCard_subgroupOf_eq K U hK_le_U
  have hcardKIndex : Nat.card K * K.relIndex U = Nat.card U := by
    rw [Subgroup.relIndex, ← hcardKsub]
    exact (K.subgroupOf U).card_mul_index
  have hrelHK : HK.relIndex D = K.relIndex U := by
    have hmain : (Nat.card MF * Nat.card K) * HK.relIndex D =
        (Nat.card MF * Nat.card K) * K.relIndex U := by
      calc
        (Nat.card MF * Nat.card K) * HK.relIndex D
            = Nat.card HK * HK.relIndex D := by rw [hcardHK]
        _ = Nat.card D := hmulIndex
        _ = Nat.card MF * Nat.card U := hcardD
        _ = Nat.card MF * (Nat.card K * K.relIndex U) := by rw [hcardKIndex]
        _ = (Nat.card MF * Nat.card K) * K.relIndex U := by ac_rfl
    exact Nat.mul_left_cancel (Nat.mul_pos Nat.card_pos Nat.card_pos) hmain
  have hHKsub_le_Dsub : HK.subgroupOf M ≤ D.subgroupOf M := by
    intro x hx
    simpa [Subgroup.mem_subgroupOf, HK, D] using
      hHK_le_D (by simpa [Subgroup.mem_subgroupOf, HK] using hx)
  have hrel_sub_eq :
      (HK.subgroupOf M).relIndex (D.subgroupOf M) = HK.relIndex D := by
    exact Subgroup.relIndex_subgroupOf (H := HK) (K := D) (L := M) hDleM
  have hDindex_eq_q : (D.subgroupOf M).index = q := by
    have hDindex_eq_cardW1 : (D.subgroupOf M).index = Nat.card W1 := by
      simpa [D, Subgroup.relIndex] using hW1card.symm
    exact hDindex_eq_cardW1.trans h92.q_eq
  calc
    Subgroup.index ((MF ⊔ K).subgroupOf M)
        = Subgroup.index (HK.subgroupOf M) := rfl
    _ = (HK.subgroupOf M).relIndex (D.subgroupOf M) *
        (D.subgroupOf M).index := by
          exact (Subgroup.relIndex_mul_index hHKsub_le_Dsub).symm
    _ = HK.relIndex D * q := by rw [hrel_sub_eq, hDindex_eq_q]
    _ = K.relIndex U * q := by rw [hrelHK]
    _ = q * K.relIndex U := Nat.mul_comm _ _

public theorem HC_index_eq_q_mul_u_of_hypothesis_9_2_sec9
    {G : Type u} [Group G] [Finite G]
    (M MF U W1 W2 C : Subgroup G)
    (q u : ℕ) :
    hypothesis_9_2_statement M MF U W1 W2 q →
      quotientBarUCardinality U C u →
        Subgroup.index ((MF ⊔ C).subgroupOf M) = q * u := by
  intro h92 hBarU
  rcases hBarU with ⟨hC_le_U, hCnormalU, hUquot_card⟩
  have hrelC : C.relIndex U = u := by
    letI : (C.subgroupOf U).Normal := hCnormalU
    rw [Subgroup.relIndex, Subgroup.index_eq_card (C.subgroupOf U), hUquot_card]
  rw [HMK_index_eq_q_mul_relIndex_of_hypothesis_9_2_sec9
    M MF U W1 W2 C q h92 hC_le_U, hrelC]

public theorem degree_eq_index_of_inducedFromLinearCharacter_sec9
    {G : Type u} [Group G] [Finite G]
    (M N : Subgroup G)
    (χ : Section1.ClassFunction M) :
    inducedFromLinearCharacter M N χ →
      Section1.degree χ = (Subgroup.index (N.subgroupOf M) : ℂ) := by
  intro hlin
  rcases hlin with ⟨θ, _hθirr, hθdeg, hχeq⟩
  rw [hχeq, Section1.degree_inducedClassFunction, hθdeg]
  simp

public theorem degree_eq_q_mul_relIndex_of_inducedFromLinearCharacter_sec9
    {G : Type u} [Group G] [Finite G]
    (M N : Subgroup G) (q r : ℕ)
    (χ : Section1.ClassFunction M) :
    Subgroup.index (N.subgroupOf M) = q * r →
      inducedFromLinearCharacter M N χ →
        Section1.degree χ = (q * r : ℂ) := by
  intro hidx hlin
  rw [degree_eq_index_of_inducedFromLinearCharacter_sec9 M N χ hlin, hidx]
  simp [Nat.cast_mul]

public theorem degree_eq_q_mul_u_of_linear_HC_sec9
    {G : Type u} [Group G] [Finite G]
    (M MF C : Subgroup G) (q u : ℕ)
    (χ : Section1.ClassFunction M) :
    Subgroup.index ((MF ⊔ C).subgroupOf M) = q * u →
      inducedFromLinearCharacterOfHC M MF C χ →
        Section1.degree χ = (q * u : ℂ) := by
  intro hidx hlin
  exact degree_eq_q_mul_relIndex_of_inducedFromLinearCharacter_sec9
    M (MF ⊔ C) q u χ hidx hlin

public theorem ambientDerived_subgroupOf_index_eq_q_of_hypothesis_9_2_sec9
    {G : Type u} [Group G] [Finite G]
    (M MF U W1 W2 : Subgroup G)
    (q : ℕ) :
    hypothesis_9_2_statement M MF U W1 W2 q →
      Subgroup.index ((ambientDerivedSubgroup M).subgroupOf M) = q := by
  intro h92
  rcases h92.typeP with ⟨_hMFtype, hcommon⟩
  rcases hcommon with
    ⟨_hDhall, _hMFleD, _hcompD, _hnil, _hW1norm, _hW1cyc, hW1card,
      _hMFnotcyc, _hsecond, _hfitting, _hfittingDer, _hW2le, _hW2ne,
      _hW2cyc, _hcentralizer, _hhat, _hprimeCentralizer, _hW2der⟩
  have hDindex_eq_cardW1 :
      Subgroup.index ((ambientDerivedSubgroup M).subgroupOf M) = Nat.card W1 := by
    simpa [Subgroup.relIndex] using hW1card.symm
  exact hDindex_eq_cardW1.trans h92.q_eq

/-- The principal character induced from `HU₁` to `M`. -/
@[expose] public def principalInducedFromHU1
    {G : Type u} [Group G] [Finite G]
    (M MF U1 : Subgroup G)
    (γ : Section1.ClassFunction M) : Prop :=
  γ = Section7.principalInducedCharacter M (MF ⊔ U1)


/-- Reducibility data for a named finite subfamily. -/
@[expose] public def reducibleCharacterSubfamilyData
    {G : Type u} [Group G] [Finite G]
    (M : Subgroup G)
    (S R : Finset (Section1.ClassFunction M))
    (degree : ℕ) : Prop :=
  letI : Finite M := Finite.of_injective (fun x : M => (x : G)) Subtype.val_injective
  R ⊆ S ∧
    (∀ χ : Section1.ClassFunction M, χ ∈ R →
      ¬ Section1.IsIrreducibleCharacterOnGroup χ ∧
        Section1.degree χ = (degree : ℂ)) ∧
    ∀ χ : Section1.ClassFunction M, χ ∈ S →
      ¬ Section1.IsIrreducibleCharacterOnGroup χ → χ ∈ R

/-- Coherence of a family for the PF `(9.5)` Dade map. -/
@[expose] public def coherentFamilyForT
    {G : Type u} [Group G] [Finite G]
    (M : Subgroup G)
    (S : Finset (Section1.ClassFunction M))
    (T : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G) : Prop :=
  Section6.coherentFamily S T

/-- The final congruence and pair-extension contradiction in PF `(9.11.8)`. -/
@[expose] public def theorem_9_11_8_data
    {G : Type u} [Group G] [Finite G]
    (M : Subgroup G)
    (S1 S2 S3 S4 SH0Cprime : Finset (Section1.ClassFunction M))
    (T τ1 : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G)
    (ψ1 lam1 β α : Section1.ClassFunction M)
    (Δ : Section1.ClassFunction G)
    (a u b : ℕ) (x : ℤ) : Prop :=
  Section1.scalarProduct G (T α) (T β) = (u / a : ℂ) ∧
    T α = (x : ℂ) • (Finset.sum S1 fun ψ => τ1 ψ) - τ1 ψ1 + Δ ∧
    (∀ χ : Section1.ClassFunction M, χ ∈ S1 →
      Section1.scalarProduct G Δ (τ1 χ) = 0) ∧
    1 < u / a ∧
    (u / a) ∣ b ∧
    b = 0 ∧
    S1 ⊆ S2 ∧
    S2 ⊆ SH0Cprime ∧
    S3 = SH0Cprime \ S2 ∧
    coherentFamilyForT M S2 T ∧
    (∀ χ : Section1.ClassFunction M, χ ∈ S2 →
      Section1.conjugateCharacter χ ∈ S2) ∧
    lam1 ∈ S4 ∧
    S4 ⊆ S3 ∧
    coherentFamilyForT M (S1 ∪ {lam1, Section1.conjugateCharacter lam1}) T ∧
    ¬ ∃ S2' : Finset (Section1.ClassFunction M),
      S2 ⊂ S2' ∧
        S2' ⊆ SH0Cprime ∧
          coherentFamilyForT M S2' T ∧
            ∀ χ : Section1.ClassFunction M, χ ∈ S2' →
              Section1.conjugateCharacter χ ∈ S2'

/-- Irreducibility of the `\overline U` action on `\overline H`. -/
@[expose] public def quotientIrreducibleActionData
    {G : Type u} [Group G] [Finite G]
    (MF H0 U : Subgroup G) : Prop :=
  ∃ hnormal : (H0.subgroupOf MF).Normal,
    letI : (H0.subgroupOf MF).Normal := hnormal
    ∀ Q : Subgroup (MF ⧸ H0.subgroupOf MF),
      quotientSubgroupNormalizedBy MF H0 U Q → Q = ⊥ ∨ Q = ⊤

/-- The finite-field semidirect-product model in PF `(9.7.b)`. -/
@[expose] public def quotientFieldSemidirectModelData
    {G : Type u} [Group G] [Finite G]
    (MF H0 U C W1 : Subgroup G)
    (p q u : ℕ) : Prop :=
  ∃ hnormalH0 : (H0.subgroupOf MF).Normal,
    letI : (H0.subgroupOf MF).Normal := hnormalH0
    ∃ hnormalC : (C.subgroupOf U).Normal,
      letI : (C.subgroupOf U).Normal := hnormalC
      ∃ hW1normU : W1 ≤ Subgroup.normalizer (U : Set G),
        letI : Subgroup.Normalizes W1 U := ⟨hW1normU⟩
        ∃ hCinv : IsInvariant W1 U (C.subgroupOf U),
          letI : MulDistribMulAction W1 (U ⧸ C.subgroupOf U) :=
            quotientMulDistribMulAction (A := W1) (G := U) (C.subgroupOf U) hCinv
          ∃ F : Type u, ∃ fieldInst : Field F, ∃ fintypeInst : Fintype F,
            letI : Field F := fieldInst
            letI : Fintype F := fintypeInst
            ∃ Ustar : Subgroup Fˣ,
                Nat.card F = p ^ q ∧
                Nat.card Ustar = u ∧
                IsCyclic Ustar ∧
                AddSubgroup.closure
                  (((fun x : Ustar => ((x : Fˣ) : F)) '' Set.univ) : Set F) = ⊤ ∧
                ∃ φH : (MF ⧸ H0.subgroupOf MF) ≃* Multiplicative F,
                  ∃ φU : (U ⧸ C.subgroupOf U) ≃* Ustar,
                    ∃ φW : W1 ≃* RingAut F,
                      (∀ x : U ⧸ C.subgroupOf U, ∀ h : MF,
                        ∃ hconjMF : ∀ y : MF,
                          (x.out : U)⁻¹ * (y : G) * (x.out : U) ∈ MF,
                          φH (QuotientGroup.mk' (H0.subgroupOf MF)
                            ⟨(x.out : U)⁻¹ * (h : G) * (x.out : U), hconjMF h⟩) =
                            Multiplicative.ofAdd (((φU x : Ustar) : Fˣ) *
                              Multiplicative.toAdd
                                (φH (QuotientGroup.mk' (H0.subgroupOf MF) h)))) ∧
                        ∀ w : W1, ∀ h : MF,
                          ∃ hconjMF : ∀ y : MF,
                            (w : G)⁻¹ * (y : G) * (w : G) ∈ MF,
                            φH (QuotientGroup.mk' (H0.subgroupOf MF)
                              ⟨(w : G)⁻¹ * (h : G) * (w : G), hconjMF h⟩) =
                              Multiplicative.ofAdd ((φW w) (Multiplicative.toAdd
                                (φH (QuotientGroup.mk' (H0.subgroupOf MF) h)))) ∧
                          ∀ x : U ⧸ C.subgroupOf U,
                            ((φU x : Ustar) : Fˣ) ∈ Ustar ∧
                              Units.map (φW w).toMonoidHom (φU x : Ustar) ∈ Ustar ∧
                              Units.map (φW w).toMonoidHom (φU x : Ustar) =
                                (φU ((w⁻¹ : W1) • x) : Ustar)


@[expose] public def quotientFieldSemidirectModelWithPrimeFieldImageData
    {G : Type u} [Group G] [Finite G]
    (MF H0 U C W1 W2 : Subgroup G)
    (p q u : ℕ) : Prop :=
  ∃ hnormalH0 : (H0.subgroupOf MF).Normal,
    letI : (H0.subgroupOf MF).Normal := hnormalH0
    ∃ hnormalC : (C.subgroupOf U).Normal,
      letI : (C.subgroupOf U).Normal := hnormalC
      ∃ hW1normU : W1 ≤ Subgroup.normalizer (U : Set G),
        letI : Subgroup.Normalizes W1 U := ⟨hW1normU⟩
        ∃ hCinv : IsInvariant W1 U (C.subgroupOf U),
          letI : MulDistribMulAction W1 (U ⧸ C.subgroupOf U) :=
            quotientMulDistribMulAction (A := W1) (G := U) (C.subgroupOf U) hCinv
          ∃ F : Type u, ∃ fieldInst : Field F, ∃ fintypeInst : Fintype F,
            letI : Field F := fieldInst
            letI : Fintype F := fintypeInst
            ∃ Ustar : Subgroup Fˣ,
                Nat.card F = p ^ q ∧
                Nat.card Ustar = u ∧
                IsCyclic Ustar ∧
                AddSubgroup.closure
                  (((fun x : Ustar => ((x : Fˣ) : F)) '' Set.univ) : Set F) = ⊤ ∧
                ∃ φH : (MF ⧸ H0.subgroupOf MF) ≃* Multiplicative F,
                  ∃ φU : (U ⧸ C.subgroupOf U) ≃* Ustar,
                    ∃ φW : W1 ≃* RingAut F,
                      ((∀ x : U ⧸ C.subgroupOf U, ∀ h : MF,
                        ∃ hconjMF : ∀ y : MF,
                          (x.out : U)⁻¹ * (y : G) * (x.out : U) ∈ MF,
                          φH (QuotientGroup.mk' (H0.subgroupOf MF)
                            ⟨(x.out : U)⁻¹ * (h : G) * (x.out : U), hconjMF h⟩) =
                            Multiplicative.ofAdd (((φU x : Ustar) : Fˣ) *
                              Multiplicative.toAdd
                                (φH (QuotientGroup.mk' (H0.subgroupOf MF) h)))) ∧
                        ∀ w : W1, ∀ h : MF,
                          ∃ hconjMF : ∀ y : MF,
                            (w : G)⁻¹ * (y : G) * (w : G) ∈ MF,
                            φH (QuotientGroup.mk' (H0.subgroupOf MF)
                              ⟨(w : G)⁻¹ * (h : G) * (w : G), hconjMF h⟩) =
                              Multiplicative.ofAdd ((φW w) (Multiplicative.toAdd
                                (φH (QuotientGroup.mk' (H0.subgroupOf MF) h)))) ∧
                            ∀ x : U ⧸ C.subgroupOf U,
                              ((φU x : Ustar) : Fˣ) ∈ Ustar ∧
                                Units.map (φW w).toMonoidHom (φU x : Ustar) ∈ Ustar ∧
                                Units.map (φW w).toMonoidHom (φU x : Ustar) =
                                  (φU ((w⁻¹ : W1) • x) : Ustar)) ∧
                        (W2 ≤ MF ∧
                          Subgroup.map φH.toMonoidHom
                            ((W2.subgroupOf MF).map
                              (QuotientGroup.mk' (H0.subgroupOf MF))) =
                            Subgroup.zpowers (Multiplicative.ofAdd (1 : F)))

public theorem quotientFieldSemidirectModelData_of_withPrimeFieldImage_sec9
    {G : Type u} [Group G] [Finite G]
    {MF H0 U C W1 W2 : Subgroup G} {p q u : ℕ} :
    quotientFieldSemidirectModelWithPrimeFieldImageData MF H0 U C W1 W2 p q u →
      quotientFieldSemidirectModelData MF H0 U C W1 p q u := by
  intro h
  rcases h with
    ⟨hnormalH0, hnormalC, hW1normU, hCinv, F, fieldInst, fintypeInst, Ustar,
      hFcard, hUstarCard, hUstarCyc, hspan, φH, φU, φW, hactions, _hW2⟩
  rcases hactions with ⟨hUaction, hWaction⟩
  exact ⟨hnormalH0, hnormalC, hW1normU, hCinv, F, fieldInst, fintypeInst,
    Ustar, hFcard, hUstarCard, hUstarCyc, hspan, φH, φU, φW, hUaction,
    hWaction⟩

/-- The alternative `(9.7)(a)`. -/
@[expose] public def case_9_7_a_data
    {G : Type u} [Group G] [Finite G]
    (M MF U W1 W2 H0 C : Subgroup G)
    (p q a : ℕ) : Prop :=
  hypothesis_9_2_statement M MF U W1 W2 q ∧
    H0 ≤ MF ∧
    quotientCentralizerIn MF H0 U C ∧
    Nat.Prime p ∧
    Nat.Prime q ∧
    (∃ hp : Nat.Primes,
      hp.val = p ∧
        hoReductionData M MF U W2 H0 hp ∧
          quotientChiefFactorData_9_6 M MF H0 W1 hp) ∧
    (∃ hnormal : (H0.subgroupOf MF).Normal,
      letI : (H0.subgroupOf MF).Normal := hnormal
      ∃ H : Fin q → Subgroup (MF ⧸ H0.subgroupOf MF),
        (∀ i, Nat.card (H i) = p) ∧
          (∀ i, quotientSubgroupNormalizedBy MF H0 U (H i)) ∧
          iSupIndep H ∧
          iSup H = ⊤ ∧
          (∀ i, quotientFactorActionCentralizerData MF H0 U C (H i) a) ∧
          ∃ hqpos : 0 < q,
            ∀ i : Fin q,
              ∃ w : W1,
                quotientSubgroupConjugateByElement MF H0 (H ⟨0, hqpos⟩) (H i) (w : G)) ∧
    Nat.card (MF ⧸ H0.subgroupOf MF) = p ^ q ∧
    a ∣ p - 1 ∧
    (∃ _hCU : C ≤ U,
      ∃ hnormal : (C.subgroupOf U).Normal,
        letI : (C.subgroupOf U).Normal := hnormal
        ∃ φ : (U ⧸ C.subgroupOf U) →* (Fin (q - 1) → Multiplicative (ZMod a)),
          Function.Injective φ)

public theorem case_9_7_a_hypothesis_9_2_sec9
    {G : Type u} [Group G] [Finite G]
    {M MF U W1 W2 H0 C : Subgroup G}
    {p q a : ℕ} :
    case_9_7_a_data M MF U W1 W2 H0 C p q a →
      hypothesis_9_2_statement M MF U W1 W2 q := by
  intro hcase
  exact hcase.1

public theorem case_9_7_a_H0_le_MF_sec9
    {G : Type u} [Group G] [Finite G]
    {M MF U W1 W2 H0 C : Subgroup G}
    {p q a : ℕ} :
    case_9_7_a_data M MF U W1 W2 H0 C p q a →
      H0 ≤ MF := by
  intro hcase
  rcases hcase with ⟨_h92, hH0MF, _hrest⟩
  exact hH0MF

public theorem case_9_7_a_quotientCentralizerIn_sec9
    {G : Type u} [Group G] [Finite G]
    {M MF U W1 W2 H0 C : Subgroup G}
    {p q a : ℕ} :
    case_9_7_a_data M MF U W1 W2 H0 C p q a →
      quotientCentralizerIn MF H0 U C := by
  intro hcase
  rcases hcase with ⟨_h92, _hH0MF, hC, _hrest⟩
  exact hC

public theorem case_9_7_a_p_prime_sec9
    {G : Type u} [Group G] [Finite G]
    {M MF U W1 W2 H0 C : Subgroup G}
    {p q a : ℕ} :
    case_9_7_a_data M MF U W1 W2 H0 C p q a →
      Nat.Prime p := by
  intro hcase
  rcases hcase with ⟨_h92, _hH0MF, _hC, hpprime, _hrest⟩
  exact hpprime

public theorem case_9_7_a_q_prime_sec9
    {G : Type u} [Group G] [Finite G]
    {M MF U W1 W2 H0 C : Subgroup G}
    {p q a : ℕ} :
    case_9_7_a_data M MF U W1 W2 H0 C p q a →
      Nat.Prime q := by
  intro hcase
  rcases hcase with ⟨_h92, _hH0MF, _hC, _hpprime, hqprime, _hrest⟩
  exact hqprime

public theorem case_9_7_a_hoReductionData_sec9
    {G : Type u} [Group G] [Finite G]
    {M MF U W1 W2 H0 C : Subgroup G}
    {p q a : ℕ} :
    case_9_7_a_data M MF U W1 W2 H0 C p q a →
      ∃ hp : Nat.Primes, hp.val = p ∧ hoReductionData M MF U W2 H0 hp := by
  intro hcase
  rcases hcase with
    ⟨_h92, _hH0MF, _hC, _hpprime, _hqprime, hpData, _hrest⟩
  rcases hpData with ⟨hp, hp_eq, hho, _h96⟩
  exact ⟨hp, hp_eq, hho⟩


public theorem case_9_7_a_MF_le_M_sec9
    {G : Type u} [Group G] [Finite G]
    {M MF U W1 W2 H0 C : Subgroup G}
    {p q a : ℕ} :
    case_9_7_a_data M MF U W1 W2 H0 C p q a →
      MF ≤ M := by
  intro hcase
  rcases case_9_7_a_hoReductionData_sec9 hcase with ⟨_hp, _hpval, hpData⟩
  rcases hpData with ⟨_hH0MF, hMFM, _hrest⟩
  exact hMFM

public theorem case_9_7_a_H0_normal_M_sec9
    {G : Type u} [Group G] [Finite G]
    {M MF U W1 W2 H0 C : Subgroup G}
    {p q a : ℕ} :
    case_9_7_a_data M MF U W1 W2 H0 C p q a →
      (H0.subgroupOf M).Normal := by
  intro hcase
  rcases case_9_7_a_hoReductionData_sec9 hcase with ⟨_hp, _hpval, hpData⟩
  rcases hpData with ⟨_hH0MF, _hMFM, hH0normalM, _hrest⟩
  exact hH0normalM

public theorem case_9_7_a_H0_normal_MF_sec9
    {G : Type u} [Group G] [Finite G]
    {M MF U W1 W2 H0 C : Subgroup G}
    {p q a : ℕ} :
    case_9_7_a_data M MF U W1 W2 H0 C p q a →
      (H0.subgroupOf MF).Normal := by
  intro hcase
  rcases case_9_7_a_hoReductionData_sec9 hcase with ⟨_hp, _hpval, hpData⟩
  rcases hpData with ⟨_hH0MF, _hMFM, _hH0normalM, hH0normalMF, _hrest⟩
  exact hH0normalMF


public theorem case_9_7_a_barU_injective_data_sec9
    {G : Type u} [Group G] [Finite G]
    {M MF U W1 W2 H0 C : Subgroup G}
    {p q a : ℕ} :
    case_9_7_a_data M MF U W1 W2 H0 C p q a →
      ∃ _hCU : C ≤ U,
        ∃ hnormal : (C.subgroupOf U).Normal,
          letI : (C.subgroupOf U).Normal := hnormal
          ∃ φ : (U ⧸ C.subgroupOf U) →* (Fin (q - 1) → Multiplicative (ZMod a)),
            Function.Injective φ := by
  intro hcase
  rcases hcase with
    ⟨_h92, _hH0MF, _hC, _hpprime, _hqprime, _hpData, _hdecomp, _hcard,
      _hadiv, hinj⟩
  exact hinj

public theorem case_9_7_a_component_decomposition_sec9
    {G : Type u} [Group G] [Finite G]
    {M MF U W1 W2 H0 C : Subgroup G}
    {p q a : ℕ} :
    case_9_7_a_data M MF U W1 W2 H0 C p q a →
      ∃ hnormal : (H0.subgroupOf MF).Normal,
        letI : (H0.subgroupOf MF).Normal := hnormal
        ∃ H : Fin q → Subgroup (MF ⧸ H0.subgroupOf MF),
          (∀ i, Nat.card (H i) = p) ∧
            (∀ i, quotientSubgroupNormalizedBy MF H0 U (H i)) ∧
            iSupIndep H ∧
            iSup H = ⊤ ∧
            (∀ i, quotientFactorActionCentralizerData MF H0 U C (H i) a) ∧
            ∃ hqpos : 0 < q,
              ∀ i : Fin q,
                ∃ w : W1,
                  quotientSubgroupConjugateByElement MF H0 (H ⟨0, hqpos⟩) (H i)
                    (w : G) := by
  intro hcase
  rcases hcase with
    ⟨_h92, _hH0MF, _hC, _hpprime, _hqprime, _hpData, hdecomp, _hcard,
      _hadiv, _hinj⟩
  exact hdecomp

public theorem case_9_7_a_quotient_cardinality_sec9
    {G : Type u} [Group G] [Finite G]
    {M MF U W1 W2 H0 C : Subgroup G}
    {p q a : ℕ} :
    case_9_7_a_data M MF U W1 W2 H0 C p q a →
      Nat.card (MF ⧸ H0.subgroupOf MF) = p ^ q := by
  intro hcase
  rcases hcase with
    ⟨_h92, _hH0MF, _hC, _hpprime, _hqprime, _hpData, _hdecomp, hcard,
      _hadiv, _hinj⟩
  exact hcard


public theorem case_9_7_a_index_dvd_p_minus_one_sec9
    {G : Type u} [Group G] [Finite G]
    {M MF U W1 W2 H0 C : Subgroup G}
    {p q a : ℕ} :
    case_9_7_a_data M MF U W1 W2 H0 C p q a →
      a ∣ p - 1 := by
  intro hcase
  rcases hcase with
    ⟨_h92, _hH0MF, _hC, _hpprime, _hqprime, _hpData, _hdecomp, _hcard,
      hadiv, _hinj⟩
  exact hadiv

public theorem case_9_7_a_index_a_pos_sec9
    {G : Type u} [Group G] [Finite G]
    (M MF U W1 W2 H0 C : Subgroup G)
    (p q a : ℕ) :
    case_9_7_a_data M MF U W1 W2 H0 C p q a →
      0 < a := by
  intro hcase
  rcases hcase with
    ⟨_h92, _hH0MF, _hC, _hp, hq, _hpdata, hdecomp, _hcard, _hadiv,
      _hembed⟩
  rcases hdecomp with
    ⟨_hnormal, _H, _hHcard, _hHnorm, _hInd, _hSup, hfactor, _hconj⟩
  have hqpos : 0 < q := hq.pos
  rcases hfactor ⟨0, hqpos⟩ with
    ⟨_hnormalC, ρ, _hcyc, hcardρ, _haction, _hker⟩
  rw [← hcardρ]
  exact Nat.card_pos (α := ρ.range)

public theorem case_9_7_a_index_a_odd_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 C : Subgroup G)
    (p q a : ℕ) :
    case_9_7_a_data M MF U W1 W2 H0 C p q a →
      Odd a := by
  intro hcase
  rcases case_9_7_a_component_decomposition_sec9 hcase with
    ⟨hnormalH0, H, _hHcard, _hHnorm, _hInd, _hSup, hfactor, _hconj⟩
  letI : (H0.subgroupOf MF).Normal := hnormalH0
  have hqpos : 0 < q := (case_9_7_a_q_prime_sec9 hcase).pos
  rcases hfactor ⟨0, hqpos⟩ with
    ⟨hnormalC, ρ, _hcyc, hρcard, _haction, _hker⟩
  letI : (C.subgroupOf U).Normal := hnormalC
  have hUodd : Odd (Nat.card U) :=
    odd_of_card_dvd IsMinCE.odd_order (Subgroup.card_subgroup_dvd_card U)
  have hquotOdd : Odd (Nat.card (U ⧸ C.subgroupOf U)) :=
    odd_of_card_dvd hUodd (Subgroup.card_quotient_dvd_card (C.subgroupOf U))
  have hrangeOdd : Odd (Nat.card ρ.range) :=
    odd_of_card_dvd hquotOdd (Subgroup.card_range_dvd ρ)
  exact hρcard ▸ hrangeOdd

public theorem case_9_7_a_first_count_factor_pos_sec9
    {G : Type u} [Group G] [Finite G]
    (M MF U W1 W2 H0 C : Subgroup G)
    (p q a : ℕ) :
    case_9_7_a_data M MF U W1 W2 H0 C p q a →
      0 < (p - 1) / a := by
  intro hcase
  have ha_pos : 0 < a :=
    case_9_7_a_index_a_pos_sec9 M MF U W1 W2 H0 C p q a hcase
  rcases hcase with
    ⟨_h92, _hH0MF, _hC, hp, _hq, _hpdata, _hdecomp, _hcard, hadiv,
      _hembed⟩
  have hp_pred_pos : 0 < p - 1 := Nat.sub_pos_of_lt hp.one_lt
  have ha_le : a ≤ p - 1 := Nat.le_of_dvd hp_pred_pos hadiv
  exact Nat.div_pos ha_le ha_pos

public theorem case_9_7_a_second_count_factor_pos_sec9
    {G : Type u} [Group G] [Finite G]
    (M MF U W1 W2 H0 C Uprime : Subgroup G)
    (p q a : ℕ) :
    case_9_7_a_data M MF U W1 W2 H0 C p q a →
      Uprime = (_root_.commutator U).map U.subtype →
        0 < Nat.card U / (a * Nat.card Uprime) := by
  intro hcase hUprimeEq
  have ha_pos : 0 < a :=
    case_9_7_a_index_a_pos_sec9 M MF U W1 W2 H0 C p q a hcase
  rcases hcase with
    ⟨_h92, _hH0MF, _hC, _hp, hq, _hpdata, hdecomp, _hcard, _hadiv,
      _hembed⟩
  rcases hdecomp with
    ⟨_hnormalH0, H, _hHcard, _hHnorm, _hInd, _hSup, hfactor, _hconj⟩
  have hqpos : 0 < q := hq.pos
  rcases hfactor ⟨0, hqpos⟩ with
    ⟨hnormalC, ρ, hcyc, hcardρ, _haction, _hker⟩
  letI : (C.subgroupOf U).Normal := hnormalC
  letI : IsCyclic ρ.range := hcyc
  letI : CommGroup ρ.range := IsCyclic.commGroup
  let f : U →* ρ.range :=
    ρ.rangeRestrict.comp (QuotientGroup.mk' (C.subgroupOf U))
  have hf_range_top : f.range = ⊤ := by
    rw [MonoidHom.range_eq_top]
    intro y
    rcases y with ⟨y, hy⟩
    rcases hy with ⟨x, rfl⟩
    rcases QuotientGroup.mk'_surjective (C.subgroupOf U) x with ⟨u, rfl⟩
    exact ⟨u, rfl⟩
  have hf_range_card : Nat.card f.range = a := by
    rw [hf_range_top]
    simpa using hcardρ
  have hf_index : f.ker.index = a := by
    rw [Subgroup.index_ker, hf_range_card]
  have hUprimeU : Uprime ≤ U := by
    rw [hUprimeEq, Subgroup.map_subtype_commutator]
    exact Subgroup.commutator_le_self U
  have hUprime_le_ker : Uprime.subgroupOf U ≤ f.ker := by
    intro x hx
    have hxG : (x : G) ∈ Uprime := by
      simpa [Subgroup.mem_subgroupOf] using hx
    rw [hUprimeEq] at hxG
    rcases hxG with ⟨y, hy, hy_eq⟩
    have hxy : x = y := Subtype.ext (by simpa using hy_eq.symm)
    have hyker : y ∈ f.ker := Abelianization.commutator_subset_ker f hy
    simpa [hxy]
  have hidx_ne : (Uprime.subgroupOf U).index ≠ 0 := by
    exact Subgroup.index_ne_zero_of_finite
  have hindex_le : f.ker.index ≤ (Uprime.subgroupOf U).index := by
    simpa [Subgroup.relIndex_top_right] using
      (Subgroup.relIndex_le_of_le_left (H := Uprime.subgroupOf U) (K := f.ker)
        (L := ⊤) hUprime_le_ker
        (by simpa [Subgroup.relIndex_top_right] using hidx_ne))
  have ha_le_index : a ≤ (Uprime.subgroupOf U).index := by
    simpa [hf_index] using hindex_le
  have hcardUprimeSub : Nat.card (Uprime.subgroupOf U) = Nat.card Uprime :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUprimeU).toEquiv
  have hmul_le_sub :
      a * Nat.card (Uprime.subgroupOf U) ≤
        (Uprime.subgroupOf U).index * Nat.card (Uprime.subgroupOf U) :=
    Nat.mul_le_mul_right (Nat.card (Uprime.subgroupOf U)) ha_le_index
  have hden_le : a * Nat.card Uprime ≤ Nat.card U := by
    rw [← hcardUprimeSub]
    exact hmul_le_sub.trans (le_of_eq (Subgroup.index_mul_card (Uprime.subgroupOf U)))
  have hden_pos : 0 < a * Nat.card Uprime :=
    Nat.mul_pos ha_pos (Nat.card_pos (α := Uprime))
  exact Nat.div_pos hden_le hden_pos

public theorem case_9_7_a_count_lower_bound_pos_sec9
    {G : Type u} [Group G] [Finite G]
    (M MF U W1 W2 H0 C Uprime : Subgroup G)
    (p q a : ℕ) :
    case_9_7_a_data M MF U W1 W2 H0 C p q a →
      Uprime = (_root_.commutator U).map U.subtype →
        0 < ((p - 1) / a) * (Nat.card U / (a * Nat.card Uprime)) := by
  intro hcase hUprimeEq
  exact Nat.mul_pos
    (case_9_7_a_first_count_factor_pos_sec9 M MF U W1 W2 H0 C p q a hcase)
    (case_9_7_a_second_count_factor_pos_sec9 M MF U W1 W2 H0 C Uprime p q a
      hcase hUprimeEq)

/--
The proof-internal scalar-action consequence of case `(9.7)(a)` used in
PF `(11.7)`: for any multiplicative bilinear pairing on `MF/H0` that is
invariant under the diagonal `U`-action, every component in the reducible
decomposition lies in the left radical.

This is kept separate from the book-facing `case_9_7_a_data` so the numbered
PF `(9.7)` statement remains source-facing while downstream proofs can reuse
the character argument from the proof of `(9.7)`.
-/
@[expose] public def case_9_7_a_pairingVanishingData
    {G : Type u} [Group G] [Finite G]
    (MF U H0 : Subgroup G)
    (q : ℕ) : Prop :=
  ∃ hnormal : (H0.subgroupOf MF).Normal,
    letI : (H0.subgroupOf MF).Normal := hnormal
    ∃ hUnormMF : U ≤ Subgroup.normalizer (MF : Set G),
      letI : Subgroup.Normalizes U MF := ⟨hUnormMF⟩
      ∃ hH0inv : IsInvariant U MF (H0.subgroupOf MF),
        letI : MulAction.QuotientAction U (H0.subgroupOf MF) :=
          quotientAction_of_isInvariant (A := U) (G := MF)
            (H0.subgroupOf MF) hH0inv
        letI : MulDistribMulAction U (MF ⧸ H0.subgroupOf MF) :=
          quotientMulDistribMulAction (A := U) (G := MF)
            (H0.subgroupOf MF) hH0inv
        ∃ H : Fin q → Subgroup (MF ⧸ H0.subgroupOf MF),
          iSup H = ⊤ ∧
            ∀ {B : Type u} [Group B]
              (pairing : (MF ⧸ H0.subgroupOf MF) →
                (MF ⧸ H0.subgroupOf MF) → B),
                (∀ a b c : MF ⧸ H0.subgroupOf MF,
                  pairing (a * b) c = pairing a c * pairing b c) →
                (∀ a b c : MF ⧸ H0.subgroupOf MF,
                  pairing a (b * c) = pairing a b * pairing a c) →
                (∀ a : MF ⧸ H0.subgroupOf MF, pairing a a = 1) →
                (∀ u : U, ∀ a b : MF ⧸ H0.subgroupOf MF,
                  pairing (u • a) (u • b) = pairing a b) →
                ∀ i : Fin q, ∀ x : MF ⧸ H0.subgroupOf MF,
                  x ∈ H i → ∀ y : MF ⧸ H0.subgroupOf MF, pairing x y = 1

@[expose] public def case_9_7_a_characterData
    {G : Type u} [Group G] [Finite G]
    (M MF U _H0 C Uprime : Subgroup G)
    (p q a u : ℕ)
    (SH0 SH0C SH0U : Finset (Section1.ClassFunction M)) : Prop :=
  (∀ χ : Section1.ClassFunction M, χ ∈ SH0 → characterDegreeDivisibleBy a χ) ∧
    (∀ χ : Section1.ClassFunction M, χ ∈ SH0 →
      ∀ θ : Section1.ClassFunction ((ambientDerivedSubgroup M).subgroupOf M),
        Section1.IsIrreducibleCharacterOnGroup θ →
          ¬ Section1.subgroupInKernel' θ
            ((MF.subgroupOf M).subgroupOf ((ambientDerivedSubgroup M).subgroupOf M)) →
          Section1.subgroupInKernel' θ
            ((_H0.subgroupOf M).subgroupOf ((ambientDerivedSubgroup M).subgroupOf M)) →
          χ = Section1.inducedCF ((ambientDerivedSubgroup M).subgroupOf M) θ →
            characterDegreeDivisibleBy a θ) ∧
    quotientBarUCardinality U C u ∧
    (∃ R : Finset (Section1.ClassFunction M),
      R.card = p - 1 ∧
        reducibleCharacterSubfamilyData M SH0 R (q * u) ∧
        R ⊆ SH0C ∧
        ∀ χ : Section1.ClassFunction M, χ ∈ R →
          inducedFromLinearCharacterOfHC M MF C χ) ∧
    (∃ χ : Section1.ClassFunction M,
      χ ∈ SH0C ∧
        Section1.IsIrreducibleCharacterOnGroup χ ∧
        Section1.degree χ = (q * u : ℂ) ∧
        inducedFromLinearCharacterOfHC M MF C χ) ∧
    (∃ I : Finset (Section1.ClassFunction M),
      I ⊆ SH0U ∧
        I.card ≥ ((p - 1) / a) * (Nat.card U / (a * Nat.card Uprime)) ∧
        ∀ χ : Section1.ClassFunction M, χ ∈ I →
          Section1.IsIrreducibleCharacterOnGroup χ ∧
            Section1.degree χ = (q * a : ℂ))

/-- The alternative `(9.7)(b)`. -/
@[expose] public def case_9_7_b_data
    {G : Type u} [Group G] [Finite G]
    (M MF U W1 W2 H0 C : Subgroup G)
    (p q u : ℕ) : Prop :=
  hypothesis_9_2_statement M MF U W1 W2 q ∧
    H0 ≤ MF ∧
    quotientCentralizerIn MF H0 U C ∧
    Nat.Prime p ∧
    Nat.Prime q ∧
    (∃ hp : Nat.Primes,
      hp.val = p ∧
        hoReductionData M MF U W2 H0 hp ∧
          quotientChiefFactorData_9_6 M MF H0 W1 hp) ∧
    (∃ hnormal : (H0.subgroupOf MF).Normal,
      letI : (H0.subgroupOf MF).Normal := hnormal
      Nat.card (MF ⧸ H0.subgroupOf MF) = p ^ q) ∧
    quotientCentralizedBy MF H0 C ∧
    quotientBarUCyclicData U C u ∧
    quotientIrreducibleActionData MF H0 U ∧
    quotientFieldSemidirectModelData MF H0 U C W1 p q u ∧
    Nat.Coprime u (p - 1) ∧
    u ∣ (p ^ q - 1) / (p - 1) ∧
    quotientFieldSemidirectModelWithPrimeFieldImageData MF H0 U C W1 W2 p q u

public theorem case_9_7_b_hypothesis_9_2_sec9
    {G : Type u} [Group G] [Finite G]
    {M MF U W1 W2 H0 C : Subgroup G}
    {p q u : ℕ} :
    case_9_7_b_data M MF U W1 W2 H0 C p q u →
      hypothesis_9_2_statement M MF U W1 W2 q := by
  intro hcase
  exact hcase.1

public theorem case_9_7_b_H0_le_MF_sec9
    {G : Type u} [Group G] [Finite G]
    {M MF U W1 W2 H0 C : Subgroup G}
    {p q u : ℕ} :
    case_9_7_b_data M MF U W1 W2 H0 C p q u →
      H0 ≤ MF := by
  intro hcase
  rcases hcase with ⟨_h92, hH0MF, _hrest⟩
  exact hH0MF

public theorem case_9_7_b_quotientCentralizerIn_sec9
    {G : Type u} [Group G] [Finite G]
    {M MF U W1 W2 H0 C : Subgroup G}
    {p q u : ℕ} :
    case_9_7_b_data M MF U W1 W2 H0 C p q u →
      quotientCentralizerIn MF H0 U C := by
  intro hcase
  rcases hcase with ⟨_h92, _hH0MF, hC, _hrest⟩
  exact hC

public theorem case_9_7_b_p_prime_sec9
    {G : Type u} [Group G] [Finite G]
    {M MF U W1 W2 H0 C : Subgroup G}
    {p q u : ℕ} :
    case_9_7_b_data M MF U W1 W2 H0 C p q u →
      Nat.Prime p := by
  intro hcase
  rcases hcase with ⟨_h92, _hH0MF, _hC, hpprime, _hrest⟩
  exact hpprime

public theorem case_9_7_b_q_prime_sec9
    {G : Type u} [Group G] [Finite G]
    {M MF U W1 W2 H0 C : Subgroup G}
    {p q u : ℕ} :
    case_9_7_b_data M MF U W1 W2 H0 C p q u →
      Nat.Prime q := by
  intro hcase
  rcases hcase with ⟨_h92, _hH0MF, _hC, _hpprime, hqprime, _hrest⟩
  exact hqprime

public theorem case_9_7_b_hoReductionData_sec9
    {G : Type u} [Group G] [Finite G]
    {M MF U W1 W2 H0 C : Subgroup G}
    {p q u : ℕ} :
    case_9_7_b_data M MF U W1 W2 H0 C p q u →
      ∃ hp : Nat.Primes, hp.val = p ∧ hoReductionData M MF U W2 H0 hp := by
  intro hcase
  rcases hcase with
    ⟨_h92, _hH0MF, _hC, _hpprime, _hqprime, hpData, _hrest⟩
  rcases hpData with ⟨hp, hp_eq, hho, _h96⟩
  exact ⟨hp, hp_eq, hho⟩


public theorem case_9_7_b_MF_le_M_sec9
    {G : Type u} [Group G] [Finite G]
    {M MF U W1 W2 H0 C : Subgroup G}
    {p q u : ℕ} :
    case_9_7_b_data M MF U W1 W2 H0 C p q u →
      MF ≤ M := by
  intro hcase
  rcases case_9_7_b_hoReductionData_sec9 hcase with ⟨_hp, _hpval, hpData⟩
  rcases hpData with ⟨_hH0MF, hMFM, _hrest⟩
  exact hMFM

public theorem case_9_7_b_H0_normal_M_sec9
    {G : Type u} [Group G] [Finite G]
    {M MF U W1 W2 H0 C : Subgroup G}
    {p q u : ℕ} :
    case_9_7_b_data M MF U W1 W2 H0 C p q u →
      (H0.subgroupOf M).Normal := by
  intro hcase
  rcases case_9_7_b_hoReductionData_sec9 hcase with ⟨_hp, _hpval, hpData⟩
  rcases hpData with ⟨_hH0MF, _hMFM, hH0normalM, _hrest⟩
  exact hH0normalM

public theorem case_9_7_b_H0_normal_MF_sec9
    {G : Type u} [Group G] [Finite G]
    {M MF U W1 W2 H0 C : Subgroup G}
    {p q u : ℕ} :
    case_9_7_b_data M MF U W1 W2 H0 C p q u →
      (H0.subgroupOf MF).Normal := by
  intro hcase
  rcases case_9_7_b_hoReductionData_sec9 hcase with ⟨_hp, _hpval, hpData⟩
  rcases hpData with ⟨_hH0MF, _hMFM, _hH0normalM, hH0normalMF, _hrest⟩
  exact hH0normalMF

public theorem case_9_7_b_H0_lt_MF_sec9
    {G : Type u} [Group G] [Finite G]
    {M MF U W1 W2 H0 C : Subgroup G}
    {p q u : ℕ} :
    case_9_7_b_data M MF U W1 W2 H0 C p q u →
      H0 < MF := by
  intro hcase
  rcases case_9_7_b_hoReductionData_sec9 hcase with ⟨_hp, _hpval, hpData⟩
  rcases hpData with
    ⟨_hH0MF, _hMFM, _hH0normalM, _hH0normalMF, hH0ltMF, _hrest⟩
  exact hH0ltMF

public theorem case_9_7_b_quotient_card_sec9
    {G : Type u} [Group G] [Finite G]
    {M MF U W1 W2 H0 C : Subgroup G}
    {p q u : ℕ} :
    case_9_7_b_data M MF U W1 W2 H0 C p q u →
      ∃ hnormal : (H0.subgroupOf MF).Normal,
        letI : (H0.subgroupOf MF).Normal := hnormal
        Nat.card (MF ⧸ H0.subgroupOf MF) = p ^ q := by
  intro hcase
  rcases hcase with
    ⟨_h92, _hH0MF, _hC, _hpprime, _hqprime, _hpData, hcard, _hrest⟩
  exact hcard

public theorem case_9_7_b_quotientCentralizedBy_sec9
    {G : Type u} [Group G] [Finite G]
    {M MF U W1 W2 H0 C : Subgroup G}
    {p q u : ℕ} :
    case_9_7_b_data M MF U W1 W2 H0 C p q u →
      quotientCentralizedBy MF H0 C := by
  intro hcase
  rcases hcase with
    ⟨_h92, _hH0MF, _hC, _hpprime, _hqprime, _hpData, _hcard, hcentBy, _hrest⟩
  exact hcentBy

public theorem case_9_7_b_barU_cyclicData_sec9
    {G : Type u} [Group G] [Finite G]
    {M MF U W1 W2 H0 C : Subgroup G}
    {p q u : ℕ} :
    case_9_7_b_data M MF U W1 W2 H0 C p q u →
      quotientBarUCyclicData U C u := by
  intro hcase
  rcases hcase with
    ⟨_h92, _hH0MF, _hC, _hpprime, _hqprime, _hpData, _hcard, _hcentBy,
      hcyclic, _hrest⟩
  exact hcyclic

public theorem case_9_7_b_barU_cardinality_sec9
    {G : Type u} [Group G] [Finite G]
    {M MF U W1 W2 H0 C : Subgroup G}
    {p q u : ℕ} :
    case_9_7_b_data M MF U W1 W2 H0 C p q u →
      quotientBarUCardinality U C u := by
  intro hcase
  rcases case_9_7_b_barU_cyclicData_sec9 hcase with
    ⟨hCU, hnormal, _hcyclic, hcard⟩
  exact ⟨hCU, hnormal, hcard⟩


public theorem case_9_7_b_fieldSemidirectModelData_sec9
    {G : Type u} [Group G] [Finite G]
    {M MF U W1 W2 H0 C : Subgroup G}
    {p q u : ℕ} :
    case_9_7_b_data M MF U W1 W2 H0 C p q u →
      quotientFieldSemidirectModelData MF H0 U C W1 p q u := by
  intro hcase
  rcases hcase with
    ⟨_h92, _hH0MF, _hC, _hpprime, _hqprime, _hpData, _hcard, _hcentBy,
      _hcyclic, _hirr, hfield, _hrest⟩
  exact hfield

public theorem case_9_7_b_fieldSemidirectModelWithPrimeFieldImageData_sec9
    {G : Type u} [Group G] [Finite G]
    {M MF U W1 W2 H0 C : Subgroup G}
    {p q u : ℕ} :
    case_9_7_b_data M MF U W1 W2 H0 C p q u →
      quotientFieldSemidirectModelWithPrimeFieldImageData MF H0 U C W1 W2 p q u := by
  intro hcase
  rcases hcase with
    ⟨_h92, _hH0MF, _hC, _hpprime, _hqprime, _hpData, _hcard, _hcentBy,
      _hcyclic, _hirr, _hfield, _hcop, _hdiv, hprimeField⟩
  exact hprimeField

public theorem case_9_7_b_coprime_u_p_minus_one_sec9
    {G : Type u} [Group G] [Finite G]
    {M MF U W1 W2 H0 C : Subgroup G}
    {p q u : ℕ} :
    case_9_7_b_data M MF U W1 W2 H0 C p q u →
      Nat.Coprime u (p - 1) := by
  intro hcase
  rcases hcase with
    ⟨_h92, _hH0MF, _hC, _hpprime, _hqprime, _hpData, _hcard, _hcentBy,
      _hcyclic, _hirr, _hfield, hcop, _hrest⟩
  exact hcop

public theorem case_9_7_b_u_dvd_sec9
    {G : Type u} [Group G] [Finite G]
    {M MF U W1 W2 H0 C : Subgroup G}
    {p q u : ℕ} :
    case_9_7_b_data M MF U W1 W2 H0 C p q u →
      u ∣ (p ^ q - 1) / (p - 1) := by
  intro hcase
  rcases hcase with
    ⟨_h92, _hH0MF, _hC, _hpprime, _hqprime, _hpData, _hcard, _hcentBy,
      _hcyclic, _hirr, _hfield, _hcop, hdiv, _hprimeField⟩
  exact hdiv

@[expose] public def case_9_7_b_characterData
    {G : Type u} [Group G] [Finite G]
    (M MF _H0 C : Subgroup G)
    (p q u : ℕ)
    (SH0 SH0C SH0Cprime : Finset (Section1.ClassFunction M)) : Prop :=
  (∀ χ : Section1.ClassFunction M, χ ∈ SH0 → characterDegreeDivisibleBy u χ) ∧
    (∀ χ : Section1.ClassFunction M, χ ∈ SH0Cprime →
      Section1.degree χ = (q * u : ℂ) ∧
        inducedFromLinearCharacterOfHC M MF C χ) ∧
    (∃ R : Finset (Section1.ClassFunction M),
      R.card = p - 1 ∧
        reducibleCharacterSubfamilyData M SH0 R (q * u) ∧
        R ⊆ SH0C) ∧
    ((¬ ∃ χ : Section1.ClassFunction M,
      χ ∈ SH0Cprime ∧ Section1.IsIrreducibleCharacterOnGroup χ) →
        C = ⊥ ∧ u = (p ^ q - 1) / (p - 1))

/-- The forbidden degree-`qu` character from PF `(9.10)`. -/
@[expose] public def degreeQuIrreducibleFromLinearHC
    {G : Type u} [Group G] [Finite G]
    (M MF C : Subgroup G)
    (q u : ℕ)
    (χ : Section1.ClassFunction M) : Prop :=
  Section1.IsIrreducibleCharacterOnGroup χ ∧
    Section1.degree χ = (q * u : ℂ) ∧
    inducedFromLinearCharacterOfHC M MF C χ

/-- The PF `(9.10)` assertion that `\overline H U` is Frobenius with kernel `\overline H`. -/
@[expose] public def quotientFrobeniusWithKernelData
    {G : Type u} [Group G] [Finite G]
    (MF H0 U : Subgroup G) : Prop :=
  H0 ≤ MF ∧
    ∃ hnormal : (H0.subgroupOf (MF ⊔ U)).Normal,
      letI : (H0.subgroupOf (MF ⊔ U)).Normal := hnormal
      IsFrobeniusGroupWithKernelComplement
        ((MF.subgroupOf (MF ⊔ U)).map (QuotientGroup.mk' (H0.subgroupOf (MF ⊔ U))))
        ((U.subgroupOf (MF ⊔ U)).map (QuotientGroup.mk' (H0.subgroupOf (MF ⊔ U))))

end CFSG.Section9
