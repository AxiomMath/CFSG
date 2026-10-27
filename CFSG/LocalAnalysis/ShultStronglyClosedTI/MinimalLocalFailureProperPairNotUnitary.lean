module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureProperPairModelAlignment
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureCyclicFull
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.UnitaryModelPointStructure

public noncomputable section

namespace CFSG.ShultStronglyClosedTI.ProperPairModel

open CFSG.Open CFSG.BenderSuzuki CFSG.BenderSuzuki.MatrixGroups
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ShultStronglyClosedTI.TwoCoreGrowth CFSG.ShultStronglyClosedTI.UnitaryModel
open MulAction Matrix
open scoped LinearAlgebra.Projectivization

universe u

theorem eq_of_stabilizer_eq {P Ω : Type*} [Group P] [MulAction P Ω]
    (htwo : ∀ a b c d : Ω, a ≠ b → c ≠ d → ∃ g : P, g • a = c ∧ g • b = d)
    (hthree : ∀ a b : Ω, ∃ c : Ω, c ≠ a ∧ c ≠ b)
    {p p' : Ω} (h : stabilizer P p = stabilizer P p') : p = p' := by
  by_contra hne
  obtain ⟨c, hcp, hcp'⟩ := hthree p p'
  obtain ⟨g, hgp, hgp'⟩ := htwo p p' p c hne (Ne.symm hcp)
  have hgmem : g ∈ stabilizer P p' := h ▸ (mem_stabilizer_iff.mpr hgp)
  exact hcp' ((mem_stabilizer_iff.mp hgmem).symm.trans hgp').symm

variable {K : Type} [Field K] [Finite K]

theorem unitary_point_involutions_and_pair_preservers_proper (J : HermitianForm 3 K)
    (f : ℕ) (hf : 2 ≤ f) (hcard : Nat.card K = (2 ^ f) ^ 2)
    (hfixed : Nat.card {x : K // J.conj x = x} = 2 ^ f)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (S : Set (ProjectiveSpecialUnitaryMatrixGroup J))
    (hS : ∀ g ∈ S, (g ∈ unitaryCoordinateStabilizer J 0 ∧ orderOf g = 2) ∨
      unitaryCoordinatePairPreserving J g) :
    Subgroup.closure S ≠ ⊤ := by
  have hle : Subgroup.closure S ≤ unitaryMiddleStabilizer J := by
    apply (Subgroup.closure_le _).mpr
    intro g hg
    rcases hS g hg with ⟨hgB, hgo⟩ | hpair
    · exact unitary_entire_point_involutions_fix_middle J f hf hcard hfixed hJ hgB hgo
    · exact unitary_projective_pair_preserves_middle J hJ g hpair
  intro htop
  rw [htop] at hle
  exact (unitary_middle_stabilizer_proper J (2 ^ f) hcard hfixed hJ).ne (top_le_iff.mp hle)

variable {G : Type} [Group G] [Finite G]

theorem proper_pair_hull_quotient_not_unitary
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (hcomm : ProperStrongEmbeddingCommutingImages G)
    (hsmallerR1 : ∀ (F : Type) [Group F] [Finite F], Nat.card F < Nat.card G →
      2 ≤ twoRank F → (∃ A : Subgroup F, fusionStronglyEmbedded A) → R1Full F)
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    {t : G} (ht : t ∈ rightPairFlipFiber H z beta)
    (hproper : minimalLocalFailureProperPairHull H z beta t < ⊤)
    (J : HermitianForm 3 K) (f : ℕ) (hf : 2 ≤ f) (hcard : Nat.card K = (2 ^ f) ^ 2)
    (hfixed : Nat.card {x : K // J.conj x = x} = 2 ^ f)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) :
    IsEmpty (minimalLocalFailureProperPairHull H z beta t ⧸
      CFSG.oddCore (minimalLocalFailureProperPairHull H z beta t) ≃*
        ProjectiveSpecialUnitaryMatrixGroup J) := by
  refine ⟨fun e => ?_⟩
  set L := minimalLocalFailureProperPairHull H z beta t with hL
  let π := QuotientGroup.mk' (CFSG.oddCore L)
  let P := ProjectiveSpecialUnitaryMatrixGroup J
  let Ω := unitaryIsotropicPoints J
  let α := unitaryOuterIsotropicPoint J hJ 0 (by decide)
  let β := unitaryOuterIsotropicPoint J hJ 2 (by decide)
  obtain ⟨-, -, -, -, -, rho, -, hnat, hΩcard, htwo, hstabα, hstabβ, -, -, -, -, -, -,
    -, -, -, -, -, -, -, -, -⟩ := unitary_three_point_structure J f hf hcard hfixed hJ
  obtain ⟨-, S₀, -, -, -, hS₀R, -, hnorm, -⟩ :=
    unitary_entire_root_point_structure J f hf hcard hfixed hJ
  let : MulAction P Ω := MulAction.compHom Ω rho
  have hstab : ∀ p : Ω, stabilizer P p = (stabilizer (Equiv.Perm Ω) p).comap rho :=
    fun p => by ext g; rfl
  have hS₀ : Subgroup.normalizer ((S₀ : Subgroup P) : Set P) = stabilizer P α := by
    rw [hS₀R, hnorm, hstab, hstabα]
  have htwo' : ∀ a b c d : Ω, a ≠ b → c ≠ d → ∃ g : P, g • a = c ∧ g • b = d := htwo
  have hαβ : α ≠ β := by
    intro heq
    have h02 : unitaryCoordinatePoint (K := K) 0 = unitaryCoordinatePoint (K := K) 2 :=
      congrArg Subtype.val heq
    have := (Projectivization.mk_eq_mk_iff' K _ _ _ _).mp h02
    obtain ⟨a, ha⟩ := this
    have h0 := congrFun ha 0
    simp at h0
  have hthree : ∀ a b : Ω, ∃ c : Ω, c ≠ a ∧ c ≠ b := by
    intro a b
    by_contra hnone
    push Not at hnone
    have hsub : (Set.univ : Set Ω) ⊆ {a, b} := by
      intro c _
      by_cases hca : c = a
      · exact Or.inl hca
      · exact Or.inr (hnone c hca)
    have hle := Set.ncard_le_ncard hsub (Set.toFinite _)
    rw [Set.ncard_univ] at hle
    have hpair : ({a, b} : Set Ω).ncard ≤ 2 :=
      (Set.ncard_insert_le _ _).trans (by rw [Set.ncard_singleton])
    have hq : 4 ≤ 2 ^ f := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
    have hΩ : 2 < Nat.card Ω := by
      rw [hΩcard]
      nlinarith [Nat.pow_le_pow_left hq 3]
    omega
  obtain ⟨ψ, hψα, hψβ⟩ := proper_pair_model_alignment h hcomm hsmallerR1 hbeta ht hproper e S₀ α
    hS₀ htwo' α β hαβ
  let φ : L →* P := ψ.toMonoidHom.comp π
  have hφsurj : Function.Surjective φ :=
    ψ.surjective.comp (QuotientGroup.mk'_surjective (CFSG.oddCore L))
  have hφM : (H.subgroupOf L).map φ = stabilizer P α := by
    rw [← hψα, Subgroup.map_map]
  have hφMt : ((rightConjugate H t).subgroupOf L).map φ = stabilizer P β := by
    rw [← hψβ, Subgroup.map_map]
  have hzL : z ∈ L := minimalLocalFailureProperPair_distinguished_mem H z beta t
  have htL : t ∈ L := minimalLocalFailureProperPair_flip_mem H z beta t
  let zL : L := ⟨z, hzL⟩
  let tL : L := ⟨t, htL⟩
  have htorderG : orderOf t = 2 :=
    order_two_of_mem_pointClass h.local_datum.distinguished_order ht.1
  have htorder : orderOf tL = 2 := (Subgroup.orderOf_coe tL).symm.trans htorderG
  have hzorder : orderOf zL = 2 :=
    (Subgroup.orderOf_coe zL).symm.trans h.local_datum.distinguished_order
  have hφorder : ∀ y : L, orderOf y = 2 → orderOf (φ y) = 2 := by
    intro y hy
    change orderOf (ψ (π y)) = 2
    rw [MulEquiv.orderOf_eq]
    exact sylowAssemblyProper_quotient_involution_order_two L hy
  have hconj := rightConjugate_subgroupOf_eq_map H L htL
  have hmapconj : ((H.subgroupOf L).map (MulAut.conj tL⁻¹).toMonoidHom).map φ =
      ((H.subgroupOf L).map φ).map (MulAut.conj (φ tL)⁻¹).toMonoidHom := by
    rw [Subgroup.map_map, Subgroup.map_map]
    congr 1
    ext x
    simp [map_mul, map_inv]
  have hstabt : stabilizer P ((φ tL)⁻¹ • α) = stabilizer P β := by
    rw [stabilizer_smul_eq_stabilizer_map_conj, ← hφM, ← hmapconj, ← hconj, hφMt]
  have htα : (φ tL)⁻¹ • α = β := eq_of_stabilizer_eq htwo' hthree hstabt
  have hφtinv : (φ tL)⁻¹ = φ tL := by
    rw [← map_inv]
    congr 1
    exact inv_eq_self_of_orderOf_eq_two htorder
  have hφtα : φ tL • α = β := by rw [← hφtinv]; exact htα
  have hφtβ : φ tL • β = α := by
    rw [← hφtα, smul_smul, ← map_mul]
    have htt : tL * tL = 1 := by
      rw [← sq]
      exact (orderOf_eq_prime_iff.mp htorder).1
    rw [htt, map_one, one_smul]
  obtain ⟨-, -, -, -, -, -, -, hIB, hXI, hXK, -⟩ :=
    CyclicPair.proper_pair_cyclic_commutator h hcomm hsmallerR1 hbeta ht hproper
  have hbetaeq : beta = rightCosetMk H t := by
    rw [← ht.2, rightCosetTranslate_mk, one_mul]
  have hXboth : ∀ x ∈ rightInvolutionCommutatorSubgroup t (pairOddCore H beta),
      x ∈ H ∧ x ∈ rightConjugate H t := by
    intro x hx
    have hxB := hIB (hXI hx)
    change x ∈ rightCosetStabilizer H (rightCosetMk H 1) ⊓ rightCosetStabilizer H beta at hxB
    rw [rightCosetStabilizer_base, hbetaeq, rightCosetStabilizer_mk] at hxB
    exact hxB
  let gens : Set G := ({z, t} : Set G) ∪
    (rightInvolutionCommutatorSubgroup t (pairOddCore H beta) : Set G)
  have hgens : L = Subgroup.closure gens := rfl
  have htopL : Subgroup.closure (L.subtype ⁻¹' gens) = ⊤ := by
    rw [hgens]
    exact Subgroup.closure_preimage_eq_top gens
  have hcoord : ∀ g : P, ∀ p : Ω,
      (g : ProjGenLinGroup (Fin 3) K) • (p : ℙ K (Fin 3 → K)) = ((g • p : Ω) : ℙ K (Fin 3 → K)) :=
    fun g p => (hnat g p).symm
  have hS : ∀ g ∈ φ '' (L.subtype ⁻¹' gens),
      (g ∈ unitaryCoordinateStabilizer J 0 ∧ orderOf g = 2) ∨
        unitaryCoordinatePairPreserving J g := by
    rintro g ⟨y, hy, rfl⟩
    rcases hy with hyzt | hyX
    · rcases hyzt with hyz | hyt
      · have hyeq : y = zL := Subtype.ext hyz
        left
        refine ⟨?_, ?_⟩
        · have hmem : φ y ∈ stabilizer P α := by
            rw [← hφM, hyeq]
            exact Subgroup.mem_map_of_mem φ h.local_datum.distinguished_mem
          rw [hstab, hstabα] at hmem
          exact hmem
        · rw [hyeq]
          exact hφorder zL hzorder
      · have hyeq : y = tL := Subtype.ext hyt
        right
        right
        rw [hyeq]
        refine ⟨?_, ?_⟩
        · rw [show unitaryCoordinatePoint (K := K) 0 = (α : ℙ K (Fin 3 → K)) from rfl, hcoord,
            hφtα]
          rfl
        · rw [show unitaryCoordinatePoint (K := K) 2 = (β : ℙ K (Fin 3 → K)) from rfl, hcoord,
            hφtβ]
          rfl
    · obtain ⟨hyH, hyHt⟩ := hXboth y hyX
      have hyα : φ y • α = α := by
        have hmem : φ y ∈ stabilizer P α := by
          rw [← hφM]
          exact Subgroup.mem_map_of_mem φ (show y ∈ H.subgroupOf L from hyH)
        exact mem_stabilizer_iff.mp hmem
      have hyβ : φ y • β = β := by
        have hmem : φ y ∈ stabilizer P β := by
          rw [← hφMt]
          exact Subgroup.mem_map_of_mem φ (show y ∈ (rightConjugate H t).subgroupOf L from hyHt)
        exact mem_stabilizer_iff.mp hmem
      right
      left
      refine ⟨?_, ?_⟩
      · rw [show unitaryCoordinatePoint (K := K) 0 = (α : ℙ K (Fin 3 → K)) from rfl, hcoord, hyα]
      · rw [show unitaryCoordinatePoint (K := K) 2 = (β : ℙ K (Fin 3 → K)) from rfl, hcoord, hyβ]
  apply unitary_point_involutions_and_pair_preservers_proper J f hf hcard hfixed hJ _ hS
  rw [← MonoidHom.map_closure, htopL, Subgroup.map_top_of_surjective φ hφsurj]

end CFSG.ShultStronglyClosedTI.ProperPairModel
