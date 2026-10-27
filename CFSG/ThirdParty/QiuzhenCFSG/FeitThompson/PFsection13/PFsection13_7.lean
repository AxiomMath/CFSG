module

import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection5.PFsection5_9
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection13.PFsection13_6
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection8.PFsection8_5_a

namespace CFSG
end CFSG
open CFSG

/-!
# Peterfalvi, Section 13: PFsection13_7
-/

noncomputable section

open scoped BigOperators Pointwise

attribute [local instance] Fintype.ofFinite

namespace CFSG.Section13

universe v
universe u

/-! ## (13.7) -/


private theorem theorem_13_7_scalarProduct_finset_sum_left
    {G : Type u} [Group G] [Finite G]
    {ι : Type*} [DecidableEq ι]
    (E : Finset ι) (φ : ι → Section1.ClassFunction G)
    (ψ : Section1.ClassFunction G) :
    Section1.scalarProduct G (E.sum φ) ψ =
      E.sum (fun i => Section1.scalarProduct G (φ i) ψ) := by
  classical
  induction E using Finset.induction with
  | empty =>
      simp [Section1.scalarProduct]
  | insert a E ha ih =>
      simp [Finset.sum_insert ha, Section1.scalarProduct_add_left, ih]

private theorem theorem_13_7_scalarProduct_neg_left
    {G : Type u} [Group G] [Finite G]
    (φ ψ : Section1.ClassFunction G) :
    Section1.scalarProduct G (-φ) ψ = -Section1.scalarProduct G φ ψ := by
  have hEq : (-φ : Section1.ClassFunction G) = (-1 : ℂ) • φ := by
    ext g
    simp
  calc
    Section1.scalarProduct G (-φ) ψ =
        Section1.scalarProduct G ((-1 : ℂ) • φ) ψ := by
          rw [hEq]
    _ = (-1 : ℂ) * Section1.scalarProduct G φ ψ := by
          rw [Section1.scalarProduct_smul_left]
    _ = -Section1.scalarProduct G φ ψ := by
          norm_num

private theorem theorem_13_7_eta_orthonormal_of_notation
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax W W1 W2 : Subgroup G)
    (p q : ℕ)
    (ω : ℕ → ℕ → Section1.ClassFunction W)
    (η : ℕ → ℕ → Section1.ClassFunction G)
    (μ : ℕ → ℕ → Section1.ClassFunction Smax)
    (ν : ℕ → ℕ → Section1.ClassFunction Tmax)
    (μsum : ℕ → Section1.ClassFunction Smax)
    (νsum : ℕ → Section1.ClassFunction Tmax)
    (δ δ' : ℕ → ℤ)
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G) :
    hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2 p q
        ω η μ ν μsum νsum δ δ' σ →
      ∀ i k i' k' : ℕ, i < q → k < p → i' < q → k' < p →
        Section1.scalarProduct G (η i k) (η i' k') =
          if i = i' ∧ k = k' then 1 else 0 := by
  intro hnotation i k i' k' hi hk hi' hk'
  rcases hnotation with
    ⟨hωData, hσmap, hη, _hδ, _hδ', _hμirr, _hνirr,
      _hμzero_nonprincipal, _hνzero_nonprincipal, _hμind, _hνind,
      _hμsum, _hνsum⟩
  rcases hωData with ⟨_h31, _hqpos, _hppos, ωFin, hωFin, hωNat⟩
  let fi : Fin q := ⟨i, hi⟩
  let fk : Fin p := ⟨k, hk⟩
  let fi' : Fin q := ⟨i', hi'⟩
  let fk' : Fin p := ⟨k', hk'⟩
  have hηik : η i k = σ (ωFin fi fk) := by
    rw [hη i k hi hk, hωNat i k hi hk]
  have hηi'k' : η i' k' = σ (ωFin fi' fk') := by
    rw [hη i' k' hi' hk', hωNat i' k' hi' hk']
  have hiso :
      Section1.scalarProduct G (σ (ωFin fi fk)) (σ (ωFin fi' fk')) =
        Section1.scalarProduct W (ωFin fi fk) (ωFin fi' fk') :=
    hσmap.1 (ωFin fi fk) (ωFin fi' fk') (hωFin.is_class fi fk)
      (hωFin.is_class fi' fk')
  have hωorth :=
    Section3.isOrthonormalDoubleFamily_apply hωFin.orthonormal
      (fi, fk) (fi', fk')
  rw [hηik, hηi'k', hiso, hωorth]
  by_cases hpair : i = i' ∧ k = k'
  · rcases hpair with ⟨rfl, rfl⟩
    have hfinPair : (fi, fk) = (fi', fk') := by
      ext <;> rfl
    simp [hfinPair]
  · have hfinPair : (fi, fk) ≠ (fi', fk') := by
      intro hfin
      apply hpair
      constructor
      · exact congrArg (fun x : Fin q => (x : ℕ)) (Prod.ext_iff.mp hfin).1
      · exact congrArg (fun x : Fin p => (x : ℕ)) (Prod.ext_iff.mp hfin).2
    simp [hpair, hfinPair]

private theorem theorem_13_7_eta_row_sum_orthogonal_eta10_of_notation
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax W W1 W2 : Subgroup G)
    (p q j : ℕ)
    (ω : ℕ → ℕ → Section1.ClassFunction W)
    (η : ℕ → ℕ → Section1.ClassFunction G)
    (μ : ℕ → ℕ → Section1.ClassFunction Smax)
    (ν : ℕ → ℕ → Section1.ClassFunction Tmax)
    (μsum : ℕ → Section1.ClassFunction Smax)
    (νsum : ℕ → Section1.ClassFunction Tmax)
    (δ δ' : ℕ → ℤ)
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
    (hnotation : hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2 p q
      ω η μ ν μsum νsum δ δ' σ)
    (h1q : 1 < q) (hj0 : 0 < j) (hjp : j < p) :
    Section1.scalarProduct G ((Finset.range q).sum (fun i => η i j)) (η 1 0) = 0 := by
  rw [theorem_13_7_scalarProduct_finset_sum_left]
  apply Finset.sum_eq_zero
  intro i hi
  have hiq : i < q := Finset.mem_range.mp hi
  have h0p : 0 < p := lt_trans hj0 hjp
  have horth :=
    theorem_13_7_eta_orthonormal_of_notation
      Smax Tmax W W1 W2 p q ω η μ ν μsum νsum δ δ' σ
      hnotation i j 1 0 hiq hjp h1q h0p
  have hpair : ¬ (i = 1 ∧ j = 0) := by
    intro h
    exact (Nat.ne_of_gt hj0) h.2
  simpa [hpair] using horth

private theorem theorem_13_7_muSum_orthogonal_eta10_of_characterOutput
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax W W1 W2 P C : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u j : ℕ)
    (ω : ℕ → ℕ → Section1.ClassFunction W)
    (η : ℕ → ℕ → Section1.ClassFunction G)
    (μ : ℕ → ℕ → Section1.ClassFunction Smax)
    (ν : ℕ → ℕ → Section1.ClassFunction Tmax)
    (μsum : ℕ → Section1.ClassFunction Smax)
    (νsum : ℕ → Section1.ClassFunction Tmax)
    (δ δ' : ℕ → ℤ)
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
    (hnotation : hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2 p q
      ω η μ ν μsum νsum δ δ' σ)
    (houtput : theorem_13_3_characterOutputFor Smax P C Sfam τS p q u μsum η)
    (h1q : 1 < q) (hj0 : 0 < j) (hjp : j < p) :
    Section1.scalarProduct G (τS (μsum j)) (η 1 0) = 0 := by
  rcases houtput with ⟨_hchars, hsign⟩
  rcases hsign with hrow | ⟨hp3, hrow⟩
  · change Section1.scalarProduct G ((fun j => τS (μsum j)) j) (η 1 0) = 0
    rw [hrow j hj0 hjp]
    exact theorem_13_7_eta_row_sum_orthogonal_eta10_of_notation
      Smax Tmax W W1 W2 p q j ω η μ ν μsum νsum δ δ' σ hnotation h1q hj0 hjp
  · rcases hrow j hj0 hjp with ⟨j', hjset, hrowj⟩
    have hj'mem : j' ∈ ({1, 2} : Finset ℕ) := by
      rw [← hjset]
      simp
    have hj'0 : 0 < j' := by
      simp at hj'mem
      omega
    have hj'p : j' < p := by
      simp at hj'mem
      omega
    have hzero :
        Section1.scalarProduct G ((Finset.range q).sum (fun i => η i j')) (η 1 0) = 0 :=
      theorem_13_7_eta_row_sum_orthogonal_eta10_of_notation
        Smax Tmax W W1 W2 p q j' ω η μ ν μsum νsum δ δ' σ hnotation h1q hj'0 hj'p
    change Section1.scalarProduct G ((fun j => τS (μsum j)) j) (η 1 0) = 0
    rw [hrowj]
    rw [theorem_13_7_scalarProduct_neg_left, hzero]
    simp

private theorem theorem_13_7_map_evalCoeff
    {L : Type u} [Group L]
    {G : Type u} [Group G]
    {ι : Type*} [Fintype ι]
    (T : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (μ : ι → Section1.ClassFunction L)
    (v : Section1.CoeffVector ι) :
    T (Section1.evalCoeff μ v) = Section1.evalCoeff (fun i => T (μ i)) v := by
  classical
  ext g
  simp [Section1.evalCoeff, Finset.sum_apply]

private theorem theorem_13_7_scalarProduct_evalCoeff_left_zero
    {G : Type*} [Finite G]
    {ι : Type*} [Fintype ι]
    (μ : ι → Section1.ClassFunction G)
    (v : Section1.CoeffVector ι)
    {ψ : Section1.ClassFunction G}
    (hzero : ∀ i, Section1.scalarProduct G (μ i) ψ = 0) :
    Section1.scalarProduct G (Section1.evalCoeff μ v) ψ = 0 := by
  rw [Section1.evalCoeff]
  have hsumfun :
      (∑ j : ι, (v j : ℂ) • μ j) =
        (fun g : G => ∑ j : ι, ((v j : ℂ) • μ j) g) := by
    ext g
    simp
  rw [hsumfun, Section1.scalarProduct_fintype_sum_left]
  simp_rw [Section1.scalarProduct_smul_left, hzero]
  simp

private theorem theorem_13_7_integerSpan_orthogonal_of_generators
    {L : Type u} [Group L]
    {G : Type u} [Group G] [Finite G]
    (S : Finset (Section1.ClassFunction L))
    (T : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (χ : Section1.ClassFunction G)
    {ζ : Section1.ClassFunction L}
    (hζ : Section5.integerSpan S ζ)
    (hgen : ∀ φ : Section1.ClassFunction L, φ ∈ S →
      Section1.scalarProduct G (T φ) χ = 0) :
    Section1.scalarProduct G (T ζ) χ = 0 := by
  classical
  rcases hζ with ⟨v, hζeq⟩
  rw [hζeq, theorem_13_7_map_evalCoeff T (fun X : S =>
    (X : Section1.ClassFunction L)) v]
  apply theorem_13_7_scalarProduct_evalCoeff_left_zero
  intro X
  exact hgen (X : Section1.ClassFunction L) X.property

private noncomputable def theorem_13_7_irreducibleSubfamily
    {G : Type u} [Group G] [Finite G]
    (Smax : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax)) :
    Finset (Section1.ClassFunction Smax) :=
  section13_irreducibleSubfamily Smax Sfam

private theorem theorem_13_7_coherentFamily_of_source
    {G : Type u}
    [Group G]
    [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d) :
    Section6.coherentFamily Sfam τS := by
  rcases theorem_13_2 Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
      p q u v c d hsource with
    ⟨_hMF, _htype, _hq_lt_p, _hUcomm, _hfrob, _hPelem, _hPcard, _hu, hcoh,
      _hBook, _hA0, _hnormalizer⟩
  exact hcoh


private theorem theorem_13_7_eta10_S1_witness_source
    {G : Type u}
    [Group G]
    [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D H : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (ω : ℕ → ℕ → Section1.ClassFunction W)
    (η : ℕ → ℕ → Section1.ClassFunction G)
    (μ : ℕ → ℕ → Section1.ClassFunction Smax)
    (ν : ℕ → ℕ → Section1.ClassFunction Tmax)
    (μsum : ℕ → Section1.ClassFunction Smax)
    (νsum : ℕ → Section1.ClassFunction Tmax)
    (δ δ' : ℕ → ℤ)
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (hnotation : hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2 p q
      ω η μ ν μsum νsum δ δ' σ)
    (hH : H = P ⊔ C) :
    ∃ (S1 : Finset (Section1.ClassFunction Smax))
      (ζ0 ζ1 : Section1.ClassFunction Smax),
        H = P ⊔ C ∧
          nonkernelInducedFamily Smax H P S1 ∧
          ζ0 ∈ S1 ∧ ζ1 ∈ S1 ∧ ζ0 ≠ ζ1 := by
  have h13_3 := (theorem_13_3 Smax Tmax W W1 W2 P Q U V C D
    Sfam Tfam τS τT p q u v c d hsource).1
  rcases (h13_3 ω η μ ν μsum νsum δ δ' σ hnotation).2 with
    ⟨_τ1, _hcoh, houtput⟩
  have hsourceFull := hsource
  rcases hsource with
    ⟨hcaseB, hSTypeP, _hTTypeP, hp_card, _hq_card, hC,
      _hD, _hc_card, _hd_card, _hU_card, _hV_card, _hSfam, _hTfam,
      _hDadeS, _hDadeT, _hnotationData, _hDadeDiff, _hZeroDegree,
      _hConjIndex, _hConjBetaTau, _hChoice,
      hMin, _hFourSixS, _hFourSixT⟩
  rcases hcaseB with
    ⟨_hWprod, _hWcyc, _hW1ne, hW2ne, _hWhat, _hSmax, _hTmax, _hSMF,
      _hTMF, _hSeq, _hTeq, _hSdisj, _hTdisj, _hST, _hII, _hStype,
      _hTtype, _hclass⟩
  have h1p : 1 < p := by
    have hW2card : 1 < Nat.card W2 :=
      (Subgroup.one_lt_card_iff_ne_bot (H := W2)).2 hW2ne
    simpa [hp_card] using hW2card
  have hμdata := houtput.1 1 (by norm_num) h1p
  rcases hμdata with ⟨_hμchar, _hμdeg, hμlinearPC, hμSfam⟩
  have hμlinearH : inducedFromLinearCharacterForSection13 Smax H (μsum 1) := by
    simpa [hH] using hμlinearPC
  have hHS : H ≤ Smax := hμlinearH.1
  have hPH : P ≤ H := by
    rw [hH]
    exact le_sup_left
  rcases theorem_13_6_exists_nonkernelInducedFamily Smax H P hHS hPH with
    ⟨S1, hS1⟩
  rcases theorem_13_6_lambda_inducedFromNonkernel_H_source
      Smax Tmax W W1 W2 P Q U V C D H Sfam Tfam τS τT
      (μsum 1) (τS (μsum 1)) p q u v c d hsourceFull hμSfam hH hμlinearH with
    ⟨θH, hθHirr, hθHnotker, hμind⟩
  have hμS1 : μsum 1 ∈ S1 :=
    (hS1.2.2 (μsum 1)).2 ⟨θH, hθHirr, hθHnotker, hμind⟩
  have hfit : section8FittingSubgroup Smax = P ⊔ C := by
    simpa [hC] using Section8.theorem_8_5_a Smax P U W1 W2 hSTypeP
  have hHnormal : (H.subgroupOf Smax).Normal := by
    have hPCnormal : ((P ⊔ C).subgroupOf Smax).Normal := by
      simpa [hfit] using section8FittingSubgroup_normal_in Smax
    simpa [hH] using hPCnormal
  letI : IsMinCE G := hMin
  have hoddSmax : Odd (Nat.card Smax) :=
    section13_odd_card_subgroup_of_odd_group Smax IsMinCE.odd_order
  have hμne : μsum 1 ≠ Section1.conjugateCharacter (μsum 1) :=
    section13_nonkernelInducedFamily_ne_conjugate
      Smax H P S1 hHnormal hoddSmax hS1 (μsum 1) hμS1
  refine ⟨S1, Section1.conjugateCharacter (μsum 1), μsum 1,
    hH, hS1, ?_, hμS1, ?_⟩
  · exact theorem_13_6_nonkernelInducedFamily_conjugate_mem Smax H P S1 hS1 hμS1
  · exact hμne.symm


private theorem theorem_13_7_eta10_S1_cases_or_integerSpan_source
    {G : Type u}
    [Group G]
    [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D H : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (ω : ℕ → ℕ → Section1.ClassFunction W)
    (η : ℕ → ℕ → Section1.ClassFunction G)
    (μ : ℕ → ℕ → Section1.ClassFunction Smax)
    (ν : ℕ → ℕ → Section1.ClassFunction Tmax)
    (μsum : ℕ → Section1.ClassFunction Smax)
    (νsum : ℕ → Section1.ClassFunction Tmax)
    (δ δ' : ℕ → ℤ)
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (hnotation : hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2 p q
      ω η μ ν μsum νsum δ δ' σ)
    (hH : H = P ⊔ C) :
    ∃ (S1 : Finset (Section1.ClassFunction Smax))
      (ζ0 ζ1 : Section1.ClassFunction Smax),
        H = P ⊔ C ∧
          nonkernelInducedFamily Smax H P S1 ∧
          ζ0 ∈ S1 ∧ ζ1 ∈ S1 ∧ ζ0 ≠ ζ1 ∧
          ∀ ζ : Section1.ClassFunction Smax, ζ ∈ S1 →
            (∃ j : ℕ, 0 < j ∧ j < p ∧ ζ = μsum j) ∨
              Section5.integerSpan
                (theorem_13_7_irreducibleSubfamily Smax Sfam) ζ := by
  rcases theorem_13_7_eta10_S1_witness_source
      Smax Tmax W W1 W2 P Q U V C D H Sfam Tfam τS τT
      ω η μ ν μsum νsum δ δ' σ p q u v c d hsource hnotation hH with
    ⟨S1, ζ0, ζ1, hH5, hS1, hζ0, hζ1, hζ_ne⟩
  refine ⟨S1, ζ0, ζ1, hH5, hS1, hζ0, hζ1, hζ_ne, ?_⟩
  intro ζ hζ
  rcases section13_calS1_cases_or_integerSpan_source
      Smax Tmax W W1 W2 P Q U V C D H Sfam Tfam τS τT
      ω η μ ν μsum νsum δ δ' σ p q u v c d
      hsource hnotation hH5 S1 hS1 ζ hζ with hrow | hspan
  · exact Or.inl hrow
  · exact Or.inr hspan


private theorem theorem_13_7_eta10_orthogonal_irreducible_generators_of_coherent_source
    {G : Type u}
    [Group G]
    [Finite G]
    [IsMinCE G]
    (Smax Tmax W W1 W2 P U : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (τS τ1 : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (ω : ℕ → ℕ → Section1.ClassFunction W)
    (η : ℕ → ℕ → Section1.ClassFunction G)
    (μ : ℕ → ℕ → Section1.ClassFunction Smax)
    (ν : ℕ → ℕ → Section1.ClassFunction Tmax)
    (μsum : ℕ → Section1.ClassFunction Smax)
    (νsum : ℕ → Section1.ClassFunction Tmax)
    (δ δ' : ℕ → ℤ)
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
    (p q : ℕ)
    (h1q : 1 < q)
    (hp0 : 0 < p)
    (_hTypeP : Section8.typePDefinitionData Smax P U W1 W2)
    (_hFourSix : typePFourSixTauSourceData Smax P U W1 W2 τS)
    (_hSfam : nonkernelInducedFamily Smax (P ⊔ U) P Sfam)
    (_hcohBase : Section6.coherentFamily Sfam τS)
    (_hcoh : Section6.coherentExtension Sfam τS τ1)
    (_hDade : dadeIsometryRelativeToAZero Smax P Sfam τS)
    (_hnotation : hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2 p q
      ω η μ ν μsum νsum δ δ' σ) :
    ∀ φ : Section1.ClassFunction Smax, φ ∈ Sfam →
      Section1.IsIrreducibleCharacterOnGroup φ →
        Section1.scalarProduct G (τ1 φ) (η 1 0) = 0 := by
  intro φ hφS hφIrr
  exact section13_typeP_coherentExtension_orthogonal_cyclicTIiso_source
    Smax Tmax W W1 W2 P U Sfam τS τ1 ω η μ ν μsum νsum δ δ' σ p q
    _hTypeP _hFourSix _hSfam _hcohBase _hcoh _hnotation
      φ hφS hφIrr 1 0 h1q hp0


private theorem theorem_13_7_eta10_orthogonal_irreducible_generators_source
    {G : Type u}
    [Group G]
    [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS τ1 : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (ω : ℕ → ℕ → Section1.ClassFunction W)
    (η : ℕ → ℕ → Section1.ClassFunction G)
    (μ : ℕ → ℕ → Section1.ClassFunction Smax)
    (ν : ℕ → ℕ → Section1.ClassFunction Tmax)
    (μsum : ℕ → Section1.ClassFunction Smax)
    (νsum : ℕ → Section1.ClassFunction Tmax)
    (δ δ' : ℕ → ℤ)
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (hnotation : hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2 p q
      ω η μ ν μsum νsum δ δ' σ)
    (hcohExt : Section6.coherentExtension Sfam τS τ1) :
    ∀ φ : Section1.ClassFunction Smax, φ ∈ Sfam →
      Section1.IsIrreducibleCharacterOnGroup φ →
        Section1.scalarProduct G (τ1 φ) (η 1 0) = 0 := by
  have hcoh : Section6.coherentFamily Sfam τS :=
    theorem_13_7_coherentFamily_of_source
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT p q u v c d hsource
  have hpos := section13_theorem_13_10_rawSourcePositivity_of_sourceData
    Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT p q u v c d hsource
  rcases hsource with
    ⟨_hcase, hTypeP, _hTypePT, _hp_card, _hq_card, _hC, _hD, _hc_card,
      _hd_card, _hU_card, _hV_card, _hSfam, _hTfam, hDadeS, _hDadeT,
      _hnotationData, _hDadeDiff, _hZeroDegree, _hConjIndex, _hConjBetaTau,
      _hChoice, _hMin, hFourSixS, _hFourSixT⟩
  letI : IsMinCE G := _hMin
  exact theorem_13_7_eta10_orthogonal_irreducible_generators_of_coherent_source
    Smax Tmax W W1 W2 P U Sfam τS τ1 ω η μ ν μsum νsum δ δ' σ p q
    hpos.2.1 hpos.1 hTypeP hFourSixS _hSfam hcoh hcohExt hDadeS hnotation

/- Checked glue for PF `(13.7)`: the integer-span branch follows from the
source generator orthogonality by linearity of `τS` and the scalar product. -/
private theorem theorem_13_7_eta10_S1_cases_or_orthogonal_source
    {G : Type u}
    [Group G]
    [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D H : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS τ1 : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (ω : ℕ → ℕ → Section1.ClassFunction W)
    (η : ℕ → ℕ → Section1.ClassFunction G)
    (μ : ℕ → ℕ → Section1.ClassFunction Smax)
    (ν : ℕ → ℕ → Section1.ClassFunction Tmax)
    (μsum : ℕ → Section1.ClassFunction Smax)
    (νsum : ℕ → Section1.ClassFunction Tmax)
    (δ δ' : ℕ → ℤ)
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (hnotation : hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2 p q
      ω η μ ν μsum νsum δ δ' σ)
    (hcohExt : Section6.coherentExtension Sfam τS τ1)
    (hH : H = P ⊔ C) :
    ∃ (S1 : Finset (Section1.ClassFunction Smax))
      (ζ0 ζ1 : Section1.ClassFunction Smax),
        H = P ⊔ C ∧
          nonkernelInducedFamily Smax H P S1 ∧
          ζ0 ∈ S1 ∧ ζ1 ∈ S1 ∧ ζ0 ≠ ζ1 ∧
          ∀ ζ : Section1.ClassFunction Smax, ζ ∈ S1 →
            (∃ j : ℕ, 0 < j ∧ j < p ∧ ζ = μsum j) ∨
              Section1.scalarProduct G (τ1 ζ) (η 1 0) = 0 := by
  classical
  rcases theorem_13_7_eta10_S1_cases_or_integerSpan_source
      Smax Tmax W W1 W2 P Q U V C D H Sfam Tfam τS τT
      ω η μ ν μsum νsum δ δ' σ p q u v c d hsource hnotation hH with
    ⟨S1, ζ0, ζ1, hH5, hS1, hζ0, hζ1, hζ_ne, hcases⟩
  have hgen := theorem_13_7_eta10_orthogonal_irreducible_generators_source
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τ1 τT
      ω η μ ν μsum νsum δ δ' σ p q u v c d hsource hnotation hcohExt
  refine ⟨S1, ζ0, ζ1, hH5, hS1, hζ0, hζ1, hζ_ne, ?_⟩
  intro ζ hζ
  rcases hcases ζ hζ with hrow | hspan
  · exact Or.inl hrow
  · refine Or.inr ?_
    exact theorem_13_7_integerSpan_orthogonal_of_generators
      (theorem_13_7_irreducibleSubfamily Smax Sfam)
      τ1 (η 1 0) hspan (by
        intro φ hφ
        change φ ∈
          Sfam.filter (fun φ => Section1.IsIrreducibleCharacterOnGroup φ) at hφ
        have hφdata : φ ∈ Sfam ∧ Section1.IsIrreducibleCharacterOnGroup φ :=
          Finset.mem_filter.mp hφ
        exact hgen φ hφdata.1 hφdata.2)

/- Checked glue for PF `(13.7)`: by `(13.3)(c)`, the row-sum branch is
orthogonal to `η₁₀`; the other branch is the checked `o_tau1_eta` linear
extension above. -/
private theorem theorem_13_7_eta10_orthogonal_to_S1_source
    {G : Type u}
    [Group G]
    [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D H : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (ω : ℕ → ℕ → Section1.ClassFunction W)
    (η : ℕ → ℕ → Section1.ClassFunction G)
    (μ : ℕ → ℕ → Section1.ClassFunction Smax)
    (ν : ℕ → ℕ → Section1.ClassFunction Tmax)
    (μsum : ℕ → Section1.ClassFunction Smax)
    (νsum : ℕ → Section1.ClassFunction Tmax)
    (δ δ' : ℕ → ℤ)
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (hnotation : hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2 p q
      ω η μ ν μsum νsum δ δ' σ)
    (hH : H = P ⊔ C) :
    ∃ (τ1 : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
      (S1 : Finset (Section1.ClassFunction Smax))
      (ζ0 ζ1 : Section1.ClassFunction Smax),
        Section6.coherentExtension Sfam τS τ1 ∧
          H = P ⊔ C ∧
          nonkernelInducedFamily Smax H P S1 ∧
          ζ0 ∈ S1 ∧ ζ1 ∈ S1 ∧ ζ0 ≠ ζ1 ∧
          (∀ ζ : Section1.ClassFunction Smax, ζ ∈ S1 →
            Section5.integerSpan Sfam ζ) ∧
          ∀ ζ : Section1.ClassFunction Smax, ζ ∈ S1 →
            Section1.scalarProduct G (τ1 ζ) (η 1 0) = 0 := by
  classical
  have hsourceFull := hsource
  have h13_3 := (theorem_13_3 Smax Tmax W W1 W2 P Q U V C D
    Sfam Tfam τS τT p q u v c d hsource).1
  rcases (h13_3 ω η μ ν μsum νsum δ δ' σ hnotation).2 with
    ⟨τ1, hcoh, houtput⟩
  rcases theorem_13_7_eta10_S1_cases_or_orthogonal_source
      Smax Tmax W W1 W2 P Q U V C D H Sfam Tfam τS τ1 τT
      ω η μ ν μsum νsum δ δ' σ p q u v c d hsourceFull hnotation hcoh hH with
    ⟨S1, ζ0, ζ1, hH5, hS1, hζ0, hζ1, hζ_ne, hcases⟩
  have hS1Span : ∀ ζ : Section1.ClassFunction Smax, ζ ∈ S1 →
      Section5.integerSpan Sfam ζ := by
    intro ζ hζ
    rcases section13_calS1_cases_or_integerSpan_source
        Smax Tmax W W1 W2 P Q U V C D H Sfam Tfam τS τT
        ω η μ ν μsum νsum δ δ' σ p q u v c d hsourceFull hnotation
          hH5 S1 hS1 ζ hζ with ⟨j, hj0, hjp, rfl⟩ | hspan
    · exact Section5.integerSpan_of_mem Sfam
        (houtput.1 j hj0 hjp).2.2.2
    · exact Section5.integerSpan_mono (Finset.filter_subset _ _) hspan
  rcases hsource with
    ⟨hcaseB, _hSTypeP, _hTTypeP, _hp_card, hq_card, _hC, _hD, _hc_card,
      _hd_card, _hU_card, _hV_card, _hSfam, _hTfam, _hDadeS, _hDadeT,
      _hnotationData⟩
  rcases hcaseB with
    ⟨_hWprod, _hWcyc, hW1ne, _hW2ne, _hWhat, _hSmax, _hTmax, _hSMF,
      _hTMF, _hSeq, _hTeq, _hSdisj, _hTdisj, _hST, _hII, _hStype,
      _hTtype, _hclass⟩
  have h1q : 1 < q := by
    have hW1card : 1 < Nat.card W1 :=
      (Subgroup.one_lt_card_iff_ne_bot (H := W1)).2 hW1ne
    simpa [hq_card] using hW1card
  refine ⟨τ1, S1, ζ0, ζ1, hcoh, hH5, hS1, hζ0, hζ1, hζ_ne,
    hS1Span, ?_⟩
  intro ζ hζ
  rcases hcases ζ hζ with ⟨j, hj0, hjp, rfl⟩ | horth
  · exact theorem_13_7_muSum_orthogonal_eta10_of_characterOutput
      Smax Tmax W W1 W2 P C Sfam τ1 p q u j ω η μ ν μsum νsum δ δ' σ
      hnotation houtput h1q hj0 hjp
  · exact horth

private theorem theorem_13_7_theorem_13_5_hypothesis_core_of_orthogonal
    {G : Type u}
    [Group G]
    [Finite G]
    (Smax H P C : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (S1 : Finset (Section1.ClassFunction Smax))
    (τS τ1 : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (ζ0 ζ1 : Section1.ClassFunction Smax)
    (χ : Section1.ClassFunction G)
    (hH : H = P ⊔ C)
    (hS1 : nonkernelInducedFamily Smax H P S1)
    (hζ0 : ζ0 ∈ S1)
    (hζ1 : ζ1 ∈ S1)
    (hζ_ne : ζ0 ≠ ζ1)
    (hcoh : Section6.coherentExtension Sfam τS τ1)
    (hspan : ∀ ζ : Section1.ClassFunction Smax, ζ ∈ S1 →
      Section5.integerSpan Sfam ζ)
    (hdegree : ∀ ζ : Section1.ClassFunction Smax, ζ ∈ S1 →
      Section1.degree ζ = Section1.degree ζ0)
    (horth : ∀ ζ : Section1.ClassFunction Smax, ζ ∈ S1 →
      Section1.scalarProduct G (τ1 ζ) χ = 0) :
    H = P ⊔ C ∧
      nonkernelInducedFamily Smax H P S1 ∧
      ζ0 ∈ S1 ∧ ζ1 ∈ S1 ∧ ζ0 ≠ ζ1 ∧
      (0 : ℂ) = Section1.scalarProduct G (τS (ζ1 - ζ0)) χ ∧
      ∀ ζ : Section1.ClassFunction Smax, ζ ∈ S1 → ζ ≠ ζ0 → ζ ≠ ζ1 →
        Section1.scalarProduct G (τS (ζ - ζ0)) χ = 0 := by
  have hagree : ∀ ζ : Section1.ClassFunction Smax, ∀ hζ : ζ ∈ S1,
      τ1 (ζ - ζ0) = τS (ζ - ζ0) := by
    intro ζ hζ
    apply hcoh.2.2
    refine ⟨Section5.integerSpan_sub (hspan ζ hζ) (hspan ζ0 hζ0), ?_⟩
    apply (Section5.supportedOn_puncturedSet_iff_degree_eq_zero _).2
    change Section1.degree ζ - Section1.degree ζ0 = 0
    rw [hdegree ζ hζ]
    simp
  refine ⟨hH, hS1, hζ0, hζ1, hζ_ne, ?_, ?_⟩
  · calc
      (0 : ℂ) = Section1.scalarProduct G (τ1 (ζ1 - ζ0)) χ := by
        rw [map_sub, Section5.scalarProduct_sub_left,
          horth ζ1 hζ1, horth ζ0 hζ0]
        simp
      _ = Section1.scalarProduct G (τS (ζ1 - ζ0)) χ := by
        rw [hagree ζ1 hζ1]
  · intro ζ hζ _hζ_ne0 _hζ_ne1
    calc
      Section1.scalarProduct G (τS (ζ - ζ0)) χ =
          Section1.scalarProduct G (τ1 (ζ - ζ0)) χ := by
        rw [hagree ζ hζ]
      _ = 0 := by
        rw [map_sub, Section5.scalarProduct_sub_left,
          horth ζ hζ, horth ζ0 hζ0]
        simp

/- Checked glue from the source `η₁₀ ⟂ S₁^{τ₁}` package to the difference
orthogonality expected by PF `(13.5)`. -/
private theorem theorem_13_7_theorem_13_5_hypothesis_core_source
    {G : Type u}
    [Group G]
    [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D H : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (ω : ℕ → ℕ → Section1.ClassFunction W)
    (η : ℕ → ℕ → Section1.ClassFunction G)
    (μ : ℕ → ℕ → Section1.ClassFunction Smax)
    (ν : ℕ → ℕ → Section1.ClassFunction Tmax)
    (μsum : ℕ → Section1.ClassFunction Smax)
    (νsum : ℕ → Section1.ClassFunction Tmax)
    (δ δ' : ℕ → ℤ)
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (hnotation : hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2 p q
      ω η μ ν μsum νsum δ δ' σ)
    (hH : H = P ⊔ C) :
    ∃ (S1 : Finset (Section1.ClassFunction Smax))
      (ζ0 ζ1 : Section1.ClassFunction Smax),
        H = P ⊔ C ∧
          nonkernelInducedFamily Smax H P S1 ∧
          ζ0 ∈ S1 ∧ ζ1 ∈ S1 ∧ ζ0 ≠ ζ1 ∧
          (0 : ℂ) = Section1.scalarProduct G (τS (ζ1 - ζ0)) (η 1 0) ∧
          ∀ ζ : Section1.ClassFunction Smax, ζ ∈ S1 → ζ ≠ ζ0 → ζ ≠ ζ1 →
            Section1.scalarProduct G (τS (ζ - ζ0)) (η 1 0) = 0 := by
  rcases theorem_13_7_eta10_orthogonal_to_S1_source
      Smax Tmax W W1 W2 P Q U V C D H Sfam Tfam τS τT
      ω η μ ν μsum νsum δ δ' σ p q u v c d hsource hnotation hH with
    ⟨τ1, S1, ζ0, ζ1, hcoh, hH5, hS1, hζ0, hζ1, hζ_ne,
      hspan, horth⟩
  letI : IsMulCommutative (H.subgroupOf Smax) :=
    theorem_13_5_H_subgroupOf_isMulCommutative
      Smax Tmax W W1 W2 P Q U V C D H Sfam Tfam τS τT
        p q u v c d hsource hH5 hS1.1
  have hdegree : ∀ ζ : Section1.ClassFunction Smax, ζ ∈ S1 →
      Section1.degree ζ = Section1.degree ζ0 := by
    intro ζ hζ
    rcases (hS1.2.2 ζ).mp hζ with
      ⟨θ, hθirr, _hθnotker, hζind⟩
    rcases (hS1.2.2 ζ0).mp hζ0 with
      ⟨θ0, hθ0irr, _hθ0notker, hζ0ind⟩
    have hθdegree : Section1.degree θ = 1 :=
      Section1.isIrreducibleCharacterOnGroup_degree_eq_one_of_commutative hθirr
    have hθ0degree : Section1.degree θ0 = 1 :=
      Section1.isIrreducibleCharacterOnGroup_degree_eq_one_of_commutative hθ0irr
    calc
      Section1.degree ζ =
          (Subgroup.index (H.subgroupOf Smax) : ℂ) * Section1.degree θ := by
        rw [hζind, Section1.degree_inducedClassFunction]
      _ = (Subgroup.index (H.subgroupOf Smax) : ℂ) := by
        rw [hθdegree, mul_one]
      _ = (Subgroup.index (H.subgroupOf Smax) : ℂ) * Section1.degree θ0 := by
        rw [hθ0degree, mul_one]
      _ = Section1.degree ζ0 := by
        rw [hζ0ind, Section1.degree_inducedClassFunction]
  exact ⟨S1, ζ0, ζ1,
    theorem_13_7_theorem_13_5_hypothesis_core_of_orthogonal
      Smax H P C Sfam S1 τS τ1 ζ0 ζ1 (η 1 0)
        hH5 hS1 hζ0 hζ1 hζ_ne hcoh hspan hdegree horth⟩

private theorem theorem_13_7_eta10_virtual_of_source
    {G : Type u}
    [Group G]
    [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (ω : ℕ → ℕ → Section1.ClassFunction W)
    (η : ℕ → ℕ → Section1.ClassFunction G)
    (μ : ℕ → ℕ → Section1.ClassFunction Smax)
    (ν : ℕ → ℕ → Section1.ClassFunction Tmax)
    (μsum : ℕ → Section1.ClassFunction Smax)
    (νsum : ℕ → Section1.ClassFunction Tmax)
    (δ δ' : ℕ → ℤ)
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (hnotation : hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2 p q
      ω η μ ν μsum νsum δ δ' σ) :
    Theory.Character.IsVirtualCharacter (η 1 0) := by
  rcases hsource with
    ⟨hcaseB, _hptypeS, _hptypeT, hp_card, hq_card, _htail⟩
  rcases hcaseB with
    ⟨_hWprod, _hWcyc, hW1ne, _hW2ne, _hWhat, _hSmax, _hTmax, _hSMF,
      _hTMF, _hSeq, _hTeq, _hSdisj, _hTdisj, _hST, _hII, _hStype,
      _hTtype, _hclass⟩
  rcases hnotation with
    ⟨homegaData, hσmap, hη, _hδ, _hδ', _hμirr, _hνirr,
      _hμzero_nonprincipal, _hνzero_nonprincipal, _hμeq, _hνeq, _hμsum,
      _hνsum⟩
  rcases homegaData with ⟨_h31, _hqpos, _hppos, ωFin, hωFin, hωNat⟩
  have h1q : 1 < q := by
    have hW1card : 1 < Nat.card W1 :=
      (Subgroup.one_lt_card_iff_ne_bot (H := W1)).2 hW1ne
    simpa [hq_card] using hW1card
  have h0p : 0 < p := by
    simpa [hp_card] using (Nat.card_pos (α := W2))
  let i1 : Fin q := ⟨1, h1q⟩
  let j0 : Fin p := ⟨0, h0p⟩
  have hη10 : η 1 0 = σ (ωFin i1 j0) := by
    rw [hη 1 0 h1q h0p, hωNat 1 0 h1q h0p]
  have hωvirt : Theory.Character.IsVirtualCharacter (ωFin i1 j0) :=
    Section3.isVirtualCharacter_of_irreducibleCharacterOnGroup (hωFin.irreducible i1 j0)
  rw [hη10]
  exact hσmap.2.1 (ωFin i1 j0) hωvirt

private theorem theorem_13_7_theorem_13_5_hypothesis_source
    {G : Type u}
    [Group G]
    [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D H : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (ω : ℕ → ℕ → Section1.ClassFunction W)
    (η : ℕ → ℕ → Section1.ClassFunction G)
    (μ : ℕ → ℕ → Section1.ClassFunction Smax)
    (ν : ℕ → ℕ → Section1.ClassFunction Tmax)
    (μsum : ℕ → Section1.ClassFunction Smax)
    (νsum : ℕ → Section1.ClassFunction Tmax)
    (δ δ' : ℕ → ℤ)
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (hnotation : hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2 p q
      ω η μ ν μsum νsum δ δ' σ)
    (hH : H = P ⊔ C) :
    ∃ (S1 : Finset (Section1.ClassFunction Smax))
      (ζ0 ζ1 : Section1.ClassFunction Smax),
        theorem_13_5_hypothesis Smax H P C S1 τS ζ0 ζ1 (η 1 0) (0 : ℂ) := by
  rcases theorem_13_7_theorem_13_5_hypothesis_core_source
      Smax Tmax W W1 W2 P Q U V C D H Sfam Tfam τS τT
      ω η μ ν μsum νsum δ δ' σ p q u v c d hsource hnotation hH with
    ⟨S1, ζ0, ζ1, hH5, hS1, hζ0, hζ1, hζ_ne, ha, horth⟩
  have hηvirt : Theory.Character.IsVirtualCharacter (η 1 0) :=
    theorem_13_7_eta10_virtual_of_source
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
      ω η μ ν μsum νsum δ δ' σ p q u v c d hsource hnotation
  exact ⟨S1, ζ0, ζ1, hH5, hS1, hζ0, hζ1, hζ_ne, hηvirt, ha, horth⟩

private theorem theorem_13_7_restrictionData_of_source
    {G : Type u}
    [Group G]
    [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D H : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (ζ1 : Section1.ClassFunction Smax)
    (p q u v c d : ℕ)
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (hH : H = P ⊔ C) :
    ∃ eta10H : Section1.ClassFunction H, classFunctionRestrictionData H Smax ζ1 eta10H := by
  rcases hsource with
    ⟨_hcase, hSTypeP, _hTTypeP, _hp_card, _hq_card, hCeq, _hD, _hc_card,
      _hd_card, _hU_card, _hV_card, _hSfam, _hTfam, _hDadeS, _hDadeT,
      _hnotation, _hDadeDiff, _hZeroDegree, _hConjIndex, _hConjBetaTau,
      _hChoice, _hMin, _hFourSixS, _hFourSixT⟩
  rcases hSTypeP with
    ⟨_hMF, _hW1cyc, _hW1ne, _hW1Hall, _hScomp, hUleDer, _hUnil,
      _hW1norm, hDercomp, _hMFnotcyc, _hsecond, _hfit, _hfitDer,
      _hW2le, _hW2cyc, _hW2ne, _hcent, _hnorm⟩
  have hDerLe : ambientDerivedSubgroup Smax ≤ Smax :=
    section12_ambientDerivedSubgroup_le (G := G) (E := Smax)
  have hPleS : P ≤ Smax := hDercomp.1.trans hDerLe
  have hCleU : C ≤ U := by
    rw [hCeq]
    exact inf_le_left
  have hCleS : C ≤ Smax := hCleU.trans (hUleDer.trans hDerLe)
  have hHS : H ≤ Smax := by
    rw [hH]
    exact sup_le hPleS hCleS
  let eta10H : Section1.ClassFunction H := fun x => ζ1 ⟨(x : G), hHS x.property⟩
  exact ⟨eta10H, hHS, fun x => rfl⟩

private theorem theorem_13_7_theorem_13_5_input_source
    {G : Type u}
    [Group G]
    [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D H : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (ω : ℕ → ℕ → Section1.ClassFunction W)
    (η : ℕ → ℕ → Section1.ClassFunction G)
    (μ : ℕ → ℕ → Section1.ClassFunction Smax)
    (ν : ℕ → ℕ → Section1.ClassFunction Tmax)
    (μsum : ℕ → Section1.ClassFunction Smax)
    (νsum : ℕ → Section1.ClassFunction Tmax)
    (δ δ' : ℕ → ℤ)
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (hnotation : hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2 p q
      ω η μ ν μsum νsum δ δ' σ)
    (hH : H = P ⊔ C) :
    ∃ (S1 : Finset (Section1.ClassFunction Smax))
      (ζ0 ζ1 : Section1.ClassFunction Smax)
      (eta10H : Section1.ClassFunction H),
        theorem_13_5_hypothesis Smax H P C S1 τS ζ0 ζ1 (η 1 0) (0 : ℂ) ∧
          classFunctionRestrictionData H Smax ζ1 eta10H := by
  rcases theorem_13_7_theorem_13_5_hypothesis_source
      Smax Tmax W W1 W2 P Q U V C D H Sfam Tfam τS τT
      ω η μ ν μsum νsum δ δ' σ p q u v c d hsource hnotation hH with
    ⟨S1, ζ0, ζ1, h5hyp⟩
  rcases theorem_13_7_restrictionData_of_source
      Smax Tmax W W1 W2 P Q U V C D H Sfam Tfam τS τT ζ1
      p q u v c d hsource hH with
    ⟨eta10H, hres⟩
  exact ⟨S1, ζ0, ζ1, eta10H, h5hyp, hres⟩

/- Source leaf for PF `(13.7)`: choose `x ∈ W₂#`, `y ∈ W₁#`, and a
primitive `q`th root `ε`; `(1.10)(a)`, `(3.2)(c)`, and `(13.5)(a)` give a
nonzero value of the kernel constituent `α`. -/
private theorem theorem_13_7_exists_Hsharp_mem_W2_of_source
    {G : Type u}
    [Group G]
    [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D H : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (hH : H = P ⊔ C) :
    ∃ x : H, (x : G) ∈ W2 ∧ (x : G) ≠ 1 := by
  rcases hsource with
    ⟨_hcase, hSTypeP, _hTTypeP, _hp_card, _hq_card, _hCeq, _hD, _hc_card,
      _hd_card, _hU_card, _hV_card, _hSfam, _hTfam, _hDadeS, _hDadeT,
      _hnotation, _hDadeDiff, _hZeroDegree, _hConjIndex, _hConjBetaTau,
      _hChoice, _hMin, _hFourSixS, _hFourSixT⟩
  rcases hSTypeP with
    ⟨_hMF, _hW1cyc, _hW1ne, _hW1Hall, _hScomp, _hUleDer, _hUnil,
      _hW1norm, _hDercomp, _hMFnotcyc, _hsecond, _hfit, _hfitDer,
      hW2le, _hW2cyc, hW2ne, _hcent, _hnorm⟩
  have hW2leP : W2 ≤ P := (le_inf_iff.mp hW2le).1
  have hW2_nontrivial : ∃ x : G, x ∈ W2 ∧ x ≠ 1 := by
    by_contra hnone
    have hW2_le_bot : W2 ≤ ⊥ := by
      intro x hx
      by_cases hx1 : x = 1
      · simp [hx1]
      · exact False.elim (hnone ⟨x, hx, hx1⟩)
    exact hW2ne (le_antisymm hW2_le_bot bot_le)
  rcases hW2_nontrivial with ⟨x, hxW2, hxne⟩
  have hxH : x ∈ H := by
    rw [hH]
    exact (le_sup_left : P ≤ P ⊔ C) (hW2leP hxW2)
  exact ⟨⟨x, hxH⟩, hxW2, hxne⟩

private theorem theorem_13_7_exists_W1_order_comm_of_source
    {G : Type u}
    [Group G]
    [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D H : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (x : H)
    (hxW2 : (x : G) ∈ W2) :
    ∃ y : G, y ∈ W1 ∧ y ≠ 1 ∧ orderOf y = q ∧
      y * (x : G) = (x : G) * y := by
  rcases hsource with
    ⟨_hcase, hSTypeP, _hTTypeP, _hp_card, hq_card, _hCeq, _hD, _hc_card,
      _hd_card, _hU_card, _hV_card, _hSfam, _hTfam, _hDadeS, _hDadeT,
      _hnotation, _hDadeDiff, _hZeroDegree, _hConjIndex, _hConjBetaTau,
      _hChoice, _hMin, _hFourSixS, _hFourSixT⟩
  rcases hSTypeP with
    ⟨_hMF, hW1cyc, hW1ne, _hW1Hall, _hScomp, _hUleDer, _hUnil,
      _hW1norm, _hDercomp, _hMFnotcyc, _hsecond, _hfit, _hfitDer,
      _hW2le, _hW2cyc, _hW2ne, hcentW1, _hnorm⟩
  letI : IsCyclic W1 := hW1cyc
  rcases IsCyclic.exists_generator (α := W1) with ⟨yW1, hygen⟩
  let y : G := yW1
  have hyW1 : y ∈ W1 := yW1.property
  have hy_order_sub : orderOf yW1 = Nat.card W1 :=
    orderOf_eq_card_of_forall_mem_zpowers hygen
  have hy_order : orderOf y = q := by
    have hy_order_card : orderOf y = Nat.card W1 := by
      simpa [y, Subgroup.orderOf_coe] using hy_order_sub
    exact hy_order_card.trans hq_card.symm
  have hq_gt_one : 1 < q := by
    have hW1card : 1 < Nat.card W1 :=
      (Subgroup.one_lt_card_iff_ne_bot (H := W1)).2 hW1ne
    simpa [hq_card] using hW1card
  have hyne : y ≠ 1 := by
    intro hy1
    have hq_eq_one : q = 1 := by
      have hone : orderOf y = 1 := by
        simp [hy1]
      exact hy_order.symm.trans hone
    exact (Nat.ne_of_gt hq_gt_one) hq_eq_one
  have hW2centW1 : W2 ≤ Subgroup.centralizer (W1 : Set G) := by
    intro z hz
    rw [Subgroup.mem_centralizer_iff]
    intro a haW1
    by_cases ha1 : a = 1
    · simp [ha1]
    · have hzCent : z ∈ elementCentralizerIn (ambientDerivedSubgroup Smax) a := by
        simpa [hcentW1 a haW1 ha1] using hz
      exact (Subgroup.mem_centralizer_singleton_iff.mp hzCent.2).symm
  have hcomm : y * (x : G) = (x : G) * y :=
    Subgroup.mem_centralizer_iff.mp (hW2centW1 hxW2) y hyW1
  exact ⟨y, hyW1, hyne, hy_order, hcomm⟩

private theorem theorem_13_7_congruentModOneSub_symm
    {etaRoot eps z w : ℂ}
    (hepsMem : eps ∈ Theory.Character.cyclotomicOrder etaRoot)
    (hzMem : z ∈ Theory.Character.cyclotomicOrder etaRoot)
    (hwMem : w ∈ Theory.Character.cyclotomicOrder etaRoot)
    (hcong : Theory.Character.CongruentModOneSub etaRoot eps z w hepsMem hzMem hwMem) :
    Theory.Character.CongruentModOneSub etaRoot eps w z hepsMem hwMem hzMem := by
  let A := Theory.Character.cyclotomicOrder etaRoot
  let oneSub : A := ⟨1 - eps, A.sub_mem A.one_mem hepsMem⟩
  have hcongA : Theory.Character.congruentModIn A oneSub (⟨z, hzMem⟩ : A)
      ⟨w, hwMem⟩ := by
    simpa [Theory.Character.CongruentModOneSub, A, oneSub] using hcong
  rw [Theory.Character.congruentModIn_iff_dvd] at hcongA
  change Theory.Character.congruentModIn A oneSub (⟨w, hwMem⟩ : A) ⟨z, hzMem⟩
  rw [Theory.Character.congruentModIn_iff_dvd]
  obtain ⟨r, hr⟩ := hcongA
  refine ⟨-r, ?_⟩
  calc
    (⟨w, hwMem⟩ : A) - ⟨z, hzMem⟩ = -(⟨z, hzMem⟩ - ⟨w, hwMem⟩) := by
      ring
    _ = -(oneSub * r) := by rw [hr]
    _ = oneSub * (-r) := by ring

private theorem theorem_13_7_congruentModOneSub_trans
    {etaRoot eps z w v : ℂ}
    (hepsMem : eps ∈ Theory.Character.cyclotomicOrder etaRoot)
    (hzMem : z ∈ Theory.Character.cyclotomicOrder etaRoot)
    (hwMem : w ∈ Theory.Character.cyclotomicOrder etaRoot)
    (hvMem : v ∈ Theory.Character.cyclotomicOrder etaRoot)
    (hzw : Theory.Character.CongruentModOneSub etaRoot eps z w hepsMem hzMem hwMem)
    (hwv : Theory.Character.CongruentModOneSub etaRoot eps w v hepsMem hwMem hvMem) :
    Theory.Character.CongruentModOneSub etaRoot eps z v hepsMem hzMem hvMem := by
  let A := Theory.Character.cyclotomicOrder etaRoot
  let oneSub : A := ⟨1 - eps, A.sub_mem A.one_mem hepsMem⟩
  have hzwA : Theory.Character.congruentModIn A oneSub (⟨z, hzMem⟩ : A)
      ⟨w, hwMem⟩ := by
    simpa [Theory.Character.CongruentModOneSub, A, oneSub] using hzw
  have hwvA : Theory.Character.congruentModIn A oneSub (⟨w, hwMem⟩ : A)
      ⟨v, hvMem⟩ := by
    simpa [Theory.Character.CongruentModOneSub, A, oneSub] using hwv
  rw [Theory.Character.congruentModIn_iff_dvd] at hzwA hwvA
  change Theory.Character.congruentModIn A oneSub (⟨z, hzMem⟩ : A) ⟨v, hvMem⟩
  rw [Theory.Character.congruentModIn_iff_dvd]
  obtain ⟨r, hr⟩ := hzwA
  obtain ⟨s, hs⟩ := hwvA
  refine ⟨r + s, ?_⟩
  calc
    (⟨z, hzMem⟩ : A) - ⟨v, hvMem⟩ =
        (⟨z, hzMem⟩ - ⟨w, hwMem⟩) + (⟨w, hwMem⟩ - ⟨v, hvMem⟩) := by
      ring
    _ = oneSub * r + oneSub * s := by rw [hr, hs]
    _ = oneSub * (r + s) := by ring

private theorem theorem_13_7_eta10_one_mod_of_mul_congruence
    {etaRoot eps z x : ℂ}
    (hepsMem : eps ∈ Theory.Character.cyclotomicOrder etaRoot)
    (hzMem₁ : z ∈ Theory.Character.cyclotomicOrder etaRoot)
    (hxMem : x ∈ Theory.Character.cyclotomicOrder etaRoot)
    (hzMem₂ : z ∈ Theory.Character.cyclotomicOrder etaRoot)
    (hzx : Theory.Character.CongruentModOneSub etaRoot eps z x hepsMem hzMem₁ hxMem)
    (hz1 : Theory.Character.CongruentModOneSub etaRoot eps z 1 hepsMem hzMem₂
      (Theory.Character.cyclotomicOrder etaRoot).one_mem) :
    Theory.Character.CongruentModOneSub etaRoot eps x 1 hepsMem hxMem
      (Theory.Character.cyclotomicOrder etaRoot).one_mem := by
  have hxz := theorem_13_7_congruentModOneSub_symm hepsMem hzMem₁ hxMem hzx
  have hz1' : Theory.Character.CongruentModOneSub etaRoot eps z 1 hepsMem hzMem₁
      (Theory.Character.cyclotomicOrder etaRoot).one_mem := by
    simpa [Theory.Character.CongruentModOneSub] using hz1
  exact theorem_13_7_congruentModOneSub_trans hepsMem hxMem hzMem₁
    (Theory.Character.cyclotomicOrder etaRoot).one_mem hxz hz1'

private theorem theorem_13_7_eta10_mul_congruent_of_order_comm
    {G : Type u} [Group G] [Finite G]
    {q : ℕ} {etaRoot eps : ℂ} {eta10 : G → ℂ} {x y : G}
    (hq : Nat.Prime q)
    (hetaRoot : IsPrimitiveRoot etaRoot (Nat.card G))
    (heps : IsPrimitiveRoot eps q)
    (hepsMem : eps ∈ Theory.Character.cyclotomicOrder etaRoot)
    (hvirt : Theory.Character.IsVirtualCharacter eta10)
    (hy_order : orderOf y = q)
    (hcomm : y * x = x * y) :
    ∃ hmulMem : eta10 (y * x) ∈ Theory.Character.cyclotomicOrder etaRoot,
      ∃ hxMem : eta10 x ∈ Theory.Character.cyclotomicOrder etaRoot,
        Theory.Character.CongruentModOneSub etaRoot eps (eta10 (y * x)) (eta10 x)
          hepsMem hmulMem hxMem := by
  exact Theory.Character.virtualCharacter_congruent_at_mul heps hq.ne_zero hetaRoot hepsMem
    hvirt hy_order hcomm

private theorem theorem_13_7_nonzero_of_congruent_one_mod_one_sub
    {p : ℕ} {etaRoot eps z : ℂ}
    (hp : Nat.Prime p)
    (heps : IsPrimitiveRoot eps p)
    (heta_int : IsIntegral ℤ etaRoot)
    (hepsMem : eps ∈ Theory.Character.cyclotomicOrder etaRoot)
    (hzMem : z ∈ Theory.Character.cyclotomicOrder etaRoot)
    (hcong : Theory.Character.CongruentModOneSub etaRoot eps z 1 hepsMem hzMem
      (Theory.Character.cyclotomicOrder etaRoot).one_mem) :
    z ≠ 0 := by
  intro hz0
  let A := Theory.Character.cyclotomicOrder etaRoot
  let oneSub : A := ⟨1 - eps, A.sub_mem A.one_mem hepsMem⟩
  let zA : A := ⟨z, hzMem⟩
  have hcongA : Theory.Character.congruentModIn A oneSub zA (1 : A) :=
    hcong
  rw [Theory.Character.congruentModIn_iff_dvd] at hcongA
  have hdivOne : oneSub ∣ (1 : A) := by
    obtain ⟨r, hr⟩ := hcongA
    refine ⟨-r, ?_⟩
    have hzA0 : zA = 0 := Subtype.ext hz0
    calc
      (1 : A) = -(zA - 1) := by simp [hzA0]
      _ = -(oneSub * r) := by rw [hr]
      _ = oneSub * (-r) := by ring
  have hcongA10 : Theory.Character.congruentModIn A oneSub (1 : A) (0 : A) := by
    rw [Theory.Character.congruentModIn_iff_dvd]
    simpa using hdivOne
  have hcong10 : Theory.Character.CongruentModOneSub etaRoot eps (((1 : ℤ) : ℂ)) 0
      hepsMem
      (Theory.Character.intCast_mem_cyclotomicOrder etaRoot (1 : ℤ))
      (Theory.Character.cyclotomicOrder etaRoot).zero_mem := by
    unfold Theory.Character.CongruentModOneSub
    convert hcongA10 using 1
    · apply Subtype.ext; simp
  have hdivInt : (p : ℤ) ∣ (1 : ℤ) :=
    Theory.Character.prime_dvd_int_of_congruent_zero_mod_one_sub hp heps heta_int
      hepsMem (1 : ℤ) hcong10
  rcases hdivInt with ⟨k, hk⟩
  have hp_dvd_one_nat : p ∣ 1 := by
    refine ⟨Int.natAbs k, ?_⟩
    have habs := congrArg Int.natAbs hk
    simpa [Int.natAbs_mul] using habs
  exact hp.ne_one (Nat.dvd_one.mp hp_dvd_one_nat)

private theorem theorem_13_7_eta10_eq_omega10_on_yx_of_source
    {G : Type u}
    [Group G]
    [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D H : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (ω : ℕ → ℕ → Section1.ClassFunction W)
    (η : ℕ → ℕ → Section1.ClassFunction G)
    (μ : ℕ → ℕ → Section1.ClassFunction Smax)
    (ν : ℕ → ℕ → Section1.ClassFunction Tmax)
    (μsum : ℕ → Section1.ClassFunction Smax)
    (νsum : ℕ → Section1.ClassFunction Tmax)
    (δ δ' : ℕ → ℤ)
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (_hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (hnotation : hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2 p q
      ω η μ ν μsum νsum δ δ' σ)
    (x : H)
    (hxW2 : (x : G) ∈ W2)
    (hxne : (x : G) ≠ 1)
    (y : G)
    (hyW1 : y ∈ W1)
    (hyne : y ≠ 1)
    (hy_order : orderOf y = q) :
    ∃ hxyW : y * (x : G) ∈ W,
      (η 1 0) (y * (x : G)) = (ω 1 0) ⟨y * (x : G), hxyW⟩ := by
  rcases hnotation with
    ⟨homegaData, hσmap, hη, _hδ, _hδ', _hμirr, _hνirr,
      _hμzero_nonprincipal, _hνzero_nonprincipal, _hμeq, _hνeq, _hμsum,
      _hνsum⟩
  rcases homegaData with ⟨h31, _hqpos, hp_pos, ωFin, hωFin, hωNat⟩
  rcases hσmap with
    ⟨_hIso, _hVirt, _hInd, _hClass, _hPrincipal, hAgree, _hVanish⟩
  have hq_pos : 0 < q := by
    simpa [← hy_order] using orderOf_pos y
  have hq_ne_one : q ≠ 1 := by
    intro hq1
    exact hyne ((orderOf_eq_one_iff).1 (by simp [hy_order, hq1]))
  have h1q : 1 < q := by omega
  change Section3.isCyclicTIHypothesis W1 W2 W at h31
  rcases h31 with ⟨hW1leW, hW2leW, hIP, _hWcyc, _hWodd, _hW1card, _hW2card,
    _hTI⟩
  have hxyCyc : y * (x : G) ∈ Section3.cyclicTISet W1 W2 W := by
    refine (Section3.cyclicTISet_mem_iff W1 W2 W).2 ?_
    constructor
    · exact W.mul_mem (hW1leW hyW1) (hW2leW hxW2)
    · constructor
      · intro hxyW1
        have hxW1 : (x : G) ∈ W1 := by
          have hxW1' : y⁻¹ * (y * (x : G)) ∈ W1 :=
            W1.mul_mem (W1.inv_mem hyW1) hxyW1
          simpa [mul_assoc] using hxW1'
        have hxBot : (x : G) ∈ (⊥ : Subgroup G) := by
          simpa [hIP.inf_eq_bot] using (Subgroup.mem_inf.mpr ⟨hxW1, hxW2⟩)
        exact hxne (by simpa using hxBot)
      · intro hxyW2
        have hyW2 : y ∈ W2 := by
          have hyW2' : (y * (x : G)) * (x : G)⁻¹ ∈ W2 :=
            W2.mul_mem hxyW2 (W2.inv_mem hxW2)
          simpa [mul_assoc] using hyW2'
        have hyBot : y ∈ (⊥ : Subgroup G) := by
          simpa [hIP.inf_eq_bot] using (Subgroup.mem_inf.mpr ⟨hyW1, hyW2⟩)
        exact hyne (by simpa using hyBot)
  let hxyW : y * (x : G) ∈ W := Section3.cyclicTISet_subset W1 W2 W hxyCyc
  have hω10_class : Section1.IsClassFunction (ω 1 0) := by
    rw [hωNat 1 0 h1q hp_pos]
    exact hωFin.is_class ⟨1, h1q⟩ ⟨0, hp_pos⟩
  have hη10 : η 1 0 = σ (ω 1 0) := hη 1 0 h1q hp_pos
  refine ⟨hxyW, ?_⟩
  rw [hη10]
  exact hAgree (ω 1 0) hω10_class (y * (x : G)) hxyCyc

private theorem theorem_13_7_omega10_value_on_W2_eq_one_of_source
    {G : Type u}
    [Group G]
    [Finite G]
    (Smax Tmax W W1 W2 H : Subgroup G)
    (ω : ℕ → ℕ → Section1.ClassFunction W)
    (η : ℕ → ℕ → Section1.ClassFunction G)
    (μ : ℕ → ℕ → Section1.ClassFunction Smax)
    (ν : ℕ → ℕ → Section1.ClassFunction Tmax)
    (μsum : ℕ → Section1.ClassFunction Smax)
    (νsum : ℕ → Section1.ClassFunction Tmax)
    (δ δ' : ℕ → ℤ)
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
    (p q : ℕ)
    (hnotation : hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2 p q
      ω η μ ν μsum νsum δ δ' σ)
    (x : H)
    (hxW2 : (x : G) ∈ W2)
    (y : G)
    (hyne : y ≠ 1)
    (hy_order : orderOf y = q) :
    ∃ hxW : (x : G) ∈ W, (ω 1 0) ⟨(x : G), hxW⟩ = 1 := by
  rcases hnotation with
    ⟨homegaData, _hσmap, _hη, _hδ, _hδ', _hμirr, _hνirr,
      _hμzero_nonprincipal, _hνzero_nonprincipal, _hμeq, _hνeq, _hμsum,
      _hνsum⟩
  rcases homegaData with ⟨h31, _hqpos, hp_pos, ωFin, hωFin, hωNat⟩
  have hq_ne_one : q ≠ 1 := by
    intro hq1
    exact hyne ((orderOf_eq_one_iff).1 (by simp [hy_order, hq1]))
  have h1q : 1 < q := by
    have hq_pos : 0 < q := by
      simpa [← hy_order] using orderOf_pos y
    omega
  change Section3.isCyclicTIHypothesis W1 W2 W at h31
  rcases h31 with ⟨_hW1leW, hW2leW, _hIP, _hWcyc, _hWodd, _hW1card, _hW2card,
    _hTI⟩
  let hxW : (x : G) ∈ W := hW2leW hxW2
  refine ⟨hxW, ?_⟩
  rw [hωNat 1 0 h1q hp_pos]
  have hker := hωFin.left_kernel ⟨1, h1q⟩ ⟨⟨(x : G), hxW⟩, hxW2⟩
  simpa [hωFin.degree_one ⟨1, h1q⟩ ⟨0, hp_pos⟩] using hker

private theorem theorem_13_7_virtualCharacter_congruent_at_mul_of_order_dvd
    {K : Type*} [Group K] [Finite K]
    {p M : ℕ} {etaRoot eps : ℂ}
    (heps : IsPrimitiveRoot eps p) (hp : p ≠ 0)
    (hetaRoot : IsPrimitiveRoot etaRoot M) (hM : M ≠ 0)
    (hepsMem : eps ∈ Theory.Character.cyclotomicOrder etaRoot)
    {χ : K → ℂ} (hχ : Theory.Character.IsVirtualCharacter χ)
    {x y : K}
    (hx_order : orderOf x = p)
    (hy_order_dvd : orderOf y ∣ M)
    (hcomm : x * y = y * x) :
    ∃ hxy : χ (x * y) ∈ Theory.Character.cyclotomicOrder etaRoot,
      ∃ hy : χ y ∈ Theory.Character.cyclotomicOrder etaRoot,
        Theory.Character.CongruentModOneSub etaRoot eps (χ (x * y)) (χ y)
          hepsMem hxy hy := by
  classical
  rcases hχ with ⟨r, m, n, ρ, hχeq⟩
  let A := Theory.Character.cyclotomicOrder etaRoot
  have hrep : ∀ i : Fin r,
      ∃ hxy : (ρ i).character (x * y) ∈ A,
        ∃ hy : (ρ i).character y ∈ A,
          Theory.Character.CongruentModOneSub etaRoot eps
            ((ρ i).character (x * y)) ((ρ i).character y) hepsMem hxy hy := by
    intro i
    let N := orderOf y
    have hN : N ≠ 0 := Nat.ne_of_gt (orderOf_pos y)
    have hNM : N ∣ M := by
      simpa [N] using hy_order_dvd
    have hxpow : x ^ p = 1 := by
      rw [← hx_order]
      exact pow_orderOf_eq_one x
    have hf : (ρ i x) ^ p = 1 := by
      rw [← MonoidHom.map_pow, hxpow, MonoidHom.map_one]
    have hTpow : (ρ i y) ^ N = 1 := by
      subst N
      rw [← MonoidHom.map_pow, pow_orderOf_eq_one, MonoidHom.map_one]
    have hcommEnd : ρ i x * ρ i y = ρ i y * ρ i x := by
      calc
        ρ i x * ρ i y = ρ i (x * y) := (map_mul (ρ i) x y).symm
        _ = ρ i (y * x) := by rw [hcomm]
        _ = ρ i y * ρ i x := map_mul (ρ i) y x
    rcases Theory.Character.finite_order_commuting_trace_mul_congruent
        (η := etaRoot) (ξ := eps) (p := p) (N := N) (M := M)
        heps hp hetaRoot hM hNM hepsMem (f := ρ i x) (T := ρ i y)
        hN hf hTpow hcommEnd with
      ⟨hmul, hy, hcong⟩
    have hxy : (ρ i).character (x * y) ∈ A := by
      simpa [Representation.character, map_mul] using hmul
    refine ⟨hxy, hy, ?_⟩
    simpa [Theory.Character.CongruentModOneSub, Representation.character, map_mul] using hcong
  choose hxyi hyi hcongi using hrep
  have hxy_mem : χ (x * y) ∈ A := by
    rw [hχeq]
    exact A.sum_mem fun i _ =>
      A.mul_mem (Theory.Character.intCast_mem_cyclotomicOrder etaRoot (m i)) (hxyi i)
  have hy_mem : χ y ∈ A := by
    rw [hχeq]
    exact A.sum_mem fun i _ =>
      A.mul_mem (Theory.Character.intCast_mem_cyclotomicOrder etaRoot (m i)) (hyi i)
  refine ⟨hxy_mem, hy_mem, ?_⟩
  let oneSub : A := ⟨1 - eps, A.sub_mem A.one_mem hepsMem⟩
  change Theory.Character.congruentModIn A oneSub
    (⟨χ (x * y), hxy_mem⟩ : A)
    (⟨χ y, hy_mem⟩ : A)
  let zterm : Fin r → A := fun i =>
    ⟨(m i : ℂ) * (ρ i).character (x * y),
      A.mul_mem (Theory.Character.intCast_mem_cyclotomicOrder etaRoot (m i)) (hxyi i)⟩
  let wterm : Fin r → A := fun i =>
    ⟨(m i : ℂ) * (ρ i).character y,
      A.mul_mem (Theory.Character.intCast_mem_cyclotomicOrder etaRoot (m i)) (hyi i)⟩
  unfold Theory.Character.congruentModIn
  have hdiff :
      (⟨χ (x * y), hxy_mem⟩ : A) - ⟨χ y, hy_mem⟩ =
        ∑ i : Fin r, (zterm i - wterm i) := by
    ext
    change χ (x * y) - χ y = ((∑ i : Fin r, (zterm i - wterm i) : A) : ℂ)
    rw [hχeq]
    simp [Theory.Character.virtualCharacterOfRepresentations, zterm, wterm,
      Finset.sum_sub_distrib]
  rw [hdiff]
  refine Ideal.sum_mem _ fun i _ => ?_
  have hci : Theory.Character.congruentModIn A oneSub
      (⟨(ρ i).character (x * y), hxyi i⟩ : A)
      (⟨(ρ i).character y, hyi i⟩ : A) := by
    simpa [Theory.Character.CongruentModOneSub, oneSub] using hcongi i
  change Theory.Character.congruentModIn A oneSub (zterm i) (wterm i)
  have hmul := Theory.Character.congruentModIn_mul_left hci
    (⟨(m i : ℂ), Theory.Character.intCast_mem_cyclotomicOrder etaRoot (m i)⟩ : A)
  simpa [zterm, wterm] using hmul

/- Source leaf for the prime order `q` used by the post-`cycTIiso_restrict`
primitive-root package. -/
private theorem theorem_13_7_q_prime_of_source
    {G : Type u}
    [Group G]
    [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d) :
    Nat.Prime q := by
  have hcond : Section8.typeIIToIVSourceCondition Smax U W1 :=
    section13_theorem_13_2_case_9_7_hypothesis92SourceCondition_of_sourceContext
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT p q u v c d
      hsource
  have hW1prime : Nat.Prime (Nat.card W1) := by
    rcases hcond with ⟨_hUne, hW1primeOrder, _hTI⟩
    rcases hW1primeOrder with ⟨r, hr⟩
    rw [hr]
    exact r.property
  rcases hsource with
    ⟨_hcase, _hptypeS, _hptypeT, _hp_card, hq_card, _hrest⟩
  rw [hq_card]
  exact hW1prime

private theorem theorem_13_7_primitive_root_package_of_q_prime
    {G : Type u}
    [Group G]
    [Finite G]
    {q : ℕ}
    (hqprime : Nat.Prime q)
    (hqdvd : q ∣ Nat.card G) :
    ∃ (etaRoot eps : ℂ),
      Nat.Prime q ∧
        IsPrimitiveRoot etaRoot (Nat.card G) ∧
        IsPrimitiveRoot eps q ∧
        eps ∈ Theory.Character.cyclotomicOrder etaRoot := by
  let etaRoot : ℂ := Complex.exp (2 * Real.pi * Complex.I / (Nat.card G))
  let eps : ℂ := Complex.exp (2 * Real.pi * Complex.I / q)
  have hGne : Nat.card G ≠ 0 := (Nat.card_pos (α := G)).ne'
  have hetaRoot : IsPrimitiveRoot etaRoot (Nat.card G) := by
    dsimp [etaRoot]
    exact Complex.isPrimitiveRoot_exp (Nat.card G) hGne
  have heps : IsPrimitiveRoot eps q := by
    dsimp [eps]
    exact Complex.isPrimitiveRoot_exp q hqprime.ne_zero
  refine ⟨etaRoot, eps, hqprime, hetaRoot, heps, ?_⟩
  exact Theory.Character.primitive_root_mem_cyclotomicOrder_of_dvd
    hetaRoot hGne heps hqdvd

/- Source leaf for the primitive-root package used by the post-`cycTIiso_restrict`
congruence. -/
private theorem theorem_13_7_omega10_primitive_root_package_source
    {G : Type u}
    [Group G]
    [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D _H : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (ω : ℕ → ℕ → Section1.ClassFunction W)
    (η : ℕ → ℕ → Section1.ClassFunction G)
    (μ : ℕ → ℕ → Section1.ClassFunction Smax)
    (ν : ℕ → ℕ → Section1.ClassFunction Tmax)
    (μsum : ℕ → Section1.ClassFunction Smax)
    (νsum : ℕ → Section1.ClassFunction Tmax)
    (δ δ' : ℕ → ℤ)
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (_hnotation : hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2 p q
      ω η μ ν μsum νsum δ δ' σ) :
    ∃ (etaRoot eps : ℂ),
      Nat.Prime q ∧
        IsPrimitiveRoot etaRoot (Nat.card G) ∧
        IsPrimitiveRoot eps q ∧
        eps ∈ Theory.Character.cyclotomicOrder etaRoot := by
  have hqprime : Nat.Prime q :=
    theorem_13_7_q_prime_of_source Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d hsource
  have hqdvd : q ∣ Nat.card G := by
    rcases hsource with
      ⟨_hcase, _hptypeS, _hptypeT, _hp_card, hq_card, _hC, _hD, _hc_card,
        _hd_card, _hU_card, _hV_card, _hSfam, _hTfam, _hDadeS, _hDadeT,
        _hnotation⟩
    rw [hq_card]
    exact Subgroup.card_subgroup_dvd_card W1
  exact theorem_13_7_primitive_root_package_of_q_prime hqprime hqdvd

private theorem theorem_13_7_omega10_yx_congruent_omega10_x_of_root_package
    {G : Type u}
    [Group G]
    [Finite G]
    (Smax Tmax W W1 W2 H : Subgroup G)
    (ω : ℕ → ℕ → Section1.ClassFunction W)
    (η : ℕ → ℕ → Section1.ClassFunction G)
    (μ : ℕ → ℕ → Section1.ClassFunction Smax)
    (ν : ℕ → ℕ → Section1.ClassFunction Tmax)
    (μsum : ℕ → Section1.ClassFunction Smax)
    (νsum : ℕ → Section1.ClassFunction Tmax)
    (δ δ' : ℕ → ℤ)
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
    (p q : ℕ)
    (hnotation : hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2 p q
      ω η μ ν μsum νsum δ δ' σ)
    (x : H)
    (y : G)
    (hyW1 : y ∈ W1)
    (hyne : y ≠ 1)
    (hy_order : orderOf y = q)
    (hcomm : y * (x : G) = (x : G) * y)
    (hxW : (x : G) ∈ W)
    (hxyW : y * (x : G) ∈ W)
    {etaRoot eps : ℂ}
    (hqprime : Nat.Prime q)
    (hetaRoot : IsPrimitiveRoot etaRoot (Nat.card G))
    (heps : IsPrimitiveRoot eps q)
    (hepsMem : eps ∈ Theory.Character.cyclotomicOrder etaRoot) :
    ∃ hmulMem : (ω 1 0) ⟨y * (x : G), hxyW⟩ ∈
      Theory.Character.cyclotomicOrder etaRoot,
    ∃ hxMem : (ω 1 0) ⟨(x : G), hxW⟩ ∈
      Theory.Character.cyclotomicOrder etaRoot,
      Theory.Character.CongruentModOneSub etaRoot eps
        ((ω 1 0) ⟨y * (x : G), hxyW⟩) ((ω 1 0) ⟨(x : G), hxW⟩)
        hepsMem hmulMem hxMem := by
  rcases hnotation with
    ⟨homegaData, _hσmap, _hη, _hδ, _hδ', _hμirr, _hνirr,
      _hμzero_nonprincipal, _hνzero_nonprincipal, _hμeq, _hνeq, _hμsum,
      _hνsum⟩
  rcases homegaData with ⟨h31, _hqpos, hp_pos, ωFin, hωFin, hωNat⟩
  have hq_ne_one : q ≠ 1 := by
    intro hq1
    exact hyne ((orderOf_eq_one_iff).1 (by simp [hy_order, hq1]))
  have h1q : 1 < q := by
    have hq_pos : 0 < q := by
      simpa [← hy_order] using orderOf_pos y
    omega
  change Section3.isCyclicTIHypothesis W1 W2 W at h31
  rcases h31 with ⟨hW1leW, _hW2leW, _hIP, _hWcyc, _hWodd, _hW1card, _hW2card,
    _hTI⟩
  have hωvirt : Theory.Character.IsVirtualCharacter (ω 1 0) := by
    rw [hωNat 1 0 h1q hp_pos]
    exact Section3.isVirtualCharacter_of_irreducibleCharacterOnGroup
      (hωFin.irreducible ⟨1, h1q⟩ ⟨0, hp_pos⟩)
  let yW : W := ⟨y, hW1leW hyW1⟩
  let xW : W := ⟨(x : G), hxW⟩
  have hyW_order : orderOf yW = q := by
    simpa [yW, Subgroup.orderOf_coe] using hy_order
  have hxW_order_dvd : orderOf xW ∣ Nat.card G := by
    exact (orderOf_dvd_natCard xW).trans (Subgroup.card_subgroup_dvd_card W)
  have hcommW : yW * xW = xW * yW := by
    ext
    simpa [yW, xW] using hcomm
  rcases theorem_13_7_virtualCharacter_congruent_at_mul_of_order_dvd
      (K := W) (p := q) (M := Nat.card G) (etaRoot := etaRoot) (eps := eps)
      heps hqprime.ne_zero hetaRoot (Nat.card_pos (α := G)).ne' hepsMem
      (χ := (ω 1 0)) hωvirt (x := yW) (y := xW) hyW_order hxW_order_dvd
      hcommW with
    ⟨hmulMem, hxMem, hcong⟩
  have hyx_eq : yW * xW = ⟨y * (x : G), hxyW⟩ := by
    ext
    rfl
  have hmulMem' : (ω 1 0) ⟨y * (x : G), hxyW⟩ ∈
      Theory.Character.cyclotomicOrder etaRoot := by
    simpa [hyx_eq] using hmulMem
  have hcong' :
      Theory.Character.CongruentModOneSub etaRoot eps
        ((ω 1 0) ⟨y * (x : G), hxyW⟩) ((ω 1 0) ⟨(x : G), hxW⟩)
        hepsMem hmulMem' hxMem := by
    simpa [Theory.Character.CongruentModOneSub, hyx_eq] using hcong
  exact ⟨hmulMem', hxMem, hcong'⟩

/- Source leaf for the post-`cycTIiso_restrict` primitive-root congruence before
rewriting the `W₂` component value to `1`. -/
private theorem theorem_13_7_omega10_yx_congruent_omega10_x_cyclicTI_source
    {G : Type u}
    [Group G]
    [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D H : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (ω : ℕ → ℕ → Section1.ClassFunction W)
    (η : ℕ → ℕ → Section1.ClassFunction G)
    (μ : ℕ → ℕ → Section1.ClassFunction Smax)
    (ν : ℕ → ℕ → Section1.ClassFunction Tmax)
    (μsum : ℕ → Section1.ClassFunction Smax)
    (νsum : ℕ → Section1.ClassFunction Tmax)
    (δ δ' : ℕ → ℤ)
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (hnotation : hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2 p q
      ω η μ ν μsum νsum δ δ' σ)
    (_hH : H = P ⊔ C)
    (x : H)
    (_hxW2 : (x : G) ∈ W2)
    (_hxne : (x : G) ≠ 1)
    (y : G)
    (hyW1 : y ∈ W1)
    (hyne : y ≠ 1)
    (hy_order : orderOf y = q)
    (hcomm : y * (x : G) = (x : G) * y)
    (hxW : (x : G) ∈ W)
    (hxyW : y * (x : G) ∈ W) :
    ∃ (etaRoot eps : ℂ),
      Nat.Prime q ∧
        IsPrimitiveRoot etaRoot (Nat.card G) ∧
        IsPrimitiveRoot eps q ∧
        ∃ hepsMem : eps ∈ Theory.Character.cyclotomicOrder etaRoot,
        ∃ hmulMem : (ω 1 0) ⟨y * (x : G), hxyW⟩ ∈
          Theory.Character.cyclotomicOrder etaRoot,
        ∃ hxMem : (ω 1 0) ⟨(x : G), hxW⟩ ∈
          Theory.Character.cyclotomicOrder etaRoot,
          Theory.Character.CongruentModOneSub etaRoot eps
            ((ω 1 0) ⟨y * (x : G), hxyW⟩) ((ω 1 0) ⟨(x : G), hxW⟩)
            hepsMem hmulMem hxMem := by
  rcases theorem_13_7_omega10_primitive_root_package_source
      Smax Tmax W W1 W2 P Q U V C D H Sfam Tfam τS τT
      ω η μ ν μsum νsum δ δ' σ p q u v c d hsource hnotation with
    ⟨etaRoot, eps, hqprime, hetaRoot, heps, hepsMem⟩
  rcases theorem_13_7_omega10_yx_congruent_omega10_x_of_root_package
      Smax Tmax W W1 W2 H ω η μ ν μsum νsum δ δ' σ p q hnotation
      x y hyW1 hyne hy_order hcomm hxW hxyW hqprime hetaRoot heps hepsMem with
    ⟨hmulMem, hxMem, hcong⟩
  exact ⟨etaRoot, eps, hqprime, hetaRoot, heps, hepsMem, hmulMem, hxMem, hcong⟩


private theorem theorem_13_7_omega10_yx_one_mod_cyclicTI_source
    {G : Type u}
    [Group G]
    [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D H : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (ω : ℕ → ℕ → Section1.ClassFunction W)
    (η : ℕ → ℕ → Section1.ClassFunction G)
    (μ : ℕ → ℕ → Section1.ClassFunction Smax)
    (ν : ℕ → ℕ → Section1.ClassFunction Tmax)
    (μsum : ℕ → Section1.ClassFunction Smax)
    (νsum : ℕ → Section1.ClassFunction Tmax)
    (δ δ' : ℕ → ℤ)
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (_hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (_hnotation : hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2 p q
      ω η μ ν μsum νsum δ δ' σ)
    (_hH : H = P ⊔ C)
    (x : H)
    (_hxW2 : (x : G) ∈ W2)
    (_hxne : (x : G) ≠ 1)
    (y : G)
    (_hyW1 : y ∈ W1)
    (_hyne : y ≠ 1)
    (_hy_order : orderOf y = q)
    (_hcomm : y * (x : G) = (x : G) * y)
    (hxyW : y * (x : G) ∈ W) :
    ∃ (etaRoot eps : ℂ),
      Nat.Prime q ∧
        IsPrimitiveRoot etaRoot (Nat.card G) ∧
        IsPrimitiveRoot eps q ∧
        ∃ hepsMem : eps ∈ Theory.Character.cyclotomicOrder etaRoot,
        ∃ homegaMem : (ω 1 0) ⟨y * (x : G), hxyW⟩ ∈
          Theory.Character.cyclotomicOrder etaRoot,
          Theory.Character.CongruentModOneSub etaRoot eps
            ((ω 1 0) ⟨y * (x : G), hxyW⟩) 1
            hepsMem homegaMem (Theory.Character.cyclotomicOrder etaRoot).one_mem := by
  rcases theorem_13_7_omega10_value_on_W2_eq_one_of_source
      Smax Tmax W W1 W2 H ω η μ ν μsum νsum δ δ' σ p q _hnotation
      x _hxW2 y _hyne _hy_order with
    ⟨hxW, hxval⟩
  rcases theorem_13_7_omega10_yx_congruent_omega10_x_cyclicTI_source
      Smax Tmax W W1 W2 P Q U V C D H Sfam Tfam τS τT
      ω η μ ν μsum νsum δ δ' σ p q u v c d _hsource _hnotation
      _hH x _hxW2 _hxne y _hyW1 _hyne _hy_order _hcomm hxW hxyW with
    ⟨etaRoot, eps, hqprime, hetaRoot, heps, hepsMem, hmulMem, hxMem, hcong⟩
  have hcongOne :
      Theory.Character.CongruentModOneSub etaRoot eps
        ((ω 1 0) ⟨y * (x : G), hxyW⟩) 1
        hepsMem hmulMem (Theory.Character.cyclotomicOrder etaRoot).one_mem := by
    simpa [Theory.Character.CongruentModOneSub, hxval] using hcong
  exact ⟨etaRoot, eps, hqprime, hetaRoot, heps, hepsMem, hmulMem, hcongOne⟩


private theorem theorem_13_7_eta10_yx_one_mod_cyclicTI_source
    {G : Type u}
    [Group G]
    [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D H : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (ω : ℕ → ℕ → Section1.ClassFunction W)
    (η : ℕ → ℕ → Section1.ClassFunction G)
    (μ : ℕ → ℕ → Section1.ClassFunction Smax)
    (ν : ℕ → ℕ → Section1.ClassFunction Tmax)
    (μsum : ℕ → Section1.ClassFunction Smax)
    (νsum : ℕ → Section1.ClassFunction Tmax)
    (δ δ' : ℕ → ℤ)
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (_hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (_hnotation : hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2 p q
      ω η μ ν μsum νsum δ δ' σ)
    (_hH : H = P ⊔ C)
    (x : H)
    (_hxW2 : (x : G) ∈ W2)
    (_hxne : (x : G) ≠ 1)
    (y : G)
    (_hyW1 : y ∈ W1)
    (_hyne : y ≠ 1)
    (_hy_order : orderOf y = q)
    (_hcomm : y * (x : G) = (x : G) * y) :
    ∃ (etaRoot eps : ℂ),
      Nat.Prime q ∧
        IsPrimitiveRoot etaRoot (Nat.card G) ∧
        IsPrimitiveRoot eps q ∧
        ∃ hepsMem : eps ∈ Theory.Character.cyclotomicOrder etaRoot,
        ∃ hmulMem : (η 1 0) (y * (x : G)) ∈ Theory.Character.cyclotomicOrder etaRoot,
          Theory.Character.CongruentModOneSub etaRoot eps ((η 1 0) (y * (x : G))) 1
            hepsMem hmulMem (Theory.Character.cyclotomicOrder etaRoot).one_mem := by
  rcases theorem_13_7_eta10_eq_omega10_on_yx_of_source
      Smax Tmax W W1 W2 P Q U V C D H Sfam Tfam τS τT
      ω η μ ν μsum νsum δ δ' σ p q u v c d _hsource _hnotation
      x _hxW2 _hxne y _hyW1 _hyne _hy_order with
    ⟨hxyW, hηω⟩
  rcases theorem_13_7_omega10_yx_one_mod_cyclicTI_source
      Smax Tmax W W1 W2 P Q U V C D H Sfam Tfam τS τT
      ω η μ ν μsum νsum δ δ' σ p q u v c d _hsource _hnotation
      _hH x _hxW2 _hxne y _hyW1 _hyne _hy_order _hcomm hxyW with
    ⟨etaRoot, eps, hqprime, hetaRoot, heps, hepsMem, homegaMem, homegaCong⟩
  have hmulMem : (η 1 0) (y * (x : G)) ∈ Theory.Character.cyclotomicOrder etaRoot := by
    simpa [hηω] using homegaMem
  have hcong :
      Theory.Character.CongruentModOneSub etaRoot eps ((η 1 0) (y * (x : G))) 1
        hepsMem hmulMem (Theory.Character.cyclotomicOrder etaRoot).one_mem := by
    simpa [hηω] using homegaCong
  exact ⟨etaRoot, eps, hqprime, hetaRoot, heps, hepsMem, hmulMem, hcong⟩

private theorem theorem_13_7_eta10_yx_one_mod_on_W2_source
    {G : Type u}
    [Group G]
    [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D H : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (ω : ℕ → ℕ → Section1.ClassFunction W)
    (η : ℕ → ℕ → Section1.ClassFunction G)
    (μ : ℕ → ℕ → Section1.ClassFunction Smax)
    (ν : ℕ → ℕ → Section1.ClassFunction Tmax)
    (μsum : ℕ → Section1.ClassFunction Smax)
    (νsum : ℕ → Section1.ClassFunction Tmax)
    (δ δ' : ℕ → ℤ)
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (hnotation : hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2 p q
      ω η μ ν μsum νsum δ δ' σ)
    (hH : H = P ⊔ C)
    (x : H)
    (hxW2 : (x : G) ∈ W2)
    (hxne : (x : G) ≠ 1) :
    ∃ (etaRoot eps : ℂ) (y : G),
      Nat.Prime q ∧
        IsPrimitiveRoot etaRoot (Nat.card G) ∧
        IsPrimitiveRoot eps q ∧
        y ∈ W1 ∧
        y ≠ 1 ∧
        orderOf y = q ∧
        y * (x : G) = (x : G) * y ∧
        ∃ hepsMem : eps ∈ Theory.Character.cyclotomicOrder etaRoot,
        ∃ hmulMem : (η 1 0) (y * (x : G)) ∈ Theory.Character.cyclotomicOrder etaRoot,
          Theory.Character.CongruentModOneSub etaRoot eps ((η 1 0) (y * (x : G))) 1
            hepsMem hmulMem (Theory.Character.cyclotomicOrder etaRoot).one_mem := by
  rcases theorem_13_7_exists_W1_order_comm_of_source
      Smax Tmax W W1 W2 P Q U V C D H Sfam Tfam τS τT
      p q u v c d hsource x hxW2 with
    ⟨y, hyW1, hyne, hy_order, hcomm⟩
  rcases theorem_13_7_eta10_yx_one_mod_cyclicTI_source
      Smax Tmax W W1 W2 P Q U V C D H Sfam Tfam τS τT
      ω η μ ν μsum νsum δ δ' σ p q u v c d hsource hnotation
      hH x hxW2 hxne y hyW1 hyne hy_order hcomm with
    ⟨etaRoot, eps, hqprime, hetaRoot, heps, hepsMem, hmulMem, hcong⟩
  exact ⟨etaRoot, eps, y, hqprime, hetaRoot, heps, hyW1, hyne, hy_order,
    hcomm, hepsMem, hmulMem, hcong⟩

private theorem theorem_13_7_eta10_one_mod_on_W2_source
    {G : Type u}
    [Group G]
    [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D H : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (ω : ℕ → ℕ → Section1.ClassFunction W)
    (η : ℕ → ℕ → Section1.ClassFunction G)
    (μ : ℕ → ℕ → Section1.ClassFunction Smax)
    (ν : ℕ → ℕ → Section1.ClassFunction Tmax)
    (μsum : ℕ → Section1.ClassFunction Smax)
    (νsum : ℕ → Section1.ClassFunction Tmax)
    (δ δ' : ℕ → ℤ)
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (hnotation : hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2 p q
      ω η μ ν μsum νsum δ δ' σ)
    (_hH : H = P ⊔ C)
    (x : H)
    (hxW2 : (x : G) ∈ W2)
    (hxne : (x : G) ≠ 1) :
    ∃ (etaRoot eps : ℂ),
      Nat.Prime q ∧
        IsPrimitiveRoot etaRoot (Nat.card G) ∧
        IsPrimitiveRoot eps q ∧
        ∃ hepsMem : eps ∈ Theory.Character.cyclotomicOrder etaRoot,
        ∃ hvalMem : (η 1 0) (x : G) ∈ Theory.Character.cyclotomicOrder etaRoot,
          Theory.Character.CongruentModOneSub etaRoot eps ((η 1 0) (x : G)) 1
            hepsMem hvalMem (Theory.Character.cyclotomicOrder etaRoot).one_mem := by
  rcases theorem_13_7_eta10_yx_one_mod_on_W2_source
      Smax Tmax W W1 W2 P Q U V C D H Sfam Tfam τS τT
      ω η μ ν μsum νsum δ δ' σ p q u v c d
      hsource hnotation _hH x hxW2 hxne with
    ⟨etaRoot, eps, y, hqprime, hetaRoot, heps, _hyW1, _hyne, hy_order, hcomm,
      hepsMem, hmulMem, hmul_one⟩
  have hvirt : Theory.Character.IsVirtualCharacter (η 1 0) :=
    theorem_13_7_eta10_virtual_of_source
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
      ω η μ ν μsum νsum δ δ' σ p q u v c d hsource hnotation
  rcases theorem_13_7_eta10_mul_congruent_of_order_comm
      (q := q) (etaRoot := etaRoot) (eps := eps)
      (eta10 := (η 1 0)) (x := (x : G)) (y := y)
      hqprime hetaRoot heps hepsMem hvirt hy_order hcomm with
    ⟨hmulMem', hxMem, hmul_x⟩
  exact ⟨etaRoot, eps, hqprime, hetaRoot, heps, hepsMem, hxMem,
    theorem_13_7_eta10_one_mod_of_mul_congruence hepsMem hmulMem' hxMem hmulMem
      hmul_x hmul_one⟩

private theorem theorem_13_7_eta10_nonzero_on_W2_source
    {G : Type u}
    [Group G]
    [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D H : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (ω : ℕ → ℕ → Section1.ClassFunction W)
    (η : ℕ → ℕ → Section1.ClassFunction G)
    (μ : ℕ → ℕ → Section1.ClassFunction Smax)
    (ν : ℕ → ℕ → Section1.ClassFunction Tmax)
    (μsum : ℕ → Section1.ClassFunction Smax)
    (νsum : ℕ → Section1.ClassFunction Tmax)
    (δ δ' : ℕ → ℤ)
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (_hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (_hnotation : hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2 p q
      ω η μ ν μsum νsum δ δ' σ)
    (_hH : H = P ⊔ C)
    (x : H)
    (hxW2 : (x : G) ∈ W2)
    (hxne : (x : G) ≠ 1) :
    (η 1 0) (x : G) ≠ 0 := by
  rcases theorem_13_7_eta10_one_mod_on_W2_source
      Smax Tmax W W1 W2 P Q U V C D H Sfam Tfam τS τT
      ω η μ ν μsum νsum δ δ' σ p q u v c d
      _hsource _hnotation _hH x hxW2 hxne with
    ⟨etaRoot, eps, hqprime, hetaRoot, heps, hepsMem, hvalMem, hcong⟩
  exact theorem_13_7_nonzero_of_congruent_one_mod_one_sub hqprime heps
    (hetaRoot.isIntegral (Nat.card_pos (α := G))) hepsMem hvalMem hcong

private theorem theorem_13_7_eta10_nonzero_value_source
    {G : Type u}
    [Group G]
    [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D H : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (ω : ℕ → ℕ → Section1.ClassFunction W)
    (η : ℕ → ℕ → Section1.ClassFunction G)
    (μ : ℕ → ℕ → Section1.ClassFunction Smax)
    (ν : ℕ → ℕ → Section1.ClassFunction Tmax)
    (μsum : ℕ → Section1.ClassFunction Smax)
    (νsum : ℕ → Section1.ClassFunction Tmax)
    (δ δ' : ℕ → ℤ)
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (hnotation : hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2 p q
      ω η μ ν μsum νsum δ δ' σ)
    (hH : H = P ⊔ C) :
    ∃ x : H, (x : G) ≠ 1 ∧ (η 1 0) (x : G) ≠ 0 := by
  rcases theorem_13_7_exists_Hsharp_mem_W2_of_source
      Smax Tmax W W1 W2 P Q U V C D H Sfam Tfam τS τT p q u v c d
      hsource hH with
    ⟨x, hxW2, hxne⟩
  exact ⟨x, hxne,
    theorem_13_7_eta10_nonzero_on_W2_source
      Smax Tmax W W1 W2 P Q U V C D H Sfam Tfam τS τT
      ω η μ ν μsum νsum δ δ' σ p q u v c d hsource hnotation hH x hxW2 hxne⟩

private theorem theorem_13_7_alpha_nonzero_value_of_eta_nonzero
    {G : Type u} [Group G] [Finite G]
    {H : Subgroup G}
    {eta10 : Section1.ClassFunction G}
    {eta10H α : Section1.ClassFunction H}
    {normDenom : ℝ}
    (hexp : ∀ x : H, (x : G) ≠ 1 →
      eta10 (x : G) =
        ((0 : ℂ) / (normDenom : ℂ)) * eta10H x + α x)
    (hη : ∃ x : H, (x : G) ≠ 1 ∧ eta10 (x : G) ≠ 0) :
    ∃ x : H, α x ≠ 0 := by
  rcases hη with ⟨x, hx_ne, hηx⟩
  refine ⟨x, ?_⟩
  intro hαx
  exact hηx (by simpa [hαx] using hexp x hx_ne)

private theorem theorem_13_7_alpha_nonzero_value_source
    {G : Type u}
    [Group G]
    [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D H : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (S1 : Finset (Section1.ClassFunction Smax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (ζ0 ζ1 : Section1.ClassFunction Smax)
    (eta10H α : Section1.ClassFunction H)
    (ω : ℕ → ℕ → Section1.ClassFunction W)
    (η : ℕ → ℕ → Section1.ClassFunction G)
    (μ : ℕ → ℕ → Section1.ClassFunction Smax)
    (ν : ℕ → ℕ → Section1.ClassFunction Tmax)
    (μsum : ℕ → Section1.ClassFunction Smax)
    (νsum : ℕ → Section1.ClassFunction Tmax)
    (δ δ' : ℕ → ℤ)
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (_hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (_hnotation : hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2 p q
      ω η μ ν μsum νsum δ δ' σ)
    (_hH : H = P ⊔ C)
    (_h5hyp : theorem_13_5_hypothesis Smax H P C S1 τS ζ0 ζ1 (η 1 0) (0 : ℂ))
    (_hres : classFunctionRestrictionData H Smax ζ1 eta10H)
    (_hα : virtualCharacterKernelConstituentData H P α)
    (_hexp : ∀ x : H, (x : G) ≠ 1 →
      (η 1 0) (x : G) =
        ((0 : ℂ) / (Section5.cfNormSq ζ1 : ℂ)) * eta10H x + α x) :
    ∃ x : H, α x ≠ 0 := by
  exact theorem_13_7_alpha_nonzero_value_of_eta_nonzero _hexp <|
    theorem_13_7_eta10_nonzero_value_source
      Smax Tmax W W1 W2 P Q U V C D H Sfam Tfam τS τT
      ω η μ ν μsum νsum δ δ' σ p q u v c d _hsource _hnotation _hH

private theorem theorem_13_7_alpha_nonzero_of_value
    {G : Type u} [Group G] [Finite G]
    {H : Subgroup G} {α : Section1.ClassFunction H}
    (hval : ∃ x : H, α x ≠ 0) :
    α ≠ 0 := by
  rintro rfl
  rcases hval with ⟨x, hx⟩
  exact hx rfl

private theorem theorem_13_7_alpha_nonzero_source
    {G : Type u}
    [Group G]
    [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D H : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (S1 : Finset (Section1.ClassFunction Smax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (ζ0 ζ1 : Section1.ClassFunction Smax)
    (eta10H α : Section1.ClassFunction H)
    (ω : ℕ → ℕ → Section1.ClassFunction W)
    (η : ℕ → ℕ → Section1.ClassFunction G)
    (μ : ℕ → ℕ → Section1.ClassFunction Smax)
    (ν : ℕ → ℕ → Section1.ClassFunction Tmax)
    (μsum : ℕ → Section1.ClassFunction Smax)
    (νsum : ℕ → Section1.ClassFunction Tmax)
    (δ δ' : ℕ → ℤ)
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (hnotation : hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2 p q
      ω η μ ν μsum νsum δ δ' σ)
    (hH : H = P ⊔ C)
    (h5hyp : theorem_13_5_hypothesis Smax H P C S1 τS ζ0 ζ1 (η 1 0) (0 : ℂ))
    (hres : classFunctionRestrictionData H Smax ζ1 eta10H)
    (hα : virtualCharacterKernelConstituentData H P α)
    (hexp : ∀ x : H, (x : G) ≠ 1 →
      (η 1 0) (x : G) =
        ((0 : ℂ) / (Section5.cfNormSq ζ1 : ℂ)) * eta10H x + α x) :
    α ≠ 0 :=
  theorem_13_7_alpha_nonzero_of_value
    (theorem_13_7_alpha_nonzero_value_source
      Smax Tmax W W1 W2 P Q U V C D H Sfam Tfam S1 τS τT ζ0 ζ1
      eta10H α ω η μ ν μsum νsum δ δ' σ p q u v c d
      hsource hnotation hH h5hyp hres hα hexp)

private theorem theorem_13_7_squareSumFormula_zero_eq_alpha_energy
    {G : Type u} [Group G] [Finite G]
    (Smax H : Subgroup G)
    (ζ1 : Section1.ClassFunction Smax)
    (eta10H α : Section1.ClassFunction H)
    (eta10 : Section1.ClassFunction G)
    (hformula : theorem_13_5_squareSumFormula Smax H ζ1 eta10H α eta10 (0 : ℂ)) :
    Section7.supportEnergy (Section7.puncturedSubgroupSet H) eta10 =
      Section7.subgroupSupportEnergy H (Section7.puncturedSubgroupSet H) α := by
  unfold theorem_13_5_squareSumFormula at hformula
  have hC :
      ((Section7.supportEnergy (Section7.puncturedSubgroupSet H) eta10 : ℝ) : ℂ) =
        ((Section7.subgroupSupportEnergy H (Section7.puncturedSubgroupSet H) α : ℝ) : ℂ) := by
    simpa using hformula
  exact Complex.ofReal_inj.mp hC

private theorem theorem_13_7_squareSumLowerBound_of_alpha_energy_lower
    {G : Type u} [Group G] [Finite G]
    (Smax H : Subgroup G)
    (ζ1 : Section1.ClassFunction Smax)
    (eta10H α : Section1.ClassFunction H)
    (eta10 : Section1.ClassFunction G)
    (hformula : theorem_13_5_squareSumFormula Smax H ζ1 eta10H α eta10 (0 : ℂ))
    (henergy : (Nat.card (Section7.puncturedSubgroupSet H) : ℝ) ≤
      Section7.subgroupSupportEnergy H (Section7.puncturedSubgroupSet H) α) :
    squareSumLowerBound (Section7.puncturedSubgroupSet H) eta10
      (Nat.card (Section7.puncturedSubgroupSet H) : ℝ) := by
  unfold squareSumLowerBound
  rw [theorem_13_7_squareSumFormula_zero_eq_alpha_energy Smax H ζ1 eta10H α eta10 hformula]
  exact henergy

private theorem theorem_13_7_P_factor_ge_one_of_source
    {G : Type u}
    [Group G]
    [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d) :
    (1 : ℝ) ≤ ((Nat.card P - 1 : ℕ) : ℝ) := by
  rcases hsource with
    ⟨_hcase, hSTypeP, _hTTypeP, _hp_card, _hq_card, _hCeq, _hD, _hc_card,
      _hd_card, _hU_card, _hV_card, _hSfam, _hTfam, _hDadeS, _hDadeT,
      _hnotation, _hDadeDiff, _hZeroDegree, _hConjIndex, _hConjBetaTau,
      _hChoice, _hMin, _hFourSixS, _hFourSixT⟩
  rcases hSTypeP with
    ⟨_hMF, _hW1cyc, _hW1ne, _hW1Hall, _hScomp, _hUleDer, _hUnil,
      _hW1norm, _hDercomp, _hMFnotcyc, _hsecond, _hfit, _hfitDer,
      hW2le, _hW2cyc, hW2ne, _hcent, _hnorm⟩
  have hW2leP : W2 ≤ P := (le_inf_iff.mp hW2le).1
  have hW2card : 1 < Nat.card W2 :=
    (Subgroup.one_lt_card_iff_ne_bot (H := W2)).2 hW2ne
  have hPcard : 2 ≤ Nat.card P := by
    have hle : Nat.card W2 ≤ Nat.card P := Subgroup.card_le_of_le hW2leP
    omega
  have hfactor : 1 ≤ Nat.card P - 1 := by
    omega
  exact_mod_cast hfactor

private theorem theorem_13_7_alpha_energy_lower_of_large_alpha_one
    {G : Type u} [Group G] [Finite G]
    (P H : Subgroup G)
    (α : Section1.ClassFunction H)
    (hlarge : (Nat.card (Section7.puncturedSubgroupSet H) : ℝ) ≤ Complex.normSq (α 1))
    (hfactor : (1 : ℝ) ≤ ((Nat.card P - 1 : ℕ) : ℝ))
    (hlower : ((Nat.card P - 1 : ℕ) : ℝ) * Complex.normSq (α 1) ≤
      Section7.subgroupSupportEnergy H (Section7.puncturedSubgroupSet H) α) :
    (Nat.card (Section7.puncturedSubgroupSet H) : ℝ) ≤
      Section7.subgroupSupportEnergy H (Section7.puncturedSubgroupSet H) α := by
  have hnonneg : 0 ≤ Complex.normSq (α 1) := Complex.normSq_nonneg (α 1)
  have hmul :
      Complex.normSq (α 1) ≤
        ((Nat.card P - 1 : ℕ) : ℝ) * Complex.normSq (α 1) := by
    simpa [one_mul] using mul_le_mul_of_nonneg_right hfactor hnonneg
  exact hlarge.trans (hmul.trans hlower)

private theorem theorem_13_7_subgroupSupportEnergy_punctured_eq_card_mul_cfNormSq_sub_one
    {G : Type u} [Group G] [Finite G]
    (H : Subgroup G)
    (α : Section1.ClassFunction H) :
    Section7.subgroupSupportEnergy H (Section7.puncturedSubgroupSet H) α =
      (Nat.card H : ℝ) * Section5.cfNormSq α - Complex.normSq (α 1) := by
  classical
  letI : Fintype H := Fintype.ofFinite H
  have henergy :
      Section7.subgroupSupportEnergy H (Section7.puncturedSubgroupSet H) α =
        ∑ x : H, if x = 1 then 0 else Complex.normSq (α x) := by
    unfold Section7.subgroupSupportEnergy
    refine Finset.sum_congr ?_ ?_
    · ext x
      simp
    · intro x _hx
      by_cases hx : x = 1
      · simp [Section7.puncturedSubgroupSet, hx]
      · have hxG : (x : G) ≠ 1 := by
          intro h
          exact hx (Subtype.ext h)
        simp [Section7.puncturedSubgroupSet, hx, hxG]
  have hsum :
      (∑ x : H, if x = 1 then 0 else Complex.normSq (α x)) =
        (∑ x : H, Complex.normSq (α x)) - Complex.normSq (α 1) := by
    calc
      (∑ x : H, if x = 1 then 0 else Complex.normSq (α x)) =
          ∑ x : H, if x ≠ 1 then Complex.normSq (α x) else 0 := by
        refine Finset.sum_congr rfl ?_
        intro x _hx
        by_cases hx : x = 1 <;> simp [hx]
      _ = ∑ x ∈ Finset.univ.filter (fun x : H => x ≠ 1), Complex.normSq (α x) := by
        exact (Finset.sum_filter (s := Finset.univ) (p := fun x : H => x ≠ 1)
          (f := fun x : H => Complex.normSq (α x))).symm
      _ = ∑ x ∈ Finset.univ.erase (1 : H), Complex.normSq (α x) := by
        congr 1
        ext x
        by_cases hx : x = 1 <;> simp [hx]
      _ = (∑ x : H, Complex.normSq (α x)) - Complex.normSq (α 1) := by
        exact Finset.sum_erase_eq_sub (s := Finset.univ)
          (f := fun x : H => Complex.normSq (α x)) (Finset.mem_univ (1 : H))
  have hcf := Section5.cfNormSq_eq_inv_card_mul_sum_normSq (G := H) α
  rw [henergy, hsum, hcf]
  have hcardNat : 0 < Nat.card H := Nat.card_pos (α := H)
  have hcard : (Nat.card H : ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt hcardNat)
  field_simp [hcard]

private theorem theorem_13_7_card_puncturedSubgroupSet_eq_sub_one
    {G : Type u} [Group G] [Finite G]
    (H : Subgroup G) :
    Nat.card (Section7.puncturedSubgroupSet H) = Nat.card H - 1 := by
  classical
  let e : {x : H // x ≠ 1} ≃ Section7.puncturedSubgroupSet H :=
    { toFun := fun x => ⟨((x : H) : G), ⟨x.1.property, by
        intro hx
        exact x.2 (Subtype.ext hx)⟩⟩
      invFun := fun x => ⟨⟨(x : G), x.property.1⟩, by
        intro hx
        exact x.property.2 (congrArg (fun y : H => (y : G)) hx)⟩
      left_inv := by
        intro x
        rfl
      right_inv := by
        intro x
        rfl }
  have hcardSubtype : Nat.card {x : H // x ≠ 1} = Nat.card H - 1 := by
    have hcompl := Fintype.card_subtype_compl (fun x : H => x = 1)
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
    convert hcompl using 1
    · simp
  exact (Nat.card_congr e.symm).trans hcardSubtype

private theorem theorem_13_7_H_isMulCommutative_of_source
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D H : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (hH : H = P ⊔ C) :
    IsMulCommutative H := by
  have h13_2 := theorem_13_2 Smax Tmax W W1 W2 P Q U V C D
    Sfam Tfam τS τT p q u v c d hsource
  rcases h13_2 with
    ⟨_hMF, _hType, _hTypeIf, hUcomm, _hFrob, hPelem, _hPcard, _huBound,
      _hcoh, _hTI, _hTau⟩
  rcases hsource with
    ⟨_hcase, _hptypeS, _hptypeT, _hp_card, _hq_card, hC, _hD, _hc_card, _hd_card,
      _hU_card, _hV_card, _hSfam, _hTfam, _hDadeS, _hDadeT, _hnotation, _hChoice,
      _hMin⟩
  letI : IsElementaryAbelian p P := hPelem
  letI : IsMulCommutative P := IsElementaryAbelian.toIsMulCommutative p
  letI : IsMulCommutative U := hUcomm
  have hCU : C ≤ U := by
    rw [hC]
    exact inf_le_left
  have hCcomm : IsMulCommutative C := by
    refine IsMulCommutative.mk <| Std.Commutative.mk <| fun x y => ?_
    apply Subtype.ext
    exact setLike_mul_comm (s := U) (hCU x.property) (hCU y.property)
  letI : IsMulCommutative C := hCcomm
  have hCcent : C ≤ Subgroup.centralizer (P : Set G) := by
    intro z hz
    rw [hC] at hz
    have hz' : z ∈ U ⊓ Subgroup.centralizer (P : Set G) := by
      simpa [subgroupCentralizerIn] using hz
    exact hz'.2
  have le_centralizer_sup :
      ∀ {R A B : Subgroup G},
        R ≤ Subgroup.centralizer (A : Set G) →
          R ≤ Subgroup.centralizer (B : Set G) →
            R ≤ Subgroup.centralizer ((A ⊔ B : Subgroup G) : Set G) := by
    intro R A B hRA hRB r hr
    rw [Subgroup.sup_eq_closure, Subgroup.centralizer_closure, Subgroup.mem_centralizer_iff]
    intro x hx
    rcases hx with hxA | hxB
    · exact Subgroup.mem_centralizer_iff.mp (hRA hr) x hxA
    · exact Subgroup.mem_centralizer_iff.mp (hRB hr) x hxB
  have hPP : P ≤ Subgroup.centralizer (P : Set G) :=
    (Subgroup.le_centralizer_iff_isMulCommutative (K := P)).2 inferInstance
  have hCC : C ≤ Subgroup.centralizer (C : Set G) :=
    (Subgroup.le_centralizer_iff_isMulCommutative (K := C)).2 inferInstance
  have hPC : P ≤ Subgroup.centralizer (C : Set G) :=
    Subgroup.le_centralizer_iff.mp hCcent
  have hHcent : H ≤ Subgroup.centralizer (H : Set G) := by
    rw [hH]
    exact sup_le (le_centralizer_sup hPP hPC) (le_centralizer_sup hCcent hCC)
  exact (Subgroup.le_centralizer_iff_isMulCommutative (K := H)).1 hHcent

private theorem theorem_13_7_alpha_one_normSq_large_of_energy_lt_from_integrality
    {H : Type u} [Group H] [Finite H] [IsMulCommutative H]
    (α : Section1.ClassFunction H)
    (hvirt : Theory.Character.IsVirtualCharacter α)
    {E : ℝ} {N : ℕ}
    (hDsum : E = (Nat.card H : ℝ) * Section5.cfNormSq α - Complex.normSq (α 1))
    (hN : N = Nat.card H - 1)
    (hα_ne_zero : α ≠ 0)
    (henergy_lt : E < (N : ℝ)) :
    (N : ℝ) ≤ Complex.normSq (α 1) := by
  have hcfNorm_nat : ∃ n : ℕ, Section5.cfNormSq α = (n : ℝ) := by
    rcases Section3.scalarProduct_isVirtualCharacter_eq_int hvirt hvirt with ⟨z, hz⟩
    have hnorm : Section5.cfNormSq α = (z : ℝ) := by
      unfold Section5.cfNormSq
      rw [hz]
      simp
    have hnonneg : 0 ≤ (z : ℝ) := by
      simpa [hnorm] using Section5.cfNormSq_nonneg α
    have hz_nonneg : 0 ≤ z := by
      exact_mod_cast hnonneg
    lift z to ℕ using hz_nonneg
    exact ⟨z, by simp [hnorm]⟩
  have hnormSq_one_nat : ∃ m : ℕ, Complex.normSq (α 1) = (m : ℝ) := by
    have hvalue_int : ∃ z : ℤ, α 1 = (z : ℂ) := by
      classical
      rcases hvirt with ⟨r, m, n, ρ, rfl⟩
      refine ⟨∑ i : Fin r, m i * (Module.finrank ℂ (Fin (n i) → ℂ) : ℤ), ?_⟩
      simp [Theory.Character.virtualCharacterOfRepresentations]
    rcases hvalue_int with ⟨z, hz⟩
    have hnorm : Complex.normSq (α 1) = (z * z : ℤ) := by
      rw [hz]
      simp [Complex.normSq]
    have hzsq_nonneg : 0 ≤ z * z := mul_self_nonneg z
    refine ⟨Int.toNat (z * z), ?_⟩
    rw [hnorm]
    have hzsq_toNat : ((Int.toNat (z * z) : ℕ) : ℤ) = z * z :=
      Int.toNat_of_nonneg hzsq_nonneg
    exact_mod_cast hzsq_toNat.symm
  have hnormSq_one_eq_one_of_cfNormSq_one :
      Section5.cfNormSq α = 1 → Complex.normSq (α 1) = 1 := by
    intro hcf
    have hself : Section1.scalarProduct H α α = 1 := by
      rcases Section3.scalarProduct_isVirtualCharacter_eq_int hvirt hvirt with ⟨z, hz⟩
      have hnorm : Section5.cfNormSq α = (z : ℝ) := by
        unfold Section5.cfNormSq
        rw [hz]
        simp
      have hz_one : z = 1 := by
        have : (z : ℝ) = 1 := by linarith
        exact_mod_cast this
      rw [hz, hz_one]
      simp
    have hsigned : Section3.IsSignedIrreducibleCharacter α :=
      Section5.signed_irreducible_of_virtual_norm_one_pf59 hvirt hself
    rcases hsigned with ⟨ε, hε, μ, hμ, rfl⟩
    have hμdeg : Section1.degree μ = 1 :=
      Section1.isIrreducibleCharacterOnGroup_degree_eq_one_of_commutative hμ
    have hμone : μ 1 = 1 := by
      simpa [Section1.degree_apply] using hμdeg
    rcases hε with rfl | rfl
    · simp [Pi.smul_apply, hμone, Complex.normSq]
    · simp [Pi.smul_apply, hμone, Complex.normSq]
  rcases hcfNorm_nat with ⟨n, hn⟩
  rcases hnormSq_one_nat with ⟨m, hm⟩
  by_contra hnot
  have hm_lt_real : (m : ℝ) < (N : ℝ) := by
    simpa [hm] using lt_of_not_ge hnot
  have hm_lt_N : m < N := by
    exact_mod_cast hm_lt_real
  have hcard_ge_one_nat : 1 ≤ Nat.card H := by
    exact Nat.succ_le_of_lt (Nat.card_pos (α := H))
  have hcard_sub_cast : ((Nat.card H - 1 : ℕ) : ℝ) = (Nat.card H : ℝ) - 1 := by
    rw [Nat.cast_sub hcard_ge_one_nat]
    norm_num
  have hm_lt_card_sub : m < Nat.card H - 1 := by
    simpa [hN] using hm_lt_N
  have henergy_ge : (N : ℝ) ≤ E := by
    cases n with
    | zero =>
        have hcf0 : Section5.cfNormSq α = 0 := by simpa using hn
        exact False.elim (hα_ne_zero (Section5.cfNormSq_eq_zero hcf0))
    | succ n' =>
        cases n' with
        | zero =>
            have hnorm_one : Complex.normSq (α 1) = 1 :=
              hnormSq_one_eq_one_of_cfNormSq_one (by simpa using hn)
            have hm_one : m = 1 := by
              have : (m : ℝ) = 1 := by linarith
              exact_mod_cast this
            rw [hN, hDsum, hn, hm, hm_one, hcard_sub_cast]
            ring_nf
            exact le_rfl
        | succ n'' =>
            have hn_ge_two_nat : 2 ≤ Nat.succ (Nat.succ n'') := by omega
            have hn_ge_two : (2 : ℝ) ≤ (Nat.succ (Nat.succ n'') : ℝ) := by
              exact_mod_cast hn_ge_two_nat
            have hm_lt_card_sub_real : (m : ℝ) < (Nat.card H : ℝ) - 1 := by
              have hcast : (m : ℝ) < ((Nat.card H - 1 : ℕ) : ℝ) := by
                exact_mod_cast hm_lt_card_sub
              rw [hcard_sub_cast] at hcast
              exact hcast
            have hcard_ge_one : (1 : ℝ) ≤ (Nat.card H : ℝ) := by
              exact_mod_cast hcard_ge_one_nat
            rw [hN, hDsum, hn, hm, hcard_sub_cast]
            nlinarith
  exact not_lt_of_ge henergy_ge henergy_lt

/- Checked post-`Dsum_alpha`/`cardsD1` integrality case split. If the
`α`-energy over `H#` were smaller than `|H#|`, then naturality of
`⟨α, α⟩`, integrality of `α 1`, and `α ≠ 0` force `|α(1)|² ≥ |H#|`. -/
private theorem theorem_13_7_alpha_one_normSq_large_of_energy_lt_from_norm_formula_source
    {G : Type u}
    [Group G]
    [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D H : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (S1 : Finset (Section1.ClassFunction Smax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (ζ0 ζ1 : Section1.ClassFunction Smax)
    (eta10H α : Section1.ClassFunction H)
    (ω : ℕ → ℕ → Section1.ClassFunction W)
    (η : ℕ → ℕ → Section1.ClassFunction G)
    (μ : ℕ → ℕ → Section1.ClassFunction Smax)
    (ν : ℕ → ℕ → Section1.ClassFunction Tmax)
    (μsum : ℕ → Section1.ClassFunction Smax)
    (νsum : ℕ → Section1.ClassFunction Tmax)
    (δ δ' : ℕ → ℤ)
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (_hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (_hnotation : hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2 p q
      ω η μ ν μsum νsum δ δ' σ)
    (_hH : H = P ⊔ C)
    (_h5hyp : theorem_13_5_hypothesis Smax H P C S1 τS ζ0 ζ1 (η 1 0) (0 : ℂ))
    (_hres : classFunctionRestrictionData H Smax ζ1 eta10H)
    (_hα : virtualCharacterKernelConstituentData H P α)
    (_hexp : ∀ x : H, (x : G) ≠ 1 →
      (η 1 0) (x : G) =
        ((0 : ℂ) / (Section5.cfNormSq ζ1 : ℂ)) * eta10H x + α x)
    (_hDsum : Section7.subgroupSupportEnergy H (Section7.puncturedSubgroupSet H) α =
      (Nat.card H : ℝ) * Section5.cfNormSq α - Complex.normSq (α 1))
    (_hHsharp_card : Nat.card (Section7.puncturedSubgroupSet H) = Nat.card H - 1)
    (_hα_ne_zero : α ≠ 0)
    (_henergy_lt : Section7.subgroupSupportEnergy H (Section7.puncturedSubgroupSet H) α <
      (Nat.card (Section7.puncturedSubgroupSet H) : ℝ)) :
    (Nat.card (Section7.puncturedSubgroupSet H) : ℝ) ≤ Complex.normSq (α 1) := by
  letI : IsMulCommutative H :=
    theorem_13_7_H_isMulCommutative_of_source
      Smax Tmax W W1 W2 P Q U V C D H Sfam Tfam τS τT p q u v c d
      _hsource _hH
  exact theorem_13_7_alpha_one_normSq_large_of_energy_lt_from_integrality α _hα.1
    _hDsum _hHsharp_card _hα_ne_zero _henergy_lt

/- Checked wrapper over the generic `Dsum_alpha` formula and the `cardsD1`
cardinality formula. -/
private theorem theorem_13_7_alpha_one_normSq_large_of_energy_lt_source
    {G : Type u}
    [Group G]
    [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D H : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (S1 : Finset (Section1.ClassFunction Smax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (ζ0 ζ1 : Section1.ClassFunction Smax)
    (eta10H α : Section1.ClassFunction H)
    (ω : ℕ → ℕ → Section1.ClassFunction W)
    (η : ℕ → ℕ → Section1.ClassFunction G)
    (μ : ℕ → ℕ → Section1.ClassFunction Smax)
    (ν : ℕ → ℕ → Section1.ClassFunction Tmax)
    (μsum : ℕ → Section1.ClassFunction Smax)
    (νsum : ℕ → Section1.ClassFunction Tmax)
    (δ δ' : ℕ → ℤ)
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (hnotation : hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2 p q
      ω η μ ν μsum νsum δ δ' σ)
    (hH : H = P ⊔ C)
    (h5hyp : theorem_13_5_hypothesis Smax H P C S1 τS ζ0 ζ1 (η 1 0) (0 : ℂ))
    (hres : classFunctionRestrictionData H Smax ζ1 eta10H)
    (hα : virtualCharacterKernelConstituentData H P α)
    (hexp : ∀ x : H, (x : G) ≠ 1 →
      (η 1 0) (x : G) =
        ((0 : ℂ) / (Section5.cfNormSq ζ1 : ℂ)) * eta10H x + α x)
    (hα_ne_zero : α ≠ 0)
    (henergy_lt : Section7.subgroupSupportEnergy H (Section7.puncturedSubgroupSet H) α <
      (Nat.card (Section7.puncturedSubgroupSet H) : ℝ)) :
    (Nat.card (Section7.puncturedSubgroupSet H) : ℝ) ≤ Complex.normSq (α 1) := by
  have hDsum :
      Section7.subgroupSupportEnergy H (Section7.puncturedSubgroupSet H) α =
        (Nat.card H : ℝ) * Section5.cfNormSq α - Complex.normSq (α 1) :=
    theorem_13_7_subgroupSupportEnergy_punctured_eq_card_mul_cfNormSq_sub_one H α
  have hHsharp_card :
      Nat.card (Section7.puncturedSubgroupSet H) = Nat.card H - 1 :=
    theorem_13_7_card_puncturedSubgroupSet_eq_sub_one H
  exact theorem_13_7_alpha_one_normSq_large_of_energy_lt_from_norm_formula_source
    Smax Tmax W W1 W2 P Q U V C D H Sfam Tfam S1 τS τT ζ0 ζ1
    eta10H α ω η μ ν μsum νsum δ δ' σ p q u v c d
    hsource hnotation hH h5hyp hres hα hexp hDsum hHsharp_card hα_ne_zero henergy_lt

/- Source leaf for PF `(13.7)`: after the `(13.5)` expansion, `η₁₀ = α` on
`H#`; using the nonzero congruence above and the abelian structure of `H`,
the norm-one and norm-at-least-two cases give the lower bound for the
`α`-energy. -/
private theorem theorem_13_7_alpha_energy_lower_source
    {G : Type u}
    [Group G]
    [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D H : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (S1 : Finset (Section1.ClassFunction Smax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (ζ0 ζ1 : Section1.ClassFunction Smax)
    (eta10H α : Section1.ClassFunction H)
    (ω : ℕ → ℕ → Section1.ClassFunction W)
    (η : ℕ → ℕ → Section1.ClassFunction G)
    (μ : ℕ → ℕ → Section1.ClassFunction Smax)
    (ν : ℕ → ℕ → Section1.ClassFunction Tmax)
    (μsum : ℕ → Section1.ClassFunction Smax)
    (νsum : ℕ → Section1.ClassFunction Tmax)
    (δ δ' : ℕ → ℤ)
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (_hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (_hnotation : hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2 p q
      ω η μ ν μsum νsum δ δ' σ)
    (_hH : H = P ⊔ C)
    (_h5hyp : theorem_13_5_hypothesis Smax H P C S1 τS ζ0 ζ1 (η 1 0) (0 : ℂ))
    (_hres : classFunctionRestrictionData H Smax ζ1 eta10H)
    (_hα : virtualCharacterKernelConstituentData H P α)
    (_hexp : ∀ x : H, (x : G) ≠ 1 →
      (η 1 0) (x : G) =
        ((0 : ℂ) / (Section5.cfNormSq ζ1 : ℂ)) * eta10H x + α x)
    (_hlower : ((Nat.card P - 1 : ℕ) : ℝ) * Complex.normSq (α 1) ≤
      Section7.subgroupSupportEnergy H (Section7.puncturedSubgroupSet H) α)
    (hα_ne_zero : α ≠ 0) :
    (Nat.card (Section7.puncturedSubgroupSet H) : ℝ) ≤
      Section7.subgroupSupportEnergy H (Section7.puncturedSubgroupSet H) α := by
  by_contra hnot
  have henergy_lt :
      Section7.subgroupSupportEnergy H (Section7.puncturedSubgroupSet H) α <
        (Nat.card (Section7.puncturedSubgroupSet H) : ℝ) :=
    lt_of_not_ge hnot
  have hlarge :
      (Nat.card (Section7.puncturedSubgroupSet H) : ℝ) ≤ Complex.normSq (α 1) :=
    theorem_13_7_alpha_one_normSq_large_of_energy_lt_source
      Smax Tmax W W1 W2 P Q U V C D H Sfam Tfam S1 τS τT ζ0 ζ1
      eta10H α ω η μ ν μsum νsum δ δ' σ p q u v c d
      _hsource _hnotation _hH _h5hyp _hres _hα _hexp hα_ne_zero henergy_lt
  have hfactor : (1 : ℝ) ≤ ((Nat.card P - 1 : ℕ) : ℝ) :=
    theorem_13_7_P_factor_ge_one_of_source
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
      p q u v c d _hsource
  have henergy_ge :
      (Nat.card (Section7.puncturedSubgroupSet H) : ℝ) ≤
        Section7.subgroupSupportEnergy H (Section7.puncturedSubgroupSet H) α :=
    theorem_13_7_alpha_energy_lower_of_large_alpha_one P H α hlarge hfactor _hlower
  exact hnot henergy_ge

/- Source leaf for PF `(13.7)`: after the `(13.5)` expansion, `η₁₀ = α` on
`H#`; the remaining source content is isolated in
`theorem_13_7_alpha_energy_lower_source`, and the `a = 0` square-sum formula
transfers that lower bound back to `η₁₀`. -/
private theorem theorem_13_7_alpha_norm_lower_source
    {G : Type u}
    [Group G]
    [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D H : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (S1 : Finset (Section1.ClassFunction Smax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (ζ0 ζ1 : Section1.ClassFunction Smax)
    (eta10H α : Section1.ClassFunction H)
    (ω : ℕ → ℕ → Section1.ClassFunction W)
    (η : ℕ → ℕ → Section1.ClassFunction G)
    (μ : ℕ → ℕ → Section1.ClassFunction Smax)
    (ν : ℕ → ℕ → Section1.ClassFunction Tmax)
    (μsum : ℕ → Section1.ClassFunction Smax)
    (νsum : ℕ → Section1.ClassFunction Tmax)
    (δ δ' : ℕ → ℤ)
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (_hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (_hnotation : hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2 p q
      ω η μ ν μsum νsum δ δ' σ)
    (_hH : H = P ⊔ C)
    (_h5hyp : theorem_13_5_hypothesis Smax H P C S1 τS ζ0 ζ1 (η 1 0) (0 : ℂ))
    (_hres : classFunctionRestrictionData H Smax ζ1 eta10H)
    (_hα : virtualCharacterKernelConstituentData H P α)
    (_hexp : ∀ x : H, (x : G) ≠ 1 →
      (η 1 0) (x : G) =
        ((0 : ℂ) / (Section5.cfNormSq ζ1 : ℂ)) * eta10H x + α x)
    (hformula : theorem_13_5_squareSumFormula Smax H ζ1 eta10H α (η 1 0) (0 : ℂ))
    (hlower : ((Nat.card P - 1 : ℕ) : ℝ) * Complex.normSq (α 1) ≤
      Section7.subgroupSupportEnergy H (Section7.puncturedSubgroupSet H) α)
    (hα_ne_zero : α ≠ 0) :
    squareSumLowerBound (Section7.puncturedSubgroupSet H) (η 1 0)
      (Nat.card (Section7.puncturedSubgroupSet H) : ℝ) := by
  have henergy :
      (Nat.card (Section7.puncturedSubgroupSet H) : ℝ) ≤
        Section7.subgroupSupportEnergy H (Section7.puncturedSubgroupSet H) α :=
    theorem_13_7_alpha_energy_lower_source
      Smax Tmax W W1 W2 P Q U V C D H Sfam Tfam S1 τS τT ζ0 ζ1
      eta10H α ω η μ ν μsum νsum δ δ' σ p q u v c d
      _hsource _hnotation _hH _h5hyp _hres _hα _hexp hlower hα_ne_zero
  exact theorem_13_7_squareSumLowerBound_of_alpha_energy_lower
    Smax H ζ1 eta10H α (η 1 0) hformula henergy

public theorem theorem_13_7
    {G : Type u}
    [Group G]
    [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D H : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (ω : ℕ → ℕ → Section1.ClassFunction W)
    (η : ℕ → ℕ → Section1.ClassFunction G)
    (μ : ℕ → ℕ → Section1.ClassFunction Smax)
    (ν : ℕ → ℕ → Section1.ClassFunction Tmax)
    (μsum : ℕ → Section1.ClassFunction Smax)
    (νsum : ℕ → Section1.ClassFunction Tmax)
    (δ δ' : ℕ → ℤ)
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
        Sfam Tfam τS τT p q u v c d →
      hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2 p q
        ω η μ ν μsum νsum δ δ' σ →
        H = P ⊔ C →
          squareSumLowerBound (Section7.puncturedSubgroupSet H) (η 1 0)
            (Nat.card (Section7.puncturedSubgroupSet H) : ℝ) := by
  intro hsource hnotation hH
  rcases theorem_13_7_theorem_13_5_input_source
      Smax Tmax W W1 W2 P Q U V C D H Sfam Tfam τS τT
      ω η μ ν μsum νsum δ δ' σ p q u v c d hsource hnotation hH with
    ⟨S1, ζ0, ζ1, eta10H, h5hyp, hres⟩
  rcases theorem_13_5 Smax Tmax W W1 W2 P Q U V C D H
      Sfam Tfam S1 τS τT ζ0 ζ1 eta10H (η 1 0) (0 : ℂ)
      p q u v c d hsource h5hyp hres with
    ⟨α, hα, hexp, hformula, hlower⟩
  have hα_ne_zero : α ≠ 0 :=
    theorem_13_7_alpha_nonzero_source
      Smax Tmax W W1 W2 P Q U V C D H Sfam Tfam S1 τS τT ζ0 ζ1
      eta10H α ω η μ ν μsum νsum δ δ' σ p q u v c d
      hsource hnotation hH h5hyp hres hα hexp
  exact theorem_13_7_alpha_norm_lower_source
    Smax Tmax W W1 W2 P Q U V C D H Sfam Tfam S1 τS τT ζ0 ζ1
    eta10H α ω η μ ν μsum νsum δ δ' σ p q u v c d
    hsource hnotation hH h5hyp hres hα hexp hformula hlower hα_ne_zero
end CFSG.Section13
