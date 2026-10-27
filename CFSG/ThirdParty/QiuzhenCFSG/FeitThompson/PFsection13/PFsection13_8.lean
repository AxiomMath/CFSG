module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection13.PFsection13_7
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection8.PFsection8_5_a

namespace CFSG
end CFSG
open CFSG

/-!
# Peterfalvi, Section 13: PFsection13_8
-/

noncomputable section

open scoped BigOperators Pointwise

attribute [local instance] Fintype.ofFinite

namespace CFSG.Section13

universe v
universe u

/-! ## (13.8) -/


private theorem theorem_13_8_scalarProduct_finset_sum_left
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

private theorem theorem_13_8_scalarProduct_finset_sum_right
    {G : Type u} [Group G] [Finite G]
    {ι : Type*} [DecidableEq ι]
    (E : Finset ι) (φ : ι → Section1.ClassFunction G)
    (ψ : Section1.ClassFunction G) :
    Section1.scalarProduct G ψ (E.sum φ) =
      E.sum (fun i => Section1.scalarProduct G ψ (φ i)) := by
  classical
  induction E using Finset.induction with
  | empty =>
      simp [Section1.scalarProduct]
  | insert a E ha ih =>
      simp [Finset.sum_insert ha, Section5.scalarProduct_add_right, ih]

private theorem theorem_13_8_scalarProduct_neg_left
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

private theorem theorem_13_8_eta_orthonormal_of_notation
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
      _hμzero_nonprincipal, _hνzero_nonprincipal, _hμeq, _hνeq, _hμsum,
      _hνsum⟩
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

private theorem theorem_13_8_eta_row_sum_scalarProduct_eta01_of_notation
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax W W1 W2 : Subgroup G)
    (p q k : ℕ)
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
    (h0q : 0 < q) (hkp : k < p) (h1p : 1 < p) :
    Section1.scalarProduct G ((Finset.range q).sum (fun i => η i k)) (η 0 1) =
      if k = 1 then 1 else 0 := by
  rw [theorem_13_8_scalarProduct_finset_sum_left]
  by_cases hk1 : k = 1
  · subst hk1
    have hsum0 :
        (Finset.range q).sum (fun i =>
          Section1.scalarProduct G (η i 1) (η 0 1)) =
          Section1.scalarProduct G (η 0 1) (η 0 1) := by
      apply Finset.sum_eq_single 0
      · intro i hi hi_ne
        have hiq : i < q := Finset.mem_range.mp hi
        have horth :=
          theorem_13_8_eta_orthonormal_of_notation
            Smax Tmax W W1 W2 p q ω η μ ν μsum νsum δ δ' σ
            hnotation i 1 0 1 hiq h1p h0q h1p
        have hi_ne0 : i ≠ 0 := hi_ne
        simpa [hi_ne0] using horth
      · intro hnotmem
        exact (hnotmem (Finset.mem_range.mpr h0q)).elim
    have hself : Section1.scalarProduct G (η 0 1) (η 0 1) = 1 := by
      have horth :=
        theorem_13_8_eta_orthonormal_of_notation
          Smax Tmax W W1 W2 p q ω η μ ν μsum νsum δ δ' σ
          hnotation 0 1 0 1 h0q h1p h0q h1p
      simpa using horth
    rw [hsum0, hself]
    simp
  · have hsum :
        (Finset.range q).sum (fun i =>
          Section1.scalarProduct G (η i k) (η 0 1)) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      have hiq : i < q := Finset.mem_range.mp hi
      have horth :=
        theorem_13_8_eta_orthonormal_of_notation
          Smax Tmax W W1 W2 p q ω η μ ν μsum νsum δ δ' σ
          hnotation i k 0 1 hiq hkp h0q h1p
      have hpair : ¬ (i = 0 ∧ k = 1) := by
        intro h
        exact hk1 h.2
      simpa [hpair] using horth
    simpa [hk1] using hsum

private theorem theorem_13_8_map_evalCoeff
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

private theorem theorem_13_8_scalarProduct_evalCoeff_left_zero
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

private theorem theorem_13_8_integerSpan_orthogonal_of_generators
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
  rw [hζeq, theorem_13_8_map_evalCoeff T (fun X : S =>
    (X : Section1.ClassFunction L)) v]
  apply theorem_13_8_scalarProduct_evalCoeff_left_zero
  intro X
  exact hgen (X : Section1.ClassFunction L) X.property

private theorem theorem_13_8_coherentFamily_of_source
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

private theorem theorem_13_8_eta01_orthogonal_irreducible_generators_source
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
        Section1.scalarProduct G (τ1 φ) (η 0 1) = 0 := by
  have hcoh : Section6.coherentFamily Sfam τS :=
    theorem_13_8_coherentFamily_of_source
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT p q u v c d hsource
  rcases hsource with
    ⟨hcaseB, hTypeP, _hTypePT, hp_card, hq_card, _hC, _hD, _hc_card,
      _hd_card, _hU_card, _hV_card, hSfam, _hTfam, _hDadeS, _hDadeT,
      _hnotationData, _hDadeDiff, _hZeroDegree, _hConjIndex, _hConjBetaTau,
      _hChoice, hMin, hFourSixS, _hFourSixT⟩
  rcases hcaseB with
    ⟨_hWprod, _hWcyc, _hW1ne, hW2ne, _hWhat, _hSmax, _hTmax, _hSMF,
      _hTMF, _hSeq, _hTeq, _hSdisj, _hTdisj, _hST, _hII, _hStype,
      _hTtype, _hclass⟩
  letI : IsMinCE G := hMin
  have h0q : 0 < q := by
    simpa [hq_card] using (Nat.card_pos (α := W1))
  have h1p : 1 < p := by
    have hW2card : 1 < Nat.card W2 :=
      (Subgroup.one_lt_card_iff_ne_bot (H := W2)).2 hW2ne
    simpa [hp_card] using hW2card
  intro φ hφS hφIrr
  exact section13_typeP_coherentExtension_orthogonal_cyclicTIiso_source
    Smax Tmax W W1 W2 P U Sfam τS τ1 ω η μ ν μsum νsum δ δ' σ p q
    hTypeP hFourSixS hSfam hcoh hcohExt hnotation φ hφS hφIrr 0 1 h0q h1p

/- Checked notation glue: `η 0 1` is a virtual character, because it is the
PF `(3.2)` image of the finite Section `(3.3)` table entry `(0,1)`. -/
private theorem theorem_13_8_eta01_virtual_of_source
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
    Theory.Character.IsVirtualCharacter (η 0 1) := by
  rcases hsource with
    ⟨hcaseB, _hptypeS, _hptypeT, hp_card, hq_card, _htail⟩
  rcases hcaseB with
    ⟨_hWprod, _hWcyc, _hW1ne, hW2ne, _hWhat, _hSmax, _hTmax, _hSMF,
      _hTMF, _hSeq, _hTeq, _hSdisj, _hTdisj, _hST, _hII, _hStype,
      _hTtype, _hclass⟩
  rcases hnotation with
    ⟨homegaData, hσmap, hη, _hδ, _hδ', _hμirr, _hνirr,
      _hμzero_nonprincipal, _hνzero_nonprincipal, _hμeq, _hνeq, _hμsum,
      _hνsum⟩
  rcases homegaData with ⟨_h31, _hqpos, _hppos, ωFin, hωFin, hωNat⟩
  have h0q : 0 < q := by
    simpa [hq_card] using (Nat.card_pos (α := W1))
  have h1p : 1 < p := by
    have hW2card : 1 < Nat.card W2 :=
      (Subgroup.one_lt_card_iff_ne_bot (H := W2)).2 hW2ne
    simpa [hp_card] using hW2card
  let i0 : Fin q := ⟨0, h0q⟩
  let j1 : Fin p := ⟨1, h1p⟩
  have hη01 : η 0 1 = σ (ωFin i0 j1) := by
    rw [hη 0 1 h0q h1p, hωNat 0 1 h0q h1p]
  have hωvirt : Theory.Character.IsVirtualCharacter (ωFin i0 j1) :=
    Section3.isVirtualCharacter_of_irreducibleCharacterOnGroup (hωFin.irreducible i0 j1)
  rw [hη01]
  exact hσmap.2.1 (ωFin i0 j1) hωvirt


private def theorem_13_8_eta01RowChoiceData
    {G : Type u}
    [Group G]
    [Finite G]
    (Smax : Subgroup G)
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (η : ℕ → ℕ → Section1.ClassFunction G)
    (μsum : ℕ → Section1.ClassFunction Smax)
    (p : ℕ)
    (j1 : ℕ)
    (a : ℂ) : Prop :=
  0 < j1 ∧
    j1 < p ∧
    ∀ j : ℕ, 0 < j → j < p →
      Section1.scalarProduct G (τS (μsum j)) (η 0 1) =
        if j = j1 then a else 0


private theorem theorem_13_8_eta01_row_index_source
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
    (_hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (_hnotation : hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2 p q
      ω η μ ν μsum νsum δ δ' σ) :
    ∃ (τ1 : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
      (j1 : ℕ) (a : ℂ),
        Section6.coherentExtension Sfam τS τ1 ∧
          theorem_13_8_eta01RowChoiceData Smax τ1 η μsum p j1 a ∧
            (a = 1 ∨ a = -1) := by
  classical
  have h13_3 := (theorem_13_3 Smax Tmax W W1 W2 P Q U V C D
    Sfam Tfam τS τT p q u v c d _hsource).1
  rcases (h13_3 ω η μ ν μsum νsum δ δ' σ _hnotation).2 with
    ⟨τ1, hcoh, houtput⟩
  have h0q : 0 < q := by
    rcases _hsource with
      ⟨_hcaseB, _hptypeS, _hptypeT, _hp_card, hq_card, _htail⟩
    simpa [hq_card] using (Nat.card_pos (α := W1))
  have h1p : 1 < p := by
    rcases _hsource with
      ⟨hcaseB, _hptypeS, _hptypeT, hp_card, _hq_card, _htail⟩
    rcases hcaseB with
      ⟨_hWprod, _hWcyc, _hW1ne, hW2ne, _hWhat, _hSmax, _hTmax, _hSMF,
        _hTMF, _hSeq, _hTeq, _hSdisj, _hTdisj, _hST, _hII, _hStype,
        _hTtype, _hclass⟩
    have hW2card : 1 < Nat.card W2 :=
      (Subgroup.one_lt_card_iff_ne_bot (H := W2)).2 hW2ne
    simpa [hp_card] using hW2card
  rcases houtput with ⟨_hchars, hsign⟩
  rcases hsign with hpos | hneg
  · refine ⟨τ1, 1, 1, hcoh, ⟨by norm_num, h1p, ?_⟩, Or.inl rfl⟩
    intro j hj0 hjp
    change Section1.scalarProduct G ((fun j => τ1 (μsum j)) j) (η 0 1) =
      if j = 1 then (1 : ℂ) else 0
    rw [hpos j hj0 hjp]
    exact theorem_13_8_eta_row_sum_scalarProduct_eta01_of_notation
      Smax Tmax W W1 W2 p q j ω η μ ν μsum νsum δ δ' σ _hnotation h0q hjp h1p
  · rcases hneg with ⟨hp3, hrow⟩
    have h2p : 2 < p := by omega
    refine ⟨τ1, 2, -1, hcoh, ⟨by norm_num, h2p, ?_⟩, Or.inr rfl⟩
    intro j hj0 hjp
    rcases hrow j hj0 hjp with ⟨j', hset, hrowj⟩
    change Section1.scalarProduct G ((fun j => τ1 (μsum j)) j) (η 0 1) =
      if j = 2 then (-1 : ℂ) else 0
    rw [hrowj, theorem_13_8_scalarProduct_neg_left]
    have hj_cases : j = 1 ∨ j = 2 := by omega
    rcases hj_cases with hj1 | hj2
    · have hj'2 : j' = 2 := by
        have h2mem : 2 ∈ ({j, j'} : Finset ℕ) := by
          rw [hset]
          simp
        have h2eq : 2 = j' := by
          simpa [hj1] using h2mem
        exact h2eq.symm
      have hsum :=
        theorem_13_8_eta_row_sum_scalarProduct_eta01_of_notation
          Smax Tmax W W1 W2 p q j' ω η μ ν μsum νsum δ δ' σ
          _hnotation h0q (by simpa [hj'2] using h2p) h1p
      simp [hj1, hj'2] at hsum ⊢
      exact hsum
    · have hj'1 : j' = 1 := by
        have h1mem : 1 ∈ ({j, j'} : Finset ℕ) := by
          rw [hset]
          simp
        have h1eq : 1 = j' := by
          simpa [hj2] using h1mem
        exact h1eq.symm
      have hsum :=
        theorem_13_8_eta_row_sum_scalarProduct_eta01_of_notation
          Smax Tmax W W1 W2 p q j' ω η μ ν μsum νsum δ δ' σ
          _hnotation h0q (by simpa [hj'1] using h1p) h1p
      simp [hj2, hj'1] at hsum ⊢
      exact hsum

/- Checked `calS1` witness construction from a nonzero row of the PF `(13.3)`
character output. -/
private theorem theorem_13_8_calS1_witness_of_row_index
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
    (j1 : ℕ)
    (hj1_pos : 0 < j1)
    (hj1_lt : j1 < p) :
    ∃ S1 : Finset (Section1.ClassFunction Smax),
      H = P ⊔ C ∧
        nonkernelInducedFamily Smax H P S1 ∧
        Section1.conjugateCharacter (μsum j1) ∈ S1 ∧
        μsum j1 ∈ S1 ∧
        Section1.conjugateCharacter (μsum j1) ≠ μsum j1 := by
  have hsourceFull := hsource
  have h13_3 := (theorem_13_3 Smax Tmax W W1 W2 P Q U V C D
    Sfam Tfam τS τT p q u v c d hsource).1
  rcases (h13_3 ω η μ ν μsum νsum δ δ' σ hnotation).2 with
    ⟨_τ1, _hcoh, houtput⟩
  have hμdata := houtput.1 j1 hj1_pos hj1_lt
  rcases hμdata with ⟨_hμchar, _hμdeg, hμlinearPC, hμSfam⟩
  have hμlinearH : inducedFromLinearCharacterForSection13 Smax H (μsum j1) := by
    simpa [hH] using hμlinearPC
  have hHS : H ≤ Smax := hμlinearH.1
  have hPH : P ≤ H := by
    rw [hH]
    exact le_sup_left
  rcases theorem_13_6_exists_nonkernelInducedFamily Smax H P hHS hPH with
    ⟨S1, hS1⟩
  rcases theorem_13_6_lambda_inducedFromNonkernel_H_source
      Smax Tmax W W1 W2 P Q U V C D H Sfam Tfam τS τT
      (μsum j1) (τS (μsum j1)) p q u v c d hsourceFull hμSfam hH hμlinearH with
    ⟨θH, hθHirr, hθHnotker, hμind⟩
  have hμS1 : μsum j1 ∈ S1 :=
    (hS1.2.2 (μsum j1)).2 ⟨θH, hθHirr, hθHnotker, hμind⟩
  rcases hsource with
    ⟨_hcaseB, hSTypeP, _hTTypeP, _hp_card, _hq_card, hC,
      _hD, _hc_card, _hd_card, _hU_card, _hV_card, _hSfam, _hTfam,
      _hDadeS, _hDadeT, _hnotationData, _hDadeDiff, _hZeroDegree,
      _hConjIndex, _hConjBetaTau, _hChoice,
      hMin, _hFourSixS, _hFourSixT⟩
  have hfit : section8FittingSubgroup Smax = P ⊔ C := by
    simpa [hC] using Section8.theorem_8_5_a Smax P U W1 W2 hSTypeP
  have hHnormal : (H.subgroupOf Smax).Normal := by
    have hPCnormal : ((P ⊔ C).subgroupOf Smax).Normal := by
      simpa [hfit] using section8FittingSubgroup_normal_in Smax
    simpa [hH] using hPCnormal
  letI : IsMinCE G := hMin
  have hoddSmax : Odd (Nat.card Smax) :=
    section13_odd_card_subgroup_of_odd_group Smax IsMinCE.odd_order
  have hμne : μsum j1 ≠ Section1.conjugateCharacter (μsum j1) :=
    section13_nonkernelInducedFamily_ne_conjugate
      Smax H P S1 hHnormal hoddSmax hS1 (μsum j1) hμS1
  refine ⟨S1, hH, hS1, ?_, hμS1, ?_⟩
  · exact theorem_13_6_nonkernelInducedFamily_conjugate_mem Smax H P S1 hS1 hμS1
  · exact hμne.symm


private theorem theorem_13_8_calS1_orthogonality_source
    {G : Type u}
    [Group G]
    [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D H : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (S1 : Finset (Section1.ClassFunction Smax))
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
    (_hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (_hnotation : hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2 p q
      ω η μ ν μsum νsum δ δ' σ)
    (_hH : H = P ⊔ C)
    (j1 : ℕ)
    (a : ℂ)
    (hcoh : Section6.coherentExtension Sfam τS τ1)
    (hchoice : theorem_13_8_eta01RowChoiceData Smax τ1 η μsum p j1 a)
    (hS1 : nonkernelInducedFamily Smax H P S1)
    (hζ0 : Section1.conjugateCharacter (μsum j1) ∈ S1)
    (_hζ1 : μsum j1 ∈ S1)
    (hζ_ne : Section1.conjugateCharacter (μsum j1) ≠ μsum j1) :
    a = Section1.scalarProduct G
        (τS (μsum j1 - Section1.conjugateCharacter (μsum j1))) (η 0 1) ∧
      ∀ ζ : Section1.ClassFunction Smax, ζ ∈ S1 →
        ζ ≠ Section1.conjugateCharacter (μsum j1) → ζ ≠ μsum j1 →
        Section1.scalarProduct G
          (τS (ζ - Section1.conjugateCharacter (μsum j1))) (η 0 1) = 0 := by
  classical
  rcases hchoice with ⟨hj1_pos, hj1_lt, hrowScalar⟩
  have h13_3 := (theorem_13_3 Smax Tmax W W1 W2 P Q U V C D
    Sfam Tfam τS τT p q u v c d _hsource).1
  rcases (h13_3 ω η μ ν μsum νsum δ δ' σ _hnotation).2 with
    ⟨_τ2, _hcoh2, houtput⟩
  have hgenAll := theorem_13_8_eta01_orthogonal_irreducible_generators_source
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τ1 τT
      ω η μ ν μsum νsum δ δ' σ p q u v c d _hsource _hnotation hcoh
  have hspanOrth :
      ∀ ζ : Section1.ClassFunction Smax,
        Section5.integerSpan (section13_irreducibleSubfamily Smax Sfam) ζ →
          Section1.scalarProduct G (τ1 ζ) (η 0 1) = 0 := by
    intro ζ hζspan
    exact theorem_13_8_integerSpan_orthogonal_of_generators
      (section13_irreducibleSubfamily Smax Sfam) τ1 (η 0 1) hζspan (by
        intro φ hφ
        change φ ∈
          Sfam.filter (fun φ => Section1.IsIrreducibleCharacterOnGroup φ) at hφ
        have hφdata : φ ∈ Sfam ∧ Section1.IsIrreducibleCharacterOnGroup φ :=
          Finset.mem_filter.mp hφ
        exact hgenAll φ hφdata.1 hφdata.2)
  have horth_except :
      ∀ ζ : Section1.ClassFunction Smax, ζ ∈ S1 → ζ ≠ μsum j1 →
        Section1.scalarProduct G (τ1 ζ) (η 0 1) = 0 := by
    intro ζ hζ hζ_ne_row
    rcases section13_calS1_cases_or_integerSpan_source
        Smax Tmax W W1 W2 P Q U V C D H Sfam Tfam τS τT
        ω η μ ν μsum νsum δ δ' σ p q u v c d
        _hsource _hnotation _hH S1 hS1 ζ hζ with hrow | hspan
    · rcases hrow with ⟨j, hj0, hjp, rfl⟩
      by_cases hj : j = j1
      · exact False.elim (hζ_ne_row (by rw [hj]))
      · have hscalar := hrowScalar j hj0 hjp
        simpa [hj] using hscalar
    · exact hspanOrth ζ hspan
  have hζ1scalar : Section1.scalarProduct G (τ1 (μsum j1)) (η 0 1) = a := by
    have hscalar := hrowScalar j1 hj1_pos hj1_lt
    simpa using hscalar
  have hζ0scalar :
      Section1.scalarProduct G (τ1 (Section1.conjugateCharacter (μsum j1))) (η 0 1) = 0 :=
    horth_except (Section1.conjugateCharacter (μsum j1)) hζ0 hζ_ne
  have hS1Span : ∀ ζ : Section1.ClassFunction Smax, ζ ∈ S1 →
      Section5.integerSpan Sfam ζ := by
    intro ζ hζ
    rcases section13_calS1_cases_or_integerSpan_source
        Smax Tmax W W1 W2 P Q U V C D H Sfam Tfam τS τT
        ω η μ ν μsum νsum δ δ' σ p q u v c d
        _hsource _hnotation _hH S1 hS1 ζ hζ with ⟨j, hj0, hjp, rfl⟩ | hspan
    · exact Section5.integerSpan_of_mem Sfam
        (houtput.1 j hj0 hjp).2.2.2
    · exact Section5.integerSpan_mono (Finset.filter_subset _ _) hspan
  letI : IsMulCommutative (H.subgroupOf Smax) :=
    theorem_13_5_H_subgroupOf_isMulCommutative
      Smax Tmax W W1 W2 P Q U V C D H Sfam Tfam τS τT
        p q u v c d _hsource _hH hS1.1
  have hdegree : ∀ ζ : Section1.ClassFunction Smax, ζ ∈ S1 →
      Section1.degree ζ =
        Section1.degree (Section1.conjugateCharacter (μsum j1)) := by
    intro ζ hζ
    rcases (hS1.2.2 ζ).mp hζ with
      ⟨θ, hθirr, _hθnotker, hζind⟩
    rcases (hS1.2.2 (Section1.conjugateCharacter (μsum j1))).mp hζ0 with
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
      _ = Section1.degree (Section1.conjugateCharacter (μsum j1)) := by
        rw [hζ0ind, Section1.degree_inducedClassFunction]
  have hagree : ∀ ζ : Section1.ClassFunction Smax, ∀ hζ : ζ ∈ S1,
      τ1 (ζ - Section1.conjugateCharacter (μsum j1)) =
        τS (ζ - Section1.conjugateCharacter (μsum j1)) := by
    intro ζ hζ
    apply hcoh.2.2
    refine ⟨Section5.integerSpan_sub (hS1Span ζ hζ) (hS1Span _ hζ0), ?_⟩
    apply (Section5.supportedOn_puncturedSet_iff_degree_eq_zero _).2
    change Section1.degree ζ -
      Section1.degree (Section1.conjugateCharacter (μsum j1)) = 0
    rw [hdegree ζ hζ]
    simp
  refine ⟨?_, ?_⟩
  · calc
      a = Section1.scalarProduct G
          (τ1 (μsum j1 - Section1.conjugateCharacter (μsum j1))) (η 0 1) := by
        rw [map_sub, Section5.scalarProduct_sub_left, hζ1scalar, hζ0scalar]
        simp
      _ = Section1.scalarProduct G
          (τS (μsum j1 - Section1.conjugateCharacter (μsum j1))) (η 0 1) := by
        rw [hagree (μsum j1) _hζ1]
  · intro ζ hζ _hζ_ne0 hζ_ne1
    have hζscalar := horth_except ζ hζ hζ_ne1
    calc
      Section1.scalarProduct G
          (τS (ζ - Section1.conjugateCharacter (μsum j1))) (η 0 1) =
          Section1.scalarProduct G
            (τ1 (ζ - Section1.conjugateCharacter (μsum j1))) (η 0 1) := by
        rw [hagree ζ hζ]
      _ = 0 := by
        rw [map_sub, Section5.scalarProduct_sub_left, hζscalar, hζ0scalar]
        simp

/- Checked wrapper packaging the row choice, checked `calS1` witness, and the
narrow source orthogonality package into the PF `(13.5)` core fields. -/

/- Checked wrapper adding the virtual-character part of the PF `(13.5)`
hypothesis for `χ = η 0 1`. -/

/- Checked restriction-data construction for the selected PF `(13.5)` row
character. -/
private theorem theorem_13_8_restrictionData_of_source
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
    ∃ eta01H : Section1.ClassFunction H, classFunctionRestrictionData H Smax ζ1 eta01H := by
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
  let eta01H : Section1.ClassFunction H := fun x => ζ1 ⟨(x : G), hHS x.property⟩
  exact ⟨eta01H, hHS, fun x => rfl⟩

/- Checked PF `(13.8)` input assembly for PF `(13.5)`. -/

private theorem theorem_13_8_virtualCharacter_one_eq_int
    {G : Type u}
    [Group G]
    [Finite G]
    {χ : Section1.ClassFunction G}
    (hχ : Theory.Character.IsVirtualCharacter χ) :
    ∃ n : ℤ, χ 1 = (n : ℂ) := by
  classical
  rcases hχ with ⟨r, m, n, ρ, hχeq⟩
  refine ⟨∑ i : Fin r, m i * (n i : ℤ), ?_⟩
  have hdeg : ∀ i : Fin r, (ρ i).character 1 = (n i : ℂ) := by
    intro i
    simp
  rw [hχeq]
  unfold Theory.Character.virtualCharacterOfRepresentations
  simp_rw [hdeg]
  exact_mod_cast (rfl : (∑ i : Fin r, m i * (n i : ℤ)) =
    ∑ i : Fin r, m i * (n i : ℤ))

private theorem theorem_13_8_integer_correction_nonnegative
    (m u : ℕ) (b : ℤ) (hu : 2 * u ≤ m) :
    0 ≤ (m : ℝ) * ((b : ℝ) ^ 2) - 2 * (u : ℝ) * (b : ℝ) := by
  rcases lt_trichotomy b 0 with hbneg | hbeq | hbpos
  · have hbR : (b : ℝ) < 0 := by exact_mod_cast hbneg
    have huR : 0 ≤ (u : ℝ) := by exact_mod_cast Nat.zero_le u
    have hmR : 0 ≤ (m : ℝ) := by exact_mod_cast Nat.zero_le m
    have hb2 : 0 ≤ (b : ℝ) ^ 2 := sq_nonneg (b : ℝ)
    nlinarith
  · subst b
    simp
  · have hbInt : (1 : ℤ) ≤ b := by omega
    have hb1 : (1 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hbInt
    have huR : (2 * u : ℝ) ≤ (m : ℝ) := by exact_mod_cast hu
    nlinarith [sq_nonneg ((b : ℝ) - 1), sq_nonneg (b : ℝ)]

private theorem theorem_13_8_p_prime_of_source
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
    Nat.Prime p := by
  rcases theorem_13_2_case_9_7_sourceData_of_sourceContext
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
      p q u v c d hsource with hcaseA | hcaseB
  · rcases hcaseA with
      ⟨_hBarU, _a, _h92, _hH0le, _hCentIn, hpPrime, _hqPrime,
        _hpdata, _hquot, _hcardQuot, _hadvd, _hinj⟩
    exact hpPrime
  · rcases hcaseB with
      ⟨_h92, _hH0le, _hCentIn, hpPrime, _hqPrime, _hpdata, _hquot,
        _hcentBy, _hcyclicQuot, _hirr, _hfield, _hcop, _hdiv,
        _hprimeField⟩
    exact hpPrime

private theorem theorem_13_8_p_ne_two_of_source
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
    p ≠ 2 := by
  rcases hsource with
    ⟨_hcase, _hptypeS, _hptypeT, hp_card, _hq_card, _hC, _hD, _hc_card,
      _hd_card, _hU_card, _hV_card, _hSfam, _hTfam, _hDadeS, _hDadeT,
      _hnotation, _hDadeDiff, _hZeroBase, _hConjIndex, _hConjBeta,
      _hChoice, hMin, _hTauS, _hTauT⟩
  have hoddG : Odd (Nat.card G) := by
    letI : IsMinCE G := hMin
    exact IsMinCE.odd_order
  have hW2_ne_two : Nat.card W2 ≠ 2 :=
    Odd.ne_two_of_dvd_nat hoddG (Subgroup.card_subgroup_dvd_card W2)
  intro hp2
  apply hW2_ne_two
  rw [← hp_card, hp2]

private theorem theorem_13_8_two_mul_u_le_card_P_sub_one_of_pf13_2
    {p q u cardP : ℕ}
    (hp : Nat.Prime p)
    (hp_ne_two : p ≠ 2)
    (hPcard : cardP = p ^ q)
    (hu : u ≤ (p ^ q - 1) / (p - 1)) :
    2 * u ≤ cardP - 1 := by
  have hp_ge3 : 3 ≤ p := by
    have hp2le : 2 ≤ p := hp.two_le
    omega
  have hden_ge : 2 ≤ p - 1 := by omega
  have hquot_le : (p ^ q - 1) / (p - 1) ≤ (p ^ q - 1) / 2 := by
    exact Nat.div_le_div (Nat.le_refl (p ^ q - 1)) hden_ge
      (by decide : (2 : ℕ) ≠ 0)
  have hu_half : u ≤ (p ^ q - 1) / 2 := hu.trans hquot_le
  have hmul : u * 2 ≤ p ^ q - 1 := by
    exact (Nat.le_div_iff_mul_le (by decide : 0 < 2)).mp hu_half
  omega

private theorem theorem_13_8_two_mul_u_le_card_P_sub_one_source
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
    2 * u ≤ Nat.card P - 1 := by
  rcases theorem_13_2 Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
      p q u v c d hsource with
    ⟨_hMF, _htype, _hlarge, _hUcomm, _hFrob, _hPelem, hPcard, huBound,
      _hcoh, _hBook, _hTau, _hnorm⟩
  exact theorem_13_8_two_mul_u_le_card_P_sub_one_of_pf13_2
    (theorem_13_8_p_prime_of_source
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
      p q u v c d hsource)
    (theorem_13_8_p_ne_two_of_source
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
      p q u v c d hsource)
    hPcard huBound

private theorem theorem_13_8_smax_card_eq_P_sup_U_mul_q_source
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
    Nat.card Smax = Nat.card (P ⊔ U : Subgroup G) * q := by
  rcases hsource with
    ⟨_hcaseB, htypeS, _htypeT, _hp_card, hq_card, _hC, _hD, _hc_card,
      _hd_card, _hU_card, _hV_card, _hSfam, _hTfam, _hDadeS, _hDadeT,
      _hnotation⟩
  rcases htypeS with
    ⟨_hMF, _hW1cyc, _hW1ne, _hW1Hall, hScomp, _hUle, _hUnil, _hW1norm,
      hDercomp, _hMFnotcyc, _hsecond, _hfit, _hfitDer, _hW2le, _hW2cyc,
      _hW2ne, _hcent, _hnorm⟩
  have hDer_norm : section10NormalIn (ambientDerivedSubgroup Smax) Smax :=
    section12_normalIn_ambientDerivedSubgroup
  have hS_card : Nat.card Smax = Nat.card (ambientDerivedSubgroup Smax) * Nat.card W1 :=
    section13_card_eq_mul_of_complementIn_normal hScomp hDer_norm
  have hDer_eq : ambientDerivedSubgroup Smax = P ⊔ U := hDercomp.2.2.1
  rw [hS_card, hDer_eq, hq_card]

private theorem theorem_13_8_mu_sum_scalarProduct_self_of_notation_source
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
    (p q u v c d j : ℕ)
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (hnotation : hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2 p q
      ω η μ ν μsum νsum δ δ' σ)
    (hj : j < p) :
    Section1.scalarProduct Smax (μsum j) (μsum j) = (q : ℂ) := by
  classical
  have hnotationFull := hnotation
  rcases hnotation with
    ⟨_hωNat, _hσNat, _hηNat, _hδ, _hδ', hμirr, _hνirr,
      _hμzero_nonprincipal, _hνzero_nonprincipal, _hμind, _hνind,
      hμsum, _hνsum⟩
  rw [hμsum j hj]
  rw [theorem_13_8_scalarProduct_finset_sum_left]
  calc
    (Finset.range q).sum
        (fun i => Section1.scalarProduct Smax (μ i j)
          ((Finset.range q).sum fun i => μ i j)) =
        (Finset.range q).sum (fun _i => (1 : ℂ)) := by
          apply Finset.sum_congr rfl
          intro i hi
          have hiq : i < q := Finset.mem_range.mp hi
          rw [theorem_13_8_scalarProduct_finset_sum_right]
          calc
            (Finset.range q).sum
                (fun i' => Section1.scalarProduct Smax (μ i j) (μ i' j)) =
                Section1.scalarProduct Smax (μ i j) (μ i j) := by
                  apply Finset.sum_eq_single i
                  · intro i' hi' hne
                    have hi'q : i' < q := Finset.mem_range.mp hi'
                    have hneSubtype :
                        (⟨i, hiq⟩ : {i : ℕ // i < q}) ≠ ⟨i', hi'q⟩ := by
                      intro hsub
                      exact hne (Subtype.ext_iff.mp hsub).symm
                    exact section13_typeP_prTIres_pf4_primeTIirr_spec_natural_same_column_orthogonal_source
                      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
                      ω η μ ν μsum νsum δ δ' σ p q u v c d hsource
                      hnotationFull ⟨j, hj⟩ ⟨i, hiq⟩ ⟨i', hi'q⟩ hneSubtype
                  · intro hnot
                    exact (hnot hi).elim
            _ = 1 := section13_scalarProduct_self_of_irreducibleCharacter
              (hμirr i j hiq hj)
    _ = (q : ℂ) := by
      simp

private theorem theorem_13_8_mu_sum_cfNormSq_of_notation_source
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
    (p q u v c d j : ℕ)
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (hnotation : hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2 p q
      ω η μ ν μsum νsum δ δ' σ)
    (hj : j < p) :
    Section5.cfNormSq (μsum j) = (q : ℝ) := by
  unfold Section5.cfNormSq
  rw [theorem_13_8_mu_sum_scalarProduct_self_of_notation_source
    Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
    ω η μ ν μsum νsum δ δ' σ p q u v c d j hsource hnotation hj]
  simp

/- Row-exact PF `(13.5)` input for PF `(13.8)`, preserving the selected
`μsum j1` and the sign of the row coefficient for the final arithmetic. -/
private theorem theorem_13_8_theorem_13_5_exact_input_source
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
      (j1 : ℕ) (eta01H : Section1.ClassFunction H) (a : ℂ),
        Section6.coherentExtension Sfam τS τ1 ∧
          theorem_13_8_eta01RowChoiceData Smax τ1 η μsum p j1 a ∧
            (a = 1 ∨ a = -1) ∧
            theorem_13_5_hypothesis Smax H P C S1 τS
              (Section1.conjugateCharacter (μsum j1)) (μsum j1) (η 0 1) a ∧
            classFunctionRestrictionData H Smax (μsum j1) eta01H := by
  rcases theorem_13_8_eta01_row_index_source
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
      ω η μ ν μsum νsum δ δ' σ p q u v c d hsource hnotation with
    ⟨τ1, j1, a, hcoh, hchoice, hasign⟩
  have hchoice_data := hchoice
  rcases hchoice with ⟨hj1_pos, hj1_lt, _hrowScalar⟩
  rcases theorem_13_8_calS1_witness_of_row_index
      Smax Tmax W W1 W2 P Q U V C D H Sfam Tfam τS τT
      ω η μ ν μsum νsum δ δ' σ p q u v c d
      hsource hnotation hH j1 hj1_pos hj1_lt with
    ⟨S1, hH5, hS1, hζ0, hζ1, hζ_ne⟩
  rcases theorem_13_8_calS1_orthogonality_source
      Smax Tmax W W1 W2 P Q U V C D H Sfam Tfam S1 τS τ1 τT
      ω η μ ν μsum νsum δ δ' σ p q u v c d
      hsource hnotation hH j1 a hcoh hchoice_data hS1 hζ0 hζ1 hζ_ne with
    ⟨ha, horth⟩
  have hηvirt : Theory.Character.IsVirtualCharacter (η 0 1) :=
    theorem_13_8_eta01_virtual_of_source
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
      ω η μ ν μsum νsum δ δ' σ p q u v c d hsource hnotation
  rcases theorem_13_8_restrictionData_of_source
      Smax Tmax W W1 W2 P Q U V C D H Sfam Tfam τS τT (μsum j1)
      p q u v c d hsource hH with
    ⟨eta01H, hres⟩
  refine ⟨τ1, S1, j1, eta01H, a, hcoh, hchoice_data, hasign, ?_, hres⟩
  exact ⟨hH5, hS1, hζ0, hζ1, hζ_ne, hηvirt, ha, horth⟩


private theorem theorem_13_8_post_formula_nonnegative_correction_source
    {G : Type u}
    [Group G]
    [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D H : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (S1 : Finset (Section1.ClassFunction Smax))
    (τS τ1 : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (j1 : ℕ)
    (eta01H α : Section1.ClassFunction H)
    (ω : ℕ → ℕ → Section1.ClassFunction W)
    (η : ℕ → ℕ → Section1.ClassFunction G)
    (μ : ℕ → ℕ → Section1.ClassFunction Smax)
    (ν : ℕ → ℕ → Section1.ClassFunction Tmax)
    (μsum : ℕ → Section1.ClassFunction Smax)
    (νsum : ℕ → Section1.ClassFunction Tmax)
    (δ δ' : ℕ → ℤ)
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
    (a : ℂ)
    (p q u v c d : ℕ)
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (hnotation : hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2 p q
      ω η μ ν μsum νsum δ δ' σ)
    (_hH : H = P ⊔ C)
    (hchoice : theorem_13_8_eta01RowChoiceData Smax τ1 η μsum p j1 a)
    (hsign : a = 1 ∨ a = -1)
    (_h5hyp : theorem_13_5_hypothesis Smax H P C S1 τS
      (Section1.conjugateCharacter (μsum j1)) (μsum j1) (η 0 1) a)
    (hres : classFunctionRestrictionData H Smax (μsum j1) eta01H)
    (hα : virtualCharacterKernelConstituentData H P α)
    (_hexp : ∀ x : H, (x : G) ≠ 1 →
      (η 0 1) (x : G) =
        (a / (Section5.cfNormSq (μsum j1) : ℂ)) * eta01H x + α x)
    (hformula : theorem_13_5_squareSumFormula Smax H (μsum j1) eta01H α (η 0 1) a)
    (hlower : ((Nat.card P - 1 : ℕ) : ℝ) * Complex.normSq (α 1) ≤
      Section7.subgroupSupportEnergy H (Section7.puncturedSubgroupSet H) α) :
    ∃ correction : ℝ,
      0 ≤ correction ∧
        Section7.supportEnergy (Section7.puncturedSubgroupSet H) (η 0 1) =
          ((Nat.card (P ⊔ U : Subgroup G) : ℝ) - (u : ℝ) ^ 2) + correction := by
  classical
  rcases hchoice with ⟨hj1_pos, hj1_lt, _hrowScalar⟩
  have hqpos : 0 < q := by
    rcases hsource with
      ⟨_hcaseB, _hptypeS, _hptypeT, _hp_card, hq_card, _htail⟩
    simpa [hq_card] using (Nat.card_pos (α := W1))
  have hqC_ne : (q : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hqpos)
  have h13_3 := (theorem_13_3 Smax Tmax W W1 W2 P Q U V C D
    Sfam Tfam τS τT p q u v c d hsource).1
  rcases (h13_3 ω η μ ν μsum νsum δ δ' σ hnotation).2 with
    ⟨_τ2, _hcoh2, houtput⟩
  rcases houtput.1 j1 hj1_pos hj1_lt with
    ⟨_hμchar, hμdeg, _hμlinear, _hμSfam⟩
  have hμone : (μsum j1) 1 = ((u * q : ℕ) : ℂ) := by
    simpa [Section1.degree_apply, Nat.cast_mul] using hμdeg
  have hcf : Section5.cfNormSq (μsum j1) = (q : ℝ) :=
    theorem_13_8_mu_sum_cfNormSq_of_notation_source
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
      ω η μ ν μsum νsum δ δ' σ p q u v c d j1 hsource hnotation hj1_lt
  have hcard : Nat.card Smax = Nat.card (P ⊔ U : Subgroup G) * q :=
    theorem_13_8_smax_card_eq_P_sup_U_mul_q_source
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
      p q u v c d hsource
  have hu : 2 * u ≤ Nat.card P - 1 :=
    theorem_13_8_two_mul_u_le_card_P_sub_one_source
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
      p q u v c d hsource
  rcases hres with ⟨_hHS, hres_eval⟩
  have hetaH_one : eta01H 1 = ((u * q : ℕ) : ℂ) := by
    have hres1 := hres_eval 1
    change eta01H 1 =
      μsum j1 (⟨((1 : H) : G), _hHS (by simp)⟩ : Smax) at hres1
    have harg :
        (⟨((1 : H) : G), _hHS (by simp)⟩ : Smax) = 1 := by
      ext
      simp
    rw [hres1, harg]
    exact hμone
  rcases theorem_13_8_virtualCharacter_one_eq_int hα.1 with ⟨n, hαone⟩
  have hzdata :
      ∃ z : ℤ,
        a ^ 2 = 1 ∧
          a * α 1 = (z : ℂ) ∧
          Complex.normSq (α 1) = (z : ℝ) ^ 2 := by
    rcases hsign with ha | ha
    · refine ⟨n, ?_, ?_, ?_⟩
      · rw [ha]
        norm_num
      · rw [ha, hαone]
        simp
      · rw [hαone]
        simp [Complex.normSq]
        ring
    · refine ⟨-n, ?_, ?_, ?_⟩
      · rw [ha]
        norm_num
      · rw [ha, hαone]
        simp
      · rw [hαone]
        simp [Complex.normSq]
        ring
  rcases hzdata with ⟨z, ha_sq, haz, hαnorm⟩
  let A : ℝ := Section7.subgroupSupportEnergy H (Section7.puncturedSubgroupSet H) α
  let B : ℝ := (Nat.card (P ⊔ U : Subgroup G) : ℝ) - (u : ℝ) ^ 2
  let correction : ℝ := A - 2 * (u : ℝ) * (z : ℝ)
  unfold theorem_13_5_squareSumFormula at hformula
  have henergy :
      Section7.supportEnergy (Section7.puncturedSubgroupSet H) (η 0 1) =
        B + correction := by
    have hC :
        ((Section7.supportEnergy (Section7.puncturedSubgroupSet H) (η 0 1) : ℝ) : ℂ) =
          (B + correction : ℝ) := by
      calc
        ((Section7.supportEnergy (Section7.puncturedSubgroupSet H) (η 0 1) : ℝ) : ℂ) =
            (a ^ 2 / (Section5.cfNormSq (μsum j1) : ℂ)) *
              ((Nat.card Smax : ℂ) - ((μsum j1) 1) ^ 2 /
                (Section5.cfNormSq (μsum j1) : ℂ)) -
                2 * a * eta01H 1 * α 1 / (Section5.cfNormSq (μsum j1) : ℂ) +
                  (Section7.subgroupSupportEnergy H
                    (Section7.puncturedSubgroupSet H) α : ℂ) := hformula
        _ = (B + correction : ℝ) := by
          rw [hcf, hcard, hμone, hetaH_one, ha_sq]
          have hcross : 2 * a * ((u * q : ℕ) : ℂ) * α 1 =
              2 * ((u * q : ℕ) : ℂ) * (z : ℂ) := by
            calc
              2 * a * ((u * q : ℕ) : ℂ) * α 1 =
                  2 * ((u * q : ℕ) : ℂ) * (a * α 1) := by ring
              _ = 2 * ((u * q : ℕ) : ℂ) * (z : ℂ) := by rw [haz]
          rw [hcross]
          norm_num [Nat.cast_mul, B, A, correction]
          field_simp [hqC_ne]
          ring
    exact Complex.ofReal_inj.mp hC
  refine ⟨correction, ?_, ?_⟩
  · have hcorr0 :=
      theorem_13_8_integer_correction_nonnegative (Nat.card P - 1) u z hu
    have hlowerz : ((Nat.card P - 1 : ℕ) : ℝ) * ((z : ℝ) ^ 2) ≤ A := by
      simpa [A, hαnorm] using hlower
    nlinarith
  · simpa [B, correction] using henergy

/- Checked final order step for PF `(13.8)`: the source-normalized
post-formula expression is the target bound plus a nonnegative correction. -/
private theorem theorem_13_8_bound_of_theorem_13_5_output_source
    {G : Type u}
    [Group G]
    [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D H : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (S1 : Finset (Section1.ClassFunction Smax))
    (τS τ1 : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (j1 : ℕ)
    (eta01H α : Section1.ClassFunction H)
    (ω : ℕ → ℕ → Section1.ClassFunction W)
    (η : ℕ → ℕ → Section1.ClassFunction G)
    (μ : ℕ → ℕ → Section1.ClassFunction Smax)
    (ν : ℕ → ℕ → Section1.ClassFunction Tmax)
    (μsum : ℕ → Section1.ClassFunction Smax)
    (νsum : ℕ → Section1.ClassFunction Tmax)
    (δ δ' : ℕ → ℤ)
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
    (a : ℂ)
    (p q u v c d : ℕ)
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (hnotation : hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2 p q
      ω η μ ν μsum νsum δ δ' σ)
    (hH : H = P ⊔ C)
    (hchoice : theorem_13_8_eta01RowChoiceData Smax τ1 η μsum p j1 a)
    (hsign : a = 1 ∨ a = -1)
    (h5hyp : theorem_13_5_hypothesis Smax H P C S1 τS
      (Section1.conjugateCharacter (μsum j1)) (μsum j1) (η 0 1) a)
    (hres : classFunctionRestrictionData H Smax (μsum j1) eta01H)
    (hα : virtualCharacterKernelConstituentData H P α)
    (hexp : ∀ x : H, (x : G) ≠ 1 →
      (η 0 1) (x : G) =
        (a / (Section5.cfNormSq (μsum j1) : ℂ)) * eta01H x + α x)
    (hformula : theorem_13_5_squareSumFormula Smax H (μsum j1) eta01H α (η 0 1) a)
    (hlower : ((Nat.card P - 1 : ℕ) : ℝ) * Complex.normSq (α 1) ≤
      Section7.subgroupSupportEnergy H (Section7.puncturedSubgroupSet H) α) :
    squareSumLowerBound (Section7.puncturedSubgroupSet H) (η 0 1)
      ((Nat.card (P ⊔ U : Subgroup G) : ℝ) - (u : ℝ) ^ 2) := by
  rcases theorem_13_8_post_formula_nonnegative_correction_source
      Smax Tmax W W1 W2 P Q U V C D H Sfam Tfam S1 τS τ1 τT j1
      eta01H α ω η μ ν μsum νsum δ δ' σ a p q u v c d
      hsource hnotation hH hchoice hsign h5hyp hres hα hexp hformula hlower with
    ⟨correction, hcorr_nonneg, henergy⟩
  unfold squareSumLowerBound
  rw [henergy]
  exact le_add_of_nonneg_right hcorr_nonneg


private theorem theorem_13_8_eta_zero_one_bound_source
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
    squareSumLowerBound (Section7.puncturedSubgroupSet H) (η 0 1)
      ((Nat.card (P ⊔ U : Subgroup G) : ℝ) - (u : ℝ) ^ 2) := by
  rcases theorem_13_8_theorem_13_5_exact_input_source
      Smax Tmax W W1 W2 P Q U V C D H Sfam Tfam τS τT
      ω η μ ν μsum νsum δ δ' σ p q u v c d hsource hnotation hH with
    ⟨τ1, S1, j1, eta01H, a, _hcoh, hchoice, hsign, h5hyp, hres⟩
  rcases theorem_13_5 Smax Tmax W W1 W2 P Q U V C D H
      Sfam Tfam S1 τS τT (Section1.conjugateCharacter (μsum j1)) (μsum j1)
      eta01H (η 0 1) a
      p q u v c d hsource h5hyp hres with
    ⟨α, hα, hexp, hformula, hlower⟩
  exact theorem_13_8_bound_of_theorem_13_5_output_source
    Smax Tmax W W1 W2 P Q U V C D H Sfam Tfam S1 τS τ1 τT j1
    eta01H α ω η μ ν μsum νsum δ δ' σ a p q u v c d
    hsource hnotation hH hchoice hsign h5hyp hres hα hexp hformula hlower

private theorem theorem_13_8_bound_of_eta_zero_one_bound
    {G : Type u}
    [Group G]
    [Finite G]
    (P U H S' : Subgroup G)
    (η : ℕ → ℕ → Section1.ClassFunction G)
    (u : ℕ)
    (hS' : S' = P ⊔ U)
    (hbound : squareSumLowerBound (Section7.puncturedSubgroupSet H) (η 0 1)
      ((Nat.card (P ⊔ U : Subgroup G) : ℝ) - (u : ℝ) ^ 2)) :
    squareSumLowerBound (Section7.puncturedSubgroupSet H) (η 0 1)
      ((Nat.card S' : ℝ) - (u : ℝ) ^ 2) := by
  simpa [hS'] using hbound

public theorem theorem_13_8
    {G : Type u}
    [Group G]
    [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D H S' : Subgroup G)
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
          S' = P ⊔ U →
            squareSumLowerBound (Section7.puncturedSubgroupSet H) (η 0 1)
              ((Nat.card S' : ℝ) - (u : ℝ) ^ 2) := by
  intro hsource hnotation hH hS'
  exact theorem_13_8_bound_of_eta_zero_one_bound P U H S' η u hS'
    (theorem_13_8_eta_zero_one_bound_source
      Smax Tmax W W1 W2 P Q U V C D H Sfam Tfam τS τT
      ω η μ ν μsum νsum δ δ' σ p q u v c d hsource hnotation hH)
end CFSG.Section13
