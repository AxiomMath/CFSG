module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection13.PFsection13_16
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection12.PFsection12_7
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection12.PFsection12_16
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection13.lemma_13_13
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection9.PFsection9_1
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection8.SourceTypePBridge

namespace CFSG
end CFSG
open CFSG

/-!
# Peterfalvi, Section 13: PFsection13_17
-/

noncomputable section

open scoped BigOperators Pointwise commutatorElement

attribute [local instance] Fintype.ofFinite

namespace CFSG.Section13

universe v
universe u

/-! ## (13.17) -/


private theorem section13_theorem_13_17_typeI_of_not_conj_sourceContext
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D L H : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (hLmax : L ∈ section9MaximalSubgroups G)
    (hMF : section16MFSubgroup L H)
    (hnotS : ∀ g : G, L ≠ Smax.conjBy g)
    (hnotT : ∀ g : G, L ≠ Tmax.conjBy g) :
    Section8.typeIDefinitionData L H := by
  rcases hsource with
    ⟨hcaseB, _hptypeS, _hptypeT, _hp, _hq, _hC, _hD, _hc, _hd,
      _hUcard, _hVcard, _hSfam, _hTfam, _hDadeS, _hDadeT,
      _hnotationData, _hDadeDiff, _hZeroDegree, _hConjIndex, _hConjBetaTau,
      _hChoice, _hMin, _hFourSixS, _hFourSixT⟩
  rcases hcaseB with
    ⟨_hWprod, _hWcyc, _hW1ne, _hW2ne, _hWhat,
      _hSmaxMax, _hTmaxMax, _hSMF, _hTMF, _hSeq, _hTeq,
      _hSdisj, _hTdisj, _hST, _hII, _hStype, _hTtype, hclass⟩
  rcases hclass L hLmax with hLconjS | hLconjT | hLtypeI
  · rcases hLconjS with ⟨g, hg⟩
    exact False.elim (hnotS g hg)
  · rcases hLconjT with ⟨g, hg⟩
    exact False.elim (hnotT g hg)
  · rcases hLtypeI with ⟨H', hMF', hTypeI'⟩
    have hH' : H' = H :=
      le_antisymm (hMF.2 H' hMF'.1) (hMF'.2 H hMF.1)
    simpa [hH'] using hTypeI'


private theorem section13_theorem_13_17_frobenius_of_typeI
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    {L H : Subgroup G}
    (_hLmax : L ∈ section9MaximalSubgroups G)
    (_hMF : section16MFSubgroup L H)
    (_hTypeI : Section8.typeIDefinitionData L H) :
    Section7.frobeniusWithKernel L H := by
  exact Section12.theorem_12_7 L H _hLmax _hMF _hTypeI

private theorem section13_theorem_13_17_frobenius_of_not_conj_sourceContext
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (Smax Tmax W W1 W2 P Q U V C D L H : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (hLmax : L ∈ section9MaximalSubgroups G)
    (hMF : section16MFSubgroup L H)
    (hnotS : ∀ g : G, L ≠ Smax.conjBy g)
    (hnotT : ∀ g : G, L ≠ Tmax.conjBy g) :
    Section7.frobeniusWithKernel L H := by
  have hTypeI : Section8.typeIDefinitionData L H :=
    section13_theorem_13_17_typeI_of_not_conj_sourceContext
      Smax Tmax W W1 W2 P Q U V C D L H Sfam Tfam τS τT
      p q u v c d hsource hLmax hMF hnotS hnotT
  exact section13_theorem_13_17_frobenius_of_typeI hLmax hMF hTypeI

private theorem section13_theorem_13_17_U_le_L_of_normalizer
    {G : Type u} [Group G] [Finite G]
    {U L : Subgroup G}
    (hNormUleL : Subgroup.normalizer (U : Set G) ≤ L) :
    U ≤ L := by
  exact Subgroup.le_normalizer.trans hNormUleL

private theorem section13_theorem_13_17_W1_le_normalizer_U_of_sourceContext
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d) :
    W1 ≤ Subgroup.normalizer (U : Set G) := by
  rcases hsource with
    ⟨_hcaseB, hptypeS, _hptypeT, _hp, _hq, _hC, _hD, _hc, _hd,
      _hUcard, _hVcard, _hSfam, _hTfam, _hDadeS, _hDadeT,
      _hnotationData, _hDadeDiff, _hZeroDegree, _hConjIndex, _hConjBetaTau,
      _hChoice, _hMin, _hFourSixS, _hFourSixT⟩
  rcases hptypeS with
    ⟨_hMF, _hW1cyc, _hW1ne, _hW1Hall, _hMcomp, _hUleD, _hUnil, hW1normU,
      _hDercomp, _hMFnotcyc, _hsecond, _hfit, _hfitDer, _hW2le, _hW2cyc,
      _hW2ne, _hcent, _hnorm⟩
  intro x hx
  exact (mem_subgroupNormalizerIn.mp (hW1normU hx)).1

private theorem section13_theorem_13_17_W1_le_L_of_sourceContext
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D L : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (hNormUleL : Subgroup.normalizer (U : Set G) ≤ L) :
    W1 ≤ L := by
  intro x hx
  exact hNormUleL
    (section13_theorem_13_17_W1_le_normalizer_U_of_sourceContext
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
      p q u v c d hsource hx)

private theorem section13_subgroupOf_map_conj_eq_ambient
    {G : Type u} [Group G]
    {S H K : Subgroup G} {x : S}
    (hHleS : H ≤ S) (hKleS : K ≤ S)
    (heq : K.subgroupOf S =
      (H.subgroupOf S).map (MulAut.conj x).toMonoidHom) :
    K = H.conjBy (x : G) := by
  ext y
  constructor
  · intro hyK
    have hyS : y ∈ S := hKleS hyK
    have hySub : (⟨y, hyS⟩ : S) ∈ K.subgroupOf S := by
      simpa [Subgroup.mem_subgroupOf] using hyK
    have hyMap :
        (⟨y, hyS⟩ : S) ∈
          (H.subgroupOf S).map (MulAut.conj x).toMonoidHom := by
      simpa [heq] using hySub
    rcases Subgroup.mem_map.mp hyMap with ⟨z, hzH, hz_eq⟩
    refine Subgroup.mem_map.mpr ?_
    refine ⟨(z : G), ?_, ?_⟩
    · simpa [Subgroup.mem_subgroupOf] using hzH
    · apply Subtype.ext_iff.mp at hz_eq
      simpa [MulAut.conj_apply, mul_assoc] using hz_eq
  · intro hy
    rcases Subgroup.mem_map.mp hy with ⟨z, hzH, hz_eq⟩
    have hzS : z ∈ S := hHleS hzH
    have hyS : y ∈ S := by
      rw [← hz_eq]
      exact S.mul_mem (S.mul_mem x.property hzS) (S.inv_mem x.property)
    have hzSub : (⟨z, hzS⟩ : S) ∈ H.subgroupOf S := by
      simpa [Subgroup.mem_subgroupOf] using hzH
    have hyMap :
        (⟨y, hyS⟩ : S) ∈
          (H.subgroupOf S).map (MulAut.conj x).toMonoidHom := by
      refine Subgroup.mem_map.mpr ?_
      refine ⟨⟨z, hzS⟩, hzSub, ?_⟩
      apply Subtype.ext
      simpa [MulAut.conj_apply, mul_assoc] using hz_eq
    have hySub : (⟨y, hyS⟩ : S) ∈ K.subgroupOf S := by
      simpa [heq] using hyMap
    simpa [Subgroup.mem_subgroupOf] using hySub

private theorem section13_isHallSubgroup_subgroupOf_conjBy_of_isHallSubgroup
    {G : Type u} [Group G] [Finite G]
    {S U : Subgroup G} {a : G} {π : Set Nat.Primes}
    (hUleS : U ≤ S)
    (hUaleS : U.conjBy a ≤ S)
    (hHallU : IsHallSubgroup π (U.subgroupOf S)) :
    IsHallSubgroup π ((U.conjBy a).subgroupOf S) := by
  classical
  refine isHallSubgroup_of (G := S) (π := π)
    (H := (U.conjBy a).subgroupOf S) (hcard := ?_) (hindex := ?_)
  · intro p hp
    have hcardUa :
        Nat.card ((U.conjBy a).subgroupOf S) = Nat.card (U.subgroupOf S) := by
      calc
        Nat.card ((U.conjBy a).subgroupOf S) = Nat.card (U.conjBy a) :=
          natCard_subgroupOf_eq (U.conjBy a) S hUaleS
        _ = Nat.card U := section11_card_conjBy (G := G) U a
        _ = Nat.card (U.subgroupOf S) := (natCard_subgroupOf_eq U S hUleS).symm
    apply hHallU.p_in_pi_of_p_dvd_card p
    rw [← hcardUa]
    exact hp
  · intro p hpπ hpidx
    apply (hHallU.p_in_pi_of_p_dvd_index p ?_) hpπ
    have hcardUa :
        Nat.card ((U.conjBy a).subgroupOf S) = Nat.card (U.subgroupOf S) := by
      calc
        Nat.card ((U.conjBy a).subgroupOf S) = Nat.card (U.conjBy a) :=
          natCard_subgroupOf_eq (U.conjBy a) S hUaleS
        _ = Nat.card U := section11_card_conjBy (G := G) U a
        _ = Nat.card (U.subgroupOf S) := (natCard_subgroupOf_eq U S hUleS).symm
    have hidx :
        ((U.conjBy a).subgroupOf S).index = (U.subgroupOf S).index := by
      have hmul₁ :
          ((U.conjBy a).subgroupOf S).index *
              Nat.card ((U.conjBy a).subgroupOf S) = Nat.card S :=
        Subgroup.index_mul_card (H := (U.conjBy a).subgroupOf S)
      have hmul₂ :
          (U.subgroupOf S).index * Nat.card (U.subgroupOf S) = Nat.card S :=
        Subgroup.index_mul_card (H := U.subgroupOf S)
      have hmul₁' :
          ((U.conjBy a).subgroupOf S).index * Nat.card (U.subgroupOf S) =
            Nat.card S := by
        rw [← hcardUa]
        exact hmul₁
      have hmul :
          ((U.conjBy a).subgroupOf S).index * Nat.card (U.subgroupOf S) =
            (U.subgroupOf S).index * Nat.card (U.subgroupOf S) := by
        exact hmul₁'.trans hmul₂.symm
      exact Nat.mul_right_cancel (Nat.card_pos (α := U.subgroupOf S)) hmul
    simpa [← hidx] using hpidx

private theorem section13_exists_conj_normalizes_of_hall_subgroupOf
    {G : Type u} [Group G] [Finite G]
    {S L U : Subgroup G} {a : G} {π : Set Nat.Primes}
    (_hS : S = L.conjBy a)
    (hUleS : U ≤ S)
    (hUaleS : U.conjBy a ≤ S)
    (hsolvS : Group.IsSolvable S)
    (hHallUa : IsHallSubgroup π ((U.conjBy a).subgroupOf S))
    (hHallU : IsHallSubgroup π (U.subgroupOf S)) :
    ∃ x : G, x ∈ S ∧ U.conjBy (x * a) = U := by
  classical
  obtain ⟨x, hx⟩ :=
    exists_conj_eq_of_isHallSubgroup_of_solvable
      (G := S) hsolvS hHallUa hHallU
  refine ⟨x, x.property, ?_⟩
  have hamb : U = (U.conjBy a).conjBy (x : G) :=
    section13_subgroupOf_map_conj_eq_ambient
      (S := S) (H := U.conjBy a) (K := U) (x := x)
      hUaleS hUleS hx
  rw [Subgroup.conjBy_conjBy] at hamb
  exact hamb.symm

private theorem section13_normalizer_le_of_conj_hall_witness
    {G : Type u} [Group G] [Finite G]
    {S L U : Subgroup G} {a x : G}
    (hS : S = L.conjBy a)
    (hxS : x ∈ S)
    (hUnorm : U.conjBy (x * a) = U)
    (hNormUleL : Subgroup.normalizer (U : Set G) ≤ L) :
    Subgroup.normalizer (U : Set G) ≤ S := by
  have hyNormU : x * a ∈ Subgroup.normalizer (U : Set G) :=
    section10_mem_normalizer_of_conjBy_eq (G := G) hUnorm
  have hNfix :
      (Subgroup.normalizer (U : Set G)).conjBy (x * a) =
        Subgroup.normalizer (U : Set G) :=
    section11_conjBy_eq_of_mem_normalizer
      (H := Subgroup.normalizer (U : Set G)) (Subgroup.le_normalizer hyNormU)
  have hxNormS : x ∈ Subgroup.normalizer (S : Set G) := Subgroup.le_normalizer hxS
  have hLconj : L.conjBy (x * a) = S := by
    calc
      L.conjBy (x * a) = (L.conjBy a).conjBy x := by
        rw [Subgroup.conjBy_mul]
      _ = S.conjBy x := by rw [← hS]
      _ = S := section11_conjBy_eq_of_mem_normalizer (H := S) hxNormS
  intro n hn
  have hnConj :
      n ∈ (Subgroup.normalizer (U : Set G)).conjBy (x * a) := by
    simpa [hNfix] using hn
  rcases Subgroup.mem_map.mp hnConj with ⟨m, hmN, hm⟩
  have hmL : m ∈ L := hNormUleL hmN
  have hnLconj : n ∈ L.conjBy (x * a) := by
    refine Subgroup.mem_map.mpr ⟨m, hmL, ?_⟩
    exact hm
  simpa [hLconj] using hnLconj

private theorem section13_theorem_13_17_U_le_Smax_of_sourceContext
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d) :
    U ≤ Smax := by
  rcases hsource with
    ⟨_hcase, hptypeS, _hptypeT, _hp, _hq, _hC, _hD, _hc, _hd,
      _hUcard, _hVcard, _hSfam, _hTfam, _hDadeS, _hDadeT,
      _hnotationData, _hDadeDiff, _hZeroDegree, _hConjIndex, _hConjBetaTau,
      _hChoice, _hMin, _hFourSixS, _hFourSixT⟩
  exact hptypeS.2.2.2.2.2.1.trans section12_ambientDerivedSubgroup_le

private theorem section13_theorem_13_17_Smax_solvable_of_sourceContext
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d) :
    Group.IsSolvable Smax := by
  rcases hsource with
    ⟨hcase, _hptypeS, _hptypeT, _hp, _hq, _hC, _hD, _hc, _hd,
      _hUcard, _hVcard, _hSfam, _hTfam, _hDadeS, _hDadeT,
      _hnotationData, _hDadeDiff, _hZeroDegree, _hConjIndex, _hConjBetaTau,
      _hChoice, hMin, _hFourSixS, _hFourSixT⟩
  let : IsMinCE G := hMin
  rcases hcase with
    ⟨_hWprod, _hWcyc, _hW1ne, _hW2ne, _hWhat,
      hSmaxMax, _hTmaxMax, _hSMF, _hTMF, _hSeq, _hTeq,
      _hSdisj, _hTdisj, _hST, _hII, _hStype, _hTtype, _hclass⟩
  exact section9_solvable_of_proper_subgroup hSmaxMax.1

/-- Source fact `hallU` in the PF `(13.17)` proof: the current Type-P subgroup
`U` is a Hall subgroup of `Smax`. -/
private theorem section13_theorem_13_17_U_hall_Smax_of_sourceContext
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d) :
    IsHallSubgroup (subgroupPrimeSet U) (U.subgroupOf Smax) := by
  classical
  rcases hsource with
    ⟨_hcase, hptypeS, _hptypeT, _hp, _hq, _hC, _hD, _hc, _hd,
      _hUcard, _hVcard, _hSfam, _hTfam, _hDadeS, _hDadeT,
      _hnotationData, _hDadeDiff, _hZeroDegree, _hConjIndex, _hConjBetaTau,
      _hChoice, _hMin, _hFourSixS, _hFourSixT⟩
  have hptypeSOrig := hptypeS
  rcases hptypeS with
    ⟨hPMF, _hW1cyc, _hW1ne, hW1HallS, hScomp, _hUleD, _hUnil, _hW1norm,
      hDercomp, _hPnotcyc, _hsecond, _hfit, _hfitDer, _hW2le, _hW2cyc,
      _hW2ne, _hcent, _hnorm⟩
  have hDnormalS : section10NormalIn (ambientDerivedSubgroup Smax) Smax :=
    section12_normalIn_ambientDerivedSubgroup
  have hDHallS :
      section16HallSubgroupOf (ambientDerivedSubgroup Smax) Smax :=
    section13_complementIn_left_hallSubgroupOf_of_right_hallSubgroupOf
      (H := Smax) (K := ambientDerivedSubgroup Smax) (L := W1)
      hScomp hDnormalS hW1HallS
  have hPHallS : section16HallSubgroupOf P Smax :=
    ⟨Section12.section16MFSubgroup_le hPMF,
      Section12.section16MFSubgroup_subgroupOf_isHall hPMF⟩
  have hPHallD :
      section16HallSubgroupOf P (ambientDerivedSubgroup Smax) := by
    refine ⟨hDercomp.1, ?_⟩
    exact section13_hallSubgroup_in_intermediate_of_hall_overgroup
      (H := P) (D := ambientDerivedSubgroup Smax) (M := Smax)
      hDercomp.1 hScomp.1 hPHallS.2
  have hPnormalD : section10NormalIn P (ambientDerivedSubgroup Smax) :=
    section13_mf_normalIn_ambientDerived_of_typeP
      (M := Smax) (MF := P) (U := U) (W1 := W1) (W2 := W2) hptypeSOrig
  have hUHallD :
      section16HallSubgroupOf U (ambientDerivedSubgroup Smax) :=
    section13_complementIn_right_hallSubgroupOf_of_left_hallSubgroupOf
      (H := ambientDerivedSubgroup Smax) (K := P) (L := U)
      hDercomp hPnormalD hPHallD
  exact section13_hallSubgroup_in_overgroup_of_hall_intermediate
    (H := U) (D := ambientDerivedSubgroup Smax) (M := Smax)
    hUHallD.1 hDHallS.1 hUHallD.2 hDHallS.2

private theorem section13_theorem_13_17_hall_conj_witness_of_L_conj_Smax_sourceContext
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D L : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    {a : G}
    (hS : Smax = L.conjBy a)
    (hNormUleL : Subgroup.normalizer (U : Set G) ≤ L) :
    ∃ x : G, x ∈ Smax ∧ U.conjBy (x * a) = U := by
  classical
  have hUleS : U ≤ Smax :=
    section13_theorem_13_17_U_le_Smax_of_sourceContext
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
      p q u v c d hsource
  have hUleL : U ≤ L := Subgroup.le_normalizer.trans hNormUleL
  have hUaleS : U.conjBy a ≤ Smax := by
    intro y hy
    rw [hS]
    rcases Subgroup.mem_map.mp hy with ⟨z, hzU, hz_eq⟩
    exact Subgroup.mem_map.mpr ⟨z, hUleL hzU, hz_eq⟩
  have hsolvS : Group.IsSolvable Smax :=
    section13_theorem_13_17_Smax_solvable_of_sourceContext
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
      p q u v c d hsource
  have hHallU : IsHallSubgroup (subgroupPrimeSet U) (U.subgroupOf Smax) :=
    section13_theorem_13_17_U_hall_Smax_of_sourceContext
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
      p q u v c d hsource
  have hHallUa :
      IsHallSubgroup (subgroupPrimeSet U) ((U.conjBy a).subgroupOf Smax) :=
    section13_isHallSubgroup_subgroupOf_conjBy_of_isHallSubgroup
      hUleS hUaleS hHallU
  exact section13_exists_conj_normalizes_of_hall_subgroupOf
    hS hUleS hUaleS hsolvS hHallUa hHallU

private theorem section13_theorem_13_17_complement_alternative_of_complement_eq
    {G : Type u} [Group G] [Finite G]
    {L H W1 W2 E Q : Subgroup G}
    (hcompE : section12ComplementIn L H E)
    (halt : E = W1 ∨ ∃ y : G, y ∈ Q ∧ E = W1 ⊔ W2.conjBy y) :
    section12ComplementIn L H W1 ∨
      ∃ y : G, y ∈ Q ∧ section12ComplementIn L H (W1 ⊔ W2.conjBy y) := by
  rcases halt with hE | hE
  · left
    simpa [← hE] using hcompE
  · rcases hE with ⟨y, hyQ, hE⟩
    right
    exact ⟨y, hyQ, by simpa [← hE] using hcompE⟩

private theorem section13_theorem_13_17_U_le_H_from_centralizer_inf
    {G : Type u} [Group G] [Finite G]
    {U L H : Subgroup G}
    (hUcomm : IsMulCommutative U)
    (hUleL : U ≤ L)
    (hcent : subgroupCentralizerIn L (U ⊓ H) ≤ H) :
    U ≤ H := by
  let : IsMulCommutative U := hUcomm
  intro u hu
  apply hcent
  refine ⟨hUleL hu, ?_⟩
  change u ∈ Subgroup.centralizer (((U ⊓ H : Subgroup G) : Set G))
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  have hyU : y ∈ U := hy.1
  let uU : U := ⟨u, hu⟩
  let yU : U := ⟨y, hyU⟩
  have hcomm : uU * yU = yU * uU := mul_comm' uU yU
  exact (congrArg (fun z : U => (z : G)) hcomm).symm

private theorem section13_centralizer_nontrivial_kernel_subgroup_le_of_fixedPointFree
    {G : Type u} [Group G] [Finite G]
    {L H K : Subgroup G}
    (hKleH : K ≤ H)
    (hKne : K ≠ ⊥)
    (hfixed : ∀ x : G, x ∈ L → x ∉ H → Section2.centralizerIn H x = ⊥) :
    subgroupCentralizerIn L K ≤ H := by
  classical
  intro x hx
  by_contra hxH
  have hx' : x ∈ L ∧ x ∈ Subgroup.centralizer (K : Set G) := by
    simpa [subgroupCentralizerIn] using hx
  have hcx : Section2.centralizerIn H x = ⊥ := hfixed x hx'.1 hxH
  have hKnontrivial : ∃ k : G, k ∈ K ∧ k ≠ 1 := by
    by_contra hnone
    apply hKne
    apply le_antisymm
    · intro k hk
      have hk1 : k = 1 := by
        by_contra hkne
        exact hnone ⟨k, hk, hkne⟩
      simp [hk1]
    · exact bot_le
  rcases hKnontrivial with ⟨k, hkK, hkne⟩
  have hx_centralizes_k : x * k = k * x := by
    rw [Subgroup.mem_centralizer_iff] at hx'
    exact (hx'.2 k hkK).symm
  have hkCent : k ∈ Section2.centralizerIn H x := by
    refine ⟨hKleH hkK, ?_⟩
    change k ∈ Subgroup.centralizer ({x} : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    simp only [Set.mem_singleton_iff] at hy
    subst y
    exact hx_centralizes_k
  have hkBot : k ∈ (⊥ : Subgroup G) := by
    simpa [hcx] using hkCent
  exact hkne (by simpa using hkBot)

private theorem section13_subgroupCentralizerIn_eq_bot_of_fixedPointFree_disjoint_nontrivial
    {G : Type u} [Group G] [Finite G]
    {A H L : Subgroup G}
    (hAleL : A ≤ L)
    (hAne : A ≠ ⊥)
    (hAinfH : A ⊓ H = ⊥)
    (hfixed : ∀ x : G, x ∈ L → x ∉ H → Section2.centralizerIn H x = ⊥) :
    subgroupCentralizerIn H A = ⊥ := by
  classical
  have hAnontrivial : ∃ a : G, a ∈ A ∧ a ≠ 1 := by
    by_contra hnone
    apply hAne
    apply le_antisymm
    · intro a ha
      have ha1 : a = 1 := by
        by_contra hane
        exact hnone ⟨a, ha, hane⟩
      simp [ha1]
    · exact bot_le
  rcases hAnontrivial with ⟨a, haA, hane⟩
  have ha_not_H : a ∉ H := by
    intro haH
    have haInf : a ∈ A ⊓ H := ⟨haA, haH⟩
    have haBot : a ∈ (⊥ : Subgroup G) := by
      simpa [hAinfH] using haInf
    exact hane (by simpa using haBot)
  have hcent_a : Section2.centralizerIn H a = ⊥ := hfixed a (hAleL haA) ha_not_H
  apply le_antisymm
  · intro x hx
    have hx' : x ∈ H ∧ x ∈ Subgroup.centralizer (A : Set G) := by
      simpa [subgroupCentralizerIn] using hx
    have hxCentA : a * x = x * a := by
      rw [Subgroup.mem_centralizer_iff] at hx'
      exact hx'.2 a haA
    have hxCent : x ∈ Section2.centralizerIn H a := by
      refine ⟨hx'.1, ?_⟩
      change x ∈ Subgroup.centralizer ({a} : Set G)
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      simp only [Set.mem_singleton_iff] at hy
      subst y
      exact hxCentA
    have hxBot : x ∈ (⊥ : Subgroup G) := by
      rw [← hcent_a]
      exact hxCent
    simpa using hxBot
  · exact bot_le

private theorem section13_ne_bot_of_subgroupOf_ne_bot
    {G : Type u} [Group G] [Finite G]
    {H L : Subgroup G}
    (hne : H.subgroupOf L ≠ ⊥) :
    H ≠ ⊥ := by
  intro hHbot
  apply hne
  ext x
  constructor
  · intro hx
    have hxH : (x : G) ∈ H := by
      simpa [Subgroup.mem_subgroupOf] using hx
    have hxBot : (x : G) ∈ (⊥ : Subgroup G) := by
      simpa [hHbot] using hxH
    exact Subtype.ext (by simpa using hxBot)
  · intro hx
    simp only [Subgroup.mem_bot] at hx
    simp [hx]

private theorem section13_left_ne_bot_of_frobeniusJoinWithKernel
    {G : Type u} [Group G] [Finite G]
    {K R : Subgroup G}
    (hfrob : section12FrobeniusJoinWithKernel K R) :
    K ≠ ⊥ :=
  section13_ne_bot_of_subgroupOf_ne_bot (L := K ⊔ R) hfrob.kernel_ne_bot

private theorem section13_right_ne_bot_of_frobeniusJoinWithKernel
    {G : Type u} [Group G] [Finite G]
    {K R : Subgroup G}
    (hfrob : section12FrobeniusJoinWithKernel K R) :
    R ≠ ⊥ :=
  section13_ne_bot_of_subgroupOf_ne_bot (L := K ⊔ R) hfrob.complement_ne_bot

private theorem section13_H_ne_bot_of_frobeniusWithKernel
    {G : Type u} [Group G] [Finite G]
    {L H : Subgroup G}
    (hfrob : Section7.frobeniusWithKernel L H) :
    H ≠ ⊥ := by
  rcases hfrob with ⟨_hHL, _hHnorm, R, _hcomp, hHne, _hRne, _hfixedR⟩
  exact section13_ne_bot_of_subgroupOf_ne_bot (L := L) hHne

private theorem section13_UinfH_ne_bot_from_frobenius_action
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    {U W1 H L : Subgroup G}
    (hUleL : U ≤ L)
    (hW1leL : W1 ≤ L)
    (hHne : H ≠ ⊥)
    (hW1infH : W1 ⊓ H = ⊥)
    (haction : U ⊓ H = ⊥ → Section9.frobeniusActionData (U ⊔ W1) U W1 H)
    (hfixed : ∀ x : G, x ∈ L → x ∉ H → Section2.centralizerIn H x = ⊥) :
    U ⊓ H ≠ ⊥ := by
  classical
  intro hUinfH
  have hact : Section9.frobeniusActionData (U ⊔ W1) U W1 H := haction hUinfH
  have hfrobUW1 : section12FrobeniusJoinWithKernel U W1 := hact.2.1
  have hUne : U ≠ ⊥ := section13_left_ne_bot_of_frobeniusJoinWithKernel hfrobUW1
  have hW1ne : W1 ≠ ⊥ := section13_right_ne_bot_of_frobeniusJoinWithKernel hfrobUW1
  have hCU : subgroupCentralizerIn H U = ⊥ :=
    section13_subgroupCentralizerIn_eq_bot_of_fixedPointFree_disjoint_nontrivial
      hUleL hUne hUinfH hfixed
  have hCW1 : subgroupCentralizerIn H W1 = ⊥ :=
    section13_subgroupCentralizerIn_eq_bot_of_fixedPointFree_disjoint_nontrivial
      hW1leL hW1ne hW1infH hfixed
  have h9 := Section9.theorem_9_1 (U ⊔ W1) U W1 H hact
  have hcardH : Nat.card H = 1 := by
    have h := h9.2.2 hCU
    rw [hCW1] at h
    simpa [Subgroup.card_bot] using h
  exact hHne ((Subgroup.eq_bot_iff_card (H := H)).2 hcardH)

private theorem section13_inf_eq_bot_of_card_right_coprime
    {G : Type u} [Group G] [Finite G]
    {H K : Subgroup G} {q : ℕ}
    (hcardK : q = Nat.card K)
    (hcop : Nat.Coprime (Nat.card H) q) :
    K ⊓ H = ⊥ := by
  have hcardInf_dvd_K : Nat.card (K ⊓ H : Subgroup G) ∣ Nat.card K := by
    rw [← natCard_subgroupOf_eq (K ⊓ H) K inf_le_left]
    exact Subgroup.card_subgroup_dvd_card ((K ⊓ H).subgroupOf K)
  have hcardInf_dvd_H : Nat.card (K ⊓ H : Subgroup G) ∣ Nat.card H := by
    rw [← natCard_subgroupOf_eq (K ⊓ H) H inf_le_right]
    exact Subgroup.card_subgroup_dvd_card ((K ⊓ H).subgroupOf H)
  exact (Subgroup.eq_bot_iff_card (H := (K ⊓ H : Subgroup G))).2
    (Nat.eq_one_of_dvd_coprimes hcop hcardInf_dvd_H (by simpa [hcardK] using hcardInf_dvd_K))

private theorem section13_coprime_card_of_mf_subgroup_disjoint
    {G : Type u} [Group G] [Finite G]
    {L H K : Subgroup G}
    (hMF : section16MFSubgroup L H)
    (hKleL : K ≤ L)
    (hdisj : Disjoint K H) :
    Nat.Coprime (Nat.card H) (Nat.card K) := by
  classical
  let Hloc : Subgroup L := H.subgroupOf L
  let Kloc : Subgroup L := K.subgroupOf L
  have hHleL : H ≤ L := Section12.section16MFSubgroup_le hMF
  let : Hloc.Normal := by
    change (H.subgroupOf L).Normal
    exact Section12.section16MFSubgroup_subgroupOf_normal hMF
  have hHall : IsHallSubgroup (subgroupPrimeSet H) Hloc := by
    simpa [Hloc] using Section12.section16MFSubgroup_subgroupOf_isHall hMF
  have hcopIndex : Nat.Coprime (Nat.card H) Hloc.index := by
    have hcardHloc : Nat.card Hloc = Nat.card H := by
      simpa [Hloc] using natCard_subgroupOf_eq H L hHleL
    rw [← hcardHloc]
    exact hHall.card_coprime_index
  have hKcard_dvd_index : Nat.card K ∣ Hloc.index := by
    let HK : Subgroup L := Hloc ⊔ Kloc
    have hrel_dvd_index : Hloc.relIndex HK ∣ Hloc.index :=
      Subgroup.relIndex_dvd_index_of_le (H := Hloc) (K := HK) le_sup_left
    have hrel_eq : Hloc.relIndex HK = Nat.card K := by
      have hdisjLoc : Disjoint Hloc Kloc := by
        rw [Subgroup.disjoint_def]
        intro x hxH hxK
        apply Subtype.ext
        exact Subgroup.disjoint_def.mp hdisj
          (by simpa [Kloc, Subgroup.mem_subgroupOf] using hxK)
          (by simpa [Hloc, Subgroup.mem_subgroupOf] using hxH)
      have hcomp :
          (Hloc.subgroupOf HK).IsComplement' (Kloc.subgroupOf HK) := by
        simpa [HK] using isComplement'_subgroupOf_sup_of_disjoint Hloc Kloc hdisjLoc
      have hidx : (Hloc.subgroupOf HK).index = Nat.card (Kloc.subgroupOf HK) :=
        (Subgroup.IsComplement'.symm hcomp).index_eq_card
      have hcardKlocHK : Nat.card (Kloc.subgroupOf HK) = Nat.card K := by
        have hcard₁ : Nat.card (Kloc.subgroupOf HK) = Nat.card Kloc :=
          natCard_subgroupOf_eq Kloc HK le_sup_right
        have hcard₂ : Nat.card Kloc = Nat.card K := by
          simpa [Kloc] using natCard_subgroupOf_eq K L hKleL
        exact hcard₁.trans hcard₂
      simpa [Subgroup.relIndex] using hidx.trans hcardKlocHK
    exact hrel_eq ▸ hrel_dvd_index
  exact Nat.Coprime.of_dvd_right hKcard_dvd_index hcopIndex

private theorem section13_isPiSubgroup_primeSet_compl_of_coprime_card
    {G G' : Type*} [Group G] [Finite G] [Group G'] [Finite G']
    {H : Subgroup G} {K : Subgroup G'}
    (hcop : Nat.Coprime (Nat.card H) (Nat.card K)) :
    IsPiSubgroup (G := G') (subgroupPrimeSet H)ᶜ K := by
  intro p hpK
  change p ∉ subgroupPrimeSet H
  intro hpH
  have hpHdiv : p.val ∣ Nat.card H := by
    simpa [subgroupPrimeSet] using hpH
  have hpKcop : Nat.Coprime p.val (Nat.card K) :=
    Nat.Coprime.coprime_dvd_left hpHdiv hcop
  exact ((p.property.coprime_iff_not_dvd).1 hpKcop) hpK

private theorem section13_frobenius_complement_centralizerIn_eq_bot
    {G : Type u} [Group G] [Finite G]
    {K R : Subgroup G} [K.Normal]
    (hcomp : K.IsComplement' R)
    (hcent : ∀ r : R, r ≠ 1 → Section2.centralizerIn K (r : G) = ⊥)
    {x : G} (hxnotK : x ∉ K) :
    Section2.centralizerIn K x = ⊥ := by
  classical
  have hxSup : x ∈ K ⊔ R := by
    simp [hcomp.sup_eq_top]
  rcases (Subgroup.mem_sup_of_normal_left (s := K) (t := R) (x := x)).1 hxSup with
    ⟨k, hkK, r, hrR, hkr⟩
  let rR : R := ⟨r, hrR⟩
  have hrne : rR ≠ 1 := by
    intro hr1
    apply hxnotK
    rw [← hkr]
    have hr_eq : r = 1 := by simpa [rR] using congrArg Subtype.val hr1
    simp [hr_eq, hkK]
  let f : K → K := fun a =>
    ⟨(a : G) * r * (a : G)⁻¹ * r⁻¹, by
      have hconjK : r * (a : G)⁻¹ * r⁻¹ ∈ K :=
        (inferInstance : K.Normal).conj_mem ((a : G)⁻¹) (K.inv_mem a.2) r
      simpa [mul_assoc] using K.mul_mem a.2 hconjK⟩
  have hf_inj : Function.Injective f := by
    intro a b hab
    have habG : (a : G) * r * (a : G)⁻¹ * r⁻¹ =
        (b : G) * r * (b : G)⁻¹ * r⁻¹ := congrArg Subtype.val hab
    have hcomm : (b : G)⁻¹ * (a : G) * r = r * ((b : G)⁻¹ * (a : G)) := by
      have hab1 : (a : G) * r * (a : G)⁻¹ = (b : G) * r * (b : G)⁻¹ := by
        simpa [mul_assoc] using congrArg (fun t : G => t * r) habG
      have hab2 := congrArg (fun t : G => (b : G)⁻¹ * t * (a : G)) hab1
      simpa [mul_assoc] using hab2
    let c : K := ⟨(b : G)⁻¹ * (a : G), K.mul_mem (K.inv_mem b.2) a.2⟩
    have hcCent : (c : G) ∈ Section2.centralizerIn K (rR : G) := by
      refine ⟨c.2, ?_⟩
      change (c : G) ∈ Subgroup.centralizer ({(rR : G)} : Set G)
      exact Subgroup.mem_centralizer_singleton_iff.mpr (by simpa [c, rR] using hcomm)
    have hcBot : (c : G) ∈ (⊥ : Subgroup G) := by
      simpa [hcent rR hrne] using hcCent
    have hc_eq : (c : G) = 1 := by simpa using hcBot
    apply Subtype.ext
    have := congrArg (fun t : G => (b : G) * t) hc_eq
    simpa [c, mul_assoc] using this
  have hf_surj : Function.Surjective f := Finite.surjective_of_injective hf_inj
  rcases hf_surj ⟨k, hkK⟩ with ⟨a, ha⟩
  have haG : (a : G) * r * (a : G)⁻¹ * r⁻¹ = k := congrArg Subtype.val ha
  have hconj_x : (a : G)⁻¹ * x * (a : G) = r := by
    rw [← hkr]
    have hk_eq : k = (a : G) * r * (a : G)⁻¹ * r⁻¹ := haG.symm
    rw [hk_eq]
    group
  have hx_a : x * (a : G) = (a : G) * r := by
    calc
      x * (a : G) = (a : G) * ((a : G)⁻¹ * x * (a : G)) := by group
      _ = (a : G) * r := by rw [hconj_x]
  rw [Subgroup.eq_bot_iff_forall]
  intro y hy
  rcases hy with ⟨hyK, hycent⟩
  have hycomm : y * x = x * y := by
    simpa [Section2.elementCentralizer] using Subgroup.mem_centralizer_singleton_iff.mp hycent
  let z : K := ⟨(a : G)⁻¹ * y * (a : G), by
    simpa using (inferInstance : K.Normal).conj_mem y hyK (a : G)⁻¹⟩
  have hzComm : (z : G) * r = r * (z : G) := by
    calc
      (z : G) * r = ((a : G)⁻¹ * y * (a : G)) * r := rfl
      _ = (a : G)⁻¹ * y * ((a : G) * r) := by group
      _ = (a : G)⁻¹ * y * (x * (a : G)) := by rw [hx_a]
      _ = (a : G)⁻¹ * (y * x) * (a : G) := by group
      _ = (a : G)⁻¹ * (x * y) * (a : G) := by rw [hycomm]
      _ = ((a : G)⁻¹ * x * (a : G)) * ((a : G)⁻¹ * y * (a : G)) := by group
      _ = r * (z : G) := by rw [hconj_x]
  have hzCent : (z : G) ∈ Section2.centralizerIn K (rR : G) := by
    refine ⟨z.2, ?_⟩
    change (z : G) ∈ Subgroup.centralizer ({(rR : G)} : Set G)
    exact Subgroup.mem_centralizer_singleton_iff.mpr (by simpa [rR] using hzComm)
  have hzBot : (z : G) ∈ (⊥ : Subgroup G) := by
    simpa [hcent rR hrne] using hzCent
  have hz_eq : (z : G) = 1 := by simpa using hzBot
  have hy_eq : y = 1 := by
    have := congrArg (fun t : G => (a : G) * t * (a : G)⁻¹) hz_eq
    simpa [z, mul_assoc] using this
  simp [hy_eq]

public theorem section13_frobeniusWithKernel_centralizerIn_eq_bot_of_not_mem
    {G : Type u} [Group G] [Finite G] {L H : Subgroup G}
    (hfrob : Section7.frobeniusWithKernel L H) :
    ∀ x : G, x ∈ L → x ∉ H → Section2.centralizerIn H x = ⊥ := by
  intro x hxL hxnotH
  rcases hfrob with ⟨hHL, hHnormal, R, hcomp, _hHne, _hRne, hfixedR⟩
  let Hloc : Subgroup L := H.subgroupOf L
  let : Hloc.Normal := by simpa [Hloc] using hHnormal
  let xL : L := ⟨x, hxL⟩
  have hxnotHloc : xL ∉ Hloc := by
    intro hxHloc
    exact hxnotH (by simpa [Hloc, xL, Subgroup.mem_subgroupOf] using hxHloc)
  have hloc : Section2.centralizerIn Hloc xL = ⊥ :=
    section13_frobenius_complement_centralizerIn_eq_bot
      (K := Hloc) (R := R) hcomp hfixedR hxnotHloc
  rw [Subgroup.eq_bot_iff_forall]
  intro y hy
  rcases hy with ⟨hyH, hycent⟩
  have hyL : y ∈ L := hHL hyH
  let yL : L := ⟨y, hyL⟩
  have hyLoc : yL ∈ Section2.centralizerIn Hloc xL := by
    refine ⟨?_, ?_⟩
    · simpa [Hloc, yL, Subgroup.mem_subgroupOf] using hyH
    · change yL ∈ Subgroup.centralizer ({xL} : Set L)
      have hycomm : y * x = x * y := by
        simpa [Section2.elementCentralizer] using Subgroup.mem_centralizer_singleton_iff.mp hycent
      exact Subgroup.mem_centralizer_singleton_iff.mpr (by
        apply Subtype.ext
        exact hycomm)
  have hyBot : (yL : L) ∈ (⊥ : Subgroup L) := by
    simpa [hloc] using hyLoc
  have hy_eq : y = 1 := by
    simpa [yL] using congrArg Subtype.val (by simpa using hyBot : yL = 1)
  simp [hy_eq]

private theorem section13_complementIn_of_isComplement'_subgroupOf
    {G : Type u} [Group G]
    {D H : Subgroup G} (hHD : H ≤ D) (Vloc : Subgroup D)
    (hcomp : (H.subgroupOf D).IsComplement' Vloc) :
    section12ComplementIn D H (section8SubgroupInAmbient Vloc) := by
  classical
  refine ⟨hHD, section8SubgroupInAmbient_le Vloc, ?_, ?_⟩
  · apply le_antisymm
    · intro x hxD
      let xD : D := ⟨x, hxD⟩
      have hxTop : xD ∈ (⊤ : Subgroup D) := by simp
      have hxSup : xD ∈ H.subgroupOf D ⊔ Vloc := by
        simp [hcomp.sup_eq_top, hxTop]
      have hxSub : xD ∈ (H ⊔ section8SubgroupInAmbient Vloc).subgroupOf D := by
        have hsub_eq :
            (H ⊔ section8SubgroupInAmbient Vloc).subgroupOf D =
              H.subgroupOf D ⊔ Vloc := by
          calc
            (H ⊔ section8SubgroupInAmbient Vloc).subgroupOf D =
                H.subgroupOf D ⊔ (section8SubgroupInAmbient Vloc).subgroupOf D := by
              exact Subgroup.subgroupOf_sup (A := H)
                (A' := section8SubgroupInAmbient Vloc) (B := D)
                hHD (section8SubgroupInAmbient_le Vloc)
            _ = H.subgroupOf D ⊔ Vloc := by
              rw [section8SubgroupInAmbient_subgroupOf_eq]
        simpa [hsub_eq] using hxSup
      simpa [xD, Subgroup.mem_subgroupOf] using hxSub
    · exact sup_le hHD (section8SubgroupInAmbient_le Vloc)
  · rw [Subgroup.disjoint_def]
    intro x hxH hxV
    let xD : D := ⟨x, hHD hxH⟩
    have hxHloc : xD ∈ H.subgroupOf D := by
      simpa [xD, Subgroup.mem_subgroupOf] using hxH
    have hxVloc : xD ∈ Vloc := by
      have hxVsub : xD ∈ (section8SubgroupInAmbient Vloc).subgroupOf D := by
        simpa [xD, Subgroup.mem_subgroupOf] using hxV
      simpa [section8SubgroupInAmbient_subgroupOf_eq] using hxVsub
    have hxbot : xD ∈ (⊥ : Subgroup D) :=
      Subgroup.disjoint_def.mp hcomp.disjoint hxHloc hxVloc
    have hxbot_val : (xD : G) = (1 : G) :=
      congrArg Subtype.val (by simpa using hxbot)
    simpa [xD] using hxbot_val


private theorem section13_subgroupOf_ne_bot_of_ne_bot
    {G : Type u} [Group G] {H L : Subgroup G}
    (hHL : H ≤ L) (hHne : H ≠ ⊥) :
    H.subgroupOf L ≠ ⊥ := by
  intro hbot
  apply hHne
  apply le_antisymm
  · intro x hx
    have hxloc : (⟨x, hHL hx⟩ : L) ∈ H.subgroupOf L := by
      simpa [Subgroup.mem_subgroupOf]
    have hxbot : (⟨x, hHL hx⟩ : L) ∈ (⊥ : Subgroup L) := by
      simpa [hbot] using hxloc
    have hx_eq : x = 1 := by
      exact congrArg Subtype.val (by simpa using hxbot : (⟨x, hHL hx⟩ : L) = 1)
    simp [hx_eq]
  · exact bot_le

private theorem section13_centralizerIn_subgroupOf_eq_bot_of_ambient
    {G : Type u} [Group G] {L H : Subgroup G}
    (_hHL : H ≤ L) {x : L}
    (hcent : Section2.centralizerIn H (x : G) = ⊥) :
    Section2.centralizerIn (H.subgroupOf L) x = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro y hy
  have hyH : (y : G) ∈ H := by
    simpa [Subgroup.mem_subgroupOf] using hy.1
  have hycent : (y : G) ∈ Section2.centralizerIn H (x : G) := by
    refine ⟨hyH, ?_⟩
    change (y : G) ∈ Subgroup.centralizer ({(x : G)} : Set G)
    have hycommL := Subgroup.mem_centralizer_singleton_iff.mp hy.2
    exact Subgroup.mem_centralizer_singleton_iff.mpr (congrArg Subtype.val hycommL)
  have hybot : (y : G) ∈ (⊥ : Subgroup G) := by
    simpa [hcent] using hycent
  apply Subtype.ext
  simpa using hybot

private theorem section13_frobeniusWithKernel_complementIn_isFrobenius
    {G : Type u} [Group G] [Finite G] {L H E : Subgroup G}
    (hfrob : Section7.frobeniusWithKernel L H)
    (hcompE : section12ComplementIn L H E)
    (hEne : E ≠ ⊥) :
    IsFrobeniusGroupWithKernelComplement (H.subgroupOf L) (E.subgroupOf L) := by
  rcases hfrob with ⟨_hHL, hHnormal, _R, _hcompR, hHne, _hRne, _hfixedR⟩
  let Hloc : Subgroup L := H.subgroupOf L
  let Eloc : Subgroup L := E.subgroupOf L
  have hHlocne : Hloc ≠ ⊥ := by simpa [Hloc] using hHne
  have hElocne : Eloc ≠ ⊥ :=
    section13_subgroupOf_ne_bot_of_ne_bot hcompE.2.1 hEne
  let : Hloc.Normal := by simpa [Hloc] using hHnormal
  have hHnorm : section10NormalIn H L := ⟨_hHL, hHnormal⟩
  have hcompLoc : Hloc.IsComplement' Eloc := by
    simpa [Hloc, Eloc] using
      (section13_complementIn_of_normal_isComplement' hcompE hHnorm).symm
  refine (lemma_3_1 Hloc Eloc hHlocne hElocne inferInstance hcompLoc).2 ?_
  intro e he_ne
  have he_not_H : ((e : L) : G) ∉ H := by
    intro heH
    have heE : ((e : L) : G) ∈ E := by
      exact Subgroup.mem_subgroupOf.mp (by simp [Eloc, e.property])
    have heInf : ((e : L) : G) ∈ H ⊓ E := ⟨heH, heE⟩
    have heBot : ((e : L) : G) ∈ (⊥ : Subgroup G) := by
      simpa [hcompE.2.2.2.eq_bot] using heInf
    have he_eq_one : e = 1 := by
      apply Subtype.ext
      apply Subtype.ext
      simpa using heBot
    exact he_ne he_eq_one
  exact section13_centralizerIn_subgroupOf_eq_bot_of_ambient _hHL
    (section13_frobeniusWithKernel_centralizerIn_eq_bot_of_not_mem
      ⟨_hHL, hHnormal, _R, _hcompR, hHne, _hRne, _hfixedR⟩
      ((e : L) : G) (e : L).property he_not_H)

private theorem section13_containing_complement_of_solvable_mf
    {G : Type u} [Group G] [Finite G]
    {L H K : Subgroup G}
    (hMF : section16MFSubgroup L H)
    (hsolvL : Group.IsSolvable L)
    (hKleL : K ≤ L)
    (hKinfH : K ⊓ H = ⊥) :
    ∃ E : Subgroup G, section12ComplementIn L H E ∧ K ≤ E := by
  classical
  letI : MulDistribMulAction Unit L := {
    smul := fun _ x => x
    one_smul := fun _ => rfl
    mul_smul := fun _ _ _ => rfl
    smul_mul := fun _ _ _ => rfl
    smul_one := fun _ => rfl }
  let Hloc : Subgroup L := H.subgroupOf L
  let Kloc : Subgroup L := K.subgroupOf L
  have hHleL : H ≤ L := Section12.section16MFSubgroup_le hMF
  have hKdisj : Disjoint K H := by
    rw [Subgroup.disjoint_def]
    intro x hxK hxH
    have hxInf : x ∈ K ⊓ H := ⟨hxK, hxH⟩
    have hxBot : x ∈ (⊥ : Subgroup G) := by
      simpa [hKinfH] using hxInf
    simpa using hxBot
  have hKcop : Nat.Coprime (Nat.card H) (Nat.card K) :=
    section13_coprime_card_of_mf_subgroup_disjoint hMF hKleL hKdisj
  have hKloc_card : Nat.card Kloc = Nat.card K := by
    simpa [Kloc] using natCard_subgroupOf_eq K L hKleL
  have hKlocπ : IsPiSubgroup (G := L) (subgroupPrimeSet H)ᶜ Kloc := by
    apply section13_isPiSubgroup_primeSet_compl_of_coprime_card (H := H) (K := Kloc)
    rw [hKloc_card]
    exact hKcop
  have hKlocInv : IsInvariant Unit L Kloc := by
    refine ⟨?_⟩
    intro _ x
    simp [Kloc]
  have hcopUnit : Nat.Coprime (Nat.card Unit) (Nat.card L) := by
    simp
  obtain ⟨Eloc, hEHall, _hEInv, hKlocE⟩ :=
    exists_isHallSubgroup_isInvariant_of_isPiSubgroup
      (G := L) (A := Unit) hsolvL hcopUnit (subgroupPrimeSet H)ᶜ
      Kloc hKlocπ hKlocInv
  have hHlocHall : IsHallSubgroup (subgroupPrimeSet H) Hloc := by
    simpa [Hloc] using Section12.section16MFSubgroup_subgroupOf_isHall hMF
  have hcompLoc : Hloc.IsComplement' Eloc :=
    section11_isComplement_of_isHall_compl hHlocHall hEHall
  refine ⟨section8SubgroupInAmbient Eloc,
    section13_complementIn_of_isComplement'_subgroupOf hHleL Eloc ?_, ?_⟩
  · simpa [Hloc] using hcompLoc
  · intro x hxK
    exact Subgroup.mem_map.mpr
      ⟨⟨x, hKleL hxK⟩,
        hKlocE (show (⟨x, hKleL hxK⟩ : L) ∈ Kloc from by
          simpa [Kloc, Subgroup.mem_subgroupOf] using hxK),
        rfl⟩

private theorem section13_le_normalizer_of_subgroupOf_normal
    {G : Type u} [Group G]
    {E K : Subgroup G}
    (hKE : K ≤ E)
    (hKnormal : (K.subgroupOf E).Normal) :
    E ≤ Subgroup.normalizer (K : Set G) :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer (H := K) (K := E) hKE).1 hKnormal

private theorem section13_coprime_card_of_prime_not_mem_subgroupPrimeSet
    {G : Type u} [Group G] [Finite G] {H : Subgroup G} {q : ℕ}
    (hq : Nat.Prime q)
    (hnot : (⟨q, hq⟩ : Nat.Primes) ∉ subgroupPrimeSet H) :
    Nat.Coprime (Nat.card H) q := by
  rw [Nat.coprime_comm]
  exact (hq.coprime_iff_not_dvd).2 (by
    intro hdiv
    have hmem : (⟨q, hq⟩ : Nat.Primes) ∈ subgroupPrimeSet H := by
      apply Set.mem_setOf.mpr
      simpa using hdiv
    exact hnot hmem)

private theorem section13_subgroupPrimeSet_section10Msigma_eq
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    {M : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G) :
    subgroupPrimeSet (section10Msigma M) = section10SigmaPrimes M := by
  classical
  ext p
  constructor
  · intro hp
    exact (section10_msigma_isHall (G := G) hM).p_in_pi_of_p_dvd_card p (by
      simpa [subgroupPrimeSet] using hp)
  · intro hpσ
    have hpMset : p ∈ subgroupPrimeSet M := by
      exact (show p ∈ subgroupPrimeSet M ∧
        ∃ P : Sylow p.val M,
          Subgroup.normalizer (section10AmbientSylowSubgroup M P : Set G) ≤ M from by
          simpa [section10SigmaPrimes] using hpσ).1
    have hpM : p.val ∣ Nat.card M := by
      simpa [subgroupPrimeSet] using hpMset
    have hKHall : IsHallSubgroup (section10SigmaPrimes M) (section10MsigmaSubgroup M) :=
      section10_msigmaSubgroup_isHall (G := G) hM
    have hprod :
        p.val ∣ (section10MsigmaSubgroup M).index *
          Nat.card (section10MsigmaSubgroup M) := by
      rw [← Subgroup.index_mul_card (H := section10MsigmaSubgroup M)] at hpM
      exact hpM
    rcases p.property.dvd_or_dvd hprod with hpidx | hpcard
    · exact False.elim ((hKHall.p_in_pi_of_p_dvd_index p hpidx) hpσ)
    · have hcard_eq : Nat.card (section10Msigma M) =
          Nat.card (section10MsigmaSubgroup M) := by
        simpa [section10Msigma] using
          (Subgroup.card_map_of_injective
            (K := section10MsigmaSubgroup M) (f := M.subtype) M.subtype_injective)
      exact by
        rw [subgroupPrimeSet]
        change p.val ∣ Nat.card (section10Msigma M)
        rw [hcard_eq]
        exact hpcard

private theorem section13_subgroupPrimeSet_msChoiceSource_eq_sigma
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    {M MF Ms : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMF : section16MFSubgroup M MF)
    (hMs : Section8.msChoiceSource M MF Ms) :
    subgroupPrimeSet Ms = section10SigmaPrimes M := by
  have hMs_eq : Ms = section10Msigma M :=
    Section8.theorem_8_11_msChoiceSource_eq_msigma (G := G) hM hMF hMs
  rw [hMs_eq]
  exact section13_subgroupPrimeSet_section10Msigma_eq (G := G) hM

private theorem section13_mf_le_msChoiceSource_of_typeP
    {G : Type u} [Group G] [Finite G]
    {M MF U W1 W2 Ms : Subgroup G}
    (hP : Section8.typePDefinitionData M MF U W1 W2)
    (hMs : Section8.msChoiceSource M MF Ms) :
    MF ≤ Ms := by
  rcases hP with
    ⟨_hMF, _hW1cyc, _hW1ne, _hW1hall, _hCompM, _hUle, _hUnil,
      _hW1norm, hCompD, _hMFnotcyc, _hsecond, _hfit, _hfitD,
      _hW2le, _hW2cyc, _hW2ne, _hcent, _hnormHat⟩
  have hMFleD : MF ≤ ambientDerivedSubgroup M := hCompD.1
  rcases hMs with hI | hII | hIII | hIV | hV
  · rcases hI with ⟨_hI, _hnotII, _hnotIII, _hnotIV, _hnotV, hMs_eq⟩
    simp [hMs_eq]
  · rcases hII with ⟨_hnotI, _hII, _hnotIII, _hnotIV, _hnotV, hMs_eq⟩
    simp [hMs_eq]
  · rcases hIII with ⟨_hnotI, _hnotII, _hIII, _hnotIV, _hnotV, hMs_eq⟩
    simp [hMs_eq]
    exact hMFleD
  · rcases hIV with ⟨_hnotI, _hnotII, _hnotIII, _hIV, _hnotV, hMs_eq⟩
    simp [hMs_eq]
    exact hMFleD
  · rcases hV with ⟨_hnotI, _hnotII, _hnotIII, _hnotIV, _hV, hMs_eq⟩
    simp [hMs_eq]


public theorem section13_coprime_card_typeI_mf_of_typeP_prime
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    {L H M MF U W1 W2 K : Subgroup G} {r : ℕ}
    (hChoice : hypothesis_13_1_sourceChoiceData G)
    (hLmax : L ∈ section9MaximalSubgroups G)
    (hHMF : section16MFSubgroup L H)
    (hTypeI : Section8.typeIDefinitionData L H)
    (hMmax : M ∈ section9MaximalSubgroups G)
    (hMMF : section16MFSubgroup M MF)
    (hTypeP : Section8.typePDefinitionData M MF U W1 W2)
    (hMtypes : Section8.typeIIDefinitionData M MF ∨
      Section8.typeIIIDefinitionData M MF ∨
        Section8.typeIVDefinitionData M MF ∨
          Section8.typeVDefinitionData M MF)
    (hKle : K ≤ MF)
    (hr : Nat.Prime r)
    (hKcard : Nat.card K = r) :
    Nat.Coprime (Nat.card H) r := by
  classical
  rcases hChoice L H hLmax hHMF (Or.inl hTypeI) with ⟨MsL, hMsL⟩
  have hMsL_eq : MsL = H :=
    Section8.msChoiceSource_eq_mf_of_typeI hMsL hTypeI
  have hHsigmaL : subgroupPrimeSet H = section10SigmaPrimes L := by
    calc
      subgroupPrimeSet H = subgroupPrimeSet MsL := by rw [hMsL_eq]
      _ = section10SigmaPrimes L :=
        section13_subgroupPrimeSet_msChoiceSource_eq_sigma
          (G := G) hLmax hHMF hMsL
  rcases hChoice M MF hMmax hMMF (Or.inr hMtypes) with ⟨MsM, hMsM⟩
  have hMFleMsM : MF ≤ MsM :=
    section13_mf_le_msChoiceSource_of_typeP hTypeP hMsM
  have hrMsM : (⟨r, hr⟩ : Nat.Primes) ∈ subgroupPrimeSet MsM := by
    rw [subgroupPrimeSet]
    change r ∣ Nat.card MsM
    have hdiv : Nat.card K ∣ Nat.card MsM :=
      (Subgroup.card_dvd_of_le hKle).trans
        (Subgroup.card_dvd_of_le hMFleMsM)
    rw [← hKcard]
    exact hdiv
  have hrSigmaM : (⟨r, hr⟩ : Nat.Primes) ∈ section10SigmaPrimes M := by
    have hMsMsigma : subgroupPrimeSet MsM = section10SigmaPrimes M :=
      section13_subgroupPrimeSet_msChoiceSource_eq_sigma
        (G := G) hMmax hMMF hMsM
    simpa [hMsMsigma] using hrMsM
  have hnotConjML : section12NotConjugate M L := by
    intro g hconj
    have hHMFconj : section16MFSubgroup (M.conjBy g) H := by
      simpa [hconj] using hHMF
    have hTypeIconj : Section8.typeIDefinitionData (M.conjBy g) H := by
      simpa [hconj] using hTypeI
    exact Section8.not_typeIDefinitionData_of_typeP_source_data hTypeP
      (Section8.theorem_8_18_typeIDefinitionData_conj_back
        (G := G) (M := M) (MF := MF) (LF := H) g
        hMMF hHMFconj hTypeIconj)
  have hdis :
      Disjoint (section10SigmaPrimes L) (section10SigmaPrimes M) :=
    _root_.CFSG.theorem_13_9 (G := G) hLmax hMmax hnotConjML
  have hrNotH : (⟨r, hr⟩ : Nat.Primes) ∉ subgroupPrimeSet H := by
    intro hrH
    have hrSigmaL : (⟨r, hr⟩ : Nat.Primes) ∈ section10SigmaPrimes L := by
      simpa [hHsigmaL] using hrH
    exact (Set.disjoint_left.mp hdis) hrSigmaL hrSigmaM
  rw [Nat.coprime_comm]
  exact (hr.coprime_iff_not_dvd).2 (by
    intro hrH
    have hmem : (⟨r, hr⟩ : Nat.Primes) ∈ subgroupPrimeSet H := by
      apply Set.mem_setOf.mpr
      simpa using hrH
    exact hrNotH hmem)

private theorem section13_subgroupPrimeSet_conjBy
    {G : Type u} [Group G] [Finite G] (H : Subgroup G) (g : G) :
    subgroupPrimeSet (H.conjBy g) = subgroupPrimeSet H := by
  ext p
  constructor
  · intro hp
    rw [subgroupPrimeSet] at hp ⊢
    change p.val ∣ Nat.card H
    rw [← section11_card_conjBy (G := G) H g]
    exact hp
  · intro hp
    rw [subgroupPrimeSet] at hp ⊢
    change p.val ∣ Nat.card (H.conjBy g)
    rw [section11_card_conjBy (G := G) H g]
    exact hp

private theorem section13_section16NilpotentNormalHallIn_conjBy
    {G : Type u} [Group G] [Finite G]
    {H M : Subgroup G} (g : G)
    (hH : section16NilpotentNormalHallIn H M) :
    section16NilpotentNormalHallIn (H.conjBy g) (M.conjBy g) := by
  classical
  rcases hH with ⟨hHM, hHnormal, hHnil, hHHall⟩
  have hHMg : H.conjBy g ≤ M.conjBy g := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨y, hyH, hyx⟩
    exact Subgroup.mem_map.mpr ⟨y, hHM hyH, hyx⟩
  refine ⟨hHMg, ?_, ?_, ?_⟩
  · have hMleNormH : M ≤ Subgroup.normalizer (H : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hHM).1 hHnormal
    refine (Subgroup.normal_subgroupOf_iff_le_normalizer hHMg).2 ?_
    intro x hxM
    rcases Subgroup.mem_map.mp hxM with ⟨m, hmM, hmx⟩
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      rcases Subgroup.mem_map.mp hy with ⟨h, hhH, hhy⟩
      refine Subgroup.mem_map.mpr ⟨m * h * m⁻¹, ?_, ?_⟩
      · exact (Subgroup.mem_normalizer_iff.mp (hMleNormH hmM) h).1 hhH
      · change g * (m * h * m⁻¹) * g⁻¹ = x * y * x⁻¹
        calc
          g * (m * h * m⁻¹) * g⁻¹ =
              (MulAut.conj g).toMonoidHom m * (MulAut.conj g).toMonoidHom h *
                ((MulAut.conj g).toMonoidHom m)⁻¹ := by
                simp [MulAut.conj_apply]
                group
          _ = x * y * x⁻¹ := by rw [hmx, hhy]
    · intro hy
      rcases Subgroup.mem_map.mp hy with ⟨h, hhH, hhy⟩
      refine Subgroup.mem_map.mpr ⟨m⁻¹ * h * m, ?_, ?_⟩
      · have hmNorm : m ∈ Subgroup.normalizer (H : Set G) := hMleNormH hmM
        have hminvNorm : m⁻¹ ∈ Subgroup.normalizer (H : Set G) :=
          (Subgroup.normalizer (H : Set G)).inv_mem hmNorm
        simpa using (Subgroup.mem_normalizer_iff.mp hminvNorm h).1 hhH
      · change g * (m⁻¹ * h * m) * g⁻¹ = y
        calc
          g * (m⁻¹ * h * m) * g⁻¹ =
              ((MulAut.conj g).toMonoidHom m)⁻¹ *
                (MulAut.conj g).toMonoidHom h *
                  (MulAut.conj g).toMonoidHom m := by
                simp [MulAut.conj_apply]
                group
          _ = x⁻¹ * (x * y * x⁻¹) * x := by rw [hmx, hhy]
          _ = y := by group
  · let e : H ≃* H.conjBy g := (MulAut.conj g).subgroupMap H
    exact Group.nilpotent_of_mulEquiv (G := H) (G' := H.conjBy g) e
  · have hcardSub :
        Nat.card ((H.conjBy g).subgroupOf (M.conjBy g)) = Nat.card (H.subgroupOf M) := by
      calc
        Nat.card ((H.conjBy g).subgroupOf (M.conjBy g))
            = Nat.card (H.conjBy g) :=
              natCard_subgroupOf_eq (H.conjBy g) (M.conjBy g) hHMg
        _ = Nat.card H := section11_card_conjBy (G := G) H g
        _ = Nat.card (H.subgroupOf M) := (natCard_subgroupOf_eq H M hHM).symm
    have hindexSub :
        ((H.conjBy g).subgroupOf (M.conjBy g)).index = (H.subgroupOf M).index := by
      have hmulConj :
          ((H.conjBy g).subgroupOf (M.conjBy g)).index *
              Nat.card (H.subgroupOf M) =
            Nat.card M := by
        calc
          ((H.conjBy g).subgroupOf (M.conjBy g)).index *
              Nat.card (H.subgroupOf M)
              = ((H.conjBy g).subgroupOf (M.conjBy g)).index *
                  Nat.card ((H.conjBy g).subgroupOf (M.conjBy g)) := by
                    rw [hcardSub]
          _ = Nat.card (M.conjBy g) :=
                Subgroup.index_mul_card (H := (H.conjBy g).subgroupOf (M.conjBy g))
          _ = Nat.card M := section11_card_conjBy (G := G) M g
      have hmulOrig :
          (H.subgroupOf M).index * Nat.card (H.subgroupOf M) = Nat.card M :=
        Subgroup.index_mul_card (H := H.subgroupOf M)
      exact Nat.mul_right_cancel (Nat.card_pos (α := H.subgroupOf M))
        (hmulConj.trans hmulOrig.symm)
    rw [section13_subgroupPrimeSet_conjBy (G := G) H g]
    refine isHallSubgroup_of (G := M.conjBy g)
      (π := subgroupPrimeSet H) (H := (H.conjBy g).subgroupOf (M.conjBy g))
      ?_ ?_
    · intro p hp
      apply hHHall.p_in_pi_of_p_dvd_card p
      rw [← hcardSub]
      exact hp
    · intro p hpπ hpidx
      exact (hHHall.p_in_pi_of_p_dvd_index p (by
        rw [← hindexSub]
        exact hpidx)) hpπ

private theorem section13_section16MFSubgroup_conjBy
    {G : Type u} [Group G] [Finite G]
    {M MF : Subgroup G} (hMF : section16MFSubgroup M MF) (g : G) :
    section16MFSubgroup (M.conjBy g) (MF.conjBy g) := by
  classical
  refine ⟨section13_section16NilpotentNormalHallIn_conjBy g hMF.1, ?_⟩
  intro H hH
  have hback : section16NilpotentNormalHallIn (H.conjBy g⁻¹) M := by
    have htmp := section13_section16NilpotentNormalHallIn_conjBy (G := G) g⁻¹ hH
    simpa [section11_conjBy_inv] using htmp
  have hle_back : H.conjBy g⁻¹ ≤ MF := hMF.2 (H.conjBy g⁻¹) hback
  simpa using
    (section11_le_conjBy_inv_of_conjBy_le
      (G := G) (H := H) (K := MF) (g := g⁻¹) hle_back)

/-- Source/current-witness bridge for PF `(13.17)(a)`: in the Type-II branch,
the `U` fixed by the Section 13 source context is the Type-II subgroup whose
normalizer is not contained in `Smax`. -/
private theorem section13_theorem_13_17_current_typeII_not_normalizer_sourceContext
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (_hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (_hTypeII : Section8.typeIIDefinitionData Smax P) :
    ¬ Subgroup.normalizer (U : Set G) ≤ Smax := by
  exact section13_theorem_13_2_current_typeII_not_normalizer_of_sourceContext
    Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
    p q u v c d _hsource _hTypeII

/-- Source blocker for the first nonconjugacy exclusion in PF `(13.17)(a)`.
The TeX proof uses Hall conjugacy inside the solvable subgroup `Smax` to
transfer `N_G(U) ≤ L` to `N_G(U) ≤ Smax`, contradicting Type II. -/
private theorem section13_theorem_13_17_L_not_conj_Smax_of_sourceContext
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D L H : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (_hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (_hTypeII : Section8.typeIIDefinitionData Smax P)
    (_hLmax : L ∈ section9MaximalSubgroups G)
    (_hNormUleL : Subgroup.normalizer (U : Set G) ≤ L)
    (_hMF : section16MFSubgroup L H) :
    ∀ g : G, L ≠ Smax.conjBy g := by
  intro g hL
  have hnotNorm :
      ¬ Subgroup.normalizer (U : Set G) ≤ Smax :=
    section13_theorem_13_17_current_typeII_not_normalizer_sourceContext
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
      p q u v c d _hsource _hTypeII
  have hS : Smax = L.conjBy g⁻¹ := by
    calc
      Smax = (Smax.conjBy g).conjBy g⁻¹ := (Subgroup.conjBy_inv Smax g).symm
      _ = L.conjBy g⁻¹ := by rw [← hL]
  obtain ⟨x, hxS, hxU⟩ :=
    section13_theorem_13_17_hall_conj_witness_of_L_conj_Smax_sourceContext
      Smax Tmax W W1 W2 P Q U V C D L Sfam Tfam τS τT
      p q u v c d _hsource hS _hNormUleL
  exact hnotNorm
    (section13_normalizer_le_of_conj_hall_witness hS hxS hxU _hNormUleL)


private theorem section13_theorem_13_17_H_card_eq_q_pow_p_of_L_conj_Tmax_sourceContext
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D L H : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (_hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (_hMF : section16MFSubgroup L H)
    {g : G} (hL : L = Tmax.conjBy g) :
    Nat.card H = q ^ p := by
  have hsourceT :=
    section13_hypothesis_13_1_sourceData_swap (G := G) _hsource
  rcases theorem_13_2 Tmax Smax W W2 W1 Q P V U D C
      Tfam Sfam τT τS q p v u d c hsourceT with
    ⟨hQMF, _hType, _hTypeIf, _hVcomm, _hfrobVW2, _hQelem, hQcard,
      _hvBound, _hcohT, _hTIT, _hTauT, _hnormT⟩
  have hQconjMF : section16MFSubgroup L (Q.conjBy g) := by
    have htmp := section13_section16MFSubgroup_conjBy (G := G) hQMF g
    simpa [← hL] using htmp
  have hH_eq : H = Q.conjBy g :=
    section16MFSubgroup_unique _hMF hQconjMF
  calc
    Nat.card H = Nat.card (Q.conjBy g) := by rw [hH_eq]
    _ = Nat.card Q := section11_card_conjBy (G := G) Q g
    _ = q ^ p := hQcard

private theorem section13_theorem_13_17_U_coprime_q_of_sourceContext
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (_hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d) :
    Nat.Coprime (Nat.card U) q := by
  rcases _hsource with
    ⟨_hcaseB, hptypeS, _hptypeT, _hp, hq_card, _hC, _hD, _hc, _hd,
      _hUcard, _hVcard, _hSfam, _hTfam, _hDadeS, _hDadeT,
      _hnotationData, _hDadeDiff, _hZeroDegree, _hConjIndex, _hConjBetaTau,
      _hChoice, _hMin, _hFourSixS, _hFourSixT⟩
  have hptypeSOrig := hptypeS
  rcases hptypeS with
    ⟨_hMF, _hW1cyc, _hW1ne, _hW1Hall, _hMcomp, hUleD, _hUnil, _hW1normU,
      _hDercomp, _hMFnotcyc, _hsecond, _hfit, _hfitDer, _hW2le, _hW2cyc,
      _hW2ne, _hcent, _hnorm⟩
  have hcopW1D :
      Nat.Coprime (Nat.card W1) (Nat.card (ambientDerivedSubgroup Smax)) :=
    Section9.typePDefinitionData_W1_card_coprime_ambientDerived_sec9 hptypeSOrig
  have hcopW1U : Nat.Coprime (Nat.card W1) (Nat.card U) :=
    Nat.Coprime.of_dvd_right (Subgroup.card_dvd_of_le hUleD) hcopW1D
  simpa [hq_card] using hcopW1U.symm

private theorem section13_theorem_13_17_UinfH_eq_bot_of_L_conj_Tmax_sourceContext
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D L H : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (_hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (_hMF : section16MFSubgroup L H)
    {g : G} (hL : L = Tmax.conjBy g) :
    U ⊓ H = ⊥ := by
  have hHcard :
      Nat.card H = q ^ p :=
    section13_theorem_13_17_H_card_eq_q_pow_p_of_L_conj_Tmax_sourceContext
      Smax Tmax W W1 W2 P Q U V C D L H Sfam Tfam τS τT
      p q u v c d _hsource _hMF hL
  have hUq :
      Nat.Coprime (Nat.card U) q :=
    section13_theorem_13_17_U_coprime_q_of_sourceContext
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
      p q u v c d _hsource
  have hUH : Nat.Coprime (Nat.card U) (Nat.card H) := by
    rw [hHcard]
    exact hUq.pow_right p
  exact (Subgroup.disjoint_of_coprime_natCard hUH).eq_bot

private theorem section13_theorem_13_17_W1_le_H_of_L_conj_Tmax_sourceContext
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D L H : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (_hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (_hNormUleL : Subgroup.normalizer (U : Set G) ≤ L)
    (_hMF : section16MFSubgroup L H)
    {g : G} (hL : L = Tmax.conjBy g) :
    W1 ≤ H := by
  rcases _hsource with
    ⟨_hcaseB, _hptypeS, _hptypeT, hp_card, hq_card, _hC, _hD, _hc, _hd,
      _hUcard, _hVcard, _hSfam, _hTfam, _hDadeS, _hDadeT,
      _hnotationData, _hDadeDiff, _hZeroDegree, _hConjIndex, _hConjBetaTau,
      _hChoice, _hMin, _hFourSixS, _hFourSixT⟩
  have hsourceOrig :
      hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
        Sfam Tfam τS τT p q u v c d := by
    exact ⟨_hcaseB, _hptypeS, _hptypeT, hp_card, hq_card, _hC, _hD, _hc, _hd,
      _hUcard, _hVcard, _hSfam, _hTfam, _hDadeS, _hDadeT,
      _hnotationData, _hDadeDiff, _hZeroDegree, _hConjIndex, _hConjBetaTau,
      _hChoice, _hMin, _hFourSixS, _hFourSixT⟩
  have hW1leL : W1 ≤ L :=
    section13_theorem_13_17_W1_le_L_of_sourceContext
      Smax Tmax W W1 W2 P Q U V C D L Sfam Tfam τS τT
      p q u v c d hsourceOrig _hNormUleL
  let Hloc : Subgroup L := H.subgroupOf L
  let W1loc : Subgroup L := W1.subgroupOf L
  have hHleL : H ≤ L := Section12.section16MFSubgroup_le _hMF
  let : Hloc.Normal := by
    simpa [Hloc] using Section12.section16MFSubgroup_subgroupOf_normal _hMF
  have hHall : IsHallSubgroup (subgroupPrimeSet H) Hloc := by
    simpa [Hloc] using Section12.section16MFSubgroup_subgroupOf_isHall _hMF
  have hHcard :
      Nat.card H = q ^ p :=
    section13_theorem_13_17_H_card_eq_q_pow_p_of_L_conj_Tmax_sourceContext
      Smax Tmax W W1 W2 P Q U V C D L H Sfam Tfam τS τT
      p q u v c d hsourceOrig _hMF hL
  have hqprime : Nat.Prime q :=
    section13_prime_q_of_sourceContext
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
      p q u v c d hsourceOrig
  have hp_pos : 0 < p := by
    rw [hp_card]
    exact Nat.card_pos
  have hqπ : (⟨q, hqprime⟩ : Nat.Primes) ∈ subgroupPrimeSet H := by
    rw [subgroupPrimeSet]
    change q ∣ Nat.card H
    rw [hHcard]
    exact dvd_pow_self q (Nat.ne_of_gt hp_pos)
  have hW1loc_card : Nat.card W1loc = q := by
    simpa [W1loc, hq_card] using natCard_subgroupOf_eq W1 L hW1leL
  have : Fact (Nat.Prime q) := ⟨hqprime⟩
  have hW1locP : IsPGroup q W1loc := by
    rw [IsPGroup.iff_card]
    exact ⟨1, by simpa [← Nat.card_eq_fintype_card] using hW1loc_card⟩
  have hW1locH : W1loc ≤ Hloc :=
    section12_pSubgroup_le_normal_hall_of_prime_mem hHall hqπ hW1locP
  intro x hxW1
  have hxL : x ∈ L := hW1leL hxW1
  have hxloc : (⟨x, hxL⟩ : L) ∈ W1loc := by
    simpa [W1loc, Subgroup.mem_subgroupOf] using hxW1
  have hxHloc : (⟨x, hxL⟩ : L) ∈ Hloc := hW1locH hxloc
  simpa [Hloc, Subgroup.mem_subgroupOf] using hxHloc

private theorem section13_frobeniusJoinWithKernel_not_pointwise_centralized
    {G : Type u} [Group G] [Finite G]
    {U W1 : Subgroup G}
    (hfrob : section12FrobeniusJoinWithKernel U W1)
    (hcomm : ∀ u : G, u ∈ U → ∀ w : G, w ∈ W1 → u * w = w * u) :
    False := by
  classical
  let S : Subgroup G := U ⊔ W1
  rcases Subgroup.ne_bot_iff_exists_ne_one.mp
      (section13_left_ne_bot_of_frobeniusJoinWithKernel hfrob) with
    ⟨u, hu_ne⟩
  rcases Subgroup.ne_bot_iff_exists_ne_one.mp
      (section13_right_ne_bot_of_frobeniusJoinWithKernel hfrob) with
    ⟨w, hw_ne⟩
  let uS : S := ⟨(u : G), (show U ≤ S from le_sup_left) u.property⟩
  let wS : W1.subgroupOf S :=
    ⟨⟨(w : G), (show W1 ≤ S from le_sup_right) w.property⟩, w.property⟩
  have hwS_ne : wS ≠ 1 := by
    intro hwS
    apply hw_ne
    ext
    exact congrArg (fun z : W1.subgroupOf S => (z : G)) hwS
  have hcentBot :
      elementCentralizerIn (U.subgroupOf S) (wS : S) = ⊥ :=
    (lemma_3_1 (G := S) (K := U.subgroupOf S) (R := W1.subgroupOf S)
      hfrob.kernel_ne_bot hfrob.complement_ne_bot hfrob.normal
      hfrob.isComplement').1 hfrob wS hwS_ne
  have huCent : uS ∈ elementCentralizerIn (U.subgroupOf S) (wS : S) := by
    refine ⟨?_, ?_⟩
    · change (u : G) ∈ U
      exact u.property
    · apply Subgroup.mem_centralizer_singleton_iff.mpr
      ext
      exact hcomm (u : G) u.property (w : G) w.property
  have huBot : uS ∈ (⊥ : Subgroup S) := by
    simpa [hcentBot] using huCent
  have huS_one : uS = 1 := by
    simpa using huBot
  apply hu_ne
  ext
  exact congrArg (fun z : S => (z : G)) huS_one

/-- Source blocker for the second nonconjugacy exclusion in PF `(13.17)(a)`.
The TeX proof uses the order of `H` in the `Tmax`-conjugate case, the
containment `W1 ≤ N_G(U) ≤ L`, and PF `(13.2)(a)`. -/
private theorem section13_theorem_13_17_L_not_conj_Tmax_of_sourceContext
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D L H : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (_hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (_hTypeII : Section8.typeIIDefinitionData Smax P)
    (_hLmax : L ∈ section9MaximalSubgroups G)
    (_hNormUleL : Subgroup.normalizer (U : Set G) ≤ L)
    (_hMF : section16MFSubgroup L H) :
    ∀ g : G, L ≠ Tmax.conjBy g := by
  intro g hL
  have hsourceOrig := _hsource
  have hUleL : U ≤ L :=
    section13_theorem_13_17_U_le_L_of_normalizer _hNormUleL
  have hW1leH : W1 ≤ H :=
    section13_theorem_13_17_W1_le_H_of_L_conj_Tmax_sourceContext
      Smax Tmax W W1 W2 P Q U V C D L H Sfam Tfam τS τT
      p q u v c d hsourceOrig _hNormUleL _hMF hL
  have hUinfH : U ⊓ H = ⊥ :=
    section13_theorem_13_17_UinfH_eq_bot_of_L_conj_Tmax_sourceContext
      Smax Tmax W W1 W2 P Q U V C D L H Sfam Tfam τS τT
      p q u v c d hsourceOrig _hMF hL
  have hW1normU : W1 ≤ Subgroup.normalizer (U : Set G) :=
    section13_theorem_13_17_W1_le_normalizer_U_of_sourceContext
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
      p q u v c d hsourceOrig
  have hHleL : H ≤ L := Section12.section16MFSubgroup_le _hMF
  have hLleNormH : L ≤ Subgroup.normalizer (H : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hHleL).1
      (Section12.section16MFSubgroup_subgroupOf_normal _hMF)
  have hfrobUW1 : section12FrobeniusJoinWithKernel U W1 := by
    rcases theorem_13_2 Smax Tmax W W1 W2 P Q U V C D
        Sfam Tfam τS τT p q u v c d hsourceOrig with
      ⟨_hSMF, _hType, _hTypeIf, _hUcomm, hfrobUW1, _hPelem, _hPcard,
        _huBound, _hcoh, _hTI, _hTau, _hnorm⟩
    exact hfrobUW1
  exact section13_frobeniusJoinWithKernel_not_pointwise_centralized hfrobUW1
    (fun x hxU y hyW1 => by
      have hxNormH : x ∈ Subgroup.normalizer (H : Set G) :=
        hLleNormH (hUleL hxU)
      have hyH : y ∈ H := hW1leH hyW1
      have hxyxH : x * y * x⁻¹ ∈ H :=
        (Subgroup.mem_normalizer_iff.mp hxNormH y).1 hyH
      have hcommH : ⁅x, y⁆ ∈ H := by
        simpa [commutatorElement_def, mul_assoc] using H.mul_mem hxyxH (H.inv_mem hyH)
      have hyNormU : y ∈ Subgroup.normalizer (U : Set G) := hW1normU hyW1
      have hyxU : y * x⁻¹ * y⁻¹ ∈ U :=
        (Subgroup.mem_normalizer_iff.mp hyNormU x⁻¹).1 (U.inv_mem hxU)
      have hcommU : ⁅x, y⁆ ∈ U := by
        simpa [commutatorElement_def, mul_assoc] using U.mul_mem hxU hyxU
      have hcommBot : ⁅x, y⁆ ∈ (⊥ : Subgroup G) := by
        have hcommInf : ⁅x, y⁆ ∈ U ⊓ H := ⟨hcommU, hcommH⟩
        simpa [hUinfH] using hcommInf
      have hcommOne : ⁅x, y⁆ = 1 := by
        simpa using hcommBot
      exact commutatorElement_eq_one_iff_mul_comm.mp hcommOne)

/-- Source blocker isolating the PF `(13.17)(b)` use of PF `(8.17.a)`:
after conclusion `(a)`, the prime `q = |W1|` is not in `π(H)`. -/
private theorem section13_theorem_13_17_q_not_mem_H_primeSet_of_sourceContext
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D L H : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (hq : Nat.Prime q)
    (_hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (_hTypeII : Section8.typeIIDefinitionData Smax P)
    (_hLmax : L ∈ section9MaximalSubgroups G)
    (_hNormUleL : Subgroup.normalizer (U : Set G) ≤ L)
    (_hMF : section16MFSubgroup L H)
    (_hfrob : Section7.frobeniusWithKernel L H)
    (_hUleL : U ≤ L)
    (_hW1leL : W1 ≤ L) :
    (⟨q, hq⟩ : Nat.Primes) ∉ subgroupPrimeSet H := by
  classical
  have hsourceOrig := _hsource
  rcases _hsource with
    ⟨hcaseB, _hptypeS, hptypeT, _hp_card, hq_card, _hC, _hD, _hc_card,
      _hd_card, _hU_card, _hV_card, _hSfam, _hTfam, _hDadeS, _hDadeT,
      _hnotationData, _hDadeDiff, _hZeroDegree, _hConjIndex, _hConjBetaTau,
      hChoice, hMin, _hFourSixS, _hFourSixT⟩
  let : IsMinCE G := hMin
  rcases hcaseB with
    ⟨_hWprod, _hWcyc, _hW1ne, _hW2ne, _hWhat,
      _hSmaxMax, hTmaxMax, _hSMF, hTMF, _hSeq, _hTeq,
      _hSdisj, _hTdisj, _hST, _hII, _hStype, hTtype, _hclass⟩
  have hnotS :
      ∀ g : G, L ≠ Smax.conjBy g :=
    section13_theorem_13_17_L_not_conj_Smax_of_sourceContext
      Smax Tmax W W1 W2 P Q U V C D L H Sfam Tfam τS τT
      p q u v c d hsourceOrig _hTypeII _hLmax _hNormUleL _hMF
  have hnotT :
      ∀ g : G, L ≠ Tmax.conjBy g :=
    section13_theorem_13_17_L_not_conj_Tmax_of_sourceContext
      Smax Tmax W W1 W2 P Q U V C D L H Sfam Tfam τS τT
      p q u v c d hsourceOrig _hTypeII _hLmax _hNormUleL _hMF
  have hTypeI :
      Section8.typeIDefinitionData L H :=
    section13_theorem_13_17_typeI_of_not_conj_sourceContext
      Smax Tmax W W1 W2 P Q U V C D L H Sfam Tfam τS τT
      p q u v c d hsourceOrig _hLmax _hMF hnotS hnotT
  rcases hChoice L H _hLmax _hMF (Or.inl hTypeI) with ⟨MsL, hMsL⟩
  have hMsL_eq : MsL = H :=
    Section8.msChoiceSource_eq_mf_of_typeI hMsL hTypeI
  have hHsigmaL : subgroupPrimeSet H = section10SigmaPrimes L := by
    calc
      subgroupPrimeSet H = subgroupPrimeSet MsL := by rw [hMsL_eq]
      _ = section10SigmaPrimes L :=
        section13_subgroupPrimeSet_msChoiceSource_eq_sigma (G := G)
          _hLmax _hMF hMsL
  have hTtypes :
      Section8.typeIDefinitionData Tmax Q ∨
        Section8.typeIIDefinitionData Tmax Q ∨
          Section8.typeIIIDefinitionData Tmax Q ∨
            Section8.typeIVDefinitionData Tmax Q ∨
              Section8.typeVDefinitionData Tmax Q := Or.inr hTtype
  rcases hChoice Tmax Q hTmaxMax hTMF hTtypes with ⟨MsT, hMsT⟩
  have hQleMsT : Q ≤ MsT :=
    section13_mf_le_msChoiceSource_of_typeP hptypeT hMsT
  have hW1leQ : W1 ≤ Q := by
    rcases hptypeT with
      ⟨_hTMF, _hW2cyc, _hW2ne, _hW2hall, _hTcomp, _hVleD, _hVnil,
        _hW2norm, _hcompDV, _hQnotcyc, _hsecond, _hfit, _hfitD,
        hW1le, _hW1cyc, _hW1ne, _hcent, _hnormHat⟩
    intro x hx
    exact (hW1le hx).1
  have hqQ : (⟨q, hq⟩ : Nat.Primes) ∈ subgroupPrimeSet Q := by
    apply Set.mem_setOf.mpr
    have hcard : Nat.card W1 ∣ Nat.card Q :=
      Subgroup.card_dvd_of_le hW1leQ
    simpa [hq_card] using hcard
  have hqMsT : (⟨q, hq⟩ : Nat.Primes) ∈ subgroupPrimeSet MsT := by
    rw [subgroupPrimeSet] at hqQ ⊢
    exact Nat.dvd_trans hqQ (Subgroup.card_dvd_of_le hQleMsT)
  have hqSigmaT : (⟨q, hq⟩ : Nat.Primes) ∈ section10SigmaPrimes Tmax := by
    have hMsTsigma :
        subgroupPrimeSet MsT = section10SigmaPrimes Tmax :=
      section13_subgroupPrimeSet_msChoiceSource_eq_sigma (G := G)
        hTmaxMax hTMF hMsT
    simpa [hMsTsigma] using hqMsT
  intro hqH
  have hqSigmaL : (⟨q, hq⟩ : Nat.Primes) ∈ section10SigmaPrimes L := by
    simpa [hHsigmaL] using hqH
  have hnotConjTL : section12NotConjugate Tmax L := by
    intro g hg
    exact hnotT g hg.symm
  have hdis :
      Disjoint (section10SigmaPrimes L) (section10SigmaPrimes Tmax) :=
    _root_.CFSG.theorem_13_9 (G := G) _hLmax hTmaxMax hnotConjTL
  rw [Set.disjoint_left] at hdis
  exact hdis hqSigmaL hqSigmaT

/-- PF `(13.17)(b)` order-input wrapper: convert the source prime-set
separation from conclusion `(a)` and PF `(8.17.a)` into `|H|` prime to `q`. -/
private theorem section13_theorem_13_17_H_coprime_q_of_sourceContext
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D L H : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (_hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (_hTypeII : Section8.typeIIDefinitionData Smax P)
    (_hLmax : L ∈ section9MaximalSubgroups G)
    (_hNormUleL : Subgroup.normalizer (U : Set G) ≤ L)
    (_hMF : section16MFSubgroup L H)
    (_hfrob : Section7.frobeniusWithKernel L H)
    (_hUleL : U ≤ L)
    (_hW1leL : W1 ≤ L) :
    Nat.Coprime (Nat.card H) q := by
  have hqprime : Nat.Prime q :=
    section13_prime_q_of_sourceContext
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
      p q u v c d _hsource
  exact section13_coprime_card_of_prime_not_mem_subgroupPrimeSet hqprime
    (section13_theorem_13_17_q_not_mem_H_primeSet_of_sourceContext
      Smax Tmax W W1 W2 P Q U V C D L H Sfam Tfam τS τT
      p q u v c d hqprime _hsource _hTypeII _hLmax _hNormUleL
      _hMF _hfrob _hUleL _hW1leL)

/-- Source blocker for the PF `(13.17)(b)` step `W1 ∩ H = 1`. -/
private theorem section13_theorem_13_17_W1infH_eq_bot_of_sourceContext
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D L H : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (_hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (_hTypeII : Section8.typeIIDefinitionData Smax P)
    (_hLmax : L ∈ section9MaximalSubgroups G)
    (_hNormUleL : Subgroup.normalizer (U : Set G) ≤ L)
    (_hMF : section16MFSubgroup L H)
    (_hfrob : Section7.frobeniusWithKernel L H)
    (_hUleL : U ≤ L)
    (_hW1leL : W1 ≤ L) :
    W1 ⊓ H = ⊥ := by
  have hsourceOrig := _hsource
  rcases _hsource with
    ⟨_hcase, _hptypeS, _hptypeT, _hp_card, hq_card, _hC, _hD, _hc_card,
      _hd_card, _hU_card, _hV_card, _hSfam, _hTfam, _hDadeS, _hDadeT,
      _hnotationData, _hDadeDiff, _hZeroDegree, _hConjIndex, _hConjBetaTau,
      _hChoice, _hMin, _hFourSixS, _hFourSixT⟩
  exact section13_inf_eq_bot_of_card_right_coprime hq_card
    (section13_theorem_13_17_H_coprime_q_of_sourceContext
      Smax Tmax W W1 W2 P Q U V C D L H Sfam Tfam τS τT
      p q u v c d hsourceOrig _hTypeII _hLmax _hNormUleL _hMF
      _hfrob _hUleL _hW1leL)

/-- Source blocker for the coprime-order input in the PF `(13.17)(b)` use of
PF `(9.1)` under the temporary assumption `U ∩ H = 1`. -/
private theorem section13_theorem_13_17_H_coprime_UW1_of_UinfH_bot_sourceContext
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D L H : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (_hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (_hTypeII : Section8.typeIIDefinitionData Smax P)
    (_hLmax : L ∈ section9MaximalSubgroups G)
    (_hNormUleL : Subgroup.normalizer (U : Set G) ≤ L)
    (_hMF : section16MFSubgroup L H)
    (_hfrob : Section7.frobeniusWithKernel L H)
    (_hUleL : U ≤ L)
    (_hW1leL : W1 ≤ L)
    (_hUinfH : U ⊓ H = ⊥) :
    Nat.Coprime (Nat.card H) (Nat.card (U ⊔ W1 : Subgroup G)) := by
  have hsourceOrig := _hsource
  rcases _hsource with
    ⟨_hcase, _hptypeS, _hptypeT, _hp_card, hq_card, _hC, _hD, _hc_card,
      _hd_card, _hU_card, _hV_card, _hSfam, _hTfam, _hDadeS, _hDadeT,
      _hnotationData, _hDadeDiff, _hZeroDegree, _hConjIndex, _hConjBetaTau,
      _hChoice, _hMin, _hFourSixS, _hFourSixT⟩
  have h13_2 := theorem_13_2 Smax Tmax W W1 W2 P Q U V C D
    Sfam Tfam τS τT p q u v c d hsourceOrig
  rcases h13_2 with
    ⟨_hSMF, _hType, _hTypeIf, _hUcomm, hfrobUW1, _hPelem, _hPcard,
      _huBound, _hcoh, _hTI, _hTau⟩
  have hcardUW1 : Nat.card (U ⊔ W1 : Subgroup G) = Nat.card U * Nat.card W1 := by
    have hmul := hfrobUW1.isComplement'.card_mul_card
    have hcardUsub :
        Nat.card (U.subgroupOf (U ⊔ W1 : Subgroup G)) = Nat.card U :=
      natCard_subgroupOf_eq U (U ⊔ W1) le_sup_left
    have hcardW1sub :
        Nat.card (W1.subgroupOf (U ⊔ W1 : Subgroup G)) = Nat.card W1 :=
      natCard_subgroupOf_eq W1 (U ⊔ W1) le_sup_right
    have hmul' := hmul.symm
    rw [hcardUsub, hcardW1sub] at hmul'
    exact hmul'
  have hUdisj : Disjoint U H := by
    rw [disjoint_iff]
    exact _hUinfH
  have hUcop : Nat.Coprime (Nat.card H) (Nat.card U) :=
    section13_coprime_card_of_mf_subgroup_disjoint _hMF _hUleL hUdisj
  have hW1cop : Nat.Coprime (Nat.card H) (Nat.card W1) := by
    simpa [hq_card] using
      (section13_theorem_13_17_H_coprime_q_of_sourceContext
        Smax Tmax W W1 W2 P Q U V C D L H Sfam Tfam τS τT
        p q u v c d hsourceOrig _hTypeII _hLmax _hNormUleL _hMF
        _hfrob _hUleL _hW1leL)
  rw [hcardUW1]
  exact hUcop.mul_right hW1cop

/-- Source blocker for the PF `(13.17)(b)` setup needed to apply PF `(9.1)`
when assuming `U ∩ H = 1`. -/
private theorem section13_theorem_13_17_UW1_frobeniusActionData_of_UinfH_bot_sourceContext
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D L H : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (_hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (_hTypeII : Section8.typeIIDefinitionData Smax P)
    (_hLmax : L ∈ section9MaximalSubgroups G)
    (_hNormUleL : Subgroup.normalizer (U : Set G) ≤ L)
    (_hMF : section16MFSubgroup L H)
    (_hfrob : Section7.frobeniusWithKernel L H)
    (_hUleL : U ≤ L)
    (_hW1leL : W1 ≤ L)
    (_hUinfH : U ⊓ H = ⊥) :
    Section9.frobeniusActionData (U ⊔ W1) U W1 H := by
  have h13_2 := theorem_13_2 Smax Tmax W W1 W2 P Q U V C D
    Sfam Tfam τS τT p q u v c d _hsource
  rcases h13_2 with
    ⟨_hSMF, _hType, _hTypeIf, _hUcomm, hfrobUW1, _hPelem, _hPcard,
      _huBound, _hcoh, _hTI, _hTau⟩
  have hcomp : section12ComplementIn (U ⊔ W1) U W1 := by
    refine ⟨le_sup_left, le_sup_right, rfl, ?_⟩
    rw [Subgroup.disjoint_def]
    intro x hxU hxW1
    have hxU' :
        (⟨x, (le_sup_left : U ≤ U ⊔ W1) hxU⟩ : (U ⊔ W1 : Subgroup G)) ∈
          U.subgroupOf (U ⊔ W1) := by
      change x ∈ U
      exact hxU
    have hxW1' :
        (⟨x, (le_sup_right : W1 ≤ U ⊔ W1) hxW1⟩ : (U ⊔ W1 : Subgroup G)) ∈
          W1.subgroupOf (U ⊔ W1) := by
      change x ∈ W1
      exact hxW1
    have hxBotLocal :
        (⟨x, (le_sup_left : U ≤ U ⊔ W1) hxU⟩ : (U ⊔ W1 : Subgroup G)) = 1 := by
      exact (Subgroup.disjoint_def.mp hfrobUW1.isComplement'.disjoint) hxU' hxW1'
    exact congrArg Subtype.val hxBotLocal
  have hnormalizesH : U ⊔ W1 ≤ Subgroup.normalizer (H : Set G) := by
    rcases _hfrob with ⟨hHL, hHnormal, _R, _hcompR, _hHne, _hRne, _hfixedR⟩
    have hL_le_normH : L ≤ Subgroup.normalizer (H : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hHL).1 hHnormal
    exact (sup_le _hUleL _hW1leL).trans hL_le_normH
  have hsolvH : Group.IsSolvable H := by
    rcases _hMF.1 with ⟨_hHL, _hHnormal, hHnil, _hHall⟩
    let : Group.IsNilpotent H := hHnil
    exact inferInstance
  exact ⟨hcomp, hfrobUW1, hnormalizesH, hsolvH,
    section13_theorem_13_17_H_coprime_UW1_of_UinfH_bot_sourceContext
      Smax Tmax W W1 W2 P Q U V C D L H Sfam Tfam τS τT
      p q u v c d _hsource _hTypeII _hLmax _hNormUleL _hMF
      _hfrob _hUleL _hW1leL _hUinfH⟩

/-- Source blocker for the PF `(13.17)(b)` Frobenius-kernel centralizer step.
The source proof uses the Frobenius action of `L/H` on `H` to show that an
element of `L` outside `H` has no nontrivial fixed point in `H`. -/
private theorem section13_theorem_13_17_frobenius_kernel_centralizer_property_of_sourceContext
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D L H : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (_hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (_hTypeII : Section8.typeIIDefinitionData Smax P)
    (_hLmax : L ∈ section9MaximalSubgroups G)
    (_hNormUleL : Subgroup.normalizer (U : Set G) ≤ L)
    (_hMF : section16MFSubgroup L H)
    (_hfrob : Section7.frobeniusWithKernel L H)
    (_hUleL : U ≤ L)
    (_hW1leL : W1 ≤ L) :
    ∀ x : G, x ∈ L → x ∉ H → Section2.centralizerIn H x = ⊥ := by
  exact section13_frobeniusWithKernel_centralizerIn_eq_bot_of_not_mem _hfrob

/-- Source blocker for the PF `(13.17)(b)` nontrivial-intersection step
`U ∩ H ≠ 1`. -/
private theorem section13_theorem_13_17_UinfH_ne_bot_of_sourceContext
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (Smax Tmax W W1 W2 P Q U V C D L H : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (_hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (_hTypeII : Section8.typeIIDefinitionData Smax P)
    (_hLmax : L ∈ section9MaximalSubgroups G)
    (_hNormUleL : Subgroup.normalizer (U : Set G) ≤ L)
    (_hMF : section16MFSubgroup L H)
    (_hfrob : Section7.frobeniusWithKernel L H)
    (_hUleL : U ≤ L)
    (_hW1leL : W1 ≤ L) :
    U ⊓ H ≠ ⊥ := by
  exact section13_UinfH_ne_bot_from_frobenius_action
    _hUleL _hW1leL (section13_H_ne_bot_of_frobeniusWithKernel _hfrob)
    (section13_theorem_13_17_W1infH_eq_bot_of_sourceContext
      Smax Tmax W W1 W2 P Q U V C D L H Sfam Tfam τS τT
      p q u v c d _hsource _hTypeII _hLmax _hNormUleL _hMF
      _hfrob _hUleL _hW1leL)
    (fun hUinfH =>
      section13_theorem_13_17_UW1_frobeniusActionData_of_UinfH_bot_sourceContext
        Smax Tmax W W1 W2 P Q U V C D L H Sfam Tfam τS τT
        p q u v c d _hsource _hTypeII _hLmax _hNormUleL _hMF
        _hfrob _hUleL _hW1leL hUinfH)
    (section13_theorem_13_17_frobenius_kernel_centralizer_property_of_sourceContext
      Smax Tmax W W1 W2 P Q U V C D L H Sfam Tfam τS τT
      p q u v c d _hsource _hTypeII _hLmax _hNormUleL _hMF
      _hfrob _hUleL _hW1leL)

/-- Source blocker for the final Frobenius-centralizer step in PF `(13.17)(b)`.
The TeX proof first proves `U ∩ H ≠ 1`, then uses
`U ≤ C_L(U ∩ H) ≤ H`. -/
private theorem section13_theorem_13_17_centralizer_UinfH_le_H_of_sourceContext
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (Smax Tmax W W1 W2 P Q U V C D L H : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (_hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (_hTypeII : Section8.typeIIDefinitionData Smax P)
    (_hLmax : L ∈ section9MaximalSubgroups G)
    (_hNormUleL : Subgroup.normalizer (U : Set G) ≤ L)
    (_hMF : section16MFSubgroup L H)
    (_hfrob : Section7.frobeniusWithKernel L H)
    (_hUleL : U ≤ L)
    (_hW1leL : W1 ≤ L) :
    subgroupCentralizerIn L (U ⊓ H) ≤ H := by
  exact section13_centralizer_nontrivial_kernel_subgroup_le_of_fixedPointFree
    (L := L) (H := H) (K := U ⊓ H) inf_le_right
    (section13_theorem_13_17_UinfH_ne_bot_of_sourceContext
      Smax Tmax W W1 W2 P Q U V C D L H Sfam Tfam τS τT
      p q u v c d _hsource _hTypeII _hLmax _hNormUleL _hMF
      _hfrob _hUleL _hW1leL)
    (section13_theorem_13_17_frobenius_kernel_centralizer_property_of_sourceContext
      Smax Tmax W W1 W2 P Q U V C D L H Sfam Tfam τS τT
      p q u v c d _hsource _hTypeII _hLmax _hNormUleL _hMF
      _hfrob _hUleL _hW1leL)

/-- Source blocker for PF `(13.17)(b)`, after the Frobenius conclusion and the
small containments `U ≤ L`, `W1 ≤ L` have been separated. -/
private theorem section13_theorem_13_17_U_le_H_of_sourceContext
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (Smax Tmax W W1 W2 P Q U V C D L H : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (_hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (_hTypeII : Section8.typeIIDefinitionData Smax P)
    (_hLmax : L ∈ section9MaximalSubgroups G)
    (_hNormUleL : Subgroup.normalizer (U : Set G) ≤ L)
    (_hMF : section16MFSubgroup L H)
    (_hfrob : Section7.frobeniusWithKernel L H)
    (_hUleL : U ≤ L)
    (_hW1leL : W1 ≤ L) :
    U ≤ H := by
  have h13_2 := theorem_13_2 Smax Tmax W W1 W2 P Q U V C D
    Sfam Tfam τS τT p q u v c d _hsource
  rcases h13_2 with
    ⟨_hSMF, _hType, _hTypeIf, hUcomm, _hfrobUW1, _hPelem, _hPcard,
      _huBound, _hcoh, _hTI, _hTau⟩
  exact section13_theorem_13_17_U_le_H_from_centralizer_inf hUcomm _hUleL
    (section13_theorem_13_17_centralizer_UinfH_le_H_of_sourceContext
      Smax Tmax W W1 W2 P Q U V C D L H Sfam Tfam τS τT
      p q u v c d _hsource _hTypeII _hLmax _hNormUleL _hMF _hfrob _hUleL _hW1leL)

/-- Source blocker for PF `(13.17)(c)`: the source proof uses that the maximal
subgroup `L` is solvable before applying Hall complement containment. -/
private theorem section13_theorem_13_17_L_solvable_of_sourceContext
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D L H : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (_hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (_hTypeII : Section8.typeIIDefinitionData Smax P)
    (_hLmax : L ∈ section9MaximalSubgroups G)
    (_hNormUleL : Subgroup.normalizer (U : Set G) ≤ L)
    (_hMF : section16MFSubgroup L H)
    (_hfrob : Section7.frobeniusWithKernel L H)
    (_hUleH : U ≤ H)
    (_hW1leL : W1 ≤ L) :
    Group.IsSolvable L := by
  have hnotS :
      ∀ g : G, L ≠ Smax.conjBy g :=
    section13_theorem_13_17_L_not_conj_Smax_of_sourceContext
      Smax Tmax W W1 W2 P Q U V C D L H Sfam Tfam τS τT
      p q u v c d _hsource _hTypeII _hLmax _hNormUleL _hMF
  have hnotT :
      ∀ g : G, L ≠ Tmax.conjBy g :=
    section13_theorem_13_17_L_not_conj_Tmax_of_sourceContext
      Smax Tmax W W1 W2 P Q U V C D L H Sfam Tfam τS τT
      p q u v c d _hsource _hTypeII _hLmax _hNormUleL _hMF
  have hTypeI :
      Section8.typeIDefinitionData L H :=
    section13_theorem_13_17_typeI_of_not_conj_sourceContext
      Smax Tmax W W1 W2 P Q U V C D L H Sfam Tfam τS τT
      p q u v c d _hsource _hLmax _hMF hnotS hnotT
  rcases hTypeI with ⟨K, K1, K0, hF, _hcases⟩
  exact hF.1

/-- PF `(13.17)(c)` Hall complement choice with `W1 ≤ E`, reduced to the
source solvability of the maximal subgroup `L` and the earlier `(13.17)(b)`
prime-set input. -/
private theorem section13_theorem_13_17_W1_containing_complement_sourceData_of_sourceContext
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D L H : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (_hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (_hTypeII : Section8.typeIIDefinitionData Smax P)
    (_hLmax : L ∈ section9MaximalSubgroups G)
    (_hNormUleL : Subgroup.normalizer (U : Set G) ≤ L)
    (_hMF : section16MFSubgroup L H)
    (_hfrob : Section7.frobeniusWithKernel L H)
    (_hUleH : U ≤ H)
    (_hW1leL : W1 ≤ L) :
    ∃ E : Subgroup G, section12ComplementIn L H E ∧ W1 ≤ E := by
  have hHleL : H ≤ L := Section12.section16MFSubgroup_le _hMF
  have hUleL : U ≤ L := _hUleH.trans hHleL
  exact section13_containing_complement_of_solvable_mf _hMF
    (section13_theorem_13_17_L_solvable_of_sourceContext
      Smax Tmax W W1 W2 P Q U V C D L H Sfam Tfam τS τT
      p q u v c d _hsource _hTypeII _hLmax _hNormUleL _hMF _hfrob
      _hUleH _hW1leL)
    _hW1leL
    (section13_theorem_13_17_W1infH_eq_bot_of_sourceContext
      Smax Tmax W W1 W2 P Q U V C D L H Sfam Tfam τS τT
      p q u v c d _hsource _hTypeII _hLmax _hNormUleL _hMF
      _hfrob hUleL _hW1leL)


private theorem section13_prime_order_subgroup_normal_of_centralizes_fitting
    {E : Type u} [Group E] [Finite E] [Group.IsSolvable E] {P : Subgroup E}
    (hPprime : Nat.Prime (Nat.card P))
    (hPcentF : P ≤ Subgroup.centralizer (fittingSubgroup E : Set E))
    (hpcore_cyc : IsCyclic (pCore (Nat.card P) E)) :
    P.Normal := by
  classical
  let p := Nat.card P
  let : Fact (Nat.Prime p) := ⟨hPprime⟩
  have hP_le_F : P ≤ fittingSubgroup E := by
    exact hPcentF.trans
      (centralizer_fittingSubgroup_le_fittingSubgroup_of_solvable (G := E) inferInstance)
  have hPp : IsPGroup p P := by
    rw [IsPGroup.iff_card]
    exact ⟨1, by simp [p]⟩
  have hPsub_p : IsPGroup p (P.subgroupOf (fittingSubgroup E)) :=
    hPp.of_equiv (Subgroup.subgroupOfEquivOfLe hP_le_F).symm
  obtain ⟨S, hPsub_le_S⟩ :=
    IsPGroup.exists_le_sylow (G := fittingSubgroup E) (p := p) hPsub_p
  have hSmap_le_pCore :
      (S : Subgroup (fittingSubgroup E)).map (fittingSubgroup E).subtype ≤ pCore p E := by
    have hS_normal_sub : (S : Subgroup (fittingSubgroup E)).Normal :=
      Group.IsNilpotent.sylow_normal (p := p) inferInstance S
    have : (S : Subgroup (fittingSubgroup E)).Characteristic :=
      Sylow.characteristic_of_normal S hS_normal_sub
    have hS_normal_ambient :
        ((S : Subgroup (fittingSubgroup E)).map (fittingSubgroup E).subtype).Normal := by
      exact ConjAct.normal_of_characteristic_of_normal
    have hS_p : IsPGroup p ((S : Subgroup (fittingSubgroup E)).map
        (fittingSubgroup E).subtype) :=
      S.isPGroup'.map (fittingSubgroup E).subtype
    exact le_sSup ⟨hS_normal_ambient, hS_p⟩
  have hP_le_pCore : P ≤ pCore p E := by
    intro x hx
    have hxsub : (⟨x, hP_le_F hx⟩ : fittingSubgroup E) ∈
        P.subgroupOf (fittingSubgroup E) := by
      simpa [Subgroup.mem_subgroupOf] using hx
    have hxS : (⟨x, hP_le_F hx⟩ : fittingSubgroup E) ∈
        (S : Subgroup (fittingSubgroup E)) :=
      hPsub_le_S hxsub
    exact hSmap_le_pCore
      (Subgroup.mem_map.mpr ⟨⟨x, hP_le_F hx⟩, hxS, rfl⟩)
  let Psub : Subgroup (pCore p E) := P.subgroupOf (pCore p E)
  have : IsCyclic (pCore p E) := hpcore_cyc
  have hPsub_char : Psub.Characteristic :=
    section12_subgroup_characteristic_of_cyclic Psub
  have hPsub_normal_map : (Psub.map (pCore p E).subtype).Normal := by
    exact ConjAct.normal_of_characteristic_of_normal
  have hPsub_map_eq : Psub.map (pCore p E).subtype = P := by
    simpa [Psub] using Subgroup.map_subgroupOf_eq_of_le hP_le_pCore
  simpa [hPsub_map_eq] using hPsub_normal_map


private theorem section13_huppert_prime_order_subgroup_le_centralizer_fitting_of_odd_frobenius_complement
    {G : Type u} [Group G] [Finite G] {L H E W : Subgroup G}
    (_hEleL : E ≤ L)
    (_hfrobE :
      IsFrobeniusGroupWithKernelComplement (H.subgroupOf L) (E.subgroupOf L))
    (_hoddE : Odd (Nat.card E))
    (_hWleE : W ≤ E)
    (_hWprime : Nat.Prime (Nat.card W)) :
    W.subgroupOf E ≤ Subgroup.centralizer (fittingSubgroup E : Set E) := by
  classical
  let : (H.subgroupOf L).Normal := _hfrobE.normal
  letI : MulDistribMulAction (E.subgroupOf L) (H.subgroupOf L) :=
    Subgroup.conjMulDistribMulActionOfLeNormalizer (G := L)
      (E.subgroupOf L) (H.subgroupOf L)
      (Subgroup.le_normalizer_of_normal (H := H.subgroupOf L))
  let e : E ≃* E.subgroupOf L :=
    (Subgroup.subgroupOfEquivOfLe (H := E) (K := L) _hEleL).symm
  letI : MulDistribMulAction E (H.subgroupOf L) :=
    MulDistribMulAction.compHom (H.subgroupOf L) e.toMonoidHom
  have hregularSub : ActsRegularly (E.subgroupOf L) (H.subgroupOf L) :=
    _hfrobE.regular_conj_action
  have hregularE : ActsRegularly E (H.subgroupOf L) := by
    intro a ha
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    have hxSub : x ∈ fixedPointSubgroup (↥(Subgroup.zpowers (e a))) (H.subgroupOf L) := by
      rw [fixedPointSubgroup, FixedPoints.mem_subgroup]
      intro z
      rcases Subgroup.mem_zpowers_iff.mp z.2 with ⟨n, hn⟩
      have hzE : e.symm z ∈ Subgroup.zpowers a := by
        refine Subgroup.mem_zpowers_iff.mpr ⟨n, ?_⟩
        apply e.injective
        simp [hn]
      let y : Subgroup.zpowers a := ⟨e.symm z, hzE⟩
      have hzy : e (y : E) = z := by
        simp [y]
      have hyfix : (y : E) • x = x := by
        simpa [← Subgroup.smul_def] using hx y
      simpa [Subgroup.smul_def, MulAction.compHom_smul_def, hzy] using hyfix
    have haSub : e a ≠ 1 := by
      intro h
      exact ha (e.injective (by simpa using h))
    have hxBot : x ∈ (⊥ : Subgroup (H.subgroupOf L)) := by
      simpa [hregularSub (e a) haSub] using hxSub
    simpa using hxBot
  have : Nontrivial (H.subgroupOf L) :=
    (Subgroup.nontrivial_iff_ne_bot (H.subgroupOf L)).2 _hfrobE.kernel_ne_bot
  have hWsubPrime : Nat.Prime (Nat.card (W.subgroupOf E)) := by
    rw [natCard_subgroupOf_eq W E _hWleE]
    exact _hWprime
  exact
    prime_order_subgroup_le_centralizer_fitting_of_odd_regular_action
      (H := H.subgroupOf L) (R := E) _hoddE hregularE hWsubPrime

private theorem section13_huppert_prime_order_subgroup_normal_of_odd_frobenius_complement
    {G : Type u} [Group G] [Finite G] {L H E W : Subgroup G}
    (_hEleL : E ≤ L)
    (_hfrobE :
      IsFrobeniusGroupWithKernelComplement (H.subgroupOf L) (E.subgroupOf L))
    (_hoddE : Odd (Nat.card E))
    (_hWleE : W ≤ E)
    (_hWprime : Nat.Prime (Nat.card W)) :
    (W.subgroupOf E).Normal := by
  classical
  let P : Subgroup E := W.subgroupOf E
  change P.Normal
  have hPprime : Nat.Prime (Nat.card P) := by
    rw [show Nat.card P = Nat.card W from
      natCard_subgroupOf_eq W E _hWleE]
    exact _hWprime
  have hEsub_odd : Odd (Nat.card (E.subgroupOf L)) := by
    rw [natCard_subgroupOf_eq E L _hEleL]
    exact _hoddE
  have hZsub : IsZGroup (E.subgroupOf L) :=
    isZGroup_of_frobenius_complement_of_odd (K := H.subgroupOf L)
      (R := E.subgroupOf L) _hfrobE hEsub_odd
  let : IsZGroup (E.subgroupOf L) := hZsub
  let e : E.subgroupOf L ≃* E :=
    Subgroup.subgroupOfEquivOfLe (H := E) (K := L) _hEleL
  have hZE : IsZGroup E :=
    IsZGroup.of_injective (f := e.symm.toMonoidHom) e.symm.injective
  let : IsZGroup E := hZE
  let : Fact (Nat.Prime (Nat.card P)) := ⟨hPprime⟩
  have hpcore_cyc : IsCyclic (pCore (Nat.card P) E) :=
    IsPGroup.isCyclic_of_isZGroup (G := E) (P := pCore (Nat.card P) E)
      (pCore_isPGroup (G := E) (p := Nat.card P))
  have hPcentF : P ≤ Subgroup.centralizer (fittingSubgroup E : Set E) := by
    simpa [P] using
      section13_huppert_prime_order_subgroup_le_centralizer_fitting_of_odd_frobenius_complement
        _hEleL _hfrobE _hoddE _hWleE _hWprime
  exact section13_prime_order_subgroup_normal_of_centralizes_fitting
    (E := E) (P := P) hPprime hPcentF hpcore_cyc

/-- Source blocker for PF `(13.17)(c)`: in an odd-order Frobenius complement,
every subgroup of prime order is normal. -/
private theorem section13_theorem_13_17_W1_normal_in_complement_of_sourceContext
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D L H : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (_hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (_hTypeII : Section8.typeIIDefinitionData Smax P)
    (_hLmax : L ∈ section9MaximalSubgroups G)
    (_hNormUleL : Subgroup.normalizer (U : Set G) ≤ L)
    (_hMF : section16MFSubgroup L H)
    (_hfrob : Section7.frobeniusWithKernel L H)
    (_hUleH : U ≤ H)
    (_hW1leL : W1 ≤ L)
    (E : Subgroup G)
    (_hcompE : section12ComplementIn L H E)
    (_hW1leE : W1 ≤ E) :
    (W1.subgroupOf E).Normal := by
  have hsourceOrig := _hsource
  rcases _hsource with
    ⟨_hcaseB, hptypeS, _hptypeT, _hp_card, hq_card, _hC, _hD, _hc_card,
      _hd_card, _hU_card, _hV_card, _hSfam, _hTfam, _hDadeS, _hDadeT,
      _hnotationData, _hDadeDiff, _hZeroDegree, _hConjIndex, _hConjBetaTau,
      _hChoice, _hMin, _hFourSixS, _hFourSixT⟩
  rcases hptypeS with
    ⟨_hSMF, _hW1cyc, hW1ne, _hW1hall, _hcompMW1, _hUleD, _hUnil,
      _hW1normU, _hcompDU, _hMFnotcyc, _hsecond, _hfit, _hfitD,
      _hW2le, _hW2cyc, _hW2ne, _hcent, _hnormHat⟩
  have hEne : E ≠ ⊥ := by
    intro hEbot
    apply hW1ne
    apply le_antisymm
    · intro x hx
      have hxE : x ∈ E := _hW1leE hx
      simpa [hEbot] using hxE
    · exact bot_le
  have hfrobE :
      IsFrobeniusGroupWithKernelComplement (H.subgroupOf L) (E.subgroupOf L) :=
    section13_frobeniusWithKernel_complementIn_isFrobenius _hfrob _hcompE hEne
  have hnotS :
      ∀ g : G, L ≠ Smax.conjBy g :=
    section13_theorem_13_17_L_not_conj_Smax_of_sourceContext
      Smax Tmax W W1 W2 P Q U V C D L H Sfam Tfam τS τT
      p q u v c d hsourceOrig _hTypeII _hLmax _hNormUleL _hMF
  have hnotT :
      ∀ g : G, L ≠ Tmax.conjBy g :=
    section13_theorem_13_17_L_not_conj_Tmax_of_sourceContext
      Smax Tmax W W1 W2 P Q U V C D L H Sfam Tfam τS τT
      p q u v c d hsourceOrig _hTypeII _hLmax _hNormUleL _hMF
  have hTypeI :
      Section8.typeIDefinitionData L H :=
    section13_theorem_13_17_typeI_of_not_conj_sourceContext
      Smax Tmax W W1 W2 P Q U V C D L H Sfam Tfam τS τT
      p q u v c d hsourceOrig _hLmax _hMF hnotS hnotT
  have hoddE : Odd (Nat.card E) :=
    odd_of_card_dvd (Section12.odd_card_of_typeIDefinitionData L H hTypeI)
      (Subgroup.card_dvd_of_le _hcompE.2.1)
  have hW1prime : Nat.Prime (Nat.card W1) := by
    have hqprime : Nat.Prime q :=
      section13_prime_q_of_sourceContext
        Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
        p q u v c d hsourceOrig
    simpa [hq_card] using hqprime
  exact section13_huppert_prime_order_subgroup_normal_of_odd_frobenius_complement
    _hcompE.2.1 hfrobE hoddE _hW1leE hW1prime

/-- PF `(13.17)(c)` normalizer wrapper: once `W1` is normal in the chosen
complement, the complement lies in `N_G(W1)`. -/
private theorem section13_theorem_13_17_complement_le_normalizer_W1_of_sourceContext
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D L H : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (_hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (_hTypeII : Section8.typeIIDefinitionData Smax P)
    (_hLmax : L ∈ section9MaximalSubgroups G)
    (_hNormUleL : Subgroup.normalizer (U : Set G) ≤ L)
    (_hMF : section16MFSubgroup L H)
    (_hfrob : Section7.frobeniusWithKernel L H)
    (_hUleH : U ≤ H)
    (_hW1leL : W1 ≤ L)
    (E : Subgroup G)
    (_hcompE : section12ComplementIn L H E)
    (_hW1leE : W1 ≤ E) :
    E ≤ Subgroup.normalizer (W1 : Set G) :=
  section13_le_normalizer_of_subgroupOf_normal _hW1leE
    (section13_theorem_13_17_W1_normal_in_complement_of_sourceContext
      Smax Tmax W W1 W2 P Q U V C D L H Sfam Tfam τS τT
      p q u v c d _hsource _hTypeII _hLmax _hNormUleL _hMF _hfrob
      _hUleH _hW1leL E _hcompE _hW1leE)

private theorem section13_theorem_13_17_complement_le_Q_sup_W2_of_normalizer
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (Smax Tmax W W1 W2 P Q U V C D E : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (hEleNorm : E ≤ Subgroup.normalizer (W1 : Set G)) :
    E ≤ Q ⊔ W2 := by
  have h13_16 := theorem_13_16 Smax Tmax W W1 W2 P Q U V C D
    Sfam Tfam τS τT p q u v c d hsource
  rcases h13_16 with ⟨hnorm_eq, hcent_eq⟩
  simpa [hnorm_eq, hcent_eq] using hEleNorm

private theorem section13_eq_of_le_of_card_eq
    {G : Type u} [Group G] [Finite G] {A B : Subgroup G}
    (hAB : A ≤ B) (hcard : Nat.card B = Nat.card A) :
    B = A := by
  exact (Subgroup.eq_of_le_of_card_ge hAB (by rw [← hcard])).symm

private theorem section13_sylow_isCyclic_of_odd_frobenius_complement
    {G : Type u} [Group G] [Finite G] {L H E : Subgroup G}
    (hcompE : section12ComplementIn L H E)
    (hfrobE :
      IsFrobeniusGroupWithKernelComplement (H.subgroupOf L) (E.subgroupOf L))
    (hoddE : Odd (Nat.card E))
    (r : Nat.Primes) (R : Sylow r.val E) :
    IsCyclic R := by
  have hEsub_odd : Odd (Nat.card (E.subgroupOf L)) := by
    rw [natCard_subgroupOf_eq E L hcompE.2.1]
    exact hoddE
  have hZsub : IsZGroup (E.subgroupOf L) :=
    isZGroup_of_frobenius_complement_of_odd (K := H.subgroupOf L)
      (R := E.subgroupOf L) hfrobE hEsub_odd
  let e : E.subgroupOf L ≃* E :=
    Subgroup.subgroupOfEquivOfLe (H := E) (K := L) hcompE.2.1
  have hZE : IsZGroup E :=
    IsZGroup.of_injective (f := e.symm.toMonoidHom) e.symm.injective
  let : IsZGroup E := hZE
  let : Fact r.val.Prime := ⟨r.2⟩
  exact IsPGroup.isCyclic_of_isZGroup (G := E) (P := (R : Subgroup E))
    R.isPGroup'

private def theorem_13_17_QW2ClassifierSourceData
    {G : Type u} [Group G] [Finite G]
    (W1 W2 Q : Subgroup G) (p q : ℕ) : Prop :=
  Nat.Prime p ∧
    Nat.Prime q ∧
      p ≠ q ∧
        Nat.card W1 = q ∧
          Nat.card W2 = p ∧
            IsElementaryAbelian q Q ∧
              W1 ≤ Q ∧
                IsCyclic W2 ∧
                  Q ⊔ W2 ≤ Subgroup.normalizer (Q : Set G)

private theorem section13_prime_p_of_sourceContext
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d) :
    Nat.Prime p := by
  exact
    section13_prime_q_of_sourceContext
      Tmax Smax W W2 W1 Q P V U D C Tfam Sfam τT τS
      q p v u d c (section13_hypothesis_13_1_sourceData_swap hsource)

private theorem section13_p_ne_q_of_sourceContext
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d) :
    p ≠ q := by
  have hqprime : Nat.Prime q :=
    section13_prime_q_of_sourceContext
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
      p q u v c d hsource
  rcases hsource with
    ⟨hcase, _hptypeS, _hptypeT, hp_card, hq_card, _hC, _hD, _hc_card,
      _hd_card, _hU_card, _hV_card, _hSfam, _hTfam, _hDadeS, _hDadeT,
      _hnotationData, _hDadeDiff, _hZeroDegree, _hConjIndex, _hConjBetaTau,
      _hChoice, _hMin, _hFourSixS, _hFourSixT⟩
  rcases hcase with
    ⟨hprod, hWcyc, _hW1ne, _hW2ne, _hnorm, _hSmax, _hTmax, _hSF, _hTF,
      _hSeq, _hTeq, _hSdisj, _hTdisj, _hST, _hTypeII, _hSType, _hTType,
      _hCover⟩
  have hcop_cards : Nat.Coprime (Nat.card W1) (Nat.card W2) :=
    section13_natCard_coprime_of_section12InternalDirectProduct_cyclic hprod hWcyc
  have hcop_qp : Nat.Coprime q p := by
    simpa [hq_card, hp_card] using hcop_cards
  intro hpq
  have hcop_qq : Nat.Coprime q q := by
    simpa [hpq] using hcop_qp
  exact hqprime.ne_one (Nat.Coprime.eq_one_of_dvd hcop_qq dvd_rfl)

private theorem section13_theorem_13_17_QW2_classifierData_of_sourceContext
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d) :
    theorem_13_17_QW2ClassifierSourceData W1 W2 Q p q := by
  have hsourceOrig := hsource
  rcases hsource with
    ⟨_hcaseB, _hptypeS, hptypeT, hp_card, hq_card, _hC, _hD, _hc_card,
      _hd_card, _hU_card, _hV_card, _hSfam, _hTfam, _hDadeS, _hDadeT,
      _hnotationData, _hDadeDiff, _hZeroDegree, _hConjIndex, _hConjBetaTau,
      _hChoice, _hMin, _hFourSixS, _hFourSixT⟩
  rcases hptypeT with
    ⟨hQMF, hW2cyc, _hW2ne, _hW2Hall, hTcomp, _hVleDer, _hVnil, _hW2norm,
      _hDercomp, _hQnotcyc, _hsecond, _hfit, _hfitDer, hW1leQinf,
      _hW1cyc, _hW1ne, _hcent, _hnormType⟩
  have hQleT : Q ≤ Tmax := Section12.section16MFSubgroup_le hQMF
  have hW2leT : W2 ≤ Tmax := hTcomp.2.1
  have hTleNormQ : Tmax ≤ Subgroup.normalizer (Q : Set G) := by
    rcases hQMF with ⟨⟨hQT, hQnormT, _hQnil, _hQhallT⟩, _hmax⟩
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer hQT).1 hQnormT
  have hQW2leNormQ : Q ⊔ W2 ≤ Subgroup.normalizer (Q : Set G) :=
    (sup_le hQleT hW2leT).trans hTleNormQ
  have hsourceT := section13_hypothesis_13_1_sourceData_swap hsourceOrig
  have h2T := theorem_13_2 Tmax Smax W W2 W1 Q P V U D C
    Tfam Sfam τT τS q p v u d c hsourceT
  rcases h2T with
    ⟨_hMF, _hType, _hTypeIf, _hVcomm, _hFrob, hQelem, _hQcard, _hvBound,
      _hcoh, _hTI, _hTau⟩
  exact
    ⟨section13_prime_p_of_sourceContext
        Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
        p q u v c d hsourceOrig,
      section13_prime_q_of_sourceContext
        Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
        p q u v c d hsourceOrig,
      section13_p_ne_q_of_sourceContext
        Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
        p q u v c d hsourceOrig,
      hq_card.symm, hp_card.symm, hQelem, hW1leQinf.trans inf_le_left, hW2cyc,
      hQW2leNormQ⟩

private theorem section13_cyclic_subgroup_of_elementary_card_eq_prime
    {G : Type u} [Group G] [Finite G]
    {Q N W1 : Subgroup G} {q : ℕ}
    (hq : Nat.Prime q)
    (_hQelem : IsElementaryAbelian q Q)
    (hNleQ : N ≤ Q)
    (hNcyc : IsCyclic N)
    (hW1leN : W1 ≤ N)
    (hW1card : Nat.card W1 = q) :
    Nat.card N = q := by
  have hcard_dvd : Nat.card N ∣ q := by
    rw [← hNcyc.exponent_eq_card]
    refine Monoid.exponent_dvd_iff_forall_pow_eq_one.2 ?_
    intro x
    apply Subtype.ext
    have hxQ : (⟨(x : G), hNleQ x.2⟩ : Q) ^ q = 1 :=
      Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p q Q) ⟨(x : G), hNleQ x.2⟩
    simpa using congrArg (fun y : Q => ((y : Q) : G)) hxQ
  rcases (Nat.dvd_prime hq).1 hcard_dvd with hcard_one | hcard_q
  · have hNbot : N = ⊥ := (Subgroup.eq_bot_iff_card (H := N)).2 hcard_one
    have hW1bot : W1 = ⊥ :=
      le_bot_iff.mp (hW1leN.trans (le_of_eq hNbot))
    have hW1card_one : Nat.card W1 = 1 :=
      (Subgroup.eq_bot_iff_card (H := W1)).1 hW1bot
    exact False.elim (hq.ne_one (hW1card.symm.trans hW1card_one))
  · exact hcard_q

private theorem section13_inf_Q_isCyclic_of_cyclic_sylow_elementary
    {G : Type u} [Group G] [Finite G]
    {Q E : Subgroup G} {q : ℕ}
    (hq : Nat.Prime q)
    (hQelem : IsElementaryAbelian q Q)
    (hSylowCyclic : ∀ r : Nat.Primes, ∀ R : Sylow r.val E, IsCyclic R) :
    IsCyclic (E ⊓ Q : Subgroup G) := by
  classical
  let : Fact q.Prime := ⟨hq⟩
  let N : Subgroup G := E ⊓ Q
  have hNleE : N ≤ E := inf_le_left
  have hNleQ : N ≤ Q := inf_le_right
  have hQp : IsPGroup q Q := by
    let : IsElementaryAbelian q Q := hQelem
    exact IsElementaryAbelian.isPGroup q Q
  have hNQp : IsPGroup q (N.subgroupOf Q) :=
    hQp.to_subgroup (N.subgroupOf Q)
  have hNp : IsPGroup q N :=
    hNQp.of_equiv (Subgroup.subgroupOfEquivOfLe (H := N) (K := Q) hNleQ)
  have hNsubEp : IsPGroup q (N.subgroupOf E) :=
    hNp.of_equiv
      (Subgroup.subgroupOfEquivOfLe (H := N) (K := E) hNleE).symm
  obtain ⟨R, hNleR⟩ := IsPGroup.exists_le_sylow (G := E) hNsubEp
  have hRcyc : IsCyclic (R : Subgroup E) := hSylowCyclic ⟨q, hq⟩ R
  have hNsubEcyc : IsCyclic (N.subgroupOf E) := by
    let : IsCyclic (R : Subgroup E) := hRcyc
    exact Subgroup.isCyclic_of_le hNleR
  exact
    (Subgroup.subgroupOfEquivOfLe (H := N) (K := E) hNleE).isCyclic.1
      hNsubEcyc

private theorem section13_E_inf_Q_card_eq_W1_of_QW2_classifierData
    {G : Type u} [Group G] [Finite G]
    (W1 W2 Q : Subgroup G) (p q : ℕ)
    (hdata : theorem_13_17_QW2ClassifierSourceData W1 W2 Q p q)
    (E : Subgroup G)
    (hSylowCyclic : ∀ r : Nat.Primes, ∀ R : Sylow r.val E, IsCyclic R)
    (hW1leE : W1 ≤ E) :
    Nat.card (E ⊓ Q : Subgroup G) = Nat.card W1 := by
  rcases hdata with
    ⟨_hp, hq, _hpne, hW1card, _hW2card, hQelem, hW1leQ, _hW2cyc,
      _hQW2leNormQ⟩
  have hNcyc : IsCyclic (E ⊓ Q : Subgroup G) :=
    section13_inf_Q_isCyclic_of_cyclic_sylow_elementary
      (Q := Q) (E := E) hq hQelem hSylowCyclic
  have hW1leN : W1 ≤ E ⊓ Q := le_inf hW1leE hW1leQ
  exact
    (section13_cyclic_subgroup_of_elementary_card_eq_prime
        (Q := Q) (N := E ⊓ Q) (W1 := W1) hq hQelem inf_le_right hNcyc
        hW1leN hW1card).trans hW1card.symm

private theorem section13_E_card_eq_W1_of_le_Q_of_QW2_classifierData
    {G : Type u} [Group G] [Finite G]
    (W1 W2 Q : Subgroup G) (p q : ℕ)
    (hdata : theorem_13_17_QW2ClassifierSourceData W1 W2 Q p q)
    (E : Subgroup G)
    (hSylowCyclic : ∀ r : Nat.Primes, ∀ R : Sylow r.val E, IsCyclic R)
    (hW1leE : W1 ≤ E)
    (hEleQ : E ≤ Q) :
    Nat.card E = Nat.card W1 := by
  have hEinfQcard :
      Nat.card (E ⊓ Q : Subgroup G) = Nat.card W1 :=
    section13_E_inf_Q_card_eq_W1_of_QW2_classifierData
      W1 W2 Q p q hdata E hSylowCyclic hW1leE
  simpa [inf_eq_left.2 hEleQ] using hEinfQcard

private theorem section13_coprime_p_card_Q_of_QW2_classifierData
    {G : Type u} [Group G] [Finite G]
    (W1 W2 Q : Subgroup G) (p q : ℕ)
    (hdata : theorem_13_17_QW2ClassifierSourceData W1 W2 Q p q) :
    Nat.Coprime p (Nat.card Q) := by
  rcases hdata with
    ⟨hp, hq, hpne, _hW1card, _hW2card, hQelem, _hW1leQ, _hW2cyc,
      _hQW2leNormQ⟩
  let : IsElementaryAbelian q Q := hQelem
  let : Fact q.Prime := ⟨hq⟩
  have hQp : IsPGroup q Q := IsElementaryAbelian.isPGroup q Q
  rcases hQp.exists_card_eq with ⟨n, hcard⟩
  rw [hcard]
  exact hq.coprime_pow_of_not_dvd (m := n) (a := p) (by
    intro hq_dvd_p
    exact hpne ((hp.dvd_iff_eq hq.ne_one).1 hq_dvd_p))

private theorem section13_W2_inf_Q_eq_bot_of_QW2_classifierData
    {G : Type u} [Group G] [Finite G]
    (W1 W2 Q : Subgroup G) (p q : ℕ)
    (hdata : theorem_13_17_QW2ClassifierSourceData W1 W2 Q p q) :
    W2 ⊓ Q = ⊥ := by
  have hcop : Nat.Coprime p (Nat.card Q) :=
    section13_coprime_p_card_Q_of_QW2_classifierData W1 W2 Q p q hdata
  rcases hdata with
    ⟨_hp, _hq, _hpne, _hW1card, hW2card, _hQelem, _hW1leQ, _hW2cyc,
      _hQW2leNormQ⟩
  exact section13_inf_eq_bot_of_card_right_coprime hW2card.symm hcop.symm

private theorem section13_Q_normal_in_Q_sup_W2_of_QW2_classifierData
    {G : Type u} [Group G] [Finite G]
    (W1 W2 Q : Subgroup G) (p q : ℕ)
    (hdata : theorem_13_17_QW2ClassifierSourceData W1 W2 Q p q) :
    (Q.subgroupOf (Q ⊔ W2 : Subgroup G)).Normal := by
  rcases hdata with
    ⟨_hp, _hq, _hpne, _hW1card, _hW2card, _hQelem, _hW1leQ, _hW2cyc,
      hQW2leNormQ⟩
  exact (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).2 hQW2leNormQ

private theorem section13_Q_W2_isComplement_in_Q_sup_W2_of_QW2_classifierData
    {G : Type u} [Group G] [Finite G]
    (W1 W2 Q : Subgroup G) (p q : ℕ)
    (hdata : theorem_13_17_QW2ClassifierSourceData W1 W2 Q p q) :
    (Q.subgroupOf (Q ⊔ W2 : Subgroup G)).IsComplement'
      (W2.subgroupOf (Q ⊔ W2 : Subgroup G)) := by
  classical
  let K : Subgroup G := Q ⊔ W2
  let QK : Subgroup K := Q.subgroupOf K
  let W2K : Subgroup K := W2.subgroupOf K
  have hQnorm : QK.Normal := by
    simpa [K, QK] using
      section13_Q_normal_in_Q_sup_W2_of_QW2_classifierData W1 W2 Q p q hdata
  have hdisjAmbient : W2 ⊓ Q = ⊥ :=
    section13_W2_inf_Q_eq_bot_of_QW2_classifierData W1 W2 Q p q hdata
  have hdisj : Disjoint QK W2K := by
    rw [Subgroup.disjoint_def]
    intro x hxQ hxW2
    apply Subtype.ext
    have hxQG : (x : G) ∈ Q := by
      simpa [QK, Subgroup.mem_subgroupOf] using hxQ
    have hxW2G : (x : G) ∈ W2 := by
      simpa [W2K, Subgroup.mem_subgroupOf] using hxW2
    have hxInf : (x : G) ∈ W2 ⊓ Q := ⟨hxW2G, hxQG⟩
    have hxBot : (x : G) ∈ (⊥ : Subgroup G) := by
      simpa [hdisjAmbient] using hxInf
    simpa using hxBot
  refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hdisj ?_
  rw [Set.eq_univ_iff_forall]
  intro x
  have hxSup : x ∈ QK ⊔ W2K := by
    have htop : QK ⊔ W2K = ⊤ := by
      simpa [K, QK, W2K] using
        (Subgroup.subgroupOf_sup (A := Q) (A' := W2) (B := K)
          le_sup_left le_sup_right).symm
    rw [htop]
    trivial
  rcases (Subgroup.mem_sup_of_normal_left (s := QK) (t := W2K) (x := x)).1
      hxSup with
    ⟨q0, hq0, w0, hw0, hq0w0⟩
  exact ⟨q0, hq0, w0, hw0, hq0w0⟩

private theorem section13_quotient_image_ne_bot_of_not_le
    {G : Type u} [Group G]
    {K N E : Subgroup G}
    (hNnorm : (N.subgroupOf K).Normal)
    (hEleK : E ≤ K)
    (hEnotleN : ¬ E ≤ N) :
    (E.subgroupOf K).map (QuotientGroup.mk' (N.subgroupOf K)) ≠ ⊥ := by
  classical
  let : (N.subgroupOf K).Normal := hNnorm
  intro hmap
  apply hEnotleN
  intro x hxE
  let xK : K := ⟨x, hEleK hxE⟩
  have hxEsub : xK ∈ E.subgroupOf K := by
    simpa [xK, Subgroup.mem_subgroupOf] using hxE
  have hxmap :
      QuotientGroup.mk' (N.subgroupOf K) xK ∈
        (E.subgroupOf K).map (QuotientGroup.mk' (N.subgroupOf K)) :=
    Subgroup.mem_map_of_mem (QuotientGroup.mk' (N.subgroupOf K)) hxEsub
  have hxone : QuotientGroup.mk' (N.subgroupOf K) xK = 1 := by
    simpa [hmap] using hxmap
  have hxker : xK ∈ (QuotientGroup.mk' (N.subgroupOf K)).ker :=
    (MonoidHom.mem_ker (f := QuotientGroup.mk' (N.subgroupOf K)) (x := xK)).2
      hxone
  have hxNsub : xK ∈ N.subgroupOf K := by
    simpa [QuotientGroup.ker_mk'] using hxker
  simpa [xK, Subgroup.mem_subgroupOf] using hxNsub

private theorem section13_Q_sup_W2_quotient_Q_card_eq_p_of_QW2_classifierData
    {G : Type u} [Group G] [Finite G]
    (W1 W2 Q : Subgroup G) (p q : ℕ)
    (hdata : theorem_13_17_QW2ClassifierSourceData W1 W2 Q p q) :
    Nat.card ((Q ⊔ W2 : Subgroup G) ⧸
      Q.subgroupOf (Q ⊔ W2 : Subgroup G)) = p := by
  let K : Subgroup G := Q ⊔ W2
  let QK : Subgroup K := Q.subgroupOf K
  let W2K : Subgroup K := W2.subgroupOf K
  have hcomp : QK.IsComplement' W2K := by
    simpa [K, QK, W2K] using
      section13_Q_W2_isComplement_in_Q_sup_W2_of_QW2_classifierData
        W1 W2 Q p q hdata
  rcases hdata with
    ⟨_hp, _hq, _hpne, _hW1card, hW2card, _hQelem, _hW1leQ, _hW2cyc,
      _hQW2leNormQ⟩
  calc
    Nat.card (K ⧸ QK) = QK.index := (Subgroup.index_eq_card (H := QK)).symm
    _ = Nat.card W2K := (Subgroup.IsComplement'.symm hcomp).index_eq_card
    _ = Nat.card W2 := natCard_subgroupOf_eq W2 K le_sup_right
    _ = p := hW2card

private theorem section13_E_quotient_Q_image_card_eq_p_of_QW2_classifierData
    {G : Type u} [Group G] [Finite G]
    (W1 W2 Q : Subgroup G) (p q : ℕ)
    (hdata : theorem_13_17_QW2ClassifierSourceData W1 W2 Q p q)
    (E : Subgroup G)
    (hEleQW2 : E ≤ Q ⊔ W2)
    (hEnotleQ : ¬ E ≤ Q) :
    let K : Subgroup G := Q ⊔ W2
    let QK : Subgroup K := Q.subgroupOf K
    have : QK.Normal := by
      simpa [K, QK] using
        section13_Q_normal_in_Q_sup_W2_of_QW2_classifierData W1 W2 Q p q hdata
    Nat.card ((E.subgroupOf K).map (QuotientGroup.mk' QK)) = p := by
  classical
  let K : Subgroup G := Q ⊔ W2
  let QK : Subgroup K := Q.subgroupOf K
  let Esub : Subgroup K := E.subgroupOf K
  have hQnorm : QK.Normal := by
    simpa [K, QK] using
      section13_Q_normal_in_Q_sup_W2_of_QW2_classifierData W1 W2 Q p q hdata
  let : QK.Normal := hQnorm
  let π : K →* K ⧸ QK := QuotientGroup.mk' QK
  let Ebar : Subgroup (K ⧸ QK) := Esub.map π
  have hEbar_ne_bot : Ebar ≠ ⊥ := by
    simpa [K, QK, Esub, π, Ebar] using
      section13_quotient_image_ne_bot_of_not_le
        (K := K) (N := Q) (E := E) hQnorm hEleQW2 hEnotleQ
  have hquotcard : Nat.card (K ⧸ QK) = p := by
    simpa [K, QK] using
      section13_Q_sup_W2_quotient_Q_card_eq_p_of_QW2_classifierData W1 W2 Q p q hdata
  have hcard_dvd : Nat.card Ebar ∣ p := by
    have hdvd : Nat.card Ebar ∣ Nat.card (K ⧸ QK) :=
      Subgroup.card_subgroup_dvd_card Ebar
    rw [hquotcard] at hdvd
    exact hdvd
  rcases hdata with
    ⟨hp, _hq, _hpne, _hW1card, _hW2card, _hQelem, _hW1leQ, _hW2cyc,
      _hQW2leNormQ⟩
  rcases (Nat.dvd_prime hp).1 hcard_dvd with hcard_one | hcard_p
  · have hEbar_bot : Ebar = ⊥ :=
      (Subgroup.eq_bot_iff_card (H := Ebar)).2 hcard_one
    exact False.elim (hEbar_ne_bot hEbar_bot)
  · exact hcard_p


private theorem section13_E_card_eq_W1_mul_p_of_QW2_classifierData
    {G : Type u} [Group G] [Finite G]
    (W1 W2 Q : Subgroup G) (p q : ℕ)
    (hdata : theorem_13_17_QW2ClassifierSourceData W1 W2 Q p q)
    (E : Subgroup G)
    (hEleQW2 : E ≤ Q ⊔ W2)
    (hEinfQcard : Nat.card (E ⊓ Q : Subgroup G) = Nat.card W1)
    (hEnotleQ : ¬ E ≤ Q) :
    Nat.card E = Nat.card W1 * p := by
  classical
  let K : Subgroup G := Q ⊔ W2
  let QK : Subgroup K := Q.subgroupOf K
  have hQnorm : QK.Normal := by
    simpa [K, QK] using
      section13_Q_normal_in_Q_sup_W2_of_QW2_classifierData W1 W2 Q p q hdata
  let : QK.Normal := hQnorm
  let π : K →* K ⧸ QK := QuotientGroup.mk' QK
  let Esub : Subgroup K := E.subgroupOf K
  let ι : E →* K := Subgroup.inclusion hEleQW2
  let φ : E →* K ⧸ QK := π.comp ι
  have hker : φ.ker = (E ⊓ Q : Subgroup G).subgroupOf E := by
    ext x
    constructor
    · intro hx
      have hxone : φ x = 1 :=
        (MonoidHom.mem_ker (f := φ) (x := x)).1 hx
      have hxQK : ι x ∈ QK := by
        have hxker : ι x ∈ π.ker :=
          (MonoidHom.mem_ker (f := π) (x := ι x)).2 hxone
        simpa [π, QuotientGroup.ker_mk'] using hxker
      exact ⟨x.2, by simpa [ι, QK, Subgroup.mem_subgroupOf] using hxQK⟩
    · intro hx
      have hxQK : ι x ∈ QK := by
        exact hx.2
      have hxker : ι x ∈ π.ker := by
        simpa [π, QuotientGroup.ker_mk'] using hxQK
      have hxone : φ x = 1 :=
        (MonoidHom.mem_ker (f := π) (x := ι x)).1 hxker
      exact (MonoidHom.mem_ker (f := φ) (x := x)).2 hxone
  have hrange : φ.range = Esub.map π := by
    ext z
    constructor
    · rintro ⟨x, rfl⟩
      refine ⟨ι x, ?_, rfl⟩
      simp [ι, Esub, Subgroup.mem_subgroupOf, x.2]
    · rintro ⟨x, hxEsub, rfl⟩
      have hxE : (x : G) ∈ E := by
        simpa [Esub, Subgroup.mem_subgroupOf] using hxEsub
      refine ⟨⟨(x : G), hxE⟩, ?_⟩
      rfl
  have hrange_card : Nat.card φ.range = p := by
    have hmap_card :
        Nat.card (Esub.map π) = p := by
      simpa [K, QK, Esub, π] using
        section13_E_quotient_Q_image_card_eq_p_of_QW2_classifierData
          W1 W2 Q p q hdata E hEleQW2 hEnotleQ
    simpa [hrange] using hmap_card
  have hker_card : Nat.card φ.ker = Nat.card (E ⊓ Q : Subgroup G) := by
    rw [hker]
    exact natCard_subgroupOf_eq (E ⊓ Q : Subgroup G) E inf_le_left
  have hquot_card : Nat.card (E ⧸ φ.ker) = Nat.card φ.range :=
    Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv
  calc
    Nat.card E = Nat.card (E ⧸ φ.ker) * Nat.card φ.ker :=
      Subgroup.card_eq_card_quotient_mul_card_subgroup (s := φ.ker)
    _ = Nat.card φ.range * Nat.card φ.ker := by rw [hquot_card]
    _ = p * Nat.card (E ⊓ Q : Subgroup G) := by rw [hrange_card, hker_card]
    _ = Nat.card W1 * p := by rw [hEinfQcard, Nat.mul_comm]

private theorem section13_exists_order_p_subgroup_sup_eq_E_of_QW2_classifierData
    {G : Type u} [Group G] [Finite G]
    (W1 W2 Q : Subgroup G) (p q : ℕ)
    (hdata : theorem_13_17_QW2ClassifierSourceData W1 W2 Q p q)
    (E : Subgroup G)
    (hW1leE : W1 ≤ E)
    (hEleQW2 : E ≤ Q ⊔ W2)
    (hEinfQcard : Nat.card (E ⊓ Q : Subgroup G) = Nat.card W1)
    (hEnotleQ : ¬ E ≤ Q) :
    ∃ P : Subgroup G, P ≤ E ∧ Nat.card P = p ∧ E = W1 ⊔ P := by
  classical
  rcases hdata with
    ⟨hp, hq, hpne, hW1card, _hW2card, _hQelem, _hW1leQ, _hW2cyc,
      _hQW2leNormQ⟩
  let : Fact p.Prime := ⟨hp⟩
  have hEcard :
      Nat.card E = Nat.card W1 * p :=
    section13_E_card_eq_W1_mul_p_of_QW2_classifierData
      W1 W2 Q p q
      ⟨hp, hq, hpne, hW1card, _hW2card, _hQelem, _hW1leQ, _hW2cyc,
        _hQW2leNormQ⟩
      E hEleQW2 hEinfQcard hEnotleQ
  have hp_dvd_E : p ^ 1 ∣ Nat.card E := by
    rw [hEcard, pow_one]
    exact dvd_mul_left p (Nat.card W1)
  obtain ⟨PE, hPEcard_pow⟩ :=
    Sylow.exists_subgroup_card_pow_prime (G := E) p (n := 1) hp_dvd_E
  let P : Subgroup G := PE.map E.subtype
  have hPcard : Nat.card P = p := by
    calc
      Nat.card P = Nat.card PE := by
        simpa [P] using
          (Subgroup.card_map_of_injective
            (K := PE) (f := E.subtype) (Subgroup.subtype_injective E))
      _ = p := by simpa [pow_one] using hPEcard_pow
  have hPleE : P ≤ E := by
    intro x hx
    rcases hx with ⟨y, _hy, rfl⟩
    exact y.2
  let W1E : Subgroup E := W1.subgroupOf E
  have hW1Ecard : Nat.card W1E = Nat.card W1 :=
    natCard_subgroupOf_eq W1 E hW1leE
  have hcop_qp : Nat.Coprime q p := by
    exact hq.coprime_iff_not_dvd.2 (by
      intro hq_dvd_p
      exact hpne ((hp.dvd_iff_eq hq.ne_one).1 hq_dvd_p))
  have hdisj : Disjoint W1E PE := by
    have hcop_cards : Nat.Coprime (Nat.card W1E) (Nat.card PE) := by
      rw [hW1Ecard, hW1card, hPEcard_pow, pow_one]
      exact hcop_qp
    exact Subgroup.disjoint_of_coprime_natCard hcop_cards
  have hcard_mul : Nat.card W1E * Nat.card PE = Nat.card E := by
    rw [hW1Ecard, hPEcard_pow, pow_one, hEcard]
  have hcomp : W1E.IsComplement' PE :=
    Subgroup.isComplement'_of_card_mul_and_disjoint hcard_mul hdisj
  have hPsubE : P.subgroupOf E = PE := by
    ext x
    constructor
    · intro hx
      change (x : G) ∈ P at hx
      rcases hx with ⟨y, hy, hyx⟩
      have hyxG : (y : G) = (x : G) := hyx
      have hyxE : y = x := Subtype.ext hyxG
      rw [← hyxE]
      exact hy
    · intro hx
      change (x : G) ∈ P
      exact ⟨x, hx, rfl⟩
  have hsup_subgroupOf : (W1 ⊔ P).subgroupOf E = ⊤ := by
    rw [Subgroup.subgroupOf_sup hW1leE hPleE, hPsubE, hcomp.sup_eq_top]
  have hsup_eq_E : W1 ⊔ P = E := by
    apply le_antisymm
    · exact sup_le hW1leE hPleE
    · intro x hxE
      let xE : E := ⟨x, hxE⟩
      have hxTop : xE ∈ (⊤ : Subgroup E) := trivial
      have hxSub : xE ∈ (W1 ⊔ P).subgroupOf E := by
        simp [hsup_subgroupOf, hxTop]
      simpa [xE, Subgroup.mem_subgroupOf] using hxSub
  exact ⟨P, hPleE, hPcard, hsup_eq_E.symm⟩

private theorem section13_order_p_subgroup_conj_W2_of_QW2_classifierData
    {G : Type u} [Group G] [Finite G]
    (W1 W2 Q : Subgroup G) (p q : ℕ)
    (hdata : theorem_13_17_QW2ClassifierSourceData W1 W2 Q p q)
    (P : Subgroup G)
    (hPleQW2 : P ≤ Q ⊔ W2)
    (hPcard : Nat.card P = p) :
    ∃ y : G, y ∈ Q ∧ P = W2.conjBy y := by
  classical
  rcases hdata with
    ⟨hp, hq, hpne, _hW1card, hW2card, hQelem, _hW1leQ, _hW2cyc,
      _hQW2leNormQ⟩
  let K : Subgroup G := Q ⊔ W2
  let QK : Subgroup K := Q.subgroupOf K
  let W2K : Subgroup K := W2.subgroupOf K
  let PK : Subgroup K := P.subgroupOf K
  have hQnorm : QK.Normal := by
    simpa [K, QK] using
      section13_Q_normal_in_Q_sup_W2_of_QW2_classifierData W1 W2 Q p q
        ⟨hp, hq, hpne, _hW1card, hW2card, hQelem, _hW1leQ, _hW2cyc,
          _hQW2leNormQ⟩
  let : QK.Normal := hQnorm
  let : IsMulCommutative Q := IsElementaryAbelian.toIsMulCommutative q
  let : IsMulCommutative ↥QK := by
    refine IsMulCommutative.mk <| Std.Commutative.mk <| fun a b => ?_
    have haQ : ((a : K) : G) ∈ Q := by
      exact a.2
    have hbQ : ((b : K) : G) ∈ Q := by
      exact b.2
    have hcomm :
        (⟨((a : K) : G), haQ⟩ : Q) *
            (⟨((b : K) : G), hbQ⟩ : Q) =
            (⟨((b : K) : G), hbQ⟩ : Q) *
              (⟨((a : K) : G), haQ⟩ : Q) := by
      exact (IsMulCommutative.is_comm (M := Q)).comm
        ⟨((a : K) : G), haQ⟩ ⟨((b : K) : G), hbQ⟩
    have hcommG :
        ((a : K) : G) * ((b : K) : G) =
          ((b : K) : G) * ((a : K) : G) :=
      congrArg Subtype.val hcomm
    apply Subtype.ext
    apply Subtype.ext
    exact hcommG
  have hcompW2 : QK.IsComplement' W2K := by
    simpa [K, QK, W2K] using
      section13_Q_W2_isComplement_in_Q_sup_W2_of_QW2_classifierData
        W1 W2 Q p q
        ⟨hp, hq, hpne, _hW1card, hW2card, hQelem, _hW1leQ, _hW2cyc,
          _hQW2leNormQ⟩
  have hQKcard : Nat.card QK = Nat.card Q :=
    natCard_subgroupOf_eq Q K le_sup_left
  have hW2Kcard : Nat.card W2K = p := by
    rw [natCard_subgroupOf_eq W2 K le_sup_right, hW2card]
  have hPKcard : Nat.card PK = p := by
    rw [natCard_subgroupOf_eq P K hPleQW2, hPcard]
  have hcop_pQ : Nat.Coprime p (Nat.card Q) :=
    section13_coprime_p_card_Q_of_QW2_classifierData W1 W2 Q p q
      ⟨hp, hq, hpne, _hW1card, hW2card, hQelem, _hW1leQ, _hW2cyc,
        _hQW2leNormQ⟩
  have hPinfQ : P ⊓ Q = ⊥ :=
    section13_inf_eq_bot_of_card_right_coprime hPcard.symm hcop_pQ.symm
  have hdisj : Disjoint QK PK := by
    rw [Subgroup.disjoint_def]
    intro x hxQ hxP
    apply Subtype.ext
    have hxQG : (x : G) ∈ Q := by
      simpa [QK, Subgroup.mem_subgroupOf] using hxQ
    have hxPG : (x : G) ∈ P := by
      simpa [PK, Subgroup.mem_subgroupOf] using hxP
    have hxInf : (x : G) ∈ P ⊓ Q := ⟨hxPG, hxQG⟩
    have hxBot : (x : G) ∈ (⊥ : Subgroup G) := by
      simpa [hPinfQ] using hxInf
    simpa using hxBot
  have hcard_mul : Nat.card QK * Nat.card PK = Nat.card K := by
    calc
      Nat.card QK * Nat.card PK = Nat.card QK * p := by rw [hPKcard]
      _ = Nat.card QK * Nat.card W2K := by rw [hW2Kcard]
      _ = Nat.card K := hcompW2.card_mul_card
  have hcompP : QK.IsComplement' PK :=
    Subgroup.isComplement'_of_card_mul_and_disjoint hcard_mul hdisj
  have hQKindex : QK.index = p := by
    rw [(Subgroup.IsComplement'.symm hcompW2).index_eq_card, hW2Kcard]
  have hcop_QK : Nat.Coprime (Nat.card QK) QK.index := by
    rw [hQKcard, hQKindex]
    exact hcop_pQ.symm
  obtain ⟨yK, hPKconj⟩ :=
    Subgroup.exists_conj_eq_of_isComplement'
      (G := K) (H := QK) (K₁ := W2K) (K₂ := PK)
      hcop_QK hcompW2 hcompP
  let y : G := ((yK : K) : G)
  have hyQ : y ∈ Q := by
    change ((yK : K) : G) ∈ Q
    exact yK.2
  have hPKmap : PK.map K.subtype = P := by
    ext x
    constructor
    · rintro ⟨z, hz, rfl⟩
      simpa [PK, Subgroup.mem_subgroupOf] using hz
    · intro hxP
      exact ⟨⟨x, hPleQW2 hxP⟩, by simpa [PK, Subgroup.mem_subgroupOf] using hxP, rfl⟩
  have hW2map :
      (W2K.map (MulAut.conj (yK : K)).toMonoidHom).map K.subtype =
        W2.conjBy y := by
    simpa [K, W2K, y, Subgroup.conjBy] using
      section10_subgroupOf_conjBy_map_subtype (G := G) (M := K) (H := W2)
        le_sup_right (yK : K)
  have hmap := congrArg (fun S : Subgroup K => S.map K.subtype) hPKconj
  have hPconj : P = W2.conjBy y := by
    have hmap' :
        P = (W2K.map (MulAut.conj (yK : K)).toMonoidHom).map K.subtype := by
      rw [hPKmap] at hmap
      exact hmap
    rw [hW2map] at hmap'
    exact hmap'
  exact ⟨y, hyQ, hPconj⟩

/-- Source blocker for PF `(13.17)(c)`: once cyclicity of the Sylow
subgroups of `E` is known and the `Q`-part of `E` has been identified as
having the same cardinality as `W1`, the remaining source step is the
nontrivial Sylow-conjugacy classification inside `Q ⊔ W2`. -/
private theorem
    section13_theorem_13_17_complement_conjugate_of_QW2_classifierData_of_inf_Q_card_not_le_Q
    {G : Type u} [Group G] [Finite G]
    (W1 W2 Q : Subgroup G)
    (p q : ℕ)
    (_hdata : theorem_13_17_QW2ClassifierSourceData W1 W2 Q p q)
    (E : Subgroup G)
    (_hSylowCyclic : ∀ r : Nat.Primes, ∀ R : Sylow r.val E, IsCyclic R)
    (_hW1leE : W1 ≤ E)
    (_hEleQW2 : E ≤ Q ⊔ W2)
    (_hEinfQcard : Nat.card (E ⊓ Q : Subgroup G) = Nat.card W1)
    (_hEnotleQ : ¬ E ≤ Q) :
    ∃ y : G, y ∈ Q ∧ E = W1 ⊔ W2.conjBy y := by
  rcases
    section13_exists_order_p_subgroup_sup_eq_E_of_QW2_classifierData
      W1 W2 Q p q _hdata E _hW1leE _hEleQW2 _hEinfQcard _hEnotleQ with
    ⟨P, hPleE, hPcard, hEsup⟩
  have hPleQW2 : P ≤ Q ⊔ W2 := hPleE.trans _hEleQW2
  rcases
    section13_order_p_subgroup_conj_W2_of_QW2_classifierData
      W1 W2 Q p q _hdata P hPleQW2 hPcard with
    ⟨y, hyQ, hPconj⟩
  exact ⟨y, hyQ, by simpa [hPconj] using hEsup⟩

private theorem
    section13_theorem_13_17_complement_card_or_conjugate_of_QW2_classifierData
    {G : Type u} [Group G] [Finite G]
    (W1 W2 Q : Subgroup G)
    (p q : ℕ)
    (hdata : theorem_13_17_QW2ClassifierSourceData W1 W2 Q p q)
    (E : Subgroup G)
    (hSylowCyclic : ∀ r : Nat.Primes, ∀ R : Sylow r.val E, IsCyclic R)
    (hW1leE : W1 ≤ E)
    (hEleQW2 : E ≤ Q ⊔ W2) :
    Nat.card E = Nat.card W1 ∨
      ∃ y : G, y ∈ Q ∧ E = W1 ⊔ W2.conjBy y := by
  by_cases hEleQ : E ≤ Q
  · left
    exact
      section13_E_card_eq_W1_of_le_Q_of_QW2_classifierData
        W1 W2 Q p q hdata E hSylowCyclic hW1leE hEleQ
  · right
    exact
      section13_theorem_13_17_complement_conjugate_of_QW2_classifierData_of_inf_Q_card_not_le_Q
        W1 W2 Q p q hdata E hSylowCyclic hW1leE hEleQW2
        (section13_E_inf_Q_card_eq_W1_of_QW2_classifierData
          W1 W2 Q p q hdata E hSylowCyclic hW1leE)
        hEleQ

private theorem
    section13_theorem_13_17_complement_card_or_conjugate_of_cyclic_sylow_Q_sup_W2_sourceContext
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D L H : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (_hTypeII : Section8.typeIIDefinitionData Smax P)
    (_hLmax : L ∈ section9MaximalSubgroups G)
    (_hNormUleL : Subgroup.normalizer (U : Set G) ≤ L)
    (_hMF : section16MFSubgroup L H)
    (_hfrob : Section7.frobeniusWithKernel L H)
    (_hUleH : U ≤ H)
    (_hW1leL : W1 ≤ L)
    (E : Subgroup G)
    (hSylowCyclic : ∀ r : Nat.Primes, ∀ R : Sylow r.val E, IsCyclic R)
    (_hcompE : section12ComplementIn L H E)
    (hW1leE : W1 ≤ E)
    (hEleQW2 : E ≤ Q ⊔ W2) :
    Nat.card E = Nat.card W1 ∨
      ∃ y : G, y ∈ Q ∧ E = W1 ⊔ W2.conjBy y := by
  exact
    section13_theorem_13_17_complement_card_or_conjugate_of_QW2_classifierData
      W1 W2 Q p q
      (section13_theorem_13_17_QW2_classifierData_of_sourceContext
        Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
        p q u v c d hsource)
      E hSylowCyclic hW1leE hEleQW2

/-- PF `(13.17)(c)` source classifier with the cyclic-Sylow input supplied
from the odd Frobenius-complement theorem. -/
private theorem section13_theorem_13_17_complement_card_or_conjugate_of_Q_sup_W2_sourceContext
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D L H : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (hTypeII : Section8.typeIIDefinitionData Smax P)
    (hLmax : L ∈ section9MaximalSubgroups G)
    (hNormUleL : Subgroup.normalizer (U : Set G) ≤ L)
    (hMF : section16MFSubgroup L H)
    (hfrob : Section7.frobeniusWithKernel L H)
    (hUleH : U ≤ H)
    (hW1leL : W1 ≤ L)
    (E : Subgroup G)
    (hcompE : section12ComplementIn L H E)
    (hW1leE : W1 ≤ E)
    (hEleQW2 : E ≤ Q ⊔ W2) :
    Nat.card E = Nat.card W1 ∨
      ∃ y : G, y ∈ Q ∧ E = W1 ⊔ W2.conjBy y := by
  have hsourceOrig := hsource
  rcases hsource with
    ⟨_hcaseB, hptypeS, _hptypeT, _hp_card, _hq_card, _hC, _hD, _hc_card,
      _hd_card, _hU_card, _hV_card, _hSfam, _hTfam, _hDadeS, _hDadeT,
      _hnotationData, _hDadeDiff, _hZeroDegree, _hConjIndex, _hConjBetaTau,
      _hChoice, _hMin, _hFourSixS, _hFourSixT⟩
  rcases hptypeS with
    ⟨_hSMF, _hW1cyc, hW1ne, _hW1hall, _hcompMW1, _hUleD, _hUnil,
      _hW1normU, _hcompDU, _hMFnotcyc, _hsecond, _hfit, _hfitD,
      _hW2le, _hW2cyc, _hW2ne, _hcent, _hnormHat⟩
  have hEne : E ≠ ⊥ := by
    intro hEbot
    apply hW1ne
    apply le_antisymm
    · intro x hx
      have hxE : x ∈ E := hW1leE hx
      simpa [hEbot] using hxE
    · exact bot_le
  have hfrobE :
      IsFrobeniusGroupWithKernelComplement (H.subgroupOf L) (E.subgroupOf L) :=
    section13_frobeniusWithKernel_complementIn_isFrobenius hfrob hcompE hEne
  have hnotS :
      ∀ g : G, L ≠ Smax.conjBy g :=
    section13_theorem_13_17_L_not_conj_Smax_of_sourceContext
      Smax Tmax W W1 W2 P Q U V C D L H Sfam Tfam τS τT
      p q u v c d hsourceOrig hTypeII hLmax hNormUleL hMF
  have hnotT :
      ∀ g : G, L ≠ Tmax.conjBy g :=
    section13_theorem_13_17_L_not_conj_Tmax_of_sourceContext
      Smax Tmax W W1 W2 P Q U V C D L H Sfam Tfam τS τT
      p q u v c d hsourceOrig hTypeII hLmax hNormUleL hMF
  have hTypeI :
      Section8.typeIDefinitionData L H :=
    section13_theorem_13_17_typeI_of_not_conj_sourceContext
      Smax Tmax W W1 W2 P Q U V C D L H Sfam Tfam τS τT
      p q u v c d hsourceOrig hLmax hMF hnotS hnotT
  have hoddE : Odd (Nat.card E) :=
    odd_of_card_dvd (Section12.odd_card_of_typeIDefinitionData L H hTypeI)
      (Subgroup.card_dvd_of_le hcompE.2.1)
  have hSylowCyclic :
      ∀ r : Nat.Primes, ∀ R : Sylow r.val E, IsCyclic R := by
    intro r R
    exact section13_sylow_isCyclic_of_odd_frobenius_complement
      hcompE hfrobE hoddE r R
  exact
    section13_theorem_13_17_complement_card_or_conjugate_of_cyclic_sylow_Q_sup_W2_sourceContext
      Smax Tmax W W1 W2 P Q U V C D L H Sfam Tfam τS τT
      p q u v c d hsourceOrig hTypeII hLmax hNormUleL hMF hfrob hUleH hW1leL
      E hSylowCyclic hcompE hW1leE hEleQW2

/-- PF `(13.17)(c)` classifier, with the cardinality branch discharged
formally from `W1 ≤ E`. -/
private theorem section13_theorem_13_17_complement_alternative_of_Q_sup_W2_sourceContext
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D L H : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (hTypeII : Section8.typeIIDefinitionData Smax P)
    (hLmax : L ∈ section9MaximalSubgroups G)
    (hNormUleL : Subgroup.normalizer (U : Set G) ≤ L)
    (hMF : section16MFSubgroup L H)
    (hfrob : Section7.frobeniusWithKernel L H)
    (hUleH : U ≤ H)
    (hW1leL : W1 ≤ L)
    (E : Subgroup G)
    (hcompE : section12ComplementIn L H E)
    (hW1leE : W1 ≤ E)
    (hEleQW2 : E ≤ Q ⊔ W2) :
    E = W1 ∨ ∃ y : G, y ∈ Q ∧ E = W1 ⊔ W2.conjBy y := by
  rcases section13_theorem_13_17_complement_card_or_conjugate_of_Q_sup_W2_sourceContext
      Smax Tmax W W1 W2 P Q U V C D L H Sfam Tfam τS τT
      p q u v c d hsource hTypeII hLmax hNormUleL hMF hfrob hUleH hW1leL
      E hcompE hW1leE hEleQW2 with hcard | hconj
  · exact Or.inl (section13_eq_of_le_of_card_eq hW1leE hcard)
  · exact Or.inr hconj

/-- Wrapper for PF `(13.17)(c)`: once a complement contains `W1`, the source
normality step and public `(13.16)` reduce it to the final equality
alternative. -/
private theorem section13_theorem_13_17_complement_alternative_of_W1_le_sourceContext
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (Smax Tmax W W1 W2 P Q U V C D L H : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (_hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (_hTypeII : Section8.typeIIDefinitionData Smax P)
    (_hLmax : L ∈ section9MaximalSubgroups G)
    (_hNormUleL : Subgroup.normalizer (U : Set G) ≤ L)
    (_hMF : section16MFSubgroup L H)
    (_hfrob : Section7.frobeniusWithKernel L H)
    (_hUleH : U ≤ H)
    (_hW1leL : W1 ≤ L)
    (E : Subgroup G)
    (_hcompE : section12ComplementIn L H E)
    (_hW1leE : W1 ≤ E) :
    E = W1 ∨ ∃ y : G, y ∈ Q ∧ E = W1 ⊔ W2.conjBy y := by
  have hEleNorm :
      E ≤ Subgroup.normalizer (W1 : Set G) :=
    section13_theorem_13_17_complement_le_normalizer_W1_of_sourceContext
      Smax Tmax W W1 W2 P Q U V C D L H Sfam Tfam τS τT
      p q u v c d _hsource _hTypeII _hLmax _hNormUleL _hMF _hfrob
      _hUleH _hW1leL E _hcompE _hW1leE
  exact section13_theorem_13_17_complement_alternative_of_Q_sup_W2_sourceContext
    Smax Tmax W W1 W2 P Q U V C D L H Sfam Tfam τS τT
    p q u v c d _hsource _hTypeII _hLmax _hNormUleL _hMF _hfrob
    _hUleH _hW1leL E _hcompE _hW1leE
    (section13_theorem_13_17_complement_le_Q_sup_W2_of_normalizer
      Smax Tmax W W1 W2 P Q U V C D E Sfam Tfam τS τT
      p q u v c d _hsource hEleNorm)

/-- Source wrapper for PF `(13.17)(c)`: produce the Frobenius complement `E`
and the equality alternative inside `Q ⊔ W2`. -/
private theorem section13_theorem_13_17_complement_sourceData_of_sourceContext
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (Smax Tmax W W1 W2 P Q U V C D L H : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (_hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (_hTypeII : Section8.typeIIDefinitionData Smax P)
    (_hLmax : L ∈ section9MaximalSubgroups G)
    (_hNormUleL : Subgroup.normalizer (U : Set G) ≤ L)
    (_hMF : section16MFSubgroup L H)
    (_hfrob : Section7.frobeniusWithKernel L H)
    (_hUleH : U ≤ H)
    (_hW1leL : W1 ≤ L) :
    ∃ E : Subgroup G,
      section12ComplementIn L H E ∧
        (E = W1 ∨ ∃ y : G, y ∈ Q ∧ E = W1 ⊔ W2.conjBy y) := by
  rcases section13_theorem_13_17_W1_containing_complement_sourceData_of_sourceContext
      Smax Tmax W W1 W2 P Q U V C D L H Sfam Tfam τS τT
      p q u v c d _hsource _hTypeII _hLmax _hNormUleL _hMF _hfrob
      _hUleH _hW1leL with
    ⟨E, hcompE, hW1leE⟩
  exact ⟨E, hcompE,
    section13_theorem_13_17_complement_alternative_of_W1_le_sourceContext
      Smax Tmax W W1 W2 P Q U V C D L H Sfam Tfam τS τT
      p q u v c d _hsource _hTypeII _hLmax _hNormUleL _hMF _hfrob
      _hUleH _hW1leL E hcompE hW1leE⟩

/-- Peterfalvi `(13.17)`, assembled from the explicit source substeps above. -/
public theorem theorem_13_17
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (Smax Tmax W W1 W2 P Q U V C D L H : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
        Sfam Tfam τS τT p q u v c d →
      Section8.typeIIDefinitionData Smax P →
        L ∈ section9MaximalSubgroups G →
          Subgroup.normalizer (U : Set G) ≤ L →
            section16MFSubgroup L H →
              Section7.frobeniusWithKernel L H ∧
                U ≤ H ∧
                (section12ComplementIn L H W1 ∨
                  ∃ y : G, y ∈ Q ∧
                    section12ComplementIn L H (W1 ⊔ W2.conjBy y)) := by
  intro hsource hTypeII hLmax hNormUleL hMF
  have hnotS : ∀ g : G, L ≠ Smax.conjBy g :=
    section13_theorem_13_17_L_not_conj_Smax_of_sourceContext
      Smax Tmax W W1 W2 P Q U V C D L H Sfam Tfam τS τT
      p q u v c d hsource hTypeII hLmax hNormUleL hMF
  have hnotT : ∀ g : G, L ≠ Tmax.conjBy g :=
    section13_theorem_13_17_L_not_conj_Tmax_of_sourceContext
      Smax Tmax W W1 W2 P Q U V C D L H Sfam Tfam τS τT
      p q u v c d hsource hTypeII hLmax hNormUleL hMF
  have hfrob : Section7.frobeniusWithKernel L H :=
    section13_theorem_13_17_frobenius_of_not_conj_sourceContext
      Smax Tmax W W1 W2 P Q U V C D L H Sfam Tfam τS τT
      p q u v c d hsource hLmax hMF hnotS hnotT
  have hUleL : U ≤ L :=
    section13_theorem_13_17_U_le_L_of_normalizer hNormUleL
  have hW1leL : W1 ≤ L :=
    section13_theorem_13_17_W1_le_L_of_sourceContext
      Smax Tmax W W1 W2 P Q U V C D L Sfam Tfam τS τT
      p q u v c d hsource hNormUleL
  have hUleH : U ≤ H :=
    section13_theorem_13_17_U_le_H_of_sourceContext
      Smax Tmax W W1 W2 P Q U V C D L H Sfam Tfam τS τT
      p q u v c d hsource hTypeII hLmax hNormUleL hMF hfrob hUleL hW1leL
  rcases section13_theorem_13_17_complement_sourceData_of_sourceContext
      Smax Tmax W W1 W2 P Q U V C D L H Sfam Tfam τS τT
      p q u v c d hsource hTypeII hLmax hNormUleL hMF hfrob hUleH hW1leL with
    ⟨E, hcompE, halt⟩
  exact ⟨hfrob, hUleH,
    section13_theorem_13_17_complement_alternative_of_complement_eq hcompE halt⟩

/-- The Type-I conclusion underlying PF `(13.17)(a)`, exposed for later
Section 14 setup choices. -/
public theorem theorem_13_17_typeIDefinitionData
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D L H : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (hTypeII : Section8.typeIIDefinitionData Smax P)
    (hLmax : L ∈ section9MaximalSubgroups G)
    (hNormUleL : Subgroup.normalizer (U : Set G) ≤ L)
    (hMF : section16MFSubgroup L H) :
    Section8.typeIDefinitionData L H := by
  have hnotS : ∀ g : G, L ≠ Smax.conjBy g :=
    section13_theorem_13_17_L_not_conj_Smax_of_sourceContext
      Smax Tmax W W1 W2 P Q U V C D L H Sfam Tfam τS τT
      p q u v c d hsource hTypeII hLmax hNormUleL hMF
  have hnotT : ∀ g : G, L ≠ Tmax.conjBy g :=
    section13_theorem_13_17_L_not_conj_Tmax_of_sourceContext
      Smax Tmax W W1 W2 P Q U V C D L H Sfam Tfam τS τT
      p q u v c d hsource hTypeII hLmax hNormUleL hMF
  exact section13_theorem_13_17_typeI_of_not_conj_sourceContext
    Smax Tmax W W1 W2 P Q U V C D L H Sfam Tfam τS τT
    p q u v c d hsource hLmax hMF hnotS hnotT
end CFSG.Section13
