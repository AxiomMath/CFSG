module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KDiagL2

public noncomputable section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open Subgroup
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley


abbrev G2Adj (K : Type) [Field K] : Type := ↥(adjointGroup Tag.G2 K)

section Overgroups

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem g2_borel_overgroups {A : Subgroup (ModGL Tag.G2 K)}
    (hB : borelGroup Tag.G2 K ≤ A) (hA : A ≤ adjointGroup Tag.G2 K) :
    A = borelGroup Tag.G2 K ∨
      A = parabolicSubgroup Tag.G2 K {⟨0, by decide⟩} ∨
      A = parabolicSubgroup Tag.G2 K {⟨1, by decide⟩} ∨
      A = adjointGroup Tag.G2 K := by
  have hJ := eq_parabolicSubgroup_of_borelGroup_le hB hA
  have hcells := standard_parabolic_cells (τ := Tag.G2) (K := K)
  have hcases : ∀ i : Fin Tag.G2.rank, i = ⟨0, by decide⟩ ∨ i = ⟨1, by decide⟩ := by decide
  have key : {i | weylElt Tag.G2 K i 1 ∈ A} = {⟨0, by decide⟩} ∨
      {i | weylElt Tag.G2 K i 1 ∈ A} = {⟨1, by decide⟩} ∨
      {i | weylElt Tag.G2 K i 1 ∈ A} = Set.univ ∨
      {i | weylElt Tag.G2 K i 1 ∈ A} = ∅ := by
    by_cases h0 : weylElt Tag.G2 K (⟨0, by decide⟩ : Fin Tag.G2.rank) 1 ∈ A
    · by_cases h1 : weylElt Tag.G2 K (⟨1, by decide⟩ : Fin Tag.G2.rank) 1 ∈ A
      · refine Or.inr (Or.inr (Or.inl ?_))
        ext j
        rcases hcases j with rfl | rfl
        · rw [Set.mem_setOf_eq]; exact iff_of_true h0 trivial
        · rw [Set.mem_setOf_eq]; exact iff_of_true h1 trivial
      · refine Or.inl ?_
        ext j
        rcases hcases j with rfl | rfl
        · rw [Set.mem_setOf_eq, Set.mem_singleton_iff]; exact iff_of_true h0 rfl
        · rw [Set.mem_setOf_eq, Set.mem_singleton_iff]; exact iff_of_false h1 (by decide)
    · by_cases h1 : weylElt Tag.G2 K (⟨1, by decide⟩ : Fin Tag.G2.rank) 1 ∈ A
      · refine Or.inr (Or.inl ?_)
        ext j
        rcases hcases j with rfl | rfl
        · rw [Set.mem_setOf_eq, Set.mem_singleton_iff]; exact iff_of_false h0 (by decide)
        · rw [Set.mem_setOf_eq, Set.mem_singleton_iff]; exact iff_of_true h1 rfl
      · refine Or.inr (Or.inr (Or.inr ?_))
        ext j
        rcases hcases j with rfl | rfl
        · rw [Set.mem_setOf_eq, Set.mem_empty_iff_false]; exact iff_of_false h0 (by simp)
        · rw [Set.mem_setOf_eq, Set.mem_empty_iff_false]; exact iff_of_false h1 (by simp)
  rcases key with h | h | h | h
  · rw [hJ, h]; exact Or.inr (Or.inl rfl)
  · rw [hJ, h]; exact Or.inr (Or.inr (Or.inl rfl))
  · rw [hJ, h, hcells.2.2.2.2.2.1]; exact Or.inr (Or.inr (Or.inr rfl))
  · rw [hJ, h, hcells.2.2.2.2.1]; exact Or.inl rfl

end Overgroups

section Model

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem kDiag_adjointGroup_G2_strong (hK : 4 ≤ Nat.card K) :
    ∀ (θ : MulAut (G2Adj K)),
    ∀ S : Sylow 2 (G2Adj K),
      (∀ x ∈ (S : Subgroup (G2Adj K)), θ x ∈ (S : Subgroup (G2Adj K))) →
    ∀ P : Subgroup (G2Adj K), IsParabolicTwo (G2Adj K) P →
      (S : Subgroup (G2Adj K)) ≤ Subgroup.normalizer (P : Set (G2Adj K)) →
      ∀ x ∈ P, θ x ∈ P := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Finite (ModGL Tag.G2 K) := finite_modGL
  intro θ S hSθ P hPpar hSP x hx
  have hUsyl : CFSG.QuasithinUnique.IsSylowTwoOf
      ((posUnipotent Tag.G2 K).subgroupOf (adjointGroup Tag.G2 K)) ⊤ :=
    CFSG.QuasithinUnique.Setup.X6.isSylowTwoOf_subgroupOf_top
      (CFSG.QuasithinUnique.Setup.X6.isSylowTwoOf_iff_isSylowOf.2
        (CFSG.QuasithinUnique.Setup.X6.unique_Chevalley_positive_Sylow
          (τ := Tag.G2) (K := K) 2).1)
  have hUsyl' : CFSG.ABGLocalTools.IsSylowOf 2
      ((posUnipotent Tag.G2 K).subgroupOf (adjointGroup Tag.G2 K)) ⊤ :=
    CFSG.QuasithinUnique.Setup.X6.isSylowTwoOf_iff_isSylowOf.1 hUsyl
  have hSsyl : CFSG.ABGLocalTools.IsSylowOf 2 (S : Subgroup (G2Adj K)) ⊤ := by
    rw [CFSG.ABGLocalTools.isSylowOf_iff]
    exact ⟨le_top, S.isPGroup', by rw [Subgroup.relIndex_top_right]; exact S.not_dvd_index⟩
  obtain ⟨k, -, hk⟩ := hSsyl.exists_mem_conj hUsyl'
  let e : G2Adj K ≃* G2Adj K := MulAut.conj k
  have hconj : (S : Subgroup (G2Adj K)).map e.toMonoidHom =
      (posUnipotent Tag.G2 K).subgroupOf (adjointGroup Tag.G2 K) := by
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · intro y hy
      obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.mp hy
      refine (hk (k * (s : G2Adj K) * k⁻¹)).2 ?_
      rw [show k⁻¹ * (k * (s : G2Adj K) * k⁻¹) * k = s by group]
      exact hs
    · rw [Subgroup.card_map_of_injective e.injective,
        CFSG.ABGLocalTools.IsSylowOf.card_eq hUsyl',
        CFSG.ABGLocalTools.IsSylowOf.card_eq hSsyl]
  have hSmap : (S : Subgroup (G2Adj K)).map θ.toMonoidHom = S := by
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · rintro _ ⟨y, hy, rfl⟩
      exact hSθ y hy
    · rw [Subgroup.card_map_of_injective θ.injective]
  let θ' : MulAut (G2Adj K) := MulAut.congr e θ
  have hcomp : θ'.toMonoidHom.comp e.toMonoidHom = e.toMonoidHom.comp θ.toMonoidHom := by
    ext y
    simp [θ', MulAut.congr_apply]
  have hUθ' : ((posUnipotent Tag.G2 K).subgroupOf (adjointGroup Tag.G2 K)).map θ'.toMonoidHom =
      (posUnipotent Tag.G2 K).subgroupOf (adjointGroup Tag.G2 K) := by
    rw [← hconj, Subgroup.map_map, hcomp, ← Subgroup.map_map, hSmap, hconj]
  have hBnorm : Subgroup.normalizer
      (((posUnipotent Tag.G2 K).subgroupOf (adjointGroup Tag.G2 K) :
        Subgroup (G2Adj K)) : Set (G2Adj K)) =
      (borelGroup Tag.G2 K).subgroupOf (adjointGroup Tag.G2 K) := by
    rw [CFSG.QuasithinUnique.Setup.X6.normalizer_subgroupOf_eq' posUnipotent_le_adjointGroup,
      (borel_self_normalizers Tag.G2 K).1]
  have hBθ' : ((borelGroup Tag.G2 K).subgroupOf (adjointGroup Tag.G2 K)).map θ'.toMonoidHom =
      (borelGroup Tag.G2 K).subgroupOf (adjointGroup Tag.G2 K) := by
    rw [← hBnorm, Subgroup.map_equiv_normalizer_eq, hUθ']
  have hSP' : (S : Subgroup (G2Adj K)) ≤ P := hPpar.le_of_le_normalizer S.isPGroup' hSP
  have hNSP : Subgroup.normalizer ((S : Subgroup (G2Adj K)) : Set (G2Adj K)) ≤ P :=
    hPpar.normalizer_le S hSP'
  have hNSe : (Subgroup.normalizer ((S : Subgroup (G2Adj K)) : Set (G2Adj K))).map
      e.toMonoidHom = (borelGroup Tag.G2 K).subgroupOf (adjointGroup Tag.G2 K) := by
    rw [Subgroup.map_equiv_normalizer_eq, hconj, hBnorm]
  have hBP' : (borelGroup Tag.G2 K).subgroupOf (adjointGroup Tag.G2 K) ≤
      P.map e.toMonoidHom := by
    rw [← hNSe]
    exact Subgroup.map_mono hNSP
  have hBA : borelGroup Tag.G2 K ≤
      (P.map e.toMonoidHom).map (adjointGroup Tag.G2 K).subtype := by
    have h := Subgroup.map_mono (f := (adjointGroup Tag.G2 K).subtype) hBP'
    rwa [Subgroup.map_subgroupOf_eq_of_le (borelGroup_le_adjointGroup' (τ := Tag.G2) (K := K))] at h
  have hAC : (P.map e.toMonoidHom).map (adjointGroup Tag.G2 K).subtype ≤
      adjointGroup Tag.G2 K := Subgroup.map_subtype_le _
  have key : (P.map e.toMonoidHom).map θ'.toMonoidHom = P.map e.toMonoidHom := by
    have hsub : ∀ Q : Subgroup (G2Adj K),
        ((Q.map (adjointGroup Tag.G2 K).subtype).subgroupOf (adjointGroup Tag.G2 K)) = Q :=
      fun Q => Subgroup.comap_map_eq_self_of_injective (adjointGroup Tag.G2 K).subtype_injective Q
    rcases g2_borel_overgroups hBA hAC with hA | hA | hA | hA
    · have hP'eq : P.map e.toMonoidHom =
          (borelGroup Tag.G2 K).subgroupOf (adjointGroup Tag.G2 K) := by
        rw [← hsub (P.map e.toMonoidHom), hA]
      rw [hP'eq]
      exact hBθ'
    · have hP'eq : P.map e.toMonoidHom =
          (parabolicSubgroup Tag.G2 K {⟨0, by decide⟩}).subgroupOf (adjointGroup Tag.G2 K) := by
        rw [← hsub (P.map e.toMonoidHom), hA]
      rw [hP'eq]
      exact CFSG.QuasithinUnique.Setup.X6.G2_invariant_parabolic (K := K) hK hUθ'
        (⟨0, by decide⟩ : Fin Tag.G2.rank)
    · have hP'eq : P.map e.toMonoidHom =
          (parabolicSubgroup Tag.G2 K {⟨1, by decide⟩}).subgroupOf (adjointGroup Tag.G2 K) := by
        rw [← hsub (P.map e.toMonoidHom), hA]
      rw [hP'eq]
      exact CFSG.QuasithinUnique.Setup.X6.G2_invariant_parabolic (K := K) hK hUθ'
        (⟨1, by decide⟩ : Fin Tag.G2.rank)
    · have hP'eq : P.map e.toMonoidHom = ⊤ := by
        rw [← hsub (P.map e.toMonoidHom), hA, Subgroup.subgroupOf_self]
      rw [hP'eq, Subgroup.map_top_of_surjective _ θ'.surjective]
  have hPe : (P.map e.toMonoidHom).map θ'.toMonoidHom =
      (P.map θ.toMonoidHom).map e.toMonoidHom := by
    rw [Subgroup.map_map, Subgroup.map_map, hcomp]
  rw [hPe] at key
  have hPeq : P.map θ.toMonoidHom = P :=
    Subgroup.map_injective (f := e.toMonoidHom) e.injective key
  rw [← hPeq]
  exact Subgroup.mem_map_of_mem θ.toMonoidHom hx

theorem kDiag_adjointGroup_G2 (hK : 4 ≤ Nat.card K) :
    ∀ (θ : MulAut (G2Adj K)), Odd (orderOf θ) →
    ∀ S : Sylow 2 (G2Adj K),
      (∀ x ∈ (S : Subgroup (G2Adj K)), θ x ∈ (S : Subgroup (G2Adj K))) →
    ∀ P : Subgroup (G2Adj K), IsParabolicTwo (G2Adj K) P →
      (S : Subgroup (G2Adj K)) ≤ Subgroup.normalizer (P : Set (G2Adj K)) →
      ∀ x ∈ P, θ x ∈ P :=
  fun θ _ => kDiag_adjointGroup_G2_strong (K := K) hK θ

end Model

section Transport

theorem kDiag_of_isG2 {n : ℕ} {X : Type} [Group X] [Finite X] (hX : IsG2 X n) :
    ∀ (θ : MulAut X), Odd (orderOf θ) →
    ∀ S : Sylow 2 X, (∀ x ∈ (S : Subgroup X), θ x ∈ (S : Subgroup X)) →
    ∀ P : Subgroup X, IsParabolicTwo X P →
      (S : Subgroup X) ≤ Subgroup.normalizer (P : Set X) →
      ∀ x ∈ P, θ x ∈ P := by
  have hX' : CFSG.Blueprint.LieModel X .G2 0 2 n := hX
  have ht : (CFSG.Open.StatedLieTag.G2) ∈ CFSG.Blueprint.chevalleyExceptionalTags := by decide
  have hm : CFSG.Blueprint.ChevalleyExceptionalModel X .G2 2 n :=
    CFSG.Blueprint.LieModel.chevalleyExceptionalModel hX' ht
  obtain ⟨-, K, hfield, hfinite, hchar, hcard, ⟨e⟩⟩ :=
    CFSG.QuasithinUnique.Setup.X6.exists_mulEquiv_G2_model hm
  letI : Field K := hfield
  letI : Finite K := hfinite
  letI : CharP K 2 := hchar
  have h3 : 3 ≤ 2 ^ n := hm.1.2.2.2
  have hn2 : 2 ≤ n := by
    by_contra h
    have h1 : n ≤ 1 := by omega
    have h2 : 2 ^ n ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) h1
    rw [show (2 : ℕ) ^ 1 = 2 from rfl] at h2
    omega
  have h4 : 4 ≤ Nat.card K := by
    rw [hcard]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
  exact kDiag_transport e (kDiag_adjointGroup_G2 (K := K) h4)

end Transport


end CFSG.LocalAnalysis.UniquenessCase.UC22

end


