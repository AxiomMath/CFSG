module

public import CFSG.RankThree.Chevalley.SteinbergCFExceptionalModelCover
public import CFSG.RankThree.Chevalley.SteinbergCFTrialityCommutingSL2
public import CFSG.RankThree.CentralCover.SteinbergBNMixedFieldCommutingSL2Defining
public import CFSG.RankThree.Classical.SteinbergBJOrthogonalDefiningComponent

public noncomputable section

namespace CFSG.RankThree.Chevalley

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Assembly.LowTwoRank
open CFSG.Assembly.RankThreeEven (localRank)
open scoped MatrixGroups

theorem four_mul_le_localRank_of_triality {L : Type*} [Group L] [Finite L] {p f : ℕ}
    (hp : p.Prime) (hp3 : 3 < p) (hf : 1 ≤ f) {K : Type} [Field K]
    (hK : Nat.card K = (p ^ f) ^ 3) {σ : K →+* K} (hσ : ∀ c, σ c = c ^ (p ^ f))
    (e : L ⧸ Subgroup.center L ≃* DerivedCentralQuotient (twistedFixedGroup .D4 K σ)) :
    4 * f ≤ localRank p L := by
  classical
  have : Finite K :=
    Nat.finite_of_card_ne_zero (by rw [hK]; exact (pow_pos (pow_pos hp.pos f) _).ne')
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨φ, hφ, hker⟩ := exists_central_surjection_graphFixedRootGroup .D4 hp hf hK hσ e
  obtain ⟨σ', hσ', -, -, -, k, hk, hkcard, -⟩ := finite_graph_field_parameter_fields .D4 hp hf K hK
  have hσσ' : σ'.toRingHom = σ := RingHom.ext fun c => by
    change σ' c = σ c
    rw [hσ', hσ]
  have h3 : σ' ^ 3 = 1 := by
    refine RingEquiv.ext fun c => ?_
    change σ' (σ' (σ' c)) = c
    have : Fintype K := Fintype.ofFinite K
    rw [hσ', hσ', hσ', ← pow_mul, ← pow_mul,
      show p ^ f * (p ^ f * p ^ f) = (p ^ f) ^ 3 by ring, ← hK, Nat.card_eq_fintype_card,
      FiniteField.pow_card]
  have hfix : fixSubfield σ' = k := SetLike.ext' (by
    rw [hk]
    ext c
    change σ' c = c ↔ c ^ (p ^ f) = c
    rw [hσ'])
  have hkcard' : Fintype.card (fixSubfield σ') = p ^ f := by
    rw [← Nat.card_eq_fintype_card, hfix, hkcard]
  have hKcard : Fintype.card K = p ^ (3 * f) := by
    rw [← Nat.card_eq_fintype_card, hK, ← pow_mul, mul_comm]
  subst hσσ'
  obtain ⟨ι, η, hι, hη, hcomm⟩ := triality_D4_commuting_faithful_extension_and_fixed_SL2 K σ' h3
  let Ks : Fin 2 → Type := ![K, ↥(fixSubfield σ')]
  let instF : ∀ i, Field (Ks i) := fun i => match i with
    | 0 => (inferInstance : Field K)
    | 1 => (inferInstance : Field (fixSubfield σ'))
  let instT : ∀ i, Fintype (Ks i) := fun i => match i with
    | 0 => (inferInstance : Fintype K)
    | 1 => (inferInstance : Fintype (fixSubfield σ'))
  let ι' : ∀ i, SL(2, Ks i) →* graphFixedRootGroup .D4 K σ'.toRingHom := fun i => match i with
    | 0 => ι
    | 1 => η
  have hι' : ∀ i, Function.Injective (ι' i) := fun i => by
    fin_cases i
    · exact hι
    · exact hη
  have hcomm' : ∀ i j, i ≠ j → ∀ (A : SL(2, Ks i)) (B : SL(2, Ks j)),
      ι' i A * ι' j B = ι' j B * ι' i A := fun i j hij A B => by
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · exact hcomm A B
    · exact (hcomm B A).symm
    · exact absurd rfl hij
  obtain ⟨-, -, -, -, -, -, -, hrank⟩ :=
    CFSG.RankThree.CentralCover.mixed_field_commuting_SL2_actual_central_cover_defining_local_rank
      (⊤ : Subgroup L) hp hp3 (by norm_num : 1 ≤ 2) ![3 * f, f]
      (fun i => by fin_cases i <;> simp <;> omega) (K := Ks)
      (fun i => by
        fin_cases i
        · exact hKcard
        · exact hkcard') φ hφ hker ι' hι' hcomm'
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] at hrank
  omega

theorem triality_D4_defining_prime_actual_component_exclusion {X : Type} [Group X] [Finite X]
    {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) (N : Subgroup X) [N.Normal] (hN : ¬p ∣ Nat.card N)
    (hX : localRank p X ≤ 3) (L : Subgroup (X ⧸ N)) (f : ℕ) :
    ¬ChevalleyExceptionalModel (L ⧸ Subgroup.center L) .trialityD4 p f := by
  rintro ⟨⟨-, hf, -⟩, K, _, _, hK, σ, hσ, ⟨e⟩⟩
  have hL := CFSG.RankThree.Classical.localRank_le_of_le_quotient hp (by omega) N hN L
  have := four_mul_le_localRank_of_triality hp hp3 hf hK hσ e
  omega

end CFSG.RankThree.Chevalley
