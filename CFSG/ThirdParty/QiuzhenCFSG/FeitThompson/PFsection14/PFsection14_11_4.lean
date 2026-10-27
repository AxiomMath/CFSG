module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection14.PFsection14_11_3
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection12.PFsection12_7
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection3.PFsection3_4
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection7.PFsection7_5
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection7.PFsection7_8_b
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection8.PFsection8_5_a

namespace CFSG
end CFSG
open CFSG

/-!
# Peterfalvi, Section 14: theorem (14.11.4)
-/

noncomputable section

open scoped BigOperators Pointwise

attribute [local instance] Fintype.ofFinite

namespace CFSG.Section14

universe u v w

public theorem section14_real_ineq_of_14_11_4_inequalityData
    {G : Type u} [Group G] [Finite G]
    {M K W W1 W2 P Q : Subgroup G}
    {Go : Set G}
    {ψτ : Section1.ClassFunction G}
    {psiRhoNormSq : ℝ}
    {p q u v : ℕ}
    (hp : 0 < p) (hq : 0 < q) (hu : 0 < u) (hv : 0 < v)
    (hineq :
      theorem_14_11_4_inequalityData M K W W1 W2 P Q Go ψτ
        psiRhoNormSq p q u v) :
    1 / (p : ℝ) + 1 / (q : ℝ) ≤
      ((p * q : ℕ) : ℝ) / (Nat.card K : ℝ) +
        2 / (((p * q : ℕ) : ℝ)) +
        1 / (((u * q : ℕ) : ℝ)) +
        1 / (((v * p : ℕ) : ℝ)) := by
  dsimp [theorem_14_11_4_inequalityData] at hineq
  rcases hineq with ⟨_h75, hlo, hhi⟩
  have hchain := le_trans hlo hhi
  have htermP :
      ((Nat.card P - 1 : ℕ) : ℝ) /
          ((Nat.card P : ℝ) * (u : ℝ) * (q : ℝ)) ≤
        1 / (((u * q : ℕ) : ℝ)) := by
    rw [Nat.cast_mul]
    have hPpos : (0 : ℝ) < Nat.card P := by
      exact_mod_cast (Nat.card_pos (α := P))
    have huR : (0 : ℝ) < u := by exact_mod_cast hu
    have hqR : (0 : ℝ) < q := by exact_mod_cast hq
    have hnum_le : (((Nat.card P - 1 : ℕ) : ℝ)) ≤ (Nat.card P : ℝ) := by
      exact_mod_cast Nat.sub_le (Nat.card P) 1
    field_simp [ne_of_gt hPpos, ne_of_gt huR, ne_of_gt hqR]
    nlinarith
  have htermQ :
      ((Nat.card Q - 1 : ℕ) : ℝ) /
          ((Nat.card Q : ℝ) * (v : ℝ) * (p : ℝ)) ≤
        1 / (((v * p : ℕ) : ℝ)) := by
    rw [Nat.cast_mul]
    have hQpos : (0 : ℝ) < Nat.card Q := by
      exact_mod_cast (Nat.card_pos (α := Q))
    have hvR : (0 : ℝ) < v := by exact_mod_cast hv
    have hpR : (0 : ℝ) < p := by exact_mod_cast hp
    have hnum_le : (((Nat.card Q - 1 : ℕ) : ℝ)) ≤ (Nat.card Q : ℝ) := by
      exact_mod_cast Nat.sub_le (Nat.card Q) 1
    field_simp [ne_of_gt hQpos, ne_of_gt hvR, ne_of_gt hpR]
    nlinarith
  have htermK :
      ((Nat.card K - 1 : ℕ) : ℝ) /
          ((Nat.card K : ℝ) * (((p * q : ℕ) : ℝ))) ≤
        1 / (((p * q : ℕ) : ℝ)) := by
    rw [Nat.cast_mul]
    have hKpos : (0 : ℝ) < Nat.card K := by
      exact_mod_cast (Nat.card_pos (α := K))
    have hpR : (0 : ℝ) < p := by exact_mod_cast hp
    have hqR : (0 : ℝ) < q := by exact_mod_cast hq
    have hnum_le : (((Nat.card K - 1 : ℕ) : ℝ)) ≤ (Nat.card K : ℝ) := by
      exact_mod_cast Nat.sub_le (Nat.card K) 1
    field_simp [ne_of_gt hKpos, ne_of_gt hpR, ne_of_gt hqR]
    nlinarith
  have htwo_pq :
      2 / (((p * q : ℕ) : ℝ)) =
        1 / (((p * q : ℕ) : ℝ)) + 1 / (((p * q : ℕ) : ℝ)) := by
    ring
  nlinarith [hchain, htermP, htermQ, htermK, htwo_pq]

public theorem section14_dadeAveragingFunction_smul
    {G : Type u} [Group G] [Finite G]
    (L : Subgroup G) (H : G → Subgroup G)
    (χ : Section1.ClassFunction G) (ε : ℂ) :
    Section2.dadeAveragingFunction L H (ε • χ) =
      ε • Section2.dadeAveragingFunction L H χ := by
  ext a
  unfold Section2.dadeAveragingFunction
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [← Finset.mul_sum]
  ring

public theorem section14_dadeProjectionOn_smul
    {G : Type u} [Group G] [Finite G]
    (A : Set G) (L : Subgroup G) (H : G → Subgroup G)
    (χ : Section1.ClassFunction G) (ε : ℂ) :
    Section7.dadeProjectionOn A L H (ε • χ) =
      ε • Section7.dadeProjectionOn A L H χ := by
  ext a
  by_cases ha : (a : G) ∈ A
  · simp [Section7.dadeProjectionOn, Section7.dadeProjection, ha,
      section14_dadeAveragingFunction_smul]
  · simp [Section7.dadeProjectionOn, ha]

public theorem section14_weightedProjectionEnergy_smul_eq_of_isSign
    {G : Type u} [Group G] [Finite G]
    (A : Set G) (L : Subgroup G) (H : G → Subgroup G)
    (χ : Section1.ClassFunction G) {ε : ℂ} (hε : Section1.IsSign ε) :
    Section7.weightedProjectionEnergy A L H (ε • χ) =
      Section7.weightedProjectionEnergy A L H χ := by
  unfold Section7.weightedProjectionEnergy Section5.cfNormSq Section1.scalarProduct
  rw [section14_dadeProjectionOn_smul]
  rcases hε with rfl | rfl <;> simp

public theorem section14_normalizedSupportEnergy_smul_eq_of_isSign
    {G : Type u} [Group G] [Finite G]
    (X : Set G) (χ : Section1.ClassFunction G)
    {ε : ℂ} (hε : Section1.IsSign ε) :
    Section7.normalizedSupportEnergy X (ε • χ) =
      Section7.normalizedSupportEnergy X χ := by
  rcases hε with rfl | rfl <;>
    simp [Section7.normalizedSupportEnergy, Section7.supportEnergy]

public theorem section14_theorem_14_11_4_pf75_raw_source_bridge
    {G : Type u} [Group G] [Finite G]
    {M K V : Subgroup G}
    {Mfam : Finset (Section1.ClassFunction M)}
    {τM τM₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    {ψ βM : Section1.ClassFunction M}
    {tildeAM : Set G}
    {ψτ : Section1.ClassFunction G}
    (h1410 : hypothesis_14_10_data M K V Mfam τM τM₁ ψ βM)
    (htilde : Section10.section10TildeAData M K tildeAM)
    (hψτ : ψτ = τM₁ ψ) :
    ∃ R : G → Subgroup G,
      Section12.dadeIsometryRelativeToTypeIASet M K R τM ∧
      Section2.dadeSupport (Section12.typeIASet M K) R = tildeAM ∧
      Section7.normalizedSupportEnergy (Set.univ \ tildeAM) ψτ +
          Section7.weightedProjectionEnergy (Section12.typeIASet M K) M R ψτ ≤
        Section7.normalizedSupportEnergy (Set.univ \ tildeAM)
            (Section1.principalCharacter G) +
          ((Section12.typeIASet M K).ncard : ℝ) / (Nat.card M : ℝ) := by
  classical
  rcases section14_theorem_14_11_3_dade_support_tildeA_witness_source_bridge
      M K V Mfam τM τM₁ ψ βM tildeAM h1410 htilde with
    ⟨R, hDade, hsupp⟩
  have hsigned : Section3.IsSignedIrreducibleCharacter ψτ :=
    section14_psiTau_signedIrreducible_of_hypothesis_14_10 h1410 hψτ
  rcases hsigned with ⟨ε, hε, μ, hμ, hψτ_signed⟩
  let A : Fin 1 → Set G := fun _ => Section12.typeIASet M K
  let Ls : Fin 1 → Subgroup G := fun _ => M
  let Rs : Fin 1 → G → Subgroup G := fun _ => R
  have h74 : Section7.hypothesis_7_4_statement A Ls Rs (Set.univ \ tildeAM) := by
    refine ⟨?_, ?_⟩
    · refine ⟨?_, ?_⟩
      · intro i
        exact hDade.1
      · intro i j hij
        have hij' : i = j := by
          rw [Fin.eq_zero i, Fin.eq_zero j]
        exact False.elim (hij hij')
    · ext g
      simp [A, Rs, Section7.dadeProjectionSupport, hsupp]
  have h75 := Section7.theorem_7_5 A Ls Rs (Set.univ \ tildeAM) h74 μ hμ
  have hleft_mu :
      Section7.normalizedSupportEnergy (Set.univ \ tildeAM) μ +
          Section7.weightedProjectionEnergy (Section12.typeIASet M K) M R μ ≤
        Section7.normalizedSupportEnergy (Set.univ \ tildeAM)
            (Section1.principalCharacter G) +
          ((Section12.typeIASet M K).ncard : ℝ) / (Nat.card M : ℝ) := by
    simpa [A, Ls, Rs] using h75
  have hnorm :
      Section7.normalizedSupportEnergy (Set.univ \ tildeAM) ψτ =
        Section7.normalizedSupportEnergy (Set.univ \ tildeAM) μ := by
    rw [hψτ_signed]
    exact section14_normalizedSupportEnergy_smul_eq_of_isSign
      (Set.univ \ tildeAM) μ hε
  have hweight :
      Section7.weightedProjectionEnergy (Section12.typeIASet M K) M R ψτ =
        Section7.weightedProjectionEnergy (Section12.typeIASet M K) M R μ := by
    rw [hψτ_signed]
    exact section14_weightedProjectionEnergy_smul_eq_of_isSign
      (Section12.typeIASet M K) M R μ hε
  refine ⟨R, hDade, hsupp, ?_⟩
  rwa [hnorm, hweight]

public theorem section14_typeIASet_ncard_eq_kernel_sub_one_of_typeI
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    {M K : Subgroup G}
    (hMmax : M ∈ section9MaximalSubgroups G)
    (hKMF : section16MFSubgroup M K)
    (hTypeI : Section8.typeIDefinitionData M K) :
    (Section12.typeIASet M K).ncard = Nat.card K - 1 := by
  classical
  have hfrob : Section7.frobeniusWithKernel M K :=
    Section12.theorem_12_7 M K hMmax hKMF hTypeI
  have hA :
      Section12.typeIASet M K = Section7.puncturedSubgroupSet K := by
    calc
      Section12.typeIASet M K =
          section16NonidentityElements (K : Set G) :=
        Section12.typeIASet_eq_nonidentity_kernel_of_frobenius M K hfrob
      _ = Section7.puncturedSubgroupSet K := by
        ext g
        simp [Section7.puncturedSubgroupSet, section16NonidentityElements]
  rw [← Nat.card_coe_set_eq, hA]
  exact Section13.section13_natCard_puncturedSubgroupSet K

public theorem section14_normalizedSupportEnergy_principal
    {G : Type u} [Group G] [Finite G]
    (X : Set G) :
    Section7.normalizedSupportEnergy X (Section1.principalCharacter G) =
      (Nat.card X : ℝ) / (Nat.card G : ℝ) := by
  classical
  rw [Section7.normalizedSupportEnergy]
  have hsupp :
      Section7.supportEnergy X (Section1.principalCharacter G) =
        (Nat.card X : ℝ) := by
    rw [Section7.supportEnergy]
    simp [Section1.principalCharacter]
  rw [hsupp]
  ring

public theorem section14_normalizedSupportEnergy_principal_le_card_four_of_subset
    {G : Type u} [Group G] [Finite G]
    {X A B C D : Set G}
    (hcover : X ⊆ A ∪ B ∪ C ∪ D) :
    Section7.normalizedSupportEnergy X (Section1.principalCharacter G) ≤
      ((Nat.card A : ℝ) + (Nat.card B : ℝ) +
        (Nat.card C : ℝ) + (Nat.card D : ℝ)) / (Nat.card G : ℝ) := by
  classical
  rw [section14_normalizedSupportEnergy_principal]
  have hXcard : X.ncard ≤ (A ∪ B ∪ C ∪ D : Set G).ncard :=
    Set.ncard_le_ncard hcover
  have hUnion : (A ∪ B ∪ C ∪ D : Set G).ncard ≤
      A.ncard + B.ncard + C.ncard + D.ncard := by
    calc
      (A ∪ B ∪ C ∪ D : Set G).ncard ≤
          (A ∪ B ∪ C : Set G).ncard + D.ncard := by
        simpa [Set.union_assoc] using
          Set.ncard_union_le (A ∪ B ∪ C : Set G) D
      _ ≤ (A.ncard + B.ncard + C.ncard) + D.ncard := by
        gcongr
        calc
          (A ∪ B ∪ C : Set G).ncard ≤
              (A ∪ B : Set G).ncard + C.ncard := by
            simpa [Set.union_assoc] using
              Set.ncard_union_le (A ∪ B : Set G) C
          _ ≤ (A.ncard + B.ncard) + C.ncard := by
            gcongr
            exact Set.ncard_union_le A B
      _ = A.ncard + B.ncard + C.ncard + D.ncard := by omega
  have hnum_n : (X.ncard : ℝ) ≤
      (A.ncard : ℝ) + (B.ncard : ℝ) + (C.ncard : ℝ) + (D.ncard : ℝ) := by
    exact_mod_cast le_trans hXcard hUnion
  have hnum : (Nat.card X : ℝ) ≤
      (Nat.card A : ℝ) + (Nat.card B : ℝ) +
        (Nat.card C : ℝ) + (Nat.card D : ℝ) := by
    simpa [← Nat.card_coe_set_eq] using hnum_n
  have hGpos : (0 : ℝ) < Nat.card G := by
    exact_mod_cast Nat.card_pos (α := G)
  exact div_le_div_of_nonneg_right hnum (le_of_lt hGpos)

public theorem section14_theorem_14_11_4_nonpositive_of_pf75
    {G : Type u} [Group G] [Finite G]
    {M K : Subgroup G}
    {Go Cw Cp Cq X : Set G}
    {ψτ : Section1.ClassFunction G}
    {rho : ℝ}
    (hGoX : Go ⊆ X)
    (hcover :
      Section7.normalizedSupportEnergy X (Section1.principalCharacter G) ≤
        ((Nat.card Go : ℝ) + (Nat.card Cw : ℝ) +
          (Nat.card Cp : ℝ) + (Nat.card Cq : ℝ)) / (Nat.card G : ℝ))
    (hAcard : (Section12.typeIASet M K).ncard = Nat.card K - 1)
    (h75 :
      Section7.normalizedSupportEnergy X ψτ + rho ≤
        Section7.normalizedSupportEnergy X (Section1.principalCharacter G) +
          ((Section12.typeIASet M K).ncard : ℝ) / (Nat.card M : ℝ)) :
    (1 / (Nat.card G : ℝ)) *
        ((∑ g : Go, Complex.normSq (ψτ g.1)) -
          (Nat.card Go : ℝ) - (Nat.card Cw : ℝ) -
          (Nat.card Cp : ℝ) - (Nat.card Cq : ℝ)) + rho -
        ((Nat.card K - 1 : ℕ) : ℝ) / (Nat.card M : ℝ) ≤ 0 := by
  let S : ℝ := ∑ g : Go, Complex.normSq (ψτ g.1)
  let B : ℝ := (Nat.card Go : ℝ) + (Nat.card Cw : ℝ) +
    (Nat.card Cp : ℝ) + (Nat.card Cq : ℝ)
  let kterm : ℝ := ((Nat.card K - 1 : ℕ) : ℝ) / (Nat.card M : ℝ)
  classical
  have hsupportGoLe :
      Section7.supportEnergy Go ψτ ≤ Section7.supportEnergy X ψτ :=
    Section13.section13_supportEnergy_mono hGoX ψτ
  have hsumGo :
      Section7.supportEnergy Go ψτ = S := by
    dsimp [S]
    rw [Section7.supportEnergy]
    have hfilter :
        (∑ g : G, (if g ∈ Go then Complex.normSq (ψτ g) else 0)) =
          ∑ g ∈ (Finset.univ.filter (fun g : G => g ∈ Go)),
            Complex.normSq (ψτ g) := by
      simp [Finset.sum_filter]
    rw [hfilter]
    exact Finset.sum_subtype
      (s := Finset.univ.filter (fun g : G => g ∈ Go))
      (p := fun g : G => g ∈ Go)
      (f := fun g : G => Complex.normSq (ψτ g)) (by simp)
  have hGnonneg : 0 ≤ (Nat.card G : ℝ)⁻¹ := by positivity
  have hpsi_ge :
      (1 / (Nat.card G : ℝ)) * S ≤
        Section7.normalizedSupportEnergy X ψτ := by
    rw [Section7.normalizedSupportEnergy]
    rw [← hsumGo]
    simpa [one_div] using
      mul_le_mul_of_nonneg_left hsupportGoLe hGnonneg
  have h75' :
      Section7.normalizedSupportEnergy X ψτ + rho ≤
        Section7.normalizedSupportEnergy X (Section1.principalCharacter G) +
          kterm := by
    simpa [hAcard, kterm] using h75
  have hcover' :
      Section7.normalizedSupportEnergy X (Section1.principalCharacter G) ≤
        B / (Nat.card G : ℝ) := by
    simpa [B] using hcover
  have hmain :
      (1 / (Nat.card G : ℝ)) * S + rho ≤
        B / (Nat.card G : ℝ) + kterm := by
    linarith
  change (1 / (Nat.card G : ℝ)) *
      (S - (Nat.card Go : ℝ) - (Nat.card Cw : ℝ) -
        (Nat.card Cp : ℝ) - (Nat.card Cq : ℝ)) + rho - kterm ≤ 0
  have hrewrite :
      (1 / (Nat.card G : ℝ)) *
          (S - (Nat.card Go : ℝ) - (Nat.card Cw : ℝ) -
            (Nat.card Cp : ℝ) - (Nat.card Cq : ℝ)) + rho - kterm =
        ((1 / (Nat.card G : ℝ)) * S + rho) -
          (B / (Nat.card G : ℝ) + kterm) := by
    dsimp [B]
    ring
  rw [hrewrite]
  linarith

public theorem section14_theorem_14_11_4_upper_bound_of_nonpositive
    {G : Type u} [Group G] [Finite G]
    {M K : Subgroup G}
    {Go Cw Cp Cq : Set G}
    {ψτ : Section1.ClassFunction G}
    {rho finalBound : ℝ}
    (h113 : theorem_14_11_3_data Go ψτ)
    (hnonpos :
      (1 / (Nat.card G : ℝ)) *
          ((∑ g : Go, Complex.normSq (ψτ g.1)) -
            (Nat.card Go : ℝ) - (Nat.card Cw : ℝ) -
            (Nat.card Cp : ℝ) - (Nat.card Cq : ℝ)) + rho -
          ((Nat.card K - 1 : ℕ) : ℝ) / (Nat.card M : ℝ) ≤ 0)
    (hcard :
      ((Nat.card Cw : ℝ) + (Nat.card Cp : ℝ) + (Nat.card Cq : ℝ)) /
          (Nat.card G : ℝ) +
        ((Nat.card K - 1 : ℕ) : ℝ) / (Nat.card M : ℝ) ≤ finalBound) :
    rho ≤ finalBound := by
  let S : ℝ := ∑ g : Go, Complex.normSq (ψτ g.1)
  let C : ℝ := (Nat.card Cw : ℝ) + (Nat.card Cp : ℝ) + (Nat.card Cq : ℝ)
  let kterm : ℝ := ((Nat.card K - 1 : ℕ) : ℝ) / (Nat.card M : ℝ)
  classical
  letI : Fintype Go := Fintype.ofFinite Go
  have hSge : (Nat.card Go : ℝ) ≤ S := by
    dsimp [S]
    have hsum_one_le :
        (∑ _g : Go, (1 : ℝ)) ≤
          ∑ g : Go, Complex.normSq (ψτ g.1) := by
      refine Finset.sum_le_sum ?_
      intro g _hg
      exact h113 g.1 g.2
    have hcard_eq : (Go.ncard : ℝ) = ∑ _g : Go, (1 : ℝ) := by
      rw [← Nat.card_coe_set_eq]
      rw [Nat.card_eq_fintype_card]
      simp
    rw [hcard_eq]
    exact hsum_one_le
  have hGnonneg : 0 ≤ (Nat.card G : ℝ)⁻¹ := by positivity
  have hSminus_nonneg : 0 ≤ S - (Nat.card Go : ℝ) := by linarith
  have hmul_nonneg :
      0 ≤ (1 / (Nat.card G : ℝ)) * (S - (Nat.card Go : ℝ)) := by
    simpa [one_div] using mul_nonneg hGnonneg hSminus_nonneg
  have hnonpos' :
      (1 / (Nat.card G : ℝ)) * (S - (Nat.card Go : ℝ) - C) + rho -
          kterm ≤ 0 := by
    have hrewrite :
        (1 / (Nat.card G : ℝ)) *
            ((∑ g : Go, Complex.normSq (ψτ g.1)) -
              (Nat.card Go : ℝ) - (Nat.card Cw : ℝ) -
              (Nat.card Cp : ℝ) - (Nat.card Cq : ℝ)) + rho -
            ((Nat.card K - 1 : ℕ) : ℝ) / (Nat.card M : ℝ) =
          (1 / (Nat.card G : ℝ)) * (S - (Nat.card Go : ℝ) - C) + rho -
            kterm := by
      dsimp [S, C, kterm]
      ring
    rwa [← hrewrite]
  have hleC :
      -(C / (Nat.card G : ℝ)) ≤
        (1 / (Nat.card G : ℝ)) * (S - (Nat.card Go : ℝ) - C) := by
    have hrewrite :
        (1 / (Nat.card G : ℝ)) * (S - (Nat.card Go : ℝ) - C) =
          (1 / (Nat.card G : ℝ)) * (S - (Nat.card Go : ℝ)) -
            C / (Nat.card G : ℝ) := by
      ring
    rw [hrewrite]
    linarith
  have hrho_le : rho ≤ C / (Nat.card G : ℝ) + kterm := by
    linarith
  have hcard' : C / (Nat.card G : ℝ) + kterm ≤ finalBound := by
    simpa [C, kterm] using hcard
  exact le_trans hrho_le hcard'

public theorem section14_kernel_card_term_denominator_eq_of_relIndex_eq_mul
    {G : Type u} [Group G] [Finite G]
    {M K : Subgroup G} {p q : ℕ}
    (hKleM : K ≤ M)
    (hrel : K.relIndex M = p * q) :
    ((Nat.card K - 1 : ℕ) : ℝ) / (Nat.card M : ℝ) =
      ((Nat.card K - 1 : ℕ) : ℝ) /
        ((Nat.card K : ℝ) * ((p * q : ℕ) : ℝ)) := by
  have hidx :
      (K.subgroupOf M).index * Nat.card (K.subgroupOf M) =
        Nat.card M := by
    simpa using (Subgroup.index_mul_card (H := K.subgroupOf M))
  have hcardSub : Nat.card (K.subgroupOf M) = Nat.card K := by
    exact Nat.card_congr
      (Subgroup.subgroupOfEquivOfLe (H := K) (K := M) hKleM).toEquiv
  have hrel_def : K.relIndex M = (K.subgroupOf M).index := rfl
  have hcardM : Nat.card M = (p * q) * Nat.card K := by
    rw [← hidx, hcardSub, ← hrel_def, hrel]
  rw [hcardM]
  rw [Nat.cast_mul]
  ring_nf

public theorem section14_theorem_14_11_4_cover_subset_of_le
    {G : Type u} [Group G]
    {tildeAM : Set G}
    {W W1 W2 P Q : Subgroup G}
    (hW2P : W2 ≤ P) (hW1Q : W1 ≤ Q) :
    Set.univ \ tildeAM ⊆
      theorem_14_11_3_G0 tildeAM W P Q ∪
        conjugatesOfSet ((W : Set G) \ ((W1 : Set G) ∪ (W2 : Set G))) ∪
        conjugatesOfPuncturedSubgroup P ∪
        conjugatesOfPuncturedSubgroup Q := by
  intro g hg
  by_cases hG0 : g ∈ theorem_14_11_3_G0 tildeAM W P Q
  · exact Or.inl (Or.inl (Or.inl hG0))
  · have hg_not_tilde : g ∉ tildeAM := hg.2
    have hmem_union :
        g ∈ conjugatesOfPuncturedSubgroup W ∨
          g ∈ conjugatesOfPuncturedSubgroup P ∨
          g ∈ conjugatesOfPuncturedSubgroup Q := by
      by_contra hnot
      have hnotW : g ∉ conjugatesOfPuncturedSubgroup W := by
        intro h
        exact hnot (Or.inl h)
      have hnotP : g ∉ conjugatesOfPuncturedSubgroup P := by
        intro h
        exact hnot (Or.inr (Or.inl h))
      have hnotQ : g ∉ conjugatesOfPuncturedSubgroup Q := by
        intro h
        exact hnot (Or.inr (Or.inr h))
      apply hG0
      simpa [theorem_14_11_3_G0, Set.mem_sdiff, Set.mem_union, not_or]
        using ⟨⟨⟨hg_not_tilde, hnotW⟩, hnotP⟩, hnotQ⟩
    rcases hmem_union with hW | hP | hQ
    · rcases hW with ⟨x, hxW, hxne, a, rfl⟩
      by_cases hxW1 : x ∈ W1
      · exact Or.inr ⟨x, hW1Q hxW1, hxne, a, rfl⟩
      · by_cases hxW2 : x ∈ W2
        · exact Or.inl (Or.inr ⟨x, hW2P hxW2, hxne, a, rfl⟩)
        · exact Or.inl (Or.inl (Or.inr
            ⟨x, ⟨hxW, by simp [hxW1, hxW2]⟩, a, rfl⟩))
    · exact Or.inl (Or.inr hP)
    · exact Or.inr hQ

public theorem section14_natCard_cyclicTISet_eq
    {G : Type u} [Group G] [Finite G]
    (W1 W2 W : Subgroup G) :
    Nat.card (Section3.cyclicTISet W1 W2 W) =
      Nat.card (Section3.cyclicTISetSubgroup W1 W2 W) := by
  classical
  exact Nat.card_congr
    { toFun := fun x =>
        ⟨⟨x.1, Section3.cyclicTISet_subset W1 W2 W x.2⟩, x.2⟩
      invFun := fun x =>
        ⟨x.1.1, x.2⟩
      left_inv := by
        intro x
        ext
        rfl
      right_inv := by
        intro x
        ext
        rfl }

public theorem section14_natCard_section16HatW_eq_of_h31
    {G : Type u} [Group G] [Finite G]
    {W W1 W2 : Subgroup G}
    (h31 : Section3.hypothesis_3_1_statement W1 W2 W)
    (hW : W = W1 ⊔ W2) :
    Nat.card (section16HatW W1 W2) =
      (Nat.card W1 - 1) * (Nat.card W2 - 1) := by
  classical
  have hset :
      section16HatW W1 W2 = Section3.cyclicTISet W1 W2 W := by
    ext x
    simp [section16HatW, Section3.cyclicTISet, hW]
  rw [hset, section14_natCard_cyclicTISet_eq]
  exact Section3.cyclicTISetSubgroup_card W1 W2 W h31

public theorem section14_theorem_14_11_4_projectionData_source_bridge
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    {M K V : Subgroup G}
    {Mfam : Finset (Section1.ClassFunction M)}
    {τM τM₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    {ψ βM : Section1.ClassFunction M}
    (h1410 : hypothesis_14_10_data M K V Mfam τM τM₁ ψ βM) :
    ∀ a : ℤ, ∀ r : Section1.ClassFunction G,
      Section7.theorem_7_8_decompositionData M K Mfam τM τM₁ ψ
          (K.relIndex M) a r →
        Section7.theorem_7_8_b_projectionData (Section12.typeIASet M K) M K
          (insert (Section7.principalInducedCharacter M K) Mfam)
          τM τM₁ ψ a := by
  intro a r hdecomp
  classical
  letI : Fintype M := Fintype.ofFinite M
  rcases h1410 with
    ⟨hMmax, _hModd, _hNormVleM, hKMF, hTypeI, hDadePkg, hPunctM,
      _h52M, hExtM, hψmem, hψirr, hψdeg, _hβM⟩
  rcases hDadePkg with ⟨RM, hDadeM, _hSupportM⟩
  have hMfullNotation :
      Section7.inducedFamilyNotation (K.subgroupOf M)
        (insert (Section7.principalInducedCharacter M K) Mfam) := by
    change Section7.inducedFamilyNotation (K.subgroupOf M)
      (insert (Section1.inducedCF (K.subgroupOf M)
        (Section1.principalCharacter (K.subgroupOf M))) Mfam)
    exact
      (section14_inducedFamilyNotation_insert_principal_of_punctured
        (H := K.subgroupOf M) (S := Mfam) hPunctM)
  have h76M :
      Section7.hypothesis_7_6_statement (Section12.typeIASet M K)
        M K RM (insert (Section7.principalInducedCharacter M K) Mfam) :=
    section14_hypothesis_7_6_typeI_typeIASet_of_dade
      (L := M) (H := K) (R := RM)
      (T := insert (Section7.principalInducedCharacter M K) Mfam) (τ := τM)
      hMmax hKMF hTypeI hDadeM hMfullNotation
  have h78M :
      Section7.theorem_7_8_hypothesis M K
        (insert (Section7.principalInducedCharacter M K) Mfam) Mfam
        τM τM₁ ψ :=
    section14_theorem_7_8_hypothesis_of_typeI_punctured
      hKMF hTypeI hPunctM hExtM hψmem hψirr hψdeg
  have hDadeAgreeM :
      Section7.agreesWithDadeTransform (Section12.typeIASet M K) M RM τM := by
    rcases hDadeM with ⟨_h22, hτpack⟩
    rcases hτpack with ⟨hAMG, hτeq⟩
    exact ⟨hAMG, hτeq⟩
  exact
    Section7.theorem_7_8_b_projectionData_source_bridge
      (A := Section12.typeIASet M K) (L := M) (H := K) (K := RM)
      (T := insert (Section7.principalInducedCharacter M K) Mfam)
      (S := Mfam) (τ := τM) (ν := τM₁) (ζ := ψ) (a := a) (r := r)
      h76M hDadeAgreeM h78M hdecomp

public theorem section14_theorem_14_11_4_lower_bound_source_bridge
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (Smax Tmax W W1 W2 P Q U C D L H : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (Lfam : Finset (Section1.ClassFunction L))
    (RL : G → Subgroup G)
    (τL τL₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (φ : Section1.ClassFunction L)
    (μ01 : Section1.ClassFunction Smax)
    (ν10 : Section1.ClassFunction Tmax)
    (βS : Section1.ClassFunction Smax)
    (βT : Section1.ClassFunction Tmax)
    (βL : Section1.ClassFunction L)
    (M K V : Subgroup G)
    (Mfam : Finset (Section1.ClassFunction M))
    (τM τM₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G)
    (ψ βM : Section1.ClassFunction M)
    (R : G → Subgroup G)
    (ψτ : Section1.ClassFunction G)
    (p q u v c d : ℕ) :
    hypothesis_14_context_data Smax Tmax W W1 W2 P Q U V C D
        Sfam Tfam τS τT p q u v c d →
      hypothesis_14_3_data Smax Tmax L H P Q U W1 W2 Lfam RL τL τL₁ φ μ01 ν10 βS βT βL →
        hypothesis_14_10_data M K V Mfam τM τM₁ ψ βM →
          Section12.dadeIsometryRelativeToTypeIASet M K R τM →
            K ≠ V →
              ψτ = τM₁ ψ →
                1 - ((p * q : ℕ) : ℝ) / (Nat.card K : ℝ) ≤
                  Section7.weightedProjectionEnergy (Section12.typeIASet M K)
                    M R ψτ := by
  intro hctx h143 h1410 hDadeM hKV hψτ
  classical
  have h1410orig := h1410
  rcases h1410 with
    ⟨hMmax, _hModd, _hNormVleM, hKMF, hTypeI, _hDadePkg, hPunctM,
      _h52M, hExtM, hψmem, hψirr, hψdeg, _hβM⟩
  letI : Fintype M := Fintype.ofFinite M
  let MfullFam := insert (Section7.principalInducedCharacter M K) Mfam
  have hMfullNotation :
      Section7.inducedFamilyNotation (K.subgroupOf M) MfullFam := by
    dsimp [MfullFam]
    simpa [Section7.principalInducedCharacter] using
      (section14_inducedFamilyNotation_insert_principal_of_punctured
        (H := K.subgroupOf M) (S := Mfam) hPunctM)
  have h76M :
      Section7.hypothesis_7_6_statement (Section12.typeIASet M K)
        M K R MfullFam :=
    section14_hypothesis_7_6_typeI_typeIASet_of_dade
      (L := M) (H := K) (R := R) (T := MfullFam) (τ := τM)
      hMmax hKMF hTypeI hDadeM hMfullNotation
  have h78M :
      Section7.theorem_7_8_hypothesis M K MfullFam Mfam τM τM₁ ψ := by
    dsimp [MfullFam]
    exact section14_theorem_7_8_hypothesis_of_typeI_punctured
      hKMF hTypeI hPunctM hExtM hψmem hψirr hψdeg
  have hDadeAgreeM :
      Section7.agreesWithDadeTransform (Section12.typeIASet M K) M R τM := by
    rcases hDadeM with ⟨_h22, hτpack⟩
    rcases hτpack with ⟨hAMG, hτeq⟩
    exact ⟨hAMG, hτeq⟩
  have hhalf :
      K.relIndex M ≤ (Nat.card K - 1) / 2 := by
    have hfrobM : Section7.frobeniusWithKernel M K :=
      Section12.theorem_12_7 M K hMmax hKMF hTypeI
    exact section14_frobenius_relIndex_le_kernel_pred_half
      (L := M) (H := K)
      (Section12.odd_card_of_typeIDefinitionData M K hTypeI) hfrobM
  have hproj :
      ∀ a : ℤ, ∀ r : Section1.ClassFunction G,
        Section7.theorem_7_8_decompositionData M K Mfam τM τM₁ ψ
            (K.relIndex M) a r →
          Section7.theorem_7_8_b_projectionData (Section12.typeIASet M K)
            M K MfullFam τM τM₁ ψ a := by
    intro a r hdecomp
    simpa [MfullFam] using
      section14_theorem_14_11_4_projectionData_source_bridge
        (G := G) (M := M) (K := K) (V := V) (Mfam := Mfam)
        (τM := τM) (τM₁ := τM₁) (ψ := ψ) (βM := βM)
        h1410orig a r hdecomp
  have h78b := Section7.theorem_7_8_b
    (Section12.typeIASet M K) M K R MfullFam Mfam τM τM₁ ψ
    h76M hDadeAgreeM h78M hproj hhalf
  have hbase :
      1 - (K.relIndex M : ℝ) / (Nat.card K : ℝ) ≤
        Section7.weightedProjectionEnergy (Section12.typeIASet M K) M R ψτ := by
    simpa [Section7.weightedProjectionEnergy, hψτ] using h78b.1
  rcases section14_theorem_14_11_1_K_index_source_inputs_bridge
      Smax Tmax W W1 W2 P Q U V C D L H Sfam Tfam τS τT
      Lfam RL τL τL₁ φ μ01 ν10 βS βT βL
      M K Mfam τM τM₁ ψ βM p q u v c d hctx h143 h1410orig hKV with
    ⟨_h2q, _hKgt, hrel_le⟩
  have hleft :
      1 - ((p * q : ℕ) : ℝ) / (Nat.card K : ℝ) ≤
        1 - (K.relIndex M : ℝ) / (Nat.card K : ℝ) := by
    have hKpos : (0 : ℝ) < Nat.card K := by
      exact_mod_cast (Nat.card_pos (α := K))
    have hrel_leR : (K.relIndex M : ℝ) ≤ ((p * q : ℕ) : ℝ) := by
      exact_mod_cast hrel_le
    have hdiv_le :
        (K.relIndex M : ℝ) / (Nat.card K : ℝ) ≤
          ((p * q : ℕ) : ℝ) / (Nat.card K : ℝ) :=
      div_le_div_of_nonneg_right hrel_leR (le_of_lt hKpos)
    linarith
  exact le_trans hleft hbase

public theorem section14_theorem_14_11_4_Wexception_cardinality_source_bridge
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (Smax Tmax W W1 W2 P Q U C D L H : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (Lfam : Finset (Section1.ClassFunction L))
    (RL : G → Subgroup G)
    (τL τL₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (φ : Section1.ClassFunction L)
    (μ01 : Section1.ClassFunction Smax)
    (ν10 : Section1.ClassFunction Tmax)
    (βS : Section1.ClassFunction Smax)
    (βT : Section1.ClassFunction Tmax)
    (βL : Section1.ClassFunction L)
    (M K V : Subgroup G)
    (Mfam : Finset (Section1.ClassFunction M))
    (τM τM₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G)
    (ψ βM : Section1.ClassFunction M)
    (tildeAM : Set G)
    (p q u v c d : ℕ) :
    hypothesis_14_context_data Smax Tmax W W1 W2 P Q U V C D
        Sfam Tfam τS τT p q u v c d →
      hypothesis_14_3_data Smax Tmax L H P Q U W1 W2 Lfam RL τL τL₁ φ μ01 ν10 βS βT βL →
        hypothesis_14_10_data M K V Mfam τM τM₁ ψ βM →
          Section10.section10TildeAData M K tildeAM →
            K ≠ V →
              let Wexception : Set G :=
                (W : Set G) \ ((W1 : Set G) ∪ (W2 : Set G))
              (Nat.card (conjugatesOfSet Wexception) : ℝ) / (Nat.card G : ℝ) ≤
                1 - 1 / (p : ℝ) - 1 / (q : ℝ) +
                  1 / ((p * q : ℕ) : ℝ) := by
  intro hctx h143 h1410 htilde hKV
  classical
  let Wexception : Set G := (W : Set G) \ ((W1 : Set G) ∪ (W2 : Set G))
  change
    (Nat.card (conjugatesOfSet Wexception) : ℝ) / (Nat.card G : ℝ) ≤
      1 - 1 / (p : ℝ) - 1 / (q : ℝ) + 1 / ((p * q : ℕ) : ℝ)
  have hsrc : Section13.hypothesis_13_1_sourceData
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT p q u v c d := hctx.1
  have hprod : section12InternalDirectProduct W1 W2 W := by
    rcases hsrc with
      ⟨hcase, _hSTypeP, _hTTypeP, _hp, _hq, _hC, _hD, _hc, _hd,
        _hUcard, _hVcard, _hSfam, _hTfam, _hDadeS, _hDadeT, _hNotation,
        _hDadeDiff, _hZeroDegree, _hConjIndex, _hConjBetaTau,
        _hChoice, _hMin, _hFourSixS, _hFourSixT⟩
    exact hcase.1
  have hWcard : Nat.card W = Nat.card W1 * Nat.card W2 :=
    section14_natCard_eq_mul_of_section12InternalDirectProduct hprod
  rcases hprod with ⟨_hW1le, _hW2le, hW_eq, _hdisj, _hcent⟩
  have hSTypeP : Section8.typePDefinitionData Smax P U W1 W2 := by
    rcases hsrc with
      ⟨_hcase, hSTypeP, _hTTypeP, _hp, _hq, _hC, _hD, _hc, _hd,
        _hUcard, _hVcard, _hSfam, _hTfam, _hDadeS, _hDadeT, _hNotation,
        _hDadeDiff, _hZeroDegree, _hConjIndex, _hConjBetaTau,
        _hChoice, _hMin, _hFourSixS, _hFourSixT⟩
    exact hSTypeP
  have hp_card : p = Nat.card W2 := by
    rcases hsrc with
      ⟨_hcase, _hSTypeP, _hTTypeP, hp_card, _hq, _hC, _hD, _hc, _hd,
        _hUcard, _hVcard, _hSfam, _hTfam, _hDadeS, _hDadeT, _hNotation,
        _hDadeDiff, _hZeroDegree, _hConjIndex, _hConjBetaTau,
        _hChoice, _hMin, _hFourSixS, _hFourSixT⟩
    exact hp_card
  have hq_card : q = Nat.card W1 := by
    rcases hsrc with
      ⟨_hcase, _hSTypeP, _hTTypeP, _hp, hq_card, _hC, _hD, _hc, _hd,
        _hUcard, _hVcard, _hSfam, _hTfam, _hDadeS, _hDadeT, _hNotation,
        _hDadeDiff, _hZeroDegree, _hConjIndex, _hConjBetaTau,
        _hChoice, _hMin, _hFourSixS, _hFourSixT⟩
    exact hq_card
  have h31 : Section3.hypothesis_3_1_statement W1 W2 W := by
    rcases hsrc with
      ⟨_hcase, _hSTypeP, _hTTypeP, _hp, _hq, _hC, _hD, _hc, _hd,
        _hUcard, _hVcard, _hSfam, _hTfam, _hDadeS, _hDadeT, hNotation,
        _hDadeDiff, _hZeroDegree, _hConjIndex, _hConjBetaTau,
        _hChoice, _hMin, _hFourSixS, _hFourSixT⟩
    rcases hNotation with
      ⟨_ω, _η, _μ, _ν, _μsum, _νsum, _δ, _δ', _σ, hNotationFor⟩
    rcases hNotationFor with
      ⟨hω, _hσ, _hη, _hδ, _hδ', _hμirr, _hνirr, _hμzero_nonprincipal,
        _hνzero_nonprincipal, _hμind, _hνind, _hμsum, _hνsum⟩
    exact hω.1
  have hWexception_eq : Wexception = section16HatW W1 W2 := by
    dsimp [Wexception]
    ext x
    simp [section16HatW, hW_eq]
  have hTI :
      section16TISubsetWithNormalizer (section16HatW W1 W2) (W1 ⊔ W2 : Subgroup G) :=
    Section8.theorem_8_5_c Smax P U W1 W2 hSTypeP
  have hOne : (1 : G) ∉ section16HatW W1 W2 := by
    intro h
    exact h.2 (Or.inl W1.one_mem)
  have hconj_eq :
      conjugatesOfSet (section16HatW W1 W2) =
        section16ConjugatesOfSetBySet (section16HatW W1 W2) Set.univ := by
    ext z
    constructor
    · rintro ⟨x, hx, a, rfl⟩
      exact ⟨x, hx, a, trivial, rfl⟩
    · rintro ⟨x, hx, a, _ha, rfl⟩
      exact ⟨x, hx, a, rfl⟩
  have hcardCw :
      (Nat.card (conjugatesOfSet Wexception) : ℝ) =
        (Nat.card G : ℝ) *
          ((Nat.card (section16HatW W1 W2) : ℝ) /
            (Nat.card (W1 ⊔ W2 : Subgroup G) : ℝ)) := by
    have hcard := Section13.section13_conjugatesOfSetBySet_card_real_eq
      (X := section16HatW W1 W2) (N := (W1 ⊔ W2 : Subgroup G)) hOne hTI
    rw [hWexception_eq, hconj_eq]
    exact hcard
  have hratio :
      (Nat.card (conjugatesOfSet Wexception) : ℝ) / (Nat.card G : ℝ) =
        (Nat.card (section16HatW W1 W2) : ℝ) /
          (Nat.card (W1 ⊔ W2 : Subgroup G) : ℝ) := by
    have hGpos : (0 : ℝ) < Nat.card G := by
      exact_mod_cast (Nat.card_pos (α := G))
    rw [hcardCw]
    field_simp [hGpos.ne']
  have hhat_card :
      Nat.card (section16HatW W1 W2) =
        (Nat.card W1 - 1) * (Nat.card W2 - 1) :=
    section14_natCard_section16HatW_eq_of_h31 h31 hW_eq
  have hWsup_card :
      Nat.card (W1 ⊔ W2 : Subgroup G) = Nat.card W1 * Nat.card W2 := by
    simpa [hW_eq] using hWcard
  have hvalue :
      (Nat.card (section16HatW W1 W2) : ℝ) /
          (Nat.card (W1 ⊔ W2 : Subgroup G) : ℝ) =
        1 - 1 / (p : ℝ) - 1 / (q : ℝ) + 1 / ((p * q : ℕ) : ℝ) := by
    have hW1posNat : 0 < Nat.card W1 := Nat.card_pos (α := W1)
    have hW2posNat : 0 < Nat.card W2 := Nat.card_pos (α := W2)
    have hW1one : (1 : ℕ) ≤ Nat.card W1 := Nat.succ_le_of_lt hW1posNat
    have hW2one : (1 : ℕ) ≤ Nat.card W2 := Nat.succ_le_of_lt hW2posNat
    have hW1pos : (0 : ℝ) < Nat.card W1 := by exact_mod_cast hW1posNat
    have hW2pos : (0 : ℝ) < Nat.card W2 := by exact_mod_cast hW2posNat
    rw [hhat_card, hWsup_card, hp_card, hq_card]
    repeat rw [Nat.cast_mul]
    rw [Nat.cast_sub hW1one, Nat.cast_sub hW2one]
    field_simp [hW1pos.ne', hW2pos.ne']
    ring_nf
  rw [hratio, hvalue]

private theorem section14_conjugatesOfPuncturedSubgroup_eq_conjugatesOfSetBySet
    {G : Type u} [Group G] (H : Subgroup G) :
    conjugatesOfPuncturedSubgroup H =
      section16ConjugatesOfSetBySet (Section7.puncturedSubgroupSet H) Set.univ := by
  ext z
  constructor
  · rintro ⟨x, hxH, hx1, a, rfl⟩
    exact ⟨x, ⟨hxH, hx1⟩, a, trivial, rfl⟩
  · rintro ⟨x, hx, a, _ha, rfl⟩
    exact ⟨x, hx.1, hx.2, a, rfl⟩

private theorem section14_smax_card_eq_core_mul_u_q_of_source
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (hsource : Section13.hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (hCbot : C = ⊥) :
    Nat.card Smax = Nat.card P * u * q := by
  rcases hsource with
    ⟨_hcaseB, htypeS, _htypeT, _hp_card, hq_card, _hC, _hD, hc_card,
      _hd_card, hU_card, _hV_card, _hSfam, _hTfam, _hDadeS, _hDadeT,
      _hnotation⟩
  have htypeSOrig := htypeS
  rcases htypeS with
    ⟨_hMF, _hW1cyc, _hW1ne, _hW1Hall, hScomp, _hUle, _hUnil, _hW1norm,
      hDercomp, _hMFnotcyc, _hsecond, _hfit, _hfitDer, _hW2le, _hW2cyc,
      _hW2ne, _hcent, _hnorm⟩
  have hDer_norm : section10NormalIn (ambientDerivedSubgroup Smax) Smax :=
    section12_normalIn_ambientDerivedSubgroup
  have hS_card : Nat.card Smax = Nat.card (ambientDerivedSubgroup Smax) * Nat.card W1 :=
    Section13.section13_card_eq_mul_of_complementIn_normal hScomp hDer_norm
  have hP_norm_der : section10NormalIn P (ambientDerivedSubgroup Smax) :=
    Section13.section13_mf_normalIn_ambientDerived_of_typeP (M := Smax) (MF := P)
      (U := U) (W1 := W1) (W2 := W2) htypeSOrig
  have hDer_card : Nat.card (ambientDerivedSubgroup Smax) = Nat.card P * Nat.card U :=
    Section13.section13_card_eq_mul_of_complementIn_normal hDercomp hP_norm_der
  have hC_card : Nat.card C = 1 := by
    rw [hCbot]
    exact Subgroup.card_bot
  have hc_one : c = 1 := by
    rw [hc_card, hC_card]
  rw [hS_card, hDer_card, hU_card, hc_one, Nat.mul_one, ← hq_card]

private theorem section14_tmax_card_eq_core_mul_v_p_of_source
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (hsource : Section13.hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (hDbot : D = ⊥) :
    Nat.card Tmax = Nat.card Q * v * p := by
  rcases hsource with
    ⟨_hcaseB, _htypeS, htypeT, hp_card, _hq_card, _hC, _hD, _hc_card,
      hd_card, _hU_card, hV_card, _hSfam, _hTfam, _hDadeS, _hDadeT,
      _hnotation⟩
  have htypeTOrig := htypeT
  rcases htypeT with
    ⟨_hMF, _hW2cyc, _hW2ne, _hW2Hall, hTcomp, _hVle, _hVnil, _hW2norm,
      hDercomp, _hMFnotcyc, _hsecond, _hfit, _hfitDer, _hW1le, _hW1cyc,
      _hW1ne, _hcent, _hnorm⟩
  have hDer_norm : section10NormalIn (ambientDerivedSubgroup Tmax) Tmax :=
    section12_normalIn_ambientDerivedSubgroup
  have hT_card : Nat.card Tmax = Nat.card (ambientDerivedSubgroup Tmax) * Nat.card W2 :=
    Section13.section13_card_eq_mul_of_complementIn_normal hTcomp hDer_norm
  have hQ_norm_der : section10NormalIn Q (ambientDerivedSubgroup Tmax) :=
    Section13.section13_mf_normalIn_ambientDerived_of_typeP (M := Tmax) (MF := Q)
      (U := V) (W1 := W2) (W2 := W1) htypeTOrig
  have hDer_card : Nat.card (ambientDerivedSubgroup Tmax) = Nat.card Q * Nat.card V :=
    Section13.section13_card_eq_mul_of_complementIn_normal hDercomp hQ_norm_der
  have hD_card : Nat.card D = 1 := by
    rw [hDbot]
    exact Subgroup.card_bot
  have hd_one : d = 1 := by
    rw [hd_card, hD_card]
  rw [hT_card, hDer_card, hV_card, hd_one, Nat.mul_one, ← hp_card]

public theorem section14_theorem_14_11_4_Ppunctured_cardinality_source_bridge
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (Smax Tmax W W1 W2 P Q U C D L H : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (Lfam : Finset (Section1.ClassFunction L))
    (RL : G → Subgroup G)
    (τL τL₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (φ : Section1.ClassFunction L)
    (μ01 : Section1.ClassFunction Smax)
    (ν10 : Section1.ClassFunction Tmax)
    (βS : Section1.ClassFunction Smax)
    (βT : Section1.ClassFunction Tmax)
    (βL : Section1.ClassFunction L)
    (M K V : Subgroup G)
    (Mfam : Finset (Section1.ClassFunction M))
    (τM τM₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G)
    (ψ βM : Section1.ClassFunction M)
    (tildeAM : Set G)
    (p q u v c d : ℕ) :
    hypothesis_14_context_data Smax Tmax W W1 W2 P Q U V C D
        Sfam Tfam τS τT p q u v c d →
      hypothesis_14_3_data Smax Tmax L H P Q U W1 W2 Lfam RL τL τL₁ φ μ01 ν10 βS βT βL →
        hypothesis_14_10_data M K V Mfam τM τM₁ ψ βM →
          Section10.section10TildeAData M K tildeAM →
              K ≠ V →
                (Nat.card (conjugatesOfPuncturedSubgroup P) : ℝ) /
                    (Nat.card G : ℝ) ≤
                  ((Nat.card P - 1 : ℕ) : ℝ) /
                    ((Nat.card P : ℝ) * (u : ℝ) * (q : ℝ)) := by
  intro hctx _h143 _h1410 _htilde _hKV
  classical
  have hsrc : Section13.hypothesis_13_1_sourceData
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT p q u v c d := hctx.1
  have hCbot : C = ⊥ :=
    section14_C_eq_bot_of_pf13_12_source hsrc
  have hSTypeP : Section8.typePDefinitionData Smax P U W1 W2 := by
    rcases hsrc with
      ⟨_hcase, hSTypeP, _hTTypeP, _hp, _hq, _hC, _hD, _hc, _hd,
        _hUcard, _hVcard, _hSfam, _hTfam, _hDadeS, _hDadeT, _hNotation,
        _hDadeDiff, _hZeroDegree, _hConjIndex, _hConjBetaTau,
        _hChoice, _hMin, _hFourSixS, _hFourSixT⟩
    exact hSTypeP
  have hCsrc : C = subgroupCentralizerIn U P := by
    rcases hsrc with
      ⟨_hcase, _hSTypeP, _hTTypeP, _hp, _hq, hC, _hD, _hc, _hd,
        _hUcard, _hVcard, _hSfam, _hTfam, _hDadeS, _hDadeT, _hNotation,
        _hDadeDiff, _hZeroDegree, _hConjIndex, _hConjBetaTau,
        _hChoice, _hMin, _hFourSixS, _hFourSixT⟩
    exact hC
  have hPfit : P = section8FittingSubgroup Smax := by
    calc
      P = P ⊔ C := by rw [hCbot, sup_bot_eq]
      _ = P ⊔ subgroupCentralizerIn U P := by rw [hCsrc]
      _ = section8FittingSubgroup Smax := by
        exact (Section8.theorem_8_5_a Smax P U W1 W2 hSTypeP).symm
  have hPpunct_fit :
      Section7.puncturedSubgroupSet P =
        section16NonidentityElements (section8FittingSubgroup Smax : Set G) := by
    ext x
    simp [Section7.puncturedSubgroupSet, section16NonidentityElements, hPfit]
  have hTI_fit :
      section16TISubsetWithNormalizer
        (section16NonidentityElements (section8FittingSubgroup Smax : Set G)) Smax :=
    Section13.section13_theorem_13_10_fitting_punctured_tiNormalizer_of_sourceContext
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
      p q u v c d hsrc
  have hTI :
      section16TISubsetWithNormalizer (Section7.puncturedSubgroupSet P) Smax := by
    simpa [hPpunct_fit] using hTI_fit
  have hOne : (1 : G) ∉ Section7.puncturedSubgroupSet P := by
    intro h
    exact h.2 rfl
  have hcard :
      (Nat.card (conjugatesOfPuncturedSubgroup P) : ℝ) =
        (Nat.card G : ℝ) *
          ((Nat.card (Section7.puncturedSubgroupSet P) : ℝ) /
            (Nat.card Smax : ℝ)) := by
    have hcard' := Section13.section13_conjugatesOfSetBySet_card_real_eq
      (X := Section7.puncturedSubgroupSet P) (N := Smax) hOne hTI
    rw [section14_conjugatesOfPuncturedSubgroup_eq_conjugatesOfSetBySet P]
    exact hcard'
  have hratio :
      (Nat.card (conjugatesOfPuncturedSubgroup P) : ℝ) / (Nat.card G : ℝ) =
        (Nat.card (Section7.puncturedSubgroupSet P) : ℝ) /
          (Nat.card Smax : ℝ) := by
    have hGpos : (0 : ℝ) < Nat.card G := by
      exact_mod_cast (Nat.card_pos (α := G))
    rw [hcard]
    field_simp [hGpos.ne']
  have hS_card : Nat.card Smax = Nat.card P * u * q :=
    section14_smax_card_eq_core_mul_u_q_of_source
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
      p q u v c d hsrc hCbot
  have hfinal :
      (Nat.card (conjugatesOfPuncturedSubgroup P) : ℝ) / (Nat.card G : ℝ) =
        ((Nat.card P - 1 : ℕ) : ℝ) /
          ((Nat.card P : ℝ) * (u : ℝ) * (q : ℝ)) := by
    rw [hratio, Section13.section13_natCard_puncturedSubgroupSet P, hS_card]
    simp [Nat.cast_mul, mul_assoc]
  -- for the S-side core `P`.
  exact le_of_eq hfinal

public theorem section14_theorem_14_11_4_Qpunctured_cardinality_source_bridge
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (Smax Tmax W W1 W2 P Q U C D L H : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (Lfam : Finset (Section1.ClassFunction L))
    (RL : G → Subgroup G)
    (τL τL₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (φ : Section1.ClassFunction L)
    (μ01 : Section1.ClassFunction Smax)
    (ν10 : Section1.ClassFunction Tmax)
    (βS : Section1.ClassFunction Smax)
    (βT : Section1.ClassFunction Tmax)
    (βL : Section1.ClassFunction L)
    (M K V : Subgroup G)
    (Mfam : Finset (Section1.ClassFunction M))
    (τM τM₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G)
    (ψ βM : Section1.ClassFunction M)
    (tildeAM : Set G)
    (p q u v c d : ℕ) :
    hypothesis_14_context_data Smax Tmax W W1 W2 P Q U V C D
        Sfam Tfam τS τT p q u v c d →
      hypothesis_14_3_data Smax Tmax L H P Q U W1 W2 Lfam RL τL τL₁ φ μ01 ν10 βS βT βL →
        hypothesis_14_10_data M K V Mfam τM τM₁ ψ βM →
          Section10.section10TildeAData M K tildeAM →
              K ≠ V →
                (Nat.card (conjugatesOfPuncturedSubgroup Q) : ℝ) /
                    (Nat.card G : ℝ) ≤
                  ((Nat.card Q - 1 : ℕ) : ℝ) /
                    ((Nat.card Q : ℝ) * (v : ℝ) * (p : ℝ)) := by
  intro hctx _h143 _h1410 _htilde _hKV
  classical
  have hsrc : Section13.hypothesis_13_1_sourceData
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT p q u v c d := hctx.1
  have hsrcT : Section13.hypothesis_13_1_sourceData
      Tmax Smax W W2 W1 Q P V U D C Tfam Sfam τT τS q p v u d c :=
    section14_hypothesis_13_1_sourceData_swap hsrc
  have hDbot : D = ⊥ :=
    section14_C_eq_bot_of_pf13_12_source hsrcT
  have hTTypeP : Section8.typePDefinitionData Tmax Q V W2 W1 := by
    rcases hsrc with
      ⟨_hcase, _hSTypeP, hTTypeP, _hp, _hq, _hC, _hD, _hc, _hd,
        _hUcard, _hVcard, _hSfam, _hTfam, _hDadeS, _hDadeT, _hNotation,
        _hDadeDiff, _hZeroDegree, _hConjIndex, _hConjBetaTau,
        _hChoice, _hMin, _hFourSixS, _hFourSixT⟩
    exact hTTypeP
  have hDsrc : D = subgroupCentralizerIn V Q := by
    rcases hsrc with
      ⟨_hcase, _hSTypeP, _hTTypeP, _hp, _hq, _hC, hD, _hc, _hd,
        _hUcard, _hVcard, _hSfam, _hTfam, _hDadeS, _hDadeT, _hNotation,
        _hDadeDiff, _hZeroDegree, _hConjIndex, _hConjBetaTau,
        _hChoice, _hMin, _hFourSixS, _hFourSixT⟩
    exact hD
  have hQfit : Q = section8FittingSubgroup Tmax := by
    calc
      Q = Q ⊔ D := by rw [hDbot, sup_bot_eq]
      _ = Q ⊔ subgroupCentralizerIn V Q := by rw [hDsrc]
      _ = section8FittingSubgroup Tmax := by
        exact (Section8.theorem_8_5_a Tmax Q V W2 W1 hTTypeP).symm
  have hQpunct_fit :
      Section7.puncturedSubgroupSet Q =
        section16NonidentityElements (section8FittingSubgroup Tmax : Set G) := by
    ext x
    simp [Section7.puncturedSubgroupSet, section16NonidentityElements, hQfit]
  have hTI_fit :
      section16TISubsetWithNormalizer
        (section16NonidentityElements (section8FittingSubgroup Tmax : Set G)) Tmax :=
    Section13.section13_theorem_13_10_fitting_punctured_tiNormalizer_of_sourceContext
      Tmax Smax W W2 W1 Q P V U D C Tfam Sfam τT τS
      q p v u d c hsrcT
  have hTI :
      section16TISubsetWithNormalizer (Section7.puncturedSubgroupSet Q) Tmax := by
    simpa [hQpunct_fit] using hTI_fit
  have hOne : (1 : G) ∉ Section7.puncturedSubgroupSet Q := by
    intro h
    exact h.2 rfl
  have hcard :
      (Nat.card (conjugatesOfPuncturedSubgroup Q) : ℝ) =
        (Nat.card G : ℝ) *
          ((Nat.card (Section7.puncturedSubgroupSet Q) : ℝ) /
            (Nat.card Tmax : ℝ)) := by
    have hcard' := Section13.section13_conjugatesOfSetBySet_card_real_eq
      (X := Section7.puncturedSubgroupSet Q) (N := Tmax) hOne hTI
    rw [section14_conjugatesOfPuncturedSubgroup_eq_conjugatesOfSetBySet Q]
    exact hcard'
  have hratio :
      (Nat.card (conjugatesOfPuncturedSubgroup Q) : ℝ) / (Nat.card G : ℝ) =
        (Nat.card (Section7.puncturedSubgroupSet Q) : ℝ) /
          (Nat.card Tmax : ℝ) := by
    have hGpos : (0 : ℝ) < Nat.card G := by
      exact_mod_cast (Nat.card_pos (α := G))
    rw [hcard]
    field_simp [hGpos.ne']
  have hT_card : Nat.card Tmax = Nat.card Q * v * p :=
    section14_tmax_card_eq_core_mul_v_p_of_source
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
      p q u v c d hsrc hDbot
  have hfinal :
      (Nat.card (conjugatesOfPuncturedSubgroup Q) : ℝ) / (Nat.card G : ℝ) =
        ((Nat.card Q - 1 : ℕ) : ℝ) /
          ((Nat.card Q : ℝ) * (v : ℝ) * (p : ℝ)) := by
    rw [hratio, Section13.section13_natCard_puncturedSubgroupSet Q, hT_card]
    simp [Nat.cast_mul, mul_assoc]
  exact le_of_eq hfinal

public theorem section14_theorem_14_11_4_cardinality_estimates_source_bridge
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (Smax Tmax W W1 W2 P Q U C D L H : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (Lfam : Finset (Section1.ClassFunction L))
    (RL : G → Subgroup G)
    (τL τL₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (φ : Section1.ClassFunction L)
    (μ01 : Section1.ClassFunction Smax)
    (ν10 : Section1.ClassFunction Tmax)
    (βS : Section1.ClassFunction Smax)
    (βT : Section1.ClassFunction Tmax)
    (βL : Section1.ClassFunction L)
    (M K V : Subgroup G)
    (Mfam : Finset (Section1.ClassFunction M))
    (τM τM₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G)
    (ψ βM : Section1.ClassFunction M)
    (tildeAM : Set G)
    (p q u v c d : ℕ) :
    hypothesis_14_context_data Smax Tmax W W1 W2 P Q U V C D
        Sfam Tfam τS τT p q u v c d →
      hypothesis_14_3_data Smax Tmax L H P Q U W1 W2 Lfam RL τL τL₁ φ μ01 ν10 βS βT βL →
        hypothesis_14_10_data M K V Mfam τM τM₁ ψ βM →
          Section10.section10TildeAData M K tildeAM →
            K ≠ V →
              let Go : Set G := theorem_14_11_3_G0 tildeAM W P Q
              let Wexception : Set G :=
                (W : Set G) \ ((W1 : Set G) ∪ (W2 : Set G))
              let Cw : Set G := conjugatesOfSet Wexception
              let Cp : Set G := conjugatesOfPuncturedSubgroup P
              let Cq : Set G := conjugatesOfPuncturedSubgroup Q
              Section7.normalizedSupportEnergy (Set.univ \ tildeAM)
                  (Section1.principalCharacter G) ≤
                ((Nat.card Go : ℝ) + (Nat.card Cw : ℝ) +
                  (Nat.card Cp : ℝ) + (Nat.card Cq : ℝ)) /
                  (Nat.card G : ℝ) ∧
                ((Nat.card Cw : ℝ) + (Nat.card Cp : ℝ) +
                    (Nat.card Cq : ℝ)) / (Nat.card G : ℝ) ≤
                  1 - 1 / (p : ℝ) - 1 / (q : ℝ) +
                    1 / ((p * q : ℕ) : ℝ) +
                    ((Nat.card P - 1 : ℕ) : ℝ) /
                      ((Nat.card P : ℝ) * (u : ℝ) * (q : ℝ)) +
                    ((Nat.card Q - 1 : ℕ) : ℝ) /
                      ((Nat.card Q : ℝ) * (v : ℝ) * (p : ℝ)) := by
  intro hctx h143 h1410 htilde hKV
  let Go : Set G := theorem_14_11_3_G0 tildeAM W P Q
  let Wexception : Set G :=
    (W : Set G) \ ((W1 : Set G) ∪ (W2 : Set G))
  let Cw : Set G := conjugatesOfSet Wexception
  let Cp : Set G := conjugatesOfPuncturedSubgroup P
  let Cq : Set G := conjugatesOfPuncturedSubgroup Q
  have hW2P : W2 ≤ P := by
    rcases hctx.1 with
      ⟨_hcase, hSTypeP, _hTTypeP, _hp, _hq, _hC, _hD, _hc, _hd,
        _hUcard, _hVcard, _hSfam, _hTfam, _hDadeS, _hDadeT, _hNotation,
        _hDadeDiff, _hZeroDegree, _hConjIndex, _hConjBetaTau,
        _hChoice, _hMin, _hFourSixS, _hFourSixT⟩
    rcases hSTypeP with
      ⟨_hMF, _hW1cyc, _hW1ne, _hW1Hall, _hMcomp, _hUle, _hUnil, _hW1norm,
        _hDercomp, _hMFnotcyc, _hsecond, _hfit, _hfitDer, hW2le,
        _hW2cyc, _hW2ne, _hCent, _hHatW⟩
    exact fun x hx => (hW2le hx).1
  have hW1Q : W1 ≤ Q := by
    rcases hctx.1 with
      ⟨_hcase, _hSTypeP, hTTypeP, _hp, _hq, _hC, _hD, _hc, _hd,
        _hUcard, _hVcard, _hSfam, _hTfam, _hDadeS, _hDadeT, _hNotation,
        _hDadeDiff, _hZeroDegree, _hConjIndex, _hConjBetaTau,
        _hChoice, _hMin, _hFourSixS, _hFourSixT⟩
    rcases hTTypeP with
      ⟨_hMF, _hW2cyc, _hW2ne, _hW2Hall, _hMcomp, _hVle, _hVnil, _hW2norm,
        _hDercomp, _hMFnotcyc, _hsecond, _hfit, _hfitDer, hW1le,
        _hW1cyc, _hW1ne, _hCent, _hHatW⟩
    exact fun x hx => (hW1le hx).1
  constructor
  · have hcoverSubset :
        Set.univ \ tildeAM ⊆ Go ∪ Cw ∪ Cp ∪ Cq := by
      simpa [Go, Wexception, Cw, Cp, Cq] using
        section14_theorem_14_11_4_cover_subset_of_le
          (tildeAM := tildeAM) (W := W) (W1 := W1) (W2 := W2)
          (P := P) (Q := Q) hW2P hW1Q
    exact section14_normalizedSupportEnergy_principal_le_card_four_of_subset
      (X := Set.univ \ tildeAM) (A := Go) (B := Cw) (C := Cp) (D := Cq)
      hcoverSubset
  · have hCw :
        (Nat.card Cw : ℝ) / (Nat.card G : ℝ) ≤
          1 - 1 / (p : ℝ) - 1 / (q : ℝ) +
            1 / ((p * q : ℕ) : ℝ) := by
      simpa [Wexception, Cw] using
        section14_theorem_14_11_4_Wexception_cardinality_source_bridge
          Smax Tmax W W1 W2 P Q U C D L H Sfam Tfam τS τT
          Lfam RL τL τL₁ φ μ01 ν10 βS βT βL
          M K V Mfam τM τM₁ ψ βM tildeAM p q u v c d
          hctx h143 h1410 htilde hKV
    have hCp :
        (Nat.card Cp : ℝ) / (Nat.card G : ℝ) ≤
          ((Nat.card P - 1 : ℕ) : ℝ) /
            ((Nat.card P : ℝ) * (u : ℝ) * (q : ℝ)) := by
      simpa [Cp] using
        section14_theorem_14_11_4_Ppunctured_cardinality_source_bridge
          Smax Tmax W W1 W2 P Q U C D L H Sfam Tfam τS τT
          Lfam RL τL τL₁ φ μ01 ν10 βS βT βL
          M K V Mfam τM τM₁ ψ βM tildeAM p q u v c d
          hctx h143 h1410 htilde hKV
    have hCq :
        (Nat.card Cq : ℝ) / (Nat.card G : ℝ) ≤
          ((Nat.card Q - 1 : ℕ) : ℝ) /
            ((Nat.card Q : ℝ) * (v : ℝ) * (p : ℝ)) := by
      simpa [Cq] using
        section14_theorem_14_11_4_Qpunctured_cardinality_source_bridge
          Smax Tmax W W1 W2 P Q U C D L H Sfam Tfam τS τT
          Lfam RL τL τL₁ φ μ01 ν10 βS βT βL
          M K V Mfam τM τM₁ ψ βM tildeAM p q u v c d
          hctx h143 h1410 htilde hKV
    have hGne : (Nat.card G : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.card_pos (α := G)).ne'
    have hsplit :
        ((Nat.card Cw : ℝ) + (Nat.card Cp : ℝ) +
            (Nat.card Cq : ℝ)) / (Nat.card G : ℝ) =
          (Nat.card Cw : ℝ) / (Nat.card G : ℝ) +
            (Nat.card Cp : ℝ) / (Nat.card G : ℝ) +
              (Nat.card Cq : ℝ) / (Nat.card G : ℝ) := by
      field_simp [hGne]
    rw [hsplit]
    linarith

public theorem section14_theorem_14_11_4_upper_inequalities_source_bridge
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (Smax Tmax W W1 W2 P Q U C D L H : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (Lfam : Finset (Section1.ClassFunction L))
    (RL : G → Subgroup G)
    (τL τL₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (φ : Section1.ClassFunction L)
    (μ01 : Section1.ClassFunction Smax)
    (ν10 : Section1.ClassFunction Tmax)
    (βS : Section1.ClassFunction Smax)
    (βT : Section1.ClassFunction Tmax)
    (βL : Section1.ClassFunction L)
    (M K V : Subgroup G)
    (Mfam : Finset (Section1.ClassFunction M))
    (τM τM₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G)
    (ψ βM : Section1.ClassFunction M)
    (tildeAM : Set G)
    (R : G → Subgroup G)
    (ψτ : Section1.ClassFunction G)
    (p q u v c d : ℕ) :
    hypothesis_14_context_data Smax Tmax W W1 W2 P Q U V C D
        Sfam Tfam τS τT p q u v c d →
      hypothesis_14_3_data Smax Tmax L H P Q U W1 W2 Lfam RL τL τL₁ φ μ01 ν10 βS βT βL →
        hypothesis_14_10_data M K V Mfam τM τM₁ ψ βM →
          Section10.section10TildeAData M K tildeAM →
            K ≠ V →
              ψτ = τM₁ ψ →
                theorem_14_11_3_data (theorem_14_11_3_G0 tildeAM W P Q) ψτ →
                  Section2.dadeSupport (Section12.typeIASet M K) R = tildeAM →
                    Section7.normalizedSupportEnergy (Set.univ \ tildeAM) ψτ +
                        Section7.weightedProjectionEnergy (Section12.typeIASet M K)
                          M R ψτ ≤
                      Section7.normalizedSupportEnergy (Set.univ \ tildeAM)
                          (Section1.principalCharacter G) +
                        ((Section12.typeIASet M K).ncard : ℝ) /
                          (Nat.card M : ℝ) →
                    let Wexception : Set G :=
                      (W : Set G) \ ((W1 : Set G) ∪ (W2 : Set G))
                    (1 / (Nat.card G : ℝ)) *
                        ((∑ g : theorem_14_11_3_G0 tildeAM W P Q,
                            Complex.normSq (ψτ g.1)) -
                          (Nat.card (theorem_14_11_3_G0 tildeAM W P Q) : ℝ) -
                          (Nat.card (conjugatesOfSet Wexception) : ℝ) -
                          (Nat.card (conjugatesOfPuncturedSubgroup P) : ℝ) -
                          (Nat.card (conjugatesOfPuncturedSubgroup Q) : ℝ)) +
                        Section7.weightedProjectionEnergy (Section12.typeIASet M K)
                          M R ψτ -
                          ((Nat.card K - 1 : ℕ) : ℝ) / (Nat.card M : ℝ) ≤ 0 ∧
                      Section7.weightedProjectionEnergy (Section12.typeIASet M K)
                          M R ψτ ≤
                        1 - 1 / (p : ℝ) - 1 / (q : ℝ) +
                          1 / ((p * q : ℕ) : ℝ) +
                          ((Nat.card P - 1 : ℕ) : ℝ) /
                            ((Nat.card P : ℝ) * (u : ℝ) * (q : ℝ)) +
                          ((Nat.card Q - 1 : ℕ) : ℝ) /
                            ((Nat.card Q : ℝ) * (v : ℝ) * (p : ℝ)) +
                          ((Nat.card K - 1 : ℕ) : ℝ) /
                            ((Nat.card K : ℝ) * ((p * q : ℕ) : ℝ)) := by
  intro hctx h143 h1410 htilde hKV hψτ h113 hsupp h75raw
  classical
  let Go : Set G := theorem_14_11_3_G0 tildeAM W P Q
  letI : Fintype Go := Fintype.ofFinite Go
  let Wexception : Set G :=
    (W : Set G) \ ((W1 : Set G) ∪ (W2 : Set G))
  let Cw : Set G := conjugatesOfSet Wexception
  let Cp : Set G := conjugatesOfPuncturedSubgroup P
  let Cq : Set G := conjugatesOfPuncturedSubgroup Q
  let rho : ℝ :=
    Section7.weightedProjectionEnergy (Section12.typeIASet M K) M R ψτ
  let finalBound : ℝ :=
    1 - 1 / (p : ℝ) - 1 / (q : ℝ) +
      1 / ((p * q : ℕ) : ℝ) +
      ((Nat.card P - 1 : ℕ) : ℝ) /
        ((Nat.card P : ℝ) * (u : ℝ) * (q : ℝ)) +
      ((Nat.card Q - 1 : ℕ) : ℝ) /
        ((Nat.card Q : ℝ) * (v : ℝ) * (p : ℝ)) +
      ((Nat.card K - 1 : ℕ) : ℝ) /
        ((Nat.card K : ℝ) * ((p * q : ℕ) : ℝ))
  have h1410orig := h1410
  rcases h1410 with
    ⟨hMmax, _hModd, _hNormVleM, hKMF, hTypeI, _hDadeM, _hPunctM,
      _h52M, _hExtM, _hψmem, _hψirr, _hψdeg, _hβM⟩
  rcases section14_theorem_14_11_4_cardinality_estimates_source_bridge
      Smax Tmax W W1 W2 P Q U C D L H Sfam Tfam τS τT
      Lfam RL τL τL₁ φ μ01 ν10 βS βT βL
      M K V Mfam τM τM₁ ψ βM tildeAM p q u v c d
      hctx h143 h1410orig htilde hKV with
    ⟨hcover, hcardConj⟩
  have hAcard : (Section12.typeIASet M K).ncard = Nat.card K - 1 :=
    section14_typeIASet_ncard_eq_kernel_sub_one_of_typeI
      hMmax hKMF hTypeI
  have hGoX : Go ⊆ Set.univ \ tildeAM := by
    intro g hg
    rcases section14_not_mem_components_of_mem_G0 (tildeAM := tildeAM)
        (W := W) (P := P) (Q := Q) (g := g) (by simpa [Go] using hg) with
      ⟨hnotTilde, _hnotW, _hnotP, _hnotQ⟩
    exact ⟨trivial, hnotTilde⟩
  have hnonpos :
      (1 / (Nat.card G : ℝ)) *
          ((∑ g : Go, Complex.normSq (ψτ g.1)) -
            (Nat.card Go : ℝ) - (Nat.card Cw : ℝ) -
            (Nat.card Cp : ℝ) - (Nat.card Cq : ℝ)) + rho -
          ((Nat.card K - 1 : ℕ) : ℝ) / (Nat.card M : ℝ) ≤ 0 := by
    exact section14_theorem_14_11_4_nonpositive_of_pf75
      (M := M) (K := K) (Go := Go) (Cw := Cw) (Cp := Cp) (Cq := Cq)
      (X := Set.univ \ tildeAM) (ψτ := ψτ) (rho := rho)
      hGoX (by simpa [Go, Wexception, Cw, Cp, Cq] using hcover)
      hAcard (by simpa [rho] using h75raw)
  rcases section14EtaData_of_sourceData hctx.1 with ⟨η, heta⟩
  let βMτ : Section1.ClassFunction G := τM βM
  let e : ℕ := K.relIndex M
  have h112 : theorem_14_11_2_data M K η βMτ ψτ e :=
    section14_theorem_14_11_2_source_bridge
      Smax Tmax W W1 W2 P Q U C D L H Sfam Tfam τS τT
      Lfam RL τL τL₁ φ μ01 ν10 βS βT βL
      M K V Mfam τM τM₁ ψ βM p q u v c d e η βMτ ψτ
      hctx h143 h1410orig heta hKV rfl hψτ rfl
  rcases h112 with ⟨heq, hrel_mul, _hexp⟩
  have hrel : K.relIndex M = p * q := by
    calc
      K.relIndex M = e := heq.symm
      _ = p * q := hrel_mul
  have hKleM : K ≤ M := Section12.section16MFSubgroup_le hKMF
  have hkterm :
      ((Nat.card K - 1 : ℕ) : ℝ) / (Nat.card M : ℝ) =
        ((Nat.card K - 1 : ℕ) : ℝ) /
          ((Nat.card K : ℝ) * ((p * q : ℕ) : ℝ)) :=
    section14_kernel_card_term_denominator_eq_of_relIndex_eq_mul
      (G := G) (M := M) (K := K) (p := p) (q := q) hKleM hrel
  have hcardFinal :
      ((Nat.card Cw : ℝ) + (Nat.card Cp : ℝ) + (Nat.card Cq : ℝ)) /
          (Nat.card G : ℝ) +
        ((Nat.card K - 1 : ℕ) : ℝ) / (Nat.card M : ℝ) ≤ finalBound := by
    let base : ℝ :=
      1 - 1 / (p : ℝ) - 1 / (q : ℝ) +
        1 / ((p * q : ℕ) : ℝ) +
        ((Nat.card P - 1 : ℕ) : ℝ) /
          ((Nat.card P : ℝ) * (u : ℝ) * (q : ℝ)) +
        ((Nat.card Q - 1 : ℕ) : ℝ) /
          ((Nat.card Q : ℝ) * (v : ℝ) * (p : ℝ))
    let kM : ℝ :=
      ((Nat.card K - 1 : ℕ) : ℝ) / (Nat.card M : ℝ)
    let kK : ℝ :=
      ((Nat.card K - 1 : ℕ) : ℝ) /
        ((Nat.card K : ℝ) * ((p * q : ℕ) : ℝ))
    have hcardConj' :
        ((Nat.card Cw : ℝ) + (Nat.card Cp : ℝ) + (Nat.card Cq : ℝ)) /
            (Nat.card G : ℝ) ≤ base := by
      simpa [base, Go, Wexception, Cw, Cp, Cq] using hcardConj
    have hkterm' : kM = kK := by
      simpa [kM, kK] using hkterm
    have hmain :
        ((Nat.card Cw : ℝ) + (Nat.card Cp : ℝ) + (Nat.card Cq : ℝ)) /
            (Nat.card G : ℝ) + kM ≤ base + kK := by
      linarith
    have hfinal : finalBound = base + kK := by
      dsimp [finalBound, base, kK]
    rw [hfinal]
    exact hmain
  have hupper : rho ≤ finalBound :=
    section14_theorem_14_11_4_upper_bound_of_nonpositive
      (M := M) (K := K) (Go := Go) (Cw := Cw) (Cp := Cp) (Cq := Cq)
      (ψτ := ψτ) (rho := rho) (finalBound := finalBound)
      (by simpa [Go] using h113) hnonpos hcardFinal
  exact ⟨by simpa [Go, Wexception, Cw, Cp, Cq, rho] using hnonpos,
    by simpa [finalBound, rho] using hupper⟩

public theorem section14_kernel_card_ne_one_of_frobeniusJoin
    {G : Type*} [Group G] [Finite G]
    (K R : Subgroup G)
    (hfrob : section12FrobeniusJoinWithKernel K R) :
    Nat.card K ≠ 1 := by
  classical
  let S : Subgroup G := K ⊔ R
  let Ksub : Subgroup S := K.subgroupOf S
  have hcardKsub : Nat.card Ksub = Nat.card K :=
    natCard_subgroupOf_eq K S le_sup_left
  have hKsub_ne_bot : Ksub ≠ ⊥ :=
    IsFrobeniusGroupWithKernelComplement.kernel_ne_bot hfrob
  intro hcard
  have hcardSub : Nat.card Ksub = 1 := by
    rw [hcardKsub, hcard]
  exact hKsub_ne_bot ((Subgroup.card_eq_one (H := Ksub)).1 hcardSub)

public theorem section14_two_mul_lt_of_odd_and_dvd_sub_one
    {q u : ℕ}
    (hdiv : q ∣ u - 1)
    (huOdd : Odd u)
    (hu_ne_one : u ≠ 1)
    (hqOdd : Odd q) :
    2 * q < u := by
  rcases hdiv with ⟨t, ht⟩
  rcases huOdd with ⟨ru, hru⟩
  rcases hqOdd with ⟨rq, hrq⟩
  have hu_pos : 0 < u := by omega
  have hu_eq : u = q * t + 1 := by
    calc
      u = (u - 1) + 1 := (Nat.succ_pred_eq_of_pos hu_pos).symm
      _ = q * t + 1 := by rw [ht]
  have ht_ne_zero : t ≠ 0 := by
    intro ht0
    apply hu_ne_one
    rw [hu_eq, ht0]
    simp
  have ht_ne_one : t ≠ 1 := by
    intro ht1
    have hu_eq_q : u = q + 1 := by simpa [ht1] using hu_eq
    rw [hru, hrq] at hu_eq_q
    omega
  have ht_ge_two : 2 ≤ t := by omega
  nlinarith

public theorem section14_theorem_14_11_4_u_odd_source_bridge
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (Smax Tmax W W1 W2 P Q U V C D L H : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (Lfam : Finset (Section1.ClassFunction L))
    (RL : G → Subgroup G)
    (τL τL₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (φ : Section1.ClassFunction L)
    (μ01 : Section1.ClassFunction Smax)
    (ν10 : Section1.ClassFunction Tmax)
    (βS : Section1.ClassFunction Smax)
    (βT : Section1.ClassFunction Tmax)
    (βL : Section1.ClassFunction L)
    (M K : Subgroup G)
    (Mfam : Finset (Section1.ClassFunction M))
    (τM τM₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G)
    (ψ βM : Section1.ClassFunction M)
    (p q u v c d : ℕ) :
    hypothesis_14_context_data Smax Tmax W W1 W2 P Q U V C D
        Sfam Tfam τS τT p q u v c d →
      hypothesis_14_3_data Smax Tmax L H P Q U W1 W2 Lfam RL τL τL₁ φ μ01 ν10 βS βT βL →
        hypothesis_14_10_data M K V Mfam τM τM₁ ψ βM →
          K ≠ V →
            Odd u := by
  intro hctx h143 _h1410 _hKV
  have hcase97 : Section13.case_9_7_b_for_section13 Smax C p q u :=
    section14_theorem_14_6_source_bridge
      Smax Tmax W W1 W2 P Q U V C D L H Sfam Tfam τS τT
      Lfam RL τL τL₁ φ μ01 ν10 βS βT βL p q u v c d hctx h143
  rcases hcase97 with ⟨_hC, hpPrime, hqPrime, _hcop, hdivGeom⟩
  have h2q : 2 < q := section14_two_lt_q_of_sourceData hctx
  have hqOdd : Odd q := hqPrime.odd_of_ne_two (ne_of_gt h2q)
  have hpOdd : Odd p := hpPrime.odd_of_ne_two (ne_of_gt (lt_trans h2q hctx.2))
  have hgeomOdd : Odd ((p ^ q - 1) / (p - 1)) :=
    Section13.section13_odd_geom_quotient hpPrime hpOdd hqOdd
  exact Odd.of_dvd_nat hgeomOdd hdivGeom

public theorem section14_theorem_14_11_4_v_le_pq_source_inputs_bridge
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (Smax Tmax W W1 W2 P Q U C D L H : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (Lfam : Finset (Section1.ClassFunction L))
    (RL : G → Subgroup G)
    (τL τL₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (φ : Section1.ClassFunction L)
    (μ01 : Section1.ClassFunction Smax)
    (ν10 : Section1.ClassFunction Tmax)
    (βS : Section1.ClassFunction Smax)
    (βT : Section1.ClassFunction Tmax)
    (βL : Section1.ClassFunction L)
    (M K V : Subgroup G)
    (Mfam : Finset (Section1.ClassFunction M))
    (τM τM₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G)
    (ψ βM : Section1.ClassFunction M)
    (p q u v c d : ℕ) :
    hypothesis_14_context_data Smax Tmax W W1 W2 P Q U V C D
        Sfam Tfam τS τT p q u v c d →
      hypothesis_14_3_data Smax Tmax L H P Q U W1 W2 Lfam RL τL τL₁ φ μ01 ν10 βS βT βL →
        hypothesis_14_10_data M K V Mfam τM τM₁ ψ βM →
          K ≠ V →
            2 * q < u := by
  intro hctx h143 h1410 hKV
  have huOdd : Odd u :=
    section14_theorem_14_11_4_u_odd_source_bridge
      Smax Tmax W W1 W2 P Q U V C D L H Sfam Tfam τS τT
      Lfam RL τL τL₁ φ μ01 ν10 βS βT βL
      M K Mfam τM τM₁ ψ βM p q u v c d hctx h143 h1410 hKV
  have hsrc : Section13.hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d := hctx.1
  rcases hsrc with
    ⟨_hcase, _hSTypeP, _hTTypeP, _hp, hqcard, _hC, _hD, _hc, _hd, hUcard,
      _hVcard, _hSfam, _hTfam, _hDadeS, _hDadeT, _hNotation, _hDadeDiff, _hZeroDegree, _hConjIndex, _hConjBetaTau, _hChoice, _hMin, _hFourSixS, _hFourSixT⟩
  rcases Section13.theorem_13_2 Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d hctx.1 with
    ⟨_hSmaxMF, _htypeS, _htypeII, _hUcomm, hUfrob, _hPelem,
      _hPcard, _hu, _hSfamCoh, _hTI, _hTauS⟩
  have hc_one : c = 1 :=
    Section13.theorem_13_12 Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d hctx.1
  have hUcard_eq : Nat.card U = u := by
    rw [hUcard, hc_one, Nat.mul_one]
  have hdivCard : Nat.card W1 ∣ Nat.card U - 1 :=
    section14_frobeniusJoin_complement_card_dvd_kernel_card_sub_one U W1 hUfrob
  have hdivU : Nat.card W1 ∣ u - 1 := by
    rw [hUcard_eq] at hdivCard
    exact hdivCard
  have hdiv : q ∣ u - 1 := by
    rw [hqcard]
    exact hdivU
  have hU_ne_one : u ≠ 1 := by
    intro hu1
    exact (section14_kernel_card_ne_one_of_frobeniusJoin U W1 hUfrob)
      (hUcard_eq.trans hu1)
  have h2q : 2 < q := section14_two_lt_q_of_sourceData hctx
  rcases section14_context_primes_of_sourceData hctx with ⟨_hpPrime, hqPrime⟩
  have hqOdd : Odd q := hqPrime.odd_of_ne_two (ne_of_gt h2q)
  exact section14_two_mul_lt_of_odd_and_dvd_sub_one hdiv huOdd hU_ne_one hqOdd

public theorem section14_theorem_14_11_4_v_le_pq_source_bridge
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (Smax Tmax W W1 W2 P Q U C D L H : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (Lfam : Finset (Section1.ClassFunction L))
    (RL : G → Subgroup G)
    (τL τL₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (φ : Section1.ClassFunction L)
    (μ01 : Section1.ClassFunction Smax)
    (ν10 : Section1.ClassFunction Tmax)
    (βS : Section1.ClassFunction Smax)
    (βT : Section1.ClassFunction Tmax)
    (βL : Section1.ClassFunction L)
    (M K V : Subgroup G)
    (Mfam : Finset (Section1.ClassFunction M))
    (τM τM₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G)
    (ψ βM : Section1.ClassFunction M)
    (tildeAM : Set G)
    (ψτ : Section1.ClassFunction G)
    (psiRhoNormSq : ℝ)
    (p q u v c d : ℕ) :
    hypothesis_14_context_data Smax Tmax W W1 W2 P Q U V C D
        Sfam Tfam τS τT p q u v c d →
      hypothesis_14_3_data Smax Tmax L H P Q U W1 W2 Lfam RL τL τL₁ φ μ01 ν10 βS βT βL →
        hypothesis_14_10_data M K V Mfam τM τM₁ ψ βM →
          Section10.section10TildeAData M K tildeAM →
            K ≠ V →
              ψτ = τM₁ ψ →
                theorem_14_11_4_inequalityData M K W W1 W2 P Q
                    (theorem_14_11_3_G0 tildeAM W P Q) ψτ psiRhoNormSq p q u v →
                  theorem_14_11_1_data M K p q u v →
                    Section13.case_9_7_b_for_section13 Tmax D q p v →
                      v = (q ^ p - 1) / (q - 1) →
                        v ≤ p * q := by
  intro hctx h143 h1410 htilde hKV hψτ hineq h111 hcaseT hv
  rcases section14_theorem_14_11_4_v_le_pq_source_inputs_bridge
      Smax Tmax W W1 W2 P Q U C D L H Sfam Tfam τS τT
      Lfam RL τL τL₁ φ μ01 ν10 βS βT βL
      M K V Mfam τM τM₁ ψ βM p q u v c d hctx h143 h1410 hKV with
    hu_gt
  have h2q : 2 < q := section14_two_lt_q_of_sourceData hctx
  rcases h111 with ⟨hKgt, _hratio_gt, _hratio_le⟩
  have hv_pq : v > p * q :=
    section14_v_gt_pq_of_case_b_formula hctx.2 hcaseT hv
  rcases hcaseT with ⟨_hDT, _hq, hp, _hcop, _hdiv⟩
  have hv_gt : 2 * p < v := by
    have h2p_lt_pq : 2 * p < p * q := by
      have h2p_lt_qp : 2 * p < q * p :=
        Nat.mul_lt_mul_of_pos_right h2q hp.pos
      simpa [Nat.mul_comm] using h2p_lt_qp
    exact lt_trans h2p_lt_pq hv_pq
  have hq3 : 3 ≤ q := by omega
  have hineq_core :
      1 / (p : ℝ) + 1 / (q : ℝ) ≤
        ((p * q : ℕ) : ℝ) / (Nat.card K : ℝ) +
          2 / (((p * q : ℕ) : ℝ)) +
          1 / (((u * q : ℕ) : ℝ)) +
          1 / (((v * p : ℕ) : ℝ)) :=
    section14_real_ineq_of_14_11_4_inequalityData hp.pos (by omega)
      (by omega) (by omega) hineq
  exact section14_v_le_pq_of_real_squeeze hp.pos hq3 hctx.2 hu_gt hv_gt
    hKgt hineq_core

public theorem section14_theorem_14_11_4_contradiction_with_14_11_1_source_bridge
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (Smax Tmax W W1 W2 P Q U C D L H : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (Lfam : Finset (Section1.ClassFunction L))
    (RL : G → Subgroup G)
    (τL τL₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (φ : Section1.ClassFunction L)
    (μ01 : Section1.ClassFunction Smax)
    (ν10 : Section1.ClassFunction Tmax)
    (βS : Section1.ClassFunction Smax)
    (βT : Section1.ClassFunction Tmax)
    (βL : Section1.ClassFunction L)
    (M K V : Subgroup G)
    (Mfam : Finset (Section1.ClassFunction M))
    (τM τM₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G)
    (ψ βM : Section1.ClassFunction M)
    (tildeAM : Set G)
    (ψτ : Section1.ClassFunction G)
    (psiRhoNormSq : ℝ)
    (p q u v c d : ℕ) :
    hypothesis_14_context_data Smax Tmax W W1 W2 P Q U V C D
        Sfam Tfam τS τT p q u v c d →
      hypothesis_14_3_data Smax Tmax L H P Q U W1 W2 Lfam RL τL τL₁ φ μ01 ν10 βS βT βL →
        hypothesis_14_10_data M K V Mfam τM τM₁ ψ βM →
          Section10.section10TildeAData M K tildeAM →
            K ≠ V →
              ψτ = τM₁ ψ →
                theorem_14_11_4_inequalityData M K W W1 W2 P Q
                    (theorem_14_11_3_G0 tildeAM W P Q) ψτ psiRhoNormSq p q u v →
                  theorem_14_11_1_data M K p q u v →
                    Section13.case_9_7_b_for_section13 Tmax D q p v →
                      v = (q ^ p - 1) / (q - 1) →
                  False := by
  intro hctx h143 h1410 htilde hKV hψτ hineq h111 hcaseT hv
  have hv_le : v ≤ p * q :=
    section14_theorem_14_11_4_v_le_pq_source_bridge
      Smax Tmax W W1 W2 P Q U C D L H Sfam Tfam τS τT
      Lfam RL τL τL₁ φ μ01 ν10 βS βT βL
      M K V Mfam τM τM₁ ψ βM tildeAM ψτ psiRhoNormSq p q u v c d
      hctx h143 h1410 htilde hKV hψτ hineq h111 hcaseT hv
  have hv_gt : v > p * q :=
    section14_v_gt_pq_of_case_b_formula hctx.2 hcaseT hv
  exact (Nat.not_lt_of_ge hv_le) hv_gt

public theorem section14_theorem_14_11_4_contradiction_bridge
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (Smax Tmax W W1 W2 P Q U C D L H : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (Lfam : Finset (Section1.ClassFunction L))
    (RL : G → Subgroup G)
    (τL τL₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (φ : Section1.ClassFunction L)
    (μ01 : Section1.ClassFunction Smax)
    (ν10 : Section1.ClassFunction Tmax)
    (βS : Section1.ClassFunction Smax)
    (βT : Section1.ClassFunction Tmax)
    (βL : Section1.ClassFunction L)
    (M K V : Subgroup G)
    (Mfam : Finset (Section1.ClassFunction M))
    (τM τM₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G)
    (ψ βM : Section1.ClassFunction M)
    (tildeAM : Set G)
    (ψτ : Section1.ClassFunction G)
    (psiRhoNormSq : ℝ)
    (p q u v c d : ℕ) :
    hypothesis_14_context_data Smax Tmax W W1 W2 P Q U V C D
        Sfam Tfam τS τT p q u v c d →
      hypothesis_14_3_data Smax Tmax L H P Q U W1 W2 Lfam RL τL τL₁ φ μ01 ν10 βS βT βL →
        hypothesis_14_10_data M K V Mfam τM τM₁ ψ βM →
          Section10.section10TildeAData M K tildeAM →
            K ≠ V →
              ψτ = τM₁ ψ →
                theorem_14_11_4_inequalityData M K W W1 W2 P Q
                    (theorem_14_11_3_G0 tildeAM W P Q) ψτ psiRhoNormSq p q u v →
                  False := by
  intro hctx h143 h1410 htilde hKV hψτ hineq
  have h111 : theorem_14_11_1_data M K p q u v :=
    section14_theorem_14_11_1_source_bridge
      Smax Tmax W W1 W2 P Q U C D L H Sfam Tfam τS τT
      Lfam RL τL τL₁ φ μ01 ν10 βS βT βL
      M K V Mfam τM τM₁ ψ βM p q u v c d
      hctx h143 h1410 hKV
  rcases section14_theorem_14_4_source_bridge
      Smax Tmax W W1 W2 P Q U V C D L H Sfam Tfam τS τT
      Lfam RL τL τL₁ φ μ01 ν10 βS βT βL p q u v c d hctx h143 with
    ⟨hcaseT, hv⟩
  exact section14_theorem_14_11_4_contradiction_with_14_11_1_source_bridge
    Smax Tmax W W1 W2 P Q U C D L H Sfam Tfam τS τT
    Lfam RL τL τL₁ φ μ01 ν10 βS βT βL
    M K V Mfam τM τM₁ ψ βM tildeAM ψτ psiRhoNormSq p q u v c d
    hctx h143 h1410 htilde hKV hψτ hineq h111 hcaseT hv


public theorem section14_theorem_14_11_tildeAData_source_bridge
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (Smax Tmax W W1 W2 P Q U C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (M K V : Subgroup G)
    (Mfam : Finset (Section1.ClassFunction M))
    (τM τM₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G)
    (ψ βM : Section1.ClassFunction M)
    (p q u v c d : ℕ) :
    hypothesis_14_context_data Smax Tmax W W1 W2 P Q U V C D
        Sfam Tfam τS τT p q u v c d →
      hypothesis_14_10_data M K V Mfam τM τM₁ ψ βM →
        ∃ tildeAM : Set G, Section10.section10TildeAData M K tildeAM := by
  intro hctx h1410
  rcases h1410 with
    ⟨hMmax, _hModd, _hVnorm, hMF, hTypeI, _hDade, _hPunctM, _h52M, _hCoherM,
      _hψmem, _hψirr, _hψdeg, _hβM⟩
  rcases hctx.1 with
    ⟨_hcase, _hSTypeP, _hTTypeP, _hp, _hq, _hC, _hD, _hc, _hd,
      _hUcard, _hVcard, _hSfam, _hTfam, _hDadeS, _hDadeT, _hNotation,
      _hDadeDiff, _hZeroDegree, _hConjIndex, _hConjBetaTau,
      hChoice, _hMin, _hFourSixS, _hFourSixT⟩
  rcases hChoice M K hMmax hMF (Or.inl hTypeI) with ⟨Ms, hMs⟩
  have hMsEq : Ms = K := Section8.msChoiceSource_eq_mf_of_typeI hMs hTypeI
  have hMsK : Section8.msChoiceSource M K K := by
    simpa [hMsEq] using hMs
  have h810 :
      Section8.notation_8_10_source_data M K K
        (Section12.typeIASet M K) (Section12.typeIASet M K) (Section8.a1Set K) :=
    Section12.notation_8_10_source_data_of_typeI_msChoice M K hMmax hMF hTypeI hMsK
  have hA1X : Section8.a1Set K ⊆ Section12.typeIASet M K := by
    simpa [Section8.a1Set] using
      Section12.nonidentity_kernel_subset_typeIASet M K
        (Section12.section16MFSubgroup_le hMF)
  rcases Section8.exists_notation_8_14_source_data_of_theorem_8_13
      M K K (Section12.typeIASet M K) (Section12.typeIASet M K)
      (Section8.a1Set K) (Section12.typeIASet M K)
      (by infer_instance) h810 (Or.inl rfl) hA1X with
    ⟨R, tildeAM, tildeA0, tildeA1, h814⟩
  exact ⟨tildeAM, K, Section12.typeIASet M K, Section12.typeIASet M K,
    Section8.a1Set K, Section8.section8DSet M (Section12.typeIASet M K),
    tildeA0, tildeA1, R, h810, h814⟩

public theorem section14_theorem_14_11_index_small_complement_contradiction_source_bridge
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (Smax Tmax W W1 W2 P Q U C D L H : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (Lfam : Finset (Section1.ClassFunction L))
    (RL : G → Subgroup G)
    (τL τL₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (φ : Section1.ClassFunction L)
    (μ01 : Section1.ClassFunction Smax)
    (ν10 : Section1.ClassFunction Tmax)
    (βS : Section1.ClassFunction Smax)
    (βT : Section1.ClassFunction Tmax)
    (βL : Section1.ClassFunction L)
    (M K V : Subgroup G)
    (Mfam : Finset (Section1.ClassFunction M))
    (τM τM₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G)
    (ψ βM : Section1.ClassFunction M)
    (p q u v c d : ℕ) :
    hypothesis_14_context_data Smax Tmax W W1 W2 P Q U V C D
        Sfam Tfam τS τT p q u v c d →
      hypothesis_14_3_data Smax Tmax L H P Q U W1 W2 Lfam RL τL τL₁ φ μ01 ν10 βS βT βL →
        hypothesis_14_10_data M K V Mfam τM τM₁ ψ βM →
          K = V →
            section12ComplementIn M K W2 →
              False := by
  intro hctx h143 h1410 hKV hcompW2
  classical
  rcases hctx.1 with
    ⟨hcase, _hSTypeP, hTTypeP, _hp, _hq, _hC, _hD, _hc, _hd,
      _hUcard, _hVcard, _hSfam, _hTfam, _hDadeS, _hDadeT, _hNotation,
      _hDadeDiff, _hZeroDegree, _hConjIndex, _hConjBetaTau,
      hChoice, _hMin, _hFourSixS, _hFourSixT⟩
  rcases hcase with
    ⟨_hprod, _hcyc, _hW1ne, _hW2ne, _hnorm, _hSmax, hTmax, _hSMF,
      hTMF, _hSeq, _hTeq, _hSdisj, _hTdisj, _hST, _hTypeII, _hSType,
      _hTType, _hCover⟩
  rcases hTTypeP with
    ⟨hQMF, _hW2cyc, _hW2ne, _hW2Hall, hTcomp, hVleDer,
      _hVnil, _hW2norm, _hDerComp, _hQnoncyc, _hSecond, _hFit,
      _hFitLe, _hW1le, _hW1cyc, _hW1ne, _hCent, _hNorm⟩
  rcases h1410 with
    ⟨hMmax, _hModd, _hNormVleM, hKMF, hTypeI, _hDadeM, _hPunctM, _h52M,
      _hCoherM, _hψmem, _hψirr, _hψdeg, _hβM⟩
  have hVleT : V ≤ Tmax :=
    hVleDer.trans (section12_ambientDerivedSubgroup_le (G := G) (E := Tmax))
  have hW2leT : W2 ≤ Tmax := hTcomp.2.1
  have hMleT : M ≤ Tmax := by
    rw [hcompW2.2.2.1]
    exact sup_le (by simpa [hKV] using hVleT) hW2leT
  have hMco : IsCoatom M := by
    simpa [section9MaximalSubgroups] using hMmax
  have hTco : IsCoatom Tmax := by
    simpa [section9MaximalSubgroups] using hTmax
  have hM_eq_Tmax : M = Tmax := by
    by_cases hEq : M = Tmax
    · exact hEq
    · have hlt : M < Tmax := lt_of_le_of_ne hMleT hEq
      have hTop : Tmax = ⊤ := hMco.2 Tmax hlt
      exact False.elim (hTco.1 hTop)
  have hQMF_M : section16MFSubgroup M Q := by
    simpa [hM_eq_Tmax] using hQMF
  have hQeqK : Q = K :=
    le_antisymm (hKMF.2 Q hQMF_M.1) (hQMF_M.2 K hKMF.1)
  have htypeT16 : section16TypeII Tmax Q :=
    section14_theorem_14_9_source_bridge
      Smax Tmax W W1 W2 P Q U V C D L H Sfam Tfam τS τT
      Lfam RL τL τL₁ φ μ01 ν10 βS βT βL p q u v c d hctx h143
  have htypeII_MK : section16TypeII M K := by
    simpa [hM_eq_Tmax, hQeqK] using htypeT16
  rcases hChoice M K hMmax hKMF (Or.inl hTypeI) with ⟨Ms, hMs⟩
  have hnotII : ¬ Section8.typeIIDefinitionData M K := by
    rcases hMs with hI | hII | hIII | hIV | hV
    · exact hI.2.1
    · exact False.elim (hII.1 hTypeI)
    · exact False.elim (hIII.1 hTypeI)
    · exact False.elim (hIV.1 hTypeI)
    · exact False.elim (hV.1 hTypeI)
  exact hnotII
    (Section8.theorem_8_8_typeII_to_source_public hMmax hKMF htypeII_MK)

public theorem section14_theorem_14_11_index_of_eq_source_bridge
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (Smax Tmax W W1 W2 P Q U C D L H : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (Lfam : Finset (Section1.ClassFunction L))
    (RL : G → Subgroup G)
    (τL τL₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (φ : Section1.ClassFunction L)
    (μ01 : Section1.ClassFunction Smax)
    (ν10 : Section1.ClassFunction Tmax)
    (βS : Section1.ClassFunction Smax)
    (βT : Section1.ClassFunction Tmax)
    (βL : Section1.ClassFunction L)
    (M K V : Subgroup G)
    (Mfam : Finset (Section1.ClassFunction M))
    (τM τM₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G)
    (ψ βM : Section1.ClassFunction M)
    (p q u v c d : ℕ) :
    hypothesis_14_context_data Smax Tmax W W1 W2 P Q U V C D
        Sfam Tfam τS τT p q u v c d →
      hypothesis_14_3_data Smax Tmax L H P Q U W1 W2 Lfam RL τL τL₁ φ μ01 ν10 βS βT βL →
        hypothesis_14_10_data M K V Mfam τM τM₁ ψ βM →
          K = V →
            K.relIndex M = p * q := by
  intro hctx h143 h1410 hKV
  classical
  have hsrc : Section13.hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d := hctx.1
  have htypeT : Section8.typeIIDefinitionData Tmax Q := by
    have htypeT16 : section16TypeII Tmax Q :=
      section14_theorem_14_9_source_bridge
        Smax Tmax W W1 W2 P Q U V C D L H Sfam Tfam τS τT
        Lfam RL τL τL₁ φ μ01 ν10 βS βT βL p q u v c d hctx h143
    rcases hsrc with
      ⟨hcase, _hSTypeP, _hTTypeP, _hp, _hq, _hC, _hD, _hc, _hd,
        _hUcard, _hVcard, _hSfam, _hTfam, _hDadeS, _hDadeT, _hNotation,
        _hDadeDiff, _hZeroDegree, _hConjIndex, _hConjBetaTau,
        _hChoice, _hMin, _hFourSixS, _hFourSixT⟩
    rcases hcase with
      ⟨_hprod, _hcyc, _hW1ne, _hW2ne, _hnorm, _hSmax, hTmax, _hSMF,
        hTMF, _hSeq, _hTeq, _hSdisj, _hTdisj, _hST, _hTypeII, _hSType,
        _hTType, _hCover⟩
    exact Section8.theorem_8_8_typeII_to_source_public hTmax hTMF htypeT16
  rcases h1410 with
    ⟨hMmax, _hModd, hNormVleM, hKMF, _hTypeI, _hDadeM, _hPunctM, _h52M, _hCoherM,
      _hψmem, _hψirr, _hψdeg, _hβM⟩
  rcases Section13.theorem_13_17 Tmax Smax W W2 W1 Q P V U D C M K
      Tfam Sfam τT τS q p v u d c
      (section14_hypothesis_13_1_sourceData_swap hsrc)
      htypeT hMmax hNormVleM hKMF with
    ⟨hfrobMK, _hVK, hcomp⟩
  have hp_card : p = Nat.card W2 := by
    rcases hsrc with
      ⟨_hcase, _hSTypeP, _hTTypeP, hp_card, _hq_card, _hC, _hD,
        _hc, _hd, _hUcard, _hVcard, _hSfam, _hTfam, _hDadeS,
        _hDadeT, _hNotation, _hDadeDiff, _hZeroDegree, _hConjIndex, _hConjBetaTau,
        _hChoice, _hMin, _hFourSixS, _hFourSixT⟩
    exact hp_card
  have hq_card : q = Nat.card W1 := by
    rcases hsrc with
      ⟨_hcase, _hSTypeP, _hTTypeP, _hp_card, hq_card, _hC, _hD,
        _hc, _hd, _hUcard, _hVcard, _hSfam, _hTfam, _hDadeS,
        _hDadeT, _hNotation, _hDadeDiff, _hZeroDegree, _hConjIndex, _hConjBetaTau,
        _hChoice, _hMin, _hFourSixS, _hFourSixT⟩
    exact hq_card
  have hprod : section12InternalDirectProduct W1 W2 W := by
    rcases hsrc with
      ⟨hcase, _hSTypeP, _hTTypeP, _hp_card, _hq_card, _hC, _hD,
        _hc, _hd, _hUcard, _hVcard, _hSfam, _hTfam, _hDadeS,
        _hDadeT, _hNotation, _hDadeDiff, _hZeroDegree, _hConjIndex, _hConjBetaTau,
        _hChoice, _hMin, _hFourSixS, _hFourSixT⟩
    exact hcase.1
  have hcentW2 :
      subgroupCentralizerIn (⊤ : Subgroup G) W2 = P ⊔ W1 := by
    exact (Section13.theorem_13_16 Tmax Smax W W2 W1 Q P V U D C
      Tfam Sfam τT τS q p v u d c
      (section14_hypothesis_13_1_sourceData_swap hsrc)).2
  rcases hcomp with hcompW2 | hcompSup
  · exact False.elim
      (section14_theorem_14_11_index_small_complement_contradiction_source_bridge
        Smax Tmax W W1 W2 P Q U C D L H Sfam Tfam τS τT
        Lfam RL τL τL₁ φ μ01 ν10 βS βT βL
        M K V Mfam τM τM₁ ψ βM p q u v c d hctx h143
        ⟨hMmax, _hModd, hNormVleM, hKMF, _hTypeI, _hDadeM, _hPunctM, _h52M,
          _hCoherM, _hψmem, _hψirr, _hψdeg, _hβM⟩ hKV hcompW2)
  · rcases hcompSup with ⟨y, hyP, hcompSup⟩
    have hsemi :
        Section2.IsInternalSemidirectProduct M K (W2 ⊔ W1.conjBy y) :=
      section14_semidirectProduct_of_frobenius_complement hfrobMK hcompSup
    have hycent : y ∈ Subgroup.centralizer (W2 : Set G) := by
      have hySup : y ∈ P ⊔ W1 := (show P ≤ P ⊔ W1 from le_sup_left) hyP
      have hyCentIn : y ∈ subgroupCentralizerIn (⊤ : Subgroup G) W2 := by
        simpa [hcentW2] using hySup
      exact hyCentIn.2
    have hcardSup :
        Nat.card (W2 ⊔ W1.conjBy y : Subgroup G) = p * q := by
      calc
        Nat.card (W2 ⊔ W1.conjBy y : Subgroup G) =
            Nat.card W2 * Nat.card W1 :=
          section14_card_sup_conjBy_eq_mul_of_directProduct_of_mem_centralizer
            (section14_section12InternalDirectProduct_swap hprod) hycent
        _ = p * q := by rw [← hp_card, ← hq_card]
    have hrel :
        K.relIndex M = Nat.card (W2 ⊔ W1.conjBy y : Subgroup G) :=
      Section2.internalSemidirectProduct_left_relIndex_eq_card_right hsemi
    exact hrel.trans hcardSup

public theorem section14_theorem_14_11_4_inequalityData_source_bridge
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (Smax Tmax W W1 W2 P Q U C D L H : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (Lfam : Finset (Section1.ClassFunction L))
    (RL : G → Subgroup G)
    (τL τL₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (φ : Section1.ClassFunction L)
    (μ01 : Section1.ClassFunction Smax)
    (ν10 : Section1.ClassFunction Tmax)
    (βS : Section1.ClassFunction Smax)
    (βT : Section1.ClassFunction Tmax)
    (βL : Section1.ClassFunction L)
    (M K V : Subgroup G)
    (Mfam : Finset (Section1.ClassFunction M))
    (τM τM₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G)
    (ψ βM : Section1.ClassFunction M)
    (tildeAM : Set G)
    (ψτ : Section1.ClassFunction G)
    (p q u v c d : ℕ) :
    hypothesis_14_context_data Smax Tmax W W1 W2 P Q U V C D
        Sfam Tfam τS τT p q u v c d →
      hypothesis_14_3_data Smax Tmax L H P Q U W1 W2 Lfam RL τL τL₁ φ μ01 ν10 βS βT βL →
        hypothesis_14_10_data M K V Mfam τM τM₁ ψ βM →
          Section10.section10TildeAData M K tildeAM →
            K ≠ V →
              ψτ = τM₁ ψ →
                theorem_14_11_3_data (theorem_14_11_3_G0 tildeAM W P Q) ψτ →
                  ∃ psiRhoNormSq : ℝ,
                    theorem_14_11_4_inequalityData M K W W1 W2 P Q
                      (theorem_14_11_3_G0 tildeAM W P Q) ψτ
                        psiRhoNormSq p q u v := by
  intro hctx h143 h1410 htilde hKV hψτ h113
  rcases section14_theorem_14_11_4_pf75_raw_source_bridge
      (M := M) (K := K) (V := V) (Mfam := Mfam)
      (τM := τM) (τM₁ := τM₁) (ψ := ψ) (βM := βM)
      (tildeAM := tildeAM) (ψτ := ψτ) h1410 htilde hψτ with
    ⟨R, hDadeR, hsupp, h75raw⟩
  let psiRhoNormSq : ℝ :=
    Section7.weightedProjectionEnergy (Section12.typeIASet M K) M R ψτ
  refine ⟨psiRhoNormSq, ?_⟩
  have hupper :=
    section14_theorem_14_11_4_upper_inequalities_source_bridge
      Smax Tmax W W1 W2 P Q U C D L H Sfam Tfam τS τT
      Lfam RL τL τL₁ φ μ01 ν10 βS βT βL
      M K V Mfam τM τM₁ ψ βM tildeAM R ψτ p q u v c d
      hctx h143 h1410 htilde hKV hψτ h113 hsupp h75raw
  have hlower :
      1 - ((p * q : ℕ) : ℝ) / (Nat.card K : ℝ) ≤ psiRhoNormSq := by
    dsimp [psiRhoNormSq]
    exact section14_theorem_14_11_4_lower_bound_source_bridge
      Smax Tmax W W1 W2 P Q U C D L H Sfam Tfam τS τT
      Lfam RL τL τL₁ φ μ01 ν10 βS βT βL
      M K V Mfam τM τM₁ ψ βM R ψτ p q u v c d
      hctx h143 h1410 hDadeR hKV hψτ
  dsimp [psiRhoNormSq] at hupper
  dsimp [theorem_14_11_4_inequalityData]
  exact ⟨hupper.1, hlower, hupper.2⟩

public theorem section14_theorem_14_11_source_inputs_bridge
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (Smax Tmax W W1 W2 P Q U C D L H : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (Lfam : Finset (Section1.ClassFunction L))
    (RL : G → Subgroup G)
    (τL τL₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (φ : Section1.ClassFunction L)
    (μ01 : Section1.ClassFunction Smax)
    (ν10 : Section1.ClassFunction Tmax)
    (βS : Section1.ClassFunction Smax)
    (βT : Section1.ClassFunction Tmax)
    (βL : Section1.ClassFunction L)
    (M K V : Subgroup G)
    (Mfam : Finset (Section1.ClassFunction M))
    (τM τM₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G)
    (ψ βM : Section1.ClassFunction M)
    (p q u v c d : ℕ) :
    hypothesis_14_context_data Smax Tmax W W1 W2 P Q U V C D
        Sfam Tfam τS τT p q u v c d →
      hypothesis_14_3_data Smax Tmax L H P Q U W1 W2 Lfam RL τL τL₁ φ μ01 ν10 βS βT βL →
        hypothesis_14_10_data M K V Mfam τM τM₁ ψ βM →
          (K = V → K.relIndex M = p * q) ∧
            (K ≠ V → False) := by
  intro hctx h143 h1410
  refine ⟨?_, ?_⟩
  · intro hKV
    exact section14_theorem_14_11_index_of_eq_source_bridge
      Smax Tmax W W1 W2 P Q U C D L H Sfam Tfam τS τT
      Lfam RL τL τL₁ φ μ01 ν10 βS βT βL
      M K V Mfam τM τM₁ ψ βM p q u v c d hctx h143 h1410 hKV
  · intro hKV
    rcases section14_theorem_14_11_tildeAData_source_bridge
        Smax Tmax W W1 W2 P Q U C D Sfam Tfam τS τT
        M K V Mfam τM τM₁ ψ βM p q u v c d hctx h1410 with
      ⟨tildeAM, htilde⟩
    let ψτ : Section1.ClassFunction G := τM₁ ψ
    have hψτ : ψτ = τM₁ ψ := rfl
    have h113 :
        theorem_14_11_3_data (theorem_14_11_3_G0 tildeAM W P Q) ψτ :=
      section14_theorem_14_11_3_source_bridge
        Smax Tmax W W1 W2 P Q U C D L H Sfam Tfam τS τT
        Lfam RL τL τL₁ φ μ01 ν10 βS βT βL
        M K V Mfam τM τM₁ ψ βM tildeAM ψτ p q u v c d
        hctx h143 h1410 htilde hKV hψτ
    rcases section14_theorem_14_11_4_inequalityData_source_bridge
        Smax Tmax W W1 W2 P Q U C D L H Sfam Tfam τS τT
        Lfam RL τL τL₁ φ μ01 ν10 βS βT βL
        M K V Mfam τM τM₁ ψ βM tildeAM ψτ p q u v c d
        hctx h143 h1410 htilde hKV hψτ h113 with
      ⟨psiRhoNormSq, hineq⟩
    exact section14_theorem_14_11_4_contradiction_bridge
      Smax Tmax W W1 W2 P Q U C D L H Sfam Tfam τS τT
      Lfam RL τL τL₁ φ μ01 ν10 βS βT βL
      M K V Mfam τM τM₁ ψ βM tildeAM ψτ psiRhoNormSq p q u v c d
      hctx h143 h1410 htilde hKV hψτ hineq

public theorem section14_theorem_14_11_source_bridge
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (Smax Tmax W W1 W2 P Q U C D L H : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (Lfam : Finset (Section1.ClassFunction L))
    (RL : G → Subgroup G)
    (τL τL₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (φ : Section1.ClassFunction L)
    (μ01 : Section1.ClassFunction Smax)
    (ν10 : Section1.ClassFunction Tmax)
    (βS : Section1.ClassFunction Smax)
    (βT : Section1.ClassFunction Tmax)
    (βL : Section1.ClassFunction L)
    (M K V : Subgroup G)
    (Mfam : Finset (Section1.ClassFunction M))
    (τM τM₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G)
    (ψ : Section1.ClassFunction M)
    (βM : Section1.ClassFunction M)
    (p q u v c d : ℕ) :
    hypothesis_14_context_data Smax Tmax W W1 W2 P Q U V C D
        Sfam Tfam τS τT p q u v c d →
      hypothesis_14_3_data Smax Tmax L H P Q U W1 W2 Lfam RL τL τL₁ φ μ01 ν10 βS βT βL →
        hypothesis_14_10_data M K V Mfam τM τM₁ ψ βM →
          K = V ∧ K.relIndex M = p * q := by
  intro hctx h143 h1410
  rcases section14_theorem_14_11_source_inputs_bridge
      Smax Tmax W W1 W2 P Q U C D L H Sfam Tfam τS τT
      Lfam RL τL τL₁ φ μ01 ν10 βS βT βL
      M K V Mfam τM τM₁ ψ βM p q u v c d hctx h143 h1410 with
    ⟨hindex_of_eq, hcontra⟩
  by_cases hKV : K = V
  · exact ⟨hKV, hindex_of_eq hKV⟩
  · exact False.elim (hcontra hKV)


end CFSG.Section14
