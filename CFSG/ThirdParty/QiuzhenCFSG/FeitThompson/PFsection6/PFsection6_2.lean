module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection6.PFsection6_1
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection1.PFsection1_8
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection5.PFsection5_6
import CFSG.ThirdParty.QiuzhenCFSG.Theory.Character.DegreeBounds

namespace CFSG
end CFSG
open CFSG

noncomputable section
open scoped Classical
open scoped commutatorElement

attribute [local instance] Fintype.ofFinite

namespace CFSG.Section6

universe v
universe u
open Section1 Section2 Section3 Section4

@[expose] public def theorem_6_2_statement
    {L : Type u} [Group L] [Finite L]
    {G : Type u} [Group G] [Finite G]
    (K A B C D : Subgroup L)
    (S : Finset (Section1.ClassFunction L))
    (SA SB : Finset (Section1.ClassFunction L))
    (T : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G) : Prop :=
  hypothesis_6_1_statement K S T →
    inducedKernelFamily K A SA →
        inducedKernelFamily K B SB →
        A.Normal →
        A < K →
          centralQuotientHypothesis K B C D →
            coherentFamily SA T →
              SB.Nonempty →
                ¬ coherentFamily SB T →
                  (2 : ℝ) * (C.relIndex (⊤ : Subgroup L) : ℝ) *
                    Real.sqrt (D.relIndex C : ℝ) ≥
                    (A.relIndex K : ℝ) - 1

/-- Peterfalvi `(6.3)`. -/


public theorem theorem_6_2_arithmetic_core
    {L : Type u} [Group L] [Finite L]
    (K A C D : Subgroup L)
    {ψBound : ℝ}
    (hlower : (A.relIndex K : ℝ) - 1 ≤ (2 : ℝ) * ψBound)
    (hupper : ψBound ≤ (C.relIndex (⊤ : Subgroup L) : ℝ) *
      Real.sqrt (D.relIndex C : ℝ)) :
    (2 : ℝ) * (C.relIndex (⊤ : Subgroup L) : ℝ) *
        Real.sqrt (D.relIndex C : ℝ) ≥
      (A.relIndex K : ℝ) - 1 := by
  nlinarith

public theorem theorem_6_2_pf56_numeric_obstruction
    {L : Type u} [Group L] [Finite L]
    {G : Type u} [Group G] [Finite G]
    {S S1 : Finset (Section1.ClassFunction L)}
    {T : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    (h52 : Section5.hypothesis_5_2_statement S T)
    (hS1sub : S1 ⊆ S)
    (hS1closed : ∀ χ : Section1.ClassFunction L, χ ∈ S1 →
      Section1.conjugateCharacter χ ∈ S1)
    (X : S)
    (hXbarNotin : Section1.conjugateCharacter (X : Section1.ClassFunction L) ∉ S1)
    (X1 : S1)
    (hcoh : coherentFamily S1 T)
    (hnotPair : ¬ coherentFamily
      (S1 ∪ ({(X : Section1.ClassFunction L),
        Section1.conjugateCharacter (X : Section1.ClassFunction L)} :
          Finset (Section1.ClassFunction L))) T)
    {d1 dX : ℕ}
    (hd1 : Section1.degree (X1 : Section1.ClassFunction L) = (d1 : ℂ))
    (hdX : Section1.degree (X : Section1.ClassFunction L) = (dX : ℂ))
    (hdvd : d1 ∣ dX)
    (dS1 : S1 → ℕ)
    (hdS1 : ∀ Y : S1,
      Section1.degree (Y : Section1.ClassFunction L) = (dS1 Y : ℂ)) :
    (∑ Y : S1,
      (((dS1 Y : ℝ) ^ (2 : ℕ)) /
        Section5.cfNormSq (Y : Section1.ClassFunction L))) ≤
      2 * (dX : ℝ) * (d1 : ℝ) := by
  classical
  rcases h52 with ⟨hsetup, R, h52a, h52b, h52c, h52d, h52e⟩
  have hnot_lt : ¬ 2 * (dX : ℝ) * (d1 : ℝ) <
      ∑ Y : S1,
        (((dS1 Y : ℝ) ^ (2 : ℕ)) /
          Section5.cfNormSq (Y : Section1.ClassFunction L)) := by
    intro hlt
    apply hnotPair
    have hnew := Section5.theorem_5_6 S T R hsetup h52a h52b h52c h52d h52e
      S1 hS1sub hS1closed X hXbarNotin X1 (by simpa [coherentFamily] using hcoh)
      ⟨d1, dX, hd1, hdX, hdvd, dS1, hdS1, hlt⟩
    change Section5.definition_5_1_statement Section5.puncturedSet
      (S1 ∪ ({(X : Section1.ClassFunction L),
        Section1.conjugateCharacter (X : Section1.ClassFunction L)} :
          Finset (Section1.ClassFunction L))) T
    exact hnew
  exact not_lt.mp hnot_lt

public theorem theorem_6_2_obstruction_data
    {L : Type u} [Group L] [Finite L]
    {G : Type u} [Group G] [Finite G]
    {K A B C D : Subgroup L}
    {S SA SB : Finset (Section1.ClassFunction L)}
    {T : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    (h61 : hypothesis_6_1_statement K S T)
    (hSA : inducedKernelFamily K A SA)
    (hSB : inducedKernelFamily K B SB)
    (hAnorm : A.Normal)
    (hAltK : A < K)
    (_hcent : centralQuotientHypothesis K B C D)
    (hcohSA : coherentFamily SA T)
    (hSBne : SB.Nonempty)
    (hnotSB : ¬ coherentFamily SB T) :
    ∃ S1 ψ χA,
      SA ⊆ S1 ∧ S1 ⊆ SA ∪ SB ∧
        (∀ η, η ∈ S1 → Section1.conjugateCharacter η ∈ S1) ∧
          coherentFamily S1 T ∧
            ψ ∈ SB ∧ ψ ∉ S1 ∧
              ¬ coherentFamily (S1 ∪ ({ψ, Section1.conjugateCharacter ψ} :
                Finset (Section1.ClassFunction L))) T ∧
              χA ∈ S1 ∧
                Section1.degree χA = (K.relIndex (⊤ : Subgroup L) : ℂ) := by
  classical
  haveI : K.Normal := h61.2.1
  rcases hypothesis_6_1_hypothesis_5_2 h61 with ⟨hsetup, _R, h52a, _h52b,
    _h52c, _h52d, _h52e⟩
  have hSBsub : SB ⊆ S :=
    inducedKernelFamily_subset_base
      (hypothesis_6_1_inducedKernelFamily_bot h61) hSB
  rcases hSBne with ⟨χB, hχB⟩
  rcases inducedKernelFamily_closed_obstruction_of_mem
      hsetup h52a hSBsub hSA hSB hcohSA hnotSB hχB with
    ⟨S1, ψ, hSA_S1, hS1_sub, hS1_closed, hS1_coh, hψSB, hψS1, hnotPair⟩
  rcases inducedKernelFamily_exists_degree_relIndex_of_lt
      h61.2.2.1 hAnorm hAltK hSA with
    ⟨χA, hχA_SA, hχAdeg⟩
  exact ⟨S1, ψ, χA, hSA_S1, hS1_sub, hS1_closed, hS1_coh, hψSB,
    hψS1, hnotPair, hSA_S1 hχA_SA, hχAdeg⟩

public theorem theorem_6_2_pf18_card_bound_eq_relIndex
    {L : Type u} [Group L] [Finite L]
    {K C D : Subgroup L}
    (hDC : D ≤ C) (hCK : C ≤ K) :
    (Nat.card K : ℝ) / Real.sqrt ((Nat.card (C.subgroupOf K) : ℝ) *
        Nat.card (D.subgroupOf K)) =
      (C.relIndex K : ℝ) * Real.sqrt (D.relIndex C : ℝ) := by
  have hCcard : Nat.card (C.subgroupOf K) = Nat.card C := by
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCK).toEquiv
  have hCcardF : Fintype.card (C.subgroupOf K) = Fintype.card C := by
    simpa [Nat.card_eq_fintype_card] using hCcard
  have hDcardK : Nat.card (D.subgroupOf K) = Nat.card D := by
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hDC.trans hCK)).toEquiv
  have hDcardKF : Fintype.card (D.subgroupOf K) = Fintype.card D := by
    simpa [Nat.card_eq_fintype_card] using hDcardK
  have hCindex : (C.relIndex K : ℝ) * Nat.card C = Nat.card K := by
    have h := Subgroup.index_mul_card (C.subgroupOf K)
    have hrel : (C.subgroupOf K).index = C.relIndex K := by
      simp [Subgroup.relIndex]
    exact_mod_cast (by simpa [hCcardF, hrel] using h)
  have hDindex : (D.relIndex C : ℝ) * Nat.card D = Nat.card C := by
    have h := Subgroup.index_mul_card (D.subgroupOf C)
    have hDcardC : Nat.card (D.subgroupOf C) = Nat.card D := by
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDC).toEquiv
    have hDcardCF : Fintype.card (D.subgroupOf C) = Fintype.card D := by
      simpa [Nat.card_eq_fintype_card] using hDcardC
    have hrel : (D.subgroupOf C).index = D.relIndex C := by
      simp [Subgroup.relIndex]
    exact_mod_cast (by simpa [hDcardCF, hrel] using h)
  have hCpos : (0 : ℝ) < Nat.card C := by
    exact_mod_cast (Nat.card_pos (α := C))
  have hDpos : (0 : ℝ) < Nat.card D := by
    exact_mod_cast (Nat.card_pos (α := D))
  have hrelD_nonneg : 0 ≤ (D.relIndex C : ℝ) := by positivity
  have hsqrt_sq : Real.sqrt (D.relIndex C : ℝ) ^ 2 = (D.relIndex C : ℝ) := by
    rw [sq, Real.mul_self_sqrt hrelD_nonneg]
  have hden_pos :
      0 < Real.sqrt ((Nat.card (C.subgroupOf K) : ℝ) *
        Nat.card (D.subgroupOf K)) := by
    apply Real.sqrt_pos.2
    rw [hCcard, hDcardK]
    exact mul_pos hCpos hDpos
  have hsquares :
      ((Nat.card K : ℝ) / Real.sqrt ((Nat.card (C.subgroupOf K) : ℝ) *
          Nat.card (D.subgroupOf K))) ^ 2 =
        ((C.relIndex K : ℝ) * Real.sqrt (D.relIndex C : ℝ)) ^ 2 := by
    field_simp [hden_pos.ne']
    rw [sq, Real.sq_sqrt (by rw [hCcard, hDcardK]; positivity), hCcard, hDcardK,
      hsqrt_sq]
    calc
      (Nat.card K : ℝ) * (Nat.card K : ℝ) =
          ((C.relIndex K : ℝ) * Nat.card C) *
            ((C.relIndex K : ℝ) * Nat.card C) := by
        rw [hCindex]
      _ = (Nat.card C : ℝ) * Nat.card D * (C.relIndex K : ℝ) ^ 2 *
          (D.relIndex C : ℝ) := by
        rw [← hDindex]
        ring
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsquares with h | h
  · exact h
  · have hleft_pos :
        0 < (Nat.card K : ℝ) / Real.sqrt ((Nat.card (C.subgroupOf K) : ℝ) *
          Nat.card (D.subgroupOf K)) := by
      exact div_pos (by exact_mod_cast (Nat.card_pos (α := K))) hden_pos
    have hright_nonneg :
        0 ≤ (C.relIndex K : ℝ) * Real.sqrt (D.relIndex C : ℝ) := by
      positivity
    nlinarith

private theorem theorem_6_2_centralModulo_of_centralQuotient
    {L : Type u} [Group L] [Finite L]
    {K B C D : Subgroup L}
    (hcent : centralQuotientHypothesis K B C D) :
    Theory.Character.IsCentralModulo
      ((B.subgroupOf K).subgroupOf (C.subgroupOf K))
      ((D.subgroupOf K).subgroupOf (C.subgroupOf K)) := by
  intro d hd c
  change (((⁅(d : C.subgroupOf K), (c : C.subgroupOf K)⁆ : C.subgroupOf K) :
    K) : L) ∈ B
  have hdD : (((d : C.subgroupOf K) : K) : L) ∈ D := by
    exact hd
  have hcC : (((c : C.subgroupOf K) : K) : L) ∈ C := by
    exact c.2
  have hcomm :
      ⁅(((d : C.subgroupOf K) : K) : L), (((c : C.subgroupOf K) : K) : L)⁆ ∈
        ⁅D, C⁆ :=
    Subgroup.commutator_mem_commutator hdD hcC
  exact centralQuotient_commutator_le hcent hcomm

public theorem theorem_6_2_pf18_degree_upper
    {L : Type u} [Group L] [Finite L]
    {K B C D : Subgroup L} {SB : Finset (Section1.ClassFunction L)}
    (hcent : centralQuotientHypothesis K B C D)
    (hSB : inducedKernelFamily K B SB)
    {ψ : Section1.ClassFunction L} (hψ : ψ ∈ SB) :
    ∃ dψ : ℕ,
      Section1.degree ψ = (dψ : ℂ) ∧
        K.relIndex (⊤ : Subgroup L) ∣ dψ ∧
          (dψ : ℝ) ≤ (C.relIndex (⊤ : Subgroup L) : ℝ) *
            Real.sqrt (D.relIndex C : ℝ) := by
  classical
  rcases (hSB.2 ψ).mp hψ with ⟨θ, hθirr, hθker, _hθne, hψeq⟩
  rcases hθirr with ⟨n, ρ, hρirr, hθeq⟩
  let dψ : ℕ := K.relIndex (⊤ : Subgroup L) * n
  have hψdeg : Section1.degree ψ = (dψ : ℂ) := by
    rw [hψeq, Section1.degree_inducedClassFunction K θ]
    rw [hθeq, Section1.degree_representation_character]
    simp [dψ, Subgroup.relIndex_top_right, Nat.cast_mul]
  have hdvd : K.relIndex (⊤ : Subgroup L) ∣ dψ := by
    exact dvd_mul_right _ _
  haveI : Representation.IsIrreducible ρ := hρirr
  have hθkerρ : Section1.subgroupInKernel' ρ.character (B.subgroupOf K) := by
    simpa [hθeq] using hθker
  have hBker : Section1.subgroupInRepresentationKernel ρ (B.subgroupOf K) :=
    (Section1.subgroupInKernel'_character_iff_subgroupInRepresentationKernel ρ
      (B.subgroupOf K)).mp hθkerρ
  have hBD : B.subgroupOf K ≤ D.subgroupOf K := by
    intro b hb
    exact centralQuotient_B_le_D hcent hb
  have hDC_K : D.subgroupOf K ≤ C.subgroupOf K := by
    intro d hd
    exact centralQuotient_D_lt_C hcent hd
  haveI : (B.subgroupOf K).Normal := (centralQuotient_B_normal hcent).subgroupOf K
  have hBnormal : ((B.subgroupOf K).subgroupOf (C.subgroupOf K)).Normal := by
    infer_instance
  have hn_bound_raw :
      (n : ℝ) ≤ (Nat.card K : ℝ) /
        Real.sqrt ((Nat.card (C.subgroupOf K) : ℝ) * Nat.card (D.subgroupOf K)) := by
    have h := Section1.proposition_1_8 (ρ := ρ)
      (B.subgroupOf K) (C.subgroupOf K) (D.subgroupOf K)
      hBker hBD hDC_K hBnormal (theorem_6_2_centralModulo_of_centralQuotient hcent)
    simpa using h
  have hCK : C ≤ K := centralQuotient_C_le_K hcent
  have hDC : D ≤ C := centralQuotient_D_lt_C hcent
  have hn_bound : (n : ℝ) ≤ (C.relIndex K : ℝ) *
      Real.sqrt (D.relIndex C : ℝ) := by
    rwa [theorem_6_2_pf18_card_bound_eq_relIndex hDC hCK] at hn_bound_raw
  have hmul_bound : (dψ : ℝ) ≤
      (K.relIndex (⊤ : Subgroup L) : ℝ) *
        ((C.relIndex K : ℝ) * Real.sqrt (D.relIndex C : ℝ)) := by
    change ((K.relIndex (⊤ : Subgroup L) * n : ℕ) : ℝ) ≤
      (K.relIndex (⊤ : Subgroup L) : ℝ) *
        ((C.relIndex K : ℝ) * Real.sqrt (D.relIndex C : ℝ))
    rw [Nat.cast_mul]
    exact mul_le_mul_of_nonneg_left hn_bound (by positivity)
  have hrel_mul : K.relIndex (⊤ : Subgroup L) * C.relIndex K =
      C.relIndex (⊤ : Subgroup L) := by
    rw [mul_comm]
    exact Subgroup.relIndex_mul_relIndex C K ⊤ hCK le_top
  refine ⟨dψ, hψdeg, hdvd, ?_⟩
  have hrel_mul_real :
      (K.relIndex (⊤ : Subgroup L) : ℝ) * (C.relIndex K : ℝ) =
        (C.relIndex (⊤ : Subgroup L) : ℝ) := by
    exact_mod_cast hrel_mul
  calc
    (dψ : ℝ) ≤ (K.relIndex (⊤ : Subgroup L) : ℝ) *
        ((C.relIndex K : ℝ) * Real.sqrt (D.relIndex C : ℝ)) := hmul_bound
    _ = (C.relIndex (⊤ : Subgroup L) : ℝ) * Real.sqrt (D.relIndex C : ℝ) := by
      rw [← hrel_mul_real]
      ring

private theorem theorem_6_2_principalClassFunction_irreducible
    {Q : Type u} [Group Q] [Finite Q] :
    Theory.Character.IsIrreducibleConjCharacter (fun _ : ConjClasses Q => (1 : ℂ)) := by
  classical
  let := Fintype.ofFinite Q
  constructor
  · refine ⟨1, Representation.trivial ℂ Q (Fin 1 → ℂ), ?_⟩
    ext c
    rcases ConjClasses.exists_rep c with ⟨q, rfl⟩
    change (1 : ℂ) = (Representation.trivial ℂ Q (Fin 1 → ℂ)).character q
    simp [Representation.character, Representation.trivial]
  · unfold Theory.Character.classFunctionInner
    rw [Nat.card_eq_fintype_card]
    have hcard : (Fintype.card Q : ℂ) ≠ 0 := by
      exact_mod_cast Fintype.card_ne_zero
    simp [hcard]

private noncomputable def theorem_6_2_subrepresentationCompOrderIso
    {G H k V : Type*} [Monoid G] [Monoid H] [Field k]
    [AddCommGroup V] [Module k V]
    (ρ : Representation k H V) (φ : G →* H) (hφ : Function.Surjective φ) :
    Subrepresentation (ρ.comp φ) ≃o Subrepresentation ρ where
  toFun σ :=
    { toSubmodule := σ.toSubmodule
      apply_mem_toSubmodule := by
        intro h v hv
        rcases hφ h with ⟨g, rfl⟩
        exact σ.apply_mem_toSubmodule g hv }
  invFun τ :=
    { toSubmodule := τ.toSubmodule
      apply_mem_toSubmodule := by
        intro g v hv
        exact τ.apply_mem_toSubmodule (φ g) hv }
  left_inv σ := by
    apply Subrepresentation.toSubmodule_injective
    rfl
  right_inv τ := by
    apply Subrepresentation.toSubmodule_injective
    rfl
  map_rel_iff' := by
    intro σ τ
    rfl

private theorem theorem_6_2_isIrreducible_comp_surjective
    {G H k V : Type*} [Monoid G] [Monoid H] [Field k]
    [AddCommGroup V] [Module k V]
    (ρ : Representation k H V) (φ : G →* H) (hφ : Function.Surjective φ)
    (hρ : Representation.IsIrreducible ρ) :
    Representation.IsIrreducible (ρ.comp φ) := by
  haveI : Representation.IsIrreducible ρ := hρ
  exact OrderIso.isSimpleOrder
    (theorem_6_2_subrepresentationCompOrderIso ρ φ hφ)

private theorem theorem_6_2_quotient_irreducible_degree_data
    (Q : Type u) [Group Q] [Finite Q] :
    ∃ (ι : Type) (_ : Fintype ι) (_ : DecidableEq ι)
      (χ : ι → Theory.Character.ConjClassFunction Q),
      Theory.Character.IsCompleteIrreducibleCharacterFamily χ ∧
        ∃ (d : ι → ℕ) (i0 : ι),
          (∀ i : ι, χ i (ConjClasses.mk (1 : Q)) = (d i : ℂ)) ∧
            χ i0 = (fun _ : ConjClasses Q => (1 : ℂ)) ∧
              d i0 = 1 ∧
                (∑ i : ι, (d i : ℝ) ^ (2 : ℕ)) = (Nat.card Q : ℝ) ∧
                  (Finset.univ.erase i0).sum (fun i => (d i : ℝ) ^ (2 : ℕ)) =
                    (Nat.card Q : ℝ) - 1 := by
  classical
  rcases Theory.Character.second_orthogonality (G := Q) with
    ⟨ι, hι, χ, hχ, horth⟩
  letI : Fintype ι := hι
  letI : DecidableEq ι := Classical.decEq ι
  let d : ι → ℕ := fun i => Classical.choose (hχ.1 i).1
  have hd_eval : ∀ i : ι, χ i (ConjClasses.mk (1 : Q)) = (d i : ℂ) := by
    intro i
    rcases Classical.choose_spec (hχ.1 i).1 with ⟨ρ, hρ⟩
    rw [hρ]
    change ρ.character (1 : Q) = (d i : ℂ)
    simp [d, Representation.character]
  rcases hχ.2.1 (fun _ : ConjClasses Q => (1 : ℂ))
      (theorem_6_2_principalClassFunction_irreducible (Q := Q)) with
    ⟨i0, hi0⟩
  have hdi0 : d i0 = 1 := by
    have hcomplex : (d i0 : ℂ) = 1 := by
      simpa [hi0] using (hd_eval i0).symm
    exact_mod_cast hcomplex
  have hsum_complex :
      ∑ i : ι, (d i : ℂ) * star (d i : ℂ) = (Nat.card Q : ℂ) := by
    have h := (horth (1 : Q) (1 : Q)).1 rfl
    simpa [hd_eval] using h
  have hsum_real :
      (∑ i : ι, (d i : ℝ) ^ (2 : ℕ)) = (Nat.card Q : ℝ) := by
    have hreal := congrArg Complex.re hsum_complex
    simpa [pow_two] using hreal
  have herase :
      (Finset.univ.erase i0).sum (fun i => (d i : ℝ) ^ (2 : ℕ)) =
        (Nat.card Q : ℝ) - 1 := by
    have hsplit := Finset.sum_erase_add (s := (Finset.univ : Finset ι))
      (f := fun i => (d i : ℝ) ^ (2 : ℕ)) (a := i0) (by simp)
    have hdi0real : (d i0 : ℝ) ^ (2 : ℕ) = 1 := by
      rw [hdi0]
      norm_num
    nlinarith [hsum_real, hsplit, hdi0real]
  exact ⟨ι, hι, Classical.decEq ι, χ, hχ, d, i0, hd_eval, hi0, hdi0,
    hsum_real, herase⟩

public theorem theorem_6_2_pf15_orbit_contribution
    {L : Type u} [Group L] [Finite L]
    {K : Subgroup L} [K.Normal]
    {θ : Section1.ClassFunction K}
    (hθirr : Section1.IsIrreducibleCharacterOnGroup θ) :
    ∃ dθ dχ : ℕ,
      Section1.degree θ = (dθ : ℂ) ∧
        Section1.degree (Section1.inducedCF K θ) = (dχ : ℂ) ∧
          ((dχ : ℝ) ^ (2 : ℕ) /
              Section5.cfNormSq (Section1.inducedCF K θ)) =
            (K.relIndex (⊤ : Subgroup L) : ℝ) *
              ∑ _ : Section1.conjugateOrbitIndex K θ, (dθ : ℝ) ^ (2 : ℕ) := by
  classical
  rcases hθirr with ⟨n, ρ, hρirr, hθeq⟩
  refine ⟨n, K.relIndex (⊤ : Subgroup L) * n, ?_, ?_, ?_⟩
  · rw [hθeq, Section1.degree_representation_character]
    simp
  · rw [hθeq, Section1.degree_inducedClassFunction, Section1.degree_representation_character]
    simp [Subgroup.relIndex_top_right, Nat.cast_mul]
  · letI orbitFintype : Fintype (Section1.conjugateOrbitIndex K ρ.character) :=
      Fintype.ofFinite _
    have hd :=
      Section1.proposition_1_5_d_rep_orbit_relIndex_canonical K ρ hρirr
    have heval := congrFun hd (1 : K)
    have hcomplex :
        (Section1.degree (Section1.inducedCF K ρ.character) /
            Section1.scalarProduct L (Section1.inducedCF K ρ.character)
              (Section1.inducedCF K ρ.character)) *
            Section1.degree (Section1.inducedCF K ρ.character) =
          (Subgroup.index K : ℂ) *
            ∑ i : Section1.conjugateOrbitIndex K ρ.character,
              Section1.degree (Section1.conjugateOrbitConj K ρ.character i) *
                Section1.degree (Section1.conjugateOrbitConj K ρ.character i) := by
      simpa [Section1.degree, Section1.subgroupRestriction] using heval
    have hsp : Section1.scalarProduct L
          (Section1.inducedCF K ρ.character)
          (Section1.inducedCF K ρ.character) =
          (K.relIndex (Section1.inertiaSubgroup K ρ.character) : ℂ) := by
        exact Section1.proposition_1_5_b_rep_orbit_relIndex_canonical K ρ hρirr
    have hcomplex' :
        ((((K.relIndex (⊤ : Subgroup L) * n : ℕ) : ℂ) ^ (2 : ℕ)) /
            (K.relIndex (Section1.inertiaSubgroup K ρ.character) : ℂ)) =
          (K.relIndex (⊤ : Subgroup L) : ℂ) *
            ∑ i : Section1.conjugateOrbitIndex K ρ.character,
              ((n : ℂ) ^ (2 : ℕ)) := by
      calc
        ((((K.relIndex (⊤ : Subgroup L) * n : ℕ) : ℂ) ^ (2 : ℕ)) /
            (K.relIndex (Section1.inertiaSubgroup K ρ.character) : ℂ))
            = (Section1.degree (Section1.inducedCF K ρ.character) /
                Section1.scalarProduct L (Section1.inducedCF K ρ.character)
                  (Section1.inducedCF K ρ.character)) *
                Section1.degree (Section1.inducedCF K ρ.character) := by
                rw [hsp]
                rw [Section1.degree_inducedClassFunction]
                rw [Section1.degree_representation_character]
                simp [Subgroup.relIndex_top_right, Nat.cast_mul, pow_two]
                ring
        _ = (Subgroup.index K : ℂ) *
            ∑ i : Section1.conjugateOrbitIndex K ρ.character,
              Section1.degree (Section1.conjugateOrbitConj K ρ.character i) *
                Section1.degree (Section1.conjugateOrbitConj K ρ.character i) := hcomplex
        _ = (K.relIndex (⊤ : Subgroup L) : ℂ) *
            ∑ i : Section1.conjugateOrbitIndex K ρ.character,
              ((n : ℂ) ^ (2 : ℕ)) := by
              rw [Subgroup.relIndex_top_right]
              congr 1
              refine Finset.sum_congr rfl ?_
              intro i _
              have hdeg :
                  Section1.degree (Section1.conjugateOrbitConj K ρ.character i) =
                    (n : ℂ) := by
                refine Quotient.inductionOn i ?_
                intro g
                unfold Section1.degree Section1.conjugateOrbitConj
                dsimp [Section1.conjugateOnNormal]
                change ρ.character
                  ⟨g * 1 * g⁻¹, by
                    simp⟩ = (n : ℂ)
                have hone : (⟨g * 1 * g⁻¹, by
                    simp⟩ : K) = 1 := by
                  ext
                  simp
                rw [hone]
                simp
              rw [hdeg]
              ring
    have hcf : Section5.cfNormSq (Section1.inducedCF K θ) =
        (K.relIndex (Section1.inertiaSubgroup K ρ.character) : ℝ) := by
      unfold Section5.cfNormSq
      rw [hθeq]
      rw [hsp]
      simp
    rw [hcf]
    have hreal := congrArg Complex.re hcomplex'
    have huniv_orbit :
        (@Finset.univ (Section1.conjugateOrbitIndex K ρ.character) orbitFintype) =
          (@Finset.univ (Section1.conjugateOrbitIndex K ρ.character)
            (Quotient.fintype (Section1.conjugateOrbitSetoid K ρ.character))) := by
      ext i
      simp
    rw [huniv_orbit] at hreal
    rw [hθeq]
    simpa [Complex.ofReal_div, Nat.cast_sum, Finset.mul_sum, pow_two, Nat.cast_mul]
      using hreal

private theorem theorem_6_2_inducedKernelFamily_term_nonneg
    {L : Type u} [Group L] [Finite L]
    {K A : Subgroup L} [K.Normal]
    {S : Finset (Section1.ClassFunction L)}
    (hS : inducedKernelFamily K A S)
    {χ : Section1.ClassFunction L} (hχ : χ ∈ S) {dχ : ℕ}
    (hdχ : Section1.degree χ = (dχ : ℂ)) :
    0 ≤ (((dχ : ℝ) ^ (2 : ℕ)) / Section5.cfNormSq χ) := by
  classical
  rcases (hS.2 χ).mp hχ with ⟨θ, hθirr, _hθker, _hθne, hχeq⟩
  rcases theorem_6_2_pf15_orbit_contribution (L := L) (K := K) hθirr with
    ⟨dθ, dχ', _hθdeg, hχdeg, hterm⟩
  have hd_eq : dχ = dχ' := by
    have hcast : (dχ : ℂ) = (dχ' : ℂ) := by
      rw [← hdχ, hχeq, hχdeg]
    exact_mod_cast hcast
  rw [hd_eq, hχeq, hterm]
  positivity

public theorem theorem_6_2_pf15_degree_lower
    {L : Type u} [Group L] [Finite L]
    {G : Type u} [Group G] [Finite G]
    {K A B : Subgroup L}
    {S SA SB S1 : Finset (Section1.ClassFunction L)}
    {T : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    (h61 : hypothesis_6_1_statement K S T)
    (hSA : inducedKernelFamily K A SA)
    (hSB : inducedKernelFamily K B SB)
    (hAnorm : A.Normal)
    (hS1sub : S1 ⊆ SA ∪ SB)
    (hSA_S1 : SA ⊆ S1)
    (dS1 : S1 → ℕ)
    (hdS1 : ∀ Y : S1,
      Section1.degree (Y : Section1.ClassFunction L) = (dS1 Y : ℂ)) :
    (K.relIndex (⊤ : Subgroup L) : ℝ) * ((A.relIndex K : ℝ) - 1) ≤
      ∑ Y : S1,
        (((dS1 Y : ℝ) ^ (2 : ℕ)) /
          Section5.cfNormSq (Y : Section1.ClassFunction L)) := by
  classical
  haveI : K.Normal := h61.2.1
  letI : (A.subgroupOf K).Normal := hAnorm.subgroupOf K
  let Q := K ⧸ A.subgroupOf K
  rcases theorem_6_2_quotient_irreducible_degree_data Q with
    ⟨ι, hι, hιdec, χQ, hχQ, dQ, i0, hdQ_eval, hχQ0, _hdQ0,
      _hsum_all, hsum_nonprincipal⟩
  letI : Fintype ι := hι
  letI : DecidableEq ι := hιdec
  let I := {i : ι // i ≠ i0}
  letI : Fintype I := Fintype.ofFinite I
  letI : DecidableEq I := Classical.decEq I
  let nQ : ι → ℕ := fun i => Classical.choose (hχQ.1 i).1
  let ρQ : (i : ι) → Representation ℂ Q (Fin (nQ i) → ℂ) :=
    fun i => Classical.choose (Classical.choose_spec (hχQ.1 i).1)
  have hχρ : ∀ i, χQ i = (Theory.Character.characterClassFunction (ρQ i)) := by
    intro i
    exact Classical.choose_spec (Classical.choose_spec (hχQ.1 i).1)
  have hnQ_dQ : ∀ i, nQ i = dQ i := by
    intro i
    have hcast : (nQ i : ℂ) = (dQ i : ℂ) := by
      rw [← hdQ_eval i]
      rw [hχρ i]
      change (nQ i : ℂ) = (ρQ i).character (1 : Q)
      simp [nQ, Representation.character]
    exact_mod_cast hcast
  let q : K →* Q := QuotientGroup.mk' (A.subgroupOf K)
  let ρK : (i : ι) → Representation ℂ K (Fin (nQ i) → ℂ) := fun i => (ρQ i).comp q
  let θ : ι → Section1.ClassFunction K := fun i => (ρK i).character
  have hρQirr : ∀ i, Representation.IsIrreducible (ρQ i) := by
    intro i
    have hnorm : Theory.Character.classFunctionInner (Theory.Character.characterClassFunction (ρQ i))
        (Theory.Character.characterClassFunction (ρQ i)) = 1 := by
      simpa [← hχρ i] using (hχQ.1 i).2
    exact (Theory.Character.irreducible_iff_character_norm_one (ρQ i)).2 hnorm
  have hρKirr : ∀ i, Representation.IsIrreducible (ρK i) := by
    intro i
    exact theorem_6_2_isIrreducible_comp_surjective (ρQ i) q
      (QuotientGroup.mk'_surjective (A.subgroupOf K)) (hρQirr i)
  have hθirr : ∀ i, Section1.IsIrreducibleCharacterOnGroup (θ i) := by
    intro i
    exact Section1.isIrreducibleCharacterOnGroup_of_representation (ρK i) (hρKirr i)
  have hθdegree : ∀ i, Section1.degree (θ i) = (dQ i : ℂ) := by
    intro i
    change (ρK i).character (1 : K) = (dQ i : ℂ)
    rw [← hnQ_dQ i]
    simp [ρK, Representation.character]
  have hθker : ∀ i, Section1.subgroupInKernel' (θ i) (A.subgroupOf K) := by
    intro i
    have hrepker : Section1.subgroupInRepresentationKernel (ρK i) (A.subgroupOf K) := by
      intro a
      have hqa : q (a : K) = 1 := by
        exact (QuotientGroup.eq_one_iff (N := A.subgroupOf K) (x := (a : K))).2 a.2
      ext v x
      simp [ρK, hqa]
    exact (Section1.subgroupInKernel'_character_iff_subgroupInRepresentationKernel
      (ρK i) (A.subgroupOf K)).mpr hrepker
  have hθne : ∀ i : I, θ i.1 ≠ Section1.principalCharacter K := by
    intro i hprin
    apply i.2
    apply hχQ.2.2
    rw [hχρ i.1, hχQ0]
    ext c
    rcases ConjClasses.exists_rep c with ⟨qq, rfl⟩
    rcases QuotientGroup.mk'_surjective (A.subgroupOf K) qq with ⟨k, rfl⟩
    change (ρQ i.1).character (QuotientGroup.mk' (A.subgroupOf K) k) = 1
    have hval := congrFun hprin k
    change (ρQ i.1).character (QuotientGroup.mk' (A.subgroupOf K) k) = 1 at hval
    exact hval
  let Y : I → Section1.ClassFunction L := fun i => Section1.inducedCF K (θ i.1)
  have hYdef : ∀ i : I, Y i = Section1.inducedCF K (θ i.1) := by
    intro i
    rfl
  have hYSA : ∀ i : I, Y i ∈ SA := by
    intro i
    exact (hSA.2 (Y i)).mpr ⟨θ i.1, hθirr i.1, hθker i.1, hθne i, rfl⟩
  let YS1 : I → S1 := fun i => ⟨Y i, hSA_S1 (hYSA i)⟩
  have hYS1coe : ∀ i : I, (YS1 i : Section1.ClassFunction L) = Y i := by
    intro i
    rfl
  let term : S1 → ℝ := fun Y =>
    (((dS1 Y : ℝ) ^ (2 : ℕ)) / Section5.cfNormSq (Y : Section1.ClassFunction L))
  have hterm_nonneg : ∀ Y : S1, 0 ≤ term Y := by
    intro Y
    rcases Finset.mem_union.mp (hS1sub Y.2) with hYSA' | hYSB'
    · simpa [term] using theorem_6_2_inducedKernelFamily_term_nonneg hSA hYSA' (hdS1 Y)
    · simpa [term] using theorem_6_2_inducedKernelFamily_term_nonneg hSB hYSB' (hdS1 Y)
  have hterm_rep : ∀ i : I, term (YS1 i) =
      (K.relIndex (⊤ : Subgroup L) : ℝ) *
        ∑ o : Section1.conjugateOrbitIndex K (θ i.1), (dQ i.1 : ℝ) ^ (2 : ℕ) := by
    intro i
    rcases theorem_6_2_pf15_orbit_contribution (L := L) (K := K) (hθirr i.1) with
      ⟨dθ, dχ, hθdeg, hχdeg, hterm⟩
    have hdθ_eq : dθ = dQ i.1 := by
      have hcast : (dθ : ℂ) = (dQ i.1 : ℂ) := by
        rw [← hθdeg, hθdegree]
      exact_mod_cast hcast
    have hdχ_eq : dχ = dS1 (YS1 i) := by
      have hcast : (dχ : ℂ) = (dS1 (YS1 i) : ℂ) := by
        rw [← hχdeg]
        rw [← hYdef i, ← hYS1coe i]
        exact hdS1 (YS1 i)
      exact_mod_cast hcast
    change (((dS1 (YS1 i) : ℝ) ^ (2 : ℕ)) /
        Section5.cfNormSq (YS1 i : Section1.ClassFunction L)) =
      (K.relIndex (⊤ : Subgroup L) : ℝ) *
        ∑ o : Section1.conjugateOrbitIndex K (θ i.1), (dQ i.1 : ℝ) ^ (2 : ℕ)
    rw [← hdχ_eq]
    rw [hYS1coe i, hYdef i]
    rw [hterm, hdθ_eq]
  have hθinj : ∀ {i j : I}, θ i.1 = θ j.1 → i = j := by
    intro i j hθeq
    apply Subtype.ext
    apply hχQ.2.2
    rw [hχρ i.1, hχρ j.1]
    ext c
    rcases ConjClasses.exists_rep c with ⟨qq, rfl⟩
    rcases QuotientGroup.mk'_surjective (A.subgroupOf K) qq with ⟨k, rfl⟩
    change (ρQ i.1).character (QuotientGroup.mk' (A.subgroupOf K) k) =
      (ρQ j.1).character (QuotientGroup.mk' (A.subgroupOf K) k)
    have hval := congrFun hθeq k
    change (ρQ i.1).character (QuotientGroup.mk' (A.subgroupOf K) k) =
      (ρQ j.1).character (QuotientGroup.mk' (A.subgroupOf K) k) at hval
    exact hval
  have hconjS1 : ∀ i j : I, YS1 j = YS1 i →
      ∃ o : Section1.conjugateOrbitIndex K (θ i.1),
        θ j.1 = Section1.conjugateOrbitConj K (θ i.1) o := by
    intro i j hYS
    have hYeq : Y j = Y i := by
      have h := congrArg (fun Y : S1 => (Y : Section1.ClassFunction L)) hYS
      simpa [hYS1coe] using h
    by_contra hnone
    push Not at hnone
    have hnot : ∀ o : Section1.conjugateOrbitIndex K (θ i.1),
        θ j.1 ≠ Section1.conjugateOrbitConj K (θ i.1) o := hnone
    have horth := Section1.proposition_1_5_c_nonconjugate_rep_orbit_relIndex_canonical
      (G := L) (H := K) (phi := θ j.1) (phiRep := ρK j.1)
      (thetaRep := ρK i.1) (hphi := by simp [θ])
      (hphi_irreducible := hρKirr j.1) (htheta_irreducible := hρKirr i.1)
      (hnotConj := by simpa [θ] using hnot)
    have hself : Section1.scalarProduct L (Y i) (Y i) ≠ 0 := by
      have hsp := Section1.proposition_1_5_b_rep_orbit_relIndex_canonical
        (G := L) (H := K) (ρK i.1) (hρKirr i.1)
      have hrel_ne : K.relIndex (Section1.inertiaSubgroup K (θ i.1)) ≠ 0 := by
        rw [Subgroup.relIndex]
        exact Subgroup.index_ne_zero_of_finite
      rw [hYdef i]
      change Section1.scalarProduct L
        (Section1.inducedCF K (ρK i.1).character)
        (Section1.inducedCF K (ρK i.1).character) ≠ 0
      rw [hsp]
      exact_mod_cast hrel_ne
    apply hself
    rw [← hYdef j, ← hYdef i] at horth
    rw [hYeq] at horth
    exact horth
  let weight : I → ℝ := fun i =>
    (K.relIndex (⊤ : Subgroup L) : ℝ) * (dQ i.1 : ℝ) ^ (2 : ℕ)
  have hfiber_bound_rep : ∀ i : I,
      (Finset.univ.filter (fun j : I => YS1 j = YS1 i)).sum weight ≤ term (YS1 i) := by
    intro i
    let fiber : Finset I := Finset.univ.filter (fun j : I => YS1 j = YS1 i)
    let orbitOf : I → Section1.conjugateOrbitIndex K (θ i.1) := fun j =>
      if h : YS1 j = YS1 i then Classical.choose (hconjS1 i j h)
      else Section1.conjugateOrbitFiber K (θ i.1) 1
    have horbit_spec : ∀ j : I, (hj : j ∈ fiber) →
        θ j.1 = Section1.conjugateOrbitConj K (θ i.1) (orbitOf j) := by
      intro j hj
      have hji : YS1 j = YS1 i := by
        simpa [fiber] using hj
      dsimp [orbitOf]
      rw [dif_pos hji]
      exact Classical.choose_spec (hconjS1 i j hji)
    have hinj : Set.InjOn orbitOf (fiber : Set I) := by
      intro j hj k hk heq
      have hθj := horbit_spec j hj
      have hθk := horbit_spec k hk
      apply hθinj
      rw [hθj, hθk, heq]
    have hmaps : Set.MapsTo orbitOf (fiber : Set I)
        (Finset.univ : Finset (Section1.conjugateOrbitIndex K (θ i.1))) := by
      intro j hj
      simp
    have hcard_le : fiber.card ≤
        Fintype.card (Section1.conjugateOrbitIndex K (θ i.1)) := by
      simpa using Finset.card_le_card_of_injOn orbitOf hmaps hinj
    have hdeg_eq : ∀ j ∈ fiber, dQ j.1 = dQ i.1 := by
      intro j hj
      have hθj := horbit_spec j hj
      have hdeg_orbit :
          Section1.degree (Section1.conjugateOrbitConj K (θ i.1) (orbitOf j)) =
            Section1.degree (θ i.1) := by
        refine Quotient.inductionOn (orbitOf j) ?_
        intro g
        unfold Section1.degree Section1.conjugateOrbitConj
        dsimp [Section1.conjugateOnNormal]
        congr 1
        ext
        simp
      have hcast : (dQ j.1 : ℂ) = (dQ i.1 : ℂ) := by
        rw [← hθdegree j.1, hθj, hdeg_orbit, hθdegree i.1]
      exact_mod_cast hcast
    have hfiber_sum_eq :
        fiber.sum weight =
          fiber.card * ((K.relIndex (⊤ : Subgroup L) : ℝ) * (dQ i.1 : ℝ) ^ (2 : ℕ)) := by
      calc
        fiber.sum weight =
            fiber.sum (fun _ : I =>
              (K.relIndex (⊤ : Subgroup L) : ℝ) * (dQ i.1 : ℝ) ^ (2 : ℕ)) := by
              refine Finset.sum_congr rfl ?_
              intro j hj
              simp [weight, hdeg_eq j hj]
        _ = fiber.card *
            ((K.relIndex (⊤ : Subgroup L) : ℝ) * (dQ i.1 : ℝ) ^ (2 : ℕ)) := by
              simp [Finset.sum_const, nsmul_eq_mul]
    have horbit_sum_eq :
        (∑ o : Section1.conjugateOrbitIndex K (θ i.1), (dQ i.1 : ℝ) ^ (2 : ℕ)) =
          Fintype.card (Section1.conjugateOrbitIndex K (θ i.1)) *
            (dQ i.1 : ℝ) ^ (2 : ℕ) := by
      simp [Finset.sum_const, nsmul_eq_mul]
    change fiber.sum weight ≤ term (YS1 i)
    rw [hfiber_sum_eq, hterm_rep i, horbit_sum_eq]
    have hnonneg :
        0 ≤ (K.relIndex (⊤ : Subgroup L) : ℝ) * (dQ i.1 : ℝ) ^ (2 : ℕ) := by
      positivity
    have hcard_le_real :
        (fiber.card : ℝ) ≤
          (Fintype.card (Section1.conjugateOrbitIndex K (θ i.1)) : ℝ) := by
      exact_mod_cast hcard_le
    calc
      (fiber.card : ℝ) *
          ((K.relIndex (⊤ : Subgroup L) : ℝ) * (dQ i.1 : ℝ) ^ (2 : ℕ)) ≤
        (Fintype.card (Section1.conjugateOrbitIndex K (θ i.1)) : ℝ) *
          ((K.relIndex (⊤ : Subgroup L) : ℝ) * (dQ i.1 : ℝ) ^ (2 : ℕ)) :=
          mul_le_mul_of_nonneg_right hcard_le_real hnonneg
      _ = (K.relIndex (⊤ : Subgroup L) : ℝ) *
          ((Fintype.card (Section1.conjugateOrbitIndex K (θ i.1)) : ℝ) *
            (dQ i.1 : ℝ) ^ (2 : ℕ)) := by
          ring
  have hfiber_bound_all : ∀ Y0 : S1,
      (Finset.univ.filter (fun i : I => YS1 i = Y0)).sum weight ≤ term Y0 := by
    intro Y0
    by_cases hY0 : ∃ i : I, YS1 i = Y0
    · rcases hY0 with ⟨i, hi⟩
      have hsum_eq :
          (Finset.univ.filter (fun j : I => YS1 j = Y0)).sum weight =
            (Finset.univ.filter (fun j : I => YS1 j = YS1 i)).sum weight := by
        congr 1
        ext j
        simp [hi]
      rw [hsum_eq, ← hi]
      exact hfiber_bound_rep i
    · have hempty : Finset.univ.filter (fun j : I => YS1 j = Y0) = ∅ := by
        ext j
        simp
        intro hji
        exact (hY0 ⟨j, hji⟩).elim
      rw [hempty]
      simpa using hterm_nonneg Y0
  have hsum_weight_le : (∑ i : I, weight i) ≤ ∑ Y0 : S1, term Y0 := by
    rw [← Finset.sum_fiberwise (s := (Finset.univ : Finset I)) (g := YS1) (f := weight)]
    apply Finset.sum_le_sum
    intro Y0 _hY0
    exact hfiber_bound_all Y0
  have hsum_weight :
      (∑ i : I, weight i) =
        (K.relIndex (⊤ : Subgroup L) : ℝ) * ((A.relIndex K : ℝ) - 1) := by
    have hsubtype : (∑ i : I, (dQ i.1 : ℝ) ^ (2 : ℕ)) =
        (Finset.univ.erase i0).sum (fun i => (dQ i : ℝ) ^ (2 : ℕ)) := by
      symm
      exact Finset.sum_subtype (s := Finset.univ.erase i0)
        (f := fun i => (dQ i : ℝ) ^ (2 : ℕ)) (by intro x; simp)
    have hcardQ : Nat.card Q = A.relIndex K := by
      rw [← Subgroup.index_eq_card]
      simp [Subgroup.relIndex]
    calc
      (∑ i : I, weight i) =
          (K.relIndex (⊤ : Subgroup L) : ℝ) *
            ∑ i : I, (dQ i.1 : ℝ) ^ (2 : ℕ) := by
            simp [weight, Finset.mul_sum]
      _ = (K.relIndex (⊤ : Subgroup L) : ℝ) * ((A.relIndex K : ℝ) - 1) := by
            rw [hsubtype, hsum_nonprincipal, hcardQ]
  calc
    (K.relIndex (⊤ : Subgroup L) : ℝ) * ((A.relIndex K : ℝ) - 1) =
        ∑ i : I, weight i := hsum_weight.symm
    _ ≤ ∑ Y0 : S1, term Y0 := hsum_weight_le

public theorem theorem_6_2
    {L : Type u} [Group L] [Finite L]
    {G : Type u} [Group G] [Finite G]
    (K A B C D : Subgroup L)
    (S : Finset (Section1.ClassFunction L))
    (SA SB : Finset (Section1.ClassFunction L))
    (T : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G) :
    theorem_6_2_statement K A B C D S SA SB T := by
  classical
  intro h61 hSA hSB hAnorm hAltK hcent hcohSA hSBne hnotSB
  haveI : K.Normal := h61.2.1
  have hSbot : inducedKernelFamily K ⊥ S :=
    hypothesis_6_1_inducedKernelFamily_bot h61
  have hSAsubS : SA ⊆ S :=
    inducedKernelFamily_subset_base hSbot hSA
  have hSBsubS : SB ⊆ S :=
    inducedKernelFamily_subset_base hSbot hSB
  rcases theorem_6_2_obstruction_data h61 hSA hSB hAnorm hAltK hcent
      hcohSA hSBne hnotSB with
    ⟨S1, ψ, χA, hSA_S1, hS1sub, hS1closed, hS1coh, hψSB, hψnotS1,
      hnotPair, hχA_S1, hχAdeg⟩
  have hS1subS : S1 ⊆ S := by
    intro χ hχ
    rcases Finset.mem_union.mp (hS1sub hχ) with hχA | hχB
    · exact hSAsubS hχA
    · exact hSBsubS hχB
  have hψS : ψ ∈ S := hSBsubS hψSB
  have hψbar_notS1 :
      Section1.conjugateCharacter ψ ∉ S1 := by
    intro hψbar
    apply hψnotS1
    have hbarbar : Section1.conjugateCharacter
        (Section1.conjugateCharacter ψ) ∈ S1 :=
      hS1closed _ hψbar
    have hcc : Section1.conjugateCharacter
        (Section1.conjugateCharacter ψ) = ψ := by
      ext x
      simp [Section1.conjugateCharacter]
    simpa [hcc] using hbarbar
  rcases theorem_6_2_pf18_degree_upper hcent hSB hψSB with
    ⟨dψ, hψdeg, hdvdψ, hψupper⟩
  have hYdegree : ∀ Y : S1,
      ∃ dY : ℕ, Section1.degree (Y : Section1.ClassFunction L) = (dY : ℂ) := by
    intro Y
    rcases Finset.mem_union.mp (hS1sub Y.2) with hYSA | hYSB
    · rcases inducedKernelFamily_degree_data hSA hYSA with
        ⟨_dθ, dχ, hdeg, _hmul, _hdvd⟩
      exact ⟨dχ, hdeg⟩
    · rcases inducedKernelFamily_degree_data hSB hYSB with
        ⟨_dθ, dχ, hdeg, _hmul, _hdvd⟩
      exact ⟨dχ, hdeg⟩
  let dS1 : S1 → ℕ := fun Y => Classical.choose (hYdegree Y)
  have hdS1 : ∀ Y : S1,
      Section1.degree (Y : Section1.ClassFunction L) = (dS1 Y : ℂ) := by
    intro Y
    exact Classical.choose_spec (hYdegree Y)
  have hsumUpper :
      (∑ Y : S1,
        (((dS1 Y : ℝ) ^ (2 : ℕ)) /
          Section5.cfNormSq (Y : Section1.ClassFunction L))) ≤
        2 * (dψ : ℝ) * (K.relIndex (⊤ : Subgroup L) : ℝ) := by
    exact theorem_6_2_pf56_numeric_obstruction
      (h52 := hypothesis_6_1_hypothesis_5_2 h61)
      (hS1sub := hS1subS)
      (hS1closed := hS1closed)
      (X := ⟨ψ, hψS⟩)
      (hXbarNotin := hψbar_notS1)
      (X1 := ⟨χA, hχA_S1⟩)
      (hcoh := hS1coh)
      (hnotPair := hnotPair)
      (d1 := K.relIndex (⊤ : Subgroup L))
      (dX := dψ)
      hχAdeg hψdeg hdvdψ dS1 hdS1
  have hsumLower :
      (K.relIndex (⊤ : Subgroup L) : ℝ) * ((A.relIndex K : ℝ) - 1) ≤
      ∑ Y : S1,
        (((dS1 Y : ℝ) ^ (2 : ℕ)) /
          Section5.cfNormSq (Y : Section1.ClassFunction L)) :=
    theorem_6_2_pf15_degree_lower h61 hSA hSB hAnorm hS1sub hSA_S1 dS1 hdS1
  have hlower :
      (A.relIndex K : ℝ) - 1 ≤ 2 * (dψ : ℝ) := by
    have hchain :
        (K.relIndex (⊤ : Subgroup L) : ℝ) * ((A.relIndex K : ℝ) - 1) ≤
          2 * (dψ : ℝ) * (K.relIndex (⊤ : Subgroup L) : ℝ) :=
      le_trans hsumLower hsumUpper
    have hKindex_ne : K.index ≠ 0 := Subgroup.index_ne_zero_of_finite (H := K)
    have hKindex_pos : 0 < (K.relIndex (⊤ : Subgroup L) : ℝ) := by
      rw [Subgroup.relIndex_top_right]
      exact_mod_cast Nat.pos_of_ne_zero hKindex_ne
    nlinarith
  exact theorem_6_2_arithmetic_core K A C D hlower hψupper

end CFSG.Section6
