module

public import CFSG.RankThree.PartOne.KF4.QPlusFam
public import CFSG.RankThree.PartOne.KF4.F4ThreeFamily
public import CFSG.RankThree.PartOne.KF4.F4ThreeKernel

public noncomputable section

namespace CFSG.RankThree.PartOne.KF4

open Matrix CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.E6
  CFSG.RankThree.Chevalley CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag (blockSL)
open CFSG.RankThree.PartOne.KE
open scoped Matrix MatrixGroups Pointwise


section A2

variable {L : Type} [Field L] [CharP L 2] [IsAlgClosed L] {K : Type} [Field K] [Algebra K L]
  [IsAlgClosure K L]

omit
  [IsAlgClosed L] in
theorem qp_frobenius_pow (f : ℕ) (c : L) : iterateFrobenius L 2 f c = c ^ 2 ^ f :=
  iterateFrobenius_def 2 f c

theorem long_cast_eq : (({f4Index 0, f4Index 1} : Finset (Fin Tag.F4.rank)) :
    Set (Fin Tag.F4.rank)) = f4LongSupport := by
  ext i
  simp [f4LongSupport]

theorem short_cast_eq : (({f4Index 2, f4Index 3} : Finset (Fin Tag.F4.rank)) :
    Set (Fin Tag.F4.rank)) = f4ShortSupport := by
  ext i
  simp [f4ShortSupport]

theorem qpFactor_longA2 (f : ℕ) (hf : 1 ≤ f) (hk : Nat.card K = 2 ^ f) (hq : 2 < 2 ^ f) :
    ∃ P : Subgroup (ModGL Tag.F4 L),
      QPFactor (qpRep L) (Units.map (entrywiseHom (iterateFrobenius L 2 f)))
        (parabolicRoots Tag.F4 (({f4Index 0, f4Index 1} : Finset (Fin Tag.F4.rank)) :
          Set (Fin Tag.F4.rank))) P ∧
      ∃ h₀ : ModGL Tag.F4 L, h₀ ∈ adjointGroup Tag.F4 L ∧ ∀ Y : SL(2, K),
        h₀ * simpleRootSL2 Tag.F4 L (f4Index 0)
          (Matrix.SpecialLinearGroup.map (algebraMap K L) Y) * h₀⁻¹ ∈ P := by
  obtain ⟨P, hP, hP1, J, hJ⟩ := (f4Long_frame (L := L)).family_unitary_ex Nat.prime_two hf
    hk hq (iterateFrobenius L 2 f) (qp_frobenius_pow f) (qpRep L) qpRep_mem_monomial
    (Equiv.refl (Fin 3)) (fun i j _ => by
      rw [weylQuotientHom_qpRep_smul]
      exact (f4chainLong_neg i j).symm)
  have hS : parabolicRoots Tag.F4 (({f4Index 0, f4Index 1} : Finset (Fin Tag.F4.rank)) :
      Set (Fin Tag.F4.rank)) = {r | ∃ i j : Fin 3, i ≠ j ∧ r = chainRoot f4chainLong i j} := by
    rw [long_cast_eq]
    exact parabolicRoots_long_eq
  refine ⟨P (), ⟨hP.1 (), hP.2.1 (), by rw [hS]; exact hP1, ?_⟩, ?_⟩
  · intro y hy hyR hc
    rw [hS] at hy ⊢
    have h := hP.2.2.2.2.2.2 y hy hyR (fun i u hu => hc u hu)
    obtain ⟨h1, h2⟩ := Subgroup.mem_inf.1 h
    exact ⟨(mem_twistedTorusOf.1 h1).1, h2⟩
  · refine ⟨f4rhoLong L J, f4rhoLong_mem_adjointGroup J, fun Y => ?_⟩
    have h := hJ Y
    rw [map_mul, map_mul, map_inv, f4rhoLong_blockSL] at h
    exact h

theorem qpFactor_shortA2 (f : ℕ) (hf : 1 ≤ f) (hk : Nat.card K = 2 ^ f) (hq : 2 < 2 ^ f) :
    ∃ P : Subgroup (ModGL Tag.F4 L),
      QPFactor (qpRep L) (Units.map (entrywiseHom (iterateFrobenius L 2 f)))
        (parabolicRoots Tag.F4 (({f4Index 2, f4Index 3} : Finset (Fin Tag.F4.rank)) :
          Set (Fin Tag.F4.rank))) P ∧
      ∃ h₀ : ModGL Tag.F4 L, h₀ ∈ adjointGroup Tag.F4 L ∧ ∀ Y : SL(2, K),
        h₀ * simpleRootSL2 Tag.F4 L (f4Index 2)
          (Matrix.SpecialLinearGroup.map (algebraMap K L) Y) * h₀⁻¹ ∈ P := by
  obtain ⟨P, hP, hP1, J, hJ⟩ := (f4Short_frame (L := L)).family_unitary_ex Nat.prime_two hf
    hk hq (iterateFrobenius L 2 f) (qp_frobenius_pow f) (qpRep L) qpRep_mem_monomial
    (Equiv.refl (Fin 3)) (fun i j _ => by
      rw [weylQuotientHom_qpRep_smul]
      exact (f4ShortSigma_neg i j).symm)
  have hS : parabolicRoots Tag.F4 (({f4Index 2, f4Index 3} : Finset (Fin Tag.F4.rank)) :
      Set (Fin Tag.F4.rank)) = {r | ∃ i j : Fin 3, i ≠ j ∧ r = f4ShortSigma i j} := by
    rw [short_cast_eq]
    exact parabolicRoots_short_eq
  refine ⟨P (), ⟨hP.1 (), hP.2.1 (), by rw [hS]; exact hP1, ?_⟩, ?_⟩
  · intro y hy hyR hc
    rw [hS] at hy ⊢
    have h := hP.2.2.2.2.2.2 y hy hyR (fun i u hu => hc u hu)
    obtain ⟨h1, h2⟩ := Subgroup.mem_inf.1 h
    exact ⟨(mem_twistedTorusOf.1 h1).1, h2⟩
  · refine ⟨f4rhoShort L J * simpleRootSL2 Tag.F4 L (f4Index 2) WSL,
      mul_mem (f4rhoShort_mem_adjointGroup J) (simpleRootSL2_mem_adjointGroup _ _), fun Y => ?_⟩
    have h := hJ Y
    have e : f4rhoShort L (J * blockSL L 2 1 (Matrix.SpecialLinearGroup.map (algebraMap K L) Y) *
        J⁻¹) = (f4rhoShort L J * simpleRootSL2 Tag.F4 L (f4Index 2) WSL) *
          simpleRootSL2 Tag.F4 L (f4Index 2) (Matrix.SpecialLinearGroup.map (algebraMap K L) Y) *
          (f4rhoShort L J * simpleRootSL2 Tag.F4 L (f4Index 2) WSL)⁻¹ := by
      rw [map_mul, map_mul, map_inv, f4rhoShort_blockSL]
      group
    rw [e] at h
    exact h

theorem qpFam_A2_long (f : ℕ) (hf : 1 ≤ f) (hk : Nat.card K = 2 ^ f) (hq : 2 < 2 ^ f) :
    QPFam L K f {f4Index 0, f4Index 1} (f4Index 0) := by
  obtain ⟨P, hP, hroot⟩ := qpFactor_longA2 (L := L) (K := K) f hf hk hq
  exact qpFam_of_factor f (f4Index 0) hP hroot

theorem qpFam_A2_short (f : ℕ) (hf : 1 ≤ f) (hk : Nat.card K = 2 ^ f) (hq : 2 < 2 ^ f) :
    QPFam L K f {f4Index 2, f4Index 3} (f4Index 2) := by
  obtain ⟨P, hP, hroot⟩ := qpFactor_shortA2 (L := L) (K := K) f hf hk hq
  exact qpFam_of_factor f (f4Index 2) hP hroot

theorem qp_checks_A2A1_long :
    qpOrthSuppB {f4Index 0, f4Index 1} {f4Index 3} = true ∧
      qpUnionB {f4Index 0, f4Index 1, f4Index 3} {f4Index 0, f4Index 1} {f4Index 3} = true ∧
        qpA1B (f4Index 3) = true := by
  refine ⟨?_, ?_, ?_⟩ <;> decide +kernel

theorem qp_checks_A2A1_short :
    qpOrthSuppB {f4Index 2, f4Index 3} {f4Index 0} = true ∧
      qpUnionB {f4Index 0, f4Index 2, f4Index 3} {f4Index 2, f4Index 3} {f4Index 0} = true ∧
        qpA1B (f4Index 0) = true := by
  refine ⟨?_, ?_, ?_⟩ <;> decide +kernel

theorem qpFam_A2A1_long (f : ℕ) [Finite (qpK L f)] (hf : 1 ≤ f) (hk : Nat.card K = 2 ^ f)
    (hq : 2 < 2 ^ f) (h4 : 4 ≤ Nat.card (qpK L f))
    (hK : ∀ a : K, iterateFrobenius L 2 f (algebraMap K L a) = algebraMap K L a) :
    QPFam L K f {f4Index 0, f4Index 1, f4Index 3} (f4Index 3) := by
  obtain ⟨ω, hω⟩ := exists_qpOmega (Ω := L) hf
  obtain ⟨P₁, h₁, -⟩ := qpFactor_longA2 (L := L) (K := K) f hf hk hq
  obtain ⟨hO, hU, hA⟩ := qp_checks_A2A1_long
  have hne : (({f4Index 3} : Finset (Fin Tag.F4.rank)) : Set (Fin Tag.F4.rank)).Nonempty :=
    ⟨f4Index 3, by simp⟩
  have h₂ := qp_factor_connected f h4 qpCascade_3 hne (connected_singleton (f4Index 3)) hω
  refine qpFam_union f (f4Index 3) (parabolicRoots_union_of_check hU) h₁ h₂
    (qpFix_free f h4 qpCascade_3 ω) (qp_comm_of_check hO) (qp_hcen_single hA) ?_
  obtain ⟨h₀, hh₀, hY⟩ := qp_rootclause f hK qpCascade_3 ω (Finset.mem_singleton_self (f4Index 3))
  exact ⟨h₀, hh₀, fun Y => Subgroup.mem_sup_right (hY Y)⟩

theorem qpFam_A2A1_short (f : ℕ) [Finite (qpK L f)] (hf : 1 ≤ f) (hk : Nat.card K = 2 ^ f)
    (hq : 2 < 2 ^ f) (h4 : 4 ≤ Nat.card (qpK L f))
    (hK : ∀ a : K, iterateFrobenius L 2 f (algebraMap K L a) = algebraMap K L a) :
    QPFam L K f {f4Index 0, f4Index 2, f4Index 3} (f4Index 0) := by
  obtain ⟨ω, hω⟩ := exists_qpOmega (Ω := L) hf
  obtain ⟨P₁, h₁, -⟩ := qpFactor_shortA2 (L := L) (K := K) f hf hk hq
  obtain ⟨hO, hU, hA⟩ := qp_checks_A2A1_short
  have hne : (({f4Index 0} : Finset (Fin Tag.F4.rank)) : Set (Fin Tag.F4.rank)).Nonempty :=
    ⟨f4Index 0, by simp⟩
  have h₂ := qp_factor_connected f h4 qpCascade_0 hne (connected_singleton (f4Index 0)) hω
  refine qpFam_union f (f4Index 0) (parabolicRoots_union_of_check hU) h₁ h₂
    (qpFix_free f h4 qpCascade_0 ω) (qp_comm_of_check hO) (qp_hcen_single hA) ?_
  obtain ⟨h₀, hh₀, hY⟩ := qp_rootclause f hK qpCascade_0 ω (Finset.mem_singleton_self (f4Index 0))
  exact ⟨h₀, hh₀, fun Y => Subgroup.mem_sup_right (hY Y)⟩

end A2

end CFSG.RankThree.PartOne.KF4
