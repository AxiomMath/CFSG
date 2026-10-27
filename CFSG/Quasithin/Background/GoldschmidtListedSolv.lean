module

import CFSG.CharacterTheory.Burnside
import CFSG.LieType.SteinbergBRMulEquivCores
import CFSG.LinearAlgebra.LinearGroups.ProjectiveSimple
import CFSG.SignalizerFunctorTheorem.McBride.Models.Suzuki.Local
public import CFSG.LocalAnalysis.SectionRank.SuzukiCover
public import CFSG.Quasithin.Background.GoldschmidtRankOneSUTwo
public import CFSG.Quasithin.EmptyFaithful.S1421L2Two

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.BenderSuzuki CFSG.BenderSuzuki.MatrixGroups

section Generic

variable {K K' : Type*} [Group K] [Group K']

theorem isSolvable_of_ker_le_center (π : K →* K') (hZ : π.ker ≤ Subgroup.center K)
    [Group.IsSolvable K'] : Group.IsSolvable K := by
  have : Group.IsSolvable ↥π.ker :=
    Group.isSolvable_of_comm fun a b => Subtype.ext (Subgroup.mem_center_iff.mp (hZ b.2) a)
  exact Group.isSolvable_of_ker_le_range π.ker.subtype π (by rw [Subgroup.range_subtype])

theorem not_isSolvable_of_isPerfect_of_ne_one [Group.IsPerfect K] {a : K} (h : a ≠ 1) :
    ¬ Group.IsSolvable K := by
  have : Nontrivial K := ⟨⟨a, 1, h⟩⟩
  exact Group.IsPerfect.not_isSolvable K

end Generic

theorem not_isSolvable_psl_two_pow {n : ℕ} (hn : 2 ≤ n) :
    ¬ Group.IsSolvable (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 n)) := by
  have h4 : 4 ≤ Nat.card (GaloisField 2 n) := by
    rw [GaloisField.card 2 n (by omega)]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have : Fintype (GaloisField 2 n) := Fintype.ofFinite _
  have hs4 : ∃ s : Finset (GaloisField 2 n), s.card = 4 := by
    obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq
      (s := (Finset.univ : Finset (GaloisField 2 n))) (n := 4)
      (by rw [Finset.card_univ, ← Nat.card_eq_fintype_card]; exact h4)
    exact ⟨s, hs⟩
  obtain ⟨hnt, -, -⟩ := CFSG.LinearGroups.linear_projective_simple (K := GaloisField 2 n) le_rfl
    (Or.inr hs4)
  have := CFSG.LinearGroups.linear_projective_perfect (K := GaloisField 2 n) le_rfl (Or.inr hs4)
  exact CFSG.LieType.SteinbergBR.not_isSolvable_of_isPerfect

theorem not_isSolvable_sz {a : ℕ} (ha : 1 ≤ a) : ¬ Group.IsSolvable ↥(Sz a) := by
  intro hs
  have hS : Group.IsSolvable ↥(SuzukiMatrixGroup a) :=
    Group.isSolvable_of_isSolvable_injective
      (f := (CFSG.SignalizerFunctorTheorem.McBride.SzModel.szEquiv a).symm.toMonoidHom)
      (MulEquiv.injective _)
  have := CFSG.SectionRank.suzukiMatrixGroup_isPerfect a ha
  obtain ⟨x, y, hxy⟩ := CFSG.SectionRank.suzukiMatrixGroup_nonabelian a ha
  have hne : x * y * (y * x)⁻¹ ≠ 1 := fun h => hxy (mul_inv_eq_one.mp h)
  exact (not_isSolvable_of_isPerfect_of_ne_one hne) hS

section Unitary

variable {F : Type} [Field F]

theorem suTwoPGL_mem_statedSU (n : ℕ) : (suTwoPGL : GL (Fin 3) F) ∈ StatedSU 3 (2 ^ n) F := by
  refine Subgroup.subset_closure ⟨det_suTwoP, ?_⟩
  have h : (suTwoP : Matrix (Fin 3) (Fin 3) F).map (· ^ (2 ^ n)) =
      (suTwoP : Matrix (Fin 3) (Fin 3) F).map (· ^ (2 ^ 1)) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [suTwoP, zero_pow (pow_ne_zero n two_ne_zero)]
  show Matrix.transpose ((suTwoP : Matrix (Fin 3) (Fin 3) F).map (· ^ (2 ^ n))) * suTwoP = 1
  rw [h]
  exact unitary_suTwoP

theorem suTwoPGL_ne_one : (suTwoPGL : GL (Fin 3) F) ≠ 1 := by
  intro h
  have := congrArg (fun u : GL (Fin 3) F => (u : Matrix (Fin 3) (Fin 3) F) 0 0) h
  simp [suTwoPGL, suTwoP] at this

variable [Finite F]

theorem not_isSolvable_statedSU {n : ℕ} (hn : 2 ≤ n) (hF : Nat.card F = (2 ^ n) ^ 2) :
    ¬ Group.IsSolvable (StatedSU 3 (2 ^ n) F) := by
  have hnq : (3, 2 ^ n) ≠ (3, 2) := fun h => by
    have h2 : 2 ^ n = 2 ^ 1 := by simpa using congrArg Prod.snd h
    have := Nat.pow_right_injective le_rfl h2
    omega
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Group.IsPerfect (StatedSU 3 (2 ^ n) F) :=
    CFSG.ClassicalGroups.Unitary.isPerfect_statedSU hF (n := 3) le_rfl hnq
  refine not_isSolvable_of_isPerfect_of_ne_one (a := ⟨suTwoPGL, suTwoPGL_mem_statedSU n⟩) ?_
  intro h
  exact suTwoPGL_ne_one (congrArg Subtype.val h)

theorem not_isSolvable_statedProj {n : ℕ} (hn : 2 ≤ n) (hF : Nat.card F = (2 ^ n) ^ 2) :
    ¬ Group.IsSolvable (StatedProj (StatedSU 3 (2 ^ n) F)) := by
  intro hs
  exact not_isSolvable_statedSU hn hF (isSolvable_of_ker_le_center
    (QuotientGroup.mk' ((StatedScalars (Fin 3) F).subgroupOf (StatedSU 3 (2 ^ n) F)))
    (by rw [QuotientGroup.ker_mk']; exact statedSU_scalars_le_center))

theorem card_statedProj_one (hF : Nat.card F = (2 ^ 1) ^ 2) :
    Nat.card (StatedProj (StatedSU 3 (2 ^ 1) F)) = 72 := by
  obtain ⟨σ, hσ, hfix, ⟨e⟩⟩ := exists_statedProj_equiv_psu (n := 1) one_ne_zero hF
  have H := External.huppert_II_10_12 (RankTwoShapes.antidiagonalHermitianForm σ hσ) (2 ^ 1) hF
    hfix rfl
  dsimp only at H
  obtain ⟨-, -, -, -, -, -, -, -, hGcard, -⟩ := H
  rw [Nat.card_congr e.toEquiv, hGcard]
  norm_num

theorem isSolvable_statedProj_one (hF : Nat.card F = (2 ^ 1) ^ 2) :
    Group.IsSolvable (StatedProj (StatedSU 3 (2 ^ 1) F)) := by
  have hcard := card_statedProj_one hF
  have : Finite (StatedProj (StatedSU 3 (2 ^ 1) F)) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  have := Fintype.ofFinite (StatedProj (StatedSU 3 (2 ^ 1) F))
  exact CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow (a := 3) (b := 2)
    Nat.prime_two Nat.prime_three (by norm_num)
    (by rw [← Nat.card_eq_fintype_card, hcard]; norm_num)

theorem isSolvable_statedSU_one (hF : Nat.card F = (2 ^ 1) ^ 2) :
    Group.IsSolvable (StatedSU 3 (2 ^ 1) F) := by
  have := isSolvable_statedProj_one hF
  exact isSolvable_of_ker_le_center
    (QuotientGroup.mk' ((StatedScalars (Fin 3) F).subgroupOf (StatedSU 3 (2 ^ 1) F)))
    (by rw [QuotientGroup.ker_mk']; exact statedSU_scalars_le_center)

end Unitary

@[expose] def IsSmallListed (K : Type*) [Group K] : Prop :=
  Nonempty (K ≃* Equiv.Perm (Fin 3)) ∨
    ((Nonempty (K ≃* DihedralGroup 5) ∨ Nonempty (K ≃* ↥(Sz 0))) ∨
      ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 2 ^ 2 ∧
        (Nonempty (K ≃* StatedSU 3 2 F) ∨ Nonempty (K ≃* StatedProj (StatedSU 3 2 F))))

theorem IsSmallListed.isSolvable {K : Type*} [Group K] (h : IsSmallListed K) :
    Group.IsSolvable K := by
  rcases h with ⟨⟨e⟩⟩ | (⟨⟨e⟩⟩ | ⟨⟨e⟩⟩) | ⟨F, i1, i2, hF, ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩⟩
  · exact isSolvable_of_isL2Quot_one (isL2Quot_one_iff_perm3.2 ⟨e⟩)
  · exact isSolvable_of_equiv_dihedral_five e
  · exact isSolvable_of_equiv_sz_zero e
  · have := isSolvable_statedSU_one (F := F) (by simpa using hF)
    exact Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
  · have := isSolvable_statedProj_one (F := F) (by simpa using hF)
    exact Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective

theorem IsRankOneListed.isSmallListed_of_isSolvable {K : Type*} [Group K]
    (h : IsRankOneListed K) (hs : Group.IsSolvable K) : IsSmallListed K := by
  rcases h with ⟨n, hn, ⟨e⟩⟩ | ⟨a, ⟨e⟩⟩ | ⟨n, hn, F, i1, i2, hF, ⟨e⟩⟩ |
    ⟨n, hn, F, i1, i2, hF, ⟨e⟩⟩ | ⟨⟨e⟩⟩
  · rcases Nat.lt_or_ge n 2 with h1 | h2
    · obtain rfl : n = 1 := by omega
      exact Or.inl (isL2Quot_one_iff_perm3.1 ⟨e⟩)
    · exact absurd (Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective)
        (not_isSolvable_psl_two_pow h2)
  · rcases Nat.eq_zero_or_pos a with h0 | h1
    · subst h0
      exact Or.inr (Or.inl (Or.inr ⟨e⟩))
    · exact absurd (Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective)
        (not_isSolvable_sz h1)
  · rcases Nat.lt_or_ge n 2 with h1 | h2
    · obtain rfl : n = 1 := by omega
      exact Or.inr (Or.inr ⟨F, i1, i2, by simpa using hF, Or.inl ⟨e⟩⟩)
    · exact absurd (Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective)
        (not_isSolvable_statedSU h2 hF)
  · rcases Nat.lt_or_ge n 2 with h1 | h2
    · obtain rfl : n = 1 := by omega
      exact Or.inr (Or.inr ⟨F, i1, i2, by simpa using hF, Or.inr ⟨e⟩⟩)
    · exact absurd (Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective)
        (not_isSolvable_statedProj h2 hF)
  · exact Or.inr (Or.inl (Or.inl ⟨e⟩))

theorem isSmallListed_iff_isSolvable {K : Type*} [Group K] (h : IsRankOneListed K) :
    IsSmallListed K ↔ Group.IsSolvable K :=
  ⟨IsSmallListed.isSolvable, h.isSmallListed_of_isSolvable⟩

end CFSG.Quasithin
