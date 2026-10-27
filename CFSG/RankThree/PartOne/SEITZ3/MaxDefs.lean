module

public import CFSG.RankThree.Chevalley.SteinbergCFOddG2QPlusTorus
public import CFSG.LinearAlgebra.SL2MinimalFaithfulMatrix

public section

namespace CFSG.RankThree.PartOne.SEITZ3

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.ComponentClassification.UnbalancedCatalog CFSG.RankThree.Chevalley

variable (K : Type) [Field K]

@[expose] noncomputable def a1a1Hom :
    Matrix.SpecialLinearGroup (Fin 2) K × Matrix.SpecialLinearGroup (Fin 2) K →*
      adjointGroup .G2 K :=
  MonoidHom.noncommCoprod
    ((rootSL2 .G2 K g2a).codRestrict (adjointGroup .G2 K) fun A =>
      (exceptional_Lang_root_rank_one_data .G2 K g2a).2.2.2.2.1 A)
    ((rootSL2 .G2 K g2v).codRestrict (adjointGroup .G2 K) fun A =>
      (exceptional_Lang_root_rank_one_data .G2 K g2v).2.2.2.2.1 A)
    fun A B => Subtype.ext (rootSL2_g2v_mul_rootSL2_g2a B A).symm

@[expose] noncomputable def stdA1A1 :
    Subgroup (adjointGroup .G2 K) :=
  (a1a1Hom K).range

variable {K}

theorem a1a1Hom_apply
    (A B : Matrix.SpecialLinearGroup (Fin 2) K) :
    ((a1a1Hom K (A, B) : adjointGroup .G2 K) : ModGL .G2 K) =
      rootSL2 .G2 K g2a A * rootSL2 .G2 K g2v B := rfl

theorem a1a1Hom_apply_inl
    (A : Matrix.SpecialLinearGroup (Fin 2) K) :
    ((a1a1Hom K (A, 1) : adjointGroup .G2 K) : ModGL .G2 K) = rootSL2 .G2 K g2a A := by
  rw [a1a1Hom_apply, map_one, mul_one]

theorem a1a1Hom_apply_inr
    (B : Matrix.SpecialLinearGroup (Fin 2) K) :
    ((a1a1Hom K (1, B) : adjointGroup .G2 K) : ModGL .G2 K) = rootSL2 .G2 K g2v B := by
  rw [a1a1Hom_apply, map_one, one_mul]

theorem eq_one_of_mem_center_sl2 [CharP K 2] {A : Matrix.SpecialLinearGroup (Fin 2) K}
    (hA : A ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K)) : A = 1 := by
  obtain ⟨r, hr, hrA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hA
  have h2 : r ^ 2 = 1 := by simpa using hr
  have h3 : (r + 1) ^ 2 = 0 := by
    rw [add_sq, h2, one_pow, mul_one, CharTwo.two_eq_zero, zero_mul, add_zero,
      CharTwo.add_self_eq_zero]
  have h4 : r = 1 := by
    have := pow_eq_zero_iff (two_ne_zero) |>.1 h3
    rw [CharTwo.add_eq_zero] at this
    exact this
  subst h4
  ext i j
  have := congrFun (congrFun hrA i) j
  simpa [Matrix.scalar_apply, Matrix.one_apply] using this.symm

theorem a1a1Hom_injective
    [CharP K 2] : Function.Injective
    (a1a1Hom K) := by
  rw [injective_iff_map_eq_one]
  rintro ⟨A, B⟩ h
  have hprod : rootSL2 .G2 K g2a A * rootSL2 .G2 K g2v B = 1 := by
    have h' : ((a1a1Hom K (A, B) : adjointGroup .G2 K) : ModGL .G2 K) = 1 := by
      rw [h]; rfl
    have e : a1a1Hom K (A, B) = a1a1Hom K (A, 1) * a1a1Hom K (1, B) := by
      rw [← map_mul]; simp
    rw [e] at h'
    simpa [a1a1Hom_apply_inl, a1a1Hom_apply_inr] using h'
  have hAinv : rootSL2 .G2 K g2a A = (rootSL2 .G2 K g2v B)⁻¹ := eq_inv_of_mul_eq_one_left hprod
  have hA : A ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K) := by
    rw [Subgroup.mem_center_iff]
    intro A'
    apply rootSL2_injective_of_field (τ := .G2) (K := K) g2a
    rw [map_mul, map_mul, hAinv]
    have hc := rootSL2_g2v_mul_rootSL2_g2a (L := K) B A'
    calc rootSL2 .G2 K g2a A' * (rootSL2 .G2 K g2v B)⁻¹
        = (rootSL2 .G2 K g2v B)⁻¹ * (rootSL2 .G2 K g2v B * rootSL2 .G2 K g2a A') *
            (rootSL2 .G2 K g2v B)⁻¹ := by group
      _ = (rootSL2 .G2 K g2v B)⁻¹ * (rootSL2 .G2 K g2a A' * rootSL2 .G2 K g2v B) *
            (rootSL2 .G2 K g2v B)⁻¹ := by rw [hc]
      _ = (rootSL2 .G2 K g2v B)⁻¹ * rootSL2 .G2 K g2a A' := by group
  have hA1 : A = 1 := eq_one_of_mem_center_sl2 hA
  subst hA1
  have hB : rootSL2 .G2 K g2v B = 1 := by
    rw [map_one, one_mul] at hprod
    exact hprod
  have hB1 : B = 1 := rootSL2_injective_of_field (τ := .G2) (K := K) g2v (by rw [hB, map_one])
  rw [hB1]
  rfl

theorem card_stdA1A1
    [Finite K] [CharP K 2] :
    Nat.card (stdA1A1 K) = (Nat.card K * (Nat.card K ^ 2 - 1)) ^ 2 := by
  unfold stdA1A1
  rw [← Nat.card_congr (MonoidHom.ofInjective (a1a1Hom_injective (K := K))).toEquiv, Nat.card_prod,
    CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two]
  exact (sq _).symm

@[expose] def MaxSL2SL2G2 :
    Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2], 4 ≤ Nat.card K →
    ∀ N : Subgroup (adjointGroup .G2 K), stdA1A1 K ≤ N → N = stdA1A1 K ∨ N = ⊤

end CFSG.RankThree.PartOne.SEITZ3
