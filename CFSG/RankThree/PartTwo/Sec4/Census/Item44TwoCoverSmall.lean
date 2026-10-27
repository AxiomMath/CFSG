module

public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverRanks
public import CFSG.LocalAnalysis.ComponentClassification.PresentationLocalSymplecticSix
import CFSG.CharacterTheory.Burnside
import CFSG.RankThree.PartTwo.Sec13.Item13Models
import CFSG.RankThree.PartTwo.KFacts.K71Sp4

public section

namespace CFSG.RankThree.PartTwo.Sec4.Census

open CFSG Matrix Subgroup
open CFSG.Assembly.LowTwoRank (StatedSp)
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)
open CFSG.ComponentClassification.PresentationLocal (sympFour antidiagGram omegaPerm)

theorem not_isTwoCover_of_card_dvd {J X : Type} [Group J] [Finite J] [Group X] {a b : ℕ}
    (hX : Nat.card X ∣ 2 ^ a * 3 ^ b) : ¬ IsTwoCover J X := by
  rintro ⟨hq, -, -, ⟨e⟩⟩
  have : IsSimpleGroup (J ⧸ center J) := hq.2.1
  have hcard : Nat.card (J ⧸ center J) ∣ 2 ^ a * 3 ^ b := by rwa [Nat.card_congr e.toEquiv]
  obtain ⟨d₁, d₂, hd₁, hd₂, hd⟩ := dvd_mul.mp hcard
  obtain ⟨i, -, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd₁
  obtain ⟨j, -, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hd₂
  have := Fintype.ofFinite (J ⧸ center J)
  have hsolv : Group.IsSolvable (J ⧸ center J) :=
    CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow Nat.prime_two
      Nat.prime_three (by norm_num) (by rw [← Nat.card_eq_fintype_card, hd])
  obtain ⟨x, y, hxy⟩ := hq.2.2
  exact hxy (IsSimpleGroup.comm_iff_isSolvable.mpr hsolv x y)

theorem card_projSL_two_dvd (p : ℕ) [Fact p.Prime] :
    Nat.card (projSL 2 (GaloisField p 1)) ∣ (p ^ 2 - 1) * (p ^ 2 - p) := by
  have := Fintype.ofFinite (GaloisField p 1)
  have hK : Fintype.card (GaloisField p 1) = p := by
    rw [← Nat.card_eq_fintype_card, GaloisField.card p 1 one_ne_zero, pow_one]
  have hGL : Nat.card (GL (Fin 2) (GaloisField p 1)) = (p ^ 2 - 1) * (p ^ 2 - p) := by
    rw [Matrix.card_GL_field, hK, Fin.prod_univ_two]
    simp
  rw [← hGL]
  exact (Subgroup.card_subgroup_dvd_card _).trans
    (Subgroup.card_dvd_of_surjective ProjGenLinGroup.mk_surjective)

theorem not_isTwoCover_projSL_two {J : Type} [Group J] [Finite J] (p : ℕ) [Fact p.Prime]
    (hp : p = 2 ∨ p = 3) : ¬ IsTwoCover J (projSL 2 (GaloisField p 1)) := by
  rcases hp with rfl | rfl
  · exact not_isTwoCover_of_card_dvd (a := 1) (b := 1) (card_projSL_two_dvd 2)
  · exact not_isTwoCover_of_card_dvd (a := 4) (b := 1) (card_projSL_two_dvd 3)

theorem not_isTwoCover_projSU_three_two {J : Type} [Group J] [Finite J] :
    ¬ IsTwoCover J (projSU 3 2 1) := by
  rintro ⟨hq, -, -, ⟨e⟩⟩
  have : IsSimpleGroup (J ⧸ center J) := hq.2.1
  have := Sec13.isSolvable_projSU_two
  have hsolv : Group.IsSolvable (J ⧸ center J) :=
    Group.isSolvable_of_surjective (f := e.symm.toMonoidHom) e.symm.surjective
  obtain ⟨x, y, hxy⟩ := hq.2.2
  exact hxy (IsSimpleGroup.comm_iff_isSolvable.mpr hsolv x y)

section SpFourTwo

@[expose] def sp4Index : Fin 2 ⊕ Fin 2 ≃ Fin 4 where
  toFun := Sum.elim ![0, 1] ![3, 2]
  invFun := ![.inl 0, .inl 1, .inr 1, .inr 0]
  left_inv := by decide
  right_inv := by decide

noncomputable abbrev F2 : Type := GaloisField 2 1

@[expose] noncomputable def f2Equiv : F2 ≃+* ZMod 2 := (GaloisField.equivZmodP 2).toRingEquiv

@[expose] noncomputable def sp4GL : GL (Fin 2 ⊕ Fin 2) F2 →* GL (Fin 4) (ZMod 2) :=
  Units.map ((Matrix.reindexRingEquiv (ZMod 2) sp4Index).toRingHom.comp
    f2Equiv.toRingHom.mapMatrix).toMonoidHom

theorem coe_sp4GL (A : GL (Fin 2 ⊕ Fin 2) F2) :
    (sp4GL A : Matrix (Fin 4) (Fin 4) (ZMod 2)) =
      reindex sp4Index sp4Index ((A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F2).map f2Equiv) :=
  rfl

theorem reindex_gram :
    reindex sp4Index sp4Index ((fromBlocks 0 1 (-1) 0 :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F2).map f2Equiv) = antidiagGram := by
  have h1 : f2Equiv (-1) = 1 := by rw [map_neg, map_one]; decide
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [antidiagGram, sp4Index, fromBlocks, h1]

theorem sp4GL_mem {A : GL (Fin 2 ⊕ Fin 2) F2} (hA : A ∈ StatedSp 2 F2) : sp4GL A ∈ sympFour := by
  refine (Subgroup.closure_le (sympFour.comap sp4GL)).mpr (fun B hB => ?_) hA
  change (sp4GL B : Matrix (Fin 4) (Fin 4) (ZMod 2))ᵀ * antidiagGram *
    (sp4GL B : Matrix (Fin 4) (Fin 4) (ZMod 2)) = antidiagGram
  have hB' : (B : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F2)ᵀ * fromBlocks 0 1 (-1) 0 *
      (B : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F2) = fromBlocks 0 1 (-1) 0 := hB
  rw [coe_sp4GL, ← reindex_gram]
  simp only [reindex_apply]
  rw [transpose_submatrix, submatrix_mul_equiv, submatrix_mul_equiv, ← Matrix.transpose_map,
    ← Matrix.map_mul, ← Matrix.map_mul, hB']

@[expose] noncomputable def sp4Hom : StatedSp 2 F2 →* sympFour :=
  (sp4GL.comp (StatedSp 2 F2).subtype).codRestrict sympFour fun A => sp4GL_mem A.2

@[expose] noncomputable def sp4Transvection : StatedSp 2 F2 :=
  ⟨sqZeroUnit (radSp4 F2) (radSp4_mul F2) ![1, 0, 0], Subgroup.subset_closure (by
    change (1 + radSp4 F2 ![1, 0, 0])ᵀ * fromBlocks 0 1 (-1) 0 * (1 + radSp4 F2 ![1, 0, 0]) =
      fromBlocks 0 1 (-1) 0
    rw [← fromBlocks_one]
    simp only [radSp4, AddMonoidHom.coe_mk, ZeroHom.coe_mk, fromBlocks_add,
      fromBlocks_transpose, fromBlocks_multiply]
    simp [symMat_transpose])⟩

@[expose] def t03Mat : Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  !![1, 0, 0, 1; 0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1]

@[expose] def t03 : GL (Fin 4) (ZMod 2) := ⟨t03Mat, t03Mat, by decide, by decide⟩

theorem t03_mem : t03 ∈ sympFour := by
  rw [CFSG.ComponentClassification.PresentationLocal.mem_sympFour_iff]
  decide

theorem sign_omegaPerm_t03 : Equiv.Perm.sign (omegaPerm ⟨t03, t03_mem⟩) = -1 := by
  decide

theorem sp4Hom_transvection : sp4Hom sp4Transvection = ⟨t03, t03_mem⟩ := by
  have h1 : f2Equiv 1 = 1 := map_one _
  have h0 : f2Equiv 0 = 0 := map_zero _
  refine Subtype.ext (Units.ext ?_)
  change reindex sp4Index sp4Index ((1 + radSp4 F2 ![1, 0, 0]).map f2Equiv) = t03Mat
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sp4Index, radSp4, symMat, t03Mat, fromBlocks, h0, h1]

theorem not_isTwoCover_projSp_two_two {J : Type} [Group J] [Finite J] :
    ¬ IsTwoCover J (projSp 2 F2) := by
  rintro ⟨hq, -, -, ⟨e⟩⟩
  have : Group.IsPerfect J := hq.1
  let ε := CFSG.RankThree.PartTwo.KFacts.statedSpEquivProjSpOfCharTwo F2
  let χ : J →* ℤˣ := Equiv.Perm.sign.comp (omegaPerm.comp (sp4Hom.comp
    (ε.symm.toMonoidHom.comp (e.toMonoidHom.comp (QuotientGroup.mk' (center J))))))
  obtain ⟨y, hy⟩ := QuotientGroup.mk'_surjective (center J) (e.symm (ε sp4Transvection))
  have hχ : χ y = -1 := by
    change Equiv.Perm.sign (omegaPerm (sp4Hom (ε.symm (e (QuotientGroup.mk' (center J) y))))) =
      -1
    rw [hy, MulEquiv.apply_symm_apply, MulEquiv.symm_apply_apply, sp4Hom_transvection,
      sign_omegaPerm_t03]
  have hker : y ∈ χ.ker :=
    Abelianization.commutator_subset_ker χ (Group.IsPerfect.mem_commutator (g := y))
  rw [MonoidHom.mem_ker, hχ] at hker
  exact absurd hker (by decide)

end SpFourTwo

end CFSG.RankThree.PartTwo.Sec4.Census
