module

public import CFSG.RankThree.PartOne.KLCE.A2Model

public section

namespace CFSG.RankThree.PartOne.TCX.F4

open Matrix Subgroup CFSG CFSG.RankThree.Classical2 CFSG.RankThree.PartOne.KLCE
open CFSG.Assembly.LowTwoRank (StatedLieTag StatedSU)
open CFSG.Blueprint (LieModel)
open CFSG.LieType.CurtisTits (lieModel_of_mulEquiv)
open scoped MatrixGroups

variable {L : Type} [Field L]

theorem unitary_cond_map {K₂ : Type} [Field K₂] (ι : K₂ →+* L) (k : ℕ)
    (B : Matrix (Fin 3) (Fin 3) K₂) :
    ((B.map ι).map (· ^ k))ᵀ * B.map ι = ((B.map (· ^ k))ᵀ * B).map ι := by
  ext i j
  simp [Matrix.mul_apply, Matrix.map_apply, Matrix.transpose_apply, map_sum, map_mul, map_pow]

theorem exists_unitary_hom_of_fix {g : ℕ} {K₂ : Type} [Field K₂] [Finite K₂]
    (ι : K₂ →+* L) (hK₂ : Nat.card K₂ = (2 ^ g) ^ 2)
    (hι : ∀ y : L, y ^ 2 ^ (2 * g) = y ↔ ∃ c, ι c = y) (Φ : SL(3, L) ≃* SL(3, L)) (H : SL(3, L))
    (hH : ∀ X : SL(3, L), X ∈ fixSubgroup Φ ↔
      ∃ Y ∈ unitarySet (2 ^ g) 3, Matrix.SpecialLinearGroup.toGL X =
        Matrix.SpecialLinearGroup.toGL H * Y * (Matrix.SpecialLinearGroup.toGL H)⁻¹) :
    ∃ ψ : ↥(StatedSU 3 (2 ^ g) K₂) →* SL(3, L), Function.Injective ψ ∧
      ψ.range = fixSubgroup Φ := by
  classical
  have : Fintype K₂ := Fintype.ofFinite K₂
  have hpow : ∀ c : K₂, c ^ (2 ^ g) ^ 2 = c := fun c => by
    rw [← hK₂, Nat.card_eq_fintype_card]
    exact FiniteField.pow_card c
  have hexp : (2 ^ g) ^ 2 = 2 ^ (2 * g) := by rw [← pow_mul, mul_comm]
  set toSL := statedSU_toSL hK₂ with htoSL
  let ψ : ↥(StatedSU 3 (2 ^ g) K₂) →* SL(3, L) :=
    (MulAut.conj H).toMonoidHom.comp ((SpecialLinearGroup.map (n := Fin 3) ι).comp toSL)
  have hψ : ∀ A, ψ A = H * SpecialLinearGroup.map ι (toSL A) * H⁻¹ := fun A => by
    simp [ψ, MulAut.conj_apply]
  have hcoe : ∀ B : SL(3, K₂), ((SpecialLinearGroup.map ι B : SL(3, L)) : Matrix (Fin 3) (Fin 3) L)
      = (B : Matrix (Fin 3) (Fin 3) K₂).map ι := fun B => by
    rw [SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply]
  refine ⟨ψ, ?_, ?_⟩
  · intro A B hAB
    rw [hψ, hψ] at hAB
    have h1 : SpecialLinearGroup.map ι (toSL A) = SpecialLinearGroup.map ι (toSL B) :=
      mul_left_cancel (mul_right_cancel hAB)
    exact statedSU_toSL_injective hK₂ (map_injective₃ ι h1)
  · ext X
    constructor
    · rintro ⟨A, rfl⟩
      refine (hH _).2 ⟨Matrix.SpecialLinearGroup.toGL (SpecialLinearGroup.map ι (toSL A)),
        ⟨?_, ?_, ?_⟩, ?_⟩
      · intro i j
        have h := hpow ((toSL A : SL(3, K₂)) i j)
        have hc : (((Matrix.SpecialLinearGroup.toGL (SpecialLinearGroup.map ι (toSL A)) : GL _ _) :
            Matrix (Fin 3) (Fin 3) L)) i j = ι ((toSL A : SL(3, K₂)) i j) := by
          change ((SpecialLinearGroup.map ι (toSL A) : SL(3, L)) : Matrix (Fin 3) (Fin 3) L) i j = _
          rw [hcoe]
          rfl
        rw [hc, ← map_pow, h]
      · exact (SpecialLinearGroup.map ι (toSL A)).2
      · have h1 := statedSU_toSL_unitary hK₂ A
        change (((SpecialLinearGroup.map ι (toSL A) : SL(3, L)) : Matrix (Fin 3) (Fin 3) L).map
          (· ^ 2 ^ g))ᵀ * ((SpecialLinearGroup.map ι (toSL A) : SL(3, L)) :
            Matrix (Fin 3) (Fin 3) L) = 1
        rw [hcoe, unitary_cond_map ι (2 ^ g) (toSL A : SL(3, K₂)), h1, Matrix.map_one _ (map_zero ι)
          (map_one ι)]
      · rw [hψ, map_mul, map_mul, map_inv]
    · intro hX
      obtain ⟨Y, hY, hXY⟩ := (hH X).1 hX
      set Yt : SL(3, L) := H⁻¹ * X * H with hYtdef
      have hYt : Matrix.SpecialLinearGroup.toGL Yt = Y := by
        rw [hYtdef, map_mul, map_mul, map_inv, hXY]
        group
      obtain ⟨hent, hdet, hu⟩ := hY
      have hYc : ((Y : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) =
          (Yt : Matrix (Fin 3) (Fin 3) L) := by
        rw [← hYt]
        rfl
      have hentries : ∀ a b, ∃ c : K₂, ι c = (Yt : Matrix (Fin 3) (Fin 3) L) a b := by
        intro a b
        refine (hι _).1 ?_
        have := hent a b
        rw [hYc, hexp] at this
        exact this
      obtain ⟨B, hB⟩ := exists_of_entries_in_range ι Yt hentries
      have hBu : ((B : Matrix (Fin 3) (Fin 3) K₂).map (· ^ 2 ^ g))ᵀ *
          (B : Matrix (Fin 3) (Fin 3) K₂) = 1 := by
        have hmat : (B : Matrix (Fin 3) (Fin 3) K₂).map ι = (Yt : Matrix (Fin 3) (Fin 3) L) := by
          rw [← hcoe, hB]
        rw [hYc] at hu
        have key := unitary_cond_map ι (2 ^ g) (B : Matrix (Fin 3) (Fin 3) K₂)
        rw [hmat, hu] at key
        have h2 : (((B : Matrix (Fin 3) (Fin 3) K₂).map (· ^ 2 ^ g))ᵀ *
            (B : Matrix (Fin 3) (Fin 3) K₂)).map ι = (1 : Matrix (Fin 3) (Fin 3) K₂).map ι := by
          rw [← key, Matrix.map_one _ (map_zero ι) (map_one ι)]
        exact Matrix.map_injective ι.injective h2
      have hmem := toGL_mem_statedSU hK₂ B hBu
      refine ⟨⟨_, hmem⟩, ?_⟩
      have hts : toSL ⟨Matrix.SpecialLinearGroup.toGL B, hmem⟩ = B := Subtype.ext rfl
      rw [hψ, hts, hB, hYtdef]
      group

variable {K₀ K : Type} [Field K₀] [Finite K₀] [Field K] [Finite K] [Algebra K₀ L]
  [IsAlgClosure K₀ L] [Algebra K L] [IsAlgClosure K L] [CharP L 2]

end CFSG.RankThree.PartOne.TCX.F4
