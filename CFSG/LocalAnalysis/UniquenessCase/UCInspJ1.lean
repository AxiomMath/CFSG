module

public import CFSG.LocalAnalysis.UniquenessCase.UCK461
public import CFSG.LocalAnalysis.UniquenessCase.UCInspPair

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK.Insp

open CFSG.Blueprint CFSG.ProperTwoGeneratedCore
open scoped commutatorElement

section Word

@[expose] def wordProd {M : Type*} [Monoid M] (x y : M) : List ℕ → M
  | [] => 1
  | n :: w => (if n = 0 then x else if n = 1 then y else y ^ 2) * wordProd x y w

@[expose] def j1Word : List ℕ :=
  [0, 2, 0, 2, 0, 1, 0, 1, 0, 2, 0, 1, 0, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 1, 0, 1]

@[expose] def zMat : Matrix (Fin 7) (Fin 7) (ZMod 11) :=
  wordProd j1_first_matrix j1_second_matrix j1Word

theorem zMat_pow_seven : zMat ^ 7 = 1 := by
  decide +kernel

theorem zMat_ne_one : zMat ≠ 1 := by
  decide +kernel

theorem second_conj_zMat :
    j1_second_matrix * zMat * j1_second_matrix ^ 2 = zMat ^ 2 := by
  decide +kernel

end Word

section JLevel

open CFSG.Sporadic.J1 (J mat mat_mul mat_one mat_pow mat_a mat_b mat_injective b_cube b_ne_one
  card_J nativeEquiv)

@[expose] noncomputable def zJ : J := wordProd CFSG.Sporadic.J1.a CFSG.Sporadic.J1.b j1Word

theorem mat_wordProd : ∀ w : List ℕ,
    mat (wordProd CFSG.Sporadic.J1.a CFSG.Sporadic.J1.b w) =
      wordProd j1_first_matrix j1_second_matrix w
  | [] => mat_one
  | n :: w => by
    rw [wordProd, wordProd, mat_mul, mat_wordProd w]
    congr 1
    split_ifs <;> simp [mat_a, mat_b, mat_pow]

theorem mat_zJ : mat zJ = zMat := mat_wordProd j1Word

theorem zJ_pow_seven : zJ ^ 7 = 1 :=
  mat_injective (by rw [mat_pow, mat_zJ, zMat_pow_seven, mat_one])

theorem zJ_ne_one : zJ ≠ 1 := fun h => zMat_ne_one (by rw [← mat_zJ, h, mat_one])

theorem b_inv_eq : (CFSG.Sporadic.J1.b : J)⁻¹ = CFSG.Sporadic.J1.b ^ 2 := by
  apply inv_eq_of_mul_eq_one_right
  rw [← pow_succ', b_cube]

theorem b_conj_zJ : CFSG.Sporadic.J1.b * zJ * (CFSG.Sporadic.J1.b : J)⁻¹ = zJ ^ 2 := by
  apply mat_injective
  rw [b_inv_eq, mat_mul, mat_mul, mat_pow, mat_pow, mat_b, mat_zJ]
  exact second_conj_zMat

theorem inspPair_J : InspPair 7 (Subgroup.zpowers (CFSG.Sporadic.J1.b : J))
    (Subgroup.zpowers zJ) :=
  inspPair_of_triple (by norm_num) b_cube zJ_pow_seven zJ_ne_one b_conj_zJ (by norm_num)

theorem factorization_three_card_J :
    (Nat.card J).factorization 3 = 1 := by
  rw [card_J]
  have e1 := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three
    (by norm_num : (175560 : ℕ) ≠ 0)).1 (by norm_num : 3 ^ 1 ∣ 175560)
  have e2 : ¬ 2 ≤ (175560 : ℕ).factorization 3 := fun h =>
    (by norm_num : ¬ 3 ^ 2 ∣ 175560) ((Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three
      (by norm_num : (175560 : ℕ) ≠ 0)).2 h)
  omega

theorem inspJ1_core (D : Subgroup J) (hD : Nat.card D = 3) :
    ∃ R : Subgroup J, InspPair 7 D R := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hfac := factorization_three_card_J
  have hb : Nat.card (Subgroup.zpowers (CFSG.Sporadic.J1.b : J)) =
      3 ^ (Nat.card J).factorization 3 := by
    rw [card_zpowers_three b_cube b_ne_one, hfac, pow_one]
  have hD' : Nat.card D = 3 ^ (Nat.card J).factorization 3 := by rw [hD, hfac, pow_one]
  obtain ⟨P₀, hP₀⟩ : ∃ P₀ : Sylow 3 J,
      (P₀ : Subgroup J) = Subgroup.zpowers (CFSG.Sporadic.J1.b : J) := ⟨Sylow.ofCard _ hb, rfl⟩
  obtain ⟨P, hP⟩ : ∃ P : Sylow 3 J, (P : Subgroup J) = D := ⟨Sylow.ofCard D hD', rfl⟩
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq J P₀ P
  have hDeq : D = (Subgroup.zpowers (CFSG.Sporadic.J1.b : J)).map
      (MulAut.conj g).toMonoidHom := by
    have h := congrArg (fun Q : Sylow 3 J => (Q : Subgroup J)) hg
    simp only [Sylow.coe_subgroup_smul, hP₀, hP] at h
    rw [← h]
    rfl
  refine ⟨(Subgroup.zpowers zJ).map (MulAut.conj g).toMonoidHom, ?_⟩
  rw [hDeq]
  exact inspPair_J.map (MulAut.conj g)

end JLevel

end CFSG.LocalAnalysis.UniquenessCase.UCK.Insp

namespace CFSG.LocalAnalysis.UniquenessCase.UCK

open CFSG.Blueprint
open CFSG.LocalAnalysis.UniquenessCase.UCK.Insp
open scoped commutatorElement

theorem inspJ1_holds : InspJ1 := by
  intro G _ _ hG D hD
  obtain ⟨e⟩ := hG
  let e' : G ≃* CFSG.Sporadic.J1.J := e.trans CFSG.Sporadic.J1.nativeEquiv
  obtain ⟨R', hR'⟩ := inspJ1_core (D.map e'.toMonoidHom)
    (by rw [Subgroup.card_map_of_injective e'.injective, hD])
  refine ⟨R'.map e'.symm.toMonoidHom, ?_⟩
  have h := hR'.map e'.symm
  have hDe : (D.map e'.toMonoidHom).map e'.symm.toMonoidHom = D := by
    rw [Subgroup.map_map]
    have : e'.symm.toMonoidHom.comp e'.toMonoidHom = MonoidHom.id G := by
      ext x; simp
    rw [this, Subgroup.map_id]
  rw [hDe] at h
  exact h

end CFSG.LocalAnalysis.UniquenessCase.UCK
