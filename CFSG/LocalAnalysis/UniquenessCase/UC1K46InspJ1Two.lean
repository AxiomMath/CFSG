module

public import CFSG.LocalAnalysis.UniquenessCase.UC1K462Inputs
public import CFSG.LocalAnalysis.UniquenessCase.UCInspJ1
public import CFSG.LocalAnalysis.UniquenessCase.UCInspL2Abs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK.Insp

open CFSG.Blueprint CFSG.ProperTwoGeneratedCore
open scoped commutatorElement

section Word

@[expose] def j1Word2 : List ℕ :=
  [0, 1, 0, 2, 0, 2, 0, 1, 0, 1, 0, 2, 0, 2, 0, 1, 0, 1, 0, 2, 0, 2, 0, 1, 0, 1, 0, 2, 0]

@[expose] def xMat : Matrix (Fin 7) (Fin 7) (ZMod 11) :=
  wordProd j1_first_matrix j1_second_matrix j1Word2

@[expose] def yMat : Matrix (Fin 7) (Fin 7) (ZMod 11) :=
  j1_second_matrix ^ 2 * xMat * j1_second_matrix

theorem xMat_mul_self : xMat * xMat = 1 := by
  decide +kernel

theorem xMat_ne_one : xMat ≠ 1 := by
  decide +kernel

theorem xMat_ne_yMat : xMat ≠ yMat := by
  decide +kernel

theorem yMat_ne_one : yMat ≠ 1 := by
  decide +kernel

theorem yMat_mul_self : yMat * yMat = 1 := by
  decide +kernel

theorem xMat_comm_yMat : xMat * yMat = yMat * xMat := by
  decide +kernel

theorem second_conj_xMat :
    j1_second_matrix * xMat * j1_second_matrix ^ 2 = xMat * yMat := by
  decide +kernel

end Word

section JLevel

open CFSG.Sporadic.J1 (J mat mat_mul mat_one mat_pow mat_a mat_b mat_injective b_cube b_ne_one
  card_J nativeEquiv)

@[expose] noncomputable def xJ : J :=
  wordProd CFSG.Sporadic.J1.a CFSG.Sporadic.J1.b j1Word2

@[expose] noncomputable def yJ : J :=
  (CFSG.Sporadic.J1.b : J)⁻¹ * xJ * CFSG.Sporadic.J1.b

theorem mat_xJ : mat xJ = xMat := mat_wordProd j1Word2

theorem mat_yJ : mat yJ = yMat := by
  rw [yJ, mat_mul, mat_mul, mat_xJ, b_inv_eq, mat_pow, mat_b]
  rfl

theorem xJ_mul_self : xJ * xJ = 1 :=
  mat_injective (by rw [mat_mul, mat_xJ, xMat_mul_self, mat_one])

theorem xJ_ne_one : xJ ≠ 1 := fun h => xMat_ne_one (by rw [← mat_xJ, h, mat_one])

theorem yJ_mul_self : yJ * yJ = 1 :=
  mat_injective (by rw [mat_mul, mat_yJ, yMat_mul_self, mat_one])

theorem yJ_ne_one : yJ ≠ 1 := by
  intro h
  have h' := congrArg mat h
  rw [mat_yJ, mat_one] at h'
  exact yMat_ne_one h'

theorem xJ_ne_yJ : xJ ≠ yJ := by
  intro h
  have h' := congrArg mat h
  rw [mat_xJ, mat_yJ] at h'
  exact xMat_ne_yMat h'

theorem xJ_comm_yJ : xJ * yJ = yJ * xJ :=
  mat_injective (by rw [mat_mul, mat_mul, mat_xJ, mat_yJ, xMat_comm_yMat])

theorem b_conj_xJ : (CFSG.Sporadic.J1.b : J) * xJ * (CFSG.Sporadic.J1.b : J)⁻¹ = xJ * yJ := by
  apply mat_injective
  rw [mat_mul, mat_mul, mat_mul, mat_xJ, mat_yJ, mat_b, b_inv_eq, mat_pow, mat_b]
  exact second_conj_xMat

theorem b_conj_yJ : (CFSG.Sporadic.J1.b : J) * yJ * (CFSG.Sporadic.J1.b : J)⁻¹ = xJ := by
  rw [yJ]
  group

theorem kleinian_pair_J : ∃ S : Subgroup J,
    InspPair 2 (Subgroup.zpowers (CFSG.Sporadic.J1.b : J)) S := by
  obtain ⟨S, hEl, hcard, hnorm, hcomm⟩ :=
    exists_klein_of_triple (d := (CFSG.Sporadic.J1.b : J)) (x := xJ) (y := yJ)
      xJ_mul_self yJ_mul_self xJ_comm_yJ xJ_ne_one yJ_ne_one xJ_ne_yJ b_conj_xJ b_conj_yJ
  refine ⟨S, IsPGroup.of_card (n := 2) (by rw [hcard]; norm_num), hEl.1, ?_, hnorm, hcomm⟩
  intro h
  rw [h, Subgroup.card_bot] at hcard
  omega

theorem inspPair_of_card_three {ℓ : ℕ} {R₀ : Subgroup J}
    (h : InspPair ℓ (Subgroup.zpowers (CFSG.Sporadic.J1.b : J)) R₀)
    (D : Subgroup J) (hD : Nat.card D = 3) : ∃ R : Subgroup J, InspPair ℓ D R := by
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
    have h' := congrArg (fun Q : Sylow 3 J => (Q : Subgroup J)) hg
    simp only [Sylow.coe_subgroup_smul, hP₀, hP] at h'
    rw [← h']
    rfl
  refine ⟨R₀.map (MulAut.conj g).toMonoidHom, ?_⟩
  rw [hDeq]
  exact h.map (MulAut.conj g)

theorem insp2J1_core (D : Subgroup J) (hD : Nat.card D = 3) :
    ∃ S : Subgroup J, InspPair 2 D S := by
  obtain ⟨S, hS⟩ := kleinian_pair_J
  exact inspPair_of_card_three hS D hD

end JLevel

end CFSG.LocalAnalysis.UniquenessCase.UCK.Insp

namespace CFSG.LocalAnalysis.UniquenessCase.UCK

open CFSG.Blueprint
open CFSG.LocalAnalysis.UniquenessCase.UCK.Insp
open scoped commutatorElement

theorem insp2J1_holds : Insp2J1 := by
  intro G _ _ hG D hD
  obtain ⟨e⟩ := hG
  let e' : G ≃* CFSG.Sporadic.J1.J := e.trans CFSG.Sporadic.J1.nativeEquiv
  obtain ⟨S', hS'⟩ := insp2J1_core (D.map e'.toMonoidHom)
    (by rw [Subgroup.card_map_of_injective e'.injective, hD])
  refine ⟨S'.map e'.symm.toMonoidHom, ?_⟩
  have h := hS'.map e'.symm
  have hDe : (D.map e'.toMonoidHom).map e'.symm.toMonoidHom = D := by
    rw [Subgroup.map_map]
    have : e'.symm.toMonoidHom.comp e'.toMonoidHom = MonoidHom.id G := by
      ext x; simp
    rw [this, Subgroup.map_id]
  rw [hDe] at h
  exact h

end CFSG.LocalAnalysis.UniquenessCase.UCK
