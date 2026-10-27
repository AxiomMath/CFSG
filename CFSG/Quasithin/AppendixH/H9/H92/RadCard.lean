module

public import CFSG.Quasithin.AppendixH.H9.H92.RadHom
public import CFSG.Quasithin.AppendixH.H9.H92.RadCard.NatCardSubmodule
public import CFSG.Quasithin.AppendixH.H9.H92.RadCard.ElemAbelianMap

public section

open scoped Matrix

namespace CFSG.ASVolI.ChH

open CFSG.Quasithin CFSG.Open

theorem finrank_v1Space_eq_rk {n : ℕ} (U : Subgroup (PairN n)) (hU : U ≤ V1n n) :
    Module.finrank (ZMod 2) (v1Space n U) = rk ↥U := by
  have hcard : Nat.card (v1Space n U) = Nat.card U := by
    refine Nat.card_eq_of_bijective (fun a => ⟨pairVec (a : Fin n → ZMod 2) 0, a.2⟩) ⟨?_, ?_⟩
    · intro a b hab
      exact Subtype.ext (pairVec_inj.mp (congrArg Subtype.val hab)).1
    · rintro ⟨x, hx⟩
      obtain ⟨a, b, rfl⟩ := pairVec_surj x
      have hb : b = 0 := ofAdd_eq_one.mp (mem_V1n.mp (hU hx))
      subst hb
      exact ⟨⟨a, hx⟩, rfl⟩
  have hpow : Nat.card (v1Space n U) = 2 ^ Module.finrank (ZMod 2) (v1Space n U) := by
    rw [natCard_submodule_fun_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
  rw [rk, ← hcard, hpow, padicValNat.prime_pow]

theorem radMat_comm_sq {n : ℕ} (D : Submodule (ZMod 2) (Fin n → ZMod 2)) :
    (∀ a ∈ RadMat n D, ∀ b ∈ RadMat n D, a * b = b * a) ∧ ∀ a ∈ RadMat n D, a * a = 1 := by
  have h2 : ∀ M : Matrix (Fin n) (Fin n) (ZMod 2), M + M = 0 := by
    intro M
    ext i j
    simp only [Matrix.add_apply, Matrix.zero_apply]
    exact (by decide : ∀ c : ZMod 2, c + c = 0) _
  have hdecomp : ∀ a ∈ RadMat n D, ∃ N ∈ radNil n D,
      (a : Matrix (Fin n) (Fin n) (ZMod 2)) = 1 + N := fun a ha =>
    ⟨(a : Matrix (Fin n) (Fin n) (ZMod 2)) - 1, (mem_radMat_iff_sub_mem_radNil a).1 ha, by abel⟩
  constructor
  · intro a ha b hb
    obtain ⟨N, hN, haN⟩ := hdecomp a ha
    obtain ⟨N', hN', hbN⟩ := hdecomp b hb
    refine Units.ext ?_
    rw [Units.val_mul, Units.val_mul, haN, hbN]
    have e1 : (1 + N) * (1 + N') = 1 + N + N' + N * N' := by noncomm_ring
    have e2 : (1 + N') * (1 + N) = 1 + N' + N + N' * N := by noncomm_ring
    rw [e1, e2, radNil_mul_radNil hN hN', radNil_mul_radNil hN' hN, add_zero, add_zero]
    abel
  · intro a ha
    obtain ⟨N, hN, haN⟩ := hdecomp a ha
    refine Units.ext ?_
    rw [Units.val_mul, Units.val_one, haN]
    have e : (1 + N) * (1 + N) = 1 + (N + N) + N * N := by noncomm_ring
    rw [e, h2 N, radNil_mul_radNil hN hN, add_zero, add_zero]

theorem card_radMat (D : Submodule (ZMod 2) (Fin 5 → ZMod 2))
    (hD : Module.finrank (ZMod 2) D = 2 ∨ Module.finrank (ZMod 2) D = 3) :
    Nat.card ↥(RadMat 5 D) = 64 := by
  have hbij : Nat.card (RadMat 5 D) = Nat.card (radNil 5 D) := by
    refine Nat.card_eq_of_bijective (fun B => ⟨(B : GL (Fin 5) (ZMod 2)).val - 1,
      (mem_radMat_iff_sub_mem_radNil _).1 B.2⟩) ⟨?_, ?_⟩
    · intro B C h
      have h' := congrArg Subtype.val h
      exact Subtype.ext (Units.ext (sub_left_injective h'))
    · rintro ⟨N, hN⟩
      obtain ⟨B, hB, hBN⟩ := exists_radMat_of_mem_radNil hN
      refine ⟨⟨B, hB⟩, Subtype.ext ?_⟩
      show (B : Matrix (Fin 5) (Fin 5) (ZMod 2)) - 1 = N
      rw [hBN]
      abel
  rw [hbij, natCard_submodule_matrix_eq_pow_finrank (K := ZMod 2), Nat.card_zmod,
    finrank_radNil]
  rcases hD with h | h <;> rw [h] <;> norm_num

theorem isElemAbelian2_radV1 (n : ℕ) (U : Subgroup (PairN n)) : IsElemAbelian2 (RadV1 n U) :=
  isElemAbelian2_map_of_comm_sq (pairActN n) (RadMat n (v1Space n U))
    (radMat_comm_sq (v1Space n U)).1 (radMat_comm_sq (v1Space n U)).2

theorem card_radV1 (U : Subgroup (PairN 5)) (hU : U ≤ V1n 5) (hr : rk ↥U = 2 ∨ rk ↥U = 3) :
    Nat.card ↥(RadV1 5 U) = 64 := by
  unfold RadV1
  rw [Subgroup.card_map_of_injective pairActN_injective]
  refine card_radMat _ ?_
  rw [finrank_v1Space_eq_rk U hU]
  exact hr

end CFSG.ASVolI.ChH
