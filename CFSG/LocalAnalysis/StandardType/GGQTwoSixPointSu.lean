module

public import CFSG.LocalAnalysis.StandardType.GGQTwoSixPointNative
public import CFSG.LocalAnalysis.StandardType.GGQTwoSUOrder

public section

namespace CFSG.StandardType.QTwo.SixPoint

open CFSG.ClassicalInvolution.Phan
open CFSG.GH74.Uniqueness.SU.SU5 (F4c)

@[expose] def evalG {X : Type} [Group X] (g : Fin 18 → X) (w : List (Fin 18 × Bool)) : X :=
  (w.map fun p => cond p.2 (g p.1) (g p.1)⁻¹).prod

section Native

variable {K : Type} [Field K] [Finite K] [CharP K 2]

noncomputable def f4cEmb (hK : Nat.card K = 4) : F4c →+* K := by
  classical
  letI : Fintype K := Fintype.ofFinite K
  exact (FiniteField.ringEquivOfCardEq (K := F4c) (K' := K) (by
    rw [F4c.card_eq, Fintype.card_eq_nat_card]; exact hK.symm)).toRingHom

noncomputable def nativeGL (hK : Nat.card K = 4) (i : Fin 18) : GL (Fin 6) K :=
  ⟨(nativeGen i).map (f4cEmb hK), (nativeInv i).map (f4cEmb hK),
    by rw [← Matrix.map_mul, nativeGen_mul_nativeInv, Matrix.map_one _ (map_zero _) (map_one _)],
    by rw [← Matrix.map_mul, nativeInv_mul_nativeGen, Matrix.map_one _ (map_zero _) (map_one _)]⟩

noncomputable def nativeSu (hK : Nat.card K = 4) (i : Fin 18) : Su K 2 1 6 :=
  ⟨nativeGL hK i, by
    refine ⟨?_, ?_⟩
    · show ((nativeGen i).map (f4cEmb hK)).det = 1
      rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, nativeGen_det, map_one]
    · show CFSG.LieType.Universal.Unitary.conjTr (CFSG.LieType.BorelTits.unitaryInvolution K 2 1)
        ((nativeGen i).map (f4cEmb hK)) * (nativeGen i).map (f4cEmb hK) = 1
      have h : CFSG.LieType.Universal.Unitary.conjTr (CFSG.LieType.BorelTits.unitaryInvolution K 2 1)
          ((nativeGen i).map (f4cEmb hK)) = (nativeInv i).map (f4cEmb hK) := by
        ext a b
        simp only [CFSG.LieType.Universal.Unitary.conjTr, nativeInv, Matrix.transpose_apply,
          Matrix.map_apply, CFSG.LieType.BorelTits.unitaryInvolution_apply, pow_one]
        rw [← map_pow]
        exact congrArg _ (sq _)
      rw [h, ← Matrix.map_mul, nativeInv_mul_nativeGen, Matrix.map_one _ (map_zero _) (map_one _)]⟩

theorem coe_evalG_nativeSu (hK : Nat.card K = 4) (w : List (Fin 18 × Bool)) :
    (((evalG (nativeSu hK) w : Su K 2 1 6) : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) =
      (evalNative w).map (f4cEmb hK) := by
  induction w with
  | nil =>
    simp only [evalG, evalNative, List.map_nil, List.prod_nil]
    rw [Matrix.map_one _ (map_zero _) (map_one _)]
    rfl
  | cons p w ih =>
    obtain ⟨i, b⟩ := p
    simp only [evalG, evalNative, List.map_cons, List.prod_cons] at ih ⊢
    rw [Matrix.map_mul, ← ih]
    cases b
    · show ((((nativeSu hK i)⁻¹ * (w.map fun p => cond p.2 (nativeSu hK p.1) (nativeSu hK p.1)⁻¹).prod :
        Su K 2 1 6) : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) = _
      rfl
    · rfl

theorem nativeSu_rels (hK : Nat.card K = 4) : ∀ w ∈ relsP, evalG (nativeSu hK) w = 1 := by
  intro w hw
  apply Subtype.ext
  apply Units.ext
  rw [coe_evalG_nativeSu, nativeRels w hw, Matrix.map_one _ (map_zero _) (map_one _)]
  rfl

theorem nativeSu_comm (hK : Nat.card K = 4) :
    ∀ a ∈ ([10, 11] : List (Fin 18)), ∀ b ∈ ([16, 17] : List (Fin 18)),
      nativeSu hK a * nativeSu hK b = nativeSu hK b * nativeSu hK a := by
  intro a ha b hb
  apply Subtype.ext
  apply Units.ext
  have h := nativeComm_edge_one_four a ha b hb
  show ((nativeGen a).map (f4cEmb hK)) * ((nativeGen b).map (f4cEmb hK)) =
    ((nativeGen b).map (f4cEmb hK)) * ((nativeGen a).map (f4cEmb hK))
  rw [← Matrix.map_mul, ← Matrix.map_mul, h]

end Native

end CFSG.StandardType.QTwo.SixPoint

end
