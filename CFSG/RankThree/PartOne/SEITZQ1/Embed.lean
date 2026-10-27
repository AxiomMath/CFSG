module

public import CFSG.RankThree.PartOne.SEITZQ1.Conj

public noncomputable section

namespace CFSG.RankThree.PartOne.SEITZQ1

open Matrix CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.RankThree.PartOne.KF4 CFSG.RankThree.PartOne.KLR CFSG.ClassicalGroups.UnitaryFlag
open scoped MatrixGroups

section Hom

variable {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime] {a : ℕ}
  {L : Type} [Field L] [Algebra K L] [IsAlgClosure K L] [CharP L 2]

omit [IsAlgClosure K L] [CharP L 2] in
theorem frq_eq_pow (D : ReeFrameData K L a) (hK : Nat.card K = 2 ^ (2 * a + 1)) (c : L) :
    D.Frq c = c ^ 2 ^ (2 * a + 1) := by
  rw [D.Frq_pow, hK]

theorem q1_exists_hom (D : ReeFrameData K L a) (hK : Nat.card K = 2 ^ (2 * a + 1)) {ω : L}
    (hω : ω ^ 2 + ω + 1 = 0) {G₀ : Type*} [Group G₀] (j : G₀ →* SL(3, L))
    (hj : ∀ x, q1Tr D.Frq (j x) = j x) :
    ∃ Ψ : G₀ →* ReeTag.F4.reeGamma K a, ∀ x,
      thetaGamma L a (Ψ x) = q1C ω * q1Psi0 D.isFrob (j x) * (q1C ω)⁻¹ := by
  classical
  have hθ : ∀ x, ∃ γ : ReeTag.F4.reeGamma K a,
      thetaGamma L a γ = q1C ω * q1Psi0 D.isFrob (j x) * (q1C ω)⁻¹ := by
    intro x
    obtain ⟨hadj, hfix⟩ := fixed_of_mem_twistedFixed D.F (q1C_mem_adjoint ω)
      (q1C_fext D.isFrob hω)
      (q1Psi0_mem_twistedFixed D.isFrob D.Frq (frq_eq_pow D hK) (hj x))
    exact D.exists_theta_of_fixed hadj hfix
  choose ψ hψ using hθ
  have hinjθ := thetaGamma_injective (K := K) L (a := a)
  refine ⟨{ toFun := ψ
            map_one' := by
              apply hinjθ
              simp only [hψ, map_one, mul_one, mul_inv_cancel]
            map_mul' := fun x y => by
              apply hinjθ
              rw [map_mul (thetaGamma L a) (ψ x) (ψ y), hψ (x * y), hψ x, hψ y, map_mul j x y,
                map_mul]
              group }, fun x => hψ x⟩

end Hom

section Unitary

open CFSG.LocalAnalysis.ComponentInitial

variable {f : ℕ} {K' : Type} [Field K'] {L : Type} [Field L]

@[expose] def q1SUToSL (h : UnitaryFieldData 2 f K') (ι : K' →+* L) :
    unitarySU 2 f K' 3 →* SL(3, L) :=
  (Matrix.SpecialLinearGroup.map ι).comp
    { toFun g := ⟨((g : GL (Fin 3) K') : Matrix (Fin 3) (Fin 3) K'), ((mem_unitarySU_iff h).1 g.2).1⟩
      map_one' := Subtype.ext rfl
      map_mul' _ _ := Subtype.ext rfl }

theorem coe_q1SUToSL (h : UnitaryFieldData 2 f K') (ι : K' →+* L) (g : unitarySU 2 f K' 3) :
    ((q1SUToSL h ι g : SL(3, L)) : Matrix (Fin 3) (Fin 3) L) =
      ((g : GL (Fin 3) K') : Matrix (Fin 3) (Fin 3) K').map ι :=
  rfl

theorem q1SUToSL_fixed (h : UnitaryFieldData 2 f K') (ι : K' →+* L) (Fr : L →+* L)
    (hFr : ∀ c, Fr (ι c) = ι (h.bar c)) (g : unitarySU 2 f K' 3) :
    q1Tr Fr (q1SUToSL h ι g) = q1SUToSL h ι g := by
  have hu := ((mem_unitarySU_iff h).1 g.2).2
  rw [q1Tr_apply, inv_eq_iff_mul_eq_one]
  refine Subtype.ext ?_
  change ((Matrix.SpecialLinearGroup.map Fr (q1SUToSL h ι g) : SL(3, L)) :
      Matrix (Fin 3) (Fin 3) L)ᵀ * ((q1SUToSL h ι g : SL(3, L)) : Matrix (Fin 3) (Fin 3) L) = 1
  have e1 : ((Matrix.SpecialLinearGroup.map Fr (q1SUToSL h ι g) : SL(3, L)) :
      Matrix (Fin 3) (Fin 3) L)ᵀ =
      ((((g : GL (Fin 3) K') : Matrix (Fin 3) (Fin 3) K').map h.bar)ᵀ).map ι := by
    ext i j
    simp [coe_q1SUToSL, hFr]
  rw [e1, coe_q1SUToSL, ← Matrix.map_mul, hu, Matrix.map_one ι ι.map_zero ι.map_one]

end Unitary

end CFSG.RankThree.PartOne.SEITZQ1
