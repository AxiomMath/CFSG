module

public import CFSG.LocalAnalysis.StandardType.GGQTwoRationalWeyl
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.TypeASplitConj

public section

namespace CFSG.StandardType.QTwoCav

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Chevalley.RootTorus CFSG.StandardType.LangRat
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.PartOne.KE CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.Proving
open scoped commutatorElement MatrixGroups


variable {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p : ℕ} (S : LangSetup τ L p)

theorem exists_split_source_perfect_of_frame_of_rho
    {ν : ℕ} {ψ : SL(ν, L) →* ModGL τ L} {σ : Fin ν → Fin ν → Fin τ.rank → ℤ}
    (hν : 3 ≤ ν) (hψ : IsSLFrame ψ σ) (π : Equiv.Perm (Fin ν))
    (hπ : ∀ x y, x ≠ y → S.ρ (σ x y) = σ (π x) (π y))
    {k' : Type} [Field k'] [Finite k'] [Algebra k' L] [IsAlgClosure k' L]
    {r e : ℕ} (hr : r.Prime) [CharP L r] (he : 0 < e) (hq : S.D.q = r ^ e) :
    ∃ F' : SL(ν, L) →* SL(ν, L),
      (∀ X, S.D.step (ψ X) = ψ (F' X)) ∧
        Group.IsPerfect (F'.eqLocus (MonoidHom.id _)) := by
  classical
  have : Fact r.Prime := ⟨hr⟩
  obtain ⟨σQ, hσQ⟩ := exists_ringEquiv_frob (L := L) r e
  have hσc : ∀ c, σQ c = c ^ (r ^ e) := by
    intro c
    have h1 : σQ c = iterateFrobenius L r e c := by
      rw [← hσQ]
      rfl
    rw [h1, iterateFrobenius_def]
  have hσc' : ∀ c, σQ c = c ^ (r ^ (e * 1)) := by
    intro c
    rw [Nat.mul_one]
    exact hσc c
  obtain ⟨B, hstd⟩ := CFSG.HardMathSupport.Solomon.Coordinator.LieComp.split_exists_pin
    S (s := 1) hν hψ π (fun x y hxy => by simpa [Function.iterate_one] using hπ x y hxy)
      hq hσc'
  have hstd1 : ∀ X : SL(ν, L),
      ψ B * S.D.step (ψ X) * (ψ B)⁻¹ =
        ψ (Matrix.SpecialLinearGroup.map σQ.toRingHom X) := fun X => by
    simpa [iterHom_eq_iterate, Function.iterate_one] using hstd X
  have hB : ∀ X : SL(ν, L),
      S.D.step (ψ X) = ψ (B⁻¹ * Matrix.SpecialLinearGroup.map σQ.toRingHom X * B) := by
    intro X
    calc S.D.step (ψ X)
        = (ψ B)⁻¹ * (ψ B * S.D.step (ψ X) * (ψ B)⁻¹) * ψ B := by group
      _ = (ψ B)⁻¹ * ψ (Matrix.SpecialLinearGroup.map σQ.toRingHom X) * ψ B := by
            rw [hstd1 X]
      _ = ψ (B⁻¹ * Matrix.SpecialLinearGroup.map σQ.toRingHom X * B) := by
            rw [map_mul, map_mul, map_inv]
  let A : GL (Fin ν) L := Matrix.SpecialLinearGroup.toGL B⁻¹
  let F' : SL(ν, L) →* SL(ν, L) :=
    (CFSG.RankThree.Classical2.conjSLn A).comp
      (Matrix.SpecialLinearGroup.map σQ.toRingHom)
  have hF' : ∀ X, F' X = B⁻¹ * Matrix.SpecialLinearGroup.map σQ.toRingHom X * B := by
    intro X
    simp only [F', MonoidHom.comp_apply]
    rw [CFSG.RankThree.Classical2.conjSLn_toGL]
    simp
  refine ⟨F', ?_, ?_⟩
  · intro X
    rw [hF' X]
    exact hB X
  · have hQ := CFSG.RankThree.Classical2.isQuasisimple_eqLocus_conjSLn_frobenius_split
      (k' := k') (Ω := L) (n := ν) (ℓ := r) (f := e) hr he (by omega)
      (Or.inl (by omega)) σQ.toRingHom hσc A
    simpa [F', A] using hQ.2.1

end CFSG.StandardType.QTwoCav

end
