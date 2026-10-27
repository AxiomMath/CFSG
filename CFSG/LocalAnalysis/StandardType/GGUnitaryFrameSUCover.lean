module

public import CFSG.LocalAnalysis.StandardType.GGTwE6A5KModelRat
public import CFSG.LocalAnalysis.StandardType.GGTwE6A5KModelTheta
import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24ConnGenFrame
import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.InnExcSuNHom
import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24CentreHom
import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24ConnGenPin
import CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQThreeE6FourCore

public section

namespace CFSG.StandardType.SCFourCover

open CFSG.Open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.RankThree.Classical2
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three
open scoped MatrixGroups


theorem exists_suCover_of_unitary_frame {τ : Tag} {L : Type} [Field L] [IsAlgClosed L]
    {p : ℕ} (S : LangSetup τ L p) {a : Fin τ.rank → Lˣ}
    (hT : rootDiagUnit τ a ∈ S.D.torus) (i : KernelComponent (rootCharHom a)) {ν : ℕ}
    {ψ : SL(ν, L) →* ModGL τ L} {σ' : Fin ν → Fin ν → Fin τ.rank → ℤ}
    (hψ : IsSLFrame ψ σ') (hΨ : componentRoots (rootCharHom a) i = frameRoots σ')
    (π : Equiv.Perm (Fin ν)) (hπ : ∀ x y, x ≠ y → S.ρ (σ' x y) = σ' (π y) (π x))
    {r e : ℕ} (hr : r.Prime) [CharP L r] (he : 0 < e) (hq : S.D.q = r ^ e)
    (hν : 3 ≤ ν) (hνq : (ν, r ^ e) ≠ (3, 2)) {L' : Type} [Group L'] {J : Subgroup L'}
    {ι : L' →* ModGL τ L} (hι : Function.Injective ι)
    (hJ : J.map ι = rationalComponent S.ρ S.Γ (rootCharHom a) i) :
    ∃ (z : ModGL τ L) (W : GL (Fin ν) L), z ∈ adjointGroup τ L ∧
      (∀ X, z * ψ X * z⁻¹ = ψ (conjSLn W X)) ∧
      ∃ F : Subfield L, Nat.card F = (r ^ e) ^ 2 ∧ (∀ c, c ∈ F ↔ c ^ (r ^ e) ^ 2 = c) ∧
        ∃ (Φ : StatedSU ν (r ^ e) F →* J)
          (θ : ↥J ⧸ Subgroup.center ↥J ≃* LargeEvenProj (LargeEvenSUGroup (Fin ν) F (r ^ e))),
          (∀ s, ι (Φ s) = z * ψ (statedSUToSL F ν (r ^ e) s) * z⁻¹) ∧
          (∀ s, θ (QuotientGroup.mk (Φ s)) =
            LargeEvenProjMk (LargeEvenSUGroup (Fin ν) F (r ^ e)) s) ∧
          Function.Surjective Φ ∧ Φ.ker ≤ Subgroup.center (StatedSU ν (r ^ e) F) := by
  obtain ⟨σQ, z, W, hσQ, hzC, hW, hR⟩ := rationalComponent_eq_conj_fix_of_unitary_frame S hT i
    hψ hΨ π hπ hr inferInstance he hq hν hνq
  obtain ⟨F, hF, hFmem, Φ, θ, hΦ, hθ, hsurj, hker⟩ := exists_psu_equiv_of_conj_frame hr he
    (fun c => by rw [hσQ, hq]) hν hνq (KSGen.frame_ker_le_center hν hψ) z hι
    (fun g => by rw [hJ]; exact hR g)
  exact ⟨z, W, hzC, hW, F, hF, hFmem, Φ, θ, hΦ, hθ, hsurj, hker⟩

theorem exists_suCover_of_unitary_frame_of_neg {τ : Tag} {L : Type} [Field L] [IsAlgClosed L]
    {p : ℕ} (S : LangSetup τ L p) (hρ : ∀ γ, S.ρ γ = -γ) {a : Fin τ.rank → Lˣ}
    (hT : rootDiagUnit τ a ∈ S.D.torus) (i : KernelComponent (rootCharHom a)) {ν : ℕ}
    {ψ : SL(ν, L) →* ModGL τ L} {σ' : Fin ν → Fin ν → Fin τ.rank → ℤ}
    (hψ : IsSLFrame ψ σ') (hΨ : componentRoots (rootCharHom a) i = frameRoots σ')
    {r e : ℕ} (hr : r.Prime) [CharP L r] (he : 0 < e) (hq : S.D.q = r ^ e)
    (hν : 3 ≤ ν) (hνq : (ν, r ^ e) ≠ (3, 2)) {L' : Type} [Group L'] {J : Subgroup L'}
    {ι : L' →* ModGL τ L} (hι : Function.Injective ι)
    (hJ : J.map ι = rationalComponent S.ρ S.Γ (rootCharHom a) i) :
    ∃ (z : ModGL τ L) (W : GL (Fin ν) L), z ∈ adjointGroup τ L ∧
      (∀ X, z * ψ X * z⁻¹ = ψ (conjSLn W X)) ∧
      ∃ F : Subfield L, Nat.card F = (r ^ e) ^ 2 ∧ (∀ c, c ∈ F ↔ c ^ (r ^ e) ^ 2 = c) ∧
        ∃ (Φ : StatedSU ν (r ^ e) F →* J)
          (θ : ↥J ⧸ Subgroup.center ↥J ≃* LargeEvenProj (LargeEvenSUGroup (Fin ν) F (r ^ e))),
          (∀ s, ι (Φ s) = z * ψ (statedSUToSL F ν (r ^ e) s) * z⁻¹) ∧
          (∀ s, θ (QuotientGroup.mk (Φ s)) =
            LargeEvenProjMk (LargeEvenSUGroup (Fin ν) F (r ^ e)) s) ∧
          Function.Surjective Φ ∧ Φ.ker ≤ Subgroup.center (StatedSU ν (r ^ e) F) :=
  exists_suCover_of_unitary_frame S hT i hψ hΨ 1
    (fun x y _ => by
      simp only [hρ, Equiv.Perm.one_apply]
      exact (hψ.neg x y).symm) hr he hq hν hνq hι hJ

end CFSG.StandardType.SCFourCover

end
