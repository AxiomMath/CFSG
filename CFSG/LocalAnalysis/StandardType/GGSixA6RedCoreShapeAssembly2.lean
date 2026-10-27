module

public import CFSG.LocalAnalysis.StandardType.GGSixA6RedCoreShapeAssembly
public import CFSG.LocalAnalysis.StandardType.GGSixA6RedCoreShapeGL

public section

namespace CFSG.StandardType.A6Red.CoreShape

open Matrix CFSG.StandardType.LayerCores

theorem exists_coreFamily_unitaryOf_lie {r : ℕ} {D : Fin r → Type} [∀ i, Field (D i)]
    {d : Fin r → ℕ} [∀ i, NeZero (d i)] {τ : PiMat D d → PiMat D d}
    (hHerm : HermCoreInputLie) (hAlt : AltCoreInputLie)
    [∀ i, Finite (D i)] [∀ i, CharP (D i) 2] (hτ : IsInvol τ) (hy : ∃ y, y + τ y = 1)
    (hbig : ∀ b : Fin r, τ (piE D d b) = piE D d b →
      (∀ c : D b, tauFix τ b (Matrix.scalar (Fin (d b)) c) = Matrix.scalar (Fin (d b)) c) →
        4 ≤ Nat.card (D b)) :
    ∃ (β : Type) (S : β → Subgroup (PiMat D d)ˣ), IsCoreFamily (unitaryOf hτ) S ∧
      ∀ c, GGA6CharTwoLie ↥(S c) := by
  obtain ⟨π, hπ⟩ := hτ.exists_perm
  have hfix : ∀ b (hb : π b = b), HasCoreLie (matUnitary (isInvol_tauFix hτ hπ hb)) := by
    intro b hb
    by_cases hk : ∀ c : D b, tauFix τ b (Matrix.scalar (Fin (d b)) c) =
        Matrix.scalar (Fin (d b)) c
    · obtain ⟨Y, hY⟩ := hy
      refine hAlt (D b) (d b) (tauFix τ b) (isInvol_tauFix hτ hπ hb) hk ⟨Y b, ?_⟩
        (hbig b ?_ hk)
      · have h1 := congrFun hY b
        rwa [Pi.add_apply, apply_tau_eq_tauFix hτ hπ hb, Pi.one_apply] at h1
      · rw [hπ b, hb]
    · push Not at hk
      exact hHerm (D b) (d b) (tauFix τ b) (isInvol_tauFix hτ hπ hb) hk
  exact exists_core_of_factors_lie hτ hπ hfix (fun b _ => hasCoreLie_top_GL (d b))

end CFSG.StandardType.A6Red.CoreShape

end
