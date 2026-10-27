module

public import CFSG.LocalAnalysis.StandardType.GGTCJDescent

public section

namespace CFSG.StandardType.TCJ

theorem ggTCJ_cover_prop {p : ℕ} {R L' : Type} [Group R] [Group L'] (ψ : L' →* R)
    (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center L') (e : MulAut L')
    (he : e ^ p = 1) (φ : MulAut R) (hφ : ∀ l : L', φ (ψ l) = ψ (e l))
    (Q : ∀ (X : Type) [Group X], Prop)
    (hQ : ∀ (X Y : Type) [Group X] [Group Y], X ≃* Y → Q X → Q Y)
    (hR : φ ^ p = 1 → ∀ K : Subgroup R, CFSG.Assembly.IsComponentOf K (ggFixSub φ) →
      Q (K ⧸ Subgroup.center K)) :
    ∀ J : Subgroup L', CFSG.Assembly.IsComponentOf J (ggFixSub e) → Q (J ⧸ Subgroup.center J) := by
  intro J hJ
  have hpow : ∀ n : ℕ, ∀ l : L', (φ ^ n) (ψ l) = ψ ((e ^ n) l) := by
    intro n
    induction n with
    | zero => intro l; simp
    | succ n ih =>
        intro l
        rw [pow_succ, MulAut.mul_apply, hφ l, ih (e l), pow_succ, MulAut.mul_apply]
  have hφp : φ ^ p = 1 := by
    ext r
    obtain ⟨l, rfl⟩ := hψ r
    have hev : (e ^ p) l = l := by simpa using congrArg (fun f : MulAut L' => f l) he
    rw [hpow p l, hev]
    rfl
  obtain ⟨hcomp, ⟨iso⟩⟩ := ggTCJ_descent ψ hψ hker e φ hφ J hJ
  exact hQ _ _ iso.symm (hR hφp (J.map ψ) hcomp)

end CFSG.StandardType.TCJ

end
