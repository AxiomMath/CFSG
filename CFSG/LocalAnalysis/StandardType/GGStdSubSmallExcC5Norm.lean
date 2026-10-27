module

public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallExcC5Trans
public import CFSG.Sporadic.Schreier.J4SProfileNode

public section

namespace CFSG.StandardType.SmallExc

open CFSG.Assembly TableB

section Norm

variable {p : ℕ} {G0 : Type} [Group G0]

theorem ggStdSubTwoTorusNormSmall_of_count {r : ℕ} {R : Type} [Group R] {I : Set (MulAut R)}
    (ε : R ≃* G0) (hZ : Subgroup.center G0 = ⊥)
    (hI : ∀ φ ∈ I, MulAut.congr ε φ ∈ Set.range (MulAut.conj : G0 →* MulAut G0))
    (hclosed : ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R), Function.Surjective ψ →
      ψ.ker ≤ Subgroup.center L' → commutator L' = ⊤ → ψ.ker = ⊥)
    (hcount : ∀ B : Subgroup G0, IsElemAbelian p B → p ^ r ≤ Nat.card B →
      NormalizesTwoGroup B → ∀ x ∈ B, x ≠ 1 → NodeCount p B x) :
    GGStdSubTwoTorusNormSmall p r R I := by
  intro L' _ _ ψ hψ hker hperf A hA hAI hr h3 hNorm a₀ ha₀ ha₀1 hcomp hcent hsmall
  exfalso
  have hψinj : Function.Injective ψ := (MonoidHom.ker_eq_bot_iff ψ).1 (hclosed L' ψ hψ hker hperf)
  let θ : L' ≃* G0 := (MulEquiv.ofBijective ψ ⟨hψinj, hψ⟩).trans ε
  refine false_of_count θ hZ hA ?_ ?_ ha₀ ha₀1 hcomp hcent hsmall ?_
  · intro a ha
    obtain ⟨φ, hφ, hφa⟩ := hAI a ha
    have h1 : MulAut.congr θ a = MulAut.congr ε φ := by
      ext x
      obtain ⟨l, rfl⟩ := θ.surjective x
      have h3 : MulAut.congr θ a (θ l) = θ (a l) := by simp [MulAut.congr_apply]
      have h4 : MulAut.congr ε φ (ε (ψ l)) = ε (φ (ψ l)) := by simp [MulAut.congr_apply]
      rw [h3]
      change _ = MulAut.congr ε φ (ε (ψ l))
      rw [h4, hφa l]
      rfl
    rw [h1]
    exact hI φ hφ
  · obtain ⟨U, hU1, hU2, hUA⟩ := hNorm
    refine ⟨U.comap ψ, ?_, hU2.comap_of_injective ψ hψinj, fun a ha u hu => hUA a ha u hu⟩
    intro h
    apply hU1
    rw [eq_bot_iff]
    intro u hu
    obtain ⟨l, rfl⟩ := hψ u
    have h1 : l ∈ U.comap ψ := hu
    rw [h, Subgroup.mem_bot] at h1
    rw [h1, map_one]
    exact Subgroup.one_mem _
  · intro B hB hBc hB2 x hx hx1
    exact hcount B hB (by rw [hBc]; exact hr) hB2 x hx hx1


end Norm

end CFSG.StandardType.SmallExc

end
