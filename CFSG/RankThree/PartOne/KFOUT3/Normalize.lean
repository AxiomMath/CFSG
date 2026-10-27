module

public import CFSG.RankThree.PartOne.KFOUT3.Std
public import CFSG.RankThree.PartOne.KFOUT3.Cocycle

public section

namespace CFSG.RankThree.PartOne.KFOUT3

variable {K : Type} [Field K] [CharP K 2] [Finite K]

theorem exists_std_normalization {p : ℕ} {ζ : Kˣ} (hζ : IsZeta p ζ) (Ψ : PSL3 K ≃* PSL3 K)
    (hT : ∀ t, t ∈ Tbar p K ↔ Ψ t ∈ Tbar p K) :
    ∃ (π : Equiv.Perm (Fin 3)) (ε : Bool) (d : Fin 3 → Kˣ) (σ : K ≃+* K), ∀ x : SL3 K,
      Ψ (QuotientGroup.mk x) =
        cPerm π (gammaPow ε (QuotientGroup.mk (stdHom (KFU.diagU d) σ x))) := by
  obtain ⟨ρ, hρcomm, hρ⟩ := exists_hexagon_aut_of_roots (K := K) (T := Tbar p K) RB
    (isRoot_iff hζ) (fun b b' s s' hs hs' => commute_RB_iff b b' hs hs') Ψ hT
  obtain ⟨π, ε, hπε⟩ := hexagon_aut ρ hρcomm
  let Ψ'' : PSL3 K ≃* PSL3 K := Ψ.trans ((cPerm π⁻¹).trans (gammaPow ε))
  have hΨ'' : ∀ u, Ψ'' u = gammaPow ε (cPerm π⁻¹ (Ψ u)) := fun u => rfl
  have hroot : ∀ (i j : Fin 3) (h : i ≠ j) (s : K),
      ∃ t, Ψ'' (QuotientGroup.mk (rt h s)) = QuotientGroup.mk (rt h t) := by
    intro i j h s
    by_cases hs : s = 0
    · refine ⟨0, ?_⟩
      subst hs
      rw [rt_zero, QuotientGroup.mk_one, map_one]
    · obtain ⟨s', hs', hΨ⟩ := hρ ⟨(i, j), h⟩ s hs
      refine ⟨s', ?_⟩
      show Ψ'' (RB ⟨(i, j), h⟩ s) = RB ⟨(i, j), h⟩ s'
      rw [hΨ'', hΨ, hπε]
      cases ε
      · rw [rho_false, cPerm_RB, permB_permB]
        rfl
      · rw [rho_true, cPerm_RB, permB_permB, gammaPow_RB]
        rfl
  obtain ⟨d, σ, hD⟩ := std_of_root_stable Ψ'' hroot
  refine ⟨π, ε, d, σ, fun x => ?_⟩
  rw [← hD x, hΨ'', gammaPow_gammaPow, cPerm_cPerm_inv]

end CFSG.RankThree.PartOne.KFOUT3
