module

public import CFSG.LocalAnalysis.UniquenessCase.Lie.Cover

public section

namespace CFSG.StandardType

theorem ggExists_universal_cover_of_marking {X U : Type} [Group X] [Group U] [Finite X]
    [Finite U] (hX : commutator X = ⊤)
    (hiso : Nonempty (X ⧸ Subgroup.center X ≃* U ⧸ Subgroup.center U))
    (hsplit : ∀ (E : Type) [Group E] [Finite E] (π : E →* U), Function.Surjective π →
      π.ker ≤ Subgroup.center E → ∃ s : U →* E, π.comp s = MonoidHom.id U) :
    ∃ ψ : U →* X, Function.Surjective ψ ∧ ψ.ker ≤ Subgroup.center U := by
  obtain ⟨φ⟩ := hiso
  let π : X →* U ⧸ Subgroup.center U :=
    φ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center X))
  have hπ : Function.Surjective π := fun q => by
    obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective (φ.symm q)
    refine ⟨x, ?_⟩
    change φ (x : X ⧸ Subgroup.center X) = q
    rw [hx, MulEquiv.apply_symm_apply]
  have hπc : π.ker ≤ Subgroup.center X := by
    intro x hx
    change φ (x : X ⧸ Subgroup.center X) = 1 at hx
    exact (QuotientGroup.eq_one_iff x).mp (φ.map_eq_one_iff.mp hx)
  obtain ⟨ψ, hψ, hker, -⟩ :=
    CFSG.LocalAnalysis.UniquenessCase.UC22.uc22pwlie_exists_cover_of_closed_fin
      (fun E _ _ p hp hpc => (hsplit E p hp hpc).imp fun s hs g => DFunLike.congr_fun hs g)
      hX π hπ hπc (QuotientGroup.mk' (Subgroup.center U))
      (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _).le
  exact ⟨ψ, hψ, hker⟩

end CFSG.StandardType

end
