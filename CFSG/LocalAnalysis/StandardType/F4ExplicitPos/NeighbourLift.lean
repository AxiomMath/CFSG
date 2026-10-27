module

public import CFSG.LocalAnalysis.StandardType.GGSixPositionDefs

@[expose] public section

public section

open CFSG.LieType.Universal CFSG.StandardType CFSG.StandardType.S2MathFi1035Pos

namespace CFSG.StandardType.F4ExplicitPos.NeighbourLift

theorem ggRootVia_of_injective_range_lift
    {X Y : Type} [Group X] [Group Y]
    (G0 K R : Subgroup X) (hKG : K ≤ G0) (hRG : R ≤ G0)
    (η : G0 →* Y) (hη : Function.Injective η)
    (M : LieUniversal) (κ : M.K →* Y) (hκ : Function.Injective κ)
    (hκrange : κ.range = (K.subgroupOf G0).map η)
    (β : Fin M.D.rank → ℤ) (u : M.K)
    (hRbar : (R.subgroupOf G0).map η =
      ((M.D.rootGroup β).map (MulAut.conj u).toMonoidHom).map κ) :
    GGRootVia M K R β := by
  have hrange_le : κ.range ≤ η.range :=
    hκrange.symm ▸ Subgroup.map_le_range η (K.subgroupOf G0)
  have hκle : ∀ x : M.K, κ x ∈ η.range := fun x =>
    hrange_le (MonoidHom.mem_range.mpr ⟨x, rfl⟩)
  let κ' : M.K →* η.range := κ.codRestrict η.range hκle
  let φ0 : M.K →* G0 := (MonoidHom.ofInjective hη).symm.toMonoidHom.comp κ'
  have hφ0 : η.comp φ0 = κ := by
    ext x
    simp [φ0, κ']
  have hφ0inj : Function.Injective φ0 := by
    intro x y hxy
    apply hκ
    have h : (η.comp φ0) x = (η.comp φ0) y := congrArg (fun z : G0 => η z) hxy
    rwa [hφ0] at h
  have hφ0range : φ0.range = K.subgroupOf G0 := by
    apply Subgroup.map_injective (f := η) hη
    calc (φ0.range).map η = (η.comp φ0).range := (MonoidHom.range_comp η φ0).symm
      _ = κ.range := by rw [hφ0]
      _ = (K.subgroupOf G0).map η := hκrange
  let φ : M.K →* X := G0.subtype.comp φ0
  have hφrange : φ.range = K := by
    change (G0.subtype.comp φ0).range = K
    rw [MonoidHom.range_comp, hφ0range, Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hKG]
  have hφinj : Function.Injective φ := by
    intro x y hxy
    apply hφ0inj
    apply G0.subtype_injective
    simpa only [φ, MonoidHom.comp_apply] using hxy
  have hφker : φ.ker ≤ Subgroup.center M.K := by
    have hker : φ.ker = ⊥ := (MonoidHom.ker_eq_bot_iff φ).mpr hφinj
    rw [hker]
    exact bot_le
  have hmapκ :
      ((M.D.rootGroup β).map (MulAut.conj u).toMonoidHom).map κ =
        (((M.D.rootGroup β).map (MulAut.conj u).toMonoidHom).map φ0).map η := by
    rw [← hφ0, ← Subgroup.map_map]
  have hRsub : R.subgroupOf G0 =
      ((M.D.rootGroup β).map (MulAut.conj u).toMonoidHom).map φ0 := by
    apply Subgroup.map_injective (f := η) hη
    rw [hRbar, hmapκ]
  have hRG' : R = (R.subgroupOf G0).map G0.subtype := by
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hRG]
  refine ⟨φ, hφrange, hφker, u, ?_⟩
  rw [hRG', hRsub, Subgroup.map_map]
  rfl

section Pullback

variable {S T Y : Type*} [Group S] [Group T] [Group Y]

theorem comap_map_eq_and_card
    (κ : S →* Y) (hκ : Function.Injective κ) (Rbar : Subgroup Y) (hR : Rbar ≤ κ.range) :
    (Rbar.comap κ).map κ = Rbar ∧ Nat.card (Rbar.comap κ) = Nat.card Rbar := by
  have hmap : (Rbar.comap κ).map κ = Rbar := by
    rw [Subgroup.map_comap_eq, inf_eq_right.2 hR]
  refine ⟨hmap, ?_⟩
  calc Nat.card (Rbar.comap κ) = Nat.card ((Rbar.comap κ).map κ) :=
        (Subgroup.card_map_of_injective (f := κ) hκ).symm
    _ = Nat.card Rbar := by rw [hmap]

theorem comap_map_le_of_comp_injective
    (j : S →* T) (Λ : T →* Y) (hΛ : Function.Injective Λ) (κ : S →* Y)
    (hκ : κ = Λ.comp j) (Rbar : Subgroup Y) (Q : Subgroup T) (hR : Rbar ≤ Q.map Λ) :
    (Rbar.comap κ).map j ≤ Q := by
  rintro x ⟨s, hs, rfl⟩
  have hmem : κ s ∈ Q.map Λ := hR hs
  rw [show κ s = Λ (j s) from by rw [hκ]; rfl] at hmem
  exact (Subgroup.mem_map_iff_mem (f := Λ) hΛ).1 hmem

end Pullback

end CFSG.StandardType.F4ExplicitPos.NeighbourLift

end

end
