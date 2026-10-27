module

public import CFSG.Quasithin.Vol2.GoldschmidtF431D4F48Equiv

public noncomputable section

namespace CFSG.Quasithin.D4Hex

open CFSG.Quasithin CFSG.Quasithin.TitsGeo CFSG.Quasithin.H13.F48Gen
  CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion

section Kappa

variable (S : LieSetting.{0, 0}) (κ : Pt S.ι ≃ Fin 819) (ρ₁ : S.α.G1 →* Equiv.Perm (Fin 819))
  (ρ₂ : S.α.G2 →* Equiv.Perm (Fin 819)) (lay : Array ℕ)
  (hκ1 : ∀ (y : S.α.G1) (z : Pt S.ι), κ (f1 (c := S.ι) y • z) = ρ₁ y (κ z))
  (hκ2 : ∀ (q : S.α.G2) (z : Pt S.ι), κ (f2 (c := S.ι) q • z) = ρ₂ q (κ z))
  (hκnear : ∀ z : Pt S.ι, Near S.m S.ι z ↔ lay[(κ z : ℕ)]! ≤ 4)

include hκ1 hκ2 hκnear in
theorem ptRigid_of_fin {n : S.α.G1} {q : S.α.G2} {M : ℕ}
    (R : ∀ π' : S.α.G1 →* Equiv.Perm (Fin 819),
      (∀ x : S.α.G12, π' (S.α.α1 x) = ρ₁ (S.α.α1 x)) →
      (∀ (y : S.α.G1) (p : Fin 819), lay[(p : ℕ)]! ≤ 4 → π' y p = ρ₁ y p) →
      (π' n * ρ₂ q) ^ M = 1 → ∀ y, π' y = ρ₁ y) : PtRigid S n q M := by
  intro π hB hN hX p z
  let π' : S.α.G1 →* Equiv.Perm (Fin 819) := (titsPermConj κ).comp π
  have hπ' : ∀ y m, π' y m = κ (π y (κ.symm m)) := fun _ _ => rfl
  have hB' : ∀ x : S.α.G12, π' (S.α.α1 x) = ρ₁ (S.α.α1 x) := by
    intro x
    refine Equiv.ext fun m => ?_
    rw [hπ', hB x (κ.symm m), hκ1, Equiv.apply_symm_apply]
  have hN' : ∀ (y : S.α.G1) (m : Fin 819), lay[(m : ℕ)]! ≤ 4 → π' y m = ρ₁ y m := by
    intro y m hm
    have hz : Near S.m S.ι (κ.symm m) := (hκnear _).2 (by rw [Equiv.apply_symm_apply]; exact hm)
    rw [hπ', hN y _ hz, hκ1, Equiv.apply_symm_apply]
  have hX' : (π' n * ρ₂ q) ^ M = 1 := by
    have h2 : titsPermConj κ (MulAction.toPerm (f2 (c := S.ι) q)) = ρ₂ q := by
      refine Equiv.ext fun m => ?_
      rw [titsPermConj_apply, MulAction.toPerm_apply, hκ2, Equiv.apply_symm_apply]
    have := congrArg (titsPermConj κ) hX
    rw [map_pow, map_mul, h2, map_one] at this
    exact this
  have h3 := R π' hB' hN' hX' p
  have h4 := congrArg (fun σ : Equiv.Perm (Fin 819) => σ (κ z)) h3
  apply κ.injective
  calc κ (π p z) = π' p (κ z) := by
        show _ = κ (π p (κ.symm (κ z)))
        rw [Equiv.symm_apply_apply]
    _ = ρ₁ p (κ z) := h4
    _ = κ (f1 (c := S.ι) p • z) := (hκ1 p z).symm

end Kappa

section Equivariant

variable (S : LieSetting.{0, 0}) (κ : Pt S.ι ≃ Fin 819) (ρ₀ : S.ι.G0 →* Equiv.Perm (Fin 819))
  (hκ : ∀ (g : S.ι.G0) (z : Pt S.ι), κ (g • z) = ρ₀ g (κ z))

include hκ in
theorem toPerm_injective_of_kappa (hρ₀ : Function.Injective ρ₀) :
    Function.Injective (MulAction.toPermHom S.ι.G0 (Pt S.ι)) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  apply hρ₀
  rw [map_one]
  refine Equiv.ext fun m => ?_
  obtain ⟨z, rfl⟩ := κ.surjective m
  have h2 := congrArg (fun σ : Equiv.Perm (Pt S.ι) => σ z) hg
  simp only [MulAction.toPermHom_apply, MulAction.toPerm_apply, Equiv.Perm.one_apply] at h2
  rw [← hκ, h2]
  rfl

include hκ in
theorem fix_of_kappa
    (h819 : ∀ w : Fin 819, (∀ b ∈ stv S.ι S.ι.xv ⊓ stv S.ι S.ι.lv, ρ₀ b w = w) →
      w = κ ((1 : S.ι.G0) : Pt S.ι)) :
    ∀ v : S.ι.Γ, CosetGeom.vtype v = false →
      (∀ b ∈ stv S.ι S.ι.xv ⊓ stv S.ι S.ι.lv, b • v = v) → v = S.ι.xv := by
  intro v hv hfix
  rcases v with w | w
  swap
  · simp [CosetGeom.vtype] at hv
  have hw : κ w = κ ((1 : S.ι.G0) : Pt S.ι) := by
    refine h819 _ fun b hb => ?_
    have h1 := hfix b hb
    rw [CosetGeom.smul_inl] at h1
    have h2 : b • w = w := Sum.inl_injective h1
    rw [← hκ, h2]
  have := κ.injective hw
  rw [this]
  rfl

end Equivariant

end CFSG.Quasithin.D4Hex
