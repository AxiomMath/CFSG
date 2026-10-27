module

public import CFSG.Quasithin.Vol2.TwoF4F48Model
public import CFSG.Quasithin.Vol2.TwoF4F48Fin

public section

namespace CFSG.Quasithin.H13.TwoF4F48

open CFSG.Quasithin CFSG.Sporadic.Schreier.Tits CFSG.RuF45 CFSG.Quasithin.RuType
  CFSG.Quasithin.H13.F45Ru CFSG.Quasithin.H13.F48Gen CFSG.Monster.B.Co2
  CFSG.Monster.B.Co2.Native CFSG.TwoF4F48 CFSG.Quasithin.RankTwoAmalgam.Completion

@[expose] def permConj {X Z : Type*} (e : X ≃ Z) : Equiv.Perm X →* Equiv.Perm Z where
  toFun σ := e.permCongr σ
  map_one' := by ext; simp [Equiv.permCongr_apply]
  map_mul' a b := by ext; simp [Equiv.permCongr_apply]

theorem permConj_apply {X Z : Type*} (e : X ≃ Z) (σ : Equiv.Perm X) (z : Z) :
    permConj e σ z = e (σ (e.symm z)) := rfl

section Rig


theorem kappa_f1 (y : ↥twoF4H) (w : Pt twoF4Setting.ι) :
    twoF4Kappa (f1 (c := twoF4Setting.ι) y • w) = (y : Equiv.Perm (Fin 1755)) (twoF4Kappa w) := by
  rw [kappa_smul]
  rfl

theorem kappa_f2 (q : ↥twoF4N) (w : Pt twoF4Setting.ι) :
    twoF4Kappa (f2 (c := twoF4Setting.ι) q • w) = (q : Equiv.Perm (Fin 1755)) (twoF4Kappa w) := by
  rw [kappa_smul]
  rfl

theorem twoF4_rigid_pt (π : twoF4Setting.α.G1 →* Equiv.Perm (Pt twoF4Setting.ι))
    (hB : ∀ (x : twoF4Setting.α.G12) (z : Pt twoF4Setting.ι),
      π (twoF4Setting.α.α1 x) z = f1 (c := twoF4Setting.ι) (twoF4Setting.α.α1 x) • z)
    (hN : ∀ (p : twoF4Setting.α.G1) (z : Pt twoF4Setting.ι), Near 8 twoF4Setting.ι z →
      π p z = f1 (c := twoF4Setting.ι) p • z)
    (hX : (π ⟨titsGen 3, n1_mem⟩ *
      MulAction.toPerm (f2 (c := twoF4Setting.ι) ⟨titsGen 2, q_mem_N⟩)) ^ gOrder = 1)
    (p : twoF4Setting.α.G1) (z : Pt twoF4Setting.ι) :
    π p z = f1 (c := twoF4Setting.ι) p • z := by
  let π' : ↥twoF4H →* Equiv.Perm (Fin 1755) := (permConj twoF4Kappa).comp π
  have hπ' : ∀ y m, π' y m = twoF4Kappa (π y (twoF4Kappa.symm m)) := fun _ _ => rfl
  have hB' : ∀ (x : Equiv.Perm (Fin 1755)) (hx : x ∈ twoF4H), x ∈ twoF4N → π' ⟨x, hx⟩ = x := by
    intro x hx hxN
    refine Equiv.ext fun m => ?_
    let w : twoF4Setting.α.G12 := ⟨x, Subgroup.mem_inf.2 ⟨hx, hxN⟩⟩
    have hw : twoF4Setting.α.α1 w = ⟨x, hx⟩ := rfl
    have e := hB w (twoF4Kappa.symm m)
    rw [hw] at e
    rw [hπ', e, kappa_f1, Equiv.apply_symm_apply, Subgroup.coe_mk]
  have hN' : ∀ (x : Equiv.Perm (Fin 1755)) (hx : x ∈ twoF4H) (m : Fin 1755),
      octGraph.dist (Sum.inl 0) (Sum.inl m) ≤ 6 → π' ⟨x, hx⟩ m = x m := by
    intro x hx m hm
    have hz : Near 8 twoF4Setting.ι (twoF4Kappa.symm m) :=
      (near_iff _).2 (by rw [Equiv.apply_symm_apply]; exact hm)
    rw [hπ', hN ⟨x, hx⟩ _ hz, kappa_f1, Equiv.apply_symm_apply, Subgroup.coe_mk]
  have hX' : (π' ⟨titsGen 3, n1_mem⟩ * titsGen 2) ^ gOrder = 1 := by
    have h2 : permConj twoF4Kappa
        (MulAction.toPerm (f2 (c := twoF4Setting.ι) ⟨titsGen 2, q_mem_N⟩)) = titsGen 2 := by
      refine Equiv.ext fun m => ?_
      rw [permConj_apply, MulAction.toPerm_apply, kappa_f2, Equiv.apply_symm_apply,
        Subgroup.coe_mk]
    have := congrArg (permConj twoF4Kappa) hX
    rw [map_pow, map_mul, h2, map_one] at this
    exact this
  have h := twoF4_rigid π' hB' hN' hX' p
  have h2 := congrArg (fun σ : Equiv.Perm (Fin 1755) => σ (twoF4Kappa z)) h
  apply twoF4Kappa.injective
  calc twoF4Kappa (π p z) = π' p (twoF4Kappa z) := by
        show _ = twoF4Kappa (π p (twoF4Kappa.symm (twoF4Kappa z)))
        rw [Equiv.symm_apply_apply]
    _ = p.1 (twoF4Kappa z) := h2
    _ = twoF4Kappa (f1 (c := twoF4Setting.ι) p • z) := (kappa_f1 p z).symm

end Rig

end CFSG.Quasithin.H13.TwoF4F48
