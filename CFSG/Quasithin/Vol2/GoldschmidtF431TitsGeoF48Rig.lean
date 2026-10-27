module

public import CFSG.Quasithin.Vol2.GoldschmidtF431TitsGeoF48Kappa
public import Certificates.Certificate4191

public noncomputable section

namespace CFSG.Quasithin.TitsGeo

open CFSG.Quasithin CFSG.Sporadic.Schreier.Tits CFSG.Quasithin.H13.F45Ru CFSG.Quasithin.H13.F48Gen
  CFSG.TitsF46 CFSG.Quasithin.RankTwoAmalgam.Completion

@[expose] def titsPermConj {X Z : Type*} (e : X ≃ Z) : Equiv.Perm X →* Equiv.Perm Z where
  toFun σ := e.permCongr σ
  map_one' := by ext; simp [Equiv.permCongr_apply]
  map_mul' a b := by ext; simp [Equiv.permCongr_apply]

theorem titsPermConj_apply {X Z : Type*} (e : X ≃ Z) (σ : Equiv.Perm X) (z : Z) :
    titsPermConj e σ z = e (σ (e.symm z)) := rfl

variable
  (h : Certificates.titsGeoFacts)
  (hc : Certificates.titsF48Facts)

theorem kappa_f1 (y : ↥titsH) (w : Pt titsSetting.ι) :
    titsKappa h (f1 (c := titsSetting.ι) y • w) = (y : Equiv.Perm (Fin 1755)) (titsKappa h w) := by
  rw [titsKappa_smul]
  rfl

theorem kappa_f2 (q : ↥titsN) (w : Pt titsSetting.ι) :
    titsKappa h (f2 (c := titsSetting.ι) q • w) = (q : Equiv.Perm (Fin 1755)) (titsKappa h w) := by
  rw [titsKappa_smul]
  rfl

include h hc in
theorem tits_rigid_pt (π : titsSetting.α.G1 →* Equiv.Perm (Pt titsSetting.ι))
    (hB : ∀ (x : titsSetting.α.G12) (z : Pt titsSetting.ι),
      π (titsSetting.α.α1 x) z = f1 (c := titsSetting.ι) (titsSetting.α.α1 x) • z)
    (hN : ∀ (p : titsSetting.α.G1) (z : Pt titsSetting.ι), Near 8 titsSetting.ι z →
      π p z = f1 (c := titsSetting.ι) p • z)
    (hX : ∀ (y : titsSetting.α.G1) (q : ↥titsN),
      (π y * MulAction.toPerm (f2 (c := titsSetting.ι) q)) ^ 17971200 = 1)
    (p : titsSetting.α.G1) (z : Pt titsSetting.ι) :
    π p z = f1 (c := titsSetting.ι) p • z := by
  obtain ⟨-, hrig⟩ := hc
  let π' : ↥titsH →* Equiv.Perm (Fin 1755) := (titsPermConj (titsKappa h)).comp π
  have hπ' : ∀ y m, π' y m = titsKappa h (π y ((titsKappa h).symm m)) := fun _ _ => rfl
  have hB' : ∀ (x : Equiv.Perm (Fin 1755)) (hx : x ∈ titsH), x ∈ titsN → π' ⟨x, hx⟩ = x := by
    intro x hx hxN
    refine Equiv.ext fun m => ?_
    let w : titsSetting.α.G12 := ⟨x, Subgroup.mem_inf.2 ⟨hx, hxN⟩⟩
    have hw : titsSetting.α.α1 w = ⟨x, hx⟩ := rfl
    have e := hB w ((titsKappa h).symm m)
    rw [hw] at e
    rw [hπ', e, kappa_f1, Equiv.apply_symm_apply, Subgroup.coe_mk]
  have hN' : ∀ (x : Equiv.Perm (Fin 1755)) (hx : x ∈ titsH) (m : Fin 1755),
      octGraph.dist (Sum.inl 0) (Sum.inl m) ≤ 6 → π' ⟨x, hx⟩ m = x m := by
    intro x hx m hm
    have hz : Near 8 titsSetting.ι ((titsKappa h).symm m) :=
      (titsKappa_near h _).2 (by rw [Equiv.apply_symm_apply]; exact hm)
    rw [hπ', hN ⟨x, hx⟩ _ hz, kappa_f1, Equiv.apply_symm_apply, Subgroup.coe_mk]
  have hX' : ∀ (y : Equiv.Perm (Fin 1755)) (hy : y ∈ titsH) (q : Equiv.Perm (Fin 1755)),
      q ∈ titsN → (π' ⟨y, hy⟩ * q) ^ 17971200 = 1 := by
    intro y hy q hq
    have h2 : titsPermConj (titsKappa h)
        (MulAction.toPerm (f2 (c := titsSetting.ι) ⟨q, hq⟩)) = q := by
      refine Equiv.ext fun m => ?_
      rw [titsPermConj_apply, MulAction.toPerm_apply, kappa_f2, Equiv.apply_symm_apply,
        Subgroup.coe_mk]
    have := congrArg (titsPermConj (titsKappa h)) (hX ⟨y, hy⟩ ⟨q, hq⟩)
    rw [map_pow, map_mul, h2, map_one] at this
    exact this
  have h3 := hrig π' hB' hN' hX' p
  have h4 := congrArg (fun σ : Equiv.Perm (Fin 1755) => σ (titsKappa h z)) h3
  apply (titsKappa h).injective
  calc titsKappa h (π p z) = π' p (titsKappa h z) := by
        show _ = titsKappa h (π p ((titsKappa h).symm (titsKappa h z)))
        rw [Equiv.symm_apply_apply]
    _ = p.1 (titsKappa h z) := h4
    _ = titsKappa h (f1 (c := titsSetting.ι) p • z) := (kappa_f1 h p z).symm

end CFSG.Quasithin.TitsGeo
