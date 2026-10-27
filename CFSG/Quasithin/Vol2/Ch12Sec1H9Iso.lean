module

public import CFSG.Quasithin.Vol2.Ch12Sec1H9Conj

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin.E3

namespace H9Iso

variable {W W' : Type} [CommGroup W] [CommGroup W'] (e : W ≃* W')

@[expose] def isoAut (A : Subgroup (MulAut W)) : Subgroup (MulAut W') :=
  A.map (MulAut.congr e).toMonoidHom

theorem congr_apply' (x : MulAut W) (w : W) : MulAut.congr e x (e w) = e (x w) := by
  simp

theorem mem_isoAut {A : Subgroup (MulAut W)} {x : MulAut W'} :
    x ∈ isoAut e A ↔ (MulAut.congr e).symm x ∈ A :=
  Subgroup.mem_map_equiv

theorem congr_mem_isoAut {A : Subgroup (MulAut W)} {x : MulAut W} :
    MulAut.congr e x ∈ isoAut e A ↔ x ∈ A := by
  rw [mem_isoAut, MulEquiv.symm_apply_apply]

theorem isoAut_le_iff {A B : Subgroup (MulAut W)} : isoAut e A ≤ isoAut e B ↔ A ≤ B :=
  Subgroup.map_le_map_iff_of_injective (MulAut.congr e).injective

theorem isoAut_inf (A B : Subgroup (MulAut W)) :
    isoAut e (A ⊓ B) = isoAut e A ⊓ isoAut e B :=
  Subgroup.map_inf_eq _ _ _ (MulAut.congr e).injective

theorem card_isoAut (A : Subgroup (MulAut W)) : Nat.card (isoAut e A) = Nat.card A :=
  Subgroup.card_map_of_injective (f := (MulAut.congr e).toMonoidHom) (MulAut.congr e).injective

theorem isoAut_eq_bot_iff {A : Subgroup (MulAut W)} : isoAut e A = ⊥ ↔ A = ⊥ := by
  rw [isoAut, Subgroup.map_eq_bot_iff_of_injective _ (MulAut.congr e).injective]

theorem isoAut_symm (B : Subgroup (MulAut W')) : isoAut e (isoAut e.symm B) = B := by
  ext x
  rw [mem_isoAut, mem_isoAut]
  have h : (MulAut.congr e.symm).symm ((MulAut.congr e).symm x) = x := by
    ext w
    simp
  rw [h]

theorem fixV_isoAut (A : Subgroup (MulAut W)) :
    fixV (isoAut e A) = (fixV A).map e.toMonoidHom := by
  ext w'
  rw [mem_fixV, Subgroup.mem_map]
  constructor
  · intro h
    refine ⟨e.symm w', fun x hx => ?_, by simp⟩
    have h1 := h (MulAut.congr e x) ((congr_mem_isoAut e).mpr hx)
    apply e.injective
    rw [← congr_apply', MulEquiv.apply_symm_apply, h1]
  · rintro ⟨w, hw, rfl⟩ x hx
    have hx' := (mem_isoAut e).mp hx
    have h1 := hw _ hx'
    have h2 : x = MulAut.congr e ((MulAut.congr e).symm x) :=
      ((MulAut.congr e).apply_symm_apply x).symm
    rw [MulEquiv.coe_toMonoidHom, h2, congr_apply', h1]

theorem card_fixV_isoAut (A : Subgroup (MulAut W)) :
    Nat.card (fixV (isoAut e A)) = Nat.card (fixV A) := by
  rw [fixV_isoAut]
  exact Subgroup.card_map_of_injective (f := e.toMonoidHom) e.injective

theorem commV_isoAut (A : Subgroup (MulAut W)) :
    commV (isoAut e A) = (commV A).map e.toMonoidHom := by
  unfold commV
  rw [MonoidHom.map_closure]
  congr 1
  ext w'
  constructor
  · rintro ⟨x, hx, v, rfl⟩
    refine ⟨(MulAut.congr e).symm x (e.symm v) * (e.symm v)⁻¹,
      ⟨_, (mem_isoAut e).mp hx, e.symm v, rfl⟩, ?_⟩
    have h3 : e (((MulAut.congr e).symm x) (e.symm v)) = x v := by
      have h4 := congr_apply' e ((MulAut.congr e).symm x) (e.symm v)
      rw [MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply] at h4
      exact h4.symm
    rw [MulEquiv.coe_toMonoidHom, map_mul, map_inv, h3, MulEquiv.apply_symm_apply]
  · rintro ⟨u, ⟨x, hx, v, rfl⟩, rfl⟩
    refine ⟨MulAut.congr e x, (congr_mem_isoAut e).mpr hx, e v, ?_⟩
    rw [congr_apply', MulEquiv.coe_toMonoidHom, map_mul, map_inv]

theorem card_commV_isoAut (A : Subgroup (MulAut W)) :
    Nat.card (commV (isoAut e A)) = Nat.card (commV A) := by
  rw [commV_isoAut]
  exact Subgroup.card_map_of_injective (f := e.toMonoidHom) e.injective

theorem mQuot_isoAut (P X : Subgroup (MulAut W)) :
    mQuot (isoAut e P) (isoAut e X) = mQuot P X := by
  unfold mQuot isoAut
  rw [Subgroup.relIndex_map_map_of_injective (f := (MulAut.congr e).toMonoidHom) _ _
    (MulAut.congr e).injective]

theorem gammaCheck_isoAut (k : ℕ) (P : Subgroup (MulAut W)) :
    gammaCheck k (isoAut e P) = (gammaCheck k P).map e.toMonoidHom := by
  apply le_antisymm
  · refine H9Conj.gammaCheck_le fun X hX hXk => ?_
    have hXY : isoAut e (isoAut e.symm X) = X := isoAut_symm e X
    have hYP : isoAut e.symm X ≤ P := by
      rw [← isoAut_le_iff e, hXY]
      exact hX
    have hYk : mQuot P (isoAut e.symm X) ≤ k := by
      rw [← mQuot_isoAut e P, hXY]
      exact hXk
    rw [← hXY, fixV_isoAut]
    exact Subgroup.map_mono (H9Conj.fixV_le_gammaCheck hYP hYk)
  · rw [Subgroup.map_le_iff_le_comap]
    refine H9Conj.gammaCheck_le fun Y hY hYk => ?_
    rw [← Subgroup.map_le_iff_le_comap, ← fixV_isoAut]
    exact H9Conj.fixV_le_gammaCheck ((isoAut_le_iff e).mpr hY)
      (by rw [mQuot_isoAut]; exact hYk)

theorem card_gammaCheck_isoAut (k : ℕ) (P : Subgroup (MulAut W)) :
    Nat.card (gammaCheck k (isoAut e P)) = Nat.card (gammaCheck k P) := by
  rw [gammaCheck_isoAut]
  exact Subgroup.card_map_of_injective (f := e.toMonoidHom) e.injective

theorem gammaCheck_isoAut_eq_top_iff (k : ℕ) (P : Subgroup (MulAut W)) :
    gammaCheck k (isoAut e P) = ⊤ ↔ gammaCheck k P = ⊤ := by
  rw [gammaCheck_isoAut]
  constructor
  · intro h
    rw [eq_top_iff]
    intro w _
    have hw : e w ∈ (gammaCheck k P).map e.toMonoidHom := by rw [h]; trivial
    obtain ⟨u, hu, hue⟩ := hw
    rw [show u = w from e.injective hue] at hu
    exact hu
  · intro h
    rw [h]
    exact Subgroup.map_top_of_surjective _ e.surjective

theorem mem_stabV_congr_iff (U : Subgroup W) (x : MulAut W) :
    MulAut.congr e x ∈ stabV (U.map e.toMonoidHom) ↔ x ∈ stabV U := by
  have hmem : ∀ w : W, e w ∈ U.map e.toMonoidHom ↔ w ∈ U := fun w => by
    rw [Subgroup.mem_map]
    exact ⟨fun ⟨u, hu, h⟩ => (e.injective h) ▸ hu, fun h => ⟨w, h, rfl⟩⟩
  constructor
  · intro h w
    have h1 := h (e w)
    rw [congr_apply', hmem, hmem] at h1
    exact h1
  · intro h w'
    obtain ⟨w, rfl⟩ := e.surjective w'
    rw [congr_apply', hmem, hmem]
    exact h w

theorem zpowers_congr (x : MulAut W) :
    Subgroup.zpowers (MulAut.congr e x) = isoAut e (Subgroup.zpowers x) := by
  rw [isoAut, MonoidHom.map_zpowers]
  rfl

theorem isTransvOn_congr (x : MulAut W) (U : Subgroup W) :
    IsTransvOn (MulAut.congr e x) (U.map e.toMonoidHom) ↔ IsTransvOn x U := by
  unfold IsTransvOn
  rw [mem_stabV_congr_iff, zpowers_congr, fixV_isoAut,
    ← Subgroup.map_inf_eq _ _ _ e.injective,
    Subgroup.relIndex_map_map_of_injective (f := e.toMonoidHom) _ _ e.injective]

theorem conjAut_isoAut (A : Subgroup (MulAut W)) (m : MulAut W) :
    isoAut e (conjAut A m) = conjAut (isoAut e A) (MulAut.congr e m) := by
  unfold isoAut conjAut
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext x w
  simp

theorem isElemAbelian2_isoAut {A : Subgroup (MulAut W)} (h : IsElemAbelian2 A) :
    IsElemAbelian2 (isoAut e A) := by
  refine ⟨fun x hx y hy => ?_, fun x hx => ?_⟩
  · obtain ⟨a, ha, rfl⟩ := hx
    obtain ⟨b, hb, rfl⟩ := hy
    rw [← map_mul, ← map_mul, h.1 a ha b hb]
  · obtain ⟨a, ha, rfl⟩ := hx
    rw [← map_pow, h.2 a ha, map_one]

theorem isElemAbelian2_isoAut_iff {A : Subgroup (MulAut W)} :
    IsElemAbelian2 (isoAut e A) ↔ IsElemAbelian2 A := by
  refine ⟨fun h => ?_, isElemAbelian2_isoAut e⟩
  have h1 := isElemAbelian2_isoAut e.symm h
  rwa [show isoAut e.symm (isoAut e A) = A by
    have := isoAut_symm e.symm A
    rwa [MulEquiv.symm_symm] at this] at h1

end H9Iso

end CFSG.Quasithin.H13
