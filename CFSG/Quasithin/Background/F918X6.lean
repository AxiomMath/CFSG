module

public import CFSG.Quasithin.Background.F918X5

public section

namespace CFSG.Quasithin.F918X

open CFSG.Quasithin CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique

section Orbit

variable {X : Type} [CommGroup X] [Finite X] {Mb Tb Lb : Subgroup (MulAut X)} {Vb : Subgroup X}

@[expose] def conjInv (hZ : Z35 Mb Tb Lb Vb) (hML : Mb = Lb) {t : MulAut X} (ht : t ∈ Tb) :
    MulAut ↥Lb where
  toFun l := ⟨t⁻¹ * (l : MulAut X) * t, conj_inv_mem hZ hML ht l.2⟩
  invFun l := ⟨t * (l : MulAut X) * t⁻¹, z35_conj_mem hZ hML ht l.2⟩
  left_inv l := Subtype.ext (by simp [mul_assoc])
  right_inv l := Subtype.ext (by simp [mul_assoc])
  map_mul' a b := Subtype.ext (by simp [mul_assoc])

theorem conjInv_apply (hZ : Z35 Mb Tb Lb Vb) (hML : Mb = Lb) {t : MulAut X} (ht : t ∈ Tb)
    (l : ↥Lb) :
    ((conjInv hZ hML ht l : ↥Lb) : MulAut X) = t⁻¹ * (l : MulAut X) * t := rfl

theorem conjInv_inv_mul (hZ : Z35 Mb Tb Lb Vb) (hML : Mb = Lb) {s r : MulAut X} (hs : s ∈ Tb)
    (hr : r ∈ Tb) :
    conjInv hZ hML (Tb.mul_mem (Tb.inv_mem hs) hr) =
      conjInv hZ hML hr * (conjInv hZ hML hs)⁻¹ := by
  refine MulEquiv.ext fun l => Subtype.ext ?_
  show (s⁻¹ * r)⁻¹ * (l : MulAut X) * (s⁻¹ * r) = r⁻¹ * (s * (l : MulAut X) * s⁻¹) * r
  group

@[expose] noncomputable def lbEquiv (hZ : Z35 Mb Tb Lb Vb) (hML : Mb = Lb)
    (hinj : Function.Injective (rho hZ hML)) : ↥Lb ≃* ↥(autSub Lb Vb) :=
  MulEquiv.ofBijective (rho' hZ hML)
    ⟨(rho'_injective_iff hZ hML).mpr hinj, rho'_surjective hZ hML⟩

@[expose] noncomputable def twist (hZ : Z35 Mb Tb Lb Vb) (hML : Mb = Lb)
    (hinj : Function.Injective (rho hZ hML)) {t : MulAut X} (ht : t ∈ Tb) :
    MulAut ↥(autSub Lb Vb) :=
  ((lbEquiv hZ hML hinj).symm.trans (conjInv hZ hML ht)).trans (lbEquiv hZ hML hinj)

theorem twist_rho' (hZ : Z35 Mb Tb Lb Vb) (hML : Mb = Lb)
    (hinj : Function.Injective (rho hZ hML)) {t : MulAut X} (ht : t ∈ Tb) (l : ↥Lb) :
    twist hZ hML hinj ht (rho' hZ hML l) = rho' hZ hML (conjInv hZ hML ht l) := by
  have h1 : (lbEquiv hZ hML hinj).symm (rho' hZ hML l) = l := by
    rw [MulEquiv.symm_apply_eq]
    rfl
  show lbEquiv hZ hML hinj (conjInv hZ hML ht ((lbEquiv hZ hML hinj).symm (rho' hZ hML l))) = _
  rw [h1]
  rfl

theorem twist_inv_mul (hZ : Z35 Mb Tb Lb Vb) (hML : Mb = Lb)
    (hinj : Function.Injective (rho hZ hML)) {s r : MulAut X} (hs : s ∈ Tb) (hr : r ∈ Tb) :
    twist hZ hML hinj (Tb.mul_mem (Tb.inv_mem hs) hr) =
      twist hZ hML hinj hr * (twist hZ hML hinj hs)⁻¹ := by
  refine MulEquiv.ext fun x => ?_
  obtain ⟨l, rfl⟩ := rho'_surjective hZ hML x
  obtain ⟨l', hl'⟩ : ∃ l' : ↥Lb, (twist hZ hML hinj hs)⁻¹ (rho' hZ hML l) = rho' hZ hML l' := by
    obtain ⟨l', hl'⟩ := rho'_surjective hZ hML ((twist hZ hML hinj hs)⁻¹ (rho' hZ hML l))
    exact ⟨l', hl'.symm⟩
  rw [MulAut.mul_apply, hl', twist_rho', twist_rho']
  have : (conjInv hZ hML hs) l' = l := by
    have h1 : twist hZ hML hinj hs (rho' hZ hML l') = rho' hZ hML l := by
      rw [← hl']; exact MulAut.apply_inv_self _ _ _
    rw [twist_rho'] at h1
    exact ((rho'_injective_iff hZ hML).mpr hinj) h1
  rw [conjInv_inv_mul hZ hML hs hr, MulAut.mul_apply, ← this]
  simp

@[expose] noncomputable def mapEquivOf (Vb : Subgroup X) (t : MulAut X) :
    ↥Vb ≃* ↥(Vb.map t.toMonoidHom) :=
  MulEquiv.subgroupMap t Vb

omit [Finite X] in
theorem mapEquivOf_apply (t : MulAut X) (v : ↥Vb) :
    ((mapEquivOf Vb t v : ↥(Vb.map t.toMonoidHom)) : X) = t (v : X) :=
  MulEquiv.coe_subgroupMap_apply t Vb v

theorem iso_of_realized (hZ : Z35 Mb Tb Lb Vb) (hML : Mb = Lb)
    (hinj : Function.Injective (rho hZ hML)) {s r : MulAut X} (hs : s ∈ Tb) (hr : r ∈ Tb)
    (h : twist hZ hML hinj (Tb.mul_mem (Tb.inv_mem hs) hr) ∈ realized (autSub Lb Vb)) :
    XMod.Iso ↥Lb (Vb.map s.toMonoidHom) (Vb.map r.toMonoidHom) := by
  obtain ⟨g, hg⟩ := mem_realized.mp h
  have key : ∀ (a : ↥Lb) (v : ↥Vb), (a : MulAut X) (r ((g v : ↥Vb) : X)) =
      r ((g (rho hZ hML (conjInv hZ hML hs a) v : ↥Vb) : ↥Vb) : X) := by
    intro a v
    have h1 := hg (rho' hZ hML (conjInv hZ hML hs a))
    rw [twist_rho'] at h1
    have h2 := congrArg (fun φ : MulAut ↥Vb => ((φ (g v) : ↥Vb) : X)) h1
    simp only [MulAut.mul_apply, MulAut.inv_apply_self, rho'_apply, rho_apply] at h2
    rw [h2]
    have e : (s⁻¹ * r)⁻¹ * (s⁻¹ * (a : MulAut X) * s) * (s⁻¹ * r) = r⁻¹ * (a : MulAut X) * r := by
      group
    show (a : MulAut X) (r ((g v : ↥Vb) : X)) = r
      (((conjInv hZ hML (Tb.mul_mem (Tb.inv_mem hs) hr) (conjInv hZ hML hs a) : ↥Lb) : MulAut X)
        ((g v : ↥Vb) : X))
    rw [conjInv_apply, conjInv_apply, e]
    simp [MulAut.mul_apply]
  refine ⟨(mapEquivOf Vb s).symm.trans (g.trans (mapEquivOf Vb r)), fun a l l' hll' => ?_⟩
  set v : ↥Vb := (mapEquivOf Vb s).symm l with hv
  set v' : ↥Vb := (mapEquivOf Vb s).symm l' with hv'
  have hsv : s (v : X) = (l : X) := by
    rw [← mapEquivOf_apply, hv, MulEquiv.apply_symm_apply]
  have hsv' : s (v' : X) = (l' : X) := by
    rw [← mapEquivOf_apply, hv', MulEquiv.apply_symm_apply]
  have hv'eq : v' = rho hZ hML (conjInv hZ hML hs a) v := by
    apply Subtype.ext
    rw [rho_apply, conjInv_apply]
    have h1 : (l' : X) = (a : MulAut X) (l : X) := hll'.symm
    rw [← hsv'] at h1
    rw [← hsv] at h1
    simp only [MulAut.mul_apply]
    rw [← h1]
    simp
  show (a : MulAut X) (((mapEquivOf Vb r (g v)) : ↥(Vb.map r.toMonoidHom)) : X) =
    ((mapEquivOf Vb r (g v')) : ↥(Vb.map r.toMonoidHom)) 
  rw [mapEquivOf_apply, mapEquivOf_apply, key a v, hv'eq]

theorem iso_of_stable (hZ : Z35 Mb Tb Lb Vb) (hML : Mb = Lb)
    (hinj : Function.Injective (rho hZ hML)) (hst : StableMod (autSub Lb Vb)) :
    ∀ s ∈ Tb, XMod.Iso ↥Lb (Vb.map s.toMonoidHom) Vb := by
  intro s hs
  have h1 : Vb.map (1 : MulAut X).toMonoidHom = Vb := mem_stabSub_iff_map_eq.mp (one_mem _)
  have := iso_of_realized hZ hML hinj hs Tb.one_mem (hst.mem_realized _)
  rwa [h1] at this

theorem two_of_twoClass (hZ : Z35 Mb Tb Lb Vb) (hML : Mb = Lb)
    (hinj : Function.Injective (rho hZ hML)) (htc : TwoClassMod (autSub Lb Vb)) :
    ∀ s ∈ Tb, ∀ r ∈ Tb, XMod.Iso ↥Lb (Vb.map s.toMonoidHom) Vb ∨
      XMod.Iso ↥Lb (Vb.map r.toMonoidHom) Vb ∨
      XMod.Iso ↥Lb (Vb.map s.toMonoidHom) (Vb.map r.toMonoidHom) := by
  intro s hs r hr
  have h1 : Vb.map (1 : MulAut X).toMonoidHom = Vb := mem_stabSub_iff_map_eq.mp (one_mem _)
  set R := realized (autSub Lb Vb) with hR
  have hA₂ : twist hZ hML hinj (Tb.mul_mem (Tb.inv_mem hs) hr) =
      (twist hZ hML hinj (Tb.mul_mem (Tb.inv_mem hr) Tb.one_mem))⁻¹ *
        twist hZ hML hinj (Tb.mul_mem (Tb.inv_mem hs) Tb.one_mem) := by
    rw [twist_inv_mul hZ hML hinj hs hr, twist_inv_mul hZ hML hinj hs Tb.one_mem,
      twist_inv_mul hZ hML hinj hr Tb.one_mem]
    group
  by_cases h0 : twist hZ hML hinj (Tb.mul_mem (Tb.inv_mem hs) Tb.one_mem) ∈ R
  · left
    have := iso_of_realized hZ hML hinj hs Tb.one_mem h0
    rwa [h1] at this
  by_cases h1' : twist hZ hML hinj (Tb.mul_mem (Tb.inv_mem hr) Tb.one_mem) ∈ R
  · right; left
    have := iso_of_realized hZ hML hinj hr Tb.one_mem h1'
    rwa [h1] at this
  right; right
  refine iso_of_realized hZ hML hinj hs hr ?_
  rw [hA₂]
  have hidx : R.index ≤ 2 := htc
  have hne : R.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  rcases Nat.lt_or_ge R.index 2 with hlt | hge
  · have h1i : R.index = 1 := by omega
    exact absurd (Subgroup.index_eq_one.mp h1i ▸ Subgroup.mem_top _) h0
  · have h2 : R.index = 2 := by omega
    exact (Subgroup.mul_mem_iff_of_index_two h2).mpr
      (iff_of_false (fun h => h1' (R.inv_mem_iff.mp h)) h0)

end Orbit

end CFSG.Quasithin.F918X
