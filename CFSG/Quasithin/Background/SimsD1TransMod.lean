module

public import CFSG.Quasithin.Background.D1Statement
public import CFSG.Quasithin.Background.D2Transport
public import CFSG.Quasithin.Background.ElemAbTransport

public section

namespace CFSG.Quasithin.SimsD1.TransMod

open CFSG.Open CFSG.Quasithin

section Iso

theorem coe_conjAct_apply {G : Type*} [Group G] (V : Subgroup G)
    (g : Subgroup.normalizer (V : Set G)) (v : V) :
    ((conjAct V g v : V) : G) = g * v * (g : G)⁻¹ :=
  Subgroup.normalizerMonoidHom_apply_apply_coe V (Subgroup.inclusion le_rfl g) v

theorem congr_symm_comp_congr {V V' : Type*} [Group V] [Group V'] (e : V ≃* V') :
    (MulAut.congr e.symm).toMonoidHom.comp (MulAut.congr e).toMonoidHom =
      MonoidHom.id (MulAut V) := by
  ext x
  simp

theorem qOf_map_congr {V V' : Type*} [CommGroup V] [CommGroup V'] [Finite V] [Finite V']
    (e : V ≃* V') (X : Subgroup (MulAut V)) :
    qOf (X.map (MulAut.congr e).toMonoidHom) = qOf X := by
  refine le_antisymm (kq_map_mulAutCongr_le e X 2) ?_
  have h := kq_map_mulAutCongr_le e.symm (X.map (MulAut.congr e).toMonoidHom) 2
  rwa [Subgroup.map_map, congr_symm_comp_congr, Subgroup.map_id] at h

theorem isFFModule_map_congr {W W' : Type*} [CommGroup W] [CommGroup W'] (φ : W ≃* W')
    {X : Subgroup (MulAut W)} (h : IsFFModule X) :
    IsFFModule (X.map (MulAut.congr φ).toMonoidHom) := by
  obtain ⟨A, hAX, hA1, hAel, hcard⟩ := h
  have hinj : Function.Injective (MulAut.congr φ).toMonoidHom := (MulAut.congr φ).injective
  refine ⟨A.map (MulAut.congr φ).toMonoidHom, Subgroup.map_mono hAX,
    fun h => hA1 ((Subgroup.map_eq_bot_iff_of_injective A hinj).1 h),
    (FixVLat.isElemAbelian2_map_congr_iff φ).2 hAel, ?_⟩
  rw [fixV_map_congr_equiv, Subgroup.card_map_of_injective hinj,
    Subgroup.card_map_of_injective φ.injective, Nat.card_congr φ.toEquiv.symm]
  exact hcard

theorem isFFModule_map_congr_iff {W W' : Type*} [CommGroup W] [CommGroup W'] (φ : W ≃* W')
    {X : Subgroup (MulAut W)} :
    IsFFModule (X.map (MulAut.congr φ).toMonoidHom) ↔ IsFFModule X := by
  refine ⟨fun h => ?_, isFFModule_map_congr φ⟩
  have h' := isFFModule_map_congr φ.symm h
  rwa [Subgroup.map_map, congr_symm_comp_congr, Subgroup.map_id] at h'

theorem isFFModule_map_equivariant_iff {Γ Γ' M M' : Type*} [Group Γ] [Group Γ'] [CommGroup M]
    [CommGroup M'] (Φ : M ≃* M') (ρ : Γ →* MulAut M) (ρ' : Γ' →* MulAut M') (π : Γ →* Γ')
    (hρ : ∀ (γ : Γ) (m : M), ρ' (π γ) (Φ m) = Φ (ρ γ m)) (X : Subgroup Γ) :
    IsFFModule ((X.map π).map ρ') ↔ IsFFModule (X.map ρ) := by
  have h : ρ'.comp π = (MulAut.congr Φ).toMonoidHom.comp ρ := by
    ext γ m'
    obtain ⟨m, rfl⟩ := Φ.surjective m'
    simp [hρ γ m, MulAut.congr_apply]
  rw [Subgroup.map_map, h, ← Subgroup.map_map]
  exact isFFModule_map_congr_iff Φ

theorem isFFModule_dual_map_congr_iff {W W' : Type*} [CommGroup W] [CommGroup W']
    (φ : W ≃* W') (X : Subgroup (MulAut W)) :
    @IsFFModule (W' →* Multiplicative (ZMod 2)) MonoidHom.instCommGroup
        ((X.map (MulAut.congr φ).toMonoidHom).map (dualAct W')) ↔
      @IsFFModule (W →* Multiplicative (ZMod 2)) MonoidHom.instCommGroup (X.map (dualAct W)) := by
  refine @isFFModule_map_equivariant_iff (MulAut W) (MulAut W') (W →* Multiplicative (ZMod 2))
    (W' →* Multiplicative (ZMod 2)) _ _ MonoidHom.instCommGroup MonoidHom.instCommGroup
    (φ.monoidHomCongrLeft (N := Multiplicative (ZMod 2))) (dualAct W) (dualAct W')
    (MulAut.congr φ).toMonoidHom (fun σ ψ => ?_) X
  ext w'
  show ψ (φ.symm ((MulAut.congr φ σ)⁻¹ w')) = ψ (σ⁻¹ (φ.symm w'))
  rw [← map_inv]
  simp [MulAut.congr_apply]

end Iso

section Injective

variable {A B : Type*} [Group A] [Group B] (f : A →* B)

theorem isElemAbelian_two_map_iff (hf : Function.Injective f) {E : Subgroup A} :
    IsElemAbelian 2 (E.map f) ↔ IsElemAbelian 2 E := by
  constructor
  · rintro ⟨hc, h2⟩
    refine ⟨⟨⟨fun a b => Subtype.ext (hf ?_)⟩⟩, fun x hx => hf ?_⟩
    · have := congrArg Subtype.val
        (mul_comm' (⟨f a, a, a.2, rfl⟩ : E.map f) ⟨f b, b, b.2, rfl⟩)
      simpa using this
    · simpa using h2 (f x) ⟨x, hx, rfl⟩
  · rintro ⟨hc, h2⟩
    refine ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩
    · obtain ⟨a', ha', ha⟩ := Subgroup.mem_map.mp a.2
      obtain ⟨b', hb', hb⟩ := Subgroup.mem_map.mp b.2
      refine Subtype.ext ?_
      have := congrArg (fun x : E => f x) (mul_comm' (⟨a', ha'⟩ : E) ⟨b', hb'⟩)
      simp only [Subgroup.coe_mul, map_mul] at this ⊢
      rw [← ha, ← hb, this]
    · rintro _ ⟨x, hx, rfl⟩
      rw [← map_pow, h2 x hx, map_one]

theorem map_mem_normalizer_iff (hf : Function.Injective f) (V : Subgroup A) (h : A) :
    f h ∈ Subgroup.normalizer ((V.map f : Subgroup B) : Set B) ↔
      h ∈ Subgroup.normalizer (V : Set A) := by
  rw [Subgroup.mem_normalizer_iff, Subgroup.mem_normalizer_iff]
  constructor
  · intro H a
    refine (Subgroup.mem_map_iff_mem hf).symm.trans ((H (f a)).trans ?_)
    simp only [← map_inv, ← map_mul]
    exact Subgroup.mem_map_iff_mem hf
  · intro H x
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ⟨h * a * h⁻¹, (H a).1 ha, by simp⟩
    · rintro ⟨b, hb, hbx⟩
      refine ⟨h⁻¹ * b * h, (H (h⁻¹ * b * h)).2 (by simpa [mul_assoc] using hb), ?_⟩
      simp only [map_mul, map_inv, hbx]
      group

theorem map_mem_centralizer_iff (hf : Function.Injective f) (V : Subgroup A) (c : A) :
    f c ∈ Subgroup.centralizer ((V.map f : Subgroup B) : Set B) ↔
      c ∈ Subgroup.centralizer (V : Set A) := by
  simp only [Subgroup.mem_centralizer_iff]
  constructor
  · intro H v hv
    exact hf (by simpa using H (f v) ⟨v, hv, rfl⟩)
  · rintro H _ ⟨v, hv, rfl⟩
    simpa using congrArg f (H v hv)

theorem finite_map_iff (hf : Function.Injective f) {V : Subgroup A} :
    Finite ↥(V.map f) ↔ Finite ↥V :=
  (V.equivMapOfInjective f hf).toEquiv.finite_iff.symm

theorem congr_conjAct_map (hf : Function.Injective f) (V : Subgroup A) {h : A}
    (hh : h ∈ Subgroup.normalizer (V : Set A)) :
    MulAut.congr (V.equivMapOfInjective f hf) (conjAct V ⟨h, hh⟩) =
      conjAct (V.map f) ⟨f h, (map_mem_normalizer_iff f hf V h).2 hh⟩ := by
  ext w
  obtain ⟨v, rfl⟩ := (V.equivMapOfInjective f hf).surjective w
  simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
  rw [coe_conjAct_apply]
  show f ((conjAct V ⟨h, hh⟩ v : V) : A) = _
  rw [coe_conjAct_apply]
  simp

theorem autOn_map (hf : Function.Injective f) (H V : Subgroup A) :
    autOn (H.map f) (V.map f) =
      (autOn H V).map (MulAut.congr (V.equivMapOfInjective f hf)).toMonoidHom := by
  ext σ
  simp only [autOn, Subgroup.mem_map, Subgroup.mem_subgroupOf]
  constructor
  · rintro ⟨⟨x, hxN⟩, hxH, rfl⟩
    obtain ⟨h, hh, rfl⟩ := Subgroup.mem_map.mp hxH
    have hhN : h ∈ Subgroup.normalizer (V : Set A) := (map_mem_normalizer_iff f hf V h).1 hxN
    exact ⟨conjAct V ⟨h, hhN⟩, ⟨⟨h, hhN⟩, hh, rfl⟩, congr_conjAct_map f hf V hhN⟩
  · rintro ⟨_, ⟨⟨h, hhN⟩, hh, rfl⟩, rfl⟩
    exact ⟨⟨f h, (map_mem_normalizer_iff f hf V h).2 hhN⟩, ⟨h, hh, rfl⟩,
      (congr_conjAct_map f hf V hhN).symm⟩

theorem qOf_map_equivMapOfInjective (hf : Function.Injective f) {V : Subgroup A}
    (hV : IsElemAbelian 2 V) (hV' : IsElemAbelian 2 (V.map f)) [Finite ↥V] [Finite ↥(V.map f)]
    (X : Subgroup (MulAut ↥V)) :
    @qOf ↥(V.map f) (commGroupOfElemAbelian hV') _
        (X.map (MulAut.congr (V.equivMapOfInjective f hf)).toMonoidHom) =
      @qOf ↥V (commGroupOfElemAbelian hV) _ X :=
  @qOf_map_congr ↥V ↥(V.map f) (commGroupOfElemAbelian hV) (commGroupOfElemAbelian hV') _ _
    (V.equivMapOfInjective f hf) X

theorem qOf_autOn_map (hf : Function.Injective f) {H V : Subgroup A}
    (hV : IsElemAbelian 2 V) (hV' : IsElemAbelian 2 (V.map f)) [Finite ↥V] [Finite ↥(V.map f)] :
    @qOf ↥(V.map f) (commGroupOfElemAbelian hV') _ (autOn (H.map f) (V.map f)) =
      @qOf ↥V (commGroupOfElemAbelian hV) _ (autOn H V) := by
  rw [autOn_map f hf H V]
  exact qOf_map_equivMapOfInjective f hf hV hV' _

theorem isFFInt_map (hf : Function.Injective f) {H V : Subgroup A}
    (hV : IsElemAbelian 2 V) (hV' : IsElemAbelian 2 (V.map f)) :
    IsFFInt (H.map f) (V.map f) hV' ↔ IsFFInt H V hV := by
  unfold IsFFInt
  rw [autOn_map f hf H V]
  exact @isFFModule_map_congr_iff ↥V ↥(V.map f) (commGroupOfElemAbelian hV)
    (commGroupOfElemAbelian hV') (V.equivMapOfInjective f hf) _

theorem isDualFFInt_map (hf : Function.Injective f) {H V : Subgroup A}
    (hV : IsElemAbelian 2 V) (hV' : IsElemAbelian 2 (V.map f)) :
    IsDualFFInt (H.map f) (V.map f) hV' ↔ IsDualFFInt H V hV := by
  unfold IsDualFFInt
  rw [autOn_map f hf H V]
  exact @isFFModule_dual_map_congr_iff ↥V ↥(V.map f) (commGroupOfElemAbelian hV)
    (commGroupOfElemAbelian hV') (V.equivMapOfInjective f hf) (autOn H V)

theorem isTwoReducedIn_map (hf : Function.Injective f) (H V : Subgroup A) :
    IsTwoReducedIn (H.map f) (V.map f) ↔ IsTwoReducedIn H V := by
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨(Subgroup.map_le_map_iff_of_injective hf).1 h1,
      fun x hx => (map_mem_normalizer_iff f hf V x).1 (h2 ⟨x, hx, rfl⟩),
      (isElemAbelian_two_map_iff f hf).1 h3, fun D hDH hDN hD d hd => ?_⟩
    refine (map_mem_centralizer_iff f hf V d).1 (h4 (D.map f) (Subgroup.map_mono hDH) ?_ ?_
      ⟨d, hd, rfl⟩)
    · rintro _ ⟨x, hx, rfl⟩
      exact (map_mem_normalizer_iff f hf D x).2 (hDN hx)
    · rintro _ ⟨d', hd', rfl⟩
      obtain ⟨k, hk⟩ := hD d' hd'
      exact ⟨k, by rw [← map_pow]; exact (map_mem_centralizer_iff f hf V _).2 hk⟩
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨Subgroup.map_mono h1,
      fun y => ?_, (isElemAbelian_two_map_iff f hf).2 h3, fun D hDH hDN hD y hy => ?_⟩
    · rintro ⟨x, hx, rfl⟩
      exact (map_mem_normalizer_iff f hf V x).2 (h2 hx)
    · obtain ⟨x, hx, rfl⟩ := hDH hy
      refine (map_mem_centralizer_iff f hf V x).2 (h4 (D.comap f) ?_ ?_ ?_ hy)
      · intro d hd
        obtain ⟨x', hx', hx'd⟩ := hDH hd
        exact hf hx'd ▸ hx'
      · intro x' hx'
        refine Subgroup.mem_normalizer_iff.2 fun d => ?_
        simpa [Subgroup.mem_comap] using
          Subgroup.mem_normalizer_iff.1 (hDN ⟨x', hx', rfl⟩) (f d)
      · intro d hd
        obtain ⟨k, hk⟩ := hD (f d) hd
        exact ⟨k, (map_mem_centralizer_iff f hf V _).1 (by rwa [map_pow])⟩

variable {H V : Subgroup A} {H₂ V₂ : Subgroup B}

theorem qOf_autOn_of_map_eq (hf : Function.Injective f) (hH : H.map f = H₂) (hV : V.map f = V₂)
    (hV₁ : IsElemAbelian 2 V) (hV₂ : IsElemAbelian 2 V₂) [Finite ↥V] [Finite ↥V₂] :
    @qOf ↥V₂ (commGroupOfElemAbelian hV₂) _ (autOn H₂ V₂) =
      @qOf ↥V (commGroupOfElemAbelian hV₁) _ (autOn H V) := by
  subst hH hV
  exact qOf_autOn_map f hf hV₁ hV₂

theorem isFFInt_of_map_eq (hf : Function.Injective f) (hH : H.map f = H₂) (hV : V.map f = V₂)
    (hV₁ : IsElemAbelian 2 V) (hV₂ : IsElemAbelian 2 V₂) :
    IsFFInt H₂ V₂ hV₂ ↔ IsFFInt H V hV₁ := by
  subst hH hV
  exact isFFInt_map f hf hV₁ hV₂

theorem isDualFFInt_of_map_eq (hf : Function.Injective f) (hH : H.map f = H₂)
    (hV : V.map f = V₂) (hV₁ : IsElemAbelian 2 V) (hV₂ : IsElemAbelian 2 V₂) :
    IsDualFFInt H₂ V₂ hV₂ ↔ IsDualFFInt H V hV₁ := by
  subst hH hV
  exact isDualFFInt_map f hf hV₁ hV₂

end Injective

end CFSG.Quasithin.SimsD1.TransMod
