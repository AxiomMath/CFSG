module

public import CFSG.Quasithin.Background.B5FinTransport
public import CFSG.Quasithin.Background.B4ModelsAction
public import CFSG.Quasithin.Background.B4ModelsIso
public import CFSG.Quasithin.Background.F7Basic

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin.H13.M338

open CFSG.Quasithin CFSG.Assembly.LowTwoRank

variable {V : Type} [CommGroup V]

section Nat

variable {K : Type} [Field K] {n : ℕ} {H : Subgroup (MulAut V)} {W C : Subgroup V}
  {π : (FFModel.nat (StatedSL n K)).Gam →* ↥H}

theorem injective_of_nat (h : (FFModel.nat (StatedSL n K)).RealizesVia H W C π) :
    Function.Injective π := by
  rw [injective_iff_map_eq_one]
  intro γ hγ
  obtain ⟨-, -, -, hWinv, -, -, -, β, hβs, -, hβe⟩ := h
  apply natAct_faithful (StatedSL n K) γ
  intro m
  obtain ⟨u, hu⟩ := hβs (QuotientGroup.mk ⟨m, Subgroup.mem_top m⟩)
  have hmem : ((π γ : ↥H) : MulAut V) (u : V) ∈ W := hWinv _ u u.2
  have h1 := hβe γ u ⟨m, Subgroup.mem_top m⟩ hmem (Subgroup.mem_top _) hu
  have h2 : (⟨((π γ : ↥H) : MulAut V) (u : V), hmem⟩ : ↥W) = u := by
    apply Subtype.ext
    show ((π γ : ↥H) : MulAut V) (u : V) = u
    rw [hγ]
    rfl
  rw [h2, hu, QuotientGroup.eq] at h1
  have h3 : (m⁻¹ * natAct (StatedSL n K) γ m : Multiplicative (Fin n → K)) ∈
      (⊥ : Subgroup (Multiplicative (Fin n → K))) := Subgroup.mem_subgroupOf.mp h1
  rw [Subgroup.mem_bot, inv_mul_eq_one] at h3
  rw [← h3, mul_inv_cancel]

end Nat

section Field

variable {K₁ K₂ : Type} [Field K₁] [Field K₂] {n : ℕ}

@[expose] noncomputable def mapSL (e : K₁ ≃+* K₂) : ↥(StatedSL n K₁) →* ↥(StatedSL n K₂) :=
  ((Matrix.GeneralLinearGroup.map e.toRingHom).comp (StatedSL n K₁).subtype).codRestrict _
    fun g => by
      have hle : StatedSL n K₁ ≤
          (StatedSL n K₂).comap (Matrix.GeneralLinearGroup.map e.toRingHom) := by
        rw [StatedSL, Subgroup.closure_le]
        intro A hA
        apply Subgroup.subset_closure
        show (e.toRingHom.mapMatrix (A : Matrix (Fin n) (Fin n) K₁)).det = 1
        have hA' : (A : Matrix (Fin n) (Fin n) K₁).det = 1 := hA
        have h1 := RingHom.map_det e.toRingHom (A : Matrix (Fin n) (Fin n) K₁)
        rw [hA', map_one] at h1
        exact h1.symm
      exact hle g.2

theorem mapSL_coe (e : K₁ ≃+* K₂) (g : ↥(StatedSL n K₁)) :
    (((mapSL e g : ↥(StatedSL n K₂)) : GL (Fin n) K₂) : Matrix (Fin n) (Fin n) K₂) =
      ((g : GL (Fin n) K₁) : Matrix (Fin n) (Fin n) K₁).map e := rfl

theorem mapSL_symm (e : K₁ ≃+* K₂) (g : ↥(StatedSL n K₂)) : mapSL e (mapSL e.symm g) = g := by
  apply Subtype.ext
  apply Units.ext
  rw [mapSL_coe, mapSL_coe, Matrix.map_map]
  have : (⇑e ∘ ⇑e.symm : K₂ → K₂) = id := funext fun x => e.apply_symm_apply x
  rw [this, Matrix.map_id]

@[expose] def mapVec (e : K₁ ≃+* K₂) :
    ↥(FFModel.nat (StatedSL n K₁)).sec →* ↥(FFModel.nat (StatedSL n K₂)).sec where
  toFun x := ⟨Multiplicative.ofAdd fun i =>
    e (Multiplicative.toAdd (x.1 : Multiplicative (Fin n → K₁)) i), Subgroup.mem_top _⟩
  map_one' := by
    apply Subtype.ext
    apply Multiplicative.toAdd.injective
    funext i
    exact map_zero e
  map_mul' x y := by
    apply Subtype.ext
    apply Multiplicative.toAdd.injective
    funext i
    exact map_add e _ _

theorem mapVec_act (e : K₂ ≃+* K₁) (σ : GL (Fin n) K₂) (x : Multiplicative (Fin n → K₂))
    (i : Fin n) :
    e (((σ : Matrix (Fin n) (Fin n) K₂)).mulVec (Multiplicative.toAdd x) i) =
      (((σ : Matrix (Fin n) (Fin n) K₂)).map e).mulVec (fun j => e (Multiplicative.toAdd x j)) i :=
  RingHom.map_mulVec e.toRingHom (σ : Matrix (Fin n) (Fin n) K₂) (Multiplicative.toAdd x) i

theorem mapVec_mem_bot_iff (e : K₂ ≃+* K₁) (x : Multiplicative (Fin n → K₂)) :
    Multiplicative.ofAdd (fun i => e (Multiplicative.toAdd x i)) ∈
        (⊥ : Subgroup (Multiplicative (Fin n → K₁))) ↔
      x ∈ (⊥ : Subgroup (Multiplicative (Fin n → K₂))) := by
  rw [Subgroup.mem_bot, Subgroup.mem_bot]
  constructor
  · intro h
    apply Multiplicative.toAdd.injective
    funext i
    have h2 := congrFun (congrArg Multiplicative.toAdd h) i
    exact e.injective (by simpa using h2)
  · intro h
    rw [h]
    apply Multiplicative.toAdd.injective
    funext i
    exact map_zero e

theorem realizesVia_map (e : K₂ ≃+* K₁) {H : Subgroup (MulAut V)} {W C : Subgroup V}
    {π : (FFModel.nat (StatedSL n K₁)).Gam →* ↥H}
    (h : (FFModel.nat (StatedSL n K₁)).RealizesVia H W C π) :
    (FFModel.nat (StatedSL n K₂)).RealizesVia H W C (π.comp (mapSL e)) := by
  refine FFModel.RealizesVia.of_surjHom (FFModel.nat_isActionModel _) h (mapSL e)
    (fun g => ⟨mapSL e.symm g, mapSL_symm e g⟩) (mapVec e) (fun x => ?_) ?_ ?_
  · refine ⟨mapVec e.symm x, ?_⟩
    apply Subtype.ext
    apply Multiplicative.toAdd.injective
    funext i
    exact e.apply_symm_apply _
  · intro σ m hm
    apply Multiplicative.toAdd.injective
    funext i
    exact mapVec_act e σ.1 m.1 i
  · intro m
    exact mapVec_mem_bot_iff e m.1

end Field

section Alt

variable {H : Subgroup (MulAut V)} {W C : Subgroup V}

theorem realizesVia_alt {π : (FFModel.symDn 5).Gam →* ↥H}
    (h : (FFModel.symDn 5).RealizesVia H W C π) {K : Subgroup (MulAut V)}
    (hK : ∀ x, x ∈ K ↔ ∃ σ ∈ alternatingGroup (Fin 5), ((π σ : ↥H) : MulAut V) = x) :
    AlternatingNatural K W C 5 := by
  obtain ⟨hπs, hCW, hks, hWinv, hCinv, hsec, hker, β, hβs, hβk, hβe⟩ := h
  set π' : ↥(alternatingGroup (Fin 5)) →* ↥K :=
    { toFun := fun σ => ⟨((π σ.1 : ↥H) : MulAut V), (hK _).mpr ⟨σ.1, σ.2, rfl⟩⟩
      map_one' := Subtype.ext (show ((π 1 : ↥H) : MulAut V) = 1 by rw [map_one]; rfl)
      map_mul' := fun σ τ => Subtype.ext (show ((π (σ.1 * τ.1) : ↥H) : MulAut V) =
        ((π σ.1 : ↥H) : MulAut V) * ((π τ.1 : ↥H) : MulAut V) from
          congrArg Subtype.val (map_mul π σ.1 τ.1)) } with hπ'
  refine ⟨π', ?_, hCW, hks, fun k u hu => ?_, fun k z hz => ?_, fun γ m hm => hsec γ.1 m hm,
    fun γ m hm => hker γ.1 m hm, β, hβs, hβk, fun γ u m hu hm hum => ?_⟩
  · rintro ⟨x, hx⟩
    obtain ⟨σ, hσ, rfl⟩ := (hK x).mp hx
    exact ⟨⟨σ, hσ⟩, rfl⟩
  · obtain ⟨σ, -, hσ⟩ := (hK _).mp k.2
    rw [← hσ]
    exact hWinv (π σ) u hu
  · obtain ⟨σ, -, hσ⟩ := (hK _).mp k.2
    rw [← hσ]
    exact hCinv (π σ) z hz
  · exact hβe γ.1 u m hu hm hum

end Alt

section Conj

variable {D : FFModel} {H : Subgroup (MulAut V)} {W C : Subgroup V} {π : D.Gam →* ↥H}

@[expose] noncomputable def conjEquiv (y : MulAut V) (H : Subgroup (MulAut V)) :
    ↥H ≃* ↥(conjSub y H) :=
  H.equivMapOfInjective (MulAut.conj y).toMonoidHom (MulAut.conj y).injective

theorem realizesVia_conj (y : MulAut V) (h : D.RealizesVia H W C π) :
    D.RealizesVia (conjSub y H) (W.map y.toMonoidHom) (C.map y.toMonoidHom)
      ((conjEquiv y H).toMonoidHom.comp π) := by
  obtain ⟨hπs, hCW, hks, hWinv, hCinv, hsec, hker, β, hβs, hβk, hβe⟩ := h
  have hW : ∀ v, v ∈ W.map y.toMonoidHom ↔ y⁻¹ v ∈ W := fun v => by
    constructor
    · rintro ⟨w, hw, rfl⟩
      simpa using hw
    · intro hv
      exact ⟨y⁻¹ v, hv, by simp⟩
  have hC : ∀ v, v ∈ C.map y.toMonoidHom ↔ y⁻¹ v ∈ C := fun v => by
    constructor
    · rintro ⟨w, hw, rfl⟩
      simpa using hw
    · intro hv
      exact ⟨y⁻¹ v, hv, by simp⟩
  have hconj : ∀ h : ↥H, (((conjEquiv y H) h : ↥(conjSub y H)) : MulAut V) =
      y * (h : MulAut V) * y⁻¹ := fun h => rfl
  set φ : ↥(W.map y.toMonoidHom) →* ↥W :=
    { toFun := fun w => ⟨y⁻¹ w, (hW w).mp w.2⟩
      map_one' := Subtype.ext (map_one y⁻¹)
      map_mul' := fun a b => Subtype.ext (map_mul y⁻¹ (a : V) b) } with hφ
  refine ⟨(conjEquiv y H).surjective.comp hπs, Subgroup.map_mono hCW, hks, fun k u hu => ?_,
    fun k z hz => ?_, hsec, hker, β.comp φ, fun q => ?_, fun u => ?_, fun γ u m hu hm hum => ?_⟩
  · obtain ⟨h, rfl⟩ := (conjEquiv y H).surjective k
    rw [hconj, hW]
    have h1 := hWinv h _ ((hW u).mp hu)
    simpa [MulAut.mul_apply] using h1
  · obtain ⟨h, rfl⟩ := (conjEquiv y H).surjective k
    rw [hconj, hC]
    have h1 := hCinv h _ ((hC z).mp hz)
    simpa [MulAut.mul_apply] using h1
  · obtain ⟨w, hw⟩ := hβs q
    have hyw : y (w : V) ∈ W.map y.toMonoidHom := ⟨w, w.2, rfl⟩
    refine ⟨⟨_, hyw⟩, ?_⟩
    have e : φ ⟨_, hyw⟩ = w := Subtype.ext (by show y⁻¹ (y (w : V)) = w; simp)
    show β (φ ⟨_, hyw⟩) = q
    rw [e, hw]
  · rw [MonoidHom.comp_apply, hβk, hC]
    rfl
  · have hu' : ((π γ : ↥H) : MulAut V) (y⁻¹ u) ∈ W := by
      have := (hW _).mp hu
      simpa [hconj, MulAut.mul_apply] using this
    have h1 := hβe γ (φ u) m hu' hm hum
    have e : φ ⟨_, hu⟩ = ⟨_, hu'⟩ := by
      apply Subtype.ext
      show y⁻¹ ((y * ((π γ : ↥H) : MulAut V) * y⁻¹) (u : V)) = ((π γ : ↥H) : MulAut V) (y⁻¹ u)
      simp [MulAut.mul_apply]
    show β (φ ⟨_, hu⟩) = _
    rw [e]
    exact h1

theorem realizesVia_conj' (y : MulAut V) (h : D.RealizesVia H W C π) {H' : Subgroup (MulAut V)}
    {W' C' : Subgroup V} (hH : conjSub y H = H') (hW : W.map y.toMonoidHom = W')
    (hC : C.map y.toMonoidHom = C') : ∃ π' : D.Gam →* ↥H', D.RealizesVia H' W' C' π' := by
  subst hH hW hC
  exact ⟨_, realizesVia_conj y h⟩

end Conj

section Sup

variable {U Z : Subgroup V}

theorem exists_decomp_sup (x : ↥(U ⊔ Z)) : ∃ u : ↥U, ∃ z ∈ Z, (u : V) * z = x := by
  obtain ⟨u, hu, z, hz, e⟩ := Subgroup.mem_sup.mp x.2
  exact ⟨⟨u, hu⟩, z, hz, e⟩

theorem decomp_unique (hUZ : U ⊓ Z = ⊥) {u u' : ↥U} {z z' : V} (hz : z ∈ Z) (hz' : z' ∈ Z)
    (h : (u : V) * z = u' * z') : u = u' := by
  have h1 : (u' : V)⁻¹ * u ∈ U ⊓ Z := by
    refine ⟨U.mul_mem (U.inv_mem u'.2) u.2, ?_⟩
    have e : (u' : V)⁻¹ * u = z' * z⁻¹ := by
      calc (u' : V)⁻¹ * u = (u' : V)⁻¹ * (u * z) * z⁻¹ := by group
        _ = (u' : V)⁻¹ * (u' * z') * z⁻¹ := by rw [h]
        _ = z' * z⁻¹ := by group
    rw [e]
    exact Z.mul_mem hz' (Z.inv_mem hz)
  rw [hUZ, Subgroup.mem_bot, inv_mul_eq_one] at h1
  exact (Subtype.ext h1).symm

variable (U Z) in
@[expose] noncomputable def projU (hUZ : U ⊓ Z = ⊥) : ↥(U ⊔ Z) →* ↥U where
  toFun x := Classical.choose (exists_decomp_sup x)
  map_one' := by
    obtain ⟨z, hz, e⟩ := Classical.choose_spec (exists_decomp_sup (1 : ↥(U ⊔ Z)))
    exact decomp_unique hUZ hz Z.one_mem (by rw [e, mul_one]; rfl)
  map_mul' x y := by
    obtain ⟨z, hz, e⟩ := Classical.choose_spec (exists_decomp_sup x)
    obtain ⟨z', hz', e'⟩ := Classical.choose_spec (exists_decomp_sup y)
    obtain ⟨z'', hz'', e''⟩ := Classical.choose_spec (exists_decomp_sup (x * y))
    refine decomp_unique hUZ hz'' (Z.mul_mem hz hz') ?_
    rw [e'', Subgroup.coe_mul, Subgroup.coe_mul, mul_mul_mul_comm, e, e']

theorem projU_eq (hUZ : U ⊓ Z = ⊥) {x : ↥(U ⊔ Z)} {u : ↥U} {z : V} (hz : z ∈ Z)
    (h : (u : V) * z = x) : projU U Z hUZ x = u := by
  obtain ⟨z', hz', e⟩ := Classical.choose_spec (exists_decomp_sup x)
  exact decomp_unique hUZ hz' hz (e.trans h.symm)

variable {D : FFModel} {H : Subgroup (MulAut V)} {π : D.Gam →* ↥H}

theorem realizesVia_sup (h : D.RealizesVia H U ⊥ π) (hUZ : U ⊓ Z = ⊥)
    (hZinv : ∀ g : ↥H, ∀ z ∈ Z, (g : MulAut V) z ∈ Z) : D.RealizesVia H (U ⊔ Z) Z π := by
  obtain ⟨hπs, -, hks, hUinv, -, hsec, hker, β, hβs, hβk, hβe⟩ := h
  refine ⟨hπs, le_sup_right, hks, fun g x hx => ?_, hZinv, hsec, hker, β.comp (projU U Z hUZ),
    fun q => ?_, fun x => ?_, fun γ x m hx hm hxm => ?_⟩
  · obtain ⟨u, hu, z, hz, rfl⟩ := Subgroup.mem_sup.mp hx
    rw [map_mul]
    exact Subgroup.mul_mem_sup (hUinv g u hu) (hZinv g z hz)
  · obtain ⟨u, hu⟩ := hβs q
    refine ⟨⟨u, Subgroup.mem_sup_left u.2⟩, ?_⟩
    rw [MonoidHom.comp_apply, projU_eq hUZ Z.one_mem (mul_one _), hu]
  · obtain ⟨u, z, hz, e⟩ := exists_decomp_sup x
    rw [MonoidHom.comp_apply, projU_eq hUZ hz e, hβk, Subgroup.mem_bot, ← e]
    constructor
    · intro h1
      rw [h1, one_mul]
      exact hz
    · intro h1
      have h2 : (u : V) = ((u : V) * z) * z⁻¹ := by group
      rw [h2]
      have h3 : ((u : V) * z) * z⁻¹ ∈ Z := Z.mul_mem h1 (Z.inv_mem hz)
      have h4 : ((u : V) * z) * z⁻¹ ∈ U := by rw [← h2]; exact u.2
      have h5 : ((u : V) * z) * z⁻¹ ∈ U ⊓ Z := ⟨h4, h3⟩
      rw [hUZ, Subgroup.mem_bot] at h5
      exact h5
  · obtain ⟨u, z, hz, e⟩ := exists_decomp_sup x
    have hu : ((π γ : ↥H) : MulAut V) (u : V) ∈ U := hUinv _ u u.2
    have hz' : ((π γ : ↥H) : MulAut V) z ∈ Z := hZinv _ z hz
    have h1 : projU U Z hUZ x = u := projU_eq hUZ hz e
    have h2 : projU U Z hUZ ⟨_, hx⟩ = ⟨_, hu⟩ := projU_eq hUZ hz' (by rw [← map_mul, e])
    rw [MonoidHom.comp_apply] at hxm ⊢
    rw [h1] at hxm
    rw [h2]
    exact hβe γ u m hu hm hxm

end Sup

end CFSG.Quasithin.H13.M338
