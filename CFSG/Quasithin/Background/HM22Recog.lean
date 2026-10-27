module

public import CFSG.Quasithin.Background.HM22Out
public import CFSG.Quasithin.H13.L32NLem14412a

public section

namespace CFSG.Quasithin.H.Mathieu.M22Link

open CFSG.Quasithin CFSG.Quasithin.H13 Matrix

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem isHat_G :
    IsHat ↥H12Cert.G ↥CFSG.Blueprint.NativeSporadic.M22 := by
  have hq : CFSG.Open.quasithinM22 = CFSG.Blueprint.NativeSporadic.M22 := rfl
  have h := HatM22.isHat_hatM22Γ₀
  rw [hq] at h
  exact isHat_of_mulEquiv' hatEquivG' h

theorem card_mulAut_G_le :
    Nat.card (MulAut ↥H12Cert.G) ≤ 2 * 443520 := by
  have hG := isHat_G
  obtain ⟨hq, -, ⟨f⟩⟩ := hG
  have : Group.IsPerfect ↥H12Cert.G := hq.1
  have hq' : CFSG.Open.IsQuasisimple ↥H12Cert.G := ⟨Group.IsPerfect.commutator_eq_top, hq.2.1⟩
  have hidx := index_inn_le hq' ⟨f⟩
  have h1 := Subgroup.card_mul_index (MulAut.conj : ↥H12Cert.G →* MulAut ↥H12Cert.G).range
  rw [card_inn, Nat.card_congr f.toEquiv, CFSG.Sporadic.Schreier.m22_card] at h1
  rw [← h1, mul_comm]
  exact Nat.mul_le_mul_right _ hidx

theorem mem_zpowers_of_comm {x : GL (Fin 12) (ZMod 2)}
    (hx : ∀ g ∈ H12Cert.G, g * x = x * g) : x ∈ Subgroup.zpowers H12Cert.zU := by
  have hA : ∀ g ∈ H12Cert.G, (x : Matrix (Fin 12) (Fin 12) (ZMod 2)) *
      ((g : GL (Fin 12) (ZMod 2)) : Matrix (Fin 12) (Fin 12) (ZMod 2)) =
      ((g : GL (Fin 12) (ZMod 2)) : Matrix (Fin 12) (Fin 12) (ZMod 2)) * x := fun g hg => by
    rw [← Units.val_mul, ← Units.val_mul, hx g hg]
  rcases commutant_G hA with h | h | h | h
  · exfalso
    have h1 : ((x * x⁻¹ : GL (Fin 12) (ZMod 2)) : Matrix (Fin 12) (Fin 12) (ZMod 2)) = 0 := by
      rw [Units.val_mul, h, Matrix.zero_mul]
    rw [mul_inv_cancel, Units.val_one] at h1
    exact one_ne_zero h1
  · have : x = 1 := Units.ext h
    rw [this]
    exact Subgroup.one_mem _
  · have : x = H12Cert.zU := Units.ext h
    rw [this]
    exact Subgroup.mem_zpowers _
  · have : x = H12Cert.zU ^ 2 := Units.ext (by rw [h, pow_two, Units.val_mul])
    rw [this]
    exact Subgroup.npow_mem_zpowers _ 2

abbrev normG : Subgroup (GL (Fin 12) (ZMod 2)) := Subgroup.normalizer (H12Cert.G : Set _)

theorem card_normG_le :
    Nat.card ↥normG ≤ 2661120 := by
  set K := H12Cert.G.subgroupOf normG with hK
  have h1 := CFSG.Quasithin.H13.card_le_centralizer_mul_mulAut_82 K
  have hKG : ↥K ≃* ↥H12Cert.G := Subgroup.subgroupOfEquivOfLe Subgroup.le_normalizer
  rw [Nat.card_congr (MulAut.congr hKG).toEquiv] at h1
  have h2 : Nat.card ↥(Subgroup.centralizer (K : Set ↥normG)) ≤ 3 := by
    have hinj : Function.Injective fun x : ↥(Subgroup.centralizer (K : Set ↥normG)) =>
        (⟨((x : ↥normG) : GL (Fin 12) (ZMod 2)), mem_zpowers_of_comm fun g hg => by
          have := Subgroup.mem_centralizer_iff.mp x.2 ⟨g, Subgroup.le_normalizer hg⟩
            (show (⟨g, Subgroup.le_normalizer hg⟩ : ↥normG) ∈ K from hg)
          exact congrArg Subtype.val this⟩ : ↥(Subgroup.zpowers H12Cert.zU)) := by
      intro a b hab
      have h : ((a : ↥normG) : GL (Fin 12) (ZMod 2)) = ((b : ↥normG) : GL (Fin 12) (ZMod 2)) :=
        congrArg (fun y : ↥(Subgroup.zpowers H12Cert.zU) => (y : GL (Fin 12) (ZMod 2))) hab
      exact Subtype.ext (Subtype.ext h)
    have h3 := Nat.card_le_card_of_injective _ hinj
    rwa [Nat.card_zpowers, H12Cert.orderOf_zU] at h3
  calc Nat.card ↥normG ≤ 3 * (2 * 443520) :=
        h1.trans (Nat.mul_le_mul h2 card_mulAut_G_le)
    _ = 2661120 := by norm_num

@[expose] def m22P : Subgroup (GL (Fin 12) (ZMod 2)) :=
  L1442M.m22.map (MulAut.conj conjP⁻¹).toMonoidHom

theorem card_m22P : Nat.card m22P = 2661120 := by
  rw [m22P, Subgroup.card_map_of_injective (MulAut.conj conjP⁻¹).injective, M22Cert.card_m22]

theorem conj_mem_G_of_m22
    {x g : GL (Fin 12) (ZMod 2)} (hx : x ∈ L1442M.m22) (hg : g ∈ H12Cert.G) :
    (conjP⁻¹ * x * conjP) * g * (conjP⁻¹ * x * conjP)⁻¹ ∈ H12Cert.G := by
  have hz : conjP * g * conjP⁻¹ ∈ m22Zero := conj_mem_m22Zero hg
  have hN := normal_m22Zero.conj_mem ⟨_, m22Zero_le_m22 hz⟩ hz ⟨x, hx⟩
  have h1 : x * (conjP * g * conjP⁻¹) * x⁻¹ ∈ m22Zero := hN
  rw [mem_m22Zero_iff] at h1
  have h2 : (conjP⁻¹ * x * conjP) * g * (conjP⁻¹ * x * conjP)⁻¹ =
      conjP⁻¹ * (x * (conjP * g * conjP⁻¹) * x⁻¹) * conjP := by group
  rw [h2]
  exact h1

theorem m22P_le_normG :
    m22P ≤ normG := by
  rintro _ ⟨x, hx, rfl⟩
  rw [Subgroup.mem_normalizer_iff]
  intro g
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
  constructor
  · exact conj_mem_G_of_m22 hx
  · intro hg
    have h1 := conj_mem_G_of_m22 (L1442M.m22.inv_mem hx) hg
    have h2 : (conjP⁻¹ * x⁻¹ * conjP) * ((conjP⁻¹ * x * conjP) * g * (conjP⁻¹ * x * conjP)⁻¹) *
        (conjP⁻¹ * x⁻¹ * conjP)⁻¹ = g := by group
    rwa [h2] at h1

theorem normG_eq :
    normG = m22P :=
  (Subgroup.eq_of_le_of_card_ge m22P_le_normG (by rw [card_m22P]; exact card_normG_le)).symm

@[expose] def toMulAutV (V : Type*) [AddCommGroup V] [Module (ZMod 2) V] :
    (V ≃ₗ[ZMod 2] V) →* MulAut (Multiplicative V) where
  toFun φ := AddEquiv.toMultiplicative φ.toAddEquiv
  map_one' := by ext; rfl
  map_mul' _ _ := by ext; rfl

theorem toMulAutV_apply {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] (φ : V ≃ₗ[ZMod 2] V)
    (w : Multiplicative V) :
    toMulAutV V φ w = Multiplicative.ofAdd (φ (Multiplicative.toAdd w)) := rfl

theorem toMulAutV_injective {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] :
    Function.Injective (toMulAutV V) := by
  intro φ χ h
  ext v
  have := congrArg (fun f : MulAut (Multiplicative V) => f (Multiplicative.ofAdd v)) h
  simpa only [toMulAutV_apply, toAdd_ofAdd, ofAdd_toAdd] using congrArg Multiplicative.toAdd this

theorem matOfN_surjective {n : ℕ} {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (e : V ≃ₗ[ZMod 2] (Fin n → ZMod 2)) : Function.Surjective (L14411.matOfN e) := by
  intro x
  refine ⟨e.trans ((L14411.linOfN x).trans e.symm), ?_⟩
  rw [L14411.matOfN_eq_iff]
  intro v
  simp [L14411.linOfN_apply]

theorem exists_linearEquiv_m22
    {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V] (hV : Nat.card V = 4096)
    (Γ N : Subgroup (V ≃ₗ[ZMod 2] V)) (hNn : ∀ γ ∈ Γ, ∀ n ∈ N, γ * n * γ⁻¹ ∈ N)
    (hN : IsHat ↥N ↥CFSG.Blueprint.NativeSporadic.M22) (hΓ : Nat.card ↥Γ = 2661120) :
    ∃ e : V ≃ₗ[ZMod 2] (Fin 12 → ZMod 2), ∀ φ : V ≃ₗ[ZMod 2] V,
      φ ∈ Γ ↔ ∃ γ ∈ L1442M.m22,
        ∀ v, e (φ v) = (γ : Matrix (Fin 12) (Fin 12) (ZMod 2)).mulVec (e v) := by
  have hW2 : ∀ w : Multiplicative V, w ^ 2 = 1 := fun w => by
    apply Multiplicative.toAdd.injective
    rw [toAdd_pow, toAdd_one]
    exact ZModModule.char_nsmul_eq_zero 2 _
  have hWc : Nat.card (Multiplicative V) = 4096 := hV
  set L := N.map (toMulAutV V) with hLdef
  have hL : IsHat ↥L (CFSG.Blueprint.NativeSporadic.Carrier .M22) :=
    isHat_of_mulEquiv' (N.equivMapOfInjective _ toMulAutV_injective) hN
  obtain ⟨ψ, θ, hψθ⟩ := exists_model_of_isHat hW2 hWc hL
  let ea : V ≃+ (Fin 12 → ZMod 2) := AddEquiv.toMultiplicative.symm θ
  let e : V ≃ₗ[ZMod 2] (Fin 12 → ZMod 2) := ea.toLinearEquiv fun c x => ZMod.map_smul ea c x
  have he : ∀ v, e v = Multiplicative.toAdd (θ (Multiplicative.ofAdd v)) := fun _ => rfl
  have hmat : ∀ n ∈ N, ∀ g : ↥H12Cert.G, ((ψ g : ↥L) : MulAut (Multiplicative V)) =
      toMulAutV V n → L14411.matOfN e n = g := by
    intro n _ g hg
    rw [L14411.matOfN_eq_iff]
    intro v
    rw [he, he, ← hψθ, hg, toMulAutV_apply, toAdd_ofAdd]
  have hmapN : N.map (L14411.matOfN e) = H12Cert.G := by
    ext x
    constructor
    · rintro ⟨n, hn, rfl⟩
      obtain ⟨g, hg⟩ := ψ.surjective ⟨toMulAutV V n, n, hn, rfl⟩
      rw [hmat n hn g (congrArg Subtype.val hg)]
      exact g.2
    · intro hx
      obtain ⟨n, hn, hgn⟩ := (ψ ⟨x, hx⟩).2
      exact ⟨n, hn, hmat n hn ⟨x, hx⟩ hgn.symm⟩
  have hmemG : ∀ χ : V ≃ₗ[ZMod 2] V, L14411.matOfN e χ ∈ H12Cert.G ↔ χ ∈ N := by
    intro χ
    rw [← hmapN]
    constructor
    · rintro ⟨n, hn, hnχ⟩
      rwa [← L14411.matOfN_injective e hnχ]
    · intro hχ
      exact ⟨χ, hχ, rfl⟩
  have hΓN : Γ.map (L14411.matOfN e) ≤ normG := by
    rintro _ ⟨γ, hγ, rfl⟩
    rw [Subgroup.mem_normalizer_iff]
    intro h
    obtain ⟨χ, rfl⟩ := matOfN_surjective e h
    rw [← map_inv, ← map_mul, ← map_mul, hmemG, hmemG]
    constructor
    · exact hNn γ hγ χ
    · intro hc
      have := hNn γ⁻¹ (Γ.inv_mem hγ) _ hc
      rwa [inv_inv, show γ⁻¹ * (γ * χ * γ⁻¹) * γ = χ by group] at this
  have hcard : Nat.card ↥(Γ.map (L14411.matOfN e)) = 2661120 := by
    rw [Subgroup.card_map_of_injective (L14411.matOfN_injective e), hΓ]
  have heq : Γ.map (L14411.matOfN e) = m22P := by
    rw [← normG_eq]
    exact Subgroup.eq_of_le_of_card_ge hΓN (by rw [hcard]; exact card_normG_le)
  refine ⟨e.trans (L14411.linOfN conjP), fun φ => ?_⟩
  have htr := L14411.matOfN_trans e conjP φ
  constructor
  · intro hφ
    have h1 : L14411.matOfN e φ ∈ m22P := heq ▸ ⟨φ, hφ, rfl⟩
    obtain ⟨x, hx, hxφ⟩ := h1
    refine ⟨x, hx, (L14411.matOfN_eq_iff _ _ _).mp ?_⟩
    rw [htr, ← hxφ, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  · rintro ⟨γ, hγ, hγv⟩
    have h1 := (L14411.matOfN_eq_iff _ _ _).mpr hγv
    rw [htr] at h1
    have h2 : L14411.matOfN e φ ∈ m22P := by
      refine ⟨γ, hγ, ?_⟩
      rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, ← h1]
      group
    rw [← heq] at h2
    obtain ⟨φ', hφ', hφ'eq⟩ := h2
    rwa [← L14411.matOfN_injective e hφ'eq]

theorem exists_linearEquiv_m22_of_normal
    {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (hd : Module.finrank (ZMod 2) V = 12) {Γ : Subgroup (V ≃ₗ[ZMod 2] V)}
    (hc : Nat.card ↥Γ = 2661120)
    (h13a : ∃ N : Subgroup ↥Γ, N.Normal ∧ N.index = 2 ∧
      IsHat ↥N ↥CFSG.Blueprint.NativeSporadic.M22) :
    ∃ e : V ≃ₗ[ZMod 2] (Fin 12 → ZMod 2), ∀ φ : V ≃ₗ[ZMod 2] V,
      φ ∈ Γ ↔ ∃ γ ∈ L1442M.m22,
        ∀ v, e (φ v) = (γ : Matrix (Fin 12) (Fin 12) (ZMod 2)).mulVec (e v) := by
  obtain ⟨N, hNn, -, hN⟩ := h13a
  have hV : Nat.card V = 4096 := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), hd, Nat.card_zmod]
    norm_num
  refine exists_linearEquiv_m22 hV Γ (N.map Γ.subtype) ?_
    (isHat_of_mulEquiv' (N.equivMapOfInjective _ Γ.subtype_injective) hN) hc
  rintro γ hγ _ ⟨n, hn, rfl⟩
  exact ⟨⟨γ, hγ⟩ * n * ⟨γ, hγ⟩⁻¹, hNn.conj_mem n hn ⟨γ, hγ⟩, rfl⟩

end CFSG.Quasithin.H.Mathieu.M22Link
