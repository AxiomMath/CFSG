module

public import CFSG.Sporadic.HN.Local.Labels
public import CFSG.Sporadic.HN.Local.AltCertificate
public import Certificates.Certificate3166

set_option maxRecDepth 100000

public section

namespace CFSG.Sporadic.HN.Local

open CFSG.Sporadic.F5 Equiv CFSG.Sporadic.HN.LocalK

theorem orbit_squeeze {G X : Type*} [Group G] [Finite G] [MulAction G X] (v : X)
    (H : Subgroup G) (hH : H ≤ MulAction.stabilizer G v) {N s : ℕ}
    (hN : N ≤ Nat.card (MulAction.orbit G v)) (hG : Nat.card G = N * s) (hs : s ≤ Nat.card H) :
    H = MulAction.stabilizer G v ∧ Nat.card H = s ∧ Nat.card (MulAction.orbit G v) = N := by
  have h1 := (MulAction.stabilizer G v).card_mul_index
  rw [MulAction.index_stabilizer, ← Nat.card_coe_set_eq] at h1
  have hHS : Nat.card H ≤ Nat.card (MulAction.stabilizer G v) := Subgroup.card_le_of_le hH
  have hGpos : 0 < Nat.card G := Nat.card_pos
  have hspos : 0 < s := by
    rcases Nat.eq_zero_or_pos s with h | h
    · rw [h, mul_zero] at hG; omega
    · exact h
  have hNpos : 0 < N := by
    rcases Nat.eq_zero_or_pos N with h | h
    · rw [h, zero_mul] at hG; omega
    · exact h
  have hS : Nat.card (MulAction.stabilizer G v) = s := by
    by_contra hne
    have hlt : s < Nat.card (MulAction.stabilizer G v) := by omega
    have := Nat.mul_lt_mul_of_le_of_lt hN hlt (lt_of_lt_of_le hNpos hN)
    have h2 : Nat.card (MulAction.orbit G v) * Nat.card (MulAction.stabilizer G v) =
        Nat.card G := by
      rw [Nat.mul_comm]
      exact h1
    rw [h2, hG] at this
    exact absurd this (by simp [Nat.mul_comm])
  have hO : Nat.card (MulAction.orbit G v) = N := by
    rw [hS, hG] at h1
    exact Nat.eq_of_mul_eq_mul_left hspos (by rw [h1, Nat.mul_comm])
  have hHs : Nat.card H = s := le_antisymm (hS ▸ hHS) hs
  exact ⟨Subgroup.eq_of_le_of_card_ge hH (by rw [hS, hHs]), hHs, hO⟩

theorem inv_mapsTo_of_finite {G X : Type*} [Group G] [MulAction G X] {S : Set X} (hS : S.Finite)
    {g : G} (h : ∀ x ∈ S, g • x ∈ S) : ∀ x ∈ S, g⁻¹ • x ∈ S := by
  have hm : Set.MapsTo (fun x => g • x) S S := fun x hx => h x hx
  have hinj : Set.InjOn (fun x => g • x) S := fun x _ y _ e => smul_left_cancel g e
  have hb := (hS.injOn_iff_bijOn_of_mapsTo hm).1 hinj
  intro x hx
  obtain ⟨y, hy, rfl⟩ := hb.2.2 hx
  simpa using hy

noncomputable abbrev stabHN : Subgroup (J dHN) := MulAction.stabilizer (J dHN) rootV

noncomputable abbrev Hx : Subgroup (J dHN) := Subgroup.closure {wG 2, wG 3}

theorem card_Jd : Nat.card (J dHN) = 273030912000000 :=
  Certificates.certificate3166.2.2.2.2.1

theorem Hx_le : Hx ≤ stabHN := by
  rw [Subgroup.closure_le]
  rintro _ (rfl | rfl)
  · exact alt_certificate.1
  · exact alt_certificate.2.1

noncomputable abbrev wSet : Set (Vec dHN) := Set.range hnW

theorem wSet_finite : wSet.Finite := Set.finite_range _

theorem Hx_mapsTo : ∀ h ∈ Hx, ∀ v ∈ wSet, h • v ∈ wSet := by
  intro h hh
  induction hh using Subgroup.closure_induction with
  | mem g hg =>
    rintro _ ⟨k, rfl⟩
    rcases hg with rfl | rfl
    · exact ⟨pi2 k, (alt_certificate.2.2.2.1 k).symm⟩
    · exact ⟨pi3 k, (alt_certificate.2.2.2.2.1 k).symm⟩
  | one => intro v hv; simpa using hv
  | mul a b _ _ ha hb => intro v hv; rw [mul_smul]; exact ha _ (hb v hv)
  | inv a _ ha => exact inv_mapsTo_of_finite wSet_finite ha

@[expose] noncomputable def wSub : SubMulAction Hx (Vec dHN) where
  carrier := wSet
  smul_mem' h v hv := Hx_mapsTo h.1 h.2 v hv

@[expose] noncomputable def wEquiv : Fin 462 ≃ wSub :=
  Equiv.ofBijective (fun k => ⟨hnW k, k, rfl⟩)
    ⟨fun j k e => alt_certificate.2.2.1 (congrArg Subtype.val e), fun ⟨_, k, rfl⟩ => ⟨k, rfl⟩⟩

@[expose] noncomputable def phiW : Hx →* Perm (Fin 462) :=
  wEquiv.symm.permCongrHom.toMonoidHom.comp (MulAction.toPermHom Hx wSub)

theorem hnW_phiW (h : Hx) (k : Fin 462) :
    hnW (phiW h k) = (h : J dHN) • hnW k := by
  have e : wEquiv (phiW h k) = h • wEquiv k := by
    change wEquiv (wEquiv.symm (h • wEquiv k)) = _
    rw [Equiv.apply_symm_apply]
  exact congrArg Subtype.val e

theorem phiW_eq {h : Hx} {σ : Fin 462 → Fin 462}
    (hσ : ∀ k, (h : J dHN) • hnW k = hnW (σ k)) (k : Fin 462) : phiW h k = σ k :=
  alt_certificate.2.2.1 (by rw [hnW_phiW, hσ])

@[expose] noncomputable def xH : Hx := ⟨wG 2, Subgroup.subset_closure (Set.mem_insert _ _)⟩

@[expose] noncomputable def yH : Hx := ⟨wG 3, Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)⟩

theorem closure_xyH : Subgroup.closure ({xH, yH} : Set Hx) = ⊤ := by
  have : ({xH, yH} : Set Hx) = Subtype.val ⁻¹' ({wG 2, wG 3} : Set (J dHN)) := by
    ext z
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_preimage]
    constructor
    · rintro (rfl | rfl)
      · exact Or.inl rfl
      · exact Or.inr rfl
    · rintro (h | h)
      · exact Or.inl (Subtype.ext h)
      · exact Or.inr (Subtype.ext h)
  rw [this]
  exact Subgroup.closure_closure_coe_preimage

theorem labP_xH (k : Fin 462) :
    labP (phiW xH k) = pOne • labP k := by
  have e : phiW xH k = pi2 k := phiW_eq (h := xH) (σ := pi2) (fun k => alt_certificate.2.2.2.1 k) k
  rw [e]
  exact labP_pi2 k

theorem labP_yH (k : Fin 462) :
    labP (phiW yH k) = pTwo • labP k := by
  have e : phiW yH k = pi3 k :=
    phiW_eq (h := yH) (σ := pi3) (fun k => alt_certificate.2.2.2.2.1 k) k
  rw [e]
  exact labP_pi3 k

noncomputable abbrev labHom {K : Type*} [Group K] (φ : K →* Perm (Fin 462)) : K →* Perm Part :=
  (Equiv.ofBijective labP labP_bijective).permCongrHom.toMonoidHom.comp φ

noncomputable abbrev nuA : alternatingGroup (Fin 12) →* Perm Part :=
  natHom.comp (alternatingGroup (Fin 12)).subtype

theorem labHom_apply {K : Type*} [Group K] (φ : K →* Perm (Fin 462)) (h : K) (k : Fin 462) :
    labHom φ h (labP k) = labP (φ h k) := by
  change (Equiv.ofBijective labP labP_bijective) (φ h ((Equiv.ofBijective labP labP_bijective).symm
    (labP k))) = _
  have : (Equiv.ofBijective labP labP_bijective).symm (labP k) = k :=
    (Equiv.ofBijective labP labP_bijective).symm_apply_eq.2 rfl
  rw [this]
  rfl

theorem closure_alt_gens :
    Subgroup.closure ({⟨pOne, pOne_even⟩, ⟨pTwo, pTwo_even⟩} : Set (alternatingGroup (Fin 12))) = ⊤ := by
  have : ({⟨pOne, pOne_even⟩, ⟨pTwo, pTwo_even⟩} : Set (alternatingGroup (Fin 12))) =
      Subtype.val ⁻¹' ({pOne, pTwo} : Set (Perm (Fin 12))) := by
    ext z
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_preimage]
    constructor
    · rintro (rfl | rfl)
      · exact Or.inl rfl
      · exact Or.inr rfl
    · rintro (h | h)
      · exact Or.inl (Subtype.ext h)
      · exact Or.inr (Subtype.ext h)
  rw [this]
  have h := Subgroup.closure_closure_coe_preimage (k := ({pOne, pTwo} : Set (Perm (Fin 12))))
  have hK : Subgroup.closure ({pOne, pTwo} : Set (Perm (Fin 12))) = alternatingGroup (Fin 12) :=
    closure_pOne_pTwo
  rw [hK] at h
  exact h

theorem labHom_range {K : Type*} [Group K] (φ : K →* Perm (Fin 462)) (x y : K)
    (hxy : Subgroup.closure ({x, y} : Set K) = ⊤)
    (hx : ∀ k, labP (φ x k) = pOne • labP k) (hy : ∀ k, labP (φ y k) = pTwo • labP k) :
    (labHom φ).range = nuA.range := by
  have hΦx : labHom φ x = nuA ⟨pOne, pOne_even⟩ := by
    ext S
    obtain ⟨k, rfl⟩ := labP_bijective.2 S
    rw [labHom_apply, hx]; rfl
  have hΦy : labHom φ y = nuA ⟨pTwo, pTwo_even⟩ := by
    ext S
    obtain ⟨k, rfl⟩ := labP_bijective.2 S
    rw [labHom_apply, hy]; rfl
  rw [MonoidHom.range_eq_map, ← hxy, MonoidHom.map_closure, MonoidHom.range_eq_map,
    ← closure_alt_gens, MonoidHom.map_closure, Set.image_pair, Set.image_pair, hΦx, hΦy]

theorem card_nuA_range : Nat.card nuA.range = Nat.factorial 12 / 2 := by
  rw [← Nat.card_congr (MonoidHom.ofInjective natHom_alt_injective).toEquiv,
    Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]

theorem card_range_phi {K : Type*} [Group K] (φ : K →* Perm (Fin 462)) (x y : K)
    (hxy : Subgroup.closure ({x, y} : Set K) = ⊤)
    (hx : ∀ k, labP (φ x k) = pOne • labP k) (hy : ∀ k, labP (φ y k) = pTwo • labP k) :
    Nat.card φ.range = Nat.factorial 12 / 2 := by
  rw [← card_nuA_range, ← labHom_range φ x y hxy hx hy]
  have hinj : Function.Injective
      (Equiv.ofBijective labP labP_bijective).permCongrHom.toMonoidHom :=
    (Equiv.ofBijective labP labP_bijective).permCongrHom.injective
  rw [MonoidHom.range_comp, Subgroup.card_map_of_injective hinj]

theorem card_Hx_ge : Nat.factorial 12 / 2 ≤ Nat.card Hx := by
  rw [← card_range_phi phiW xH yH closure_xyH labP_xH labP_yH]
  exact Nat.card_le_card_of_surjective _ (MonoidHom.rangeRestrict_surjective _)

theorem squeeze :
    Hx = stabHN ∧ Nat.card Hx = 239500800 ∧ Nat.card (MulAction.orbit (J dHN) rootV) = 1140000 := by
  have h := orbit_squeeze rootV Hx Hx_le (N := 1140000) (s := 239500800)
    alt_certificate.2.2.2.2.2 (by rw [card_Jd]) (by
      have := card_Hx_ge
      rw [show Nat.factorial 12 / 2 = 239500800 by decide] at this
      exact this)
  exact h

theorem Hx_eq : Hx = stabHN :=
  squeeze.1

theorem card_stabHN :
    Nat.card stabHN = 239500800 := by
  rw [← Hx_eq]; exact squeeze.2.1

theorem card_orbit_root :
    Nat.card (MulAction.orbit (J dHN) rootV) = 1140000 := squeeze.2.2

theorem phiW_injective :
    Function.Injective phiW := by
  have h1 := card_range_phi phiW xH yH closure_xyH labP_xH labP_yH
  have h2 : Nat.card Hx = Nat.card phiW.range := by
    rw [h1, squeeze.2.1]; decide
  have hsurj := MonoidHom.rangeRestrict_surjective phiW
  have hb := hsurj.bijective_of_nat_card_le h2.le
  intro a b e
  exact hb.1 (Subtype.ext e)

theorem theta_exists_aux :
    (∀ σ τ : alternatingGroup (Fin 12),
      (∀ S : Part, (σ : Equiv.Perm (Fin 12)) • S = (τ : Equiv.Perm (Fin 12)) • S) → σ = τ) ∧
    ∃ θ : Hx ≃* alternatingGroup (Fin 12),
      (θ xH : Equiv.Perm (Fin 12)) = pOne ∧ (θ yH : Equiv.Perm (Fin 12)) = pTwo ∧
        ∀ (h : Hx) (k : Fin 462), labP (phiW h k) = (θ h : Equiv.Perm (Fin 12)) • labP k :=
  exists_mulEquiv_alt phiW phiW_injective xH yH closure_xyH labP labP_injective pOne pTwo
    pOne_even pTwo_even labP_xH labP_yH (by rw [squeeze.2.1]; decide +kernel)

theorem alt_action_faithful (σ τ : alternatingGroup (Fin 12))
    (h : ∀ S : Part, (σ : Equiv.Perm (Fin 12)) • S = (τ : Equiv.Perm (Fin 12)) • S) : σ = τ :=
  natHom_alt_injective (Equiv.ext fun S => h S)

noncomputable def thetaH :
    Hx ≃* alternatingGroup (Fin 12) := theta_exists_aux.2.choose

theorem thetaH_xH :
    (thetaH xH : Equiv.Perm (Fin 12)) = pOne := theta_exists_aux.2.choose_spec.1

theorem thetaH_yH :
    (thetaH yH : Equiv.Perm (Fin 12)) = pTwo := theta_exists_aux.2.choose_spec.2.1

theorem thetaH_equivariant
    (h : Hx) (k : Fin 462) : labP (phiW h k) = (thetaH h : Equiv.Perm (Fin 12)) • labP k :=
  theta_exists_aux.2.choose_spec.2.2 h k

@[expose] noncomputable def thetaS :
    stabHN ≃* alternatingGroup (Fin 12) :=
  (MulEquiv.subgroupCongr Hx_eq.symm).trans thetaH

theorem thetaS_apply (h : stabHN) :
    thetaS h = thetaH ⟨h.1, by rw [Hx_eq]; exact h.2⟩ := rfl

theorem mem_Hx_of_stab
    {g : J dHN} (hg : g ∈ stabHN) : g ∈ Hx := by
  rw [Hx_eq]
  exact hg

theorem thetaS_of_action
    {g : J dHN} (hg : g ∈ stabHN) {σ : Fin 462 → Fin 462} {ρ : alternatingGroup (Fin 12)}
    (hσ : ∀ k, g • hnW k = hnW (σ k)) (hρ : ∀ k, labP (σ k) = (ρ : Equiv.Perm (Fin 12)) • labP k) :
    thetaS ⟨g, hg⟩ = ρ := by
  apply alt_action_faithful
  intro S
  obtain ⟨k, rfl⟩ := labP_bijective.2 S
  rw [thetaS_apply, ← thetaH_equivariant, phiW_eq (h := ⟨g, mem_Hx_of_stab hg⟩) hσ, hρ]

theorem ctuc_hn_point_stabilizer_alternating_twelve :
    stabHN = Subgroup.closure {wG 2, wG 3} ∧ Nat.card stabHN = 239500800 ∧
      (∀ hx : wG 2 ∈ stabHN, (thetaS ⟨wG 2, hx⟩ : Equiv.Perm (Fin 12)) = pOne) ∧
      (∀ hy : wG 3 ∈ stabHN, (thetaS ⟨wG 3, hy⟩ : Equiv.Perm (Fin 12)) = pTwo) :=
  ⟨Hx_eq.symm, card_stabHN, fun _ => thetaH_xH, fun _ => thetaH_yH⟩

end CFSG.Sporadic.HN.Local
