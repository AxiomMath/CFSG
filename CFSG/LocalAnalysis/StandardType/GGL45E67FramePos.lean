module

public import CFSG.LocalAnalysis.StandardType.GGE6ThreeModelFrame
public import CFSG.LocalAnalysis.StandardType.GGL45NtDefs
public import CFSG.RankThree.PartOne.KE.A1Weyl
public import CFSG.RankThree.PartOne.KE.A1SL2
public import CFSG.RankThree.PartOne.KE.A1Torus
public import CFSG.RankThree.PartOne.KE.A1Untwisted

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.RankThree.PartOne.KE

private theorem ggL45E67_frame_rho_theta {τ : Tag} {L : Type} [Field L]
    {H : Subgroup (ModGL τ L)} {R : Type} [Group R] (ρ : R →* ModGL τ L)
    (Θ : H →* MulAut R) (hρinj : Function.Injective ρ) (hρH : ∀ r, ρ r ∈ H)
    (hρΘ : ∀ g r, ρ (Θ g r) = g * ρ r * (g : ModGL τ L)⁻¹) (r : R) :
    Θ ⟨ρ r, hρH r⟩ = MulAut.conj r := by
  refine MulEquiv.ext fun y => ?_
  apply hρinj
  calc ρ (Θ ⟨ρ r, hρH r⟩ y) = ρ r * ρ y * (ρ r)⁻¹ := hρΘ _ y
    _ = ρ (MulAut.conj r y) := by rw [MulAut.conj_apply, map_mul, map_mul, map_inv]

private theorem ggL45E67_frame_conj_mem_torus
    {τ : Tag} {L : Type} [Field L]
    {H : Subgroup (ModGL τ L)} (hHG : H ≤ adjointGroup τ L)
    {R : Type} [Group R] (Θ : H →* MulAut R) (hΘ : Function.Injective Θ)
    {K : Type} [Group K] (θ : K ⧸ Subgroup.center K ≃* R) {E : Subgroup (MulAut K)}
    {x : ModGL τ L} (hx : x ∈ adjointGroup τ L)
    (hcent : adjointGroup τ L ⊓ Subgroup.centralizer
      ((((E.map (ggInducedAut θ)).comap Θ).map H.subtype).map (MulAut.conj x⁻¹).toMonoidHom :
        Set (ModGL τ L)) = torusGroup τ L)
    {h : H} (hcomm : ∀ e ∈ E, Θ h * ggInducedAut θ e = ggInducedAut θ e * Θ h) :
    MulAut.conj x⁻¹ (h : ModGL τ L) ∈ torusGroup τ L := by
  rw [← hcent]
  refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
  · simpa only [MulAut.conj_apply, inv_inv] using
      mul_mem (mul_mem (inv_mem hx) (hHG h.property)) hx
  · refine Subgroup.mem_centralizer_iff.mpr fun y hy => ?_
    obtain ⟨b, hb, hfb⟩ := Subgroup.mem_map.mp hy
    obtain ⟨b', hb', rfl⟩ := Subgroup.mem_map.mp hb
    obtain ⟨e, he, heq⟩ := Subgroup.mem_map.mp (Subgroup.mem_comap.mp hb')
    have hH : b' * h = h * b' := hΘ (by
      calc Θ (b' * h) = Θ b' * Θ h := map_mul Θ b' h
        _ = ggInducedAut θ e * Θ h := by rw [← heq]
        _ = Θ h * ggInducedAut θ e := (hcomm e he).symm
        _ = Θ h * Θ b' := by rw [← heq]
        _ = Θ (h * b') := (map_mul Θ h b').symm)
    have hbh : (b' : ModGL τ L) * (h : ModGL τ L) = (h : ModGL τ L) * (b' : ModGL τ L) :=
      congrArg (fun g : H => (g : ModGL τ L)) hH
    rw [← hfb]
    calc MulAut.conj x⁻¹ (b' : ModGL τ L) * MulAut.conj x⁻¹ (h : ModGL τ L)
        = MulAut.conj x⁻¹ ((b' : ModGL τ L) * (h : ModGL τ L)) :=
          (map_mul (MulAut.conj x⁻¹) _ _).symm
      _ = MulAut.conj x⁻¹ ((h : ModGL τ L) * (b' : ModGL τ L)) := by rw [hbh]
      _ = MulAut.conj x⁻¹ (h : ModGL τ L) * MulAut.conj x⁻¹ (b' : ModGL τ L) :=
          map_mul (MulAut.conj x⁻¹) _ _

private theorem ggL45E67_frame_fix_torus
    {τ : Tag} {L : Type} [Field L]
    {H : Subgroup (ModGL τ L)} (hHG : H ≤ adjointGroup τ L)
    {R : Type} [Group R] {I : Set (MulAut R)} (ρ : R →* ModGL τ L)
    (Θ : H →* MulAut R) (hρinj : Function.Injective ρ)
    (hΘ : Function.Injective Θ)
    (hρΘ : ∀ g r, ρ (Θ g r) = g * ρ r * (g : ModGL τ L)⁻¹)
    (hI : ∀ φ, φ ∈ I ↔ ∃ g, Θ g = φ)
    {K : Type} [Group K] (θ : K ⧸ Subgroup.center K ≃* R) {E : Subgroup (MulAut K)}
    {x : ModGL τ L} (hx : x ∈ adjointGroup τ L)
    (hcent : adjointGroup τ L ⊓ Subgroup.centralizer
      ((((E.map (ggInducedAut θ)).comap Θ).map H.subtype).map (MulAut.conj x⁻¹).toMonoidHom :
        Set (ModGL τ L)) = torusGroup τ L)
    {D : E6ThreeModel.FrameData R}
    (hTor : ∀ r, r ∈ D.Tor ↔ x⁻¹ * ρ r * x ∈ torusGroup τ L)
    {u : MulAut R} (hu : u ∈ I)
    (hcomm : ∀ e ∈ E, u * ggInducedAut θ e = ggInducedAut θ e * u)
    {t : R} (ht : t ∈ D.Tor) : u t = t := by
  obtain ⟨g, hgu⟩ := (hI u).mp hu
  have hcommg : ∀ e ∈ E, Θ g * ggInducedAut θ e = ggInducedAut θ e * Θ g := by
    intro e he
    rw [hgu]
    exact hcomm e he
  have hgT : MulAut.conj x⁻¹ (g : ModGL τ L) ∈ torusGroup τ L :=
    ggL45E67_frame_conj_mem_torus hHG Θ hΘ θ hx hcent hcommg
  have htT : MulAut.conj x⁻¹ (ρ t) ∈ torusGroup τ L := by
    simpa only [MulAut.conj_apply, inv_inv] using (hTor t).mp ht
  have hgt : (g : ModGL τ L) * ρ t = ρ t * (g : ModGL τ L) := by
    have hmul : MulAut.conj x⁻¹ ((g : ModGL τ L) * ρ t) =
        MulAut.conj x⁻¹ (ρ t * (g : ModGL τ L)) := by
      calc MulAut.conj x⁻¹ ((g : ModGL τ L) * ρ t)
          = MulAut.conj x⁻¹ (g : ModGL τ L) * MulAut.conj x⁻¹ (ρ t) :=
            map_mul (MulAut.conj x⁻¹) _ _
        _ = MulAut.conj x⁻¹ (ρ t) * MulAut.conj x⁻¹ (g : ModGL τ L) :=
            torusGroup_comm hgT htT
        _ = MulAut.conj x⁻¹ (ρ t * (g : ModGL τ L)) :=
            (map_mul (MulAut.conj x⁻¹) _ _).symm
    exact (MulAut.conj x⁻¹).injective hmul
  have hfix : Θ g t = t := by
    apply hρinj
    rw [hρΘ, hgt]
    exact mul_inv_cancel_right _ _
  rw [← hgu]
  exact hfix

private theorem ggL45E67_frame_inner
    {τ : Tag} {L : Type} [Field L]
    {H : Subgroup (ModGL τ L)} (hHG : H ≤ adjointGroup τ L)
    {R : Type} [Group R] {I : Set (MulAut R)} (ρ : R →* ModGL τ L)
    (Θ : H →* MulAut R) (hρinj : Function.Injective ρ) (hρH : ∀ r, ρ r ∈ H)
    (hΘ : Function.Injective Θ)
    (hρΘ : ∀ g r, ρ (Θ g r) = g * ρ r * (g : ModGL τ L)⁻¹)
    (hInv : ∀ φ ∈ I, ∃ r : R, φ ^ 3 = MulAut.conj r)
    {K : Type} [Group K] (θ : K ⧸ Subgroup.center K ≃* R) {E : Subgroup (MulAut K)}
    {x : ModGL τ L} (hx : x ∈ adjointGroup τ L)
    (hcent : adjointGroup τ L ⊓ Subgroup.centralizer
      ((((E.map (ggInducedAut θ)).comap Θ).map H.subtype).map (MulAut.conj x⁻¹).toMonoidHom :
        Set (ModGL τ L)) = torusGroup τ L)
    {D : E6ThreeModel.FrameData R}
    (hTor : ∀ r, r ∈ D.Tor ↔ x⁻¹ * ρ r * x ∈ torusGroup τ L)
    {u : MulAut R} (hu : u ∈ I)
    (hcomm : ∀ e ∈ E, u * ggInducedAut θ e = ggInducedAut θ e * u)
    (hcop : Nat.Coprime 3 (orderOf u)) : ∃ t ∈ D.Tor, u = MulAut.conj t := by
  by_cases hu1 : u = 1
  · exact ⟨1, D.Tor.one_mem, by rw [hu1, map_one]⟩
  obtain ⟨r, hr⟩ := hInv u hu
  have hm1 : 1 < orderOf u := by
    have hm0 : orderOf u ≠ 0 := by
      intro h0
      have h3 : Nat.gcd 3 0 = 1 := h0 ▸ hcop
      norm_num at h3
    have hmne : orderOf u ≠ 1 := fun h => hu1 (orderOf_eq_one_iff.mp h)
    omega
  obtain ⟨k, -, hkmod⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop hm1
  have hpow : u ^ (3 * k) = u := by
    rw [pow_eq_pow_mod (3 * k) (pow_orderOf_eq_one u), hkmod, pow_one]
  have huk : u = MulAut.conj (r ^ k) := by
    rw [← hpow, pow_mul, hr]
    exact (map_pow (MulAut.conj : R →* MulAut R) r k).symm
  have hcomm' : ∀ e ∈ E, Θ ⟨ρ (r ^ k), hρH _⟩ * ggInducedAut θ e =
      ggInducedAut θ e * Θ ⟨ρ (r ^ k), hρH _⟩ := by
    intro e he
    rw [ggL45E67_frame_rho_theta ρ Θ hρinj hρH hρΘ (r ^ k), ← huk]
    exact hcomm e he
  have hT : MulAut.conj x⁻¹ (ρ (r ^ k)) ∈ torusGroup τ L :=
    ggL45E67_frame_conj_mem_torus hHG Θ hΘ θ hx hcent hcomm'
  refine ⟨r ^ k, (hTor (r ^ k)).mpr ?_, huk⟩
  simpa only [MulAut.conj_apply, inv_inv] using hT

private theorem ggL45E67_frame_centralizer
    {τ : Tag} {L : Type} [Field L]
    {H : Subgroup (ModGL τ L)} (hHG : H ≤ adjointGroup τ L)
    {R : Type} [Group R] (ρ : R →* ModGL τ L)
    (Θ : H →* MulAut R) (hρinj : Function.Injective ρ) (hρH : ∀ r, ρ r ∈ H)
    (hΘ : Function.Injective Θ)
    (hρΘ : ∀ g r, ρ (Θ g r) = g * ρ r * (g : ModGL τ L)⁻¹)
    {K : Type} [Group K] (θ : K ⧸ Subgroup.center K ≃* R) {E : Subgroup (MulAut K)}
    {x : ModGL τ L} (hx : x ∈ adjointGroup τ L)
    (hcent : adjointGroup τ L ⊓ Subgroup.centralizer
      ((((E.map (ggInducedAut θ)).comap Θ).map H.subtype).map (MulAut.conj x⁻¹).toMonoidHom :
        Set (ModGL τ L)) = torusGroup τ L)
    {D : E6ThreeModel.FrameData R}
    (hTor : ∀ r, r ∈ D.Tor ↔ x⁻¹ * ρ r * x ∈ torusGroup τ L)
    {r : R} (hfix : ∀ e ∈ E, ggInducedAut θ e r = r) : r ∈ D.Tor := by
  have hcomm : ∀ e ∈ E, Θ ⟨ρ r, hρH r⟩ * ggInducedAut θ e =
      ggInducedAut θ e * Θ ⟨ρ r, hρH r⟩ := by
    intro e he
    rw [ggL45E67_frame_rho_theta ρ Θ hρinj hρH hρΘ r]
    ext y
    simp [MulAut.conj_apply, hfix e he]
  refine (hTor r).mpr ?_
  simpa only [MulAut.conj_apply, inv_inv] using
    ggL45E67_frame_conj_mem_torus hHG Θ hΘ θ hx hcent hcomm

theorem ggL45E67_frame_pos
    {τ : Tag} {L : Type} [Field L] {H : Subgroup (ModGL τ L)} (hHG : H ≤ adjointGroup τ L)
    {R : Type} [Group R] {I : Set (MulAut R)} (ρ : R →* ModGL τ L)
    (Θ : H →* MulAut R) (hρinj : Function.Injective ρ) (hρH : ∀ r, ρ r ∈ H)
    (hΘ : Function.Injective Θ) (hI : ∀ φ, φ ∈ I ↔ ∃ g, Θ g = φ)
    (hρΘ : ∀ g r, ρ (Θ g r) = g * ρ r * (g : ModGL τ L)⁻¹)
    (hInv : ∀ φ ∈ I, ∃ r : R, φ ^ 3 = MulAut.conj r)
    {K : Type} [Group K] (θ : K ⧸ Subgroup.center K ≃* R) {E : Subgroup (MulAut K)}
    {x : ModGL τ L} (hx : x ∈ adjointGroup τ L)
    (hcent : adjointGroup τ L ⊓ Subgroup.centralizer
      ((((E.map (ggInducedAut θ)).comap Θ).map H.subtype).map (MulAut.conj x⁻¹).toMonoidHom :
        Set (ModGL τ L)) = torusGroup τ L)
    (D : E6ThreeModel.FrameData R) (hTor : ∀ r, r ∈ D.Tor ↔ x⁻¹ * ρ r * x ∈ torusGroup τ L) :
    (∃ J : Subgroup (MulAut R), (J : Set (MulAut R)) = I) ∧ (∀ t ∈ D.Tor, MulAut.conj t ∈ I) ∧
      (∀ u ∈ I, (∀ e ∈ E, u * ggInducedAut θ e = ggInducedAut θ e * u) → ∀ t ∈ D.Tor, u t = t) ∧
      (∀ u ∈ I, (∀ e ∈ E, u * ggInducedAut θ e = ggInducedAut θ e * u) →
        Nat.Coprime 3 (orderOf u) → ∃ t ∈ D.Tor, u = MulAut.conj t) ∧
      (∀ r : R, (∀ e ∈ E, ggInducedAut θ e r = r) → r ∈ D.Tor) := by
  refine ⟨⟨Θ.range, ?_⟩, ?_, ?_, ?_, ?_⟩
  · ext φ
    exact Iff.trans MonoidHom.mem_range (hI φ).symm
  · intro t ht
    exact (hI _).mpr ⟨⟨ρ t, hρH t⟩, ggL45E67_frame_rho_theta ρ Θ hρinj hρH hρΘ t⟩
  · intro u hu hcomm t ht
    exact ggL45E67_frame_fix_torus hHG ρ Θ hρinj hΘ hρΘ hI θ hx hcent hTor hu hcomm ht
  · intro u hu hcomm hcop
    exact ggL45E67_frame_inner hHG ρ Θ hρinj hρH hΘ hρΘ hInv θ hx hcent hTor hu hcomm hcop
  · intro r hr
    exact ggL45E67_frame_centralizer hHG ρ Θ hρinj hρH hΘ hρΘ θ hx hcent hTor hr

end CFSG.StandardType
