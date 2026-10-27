module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKK1IDefs
public import CFSG.LocalAnalysis.StandardType.GGSixRCKC1LemmaHTriD4
public import CFSG.GH74.GLS.Stage4.HexModelD4

public section

namespace CFSG.StandardType.RCKK1I

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Universal
  CFSG.LieType.RootSystem CFSG.StandardType CFSG.SeitzReduction
  CFSG.StandardType.S2MathFi1035Pos CFSG.StandardType.RCKC1 CFSG.StandardType.RCKRP
  CFSG.StandardType.LieOddCover CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.Steinberg.TwistedD4
open CFSG.Open (StatedLieTag StatedLieAdmissible)
open CFSG.StandardType.RCKSmall (RCKSmallTag)

theorem rckK1I_rootField_triD4
    {F : Type} [Field F] [Finite F] {σ : F →+* F} {g : ℕ} (hF : TriField F σ g) :
    ∃ β : Fin (triD4Universal F σ).D.rank → ℤ, β ∈ (triD4Universal F σ).D.roots ∧
      GGLongRoot (triD4Universal F σ).D β ∧
      ∃ (Fq : Type) (_ : Field Fq) (_ : Finite Fq) (ε : Multiplicative Fq ≃* (triD4Universal F σ).D.rootGroup β),
        Nat.card Fq = 2 ^ g ∧ RCKRootFieldExact ((triD4Universal F σ).D.rootGroup β) Fq ε := by
  haveI hchar : CharP F 2 := CFSG.StandardType.RCKC1.charP_two_of_triField hF
  have hσ : ∀ c, σ (σ (σ c)) = c := sigma_three_of_card hF.2.1 hF.2.2
  have hconj : ∀ (t : Fˣ) (c : F),
      torusElement d4 F (nd 2) t * xPar (rootOperatorFamily d4) (Pi.single (nd 2) 1) c *
        (torusElement d4 F (nd 2) t)⁻¹ =
      xPar (rootOperatorFamily d4) (Pi.single (nd 2) 1) (((t : F)) ^ 2 * c) := by
    intro t c
    rw [xPar_of_isRoot (isRoot_single d4 (nd 2)) c,
      xPar_of_isRoot (isRoot_single d4 (nd 2)) (((t : F)) ^ 2 * c)]
    rw [(rootOperatorFamily d4).torusElement_mul_eltElement_mul_inv (nd 2) t
      ⟨Pi.single (nd 2) 1, isRoot_single d4 (nd 2)⟩ c]
    rw [show (∑ j, d4.cartan (nd 2) j * (Pi.single (nd 2) 1 : Fin d4.rank → ℤ) j) = 2 by
      decide +kernel]
    rw [zpow_ofNat, Units.val_pow_eq_pow_val]
  have hsq : Function.Surjective (fun t : fixedUnits σ => t * t) := by
    haveI : Finite (fixedUnits σ) := inferInstance
    have hsq1 : ∀ x : Fˣ, x * x = 1 → x = 1 := by
      intro x hx
      have hx' : (x : F) * (x : F) = 1 := by simpa using congrArg (fun u : Fˣ => (u : F)) hx
      rcases (mul_self_eq_one_iff (a := (x : F))).1 hx' with h | h
      · exact Units.ext h
      · refine Units.ext ?_
        rw [h]
        exact CharTwo.neg_eq 1
    have hinj : Function.Injective (fun t : fixedUnits σ => t * t) := by
      intro s t hst
      apply Subtype.ext
      have hst' : (s : Fˣ) * (s : Fˣ) = (t : Fˣ) * (t : Fˣ) := by
        simpa only [Subgroup.coe_mul] using congrArg Subtype.val hst
      have h1 : ((s : Fˣ) * (t : Fˣ)⁻¹) * ((s : Fˣ) * (t : Fˣ)⁻¹) = 1 := by
        calc ((s : Fˣ) * (t : Fˣ)⁻¹) * ((s : Fˣ) * (t : Fˣ)⁻¹)
              = ((s : Fˣ) * (s : Fˣ)) * ((t : Fˣ)⁻¹ * (t : Fˣ)⁻¹) := by ac_rfl
          _ = ((t : Fˣ) * (t : Fˣ)) * ((t : Fˣ)⁻¹ * (t : Fˣ)⁻¹) := by rw [hst']
          _ = 1 := by rw [← mul_inv_rev, mul_inv_cancel]
      have h2 : (s : Fˣ) * (t : Fˣ)⁻¹ = 1 := hsq1 _ h1
      rwa [mul_inv_eq_one] at h2
    exact Finite.surjective_of_injective hinj
  let β : Fin (triD4Universal F σ).D.rank → ℤ := Pi.single (ng 0) 1
  have hβmem : β ∈ (triD4Universal F σ).D.roots := by
    change β ∈ (twistedDatum σ).roots
    rw [twistedDatum_roots]
    exact IsRoot.basis (ng 0)
  have hβlong : GGLongRoot (triD4Universal F σ).D β := by
    change GGLongRoot (twistedDatum σ) β
    refine ⟨simple .G2 (ng 1) * simple .G2 (ng 0), highRoot .G2, ?_, ?_, ?_⟩
    · rw [twistedDatum_roots]; exact isRoot_highRoot .G2
    · intro δ hδ
      rw [twistedDatum_roots] at hδ
      exact height_le_height_highRoot hδ
    · exact (show (simple .G2 (ng 1) * simple .G2 (ng 0)) • highRoot .G2 = Pi.single (ng 0) 1 by
        simp only [mul_smul, simple_smul]; decide +kernel).symm
  have hCent : RCKLemmaHCent ⟨↥(twistedGroup σ), twistedDatum σ⟩ β :=
    rckHB_cent_triD4 hF hβlong
  let xβ : fixedField σ → twistedRootGroup σ β := fun c =>
    ⟨⟨xPar (rootOperatorFamily d4) (Pi.single (nd 2) 1) (c : F),
        twistedRootSubgroupD4_le_twistedGroup σ (IsRoot.basis (ng 0))
          (xPar_single_two_mem_twisted hσ c.2)⟩,
      (mem_twistedRootGroup (σ := σ)).2 (xPar_single_two_mem_twisted hσ c.2)⟩
  have hxβ : ∀ c : fixedField σ,
      ((xβ c : twistedRootGroup σ β) : adjointGroup d4 F) =
        xPar (rootOperatorFamily d4) (Pi.single (nd 2) 1) (c : F) := fun c => rfl
  let εhom : Multiplicative (fixedField σ) →* twistedRootGroup σ β :=
    { toFun := fun c => xβ (Multiplicative.toAdd c)
      map_one' := by
        apply Subtype.ext
        apply Subtype.ext
        change xPar (rootOperatorFamily d4) (Pi.single (nd 2) 1) (0 : F) = 1
        rw [xPar_zero]
      map_mul' := fun c d => by
        apply Subtype.ext
        apply Subtype.ext
        simp only [Subgroup.coe_mul, hxβ]
        change xPar (rootOperatorFamily d4) (Pi.single (nd 2) 1)
            (((Multiplicative.toAdd c : fixedField σ) : F) +
              ((Multiplicative.toAdd d : fixedField σ) : F)) =
          xPar (rootOperatorFamily d4) (Pi.single (nd 2) 1)
            ((Multiplicative.toAdd c : fixedField σ) : F) *
          xPar (rootOperatorFamily d4) (Pi.single (nd 2) 1)
            ((Multiplicative.toAdd d : fixedField σ) : F)
        rw [xPar_add] }
  have hinj : Function.Injective εhom := by
    intro c d h
    have hv : xPar (rootOperatorFamily d4) (Pi.single (nd 2) 1)
          ((Multiplicative.toAdd c : fixedField σ) : F) =
        xPar (rootOperatorFamily d4) (Pi.single (nd 2) 1)
          ((Multiplicative.toAdd d : fixedField σ) : F) := by
      have h1 : ((εhom c : twistedRootGroup σ β) : adjointGroup d4 F) =
          ((εhom d : twistedRootGroup σ β) : adjointGroup d4 F) :=
        congrArg (fun z : twistedRootGroup σ β => (z : adjointGroup d4 F)) h
      change ((xβ (Multiplicative.toAdd c) : twistedRootGroup σ β) : adjointGroup d4 F) =
        ((xβ (Multiplicative.toAdd d) : twistedRootGroup σ β) : adjointGroup d4 F) at h1
      simpa only [hxβ] using h1
    have hcdF : ((Multiplicative.toAdd c : fixedField σ) : F) =
        ((Multiplicative.toAdd d : fixedField σ) : F) :=
      xPar_injective (isRoot_single d4 (nd 2)) hv
    have hcd : Multiplicative.toAdd c = Multiplicative.toAdd d := Subtype.ext hcdF
    calc c = Multiplicative.ofAdd (Multiplicative.toAdd c) := rfl
      _ = Multiplicative.ofAdd (Multiplicative.toAdd d) := by rw [hcd]
      _ = d := rfl
  have hsurj : Function.Surjective εhom := by
    intro x
    have hx : (x : adjointGroup d4 F) ∈ twistedRootSubgroupD4 σ β :=
      (mem_twistedRootGroup (σ := σ)).1 x.2
    obtain ⟨c, hc, hxc⟩ := (mem_twistedRootSubgroupD4_iff_of_fixed hσ
      (isRoot_single d4 (nd 2)) proj_single_two rho_single_two (x : adjointGroup d4 F)).1 hx
    refine ⟨Multiplicative.ofAdd ⟨c, hc⟩, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    change xPar (rootOperatorFamily d4) (Pi.single (nd 2) 1) c = (x : adjointGroup d4 F)
    exact hxc.symm
  let ε : Multiplicative (fixedField σ) ≃* twistedRootGroup σ β :=
    MulEquiv.ofBijective εhom ⟨hinj, hsurj⟩
  have hε : ∀ c : fixedField σ,
      ((ε (Multiplicative.ofAdd c) : twistedRootGroup σ β) : adjointGroup d4 F) =
        xPar (rootOperatorFamily d4) (Pi.single (nd 2) 1) (c : F) := fun c => hxβ c
  refine ⟨β, hβmem, hβlong, ↥(fixedField σ), inferInstance, inferInstance, ε, ?_, ?_⟩
  · exact CFSG.GH74.GLS.Stage4.Hex.card_fixedField_of_cube σ
      (by have h1 : (1 : ℕ) ≤ g := hF.1
          calc (2 : ℕ) = 2 ^ 1 := by norm_num
            _ ≤ 2 ^ g := Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) h1) hF.2.1 hF.2.2
  · change (∀ l : fixedField σ, l ≠ 0 → ∃ h : twistedGroup σ, ∀ t : fixedField σ,
        h * (ε (Multiplicative.ofAdd t) : twistedGroup σ) * h⁻¹ =
          ε (Multiplicative.ofAdd (l * t))) ∧
      ∀ n ∈ Subgroup.normalizer (twistedRootGroup σ β : Set (twistedGroup σ)),
        ∃ l : fixedField σ, l ≠ 0 ∧ ∀ t : fixedField σ,
          n * (ε (Multiplicative.ofAdd t) : twistedGroup σ) * n⁻¹ =
            ε (Multiplicative.ofAdd (l * t))
    refine ⟨?_, ?_⟩
    ·
      intro l hl
      have hlF : (l : F) ≠ 0 := by intro h; exact hl (Subtype.ext h)
      have hlfix : σ (l : F) = (l : F) := l.2
      let lu : fixedUnits σ := ⟨Units.mk0 (l : F) hlF, by
        rw [mem_fixedUnits]
        exact hlfix⟩
      obtain ⟨t, ht⟩ := hsq lu
      have ht2 : ((t : Fˣ) : F) * ((t : Fˣ) : F) = (l : F) := by
        have hh := congrArg (fun u : fixedUnits σ => ((u : Fˣ) : F)) ht
        simpa only [lu, Subgroup.coe_mul, Units.val_mul, Units.val_mk0] using hh
      obtain ⟨h, _, hh_val⟩ := exists_hLongElt (σ := σ) ((mem_fixedUnits σ).1 t.2)
      refine ⟨h, fun s => ?_⟩
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, hε]
      rw [hh_val, hconj t (s : F)]
      congr 1
      rw [pow_two, ht2]
      rfl
    ·
      intro n hn
      let x₀ : twistedRootGroup σ β := ε (Multiplicative.ofAdd 1)
      have hx₀_ne : x₀ ≠ 1 := by
        intro h
        have hv : xPar (rootOperatorFamily d4) (Pi.single (nd 2) 1) (1 : F) = 1 := by
          have := congrArg (fun z : twistedRootGroup σ β => (z : adjointGroup d4 F)) h
          simpa [x₀, hε] using this
        have h1 : (1 : F) = 0 := xPar_injective (isRoot_single d4 (nd 2)) (by
          simpa [xPar_zero] using hv)
        exact one_ne_zero h1
      have hx₀_ne' : (x₀ : twistedGroup σ) ≠ 1 := fun h => hx₀_ne (Subtype.ext h)
      let y : twistedRootGroup σ β :=
        ⟨n * (x₀ : twistedGroup σ) * n⁻¹, (Subgroup.mem_normalizer_iff.1 hn x₀).1 x₀.2⟩
      have hy_ne : y ≠ 1 := by
        intro h
        apply hx₀_ne
        apply Subtype.ext
        calc (x₀ : twistedGroup σ)
            = n⁻¹ * (n * (x₀ : twistedGroup σ) * n⁻¹) * n := by group
          _ = n⁻¹ * (y : twistedGroup σ) * n := rfl
          _ = n⁻¹ * 1 * n := by rw [h]; rfl
          _ = 1 := by group
      let d : fixedField σ := Multiplicative.toAdd (ε.symm y)
      have hd_eq : ε (Multiplicative.ofAdd d) = y := by
        change ε (ε.symm y) = y
        exact ε.apply_symm_apply y
      have hd_ne : d ≠ 0 := by
        intro h
        apply hy_ne
        rw [← hd_eq, h]
        simpa using map_one ε
      have hdF_ne : (d : F) ≠ 0 := by intro h; exact hd_ne (Subtype.ext h)
      have hdfix : σ (d : F) = (d : F) := d.2
      let du : fixedUnits σ := ⟨Units.mk0 (d : F) hdF_ne, by
        rw [mem_fixedUnits]
        exact hdfix⟩
      obtain ⟨t, ht⟩ := hsq du
      have ht2 : ((t : Fˣ) : F) * ((t : Fˣ) : F) = (d : F) := by
        have hh := congrArg (fun u : fixedUnits σ => ((u : Fˣ) : F)) ht
        simpa only [du, Subgroup.coe_mul, Units.val_mul, Units.val_mk0] using hh
      obtain ⟨h, _, hh_val⟩ := exists_hLongElt (σ := σ) ((mem_fixedUnits σ).1 t.2)
      have hh_conj : ∀ s : fixedField σ, h * ε (Multiplicative.ofAdd s) * h⁻¹ =
          ε (Multiplicative.ofAdd (d * s)) := by
        intro s
        apply Subtype.ext
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, hε]
        rw [hh_val, hconj t (s : F)]
        congr 1
        rw [pow_two, ht2]
        rfl
      have hhx : h * x₀ * h⁻¹ = y := by
        rw [← hd_eq]
        simpa [x₀, mul_one] using hh_conj 1
      have hcent_singleton : h⁻¹ * n ∈
          Subgroup.centralizer ({(x₀ : twistedGroup σ)} : Set (twistedGroup σ)) := by
        rw [Subgroup.mem_centralizer_singleton_iff]
        have hhx' : h * (x₀ : twistedGroup σ) * h⁻¹ = n * (x₀ : twistedGroup σ) * n⁻¹ := by
          simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using hhx
        have hconj' : (h⁻¹ * n) * (x₀ : twistedGroup σ) * (h⁻¹ * n)⁻¹ = (x₀ : twistedGroup σ) := by
          calc (h⁻¹ * n) * (x₀ : twistedGroup σ) * (h⁻¹ * n)⁻¹
              = h⁻¹ * (n * (x₀ : twistedGroup σ) * n⁻¹) * h := by group
            _ = h⁻¹ * (h * (x₀ : twistedGroup σ) * h⁻¹) * h := by rw [← hhx']
            _ = (x₀ : twistedGroup σ) := by group
        calc (h⁻¹ * n) * (x₀ : twistedGroup σ)
            = ((h⁻¹ * n) * (x₀ : twistedGroup σ) * (h⁻¹ * n)⁻¹) * (h⁻¹ * n) := by group
          _ = (x₀ : twistedGroup σ) * (h⁻¹ * n) := by rw [hconj']
      have hcentX : h⁻¹ * n ∈
          Subgroup.centralizer (twistedRootGroup σ β : Set (twistedGroup σ)) :=
        hCent (x₀ : twistedGroup σ) x₀.2 hx₀_ne' hcent_singleton
      have hcomm_s : ∀ s : fixedField σ,
          (h⁻¹ * n) * ε (Multiplicative.ofAdd s) = ε (Multiplicative.ofAdd s) * (h⁻¹ * n) := by
        intro s
        have := (Subgroup.mem_centralizer_iff.1 hcentX) (ε (Multiplicative.ofAdd s))
          (ε (Multiplicative.ofAdd s)).2
        rw [this]
      refine ⟨d, hd_ne, fun s => ?_⟩
      calc n * ε (Multiplicative.ofAdd s) * n⁻¹
          = h * ((h⁻¹ * n) * ε (Multiplicative.ofAdd s) * (h⁻¹ * n)⁻¹) * h⁻¹ := by group
        _ = h * ε (Multiplicative.ofAdd s) * h⁻¹ := by rw [hcomm_s s]; group
        _ = ε (Multiplicative.ofAdd (d * s)) := hh_conj s

end CFSG.StandardType.RCKK1I
