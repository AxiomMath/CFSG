module

public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2TriD4InnerAction

public section

namespace CFSG.StandardType.LieKnownR2.TriD4.Inner

open CFSG.Open CFSG.StandardType CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Universal
  CFSG.LieType.RootSystem CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.Steinberg.TwistedD4 CFSG.SeitzReduction
open CFSG.StandardType.RootCentExc
open CFSG.StandardType.LieKnownR2.TriD4.Bridge
open CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

private theorem tchar_coe_xPar_highRoot
    {K : Type} [Field K] (c : K) :
    ((xPar (rootOperatorFamily d4) (highRoot d4) c : adjointGroup d4 K) : ModGL d4 K) =
      pinnedX d4 K (highRoot d4)
        (((rootOperatorFamily d4).pinnedFamilySign (highRoot d4) : K) * c) := by
  have h2 : pinnedX d4 K (highRoot d4)
        (((rootOperatorFamily d4).pinnedFamilySign (highRoot d4) : K) * c) =
      (rootOperatorFamily d4).eltUnit K ⟨highRoot d4, isRoot_highRoot d4⟩ c := by
    rw [(rootOperatorFamily d4).pinnedX_eq_eltUnit K (isRoot_highRoot d4)]
    rw [← mul_assoc, (rootOperatorFamily d4).pinnedFamilySign_mul_self, one_mul]
  rw [xPar_of_isRoot (isRoot_highRoot d4)]
  exact h2.symm

private theorem tchar_borel_action
    {K : Type} [Field K] {σ : K →+* K} (hsurj : Function.Surjective σ) {b : ModGL d4 K}
    (hb : b ∈ graphFixedBorel TwistTag.D4 K σ) :
    ∃ χ : K, ∀ c : K, b * pinnedX d4 K (highRoot d4) c * b⁻¹ =
      pinnedX d4 K (highRoot d4) (χ * c) := by
  have hθ : IsRoot d4 (highRoot d4) := isRoot_highRoot d4
  have hmax : IsMaxHeight d4 (highRoot d4) := isMaxHeight_highRoot d4
  have hbS : b ∈ (graphFixedBorel TwistTag.D4 K σ : Set (ModGL d4 K)) := hb
  rw [graphFixedBorel_eq_mul hsurj] at hbS
  obtain ⟨h, hh, u, hu, rfl⟩ := hbS
  obtain ⟨a, ha⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup (τ := d4) (Subgroup.mem_inf.1 hh).1
  refine ⟨(rootChar a (highRoot d4) : K), fun c => ?_⟩
  have hucomm : u * pinnedX d4 K (highRoot d4) c * u⁻¹ = pinnedX d4 K (highRoot d4) c := by
    rw [(commute_of_mem_posUnipotent hmax (Subgroup.mem_inf.1 hu).1 c).eq, mul_inv_cancel_right]
  calc (h * u) * pinnedX d4 K (highRoot d4) c * (h * u)⁻¹
      = h * (u * pinnedX d4 K (highRoot d4) c * u⁻¹) * h⁻¹ := by group
    _ = h * pinnedX d4 K (highRoot d4) c * h⁻¹ := by rw [hucomm]
    _ = pinnedX d4 K (highRoot d4) ((rootChar a (highRoot d4) : K) * c) := by
        rw [ha, rootDiagUnit_conj_pinnedX a hθ c]

private theorem tchar_scalar
    {K : Type} [Field K] (σ : K ≃+* K) (hσ : ∀ c, σ (σ (σ c)) = c)
    {g : ModGL d4 K}
    (hgΓ : g ∈ twistedFixedGroup TwistTag.D4 K σ.toRingHom)
    (hy : g * pinnedX d4 K (highRoot d4)
        (((rootOperatorFamily d4).pinnedFamilySign (highRoot d4) : K)) * g⁻¹ ∈
      (rootSubgroup d4 K (highRoot d4) ⊓
        twistedFixedGroup TwistTag.D4 K σ.toRingHom)) :
    ∃ ν : K, σ ν = ν ∧ ν ≠ 0 ∧
      ∀ c : K, g * pinnedX d4 K (highRoot d4) c * g⁻¹ =
        pinnedX d4 K (highRoot d4) (ν * c) := by
  have hsurj : Function.Surjective σ.toRingHom := σ.surjective
  have hθ : IsRoot d4 (highRoot d4) := isRoot_highRoot d4
  have hmax : IsMaxHeight d4 (highRoot d4) := isMaxHeight_highRoot d4
  have hρθ : rho (highRoot d4) = highRoot d4 := by decide
  let s : K := ((rootOperatorFamily d4).pinnedFamilySign (highRoot d4) : K)
  have hs2 : s * s = 1 := (rootOperatorFamily d4).pinnedFamilySign_mul_self K (highRoot d4)
  have hs0 : s ≠ 0 := fun h => by rw [h, zero_mul] at hs2; exact zero_ne_one hs2
  have hxs_ne : pinnedX d4 K (highRoot d4) s ≠ 1 := by
    intro h
    have h1 : pinnedX d4 K (highRoot d4) s = pinnedX d4 K (highRoot d4) 0 :=
      h.trans (pinnedX_zero d4 K (highRoot d4)).symm
    exact hs0 ((pinnedX_injective (R := K) (α := highRoot d4)) h1)
  have hgU : g ∈ ⋃ w : relWeylTwist TwistTag.D4,
      graphFixedBruhatCell TwistTag.D4 K σ.toRingHom w := by
    rw [← twistedFixedGroup_eq_iUnion_graphFixedBruhatCell hsurj]
    exact hgΓ
  obtain ⟨w, hw⟩ := Set.mem_iUnion.1 hgU
  obtain ⟨b, hb, b', hb', rfl⟩ := mem_graphFixedBruhatCell.1 hw
  let R := canonicalRep (coxeterSystem d4) K (w : WeylGroup d4)
  have hbB : b ∈ borelGroup d4 K := (Subgroup.mem_inf.1 hb).1
  have hb'B : b' ∈ borelGroup d4 K := (Subgroup.mem_inf.1 hb').1
  have hN := borelGroup_le_normalizer_rootSubgroup (τ := d4) (K := K) hmax
  have hb'x : b' * pinnedX d4 K (highRoot d4) s * b'⁻¹ ∈ rootSubgroup d4 K (highRoot d4) :=
    (Subgroup.mem_normalizer_iff.1 (hN hb'B) (pinnedX d4 K (highRoot d4) s)).1
      (CFSG.Blueprint.Chevalley.mem_rootSubgroup.2 ⟨s, rfl⟩)
  obtain ⟨d, hd⟩ := CFSG.Blueprint.Chevalley.mem_rootSubgroup.1 hb'x
  have hd0 : d ≠ 0 := by
    intro hdzero
    apply hxs_ne
    have h1 : b' * pinnedX d4 K (highRoot d4) s * b'⁻¹ = 1 := by
      rw [← hd, hdzero, pinnedX_zero]
    calc pinnedX d4 K (highRoot d4) s
        = b'⁻¹ * (b' * pinnedX d4 K (highRoot d4) s * b'⁻¹) * b' := by group
      _ = 1 := by rw [h1]; group
  have hb'conj : b' * pinnedX d4 K (highRoot d4) s * b'⁻¹ = pinnedX d4 K (highRoot d4) d := hd.symm
  have hconj_eq : (b * R * b') * pinnedX d4 K (highRoot d4) s * (b * R * b')⁻¹ =
      b * (R * pinnedX d4 K (highRoot d4) d * R⁻¹) * b⁻¹ := by
    calc (b * R * b') * pinnedX d4 K (highRoot d4) s * (b * R * b')⁻¹
        = b * (R * (b' * pinnedX d4 K (highRoot d4) s * b'⁻¹) * R⁻¹) * b⁻¹ := by group
      _ = b * (R * pinnedX d4 K (highRoot d4) d * R⁻¹) * b⁻¹ := by rw [hb'conj]
  have hmemθ : b * (R * pinnedX d4 K (highRoot d4) d * R⁻¹) * b⁻¹ ∈
      rootSubgroup d4 K (highRoot d4) := by
    rw [← hconj_eq]
    exact (Subgroup.mem_inf.1 hy).1
  obtain ⟨ε, hε, hεact⟩ :=
    exists_canonicalRep_mul_pinnedX_mul_inv (τ := d4) K (w : WeylGroup d4) hθ
  have hεd : R * pinnedX d4 K (highRoot d4) d * R⁻¹ =
      pinnedX d4 K ((w : WeylGroup d4) • highRoot d4) (ε * d) := hεact d
  rw [hεd] at hmemθ
  have hmem2 : pinnedX d4 K ((w : WeylGroup d4) • highRoot d4) (ε * d) ∈
      rootSubgroup d4 K (highRoot d4) :=
    (Subgroup.mem_normalizer_iff.1 (hN hbB)
      (pinnedX d4 K ((w : WeylGroup d4) • highRoot d4) (ε * d))).2 hmemθ
  obtain ⟨f, hf⟩ := CFSG.Blueprint.Chevalley.mem_rootSubgroup.1 hmem2
  have hε0 : ε ≠ 0 := fun h => by rw [h, zero_mul] at hε; exact zero_ne_one hε
  have hwθ : (w : WeylGroup d4) • highRoot d4 = highRoot d4 :=
    eq_of_pinnedX_eq hmax.1 hmax.height_pos (IsRoot.smul hθ (w : WeylGroup d4))
      (mul_ne_zero hε0 hd0) hf.symm
  obtain ⟨χ, hχ⟩ := tchar_borel_action hsurj hb
  obtain ⟨χ', hχ'⟩ := tchar_borel_action hsurj hb'
  have hformula : ∀ c : K, (b * R * b') * pinnedX d4 K (highRoot d4) c * (b * R * b')⁻¹ =
      pinnedX d4 K (highRoot d4) ((χ * ε * χ') * c) := by
    intro c
    calc (b * R * b') * pinnedX d4 K (highRoot d4) c * (b * R * b')⁻¹
        = b * (R * (b' * pinnedX d4 K (highRoot d4) c * b'⁻¹) * R⁻¹) * b⁻¹ := by group
      _ = b * (R * pinnedX d4 K (highRoot d4) (χ' * c) * R⁻¹) * b⁻¹ := by rw [hχ' c]
      _ = b * pinnedX d4 K ((w : WeylGroup d4) • highRoot d4) (ε * (χ' * c)) * b⁻¹ := by
          rw [hεact (χ' * c)]
      _ = b * pinnedX d4 K (highRoot d4) (ε * (χ' * c)) * b⁻¹ := by rw [hwθ]
      _ = pinnedX d4 K (highRoot d4) (χ * (ε * (χ' * c))) := by rw [hχ (ε * (χ' * c))]
      _ = pinnedX d4 K (highRoot d4) ((χ * ε * χ') * c) := by congr 1; ring
  have hΓmem : pinnedX d4 K (highRoot d4) ((χ * ε * χ') * s) ∈
      twistedFixedGroup TwistTag.D4 K σ.toRingHom := by
    rw [← hformula s]
    exact (Subgroup.mem_inf.1 hy).2
  have hcoe : ((xPar (rootOperatorFamily d4) (highRoot d4) (χ * ε * χ') :
      adjointGroup d4 K) : ModGL d4 K) = pinnedX d4 K (highRoot d4) ((χ * ε * χ') * s) := by
    rw [tchar_coe_xPar_highRoot]
    congr 1
    ring
  have hfixraw : σ (χ * ε * χ') = χ * ε * χ' := by
    have hΓcoe : ((xPar (rootOperatorFamily d4) (highRoot d4) (χ * ε * χ') :
        adjointGroup d4 K) : ModGL d4 K) ∈ twistedFixedGroup TwistTag.D4 K σ.toRingHom := by
      rw [hcoe]; exact hΓmem
    rw [mem_twistedFixedGroup_iff_twistHom] at hΓcoe
    obtain ⟨-, htw⟩ := hΓcoe
    have h1 : twistC TwistTag.D4 K σ.toRingHom
        (xPar (rootOperatorFamily d4) (highRoot d4) (χ * ε * χ')) =
        xPar (rootOperatorFamily d4) (highRoot d4) (χ * ε * χ') := by
      apply Subtype.ext
      rw [coe_twistC]
      exact htw
    rw [twistC_xPar σ.toRingHom hθ, hρθ,
      twistSign_of_rho_eq σ.toRingHom hσ hθ hρθ, one_mul] at h1
    exact xPar_injective hθ h1
  have hν0 : χ * ε * χ' ≠ 0 := by
    intro hν
    have hconj1 : (b * R * b') * pinnedX d4 K (highRoot d4) s * (b * R * b')⁻¹ = 1 := by
      rw [hformula s, hν, zero_mul, pinnedX_zero]
    have hxs1 : pinnedX d4 K (highRoot d4) s = 1 := by
      calc pinnedX d4 K (highRoot d4) s
          = (b * R * b')⁻¹ * ((b * R * b') * pinnedX d4 K (highRoot d4) s * (b * R * b')⁻¹) *
              (b * R * b') := by group
        _ = 1 := by rw [hconj1]; group
    exact hxs_ne hxs1
  exact ⟨χ * ε * χ', hfixraw, hν0, hformula⟩


private theorem tchar_mem_highRoot_iff
    {K : Type} [Field K] (σ : K →+* K) {x : graphFixedRootGroup TwistTag.D4 K σ} :
    x ∈ triD4C0HighRoot K σ ↔ (↑x : ModGL d4 K) ∈
      (rootSubgroup d4 K (highRoot d4) ⊓ twistedFixedGroup TwistTag.D4 K σ) := by
  rw [show triD4C0HighRoot K σ = (rootSubgroup d4 K (highRoot d4) ⊓
      twistedFixedGroup TwistTag.D4 K σ).subgroupOf (graphFixedRootGroup TwistTag.D4 K σ)
      from rfl]
  exact Subgroup.mem_subgroupOf

private theorem tchar_X_mem
    {K : Type} [Field K] (σ : K ≃+* K) (t : fixedField σ.toRingHom) :
    (↑(triD4C0Xtheta σ t) : ModGL d4 K) ∈ rootSubgroup d4 K (highRoot d4) ⊓
      twistedFixedGroup TwistTag.D4 K σ.toRingHom := by
  refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
  · rw [show (↑(triD4C0Xtheta σ t) : ModGL d4 K) = pinnedX d4 K (highRoot d4)
        (((rootOperatorFamily d4).pinnedFamilySign (highRoot d4) : K) * (t : K))
        from tchar_coe_xPar_highRoot (t : K)]
    exact CFSG.Blueprint.Chevalley.mem_rootSubgroup.2 ⟨_, rfl⟩
  · exact graphFixedRootGroup_le TwistTag.D4 K σ.toRingHom (triD4C0Xtheta σ t).2

theorem triD4_normalizer_actionChar
    {K : Type} [Field K] (σ : K ≃+* K) (hσ : ∀ c, σ (σ (σ c)) = c)
    {g : graphFixedRootGroup TwistTag.D4 K σ.toRingHom}
    (hg : g ∈ Subgroup.normalizer (Bridge.triD4C0HighRoot K σ.toRingHom :
      Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))) :
    ∃ μ : (fixedField σ.toRingHom)ˣ,
      ∀ t : fixedField σ.toRingHom,
        g * triD4C0Xtheta σ t * g⁻¹ = triD4C0Xtheta σ (μ * t) := by
  let s : K := ((rootOperatorFamily d4).pinnedFamilySign (highRoot d4) : K)
  have hX1 : triD4C0Xtheta σ (1 : fixedField σ.toRingHom) ∈
      triD4C0HighRoot K σ.toRingHom :=
    (tchar_mem_highRoot_iff σ.toRingHom).2 (tchar_X_mem σ (1 : fixedField σ.toRingHom))
  have hconjX : g * triD4C0Xtheta σ (1 : fixedField σ.toRingHom) * g⁻¹ ∈
      triD4C0HighRoot K σ.toRingHom :=
    (Subgroup.mem_normalizer_iff.1 hg _).1 hX1
  have hgΓ : (↑g : ModGL d4 K) ∈ twistedFixedGroup TwistTag.D4 K σ.toRingHom :=
    graphFixedRootGroup_le TwistTag.D4 K σ.toRingHom g.2
  have hy : (↑g : ModGL d4 K) * pinnedX d4 K (highRoot d4) s * (↑g : ModGL d4 K)⁻¹ ∈
      rootSubgroup d4 K (highRoot d4) ⊓ twistedFixedGroup TwistTag.D4 K σ.toRingHom := by
    have hconjX' : (↑(g * triD4C0Xtheta σ (1 : fixedField σ.toRingHom) * g⁻¹) : ModGL d4 K) ∈
        (rootSubgroup d4 K (highRoot d4) ⊓ twistedFixedGroup TwistTag.D4 K σ.toRingHom) :=
      (tchar_mem_highRoot_iff σ.toRingHom).1 hconjX
    have hcoe : (↑(g * triD4C0Xtheta σ (1 : fixedField σ.toRingHom) * g⁻¹) : ModGL d4 K) =
        (↑g : ModGL d4 K) * pinnedX d4 K (highRoot d4) s * (↑g : ModGL d4 K)⁻¹ := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [show (↑(triD4C0Xtheta σ (1 : fixedField σ.toRingHom)) : ModGL d4 K) =
          pinnedX d4 K (highRoot d4) (s * (1 : K)) from tchar_coe_xPar_highRoot (1 : K),
        mul_one]
    rwa [hcoe] at hconjX'
  obtain ⟨ν, hσν, hν0, hformula⟩ := tchar_scalar σ hσ hgΓ hy
  refine ⟨Units.mk0 ⟨ν, hσν⟩ (by intro h; exact hν0 (congrArg Subtype.val h)), fun t => ?_⟩
  apply Subtype.ext
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  rw [show (↑(triD4C0Xtheta σ t) : ModGL d4 K) = pinnedX d4 K (highRoot d4) (s * (t : K))
      from tchar_coe_xPar_highRoot (t : K)]
  rw [show (↑(triD4C0Xtheta σ
        ((Units.mk0 ⟨ν, hσν⟩ (by intro h; exact hν0 (congrArg Subtype.val h)) :
          (fixedField σ.toRingHom)ˣ) * t)) : ModGL d4 K) = pinnedX d4 K (highRoot d4)
        (s * (((Units.mk0 ⟨ν, hσν⟩ (by intro h; exact hν0 (congrArg Subtype.val h)) :
          (fixedField σ.toRingHom)ˣ) * t : fixedField σ.toRingHom) : K))
          from tchar_coe_xPar_highRoot _]
  rw [hformula (s * (t : K))]
  congr 1
  simp only [Units.val_mk0, Subfield.coe_mul]
  ring


end CFSG.StandardType.LieKnownR2.TriD4.Inner
