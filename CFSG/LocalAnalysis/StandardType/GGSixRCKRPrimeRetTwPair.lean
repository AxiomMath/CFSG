module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeRetAssembly
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimePairTwCover6Aux2

public section

namespace CFSG.StandardType.RCKRP

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Universal
  CFSG.StandardType CFSG.StandardType.GGFinModel CFSG.LieType.Chevalley
  CFSG.StandardType.S2MathFi1035Pos CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.StandardType.LieCore
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.Steinberg.Exceptional CFSG.LieType.Steinberg.TwistedE6
  CFSG.Timmesfeld CFSG.LieType.Steinberg.Minuscule
open CFSG.Open (StatedLieTag StatedLieAdmissible)

theorem rckTp_pair_root_of_rel
    {σ : GGL ≃+* GGL} {z : ModGL Tag.E6 GGL} {step : ModGL Tag.E6 GGL →* ModGL Tag.E6 GGL}
    {γ : Fin Tag.E6.rank → ℤ}
    (hst : ∀ c, step (z * pinnedX Tag.E6 GGL γ c * z⁻¹) = z * pinnedX Tag.E6 GGL γ (σ c) * z⁻¹) :
    ((rootSubgroup Tag.E6 GGL γ).map (MulAut.conj z).toMonoidHom).map step =
        (rootSubgroup Tag.E6 GGL γ).map (MulAut.conj z).toMonoidHom ∧
      ∀ y, y ∈ ((rootSubgroup Tag.E6 GGL γ).map (MulAut.conj z).toMonoidHom ⊓
          step.eqLocus (MonoidHom.id _)) ↔
        ∃ c, σ c = c ∧ y = z * pinnedX Tag.E6 GGL γ c * z⁻¹ := by
  classical
  refine ⟨?_, ?_⟩
  · ext y
    constructor
    · rintro ⟨x, ⟨x', hx', rfl⟩, rfl⟩
      obtain ⟨c, rfl⟩ := mem_rootSubgroup.1 hx'
      refine ⟨pinnedX Tag.E6 GGL γ (σ c), mem_rootSubgroup.2 ⟨_, rfl⟩, ?_⟩
      change z * pinnedX Tag.E6 GGL γ (σ c) * z⁻¹ = step (z * pinnedX Tag.E6 GGL γ c * z⁻¹)
      rw [hst]
    · rintro ⟨x', hx', rfl⟩
      obtain ⟨c, rfl⟩ := mem_rootSubgroup.1 hx'
      refine ⟨z * pinnedX Tag.E6 GGL γ (σ.symm c) * z⁻¹,
        ⟨pinnedX Tag.E6 GGL γ (σ.symm c), mem_rootSubgroup.2 ⟨_, rfl⟩, rfl⟩, ?_⟩
      rw [hst, RingEquiv.apply_symm_apply]
      rfl
  · intro y
    constructor
    · rintro ⟨⟨x', hx', rfl⟩, hfix⟩
      obtain ⟨c, rfl⟩ := mem_rootSubgroup.1 hx'
      refine ⟨c, ?_, rfl⟩
      have h1 : step (z * pinnedX Tag.E6 GGL γ c * z⁻¹) = z * pinnedX Tag.E6 GGL γ c * z⁻¹ :=
        hfix
      rw [hst] at h1
      have h2 : pinnedX Tag.E6 GGL γ (σ c) = pinnedX Tag.E6 GGL γ c :=
        mul_left_cancel (mul_right_cancel h1)
      exact pinnedX_injective (τ := Tag.E6) (R := GGL) γ h2
    · rintro ⟨c, hc, rfl⟩
      refine ⟨⟨pinnedX Tag.E6 GGL γ c, mem_rootSubgroup.2 ⟨_, rfl⟩, rfl⟩, ?_⟩
      change step (z * pinnedX Tag.E6 GGL γ c * z⁻¹) = z * pinnedX Tag.E6 GGL γ c * z⁻¹
      rw [hst, hc]

theorem rckTp_map_fixSubfield
    {σ : GGL ≃+* GGL} {z : ModGL Tag.E6 GGL} {step : ModGL Tag.E6 GGL →* ModGL Tag.E6 GGL}
    {γ : Fin Tag.E6.rank → ℤ}
    (hst : ∀ c, step (z * pinnedX Tag.E6 GGL γ c * z⁻¹) = z * pinnedX Tag.E6 GGL γ (σ c) * z⁻¹) :
    ((rootSubgroup Tag.E6 ↥(fixSubfield σ) γ).map (baseChangeGL (fixSubfield σ).subtype)).map
        (MulAut.conj z).toMonoidHom =
      (rootSubgroup Tag.E6 GGL γ).map (MulAut.conj z).toMonoidHom ⊓
        step.eqLocus (MonoidHom.id _) := by
  classical
  obtain ⟨-, hfix⟩ := rckTp_pair_root_of_rel hst
  ext y
  rw [hfix y]
  constructor
  · rintro ⟨x, ⟨x', hx', rfl⟩, rfl⟩
    obtain ⟨c, rfl⟩ := mem_rootSubgroup.1 hx'
    refine ⟨(c : GGL), ((mem_fixSubfield σ).1 c.2), ?_⟩
    change z * baseChangeGL (fixSubfield σ).subtype (pinnedX Tag.E6 ↥(fixSubfield σ) γ c) * z⁻¹ = _
    rw [baseChangeGL_pinnedX]
    rfl
  · rintro ⟨c, hc, rfl⟩
    refine ⟨baseChangeGL (fixSubfield σ).subtype
      (pinnedX Tag.E6 ↥(fixSubfield σ) γ ⟨c, (mem_fixSubfield σ).2 hc⟩),
      ⟨_, mem_rootSubgroup.2 ⟨_, rfl⟩, rfl⟩, ?_⟩
    change z * baseChangeGL (fixSubfield σ).subtype
      (pinnedX Tag.E6 ↥(fixSubfield σ) γ ⟨c, (mem_fixSubfield σ).2 hc⟩) * z⁻¹ = _
    rw [baseChangeGL_pinnedX]
    rfl

theorem rckRet_tw_pair
    {h : ℕ} (hh : 0 < h) {p₁ : ℕ} (SK : LangSetup Tag.E6 GGL p₁)
    (hSKΦ : SK.D.Φ = twistHom TwistTag.E6 GGL (ggFrobT h)) (hSKq : SK.D.q = 2 ^ h) :
    ∃ γ₀ : Fin Tag.E6.rank → ℤ, IsRoot Tag.E6 γ₀ ∧
      ((rootSubgroup Tag.E6 GGL γ₀).map (MulAut.conj SK.D.g0⁻¹).toMonoidHom).map SK.D.step =
        (rootSubgroup Tag.E6 GGL γ₀).map (MulAut.conj SK.D.g0⁻¹).toMonoidHom ∧
      ((rootSubgroup Tag.E6 GGL (-γ₀)).map (MulAut.conj SK.D.g0⁻¹).toMonoidHom).map SK.D.step =
        (rootSubgroup Tag.E6 GGL (-γ₀)).map (MulAut.conj SK.D.g0⁻¹).toMonoidHom ∧
      ((twistedE6Datum 2 h).rootGroup (Pi.single (0 : Fin 4) 1)).map
          ((MulAut.conj SK.D.g0⁻¹).toMonoidHom.comp
            ((rckTw6_iota h).comp (rckTw6_psi h hh))) =
        (rootSubgroup Tag.E6 GGL γ₀).map (MulAut.conj SK.D.g0⁻¹).toMonoidHom ⊓
          SK.D.step.eqLocus (MonoidHom.id _) ∧
      ((twistedE6Datum 2 h).rootGroup (-Pi.single (0 : Fin 4) 1)).map
          ((MulAut.conj SK.D.g0⁻¹).toMonoidHom.comp
            ((rckTw6_iota h).comp (rckTw6_psi h hh))) =
        (rootSubgroup Tag.E6 GGL (-γ₀)).map (MulAut.conj SK.D.g0⁻¹).toMonoidHom ⊓
          SK.D.step.eqLocus (MonoidHom.id _) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hf : 1 ≤ h := hh
  let σ : GGL ≃+* GGL := by
    refine RingEquiv.ofBijective (ggFrobT h) ⟨(iterateFrobenius GGL 2 h).injective, ?_⟩
    intro c
    obtain ⟨y, hy⟩ := IsAlgClosed.exists_pow_nat_eq c (pow_pos (by norm_num : (0 : ℕ) < 2) h)
    exact ⟨y, by rw [ggFrobT_apply, hy]⟩
  have hσ : ∀ c, σ c = c ^ 2 ^ h := fun c => ggFrobT_apply h c
  have hσ' : σ.toRingHom = ggFrobT h := rfl
  have huntwist := rckTw6_untwist SK h hSKΦ σ hσ'
  have hγroot : IsRoot TwistTag.E6.tag (Pi.single (1 : Fin TwistTag.E6.tag.rank) 1) :=
    isRoot_single TwistTag.E6.tag 1
  have hprojγ : proj (Pi.single (1 : Fin TwistTag.E6.tag.rank) 1) = Pi.single (0 : Fin 4) 1 :=
    (proj_single (1 : Fin TwistTag.E6.tag.rank)).trans rfl
  have hrhoγ : rho (Pi.single (1 : Fin TwistTag.E6.tag.rank) 1) =
      Pi.single (1 : Fin TwistTag.E6.tag.rank) 1 :=
    (rho_single (1 : Fin TwistTag.E6.tag.rank)).trans
      (by
        change Pi.single ((TwistTag.E6.perm) 1) 1 = Pi.single 1 1
        rw [show (TwistTag.E6.perm) 1 = 1 by decide]
        rfl)
  have hγproj : proj (-Pi.single (1 : Fin TwistTag.E6.tag.rank) 1) = -Pi.single (0 : Fin 4) 1 :=
    (proj.map_neg (Pi.single (1 : Fin TwistTag.E6.tag.rank) 1)).trans (by rw [hprojγ]; rfl)
  have hrhoneg : rho (-Pi.single (1 : Fin TwistTag.E6.tag.rank) 1) =
      -Pi.single (1 : Fin TwistTag.E6.tag.rank) 1 := by
    rw [show rho (-Pi.single (1 : Fin TwistTag.E6.tag.rank) 1) =
      -rho (Pi.single (1 : Fin TwistTag.E6.tag.rank) 1) from rfl, hrhoγ]
    rfl
  have hpin_core := rckTw6_pin_of h hf σ hσ (Pi.single (1 : Fin TwistTag.E6.tag.rank) 1)
    (Pi.single (0 : Fin 4) 1) hγroot hprojγ hrhoγ
  have hpin_core_neg := rckTw6_pin_of h hf σ hσ
    (-Pi.single (1 : Fin TwistTag.E6.tag.rank) 1) (-Pi.single (0 : Fin 4) 1)
    (IsRoot.neg hγroot) hγproj hrhoneg
  have hrel : ∀ δ : Fin Tag.E6.rank → ℤ,
      (δ = Pi.single (1 : Fin Tag.E6.rank) 1 ∨ δ = -Pi.single (1 : Fin Tag.E6.rank) 1) →
      ∀ c : GGL,
      SK.D.step (SK.D.g0⁻¹ * pinnedX Tag.E6 GGL δ c * SK.D.g0) =
        SK.D.g0⁻¹ * pinnedX Tag.E6 GGL δ (σ c) * SK.D.g0 := by
    intro δ hδ c
    have hmem : pinnedX Tag.E6 GGL δ c ∈ rootSpan Tag.E6 GGL
        ({Pi.single (1 : Fin Tag.E6.rank) 1, -Pi.single (1 : Fin Tag.E6.rank) 1} :
          Set (Fin Tag.E6.rank → ℤ)) := by
      refine pinnedX_mem_rootSpan ?_ c
      rcases hδ with rfl | rfl <;> simp
    have h1 := huntwist.2 _ hmem
    have h2 : frobGL σ (pinnedX Tag.E6 GGL δ c) = pinnedX Tag.E6 GGL δ (σ c) :=
      CFSG.RankThree.PartOne.KE.units_map_entrywiseHom_pinnedX _ _ _
    exact h1.trans (congrArg (fun m => SK.D.g0⁻¹ * m * SK.D.g0) h2)
  have hrel1 : ∀ c : GGL, SK.D.step (SK.D.g0⁻¹ * pinnedX Tag.E6 GGL
      (Pi.single (1 : Fin Tag.E6.rank) 1) c * SK.D.g0⁻¹⁻¹) =
      SK.D.g0⁻¹ * pinnedX Tag.E6 GGL (Pi.single (1 : Fin Tag.E6.rank) 1) (σ c) *
        SK.D.g0⁻¹⁻¹ := fun c => by
    rw [inv_inv]
    exact hrel _ (Or.inl rfl) c
  have hrel2 : ∀ c : GGL, SK.D.step (SK.D.g0⁻¹ * pinnedX Tag.E6 GGL
      (-Pi.single (1 : Fin Tag.E6.rank) 1) c * SK.D.g0⁻¹⁻¹) =
      SK.D.g0⁻¹ * pinnedX Tag.E6 GGL (-Pi.single (1 : Fin Tag.E6.rank) 1) (σ c) *
        SK.D.g0⁻¹⁻¹ := fun c => by
    rw [inv_inv]
    exact hrel _ (Or.inr rfl) c
  obtain ⟨hst1, -⟩ := rckTp_pair_root_of_rel (σ := σ) (z := SK.D.g0⁻¹) (step := SK.D.step)
    (γ := Pi.single (1 : Fin Tag.E6.rank) 1) hrel1
  obtain ⟨hst2, -⟩ := rckTp_pair_root_of_rel (σ := σ) (z := SK.D.g0⁻¹) (step := SK.D.step)
    (γ := -Pi.single (1 : Fin Tag.E6.rank) 1) hrel2
  have hmap_pin : ∀ β' : Fin (Tag.rank .F4) → ℤ,
      (twistedRootGroup (GaloisField 2 (2 * h)) (frobQ 2 h) β').map
          ((MulAut.conj SK.D.g0⁻¹).toMonoidHom.comp ((rckTw6_iota h).comp (rckTw6_psi h hh))) =
        ((twistedRootGroup (GaloisField 2 (2 * h)) (frobQ 2 h) β').map
          ((rckTw6_iota h).comp (rckTw6_psi h hh))).map (MulAut.conj SK.D.g0⁻¹).toMonoidHom := by
    intro β'
    exact (Subgroup.map_map (twistedRootGroup (GaloisField 2 (2 * h)) (frobQ 2 h) β')
      (MulAut.conj SK.D.g0⁻¹).toMonoidHom ((rckTw6_iota h).comp (rckTw6_psi h hh))).symm
  refine ⟨Pi.single (1 : Fin Tag.E6.rank) 1, hγroot, hst1, hst2, ?_, ?_⟩
  · rw [show (twistedE6Datum 2 h).rootGroup (Pi.single (0 : Fin 4) 1) =
        twistedRootGroup (GaloisField 2 (2 * h)) (frobQ 2 h) (Pi.single (0 : Fin 4) 1) from rfl]
    rw [hmap_pin (Pi.single (0 : Fin 4) 1), hpin_core]
    exact rckTp_map_fixSubfield (σ := σ) (z := SK.D.g0⁻¹) (step := SK.D.step)
      (γ := Pi.single (1 : Fin Tag.E6.rank) 1) hrel1
  · rw [show (twistedE6Datum 2 h).rootGroup (-Pi.single (0 : Fin 4) 1) =
        twistedRootGroup (GaloisField 2 (2 * h)) (frobQ 2 h) (-Pi.single (0 : Fin 4) 1) from rfl]
    rw [hmap_pin (-Pi.single (0 : Fin 4) 1), hpin_core_neg]
    exact rckTp_map_fixSubfield (σ := σ) (z := SK.D.g0⁻¹) (step := SK.D.step)
      (γ := -Pi.single (1 : Fin Tag.E6.rank) 1) hrel2

end CFSG.StandardType.RCKRP

end
