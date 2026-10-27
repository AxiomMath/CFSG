module

public import CFSG.LocalAnalysis.StandardType.GGSelectedTwistedE6Cover
public import CFSG.LocalAnalysis.StandardType.ExcPos.TwE6U1aRootSub

public section
namespace CFSG.StandardType.TwistedE6SourceCover

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Universal
  CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Exceptional CFSG.LieType.Steinberg.Minuscule
  CFSG.LieType.Steinberg.Isogeny CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.StandardType.GGFinModel CFSG.StandardType.LieKnownR2.ExcPos
  CFSG.LieType.Steinberg.TwistedE6


theorem iota_comp_pi_eq
    (S : LangSetup TwistTag.E6.tag GGL 5)
    (pi : (ggU .twistedE6 0 1).K →*
      ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * 1)) (frobQ 2 1)))
    (hpival : ∀ z, ((pi z : graphFixedRootGroup TwistTag.E6
        (GaloisField 2 (2 * 1)) (frobQ 2 1)) : ModGL TwistTag.E6.tag
          (GaloisField 2 (2 * 1))) =
      ((e6IsogenyT (GaloisField 2 (2 * 1))
        (Subtype.val (show twistedE6Group 2 1 from z)) :
          adjointGroup TwistTag.E6.tag (GaloisField 2 (2 * 1))) :
            ModGL TwistTag.E6.tag (GaloisField 2 (2 * 1))))
    (iota : ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * 1)) (frobQ 2 1)) →*
      ModGL TwistTag.E6.tag GGL)
    (hival : ∀ c, S.D.g0 * iota c * S.D.g0⁻¹ =
      baseChangeGL (ggRatEmb (2 * 1)) (c : ModGL TwistTag.E6.tag (GaloisField 2 (2 * 1)))) :
    iota.comp pi = (MulAut.conj S.D.g0⁻¹).toMonoidHom.comp (ggIotaK .twistedE6 0 1 le_rfl) := by
  have hbc : ∀ u, ggIotaK .twistedE6 0 1 le_rfl u =
      baseChangeGL (ggRatEmb (2 * 1)) (pi u : ModGL TwistTag.E6.tag (GaloisField 2 (2 * 1))) := by
    intro u
    rw [ggIotaK_twistedE6_eq_isogeny_minBC]
    have he := e6IsogenyAlgebraic_minBC (GaloisField 2 (2 * 1)) (ggRatEmb (2 * 1))
      ((show twistedE6Group 2 1 from u) : e6Data_valid.minGroup (GaloisField 2 (2 * 1)))
    refine he.trans ?_
    rw [hpival u]
    rfl
  refine MonoidHom.ext fun u => ?_
  have hs := hival (pi u)
  rw [← hbc u] at hs
  change iota (pi u) = S.D.g0⁻¹ *
    (show ModGL TwistTag.E6.tag GGL from ggIotaK .twistedE6 0 1 le_rfl u) * S.D.g0
  rw [← hs]
  group

theorem fixed_root_image
    (S : LangSetup TwistTag.E6.tag GGL 5)
    (pi : (ggU .twistedE6 0 1).K →*
      ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * 1)) (frobQ 2 1)))
    (hpival : ∀ z, ((pi z : graphFixedRootGroup TwistTag.E6
        (GaloisField 2 (2 * 1)) (frobQ 2 1)) : ModGL TwistTag.E6.tag
          (GaloisField 2 (2 * 1))) =
      ((e6IsogenyT (GaloisField 2 (2 * 1))
        (Subtype.val (show twistedE6Group 2 1 from z)) :
          adjointGroup TwistTag.E6.tag (GaloisField 2 (2 * 1))) :
            ModGL TwistTag.E6.tag (GaloisField 2 (2 * 1))))
    (iota : ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * 1)) (frobQ 2 1)) →*
      ModGL TwistTag.E6.tag GGL)
    (hival : ∀ c, S.D.g0 * iota c * S.D.g0⁻¹ =
      baseChangeGL (ggRatEmb (2 * 1)) (c : ModGL TwistTag.E6.tag (GaloisField 2 (2 * 1))))
    (hPhi : S.D.Φ = twistHom TwistTag.E6 GGL (ggFrobT 1))
    {delta : Fin TwistTag.E6.tag.rank → ℤ} (hdelta : IsRoot TwistTag.E6.tag delta)
    (hrho : rho delta = delta) :
    ((ggU .twistedE6 0 1).D.rootGroup (proj delta)).map (iota.comp pi) =
      excCurve (τ := TwistTag.E6.tag) delta S.D.g0⁻¹ ⊓ S.D.model := by
  have hEta := iota_comp_pi_eq S pi hpival iota hival
  have hPhiEq : S.D.Φ = ggPhi .twistedE6 1 := hPhi
  have hsymm : (MulAut.conj S.D.g0).symm.toMonoidHom =
      (MulAut.conj S.D.g0⁻¹).toMonoidHom := by
    ext z
    simp [MulAut.conj]
  have hM : (ggFixGp .twistedE6 1).map (MulAut.conj S.D.g0⁻¹).toMonoidHom = S.D.model := by
    rw [← hsymm]
    apply (Subgroup.map_symm_eq_iff_map_eq S.D.model (e := MulAut.conj S.D.g0)).2
    exact S.D.map_conj_model.trans (ggFixGp_eq_fix (t := .twistedE6) (f := 1) S.D hPhiEq)
  rw [hEta]
  have hcomp :
      ((ggU .twistedE6 0 1).D.rootGroup (proj delta)).map
        ((MulAut.conj S.D.g0⁻¹).toMonoidHom.comp (ggIotaK .twistedE6 0 1 le_rfl)) =
      (((ggU .twistedE6 0 1).D.rootGroup (proj delta)).map (ggIotaK .twistedE6 0 1 le_rfl)).map
        (MulAut.conj S.D.g0⁻¹).toMonoidHom :=
    (Subgroup.map_map _ _ _).symm
  rw [hcomp]
  have hBC := ggBC_twistedE6_of_fixed_root 0 1 le_rfl (α := delta) hdelta hrho
  rw [hBC]
  have hinf :
      ((rootSubgroup TwistTag.E6.tag GGL delta) ⊓ ggFixGp .twistedE6 1).map
        (MulAut.conj S.D.g0⁻¹).toMonoidHom =
      (rootSubgroup TwistTag.E6.tag GGL delta).map (MulAut.conj S.D.g0⁻¹).toMonoidHom ⊓
        (ggFixGp .twistedE6 1).map (MulAut.conj S.D.g0⁻¹).toMonoidHom :=
    Subgroup.map_inf _ _ _ (MulAut.conj S.D.g0⁻¹).injective
  exact hinf.trans (by rw [hM]; rfl)

theorem canonical_root_pair_image
    (S : LangSetup TwistTag.E6.tag GGL 5)
    (pi : (ggU .twistedE6 0 1).K →*
      ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * 1)) (frobQ 2 1)))
    (hpival : ∀ z, ((pi z : graphFixedRootGroup TwistTag.E6
        (GaloisField 2 (2 * 1)) (frobQ 2 1)) : ModGL TwistTag.E6.tag
          (GaloisField 2 (2 * 1))) =
      ((e6IsogenyT (GaloisField 2 (2 * 1))
        (Subtype.val (show twistedE6Group 2 1 from z)) :
          adjointGroup TwistTag.E6.tag (GaloisField 2 (2 * 1))) :
            ModGL TwistTag.E6.tag (GaloisField 2 (2 * 1))))
    (iota : ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * 1)) (frobQ 2 1)) →*
      ModGL TwistTag.E6.tag GGL)
    (hival : ∀ c, S.D.g0 * iota c * S.D.g0⁻¹ =
      baseChangeGL (ggRatEmb (2 * 1)) (c : ModGL TwistTag.E6.tag (GaloisField 2 (2 * 1))))
    (hPhi : S.D.Φ = twistHom TwistTag.E6 GGL (ggFrobT 1)) :
    ((ggU .twistedE6 0 1).D.rootGroup (Pi.single (1 : Fin 4) 1)).map (iota.comp pi) =
        excCurve (τ := TwistTag.E6.tag) (Pi.single (3 : Fin 6) 1) S.D.g0⁻¹ ⊓ S.D.model ∧
      ((ggU .twistedE6 0 1).D.rootGroup (-Pi.single (1 : Fin 4) 1)).map (iota.comp pi) =
        excCurve (τ := TwistTag.E6.tag) (-Pi.single (3 : Fin 6) 1) S.D.g0⁻¹ ⊓ S.D.model := by
  let a0 : Fin TwistTag.E6.tag.rank → ℤ := Pi.single 3 1
  have ha0 : IsRoot TwistTag.E6.tag a0 := isRoot_single .E6 3
  have ha0m : IsRoot TwistTag.E6.tag (-a0) := isRoot_neg_single .E6 3
  have hrho : rho a0 = a0 := by
    funext j
    fin_cases j <;> rfl
  have hrhom : rho (-a0) = -a0 := by
    change -rho a0 = -a0
    rw [hrho]
    rfl
  have hproj : proj a0 = Pi.single (1 : Fin 4) 1 := by
    funext j
    fin_cases j <;> rfl
  have hprojm : proj (-a0) = -Pi.single (1 : Fin 4) 1 := by
    have h := map_neg proj a0
    exact h.trans (congrArg Neg.neg hproj)
  have hp := fixed_root_image S pi hpival iota hival hPhi ha0 hrho
  have hm := fixed_root_image S pi hpival iota hival hPhi ha0m hrhom
  rw [hproj] at hp
  rw [hprojm] at hm
  exact ⟨hp, hm⟩

theorem canonical_root_pair_position
    (S : LangSetup TwistTag.E6.tag GGL 5)
    (pi : (ggU .twistedE6 0 1).K →*
      ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * 1)) (frobQ 2 1)))
    (hpival : ∀ z, ((pi z : graphFixedRootGroup TwistTag.E6
        (GaloisField 2 (2 * 1)) (frobQ 2 1)) : ModGL TwistTag.E6.tag
          (GaloisField 2 (2 * 1))) =
      ((e6IsogenyT (GaloisField 2 (2 * 1))
        (Subtype.val (show twistedE6Group 2 1 from z)) :
          adjointGroup TwistTag.E6.tag (GaloisField 2 (2 * 1))) :
            ModGL TwistTag.E6.tag (GaloisField 2 (2 * 1))))
    (iota : ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * 1)) (frobQ 2 1)) →*
      ModGL TwistTag.E6.tag GGL)
    (hival : ∀ c, S.D.g0 * iota c * S.D.g0⁻¹ =
      baseChangeGL (ggRatEmb (2 * 1)) (c : ModGL TwistTag.E6.tag (GaloisField 2 (2 * 1))))
    (hrange : iota.range = S.Γ) (hq : S.D.q = 2 ^ 1)
    (hPhi : S.D.Φ = twistHom TwistTag.E6 GGL (ggFrobT 1))
    {alpha : Fin TwistTag.E6.tag.rank → ℤ} {w : ModGL TwistTag.E6.tag GGL}
    (halpha : IsRoot TwistTag.E6.tag alpha) (hw : w ∈ adjointGroup TwistTag.E6.tag GGL)
    (hV : (excCurve (τ := TwistTag.E6.tag) alpha w).map S.D.step = excCurve (τ := TwistTag.E6.tag) alpha w)
    (hVm : (excCurve (τ := TwistTag.E6.tag) (-alpha) w).map S.D.step = excCurve (τ := TwistTag.E6.tag) (-alpha) w) :
    ∃ k : (ggU .twistedE6 0 1).K,
      ((ggU .twistedE6 0 1).D.rootGroup (Pi.single (1 : Fin 4) 1)).map
          ((iota.comp pi).comp (MulAut.conj k).toMonoidHom) = excCurve (τ := TwistTag.E6.tag) alpha w ⊓ S.D.model ∧
        ((ggU .twistedE6 0 1).D.rootGroup (-Pi.single (1 : Fin 4) 1)).map
          ((iota.comp pi).comp (MulAut.conj k).toMonoidHom) = excCurve (τ := TwistTag.E6.tag) (-alpha) w ⊓ S.D.model := by
  with_unfolding_all
    have hEta0 := iota_comp_pi_eq S pi hpival iota hival
    obtain ⟨hrootp, hrootm⟩ := canonical_root_pair_image S pi hpival iota hival hPhi
    change LangSetup Tag.E6 GGL 5 at S
    change _ →* ModGL Tag.E6 GGL at iota
    change ModGL Tag.E6 GGL at w
    dsimp +instances only [langTag, TwistTag.tag] at *
    let Phi : ModGL Tag.E6 GGL →* ModGL Tag.E6 GGL := ggPhi .twistedE6 1
    let g0 := S.D.g0
    let A := adjointGroup Tag.E6 GGL
    let M := S.D.model
    let eta : (ggU .twistedE6 0 1).K →* ModGL Tag.E6 GGL := iota.comp pi
    let iota0 : (ggU .twistedE6 0 1).K →* ModGL Tag.E6 GGL := ggIotaK .twistedE6 0 1 le_rfl
    let a0 : Fin Tag.E6.rank → ℤ := Pi.single 3 1
    let V0 := excCurve (τ := Tag.E6) a0 g0⁻¹
    let Vm0 := excCurve (τ := Tag.E6) (-a0) g0⁻¹
    have ha0 : IsRoot Tag.E6 a0 := isRoot_single .E6 3
    have ha0m : IsRoot Tag.E6 (-a0) := isRoot_neg_single .E6 3
    have hrho : rho a0 = a0 := by
      funext j
      fin_cases j <;> rfl
    have hrhom : rho (-a0) = -a0 := by
      change -rho a0 = -a0
      rw [hrho] <;> rfl
    have hPhiEq : S.D.Φ = Phi := hPhi
    have hEta : eta = (MulAut.conj g0⁻¹).toMonoidHom.comp iota0 :=
      hEta0
    have hstepmap : S.D.step.comp (MulAut.conj g0⁻¹).toMonoidHom =
        (MulAut.conj g0⁻¹).toMonoidHom.comp (Phi) := by
      exact S.D.step_comp_conj_g0_inv.trans
        (congrArg (fun f : ModGL Tag.E6 GGL →* ModGL Tag.E6 GGL =>
          (MulAut.conj S.D.g0⁻¹).toMonoidHom.comp f) hPhiEq)
    have hstable : ∀ delta : Fin Tag.E6.rank → ℤ, IsRoot Tag.E6 delta → rho delta = delta →
        (excCurve (τ := Tag.E6) delta g0⁻¹).map S.D.step = excCurve (τ := Tag.E6) delta g0⁻¹ := by
      intro delta hdelta hdeltaR
      change ((rootSubgroup Tag.E6 GGL delta).map
        (MulAut.conj g0⁻¹).toMonoidHom).map S.D.step = _
      have hmap : ((rootSubgroup Tag.E6 GGL delta).map (MulAut.conj g0⁻¹).toMonoidHom).map S.D.step =
          ((rootSubgroup Tag.E6 GGL delta).map (Phi)).map (MulAut.conj g0⁻¹).toMonoidHom := by
        calc
          _ = (rootSubgroup Tag.E6 GGL delta).map
              (S.D.step.comp (MulAut.conj g0⁻¹).toMonoidHom) := Subgroup.map_map _ _ _
          _ = (rootSubgroup Tag.E6 GGL delta).map
              ((MulAut.conj g0⁻¹).toMonoidHom.comp (Phi)) :=
            congrArg (fun f : ModGL Tag.E6 GGL →* ModGL Tag.E6 GGL =>
              (rootSubgroup Tag.E6 GGL delta).map f) hstepmap
          _ = _ := (Subgroup.map_map _ _ _).symm
      have hroot : (rootSubgroup Tag.E6 GGL delta).map (Phi) =
          rootSubgroup Tag.E6 GGL delta := by
        have h : (rootSubgroup Tag.E6 GGL delta).map (Phi) =
            rootSubgroup Tag.E6 GGL (rho delta) := map_ggPhi_rootSubgroup_twistedE6 1 hdelta
        exact h.trans (congrArg (rootSubgroup Tag.E6 GGL) hdeltaR)
      exact hmap.trans (congrArg (fun H : Subgroup (ModGL Tag.E6 GGL) =>
        H.map (MulAut.conj g0⁻¹).toMonoidHom) hroot)
    obtain ⟨h, hh, hH, hHm⟩ := exists_conj_stableOppositePair le_rfl S.D hq
      ha0 halpha (A.inv_mem S.D.g0_mem) hw (hstable a0 ha0 hrho)
      (hstable (-a0) ha0m hrhom) hV hVm
    have hyA : g0 * h * g0⁻¹ ∈ A :=
      A.mul_mem (A.mul_mem S.D.g0_mem (S.D.mem_model.1 hh).1) (A.inv_mem S.D.g0_mem)
    have hyfix : Phi (g0 * h * g0⁻¹) = g0 * h * g0⁻¹ := by
      have he : (MulAut.conj g0⁻¹) (g0 * h * g0⁻¹) = h := by
        change g0⁻¹ * (g0 * h * g0⁻¹) * g0 = h
        group
      have hhfix : S.D.step h = h := (S.D.mem_model.1 hh).2
      apply (MulAut.conj g0⁻¹).injective
      have hs := DFunLike.congr_fun hstepmap (g0 * h * g0⁻¹)
      change S.D.step ((MulAut.conj g0⁻¹) (g0 * h * g0⁻¹)) =
        (MulAut.conj g0⁻¹) (Phi (g0 * h * g0⁻¹)) at hs
      exact hs.symm.trans ((congrArg S.D.step he).trans (hhfix.trans he.symm))
    obtain ⟨k, t, ht, hkt⟩ := exists_native_factor_of_twisted_fixed 0 1 le_rfl hyA hyfix
    change ModGL Tag.E6 GGL at t
    let c := eta k
    let tor := g0⁻¹ * t * g0
    have hc : c = g0⁻¹ * iota0 k * g0 := by
      change eta k = _
      rw [hEta]
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    have hprod : h = c * tor := by
      rw [hc]
      apply (MulAut.conj g0).injective
      simp only [MulAut.conj_apply]
      change g0 * h * g0⁻¹ = g0 * ((g0⁻¹ * iota0 k * g0) * (g0⁻¹ * t * g0)) * g0⁻¹
      rw [hkt]
      group
      rfl
    obtain ⟨a, hta⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup ht
    have htroot : ∀ delta, IsRoot Tag.E6 delta →
        (rootSubgroup Tag.E6 GGL delta).map (MulAut.conj t).toMonoidHom =
          rootSubgroup Tag.E6 GGL delta := by
      intro delta hdelta
      rw [hta]
      exact map_conj_rootDiagUnit_rootSubgroup a hdelta
    have htorcomp : (MulAut.conj tor).toMonoidHom.comp (MulAut.conj g0⁻¹).toMonoidHom =
        (MulAut.conj g0⁻¹).toMonoidHom.comp (MulAut.conj t).toMonoidHom := by
      refine MonoidHom.ext fun z => ?_
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      dsimp only [tor]
      group
    have htorroot : ∀ delta, IsRoot Tag.E6 delta →
        (excCurve (τ := Tag.E6) delta g0⁻¹).map (MulAut.conj tor).toMonoidHom = excCurve (τ := Tag.E6) delta g0⁻¹ := by
      intro delta hdelta
      change ((rootSubgroup Tag.E6 GGL delta).map
        (MulAut.conj g0⁻¹).toMonoidHom).map (MulAut.conj tor).toMonoidHom = _
      rw [Subgroup.map_map, htorcomp, ← Subgroup.map_map, htroot delta hdelta]
      rfl
    have hconjprod : (MulAut.conj h).toMonoidHom =
        (MulAut.conj c).toMonoidHom.comp (MulAut.conj tor).toMonoidHom := by
      rw [hprod]
      refine MonoidHom.ext fun z => ?_
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    have hcV : V0.map (MulAut.conj c).toMonoidHom = excCurve (τ := Tag.E6) alpha w := by
      rw [hconjprod, ← Subgroup.map_map, htorroot a0 ha0] at hH
      exact hH
    have hcVm : Vm0.map (MulAut.conj c).toMonoidHom = excCurve (τ := Tag.E6) (-alpha) w := by
      rw [hconjprod, ← Subgroup.map_map, htorroot (-a0) ha0m] at hHm
      exact hHm
    have hcM : c ∈ M := by
      have hcr : c ∈ iota.range := ⟨pi k, rfl⟩
      have hrange' : iota.range = ⁅M, M⁆ := hrange
      have hcr' : c ∈ ⁅M, M⁆ := hrange' ▸ hcr
      have hle := Subgroup.commutator_le_sup (H₁ := M) (H₂ := M)
      rw [sup_idem] at hle
      exact hle hcr'
    have hMc : M.map (MulAut.conj c).toMonoidHom = M :=
      Subgroup.mem_normalizer_iff_map_conj_eq.1 (M.le_normalizer hcM)
    have hconj : (MulAut.conj c).toMonoidHom.comp eta = eta.comp (MulAut.conj k).toMonoidHom := by
      refine MonoidHom.ext fun u => ?_
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul, map_inv]
      rfl
    have hrootp' : ((ggU .twistedE6 0 1).D.rootGroup (Pi.single (1 : Fin 4) 1)).map eta = V0 ⊓ M := hrootp
    have hrootm' : ((ggU .twistedE6 0 1).D.rootGroup (-Pi.single (1 : Fin 4) 1)).map eta = Vm0 ⊓ M := hrootm
    refine ⟨k, ?_, ?_⟩
    · change ((ggU .twistedE6 0 1).D.rootGroup (Pi.single (1 : Fin 4) 1)).map
        (eta.comp (MulAut.conj k).toMonoidHom) = _
      rw [← hconj, ← Subgroup.map_map, hrootp',
        Subgroup.map_inf _ _ _ (MulAut.conj c).injective, hcV, hMc] <;> rfl
    · change ((ggU .twistedE6 0 1).D.rootGroup (-Pi.single (1 : Fin 4) 1)).map
        (eta.comp (MulAut.conj k).toMonoidHom) = _
      rw [← hconj, ← Subgroup.map_map, hrootm',
        Subgroup.map_inf _ _ _ (MulAut.conj c).injective, hcVm, hMc] <;> rfl

end CFSG.StandardType.TwistedE6SourceCover
