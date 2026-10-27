module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKK1IIISUCoordRoot
public import CFSG.LocalAnalysis.StandardType.GGRootCentKGStructTwE6Levi
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotCTGraphTwisted
public import CFSG.LieType.Chevalley.E6GraphLeviRealization
public import CFSG.LieType.Chevalley.E6GraphRadicalCoords
public import CFSG.LieType.Steinberg.TwistedE6.Local
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotLeviHom
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2ShortF4IsoLen

public section

namespace CFSG.StandardType.RCKC1

open Matrix CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.RootSystem CFSG.LieType.Steinberg.TwistedE6 CFSG.SeitzReduction
  CFSG.SeitzReduction.F4Pilot CFSG.SeitzReduction.TwistedE6Pilot
  CFSG.StandardType.RCKK1IIISU CFSG.StandardType.KGTwE6
open CFSG.LieType.Universal.Unitary (SU)

private theorem suCorner_six_support (a b : ZMod 2) :
    (suCorner (k := 6) (by decide) ![0, a, b, 0] :
      Matrix (Fin 6) (Fin 6) SUF) =
    ((Matrix.SpecialLinearGroup.transvection (i := (0 : Fin 6)) (j := (4 : Fin 6))
        (by decide) (algebraMap (ZMod 2) SUF a + algebraMap (ZMod 2) SUF b * suOmega) :
        Matrix.SpecialLinearGroup (Fin 6) SUF) *
      (Matrix.SpecialLinearGroup.transvection (i := (1 : Fin 6)) (j := (5 : Fin 6))
        (by decide) (SUσ (algebraMap (ZMod 2) SUF a +
          algebraMap (ZMod 2) SUF b * suOmega)) :
        Matrix.SpecialLinearGroup (Fin 6) SUF) : Matrix (Fin 6) (Fin 6) SUF) := by
  rw [Matrix.SpecialLinearGroup.transvection_coe (F := SUF) (ι := Fin 6),
    Matrix.SpecialLinearGroup.transvection_coe (F := SUF) (ι := Fin 6)]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [suCorner, sI0, sI1, Fin.rev, Matrix.add_apply, Matrix.mul_apply,
      Fin.sum_univ_six]

private theorem rho_rootE15_eq :
    rho CFSG.SeitzReduction.TwistedE6Pilot.rootE15 =
      CFSG.SeitzReduction.TwistedE6Pilot.rootE26 := by
  have h := (CFSG.SeitzReduction.TwistedE6Pilot.repRoots_check).1.2.2.2.1
  exact h

private theorem rootE26_ne_rootE15 :
    CFSG.SeitzReduction.TwistedE6Pilot.rootE26 ≠
      CFSG.SeitzReduction.TwistedE6Pilot.rootE15 := by
  intro h
  have h0 := congrFun h (0 : Fin 6)
  norm_num [CFSG.SeitzReduction.TwistedE6Pilot.rootE15,
    CFSG.SeitzReduction.TwistedE6Pilot.rootE26] at h0

private theorem rho_rootE15_ne_self :
    rho CFSG.SeitzReduction.TwistedE6Pilot.rootE15 ≠
      CFSG.SeitzReduction.TwistedE6Pilot.rootE15 := by
  intro h
  rw [rho_rootE15_eq] at h
  exact rootE26_ne_rootE15 h

private theorem unitarySLEquiv_symm_suZ_six
    (hσ : ∀ c, SUσ.toRingHom c = c ^ (2 ^ 1)) (a b : ZMod 2) :
    ((((E6GraphLevi.unitarySLEquiv (K := SUF) (f := 1) (σ := SUσ.toRingHom) hσ).symm
        (suZ (k := 6) (by decide) ![0, a, b, 0]) :
        ↥(E6GraphLevi.unitarySL SUσ.toRingHom)) :
        Matrix.SpecialLinearGroup (Fin 6) SUF)) =
      Matrix.SpecialLinearGroup.transvection (i := (0 : Fin 6)) (j := (4 : Fin 6))
          (by decide) (algebraMap (ZMod 2) SUF a + algebraMap (ZMod 2) SUF b * suOmega) *
        Matrix.SpecialLinearGroup.transvection (i := (1 : Fin 6)) (j := (5 : Fin 6))
          (by decide) (SUσ (algebraMap (ZMod 2) SUF a +
            algebraMap (ZMod 2) SUF b * suOmega)) := by
  let c : SUF := algebraMap (ZMod 2) SUF a + algebraMap (ZMod 2) SUF b * suOmega
  let B : SUG 6 := suZ (k := 6) (by decide) ![0, a, b, 0]
  let T04 : Matrix.SpecialLinearGroup (Fin 6) SUF :=
    Matrix.SpecialLinearGroup.transvection (i := (0 : Fin 6)) (j := (4 : Fin 6))
      (by decide) c
  let T15 : Matrix.SpecialLinearGroup (Fin 6) SUF :=
    Matrix.SpecialLinearGroup.transvection (i := (1 : Fin 6)) (j := (5 : Fin 6))
      (by decide) (SUσ c)
  have hcoe := E6GraphLevi.coe_unitarySLEquiv (K := SUF) (f := 1)
    (σ := SUσ.toRingHom) hσ
    ((E6GraphLevi.unitarySLEquiv (K := SUF) (f := 1) (σ := SUσ.toRingHom) hσ).symm B)
  rw [MulEquiv.apply_symm_apply] at hcoe
  have hcoeM := congrArg
    (fun u : GL (Fin 6) SUF => (u : Matrix (Fin 6) (Fin 6) SUF)) hcoe
  rw [Matrix.SpecialLinearGroup.coe_GL_coe_matrix] at hcoeM
  change (((B : SUG 6) : GL (Fin 6) SUF) : Matrix (Fin 6) (Fin 6) SUF) =
    ((((E6GraphLevi.unitarySLEquiv (K := SUF) (f := 1) (σ := SUσ.toRingHom) hσ).symm B :
      ↥(E6GraphLevi.unitarySL SUσ.toRingHom)) :
      Matrix.SpecialLinearGroup (Fin 6) SUF) : Matrix (Fin 6) (Fin 6) SUF) at hcoeM
  rw [suZ_val] at hcoeM
  have hSL : ((((E6GraphLevi.unitarySLEquiv (K := SUF) (f := 1)
      (σ := SUσ.toRingHom) hσ).symm B :
      ↥(E6GraphLevi.unitarySL SUσ.toRingHom)) :
      Matrix.SpecialLinearGroup (Fin 6) SUF)) = T04 * T15 := by
    apply Subtype.ext
    calc
      (((((E6GraphLevi.unitarySLEquiv (K := SUF) (f := 1)
          (σ := SUσ.toRingHom) hσ).symm B :
          ↥(E6GraphLevi.unitarySL SUσ.toRingHom)) :
          Matrix.SpecialLinearGroup (Fin 6) SUF)) :
          Matrix (Fin 6) (Fin 6) SUF) = suCorner (k := 6) (by decide)
            ![0, a, b, 0] := hcoeM.symm
      _ = (((T04 * T15 : Matrix.SpecialLinearGroup (Fin 6) SUF)) :
          Matrix (Fin 6) (Fin 6) SUF) := by
        simp only [T04, T15, c]
        exact suCorner_six_support a b
  simpa [B, T04, T15, c] using hSL

private theorem proj_rootE15_eq :
    proj CFSG.SeitzReduction.TwistedE6Pilot.rootE15 =
      CFSG.SeitzReduction.TwistedE6Pilot.relRoot0121 := by
  funext i
  fin_cases i <;> decide +kernel


section Realization


private theorem realize_transvection_04
    {E : Type} [Field E] (h2 : (2 : E) = 0) (c : E) :
    E6GraphLevi.realize (E := E) h2
      (Matrix.SpecialLinearGroup.transvection (i := (0 : Fin 6)) (j := (4 : Fin 6))
        (by decide) c) =
      pinnedX TwistTag.E6.tag E rootE15 c := by
  have hp : E6GraphLevi.pathSum (3 : Fin 5) = rootE15 := by decide +kernel
  have h := E6GraphLevi.realize_upper (E := E) h2 c (3 : Fin 5)
  simpa [hp] using h

private theorem realize_transvection_15
    {E : Type} [Field E] (h2 : (2 : E) = 0) (c : E) :
    E6GraphLevi.realize (E := E) h2
      (Matrix.SpecialLinearGroup.transvection (i := (1 : Fin 6)) (j := (5 : Fin 6))
        (by decide) c) =
      pinnedX TwistTag.E6.tag E rootE26 c := by
  let T04 : Matrix.SpecialLinearGroup (Fin 6) E :=
    Matrix.SpecialLinearGroup.transvection (i := (0 : Fin 6)) (j := (4 : Fin 6))
      (by decide) c
  let T15 : Matrix.SpecialLinearGroup (Fin 6) E :=
    Matrix.SpecialLinearGroup.transvection (i := (1 : Fin 6)) (j := (5 : Fin 6))
      (by decide) c
  let D : ModGL TwistTag.E6.tag E := diagramMap TwistTag.E6 E
  have hgraph : E6GraphLevi.graphSL E T04 = T15 := by
    dsimp [T04, T15]
    simpa using E6GraphLevi.graphSL_transvection (E := E) h2 (i := (0 : Fin 6))
      (j := (4 : Fin 6)) (by decide) c
  have h04 : E6GraphLevi.realize h2 T04 = pinnedX TwistTag.E6.tag E rootE15 c :=
    realize_transvection_04 (E := E) h2 c
  have hconj := E6GraphLevi.diagramMap_conj_realize (E := E) h2 T04
  have hroot : IsRoot TwistTag.E6.tag rootE15 :=
    (CFSG.SeitzReduction.TwistedE6Pilot.isRoot_rootE15).1
  have hpin := E6GraphRadical.diagramMap_conj_pinnedX_of_two (E := E) h2 hroot c
  calc
    E6GraphLevi.realize h2 T15 = D * E6GraphLevi.realize h2 T04 * D⁻¹ := by
      rw [← hgraph]
      exact hconj.symm
    _ = D * pinnedX TwistTag.E6.tag E rootE15 c * D⁻¹ := by rw [h04]
    _ = pinnedX TwistTag.E6.tag E rootE26 c := by
      change D * pinnedX TwistTag.E6.tag E rootE15 c * D⁻¹ =
        pinnedX TwistTag.E6.tag E (rho rootE15) c at hpin
      rw [rho_rootE15_eq] at hpin
      exact hpin

theorem su6LeviHom_suZ_eq_pinned
    (hF : Nat.card SUF = (2 ^ 1) ^ 2)
    (hσ : ∀ c, SUσ.toRingHom c = c ^ (2 ^ 1)) (a b : ZMod 2) :
    ((KGTwE6.su6LeviHom (f := 1) hF hσ
      (suZ (k := 6) (by decide) ![0, a, b, 0]) :
      ↥((su6Levi SUσ.toRingHom).subgroupOf
        (graphFixedRootGroup TwistTag.E6 SUF SUσ.toRingHom))) :
      ModGL TwistTag.E6.tag SUF) =
    pinnedX TwistTag.E6.tag SUF rootE15
      (algebraMap (ZMod 2) SUF a + algebraMap (ZMod 2) SUF b * suOmega) *
    pinnedX TwistTag.E6.tag SUF rootE26
      (SUσ (algebraMap (ZMod 2) SUF a + algebraMap (ZMod 2) SUF b * suOmega)) := by
  let c : SUF := algebraMap (ZMod 2) SUF a + algebraMap (ZMod 2) SUF b * suOmega
  have h2 : (2 : SUF) = 0 := CharP.cast_eq_zero SUF 2
  have hSL := unitarySLEquiv_symm_suZ_six (hσ := hσ) a b
  rw [KGTwE6.coe_su6LeviHom]
  rw [hSL, map_mul]
  rw [realize_transvection_04 (E := SUF) h2 c]
  rw [realize_transvection_15 (E := SUF) h2 (SUσ c)]

end Realization

section RootMembership


theorem relRoot0121_mem_roots {K : Type} [Field K] (θ : K →+* K) :
    relRoot0121 ∈ (twistedDatum K θ).roots := by
  rw [twistedDatum_roots]
  exact (mem_rootFinset (τ := Tag.F4) (v := CFSG.SeitzReduction.TwistedE6Pilot.relRoot0121)).1 (by decide +kernel)

theorem relRoot0121_two_smul_not_mem_roots {K : Type} [Field K] (θ : K →+* K) :
    (2 : ℕ) • relRoot0121 ∉ (twistedDatum K θ).roots := by
  rw [twistedDatum_roots]
  intro h
  exact (by decide +kernel :
    (2 : ℕ) • CFSG.SeitzReduction.TwistedE6Pilot.relRoot0121 ∉
      rootFinset Tag.F4) ((mem_rootFinset (τ := Tag.F4) (v := (2 : ℕ) • CFSG.SeitzReduction.TwistedE6Pilot.relRoot0121)).2 h)

end RootMembership

section RootLength


theorem relRoot0121_not_long {K : Type} [Field K] (θ : K →+* K) :
    ¬ GGLongRoot (twistedDatum K θ) relRoot0121 := by
  let D := CFSG.LieType.Steinberg.Adjoint.f4Datum K
  let hA : TauCeti.IsFiniteType (Tag.cartan .F4) :=
    CFSG.LieType.Chevalley.isFiniteType_cartan .F4
  let s := (coxeterMatrix hA).toCoxeterSystem.simple
  let i3 : Fin (Tag.rank .F4) := ⟨3, by decide⟩
  let j3 : Fin D.rank := ⟨3, by change 3 < 4; decide⟩
  let w : (coxeterMatrix hA).Group :=
    s ⟨2, by decide⟩ * s ⟨1, by decide⟩ * s ⟨2, by decide⟩
  have hw : relRoot0121 = weylAction hA w (Pi.single i3 1) := by
    simp only [w, s, i3, weylAction_mul_apply, weylAction_simple,
      reflection_apply, relRoot0121]
    funext i
    fin_cases i <;> decide +kernel
  intro hlong
  have hD : GGLongRoot D relRoot0121 := hlong
  have hW : GGLongRoot D
      (weylAction D.isFiniteType (show GGWeyl D from w)
        (Pi.single j3 1)) :=
    (congrArg (fun v : Fin (Tag.rank .F4) → ℤ => GGLongRoot D v) hw).mp hD
  have h3 : GGLongRoot D (Pi.single j3 1) :=
    (CFSG.StandardType.LieKnownR2.Short.ggLongRoot_weylAction_iff
      D (show GGWeyl D from w) (Pi.single j3 1)).mp hW
  have hle : j3.val ≤ 1 :=
    (CFSG.StandardType.LieKnownR2.Short.f4_ggLongRoot_single_iff
      K (show Fin (CFSG.LieType.Steinberg.Adjoint.f4Datum K).rank from j3)).mp h3
  exact (by decide : ¬ (3 : ℕ) ≤ 1) hle

end RootLength

private theorem coe_pi_xPair_rootE15
    (hF : Nat.card SUF = (2 ^ 1) ^ 2)
    (hσ : ∀ c, SUσ.toRingHom c = c ^ (2 ^ 1)) (c : SUF) :
    ((F4Pilot.twistedIsogenyC (f := 1) (by decide) hF SUσ.toRingHom hσ
        (xPair SUσ.toRingHom (F4Pilot.involutive_of_natCard_eq hF hσ)
          (CFSG.SeitzReduction.TwistedE6Pilot.isRoot_rootE15).1
          rho_rootE15_ne_self c) :
        graphFixedRootGroup TwistTag.E6 SUF SUσ.toRingHom) :
        ModGL TwistTag.E6.tag SUF) =
      pinnedX TwistTag.E6.tag SUF CFSG.SeitzReduction.TwistedE6Pilot.rootE15 c *
      pinnedX TwistTag.E6.tag SUF CFSG.SeitzReduction.TwistedE6Pilot.rootE26 (SUσ c) := by
  let γ : Fin (Tag.rank .E6) → ℤ := CFSG.SeitzReduction.TwistedE6Pilot.rootE15
  have hγ : IsRoot .E6 γ := by
    change IsRoot TwistTag.E6.tag CFSG.SeitzReduction.TwistedE6Pilot.rootE15
    exact (CFSG.SeitzReduction.TwistedE6Pilot.isRoot_rootE15).1
  have hneγ : rho γ ≠ γ := by
    change rho CFSG.SeitzReduction.TwistedE6Pilot.rootE15 ≠
      CFSG.SeitzReduction.TwistedE6Pilot.rootE15
    exact rho_rootE15_ne_self
  have hθ : ∀ c, SUσ.toRingHom (SUσ.toRingHom c) = c :=
    F4Pilot.involutive_of_natCard_eq hF hσ
  have hs : ((twistSign γ : ℤ) : SUF) = 1 := by
    rcases twistSign_eq_one_or γ with h | h
    · rw [h, Int.cast_one]
    · rw [h, Int.cast_neg, Int.cast_one, CharTwo.neg_eq]
  rw [CFSG.SeitzReduction.F4Pilot.coe_twistedIsogenyC]
  change ((CFSG.LieType.Steinberg.Isogeny.e6Isogeny SUF
      ((xPair SUσ.toRingHom hθ hγ hneγ c : fixedGroup SUF SUσ.toRingHom) :
        CFSG.LieType.Steinberg.Minuscule.e6Data_valid.minGroup SUF) :
        adjointGroup .E6 SUF) : ModGL .E6 SUF) = _
  rw [xPair_val SUσ.toRingHom hθ hγ hneγ c, map_mul, Subgroup.coe_mul,
    CFSG.SeitzReduction.E6Pilot.coe_e6Isogeny_xm hγ,
    CFSG.SeitzReduction.E6Pilot.coe_e6Isogeny_xm (isRoot_rho hγ),
    hs, one_mul]
  change pinnedX Tag.E6 SUF γ c * pinnedX Tag.E6 SUF (rho γ) (SUσ c) =
    pinnedX TwistTag.E6.tag SUF CFSG.SeitzReduction.TwistedE6Pilot.rootE15 c *
    pinnedX TwistTag.E6.tag SUF CFSG.SeitzReduction.TwistedE6Pilot.rootE26 (SUσ c)
  rw [show rho γ = CFSG.SeitzReduction.TwistedE6Pilot.rootE26 from by
    simpa [γ] using rho_rootE15_eq]
  rfl

private theorem su6LeviHom_suZ_eq_pi_xPair
    (hF : Nat.card SUF = (2 ^ 1) ^ 2)
    (hσ : ∀ c, SUσ.toRingHom c = c ^ (2 ^ 1)) (a b : ZMod 2) :
    ((((su6Levi SUσ.toRingHom).subgroupOf
        (graphFixedRootGroup TwistTag.E6 SUF SUσ.toRingHom)).subtype.comp
        (KGTwE6.su6LeviHom (f := 1) hF hσ)) (suZ (k := 6) (by decide) ![0, a, b, 0])) =
      (F4Pilot.twistedIsogenyC (f := 1) (by decide) hF SUσ.toRingHom hσ
        (xPair SUσ.toRingHom (F4Pilot.involutive_of_natCard_eq hF hσ)
          (CFSG.SeitzReduction.TwistedE6Pilot.isRoot_rootE15).1
          rho_rootE15_ne_self
          (algebraMap (ZMod 2) SUF a + algebraMap (ZMod 2) SUF b * suOmega))) := by
  apply Subtype.ext
  change ((KGTwE6.su6LeviHom (f := 1) hF hσ
      (suZ (k := 6) (by decide) ![0, a, b, 0]) :
      ↥((su6Levi SUσ.toRingHom).subgroupOf
        (graphFixedRootGroup TwistTag.E6 SUF SUσ.toRingHom))) :
      ModGL TwistTag.E6.tag SUF) =
    ((F4Pilot.twistedIsogenyC (f := 1) (by decide) hF SUσ.toRingHom hσ
      (xPair SUσ.toRingHom (F4Pilot.involutive_of_natCard_eq hF hσ)
        (CFSG.SeitzReduction.TwistedE6Pilot.isRoot_rootE15).1
        rho_rootE15_ne_self
        (algebraMap (ZMod 2) SUF a + algebraMap (ZMod 2) SUF b * suOmega)) :
      graphFixedRootGroup TwistTag.E6 SUF SUσ.toRingHom) :
      ModGL TwistTag.E6.tag SUF)
  rw [su6LeviHom_suZ_eq_pinned hF hσ a b, coe_pi_xPair_rootE15 hF hσ]

theorem su6LeviHom_map_suV
    (hF : Nat.card SUF = (2 ^ 1) ^ 2)
    (hσ : ∀ c, SUσ.toRingHom c = c ^ (2 ^ 1)) :
    (suV (k := 6) (by decide)).map
      (((su6Levi SUσ.toRingHom).subgroupOf
        (graphFixedRootGroup TwistTag.E6 SUF SUσ.toRingHom)).subtype.comp
        (KGTwE6.su6LeviHom (f := 1) hF hσ)) =
    ((twistedDatum SUF SUσ.toRingHom).rootGroup relRoot0121).map
      (F4Pilot.twistedIsogenyC (f := 1) (by decide) hF SUσ.toRingHom hσ) := by
  apply Subgroup.ext
  intro y
  constructor
  · rintro hy
    rw [Subgroup.mem_map] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    rw [mem_suV_iff (k := 6) (by decide)] at hx
    obtain ⟨a, b, rfl⟩ := hx
    have hθ : ∀ c, SUσ.toRingHom (SUσ.toRingHom c) = c :=
      F4Pilot.involutive_of_natCard_eq hF hσ
    have hroot : IsRoot TwistTag.E6.tag CFSG.SeitzReduction.TwistedE6Pilot.rootE15 :=
      (CFSG.SeitzReduction.TwistedE6Pilot.isRoot_rootE15).1
    have hne : rho CFSG.SeitzReduction.TwistedE6Pilot.rootE15 ≠
        CFSG.SeitzReduction.TwistedE6Pilot.rootE15 := rho_rootE15_ne_self
    have hp : proj CFSG.SeitzReduction.TwistedE6Pilot.rootE15 =
        CFSG.SeitzReduction.TwistedE6Pilot.relRoot0121 := proj_rootE15_eq
    let c : SUF := algebraMap (ZMod 2) SUF a + algebraMap (ZMod 2) SUF b * suOmega
    refine Subgroup.mem_map.2 ⟨xPair SUσ.toRingHom hθ hroot hne c, ?_, ?_⟩
    · change xPair SUσ.toRingHom hθ hroot hne c ∈
        twistedRootGroup SUF (SUσ.toRingHom) relRoot0121
      simpa [hp] using xPair_mem SUσ.toRingHom hθ hroot hne c
    · exact (su6LeviHom_suZ_eq_pi_xPair hF hσ a b).symm
  · rintro hy
    rw [Subgroup.mem_map] at hy
    obtain ⟨z, hz, rfl⟩ := hy
    have hθ : ∀ c, SUσ.toRingHom (SUσ.toRingHom c) = c :=
      F4Pilot.involutive_of_natCard_eq hF hσ
    have hroot : IsRoot TwistTag.E6.tag CFSG.SeitzReduction.TwistedE6Pilot.rootE15 :=
      (CFSG.SeitzReduction.TwistedE6Pilot.isRoot_rootE15).1
    have hne : rho CFSG.SeitzReduction.TwistedE6Pilot.rootE15 ≠
        CFSG.SeitzReduction.TwistedE6Pilot.rootE15 := rho_rootE15_ne_self
    have hp : proj CFSG.SeitzReduction.TwistedE6Pilot.rootE15 =
        CFSG.SeitzReduction.TwistedE6Pilot.relRoot0121 := proj_rootE15_eq
    have hz' := (mem_twistedRootGroup_iff_of_pair SUσ.toRingHom hroot hp hne z).1 hz
    obtain ⟨c, hc⟩ := hz'
    have hz_eq : z = xPair SUσ.toRingHom hθ hroot hne c := by
      apply Subtype.ext
      exact hc.trans (xPair_val SUσ.toRingHom hθ hroot hne c).symm
    obtain ⟨a, b, hab⟩ := exists_suOmega_coordinates c
    have hx : suZ (k := 6) (by decide) ![0, a, b, 0] ∈ suV (k := 6) (by decide) := by
      rw [mem_suV_iff (k := 6) (by decide)]
      exact ⟨a, b, rfl⟩
    refine Subgroup.mem_map.2 ⟨suZ (k := 6) (by decide) ![0, a, b, 0], hx, ?_⟩
    rw [hz_eq, ← hab]
    exact su6LeviHom_suZ_eq_pi_xPair hF hσ a b

end CFSG.StandardType.RCKC1

end
