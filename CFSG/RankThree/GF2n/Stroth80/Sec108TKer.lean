module

public import CFSG.RankThree.GF2n.Stroth80.Sec108T
public import CFSG.RankThree.GF2n.Stroth80.Sec108Fix
import all CFSG.RankThree.GF2n.Stroth80.Sec108T
import all CFSG.RankThree.GF2n.Stroth80.Sec108Rho
import all CFSG.RankThree.GF2n.Stroth80.Sec108BarLift
import all CFSG.RankThree.GF2n.Stroth80.Defs
import all CFSG.RankThree.GF2n.Stroth80.Ctx
import all CFSG.RankThree.GF2n.Stroth80.Basic
import all Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n.Smith81
open scoped commutatorElement
open Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
  {hc : Ctx M Q Z B} {t : G} {Y : Subgroup G} [(Q.subgroupOf M).Normal]
  (D : Sec108Data hc t Y) (AM : Smith81.Smith23E1.ActionModel M Q Z)

private noncomputable abbrev Pmat : Matrix (Fin 3) (Fin 3) AM.K :=
  (D.frameB AM : Matrix (Fin 3) (Fin 3) AM.K)

private noncomputable abbrev PinvMat : Matrix (Fin 3) (Fin 3) AM.K :=
  (((D.frameB AM)⁻¹ : Matrix.SpecialLinearGroup (Fin 3) AM.K) : Matrix (Fin 3) (Fin 3) AM.K)

private theorem frameVec_mem (v : Fin 3 → AM.K) : D.frameVec AM v ∈ AM.Vsp hc t := by
  unfold Sec108Data.frameVec
  refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (D.bV AM i).2

private theorem frameVec_eq_sum (c : Fin 3 → AM.K) :
    D.frameVec AM c = ∑ i, (Pmat D AM *ᵥ c) i • (D.bV AM i : AM.M₀.E) := rfl

private theorem frame_mul_inv (v : Fin 3 → AM.K) :
    Pmat D AM *ᵥ (PinvMat D AM *ᵥ v) = v := by
  have hmul : Pmat D AM * PinvMat D AM = 1 := by
    have h : ((D.frameB AM * (D.frameB AM)⁻¹ : Matrix.SpecialLinearGroup (Fin 3) AM.K) :
        Matrix (Fin 3) (Fin 3) AM.K) = 1 := by
      rw [mul_inv_cancel]
      rfl
    rw [show Pmat D AM * PinvMat D AM =
      ((D.frameB AM * (D.frameB AM)⁻¹ : Matrix.SpecialLinearGroup (Fin 3) AM.K) :
        Matrix (Fin 3) (Fin 3) AM.K) from rfl, h]
  calc Pmat D AM *ᵥ (PinvMat D AM *ᵥ v)
      = (Pmat D AM * PinvMat D AM) *ᵥ v := Matrix.mulVec_mulVec v _ _
    _ = 1 *ᵥ v := by rw [hmul]
    _ = v := Matrix.one_mulVec v

private theorem frame_inv_mul (v : Fin 3 → AM.K) :
    PinvMat D AM *ᵥ (Pmat D AM *ᵥ v) = v := by
  have hmul : PinvMat D AM * Pmat D AM = 1 := by
    have h : (((D.frameB AM)⁻¹ * D.frameB AM : Matrix.SpecialLinearGroup (Fin 3) AM.K) :
        Matrix (Fin 3) (Fin 3) AM.K) = 1 := by
      rw [inv_mul_cancel]
      rfl
    rw [show PinvMat D AM * Pmat D AM =
      (((D.frameB AM)⁻¹ * D.frameB AM : Matrix.SpecialLinearGroup (Fin 3) AM.K) :
        Matrix (Fin 3) (Fin 3) AM.K) from rfl, h]
  calc PinvMat D AM *ᵥ (Pmat D AM *ᵥ v)
      = (PinvMat D AM * Pmat D AM) *ᵥ v := Matrix.mulVec_mulVec v _ _
    _ = 1 *ᵥ v := by rw [hmul]
    _ = v := Matrix.one_mulVec v

private theorem repr_frameVec (c : Fin 3 → AM.K) :
    ((D.bV AM).repr ⟨D.frameVec AM c, frameVec_mem D AM c⟩ : Fin 3 → AM.K) =
      Pmat D AM *ᵥ c := by
  have h : (⟨D.frameVec AM c, frameVec_mem D AM c⟩ : ↥(AM.Vsp hc t)) =
      ∑ i, (Pmat D AM *ᵥ c) i • D.bV AM i := by
    refine Subtype.ext ?_
    change D.frameVec AM c = ∑ i, (Pmat D AM *ᵥ c) i • (D.bV AM i : AM.M₀.E)
    rw [frameVec_eq_sum]
  rw [h, Module.Basis.repr_sum_self]

private theorem frameCoord_apply {e : AM.M₀.E} (he : e ∈ AM.Vsp hc t) :
    D.frameCoord AM e =
      PinvMat D AM *ᵥ ((D.bV AM).repr ⟨e, he⟩ : Fin 3 → AM.K) := by
  unfold Sec108Data.frameCoord
  rw [dif_pos he]

private theorem frameCoord_frameVec (v : Fin 3 → AM.K) :
    D.frameCoord AM (D.frameVec AM v) = v := by
  rw [show D.frameCoord AM (D.frameVec AM v) =
      PinvMat D AM *ᵥ ((D.bV AM).repr ⟨D.frameVec AM v, frameVec_mem D AM v⟩ :
        Fin 3 → AM.K) from frameCoord_apply D AM (frameVec_mem D AM v)]
  rw [repr_frameVec]
  exact frame_inv_mul D AM v

private theorem frameVec_frameCoord {e : AM.M₀.E} (he : e ∈ AM.Vsp hc t) :
    D.frameVec AM (D.frameCoord AM e) = e := by
  calc D.frameVec AM (D.frameCoord AM e)
      = D.frameVec AM (PinvMat D AM *ᵥ
          ((D.bV AM).repr ⟨e, he⟩ : Fin 3 → AM.K)) := by
        rw [frameCoord_apply D AM he]
    _ = ∑ i, (Pmat D AM *ᵥ (PinvMat D AM *ᵥ
          ((D.bV AM).repr ⟨e, he⟩ : Fin 3 → AM.K))) i • (D.bV AM i : AM.M₀.E) :=
        frameVec_eq_sum D AM _
    _ = ∑ i, ((D.bV AM).repr ⟨e, he⟩ : Fin 3 → AM.K) i • (D.bV AM i : AM.M₀.E) := by
        rw [frame_mul_inv D AM ((D.bV AM).repr ⟨e, he⟩ : Fin 3 → AM.K)]
    _ = e := congrArg Subtype.val (Module.Basis.sum_repr (D.bV AM) ⟨e, he⟩)

private theorem e0_ne_zero : Sec108.e₀ AM.K ≠ 0 := by
  intro h
  have h1 := congrFun h 0
  simp [Sec108.e₀] at h1

private theorem frameVec_e0_ne_zero : D.frameVec AM (Sec108.e₀ AM.K) ≠ 0 := by
  intro h
  have h0 : D.frameCoord AM (0 : AM.M₀.E) = 0 := by
    rw [frameCoord_apply D AM (Submodule.zero_mem _)]
    have hrep : ((D.bV AM).repr (0 : ↥(AM.Vsp hc t)) : Fin 3 → AM.K) = 0 := by simp
    rw [show (⟨0, Submodule.zero_mem _⟩ : ↥(AM.Vsp hc t)) = 0 from rfl, hrep]
    simp
  have hc := frameCoord_frameVec D AM (Sec108.e₀ AM.K)
  rw [h, h0] at hc
  exact e0_ne_zero AM hc.symm

private abbrev NLYsub : Subgroup (Mbar M Q) :=
  Sec108.NLY (bar M Q (LB M Q B)) (bar M Q Y)

private theorem semiFun_eq_self_of_mem_ker
    (d : ↥(M ⊓ Subgroup.normalizer ((Y ⊔ Q : Subgroup G) : Set G)))
    (hdN : HS6.piM M Q (d : G) ∈ NLYsub (M := M) (Q := Q) (B := B) (Y := Y))
    (hT : D.semiT AM ⟨HS6.piM M Q (d : G), hdN⟩ = 1) :
    ∀ v, D.semiFun AM d v = v := by
  intro v
  have h := congrArg (fun f : AddMonoid.End (Fin 3 → AM.K) => f v) hT
  rw [D.semiT_piM AM d.2 hdN v] at h
  simpa using h

private theorem frameCoord_act_eq
    (d : ↥(M ⊓ Subgroup.normalizer ((Y ⊔ Q : Subgroup G) : Set G)))
    (hfun : ∀ v, D.semiFun AM d v = v) :
    ∀ v, D.frameCoord AM
      ((AM.glob.act (d : G) (Subgroup.mem_inf.mp d.2).1).choose_spec.choose_spec.choose
        (D.frameVec AM v)) = v := by
  intro v
  simpa only [Sec108Data.semiFun] using hfun v

private theorem act_fixes_Vsp
    (d : ↥(M ⊓ Subgroup.normalizer ((Y ⊔ Q : Subgroup G) : Set G)))
    (hcoord : ∀ v, D.frameCoord AM
      ((AM.glob.act (d : G) (Subgroup.mem_inf.mp d.2).1).choose_spec.choose_spec.choose
        (D.frameVec AM v)) = v) :
    ∀ e ∈ AM.Vsp hc t,
      (AM.glob.act (d : G) (Subgroup.mem_inf.mp d.2).1).choose_spec.choose_spec.choose e = e := by
  let T : AM.M₀.E ≃+ AM.M₀.E :=
    (AM.glob.act (d : G) (Subgroup.mem_inf.mp d.2).1).choose_spec.choose_spec.choose
  have hcoord' : ∀ v, D.frameCoord AM (T (D.frameVec AM v)) = v := by
    intro v
    simpa [T] using hcoord v
  intro e he
  have hcoord_e : D.frameCoord AM (T e) = D.frameCoord AM e := by
    have h := hcoord' (D.frameCoord AM e)
    rwa [frameVec_frameCoord D AM he] at h
  by_cases hTmem : T e ∈ AM.Vsp hc t
  · calc T e = D.frameVec AM (D.frameCoord AM (T e)) :=
        (frameVec_frameCoord D AM hTmem).symm
      _ = D.frameVec AM (D.frameCoord AM e) := by rw [hcoord_e]
      _ = e := frameVec_frameCoord D AM he
  · exfalso
    have hz : D.frameCoord AM (T e) = 0 := by
      rw [Sec108Data.frameCoord]
      exact dif_neg hTmem
    rw [hz] at hcoord_e
    have he0 : e = 0 := by
      calc e = D.frameVec AM (D.frameCoord AM e) := (frameVec_frameCoord D AM he).symm
        _ = D.frameVec AM 0 := by rw [← hcoord_e]
        _ = 0 := by simp [Sec108Data.frameVec]
    exact hTmem (by rw [he0, map_zero]; exact Submodule.zero_mem _)

private theorem act_sigma_eq_one_of_semiT_one
    (d : ↥(M ⊓ Subgroup.normalizer ((Y ⊔ Q : Subgroup G) : Set G)))
    (hdN : HS6.piM M Q (d : G) ∈ NLYsub (M := M) (Q := Q) (B := B) (Y := Y))
    (hTker : D.semiT AM ⟨HS6.piM M Q (d : G), hdN⟩ = 1) :
    (AM.glob.act (d : G) (Subgroup.mem_inf.mp d.2).1).choose = 1 := by
  let σ : AM.K ≃+* AM.K := (AM.glob.act (d : G) (Subgroup.mem_inf.mp d.2).1).choose
  let T : AM.M₀.E ≃+ AM.M₀.E :=
    (AM.glob.act (d : G) (Subgroup.mem_inf.mp d.2).1).choose_spec.choose_spec.choose
  have hsmul : ∀ (c : AM.K) (e : AM.M₀.E), T (c • e) = σ c • T e :=
    (AM.glob.act (d : G) (Subgroup.mem_inf.mp d.2).1).choose_spec.choose_spec.choose_spec.1
  change σ = 1
  have hfix := act_fixes_Vsp D AM d (frameCoord_act_eq D AM d
    (semiFun_eq_self_of_mem_ker D AM d hdN hTker))
  have he0' : D.frameVec AM (Sec108.e₀ AM.K) ≠ 0 := frameVec_e0_ne_zero D AM
  have hmem0 : D.frameVec AM (Sec108.e₀ AM.K) ∈ AM.Vsp hc t := frameVec_mem D AM _
  ext c
  have h1 : T (c • D.frameVec AM (Sec108.e₀ AM.K)) =
      c • D.frameVec AM (Sec108.e₀ AM.K) := hfix _ (Submodule.smul_mem _ c hmem0)
  rw [hsmul, hfix _ hmem0] at h1
  simpa using smul_left_injective AM.K he0' h1

private noncomputable abbrev actScalar
    (d : ↥(M ⊓ Subgroup.normalizer ((Y ⊔ Q : Subgroup G) : Set G))) : AM.Kˣ :=
  (AM.glob.act (d : G) (Subgroup.mem_inf.mp d.2).1).choose_spec.choose

private theorem gamma_actScalar
    (d : ↥(M ⊓ Subgroup.normalizer ((Y ⊔ Q : Subgroup G) : Set G)))
    (hσ : (AM.glob.act (d : G) (Subgroup.mem_inf.mp d.2).1).choose = 1) :
    ∀ z ∈ Z, AM.γ ((d : G) * z * (d : G)⁻¹) = (actScalar AM d : AM.K) * AM.γ z := by
  intro z hz
  have hσγ : ∀ c : AM.K,
      (AM.glob.act (d : G) (Subgroup.mem_inf.mp d.2).1).choose c = c := by
    intro c; rw [hσ]; rfl
  have h := (AM.glob.act (d : G)
    (Subgroup.mem_inf.mp d.2).1).choose_spec.choose_spec.choose_spec.2.2.1 z hz
  rw [h, hσγ]

private theorem gamma_conj_inv_one (hc : Ctx M Q Z B) {x : G} (hxM : x ∈ M) {a : AM.Kˣ}
    (hγ : ∀ z ∈ Z, AM.γ (x * z * x⁻¹) = (a : AM.K) * AM.γ z) :
    ∀ w ∈ Z, AM.γ (x⁻¹ * w * x) = ((a⁻¹ : AM.Kˣ) : AM.K) * AM.γ w := by
  intro w hw
  have hxZ : x ∈ Subgroup.normalizer (Z : Set G) := (StrothHyp.Z_normal hc.hyp).2 hxM
  have hxZ' : x⁻¹ ∈ Subgroup.normalizer (Z : Set G) := Subgroup.inv_mem _ hxZ
  have hz : x⁻¹ * w * x ∈ Z := by
    simpa [inv_inv] using (Subgroup.mem_normalizer_iff.mp hxZ' w).mp (by simpa using hw)
  have h := hγ (x⁻¹ * w * x) hz
  have hxw : x * (x⁻¹ * w * x) * x⁻¹ = w := by group
  rw [hxw] at h
  have ha : (a : AM.K) ≠ 0 := Units.ne_zero a
  calc AM.γ (x⁻¹ * w * x)
      = ((a : AM.K)⁻¹) * ((a : AM.K) * AM.γ (x⁻¹ * w * x)) := by
        rw [← mul_assoc, inv_mul_cancel₀ ha, one_mul]
    _ = ((a⁻¹ : AM.Kˣ) : AM.K) * AM.γ w := by
        rw [← h, Units.val_inv_eq_inv_val]

private theorem gamma_conj_commutator_one (hc : Ctx M Q Z B) {d e : G} (hdM : d ∈ M)
    (heM : e ∈ M) {ad ae : AM.Kˣ}
    (hd : ∀ z ∈ Z, AM.γ (d * z * d⁻¹) = (ad : AM.K) * AM.γ z)
    (he : ∀ z ∈ Z, AM.γ (e * z * e⁻¹) = (ae : AM.K) * AM.γ z) :
    ∀ w ∈ Z, AM.γ (⁅d, e⁆ * w * ⁅d, e⁆⁻¹) = AM.γ w := by
  intro w hw
  have hz1 : e⁻¹ * w * e ∈ Z := by
    simpa [inv_inv] using (Subgroup.mem_normalizer_iff.mp
      (Subgroup.inv_mem _ ((StrothHyp.Z_normal hc.hyp).2 heM)) w).mp (by simpa using hw)
  have hz2 : d⁻¹ * (e⁻¹ * w * e) * d ∈ Z := by
    simpa [inv_inv] using (Subgroup.mem_normalizer_iff.mp
      (Subgroup.inv_mem _ ((StrothHyp.Z_normal hc.hyp).2 hdM)) _).mp hz1
  have hz3 : e * (d⁻¹ * (e⁻¹ * w * e) * d) * e⁻¹ ∈ Z :=
    (Subgroup.mem_normalizer_iff.mp ((StrothHyp.Z_normal hc.hyp).2 heM) _).mp hz2
  have h1 := gamma_conj_inv_one (AM := AM) hc heM he w hw
  have h2 := gamma_conj_inv_one (AM := AM) hc hdM hd (e⁻¹ * w * e) hz1
  have h3 := he (d⁻¹ * (e⁻¹ * w * e) * d) hz2
  have h4 := hd (e * (d⁻¹ * (e⁻¹ * w * e) * d) * e⁻¹) hz3
  have hscalar : (ad : AM.K) * (ae : AM.K) * ((ad⁻¹ : AM.Kˣ) : AM.K) *
      ((ae⁻¹ : AM.Kˣ) : AM.K) = 1 := by
    simpa only [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_one] using
      congrArg Units.val (show ad * ae * ad⁻¹ * ae⁻¹ = (1 : AM.Kˣ) by
        rw [mul_comm ad ae]; simp [mul_assoc])
  calc AM.γ (⁅d, e⁆ * w * ⁅d, e⁆⁻¹)
      = AM.γ (d * (e * (d⁻¹ * (e⁻¹ * w * e) * d) * e⁻¹) * d⁻¹) := by
        rw [commutatorElement_def]
        congr 1
        group
    _ = (ad : AM.K) * AM.γ (e * (d⁻¹ * (e⁻¹ * w * e) * d) * e⁻¹) := h4
    _ = (ad : AM.K) * ((ae : AM.K) * AM.γ (d⁻¹ * (e⁻¹ * w * e) * d)) := by rw [h3]
    _ = (ad : AM.K) * ((ae : AM.K) * (((ad⁻¹ : AM.Kˣ) : AM.K) *
          AM.γ (e⁻¹ * w * e))) := by rw [h2]
    _ = (ad : AM.K) * ((ae : AM.K) * (((ad⁻¹ : AM.Kˣ) : AM.K) *
          (((ae⁻¹ : AM.Kˣ) : AM.K) * AM.γ w))) := by rw [h1]
    _ = AM.γ w := by
        rw [show (ad : AM.K) * ((ae : AM.K) * (((ad⁻¹ : AM.Kˣ) : AM.K) *
          (((ae⁻¹ : AM.Kˣ) : AM.K) * AM.γ w))) =
          ((ad : AM.K) * (ae : AM.K) * ((ad⁻¹ : AM.Kˣ) : AM.K) *
            ((ae⁻¹ : AM.Kˣ) : AM.K)) * AM.γ w by ring]
        rw [hscalar, one_mul]

private theorem gamma_conj_pow_one (hc : Ctx M Q Z B) {x : G} (hxM : x ∈ M) {a : AM.Kˣ}
    (hγ : ∀ z ∈ Z, AM.γ (x * z * x⁻¹) = (a : AM.K) * AM.γ z) (n : ℕ) :
    ∀ z ∈ Z, AM.γ (x ^ n * z * (x ^ n)⁻¹) = ((a ^ n : AM.Kˣ) : AM.K) * AM.γ z := by
  induction n with
  | zero => intro z hz; simp
  | succ n ih =>
    intro z hz
    have hxZ : x ∈ Subgroup.normalizer (Z : Set G) := (StrothHyp.Z_normal hc.hyp).2 hxM
    have hw : x ^ n * z * (x ^ n)⁻¹ ∈ Z :=
      (Subgroup.mem_normalizer_iff.mp (Subgroup.pow_mem _ hxZ n) z).mp hz
    have h1 := hγ (x ^ n * z * (x ^ n)⁻¹) hw
    have e : x ^ (n + 1) * z * (x ^ (n + 1))⁻¹ =
        x * (x ^ n * z * (x ^ n)⁻¹) * x⁻¹ := by
      rw [pow_succ']; group
    rw [e, h1, ih z hz, pow_succ, Units.val_mul]
    ring

private theorem commutator_mem_H0_of_rep (hctx : Ctx M Q Z B)
    (d e : ↥(M ⊓ Subgroup.normalizer ((Y ⊔ Q : Subgroup G) : Set G)))
    (hdσ : (AM.glob.act (d : G) (Subgroup.mem_inf.mp d.2).1).choose = 1)
    (heσ : (AM.glob.act (e : G) (Subgroup.mem_inf.mp e.2).1).choose = 1) :
    ⁅(d : G), (e : G)⁆ ∈ H0 M Z := by
  have hdM : (d : G) ∈ M := (Subgroup.mem_inf.mp d.2).1
  have heM : (e : G) ∈ M := (Subgroup.mem_inf.mp e.2).1
  have hcentral := gamma_conj_commutator_one (AM := AM) hctx hdM heM
    (gamma_actScalar AM d hdσ) (gamma_actScalar AM e heσ)
  have hcM : ⁅(d : G), (e : G)⁆ ∈ M := by
    rw [commutatorElement_def]
    exact M.mul_mem (M.mul_mem (M.mul_mem hdM heM) (M.inv_mem hdM)) (M.inv_mem heM)
  refine ⟨hcM, Subgroup.mem_centralizer_iff.mpr fun z hz => ?_⟩
  have hzZ : ⁅(d : G), (e : G)⁆ * z * ⁅(d : G), (e : G)⁆⁻¹ ∈ Z :=
    (Subgroup.mem_normalizer_iff.mp ((StrothHyp.Z_normal hctx.hyp).2 hcM) z).mp hz
  have heq : ⁅(d : G), (e : G)⁆ * z * ⁅(d : G), (e : G)⁆⁻¹ = z :=
    AM.glob.reg.eq_of_γ_eq hzZ hz (hcentral z hz)
  rw [mul_inv_eq_iff_eq_mul] at heq
  exact heq.symm

private noncomputable def repNLY (g : ↥(NLYsub (M := M) (Q := Q) (B := B) (Y := Y))) :
    ↥(M ⊓ Subgroup.normalizer ((Y ⊔ Q : Subgroup G) : Set G)) :=
  barRep ⟨g, NLY_le_bar_normalizer hc.hyp.Q_normal.1
    (D.root_le_LB.trans hc.LB_le_M) g.2⟩

private theorem repNLY_piM (g : ↥(NLYsub (M := M) (Q := Q) (B := B) (Y := Y))) :
    HS6.piM M Q (repNLY D g : G) = (g : Mbar M Q) := by
  exact piM_barRep (S := M ⊓
    Subgroup.normalizer ((Y ⊔ Q : Subgroup G) : Set G))
    ⟨g, NLY_le_bar_normalizer hc.hyp.Q_normal.1
      (D.root_le_LB.trans hc.LB_le_M) g.2⟩

private theorem piM_pow {x : G} (hx : x ∈ M) (n : ℕ) :
    HS6.piM M Q (x ^ n) = (HS6.piM M Q x) ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, HS6.piM_one]
  | succ n ih =>
    rw [pow_succ, pow_succ, HS6.piM_mul (M.pow_mem hx n) hx, ih]

private theorem piM_commutator {x y : G} (hx : x ∈ M) (hy : y ∈ M) :
    HS6.piM M Q ⁅x, y⁆ = ⁅HS6.piM M Q x, HS6.piM M Q y⁆ := by
  rw [commutatorElement_def, commutatorElement_def]
  rw [HS6.piM_mul (M.mul_mem (M.mul_mem hx hy) (M.inv_mem hx)) (M.inv_mem hy),
    HS6.piM_mul (M.mul_mem hx hy) (M.inv_mem hx), HS6.piM_mul hx hy,
    HS6.piM_inv hx, HS6.piM_inv hy]

private theorem act_sigma_of_rep (g : ↥(NLYsub (M := M) (Q := Q) (B := B) (Y := Y)))
    (hg : g ∈ (D.semiT AM).ker) :
    (AM.glob.act (repNLY D g : G) (Subgroup.mem_inf.mp (repNLY D g).2).1).choose = 1 := by
  have hdN : HS6.piM M Q (repNLY D g : G) ∈ NLYsub (M := M) (Q := Q) (B := B) (Y := Y) := by
    rw [repNLY_piM D g]; exact g.2
  have hTd : D.semiT AM ⟨HS6.piM M Q (repNLY D g : G), hdN⟩ = 1 := by
    have hg' : (⟨HS6.piM M Q (repNLY D g : G), hdN⟩ :
        ↥(NLYsub (M := M) (Q := Q) (B := B) (Y := Y))) = g :=
      Subtype.ext (repNLY_piM D g)
    rw [hg']
    exact MonoidHom.mem_ker.mp hg
  exact act_sigma_eq_one_of_semiT_one D AM (repNLY D g) hdN hTd

private theorem commutator_mem_H0_ker
    (g h : ↥(NLYsub (M := M) (Q := Q) (B := B) (Y := Y)))
    (hg : g ∈ (D.semiT AM).ker) (hh : h ∈ (D.semiT AM).ker) :
    ((⁅g, h⁆ : ↥(NLYsub (M := M) (Q := Q) (B := B) (Y := Y))) : Mbar M Q) ∈
      bar M Q (H0 M Z) := by
  let d : ↥(M ⊓ Subgroup.normalizer ((Y ⊔ Q : Subgroup G) : Set G)) := repNLY D g
  let e : ↥(M ⊓ Subgroup.normalizer ((Y ⊔ Q : Subgroup G) : Set G)) := repNLY D h
  have hH0 : ⁅(d : G), (e : G)⁆ ∈ H0 M Z :=
    commutator_mem_H0_of_rep (hctx := hc) (AM := AM) d e
      (by simpa [d] using act_sigma_of_rep D AM g hg)
      (by simpa [e] using act_sigma_of_rep D AM h hh)
  have hdM : (d : G) ∈ M := (Subgroup.mem_inf.mp d.2).1
  have hpiD : HS6.piM M Q (d : G) = (g : Mbar M Q) := by
    simpa [d] using repNLY_piM D g
  have hpiE : HS6.piM M Q (e : G) = (h : Mbar M Q) := by
    simpa [e] using repNLY_piM D h
  have hpiComm : HS6.piM M Q (⁅(d : G), (e : G)⁆ : G) =
      ((⁅g, h⁆ : ↥(NLYsub (M := M) (Q := Q) (B := B) (Y := Y))) : Mbar M Q) := by
    rw [piM_commutator hdM (Subgroup.mem_inf.mp e.2).1, hpiD, hpiE]
    rfl
  rw [← hpiComm]
  exact HS6.piM_mem_bar (M := M) (Q := Q) hH0 (Subgroup.mem_inf.mp hH0).1

private theorem rho_eq_one_of_semiT_eq_one {u : ↥(NLYsub (M := M) (Q := Q) (B := B) (Y := Y))}
    (hu : (u : Mbar M Q) ∈ bar M Q (Rt M (LB M Q B) t))
    (hT : D.semiT AM u = 1) :
    (D.rho AM) ⟨(u : Mbar M Q), hu⟩ = 1 := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  have h := D.semiT_rho AM u hu (Pi.single j 1)
  have hT1 : D.semiT AM u (Pi.single j 1) = Pi.single j 1 := by
    have := congrArg (fun f : AddMonoid.End (Fin 3 → AM.K) => f (Pi.single j 1)) hT
    simpa using this
  rw [hT1] at h
  have h2 := congrFun h i
  simpa [Matrix.mulVec, dotProduct, Pi.single_apply, Matrix.one_apply] using h2.symm

private theorem ker_barLift_le_of_ker_le {S T : Subgroup G} {H : Type*} [Monoid H]
    (f : ↥S →* H) (hf : ∀ s : ↥S, (s : G) ∈ Q → f s = 1)
    (hker : f.ker ≤ T.subgroupOf S) :
    ∀ x : ↥(bar M Q S), x ∈ (barLift f hf).ker → (x : Mbar M Q) ∈ bar M Q T := by
  intro x hx
  have hx' : f (barRep x) = 1 := by
    have h := hx
    rw [MonoidHom.mem_ker] at h
    simpa [barLift] using h
  have hmem : barRep x ∈ f.ker := MonoidHom.mem_ker.mpr hx'
  have hT : ((barRep x : ↥S) : G) ∈ T := Subgroup.mem_subgroupOf.mp (hker hmem)
  have hpi : HS6.piM M Q (barRep x : G) = x := piM_barRep x
  rw [← hpi]
  exact HS6.piM_mem_bar (M := M) (Q := Q) hT (barRep_mem x)

private theorem odd_card_units (D : Sec108Data hc t Y)
    (AM : Smith81.Smith23E1.ActionModel M Q Z) : Odd (Nat.card AM.Kˣ) := by
  have h := D.odd_card_units_prod AM
  rw [Nat.card_prod] at h
  exact Nat.Odd.of_mul_left h

private theorem units_eq_one_of_pow_two_pow (D : Sec108Data hc t Y) {a : AM.Kˣ} {k : ℕ}
    (h : a ^ 2 ^ k = 1) : a = 1 := by
  have hodd : Odd (Nat.card AM.Kˣ) := odd_card_units D AM
  refine orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes ?_ (orderOf_dvd_of_pow_eq_one h)
    (orderOf_dvd_natCard a))
  exact Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hodd)

private theorem pow_mem_CN_of_pow_mem_bar (D₀ : Sec108Data hc t Y)
    (g : ↥(NLYsub (M := M) (Q := Q) (B := B) (Y := Y))) (k : ℕ)
    (hk : (g : Mbar M Q) ^ 2 ^ k ∈ bar M Q (hc.CN t)) :
    (repNLY D₀ g : G) ^ 2 ^ k ∈ hc.CN t := by
  have hdM : (repNLY D₀ g : G) ∈ M := (Subgroup.mem_inf.mp (repNLY D₀ g).2).1
  have hpowpi : HS6.piM M Q ((repNLY D₀ g : G) ^ 2 ^ k) = (g : Mbar M Q) ^ 2 ^ k := by
    rw [piM_pow hdM, repNLY_piM D₀ g]
  exact (HS6.piM_mem_bar_iff (S := hc.CN t) (hc.Q_le_CN D₀.good.1.mem_LB)
    (M.pow_mem hdM _)).mp (by rw [hpowpi]; exact hk)

private theorem actScalar_pow_eq_one (D₀ : Sec108Data hc t Y) (hctx : Ctx M Q Z B)
    (d : ↥(M ⊓ Subgroup.normalizer ((Y ⊔ Q : Subgroup G) : Set G)))
    (hσ : (AM.glob.act (d : G) (Subgroup.mem_inf.mp d.2).1).choose = 1)
    {k : ℕ} (hdCN : (d : G) ^ 2 ^ k ∈ hctx.CN t) :
    actScalar AM d ^ 2 ^ k = 1 := by
  have hdM : (d : G) ∈ M := (Subgroup.mem_inf.mp d.2).1
  have hdCNH : (d : G) ^ 2 ^ k ∈ H0 M Z :=
    D₀.Rt_le_H0 ((Ctx.mem_CN (hc := hctx)).mp hdCN).1
  obtain ⟨z0, hz0Z, hz0⟩ := AM.glob.reg.surj 1
  have hγpow := gamma_conj_pow_one (AM := AM) hctx hdM (gamma_actScalar AM d hσ) (2 ^ k) z0 hz0Z
  have hcomm := (Subgroup.mem_centralizer_iff.mp hdCNH.2) z0 hz0Z
  have hfix : (d : G) ^ 2 ^ k * z0 * ((d : G) ^ 2 ^ k)⁻¹ = z0 := by
    calc (d : G) ^ 2 ^ k * z0 * ((d : G) ^ 2 ^ k)⁻¹
        = z0 * (d : G) ^ 2 ^ k * ((d : G) ^ 2 ^ k)⁻¹ := by rw [← hcomm]
      _ = z0 := by group
  rw [hfix, hz0] at hγpow
  exact Units.ext (by simpa using hγpow.symm)

private theorem actScalar_rep_eq_one (g : ↥(NLYsub (M := M) (Q := Q) (B := B) (Y := Y)))
    (hg : g ∈ (D.semiT AM).ker) (k : ℕ)
    (hk : (g : Mbar M Q) ^ 2 ^ k ∈ bar M Q (hc.CN t)) :
    actScalar AM (repNLY D g) = 1 :=
  units_eq_one_of_pow_two_pow (D := D) (AM := AM)
    (actScalar_pow_eq_one (D₀ := D) (hctx := hc) (AM := AM) (repNLY D g)
      (act_sigma_of_rep D AM g hg) (pow_mem_CN_of_pow_mem_bar (D₀ := D) g k hk))

private theorem mem_H0_of_actScalar_eq_one (hctx : Ctx M Q Z B)
    (d : ↥(M ⊓ Subgroup.normalizer ((Y ⊔ Q : Subgroup G) : Set G)))
    (hσ : (AM.glob.act (d : G) (Subgroup.mem_inf.mp d.2).1).choose = 1)
    (had1 : actScalar AM d = 1) : (d : G) ∈ H0 M Z := by
  have hdM : (d : G) ∈ M := (Subgroup.mem_inf.mp d.2).1
  refine ⟨hdM, Subgroup.mem_centralizer_iff.mpr fun z hz => ?_⟩
  have hγ' : AM.γ ((d : G) * z * (d : G)⁻¹) = AM.γ z := by
    rw [gamma_actScalar AM d hσ z hz, had1, Units.val_one, one_mul]
  have hzZ : (d : G) * z * (d : G)⁻¹ ∈ Z :=
    (Subgroup.mem_normalizer_iff.mp ((StrothHyp.Z_normal hctx.hyp).2 hdM) z).mp hz
  have heq := AM.glob.reg.eq_of_γ_eq hzZ hz hγ'
  rw [mul_inv_eq_iff_eq_mul] at heq
  exact heq.symm

private theorem pow_succ_mem_Q (D₀ : Sec108Data hc t Y)
    (g : ↥(NLYsub (M := M) (Q := Q) (B := B) (Y := Y))) {k : ℕ}
    (hk : (g : Mbar M Q) ^ 2 ^ k ∈ bar M Q (hc.CN t)) :
    (repNLY D₀ g : G) ^ 2 ^ (k + 1) ∈ Q := by
  have hdM : (repNLY D₀ g : G) ∈ M := (Subgroup.mem_inf.mp (repNLY D₀ g).2).1
  have hNexp : (g : Mbar M Q) ^ 2 ^ (k + 1) = 1 := by
    have h2 : ((g : Mbar M Q) ^ 2 ^ k) ^ 2 = 1 := D₀.isElemAbelian_bar_CN.2 _ hk
    rwa [← pow_mul, ← pow_succ] at h2
  have hpipi : HS6.piM M Q ((repNLY D₀ g : G) ^ 2 ^ (k + 1)) = 1 := by
    rw [piM_pow hdM, repNLY_piM D₀ g, hNexp]
  exact (HS6.piM_eq_one_iff (M.pow_mem hdM _)).mp hpipi

private theorem mem_bar_E_of_mem_NLY_H0 (D₀ : Sec108Data hc t Y) (hctx : Ctx M Q Z B)
    (g : ↥(NLYsub (M := M) (Q := Q) (B := B) (Y := Y)))
    (hgH : (g : Mbar M Q) ∈ bar M Q (H0 M Z)) :
    (g : Mbar M Q) ∈ bar M Q (H0 M Z ⊓
      Subgroup.normalizer ((Y ⊔ Q : Subgroup G) : Set G)) := by
  have hQH0 : Q ≤ H0 M Z := hctx.Q_le_H0
  have hQN : Q ≤ Subgroup.normalizer ((Y ⊔ Q : Subgroup G) : Set G) :=
    le_sup_right.trans Subgroup.le_normalizer
  rw [HS6.bar_inf hQH0 hQN]
  exact ⟨hgH, HS6.bar_mono inf_le_right (NLY_le_bar_normalizer hctx.hyp.Q_normal.1
    (D₀.root_le_LB.trans hctx.LB_le_M) g.2)⟩

private theorem commutator_mem_Rt_of_mem_ker_Hbar (D₀ : Sec108Data hc t Y)
    (hctx : Ctx M Q Z B) (AM₀ : Smith81.Smith23E1.ActionModel M Q Z)
    (g h : ↥(NLYsub (M := M) (Q := Q) (B := B) (Y := Y)))
    (hgH : (g : Mbar M Q) ∈ bar M Q (H0 M Z))
    (hhH : (h : Mbar M Q) ∈ bar M Q (H0 M Z)) :
    ((⁅g, h⁆ : ↥(NLYsub (M := M) (Q := Q) (B := B) (Y := Y))) : Mbar M Q) ∈
      bar M Q (Rt M (LB M Q B) t) := by
  let E : Subgroup G := H0 M Z ⊓ Subgroup.normalizer ((Y ⊔ Q : Subgroup G) : Set G)
  have hgE : (g : Mbar M Q) ∈ bar M Q E := by
    simpa [E] using mem_bar_E_of_mem_NLY_H0 (D₀ := D₀) (hctx := hctx) g hgH
  have hhE : (h : Mbar M Q) ∈ bar M Q E := by
    simpa [E] using mem_bar_E_of_mem_NLY_H0 (D₀ := D₀) (hctx := hctx) h hhH
  have hcoe : ((⁅g, h⁆ : ↥(NLYsub (M := M) (Q := Q) (B := B) (Y := Y))) : Mbar M Q) =
      ⁅(g : Mbar M Q), (h : Mbar M Q)⁆ :=
    map_commutatorElement (Subgroup.subtype _) g h
  have hcommE : ((⁅g, h⁆ : ↥(NLYsub (M := M) (Q := Q) (B := B) (Y := Y))) :
      Mbar M Q) ∈ bar M Q E := by
    rw [hcoe]
    exact (bar M Q E).mul_mem ((bar M Q E).mul_mem ((bar M Q E).mul_mem hgE hhE)
      ((bar M Q E).inv_mem hgE)) ((bar M Q E).inv_mem hhE)
  let f : ↥E →* AM₀.Kˣ × AM₀.Kˣ := D₀.oddChar AM₀
  have hf : ∀ s : ↥E, (s : G) ∈ Q → f s = 1 :=
    fun s hs => D₀.oddChar_eq_one_of_mem_Q AM₀ s hs
  have hsub : (⟨((⁅g, h⁆ : ↥(NLYsub (M := M) (Q := Q) (B := B) (Y := Y))) :
        Mbar M Q), hcommE⟩ : ↥(bar M Q E)) =
      ⁅(⟨(g : Mbar M Q), hgE⟩ : ↥(bar M Q E)),
        (⟨(h : Mbar M Q), hhE⟩ : ↥(bar M Q E))⁆ := by
    refine Subtype.ext ?_
    exact hcoe
  have hker : (⟨((⁅g, h⁆ : ↥(NLYsub (M := M) (Q := Q) (B := B) (Y := Y))) :
        Mbar M Q), hcommE⟩ : ↥(bar M Q E)) ∈ (barLift f hf).ker := by
    rw [MonoidHom.mem_ker, hsub, map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.mpr (mul_comm _ _)
  exact ker_barLift_le_of_ker_le f hf (D₀.ker_oddChar_le AM₀) ⟨_, hcommE⟩ hker

private theorem commutator_mem_Nbar_of_mem_ker_Hbar
    (g h : ↥(NLYsub (M := M) (Q := Q) (B := B) (Y := Y)))
    (hgK : g ∈ (D.semiT AM).ker) (hhK : h ∈ (D.semiT AM).ker)
    (hgH : (g : Mbar M Q) ∈ bar M Q (H0 M Z))
    (hhH : (h : Mbar M Q) ∈ bar M Q (H0 M Z)) :
    ((⁅g, h⁆ : ↥(NLYsub (M := M) (Q := Q) (B := B) (Y := Y))) : Mbar M Q) ∈
      bar M Q (hc.CN t) := by
  have hRt : ((⁅g, h⁆ : ↥(NLYsub (M := M) (Q := Q) (B := B) (Y := Y))) :
      Mbar M Q) ∈ bar M Q (Rt M (LB M Q B) t) :=
    commutator_mem_Rt_of_mem_ker_Hbar (D₀ := D) (hctx := hc) (AM₀ := AM) g h hgH hhH
  have hKcomm : ⁅g, h⁆ ∈ (D.semiT AM).ker := by
    rw [commutatorElement_def]
    exact (D.semiT AM).ker.mul_mem ((D.semiT AM).ker.mul_mem
      ((D.semiT AM).ker.mul_mem hgK hhK) ((D.semiT AM).ker.inv_mem hgK))
      ((D.semiT AM).ker.inv_mem hhK)
  have hTcomm : D.semiT AM ⁅g, h⁆ = 1 := MonoidHom.mem_ker.mp hKcomm
  have hρ := rho_eq_one_of_semiT_eq_one D AM hRt hTcomm
  have hmem : (⟨((⁅g, h⁆ : ↥(NLYsub (M := M) (Q := Q) (B := B) (Y := Y))) :
      Mbar M Q), hRt⟩ : ↥(bar M Q (Rt M (LB M Q B) t))) ∈ (D.rho AM).ker :=
    MonoidHom.mem_ker.mpr hρ
  rw [D.ker_rho AM] at hmem
  exact Subgroup.mem_subgroupOf.mp hmem

theorem Sec108Data.semiT_ker_comm :
    ⁅⁅(D.semiT AM).ker, (D.semiT AM).ker⁆, ⁅(D.semiT AM).ker, (D.semiT AM).ker⁆⁆ ≤
      (bar M Q (hc.CN t)).subgroupOf (Sec108.NLY (bar M Q (LB M Q B)) (bar M Q Y)) := by
  let K := (D.semiT AM).ker
  let HbarN := (bar M Q (H0 M Z)).subgroupOf
    (Sec108.NLY (bar M Q (LB M Q B)) (bar M Q Y))
  let NbarN := (bar M Q (hc.CN t)).subgroupOf
    (Sec108.NLY (bar M Q (LB M Q B)) (bar M Q Y))
  have hKK : ⁅K, K⁆ ≤ K := by
    rw [Subgroup.commutator_le]
    intro x hx y hy
    rw [commutatorElement_def]
    exact K.mul_mem (K.mul_mem (K.mul_mem hx hy) (K.inv_mem hx)) (K.inv_mem hy)
  have hKH : ⁅K, K⁆ ≤ HbarN := by
    rw [Subgroup.commutator_le]
    intro x hx y hy
    exact Subgroup.mem_subgroupOf.mpr (commutator_mem_H0_ker D AM x y hx hy)
  have hder1 : ⁅K, K⁆ ≤ K ⊓ HbarN := le_inf hKK hKH
  have hder2 : ⁅K ⊓ HbarN, K ⊓ HbarN⁆ ≤ NbarN := by
    rw [Subgroup.commutator_le]
    intro x hx y hy
    exact Subgroup.mem_subgroupOf.mpr
      (commutator_mem_Nbar_of_mem_ker_Hbar D AM x y hx.1 hy.1
        (Subgroup.mem_subgroupOf.mp hx.2) (Subgroup.mem_subgroupOf.mp hy.2))
  calc ⁅⁅K, K⁆, ⁅K, K⁆⁆ ≤ ⁅K ⊓ HbarN, K ⊓ HbarN⁆ :=
        Subgroup.commutator_mono hder1 hder1
    _ ≤ NbarN := hder2

theorem Sec108Data.semiT_ker_two (g : ↥(Sec108.NLY (bar M Q (LB M Q B)) (bar M Q Y)))
    (hg : D.semiT AM g = 1) (k : ℕ) (hk : (g : Mbar M Q) ^ 2 ^ k ∈ bar M Q (hc.CN t)) :
    (g : Mbar M Q) ∈ bar M Q (hc.CN t) := by
  let d : ↥(M ⊓ Subgroup.normalizer ((Y ⊔ Q : Subgroup G) : Set G)) := repNLY D g
  have hdM : (d : G) ∈ M := (Subgroup.mem_inf.mp d.2).1
  have hdNY : (d : G) ∈ Subgroup.normalizer ((Y ⊔ Q : Subgroup G) : Set G) :=
    (Subgroup.mem_inf.mp d.2).2
  have hpiD : HS6.piM M Q (d : G) = (g : Mbar M Q) := by
    simpa [d] using repNLY_piM D g
  have hdCN : (d : G) ^ 2 ^ k ∈ hc.CN t := by
    simpa [d] using pow_mem_CN_of_pow_mem_bar (D₀ := D) g k hk
  have hσ : (AM.glob.act (d : G) (Subgroup.mem_inf.mp d.2).1).choose = 1 := by
    simpa [d] using act_sigma_of_rep D AM g hg
  have had1 : actScalar AM d = 1 := by
    simpa [d] using actScalar_rep_eq_one D AM g hg k hk
  have hdH : (d : G) ∈ H0 M Z :=
    mem_H0_of_actScalar_eq_one (hctx := hc) (AM := AM) d hσ had1
  have hdQ : (d : G) ^ 2 ^ (k + 1) ∈ Q := by
    simpa [d] using pow_succ_mem_Q (D₀ := D) g hk
  have hdR : (d : G) ∈ Rt M (LB M Q B) t :=
    D.twoElt_mem_Rt (M := M) (Q := Q) (B := B) (t := t) hdH hdNY hdQ
  have hgR : (g : Mbar M Q) ∈ bar M Q (Rt M (LB M Q B) t) := by
    have h := HS6.piM_mem_bar (M := M) (Q := Q) (S := Rt M (LB M Q B) t) hdR hdM
    rwa [hpiD] at h
  have hρ := rho_eq_one_of_semiT_eq_one D AM hgR hg
  have hmem : (⟨(g : Mbar M Q), hgR⟩ : ↥(bar M Q (Rt M (LB M Q B) t))) ∈
      (D.rho AM).ker := MonoidHom.mem_ker.mpr hρ
  rw [D.ker_rho AM] at hmem
  exact Subgroup.mem_subgroupOf.mp hmem

end CFSG.RankThree.GF2n.Stroth80
