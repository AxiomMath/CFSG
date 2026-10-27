module

public import CFSG.RankThree.GF2n.Stroth80.HeringSec63Step1
public import CFSG.RankThree.GF2n.Stroth80.HeringSec63Lom
public import CFSG.RankThree.GF2n.Stroth80.HeringSec63Bar
public import CFSG.RankThree.GF2n.Stroth80.HeringSec63Glue

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin QuadraticMap
open CFSG.RankThree.GF2n
open scoped commutatorElement Matrix

namespace HS6

section PhiG

variable {G : Type} [Group G] {M Q B : Subgroup G} {t : G} {ι : Type} [Fintype ι]
  [DecidableEq ι] {K : Type} [Field K]

@[expose] noncomputable def phiG (φ : ↥(Rt M (LB M Q B) t) →* GL ι K) (g : G) : GL ι K := by
  classical
  exact if h : g ∈ Rt M (LB M Q B) t then φ ⟨g, h⟩ else 1

theorem phiG_of_mem (φ : ↥(Rt M (LB M Q B) t) →* GL ι K) {g : G}
    (hg : g ∈ Rt M (LB M Q B) t) : phiG φ g = φ ⟨g, hg⟩ := by
  unfold phiG
  exact dif_pos hg

theorem phiG_mul (φ : ↥(Rt M (LB M Q B) t) →* GL ι K) {g h : G} (hg : g ∈ Rt M (LB M Q B) t)
    (hh : h ∈ Rt M (LB M Q B) t) : phiG φ (g * h) = phiG φ g * phiG φ h := by
  rw [phiG_of_mem φ ((Rt M (LB M Q B) t).mul_mem hg hh), phiG_of_mem φ hg, phiG_of_mem φ hh]
  exact map_mul φ ⟨g, hg⟩ ⟨h, hh⟩

theorem phiG_inv (φ : ↥(Rt M (LB M Q B) t) →* GL ι K) {g : G} (hg : g ∈ Rt M (LB M Q B) t) :
    phiG φ g⁻¹ = (phiG φ g)⁻¹ := by
  rw [phiG_of_mem φ ((Rt M (LB M Q B) t).inv_mem hg), phiG_of_mem φ hg]
  exact map_inv φ ⟨g, hg⟩

end PhiG

section Basic

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
  {hc : Ctx M Q Z B} {n : ℕ} {t : G} {m : ℕ} {X : Subgroup G}

theorem conj_Q_mem (hc : Ctx M Q Z B) : ∀ x ∈ Q, ∀ k ∈ M, k * x * k⁻¹ ∈ Q :=
  fun x hx k hk => (hc.conj_mem_Q_of_mem_M hk).1 x hx

theorem Env.CN_le_M (e : Env hc n t m X) : hc.CN t ≤ M := fun a ha =>
  hc.Rt_le_M t (Ctx.mem_CN.mp ha).1

theorem Env.X_le_M (e : Env hc n t m X) : X ≤ M := e.hXR.trans (hc.Rt_le_M t)

theorem Env.Q_le_conj_CN (e : Env hc n t m X) {h : G} (hh : h ∈ M) :
    Q ≤ conjSubgroup h (hc.CN t) := by
  intro x hx
  rw [mem_conjSubgroup]
  have := conj_Q_mem hc x hx h⁻¹ (M.inv_mem hh)
  rw [inv_inv] at this
  exact hc.Q_le_CN e.hs.toSec5.mem this

theorem Env.conj_CN_le_M (e : Env hc n t m X) {h : G} (hh : h ∈ M) :
    conjSubgroup h (hc.CN t) ≤ M := by
  intro y hy
  have hy' : h⁻¹ * y * h ∈ hc.CN t := mem_conjSubgroup.mp hy
  have : y = h * (h⁻¹ * y * h) * h⁻¹ := by group
  rw [this]
  exact M.mul_mem (M.mul_mem hh (e.CN_le_M hy')) (M.inv_mem hh)

end Basic

section Quot

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
  {hc : Ctx M Q Z B} {n : ℕ} {t : G} {m : ℕ} {X : Subgroup G}
  {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K] [Finite K] [CharP K 2]
  {Q' : QuadraticForm K (ι → K)} {X' : Subgroup (GL ι K)} {E : ElemMatrixIso Q' X'}
  {φ : ↥(Rt M (LB M Q B) t) →* GL ι K}
  [(Z.subgroupOf (Vt M (LB M Q B) B Z t)).Normal]
  {ψ : ↥(Vt M (LB M Q B) B Z t) ⧸ Z.subgroupOf (Vt M (LB M Q B) B Z t) ≃*
    Multiplicative (ι → K)} {P : HypPair Q'}

theorem OmegaModel.phiG_N (hmod : OmegaModel hc t Q' E φ ψ P.e) {a : G} (ha : a ∈ hc.CN t) :
    phiG φ a = 1 := by
  have haR : a ∈ Rt M (LB M Q B) t := (Ctx.mem_CN.mp ha).1
  rw [phiG_of_mem φ haR]
  have : (⟨a, haR⟩ : ↥(Rt M (LB M Q B) t)) ∈ φ.ker := by
    rw [hmod.ker]
    exact Subgroup.mem_subgroupOf.mpr ha
  exact this

theorem OmegaModel.mem_Q_of_phiG (e : Env hc n t m X) (hmod : OmegaModel hc t Q' E φ ψ P.e)
    {y : G} (hyX : y ∈ X) (hy : phiG φ y = 1) : y ∈ Q := by
  have hyR : y ∈ Rt M (LB M Q B) t := e.hXR hyX
  have h1 : (⟨y, hyR⟩ : ↥(Rt M (LB M Q B) t)) ∈ φ.ker := by
    rw [MonoidHom.mem_ker, ← phiG_of_mem φ hyR]
    exact hy
  rw [hmod.ker] at h1
  have h2 : y ∈ hc.CN t ⊓ X := ⟨Subgroup.mem_subgroupOf.mp h1, hyX⟩
  rwa [e.hNXQ] at h2

theorem OmegaModel.exists_mem_X (e : Env hc n t m X) (hmod : OmegaModel hc t Q' E φ ψ P.e)
    {g : GL ι K} (hg : g ∈ X') : ∃ x ∈ X, phiG φ x = g := by
  rw [← hmod.range] at hg
  obtain ⟨r, rfl⟩ := hg
  have hr : (r : G) ∈ X ⊔ hc.CN t := by rw [sup_comm, e.hNX]; exact r.2
  obtain ⟨x, hx, a, ha, hxa⟩ := exists_mul_of_mem_sup_of_le_normalizer e.X_le_normalizer_CN hr
  refine ⟨x, hx, ?_⟩
  have hxR : x ∈ Rt M (LB M Q B) t := e.hXR hx
  have haR : a ∈ Rt M (LB M Q B) t := (Ctx.mem_CN.mp ha).1
  have h1 : phiG φ (r : G) = φ r := phiG_of_mem φ r.2
  rw [← hxa, phiG_mul φ hxR haR, hmod.phiG_N ha, mul_one] at h1
  exact h1

theorem OmegaModel.mem_Q_of_phiG_eq (e : Env hc n t m X) (hmod : OmegaModel hc t Q' E φ ψ P.e)
    {y y' : G} (hy : y ∈ X) (hy' : y' ∈ X) (h : phiG φ y = phiG φ y') : y⁻¹ * y' ∈ Q := by
  refine hmod.mem_Q_of_phiG e (X.mul_mem (X.inv_mem hy) hy') ?_
  have hyR : y ∈ Rt M (LB M Q B) t := e.hXR hy
  have hy'R : y' ∈ Rt M (LB M Q B) t := e.hXR hy'
  rw [phiG_mul φ ((Rt M (LB M Q B) t).inv_mem hyR) hy'R, phiG_inv φ hyR, h, inv_mul_cancel]

theorem OmegaModel.exists_mem_LX (I : Inputs) (e : Env hc n t m X)
    (hmod : OmegaModel hc t Q' E φ ψ P.e) {w : ι → K} (hw : polar Q' P.e w = 0) :
    ∃ y ∈ LB M Q B, y ∈ X ∧ phiG φ y = lomMat E P.e w := by
  have h1 : lomMat E P.e w ∈ E.LomGL P.e := lomMat_mem_LomGL E hw
  rw [← hmod.hL] at h1
  obtain ⟨l, hl, hlφ⟩ := Subgroup.mem_map.mp h1
  have hlL : (l : G) ∈ LB M Q B := Subgroup.mem_subgroupOf.mp hl
  obtain ⟨y, hyX, hyL, a, ha, hla⟩ := e.LB_decomp I hlL
  refine ⟨y, hyL, hyX, ?_⟩
  have hyR : y ∈ Rt M (LB M Q B) t := e.hXR hyX
  have haR : a ∈ Rt M (LB M Q B) t := (Ctx.mem_CN.mp ha).1
  have h2 : phiG φ (l : G) = φ l := phiG_of_mem φ l.2
  rw [hla, phiG_mul φ hyR haR, hmod.phiG_N ha, mul_one] at h2
  rw [h2]
  exact hlφ

end Quot

section EpsDef

variable {G : Type} [Group G] (M Q : Subgroup G) [(Q.subgroupOf M).Normal] {ι : Type}
  [Fintype ι] [DecidableEq ι] {K : Type} [Field K]

@[expose] noncomputable def epsFun (L X : Subgroup G) (φG : G → GL ι K) (a : GL ι K) :
    ↥M ⧸ Q.subgroupOf M := by
  classical
  exact if h : ∃ y, y ∈ L ∧ y ∈ X ∧ φG y = a then piM M Q h.choose else 1

variable {M Q}

theorem epsFun_eq {L X : Subgroup G} {φG : G → GL ι K} {a : GL ι K} {y : G} (hyL : y ∈ L)
    (hyX : y ∈ X) (hy : φG y = a)
    (uniq : ∀ y₁ ∈ L, y₁ ∈ X → ∀ y₂ ∈ L, y₂ ∈ X → φG y₁ = φG y₂ → piM M Q y₁ = piM M Q y₂) :
    epsFun M Q L X φG a = piM M Q y := by
  have hex : ∃ y, y ∈ L ∧ y ∈ X ∧ φG y = a := ⟨y, hyL, hyX, hy⟩
  unfold epsFun
  rw [dif_pos hex]
  obtain ⟨h1, h2, h3⟩ := hex.choose_spec
  exact uniq _ h1 h2 y hyL hyX (h3.trans hy.symm)

end EpsDef

section Eps

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
  {hc : Ctx M Q Z B} {n : ℕ} {t : G} {m : ℕ} {X : Subgroup G}
  {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K] [Finite K] [CharP K 2]
  {Q' : QuadraticForm K (ι → K)} {X' : Subgroup (GL ι K)} {E : ElemMatrixIso Q' X'}
  {φ : ↥(Rt M (LB M Q B) t) →* GL ι K}
  [(Z.subgroupOf (Vt M (LB M Q B) B Z t)).Normal]
  {ψ : ↥(Vt M (LB M Q B) B Z t) ⧸ Z.subgroupOf (Vt M (LB M Q B) B Z t) ≃*
    Multiplicative (ι → K)} {P : HypPair Q'} [(Q.subgroupOf M).Normal]

theorem OmegaModel.piM_eq_of_phiG_eq (e : Env hc n t m X) (hmod : OmegaModel hc t Q' E φ ψ P.e)
    {y₁ y₂ : G} (h1L : y₁ ∈ LB M Q B) (h1X : y₁ ∈ X) (h2L : y₂ ∈ LB M Q B) (h2X : y₂ ∈ X)
    (h : phiG φ y₁ = phiG φ y₂) : piM M Q y₁ = piM M Q y₂ :=
  (piM_eq_iff (hc.LB_le_M h1L) (hc.LB_le_M h2L)).mpr (hmod.mem_Q_of_phiG_eq e h1X h2X h)

theorem OmegaModel.epsFun_lomHom (e : Env hc n t m X) (hmod : OmegaModel hc t Q' E φ ψ P.e)
    (w : Multiplicative ↥P.perp) {y : G} (hyL : y ∈ LB M Q B) (hyX : y ∈ X)
    (hy : phiG φ y = lomHom E P w) :
    epsFun M Q (LB M Q B) X (phiG φ) (lomHom E P w) = piM M Q y :=
  epsFun_eq hyL hyX hy fun y₁ h1L h1X y₂ h2L h2X h => hmod.piM_eq_of_phiG_eq e h1L h1X h2L h2X h

theorem OmegaModel.exists_lomHom (I : Inputs) (e : Env hc n t m X)
    (hmod : OmegaModel hc t Q' E φ ψ P.e) (w : Multiplicative ↥P.perp) :
    ∃ y ∈ LB M Q B, y ∈ X ∧ phiG φ y = lomHom E P w :=
  hmod.exists_mem_LX I e (HypPair.mem_perp.mp (Multiplicative.toAdd w).2).1

@[expose] noncomputable def epsHom (I : Inputs) (e : Env hc n t m X)
    (hmod : OmegaModel hc t Q' E φ ψ P.e) : Multiplicative ↥P.perp →* ↥M ⧸ Q.subgroupOf M :=
  MonoidHom.mk' (fun w => epsFun M Q (LB M Q B) X (phiG φ) (lomHom E P w)) (fun a b => by
    obtain ⟨ya, haL, haX, ha⟩ := hmod.exists_lomHom I e a
    obtain ⟨yb, hbL, hbX, hb⟩ := hmod.exists_lomHom I e b
    have haR : ya ∈ Rt M (LB M Q B) t := le_Rt (LB M Q B) e.hs.toSec5.mem haL
    have hbR : yb ∈ Rt M (LB M Q B) t := le_Rt (LB M Q B) e.hs.toSec5.mem hbL
    have hab : phiG φ (ya * yb) = lomHom E P (a * b) := by
      rw [phiG_mul φ haR hbR, ha, hb, map_mul]
    rw [hmod.epsFun_lomHom e (a * b) ((LB M Q B).mul_mem haL hbL) (X.mul_mem haX hbX) hab,
      hmod.epsFun_lomHom e a haL haX ha, hmod.epsFun_lomHom e b hbL hbX hb,
      piM_mul (hc.LB_le_M haL) (hc.LB_le_M hbL)])

theorem OmegaModel.epsHom_eq (I : Inputs) (e : Env hc n t m X)
    (hmod : OmegaModel hc t Q' E φ ψ P.e) (w : Multiplicative ↥P.perp) {y : G}
    (hyL : y ∈ LB M Q B) (hyX : y ∈ X) (hy : phiG φ y = lomHom E P w) :
    epsHom I e hmod w = piM M Q y :=
  hmod.epsFun_lomHom e w hyL hyX hy

end Eps

section EpsProps

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
  {hc : Ctx M Q Z B} {n : ℕ} {t : G} {m : ℕ} {X : Subgroup G}
  {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K] [Finite K] [CharP K 2]
  {Q' : QuadraticForm K (ι → K)} {X' : Subgroup (GL ι K)} {E : ElemMatrixIso Q' X'}
  {φ : ↥(Rt M (LB M Q B) t) →* GL ι K}
  [(Z.subgroupOf (Vt M (LB M Q B) B Z t)).Normal]
  {ψ : ↥(Vt M (LB M Q B) B Z t) ⧸ Z.subgroupOf (Vt M (LB M Q B) B Z t) ≃*
    Multiplicative (ι → K)} {P : HypPair Q'} [(Q.subgroupOf M).Normal]

theorem OmegaModel.epsHom_injective (I : Inputs) (e : Env hc n t m X) (hg : OmegaGeom Q' m)
    (hmod : OmegaModel hc t Q' E φ ψ P.e) : Function.Injective (epsHom I e hmod) := by
  rw [injective_iff_map_eq_one]
  intro w hw
  obtain ⟨y, hyL, hyX, hy⟩ := hmod.exists_lomHom I e w
  rw [hmod.epsHom_eq I e w hyL hyX hy, piM_eq_one_iff (hc.LB_le_M hyL)] at hw
  have h1 : phiG φ y = 1 := hmod.phiG_N (hc.Q_le_CN e.hs.toSec5.mem hw)
  rw [h1] at hy
  exact lomHom_injective E P hg.nondeg (hy.symm.trans (map_one _).symm)

theorem OmegaModel.piM_comm_epsHom (I : Inputs) (e : Env hc n t m X)
    (hmod : OmegaModel hc t Q' E φ ψ P.e) {a : G} (ha : a ∈ hc.CN t)
    (w : Multiplicative ↥P.perp) :
    piM M Q a * epsHom I e hmod w = epsHom I e hmod w * piM M Q a := by
  obtain ⟨y, hyL, hyX, hy⟩ := hmod.exists_lomHom I e w
  rw [hmod.epsHom_eq I e w hyL hyX hy]
  exact piM_comm_of_comm_mem (e.CN_le_M ha) (e.X_le_M hyX) (e.hcen a ha y hyX)

theorem OmegaModel.eq_one_of_piM_eq_epsHom (I : Inputs) (e : Env hc n t m X)
    (hmod : OmegaModel hc t Q' E φ ψ P.e) {a : G} (ha : a ∈ hc.CN t)
    (w : Multiplicative ↥P.perp) (h : piM M Q a = epsHom I e hmod w) : piM M Q a = 1 := by
  obtain ⟨y, hyL, hyX, hy⟩ := hmod.exists_lomHom I e w
  rw [hmod.epsHom_eq I e w hyL hyX hy] at h
  have h1 : a⁻¹ * y ∈ Q := (piM_eq_iff (e.CN_le_M ha) (hc.LB_le_M hyL)).mp h
  have hyN : y ∈ hc.CN t := by
    have : y = a * (a⁻¹ * y) := by group
    rw [this]
    exact (hc.CN t).mul_mem ha (hc.Q_le_CN e.hs.toSec5.mem h1)
  have hyQ : y ∈ Q := by
    have : y ∈ hc.CN t ⊓ X := ⟨hyN, hyX⟩
    rwa [e.hNXQ] at this
  rw [h]
  exact (piM_eq_one_iff (hc.LB_le_M hyL)).mpr hyQ

theorem OmegaModel.mem_LB_iff (I : Inputs) (e : Env hc n t m X) (hg : OmegaGeom Q' m)
    (hmod : OmegaModel hc t Q' E φ ψ P.e) (x : ↥M ⧸ Q.subgroupOf M) :
    x ∈ bar M Q (LB M Q B) ↔ ∃ a ∈ hc.CN t, ∃ w : Multiplicative ↥P.perp,
      x = piM M Q a * epsHom I e hmod w := by
  constructor
  · intro hx
    obtain ⟨l, hl, hlM, rfl⟩ := (mem_bar x).mp hx
    obtain ⟨y, hyX, hyL, a, ha, hla⟩ := e.LB_decomp I hl
    have hyR : y ∈ Rt M (LB M Q B) t := e.hXR hyX
    have hA : phiG φ y ∈ E.LomGL P.e := by
      rw [phiG_of_mem φ hyR, ← hmod.hL]
      exact Subgroup.mem_map_of_mem φ (Subgroup.mem_subgroupOf.mpr hyL)
    rw [← lomHom_range E P hg.nondeg] at hA
    obtain ⟨w, hw⟩ := hA
    refine ⟨a, ha, w, ?_⟩
    rw [hmod.epsHom_eq I e w hyL hyX hw.symm, hla, piM_mul (e.X_le_M hyX) (e.CN_le_M ha)]
    exact (piM_comm_of_comm_mem (e.CN_le_M ha) (e.X_le_M hyX) (e.hcen a ha y hyX)).symm
  · rintro ⟨a, ha, w, rfl⟩
    obtain ⟨y, hyL, hyX, hy⟩ := hmod.exists_lomHom I e w
    rw [hmod.epsHom_eq I e w hyL hyX hy, ← piM_mul (e.CN_le_M ha) (hc.LB_le_M hyL)]
    exact piM_mem_bar ((LB M Q B).mul_mem (e.N_le_LB I ha) hyL)
      (M.mul_mem (e.CN_le_M ha) (hc.LB_le_M hyL))

end EpsProps

section ConjAct

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
  {hc : Ctx M Q Z B} {n : ℕ} {t : G} {m : ℕ} {X : Subgroup G}
  {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K] [Finite K] [CharP K 2]
  {Q' : QuadraticForm K (ι → K)} {X' : Subgroup (GL ι K)} {E : ElemMatrixIso Q' X'}
  {φ : ↥(Rt M (LB M Q B) t) →* GL ι K}
  [(Z.subgroupOf (Vt M (LB M Q B) B Z t)).Normal]
  {ψ : ↥(Vt M (LB M Q B) B Z t) ⧸ Z.subgroupOf (Vt M (LB M Q B) B Z t) ≃*
    Multiplicative (ι → K)} {P : HypPair Q'} [(Q.subgroupOf M).Normal]

theorem OmegaModel.conj_LB_eq (I : Inputs) (e : Env hc n t m X)
    (hmod : OmegaModel hc t Q' E φ ψ P.e) {x : G}
    (hxR : x ∈ Rt M (LB M Q B) t) {d : K} (hd : d ≠ 0)
    (hge : ((phiG φ x : GL ι K) : Matrix ι ι K) *ᵥ P.e = d • P.e) :
    conjSubgroup x (LB M Q B) = LB M Q B := by
  have h1 := hmod.hLr ⟨x, hxR⟩
  rw [phiG_of_mem φ hxR] at hge
  rw [hge] at h1
  have h2 : E.LomGL (d • P.e) = E.LomGL P.e := by
    unfold ElemMatrixIso.LomGL
    rw [Lom_smul hd]
  rw [h2, ← hmod.hL] at h1
  have hle : conjSubgroup x (LB M Q B) ≤ LB M Q B := by
    intro y hy
    have hyL : x⁻¹ * y * x ∈ LB M Q B := mem_conjSubgroup.mp hy
    have hyR : y ∈ Rt M (LB M Q B) t := by
      have h3 : x * (x⁻¹ * y * x) * x⁻¹ ∈ Rt M (LB M Q B) t :=
        (Rt M (LB M Q B) t).mul_mem ((Rt M (LB M Q B) t).mul_mem hxR
          (le_Rt (LB M Q B) e.hs.toSec5.mem hyL)) ((Rt M (LB M Q B) t).inv_mem hxR)
      rwa [show x * (x⁻¹ * y * x) * x⁻¹ = y by group] at h3
    have hmem : φ ⟨y, hyR⟩ ∈ ((LB M Q B).subgroupOf (Rt M (LB M Q B) t)).map φ := by
      rw [← h1]
      exact Subgroup.mem_map_of_mem φ (Subgroup.mem_subgroupOf.mpr hy)
    obtain ⟨l, hl, hlφ⟩ := hmem
    have hker : l⁻¹ * ⟨y, hyR⟩ ∈ φ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hlφ, inv_mul_cancel]
    rw [hmod.ker] at hker
    have hlL : (l : G) ∈ LB M Q B := Subgroup.mem_subgroupOf.mp hl
    have hN : (l : G)⁻¹ * y ∈ hc.CN t := Subgroup.mem_subgroupOf.mp hker
    have : y = (l : G) * ((l : G)⁻¹ * y) := by group
    rw [this]
    exact (LB M Q B).mul_mem hlL (e.N_le_LB I hN)
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [card_conjSubgroup])

theorem OmegaModel.conj_epsHom (I : Inputs) (e : Env hc n t m X) (hg : OmegaGeom Q' m)
    (hmod : OmegaModel hc t Q' E φ ψ P.e) {x : G} (hxX : x ∈ X) {d : K} (hd : d ≠ 0)
    (hge : ((phiG φ x : GL ι K) : Matrix ι ι K) *ᵥ P.e = d • P.e) (w : ↥P.perp) :
    piM M Q x * epsHom I e hmod (Multiplicative.ofAdd w) * (piM M Q x)⁻¹ =
      epsHom I e hmod (Multiplicative.ofAdd
        ⟨P.proj (d • (((phiG φ x : GL ι K) : Matrix ι ι K) *ᵥ (w : ι → K))),
          P.proj_mem_perp _⟩) := by
  have hxR : x ∈ Rt M (LB M Q B) t := e.hXR hxX
  have hxM : x ∈ M := hc.Rt_le_M t hxR
  have hxL := hmod.conj_LB_eq I e hxR hd hge
  obtain ⟨y, hyL, hyX, hy⟩ := hmod.exists_lomHom I e (Multiplicative.ofAdd w)
  have hyR : y ∈ Rt M (LB M Q B) t := le_Rt (LB M Q B) e.hs.toSec5.mem hyL
  have hy' : x * y * x⁻¹ ∈ LB M Q B := by
    have : x * y * x⁻¹ ∈ conjSubgroup x (LB M Q B) :=
      mem_conjSubgroup.mpr (by rw [show x⁻¹ * (x * y * x⁻¹) * x = y by group]; exact hyL)
    rwa [hxL] at this
  have hg' : phiG φ x ∈ X' := by
    rw [phiG_of_mem φ hxR, ← hmod.range]
    exact ⟨_, rfl⟩
  have hconj : phiG φ (x * y * x⁻¹) = lomHom E P (Multiplicative.ofAdd
      ⟨P.proj (d • (((phiG φ x : GL ι K) : Matrix ι ι K) *ᵥ (w : ι → K))),
        P.proj_mem_perp _⟩) := by
    rw [phiG_mul φ ((Rt M (LB M Q B) t).mul_mem hxR hyR) ((Rt M (LB M Q B) t).inv_mem hxR),
      phiG_mul φ hxR hyR, phiG_inv φ hxR, hy, lomHom_apply]
    exact lomMat_conj_perp E P hg' hd hge w.2
  rw [hmod.epsHom_eq I e _ hy' (X.mul_mem (X.mul_mem hxX hyX) (X.inv_mem hxX)) hconj,
    hmod.epsHom_eq I e _ hyL hyX hy, piM_conj hxM (hc.LB_le_M hyL)]

end ConjAct

section Glue

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
  {hc : Ctx M Q Z B} {n : ℕ} {t : G} {m : ℕ} {X : Subgroup G}
  {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K] [Finite K] [CharP K 2]
  {Q' : QuadraticForm K (ι → K)} {X' : Subgroup (GL ι K)} {E : ElemMatrixIso Q' X'}
  {φ : ↥(Rt M (LB M Q B) t) →* GL ι K}
  [(Z.subgroupOf (Vt M (LB M Q B) B Z t)).Normal]
  {ψ : ↥(Vt M (LB M Q B) B Z t) ⧸ Z.subgroupOf (Vt M (LB M Q B) B Z t) ≃*
    Multiplicative (ι → K)} {P : HypPair Q'} [(Q.subgroupOf M).Normal]

theorem OmegaModel.glue_lineOf (I : Inputs) (e : Env hc n t m X) (hg : OmegaGeom Q' m)
    (hmod : OmegaModel hc t Q' E φ ψ P.e) {h : G} (hhM : h ∈ M)
    (hhL : conjSubgroup h (LB M Q B) = LB M Q B) (hne : conjSubgroup h (hc.CN t) ≠ hc.CN t) :
    ∃ w₀ : ↥P.perp, Q'.restrict P.perp w₀ = 0 ∧ w₀ ≠ 0 ∧
      conjSubgroup (piM M Q h) (bar M Q (hc.CN t)) ≤
        bar M Q (hc.CN t) ⊔ (lineGrp K w₀).map (epsHom I e hmod) := by
  have hQM : Q ≤ M := hc.hyp.Q_normal.1
  obtain ⟨s₀, hs₀, hs₀N⟩ := exists_mem_conj_not_mem hne
  obtain ⟨hs₀R, w, hw, hwu, hwA, hV⟩ := e.step1a I hmod hhM hhL hs₀ hs₀N
  obtain ⟨hQw, -, -⟩ := e.step2 I hg hmod hhM hhL hne hw hwu hV
  have hdec : w = polar Q' w P.f • P.e + P.proj w := by
    have h1 := P.eq_add_proj w
    have h2 : polar Q' w P.e = 0 := by rw [polar_comm]; exact hw
    rw [h2, zero_smul, add_zero] at h1
    exact h1
  let w₀ : ↥P.perp := ⟨P.proj w, P.proj_mem_perp w⟩
  have hQ₀ : Q'.restrict P.perp w₀ = 0 := by
    show Q' (P.proj w) = 0
    have h1 : P.proj w = w + (-polar Q' w P.f) • P.e := by
      rw [neg_smul, ← sub_eq_add_neg]
      exact eq_sub_of_add_eq' hdec.symm
    rw [h1, QuadraticMap.map_add Q', map_smul_eq_sq, P.Q_e, polar_smul_right_eq,
      polar_comm Q' w P.e, hw, hQw]
    ring
  have hw₀ne : w₀ ≠ 0 := by
    intro h0
    have h1 : P.proj w = 0 := congrArg Subtype.val h0
    rw [h1, add_zero] at hdec
    exact hwu _ hdec
  refine ⟨w₀, hQ₀, hw₀ne, ?_⟩
  intro z hz
  rw [conj_bar hQM hhM] at hz
  obtain ⟨s, hsN', hsM, rfl⟩ := (mem_bar z).mp hz
  by_cases hsN : s ∈ hc.CN t
  · exact Subgroup.mem_sup_left (piM_mem_bar hsN hsM)
  · obtain ⟨hsR, w', hw', hwu', hwA', hV'⟩ := e.step1a I hmod hhM hhL hsN' hsN
    have hfix : ∀ x, eichler Q' P.e w x = x ↔ eichler Q' P.e w' x = x := by
      intro x
      obtain ⟨v, rfl⟩ := exists_secVec_eq ψ x
      rw [eichler_fix_iff hmod.Qu hw hmod.u0 hwu, eichler_fix_iff hmod.Qu hw' hmod.u0 hwu',
        ← hV v, ← hV' v]
    obtain ⟨c, hc0, hceq⟩ := exists_smul_of_fix_eq hg.nondeg hmod.Qu hmod.u0 hw hw' hwu hwu' hfix
    have hE : eichler Q' P.e w' = eichler Q' P.e (c • P.proj w) := by
      rw [hceq]
      conv_lhs => rw [hdec, smul_add, smul_smul, add_comm]
      exact eichler_add_smul_self P.Q_e _ _
    have hsL : s ∈ LB M Q B := e.conj_CN_le_LB I hhL hsN'
    obtain ⟨y, hyX, hyL, a, ha, hsya⟩ := e.LB_decomp I hsL
    have hyR : y ∈ Rt M (LB M Q B) t := e.hXR hyX
    have haR : a ∈ Rt M (LB M Q B) t := (Ctx.mem_CN.mp ha).1
    have hphi : phiG φ y = lomHom E P (Multiplicative.ofAdd (c • w₀)) := by
      have h1 : phiG φ s = phiG φ y := by
        rw [hsya, phiG_mul φ hyR haR, hmod.phiG_N ha, mul_one]
      rw [← h1, phiG_of_mem φ hsR]
      apply Units.ext
      apply Matrix.ext_iff_mulVec.mpr
      intro x
      rw [hwA' x, hE, lomHom_apply]
      exact (lomMat_mulVec E P.e (c • P.proj w) x).symm
    rw [hsya, piM_mul (e.X_le_M hyX) (e.CN_le_M ha),
      hmod.epsHom_eq I e _ hyL hyX hphi |>.symm]
    rw [sup_comm]
    exact Subgroup.mul_mem_sup ⟨Multiplicative.ofAdd (c • w₀), ofAdd_smul_mem_lineGrp w₀ c, rfl⟩
      (piM_mem_bar ha (e.CN_le_M ha))

theorem OmegaModel.glue_elt (I : Inputs) (e : Env hc n t m X) (hmod : OmegaModel hc t Q' E φ ψ P.e)
    {x : G} (hxX : x ∈ X) {d : K} (hd : d ≠ 0)
    (hge : ((phiG φ x : GL ι K) : Matrix ι ι K) *ᵥ P.e = d • P.e) :
    piM M Q x ∈ Subgroup.normalizer ((bar M Q (LB M Q B) : Subgroup _) : Set _) ∧
      ∀ a ∈ hc.CN t, piM M Q x * piM M Q a * (piM M Q x)⁻¹ = piM M Q a := by
  have hQM : Q ≤ M := hc.hyp.Q_normal.1
  refine ⟨piM_mem_normalizer hQM (e.X_le_M hxX) (hmod.conj_LB_eq I e (e.hXR hxX) hd hge),
    fun a ha => ?_⟩
  exact mul_inv_eq_iff_eq_mul.mpr
    (piM_comm_of_comm_mem (e.CN_le_M ha) (e.X_le_M hxX) (e.hcen a ha x hxX)).symm

theorem OmegaModel.glue_trans (I : Inputs) (e : Env hc n t m X) (hg : OmegaGeom Q' m)
    (hmod : OmegaModel hc t Q' E φ ψ P.e) (hmin : IsMinus (Q'.restrict P.perp) 2)
    {w w' : ↥P.perp} (hw : Q'.restrict P.perp w = 0) (hw0 : w ≠ 0)
    (hw' : Q'.restrict P.perp w' = 0) (hw0' : w' ≠ 0) :
    ∃ ĥ ∈ Subgroup.normalizer ((bar M Q (LB M Q B) : Subgroup _) : Set _),
      (∀ a ∈ hc.CN t, ĥ * piM M Q a * ĥ⁻¹ = piM M Q a) ∧
      conjSubgroup ĥ ((lineGrp K w).map (epsHom I e hmod)) =
        (lineGrp K w').map (epsHom I e hmod) := by
  obtain ⟨g, hgX', hge, c, hc0, hproj⟩ := exists_g_trans E P hmin hw hw0 hw' hw0'
  obtain ⟨x, hxX, hxg⟩ := hmod.exists_mem_X e hgX'
  have hge' : ((phiG φ x : GL ι K) : Matrix ι ι K) *ᵥ P.e = (1 : K) • P.e := by
    rw [hxg, one_smul]
    exact hge
  obtain ⟨hnorm, hfix⟩ := hmod.glue_elt I e hxX one_ne_zero hge'
  refine ⟨piM M Q x, hnorm, hfix, ?_⟩
  have hεinj := hmod.epsHom_injective I e hg
  have hle : conjSubgroup (piM M Q x) ((lineGrp K w).map (epsHom I e hmod)) ≤
      (lineGrp K w').map (epsHom I e hmod) := by
    intro z hz
    rw [mem_conjSubgroup] at hz
    obtain ⟨v, ⟨a, ha⟩, hv⟩ := hz
    have hv' : v = Multiplicative.ofAdd (a • w) := Multiplicative.toAdd.injective ha
    have hz' : z = piM M Q x * epsHom I e hmod v * (piM M Q x)⁻¹ := by
      rw [hv]
      group
    have key := hmod.conj_epsHom I e hg hxX one_ne_zero hge' (a • w)
    rw [hxg] at key
    have hvec : P.proj ((1 : K) • (((g : GL ι K) : Matrix ι ι K) *ᵥ
        ((a • w : ↥P.perp) : ι → K))) = (a * c) • (w' : ι → K) := by
      rw [one_smul, Submodule.coe_smul, Matrix.mulVec_smul, proj_smul, hproj, smul_smul]
    have hval : (⟨P.proj ((1 : K) • (((g : GL ι K) : Matrix ι ι K) *ᵥ
        ((a • w : ↥P.perp) : ι → K))), P.proj_mem_perp _⟩ : ↥P.perp) = (a * c) • w' :=
      Subtype.ext (hvec.trans (Submodule.coe_smul _ _).symm)
    rw [hz', hv', key, hval]
    exact ⟨Multiplicative.ofAdd ((a * c) • w'), ofAdd_smul_mem_lineGrp w' (a * c), rfl⟩
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [card_conjSubgroup, Subgroup.card_map_of_injective hεinj,
    Subgroup.card_map_of_injective hεinj, card_lineGrp hw0, card_lineGrp hw0']

theorem OmegaModel.glue_torus (I : Inputs) (e : Env hc n t m X) (hg : OmegaGeom Q' m)
    (hmod : OmegaModel hc t Q' E φ ψ P.e) (hmin : IsMinus (Q'.restrict P.perp) 2)
    {w : ↥P.perp} (hw : Q'.restrict P.perp w = 0) (hw0 : w ≠ 0) {c : K} (hc0 : c ≠ 0) :
    ∃ ĥ ∈ Subgroup.normalizer ((bar M Q (LB M Q B) : Subgroup _) : Set _),
      (∀ a ∈ hc.CN t, ĥ * piM M Q a * ĥ⁻¹ = piM M Q a) ∧
      ∀ a : K, ĥ * epsHom I e hmod (Multiplicative.ofAdd (a • w)) * ĥ⁻¹ =
        epsHom I e hmod (Multiplicative.ofAdd ((c * a) • w)) := by
  obtain ⟨g, hgX', d, hd, hge, hproj⟩ := exists_g_torus E P hmin hw hw0 hc0
  obtain ⟨x, hxX, hxg⟩ := hmod.exists_mem_X e hgX'
  have hge' : ((phiG φ x : GL ι K) : Matrix ι ι K) *ᵥ P.e = d • P.e := by
    rw [hxg]
    exact hge
  obtain ⟨hnorm, hfix⟩ := hmod.glue_elt I e hxX hd hge'
  refine ⟨piM M Q x, hnorm, hfix, fun a => ?_⟩
  have key := hmod.conj_epsHom I e hg hxX hd hge' (a • w)
  rw [hxg] at key
  have hvec : P.proj (d • (((g : GL ι K) : Matrix ι ι K) *ᵥ ((a • w : ↥P.perp) : ι → K))) =
      (c * a) • (w : ι → K) := by
    rw [Submodule.coe_smul, Matrix.mulVec_smul, smul_comm d a, proj_smul, hproj, smul_smul,
      mul_comm a c]
  have hval : (⟨P.proj (d • (((g : GL ι K) : Matrix ι ι K) *ᵥ ((a • w : ↥P.perp) : ι → K))),
      P.proj_mem_perp _⟩ : ↥P.perp) = (c * a) • w :=
    Subtype.ext (hvec.trans (Submodule.coe_smul _ _).symm)
  rw [key, hval]

end Glue

section Final

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
  {hc : Ctx M Q Z B} {n : ℕ} {t : G} {m : ℕ} {X : Subgroup G}

theorem Env.conj_CN_eq (I : Inputs) (e : Env hc n t m X) {h : G} (hhM : h ∈ M)
    (hhL : conjSubgroup h (LB M Q B) = LB M Q B) : conjSubgroup h (hc.CN t) = hc.CN t := by
  by_contra hne
  haveI hQn : (Q.subgroupOf M).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer hc.hyp.Q_normal.2
  have hQM : Q ≤ M := hc.hyp.Q_normal.1
  obtain ⟨ι, _, _, K, _, _, _, Q', X', E, φ, _, ψ, u, hK, hg, hmod⟩ := e.exists_model I
  obtain ⟨s, hs, hsN⟩ := exists_mem_conj_not_mem hne
  obtain ⟨hsR, w, hw, hwu, hwA, hV⟩ := e.step1a I hmod hhM hhL hs hsN
  obtain ⟨-, -, hmin3⟩ := e.step2 I hg hmod hhM hhL hne hw hwu hV
  obtain ⟨P, rfl⟩ := exists_hypPair hg.nondeg hmod.Qu hmod.u0
  have hmin : IsMinus (Q'.restrict P.perp) 2 := hmin3.perp P
  obtain ⟨e', -, he', -⟩ := hc.hyp.cp
  have hq : Nat.card K = 2 ^ e' := hK.trans he'
  have hs2 : 2 ≤ e' := by
    by_contra hlt
    have h1 : 2 ^ e' ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h2 := hc.hyp.q4
    omega
  have hlift : ∀ ĥ ∈ Subgroup.normalizer ((bar M Q (LB M Q B) : Subgroup _) : Set _),
      conjSubgroup ĥ (bar M Q (hc.CN t)) ≠ bar M Q (hc.CN t) →
      ∃ h' ∈ M, piM M Q h' = ĥ ∧ conjSubgroup h' (LB M Q B) = LB M Q B ∧
        conjSubgroup h' (hc.CN t) ≠ hc.CN t := by
    intro ĥ hĥ hne'
    obtain ⟨h', hh'M, rfl, hh'L⟩ :=
      exists_lift_normalizer hQM (conj_Q_mem hc) sec39_Q_le_LB hc.LB_le_M hĥ
    refine ⟨h', hh'M, rfl, hh'L, fun heq => hne' ?_⟩
    rw [conj_bar hQM hh'M, heq]
  refine pencil_glue_false' hs2 hq hmin (bar M Q (hc.CN t)) ?comm ?sq ?card
    (epsHom I e hmod) (hmod.epsHom_injective I e hg) ?hcomm ?hdisj (bar M Q (LB M Q B))
    (Subgroup.normalizer ((bar M Q (LB M Q B) : Subgroup _) : Set _)) ?hA ?hHA ?hTI ?hline ?htrans
    ?htorus ?hnon
  case comm =>
    intro x hx y hy
    obtain ⟨a, ha, haM, rfl⟩ := (mem_bar x).mp hx
    obtain ⟨b, hb, hbM, rfl⟩ := (mem_bar y).mp hy
    exact piM_comm_of_comm_mem haM hbM ((e.N_mod_Q I.h34).1 a ha b hb)
  case sq =>
    intro x hx
    obtain ⟨a, ha, haM, rfl⟩ := (mem_bar x).mp hx
    rw [← piM_mul haM haM, piM_eq_one_iff (M.mul_mem haM haM)]
    have := (e.N_mod_Q I.h34).2 a ha
    rwa [pow_two] at this
  case card =>
    have h1 := card_bar_mul (hc.Q_le_CN e.hs.toSec5.mem) e.CN_le_M
    have h2 := e.hs.cardN
    have hQpos : 0 < Nat.card Q := Nat.card_pos
    rw [hK]
    apply Nat.eq_of_mul_eq_mul_right hQpos
    rw [h1, h2, mul_comm]
  case hcomm =>
    intro x hx w
    obtain ⟨a, ha, haM, rfl⟩ := (mem_bar x).mp hx
    exact hmod.piM_comm_epsHom I e ha w
  case hdisj =>
    intro x hx w hxw
    obtain ⟨a, ha, haM, rfl⟩ := (mem_bar x).mp hx
    exact hmod.eq_one_of_piM_eq_epsHom I e ha w hxw
  case hA =>
    intro x
    rw [hmod.mem_LB_iff I e hg x]
    constructor
    · rintro ⟨a, ha, w, rfl⟩
      exact ⟨piM M Q a, piM_mem_bar ha (e.CN_le_M ha), w, rfl⟩
    · rintro ⟨y, hy, w, rfl⟩
      obtain ⟨a, ha, haM, rfl⟩ := (mem_bar y).mp hy
      exact ⟨a, ha, w, rfl⟩
  case hHA =>
    intro h' hh' x hx
    exact ((Subgroup.mem_normalizer_iff.mp hh') x).mp hx
  case hTI =>
    intro ĥ hĥ hne'
    obtain ⟨h', hh'M, rfl, hh'L, hne''⟩ := hlift ĥ hĥ hne'
    rw [conj_bar hQM hh'M, ← bar_inf (hc.Q_le_CN e.hs.toSec5.mem) (e.Q_le_conj_CN hh'M)]
    exact bar_eq_bot_of_le (e.step1c I hg hmod hh'M hh'L hne'') (inf_le_left.trans e.CN_le_M)
  case hline =>
    intro ĥ hĥ hne'
    obtain ⟨h', hh'M, rfl, hh'L, hne''⟩ := hlift ĥ hĥ hne'
    exact hmod.glue_lineOf I e hg hh'M hh'L hne''
  case htrans =>
    intro w w' hw hw0 hw' hw0'
    obtain ⟨ĥ, hĥ, hfix, hl⟩ := hmod.glue_trans I e hg hmin hw hw0 hw' hw0'
    refine ⟨ĥ, hĥ, fun x hx => ?_, hl⟩
    obtain ⟨a, ha, haM, rfl⟩ := (mem_bar x).mp hx
    exact hfix a ha
  case htorus =>
    intro w hw hw0 c hc0
    obtain ⟨ĥ, hĥ, hfix, hact⟩ := hmod.glue_torus I e hg hmin hw hw0 hc0
    refine ⟨ĥ, hĥ, fun x hx => ?_, hact⟩
    obtain ⟨a, ha, haM, rfl⟩ := (mem_bar x).mp hx
    exact hfix a ha
  case hnon =>
    refine ⟨piM M Q h, piM_mem_normalizer hQM hhM hhL, fun heq => hne ?_⟩
    rw [conj_bar hQM hhM] at heq
    exact bar_injective (e.Q_le_conj_CN hhM) (hc.Q_le_CN e.hs.toSec5.mem) (e.conj_CN_le_M hhM)
      e.CN_le_M heq

end Final

end HS6

end CFSG.RankThree.GF2n.Stroth80
