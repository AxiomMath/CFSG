module

public import CFSG.RankThree.GF2n.Stroth80.HeringSec63Model
public import CFSG.RankThree.GF2n.Stroth80.Sec8StepsConj
public import CFSG.RankThree.GF2n.Stroth80.HeringSec63Geom
public import CFSG.RankThree.GF2n.Stroth80.HeringSec63Step0
public import CFSG.RankThree.GF2n.Stroth80.Sec311Conj
public import CFSG.RankThree.GF2n.Stroth80.Sec7RootLemma

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin QuadraticMap
open scoped commutatorElement Matrix

namespace HS6

section Step1

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
  {hc : Ctx M Q Z B} {n : ℕ} {t : G} {m : ℕ} {X : Subgroup G}

theorem Env.conj_CN_le_LB (I : Inputs) (e : Env hc n t m X) {h : G}
    (hhL : conjSubgroup h (LB M Q B) = LB M Q B) : conjSubgroup h (hc.CN t) ≤ LB M Q B :=
  (Subgroup.map_mono (e.N_le_LB I)).trans hhL.le

theorem exists_mem_conj_not_mem {N : Subgroup G} {h : G} (hne : conjSubgroup h N ≠ N) :
    ∃ s ∈ conjSubgroup h N, s ∉ N := by
  by_contra hcon
  push Not at hcon
  exact hne (Subgroup.eq_of_le_of_card_ge hcon (by rw [card_conjSubgroup]))

theorem Env.Q1_conj_eq (I : Inputs) (e : Env hc n t m X) {h : G} (hhM : h ∈ M) {s : G}
    (hs : s ∈ conjSubgroup h (hc.CN t)) (hsQ : s ∉ Q) :
    Q1 hc s = conjSubgroup h (Vt M (LB M Q B) B Z t) := by
  have ha' : h⁻¹ * s * h ∈ hc.CN t := mem_conjSubgroup.mp hs
  have haM' : h⁻¹ * s * h ∈ M := hc.Rt_le_M t (Ctx.mem_CN.mp ha').1
  have haQ' : h⁻¹ * s * h ∉ Q := by
    intro hq
    apply hsQ
    have := (hc.conj_mem_Q_of_mem_M hhM).1 _ hq
    rwa [show h * (h⁻¹ * s * h) * h⁻¹ = s by group] at this
  have hh : Q1 hc (h * (h⁻¹ * s * h) * h⁻¹) = conjSubgroup h (Q1 hc (h⁻¹ * s * h)) :=
    Q1_conj hc hhM haM'
  rw [show h * (h⁻¹ * s * h) * h⁻¹ = s by group] at hh
  rw [hh, e.Q1_eq_V I ha' haQ']

theorem Env.V_eq_conj_of_mem {I : Inputs} (e : Env hc n t m X) {h : G} (hhM : h ∈ M) {a : G}
    (haN : a ∈ hc.CN t) (haNh : a ∈ conjSubgroup h (hc.CN t)) (haQ : a ∉ Q) :
    Vt M (LB M Q B) B Z t = conjSubgroup h (Vt M (LB M Q B) B Z t) := by
  exact (e.Q1_eq_V I haN haQ).symm.trans (e.Q1_conj_eq I hhM haNh haQ)

theorem Env.CN_le_conj_LB (I : Inputs) (e : Env hc n t m X) {ρ : G}
    (hρ : ρ ∈ Rt M (LB M Q B) t) : hc.CN t ≤ conjSubgroup ρ (LB M Q B) := by
  intro a ha
  rw [mem_conjSubgroup]
  have := hc.CN_conj_mem e.hs.toSec5.mem ((Rt M (LB M Q B) t).inv_mem hρ) ha
  rw [inv_inv] at this
  exact e.N_le_LB I this

theorem Env.conj_CN_eq_of_Rt (I : Inputs) (e : Env hc n t m X) {h : G} (hhM : h ∈ M)
    (hhL : conjSubgroup h (LB M Q B) = LB M Q B)
    (hR : conjSubgroup h (Rt M (LB M Q B) t) = Rt M (LB M Q B) t) :
    conjSubgroup h (hc.CN t) = hc.CN t := by
  have ht' : h * t * h⁻¹ ∈ LB M Q B := by
    have h1 : h * t * h⁻¹ ∈ conjSubgroup h (LB M Q B) :=
      mem_conjSubgroup.mpr (by
        rw [show h⁻¹ * (h * t * h⁻¹) * h = t by group]
        exact e.hs.toSec5.mem)
    rwa [hhL] at h1
  have ht'Q : h * t * h⁻¹ ∉ Q := by
    intro hq
    apply e.hs.toSec5.notQ
    have := (hc.conj_mem_Q_of_mem_M (M.inv_mem hhM)).1 _ hq
    rwa [show h⁻¹ * (h * t * h⁻¹) * h⁻¹⁻¹ = t by group] at this
  have hN' : Nt M (LB M Q B) (h * t * h⁻¹) = hc.CN (h * t * h⁻¹) :=
    I.hNt G M Q Z B hc n e.hs.toSec5.width e.hs.toSec5.n_gt e.hs.toSec5.noA2 e.hs.toSec5.gen _
      ht' ht'Q
  rw [← Ctx.CN_conjM hc hhM t, ← hN', ← e.Nt_eq I]
  show inSubgroup (pCore 2) (Rt M (LB M Q B) (h * t * h⁻¹)) =
    inSubgroup (pCore 2) (Rt M (LB M Q B) t)
  rw [← conjSubgroup_Rt_eq hhM t, hR]

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K] [Finite K] [CharP K 2]
  {Q' : QuadraticForm K (ι → K)} {X' : Subgroup (GL ι K)} {E : ElemMatrixIso Q' X'}
  {φ : ↥(Rt M (LB M Q B) t) →* GL ι K}
  [(Z.subgroupOf (Vt M (LB M Q B) B Z t)).Normal]
  {ψ : ↥(Vt M (LB M Q B) B Z t) ⧸ Z.subgroupOf (Vt M (LB M Q B) B Z t) ≃*
    Multiplicative (ι → K)} {u : ι → K}

theorem Env.step1a (I : Inputs) (e : Env hc n t m X) (hmod : OmegaModel hc t Q' E φ ψ u)
    {h : G} (hhM : h ∈ M) (hhL : conjSubgroup h (LB M Q B) = LB M Q B) {s : G}
    (hs : s ∈ conjSubgroup h (hc.CN t)) (hsN : s ∉ hc.CN t) :
    ∃ (hsR : s ∈ Rt M (LB M Q B) t) (w : ι → K), polar Q' u w = 0 ∧ (∀ c : K, w ≠ c • u) ∧
      (∀ y : ι → K, (φ ⟨s, hsR⟩ : Matrix ι ι K) *ᵥ y = eichler Q' u w y) ∧
      ∀ v : ↥(Vt M (LB M Q B) B Z t), (v : G) ∈ conjSubgroup h (Vt M (LB M Q B) B Z t) ↔
        (polar Q' (secVec ψ v) u = 0 ∧ polar Q' (secVec ψ v) w = 0) := by
  have ht : t ∈ LB M Q B := e.hs.toSec5.mem
  have hsL : s ∈ LB M Q B := e.conj_CN_le_LB I hhL hs
  have hsR : s ∈ Rt M (LB M Q B) t := le_Rt (LB M Q B) ht hsL
  have hsM : s ∈ M := hc.Rt_le_M t hsR
  have hAmem : φ ⟨s, hsR⟩ ∈ E.LomGL u := by
    rw [← hmod.hL]
    exact Subgroup.mem_map_of_mem φ (Subgroup.mem_subgroupOf.mpr hsL)
  obtain ⟨w, hw, hwA⟩ := eichler_of_mem_LomGL E hAmem
  have hwu : ∀ c : K, w ≠ c • u := by
    intro c hcw
    apply hsN
    have h1 : eichler Q' u w = 1 := eichler_eq_one_of_smul hmod.Qu hcw
    have hker : (⟨s, hsR⟩ : ↥(Rt M (LB M Q B) t)) ∈ φ.ker := by
      rw [MonoidHom.mem_ker]
      apply Units.ext
      rw [Units.val_one]
      apply Matrix.ext_iff_mulVec.mpr
      intro x
      rw [Matrix.one_mulVec, hwA x, h1]
      rfl
    rw [hmod.ker] at hker
    exact Subgroup.mem_subgroupOf.mp hker
  have hsQ : s ∉ Q := fun hq => hsN (hc.Q_le_CN e.hs.toSec5.mem hq)
  have hQ1 := e.Q1_conj_eq I hhM hs hsQ
  have hVR := hc.Rt_normalizes_Vt ht
  refine ⟨hsR, w, hw, hwu, hwA, fun v => ?_⟩
  have hcomm := secVec_comm φ ψ hmod.equi hVR ⟨s, hsR⟩ v
  have key : ⁅s, (v : G)⁆ ∈ Z ↔ polar Q' (secVec ψ v) u = 0 ∧ polar Q' (secVec ψ v) w = 0 := by
    have h1 := secVec_eq_zero_iff ψ ⟨⁅s, (v : G)⁆, comm_mem_of_le_normalizer hVR ⟨s, hsR⟩ v⟩
    refine h1.symm.trans ?_
    rw [hcomm, sub_eq_zero]
    have h2 : (φ ⟨s, hsR⟩ : Matrix ι ι K) *ᵥ secVec ψ v = eichler Q' u w (secVec ψ v) := hwA _
    rw [h2]
    exact eichler_fix_iff hmod.Qu hw hmod.u0 hwu _
  rw [← hQ1, hc.mem_Q1_iff hsM]
  exact ⟨fun hh => key.mp hh.2, fun hh => ⟨hc.Vt_le_Q t v.2, key.mpr hh⟩⟩

theorem Env.exists_conj_LB_le (I : Inputs) (e : Env hc n t m X) (hg : OmegaGeom Q' m)
    (hmod : OmegaModel hc t Q' E φ ψ u) {h : G} (hhM : h ∈ M)
    (hhL : conjSubgroup h (LB M Q B) = LB M Q B) {w : ι → K}
    (hV : ∀ v : ↥(Vt M (LB M Q B) B Z t), (v : G) ∈ conjSubgroup h (Vt M (LB M Q B) B Z t) ↔
      (polar Q' (secVec ψ v) u = 0 ∧ polar Q' (secVec ψ v) w = 0))
    {x : ι → K} (hQx : Q' x = 0) (hx0 : x ≠ 0) (hxu : polar Q' x u = 0)
    (hxw : polar Q' x w = 0) :
    ∃ ρ : ↥(Rt M (LB M Q B) t),
      conjSubgroup (ρ : G) (LB M Q B) ≤ conjSubgroup h (Rt M (LB M Q B) t) ∧
      ((conjSubgroup (ρ : G) (LB M Q B)).subgroupOf (Rt M (LB M Q B) t)).map φ = E.LomGL x := by
  have ht : t ∈ LB M Q B := e.hs.toSec5.mem
  obtain ⟨P, P', hP⟩ := hg.two
  obtain ⟨A, hAX, hAu⟩ := E.exists_mulVec_eq hg.nondeg hP hmod.u0 hx0 (by rw [hmod.Qu, hQx])
  obtain ⟨ρ, hρ⟩ := exists_mulVec_eq_of_range φ hmod.range ⟨A, hAX, hAu⟩
  have hρM : (ρ : G) ∈ M := hc.Rt_le_M t ρ.2
  have hVR := hc.Rt_normalizes_Vt ht
  have hBV : B ≤ Vt M (LB M Q B) B Z t := hc.B_le_Vt ht
  have hhρ : h⁻¹ * (ρ : G) ∈ M := M.mul_mem (M.inv_mem hhM) hρM
  have hle : conjSubgroup (h⁻¹ * (ρ : G)) B ⊔ Z ≤ Vt M (LB M Q B) B Z t := by
    refine sup_le (fun y hy => ?_) sec39_Z_le_Vt
    rw [mem_conjSubgroup] at hy
    have hbB : (h⁻¹ * (ρ : G))⁻¹ * y * (h⁻¹ * (ρ : G)) ∈ B := hy
    set b := (h⁻¹ * (ρ : G))⁻¹ * y * (h⁻¹ * (ρ : G)) with hb
    have hbV : b ∈ Vt M (LB M Q B) B Z t := hBV hbB
    have hy_eq : y = h⁻¹ * ((ρ : G) * b * (ρ : G)⁻¹) * h := by rw [hb]; group
    have hb'V : (ρ : G) * b * (ρ : G)⁻¹ ∈ Vt M (LB M Q B) B Z t :=
      (Subgroup.mem_normalizer_iff.mp (hVR ρ.2) b).mp hbV
    obtain ⟨c, hcb⟩ := (hmod.hB (secVec ψ ⟨b, hbV⟩)).mp ⟨⟨b, hbV⟩, hbB, rfl⟩
    have hvec : secVec ψ ⟨(ρ : G) * b * (ρ : G)⁻¹, hb'V⟩ = c • x := by
      have h1 := hmod.equi ρ ⟨b, hbV⟩ ⟨(ρ : G) * b * (ρ : G)⁻¹, hb'V⟩ rfl
      change secVec ψ ⟨(ρ : G) * b * (ρ : G)⁻¹, hb'V⟩ =
        (φ ρ : Matrix ι ι K) *ᵥ secVec ψ ⟨b, hbV⟩ at h1
      rw [h1, hcb, Matrix.mulVec_smul, hρ]
    have hb'h : (ρ : G) * b * (ρ : G)⁻¹ ∈ conjSubgroup h (Vt M (LB M Q B) B Z t) :=
      (hV ⟨_, hb'V⟩).mpr (by
        rw [hvec, polar_smul_left_eq, polar_smul_left_eq, hxu, hxw]
        simp)
    rw [hy_eq]
    exact mem_conjSubgroup.mp hb'h
  obtain ⟨r, hrR, hr⟩ := e.conj_orbit I (h⁻¹ * (ρ : G)) hhρ hle
  have hrM : r ∈ M := hc.Rt_le_M t hrR
  have hLeq : conjSubgroup (h⁻¹ * (ρ : G)) (LB M Q B) = conjSubgroup r (LB M Q B) :=
    hc.conj_LB_eq_of_conj_BZ hhρ hrM hr
  have hLρ : conjSubgroup (ρ : G) (LB M Q B) = conjSubgroup (h * r * h⁻¹) (LB M Q B) := by
    have h1 : conjSubgroup (ρ : G) (LB M Q B) =
        conjSubgroup h (conjSubgroup (h⁻¹ * (ρ : G)) (LB M Q B)) := by
      rw [← conjSubgroup_mul]
      congr 1
      group
    have h2 : conjSubgroup (h * r) (LB M Q B) =
        conjSubgroup (h * r * h⁻¹) (conjSubgroup h (LB M Q B)) := by
      rw [← conjSubgroup_mul]
      congr 1
      group
    rw [h1, hLeq, ← conjSubgroup_mul, h2, hhL]
  refine ⟨ρ, ?_, ?_⟩
  · rw [hLρ]
    intro y hy
    rw [mem_conjSubgroup] at hy
    have hl : (h * r * h⁻¹)⁻¹ * y * (h * r * h⁻¹) ∈ conjSubgroup h (LB M Q B) := by
      rw [hhL]; exact hy
    have hlR : (h * r * h⁻¹)⁻¹ * y * (h * r * h⁻¹) ∈ conjSubgroup h (Rt M (LB M Q B) t) :=
      Subgroup.map_mono (le_Rt (LB M Q B) ht) hl
    have hr' : h * r * h⁻¹ ∈ conjSubgroup h (Rt M (LB M Q B) t) :=
      mem_conjSubgroup.mpr (by rwa [show h⁻¹ * (h * r * h⁻¹) * h = r by group])
    have hy_eq : y = (h * r * h⁻¹) * ((h * r * h⁻¹)⁻¹ * y * (h * r * h⁻¹)) *
        (h * r * h⁻¹)⁻¹ := by group
    rw [hy_eq]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hr' hlR) (Subgroup.inv_mem _ hr')
  · have := hmod.hLr ρ
    rwa [hρ] at this

theorem Env.step1b (I : Inputs) (e : Env hc n t m X) (hg : OmegaGeom Q' m)
    (hmod : OmegaModel hc t Q' E φ ψ u) {h : G} (hhM : h ∈ M)
    (hhL : conjSubgroup h (LB M Q B) = LB M Q B)
    (hne : conjSubgroup h (hc.CN t) ≠ hc.CN t) {w : ι → K}
    (hV : ∀ v : ↥(Vt M (LB M Q B) B Z t), (v : G) ∈ conjSubgroup h (Vt M (LB M Q B) B Z t) ↔
      (polar Q' (secVec ψ v) u = 0 ∧ polar Q' (secVec ψ v) w = 0))
    {x₁ x₂ : ι → K} (hQ₁ : Q' x₁ = 0) (hQ₂ : Q' x₂ = 0) (hx₁ : x₁ ≠ 0) (hx₂ : x₂ ≠ 0)
    (h12 : polar Q' x₁ x₂ ≠ 0) (h1u : polar Q' x₁ u = 0) (h1w : polar Q' x₁ w = 0)
    (h2u : polar Q' x₂ u = 0) (h2w : polar Q' x₂ w = 0) : False := by
  obtain ⟨ρ₁, hρ₁R, hρ₁⟩ := e.exists_conj_LB_le I hg hmod hhM hhL hV hQ₁ hx₁ h1u h1w
  obtain ⟨ρ₂, hρ₂R, hρ₂⟩ := e.exists_conj_LB_le I hg hmod hhM hhL hV hQ₂ hx₂ h2u h2w
  have hN1 : hc.CN t ≤ conjSubgroup (ρ₁ : G) (LB M Q B) := e.CN_le_conj_LB I ρ₁.2
  have hgen := le_sup_secOmega E hg.nondeg φ hmod.range hmod.ker hQ₁ hQ₂ h12 hρ₁ hρ₂
  have hRle : Rt M (LB M Q B) t ≤ conjSubgroup h (Rt M (LB M Q B) t) :=
    hgen.trans (sup_le (hN1.trans hρ₁R) (sup_le hρ₁R hρ₂R))
  have hReq : conjSubgroup h (Rt M (LB M Q B) t) = Rt M (LB M Q B) t :=
    (Subgroup.eq_of_le_of_card_ge hRle (by rw [card_conjSubgroup])).symm
  exact hne (e.conj_CN_eq_of_Rt I hhM hhL hReq)

theorem Env.step1c (I : Inputs) (e : Env hc n t m X) (hg : OmegaGeom Q' m)
    (hmod : OmegaModel hc t Q' E φ ψ u) {h : G} (hhM : h ∈ M)
    (hhL : conjSubgroup h (LB M Q B) = LB M Q B)
    (hne : conjSubgroup h (hc.CN t) ≠ hc.CN t) :
    hc.CN t ⊓ conjSubgroup h (hc.CN t) ≤ Q := by
  intro a ha
  by_contra haQ
  obtain ⟨s, hs, hsN⟩ := exists_mem_conj_not_mem hne
  obtain ⟨hsR, w, hw, hwu, hwA, hV⟩ := e.step1a I hmod hhM hhL hs hsN
  have hVV := e.V_eq_conj_of_mem (I := I) hhM ha.1 ha.2 haQ
  obtain ⟨y₀, hy₀⟩ := exists_polar_eq_one_of_ne_zero hg.nondeg hmod.u0
  obtain ⟨v, hv⟩ := exists_secVec_eq ψ y₀
  have hvV : (v : G) ∈ conjSubgroup h (Vt M (LB M Q B) B Z t) := by
    rw [← hVV]
    exact v.2
  have h0 := ((hV v).mp hvV).1
  rw [hv, polar_comm, hy₀] at h0
  exact one_ne_zero h0

theorem Env.step2 (I : Inputs) (e : Env hc n t m X) (hg : OmegaGeom Q' m)
    (hmod : OmegaModel hc t Q' E φ ψ u) {h : G} (hhM : h ∈ M)
    (hhL : conjSubgroup h (LB M Q B) = LB M Q B)
    (hne : conjSubgroup h (hc.CN t) ≠ hc.CN t) {w : ι → K} (hw : polar Q' u w = 0)
    (hwu : ∀ c : K, w ≠ c • u)
    (hV : ∀ v : ↥(Vt M (LB M Q B) B Z t), (v : G) ∈ conjSubgroup h (Vt M (LB M Q B) B Z t) ↔
      (polar Q' (secVec ψ v) u = 0 ∧ polar Q' (secVec ψ v) w = 0)) :
    Q' w = 0 ∧ m = 3 ∧ IsMinus Q' 3 := by
  have hfalse : ∀ x₁ x₂ : ι → K, Q' x₁ = 0 → Q' x₂ = 0 → polar Q' x₁ x₂ = 1 →
      polar Q' x₁ u = 0 → polar Q' x₁ w = 0 → polar Q' x₂ u = 0 → polar Q' x₂ w = 0 → False := by
    intro x₁ x₂ h1 h2 h12 h1u h1w h2u h2w
    have hx₁ : x₁ ≠ 0 := by
      rintro rfl
      rw [polar_zero_left] at h12
      exact zero_ne_one h12
    have hx₂ : x₂ ≠ 0 := by
      rintro rfl
      rw [polar_zero_right] at h12
      exact zero_ne_one h12
    exact e.step1b I hg hmod hhM hhL hne hV h1 h2 hx₁ hx₂ (by rw [h12]; exact one_ne_zero)
      h1u h1w h2u h2w
  have hQw : Q' w = 0 := by
    by_contra hQw
    have h6 : 6 ≤ Module.finrank K (ι → K) := by
      rw [hg.dim]; have := hg.three_le; omega
    obtain ⟨x₁, x₂, h1, h2, h12, h1u, h1w, h2u, h2w⟩ :=
      exists_pair_in_perp_of_ne hg.nondeg h6 hw hQw
    exact hfalse x₁ x₂ h1 h2 h12 h1u h1w h2u h2w
  refine ⟨hQw, ?_⟩
  rcases hg.three with hthree | h3
  · exfalso
    obtain ⟨x₁, x₂, h1, h2, h12, h1u, h1w, h2u, h2w⟩ :=
      exists_pair_in_perp_of_threePairs hg.nondeg hthree hmod.Qu hmod.u0 hw hQw hwu
    exact hfalse x₁ x₂ h1 h2 h12 h1u h1w h2u h2w
  · exact h3

end Step1

end HS6

end CFSG.RankThree.GF2n.Stroth80
