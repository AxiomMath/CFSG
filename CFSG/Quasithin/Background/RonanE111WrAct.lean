module

public import CFSG.Quasithin.Background.RonanE111Wr

public section

namespace CFSG.Quasithin.RonanE111

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.Quasithin.E2.E22N
  CFSG.Quasithin.E2.E22N.E111R
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {X T A J C : Subgroup G} [Fintype ↥C]

theorem wr_indep_B (h : DiagSetting X T A J C) {Y : Subgroup G} (hYJ : Y ≤ J)
    (hE : ∀ e ∈ actE T A J, A1b.conjSub e Y = Y) :
    ∃ B : Subgroup G, diagSub J C h.diagComm ⊓ B = ⊥ ∧
      B ≤ Subgroup.centralizer (diagSub J C h.diagComm : Set G) ∧
      (∀ k ∈ actT T A, A1b.conjSub k (diagSub J C h.diagComm) ≠ diagSub J C h.diagComm →
        A1b.conjSub k (diagSub J C h.diagComm) ≤ B) ∧
      wrY h.diagComm T A Y ≤ dimg h.diagComm Y ⊔ B := by
  have hI_mem := wr_I_mem h
  obtain ⟨i₀, hi₀⟩ : ∃ i₀ : ↥(diagFam T A J C h.diagComm),
      (i₀ : Subgroup G) = diagSub J C h.diagComm := ⟨⟨_, hI_mem⟩, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B : Subgroup G, B = ⨆ (j : ↥(diagFam T A J C h.diagComm))
      (_ : j ≠ i₀), (j : Subgroup G) := ⟨_, rfl⟩
  have hdisj : Disjoint (diagSub J C h.diagComm) B := by
    rw [hB, ← hi₀]
    exact h.semiFam.iSupIndep i₀
  have hIB : diagSub J C h.diagComm ⊓ B = ⊥ := disjoint_iff.mp hdisj
  have hBc : B ≤ Subgroup.centralizer (diagSub J C h.diagComm : Set G) := by
    rw [hB]
    refine iSup₂_le fun j hj => ?_
    intro y hy
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact h.semiFam.comm (diagSub J C h.diagComm) hI_mem (j : Subgroup G) j.2
      (fun e => hj (Subtype.ext (e.symm.trans hi₀.symm))) x hx y hy
  have hkB : ∀ k ∈ actT T A, A1b.conjSub k (diagSub J C h.diagComm) ≠ diagSub J C h.diagComm →
      A1b.conjSub k (diagSub J C h.diagComm) ≤ B := by
    intro k hk hkI
    rw [hB]
    exact le_iSup₂_of_le (⟨A1b.conjSub k (diagSub J C h.diagComm), wr_block_mem h hk⟩ :
      ↥(diagFam T A J C h.diagComm))
      (fun e => hkI ((congrArg Subtype.val e).trans hi₀)) le_rfl
  have hYB : wrY h.diagComm T A Y ≤ dimg h.diagComm Y ⊔ B := by
    rw [wrY_eq]
    refine iSup₂_le fun k hk => ?_
    by_cases hkI : A1b.conjSub k (diagSub J C h.diagComm) = diagSub J C h.diagComm
    · rw [wr_stab_dimg h hYJ hE hk hkI]
      exact le_sup_left
    · exact le_sup_of_le_right (le_trans (A1b.conjSub_mono k (dimg_le_diagSub h hYJ))
        (hkB k hk hkI))
  exact ⟨B, hIB, hBc, hkB, hYB⟩

theorem wr_indep_key (h : DiagSetting X T A J C) {Y : Subgroup G} (hYJ : Y ≤ J)
    (hE : ∀ e ∈ actE T A J, A1b.conjSub e Y = Y) {k : G} (hk : k ∈ actT T A)
    (hkI : A1b.conjSub k (diagSub J C h.diagComm) ≠ diagSub J C h.diagComm) {x x' : G}
    (hx : x ∈ diagSub J C h.diagComm) (hx' : x' ∈ A1b.conjSub k (diagSub J C h.diagComm))
    (hxx : x * x' ∈ wrY h.diagComm T A Y) : x ∈ dimg h.diagComm Y := by
  obtain ⟨B, hIB, hBc, hkB, hYB⟩ := wr_indep_B h hYJ hE
  have hx'B : x' ∈ B := hkB k hk hkI hx'
  have hHK : ∀ y ∈ dimg h.diagComm Y, ∀ b ∈ B, y * b * y⁻¹ ∈ B := by
    intro y hy b hb
    have hyb : y * b = b * y :=
      Subgroup.mem_centralizer_iff.mp (hBc hb) y (dimg_le_diagSub h hYJ hy)
    rw [hyb, mul_inv_cancel_right]
    exact hb
  obtain ⟨y, hy, b, hb, hyb⟩ := wr_mem_sup hHK (hYB hxx)
  have hyx : y⁻¹ * x = b * x'⁻¹ := by
    calc y⁻¹ * x = y⁻¹ * (x * x') * x'⁻¹ := by group
      _ = y⁻¹ * (y * b) * x'⁻¹ := by rw [hyb]
      _ = b * x'⁻¹ := by group
  have hmem : y⁻¹ * x ∈ diagSub J C h.diagComm ⊓ B := by
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · exact (diagSub J C h.diagComm).mul_mem
        ((diagSub J C h.diagComm).inv_mem (dimg_le_diagSub h hYJ hy)) hx
    · rw [hyx]
      exact B.mul_mem hb (B.inv_mem hx'B)
  rw [hIB, Subgroup.mem_bot] at hmem
  have hxy : x = y := by
    calc x = y * (y⁻¹ * x) := by group
      _ = y := by rw [hmem, mul_one]
  rw [hxy]
  exact hy

theorem wr_delta_mem_dimg_iff (h : DiagSetting X T A J C) {U : Subgroup G} (hU : U ≤ J)
    {u : G} (hu : u ∈ J) :
    diagHom J C h.diagComm ⟨u, hu⟩ ∈ dimg h.diagComm U ↔ u ∈ U := by
  constructor
  · intro hmem
    obtain ⟨v, hv, heq⟩ := (mem_dimg_iff h.diagComm).mp hmem
    have hvu : v = ⟨u, hu⟩ := diagHom_injective h.diagComm h.center_trivial heq
    have e : (v : G) = u := congrArg Subtype.val hvu
    rw [← e]
    exact hv
  · intro hu'
    exact (mem_dimg_iff h.diagComm).mpr ⟨⟨u, hu⟩, hu', rfl⟩

theorem wr_delta_mem_wrY_iff (h : DiagSetting X T A J C) {Y : Subgroup G} (hYJ : Y ≤ J)
    (hE : ∀ e ∈ actE T A J, A1b.conjSub e Y = Y) {u : G} (hu : u ∈ J) :
    diagHom J C h.diagComm ⟨u, hu⟩ ∈ wrY h.diagComm T A Y ↔ u ∈ Y := by
  constructor
  · intro hmem
    have hI : diagHom J C h.diagComm ⟨u, hu⟩ ∈ diagSub J C h.diagComm := by
      rw [← dimg_J h]
      exact (mem_dimg_iff h.diagComm).mpr ⟨⟨u, hu⟩, hu, rfl⟩
    exact (wr_delta_mem_dimg_iff h hYJ hu).mp
      (wr_inf_wrY h hYJ hE (Subgroup.mem_inf.mpr ⟨hI, hmem⟩))
  · intro huY
    exact wr_dimg_le_wrY h ((wr_delta_mem_dimg_iff h hYJ hu).mpr huY)

theorem wr_dimg_le_dimg_iff (h : DiagSetting X T A J C) {U V : Subgroup G} (hU : U ≤ J)
    (hV : V ≤ J) : dimg h.diagComm U ≤ dimg h.diagComm V ↔ U ≤ V := by
  constructor
  · intro hle x hx
    have hxJ : x ∈ J := hU hx
    have hmem := hle ((wr_delta_mem_dimg_iff h hU hxJ).mpr hx)
    exact (wr_delta_mem_dimg_iff h hV hxJ).mp hmem
  · exact dimg_mono h.diagComm

theorem wr_cv_conj_delta (h : DiagSetting X T A J C) {c v : G} (hc : c ∈ C)
    (hv : v ∈ A ⊓ Subgroup.normalizer (J : Set G)) {x : G} (hx : x ∈ J) :
    (c * v) * diagHom J C h.diagComm ⟨x, hx⟩ * (c * v)⁻¹ =
      diagHom J C h.diagComm ⟨v * x * v⁻¹, (Subgroup.mem_normalizer_iff.mp
        (Subgroup.mem_inf.mp hv).2 x).mp hx⟩ := by
  have hvN : v ∈ Subgroup.normalizer (J : Set G) := (Subgroup.mem_inf.mp hv).2
  have hvC : ∀ d ∈ C, v * d = d * v := fun d hd =>
    h.comm (Subgroup.mem_inf.mp hv).1 (h.CA hd)
  rw [show (c * v) * diagHom J C h.diagComm ⟨x, hx⟩ * (c * v)⁻¹ =
      c * (v * diagHom J C h.diagComm ⟨x, hx⟩ * v⁻¹) * c⁻¹ by group]
  rw [conj_diagHom_of_comm h.diagComm ⟨x, hx⟩ hvN hvC]
  exact conj_diagHom_of_mem h.diagComm _ hc

theorem wr_A_mem_actT (h : DiagSetting X T A J C) {a : G} (ha : a ∈ A) : a ∈ actT T A :=
  mem_actT_iff.mpr ⟨h.AT ha, Subgroup.mem_centralizer_iff.mpr fun b hb => h.comm hb ha⟩

theorem wr_A_conj_wrY (h : DiagSetting X T A J C) {Y : Subgroup G} {a : G} (ha : a ∈ A)
    {y : G} (hy : y ∈ wrY h.diagComm T A Y) : a * y * a⁻¹ ∈ wrY h.diagComm T A Y := by
  have hk := wr_A_mem_actT h ha
  have := A1b.mem_conjSub_of_mem (g := a) hy
  rwa [wr_conjSub_wrY h hk] at this

theorem wr_normal_subgroupOf_comm {W K : Subgroup G} (hWA : ∀ g ∈ W, ∀ n ∈ W, g * n = n * g)
    (hKW : K ≤ W) : (K.subgroupOf W).Normal := by
  refine ⟨fun n hn g => ?_⟩
  have hn' : (n : G) ∈ K := Subgroup.mem_subgroupOf.mp hn
  have hc : (g : G) * (n : G) = (n : G) * (g : G) := hWA (g : G) g.2 (n : G) n.2
  rw [Subgroup.mem_subgroupOf]
  have e : ((g * n * g⁻¹ : ↥W) : G) = (n : G) := by
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hc]
    group
  rw [e]
  exact hn'

theorem wr_relIndex_CX {W X B₁ C : Subgroup G} (hWA : ∀ g ∈ W, ∀ n ∈ W, g * n = n * g)
    (hXW : X ≤ W) (hB₁X : B₁ ≤ X) (hCW : C ≤ W) (hW : C ⊔ X = W) (hCX : C ⊓ X = ⊥) :
    (C ⊔ B₁).relIndex W = B₁.relIndex X := by
  have hBW : C ⊔ B₁ ≤ W := sup_le hCW (hB₁X.trans hXW)
  have hCB : ∀ c ∈ C, ∀ b ∈ B₁, c * b * c⁻¹ ∈ B₁ := by
    intro c hc b hb
    have e := hWA c (hCW hc) b (hXW (hB₁X hb))
    rw [e, mul_inv_cancel_right]
    exact hb
  have hBX : (C ⊔ B₁) ⊓ X = B₁ := by
    refine le_antisymm ?_ (le_inf le_sup_right hB₁X)
    intro x hx
    obtain ⟨hxB, hxX⟩ := Subgroup.mem_inf.mp hx
    obtain ⟨c, hc, b, hb, hcb⟩ := wr_mem_sup hCB hxB
    have hcX : c ∈ C ⊓ X := by
      refine Subgroup.mem_inf.mpr ⟨hc, ?_⟩
      have hce : c = x * b⁻¹ := by rw [← hcb]; group
      rw [hce]
      exact X.mul_mem hxX (X.inv_mem (hB₁X hb))
    rw [hCX, Subgroup.mem_bot] at hcX
    rw [hcX, one_mul] at hcb
    rw [← hcb]
    exact hb
  have hsup : X ⊔ (C ⊔ B₁) = W := by
    refine le_antisymm (sup_le hXW hBW) ?_
    rw [← hW]
    exact sup_le (le_sup_of_le_right le_sup_left) le_sup_left
  haveI : ((C ⊔ B₁).subgroupOf W).Normal := wr_normal_subgroupOf_comm hWA hBW
  have htop : X.subgroupOf W ⊔ (C ⊔ B₁).subgroupOf W = ⊤ := by
    rw [eq_top_iff]
    rintro x -
    have hxW : (x : G) ∈ X ⊔ (C ⊔ B₁) := by
      rw [hsup]
      exact x.2
    have hXnorm : ∀ p ∈ X, ∀ k ∈ C ⊔ B₁, p * k * p⁻¹ ∈ C ⊔ B₁ := by
      intro p hp k hk
      have e := hWA p (hXW hp) k (hBW hk)
      rw [e, mul_inv_cancel_right]
      exact hk
    obtain ⟨p, hp, q, hq, hpq⟩ := wr_mem_sup hXnorm hxW
    have hx : x = (⟨p, hXW hp⟩ : ↥W) * ⟨q, hBW hq⟩ := Subtype.ext hpq.symm
    rw [hx]
    exact Subgroup.mul_mem_sup (Subgroup.mem_subgroupOf.mpr hp) (Subgroup.mem_subgroupOf.mpr hq)
  have hinf : (C ⊔ B₁).subgroupOf W ⊓ X.subgroupOf W = B₁.subgroupOf W := by
    ext x
    rw [Subgroup.mem_inf, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf,
      Subgroup.mem_subgroupOf, ← Subgroup.mem_inf, hBX]
  calc (C ⊔ B₁).relIndex W = ((C ⊔ B₁).subgroupOf W).index := rfl
    _ = ((C ⊔ B₁).subgroupOf W).relIndex ⊤ := by rw [Subgroup.relIndex_top_right]
    _ = ((C ⊔ B₁).subgroupOf W).relIndex (X.subgroupOf W ⊔ (C ⊔ B₁).subgroupOf W) := by
        rw [htop]
    _ = ((C ⊔ B₁).subgroupOf W).relIndex (X.subgroupOf W) :=
        Subgroup.relIndex_sup_right _ _
    _ = ((C ⊔ B₁).subgroupOf W ⊓ X.subgroupOf W).relIndex (X.subgroupOf W) :=
        (Subgroup.inf_relIndex_right _ _).symm
    _ = (B₁.subgroupOf W).relIndex (X.subgroupOf W) := by rw [hinf]
    _ = B₁.relIndex X := Subgroup.relIndex_subgroupOf hXW

theorem wreath_move (h : DiagSetting X T A J C) {D Y : Subgroup G} {𝒟 : Set (Subgroup G)}
    (hJD : JData (actE T A J) J D Y 𝒟) {S₀ : Subgroup G} (hS₀ : S₀ ∈ 𝒟)
    (hmove : (∃ S ∈ 𝒟, ∃ v ∈ A ⊓ Subgroup.normalizer (J : Set G), ∃ s ∈ S,
        v * s * v⁻¹ * s⁻¹ ∉ Y) ∨
      (∃ a ∈ A, a ∉ C ⊔ (A ⊓ Subgroup.normalizer (J : Set G)))) :
    ∃ S ∈ wrFam h.diagComm T A S₀ Y, ∃ a ∈ A, ∃ s ∈ S,
      a * s * a⁻¹ * s⁻¹ ∉ wrY h.diagComm T A Y := by
  have hS₀D : S₀ ≤ D := hJD.SM.le_D S₀ hS₀
  have hS₀J : S₀ ≤ J := hS₀D.trans hJD.D_le
  have hYS₀ : Y ≤ S₀ := hJD.SM.Y_le S₀ hS₀
  have hYJ : Y ≤ J := hYS₀.trans hS₀J
  have hE : ∀ e ∈ actE T A J, A1b.conjSub e Y = Y := hJD.E_Y
  have hnab : ¬ ⁅S₀, S₀⁆ ≤ Y := hJD.SM.nonab S₀ hS₀
  rcases hmove with ⟨S, hS, v, hv, s, hs, hvs⟩ | ⟨a, ha, haC⟩
  ·
    obtain ⟨e, he, rfl⟩ := hJD.SM.trans S₀ hS₀ S hS
    have heN : e ∈ Subgroup.normalizer (J : Set G) := wr_actE_normalizer he
    have heC : ∀ c ∈ C, e * c = c * e := wr_actE_comm h he
    have heT : e ∈ actT T A :=
      mem_actT_iff.mpr ⟨(mem_actE_iff.mp he).1, (mem_actE_iff.mp he).2.2⟩
    have hsJ : s ∈ J := hJD.D_le (hJD.SM.le_D _ hS hs)
    have hvN : v ∈ Subgroup.normalizer (J : Set G) := (Subgroup.mem_inf.mp hv).2
    have hvC : ∀ c ∈ C, v * c = c * v := fun c hc =>
      h.comm (Subgroup.mem_inf.mp hv).1 (h.CA hc)
    have hJ2 : v * s * v⁻¹ * s⁻¹ ∈ J :=
      J.mul_mem ((Subgroup.mem_normalizer_iff.mp hvN s).mp hsJ) (J.inv_mem hsJ)
    refine ⟨A1b.conjSub e (dimg h.diagComm S₀ ⊔ wrY h.diagComm T A Y), ⟨e, heT, rfl⟩,
      v, (Subgroup.mem_inf.mp hv).1, diagHom J C h.diagComm ⟨s, hsJ⟩, ?_, ?_⟩
    · have hmem : diagHom J C h.diagComm ⟨s, hsJ⟩ ∈ A1b.conjSub e (dimg h.diagComm S₀) := by
        rw [conj_dimg_eq h hS₀J heN heC]
        exact (mem_dimg_iff h.diagComm).mpr ⟨⟨s, hsJ⟩, hs, rfl⟩
      exact A1b.conjSub_mono e le_sup_left hmem
    · intro hcontra
      apply hvs
      have e1 : v * diagHom J C h.diagComm ⟨s, hsJ⟩ * v⁻¹ *
          (diagHom J C h.diagComm ⟨s, hsJ⟩)⁻¹ =
          diagHom J C h.diagComm ⟨v * s * v⁻¹ * s⁻¹, hJ2⟩ := by
        rw [conj_diagHom_of_comm h.diagComm ⟨s, hsJ⟩ hvN hvC, ← map_inv, ← map_mul]
        rfl
      rw [e1] at hcontra
      exact (wr_delta_mem_wrY_iff h hYJ hE hJ2).mp hcontra
  ·
    have haT : a ∈ actT T A := wr_A_mem_actT h ha
    have hconj : A1b.conjSub a (diagSub J C h.diagComm) ≠ diagSub J C h.diagComm := by
      intro hI
      obtain ⟨e, he, c, hc, c', hc', hae⟩ := wr_stab_decomp h haT hI
      apply haC
      have heA : e ∈ A := by
        have hee : e = c'⁻¹ * a * c := by rw [hae]; group
        rw [hee]
        exact A.mul_mem (A.mul_mem (A.inv_mem (h.CA hc')) ha) (h.CA hc)
      rw [hae]
      exact (C ⊔ (A ⊓ Subgroup.normalizer (J : Set G))).mul_mem
        ((C ⊔ (A ⊓ Subgroup.normalizer (J : Set G))).mul_mem (Subgroup.mem_sup_left hc')
          (Subgroup.mem_sup_right (Subgroup.mem_inf.mpr ⟨heA, wr_actE_normalizer he⟩)))
        (Subgroup.mem_sup_left (C.inv_mem hc))
    obtain ⟨s₀, hs₀S, hs₀Y⟩ : ∃ s₀ ∈ S₀, s₀ ∉ Y := by
      by_contra hcon
      push Not at hcon
      exact hnab ((E111R.commutator_le_self S₀).trans (show S₀ ≤ Y from fun x hx => hcon x hx))
    have hs₀J : s₀ ∈ J := hS₀J hs₀S
    have hsδI : diagHom J C h.diagComm ⟨s₀, hs₀J⟩ ∈ diagSub J C h.diagComm := by
      rw [← dimg_J h]
      exact (mem_dimg_iff h.diagComm).mpr ⟨⟨s₀, hs₀J⟩, hs₀J, rfl⟩
    have hsδP : diagHom J C h.diagComm ⟨s₀, hs₀J⟩ ∈ dimg h.diagComm S₀ ⊔ wrY h.diagComm T A Y :=
      (le_sup_left : dimg h.diagComm S₀ ≤ dimg h.diagComm S₀ ⊔ wrY h.diagComm T A Y)
        ((mem_dimg_iff h.diagComm).mpr ⟨⟨s₀, hs₀J⟩, hs₀S, rfl⟩)
    refine ⟨dimg h.diagComm S₀ ⊔ wrY h.diagComm T A Y, ?_, a, ha,
      diagHom J C h.diagComm ⟨s₀, hs₀J⟩, hsδP, ?_⟩
    · rw [wrFam_eq]
      exact ⟨1, (actT T A).one_mem, A1b.conjSub_one _⟩
    · intro hcomm
      have hcomm2 := wr_block_comm_I h haT hconj _ (A1b.mem_conjSub_of_mem hsδI) _ hsδI
      have e3 : (diagHom J C h.diagComm ⟨s₀, hs₀J⟩)⁻¹ *
          (a * diagHom J C h.diagComm ⟨s₀, hs₀J⟩ * a⁻¹) =
          a * diagHom J C h.diagComm ⟨s₀, hs₀J⟩ * a⁻¹ *
            (diagHom J C h.diagComm ⟨s₀, hs₀J⟩)⁻¹ := by
        calc (diagHom J C h.diagComm ⟨s₀, hs₀J⟩)⁻¹ *
              (a * diagHom J C h.diagComm ⟨s₀, hs₀J⟩ * a⁻¹)
            = (diagHom J C h.diagComm ⟨s₀, hs₀J⟩)⁻¹ *
                ((a * diagHom J C h.diagComm ⟨s₀, hs₀J⟩ * a⁻¹) *
                  diagHom J C h.diagComm ⟨s₀, hs₀J⟩) *
                (diagHom J C h.diagComm ⟨s₀, hs₀J⟩)⁻¹ := by group
          _ = (diagHom J C h.diagComm ⟨s₀, hs₀J⟩)⁻¹ *
                (diagHom J C h.diagComm ⟨s₀, hs₀J⟩ * (a * diagHom J C h.diagComm ⟨s₀, hs₀J⟩ * a⁻¹)) *
                (diagHom J C h.diagComm ⟨s₀, hs₀J⟩)⁻¹ := by rw [hcomm2]
          _ = a * diagHom J C h.diagComm ⟨s₀, hs₀J⟩ * a⁻¹ *
                (diagHom J C h.diagComm ⟨s₀, hs₀J⟩)⁻¹ := by group
      have hxx : (diagHom J C h.diagComm ⟨s₀, hs₀J⟩)⁻¹ *
          (a * diagHom J C h.diagComm ⟨s₀, hs₀J⟩ * a⁻¹) ∈ wrY h.diagComm T A Y := by
        rw [e3]
        exact hcomm
      have hinv : (diagHom J C h.diagComm ⟨s₀, hs₀J⟩)⁻¹ ∈ dimg h.diagComm Y :=
        wr_indep_key h hYJ hE haT hconj ((diagSub J C h.diagComm).inv_mem hsδI)
          (A1b.mem_conjSub_of_mem hsδI) hxx
      have hsY : diagHom J C h.diagComm ⟨s₀, hs₀J⟩ ∈ dimg h.diagComm Y := by
        simpa using (dimg h.diagComm Y).inv_mem hinv
      exact hs₀Y ((wr_delta_mem_dimg_iff h hYJ hs₀J).mp hsY)

theorem wr_dimg_normalizes_wrY (h : DiagSetting X T A J C) {Y S₀ : Subgroup G} (hS₀J : S₀ ≤ J)
    (hYJ : Y ≤ J) (hS₀N : S₀ ≤ Subgroup.normalizer (Y : Set G))
    (hE : ∀ e ∈ actE T A J, A1b.conjSub e Y = Y) {p : G} (hp : p ∈ dimg h.diagComm S₀)
    {y : G} (hy : y ∈ wrY h.diagComm T A Y) : p * y * p⁻¹ ∈ wrY h.diagComm T A Y :=
  (Subgroup.mem_normalizer_iff.mp
    (wr_dimg_le_normalizer_wrY h le_rfl hS₀J hYJ hS₀N hE hp) y).mp hy

theorem wr_comm_step (h : DiagSetting X T A J C) {Y : Subgroup G} (hYJ : Y ≤ J)
    (hE : ∀ e ∈ actE T A J, A1b.conjSub e Y = Y) {c v : G} (hc : c ∈ C)
    (hv : v ∈ A ⊓ Subgroup.normalizer (J : Set G)) {s₀ : G} (hs₀ : s₀ ∈ J)
    (hvs : v * s₀ * v⁻¹ * s₀⁻¹ ∈ Y) {d : G} (hd : d = diagHom J C h.diagComm ⟨s₀, hs₀⟩)
    (hdN : ∀ y ∈ wrY h.diagComm T A Y, d * y * d⁻¹ ∈ wrY h.diagComm T A Y)
    {y : G} (hy : y ∈ wrY h.diagComm T A Y) :
    (c * v) * (d * y) * (c * v)⁻¹ * (d * y)⁻¹ ∈ wrY h.diagComm T A Y := by
  have hvN : v ∈ Subgroup.normalizer (J : Set G) := (Subgroup.mem_inf.mp hv).2
  have hJ1 : v * s₀ * v⁻¹ ∈ J := (Subgroup.mem_normalizer_iff.mp hvN s₀).mp hs₀
  have hJ2 : v * s₀ * v⁻¹ * s₀⁻¹ ∈ J := J.mul_mem hJ1 (J.inv_mem hs₀)
  have hgA : c * v ∈ A := A.mul_mem (h.CA hc) (Subgroup.mem_inf.mp hv).1
  have hgY : ∀ z ∈ wrY h.diagComm T A Y, (c * v) * z * (c * v)⁻¹ ∈ wrY h.diagComm T A Y :=
    fun z hz => wr_A_conj_wrY h hgA hz
  have h1 : (c * v) * d * (c * v)⁻¹ * d⁻¹ ∈ wrY h.diagComm T A Y := by
    have e1 : (c * v) * d * (c * v)⁻¹ * d⁻¹ =
        diagHom J C h.diagComm ⟨v * s₀ * v⁻¹ * s₀⁻¹, hJ2⟩ := by
      rw [hd, wr_cv_conj_delta h hc hv hs₀, ← map_inv, ← map_mul]
      rfl
    rw [e1]
    exact (wr_delta_mem_wrY_iff h hYJ hE hJ2).mpr hvs
  have e2 : (c * v) * (d * y) * (c * v)⁻¹ * (d * y)⁻¹ =
      ((c * v) * d * (c * v)⁻¹ * d⁻¹) * (d * ((c * v) * y * (c * v)⁻¹ * y⁻¹) * d⁻¹) := by
    group
  rw [e2]
  refine (wrY h.diagComm T A Y).mul_mem h1 (hdN _ ?_)
  exact (wrY h.diagComm T A Y).mul_mem (hgY y hy) ((wrY h.diagComm T A Y).inv_mem hy)

theorem wr_W_stab (h : DiagSetting X T A J C) {Y S₀ : Subgroup G} (hYJ : Y ≤ J) (hS₀J : S₀ ≤ J)
    (hS₀N : S₀ ≤ Subgroup.normalizer (Y : Set G))
    (hE : ∀ e ∈ actE T A J, A1b.conjSub e Y = Y) (hnab : ¬ ⁅S₀, S₀⁆ ≤ Y) {a : G}
    (ha : a ∈ A ⊓ Subgroup.normalizer
      ((dimg h.diagComm S₀ ⊔ wrY h.diagComm T A Y : Subgroup G) : Set G)) :
    A1b.conjSub a (diagSub J C h.diagComm) = diagSub J C h.diagComm := by
  by_contra hconj
  have haA : a ∈ A := (Subgroup.mem_inf.mp ha).1
  have haN := (Subgroup.mem_inf.mp ha).2
  have haT : a ∈ actT T A := wr_A_mem_actT h haA
  have hstep : ∀ s₁ ∈ dimg h.diagComm S₀, a * s₁ * a⁻¹ ∈ wrY h.diagComm T A Y := by
    intro s₁ hs₁
    have hmemS : a * s₁ * a⁻¹ ∈ dimg h.diagComm S₀ ⊔ wrY h.diagComm T A Y :=
      (Subgroup.mem_normalizer_iff.mp haN s₁).mp
        ((le_sup_left : dimg h.diagComm S₀ ≤ dimg h.diagComm S₀ ⊔ wrY h.diagComm T A Y) hs₁)
    obtain ⟨p, hp, y, hy, hpy⟩ := wr_mem_sup
      (H := dimg h.diagComm S₀) (K := wrY h.diagComm T A Y)
      (fun p hp y hy => wr_dimg_normalizes_wrY h hS₀J hYJ hS₀N hE hp hy) hmemS
    have hx' : a * s₁ * a⁻¹ ∈ A1b.conjSub a (diagSub J C h.diagComm) :=
      A1b.mem_conjSub_of_mem (dimg_le_diagSub h hS₀J hs₁)
    have hpI : p⁻¹ ∈ diagSub J C h.diagComm :=
      (diagSub J C h.diagComm).inv_mem (dimg_le_diagSub h hS₀J hp)
    have hxx : p⁻¹ * (a * s₁ * a⁻¹) ∈ wrY h.diagComm T A Y := by
      rw [← hpy, ← mul_assoc, inv_mul_cancel, one_mul]
      exact hy
    have hpd : p⁻¹ ∈ dimg h.diagComm Y :=
      wr_indep_key h hYJ hE haT hconj hpI hx' hxx
    have hp' : p ∈ dimg h.diagComm Y := by simpa using (dimg h.diagComm Y).inv_mem hpd
    rw [← hpy]
    exact (wrY h.diagComm T A Y).mul_mem (wr_dimg_le_wrY h hp') hy
  have hSY : dimg h.diagComm S₀ ≤ wrY h.diagComm T A Y := by
    intro s₁ hs₁
    have hc := wr_A_conj_wrY h (A.inv_mem haA) (hstep s₁ hs₁)
    have e : a⁻¹ * (a * s₁ * a⁻¹) * (a⁻¹)⁻¹ = s₁ := by group
    rw [e] at hc
    exact hc
  have hSI : dimg h.diagComm S₀ ≤ dimg h.diagComm Y := fun s₁ hs₁ =>
    wr_inf_wrY h hYJ hE (Subgroup.mem_inf.mpr ⟨dimg_le_diagSub h hS₀J hs₁, hSY hs₁⟩)
  have hS₀Y : S₀ ≤ Y := (wr_dimg_le_dimg_iff h hS₀J hYJ).mp hSI
  exact hnab ((E111R.commutator_le_self S₀).trans hS₀Y)

theorem wr_C_normalizes (h : DiagSetting X T A J C) {Y S₀ : Subgroup G} (hS₀J : S₀ ≤ J) {c : G}
    (hc : c ∈ C) :
    c ∈ Subgroup.normalizer ((dimg h.diagComm S₀ ⊔ wrY h.diagComm T A Y : Subgroup G) : Set G) := by
  refine E111R.mem_normalizer_of_conjSub_eq ?_
  rw [wr_conjSub_sup, dimg_fix h hS₀J hc, wr_conjSub_wrY h (wr_A_mem_actT h (h.CA hc))]

theorem wr_X_normalizes (h : DiagSetting X T A J C) {Y S₀ : Subgroup G} (hS₀J : S₀ ≤ J)
    {v : G} (hv : v ∈ A ⊓ Subgroup.normalizer (J : Set G))
    (hvS : v ∈ Subgroup.normalizer (S₀ : Set G)) :
    v ∈ Subgroup.normalizer ((dimg h.diagComm S₀ ⊔ wrY h.diagComm T A Y : Subgroup G) : Set G) := by
  have hvN : v ∈ Subgroup.normalizer (J : Set G) := (Subgroup.mem_inf.mp hv).2
  have hvC : ∀ c ∈ C, v * c = c * v := fun c hc => h.comm (Subgroup.mem_inf.mp hv).1 (h.CA hc)
  have e1 : A1b.conjSub v (dimg h.diagComm S₀) = dimg h.diagComm S₀ := by
    rw [conj_dimg_eq h hS₀J hvN hvC, E111R.conjSub_eq_of_mem_normalizer hvS]
  refine E111R.mem_normalizer_of_conjSub_eq ?_
  rw [wr_conjSub_sup, e1, wr_conjSub_wrY h (wr_A_mem_actT h (Subgroup.mem_inf.mp hv).1)]

theorem wr_W_normalizes_S0 (h : DiagSetting X T A J C) {Y S₀ : Subgroup G} (hYS₀ : Y ≤ S₀)
    (hS₀J : S₀ ≤ J) (hYJ : Y ≤ J) (hS₀N : S₀ ≤ Subgroup.normalizer (Y : Set G))
    (hE : ∀ e ∈ actE T A J, A1b.conjSub e Y = Y) {v : G}
    (hv : v ∈ A ⊓ Subgroup.normalizer (J : Set G))
    (hvS : v ∈ Subgroup.normalizer ((dimg h.diagComm S₀ ⊔ wrY h.diagComm T A Y : Subgroup G) : Set G)) :
    v ∈ Subgroup.normalizer (S₀ : Set G) := by
  have hvN : v ∈ Subgroup.normalizer (J : Set G) := (Subgroup.mem_inf.mp hv).2
  have hvC : ∀ c ∈ C, v * c = c * v := fun c hc => h.comm (Subgroup.mem_inf.mp hv).1 (h.CA hc)
  have hS'eq : A1b.conjSub v (dimg h.diagComm S₀ ⊔ wrY h.diagComm T A Y) =
      dimg h.diagComm S₀ ⊔ wrY h.diagComm T A Y := E111R.conjSub_eq_of_mem_normalizer hvS
  have hI : A1b.conjSub v (diagSub J C h.diagComm) = diagSub J C h.diagComm :=
    h.conjSub_diag_of_comm hvN hvC
  have e1 : A1b.conjSub v (dimg h.diagComm S₀) = dimg h.diagComm (A1b.conjSub v S₀) :=
    conj_dimg_eq h hS₀J hvN hvC
  have h1 : A1b.conjSub v (dimg h.diagComm S₀) ≤ dimg h.diagComm S₀ ⊔ wrY h.diagComm T A Y := by
    have := A1b.conjSub_mono v (le_sup_left : dimg h.diagComm S₀ ≤
      dimg h.diagComm S₀ ⊔ wrY h.diagComm T A Y)
    rwa [hS'eq] at this
  have h2 : A1b.conjSub v (dimg h.diagComm S₀) ≤ diagSub J C h.diagComm := by
    have := A1b.conjSub_mono v (dimg_le_diagSub h hS₀J)
    rwa [hI] at this
  have hle2 : A1b.conjSub v (dimg h.diagComm S₀) ≤ dimg h.diagComm S₀ := by
    intro x hx
    obtain ⟨p, hp, y, hy, hpy⟩ := wr_mem_sup
      (H := dimg h.diagComm S₀) (K := wrY h.diagComm T A Y)
      (fun p hp y hy => wr_dimg_normalizes_wrY h hS₀J hYJ hS₀N hE hp hy) (h1 hx)
    have hpI : p ∈ diagSub J C h.diagComm := dimg_le_diagSub h hS₀J hp
    have hyI : y ∈ diagSub J C h.diagComm := by
      have hye : y = p⁻¹ * x := by rw [← hpy]; group
      rw [hye]
      exact (diagSub J C h.diagComm).mul_mem ((diagSub J C h.diagComm).inv_mem hpI) (h2 hx)
    have hyY : y ∈ dimg h.diagComm Y :=
      wr_inf_wrY h hYJ hE (Subgroup.mem_inf.mpr ⟨hyI, hy⟩)
    have hyS : y ∈ dimg h.diagComm S₀ := dimg_mono h.diagComm hYS₀ hyY
    rw [← hpy]
    exact (dimg h.diagComm S₀).mul_mem hp hyS
  have hdle : dimg h.diagComm (A1b.conjSub v S₀) ≤ dimg h.diagComm S₀ := by
    rw [← e1]
    exact hle2
  have hS₀'J : A1b.conjSub v S₀ ≤ J :=
    (A1b.conjSub_mono v hS₀J).trans (le_of_eq (E111R.conjSub_eq_of_mem_normalizer hvN))
  have hle3 : A1b.conjSub v S₀ ≤ S₀ := (wr_dimg_le_dimg_iff h hS₀'J hS₀J).mp hdle
  have hceq : A1b.conjSub v S₀ = S₀ :=
    Subgroup.eq_of_le_of_card_ge hle3 (E111R.card_conjSub v S₀).ge
  exact E111R.mem_normalizer_of_conjSub_eq hceq

theorem wr_W_decomp (h : DiagSetting X T A J C) {Y S₀ : Subgroup G} (hYS₀ : Y ≤ S₀)
    (hS₀J : S₀ ≤ J) (hYJ : Y ≤ J) (hS₀N : S₀ ≤ Subgroup.normalizer (Y : Set G))
    (hE : ∀ e ∈ actE T A J, A1b.conjSub e Y = Y) (hnab : ¬ ⁅S₀, S₀⁆ ≤ Y) {a : G}
    (ha : a ∈ A ⊓ Subgroup.normalizer
      ((dimg h.diagComm S₀ ⊔ wrY h.diagComm T A Y : Subgroup G) : Set G)) :
    ∃ c ∈ C, ∃ v ∈ A ⊓ Subgroup.normalizer (J : Set G) ⊓ Subgroup.normalizer (S₀ : Set G),
      a = c * v := by
  have haA : a ∈ A := (Subgroup.mem_inf.mp ha).1
  have haN := (Subgroup.mem_inf.mp ha).2
  obtain ⟨e, he, c, hc, c', hc', hae⟩ :=
    wr_stab_decomp h (wr_A_mem_actT h haA) (wr_W_stab h hYJ hS₀J hS₀N hE hnab ha)
  have hee : e = c'⁻¹ * a * c := by rw [hae]; group
  have heA : e ∈ A := by
    rw [hee]
    exact A.mul_mem (A.mul_mem (A.inv_mem (h.CA hc')) haA) (h.CA hc)
  have heN' : e ∈ Subgroup.normalizer ((dimg h.diagComm S₀ ⊔ wrY h.diagComm T A Y : Subgroup G) :
      Set G) := by
    rw [hee]
    exact (Subgroup.normalizer ((dimg h.diagComm S₀ ⊔ wrY h.diagComm T A Y : Subgroup G) :
      Set G)).mul_mem ((Subgroup.normalizer ((dimg h.diagComm S₀ ⊔ wrY h.diagComm T A Y :
        Subgroup G) : Set G)).mul_mem
        ((Subgroup.normalizer ((dimg h.diagComm S₀ ⊔ wrY h.diagComm T A Y : Subgroup G) :
          Set G)).inv_mem (wr_C_normalizes h hS₀J hc')) haN)
      (wr_C_normalizes h hS₀J hc)
  have heS₀ : e ∈ Subgroup.normalizer (S₀ : Set G) :=
    wr_W_normalizes_S0 h hYS₀ hS₀J hYJ hS₀N hE
      (Subgroup.mem_inf.mpr ⟨heA, wr_actE_normalizer he⟩) heN'
  have hce : c⁻¹ * e = e * c⁻¹ := h.comm (A.inv_mem (h.CA hc)) heA
  refine ⟨c' * c⁻¹, C.mul_mem hc' (C.inv_mem hc), e,
    Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨heA, wr_actE_normalizer he⟩, heS₀⟩, ?_⟩
  rw [hae]
  calc c' * e * c⁻¹ = c' * (e * c⁻¹) := mul_assoc _ _ _
    _ = c' * (c⁻¹ * e) := by rw [← hce]
    _ = c' * c⁻¹ * e := (mul_assoc _ _ _).symm

theorem wr_inf_normalizer_conjSub (h : DiagSetting X T A J C) {k : G} (hk : k ∈ actT T A)
    (U : Subgroup G) :
    A ⊓ Subgroup.normalizer ((A1b.conjSub k U : Subgroup G) : Set G) =
      A ⊓ Subgroup.normalizer (U : Set G) := by
  have hkC : k ∈ Subgroup.centralizer (A : Set G) := (mem_actT_iff.mp hk).2
  ext a
  rw [Subgroup.mem_inf, Subgroup.mem_inf]
  refine and_congr_right fun haA => ?_
  have hak : a * k = k * a := Subgroup.mem_centralizer_iff.mp hkC a haA
  have hconj_eq : A1b.conjSub a (A1b.conjSub k U) = A1b.conjSub k (A1b.conjSub a U) := by
    rw [← A1b.conjSub_mul, hak, A1b.conjSub_mul]
  constructor
  · intro hn
    have h1 := E111R.conjSub_eq_of_mem_normalizer hn
    rw [hconj_eq, A1b.conjSub_inj] at h1
    exact E111R.mem_normalizer_of_conjSub_eq h1
  · intro hn
    have h1 := E111R.conjSub_eq_of_mem_normalizer hn
    apply E111R.mem_normalizer_of_conjSub_eq
    rw [hconj_eq, h1]

theorem wr_rank_core (h : DiagSetting X T A J C) {D Y : Subgroup G} {𝒟 : Set (Subgroup G)}
    (hJD : JData (actE T A J) J D Y 𝒟) {S₀ : Subgroup G} (hS₀ : S₀ ∈ 𝒟) (n : ℕ)
    (hrank : ∀ S ∈ 𝒟, (∃ v ∈ A ⊓ Subgroup.normalizer (J : Set G) ⊓ Subgroup.normalizer (S : Set G),
        ∃ s ∈ S, v * s * v⁻¹ * s⁻¹ ∉ Y) →
      ∃ B ≤ A ⊓ Subgroup.normalizer (J : Set G) ⊓ Subgroup.normalizer (S : Set G),
        (∀ b ∈ B, ∀ s ∈ S, b * s * b⁻¹ * s⁻¹ ∈ Y) ∧
          B.relIndex (A ⊓ Subgroup.normalizer (J : Set G) ⊓ Subgroup.normalizer (S : Set G)) ≤ 2 ^ n)
    {a : G} (ha : a ∈ A ⊓ Subgroup.normalizer
      ((dimg h.diagComm S₀ ⊔ wrY h.diagComm T A Y : Subgroup G) : Set G))
    {s : G} (hs : s ∈ dimg h.diagComm S₀ ⊔ wrY h.diagComm T A Y)
    (has : a * s * a⁻¹ * s⁻¹ ∉ wrY h.diagComm T A Y) :
    ∃ B ≤ A ⊓ Subgroup.normalizer
        ((dimg h.diagComm S₀ ⊔ wrY h.diagComm T A Y : Subgroup G) : Set G),
      (∀ b ∈ B, ∀ t ∈ dimg h.diagComm S₀ ⊔ wrY h.diagComm T A Y,
        b * t * b⁻¹ * t⁻¹ ∈ wrY h.diagComm T A Y) ∧
        B.relIndex (A ⊓ Subgroup.normalizer
          ((dimg h.diagComm S₀ ⊔ wrY h.diagComm T A Y : Subgroup G) : Set G)) ≤ 2 ^ n := by
  have hS₀D : S₀ ≤ D := hJD.SM.le_D S₀ hS₀
  have hS₀J : S₀ ≤ J := hS₀D.trans hJD.D_le
  have hYS₀ : Y ≤ S₀ := hJD.SM.Y_le S₀ hS₀
  have hYJ : Y ≤ J := hYS₀.trans hS₀J
  have hE : ∀ e ∈ actE T A J, A1b.conjSub e Y = Y := hJD.E_Y
  have hnab : ¬ ⁅S₀, S₀⁆ ≤ Y := hJD.SM.nonab S₀ hS₀
  have hDN : D ≤ Subgroup.normalizer (Y : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (hYS₀.trans hS₀D)).mp hJD.Y_normal
  have hS₀N : S₀ ≤ Subgroup.normalizer (Y : Set G) := hS₀D.trans hDN
  have hPnorm : ∀ p ∈ dimg h.diagComm S₀, ∀ y ∈ wrY h.diagComm T A Y,
      p * y * p⁻¹ ∈ wrY h.diagComm T A Y :=
    fun p hp y hy => wr_dimg_normalizes_wrY h hS₀J hYJ hS₀N hE hp hy
  obtain ⟨c, hc, v, hvX, hav⟩ := wr_W_decomp h hYS₀ hS₀J hYJ hS₀N hE hnab ha
  obtain ⟨d, hd, y', hy', hds⟩ := wr_mem_sup
    (H := dimg h.diagComm S₀) (K := wrY h.diagComm T A Y) hPnorm hs
  obtain ⟨u, hu, hdu⟩ := (mem_dimg_iff h.diagComm).mp hd
  subst hav
  subst hdu
  subst hds
  have hvXA : v ∈ A ⊓ Subgroup.normalizer (J : Set G) := (Subgroup.mem_inf.mp hvX).1
  have hnot : v * (u : G) * v⁻¹ * (u : G)⁻¹ ∉ Y := by
    intro hvu
    apply has
    exact wr_comm_step h hYJ hE hc hvXA u.2 hvu rfl
      (fun y hy => hPnorm _ ((mem_dimg_iff h.diagComm).mpr ⟨u, hu, rfl⟩) y hy) hy'
  obtain ⟨B₁, hB₁X, hB₁, hB₁idx⟩ := hrank S₀ hS₀ ⟨v, hvX, (u : G), hu, hnot⟩
  have hXW : A ⊓ Subgroup.normalizer (J : Set G) ⊓ Subgroup.normalizer (S₀ : Set G) ≤
      A ⊓ Subgroup.normalizer ((dimg h.diagComm S₀ ⊔ wrY h.diagComm T A Y : Subgroup G) : Set G) :=
    fun x hx => Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp (Subgroup.mem_inf.mp hx).1).1,
      wr_X_normalizes h hS₀J (Subgroup.mem_inf.mp hx).1 (Subgroup.mem_inf.mp hx).2⟩
  have hCW : C ≤ A ⊓ Subgroup.normalizer
      ((dimg h.diagComm S₀ ⊔ wrY h.diagComm T A Y : Subgroup G) : Set G) :=
    fun x hx => Subgroup.mem_inf.mpr ⟨h.CA hx, wr_C_normalizes h hS₀J hx⟩
  have hWA : ∀ g ∈ A ⊓ Subgroup.normalizer
      ((dimg h.diagComm S₀ ⊔ wrY h.diagComm T A Y : Subgroup G) : Set G),
      ∀ m ∈ A ⊓ Subgroup.normalizer
        ((dimg h.diagComm S₀ ⊔ wrY h.diagComm T A Y : Subgroup G) : Set G),
      g * m = m * g :=
    fun g hg m hm => h.comm (Subgroup.mem_inf.mp hg).1 (Subgroup.mem_inf.mp hm).1
  have hCX : C ⊓ (A ⊓ Subgroup.normalizer (J : Set G) ⊓ Subgroup.normalizer (S₀ : Set G)) = ⊥ :=
    le_bot_iff.mp ((inf_le_inf_left C (inf_le_left : A ⊓ Subgroup.normalizer (J : Set G) ⊓
      Subgroup.normalizer (S₀ : Set G) ≤ A ⊓ Subgroup.normalizer (J : Set G))).trans h.CV.le)
  have hW : C ⊔ (A ⊓ Subgroup.normalizer (J : Set G) ⊓ Subgroup.normalizer (S₀ : Set G)) =
      A ⊓ Subgroup.normalizer ((dimg h.diagComm S₀ ⊔ wrY h.diagComm T A Y : Subgroup G) : Set G) := by
    refine le_antisymm (sup_le hCW hXW) ?_
    intro x hx
    obtain ⟨c', hc', v', hv', hxv⟩ := wr_W_decomp h hYS₀ hS₀J hYJ hS₀N hE hnab hx
    rw [hxv]
    exact Subgroup.mul_mem_sup hc' hv'
  refine ⟨C ⊔ B₁, sup_le hCW (hB₁X.trans hXW), ?_, ?_⟩
  · intro b hb t ht
    obtain ⟨c', hc', β, hβ, hcβ⟩ := wr_mem_sup (H := C) (K := B₁)
      (fun c hc β hβ => by
        rw [hWA c (hCW hc) β (hXW (hB₁X hβ)), mul_inv_cancel_right]
        exact hβ) hb
    obtain ⟨d', hd', y'', hy'', hdy⟩ := wr_mem_sup
      (H := dimg h.diagComm S₀) (K := wrY h.diagComm T A Y) hPnorm ht
    obtain ⟨u', hu', hdu'⟩ := (mem_dimg_iff h.diagComm).mp hd'
    subst hcβ
    subst hdy
    subst hdu'
    exact wr_comm_step h hYJ hE hc' (Subgroup.mem_inf.mp (hB₁X hβ)).1 u'.2 (hB₁ β hβ _ hu') rfl
      (fun y hy => hPnorm _ ((mem_dimg_iff h.diagComm).mpr ⟨u', hu', rfl⟩) y hy) hy''
  · rw [wr_relIndex_CX hWA hXW hB₁X hCW hW hCX]
    exact hB₁idx

theorem wreath_rank (h : DiagSetting X T A J C) {D Y : Subgroup G} {𝒟 : Set (Subgroup G)}
    (hJD : JData (actE T A J) J D Y 𝒟) {S₀ : Subgroup G} (hS₀ : S₀ ∈ 𝒟) (n : ℕ)
    (hrank : ∀ S ∈ 𝒟, (∃ v ∈ A ⊓ Subgroup.normalizer (J : Set G) ⊓ Subgroup.normalizer (S : Set G),
        ∃ s ∈ S, v * s * v⁻¹ * s⁻¹ ∉ Y) →
      ∃ B ≤ A ⊓ Subgroup.normalizer (J : Set G) ⊓ Subgroup.normalizer (S : Set G),
        (∀ b ∈ B, ∀ s ∈ S, b * s * b⁻¹ * s⁻¹ ∈ Y) ∧
          B.relIndex (A ⊓ Subgroup.normalizer (J : Set G) ⊓ Subgroup.normalizer (S : Set G)) ≤ 2 ^ n) :
    ∀ S ∈ wrFam h.diagComm T A S₀ Y,
      (∃ a ∈ A ⊓ Subgroup.normalizer (S : Set G), ∃ s ∈ S,
        a * s * a⁻¹ * s⁻¹ ∉ wrY h.diagComm T A Y) →
      ∃ B ≤ A ⊓ Subgroup.normalizer (S : Set G),
        (∀ b ∈ B, ∀ s ∈ S, b * s * b⁻¹ * s⁻¹ ∈ wrY h.diagComm T A Y) ∧
          B.relIndex (A ⊓ Subgroup.normalizer (S : Set G)) ≤ 2 ^ n := by
  intro S hS hA
  rw [wrFam_eq] at hS
  obtain ⟨k, hk, rfl⟩ := hS
  rw [wr_inf_normalizer_conjSub h hk] at hA ⊢
  obtain ⟨a, ha, s, hs, has⟩ := hA
  have hkC : k ∈ Subgroup.centralizer (A : Set G) := (mem_actT_iff.mp hk).2
  have hkA : ∀ x ∈ A, k * x = x * k := fun x hx =>
    (Subgroup.mem_centralizer_iff.mp hkC x hx).symm
  have haA : a ∈ A := (Subgroup.mem_inf.mp ha).1
  have hka : k * a * k⁻¹ = a := by rw [hkA a haA, mul_inv_cancel_right]
  have hka' : k * a⁻¹ * k⁻¹ = a⁻¹ := by rw [hkA a⁻¹ (A.inv_mem haA), mul_inv_cancel_right]
  have hs' : k⁻¹ * s * k ∈ dimg h.diagComm S₀ ⊔ wrY h.diagComm T A Y :=
    (A1b.mem_conjSub_iff).mp hs
  have hnot : a * (k⁻¹ * s * k) * a⁻¹ * (k⁻¹ * s * k)⁻¹ ∉ wrY h.diagComm T A Y := by
    intro hmem
    apply has
    have hc := A1b.mem_conjSub_of_mem (g := k) hmem
    rw [wr_conjSub_wrY h hk] at hc
    have e : k * (a * (k⁻¹ * s * k) * a⁻¹ * (k⁻¹ * s * k)⁻¹) * k⁻¹ = a * s * a⁻¹ * s⁻¹ := by
      have e' : k * (a * (k⁻¹ * s * k) * a⁻¹ * (k⁻¹ * s * k)⁻¹) * k⁻¹ =
          (k * a * k⁻¹) * s * (k * a⁻¹ * k⁻¹) * s⁻¹ := by group
      rw [e', hka, hka']
    rw [← e]
    exact hc
  obtain ⟨B, hB1, hB2, hB3⟩ := wr_rank_core h hJD hS₀ n hrank ha hs' hnot
  refine ⟨B, hB1, fun b hb t ht => ?_, hB3⟩
  have hbA : b ∈ A := (Subgroup.mem_inf.mp (hB1 hb)).1
  have ht' : k⁻¹ * t * k ∈ dimg h.diagComm S₀ ⊔ wrY h.diagComm T A Y :=
    (A1b.mem_conjSub_iff).mp ht
  have hm := A1b.mem_conjSub_of_mem (g := k) (hB2 b hb _ ht')
  rw [wr_conjSub_wrY h hk] at hm
  have hkb : k * b * k⁻¹ = b := by rw [hkA b hbA, mul_inv_cancel_right]
  have hkb' : k * b⁻¹ * k⁻¹ = b⁻¹ := by rw [hkA b⁻¹ (A.inv_mem hbA), mul_inv_cancel_right]
  have e : k * (b * (k⁻¹ * t * k) * b⁻¹ * (k⁻¹ * t * k)⁻¹) * k⁻¹ = b * t * b⁻¹ * t⁻¹ := by
    have e' : k * (b * (k⁻¹ * t * k) * b⁻¹ * (k⁻¹ * t * k)⁻¹) * k⁻¹ =
        (k * b * k⁻¹) * t * (k * b⁻¹ * k⁻¹) * t⁻¹ := by group
    rw [e', hkb, hkb']
  rw [← e]
  exact hm

end CFSG.Quasithin.RonanE111
