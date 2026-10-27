module

public import CFSG.RankThree.GF2n.Tim79a34C8Base
public import CFSG.RankThree.GF2n.Tim79a34StrothCasesB
public import CFSG.RankThree.GF2n.Tim79a34C8Group

public section

namespace CFSG.RankThree.GF2n.Tim79a

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Timmesfeld.ARS CFSG.Timmesfeld.Transvection
  CFSG.Timmesfeld.Transvection.ModelRank CFSG.LieType.Universal.Symplectic
open CFSG.LargeExtraspecial.Timmesfeld (Qa IsExtraspecial2 HasWidth)
open scoped commutatorElement Matrix

section C8Cfg

variable {G : Type} [Group G] [Finite G] {M V Q P H : Subgroup G} {n : ℕ}
    {Φ : ↥(StatedSp n (GaloisField 2 1)) ≃* Xbar V H}
    {ψ : (Fin n ⊕ Fin n → GaloisField 2 1) ≃+ Additive ↥(wOf V H)}
    {a : Fin n ⊕ Fin n → GaloisField 2 1} {T : Subgroup ↥(StatedSp n (GaloisField 2 1))}

theorem c8_theta_dichotomy (h11a : Lemma11aStatement) (cfg : QPCfg M V Q P H Φ ψ a T)
    {b : Fin n ⊕ Fin n → GaloisField 2 1} (hb : CaseM.spForm a b = 1) {ρ : G}
    (hρP : ∀ p ∈ P, ρ * p * ρ⁻¹ ∈ P) (hρa : ρ * c8W ψ a = c8W ψ a * ρ)
    (hMN : ∀ x ∈ Subgroup.centralizer ({c8W ψ a} : Set G), ∀ y ∈ P, x * y * x⁻¹ ∈ P)
    (hcomm : ∀ x ∈ xOf V H ⊓ Subgroup.centralizer ({c8W ψ a} : Set G),
      ∀ y ∈ xOf V H ⊓ Subgroup.centralizer ({c8W ψ a} : Set G),
      ρ * ⁅x, y⁆ * ρ⁻¹ * ⁅x, y⁆⁻¹ ∈ P) :
    (∀ u, CaseM.spForm a u = 0 → C8Cong a (c8R cfg b ρ (c8W ψ u)) 0) ∨
    (∀ u, CaseM.spForm a u = 0 → C8Cong a (c8R cfg b ρ (c8W ψ u)) u) := by
  have hn : 3 ≤ n := cfg.three
  have hWP : ∀ u, CaseM.spForm a u = 0 → c8W ψ u ∈ P := fun u hu =>
    ((c8_h11a h11a cfg).1 u).mpr hu
  refine c8_schur hn c8_card_two cfg.ne (fun u => c8R cfg b ρ (c8W ψ u)) ?_ ?_ ?_ ?_
  · intro u hu
    exact c8R_perp h11a cfg hb (hρP _ (hWP u hu))
  · intro u u' hu hu'
    rw [c8W_add]
    exact c8R_mul h11a cfg hb (hρP _ (hWP u hu)) (hρP _ (hWP u' hu'))
  · have h1 : ρ * c8W ψ a * ρ⁻¹ = c8W ψ a := by
      rw [hρa]
      group
    show C8Cong a (c8Kvec cfg b (ρ * c8W ψ a * ρ⁻¹)) 0
    rw [h1, c8Kvec_W cfg b (c8W_mem ψ a)]
    exact C8Cong.refl a 0
  · intro x y hx hy hxy u hu
    obtain ⟨x₁, hx₁, x₂, hx₂, hmat⟩ := c8_exists_gamma cfg hx hy hxy
    set r := ⁅x₁, x₂⁆ with hr
    have hx₁X : x₁ ∈ xOf V H := (Subgroup.mem_inf.mp hx₁).1
    have hx₂X : x₂ ∈ xOf V H := (Subgroup.mem_inf.mp hx₂).1
    have hrX : r ∈ xOf V H := by
      rw [hr, commutatorElement_def]
      exact (xOf V H).mul_mem ((xOf V H).mul_mem ((xOf V H).mul_mem hx₁X hx₂X)
        ((xOf V H).inv_mem hx₁X)) ((xOf V H).inv_mem hx₂X)
    have hrc : r ∈ Subgroup.centralizer ({c8W ψ a} : Set G) := by
      have hc₁ := (Subgroup.mem_inf.mp hx₁).2
      have hc₂ := (Subgroup.mem_inf.mp hx₂).2
      rw [hr, commutatorElement_def]
      exact (Subgroup.centralizer _).mul_mem ((Subgroup.centralizer _).mul_mem
        ((Subgroup.centralizer _).mul_mem hc₁ hc₂) ((Subgroup.centralizer _).inv_mem hc₁))
        ((Subgroup.centralizer _).inv_mem hc₂)
    have hra : SpExtras.mat n (GaloisField 2 1) (c8E cfg r) *ᵥ a = a := by
      refine c8E_fix_a cfg hrX ?_
      have := Subgroup.mem_centralizer_iff.mp hrc (c8W ψ a) (Set.mem_singleton _)
      exact this.symm
    have hrP : ∀ y ∈ P, r * y * r⁻¹ ∈ P :=
      c8_comm_normalizes (K := Subgroup.centralizer ({c8W ψ a} : Set G)) hMN
        (Subgroup.mem_inf.mp hx₁).2 (Subgroup.mem_inf.mp hx₂).2
    have hW : c8W ψ ((CaseM.spTrans x 1 * CaseM.spTrans y 1) *ᵥ u) = r * c8W ψ u * r⁻¹ := by
      rw [c8E_conj cfg hrX u, hmat]
    show C8Cong a (c8Kvec cfg b (ρ * c8W ψ ((CaseM.spTrans x 1 * CaseM.spTrans y 1) *ᵥ u) * ρ⁻¹))
      ((CaseM.spTrans x 1 * CaseM.spTrans y 1) *ᵥ c8Kvec cfg b (ρ * c8W ψ u * ρ⁻¹))
    rw [hW, ← hmat]
    exact c8R_conj h11a cfg hb (hρP _ (hWP u hu)) hrX hra hrP (hcomm x₁ hx₁ x₂ hx₂)


theorem c8_conj_W (cfg : QPCfg M V Q P H Φ ψ a T) {x w : G} (hx : x ∈ xOf V H)
    (hw : w ∈ wOf V H) : x * w * x⁻¹ ∈ wOf V H :=
  (Subgroup.mem_normalizer_iff.mp (H_le_normalizer_wOf V H
    (xOf_le_H cfg.hyp.setup.mc.toMinCex.V_le_H hx)) w).mp hw

theorem c8_mem_PW_iff (h11a : Lemma11aStatement) (cfg : QPCfg M V Q P H Φ ψ a T) {f : G} :
    f ∈ P ⊓ wOf V H ↔ ∃ u, CaseM.spForm a u = 0 ∧ f = c8W ψ u := by
  constructor
  · intro hf
    obtain ⟨hfP, hfW⟩ := Subgroup.mem_inf.mp hf
    obtain ⟨u, rfl⟩ := c8W_surj ψ hfW
    exact ⟨u, ((c8_h11a h11a cfg).1 u).mp hfP, rfl⟩
  · rintro ⟨u, hu, rfl⟩
    exact Subgroup.mem_inf.mpr ⟨((c8_h11a h11a cfg).1 u).mpr hu, c8W_mem ψ u⟩

theorem c8_exists_P_of_mem_spRad (h11a : Lemma11aStatement) (cfg : QPCfg M V Q P H Φ ψ a T)
    {g : ↥(StatedSp n (GaloisField 2 1))} (hg : g ∈ spRad a) : ∃ p ∈ P, c8E cfg p = g := by
  have hVH := cfg.hyp.setup.mc.toMinCex.V_le_H
  have hmem : Φ g ∈ Rbar V H P := by
    rw [(c8_h11a h11a cfg).2.1]
    exact Subgroup.mem_map_of_mem Φ.toMonoidHom hg
  obtain ⟨x, hxP, hxg⟩ := mem_barOf_iff.mp (mem_Rbar.mp hmem)
  have hxX : (x : G) ∈ xOf V H := by
    rw [(c8_h11a h11a cfg).2.2.1]
    exact x.2
  refine ⟨(x : G), hxP, ?_⟩
  rw [c8E_of_mem cfg hxX]
  have : xToXbar hVH ⟨(x : G), hxX⟩ = Φ g := Subtype.ext (by rw [coe_xToXbar]; exact hxg)
  rw [this, MulEquiv.symm_apply_apply]


theorem c8_case1 (h11a : Lemma11aStatement) (cfg : QPCfg M V Q P H Φ ψ a T)
    {b : Fin n ⊕ Fin n → GaloisField 2 1} (hb : CaseM.spForm a b = 1) {ρ : G}
    (hρP : ∀ p ∈ P, ρ * p * ρ⁻¹ ∈ P) (hρa : ρ * c8W ψ a = c8W ψ a * ρ) (hρ3 : ρ ^ 3 = 1)
    (hMN : ∀ x ∈ Subgroup.centralizer ({c8W ψ a} : Set G), ∀ y ∈ P, x * y * x⁻¹ ∈ P)
    (hcomm : ∀ x ∈ xOf V H ⊓ Subgroup.centralizer ({c8W ψ a} : Set G),
      ∀ y ∈ xOf V H ⊓ Subgroup.centralizer ({c8W ψ a} : Set G),
      ρ * ⁅x, y⁆ * ρ⁻¹ * ⁅x, y⁆⁻¹ ∈ P)
    (hid : ∀ u, CaseM.spForm a u = 0 → C8Cong a (c8R cfg b ρ (c8W ψ u)) u) : False := by
  have hVH := cfg.hyp.setup.mc.toMinCex.V_le_H
  let εh : ↥(xOf V H) →* ↥(StatedSp n (GaloisField 2 1)) :=
    Φ.symm.toMonoidHom.comp (xToXbar hVH)
  have hεh : ∀ (y : G) (hy : y ∈ xOf V H), εh ⟨y, hy⟩ = c8E cfg y := fun y hy =>
    (c8E_of_mem cfg hy).symm
  let Fρ : Subgroup G := (P ⊓ wOf V H).map (MulAut.conj ρ).toMonoidHom
  have hFρ : ∀ y, y ∈ Fρ ↔ ∃ f ∈ P ⊓ wOf V H, ρ * f * ρ⁻¹ = y := by
    intro y
    simp only [Fρ, Subgroup.mem_map]
    simp [MulAut.conj_apply]
  have hFρP : ∀ y ∈ Fρ, y ∈ P := by
    intro y hy
    obtain ⟨f, hf, rfl⟩ := (hFρ y).mp hy
    exact hρP f (Subgroup.mem_inf.mp hf).1
  let S : Subgroup ↥(StatedSp n (GaloisField 2 1)) := (Fρ.subgroupOf (xOf V H)).map εh
  have hS_mem : ∀ g, g ∈ S ↔ ∃ y : ↥(xOf V H), (y : G) ∈ Fρ ∧ εh y = g := by
    intro g
    simp only [S, Subgroup.mem_map, Subgroup.mem_subgroupOf]
  have hSsp : S ≤ spRad a := by
    intro g hg
    obtain ⟨y, hyF, rfl⟩ := (hS_mem g).mp hg
    rw [hεh (y : G) y.2]
    exact c8E_mem_spRad h11a cfg (hFρP _ hyF)
  have hinf : S ⊓ T = ⊥ := by
    rw [eq_bot_iff]
    intro g hg
    obtain ⟨hgS, hgT⟩ := Subgroup.mem_inf.mp hg
    obtain ⟨y, hyF, hyg⟩ := (hS_mem g).mp hgS
    obtain ⟨f, hf, hfy⟩ := (hFρ y).mp hyF
    obtain ⟨u, hu, rfl⟩ := (c8_mem_PW_iff h11a cfg).mp hf
    obtain ⟨c, hc⟩ := (cfg.trans.1 g).1 hgT
    obtain ⟨d, hd⟩ := hid u hu
    have hyE : c8E cfg (y : G) = g := by
      rw [← hεh (y : G) y.2]
      exact hyg
    have hvec : c8Kvec cfg b (y : G) = c • a := by
      unfold c8Kvec
      rw [hyE, hc, CFSG.Timmesfeld.Transvection.ModelRank.spTrans_mulVec, hb, mul_one]
      have h2 := two_smul_vec_eq_zero b
      linear_combination (norm := module) (1 : GaloisField 2 1) • h2
    have hdvec : c8Kvec cfg b (y : G) = u + d • a := by
      rw [← hfy]
      exact hd
    have hu_eq : u = (c - d) • a := by
      have h3 : u + d • a = c • a := hdvec.symm.trans hvec
      linear_combination (norm := module) h3
    have hyW : (y : G) ∈ wOf V H := by
      have hcd : c - d = 0 ∨ c - d = 1 := c8_zero_or_one c8_card_two (c - d)
      rcases hcd with h0 | h1
      · have : (y : G) = 1 := by
          rw [← hfy, hu_eq, h0, zero_smul, c8W_zero]
          group
        rw [this]
        exact (wOf V H).one_mem
      · have : (y : G) = c8W ψ a := by
          rw [← hfy, hu_eq, h1, one_smul, mul_inv_eq_iff_eq_mul]
          exact hρa
        rw [this]
        exact c8W_mem ψ a
    have hg1 : g = 1 := by
      rw [← hyE]
      exact (c8E_eq_one_iff cfg y.2).mpr hyW
    rw [hg1]
    exact (⊥ : Subgroup _).one_mem
  have hsup : S ⊔ T = spRad a := by
    apply le_antisymm
    · exact sup_le hSsp (le_spRad_of_isTransGroup cfg.trans)
    · intro g hg
      obtain ⟨p, hpP, hpg⟩ := c8_exists_P_of_mem_spRad h11a cfg hg
      have hgfix : SpExtras.mat n (GaloisField 2 1) g *ᵥ a = a := hg.1
      have hu : CaseM.spForm a (c8Kvec cfg b p) = 0 :=
        c8Kvec_perp cfg hb (by rw [hpg]; exact hgfix)
      have hfPW : c8W ψ (c8Kvec cfg b p) ∈ P ⊓ wOf V H :=
        (c8_mem_PW_iff h11a cfg).mpr ⟨_, hu, rfl⟩
      have hyF : ρ * c8W ψ (c8Kvec cfg b p) * ρ⁻¹ ∈ Fρ := (hFρ _).mpr ⟨_, hfPW, rfl⟩
      have hyP := hFρP _ hyF
      have hyX := c8_P_le_X h11a cfg hyP
      obtain ⟨d, hd⟩ := hid _ hu
      have hgyS : c8E cfg (ρ * c8W ψ (c8Kvec cfg b p) * ρ⁻¹) ∈ S := by
        rw [← hεh _ hyX]
        exact (hS_mem _).mpr ⟨⟨_, hyX⟩, hyF, rfl⟩
      set gy := c8E cfg (ρ * c8W ψ (c8Kvec cfg b p) * ρ⁻¹) with hgy
      have hgyr : gy ∈ spRad a := c8E_mem_spRad h11a cfg hyP
      have hgb : SpExtras.mat n (GaloisField 2 1) g *ᵥ b = c8Kvec cfg b p + b := by
        have h2 := two_smul_vec_eq_zero b
        have h3 : SpExtras.mat n (GaloisField 2 1) g *ᵥ b + b = c8Kvec cfg b p := by
          unfold c8Kvec
          rw [hpg]
        linear_combination (norm := module) h3 + (-1 : GaloisField 2 1) • h2
      have hgyb : SpExtras.mat n (GaloisField 2 1) gy *ᵥ b =
          c8Kvec cfg b p + d • a + b := by
        have h2 := two_smul_vec_eq_zero b
        have h3 : SpExtras.mat n (GaloisField 2 1) gy *ᵥ b + b = c8Kvec cfg b p + d • a := hd
        linear_combination (norm := module) h3 + (-1 : GaloisField 2 1) • h2
      have hgyia : SpExtras.mat n (GaloisField 2 1) gy⁻¹ *ᵥ a = a := (inv_mem hgyr).1
      have htb : SpExtras.mat n (GaloisField 2 1) (gy⁻¹ * g) *ᵥ b = b + d • a := by
        rw [map_mul, ← Matrix.mulVec_mulVec, hgb]
        have h4 : c8Kvec cfg b p + b = SpExtras.mat n (GaloisField 2 1) gy *ᵥ b + d • a := by
          rw [hgyb]
          linear_combination (norm := module) (-1 : GaloisField 2 1) •
            two_smul_vec_eq_zero (d • a)
        rw [h4, Matrix.mulVec_add, mat_inv_mulVec_mat_mulVec, Matrix.mulVec_smul, hgyia]
      have htT : gy⁻¹ * g ∈ T :=
        c8_mem_trans_of_apply cfg.ne hb (mul_mem (inv_mem hgyr) hg) cfg.trans ⟨d, htb⟩
      have : g = gy * (gy⁻¹ * g) := by group
      rw [this]
      exact Subgroup.mul_mem_sup hgyS htT
  have hinv : ∀ x y : Fin n ⊕ Fin n → GaloisField 2 1, CaseM.spForm a x = 0 →
      CaseM.spForm a y = 0 → CaseM.spForm x y = 1 →
      ∀ g : ↥(StatedSp n (GaloisField 2 1)),
        SpExtras.mat n (GaloisField 2 1) g = CaseM.spTrans x 1 * CaseM.spTrans y 1 →
          ∀ s ∈ S, g * s * g⁻¹ ∈ S := by
    intro x y hx hy hxy g hg s hs
    obtain ⟨x₁, hx₁, x₂, hx₂, hmat⟩ := c8_exists_gamma cfg hx hy hxy
    set r := ⁅x₁, x₂⁆ with hr
    have hx₁X : x₁ ∈ xOf V H := (Subgroup.mem_inf.mp hx₁).1
    have hx₂X : x₂ ∈ xOf V H := (Subgroup.mem_inf.mp hx₂).1
    have hrX : r ∈ xOf V H := by
      rw [hr, commutatorElement_def]
      exact (xOf V H).mul_mem ((xOf V H).mul_mem ((xOf V H).mul_mem hx₁X hx₂X)
        ((xOf V H).inv_mem hx₁X)) ((xOf V H).inv_mem hx₂X)
    have hrE : c8E cfg r = g := SpExtras.mat_injective (hmat.trans hg.symm)
    have hrP : ∀ y ∈ P, r * y * r⁻¹ ∈ P :=
      c8_comm_normalizes (K := Subgroup.centralizer ({c8W ψ a} : Set G)) hMN
        (Subgroup.mem_inf.mp hx₁).2 (Subgroup.mem_inf.mp hx₂).2
    have hq : ρ * r * ρ⁻¹ * r⁻¹ ∈ P := hcomm x₁ hx₁ x₂ hx₂
    obtain ⟨y₁, hy₁F, rfl⟩ := (hS_mem s).mp hs
    obtain ⟨f, hf, hfy⟩ := (hFρ _).mp hy₁F
    have hq' : (ρ * (ρ * r * ρ⁻¹ * r⁻¹) * ρ⁻¹) * (ρ * r * ρ⁻¹ * r⁻¹) ∈ P :=
      P.mul_mem (hρP _ hq) hq
    set q' := (ρ * (ρ * r * ρ⁻¹ * r⁻¹) * ρ⁻¹) * (ρ * r * ρ⁻¹ * r⁻¹) with hq'def
    have hρ3' : ρ * ρ * ρ = 1 := by
      rw [← pow_three']
      exact hρ3
    have hρ2 : ρ * ρ = ρ⁻¹ := by
      calc ρ * ρ = (ρ * ρ * ρ) * ρ⁻¹ := by group
        _ = ρ⁻¹ := by rw [hρ3', one_mul]
    have hρ2' : ρ⁻¹ * ρ⁻¹ = ρ := by
      rw [← hρ2]
      calc ρ * ρ * (ρ * ρ) = (ρ * ρ * ρ) * ρ := by group
        _ = ρ := by rw [hρ3', one_mul]
    have hconj : ρ⁻¹ * r * ρ = q' * r := by
      have e : q' * r = ρ * ρ * r * (ρ⁻¹ * ρ⁻¹) := by
        rw [hq'def]
        group
      rw [e, hρ2, hρ2']
    have hfP : f ∈ P := (Subgroup.mem_inf.mp hf).1
    have hfW : f ∈ wOf V H := (Subgroup.mem_inf.mp hf).2
    have hf₂ : q' * (r * f * r⁻¹) * q'⁻¹ ∈ P ⊓ wOf V H := by
      have h1 : r * f * r⁻¹ ∈ P := hrP f hfP
      have h2 : r * f * r⁻¹ ∈ wOf V H := c8_conj_W cfg hrX hfW
      exact Subgroup.mem_inf.mpr ⟨P.mul_mem (P.mul_mem hq' h1) (P.inv_mem hq'),
        c8_conj_W cfg (c8_P_le_X h11a cfg hq') h2⟩
    have e : ρ * (q' * (r * f * r⁻¹) * q'⁻¹) * ρ⁻¹ = r * (ρ * f * ρ⁻¹) * r⁻¹ := by
      have e1 : q' * (r * f * r⁻¹) * q'⁻¹ = (q' * r) * f * (q' * r)⁻¹ := by group
      rw [e1, ← hconj]
      group
    set w : ↥(xOf V H) := ⟨r, hrX⟩ * y₁ * ⟨r, hrX⟩⁻¹ with hw
    have hwG : (w : G) = r * (y₁ : G) * r⁻¹ := rfl
    have hgs : g * εh y₁ * g⁻¹ = εh w := by
      rw [hw, map_mul, map_mul, map_inv, hεh r hrX, hrE]
    rw [hgs]
    refine (hS_mem _).mpr ⟨w, ?_, rfl⟩
    rw [hwG, ← hfy, ← e]
    exact (hFρ _).mpr ⟨_, hf₂, rfl⟩
  exact c8_noInvComp cfg.three c8_card_two cfg.ne cfg.trans hSsp hsup hinf hinv


theorem c8_VF_comm (cfg : QPCfg M V Q P H Φ ψ a T) :
    ∀ s ∈ V, ∀ t ∈ P ⊓ wOf V H, s * t = t * s := fun s hs t ht =>
  cfg.hyp.setup.mc.toMinCex.commute_of_mem_P (Subgroup.mem_inf.mp ht).1 hs

theorem c8Kvec_VF (h11a : Lemma11aStatement) (cfg : QPCfg M V Q P H Φ ψ a T)
    {b : Fin n ⊕ Fin n → GaloisField 2 1} (hb : CaseM.spForm a b = 1) {y : G}
    (hy : y ∈ V ⊔ (P ⊓ wOf V H)) : ∃ c : GaloisField 2 1, c8Kvec cfg b y = c • a := by
  obtain ⟨v, hv, f, hf, rfl⟩ := exists_mul_of_mem_sup (c8_VF_comm cfg) hy
  have hvP : v ∈ P := cfg.hyp.setup.mc.toMinCex.V_le_P hv
  have hfP : f ∈ P := (Subgroup.mem_inf.mp hf).1
  obtain ⟨c₁, hc₁⟩ := c8Kvec_mul h11a cfg hb hvP hfP
  obtain ⟨c₂, hc₂⟩ := c8Kvec_V cfg hb hv
  refine ⟨c₂ + c₁, ?_⟩
  rw [hc₁, hc₂, c8Kvec_W cfg b (Subgroup.mem_inf.mp hf).2, add_smul]
  abel

theorem c8R_wd (h11a : Lemma11aStatement) (cfg : QPCfg M V Q P H Φ ψ a T)
    {b : Fin n ⊕ Fin n → GaloisField 2 1} (hb : CaseM.spForm a b = 1) {ρ : G}
    (hρP : ∀ p ∈ P, ρ * p * ρ⁻¹ ∈ P)
    (hρVF : ∀ y ∈ V ⊔ (P ⊓ wOf V H), ρ * y * ρ⁻¹ ∈ V ⊔ (P ⊓ wOf V H)) {p p' : G}
    (hp : p ∈ P) (hp' : p' ∈ P) (h : C8Cong a (c8Kvec cfg b p) (c8Kvec cfg b p')) :
    C8Cong a (c8R cfg b ρ p) (c8R cfg b ρ p') := by
  have hz : p'⁻¹ * p ∈ P := P.mul_mem (P.inv_mem hp') hp
  obtain ⟨c₁, hc₁⟩ := c8Kvec_mul h11a cfg hb hp' hz
  obtain ⟨c₂, hc₂⟩ := h
  rw [mul_inv_cancel_left] at hc₁
  have hKz : c8Kvec cfg b (p'⁻¹ * p) = (c₂ - c₁) • a := by
    have h3 := hc₁.symm.trans hc₂
    linear_combination (norm := module) h3
  have hzVF : p'⁻¹ * p ∈ V ⊔ (P ⊓ wOf V H) := by
    obtain ⟨v, hv, f, hf, hvf⟩ := c8_mem_VF h11a cfg hb hz ⟨_, hKz⟩
    rw [hvf]
    exact Subgroup.mul_mem_sup hv hf
  obtain ⟨c₃, hc₃⟩ := c8Kvec_VF h11a cfg hb (hρVF _ hzVF)
  obtain ⟨c₄, hc₄⟩ := c8Kvec_mul h11a cfg hb (hρP _ hp') (hρP _ hz)
  refine ⟨c₃ + c₄, ?_⟩
  unfold c8R
  have e : ρ * p * ρ⁻¹ = (ρ * p' * ρ⁻¹) * (ρ * (p'⁻¹ * p) * ρ⁻¹) := by group
  rw [e, hc₄, hc₃, add_smul]
  abel


theorem c8_gamma_data (cfg : QPCfg M V Q P H Φ ψ a T)
    (hMN : ∀ x ∈ Subgroup.centralizer ({c8W ψ a} : Set G), ∀ y ∈ P, x * y * x⁻¹ ∈ P)
    {x y : Fin n ⊕ Fin n → GaloisField 2 1} (hx : CaseM.spForm a x = 0)
    (hy : CaseM.spForm a y = 0) (hxy : CaseM.spForm x y = 1) :
    ∃ x₁ ∈ xOf V H ⊓ Subgroup.centralizer ({c8W ψ a} : Set G),
      ∃ x₂ ∈ xOf V H ⊓ Subgroup.centralizer ({c8W ψ a} : Set G),
      ⁅x₁, x₂⁆ ∈ xOf V H ∧
      SpExtras.mat n (GaloisField 2 1) (c8E cfg ⁅x₁, x₂⁆) =
        CaseM.spTrans x 1 * CaseM.spTrans y 1 ∧
      SpExtras.mat n (GaloisField 2 1) (c8E cfg ⁅x₁, x₂⁆) *ᵥ a = a ∧
      (∀ z ∈ P, ⁅x₁, x₂⁆ * z * ⁅x₁, x₂⁆⁻¹ ∈ P) := by
  obtain ⟨x₁, hx₁, x₂, hx₂, hmat⟩ := c8_exists_gamma cfg hx hy hxy
  have hx₁X : x₁ ∈ xOf V H := (Subgroup.mem_inf.mp hx₁).1
  have hx₂X : x₂ ∈ xOf V H := (Subgroup.mem_inf.mp hx₂).1
  have hrX : ⁅x₁, x₂⁆ ∈ xOf V H := by
    rw [commutatorElement_def]
    exact (xOf V H).mul_mem ((xOf V H).mul_mem ((xOf V H).mul_mem hx₁X hx₂X)
      ((xOf V H).inv_mem hx₁X)) ((xOf V H).inv_mem hx₂X)
  have hrc : ⁅x₁, x₂⁆ ∈ Subgroup.centralizer ({c8W ψ a} : Set G) := by
    have hc₁ := (Subgroup.mem_inf.mp hx₁).2
    have hc₂ := (Subgroup.mem_inf.mp hx₂).2
    rw [commutatorElement_def]
    exact (Subgroup.centralizer _).mul_mem ((Subgroup.centralizer _).mul_mem
      ((Subgroup.centralizer _).mul_mem hc₁ hc₂) ((Subgroup.centralizer _).inv_mem hc₁))
      ((Subgroup.centralizer _).inv_mem hc₂)
  refine ⟨x₁, hx₁, x₂, hx₂, hrX, hmat, ?_, ?_⟩
  · refine c8E_fix_a cfg hrX ?_
    exact (Subgroup.mem_centralizer_iff.mp hrc (c8W ψ a) (Set.mem_singleton _)).symm
  · exact c8_comm_normalizes (K := Subgroup.centralizer ({c8W ψ a} : Set G)) hMN
      (Subgroup.mem_inf.mp hx₁).2 (Subgroup.mem_inf.mp hx₂).2

theorem c8_conj_inv_P {ρ : G} (hρP : ∀ p ∈ P, ρ * p * ρ⁻¹ ∈ P) (hρ3 : ρ ^ 3 = 1) :
    ∀ p ∈ P, ρ⁻¹ * p * ρ ∈ P := by
  intro p hp
  have hρ3' : ρ * ρ * ρ = 1 := by
    rw [← pow_three']
    exact hρ3
  have e : ρ⁻¹ * p * ρ = ρ * (ρ * p * ρ⁻¹) * ρ⁻¹ := by
    have e1 : ρ⁻¹ = ρ * ρ := by
      calc ρ⁻¹ = ρ⁻¹ * (ρ * ρ * ρ) := by rw [hρ3', mul_one]
        _ = ρ * ρ := by group
    calc ρ⁻¹ * p * ρ = ρ⁻¹ * p * ρ * (ρ * ρ * ρ) := by rw [hρ3', mul_one]
      _ = ρ * (ρ * p * ρ⁻¹) * ρ⁻¹ := by
        rw [e1]
        group
  rw [e]
  exact hρP _ (hρP _ hp)


theorem c8_case2 (h11a : Lemma11aStatement) (h11b : Lemma11bStatement)
    (h11c : Lemma11cStatement) (cfg : QPCfg M V Q P H Φ ψ a T)
    {b : Fin n ⊕ Fin n → GaloisField 2 1} (hb : CaseM.spForm a b = 1) {ρ : G}
    (hρP : ∀ p ∈ P, ρ * p * ρ⁻¹ ∈ P) (hρ3 : ρ ^ 3 = 1)
    (hρV : ∀ v ∈ V, ρ * v * ρ⁻¹ = v)
    (hMN : ∀ x ∈ Subgroup.centralizer ({c8W ψ a} : Set G), ∀ y ∈ P, x * y * x⁻¹ ∈ P)
    (hcomm : ∀ x ∈ xOf V H ⊓ Subgroup.centralizer ({c8W ψ a} : Set G),
      ∀ y ∈ xOf V H ⊓ Subgroup.centralizer ({c8W ψ a} : Set G),
      ρ * ⁅x, y⁆ * ρ⁻¹ * ⁅x, y⁆⁻¹ ∈ P)
    (hzero : ∀ u, CaseM.spForm a u = 0 → C8Cong a (c8R cfg b ρ (c8W ψ u)) 0) :
    ∀ p ∈ P, ρ * p * ρ⁻¹ * p⁻¹ ∈ V := by
  have hc : MinCex M V Q P H := cfg.hyp.setup.mc.toMinCex
  have hn : 3 ≤ n := cfg.three
  have h2a : ∀ f ∈ P ⊓ wOf V H, ρ * f * ρ⁻¹ ∈ V ⊔ (P ⊓ wOf V H) := by
    intro f hf
    obtain ⟨u, hu, rfl⟩ := (c8_mem_PW_iff h11a cfg).mp hf
    obtain ⟨c, hcc⟩ := hzero u hu
    have hfP := (Subgroup.mem_inf.mp hf).1
    have hcc' : c8Kvec cfg b (ρ * c8W ψ u * ρ⁻¹) = c • a := by
      rw [zero_add] at hcc
      exact hcc
    obtain ⟨v, hv, f', hf', hvf⟩ := c8_mem_VF h11a cfg hb (hρP _ hfP) ⟨c, hcc'⟩
    rw [hvf]
    exact Subgroup.mul_mem_sup hv hf'
  have h2b : ∀ y ∈ V ⊔ (P ⊓ wOf V H), ρ * y * ρ⁻¹ ∈ V ⊔ (P ⊓ wOf V H) := by
    intro y hy
    obtain ⟨v, hv, f, hf, rfl⟩ := exists_mul_of_mem_sup (c8_VF_comm cfg) hy
    have e : ρ * (v * f) * ρ⁻¹ = v * (ρ * f * ρ⁻¹) := by
      have := hρV v hv
      calc ρ * (v * f) * ρ⁻¹ = (ρ * v * ρ⁻¹) * (ρ * f * ρ⁻¹) := by group
        _ = v * (ρ * f * ρ⁻¹) := by rw [this]
    rw [e]
    exact (V ⊔ (P ⊓ wOf V H)).mul_mem (Subgroup.mem_sup_left hv) (h2a f hf)
  have hsurj : ∀ w, CaseM.spForm a w = 0 → ∃ p ∈ P, c8Kvec cfg b p = w := by
    intro w hw
    have h11c' := (h11c G M V Q P H cfg.hyp cfg.centre cfg.iw Φ ψ cfg.nat a T cfg.ne
      cfg.trans cfg.point b hb).2
    obtain ⟨p, hpP, hp⟩ := h11c' (c8W ψ w) ((c8_mem_PW_iff h11a cfg).mpr ⟨w, hw, rfl⟩)
    refine ⟨p, hpP, ?_⟩
    have hpX := c8_P_le_X h11a cfg hpP
    have h3 : ⁅p, c8W ψ b⁆ = c8W ψ w := hp
    rw [c8_comm_bG cfg b hpX] at h3
    exact c8W_inj ψ h3
  have hex : ∀ w : Fin n ⊕ Fin n → GaloisField 2 1,
      ∃ p : G, CaseM.spForm a w = 0 → (p ∈ P ∧ c8Kvec cfg b p = w) := by
    intro w
    by_cases hw : CaseM.spForm a w = 0
    · obtain ⟨p, hp1, hp2⟩ := hsurj w hw
      exact ⟨p, fun _ => ⟨hp1, hp2⟩⟩
    · exact ⟨1, fun h => absurd h hw⟩
  choose π hπ using hex
  have hwd : ∀ {p p' : G}, p ∈ P → p' ∈ P →
      C8Cong a (c8Kvec cfg b p) (c8Kvec cfg b p') →
      C8Cong a (c8R cfg b ρ p) (c8R cfg b ρ p') := fun {p p'} hp hp' h =>
    c8R_wd h11a cfg hb hρP h2b hp hp' h
  have hKperp : ∀ p ∈ P, CaseM.spForm a (c8Kvec cfg b p) = 0 := fun p hp =>
    c8Kvec_perp cfg hb (c8E_mem_spRad h11a cfg hp).1
  have hdich : (∀ u, CaseM.spForm a u = 0 → C8Cong a (c8R cfg b ρ (π u)) 0) ∨
      (∀ u, CaseM.spForm a u = 0 → C8Cong a (c8R cfg b ρ (π u)) u) := by
    refine c8_schur hn c8_card_two cfg.ne (fun u => c8R cfg b ρ (π u)) ?_ ?_ ?_ ?_
    · intro u hu
      exact c8R_perp h11a cfg hb (hρP _ (hπ u hu).1)
    · intro u u' hu hu'
      have h1 := hπ u hu
      have h2 := hπ u' hu'
      have h3 := hπ (u + u') (by rw [spForm_add_right, hu, hu', add_zero])
      obtain ⟨c, hc'⟩ := c8Kvec_mul h11a cfg hb h1.1 h2.1
      have hcong : C8Cong a (c8Kvec cfg b (π (u + u'))) (c8Kvec cfg b (π u * π u')) := by
        rw [h3.2, hc', h1.2, h2.2]
        exact C8Cong.symm ⟨c, rfl⟩
      exact (hwd h3.1 (P.mul_mem h1.1 h2.1) hcong).trans
        (c8R_mul h11a cfg hb (hρP _ h1.1) (hρP _ h2.1))
    · have h1 := hπ a (CaseM.spForm_self a)
      have hc1 : C8Cong a (c8Kvec cfg b (π a)) (c8Kvec cfg b 1) := by
        rw [h1.2, c8Kvec_one]
        exact ⟨1, by rw [zero_add, one_smul]⟩
      have h6 := hwd h1.1 P.one_mem hc1
      have h7 : c8R cfg b ρ 1 = 0 := by
        unfold c8R
        rw [mul_one, mul_inv_cancel, c8Kvec_one]
      rw [h7] at h6
      exact h6
    · intro x y hx hy hxy u hu
      obtain ⟨x₁, hx₁, x₂, hx₂, hrX, hmat, hra, hrP⟩ := c8_gamma_data cfg hMN hx hy hxy
      have hu' : CaseM.spForm a ((CaseM.spTrans x 1 * CaseM.spTrans y 1) *ᵥ u) = 0 := by
        rw [← hmat]
        have h := spForm_mat_mulVec (c8E cfg ⁅x₁, x₂⁆) a u
        rw [hra] at h
        rw [h]
        exact hu
      have h1 := hπ u hu
      have h2 := hπ _ hu'
      obtain ⟨c, hc'⟩ := c8Kvec_conj h11a cfg hb hrX hra h1.1
      have hcong : C8Cong a (c8Kvec cfg b (π ((CaseM.spTrans x 1 * CaseM.spTrans y 1) *ᵥ u)))
          (c8Kvec cfg b (⁅x₁, x₂⁆ * π u * ⁅x₁, x₂⁆⁻¹)) := by
        rw [h2.2, hc', h1.2, hmat]
        exact C8Cong.symm ⟨c, rfl⟩
      have hq := hcomm x₁ hx₁ x₂ hx₂
      have h3 := hwd h2.1 (hrP _ h1.1) hcong
      have h4 := c8R_conj h11a cfg hb (hρP _ h1.1) hrX hra hrP hq
      rw [hmat] at h4
      exact h3.trans h4
  rcases hdich with hA | hB
  · exfalso
    have hall : ∀ p ∈ P, C8Cong a (c8R cfg b ρ p) 0 := by
      intro p hp
      have hw := hKperp p hp
      have h1 := hπ (c8Kvec cfg b p) hw
      have h2 : C8Cong a (c8Kvec cfg b p) (c8Kvec cfg b (π (c8Kvec cfg b p))) := by
        rw [h1.2]
        exact C8Cong.refl a _
      exact (hwd hp h1.1 h2).trans (hA _ hw)
    obtain ⟨w₀, -, hw₀a, hw₀⟩ := exists_perp_vec_not_smul (by omega : 2 ≤ n) cfg.ne
    obtain ⟨p₀, hp₀, hp₀w⟩ := hsurj w₀ hw₀a
    have hp1 : ρ⁻¹ * p₀ * ρ ∈ P := c8_conj_inv_P hρP hρ3 p₀ hp₀
    have h5 := hall _ hp1
    have e : ρ * (ρ⁻¹ * p₀ * ρ) * ρ⁻¹ = p₀ := by group
    unfold c8R at h5
    rw [e, hp₀w] at h5
    obtain ⟨c, hcc⟩ := h5
    exact hw₀ c (by rw [hcc, zero_add])
  · have hall : ∀ p ∈ P, C8Cong a (c8R cfg b ρ p) (c8Kvec cfg b p) := by
      intro p hp
      have hw := hKperp p hp
      have h1 := hπ (c8Kvec cfg b p) hw
      have h2 : C8Cong a (c8Kvec cfg b p) (c8Kvec cfg b (π (c8Kvec cfg b p))) := by
        rw [h1.2]
        exact C8Cong.refl a _
      exact (hwd hp h1.1 h2).trans (hB _ hw)
    have hδVF : ∀ p ∈ P, ρ * p * ρ⁻¹ * p⁻¹ ∈ V ⊔ (P ⊓ wOf V H) := by
      intro p hp
      have hδP : ρ * p * ρ⁻¹ * p⁻¹ ∈ P := P.mul_mem (hρP p hp) (P.inv_mem hp)
      obtain ⟨c, hcc⟩ := c8Kvec_mul h11a cfg hb hδP hp
      obtain ⟨e, he⟩ := hall p hp
      have e1 : ρ * p * ρ⁻¹ * p⁻¹ * p = ρ * p * ρ⁻¹ := by group
      rw [e1] at hcc
      have hKδ : c8Kvec cfg b (ρ * p * ρ⁻¹ * p⁻¹) = (e - c) • a := by
        have he' : c8Kvec cfg b (ρ * p * ρ⁻¹) = c8Kvec cfg b p + e • a := he
        linear_combination (norm := module) hcc.symm + he'
      obtain ⟨v, hv, f, hf, hvf⟩ := c8_mem_VF h11a cfg hb hδP ⟨_, hKδ⟩
      rw [hvf]
      exact Subgroup.mul_mem_sup hv hf
    have hZP : ∀ z ∈ V, ∀ p ∈ P, z * p = p * z := fun z hz p hp => hc.commute_of_mem_P hp hz
    have hPP : ∀ p ∈ P, ∀ q ∈ P, ⁅p, q⁆ ∈ V := fun p hp q hq =>
      hc.commutator_mem_V_of_mem_P hp hq
    have hNP : V ⊔ (P ⊓ wOf V H) ≤ P := sup_le hc.V_le_P inf_le_left
    have hZN : V ≤ V ⊔ (P ⊓ wOf V H) := le_sup_left
    have hFcomm : ∀ f₁ ∈ P ⊓ wOf V H, ∀ f₂ ∈ P ⊓ wOf V H, f₁ * f₂ = f₂ * f₁ := by
      intro f₁ hf₁ f₂ hf₂
      obtain ⟨u₁, -, rfl⟩ := (c8_mem_PW_iff h11a cfg).mp hf₁
      obtain ⟨u₂, -, rfl⟩ := (c8_mem_PW_iff h11a cfg).mp hf₂
      exact c8W_comm ψ u₁ u₂
    have hFsq : ∀ f ∈ P ⊓ wOf V H, f * f = 1 := by
      intro f hf
      obtain ⟨u, -, rfl⟩ := (c8_mem_PW_iff h11a cfg).mp hf
      exact c8W_sq ψ u
    have hVP : ∀ v ∈ V, v ∈ P := fun v hv => hc.V_le_P hv
    have hNab : ∀ x ∈ V ⊔ (P ⊓ wOf V H), ∀ y ∈ V ⊔ (P ⊓ wOf V H), x * y = y * x := by
      intro x hx y hy
      obtain ⟨v₁, hv₁, f₁, hf₁, rfl⟩ := exists_mul_of_mem_sup (c8_VF_comm cfg) hx
      obtain ⟨v₂, hv₂, f₂, hf₂, rfl⟩ := exists_mul_of_mem_sup (c8_VF_comm cfg) hy
      have c11 : Commute v₁ v₂ := (hZP v₁ hv₁ v₂ (hVP v₂ hv₂) : v₁ * v₂ = v₂ * v₁)
      have c12 : Commute v₁ f₂ := (hZP v₁ hv₁ f₂ (Subgroup.mem_inf.mp hf₂).1 : _)
      have c21 : Commute f₁ v₂ := ((hZP v₂ hv₂ f₁ (Subgroup.mem_inf.mp hf₁).1 : _)).symm
      have c22 : Commute f₁ f₂ := hFcomm f₁ hf₁ f₂ hf₂
      exact ((c11.mul_right c12).mul_left (c21.mul_right c22))
    have hNsq : ∀ x ∈ V ⊔ (P ⊓ wOf V H), x * x = 1 := by
      intro x hx
      obtain ⟨v, hv, f, hf, rfl⟩ := exists_mul_of_mem_sup (c8_VF_comm cfg) hx
      have hvf : f * v = v * f := (c8_VF_comm cfg v hv f hf).symm
      have hv2 : v * v = 1 := by
        have := hc.elemAb.2 v hv
        rwa [pow_two] at this
      calc v * f * (v * f) = v * (f * v) * f := by group
        _ = v * (v * f) * f := by rw [hvf]
        _ = (v * v) * (f * f) := by group
        _ = 1 := by rw [hv2, hFsq f hf, one_mul]
    have hδN : ∀ f ∈ V ⊔ (P ⊓ wOf V H), ρ * f * ρ⁻¹ * f⁻¹ ∈ V := by
      intro f hf
      have hfd := c8_dual hZP hPP hNP hZN hNab hNsq hρP h2b hρV hρ3 hδVF f hf
      have hfP : f ∈ P := hNP hf
      have hδP : ρ * f * ρ⁻¹ * f⁻¹ ∈ P := P.mul_mem (hρP f hfP) (P.inv_mem hfP)
      have hcent : ρ * f * ρ⁻¹ * f⁻¹ ∈ Subgroup.centralizer (P : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro q hq
        have h0 := hfd q hq
        exact (commutatorElement_eq_one_iff_mul_comm.mp h0).symm
      rw [(h11b G M V Q P H cfg.hyp cfg.centre cfg.iw).2.2] at hcent
      exact hcent
    exact c8_unipotent hZP hPP hNP hZN hNab hNsq hρP h2b hρV hρ3 hδVF hδN


theorem c8_noRho (h11a : Lemma11aStatement) (h11b : Lemma11bStatement)
    (h11c : Lemma11cStatement) (h12 : Lemma12Statement) (hStr : NTStrothHypStatement)
    (cfg : QPCfg M V Q P H Φ ψ a T) {ρ : G} (hρM : ρ ∈ M) (hρ3 : ρ ^ 3 = 1) (hρQ : ρ ∉ Q)
    (hcomm : ∀ x ∈ xOf V H ⊓ Subgroup.centralizer ({c8W ψ a} : Set G),
      ∀ y ∈ xOf V H ⊓ Subgroup.centralizer ({c8W ψ a} : Set G),
      ρ * ⁅x, y⁆ * ρ⁻¹ * ⁅x, y⁆⁻¹ ∈ Q) : False := by
  have hc : MinCex M V Q P H := cfg.hyp.setup.mc.toMinCex
  have hQP : Q = P := c8_Q_eq_P cfg
  rw [hQP] at hρQ hcomm
  have hρP : ∀ p ∈ P, ρ * p * ρ⁻¹ ∈ P := fun p hp =>
    (Subgroup.mem_normalizer_iff.mp (hc.M_le_normalizer_P hρM) p).mp hp
  have hcent : Subgroup.centralizer ({c8W ψ a} : Set G) = M :=
    (h12 G M V Q P H cfg.hyp cfg.centre Φ ψ cfg.nat a T cfg.ne cfg.trans cfg.point).1
  have hρa : ρ * c8W ψ a = c8W ψ a * ρ := by
    have h : ρ ∈ Subgroup.centralizer ({c8W ψ a} : Set G) := by
      rw [hcent]
      exact hρM
    exact (Subgroup.mem_centralizer_iff.mp h (c8W ψ a) (Set.mem_singleton _)).symm
  have hρa' : ρ * c8W ψ a * ρ⁻¹ = c8W ψ a := by
    rw [hρa]
    group
  have hMN := c8_cent_normalizes h12 cfg
  have hNV : ∀ x ∈ V, ρ * x * ρ⁻¹ ∈ V := by
    intro x hx
    have hgN : ρ ∈ Subgroup.normalizer (V : Set G) := by
      rw [hc.normalizer_eq]
      exact hρM
    exact (Subgroup.mem_normalizer_iff.mp hgN x).mp hx
  have hρV : ∀ v ∈ V, ρ * v * ρ⁻¹ = v :=
    sc_conj_fix V (qpCfg_card_V cfg) (qpCfg_aG_mem_V cfg) (qpCfg_aG_ne_one cfg) hNV hρa' hρ3
  obtain ⟨b, hb⟩ := exists_spForm_eq_one cfg.ne
  rcases c8_theta_dichotomy h11a cfg hb hρP hρa hMN hcomm with hzero | hid
  · have hδ := c8_case2 h11a h11b h11c cfg hb hρP hρ3 hρV hMN hcomm hzero
    obtain ⟨E, F, w, hyp, -, -⟩ := hStr G M V Q P H Φ ψ a T cfg
    have hQa : Qa cfg.aG = Q := qa_aG_eq h12 cfg
    have hcV : centerIn (Qa cfg.aG) = V := by
      rw [hQa, centerIn_Q_eq h11b cfg]
    have hmem : ρ ∈ Qa cfg.aG := by
      refine (hyp.centralizer_quotient ρ).mp ⟨?_, ?_⟩
      · exact hcent ▸ hρM
      · intro x hx
        rw [hcV]
        rw [hQa, hQP] at hx
        exact hδ x hx
    rw [hQa, hQP] at hmem
    exact hρQ hmem
  · exact c8_case1 h11a cfg hb hρP hρa hρ3 hMN hcomm hid

end C8Cfg


section C8Final

theorem c8_card_three {K : Type*} [Group K] [Finite K] (C : Subgroup K) (hC : Nat.card C = 3)
    {r : K} (hr : r ∈ C) (hr1 : r ≠ 1) (hr3 : r ^ 3 = 1) : ∀ c ∈ C, c = 1 ∨ c = r ∨ c = r⁻¹ := by
  have hri : r⁻¹ ∈ C := C.inv_mem hr
  have hne : r ≠ r⁻¹ := by
    intro h
    apply hr1
    have h2 : r * r = 1 := by
      calc r * r = r * r⁻¹ := by rw [← h]
        _ = 1 := mul_inv_cancel r
    calc r = (r * r * r) * (r * r)⁻¹ := by group
      _ = 1 := by rw [← pow_three', hr3, h2, inv_one, mul_one]
  have h1r : (1 : K) ≠ r := fun h => hr1 h.symm
  have h1ri : (1 : K) ≠ r⁻¹ := fun h => hr1 (inv_eq_one.mp h.symm)
  have hsub : ({1, r, r⁻¹} : Set K) ⊆ (C : Set K) := by
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with h | h | h <;> rw [h]
    · exact C.one_mem
    · exact hr
    · exact hri
  have hcard : ({1, r, r⁻¹} : Set K).ncard = 3 := by
    rw [Set.ncard_insert_of_notMem (by simp [h1r, h1ri]), Set.ncard_pair hne]
  have hCn : (C : Set K).ncard = 3 := by
    rw [← Nat.card_coe_set_eq]
    exact hC
  have heq : ({1, r, r⁻¹} : Set K) = (C : Set K) :=
    Set.eq_of_subset_of_ncard_le hsub (by rw [hcard, hCn])
  intro c hc
  have hc' : c ∈ ({1, r, r⁻¹} : Set K) := by
    rw [heq]
    exact hc
  simpa using hc'

theorem ntCaseVIII_holds (h11a : Lemma11aStatement) (h11b : Lemma11bStatement)
    (h11c : Lemma11cStatement) (h12 : Lemma12Statement) (hStr : NTStrothHypStatement) :
    NTCaseVIIIStatement := by
  intro G _ _ M V Q P H n Φ ψ a T cfg w hw h8
  obtain ⟨m, hwm, hw2, ⟨hN, ⟨θ⟩⟩, -, -⟩ := h8
  have hc : MinCex M V Q P H := cfg.hyp.setup.mc.toMinCex
  have hQa : Qa cfg.aG = Q := qa_aG_eq h12 cfg
  have hcent : Subgroup.centralizer ({cfg.aG} : Set G) = M :=
    (h12 G M V Q P H cfg.hyp cfg.centre Φ ψ cfg.nat a T cfg.ne cfg.trans cfg.point).1
  have hQ2 : IsPGroup 2 ↥(Qa cfg.aG) := by
    rw [hQa, hc.hQ]
    exact (inSubgroup_pCore_two M).1
  let C₀ : Subgroup (↥(StatedSp m (ZMod 2)) × Equiv.Perm (Fin 3)) :=
    (alternatingGroup (Fin 3)).map (MonoidHom.inr (↥(StatedSp m (ZMod 2))) (Equiv.Perm (Fin 3)))
  have hC₀N : C₀.Normal := by
    refine ⟨fun n hn g => ?_⟩
    obtain ⟨τ, hτ, rfl⟩ := Subgroup.mem_map.mp hn
    refine Subgroup.mem_map.mpr ⟨g.2 * τ * g.2⁻¹, ?_, ?_⟩
    · exact Subgroup.Normal.conj_mem inferInstance τ hτ g.2
    · ext <;> simp
  have hC₀card : Nat.card C₀ = 3 := by
    show Nat.card ((alternatingGroup (Fin 3)).map (MonoidHom.inr (↥(StatedSp m (ZMod 2)))
      (Equiv.Perm (Fin 3)))) = 3
    have hinj : Function.Injective (MonoidHom.inr (↥(StatedSp m (ZMod 2)))
        (Equiv.Perm (Fin 3))) := fun x y h => by simpa using congrArg Prod.snd h
    rw [Subgroup.card_map_of_injective hinj]
    rw [nat_card_alternatingGroup, Nat.card_fin]
    rfl
  let C : Subgroup (↥(Subgroup.centralizer ({cfg.aG} : Set G)) ⧸
      (Qa cfg.aG).subgroupOf (Subgroup.centralizer ({cfg.aG} : Set G))) :=
    C₀.map θ.symm.toMonoidHom
  have hCN : C.Normal := Subgroup.Normal.map hC₀N _ θ.symm.surjective
  have hCcard : Nat.card C = 3 := by
    show Nat.card (C₀.map θ.symm.toMonoidHom) = 3
    rw [Subgroup.card_map_of_injective θ.symm.injective, hC₀card]
  haveI := hN
  obtain ⟨ρ, hρK, hord, hmem⟩ :=
    sc_lift (M := Subgroup.centralizer ({cfg.aG} : Set G)) hQ2 hCcard
  have hρ3 : ρ ^ 3 = 1 := by
    have h := pow_orderOf_eq_one ρ
    rwa [hord] at h
  have hρQ : ρ ∉ Q := by
    intro hρ
    rw [← hQa] at hρ
    obtain ⟨k, hk⟩ := hQ2 ⟨ρ, hρ⟩
    have hk' : ρ ^ 2 ^ k = 1 := by
      have h := congrArg Subtype.val hk
      simpa using h
    have hdvd := orderOf_dvd_of_pow_eq_one hk'
    rw [hord] at hdvd
    have h32 := Nat.Prime.dvd_of_dvd_pow Nat.prime_three hdvd
    norm_num at h32
  set ρbar : ↥(Subgroup.centralizer ({cfg.aG} : Set G)) ⧸
      (Qa cfg.aG).subgroupOf (Subgroup.centralizer ({cfg.aG} : Set G)) :=
    QuotientGroup.mk (⟨ρ, hρK⟩ : ↥(Subgroup.centralizer ({cfg.aG} : Set G))) with hρbar
  have hρbar1 : ρbar ≠ 1 := by
    intro h
    have h1 := (QuotientGroup.eq_one_iff _).mp h
    have h2 := Subgroup.mem_subgroupOf.mp h1
    rw [hQa] at h2
    exact hρQ h2
  have hρbar3 : ρbar ^ 3 = 1 := by
    rw [hρbar, ← QuotientGroup.mk_pow]
    have : (⟨ρ, hρK⟩ : ↥(Subgroup.centralizer ({cfg.aG} : Set G))) ^ 3 = 1 :=
      Subtype.ext (by simpa using hρ3)
    rw [this, QuotientGroup.mk_one]
  have hnorm : ∀ z, z * ρbar * z⁻¹ = ρbar ∨ z * ρbar * z⁻¹ = ρbar⁻¹ := by
    intro z
    have hzC : z * ρbar * z⁻¹ ∈ C := hCN.conj_mem ρbar hmem z
    have hz1 : z * ρbar * z⁻¹ ≠ 1 := by
      intro h
      apply hρbar1
      have := congrArg (fun y => z⁻¹ * y * z) h
      simpa [mul_assoc] using this
    rcases c8_card_three C hCcard hmem hρbar1 hρbar3 _ hzC with h | h | h
    · exact absurd h hz1
    · exact Or.inl h
    · exact Or.inr h
  refine c8_noRho h11a h11b h11c h12 hStr cfg (ρ := ρ) ?_ hρ3 hρQ ?_
  · rw [← hcent]
    exact hρK
  · intro x hx y hy
    have hxK : x ∈ Subgroup.centralizer ({cfg.aG} : Set G) := (Subgroup.mem_inf.mp hx).2
    have hyK : y ∈ Subgroup.centralizer ({cfg.aG} : Set G) := (Subgroup.mem_inf.mp hy).2
    set x' : ↥(Subgroup.centralizer ({cfg.aG} : Set G)) := ⟨x, hxK⟩ with hx'
    set y' : ↥(Subgroup.centralizer ({cfg.aG} : Set G)) := ⟨y, hyK⟩ with hy'
    set ρ' : ↥(Subgroup.centralizer ({cfg.aG} : Set G)) := ⟨ρ, hρK⟩ with hρ'
    let mkq : ↥(Subgroup.centralizer ({cfg.aG} : Set G)) →*
        (↥(Subgroup.centralizer ({cfg.aG} : Set G)) ⧸
          (Qa cfg.aG).subgroupOf (Subgroup.centralizer ({cfg.aG} : Set G))) := QuotientGroup.mk' _
    have h1 := c8_comm_cent hnorm (mkq x') (mkq y')
    have h3 : mkq ⁅x', y'⁆ = ⁅mkq x', mkq y'⁆ := map_commutatorElement mkq x' y'
    have h1' : ⁅mkq x', mkq y'⁆ * mkq ρ' * ⁅mkq x', mkq y'⁆⁻¹ = mkq ρ' := h1
    have h2 : mkq (⁅x', y'⁆ * ρ' * ⁅x', y'⁆⁻¹ * ρ'⁻¹) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, h3, h1', mul_inv_cancel]
    have h2' : (QuotientGroup.mk (⁅x', y'⁆ * ρ' * ⁅x', y'⁆⁻¹ * ρ'⁻¹) :
        ↥(Subgroup.centralizer ({cfg.aG} : Set G)) ⧸
          (Qa cfg.aG).subgroupOf (Subgroup.centralizer ({cfg.aG} : Set G))) = 1 := h2
    have h4 := Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff _).mp h2')
    rw [hQa] at h4
    have h5 : ((⁅x', y'⁆ * ρ' * ⁅x', y'⁆⁻¹ * ρ'⁻¹ : ↥(Subgroup.centralizer ({cfg.aG} : Set G))) :
        G) = ⁅x, y⁆ * ρ * ⁅x, y⁆⁻¹ * ρ⁻¹ := rfl
    rw [h5] at h4
    have h6 := Q.inv_mem h4
    have e : (⁅x, y⁆ * ρ * ⁅x, y⁆⁻¹ * ρ⁻¹)⁻¹ = ρ * ⁅x, y⁆ * ρ⁻¹ * ⁅x, y⁆⁻¹ := by group
    rwa [e] at h6

end C8Final

end CFSG.RankThree.GF2n.Tim79a
