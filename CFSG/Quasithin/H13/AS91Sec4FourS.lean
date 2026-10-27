module

public import CFSG.Quasithin.H13.AS91Sec4FourK
public import CFSG.Quasithin.H13.AS91Sec4FourModel
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.HaradaModel.NoNormal2S5

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13.AS91

open Subgroup Module CFSG.Open CFSG.LargeExtraspecial CFSG.Quasithin CFSG.Quasithin.HatM22
open CFSG.GF2Type.Smith1979.GammaU CFSG.GF2Type.Smith1979.GammaU.StepA
open CFSG.GF2Type.Smith1979.GammaU.Viol CFSG.GF2Type.Smith1979.GammaU.Enum
open CFSG.GF2Type.Smith1979.IdxFour

variable {G : Type} [Group G] [Finite G]

theorem card_QG_inf_centralizer_mul (T : Setting G) {X : Subgroup G} (hX : X ≤ T.QG)
    (hz : T.z ∈ X) :
    Nat.card (T.QG ⊓ centralizer (X : Set G) : Subgroup G) * Nat.card X =
      2 ^ (2 * T.width + 2) := by
  have hcardX : Nat.card X = 2 * 2 ^ finrank (ZMod 2) (T.clSub X) := by
    rw [← T.card_submodule, ← T.card_clPre, T.clPre_clSub hX hz]
  have hle : finrank (ZMod 2) (T.clSub X) ≤ finrank (ZMod 2) T.Qt := Submodule.finrank_le _
  have hdim : finrank (ZMod 2) T.Qt = 2 * T.width := T.finrank_Qt_eq_two_mul_width
  rw [T.centralizer_inf_QG_eq_clPre hX, T.card_clPre, T.card_submodule,
    LinearMap.BilinForm.finrank_orthogonal T.q_nondegenerate, hcardX, hdim]
  rw [hdim] at hle
  have e : 2 * T.width + 2 = (2 * T.width - finrank (ZMod 2) (T.clSub X)) + 1 +
      (finrank (ZMod 2) (T.clSub X) + 1) := by omega
  rw [e, pow_add, pow_add, pow_add, pow_one]
  ring

theorem exists_lift_of_fix (S : Setting G) {a b : G} (ha : a ∈ S.QG) (hb : b ∈ S.QG)
    (ha1 : a ≠ 1) (haz : a ≠ S.z) (hb1 : b ≠ 1) (hbz : b ≠ S.z) (hab : a ≠ b)
    (habz : a ≠ b * S.z) (m : S.M)
    (hma : ((S.ρ m : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl a) = S.cl a)
    (hmb : ((S.ρ m : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl b) = S.cl b) :
    ∃ s : S.M, S.ρ s = S.ρ m ∧ (s : G) * a * (s : G)⁻¹ = a ∧ (s : G) * b * (s : G)⁻¹ = b := by
  have hz2 : S.z * S.z = 1 := S.z_mul_z
  have hρu : ∀ (u : G) (hu : u ∈ S.QG) (m' : S.M),
      S.ρ ((⟨u, S.QG_le_M hu⟩ : S.M) * m') = S.ρ m' := by
    intro u hu m'
    rw [map_mul, (S.ρ_eq_one_iff _).mpr hu, one_mul]
  have hfix : ∀ {X c : G}, c = X * S.z → X = c * S.z := fun {X c} e => by
    calc X = X * (S.z * S.z) := by rw [hz2, mul_one]
      _ = X * S.z * S.z := by rw [mul_assoc]
      _ = c * S.z := by rw [← e]
  obtain ⟨m₁, hm₁, hm₁a⟩ : ∃ m₁ : S.M, S.ρ m₁ = S.ρ m ∧ (m₁ : G) * a * (m₁ : G)⁻¹ = a := by
    rw [S.ρ_cl m ha] at hma
    rcases (S.cl_eq_cl_iff (S.conj_mem_QG m.2 ha) ha).mp hma with e | e
    · exact ⟨m, rfl, e.symm⟩
    · have hX := hfix e
      have h1 : a * S.z ≠ 1 := fun e' => haz (by
        calc a = a * S.z * S.z := by rw [mul_assoc, hz2, mul_one]
          _ = S.z := by rw [e', one_mul])
      have h2 : a * S.z ≠ S.z := fun e' => ha1 (mul_right_cancel (e'.trans (one_mul _).symm))
      obtain ⟨u, hu, hut⟩ := S.exists_conj_eq_mul_z (S.QG.mul_mem ha S.z_mem_QG) h1 h2
      refine ⟨(⟨u, S.QG_le_M hu⟩ : S.M) * m, hρu u hu m, ?_⟩
      have e1 : (((⟨u, S.QG_le_M hu⟩ : S.M) * m : S.M) : G) * a *
          (((⟨u, S.QG_le_M hu⟩ : S.M) * m : S.M) : G)⁻¹ =
          u * ((m : G) * a * (m : G)⁻¹) * u⁻¹ := by
        simp only [Subgroup.coe_mul, mul_inv_rev]
        group
      rw [e1, hX, hut, mul_assoc, hz2, mul_one]
  have hmb₁ : ((S.ρ m₁ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl b) = S.cl b := by rw [hm₁]; exact hmb
  rw [S.ρ_cl m₁ hb] at hmb₁
  rcases (S.cl_eq_cl_iff (S.conj_mem_QG m₁.2 hb) hb).mp hmb₁ with e | e
  · exact ⟨m₁, hm₁, hm₁a, e.symm⟩
  · have hX := hfix e
    have h1 : b * S.z ≠ 1 := fun e' => hbz (by
      calc b = b * S.z * S.z := by rw [mul_assoc, hz2, mul_one]
        _ = S.z := by rw [e', one_mul])
    have h2 : b * S.z ≠ S.z := fun e' => hb1 (mul_right_cancel (e'.trans (one_mul _).symm))
    have h3 : a ≠ b * S.z * S.z := by rw [mul_assoc, hz2, mul_one]; exact hab
    obtain ⟨u, hu, hua, hut⟩ :=
      S.exists_conj_eq_mul_z_of_commute (S.QG.mul_mem hb S.z_mem_QG) ha h1 h2 habz h3
    refine ⟨(⟨u, S.QG_le_M hu⟩ : S.M) * m₁, (hρu u hu m₁).trans hm₁, ?_, ?_⟩
    · have e1 : (((⟨u, S.QG_le_M hu⟩ : S.M) * m₁ : S.M) : G) * a *
          (((⟨u, S.QG_le_M hu⟩ : S.M) * m₁ : S.M) : G)⁻¹ =
            u * ((m₁ : G) * a * (m₁ : G)⁻¹) * u⁻¹ := by
        simp only [Subgroup.coe_mul, mul_inv_rev]
        group
      rw [e1, hm₁a, hua, mul_inv_cancel_right]
    · have e1 : (((⟨u, S.QG_le_M hu⟩ : S.M) * m₁ : S.M) : G) * b *
          (((⟨u, S.QG_le_M hu⟩ : S.M) * m₁ : S.M) : G)⁻¹ =
            u * ((m₁ : G) * b * (m₁ : G)⁻¹) * u⁻¹ := by
        simp only [Subgroup.coe_mul, mul_inv_rev]
        group
      rw [e1, hX, hut, mul_assoc, hz2, mul_one]

theorem pCoreOf_eq_of {p : ℕ} {H P : Subgroup G} (hPH : P ≤ H) (hn : (P.subgroupOf H).Normal)
    (hp : IsPGroup p P)
    (hmax : ∀ X : Subgroup ↥H, X.Normal → IsPGroup p X → X ≤ P.subgroupOf H) :
    pCoreOf p H = P := by
  have hp' : IsPGroup p (P.subgroupOf H) := hp.of_equiv (subgroupOfEquivOfLe hPH).symm
  apply le_antisymm
  · have := hmax _ CFSG.pCore_normal CFSG.pCore_isPGroup
    rintro _ ⟨x, hx, rfl⟩
    exact mem_subgroupOf.mp (this hx)
  · intro x hx
    have hle : P.subgroupOf H ≤ CFSG.pCore p ↥H := le_sSup ⟨hn, hp'⟩
    exact ⟨⟨x, hPH hx⟩, hle (mem_subgroupOf.mpr hx), rfl⟩

theorem comm_of_conj_eq {s r : G} (h : s * r * s⁻¹ = r) : r * s = s * r := by
  calc r * s = s * r * s⁻¹ * s := by rw [h]
    _ = s * r := by group

namespace Data41

variable {z : G} {h : HypJ4 G z} (D : Data41 h)

@[expose] noncomputable def Bgrp (g₁ : G) (s₀ : h.setting.M) : Subgroup G :=
  centralizer (Zinf (h := h) g₁ s₀ : Set G) ⊓ pre h.setting (Two.p2Grp.comap D.Φo)

theorem centralizer_le_M {g₁ : G} {s₀ : h.setting.M} (hz : z ∈ Zinf (h := h) g₁ s₀) :
    centralizer (Zinf (h := h) g₁ s₀ : Set G) ≤ h.setting.M := fun x hx =>
  h.setting.mem_M_iff.mpr (mem_centralizer_iff.mp hx z hz).symm

include D in
theorem stabIn_three
    (hOut : KG82HatM22Out)
    (hTw : KG82HatM22Twelve) : stabIn Two.nGrp (vecOf 3) = genGrp (Two.stab1Gens ()) :=
  (D.map_stab hOut hTw 3).symm.trans (D.genGrp_stab1_eq hOut hTw).symm

section FourS

variable
  (hOut : KG82HatM22Out) (hTw : KG82HatM22Twelve) {g₁ : G} (hg₁ : g₁ * z * g₁⁻¹ = D.rep 3)
  {s₀ : h.setting.M} (hs₀ : D.Φo (h.setting.ρ s₀) = Two.tE)

include hOut hTw hg₁ hs₀

theorem hSM : centralizer (Zinf (h := h) g₁ s₀ : Set G) ≤ h.setting.M :=
  centralizer_le_M (D.z_mem_Zinf hOut hTw hg₁ hs₀)

theorem Φo_mem_gammaZ {x : G} (hx : x ∈ centralizer (Zinf (h := h) g₁ s₀ : Set G))
    (hxM : x ∈ h.setting.M) : D.Φo (h.setting.ρ ⟨x, hxM⟩) ∈ Two.gammaZ := by
  have hc : ∀ y ∈ Zinf (h := h) g₁ s₀, x * y * x⁻¹ = y := fun y hy => by
    rw [← mem_centralizer_iff.mp hx y hy, mul_inv_cancel_right]
  refine Two.mem_gammaZ.mpr ⟨D.Φo_mem_nGrp hOut hTw ⟨_, rfl⟩, ?_, ?_⟩
  · rw [← D.ψV_cl_rep 3, Φo_apply_ψV, h.setting.ρ_cl _ (D.rep_mem 3)]
    show D.ψV (h.setting.cl (x * D.rep 3 * x⁻¹)) = _
    rw [hc _ (D.rep3_mem_Zinf hOut hTw hg₁ hs₀)]
  · rw [← D.ψV_cl_conj_rep3 hOut hTw hg₁ hs₀, Φo_apply_ψV,
      h.setting.ρ_cl _ (h.setting.conj_mem_QG s₀.2 (D.rep_mem 3))]
    show D.ψV (h.setting.cl (x * ((s₀ : G) * D.rep 3 * (s₀ : G)⁻¹) * x⁻¹)) = _
    rw [hc _ (D.conj_rep3_mem_Zinf hOut hTw hg₁ hs₀)]

theorem exists_psi : ∃ ψ : ↥(centralizer (Zinf (h := h) g₁ s₀ : Set G)) →* ↥Two.gammaZ,
    Function.Surjective ψ ∧ ∀ x, ((ψ x : ↥Two.gammaZ) : V12 ≃ₗ[ZMod 2] V12) =
      D.Φo (h.setting.ρ (Subgroup.inclusion (D.hSM hOut hTw hg₁ hs₀) x)) := by
  refine ⟨((D.Φo.comp h.setting.ρ).comp (Subgroup.inclusion (D.hSM hOut hTw hg₁ hs₀))).codRestrict
    Two.gammaZ (fun x => D.Φo_mem_gammaZ hOut hTw hg₁ hs₀ x.2 _), ?_, fun x => rfl⟩
  rintro ⟨U, hU⟩
  obtain ⟨hUN, hU3, hU192⟩ := Two.mem_gammaZ.mp hU
  rw [← D.map_Mbar_Φo hOut hTw] at hUN
  obtain ⟨m, hmM, rfl⟩ := hUN
  obtain ⟨t, rfl⟩ := MonoidHom.mem_range.mp hmM
  have ha := D.rep_mem 3
  have hb := h.setting.conj_mem_QG s₀.2 (D.rep_mem 3)
  obtain ⟨-, ha1, haz⟩ := D.rep_props vecOf_three_ne q0_three
  have hca := D.ψV_cl_rep 3
  have hcb := D.ψV_cl_conj_rep3 hOut hTw hg₁ hs₀
  have h192 : vecOf 192 ≠ 0 := fun h0 =>
    absurd (vecOf_inj (by norm_num) (by norm_num) (h0.trans vecOf_zero.symm)) (by norm_num)
  have h3192 : vecOf 3 ≠ vecOf 192 := fun e =>
    absurd (vecOf_inj (by norm_num) (by norm_num) e) (by norm_num)
  have hb0 : h.setting.cl ((s₀ : G) * D.rep 3 * (s₀ : G)⁻¹) ≠ 0 := fun e =>
    h192 (by rw [← hcb, e, map_zero])
  have hb1 : (s₀ : G) * D.rep 3 * (s₀ : G)⁻¹ ≠ 1 := fun e =>
    hb0 ((h.setting.cl_eq_zero_iff hb).mpr (Or.inl e))
  have hbz : (s₀ : G) * D.rep 3 * (s₀ : G)⁻¹ ≠ h.setting.z := fun e =>
    hb0 ((h.setting.cl_eq_zero_iff hb).mpr (Or.inr e))
  have hab : D.rep 3 ≠ (s₀ : G) * D.rep 3 * (s₀ : G)⁻¹ := fun e => h3192 (by rw [← hca, e, hcb])
  have habz : D.rep 3 ≠ (s₀ : G) * D.rep 3 * (s₀ : G)⁻¹ * h.setting.z := fun e =>
    h3192 (by rw [← hca, e, h.setting.cl_mul_z hb, hcb])
  have hma : ((h.setting.ρ t : h.setting.O) : h.setting.Qt ≃ₗ[ZMod 2] h.setting.Qt)
      (h.setting.cl (D.rep 3)) = h.setting.cl (D.rep 3) := by
    apply D.ψV.injective
    rw [← Φo_apply_ψV, hca, hU3]
  have hmb : ((h.setting.ρ t : h.setting.O) : h.setting.Qt ≃ₗ[ZMod 2] h.setting.Qt)
      (h.setting.cl ((s₀ : G) * D.rep 3 * (s₀ : G)⁻¹)) =
        h.setting.cl ((s₀ : G) * D.rep 3 * (s₀ : G)⁻¹) := by
    apply D.ψV.injective
    rw [← Φo_apply_ψV, hcb, hU192]
  obtain ⟨s, hsρ, hsa, hsb⟩ :=
    exists_lift_of_fix h.setting ha hb ha1 haz hb1 hbz hab habz t hma hmb
  have hsC : (s : G) ∈ centralizer (Zinf (h := h) g₁ s₀ : Set G) := by
    rw [← D.closure_eq_Zinf hOut hTw hg₁ hs₀, centralizer_closure, mem_centralizer_iff]
    have hk : ((s₀ : G) * g₁) * z * ((s₀ : G) * g₁)⁻¹ = (s₀ : G) * D.rep 3 * (s₀ : G)⁻¹ := by
      rw [← hg₁]
      group
    rintro y (rfl | rfl | rfl)
    · exact (h.setting.mem_M_iff.mp s.2).symm
    · rw [hg₁]
      exact comm_of_conj_eq hsa
    · rw [hk]
      exact comm_of_conj_eq hsb
  refine ⟨⟨s, hsC⟩, Subtype.ext ?_⟩
  show D.Φo (h.setting.ρ ⟨(s : G), _⟩) = D.Φo (h.setting.ρ t)
  rw [show (⟨(s : G), _⟩ : h.setting.M) = s from rfl, hsρ]

theorem card_QG_inf_centralizer_Zinf :
    Nat.card (h.setting.QG ⊓ centralizer (Zinf (h := h) g₁ s₀ : Set G) : Subgroup G) = 2 ^ 11 := by
  have h1 := card_QG_inf_centralizer_mul h.setting (Zinf_le_QG g₁ s₀)
    (D.z_mem_Zinf hOut hTw hg₁ hs₀)
  rw [D.card_Zinf hOut hTw hg₁ hs₀, h.setting_width] at h1
  omega

theorem card_Qa_inf_centralizer_Zinf :
    Nat.card (h.setting.Qa g₁ ⊓ centralizer (Zinf (h := h) g₁ s₀ : Set G) : Subgroup G) =
      2 ^ 11 := by
  have h1 := card_QG_inf_centralizer_mul (h.setting.conjBy g₁) (Zinf_le_Qa₁ g₁ s₀)
    (D.conjBy₁_z_mem hOut hTw hg₁ hs₀)
  rw [D.card_Zinf hOut hTw hg₁ hs₀, Setting.width_conjBy, h.setting_width] at h1
  have e : (h.setting.conjBy g₁).QG = h.setting.Qa g₁ := rfl
  rw [e] at h1
  omega

theorem card_gammaZ : Nat.card ↥Two.gammaZ = 1920 := by
  rw [← Two.gZGrp_eq_gammaZ (D.stabIn_three hOut hTw), Two.card_gZGrp]

theorem card_centralizer_Zinf :
    Nat.card (centralizer (Zinf (h := h) g₁ s₀ : Set G)) = 2 ^ 11 * 1920 := by
  obtain ⟨ψ, hψs, hψ⟩ := D.exists_psi hOut hTw hg₁ hs₀
  have hker : ψ.ker = (h.setting.QG ⊓ centralizer (Zinf (h := h) g₁ s₀ : Set G)).subgroupOf
      (centralizer (Zinf (h := h) g₁ s₀ : Set G)) := by
    ext x
    rw [MonoidHom.mem_ker, mem_subgroupOf, mem_inf]
    constructor
    · intro h1
      have h2 : D.Φo (h.setting.ρ (Subgroup.inclusion (D.hSM hOut hTw hg₁ hs₀) x)) = D.Φo 1 := by
        rw [← hψ x, h1, map_one]
        rfl
      exact ⟨(h.setting.ρ_eq_one_iff _).mp (D.Φo_injective h2), x.2⟩
    · rintro ⟨hxQ, -⟩
      apply Subtype.ext
      rw [hψ x, (h.setting.ρ_eq_one_iff _).mpr hxQ, map_one]
      rfl
  have h1 := Subgroup.card_mul_index ψ.ker
  rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr hψs, Subgroup.card_top,
    D.card_gammaZ hOut hTw hg₁ hs₀, hker, card_subgroupOf_eq, inf_of_le_right inf_le_right,
    D.card_QG_inf_centralizer_Zinf hOut hTw hg₁ hs₀] at h1
  exact h1.symm

theorem exists_phiS : ∃ φ : ↥(centralizer (Zinf (h := h) g₁ s₀ : Set G)) →* Equiv.Perm (Fin 5),
    Function.Surjective φ ∧
      φ.ker = (D.Bgrp g₁ s₀).subgroupOf (centralizer (Zinf (h := h) g₁ s₀ : Set G)) := by
  obtain ⟨ψ, hψs, hψ⟩ := D.exists_psi hOut hTw hg₁ hs₀
  refine ⟨Two.chi.comp ψ, (Two.chi_surjective (D.stabIn_three hOut hTw)).comp hψs, ?_⟩
  ext x
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, Two.chi_ker (D.stabIn_three hOut hTw), hψ,
    mem_subgroupOf]
  constructor
  · intro h1
    exact Subgroup.mem_inf.mpr
      ⟨x.2, mem_pre_of_rho (Subgroup.inclusion (D.hSM hOut hTw hg₁ hs₀) x) h1⟩
  · intro hxB
    exact rho_mem_of_mem_pre (Subgroup.mem_inf.mp hxB).2 _

theorem Bgrp_le_centralizer : D.Bgrp g₁ s₀ ≤ centralizer (Zinf (h := h) g₁ s₀ : Set G) :=
  inf_le_left

theorem card_Bgrp : Nat.card (D.Bgrp g₁ s₀) = 2 ^ 15 := by
  obtain ⟨φ, hφs, hφk⟩ := D.exists_phiS hOut hTw hg₁ hs₀
  have h1 := Subgroup.card_mul_index φ.ker
  rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr hφs, Subgroup.card_top, Nat.card_perm,
    Nat.card_fin, show Nat.factorial 5 = 120 from rfl, hφk, card_subgroupOf_eq,
    inf_of_le_right (D.Bgrp_le_centralizer hOut hTw hg₁ hs₀),
    D.card_centralizer_Zinf hOut hTw hg₁ hs₀] at h1
  omega

theorem le_Bgrp_of_normal {P : Subgroup G} (hPS : P ≤ centralizer (Zinf (h := h) g₁ s₀ : Set G))
    (hn : (P.subgroupOf (centralizer (Zinf (h := h) g₁ s₀ : Set G))).Normal) (hp : IsPGroup 2 P) :
    P ≤ D.Bgrp g₁ s₀ := by
  obtain ⟨φ, hφs, hφk⟩ := D.exists_phiS hOut hTw hg₁ hs₀
  have hp' : IsPGroup 2 (P.subgroupOf (centralizer (Zinf (h := h) g₁ s₀ : Set G))) :=
    hp.of_equiv (subgroupOfEquivOfLe hPS).symm
  have hbot := CFSG.EvenSporadicStandard.HNRecog.HaradaModel.eq_bot_of_normal_isPGroup_perm5 _
    (hp'.map φ) (hn.map φ hφs)
  intro x hx
  have hx' : (⟨x, hPS hx⟩ : ↥(centralizer (Zinf (h := h) g₁ s₀ : Set G))) ∈ φ.ker := by
    rw [MonoidHom.mem_ker]
    have : φ ⟨x, hPS hx⟩ ∈ (P.subgroupOf (centralizer (Zinf (h := h) g₁ s₀ : Set G))).map φ :=
      ⟨_, mem_subgroupOf.mpr hx, rfl⟩
    rw [hbot] at this
    exact this
  rw [hφk, mem_subgroupOf] at hx'
  exact hx'

theorem Bgrp_normal_S : ((D.Bgrp g₁ s₀).subgroupOf
    (centralizer (Zinf (h := h) g₁ s₀ : Set G))).Normal := by
  obtain ⟨φ, -, hφk⟩ := D.exists_phiS hOut hTw hg₁ hs₀
  rw [← hφk]
  exact φ.normal_ker

theorem conj_mem_centralizer {n : G} (hn : n ∈ normalizer (Zinf (h := h) g₁ s₀ : Set G)) {x : G}
    (hx : x ∈ centralizer (Zinf (h := h) g₁ s₀ : Set G)) :
    n * x * n⁻¹ ∈ centralizer (Zinf (h := h) g₁ s₀ : Set G) := by
  rw [mem_centralizer_iff]
  intro y hy
  have hy' : n⁻¹ * y * n⁻¹⁻¹ ∈ Zinf (h := h) g₁ s₀ :=
    (mem_normalizer_iff.mp (inv_mem hn) y).mp hy
  have hc := mem_centralizer_iff.mp hx _ hy'
  calc y * (n * x * n⁻¹) = n * ((n⁻¹ * y * n⁻¹⁻¹) * x) * n⁻¹ := by group
    _ = n * (x * (n⁻¹ * y * n⁻¹⁻¹)) * n⁻¹ := by rw [hc]
    _ = n * x * n⁻¹ * y := by group

theorem conj_mem_Bgrp {n : G} (hn : n ∈ normalizer (Zinf (h := h) g₁ s₀ : Set G)) {b : G}
    (hb : b ∈ D.Bgrp g₁ s₀) : n * b * n⁻¹ ∈ D.Bgrp g₁ s₀ := by
  set P := (D.Bgrp g₁ s₀).map (MulAut.conj n).toMonoidHom with hP
  have hPS : P ≤ centralizer (Zinf (h := h) g₁ s₀ : Set G) := by
    rintro _ ⟨x, hx, rfl⟩
    exact D.conj_mem_centralizer hOut hTw hg₁ hs₀ hn (D.Bgrp_le_centralizer hOut hTw hg₁ hs₀ hx)
  have hnorm : (P.subgroupOf (centralizer (Zinf (h := h) g₁ s₀ : Set G))).Normal := by
    refine ⟨fun x hx s => ?_⟩
    rw [mem_subgroupOf] at hx ⊢
    obtain ⟨y, hy, hyx⟩ := hx
    have hs' : n⁻¹ * (s : G) * n⁻¹⁻¹ ∈ centralizer (Zinf (h := h) g₁ s₀ : Set G) :=
      D.conj_mem_centralizer hOut hTw hg₁ hs₀ (inv_mem hn) s.2
    have hBS := D.Bgrp_normal_S hOut hTw hg₁ hs₀
    have hy' : (n⁻¹ * (s : G) * n⁻¹⁻¹) * y * (n⁻¹ * (s : G) * n⁻¹⁻¹)⁻¹ ∈ D.Bgrp g₁ s₀ := by
      have := hBS.conj_mem ⟨y, D.Bgrp_le_centralizer hOut hTw hg₁ hs₀ hy⟩ (mem_subgroupOf.mpr hy)
        ⟨_, hs'⟩
      rw [mem_subgroupOf] at this
      exact this
    refine ⟨_, hy', ?_⟩
    simp only [MonoidHom.coe_coe, MulAut.conj_apply, MulEquiv.coe_toMonoidHom, coe_mul,
      Subgroup.coe_inv] at hyx ⊢
    rw [← hyx]
    group
  have hp : IsPGroup 2 P := by
    refine IsPGroup.of_card (n := 15) ?_
    rw [hP, Subgroup.card_map_of_injective (MulAut.conj n).injective,
      D.card_Bgrp hOut hTw hg₁ hs₀]
  exact D.le_Bgrp_of_normal hOut hTw hg₁ hs₀ hPS hnorm hp ⟨b, hb, rfl⟩

theorem QG_inf_le_Bgrp :
    h.setting.QG ⊓ centralizer (Zinf (h := h) g₁ s₀ : Set G) ≤ D.Bgrp g₁ s₀ := by
  rintro x ⟨hxQ, hxS⟩
  refine Subgroup.mem_inf.mpr ⟨hxS, mem_pre_of_rho ⟨x, h.setting.QG_le_M hxQ⟩ ?_⟩
  show D.Φo (h.setting.ρ ⟨x, _⟩) ∈ Two.p2Grp
  rw [(h.setting.ρ_eq_one_iff _).mpr hxQ, map_one]
  exact one_mem _

theorem commutator_mem_Bgrp {k : G} (hk : k ∈ Kgrp (h := h) g₁ s₀) {s : G}
    (hs : s ∈ centralizer (Zinf (h := h) g₁ s₀ : Set G)) : k * s * k⁻¹ * s⁻¹ ∈ D.Bgrp g₁ s₀ := by
  let C' : Subgroup G :=
    { carrier := {k | k ∈ normalizer (Zinf (h := h) g₁ s₀ : Set G) ∧
        ∀ s ∈ centralizer (Zinf (h := h) g₁ s₀ : Set G), k * s * k⁻¹ * s⁻¹ ∈ D.Bgrp g₁ s₀}
      mul_mem' := fun {a b} ha hb => ⟨mul_mem ha.1 hb.1, fun s hs => by
        have e : a * b * s * (a * b)⁻¹ * s⁻¹ =
            a * (b * s * b⁻¹ * s⁻¹) * a⁻¹ * (a * s * a⁻¹ * s⁻¹) := by group
        rw [e]
        exact mul_mem (D.conj_mem_Bgrp hOut hTw hg₁ hs₀ ha.1 (hb.2 s hs)) (ha.2 s hs)⟩
      one_mem' := ⟨one_mem _, fun s _ => by
        rw [one_mul, inv_one, mul_one, mul_inv_cancel]
        exact one_mem _⟩
      inv_mem' := fun {a} ha => ⟨inv_mem ha.1, fun s hs => by
        have e : a⁻¹ * s * a⁻¹⁻¹ * s⁻¹ = a⁻¹ * (a * s * a⁻¹ * s⁻¹)⁻¹ * a⁻¹⁻¹ := by group
        rw [e]
        exact D.conj_mem_Bgrp hOut hTw hg₁ hs₀ (inv_mem ha.1) (inv_mem (ha.2 s hs))⟩ }
  have hKC : Kgrp (h := h) g₁ s₀ ≤ C' := by
    refine iSup₂_le fun g hg => ?_
    obtain ⟨n, hn, he⟩ := D.exists_Qa_eq hOut hTw hg₁ hs₀ hg
    have hnN := D.K0_le_normalizer hOut hTw hg₁ hs₀ hn
    rw [← h.setting_QG, ← Setting.Qa_eq_map, he, Setting.Qa_eq_map]
    rintro _ ⟨q, hq, rfl⟩
    have hqN := D.K0_le_normalizer hOut hTw hg₁ hs₀ (QG_le_K0 g₁ s₀ hq)
    refine ⟨?_, fun s hs => ?_⟩
    · show n * q * n⁻¹ ∈ _
      exact mul_mem (mul_mem hnN hqN) (inv_mem hnN)
    · show n * q * n⁻¹ * s * (n * q * n⁻¹)⁻¹ * s⁻¹ ∈ _
      have hs' : n⁻¹ * s * n⁻¹⁻¹ ∈ centralizer (Zinf (h := h) g₁ s₀ : Set G) :=
        D.conj_mem_centralizer hOut hTw hg₁ hs₀ (inv_mem hnN) hs
      set s' := n⁻¹ * s * n⁻¹⁻¹ with hs'def
      have hcQ : q * s' * q⁻¹ * s'⁻¹ ∈ h.setting.QG := by
        rw [mul_assoc q s', mul_assoc q]
        refine h.setting.QG.mul_mem hq ?_
        have := h.setting.conj_mem_QG (D.hSM hOut hTw hg₁ hs₀ hs') (h.setting.QG.inv_mem hq)
        simpa [mul_assoc] using this
      have hcS : q * s' * q⁻¹ * s'⁻¹ ∈ centralizer (Zinf (h := h) g₁ s₀ : Set G) :=
        mul_mem (D.conj_mem_centralizer hOut hTw hg₁ hs₀ hqN hs') (inv_mem hs')
      have e : n * q * n⁻¹ * s * (n * q * n⁻¹)⁻¹ * s⁻¹ =
          n * (q * s' * q⁻¹ * s'⁻¹) * n⁻¹ := by
        rw [hs'def]
        group
      rw [e]
      exact D.conj_mem_Bgrp hOut hTw hg₁ hs₀ hnN (D.QG_inf_le_Bgrp hOut hTw hg₁ hs₀ ⟨hcQ, hcS⟩)
  exact (hKC hk).2 s hs

theorem Kgrp_inf_le_Bgrp :
    Kgrp (h := h) g₁ s₀ ⊓ centralizer (Zinf (h := h) g₁ s₀ : Set G) ≤ D.Bgrp g₁ s₀ := by
  obtain ⟨φ, hφs, hφk⟩ := D.exists_phiS hOut hTw hg₁ hs₀
  rintro k ⟨hkK, hkS⟩
  have hcomm : ∀ s : ↥(centralizer (Zinf (h := h) g₁ s₀ : Set G)),
      φ ⟨k, hkS⟩ * φ s = φ s * φ ⟨k, hkS⟩ := by
    intro s
    have hc := D.commutator_mem_Bgrp hOut hTw hg₁ hs₀ hkK s.2
    have h1 : φ (⟨k, hkS⟩ * s * (⟨k, hkS⟩ : ↥(centralizer (Zinf (h := h) g₁ s₀ : Set G)))⁻¹ *
        s⁻¹) = 1 := by
      rw [← MonoidHom.mem_ker, hφk, mem_subgroupOf]
      exact hc
    rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h1
    calc φ ⟨k, hkS⟩ * φ s = (φ ⟨k, hkS⟩ * φ s * (φ ⟨k, hkS⟩)⁻¹ * (φ s)⁻¹) *
          (φ s * φ ⟨k, hkS⟩) := by group
      _ = φ s * φ ⟨k, hkS⟩ := by rw [h1, one_mul]
  obtain ⟨s1, hs1⟩ := hφs (Equiv.swap 0 1)
  obtain ⟨s2, hs2⟩ := hφs (finRotate 5)
  have h1 := Two.perm5_eq_one_of_commute (φ ⟨k, hkS⟩) (by rw [← hs1]; exact hcomm s1)
    (by rw [← hs2]; exact hcomm s2)
  have : (⟨k, hkS⟩ : ↥(centralizer (Zinf (h := h) g₁ s₀ : Set G))) ∈ φ.ker := h1
  rw [hφk, mem_subgroupOf] at this
  exact this

theorem Bgrp_le_Kgrp : D.Bgrp g₁ s₀ ≤ Kgrp (h := h) g₁ s₀ := by
  set Y := h.setting.Qa g₁ ⊓ centralizer (Zinf (h := h) g₁ s₀ : Set G) with hY
  have hYS : Y ≤ centralizer (Zinf (h := h) g₁ s₀ : Set G) := inf_le_right
  have hYM : Y ≤ h.setting.M := hYS.trans (D.hSM hOut hTw hg₁ hs₀)
  have hYn : (Y.subgroupOf (centralizer (Zinf (h := h) g₁ s₀ : Set G))).Normal := by
    refine ⟨fun y hy s => ?_⟩
    rw [mem_subgroupOf] at hy ⊢
    obtain ⟨hyQ, hyS⟩ := hy
    have hsr : (s : G) ∈ (h.setting.conjBy g₁).M := by
      rw [(h.setting.conjBy g₁).mem_M_iff, Setting.conjBy_z, h.setting_z, hg₁]
      exact (mem_centralizer_iff.mp s.2 _ (D.rep3_mem_Zinf hOut hTw hg₁ hs₀)).symm
    refine ⟨(h.setting.conjBy g₁).conj_mem_QG hsr hyQ, ?_⟩
    exact D.conj_mem_centralizer hOut hTw hg₁ hs₀
      (centralizer_le_normalizer _ s.2) hyS
  have hYp : IsPGroup 2 Y :=
    ((h.setting.conjBy g₁).extraspecial.1.map _).to_le inf_le_left
  have hYB : Y ≤ D.Bgrp g₁ s₀ := D.le_Bgrp_of_normal hOut hTw hg₁ hs₀ hYS hYn hYp
  let f : ↥Y →* (V12 ≃ₗ[ZMod 2] V12) := D.Φo.comp (h.setting.ρ.comp (Subgroup.inclusion hYM))
  have hrange : f.range ≤ Two.p2Grp := by
    rintro _ ⟨y, rfl⟩
    exact rho_mem_of_mem_pre (Subgroup.mem_inf.mp (hYB y.2)).2 _
  have hker : Nat.card f.ker ≤ 2 ^ 7 := by
    rw [← D.card_QG_inf_Qa_g₁ hOut hTw hg₁]
    refine Nat.card_le_card_of_injective (fun y : ↥f.ker =>
      (⟨((y : ↥Y) : G), ?_, (Subgroup.mem_inf.mp (y : ↥Y).2).1⟩ :
        ↥(h.setting.QG ⊓ h.setting.Qa g₁ : Subgroup G))) ?_
    · have h1 : f y = 1 := y.2
      have h2 : D.Φo (h.setting.ρ (Subgroup.inclusion hYM (y : ↥Y))) = D.Φo 1 := by
        rw [map_one]
        exact h1
      exact (h.setting.ρ_eq_one_iff _).mp (D.Φo_injective h2)
    · intro a b hab
      have h' : ((a : ↥Y) : G) = ((b : ↥Y) : G) :=
        congrArg (fun w : ↥(h.setting.QG ⊓ h.setting.Qa g₁ : Subgroup G) => (w : G)) hab
      exact Subtype.ext (Subtype.ext h')
  have hcardY : Nat.card ↥Y = 2 ^ 11 := D.card_Qa_inf_centralizer_Zinf hOut hTw hg₁ hs₀
  have h1 := Subgroup.card_mul_index f.ker
  rw [Subgroup.index_ker, hcardY] at h1
  have hge : Nat.card Two.p2Grp ≤ Nat.card f.range := by
    rw [Two.card_p2Grp]
    have hpos : 0 < Nat.card f.ker := Nat.card_pos
    by_contra hlt
    push Not at hlt
    have : Nat.card f.ker * Nat.card f.range < 2 ^ 7 * 16 :=
      lt_of_le_of_lt (Nat.mul_le_mul_right _ hker) (Nat.mul_lt_mul_of_pos_left hlt (by norm_num))
    rw [h1] at this
    norm_num at this
  have heq : f.range = Two.p2Grp := Subgroup.eq_of_le_of_card_ge hrange hge
  intro b hb
  obtain ⟨hbS, hbP⟩ := Subgroup.mem_inf.mp hb
  have hbM : b ∈ h.setting.M := D.hSM hOut hTw hg₁ hs₀ hbS
  have hbr : D.Φo (h.setting.ρ ⟨b, hbM⟩) ∈ f.range := by
    rw [heq]
    exact rho_mem_of_mem_pre hbP hbM
  obtain ⟨y, hy⟩ := hbr
  have hρ : h.setting.ρ (Subgroup.inclusion hYM y) = h.setting.ρ ⟨b, hbM⟩ := D.Φo_injective hy
  have hq : b * ((y : ↥Y) : G)⁻¹ ∈ h.setting.QG := by
    have : h.setting.ρ (⟨b, hbM⟩ * (Subgroup.inclusion hYM y)⁻¹) = 1 := by
      rw [map_mul, map_inv, hρ, mul_inv_cancel]
    exact (h.setting.ρ_eq_one_iff _).mp this
  have e : b = (b * ((y : ↥Y) : G)⁻¹) * ((y : ↥Y) : G) := by group
  rw [e, D.Kgrp_eq_K0 hOut hTw hg₁ hs₀]
  exact mul_mem (QG_le_K0 g₁ s₀ hq) (Qa₁_le_K0 g₁ s₀ (Subgroup.mem_inf.mp (y : ↥Y).2).1)

theorem Kgrp_inf_eq_Bgrp :
    Kgrp (h := h) g₁ s₀ ⊓ centralizer (Zinf (h := h) g₁ s₀ : Set G) = D.Bgrp g₁ s₀ :=
  le_antisymm (D.Kgrp_inf_le_Bgrp hOut hTw hg₁ hs₀)
    (le_inf (D.Bgrp_le_Kgrp hOut hTw hg₁ hs₀) (D.Bgrp_le_centralizer hOut hTw hg₁ hs₀))

end FourS

end Data41

end CFSG.Quasithin.H13.AS91
