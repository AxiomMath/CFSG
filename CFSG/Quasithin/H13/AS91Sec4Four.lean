module

public import CFSG.Quasithin.H13.AS91Sec4FourS
public import CFSG.Quasithin.H13.AS91Sec4DefsB

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13.AS91

open Subgroup Module CFSG.Open CFSG.LargeExtraspecial CFSG.Quasithin CFSG.Quasithin.HatM22
open CFSG.GF2Type.Smith1979.GammaU CFSG.GF2Type.Smith1979.GammaU.StepA
open CFSG.GF2Type.Smith1979.GammaU.Viol CFSG.GF2Type.Smith1979.GammaU.Enum
open CFSG.GF2Type.Smith1979.IdxFour
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem polar_vecOf (a b : ℕ) : QuadraticMap.polar q0 (vecOf a) (vecOf b) =
    (if q0b (a ^^^ b) then 1 else 0) - (if q0b a then 1 else 0) - (if q0b b then 1 else 0) := by
  rw [QuadraticMap.polar, ← vecOf_xor, q0_vecOf, q0_vecOf, q0_vecOf]

namespace Data41

variable {z : G} {h : HypJ4 G z} (D : Data41 h)

theorem polar_ψV (a b : h.setting.Qt) :
    QuadraticMap.polar h.setting.q a b = QuadraticMap.polar q0 (D.ψV a) (D.ψV b) := by
  have hq : ∀ v, q0 (D.ψV v) = h.setting.q v := fun v => by
    rw [← D.q_ψV_symm, AddEquiv.symm_apply_apply]
  rw [QuadraticMap.polar, QuadraticMap.polar, ← map_add D.ψV, hq, hq, hq]

section FourC

variable
  (hOut : KG82HatM22Out) (hTw : KG82HatM22Twelve) {g₁ : G} (hg₁ : g₁ * z * g₁⁻¹ = D.rep 3)
  {s₀ : h.setting.M} (hs₀ : D.Φo (h.setting.ρ s₀) = Two.tE)

include hOut hTw hg₁ hs₀

theorem mem_Zinf_of_forall_conj {x : G}
    (hx : ∀ n ∈ normalizer (Zinf (h := h) g₁ s₀ : Set G), n⁻¹ * x * n ∈ h.setting.QG) :
    x ∈ Zinf (h := h) g₁ s₀ := by
  have hQa : ∀ g : G, g * z * g⁻¹ ∈ Zinf (h := h) g₁ s₀ → x ∈ h.setting.Qa g := by
    intro g hg
    obtain ⟨n, hn, he⟩ := D.exists_Qa_eq hOut hTw hg₁ hs₀ hg
    rw [he, Setting.Qa_eq_map]
    refine ⟨n⁻¹ * x * n, hx n (D.K0_le_normalizer hOut hTw hg₁ hs₀ hn), ?_⟩
    show n * (n⁻¹ * x * n) * n⁻¹ = x
    group
  rw [Zinf_eq]
  refine ⟨⟨?_, hQa g₁ ?_⟩, hQa _ ?_⟩
  · simpa using hx 1 (one_mem _)
  · rw [hg₁]
    exact D.rep3_mem_Zinf hOut hTw hg₁ hs₀
  · have := D.conjBy₂_z_mem hOut hTw hg₁ hs₀
    rwa [Setting.conjBy_z, h.setting_z] at this

theorem conj_mem_R {n : G} (hn : n ∈ normalizer (Zinf (h := h) g₁ s₀ : Set G)) {x : G}
    (hx : x ∈ Kgrp (h := h) g₁ s₀ ⊓ centralizer (Zinf (h := h) g₁ s₀ : Set G)) :
    n * x * n⁻¹ ∈ Kgrp (h := h) g₁ s₀ ⊓ centralizer (Zinf (h := h) g₁ s₀ : Set G) :=
  ⟨conj_mem_Kgrp (h := h) hn hx.1, D.conj_mem_centralizer hOut hTw hg₁ hs₀ hn hx.2⟩

theorem Φo_mem_p2 {x : G}
    (hx : x ∈ Kgrp (h := h) g₁ s₀ ⊓ centralizer (Zinf (h := h) g₁ s₀ : Set G))
    (hxM : x ∈ h.setting.M) : D.Φo (h.setting.ρ ⟨x, hxM⟩) ∈ Two.p2Grp := by
  rw [D.Kgrp_inf_eq_Bgrp hOut hTw hg₁ hs₀] at hx
  exact rho_mem_of_mem_pre (Subgroup.mem_inf.mp hx).2 hxM

theorem sq_mem_Zinf {x : G}
    (hx : x ∈ Kgrp (h := h) g₁ s₀ ⊓ centralizer (Zinf (h := h) g₁ s₀ : Set G)) :
    x * x ∈ Zinf (h := h) g₁ s₀ := by
  refine D.mem_Zinf_of_forall_conj hOut hTw hg₁ hs₀ fun n hn => ?_
  have hy := D.conj_mem_R hOut hTw hg₁ hs₀ (inv_mem hn) hx
  have hyM := D.hSM hOut hTw hg₁ hs₀ hy.2
  have hp := D.Φo_mem_p2 hOut hTw hg₁ hs₀ hy hyM
  have h1 : h.setting.ρ (⟨_, hyM⟩ * ⟨_, hyM⟩) = 1 := by
    apply D.Φo_injective
    rw [map_mul, map_mul, Two.p2Grp_sq hp, map_one]
  have e : n⁻¹ * (x * x) * n = (n⁻¹ * x * n⁻¹⁻¹) * (n⁻¹ * x * n⁻¹⁻¹) := by group
  rw [e]
  exact (h.setting.ρ_eq_one_iff _).mp h1

theorem commutator_mem_Zinf {x y : G}
    (hx : x ∈ Kgrp (h := h) g₁ s₀ ⊓ centralizer (Zinf (h := h) g₁ s₀ : Set G))
    (hy : y ∈ Kgrp (h := h) g₁ s₀ ⊓ centralizer (Zinf (h := h) g₁ s₀ : Set G)) :
    ⁅x, y⁆ ∈ Zinf (h := h) g₁ s₀ := by
  refine D.mem_Zinf_of_forall_conj hOut hTw hg₁ hs₀ fun n hn => ?_
  have hx' := D.conj_mem_R hOut hTw hg₁ hs₀ (inv_mem hn) hx
  have hy' := D.conj_mem_R hOut hTw hg₁ hs₀ (inv_mem hn) hy
  have hxM := D.hSM hOut hTw hg₁ hs₀ hx'.2
  have hyM := D.hSM hOut hTw hg₁ hs₀ hy'.2
  have hc := Two.p2Grp_comm (D.Φo_mem_p2 hOut hTw hg₁ hs₀ hx' hxM)
    (D.Φo_mem_p2 hOut hTw hg₁ hs₀ hy' hyM)
  have h1 : h.setting.ρ (⟨_, hxM⟩ * ⟨_, hyM⟩ * (⟨_, hxM⟩ : h.setting.M)⁻¹ *
      (⟨_, hyM⟩ : h.setting.M)⁻¹) = 1 := by
    apply D.Φo_injective
    rw [map_one, map_mul, map_mul, map_mul, map_inv, map_inv, map_mul, map_mul, map_mul, map_inv,
      map_inv, hc]
    group
  have e : n⁻¹ * ⁅x, y⁆ * n = (n⁻¹ * x * n⁻¹⁻¹) * (n⁻¹ * y * n⁻¹⁻¹) *
      (n⁻¹ * x * n⁻¹⁻¹)⁻¹ * (n⁻¹ * y * n⁻¹⁻¹)⁻¹ := by
    rw [commutatorElement_def]
    group
  rw [e]
  exact (h.setting.ρ_eq_one_iff _).mp h1

theorem rep_mem_CQZ {n : ℕ} (h3 : QuadraticMap.polar q0 (vecOf 3) (vecOf n) = 0)
    (h192 : QuadraticMap.polar q0 (vecOf 192) (vecOf n) = 0) :
    D.rep n ∈ h.setting.QG ⊓ centralizer (Zinf (h := h) g₁ s₀ : Set G) := by
  refine Subgroup.mem_inf.mpr ⟨D.rep_mem n, ?_⟩
  rw [← D.closure_eq_Zinf hOut hTw hg₁ hs₀, centralizer_closure, mem_centralizer_iff]
  have hk : ((s₀ : G) * g₁) * z * ((s₀ : G) * g₁)⁻¹ = (s₀ : G) * D.rep 3 * (s₀ : G)⁻¹ := by
    rw [← hg₁]
    group
  rintro y (rfl | rfl | rfl)
  · exact (h.setting.z_comm_QG (D.rep_mem n)).symm
  · rw [hg₁]
    refine (h.setting.polar_cl_eq_zero_iff (D.rep_mem 3) (D.rep_mem n)).mp ?_
    rw [D.polar_ψV, ψV_cl_rep, ψV_cl_rep]
    exact h3
  · rw [hk]
    refine (h.setting.polar_cl_eq_zero_iff (h.setting.conj_mem_QG s₀.2 (D.rep_mem 3))
      (D.rep_mem n)).mp ?_
    rw [D.polar_ψV, D.ψV_cl_conj_rep3 hOut hTw hg₁ hs₀, ψV_cl_rep]
    exact h192

theorem CQZ_le_R : h.setting.QG ⊓ centralizer (Zinf (h := h) g₁ s₀ : Set G) ≤
    Kgrp (h := h) g₁ s₀ ⊓ centralizer (Zinf (h := h) g₁ s₀ : Set G) := by
  rw [D.Kgrp_inf_eq_Bgrp hOut hTw hg₁ hs₀]
  exact D.QG_inf_le_Bgrp hOut hTw hg₁ hs₀

theorem center_le_QG {y : ↥(Kgrp (h := h) g₁ s₀ ⊓ centralizer (Zinf (h := h) g₁ s₀ : Set G))}
    (hy : y ∈ center ↥(Kgrp (h := h) g₁ s₀ ⊓ centralizer (Zinf (h := h) g₁ s₀ : Set G))) :
    (y : G) ∈ h.setting.QG := by
  have hyM := D.hSM hOut hTw hg₁ hs₀ y.2.2
  have hfix : ∀ n : ℕ, QuadraticMap.polar q0 (vecOf 3) (vecOf n) = 0 →
      QuadraticMap.polar q0 (vecOf 192) (vecOf n) = 0 →
      D.Φo (h.setting.ρ ⟨y, hyM⟩) (vecOf n) = vecOf n := by
    intro n h3 h192
    have hR := D.CQZ_le_R hOut hTw hg₁ hs₀ (D.rep_mem_CQZ hOut hTw hg₁ hs₀ h3 h192)
    have hc : (y : G) * D.rep n = D.rep n * y :=
      congrArg Subtype.val (mem_center_iff.mp hy ⟨_, hR⟩).symm
    rw [← D.ψV_cl_rep n, Φo_apply_ψV, h.setting.ρ_cl _ (D.rep_mem n)]
    show D.ψV (h.setting.cl ((y : G) * D.rep n * (y : G)⁻¹)) = _
    rw [hc, mul_inv_cancel_right]
  have h1 := Two.eq_one_of_fix_perp (D.Φo_mem_p2 hOut hTw hg₁ hs₀ y.2 hyM)
    (hfix 4 (by rw [polar_vecOf]; decide) (by rw [polar_vecOf]; decide))
    (hfix 24 (by rw [polar_vecOf]; decide) (by rw [polar_vecOf]; decide))
  rw [← map_one D.Φo] at h1
  exact (h.setting.ρ_eq_one_iff _).mp (D.Φo_injective h1)

theorem center_R : (center ↥(Kgrp (h := h) g₁ s₀ ⊓ centralizer (Zinf (h := h) g₁ s₀ : Set G))).map
    (Kgrp (h := h) g₁ s₀ ⊓ centralizer (Zinf (h := h) g₁ s₀ : Set G)).subtype =
      Zinf (h := h) g₁ s₀ := by
  apply le_antisymm
  · rintro _ ⟨y, hy, rfl⟩
    refine D.mem_Zinf_of_forall_conj hOut hTw hg₁ hs₀ fun n hn => ?_
    have hR := D.conj_mem_R hOut hTw hg₁ hs₀ (inv_mem hn) y.2
    have hc : (⟨_, hR⟩ : ↥(Kgrp (h := h) g₁ s₀ ⊓ centralizer (Zinf (h := h) g₁ s₀ : Set G))) ∈
        center _ := by
      refine mem_center_iff.mpr fun r => Subtype.ext ?_
      have hr := D.conj_mem_R hOut hTw hg₁ hs₀ hn r.2
      have := congrArg Subtype.val (mem_center_iff.mp hy ⟨_, hr⟩)
      simp only [Subgroup.coe_mul] at this ⊢
      calc (r : G) * (n⁻¹ * y * n⁻¹⁻¹) = n⁻¹ * ((n * r * n⁻¹) * y) * n := by group
        _ = n⁻¹ * (y * (n * r * n⁻¹)) * n := by rw [this]
        _ = n⁻¹ * y * n⁻¹⁻¹ * r := by group
    have := D.center_le_QG hOut hTw hg₁ hs₀ hc
    simpa using this
  · intro a ha
    have hcomm := (D.isElemAbelian_Zinf hOut hTw hg₁ hs₀).1
    have haC : a ∈ centralizer (Zinf (h := h) g₁ s₀ : Set G) := by
      rw [mem_centralizer_iff]
      intro b hb
      exact congrArg Subtype.val (hcomm.is_comm.comm ⟨b, hb⟩ ⟨a, ha⟩)
    have haR := D.CQZ_le_R hOut hTw hg₁ hs₀ ⟨Zinf_le_QG g₁ s₀ ha, haC⟩
    refine ⟨⟨a, haR⟩, mem_center_iff.mpr fun r => Subtype.ext ?_, rfl⟩
    exact (mem_centralizer_iff.mp r.2.2 a ha).symm

theorem comm_R : ⁅Kgrp (h := h) g₁ s₀ ⊓ centralizer (Zinf (h := h) g₁ s₀ : Set G),
    Kgrp (h := h) g₁ s₀ ⊓ centralizer (Zinf (h := h) g₁ s₀ : Set G)⁆ = Zinf (h := h) g₁ s₀ := by
  apply le_antisymm
  · rw [commutator_le]
    exact fun x hx y hy => D.commutator_mem_Zinf hOut hTw hg₁ hs₀ hx hy
  ·
    obtain ⟨x, hx, y, hy, hxy⟩ : ∃ x ∈ h.setting.QG ⊓ centralizer (Zinf (h := h) g₁ s₀ : Set G),
        ∃ y ∈ h.setting.QG ⊓ centralizer (Zinf (h := h) g₁ s₀ : Set G), x * y ≠ y * x := by
      by_contra hc
      push Not at hc
      have h1 := h.setting.card_le_of_commute inf_le_left hc
      rw [D.card_QG_inf_centralizer_Zinf hOut hTw hg₁ hs₀, h.setting_width] at h1
      norm_num at h1
    have hz : ⁅x, y⁆ = z := by
      rcases h.setting.commutator_eq_one_or_z hx.1 hy.1 with h1 | h1
      · exact absurd (by
          calc x * y = (x * y * x⁻¹ * y⁻¹) * (y * x) := by group
            _ = y * x := by rw [h1, one_mul]) hxy
      · rw [commutatorElement_def]
        exact h1
    have hxR := D.CQZ_le_R hOut hTw hg₁ hs₀ hx
    have hyR := D.CQZ_le_R hOut hTw hg₁ hs₀ hy
    intro a ha
    by_cases ha1 : a = 1
    · rw [ha1]
      exact one_mem _
    obtain ⟨n, hn, rfl⟩ := D.exists_conj_eq_of_mem hOut hTw hg₁ hs₀ ha ha1
    have hnN := D.K0_le_normalizer hOut hTw hg₁ hs₀ hn
    have e : n * z * n⁻¹ = ⁅n * x * n⁻¹, n * y * n⁻¹⁆ := by
      rw [← hz, commutatorElement_def, commutatorElement_def]
      group
    rw [e]
    exact commutator_mem_commutator (D.conj_mem_R hOut hTw hg₁ hs₀ hnN hxR)
      (D.conj_mem_R hOut hTw hg₁ hs₀ hnN hyR)

theorem card_R : Nat.card ↥(Kgrp (h := h) g₁ s₀ ⊓ centralizer (Zinf (h := h) g₁ s₀ : Set G)) =
    2 ^ 15 := by
  rw [D.Kgrp_inf_eq_Bgrp hOut hTw hg₁ hs₀]
  exact D.card_Bgrp hOut hTw hg₁ hs₀

theorem isPGroup_R :
    IsPGroup 2 ↥(Kgrp (h := h) g₁ s₀ ⊓ centralizer (Zinf (h := h) g₁ s₀ : Set G)) :=
  IsPGroup.of_card (n := 15) (D.card_R hOut hTw hg₁ hs₀)

theorem R_eq_pCoreOf_K : Kgrp (h := h) g₁ s₀ ⊓ centralizer (Zinf (h := h) g₁ s₀ : Set G) =
    pCoreOf 2 (Kgrp (h := h) g₁ s₀) := by
  obtain ⟨-, φ, hφs, hφk⟩ := D.K_facts hOut hTw hg₁ hs₀
  refine (pCoreOf_eq_of inf_le_left ?_ (D.isPGroup_R hOut hTw hg₁ hs₀) ?_).symm
  · rw [← hφk]
    exact φ.normal_ker
  · intro X hXn hXp
    haveI := CFSG.ComponentClassification.GHarris.isSimpleGroup_GL32_gh
    haveI := hXn.map φ hφs
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (X.map φ) with hb | ht
    · intro x hx
      rw [← hφk, MonoidHom.mem_ker]
      have : φ x ∈ X.map φ := ⟨x, hx, rfl⟩
      rw [hb] at this
      exact this
    · exfalso
      have hp := hXp.map φ
      rw [ht] at hp
      obtain ⟨k, hk⟩ := hp.exists_card_eq
      rw [Subgroup.card_top, CFSG.ComponentClassification.GHarris.card_GL32_gh] at hk
      have h3 : 3 ∣ 2 ^ k := by rw [← hk]; norm_num
      exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3) (by norm_num)

theorem R_eq_pCoreOf_S : Kgrp (h := h) g₁ s₀ ⊓ centralizer (Zinf (h := h) g₁ s₀ : Set G) =
    pCoreOf 2 (centralizer (Zinf (h := h) g₁ s₀ : Set G)) := by
  refine (pCoreOf_eq_of inf_le_right ?_ (D.isPGroup_R hOut hTw hg₁ hs₀) ?_).symm
  · rw [D.Kgrp_inf_eq_Bgrp hOut hTw hg₁ hs₀]
    exact D.Bgrp_normal_S hOut hTw hg₁ hs₀
  · intro X hXn hXp
    rw [D.Kgrp_inf_eq_Bgrp hOut hTw hg₁ hs₀]
    have hle := D.le_Bgrp_of_normal hOut hTw hg₁ hs₀ (P := X.map (centralizer
      (Zinf (h := h) g₁ s₀ : Set G)).subtype) (map_subtype_le _)
      (by
        have e : (X.map (centralizer (Zinf (h := h) g₁ s₀ : Set G)).subtype).subgroupOf
            (centralizer (Zinf (h := h) g₁ s₀ : Set G)) = X :=
          Subgroup.comap_map_eq_self_of_injective (Subgroup.subtype_injective _) X
        rw [e]
        exact hXn) (hXp.map _)
    intro x hx
    exact mem_subgroupOf.mpr (hle ⟨x, hx, rfl⟩)

theorem S_quot : ∃ φ : ↥(centralizer (Zinf (h := h) g₁ s₀ : Set G)) →* Equiv.Perm (Fin 5),
    Function.Surjective φ ∧
      φ.ker = (Kgrp (h := h) g₁ s₀ ⊓ centralizer (Zinf (h := h) g₁ s₀ : Set G)).subgroupOf
        (centralizer (Zinf (h := h) g₁ s₀ : Set G)) := by
  rw [D.Kgrp_inf_eq_Bgrp hOut hTw hg₁ hs₀]
  exact D.exists_phiS hOut hTw hg₁ hs₀

end FourC

@[expose] noncomputable def toLoc44
    (hHat : HatM22SmallModules)
    (hOut : KG82HatM22Out) (hTw : KG82HatM22Twelve) : Loc44 G z where
  toLoc43 := D.toLoc43 hHat hOut hTw
  K := Kgrp (h := h) (D.exists_g₁ hOut hTw).choose (D.exists_s₀ hOut hTw).choose
  K_eq := rfl
  R := Kgrp (h := h) (D.exists_g₁ hOut hTw).choose (D.exists_s₀ hOut hTw).choose ⊓
    centralizer (Zinf (h := h) (D.exists_g₁ hOut hTw).choose (D.exists_s₀ hOut hTw).choose : Set G)
  normalizer_eq := (D.K_facts hOut hTw (D.exists_g₁ hOut hTw).choose_spec
    (D.exists_s₀ hOut hTw).choose_spec).1
  K_normal := fun _ hn _ hk => conj_mem_Kgrp (h := h) hn hk
  K_inf := rfl
  R_eq_K := D.R_eq_pCoreOf_K hOut hTw (D.exists_g₁ hOut hTw).choose_spec
    (D.exists_s₀ hOut hTw).choose_spec
  R_eq_S := D.R_eq_pCoreOf_S hOut hTw (D.exists_g₁ hOut hTw).choose_spec
    (D.exists_s₀ hOut hTw).choose_spec
  K_quot := (D.K_facts hOut hTw (D.exists_g₁ hOut hTw).choose_spec
    (D.exists_s₀ hOut hTw).choose_spec).2
  S_quot := D.S_quot hOut hTw (D.exists_g₁ hOut hTw).choose_spec
    (D.exists_s₀ hOut hTw).choose_spec
  card_R := D.card_R hOut hTw (D.exists_g₁ hOut hTw).choose_spec
    (D.exists_s₀ hOut hTw).choose_spec
  center_R := D.center_R hOut hTw (D.exists_g₁ hOut hTw).choose_spec
    (D.exists_s₀ hOut hTw).choose_spec
  comm_R := D.comm_R hOut hTw (D.exists_g₁ hOut hTw).choose_spec
    (D.exists_s₀ hOut hTw).choose_spec
  sq_R := fun _ hx => D.sq_mem_Zinf hOut hTw (D.exists_g₁ hOut hTw).choose_spec
    (D.exists_s₀ hOut hTw).choose_spec hx

end Data41

end CFSG.Quasithin.H13.AS91
