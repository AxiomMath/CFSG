module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11E3C9Prod
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11E3ParaZ
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11E3C9K1A

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

private lemma s1611e3_c9k1_fac_168 : Nat.factorization (168 * 168) 2 = 6 := by
  rw [Nat.factorization_def (168 * 168) (by norm_num : Nat.Prime 2)]
  rw [padicValNat.mul (by norm_num) (by norm_num)]
  have h : padicValNat 2 168 = 3 := by
    have h := padicValNat_base_pow_mul (p := 2) (n := 21) (by norm_num) (by norm_num) 3
    norm_num at h
    rw [h, show padicValNat 2 21 = 0 from by rw [padicValNat.eq_zero_iff]; omega]
  rw [h]

private theorem s1611e3_c9k1_mem_centSub_zpowers_iff' {W : Type} [CommGroup W] (l : MulAut W)
    (w : W) : l ∈ centSub (Subgroup.zpowers w) ↔ l w = w := by
  refine ⟨fun h => h w (Subgroup.mem_zpowers w), fun h u hu => ?_⟩
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
  rw [map_zpow, h]

theorem s1611e3_case9_exists_three {D : Data G} (h : S1611e3Std D) {V₀ V L : Subgroup G}
    {hV : IsElemAbelian 2 V} (hc : Counterex16 D V₀ V L hV) (h9 : Case168_9 D V₀ V hV L) :
    ∃ Xbar : Subgroup (MulAut (Vtil V₀ V hV)), Xbar ≤ Mbar D.M V₀ V hV ∧ IsPGroup 3 ↥Xbar ∧
      ¬ IsCyclic ↥Xbar ∧ (∀ x ∈ Xbar, x ^ 3 = 1) ∧ Permutes Xbar (barSub V₀ V hV D.T) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x, hxT, hcomm, hinf, hEeq, hfixB, hfixA, hWinf, hWsup, hsyl⟩ :=
    s1611e3_case9_prod h hc h9
  have h9' := h9
  obtain ⟨⟨e⟩, hL3, hs15, hsum, hsig⟩ := h9'
  let Lb : Subgroup (MulAut (Vtil V₀ V hV)) := lBar V₀ V hV L
  let Lp : Subgroup (MulAut (Vtil V₀ V hV)) :=
    (lBar V₀ V hV L).map (MulAut.conj x).toMonoidHom
  let Wt : Subgroup (Vtil V₀ V hV) := wTil V₀ V hV L
  let Wp : Subgroup (Vtil V₀ V hV) := (wTil V₀ V hV L).map x.toMonoidHom
  let Tb : Subgroup (MulAut (Vtil V₀ V hV)) := barSub V₀ V hV D.T
  let Mb : Subgroup (MulAut (Vtil V₀ V hV)) := Mbar D.M V₀ V hV
  have hMstab : D.M ≤ stabTil V₀ V :=
    le_stabTil hc.setting.hyp151.hyp125.pairFacts.le_normalizer
      hc.setting.hyp151.hyp125.pairFacts.le_normalizer₀
  have hTsyl : IsSylowIn 2 Tb Mb :=
    s1611e3_barSub_sylow hMstab (CFSG.ABGLocalTools.isSylowOf_iff.1 D.sylowM)
  have hxMb : x ∈ Mb := hTsyl.le hxT
  have hLb_ne_bot : Lb ≠ ⊥ := by
    intro hbot
    exact hc.ne_bot (by simpa [Lb, lBar] using hbot)
  have hcls : Set.ncard {Y : Subgroup (MulAut (Vtil V₀ V hV)) |
      ∃ φ ∈ Mb, Y = Lb.map (MulAut.conj φ).toMonoidHom} = 2 := by
    simpa [s15, lBar, Lb, Mb] using hs15
  have hLb_x2 : Lb.map (MulAut.conj (x * x)).toMonoidHom = Lb :=
    s1611e3_c9k1_sq_normalizes hxMb rfl hcls hLb_ne_bot hinf
  have hxB : Wp.map x.toMonoidHom = Wt := by
    have hconj2 : x.toMonoidHom.comp x.toMonoidHom = (x * x).toMonoidHom := by ext y; rfl
    have h1 : (commSub (⊤ : Subgroup (Vtil V₀ V hV)) Lb).map (x * x).toMonoidHom =
        commSub (⊤ : Subgroup (Vtil V₀ V hV)) Lb := by
      have hh := s16c167_commSub_top_conj (x * x) Lb
      rw [hLb_x2] at hh
      exact hh.symm
    show (Wt.map x.toMonoidHom).map x.toMonoidHom = Wt
    rw [Subgroup.map_map, hconj2]
    exact h1
  have hWp_eq : commSub (⊤ : Subgroup (Vtil V₀ V hV)) Lp = Wp :=
    s16c167_commSub_top_conj x Lb
  have hAinv : ∀ a ∈ Lb, ∀ u ∈ Wt, a u ∈ Wt := by
    intro a ha u hu
    have hmap : Lb.map (MulAut.conj a).toMonoidHom = Lb :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer ha)
    have hh := s16c167_commSub_top_conj a Lb
    rw [hmap] at hh
    have hmem : a u ∈ (commSub (⊤ : Subgroup (Vtil V₀ V hV)) Lb).map a.toMonoidHom :=
      Subgroup.mem_map_of_mem a.toMonoidHom hu
    rw [← hh] at hmem
    exact hmem
  have hBinv : ∀ b ∈ Lp, ∀ u ∈ Wp, b u ∈ Wp := by
    intro b hb u hu
    have hmap : Lp.map (MulAut.conj b).toMonoidHom = Lp :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer hb)
    have hh := s16c167_commSub_top_conj b Lp
    rw [hmap] at hh
    have hmem : b u ∈ (commSub (⊤ : Subgroup (Vtil V₀ V hV)) Lp).map b.toMonoidHom := by
      rw [hWp_eq]
      exact Subgroup.mem_map_of_mem b.toMonoidHom hu
    rw [← hh] at hmem
    rwa [← hWp_eq]
  have hFn : ∀ y ∈ Mb, ∀ f ∈ Fstar (Mbar D.M V₀ V hV), y * f * y⁻¹ ∈
      Fstar (Mbar D.M V₀ V hV) :=
    (s16c167_cfg10_fstar_facts (Mbar D.M V₀ V hV)).2.1
  have hFX : Fstar (Mbar D.M V₀ V hV) ≤ Mb :=
    (s16c167_cfg10_fstar_facts (Mbar D.M V₀ V hV)).1
  have hEMb : (commutator ↥(Fstar (Mbar D.M V₀ V hV))).map
      (Fstar (Mbar D.M V₀ V hV)).subtype ≤ Mb := by
    rw [Subgroup.map_subtype_commutator]
    exact (Subgroup.commutator_le_self (Fstar (Mbar D.M V₀ V hV))).trans hFX
  have hTnorm : ∀ t ∈ Tb, ∀ y ∈ Lb ⊔ Lp, t * y * t⁻¹ ∈ Lb ⊔ Lp := by
    intro t ht y hy
    have htMb : t ∈ Mb := hTsyl.le ht
    rw [← hEeq] at hy ⊢
    exact s1611e3_commutator_conj_mem hFn t htMb y hy
  have hEnorm : (((commutator ↥(Fstar (Mbar D.M V₀ V hV))).map
      (Fstar (Mbar D.M V₀ V hV)).subtype).subgroupOf Mb).Normal :=
    (Subgroup.normal_subgroupOf_iff hEMb).2 fun hh k hhk hk =>
      s1611e3_commutator_conj_mem hFn k hk hh hhk
  have hperfLb : Group.IsPerfect ↥Lb :=
    s16c167_isPSL_isPerfect (s16c167_isPSL_of_isL3 hL3)
  have hEcard : Nat.card ↥((commutator ↥(Fstar (Mbar D.M V₀ V hV))).map
      (Fstar (Mbar D.M V₀ V hV)).subtype) = 168 * 168 := by
    rw [Subgroup.card_map_of_injective
      (f := (Fstar (Mbar D.M V₀ V hV)).subtype) (Fstar (Mbar D.M V₀ V hV)).subtype_injective,
      s1611e3_commutator_card (F := ↥(Fstar (Mbar D.M V₀ V hV))) hperfLb e,
      card_eq_of_isL3 hL3]
  have hTEsyl : IsSylowIn 2 (Tb ⊓ (commutator ↥(Fstar (Mbar D.M V₀ V hV))).map
      (Fstar (Mbar D.M V₀ V hV)).subtype)
      ((commutator ↥(Fstar (Mbar D.M V₀ V hV))).map
      (Fstar (Mbar D.M V₀ V hV)).subtype) :=
    IsSylowIn.inf_normal hTsyl hEMb hEnorm
  have hTEcard : Nat.card ↥(Tb ⊓ (commutator ↥(Fstar (Mbar D.M V₀ V hV))).map
      (Fstar (Mbar D.M V₀ V hV)).subtype) = 64 := by
    rw [IsSylowIn.card_eq hTEsyl, hEcard, s1611e3_c9k1_fac_168]
    norm_num
  have hcardTE : Nat.card ↥(Tb ⊓ (Lb ⊔ Lp)) = 64 := by
    rw [← hEeq]
    exact hTEcard
  have hv1Sub : v1Sub D.M V₀ V hV L = V₀ := s1611e3_nine_v1Sub h9
  obtain ⟨Z, hZcard, -, hZL, hZJ, hZf, -⟩ :=
    s16t_case9_frame D h.h1217 hV hc hv1Sub h9
  have hstabA : ∀ w ∈ Wt ⊓ fixV (Tb ⊓ Lb), w ≠ 1 →
      Nat.card ↥(Lb ⊓ centSub (Subgroup.zpowers w)) = 24 :=
    s1611e3_para_stab hL3 (Or.inr ⟨rfl, rfl⟩) hsum inf_le_right hsyl hZcard hZJ hZL hZf
  have hstabB : ∀ u ∈ Wp ⊓ fixV (Tb ⊓ Lp), u ≠ 1 →
      Nat.card ↥(Lp ⊓ centSub (Subgroup.zpowers u)) = 24 := by
    intro u hu hu1
    obtain ⟨w, hwWt, hxw⟩ := Subgroup.mem_map.mp hu.1
    have hxw' : x w = u := hxw
    have hw1 : w ≠ 1 := by
      intro hw
      exact hu1 (by rw [← hxw, hw, map_one])
    have hwfix : w ∈ fixV (Tb ⊓ Lb) := by
      rw [mem_fixV]
      intro t ht
      have hxt : x * t * x⁻¹ ∈ Tb ⊓ Lp := by
        refine ⟨Tb.mul_mem (Tb.mul_mem hxT ht.1) (Tb.inv_mem hxT), ?_⟩
        show x * t * x⁻¹ ∈ Lb.map (MulAut.conj x).toMonoidHom
        exact Subgroup.mem_map.mpr ⟨t, ht.2, by simp [MulAut.conj_apply]⟩
      have hu_fix : (x * t * x⁻¹) u = u := (mem_fixV.1 hu.2) (x * t * x⁻¹) hxt
      have h1 : x (t w) = x w := by
        have h := hu_fix
        rw [← hxw', MulAut.mul_apply, MulAut.mul_apply] at h
        simpa using h
      exact x.injective h1
    have h24 : Nat.card ↥(Lb ⊓ centSub (Subgroup.zpowers w)) = 24 :=
      hstabA w (Subgroup.mem_inf.2 ⟨hwWt, hwfix⟩) hw1
    have hcent : (centSub (Subgroup.zpowers w)).map (MulAut.conj x).toMonoidHom =
        centSub (Subgroup.zpowers (x w)) := by
      ext y
      rw [Subgroup.mem_map]
      constructor
      · rintro ⟨a, ha, rfl⟩
        rw [s1611e3_c9k1_mem_centSub_zpowers_iff'] at ha ⊢
        show MulAut.conj x a (x w) = x w
        simp only [MulAut.conj_apply, MulAut.mul_apply]
        rw [show x⁻¹ (x w) = w by simp, ha]
      · intro hy
        rw [s1611e3_c9k1_mem_centSub_zpowers_iff'] at hy
        refine ⟨(MulAut.conj x)⁻¹ y, ?_, ?_⟩
        · rw [s1611e3_c9k1_mem_centSub_zpowers_iff']
          show ((MulAut.conj x)⁻¹ y) w = w
          have hy' : y (x w) = x w := hy
          rw [show (MulAut.conj x)⁻¹ = MulAut.conj x⁻¹ from map_inv MulAut.conj x]
          simp only [MulAut.conj_apply, MulAut.mul_apply, inv_inv]
          rw [hy']
          simp
        · rw [show (MulAut.conj x)⁻¹ = MulAut.conj x⁻¹ from map_inv MulAut.conj x]
          show MulAut.conj x (MulAut.conj x⁻¹ y) = y
          simp only [MulAut.conj_apply, MulAut.mul_apply, inv_inv]
          group
    have hLpX : (Lb ⊓ centSub (Subgroup.zpowers w)).map (MulAut.conj x).toMonoidHom =
        Lp ⊓ centSub (Subgroup.zpowers u) := by
      rw [Subgroup.map_inf Lb (centSub (Subgroup.zpowers w)) (MulAut.conj x).toMonoidHom
        (MulAut.conj x).injective, hcent, hxw']
    rw [← hLpX, Subgroup.card_map_of_injective (MulAut.conj x).injective]
    exact h24
  have hcardW : 2 ∣ Nat.card (Vtil V₀ V hV) := by
    have hrk : rk ↥(⊤ : Subgroup (Vtil V₀ V hV)) = 18 :=
      s16t_case9_rk_top D h.h1217 hV hc.setting.hyp151 hv1Sub hc.ne_bot hs15 hsum
    have hc2 : Nat.card (Vtil V₀ V hV) = 2 ^ 18 := by
      have hh := card_eq_two_pow (s15_Infra_vtil_sq_eq_one V₀ V hV)
        (⊤ : Subgroup (Vtil V₀ V hV))
      rw [Subgroup.card_top, hrk] at hh
      exact hh
    rw [hc2]
    norm_num
  obtain ⟨Xbar, hXle, hXp, hXnc, hXexp, hXperm⟩ :=
    s1611e3_c9k1_engine (W := Vtil V₀ V hV) (L := Lb) (Q := Lp) (T := Tb)
      (A := Wt) (B := Wp) (x := x) hcomm hinf hTsyl.isPGroup hxT hTnorm hAinv hBinv rfl
      hWsup hWinf hxB hfixB hfixA hcardTE hstabA hstabB hcardW
  exact ⟨Xbar, hXle.trans (hEeq ▸ hEMb), hXp, hXnc, hXexp, hXperm⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
