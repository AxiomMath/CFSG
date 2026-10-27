module

public import CFSG.RankThree.GF2n.Stroth78.Sec2SeventeenClaim

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

public section

namespace CFSG.RankThree.GF2n.Stroth78

open CFSG CFSG.Open CFSG.RankThree.GF2n.Tim79a CFSG.LargeExtraspecial.Timmesfeld
open CFSG.RankThree.OrthogonalInvolutions
open Module
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {z : G} {E F : Subgroup G}

theorem rbar_eq_bot_of_centerIn_le_Q (S : Setting z E F) (a : G)
    (h : centerIn (QaOf a) ≤ Q z) : Rbar S a = ⊥ := by
  rw [← map_R0_eq_Rbar S a, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
  intro s hs
  exact Subgroup.mem_subgroupOf.mpr
    (h (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hs)).1)

theorem aV_eq_zero_of_mem_ZQ (S : Setting z E F) {a : G} (haQ : a ∈ Q z) (haZ : a ∈ ZQ z) :
    Additive.ofMul (mkQbar S ⟨a, haQ⟩) = 0 := by
  have h1 : (mkQbar S ⟨a, haQ⟩ : QbarOf S) = 1 := by
    rw [← MonoidHom.mem_ker]
    rw [show (mkQbar S).ker = (ZQ z).subgroupOf (Q z) from QuotientGroup.ker_mk' _]
    exact Subgroup.mem_subgroupOf.mpr haZ
  rw [h1]
  rfl

theorem aV_mem_commSpace_rhoBar_of_mem_Rbar
    (S : Setting z E F) {a : G} (haQ : a ∈ Q z) (hconj : IsConj z a) (haZ : a ∉ ZQ z)
    (hza : z ∈ QaOf a) (hZQa : ¬ centerIn (QaOf a) ≤ Q z)
    {r : Hbar z} (hr : r ∈ Rbar S a) (hr1 : r ≠ 1) :
    Additive.ofMul (mkQbar S ⟨a, haQ⟩) ∈
      commSpace ((rhoBar S r : Additive (QbarOf S) ≃ₗ[ZMod 2] Additive (QbarOf S))) := by
  classical
  letI : Module (ZMod 2) (Additive (Abelianization F)) := modAbF S
  let V := Additive (QbarOf S)
  let aV : V := Additive.ofMul (mkQbar S ⟨a, haQ⟩)
  have hzaZ : z ∉ centerIn (QaOf a) := z_not_mem_centerIn_Qa S haQ hconj haZ hza
  obtain ⟨s, hsZ, hsH, hsQ, hsr⟩ := exists_mem_centerIn_inf_H_of_mem_Rbar S hr hr1
  have hs2 : (s : G) ^ 2 = 1 := sq_eq_one_of_mem_centerIn_QaOf S hconj hsZ
  have haV0 : aV ≠ 0 := aV_ne_zero S haQ haZ
  have hσ : (rhoBar S r : V ≃ₗ[ZMod 2] V) = conjQbar S ⟨s, hsH⟩ := by
    rw [← hsr, rhoBar_apply_mk, rho_apply_mk]
  have hdim : finrank (ZMod 2) (commSpace (conjQbar S ⟨s, hsH⟩)) = 2 :=
    finrank_commSpace_eq_two S haQ hconj haZ hzaZ hsZ hsH hs2 hsQ
  rw [hσ]
  by_contra hnot
  have hex : ∃ u : V, (qS S).polarBilin aV u = 1 := by
    by_contra h
    push Not at h
    refine haV0 ((q_nondegenerate S).1 aV fun w => ?_)
    rcases CFSG.RankThree.Literature.FSmith.zmod2_cases ((qS S).polarBilin aV w) with h1 | h1
    · exact h1
    · exact absurd h1 (h w)
  obtain ⟨u, hu⟩ := hex
  have hkill : ∀ v ∈ QaInterImage S (Q z ⊓ Subgroup.centralizer ({a} : Set G)),
      ((conjQbar S ⟨s, hsH⟩ : V →ₗ[ZMod 2] V) - 1) v = 0 := by
    intro v hv
    have hmem1 : ((conjQbar S ⟨s, hsH⟩ : V →ₗ[ZMod 2] V) - 1) v ∈
        Submodule.span (ZMod 2) {aV} :=
      map_sub_QaInterImage_CQ_le_span S haQ hconj hzaZ hsZ hsH
        (Submodule.mem_map.mpr ⟨v, hv, rfl⟩)
    have hmem2 : ((conjQbar S ⟨s, hsH⟩ : V →ₗ[ZMod 2] V) - 1) v ∈
        commSpace (conjQbar S ⟨s, hsH⟩) := sub_mem_commSpace _ v
    by_contra hne
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem1
    rcases CFSG.RankThree.Literature.FSmith.zmod2_cases c with rfl | rfl
    · rw [zero_smul] at hc
      exact hne hc.symm
    · rw [one_smul] at hc
      have hgoal : Additive.ofMul (mkQbar S ⟨a, haQ⟩) =
          ((conjQbar S ⟨s, hsH⟩ : V →ₗ[ZMod 2] V) - 1) v := hc
      exact hnot (hgoal ▸ hmem2)
  have hu_mem : ∀ v : V, v + ((qS S).polarBilin aV v) • u ∈
      QaInterImage S (Q z ⊓ Subgroup.centralizer ({a} : Set G)) := by
    intro v
    rw [QaInterImage_CQ_eq_orthogonal S haQ]
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro x hx
    rw [Submodule.mem_span_singleton] at hx
    obtain ⟨d, rfl⟩ := hx
    rw [QuadraticMap.polarBilin_apply_apply]
    calc
      QuadraticMap.polar (qS S) (d • aV) (v + ((qS S).polarBilin aV v) • u)
          = d * QuadraticMap.polar (qS S) aV (v + ((qS S).polarBilin aV v) • u) := by
            rw [QuadraticMap.polar_smul_left, smul_eq_mul]
      _ = d * (QuadraticMap.polar (qS S) aV v +
            ((qS S).polarBilin aV v) * QuadraticMap.polar (qS S) aV u) := by
            rw [QuadraticMap.polar_add_right, QuadraticMap.polar_smul_right, smul_eq_mul]
      _ = 0 := by
            have hpv : QuadraticMap.polar (qS S) aV v = (qS S).polarBilin aV v :=
              (QuadraticMap.polarBilin_apply_apply (qS S) aV v).symm
            have hpu : QuadraticMap.polar (qS S) aV u = (qS S).polarBilin aV u :=
              (QuadraticMap.polarBilin_apply_apply (qS S) aV u).symm
            have hcc : (qS S).polarBilin aV v + (qS S).polarBilin aV v = 0 := by
              rcases CFSG.RankThree.Literature.FSmith.zmod2_cases
                ((qS S).polarBilin aV v) with h | h
              · rw [h]; ring
              · rw [h]; decide
            rw [hpv, hpu, hu, mul_one, hcc, mul_zero]
  have hle_span : commSpace (conjQbar S ⟨s, hsH⟩) ≤
      Submodule.span (ZMod 2)
        {((conjQbar S ⟨s, hsH⟩ : V →ₗ[ZMod 2] V) - 1) u} := by
    intro x hx
    obtain ⟨v, rfl⟩ := mem_commSpace.mp hx
    have hxv : ((conjQbar S ⟨s, hsH⟩ : V →ₗ[ZMod 2] V) - 1) v =
        (conjQbar S ⟨s, hsH⟩) v - v := rfl
    rw [← hxv]
    let c : ZMod 2 := (qS S).polarBilin aV v
    have hmem : v + c • u ∈
        QaInterImage S (Q z ⊓ Subgroup.centralizer ({a} : Set G)) := hu_mem v
    have hfv : ((conjQbar S ⟨s, hsH⟩ : V →ₗ[ZMod 2] V) - 1) v =
        c • (((conjQbar S ⟨s, hsH⟩ : V →ₗ[ZMod 2] V) - 1) u) := by
      have h0 : ((conjQbar S ⟨s, hsH⟩ : V →ₗ[ZMod 2] V) - 1) (v + c • u) = 0 :=
        hkill _ hmem
      have hcc2 : c + c = 0 := by
        rcases CFSG.RankThree.Literature.FSmith.zmod2_cases c with h | h
        · rw [h]; ring
        · rw [h]; decide
      have hv' : v = (v + c • u) + c • u := by
        rw [add_assoc, ← add_smul, hcc2, zero_smul, add_zero]
      rw [hv', map_add, h0, zero_add]
      simp only [LinearMap.sub_apply, LinearEquiv.coe_coe, LinearEquiv.map_smul,
        Module.End.one_apply, smul_sub]
    rw [hfv]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton _))
  have hfinle : finrank (ZMod 2) (commSpace (conjQbar S ⟨s, hsH⟩)) ≤ 1 := by
    refine le_trans (Submodule.finrank_mono hle_span) ?_
    simpa using finrank_span_le_card (R := ZMod 2)
      (s := {((conjQbar S ⟨s, hsH⟩ : V →ₗ[ZMod 2] V) - 1) u})
  omega

theorem commutator_Lbar_CQ_le (S : Setting z E F) {a : G} :
    ∀ l ∈ Lbar S a, ∀ v ∈ QaInterImage S (Q z ⊓ Subgroup.centralizer ({a} : Set G)),
      ((rhoBar S l : Additive (QbarOf S) ≃ₗ[ZMod 2] Additive (QbarOf S))) v - v ∈
        QaInterImage S (Q z ⊓ QaOf a) := by
  classical
  intro l hl v hv
  let V := Additive (QbarOf S)
  rw [← map_L0_eq_Lbar S a] at hl
  obtain ⟨h, hh, hhl⟩ := Subgroup.mem_map.mp hl
  have hhL0 : (h : G) ∈ L0 S a := Subgroup.mem_subgroupOf.mp hh
  have hxsup : h ∈ (Q z).subgroupOf (H z) ⊔ (L0 S a).subgroupOf (H z) := by
    rw [← Subgroup.subgroupOf_sup (Q_le_H S) (L0_le_H S a)]
    exact Subgroup.mem_subgroupOf.mpr (Subgroup.mem_sup_right hhL0)
  obtain ⟨qH, hqH, dH, hdH, hqd⟩ :=
    (Subgroup.mem_sup_of_normal_left (s := (Q z).subgroupOf (H z))
      (t := (L0 S a).subgroupOf (H z))).mp hxsup
  have hq : (qH : G) ∈ Q z := Subgroup.mem_subgroupOf.mp hqH
  have hd : (dH : G) ∈ L0 S a := Subgroup.mem_subgroupOf.mp hdH
  have hHdecomp : h = qH * dH := hqd.symm
  have hq1 : rho S qH = 1 := by
    rw [← MonoidHom.mem_ker, rho_ker S]
    exact Subgroup.mem_subgroupOf.mpr hq
  have hrho1 : rhoBar S l = rho S h := by
    rw [← hhl, QuotientGroup.mk'_apply, rhoBar_apply_mk]
  have hrho2 : rho S h = rho S dH := by
    rw [hHdecomp, map_mul, hq1, one_mul]
  have hrho3 : (rho S dH : V ≃ₗ[ZMod 2] V) = conjQbar S dH := by
    rw [rho_apply_mk]
  obtain ⟨c, hcC, hcv⟩ := (mem_QaInterImage_iff S).mp hv
  have hcQ : (c : G) ∈ Q z := c.2
  have hcCa : (c : G) ∈ Subgroup.centralizer ({a} : Set G) := (Subgroup.mem_inf.mp hcC).2
  have hdQa : (dH : G) ∈ QaOf a := (Subgroup.mem_inf.mp hd).1
  have hdH' : (dH : G) ∈ H z := (Subgroup.mem_inf.mp hd).2
  have hval : ((rhoBar S l : Additive (QbarOf S) ≃ₗ[ZMod 2] Additive (QbarOf S))) v - v =
      Additive.ofMul (mkQbar S (conjAutQ S dH c * c⁻¹)) := by
    have hv' : v = Additive.ofMul (mkQbar S c) := (congrArg Additive.ofMul hcv).symm
    have hsub : ∀ x y : ↥(Q z), Additive.ofMul (mkQbar S (x * y⁻¹)) =
        Additive.ofMul (mkQbar S x) - Additive.ofMul (mkQbar S y) := by
      intro x y
      have h1 : (mkQbar S (x * y⁻¹) : QbarOf S) = mkQbar S x * (mkQbar S y)⁻¹ := by
        rw [map_mul, map_inv]
      calc
        Additive.ofMul (mkQbar S (x * y⁻¹))
            = Additive.ofMul (mkQbar S x * (mkQbar S y)⁻¹) := by rw [h1]
        _ = Additive.ofMul (mkQbar S x) + Additive.ofMul ((mkQbar S y)⁻¹) :=
              ofMul_mul (mkQbar S x) ((mkQbar S y)⁻¹)
        _ = Additive.ofMul (mkQbar S x) + (- Additive.ofMul (mkQbar S y)) := by
              rw [ofMul_inv]
        _ = Additive.ofMul (mkQbar S x) - Additive.ofMul (mkQbar S y) := by
              rw [sub_eq_add_neg]
    rw [hv', hrho1, hrho2, hrho3]
    have hstep : conjQbar S dH (Additive.ofMul (mkQbar S c)) =
        Additive.ofMul (mkQbar S (conjAutQ S dH c)) := by
      simpa only [mkQbar, QuotientGroup.mk'_apply] using conjQbar_apply_mk S dH c
    rw [hstep, ← hsub]
  refine (mem_QaInterImage_iff S).mpr ⟨conjAutQ S dH c * c⁻¹, ?_, ?_⟩
  · refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · have h1 : (dH : G) * (c : G) * (dH : G)⁻¹ ∈ Q z :=
        fStar_normal (M := H z) hdH' hcQ
      have heq : ((conjAutQ S dH c * c⁻¹ : ↥(Q z)) : G) =
          (dH : G) * (c : G) * (dH : G)⁻¹ * (c : G)⁻¹ := by
        rw [Subgroup.coe_mul, Subgroup.coe_inv, conjAutQ_apply]
      rw [heq]
      exact (Q z).mul_mem h1 ((Q z).inv_mem hcQ)
    · haveI : ((QaOf a).subgroupOf (Subgroup.centralizer ({a} : Set G))).Normal :=
        fStar_subgroupOf_normal (Subgroup.centralizer ({a} : Set G))
      have h2 : (c : G) * (dH : G)⁻¹ * (c : G)⁻¹ ∈ QaOf a :=
        fStar_normal (M := Subgroup.centralizer ({a} : Set G)) hcCa ((QaOf a).inv_mem hdQa)
      have heq : ((conjAutQ S dH c * c⁻¹ : ↥(Q z)) : G) =
          (dH : G) * ((c : G) * (dH : G)⁻¹ * (c : G)⁻¹) := by
        rw [Subgroup.coe_mul, Subgroup.coe_inv, conjAutQ_apply]
        group
      rw [heq]
      exact (QaOf a).mul_mem hdQa h2
  · rw [hval, toMul_ofMul]

theorem span_sub_le_CQ (S : Setting z E F) {a : G}
    (haQ : a ∈ Q z) (hconj : IsConj z a) (haZ : a ∉ ZQ z) (hza : z ∈ QaOf a)
    (hZQa : ¬ centerIn (QaOf a) ≤ Q z)
    (hR : Rbar S a ≠ ⊥)
    (Y : Subgroup (Hbar z))
    (hY2 : ∀ y ∈ Y, ∀ r ∈ Rbar S a, ∀ v : Additive (QbarOf S),
      ((rhoBar S y : Additive (QbarOf S) ≃ₗ[ZMod 2] Additive (QbarOf S)))
        ((((rhoBar S r : Additive (QbarOf S) ≃ₗ[ZMod 2] Additive (QbarOf S))) v) - v) =
      (((rhoBar S r : Additive (QbarOf S) ≃ₗ[ZMod 2] Additive (QbarOf S))) v) - v) :
    Submodule.span (ZMod 2) {u | ∃ y ∈ Y, ∃ v : Additive (QbarOf S),
      u = ((rhoBar S y : Additive (QbarOf S) ≃ₗ[ZMod 2] Additive (QbarOf S))) v - v} ≤
    QaInterImage S (Q z ⊓ Subgroup.centralizer ({a} : Set G)) := by
  classical
  letI : Module (ZMod 2) (Additive (Abelianization F)) := modAbF S
  let V := Additive (QbarOf S)
  let aV : V := Additive.ofMul (mkQbar S ⟨a, haQ⟩)
  have haV0 : aV ≠ 0 := aV_ne_zero S haQ haZ
  have hfix : ∀ y ∈ Y,
      ((rhoBar S y : V ≃ₗ[ZMod 2] V)) aV = aV := by
    intro y hy
    have hRne : ∃ r ∈ Rbar S a, r ≠ 1 := by
      by_contra h
      push Not at h
      exact hR (by
        rw [eq_bot_iff]
        intro x hx
        rw [Subgroup.mem_bot]
        exact h x hx)
    obtain ⟨r, hr, hr1⟩ := hRne
    have haVc := aV_mem_commSpace_rhoBar_of_mem_Rbar S haQ hconj haZ hza hZQa hr hr1
    have haVc' : aV ∈ commSpace ((rhoBar S r : V ≃ₗ[ZMod 2] V)) := haVc
    obtain ⟨v, hv⟩ := mem_commSpace.mp haVc'
    have h2 := hY2 y hy r hr v
    rw [hv] at h2
    exact h2
  refine Submodule.span_le.mpr ?_
  rintro u ⟨y, hy, v, rfl⟩
  rw [QaInterImage_CQ_eq_orthogonal S haQ]
  change (((rhoBar S y : V ≃ₗ[ZMod 2] V)) v - v) ∈
    LinearMap.BilinForm.orthogonal (qS S).polarBilin (Submodule.span (ZMod 2) {aV})
  rw [LinearMap.BilinForm.mem_orthogonal_iff]
  intro x hx
  rw [Submodule.mem_span_singleton] at hx
  obtain ⟨c, rfl⟩ := hx
  rw [QuadraticMap.polarBilin_apply_apply]
  have hpres := TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup
    (rhoBar S y).2 aV v
  calc
    QuadraticMap.polar (qS S) (c • aV) (((rhoBar S y : V ≃ₗ[ZMod 2] V)) v - v)
        = c * QuadraticMap.polar (qS S) aV (((rhoBar S y : V ≃ₗ[ZMod 2] V)) v - v) := by
            rw [QuadraticMap.polar_smul_left, smul_eq_mul]
    _ = c * (QuadraticMap.polar (qS S) aV (((rhoBar S y : V ≃ₗ[ZMod 2] V)) v) -
          QuadraticMap.polar (qS S) aV v) := by rw [QuadraticMap.polar_sub_right]
    _ = c * (QuadraticMap.polar (qS S) (((rhoBar S y : V ≃ₗ[ZMod 2] V)) aV)
          (((rhoBar S y : V ≃ₗ[ZMod 2] V)) v) - QuadraticMap.polar (qS S) aV v) := by
            rw [hfix y hy]
    _ = c * (QuadraticMap.polar (qS S) aV v - QuadraticMap.polar (qS S) aV v) := by rw [hpres]
    _ = 0 := by rw [sub_self, mul_zero]

theorem span_sub_stable (S : Setting z E F) {a : G}
    (Y : Subgroup (Hbar z)) (hL : Lbar S a ≤ Subgroup.normalizer (Y : Set (Hbar z))) :
    ∀ l ∈ Lbar S a,
      ∀ w ∈ Submodule.span (ZMod 2) {u | ∃ y ∈ Y, ∃ v : Additive (QbarOf S),
        u = ((rhoBar S y : Additive (QbarOf S) ≃ₗ[ZMod 2] Additive (QbarOf S))) v - v},
        ((rhoBar S l : Additive (QbarOf S) ≃ₗ[ZMod 2] Additive (QbarOf S))) w ∈
          Submodule.span (ZMod 2) {u | ∃ y ∈ Y, ∃ v : Additive (QbarOf S),
            u = ((rhoBar S y : Additive (QbarOf S) ≃ₗ[ZMod 2] Additive (QbarOf S))) v - v} := by
  classical
  let V := Additive (QbarOf S)
  let W : Submodule (ZMod 2) V := Submodule.span (ZMod 2) {u | ∃ y ∈ Y, ∃ v : V,
    u = ((rhoBar S y : V ≃ₗ[ZMod 2] V)) v - v}
  intro l hl w hw
  change ((rhoBar S l : V ≃ₗ[ZMod 2] V)) w ∈ W
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hw
  · rintro u ⟨y, hy, v, rfl⟩
    let y' : ↥Y := ⟨l * y * l⁻¹, (Subgroup.mem_normalizer_iff.mp (hL hl) y).mp hy⟩
    have hyl : l * y = (y' : Hbar z) * l := by
      have hc : l * y * l⁻¹ = (y' : Hbar z) := rfl
      calc l * y = (l * y * l⁻¹) * l := by group
        _ = (y' : Hbar z) * l := by rw [hc]
    have hmul : ((rhoBar S l : V ≃ₗ[ZMod 2] V)) (((rhoBar S y : V ≃ₗ[ZMod 2] V)) v) =
        ((rhoBar S (l * y) : V ≃ₗ[ZMod 2] V)) v := by
      rw [map_mul]
      rfl
    have hmul' : ((rhoBar S (l * y) : V ≃ₗ[ZMod 2] V)) v =
        ((rhoBar S (y' : Hbar z) : V ≃ₗ[ZMod 2] V)) (((rhoBar S l : V ≃ₗ[ZMod 2] V)) v) := by
      rw [hyl, map_mul]
      rfl
    have hval : ((rhoBar S l : V ≃ₗ[ZMod 2] V))
          (((rhoBar S y : V ≃ₗ[ZMod 2] V)) v - v) =
        ((rhoBar S (y' : Hbar z) : V ≃ₗ[ZMod 2] V))
          (((rhoBar S l : V ≃ₗ[ZMod 2] V)) v) - ((rhoBar S l : V ≃ₗ[ZMod 2] V)) v := by
      rw [map_sub, hmul, hmul']
    rw [hval]
    exact Submodule.subset_span ⟨(y' : Hbar z), y'.2,
      ((rhoBar S l : V ≃ₗ[ZMod 2] V)) v, rfl⟩
  · simpa using Submodule.zero_mem W
  · intro x y _ _ hx hy
    simpa only [map_add] using Submodule.add_mem W hx hy
  · intro c x _ hx
    simpa only [map_smul] using Submodule.smul_mem W c hx

theorem commutator_Lbar_span_sub_eq (S : Setting z E F) {a : G}
    (haQ : a ∈ Q z) (hconj : IsConj z a) (haZ : a ∉ ZQ z) (hza : z ∈ QaOf a)
    (hZQa : ¬ centerIn (QaOf a) ≤ Q z)
    (hR : Rbar S a ≠ ⊥)
    (Y : Subgroup (Hbar z))
    (hY2 : ∀ y ∈ Y, ∀ r ∈ Rbar S a, ∀ v : Additive (QbarOf S),
      ((rhoBar S y : Additive (QbarOf S) ≃ₗ[ZMod 2] Additive (QbarOf S)))
        ((((rhoBar S r : Additive (QbarOf S) ≃ₗ[ZMod 2] Additive (QbarOf S))) v) - v) =
      (((rhoBar S r : Additive (QbarOf S) ≃ₗ[ZMod 2] Additive (QbarOf S))) v) - v)
    (ha_not : Additive.ofMul (mkQbar S ⟨a, haQ⟩) ∉
      Submodule.span (ZMod 2) {u | ∃ y ∈ Y, ∃ v : Additive (QbarOf S),
        u = ((rhoBar S y : Additive (QbarOf S) ≃ₗ[ZMod 2] Additive (QbarOf S))) v - v})
    (hL : Lbar S a ≤ Subgroup.normalizer (Y : Set (Hbar z))) :
    ∀ l ∈ Lbar S a,
      ∀ w ∈ Submodule.span (ZMod 2) {u | ∃ y ∈ Y, ∃ v : Additive (QbarOf S),
        u = ((rhoBar S y : Additive (QbarOf S) ≃ₗ[ZMod 2] Additive (QbarOf S))) v - v},
        ((rhoBar S l : Additive (QbarOf S) ≃ₗ[ZMod 2] Additive (QbarOf S))) w = w := by
  classical
  letI : Module (ZMod 2) (Additive (Abelianization F)) := modAbF S
  let V := Additive (QbarOf S)
  let aV : V := Additive.ofMul (mkQbar S ⟨a, haQ⟩)
  let W : Submodule (ZMod 2) V := Submodule.span (ZMod 2) {u | ∃ y ∈ Y, ∃ v : V,
    u = ((rhoBar S y : V ≃ₗ[ZMod 2] V)) v - v}
  let U : Submodule (ZMod 2) V := QaInterImage S (Q z ⊓ QaOf a)
  let W' : Submodule (ZMod 2) V := Submodule.span (ZMod 2) {u | ∃ l ∈ Lbar S a, ∃ w ∈ W,
    u = ((rhoBar S l : V ≃ₗ[ZMod 2] V)) w - w}
  have hW_le_CQ : W ≤ QaInterImage S (Q z ⊓ Subgroup.centralizer ({a} : Set G)) :=
    span_sub_le_CQ S haQ hconj haZ hza hZQa hR Y hY2
  have hstab : ∀ l ∈ Lbar S a, ∀ w ∈ W,
      ((rhoBar S l : V ≃ₗ[ZMod 2] V)) w ∈ W := span_sub_stable S Y hL
  have hW'_le_W : W' ≤ W := by
    refine Submodule.span_le.mpr ?_
    rintro u ⟨l, hl, w, hw, rfl⟩
    exact W.sub_mem (hstab l hl w hw) hw
  have hW'_le_U : W' ≤ U := by
    refine Submodule.span_le.mpr ?_
    rintro u ⟨l, hl, w, hw, rfl⟩
    exact commutator_Lbar_CQ_le S l hl w (hW_le_CQ hw)
  have hW'_stab : ∀ l ∈ Lbar S a, ∀ w ∈ W',
      ((rhoBar S l : V ≃ₗ[ZMod 2] V)) w ∈ W' := by
    intro l hl w hw
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hw
    · rintro u ⟨l₀, hl₀, w₀, hw₀, rfl⟩
      have hval : ((rhoBar S l : V ≃ₗ[ZMod 2] V))
            (((rhoBar S l₀ : V ≃ₗ[ZMod 2] V)) w₀ - w₀) =
          (((rhoBar S (l * l₀) : V ≃ₗ[ZMod 2] V)) w₀ - w₀) -
            (((rhoBar S l : V ≃ₗ[ZMod 2] V)) w₀ - w₀) := by
        rw [map_sub]
        have hmul : ((rhoBar S l : V ≃ₗ[ZMod 2] V)) (((rhoBar S l₀ : V ≃ₗ[ZMod 2] V)) w₀) =
            ((rhoBar S (l * l₀) : V ≃ₗ[ZMod 2] V)) w₀ := by
          rw [map_mul]
          rfl
        rw [hmul]
        abel
      rw [hval]
      exact W'.sub_mem
        (Submodule.subset_span ⟨l * l₀, Lbar S a |>.mul_mem hl hl₀, w₀, hw₀, rfl⟩)
        (Submodule.subset_span ⟨l, hl, w₀, hw₀, rfl⟩)
    · simpa using Submodule.zero_mem W'
    · intro x y _ _ hx hy
      simpa only [map_add] using Submodule.add_mem W' hx hy
    · intro c x _ hx
      simpa only [map_smul] using Submodule.smul_mem W' c hx
  have hW'_bot : W' = ⊥ := by
    by_contra hne
    obtain ⟨u, hu, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    by_cases hua : u = aV
    · apply ha_not
      change aV ∈ W
      rw [← hua]
      exact hW'_le_W hu
    ·
      have hbU : u ∈ U := hW'_le_U hu
      obtain ⟨b, hbA, hbv⟩ := (mem_QaInterImage_iff S).mp hbU
      have hbQ : (b : G) ∈ Q z := b.2
      have hbQa : (b : G) ∈ QaOf a := (Subgroup.mem_inf.mp hbA).2
      have hbnu : Additive.ofMul (mkQbar S b) = u := by
        rw [hbv, ofMul_toMul]
      have hb_not : Additive.ofMul (mkQbar S b) ∉
          Submodule.span (ZMod 2) {aV} := by
        rw [hbnu]
        intro hu'
        obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hu'
        rcases CFSG.RankThree.Literature.FSmith.zmod2_cases c with rfl | rfl
        · rw [zero_smul] at hc
          exact hu0 hc.symm
        · rw [one_smul] at hc
          exact hua hc.symm
      obtain ⟨l₀, hl₀, hconj₀⟩ :=
        exists_lbar_apply_sub_eq S haQ hconj hza hbQ hbQa hb_not
      apply ha_not
      have hmem : aV ∈ W' := by
        have h1 : ((rhoBar S l₀ : V ≃ₗ[ZMod 2] V)) u - u = aV := by
          rw [← hbnu]
          exact hconj₀
        rw [← h1]
        exact W'.sub_mem (hW'_stab l₀ hl₀ u hu) hu
      exact hW'_le_W hmem
  intro l hl w hw
  have hmem : ((rhoBar S l : V ≃ₗ[ZMod 2] V)) w - w ∈ W' :=
    Submodule.subset_span ⟨l, hl, w, hw, rfl⟩
  rw [hW'_bot] at hmem
  exact sub_eq_zero.mp (by simpa using hmem)

theorem span_sub_disjoint (S : Setting z E F) {a : G}
    (haQ : a ∈ Q z) (hconj : IsConj z a) (haZ : a ∉ ZQ z) (hza : z ∈ QaOf a)
    (hZQa : ¬ centerIn (QaOf a) ≤ Q z)
    (hR : Rbar S a ≠ ⊥)
    (Y : Subgroup (Hbar z))
    (hY2 : ∀ y ∈ Y, ∀ r ∈ Rbar S a, ∀ v : Additive (QbarOf S),
      ((rhoBar S y : Additive (QbarOf S) ≃ₗ[ZMod 2] Additive (QbarOf S)))
        ((((rhoBar S r : Additive (QbarOf S) ≃ₗ[ZMod 2] Additive (QbarOf S))) v) - v) =
      (((rhoBar S r : Additive (QbarOf S) ≃ₗ[ZMod 2] Additive (QbarOf S))) v) - v)
    (ha_not : Additive.ofMul (mkQbar S ⟨a, haQ⟩) ∉
      Submodule.span (ZMod 2) {u | ∃ y ∈ Y, ∃ v : Additive (QbarOf S),
        u = ((rhoBar S y : Additive (QbarOf S) ≃ₗ[ZMod 2] Additive (QbarOf S))) v - v})
    (hL : Lbar S a ≤ Subgroup.normalizer (Y : Set (Hbar z))) :
    Submodule.span (ZMod 2) {u | ∃ y ∈ Y, ∃ v : Additive (QbarOf S),
        u = ((rhoBar S y : Additive (QbarOf S) ≃ₗ[ZMod 2] Additive (QbarOf S))) v - v} ⊓
      QaInterImage S (Q z ⊓ QaOf a) = ⊥ := by
  classical
  letI : Module (ZMod 2) (Additive (Abelianization F)) := modAbF S
  let V := Additive (QbarOf S)
  let aV : V := Additive.ofMul (mkQbar S ⟨a, haQ⟩)
  let W : Submodule (ZMod 2) V := Submodule.span (ZMod 2) {u | ∃ y ∈ Y, ∃ v : V,
    u = ((rhoBar S y : V ≃ₗ[ZMod 2] V)) v - v}
  let U : Submodule (ZMod 2) V := QaInterImage S (Q z ⊓ QaOf a)
  have hact := commutator_Lbar_span_sub_eq S haQ hconj haZ hza hZQa hR Y hY2 ha_not hL
  rw [eq_bot_iff]
  intro u hu
  rw [Submodule.mem_bot]
  by_contra hu0
  have huW : u ∈ W := hu.1
  have huU : u ∈ U := hu.2
  obtain ⟨b, hbA, hbv⟩ := (mem_QaInterImage_iff S).mp huU
  have hbQ : (b : G) ∈ Q z := b.2
  have hbQa : (b : G) ∈ QaOf a := (Subgroup.mem_inf.mp hbA).2
  have hbnu : Additive.ofMul (mkQbar S b) = u := by rw [hbv, ofMul_toMul]
  by_cases hua : u = aV
  · apply ha_not
    change aV ∈ W
    rw [← hua]
    exact huW
  · have hb_not : Additive.ofMul (mkQbar S b) ∉ Submodule.span (ZMod 2) {aV} := by
      rw [hbnu]
      intro hu'
      obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hu'
      rcases CFSG.RankThree.Literature.FSmith.zmod2_cases c with rfl | rfl
      · rw [zero_smul] at hc
        exact hu0 hc.symm
      · rw [one_smul] at hc
        exact hua hc.symm
    obtain ⟨l, hl, hconj'⟩ := exists_lbar_apply_sub_eq S haQ hconj hza hbQ hbQa hb_not
    have h1 : ((rhoBar S l : V ≃ₗ[ZMod 2] V)) u - u = aV := by
      rw [← hbnu]
      exact hconj'
    have h2 : ((rhoBar S l : V ≃ₗ[ZMod 2] V)) u = u := hact l hl u huW
    apply aV_ne_zero S haQ haZ
    change aV = 0
    rw [← h1, h2, sub_self]

theorem stroth78_2_17_of_span_sub_le
    (S : Setting z E F) {a : G}
    (haQ : a ∈ Q z) (hconj : IsConj z a) (hza : z ∈ QaOf a)
    (Y : Subgroup (Hbar z))
    (hO2 : Subgroup.closure {y | y ∈ Y ∧ Odd (orderOf y)} = Y)
    (hO2' : ∀ P : Subgroup (Hbar z), P ≤ Y → IsPGroup 2 P →
      Y ≤ Subgroup.normalizer (P : Set (Hbar z)) → P = ⊥)
    (hYR : ∀ y ∈ Y, ∀ r ∈ Rbar S a, Commute y r)
    (hY2 : ∀ y ∈ Y, ∀ r ∈ Rbar S a, ∀ v : Additive (QbarOf S),
      ((rhoBar S y : Additive (QbarOf S) ≃ₗ[ZMod 2] Additive (QbarOf S)))
        ((((rhoBar S r : Additive (QbarOf S) ≃ₗ[ZMod 2] Additive (QbarOf S))) v) - v) =
      (((rhoBar S r : Additive (QbarOf S) ≃ₗ[ZMod 2] Additive (QbarOf S))) v) - v)
    (ha_not : Additive.ofMul (mkQbar S ⟨a, haQ⟩) ∉
      Submodule.span (ZMod 2) {u | ∃ y ∈ Y, ∃ v : Additive (QbarOf S),
        u = ((rhoBar S y : Additive (QbarOf S) ≃ₗ[ZMod 2] Additive (QbarOf S))) v - v})
    (hL : Lbar S a ≤ Subgroup.normalizer (Y : Set (Hbar z)))
    (hWU : ∀ w ∈ Submodule.span (ZMod 2) {u | ∃ y ∈ Y, ∃ v : Additive (QbarOf S),
        u = ((rhoBar S y : Additive (QbarOf S) ≃ₗ[ZMod 2] Additive (QbarOf S))) v - v},
        w ∈ QaInterImage S (Q z ⊓ QaOf a)) :
    Rbar S a = ⊥ ∨ Y = ⊥ := by
  classical
  by_cases hR : Rbar S a = ⊥
  · exact Or.inl hR
  right
  by_cases haZ : a ∈ ZQ z
  · exfalso
    apply ha_not
    change Additive.ofMul (mkQbar S ⟨a, haQ⟩) ∈
      Submodule.span (ZMod 2) {u | ∃ y ∈ Y, ∃ v : Additive (QbarOf S),
        u = ((rhoBar S y : Additive (QbarOf S) ≃ₗ[ZMod 2] Additive (QbarOf S))) v - v}
    rw [aV_eq_zero_of_mem_ZQ S haQ haZ]
    exact Submodule.zero_mem _
  by_cases hZQa : centerIn (QaOf a) ≤ Q z
  · exact absurd (rbar_eq_bot_of_centerIn_le_Q S a hZQa) hR
  letI : Module (ZMod 2) (Additive (Abelianization F)) := modAbF S
  let V := Additive (QbarOf S)
  let aV : V := Additive.ofMul (mkQbar S ⟨a, haQ⟩)
  let W : Submodule (ZMod 2) V := Submodule.span (ZMod 2) {u | ∃ y ∈ Y, ∃ v : V,
    u = ((rhoBar S y : V ≃ₗ[ZMod 2] V)) v - v}
  have hact := commutator_Lbar_span_sub_eq S haQ hconj haZ hza hZQa hR Y hY2 ha_not hL
  have hWbot : W = ⊥ := by
    rw [eq_bot_iff]
    intro w hw
    rw [Submodule.mem_bot]
    by_contra hw0
    have hwU : w ∈ QaInterImage S (Q z ⊓ QaOf a) := hWU w hw
    obtain ⟨b, hbA, hbv⟩ := (mem_QaInterImage_iff S).mp hwU
    have hbQ : (b : G) ∈ Q z := b.2
    have hbQa : (b : G) ∈ QaOf a := (Subgroup.mem_inf.mp hbA).2
    have hbnu : Additive.ofMul (mkQbar S b) = w := by rw [hbv, ofMul_toMul]
    by_cases hwa : w = aV
    · apply ha_not
      change aV ∈ W
      rw [← hwa]
      exact hw
    · have hb_not : Additive.ofMul (mkQbar S b) ∉ Submodule.span (ZMod 2) {aV} := by
        rw [hbnu]
        intro hw'
        obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hw'
        rcases CFSG.RankThree.Literature.FSmith.zmod2_cases c with rfl | rfl
        · rw [zero_smul] at hc
          exact hw0 hc.symm
        · rw [one_smul] at hc
          exact hwa hc.symm
      obtain ⟨l, hl, hconj'⟩ := exists_lbar_apply_sub_eq S haQ hconj hza hbQ hbQa hb_not
      have h1 : ((rhoBar S l : V ≃ₗ[ZMod 2] V)) w - w = aV := by
        rw [← hbnu]
        exact hconj'
      have h2 : ((rhoBar S l : V ≃ₗ[ZMod 2] V)) w = w := hact l hl w hw
      apply aV_ne_zero S haQ haZ
      change aV = 0
      rw [← h1, h2, sub_self]
  rw [eq_bot_iff]
  intro y hy
  rw [Subgroup.mem_bot]
  apply rhoBar_injective S
  rw [map_one]
  refine Subtype.ext (LinearEquiv.ext fun v => ?_)
  have hgen : ((rhoBar S y : V ≃ₗ[ZMod 2] V)) v - v ∈ W :=
    Submodule.subset_span ⟨y, hy, v, rfl⟩
  rw [hWbot] at hgen
  have hzero : ((rhoBar S y : V ≃ₗ[ZMod 2] V)) v = v :=
    sub_eq_zero.mp (by simpa using hgen)
  simpa using hzero

end CFSG.RankThree.GF2n.Stroth78
