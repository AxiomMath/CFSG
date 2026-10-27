module

public import CFSG.Quasithin.H13.L32A720f
public import CFSG.Quasithin.H13.L32A721b

public section

namespace CFSG.Quasithin.H13.L32A

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.C1Pack

section TwoElements

variable {G : Type} [Group G] [Finite G]

theorem eq_of_mem_of_card_eq_two {Z : Subgroup G} (hZ : Nat.card Z = 2) {x y : G} (hx : x ∈ Z)
    (hy : y ∈ Z) (hx1 : x ≠ 1) (hy1 : y ≠ 1) : x = y := by
  classical
  by_contra hxy
  have hsub : ∀ g ∈ (({1, x, y} : Finset G) : Set G), g ∈ Z := by
    intro g hg
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl
    · exact Z.one_mem
    · exact hx
    · exact hy
  have h3 : ({1, x, y} : Finset G).card = 3 := by
    rw [Finset.card_insert_of_notMem, Finset.card_pair hxy]
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨fun h => hx1 h.symm, fun h => hy1 h.symm⟩
  have := Nat.card_le_card_of_injective
    (fun g : ↥(({1, x, y} : Finset G) : Set G) => (⟨g, hsub g g.2⟩ : ↥Z))
    (fun a b e => Subtype.ext (by simpa using congrArg Subtype.val e))
  rw [Nat.card_coe_set_eq, Set.ncard_coe_finset, h3, hZ] at this
  omega

end TwoElements

namespace Ctx7153

variable {G : Type} [Group G] [Finite G] {T L V H : Subgroup G} (E : Ctx7153 G T L V H)
  (hF : HypF98 T V L (fsuV1 T V) V (hz T V))
include E hF

theorem relIndex_centralizer_qh {q : G} (hq : q ∈ pCoreOf 2 (hz T V))
    (hqU : q ∉ Subgroup.centralizer (fsuU T V : Set G)) :
    (fsuU T V ⊓ Subgroup.centralizer ({q} : Set G)).relIndex (fsuU T V) = 2 := by
  set h := hF.toHypF91 with hh
  have hUe : fsuU T V = conjClosure V (hz T V) := E.fsuU_eq
  rw [hUe] at hqU ⊢
  let f : ↥(conjClosure V (hz T V)) →* ↥(fsuV1 T V) :=
    { toFun := fun u => ⟨q * (u : G) * q⁻¹ * (u : G)⁻¹, h.commutator_mem_V₁ hq u.2⟩
      map_one' := by ext; simp
      map_mul' := fun u₁ u₂ => Subtype.ext (h.commutator_mul_right hq u₁.2 u₂.2) }
  have hf : ∀ u : ↥(conjClosure V (hz T V)), f u = 1 ↔ (u : G) * q = q * u := by
    intro u
    constructor
    · intro e
      have e' : q * (u : G) * q⁻¹ * (u : G)⁻¹ = 1 := congrArg Subtype.val e
      calc (u : G) * q = (q * (u : G) * q⁻¹ * (u : G)⁻¹)⁻¹ * q * u := by group
        _ = q * u := by rw [e']; group
    · intro e
      apply Subtype.ext
      show q * (u : G) * q⁻¹ * (u : G)⁻¹ = 1
      rw [← e]
      group
  have hker : f.ker = (conjClosure V (hz T V) ⊓ Subgroup.centralizer ({q} : Set G)).subgroupOf
      (conjClosure V (hz T V)) := by
    ext u
    rw [MonoidHom.mem_ker, hf, Subgroup.mem_subgroupOf, Subgroup.mem_inf,
      Subgroup.mem_centralizer_singleton_iff]
    exact ⟨fun e => ⟨u.2, e⟩, fun e => e.2⟩
  have hne : f.range ≠ ⊥ := by
    intro hb
    apply hqU
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    have h1 : f ⟨u, hu⟩ = 1 := by
      have hmem : f ⟨u, hu⟩ ∈ f.range := ⟨_, rfl⟩
      rw [hb] at hmem
      exact hmem
    exact (hf ⟨u, hu⟩).mp h1
  have hle : Nat.card f.range ≤ 2 := (Subgroup.card_le_card_group f.range).trans_eq h.card_V₁
  have h1 : Nat.card f.range ≠ 1 := fun e => hne (Subgroup.eq_bot_of_card_eq _ e)
  have hpos : 0 < Nat.card f.range := Nat.card_pos
  rw [Subgroup.relIndex, ← hker, Subgroup.index_ker]
  omega

omit hF in
theorem relIndex_inf_qh_le_two {A : Subgroup G} (hAR : A ≤ pCoreOf 2 (l1 T L V ⊔ T))
    (hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (hA2 : ∀ a ∈ A, a * a = 1) :
    (A ⊓ pCoreOf 2 (hz T V)).relIndex A ≤ 2 := by
  obtain ⟨x, hxL, hxH, hx3, hx1⟩ := E.exists_three
  obtain ⟨-, hR1T⟩ := E.qh_le_r1
  have hN : l1 T L V ⊔ T ≤ Subgroup.normalizer (pCoreOf 2 (l1 T L V ⊔ T) : Set G) :=
    le_normalizer_pCoreOf 2 _
  have hRL : l1 T L V ⊓ pCoreOf 2 (l1 T L V ⊔ T) ≤ pCoreOf 2 (l1 T L V) := by
    refine le_pCoreOf_of_le_normalizer 2 inf_le_left (fun l hl => ?_)
      ((pCoreOf_isPGroup 2 _).to_le inf_le_right)
    rw [Subgroup.mem_normalizer_iff]
    intro y
    have h1 := Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer hl) y
    have h2 := Subgroup.mem_normalizer_iff.mp (hN (le_sup_left (a := l1 T L V) hl)) y
    simp only [Subgroup.mem_inf]
    rw [h1, h2]
  refine (E.relIndex_le hxL hxH hx3 hx1 (hAR.trans hR1T) hAc hA2).2 fun a ha => ?_
  have haR := hAR ha
  have haH : a ∈ hz T V := E.t_le_hz (hR1T haR)
  have h1 : a * x * a⁻¹ * x⁻¹ ∈ l1 T L V :=
    mul_mem ((Subgroup.mem_normalizer_iff.mp (E.hz_le_normalizer_l1 haH) x).mp hxL) (inv_mem hxL)
  have h2 : a * x * a⁻¹ * x⁻¹ ∈ pCoreOf 2 (l1 T L V ⊔ T) := by
    have h3 : x * a⁻¹ * x⁻¹ ∈ pCoreOf 2 (l1 T L V ⊔ T) :=
      (Subgroup.mem_normalizer_iff.mp (hN (le_sup_left (a := l1 T L V) hxL)) _).mp (inv_mem haR)
    rw [show a * x * a⁻¹ * x⁻¹ = a * (x * a⁻¹ * x⁻¹) by group]
    exact mul_mem haR h3
  have h4 := hRL (Subgroup.mem_inf.mpr ⟨h1, h2⟩)
  rw [E.n1_eq] at h4
  exact h4.2

theorem not_forall_comm_mem_v1 {h : G} (hh : h ∈ hz T V) (hQ : h ∉ pCoreOf 2 (hz T V))
    {W : Subgroup G} (hidx : W.relIndex (fsuU T V) ≤ 2) :
    ¬ ∀ w ∈ W, h * w * h⁻¹ * w⁻¹ ∈ fsuV1 T V := by
  intro hW
  have hUe : fsuU T V = conjClosure V (hz T V) := E.fsuU_eq
  have hcardU : Nat.card (UMod hF.toHypF91) = 64 := E.card_umod hF
  obtain ⟨τ, hτ⟩ : ∃ τ, C1Pack.rhoH hF.toHypF91 ⟨h, hh⟩ = τ := ⟨_, rfl⟩
  have hτ1 : τ ≠ 1 := fun e => hQ ((C1Pack.rhoH_eq_one_iff hF.toHypF91 ⟨h, hh⟩).mp (hτ.trans e))
  let π : ↥(conjClosure V (hz T V)) →* UMod hF.toHypF91 :=
    { toFun := fun u => clsU hF.toHypF91 u.2
      map_one' := clsU_one hF.toHypF91
      map_mul' := fun u u' => (clsU_mul hF.toHypF91 u.2 u'.2).symm }
  have hπ : Function.Surjective π := fun w => by
    obtain ⟨u, hu, rfl⟩ := exists_clsU hF.toHypF91 w
    exact ⟨⟨u, hu⟩, rfl⟩
  have hle : (W.subgroupOf (conjClosure V (hz T V))).map π ≤ fixV (Subgroup.zpowers τ) := by
    rintro _ ⟨u, hu, rfl⟩
    rw [HeisMod.mem_fixV_zpowers]
    change τ (clsU hF.toHypF91 u.2) = clsU hF.toHypF91 u.2
    rw [← hτ, rhoH_clsU_eq_iff]
    exact hW u (Subgroup.mem_subgroupOf.mp hu)
  have hFidx : (fixV (Subgroup.zpowers τ)).index ≤ 2 := by
    have h1 : (fixV (Subgroup.zpowers τ)).index ≤
        ((W.subgroupOf (conjClosure V (hz T V))).map π).index :=
      Nat.le_of_dvd (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite)
        (Subgroup.index_dvd_of_le hle)
    have h2 : ((W.subgroupOf (conjClosure V (hz T V))).map π).index ≤
        (W.subgroupOf (conjClosure V (hz T V))).index :=
      Nat.le_of_dvd (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite)
        (Subgroup.index_map_dvd _ hπ)
    have h3 : (W.subgroupOf (conjClosure V (hz T V))).index = W.relIndex (fsuU T V) := by
      rw [hUe]
      rfl
    omega
  have hFtop : fixV (Subgroup.zpowers τ) ≠ ⊤ := by
    intro htop
    apply hτ1
    ext w
    have hw : w ∈ fixV (Subgroup.zpowers τ) := by
      rw [htop]
      exact Subgroup.mem_top w
    rw [HeisMod.mem_fixV_zpowers] at hw
    rw [hw, MulAut.one_apply]
  have hF32 : Nat.card (fixV (Subgroup.zpowers τ)) = 32 := by
    have h1 := Subgroup.index_mul_card (fixV (Subgroup.zpowers τ))
    have h2 : (fixV (Subgroup.zpowers τ)).index ≠ 1 := fun e =>
      hFtop (Subgroup.index_eq_one.mp e)
    have h3 : (fixV (Subgroup.zpowers τ)).index ≠ 0 := Subgroup.index_ne_zero_of_finite
    rw [hcardU] at h1
    have h4 : (fixV (Subgroup.zpowers τ)).index = 2 := by omega
    rw [h4] at h1
    omega
  obtain ⟨x, hxL, hxH, hx3, hx1⟩ := E.exists_three
  obtain ⟨c, hc⟩ : ∃ c, C1Pack.rhoH hF.toHypF91 ⟨x, hxH⟩ = c := ⟨_, rfl⟩
  have hc3 : c ^ 3 = 1 := by
    rw [← hc, ← map_pow]
    have e : (⟨x, hxH⟩ : ↥(hz T V)) ^ 3 = 1 := Subtype.ext (by simpa using hx3)
    rw [e, map_one]
  have hfpf : ∀ w : UMod hF.toHypF91, c w = w → w = 1 := by
    intro w hw
    obtain ⟨u, hu, rfl⟩ := exists_clsU hF.toHypF91 w
    rw [← hc, rhoH_clsU_eq_iff] at hw
    exact (clsU_eq_one_iff hF.toHypF91 hu).mpr
      (E.fpf_of_three hF hxL hxH hx3 hx1 (by rw [hUe]; exact hu) hw)
  have hrho : ∀ y : ↥(hz T V),
      rhoDot hF.toHypF91 (QuotientGroup.mk' (CFSG.pCore 2 ↥(hz T V)) y) =
        C1Pack.rhoH hF.toHypF91 y := fun y => rhoDot_mk hF.toHypF91 y
  rcases E.conj_xdot_cases hxL hxH hx3 hx1 (QuotientGroup.mk' _ ⟨h, hh⟩) with e | e
  ·
    have e' := congrArg (rhoDot hF.toHypF91) e
    rw [map_mul, map_mul, map_inv, hrho, hrho, hτ, hc] at e'
    have hτc : τ * c = c * τ := by
      calc τ * c = τ * c * τ⁻¹ * τ := by group
        _ = c * τ := by rw [e']
    have hinv : ∀ w ∈ fixV (Subgroup.zpowers τ), c w ∈ fixV (Subgroup.zpowers τ) := by
      intro w hw
      rw [HeisMod.mem_fixV_zpowers] at hw ⊢
      calc τ (c w) = c (τ w) := DFunLike.congr_fun hτc w
        _ = c w := by rw [hw]
    have h3 := S153Q.Q4A.card_mod_three hc3 hfpf hinv
    rw [hF32] at h3
    norm_num at h3
  ·
    have e' := congrArg (rhoDot hF.toHypF91) e
    rw [map_mul, map_mul, map_inv, map_inv, hrho, hrho, hτ, hc] at e'
    have hτc' : τ * c = c⁻¹ * τ := by
      calc τ * c = τ * c * τ⁻¹ * τ := by group
        _ = c⁻¹ * τ := by rw [e']
    have hτc : ∀ w : UMod hF.toHypF91, τ (c w) = c⁻¹ (τ w) := fun w =>
      DFunLike.congr_fun hτc' w
    have hmeet : fixV (Subgroup.zpowers τ) ⊓ (fixV (Subgroup.zpowers τ)).map c.toMonoidHom =
        ⊥ := by
      refine (Subgroup.eq_bot_iff_forall _).mpr fun w hw => ?_
      obtain ⟨hwF, v, hvF, rfl⟩ := Subgroup.mem_inf.mp hw
      have hvF' : τ v = v := HeisMod.mem_fixV_zpowers.mp hvF
      rw [HeisMod.mem_fixV_zpowers] at hwF
      change τ (c v) = c v at hwF
      rw [hτc, hvF'] at hwF
      have h1 : c (c v) = v := by
        have h2 : c (c⁻¹ v) = v := by
          rw [← MulAut.mul_apply, mul_inv_cancel, MulAut.one_apply]
        rw [← hwF]
        exact h2
      have h2 : c v = v := by
        have h3 := congrArg c h1
        rw [S153Q.Q4A.z_cube_apply hc3] at h3
        exact h3.symm
      change c v = 1
      rw [hfpf v h2, map_one]
    have h1 := S153Q.Q4A.card_mul_le_card_sup hmeet
    have h2 : Nat.card ↥((fixV (Subgroup.zpowers τ)).map c.toMonoidHom) =
        Nat.card (fixV (Subgroup.zpowers τ)) :=
      Subgroup.card_map_of_injective c.injective
    have h3 : Nat.card ↥(fixV (Subgroup.zpowers τ) ⊔
        (fixV (Subgroup.zpowers τ)).map c.toMonoidHom) ≤ 64 :=
      (Subgroup.card_le_card_group _).trans_eq hcardU
    rw [h2, hF32] at h1
    omega

theorem inv_mul_mem_centralizer {b c : G} (hb : b ∈ pCoreOf 2 (hz T V))
    (hc : c ∈ pCoreOf 2 (hz T V))
    (heq : fsuU T V ⊓ Subgroup.centralizer ({b} : Set G) =
      fsuU T V ⊓ Subgroup.centralizer ({c} : Set G)) :
    b⁻¹ * c ∈ Subgroup.centralizer (fsuU T V : Set G) := by
  have hcomm : ∀ x u : G, x * u * x⁻¹ * u⁻¹ = 1 ↔ u * x = x * u := by
    intro x u
    constructor
    · intro e
      calc u * x = (x * u * x⁻¹ * u⁻¹)⁻¹ * x * u := by group
        _ = x * u := by rw [e]; group
    · intro e
      rw [← e]
      group
  have hmem : ∀ x u : G, u ∈ fsuU T V →
      (u ∈ fsuU T V ⊓ Subgroup.centralizer ({x} : Set G) ↔ x * u * x⁻¹ * u⁻¹ = 1) := by
    intro x u hu
    rw [Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff, hcomm]
    exact ⟨fun e => e.2, fun e => ⟨hu, e⟩⟩
  rw [Subgroup.mem_centralizer_iff]
  intro u hu
  have hu' : u ∈ conjClosure V (hz T V) := E.fsuU_eq ▸ hu
  have key : b * u * b⁻¹ * u⁻¹ = c * u * c⁻¹ * u⁻¹ := by
    by_cases hbu : b * u * b⁻¹ * u⁻¹ = 1
    · have h1 := (hmem b u hu).mpr hbu
      rw [heq, hmem c u hu] at h1
      rw [hbu, h1]
    · have hcu : c * u * c⁻¹ * u⁻¹ ≠ 1 := by
        intro hcu
        have h1 := (hmem c u hu).mpr hcu
        rw [← heq, hmem b u hu] at h1
        exact hbu h1
      exact eq_of_mem_of_card_eq_two E.card_v1 (hF.toHypF91.commutator_mem_V₁ hb hu')
        (hF.toHypF91.commutator_mem_V₁ hc hu') hbu hcu
  calc u * (b⁻¹ * c) = b⁻¹ * (b * u * b⁻¹ * u⁻¹) * u * c := by group
    _ = b⁻¹ * (c * u * c⁻¹ * u⁻¹) * u * c := by rw [key]
    _ = b⁻¹ * c * u := by group

end Ctx7153

end CFSG.Quasithin.H13.L32A
