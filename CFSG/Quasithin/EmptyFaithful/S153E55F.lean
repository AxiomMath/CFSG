module

public import CFSG.Quasithin.EmptyFaithful.S153E53B
public import CFSG.Quasithin.EmptyFaithful.S153E55D

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.S1417 CFSG.LieType.BorelTits
open scoped commutatorElement Pointwise

namespace S153E55

open CFSG.Quasithin.S153E

section CenterU

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ : Subgroup G} {t : G}

omit [Finite G] in
theorem centerOf_U_comm {z u : G} (hz : z ∈ centerOf (UH153 T M V₁ Mc)) (hu : u ∈ UH153 T M V₁ Mc) :
    z * u = u * z :=
  (Subgroup.mem_centralizer_iff.mp hz.2 u hu).symm

theorem Z_le_centerOf_U (cx : Ctx15350 T Mc M V₁ V₂ t) :
    quasithinOmegaOneCenter T ≤ centerOf (UH153 T M V₁ Mc) := by
  intro z hz
  refine ⟨ZS_le_U cx (Z_le_ZS cx hz), Subgroup.mem_centralizer_iff.mpr fun u hu => ?_⟩
  have hu' : u ∈ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) :=
    cx.hF.H_le_centralizer ((U_le_T cx).trans (T_le_Mc cx) hu)
  exact (Subgroup.mem_centralizer_iff.mp hu' z hz).symm

omit [Finite G] in
theorem Mc_le_normalizer_centerOf_U :
    Mc ≤ Subgroup.normalizer ((centerOf (UH153 T M V₁ Mc) : Subgroup G) : Set G) :=
  (le_normalizer_conjClosure _ _).trans (normalizer_le_normalizer_centerOf _)

theorem ZS_not_le_centerOf (cx : Ctx15350 T Mc M V₁ V₂ t) (h52 : Concl15352 cx) :
    ¬ ZS153 T M V₁ ≤ centerOf (UH153 T M V₁ Mc) := by
  intro hle
  have hU : UH153 T M V₁ Mc ≤ centerOf (UH153 T M V₁ Mc) := by
    refine conjClosure_le fun x hx z hz => ?_
    exact (Subgroup.mem_normalizer_iff.mp (Mc_le_normalizer_centerOf_U (T := T) (M := M) (V₁ := V₁) hx) z).mp (hle hz)
  obtain ⟨a, ha, b, hb, hne⟩ := h52
  exact hne (centerOf_U_comm (hU ha) hb)

end CenterU

section Bar

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ : Subgroup G} {t : G}

theorem commV_zpowers_eq_fixV {W : Type} [CommGroup W] [Finite W] (hexp' : ∀ w : W, w ^ 2 = 1)
    (hcard : Nat.card W = 16) {g : MulAut W} (hgg : g * g = 1)
    (hf : Nat.card ↥(fixV (Subgroup.zpowers g)) = 4) :
    commV (Subgroup.zpowers g) = fixV (Subgroup.zpowers g) := by
  have hexp : ∀ w : W, w * w = 1 := fun w => by rw [← pow_two]; exact hexp' w
  have h1 := commV_zpowers_le_fixV_of_sq hexp hgg
  have h2 := rk_commV_add_rk_fixV g
  have h3 : rk (fixV (Subgroup.zpowers g)) = 2 :=
    T1531O4.rk_eq_of_card hexp' (n := 2) (by rw [hf]; norm_num)
  rw [S152O4.rk_V_eq_four hcard, h3] at h2
  exact eq_of_le_of_rk_le hexp' h1 (by omega)

theorem fixV_zpowers_eq (cx : Ctx15350 T Mc M V₁ V₂ t)
    {L₁ L₂ : Subgroup (MulAut (IntMod (VZ T M) cx.c.hyp.elemAbelian))}
    {tb s₁ s₂ τ : MulAut (IntMod (VZ T M) cx.c.hyp.elemAbelian)}
    {a₁ a₂ : IntMod (VZ T M) cx.c.hyp.elemAbelian}
    (hS : OfourStruct (autI cx.c.hyp.elemAbelian M) L₁ L₂ tb)
    (hF : OfourStruct.SylowFacts L₁ L₂ (autI cx.c.hyp.elemAbelian T) s₁ s₂ τ a₁ a₂) :
    fixV (Subgroup.zpowers (s₁ * s₂)) = fixV (autI cx.c.hyp.elemAbelian T ⊓ (L₁ ⊔ L₂)) := by
  have hexp' : ∀ w : IntMod (VZ T M) cx.c.hyp.elemAbelian, w ^ 2 = 1 := fun w => IntMod.sq_eq_one w
  have hfr : Nat.card ↥(fixV (Subgroup.zpowers (s₁ * s₂))) = 4 := card_fixV_mul_s hexp' hS hF.sylow
  have hrS : s₁ * s₂ ∈ autI cx.c.hyp.elemAbelian T ⊓ (L₁ ⊔ L₂) :=
    (hF.S_eq _).2 (Or.inr (Or.inr (Or.inr rfl)))
  exact (Subgroup.eq_of_le_of_card_ge (fixV_anti (Subgroup.zpowers_le.mpr hrS))
    (by rw [hfr, hF.card_fix])).symm

theorem centralizer_U_le_Z (cx : Ctx15350 T Mc M V₁ V₂ t) (h1 : ¬ VZ T M ≤ pCoreOf 2 Mc)
    (h52 : Concl15352 cx) {v : G} (hv : v ∈ VZ T M)
    (hc : ∀ u ∈ UH153 T M V₁ Mc, u * v = v * u) : v ∈ quasithinOmegaOneCenter T := by
  have hV := cx.c.hyp.elemAbelian
  obtain ⟨L₁, L₂, tb, s₁, s₂, τ, a₁, a₂, hS, hF, hV₁, -⟩ := exists_bar_model cx
  have hUS := not_le_S_of_nonabelian cx h52
  have hr := mul_mem_autI_U cx h1 hS hF
  have hfix := fixV_zpowers_eq cx hS hF
  have hSg := autI_Sgp153 hV hS (T_le_M cx) hV₁
  have hSN : Sgp153 T V₁ ≤ Subgroup.normalizer (VZ T M : Set G) := inf_le_left.trans (T_le_N cx)
  let w : IntMod (VZ T M) hV := IntMod.mk hV ⟨v, hv⟩
  have hwU : w ∈ fixV (autI hV (UH153 T M V₁ Mc)) :=
    (mem_fixV_autI hV (U_le_N cx) w).2 (Subgroup.mem_centralizer_iff.mpr hc)
  have hwr : w ∈ fixV (Subgroup.zpowers (s₁ * s₂)) :=
    fixV_anti (Subgroup.zpowers_le.mpr hr) hwU
  rw [hfix, ← hSg] at hwr
  have hvS : v ∈ Subgroup.centralizer (Sgp153 T V₁ : Set G) := (mem_fixV_autI hV hSN w).1 hwr
  obtain ⟨u₀, hu₀U, hu₀S⟩ := IsConcreteLE.not_le_iff_exists.mp hUS
  have hidx := Decomp153.relIndex_nS cx.c.hyp cx.c.decomp
  have hvT : v ∈ Subgroup.centralizer (T : Set G) := by
    refine Subgroup.mem_centralizer_iff.mpr fun y hy => ?_
    rcases coset_of_relIndex_two hidx hy (U_le_T cx hu₀U) hu₀S with h | h
    · exact Subgroup.mem_centralizer_iff.mp hvS y h
    · have h1 := Subgroup.mem_centralizer_iff.mp hvS _ h
      have h2 := hc u₀ hu₀U
      calc y * v = (y * u₀⁻¹) * (u₀ * v) := by group
        _ = (y * u₀⁻¹) * (v * u₀) := by rw [h2]
        _ = ((y * u₀⁻¹) * v) * u₀ := by group
        _ = (v * (y * u₀⁻¹)) * u₀ := by rw [h1]
        _ = v * y := by group
  rw [cx.c.hyp.lemma_15_3_2_two.1]
  exact ⟨hv, hvT⟩

theorem centerOf_U_le_centralizer (cx : Ctx15350 T Mc M V₁ V₂ t) (h52 : Concl15352 cx) :
    centerOf (UH153 T M V₁ Mc) ≤ Subgroup.centralizer (VZ T M : Set G) := by
  have hV := cx.c.hyp.elemAbelian
  obtain ⟨L₁, L₂, tb, s₁, s₂, τ, a₁, a₂, hS, hF, hV₁, -⟩ := exists_bar_model cx
  have hT := cx.c.hyp.isSylowTwoOf_autI
  have hcard16 : Nat.card (IntMod (VZ T M) hV) = 16 := cx.c.hyp.card_VZ
  have hexp' : ∀ w : IntMod (VZ T M) hV, w ^ 2 = 1 := fun w => IntMod.sq_eq_one w
  by_contra hcon
  obtain ⟨z, hzZ, hzC⟩ := IsConcreteLE.not_le_iff_exists.mp hcon
  have hzN : z ∈ Subgroup.normalizer (VZ T M : Set G) := U_le_N cx hzZ.1
  let Zb : Subgroup (MulAut (IntMod (VZ T M) hV)) := autI hV (centerOf (UH153 T M V₁ Mc))
  have hZbT : Zb ≤ autI hV T := autI_mono hV (inf_le_left.trans (U_le_T cx))
  have hZbn : ∀ h ∈ autI hV T, ∀ n ∈ Zb, h * n * h⁻¹ ∈ Zb := by
    intro h hh n hn
    obtain ⟨g', hgT, rfl⟩ := (mem_autI hV).1 hh
    obtain ⟨u, huZ, rfl⟩ := (mem_autI hV).1 hn
    have hmem : (g' : G) * u * (g' : G)⁻¹ ∈ centerOf (UH153 T M V₁ Mc) :=
      (Subgroup.mem_normalizer_iff.mp
        (Mc_le_normalizer_centerOf_U (T := T) (M := M) (V₁ := V₁) (T_le_Mc cx hgT)) _).mp huZ
    have hN : (g' : G) * u * (g' : G)⁻¹ ∈ Subgroup.normalizer (VZ T M : Set G) :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ g'.2 u.2) (Subgroup.inv_mem _ g'.2)
    have := convI_mem_autI hV hmem hN
    have e : (⟨(g' : G) * u * (g' : G)⁻¹, hN⟩ : Subgroup.normalizer (VZ T M : Set G)) = g' * u * g'⁻¹ :=
      Subtype.ext rfl
    rw [e, map_mul, map_mul, map_inv] at this
    exact this
  have hZb1 : ∃ n ∈ Zb, n ≠ 1 :=
    ⟨convI hV ⟨z, hzN⟩, convI_mem_autI hV hzZ hzN, fun h => hzC ((convI_eq_one_iff hV _).1 h)⟩
  have hr : s₁ * s₂ ∈ Zb := mul_mem_of_normal_ne_bot hS hT hF hZbT hZbn hZb1
  obtain ⟨u, hu, hur⟩ := (mem_autI hV).1 hr
  have hr2 : (s₁ * s₂) * (s₁ * s₂) = 1 := by
    calc (s₁ * s₂) * (s₁ * s₂) = s₁ * (s₂ * s₁) * s₂ := by group
      _ = s₁ * (s₁ * s₂) * s₂ := by rw [hF.comm]
      _ = (s₁ * s₁) * (s₂ * s₂) := by group
      _ = 1 := by rw [hF.s₁_sq, hF.s₂_sq, one_mul]
  have hfr : Nat.card ↥(fixV (Subgroup.zpowers (s₁ * s₂))) = 4 := card_fixV_mul_s hexp' hS hF.sylow
  have hcv := commV_zpowers_eq_fixV hexp' hcard16 hr2 hfr
  have hZS : ZS153 T M V₁ ≤ centerOf (UH153 T M V₁ Mc) := by
    intro x hx
    have hSN : Sgp153 T V₁ ≤ Subgroup.normalizer (VZ T M : Set G) := inf_le_left.trans (T_le_N cx)
    let w : IntMod (VZ T M) hV := IntMod.mk hV ⟨x, hx.1⟩
    have hwS : w ∈ fixV (autI hV (Sgp153 T V₁)) := (mem_fixV_autI hV hSN w).2 hx.2
    have hSg := autI_Sgp153 hV hS (T_le_M cx) hV₁
    rw [hSg, ← fixV_zpowers_eq cx hS hF, ← hcv] at hwS
    have hle : commV (Subgroup.zpowers (s₁ * s₂)) ≤
        (centerOf (UH153 T M V₁ Mc)).comap (inclMod hV) := by
      refine (Subgroup.closure_le _).mpr ?_
      rintro _ ⟨y, hy, w', rfl⟩
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      have hk : (s₁ * s₂) ^ k = convI hV (u ^ k) := by rw [← hur, map_zpow]
      rw [SetLike.mem_coe, Subgroup.mem_comap, hk]
      show ((convI hV (u ^ k) w' * w'⁻¹ : IntMod (VZ T M) hV).val) ∈ _
      rw [IntMod.val_mul, convI_apply_val, IntMod.val_inv]
      have e : ((u ^ k : Subgroup.normalizer (VZ T M : Set G)) : G) = (u : G) ^ k := by simp
      rw [e]
      have huk : (u : G) ^ k ∈ centerOf (UH153 T M V₁ Mc) := Subgroup.zpow_mem _ hu k
      have hw'Mc : w'.val ∈ Mc := cx.hF.V_le_H w'.val_mem
      have h2 : w'.val * ((u : G) ^ k)⁻¹ * w'.val⁻¹ ∈ centerOf (UH153 T M V₁ Mc) :=
        (Subgroup.mem_normalizer_iff.mp
          (Mc_le_normalizer_centerOf_U (T := T) (M := M) (V₁ := V₁) hw'Mc) _).mp
          (Subgroup.inv_mem _ huk)
      have h3 := Subgroup.mul_mem _ huk h2
      have e2 : (u : G) ^ k * w'.val * ((u : G) ^ k)⁻¹ * w'.val⁻¹ =
          (u : G) ^ k * (w'.val * ((u : G) ^ k)⁻¹ * w'.val⁻¹) := by group
      rw [e2]
      exact h3
    exact hle hwS
  exact ZS_not_le_centerOf cx h52 hZS

end Bar

end S153E55

end CFSG.Quasithin
