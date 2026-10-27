module

public import CFSG.Quasithin.Background.S1549CN2

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.S1417
  CFSG.Quasithin.F7 CFSG.Quasithin.CosetGeom
open scoped commutatorElement Pointwise

namespace S1549C

section Gen

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem claimN_le_normalizer_of_conj {K S : Subgroup G}
    (h : ∀ ℓ ∈ K, ∀ y ∈ S, ℓ * y * ℓ⁻¹ ∈ S) : K ≤ Subgroup.normalizer (S : Set G) := by
  intro ℓ hℓ
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨h ℓ hℓ y, fun hy => ?_⟩
  have := h ℓ⁻¹ (K.inv_mem hℓ) _ hy
  simpa [mul_assoc] using this

omit [Finite G] in
theorem claimN_exists_mul_of_mem_sup {A B : Subgroup G}
    (hB : B ≤ Subgroup.normalizer (A : Set G)) {x : G} (hx : x ∈ A ⊔ B) :
    ∃ a ∈ A, ∃ b ∈ B, x = a * b := by
  have h := Subgroup.coe_mul_of_right_le_normalizer_left A B hB
  have hx' : x ∈ ((A ⊔ B : Subgroup G) : Set G) := hx
  rw [h] at hx'
  obtain ⟨a, ha, b, hb, hab⟩ := hx'
  exact ⟨a, ha, b, hb, hab.symm⟩

theorem claimN_Uγ_le_K1 {T V L V₁ Vp H : Subgroup G} (h : HypF98 T V L V₁ Vp H)
    {γ γ' : F8.Geom T L H} {g : ↥((L ⊔ T) ⊔ H)} (s : F8Setup T V L H γ γ' g)
    (hEV : ⁅F9.EH V Vp V₁ H (g : G), F8.Uγ V H (g : G)⁆ = ⊥)
    (hVU : conjClosure V H ≤ conjClosure Vp H ⊔ F9.EH V Vp V₁ H (g : G)) :
    F8.Uγ Vp H (g : G) ≤ centralizerMod (conjClosure Vp H) H (conjClosure V H) := by
  have hVH : conjClosure V H ≤ H := conjClosure_le fun k hk v hv =>
    H.mul_mem (H.mul_mem hk (h.V_le_H hv)) (H.inv_mem hk)
  have hEN : F9.EH V Vp V₁ H (g : G) ≤ Subgroup.normalizer (conjClosure Vp H : Set G) :=
    ((centralizerMod_le_left _ _ _).trans hVH).trans (le_normalizer_conjClosure Vp H)
  intro u hu
  have huH : u ∈ H := h.Uγ_le_H s hu
  refine ⟨huH, le_normalizer_conjClosure Vp H huH, fun v hv => ?_⟩
  obtain ⟨a, ha, e, he, rfl⟩ := claimN_exists_mul_of_mem_sup hEN (hVU hv)
  have hcomm : u * e = e * u := Subgroup.mem_centralizer_iff.mp
    (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hEV he) u (h.Uγ_le_Vγ hu)
  have hue : u * e * u⁻¹ = e := by rw [hcomm]; group
  have e1 : u * (a * e) * u⁻¹ * (a * e)⁻¹ = (u * a * u⁻¹) * a⁻¹ := by
    calc u * (a * e) * u⁻¹ * (a * e)⁻¹ = (u * a * u⁻¹) * (u * e * u⁻¹) * e⁻¹ * a⁻¹ := by group
      _ = (u * a * u⁻¹) * a⁻¹ := by rw [hue]; group
  rw [e1]
  exact (conjClosure Vp H).mul_mem
    ((Subgroup.mem_normalizer_iff.mp (le_normalizer_conjClosure Vp H huH) a).mp ha)
    ((conjClosure Vp H).inv_mem ha)

theorem claimN_preStar_le {T V L V₁ Vp H : Subgroup G} (h : HypF91 T V L V₁ Vp H)
    {N W : Subgroup G} (hNH : N ≤ H) (hHN : H ≤ Subgroup.normalizer (N : Set G))
    (hQN : pCoreOf 2 H ≤ N) (hWN : W ≤ N)
    {B : Subgroup (MulAut ↥(tildeOf V₁ (conjClosure Vp H)))}
    (hB : B ≤ autOn (tildeOf V₁ W) (tildeOf V₁ (conjClosure Vp H))) :
    preStar h (conjClosure B (autOn (tildeOf V₁ H) (tildeOf V₁ (conjClosure Vp H)))) ≤ N := by
  have hWH : W ≤ H := hWN.trans hNH
  have key : conjClosure B (autOn (tildeOf V₁ H) (tildeOf V₁ (conjClosure Vp H))) ≤
      (N.subgroupOf H).map (starHom h) := by
    refine conjClosure_le fun p hp b hb => ?_
    rw [autOn_tilde_eq_map_starHom h le_rfl] at hp
    obtain ⟨x, -, rfl⟩ := Subgroup.mem_map.mp hp
    have hb' := hB hb
    rw [autOn_tilde_eq_map_starHom h hWH] at hb'
    obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.mp hb'
    rw [Subgroup.mem_subgroupOf] at hw
    refine Subgroup.mem_map.mpr ⟨x * w * x⁻¹, ?_, by simp [map_mul, map_inv]⟩
    rw [Subgroup.mem_subgroupOf]
    have := (Subgroup.mem_normalizer_iff.mp (hHN x.2) (w : G)).mp (hWN hw)
    simpa using this
  intro z hz
  obtain ⟨hzH, hzS⟩ := (mem_preStar_iff h).mp hz
  obtain ⟨n, hn, hnz⟩ := Subgroup.mem_map.mp (key hzS)
  rw [Subgroup.mem_subgroupOf] at hn
  have hq : (n : G)⁻¹ * z ∈ pCoreOf 2 H := by
    have h1 : starHom h (n⁻¹ * ⟨z, hzH⟩) = 1 := by
      rw [map_mul, map_inv, hnz, inv_mul_cancel]
    exact (starHom_eq_one_iff h _).mp h1
  have e : z = (n : G) * ((n : G)⁻¹ * z) := by group
  rw [e]
  exact N.mul_mem hn (hQN hq)

theorem claimN_le_of_perfect_of_le_sup {L K Q : Subgroup G} (hL : ⁅L, L⁆ = L)
    (hQ : IsPGroup 2 Q) (hQK : Q ≤ Subgroup.normalizer (K : Set G)) (hLKQ : L ≤ K ⊔ Q) :
    L ≤ K := by
  refine (eq_oTwoUpper_of_perfect hL).le.trans (oTwoUpper_le_of_pow_mem fun x hx => ?_)
  obtain ⟨a, ha, q, hq, rfl⟩ := claimN_exists_mul_of_mem_sup hQK (hLKQ hx)
  obtain ⟨m, hm⟩ := hQ ⟨q, hq⟩
  have hq1 : q ^ 2 ^ m = 1 := by simpa using congrArg Subtype.val hm
  obtain ⟨a', ha', hpow⟩ := A4.exists_pow_mul_eq ha (hQK hq) (2 ^ m)
  exact ⟨m, by rw [hpow, hq1, mul_one]; exact ha'⟩

omit [Finite G] in
theorem claimN_VH_le_sup {T V L V₁ Vp H : Subgroup G} (h : HypF91 T V L V₁ Vp H)
    {K Y₀ : Subgroup G} (hKH : K ≤ H)
    (hKV : ∀ ℓ ∈ K, ∀ v ∈ V, ℓ * v * ℓ⁻¹ * v⁻¹ ∈ conjClosure Vp H)
    (hY₀H : Y₀ ≤ H) (hY₀V : Y₀ ≤ Subgroup.centralizer (V : Set G))
    (hHK : H ≤ K ⊔ Y₀ ⊔ T) :
    conjClosure V H ≤ conjClosure Vp H ⊔ V := by
  have hUN := le_normalizer_conjClosure Vp H
  have hVN : V ≤ Subgroup.normalizer (conjClosure Vp H : Set G) := h.V_le_H.trans hUN
  have hK : K ≤ Subgroup.normalizer ((conjClosure Vp H ⊔ V : Subgroup G) : Set G) := by
    refine claimN_le_normalizer_of_conj fun ℓ hℓ y hy => ?_
    obtain ⟨u, hu, v, hv, rfl⟩ := claimN_exists_mul_of_mem_sup hVN hy
    have h1 : ℓ * u * ℓ⁻¹ ∈ conjClosure Vp H :=
      (Subgroup.mem_normalizer_iff.mp (hUN (hKH hℓ)) u).mp hu
    have e : ℓ * (u * v) * ℓ⁻¹ = (ℓ * u * ℓ⁻¹) * (ℓ * v * ℓ⁻¹ * v⁻¹) * v := by group
    rw [e]
    exact (conjClosure Vp H ⊔ V).mul_mem
      ((conjClosure Vp H ⊔ V).mul_mem (Subgroup.mem_sup_left h1)
        (Subgroup.mem_sup_left (hKV ℓ hℓ v hv))) (Subgroup.mem_sup_right hv)
  have hT : T ≤ Subgroup.normalizer ((conjClosure Vp H ⊔ V : Subgroup G) : Set G) :=
    (le_inf (h.T_le_H.trans hUN) h.T_normalizes_V).trans
      (Subgroup.inf_normalizer_le_normalizer_sup _ _)
  have hY : Y₀ ≤ Subgroup.normalizer ((conjClosure Vp H ⊔ V : Subgroup G) : Set G) :=
    (le_inf (hY₀H.trans hUN) (hY₀V.trans (Subgroup.centralizer_le_normalizer _))).trans
      (Subgroup.inf_normalizer_le_normalizer_sup _ _)
  have hHS : H ≤ Subgroup.normalizer ((conjClosure Vp H ⊔ V : Subgroup G) : Set G) :=
    hHK.trans (sup_le (sup_le hK hY) hT)
  exact conjClosure_le fun k hk v hv =>
    (Subgroup.mem_normalizer_iff.mp (hHS hk) v).mp (Subgroup.mem_sup_right hv)

end Gen

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ : Subgroup G} {t : G}

theorem claim_n (h11 : StageLemma14111) (h113 : StageLemma14113) (cx : Ctx49 G T Mc M V₁ V₂ t)
    {H : Subgroup G} (hb : InspBase cx H)
    {γ γ' : F8.Geom T (Y153 Mc M) H} {g : ↥(((Y153 Mc M) ⊔ T) ⊔ H)}
    (s : F8Setup T (VZ T M) (Y153 Mc M) H γ γ' g)
    (hpos : 0 < mIdx (F8.Uγ (ZS153 T M V₁) H (g : G))
      (F8.Dγ (ZS153 T M V₁) (quasithinOmegaOneCenter T) H (g : G)))
    (hle : mIdx (UH T M V₁ H) (F8.DH (ZS153 T M V₁) (quasithinOmegaOneCenter T) H (g : G)) ≤
      mIdx (F8.Uγ (ZS153 T M V₁) H (g : G))
        (F8.Dγ (ZS153 T M V₁) (quasithinOmegaOneCenter T) H (g : G)))
    {c : G} (hcH : c ∈ H) {B : Subgroup (MulAut (UTil T M V₁ H))}
    (od : OffData hb (conjSub c (F8.Uγ (VZ T M) H (g : G))) B)
    {L : Subgroup G} (hL : L ∈ cComp (Jgrp hb B))
    (hHL : H = conjClosure L T ⊔ Y0 T Mc M ⊔ T)
    (hm : UH T M V₁ H ⊔ VZ T M < VH T M H) :
    ∃ A, @IsStrongFFStarOffender (UTil T M V₁ H) (modInst hb.hF98.toHypF91)
      (StarOf T M V₁ H H) A ∧
      A ≤ StarOf T M V₁ H (pCoreOf 2 (Y0 T Mc M ⊔ T)) := by
  by_contra hno
  have h98 := hb.hF98
  have hF91 := h98.toHypF91
  obtain ⟨-, -, hVγ⟩ := claim_n1 h11 h113 cx hb hno s hpos hle
  have hn2 := claim_n2 h11 h113 cx hb hno s hpos hle
  have hEV := claim_f_EH h113 cx hb.adm h98 hb.claimC s
  have hUK := claimN_Uγ_le_K1 h98 s hEV hn2
  set K₁ := centralizerMod (conjClosure (ZS153 T M V₁) H) H (conjClosure (VZ T M) H) with hK₁
  have hHK₁ : H ≤ Subgroup.normalizer (K₁ : Set G) :=
    le_normalizer_centralizerMod (le_normalizer_conjClosure _ H) Subgroup.le_normalizer
      (le_normalizer_conjClosure _ H)
  have hK₁H : K₁ ≤ H := centralizerMod_le_left _ _ _
  have hNH : K₁ ⊔ pCoreOf 2 H ≤ H := sup_le hK₁H (pCoreOf_le 2 H)
  have hHN : H ≤ Subgroup.normalizer ((K₁ ⊔ pCoreOf 2 H : Subgroup G) : Set G) :=
    (le_inf hHK₁ (le_normalizer_pCoreOf 2 H)).trans (Subgroup.inf_normalizer_le_normalizer_sup _ _)
  have hEγQ : F9.Eγ (VZ T M) (ZS153 T M V₁) (quasithinOmegaOneCenter T) H (g : G) ≤
      pCoreOf 2 H := by
    rw [Eγ_eq_inf_pCoreOf h98 s]
    exact inf_le_right
  have hVN : F8.Uγ (VZ T M) H (g : G) ≤ K₁ ⊔ pCoreOf 2 H :=
    hVγ.le.trans (sup_le (hUK.trans le_sup_left) (hEγQ.trans le_sup_right))
  have hWN : conjSub c (F8.Uγ (VZ T M) H (g : G)) ≤ K₁ ⊔ pCoreOf 2 H := by
    have := conjSub_mono c hVN
    rwa [F7.conjSub_eq_of_mem_normalizer (hHN hcH)] at this
  have hJN : Jgrp hb B ≤ K₁ ⊔ pCoreOf 2 H := by
    unfold Jgrp
    exact claimN_preStar_le hF91 hNH hHN le_sup_right hWN od.B_le
  have hLK : L ≤ K₁ :=
    claimN_le_of_perfect_of_le_sup (perfect_of_mem_cComp hL) (pCoreOf_isPGroup 2 H)
      ((pCoreOf_le 2 H).trans hHK₁) ((le_of_mem_cComp hL).trans hJN)
  have hTH : T ≤ H := hF91.T_le_H
  have hLTK : conjClosure L T ≤ K₁ := conjClosure_le fun t ht ℓ hℓ =>
    (Subgroup.mem_normalizer_iff.mp (hHK₁ (hTH ht)) ℓ).mp (hLK hℓ)
  have hfin : conjClosure (VZ T M) H ≤ conjClosure (ZS153 T M V₁) H ⊔ VZ T M :=
    claimN_VH_le_sup hF91 (hLTK.trans hK₁H) (fun ℓ hℓ v hv =>
      (hLTK hℓ).2.2 v (le_conjClosure (VZ T M) H hv))
      (le_sup_left.trans hb.adm.hY0)
      ((Y0_le T Mc M).trans inf_le_right) hHL.le
  exact absurd hfin (not_le_of_gt hm)

end S1549C

end CFSG.Quasithin
