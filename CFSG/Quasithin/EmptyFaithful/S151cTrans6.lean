module

public import CFSG.Quasithin.EmptyFaithful.S151cCaseii
public import CFSG.Quasithin.EmptyFaithful.S151cGlue
public import CFSG.Quasithin.EmptyFaithful.S153Decomp

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique
open scoped Pointwise

namespace S151cTrans6

open CFSG.Quasithin.S1417

section Transport

variable {W W' : Type*} [CommGroup W] [CommGroup W']

theorem commV_map_congr (ϕ : W ≃* W') (X : Subgroup (MulAut W)) :
    commV (X.map (MulAut.congr ϕ).toMonoidHom) = (commV X).map ϕ.toMonoidHom :=
  commV_map_congr_equiv ϕ X

theorem isOmegaFourPlus_map_congr (ϕ : W ≃* W') {Y : Subgroup (MulAut W)}
    (hY : IsOmegaFourPlus Y) :
    IsOmegaFourPlus (Y.map (MulAut.congr ϕ).toMonoidHom) := by
  obtain ⟨hcard, q, hq, hnd, hpl, hmem⟩ := hY
  refine ⟨?_, fun w' => q (ϕ.symm w'), isQuadratic_comp ϕ.symm hq,
    isNondeg_comp ϕ.symm hnd, isPlus_comp ϕ.symm hpl, fun g' => ?_⟩
  · rw [← Nat.card_congr ϕ.toEquiv]
    exact hcard
  · obtain ⟨g, rfl⟩ : ∃ g : MulAut W, MulAut.congr ϕ g = g' :=
      ⟨(MulAut.congr ϕ).symm g', MulEquiv.apply_symm_apply _ _⟩
    have hrk : rk (commV (Subgroup.zpowers (MulAut.congr ϕ g))) =
        rk (commV (Subgroup.zpowers g)) := by
      have h1 : Subgroup.zpowers (MulAut.congr ϕ g) =
          (Subgroup.zpowers g).map (MulAut.congr ϕ).toMonoidHom :=
        (MonoidHom.map_zpowers (MulAut.congr ϕ).toMonoidHom g).symm
      rw [h1, commV_map_congr]
      unfold rk
      rw [Subgroup.card_map_of_injective ϕ.injective]
    have horth : MulAut.congr ϕ g ∈ orthogonalGroupOf (fun w' => q (ϕ.symm w')) ↔
        g ∈ orthogonalGroupOf q := by
      constructor
      · intro h v
        have := h (ϕ v)
        simpa [MulAut.congr_apply] using this
      · intro h v'
        have := h (ϕ.symm v')
        simpa [MulAut.congr_apply] using this
    rw [Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply, hmem, horth, hrk]

end Transport

section InclModAut

variable {G : Type} [Group G] {V : Subgroup G} (hV : IsElemAbelian 2 V)

theorem mem_preOn_iM {M : Subgroup G} {L : Subgroup (MulAut (IntMod V hV))} {x : G} :
    x ∈ preOn M V L ↔
      x ∈ M ∧ ∃ hx : x ∈ Subgroup.normalizer (V : Set G), convI hV ⟨x, hx⟩ ∈ L :=
  mem_preOn

@[expose] noncomputable def modEquiv (W : Subgroup (IntMod V hV)) :
    ↥W ≃* ↥(W.map (inclMod hV)) :=
  Subgroup.equivMapOfInjective W (inclMod hV) (inclMod_injective hV)

theorem modEquiv_apply_val (W : Subgroup (IntMod V hV)) (w : ↥W) :
    ((modEquiv hV W w : ↥(W.map (inclMod hV))) : G) = (w : IntMod V hV).val := rfl

theorem modEquiv_symm_val (W : Subgroup (IntMod V hV)) (u : ↥(W.map (inclMod hV))) :
    (((modEquiv hV W).symm u : ↥W) : IntMod V hV).val = (u : G) := by
  have := modEquiv_apply_val hV W ((modEquiv hV W).symm u)
  rw [MulEquiv.apply_symm_apply] at this
  exact this.symm

theorem congr_resHom_eq_conjAct {W : Subgroup (IntMod V hV)} {x : G}
    (hxN : x ∈ Subgroup.normalizer (V : Set G)) (hxs : convI hV ⟨x, hxN⟩ ∈ stabSub W)
    (hxU : x ∈ Subgroup.normalizer ((W.map (inclMod hV) : Subgroup G) : Set G)) :
    MulAut.congr (modEquiv hV W) (resHom W ⟨convI hV ⟨x, hxN⟩, hxs⟩) =
      conjAct (W.map (inclMod hV)) ⟨x, hxU⟩ := by
  refine MulEquiv.ext fun u => Subtype.ext ?_
  have h1 : ((MulAut.congr (modEquiv hV W) (resHom W ⟨convI hV ⟨x, hxN⟩, hxs⟩) u :
      ↥(W.map (inclMod hV))) : G) =
      x * (u : G) * x⁻¹ := by
    show ((modEquiv hV W (resHom W ⟨convI hV ⟨x, hxN⟩, hxs⟩ ((modEquiv hV W).symm u)) :
      ↥(W.map (inclMod hV))) : G) = _
    rw [modEquiv_apply_val, resHom_apply, ← modEquiv_symm_val hV W u]
    exact convI_apply_val hV ⟨x, hxN⟩ _
  rw [h1]
  exact (Subgroup.normalizerMonoidHom_apply_apply_coe _ (Subgroup.inclusion le_rfl ⟨x, hxU⟩) u).symm

theorem autOn_map_inclMod {M : Subgroup G} (hMN : M ≤ Subgroup.normalizer (V : Set G))
    {W : Subgroup (IntMod V hV)} (hW : ∀ x ∈ autI hV M, ∀ u ∈ W, x u ∈ W) :
    autOn M (W.map (inclMod hV)) =
      (autSub (autI hV M) W).map (MulAut.congr (modEquiv hV W)).toMonoidHom := by
  have hXs : autI hV M ≤ stabSub W := le_stabSub_of_invariant hW
  ext φ
  rw [mem_autOn_iff_exists, Subgroup.mem_map]
  constructor
  · rintro ⟨x, hxU, hxM, rfl⟩
    have hxN : x ∈ Subgroup.normalizer (V : Set G) := hMN hxM
    have hxs : convI hV ⟨x, hxN⟩ ∈ stabSub W := hXs (convI_mem_autI hV hxM hxN)
    refine ⟨resHom W ⟨convI hV ⟨x, hxN⟩, hxs⟩, ?_, congr_resHom_eq_conjAct hV hxN hxs hxU⟩
    exact mem_autSub.mpr ⟨⟨convI hV ⟨x, hxN⟩, hxs⟩, convI_mem_autI hV hxM hxN, rfl⟩
  · rintro ⟨ψ, hψ, rfl⟩
    obtain ⟨g, hgX, rfl⟩ := mem_autSub.mp hψ
    obtain ⟨y, hyM, hyg⟩ := (mem_autI hV).1 hgX
    have hys : convI hV y ∈ stabSub W := hyg ▸ g.2
    have hyU : (y : G) ∈ Subgroup.normalizer ((W.map (inclMod hV) : Subgroup G) : Set G) :=
      (mem_normalizer_map_inclMod_iff hV y.2 W).2 hys
    refine ⟨y, hyU, hyM, ?_⟩
    have := congr_resHom_eq_conjAct hV y.2 hys hyU
    rw [← this]
    have hg' : (⟨convI hV y, hys⟩ : ↥(stabSub W)) = g := Subtype.ext hyg
    rw [hg']
    rfl

theorem isOmegaFourPlusOn_map_inclMod {M : Subgroup G} (hMN : M ≤ Subgroup.normalizer (V : Set G))
    {W : Subgroup (IntMod V hV)} (hW : ∀ x ∈ autI hV M, ∀ u ∈ W, x u ∈ W)
    (hW4 : IsOmegaFourPlus (autSub (autI hV M) W)) :
    IsOmegaFourPlusOn M (W.map (inclMod hV)) := by
  have hU : IsElemAbelian 2 (W.map (inclMod hV)) :=
    B2F.isElemAbelian_mono (map_inclMod_le hV W) hV
  refine ⟨hU, ?_⟩
  let _ := commGroupOfElemAbelian hU
  rw [autOn_map_inclMod hV hMN hW]
  exact isOmegaFourPlus_map_congr (modEquiv hV W) hW4

theorem inf_centralizer_map_inclMod_eq_preOn {M : Subgroup G}
    (hMN : M ≤ Subgroup.normalizer (V : Set G)) (W : Subgroup (IntMod V hV)) :
    M ⊓ Subgroup.centralizer ((W.map (inclMod hV) : Subgroup G) : Set G) =
      preOn M V (autI hV M ⊓ centSub W : Subgroup (MulAut (IntMod V hV))) := by
  ext x
  rw [Subgroup.mem_inf, mem_preOn_iM hV]
  constructor
  · rintro ⟨hxM, hxC⟩
    have hxN := hMN hxM
    exact ⟨hxM, hxN, convI_mem_autI hV hxM hxN,
      (mem_centralizer_map_inclMod_iff hV hxN W).1 hxC⟩
  · rintro ⟨hxM, hxN, -, hx⟩
    exact ⟨hxM, (mem_centralizer_map_inclMod_iff hV hxN W).2 hx⟩

theorem inf_eq_preOn_autI {M Mc : Subgroup G} (hMN : M ≤ Subgroup.normalizer (V : Set G))
    (hC : Subgroup.centralizer (V : Set G) ≤ Mc) :
    M ⊓ Mc = preOn M V (autI hV (M ⊓ Mc)) := by
  ext x
  rw [mem_preOn_iM hV]
  constructor
  · rintro ⟨hxM, hxc⟩
    have hxN := hMN hxM
    exact ⟨hxM, hxN, convI_mem_autI hV (K := M ⊓ Mc) ⟨hxM, hxc⟩ hxN⟩
  · rintro ⟨hxM, hxN, hx⟩
    obtain ⟨g, hg, hgx⟩ := (mem_autI hV).1 hx
    refine ⟨hxM, ?_⟩
    have h1 : convI hV (g⁻¹ * (⟨x, hxN⟩ : ↥(Subgroup.normalizer (V : Set G)))) = 1 := by
      rw [map_mul, map_inv, hgx, inv_mul_cancel]
    have h2 := hC ((convI_eq_one_iff hV _).1 h1)
    have h3 : x = (g : G) * ((g : G)⁻¹ * x) := by group
    rw [h3]
    exact Mc.mul_mem hg.2 h2

theorem relIndex_preOn {M : Subgroup G} (hMN : M ≤ Subgroup.normalizer (V : Set G))
    (L : Subgroup (MulAut (IntMod V hV))) :
    (preOn M V L).relIndex M = L.relIndex (autI hV M) := by
  have h1 : (preOn M V L).subgroupOf M = L.comap (convHom hV M hMN) := by
    ext ⟨x, hxM⟩
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_comap, convHom_apply, mem_preOn_iM hV]
    exact ⟨fun ⟨_, _, h⟩ => h, fun h => ⟨hxM, hMN hxM, h⟩⟩
  rw [Subgroup.relIndex, h1, Subgroup.index_comap, range_convHom]

theorem coe_mul_mul_preOn {T M : Subgroup G} (hTM : T ≤ M)
    (hMN : M ≤ Subgroup.normalizer (V : Set G))
    {A B Xc : Subgroup (MulAut (IntMod V hV))} (hA : A ≤ autI hV M) (hB : B ≤ autI hV M)
    (hXc : (Xc : Set (MulAut (IntMod V hV))) =
      (A : Set (MulAut (IntMod V hV))) * (B : Set (MulAut (IntMod V hV))) *
        (autI hV T : Set (MulAut (IntMod V hV)))) :
    (preOn M V A : Set G) * (preOn M V B : Set G) * (T : Set G) = (preOn M V Xc : Set G) := by
  have hTN : T ≤ Subgroup.normalizer (V : Set G) := hTM.trans hMN
  ext x
  simp only [Set.mem_mul, SetLike.mem_coe]
  constructor
  · rintro ⟨_, ⟨p, hp, q, hq, rfl⟩, t, ht, rfl⟩
    obtain ⟨hpM, hpN, hpA⟩ := (mem_preOn_iM hV).mp hp
    obtain ⟨hqM, hqN, hqB⟩ := (mem_preOn_iM hV).mp hq
    have hxN : p * q * t ∈ Subgroup.normalizer (V : Set G) :=
      mul_mem (mul_mem hpN hqN) (hTN ht)
    refine (mem_preOn_iM hV).mpr ⟨M.mul_mem (M.mul_mem hpM hqM) (hTM ht), hxN, ?_⟩
    have hmul : convI hV ⟨p * q * t, hxN⟩ =
        convI hV ⟨p, hpN⟩ * convI hV ⟨q, hqN⟩ * convI hV ⟨t, hTN ht⟩ := by
      rw [← map_mul, ← map_mul]
      rfl
    have hτ : convI hV ⟨t, hTN ht⟩ ∈ autI hV T := convI_mem_autI hV ht (hTN ht)
    have hmem : convI hV ⟨p, hpN⟩ * convI hV ⟨q, hqN⟩ * convI hV ⟨t, hTN ht⟩ ∈
        (A : Set (MulAut (IntMod V hV))) * (B : Set (MulAut (IntMod V hV))) *
          (autI hV T : Set (MulAut (IntMod V hV))) :=
      Set.mul_mem_mul (Set.mul_mem_mul hpA hqB) hτ
    rw [← hXc] at hmem
    rw [hmul]
    exact hmem
  · intro hx
    obtain ⟨hxM, hxN, hxXc⟩ := (mem_preOn_iM hV).mp hx
    have hmem : convI hV ⟨x, hxN⟩ ∈ (A : Set (MulAut (IntMod V hV))) *
        (B : Set (MulAut (IntMod V hV))) * (autI hV T : Set (MulAut (IntMod V hV))) := by
      rw [← hXc]
      exact hxXc
    obtain ⟨_, ⟨a, ha, b, hb, rfl⟩, τ, hτ, hxeq⟩ := hmem
    obtain ⟨ga, hgaM, hga⟩ := (mem_autI hV).1 (hA ha)
    obtain ⟨gb, hgbM, hgb⟩ := (mem_autI hV).1 (hB hb)
    obtain ⟨gt, hgtT, hgt⟩ := (mem_autI hV).1 hτ
    have hconv : convI hV ⟨x, hxN⟩ = a * b * τ := hxeq.symm
    set p0 : ↥(Subgroup.normalizer (V : Set G)) :=
      (⟨x, hxN⟩ : ↥(Subgroup.normalizer (V : Set G))) * (ga * gb * gt)⁻¹ with hp0
    have hp0c : convI hV p0 = 1 := by
      rw [hp0, map_mul, map_inv, map_mul, map_mul, hga, hgb, hgt, hconv]
      exact mul_inv_cancel _
    have hgtM : (gt : G) ∈ M := hTM hgtT
    have hp0M : (p0 : G) ∈ M :=
      M.mul_mem hxM (M.inv_mem (M.mul_mem (M.mul_mem hgaM hgbM) hgtM))
    have hprod : p0 * ga * gb * gt = ⟨x, hxN⟩ := by
      rw [hp0]
      group
    have hpA : ((p0 * ga : ↥(Subgroup.normalizer (V : Set G))) : G) ∈ preOn M V A := by
      refine (mem_preOn_iM hV).mpr ⟨M.mul_mem hp0M hgaM, (p0 * ga).2, ?_⟩
      show convI hV (p0 * ga) ∈ A
      rw [map_mul, hp0c, one_mul, hga]
      exact ha
    have hqB : (gb : G) ∈ preOn M V B := by
      refine (mem_preOn_iM hV).mpr ⟨hgbM, gb.2, ?_⟩
      show convI hV gb ∈ B
      rw [hgb]
      exact hb
    refine ⟨((p0 * ga * gb : ↥(Subgroup.normalizer (V : Set G))) : G),
      ⟨((p0 * ga : ↥(Subgroup.normalizer (V : Set G))) : G), hpA, gb, hqB, rfl⟩, gt, hgtT, ?_⟩
    exact congrArg Subtype.val hprod

end InclModAut

section Six

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G}

theorem mJ154_le_normalizer (T M : Subgroup G) :
    mJ154 T M ≤ Subgroup.normalizer (VZ T M : Set G) :=
  (preOn_le _ _ _).trans (le_normalizer_VZ T M)

theorem autI_mJ154 (hVe : IsElemAbelian 2 (VZ T M)) :
    autI hVe (mJ154 T M) = Jhat (autI hVe M) := by
  have hJX : Jhat (autI hVe M) ≤ autOn M (VZ T M) := Jhat_le _
  unfold mJ154
  rw [JhatOn_eq_Jhat_autI M hVe]
  exact autOn_preOn hJX

theorem uJ154_eq_map_commV (hVe : IsElemAbelian 2 (VZ T M)) :
    uJ154 T M = (commV (Jhat (autI hVe M))).map (inclMod hVe) := by
  unfold uJ154
  rw [commutator_eq_map_commV hVe (mJ154_le_normalizer T M), autI_mJ154 hVe]

theorem cJ154_eq_map_fixV (hVe : IsElemAbelian 2 (VZ T M)) :
    cJ154 T M = (fixV (Jhat (autI hVe M))).map (inclMod hVe) := by
  have hfix : ∀ w : IntMod (VZ T M) hVe, w ∈ fixV (Jhat (autI hVe M)) ↔
      w.val ∈ Subgroup.centralizer (mJ154 T M : Set G) := fun w => by
    rw [← autI_mJ154 hVe]
    exact mem_fixV_autI hVe (mJ154_le_normalizer T M) w
  ext v
  constructor
  · rintro ⟨hvV, hvC⟩
    exact ⟨IntMod.mk hVe ⟨v, hvV⟩, (hfix _).2 hvC, rfl⟩
  · rintro ⟨w, hw, rfl⟩
    exact ⟨w.val_mem, (hfix w).1 hw⟩

end Six

end S151cTrans6

theorem case1512Six_of_case6Aut {G : Type} [Group G] [Finite G] {T Mc M : Subgroup G}
    (h : quasithinQTFE14Cat G T Mc) (hM : IsMf T Mc M) (hVe : IsElemAbelian 2 (VZ T M))
    (hC6 : Case6Aut (autI hVe M) (autI hVe T) (autI hVe (M ⊓ Mc)) (Jhat (autI hVe M))) :
    Case1512Six T Mc M := by
  have hMN : M ≤ Subgroup.normalizer (VZ T M : Set G) := le_normalizer_VZ T M
  have hTM : T ≤ M := hM.1.1.2
  have hCV : Subgroup.centralizer (VZ T M : Set G) ≤ Mc := centralizer_VZ_le_mc h
  have hu := S151cTrans6.uJ154_eq_map_commV hVe (T := T) (M := M)
  have hc := S151cTrans6.cJ154_eq_map_fixV hVe (T := T) (M := M)
  have hJn : NormalIn (autI hVe M) (Jhat (autI hVe M)) := fun x hx k hk => Jhat_conj_mem hx hk
  have hWinv : ∀ x ∈ autI hVe M, ∀ u ∈ commV (Jhat (autI hVe M)),
      x u ∈ commV (Jhat (autI hVe M)) := fun x hx u hu => hJn.commV_invariant hx hu
  have hinj : Function.Injective (S1417.inclMod hVe) := S1417.inclMod_injective hVe
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [JhatOn_eq_Jhat_autI M hVe]
    exact hC6.dihedral
  · rw [hu, hc, ← Subgroup.map_inf _ _ _ hinj, hC6.inf_eq, Subgroup.map_bot]
  · rw [hu, hc, ← Subgroup.map_sup, hC6.sup_eq, S1417.map_inclMod_top]
  · rw [hu, Subgroup.card_map_of_injective hinj]
    exact hC6.card_U
  · rw [hc]
    intro hbot
    exact hC6.fix_ne ((Subgroup.map_eq_bot_iff_of_injective _ hinj).1 hbot)
  · rw [hu]
    exact S151cTrans6.isOmegaFourPlusOn_map_inclMod hVe hMN hWinv hC6.omega
  · rw [hu, hc, S151cTrans6.inf_centralizer_map_inclMod_eq_preOn hVe hMN
        (commV (Jhat (autI hVe M))),
      S151cTrans6.inf_centralizer_map_inclMod_eq_preOn hVe hMN (fixV (Jhat (autI hVe M))),
      S151cTrans6.inf_eq_preOn_autI hVe hMN hCV]
    exact S151cTrans6.coe_mul_mul_preOn hVe hTM hMN inf_le_left inf_le_left hC6.xc_eq
  · rw [S151cTrans6.inf_eq_preOn_autI hVe hMN hCV, S151cTrans6.relIndex_preOn hVe hMN]
    exact hC6.index

end CFSG.Quasithin
