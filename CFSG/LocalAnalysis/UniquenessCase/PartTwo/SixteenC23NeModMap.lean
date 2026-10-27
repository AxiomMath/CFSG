module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC23NeDefs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenInfra

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

@[expose] noncomputable def c23neProj (Y V₀ V : Subgroup G) (hV : IsElemAbelian 2 V)
    (hYV₀ : Y ≤ V₀) : Vtil Y V hV →* Vtil V₀ V hV :=
  QuotientGroup.map (modNull Y V hV) (modNull V₀ V hV) (MonoidHom.id _)
    (fun x hx => (mem_modNull V₀ V hV x).2 (hYV₀ ((mem_modNull Y V hV x).1 hx)))

theorem c23neProj_mk {Y V₀ V : Subgroup G} (hV : IsElemAbelian 2 V) (hYV₀ : Y ≤ V₀)
    (x : IntMod V hV) :
    c23neProj Y V₀ V hV hYV₀ (mkTil Y V hV x) = mkTil V₀ V hV x :=
  rfl

@[expose] noncomputable def c23nePBlock (Y V₀ V : Subgroup G) (hV : IsElemAbelian 2 V)
    (hYV₀ : Y ≤ V₀) (E : Subgroup (Vtil V₀ V hV)) : Subgroup (Vtil Y V hV) :=
  E.comap (c23neProj Y V₀ V hV hYV₀)

theorem c23ne_mem_pBlock_iff {Y V₀ V : Subgroup G} (hV : IsElemAbelian 2 V) (hYV₀ : Y ≤ V₀)
    (E : Subgroup (Vtil V₀ V hV)) (q : Vtil Y V hV) :
    q ∈ c23nePBlock Y V₀ V hV hYV₀ E ↔ c23neProj Y V₀ V hV hYV₀ q ∈ E :=
  Iff.rfl

theorem c23neProj_surjective {Y V₀ V : Subgroup G} (hV : IsElemAbelian 2 V) (hYV₀ : Y ≤ V₀) :
    Function.Surjective (c23neProj Y V₀ V hV hYV₀) := by
  intro q
  obtain ⟨x, rfl⟩ := mkTil_surjective V₀ V hV q
  exact ⟨mkTil Y V hV x, c23neProj_mk hV hYV₀ x⟩

theorem c23neProj_ker {Y V₀ V : Subgroup G} (hV : IsElemAbelian 2 V) (hYV₀ : Y ≤ V₀) :
    (c23neProj Y V₀ V hV hYV₀).ker = imgTil Y V hV V₀ := by
  have hone : ∀ x : IntMod V hV, mkTil V₀ V hV x = 1 ↔ x.val ∈ V₀ := by
    intro x
    rw [← map_one (mkTil V₀ V hV), mkTil_eq_iff]
    simp
  ext q
  obtain ⟨x, rfl⟩ := mkTil_surjective Y V hV q
  rw [MonoidHom.mem_ker, c23neProj_mk, mem_imgTil, hone x]
  constructor
  · intro hx
    exact ⟨x, hx, rfl⟩
  · rintro ⟨y, hy, hyx⟩
    have h1 : y.val * x.val⁻¹ ∈ Y := (mkTil_eq_iff Y V hV y x).1 hyx
    have h2 : x.val = (y.val * x.val⁻¹)⁻¹ * y.val := by group
    rw [h2]
    exact V₀.mul_mem (V₀.inv_mem (hYV₀ h1)) hy

theorem c23neProj_actTil {Y V₀ V : Subgroup G} (hV : IsElemAbelian 2 V) (hYV₀ : Y ≤ V₀) {g : G}
    (hg₀ : g ∈ stabTil V₀ V) (hgY : g ∈ stabTil Y V) (q : Vtil Y V hV) :
    c23neProj Y V₀ V hV hYV₀ (actTil Y V hV ⟨g, hgY⟩ q) =
      actTil V₀ V hV ⟨g, hg₀⟩ (c23neProj Y V₀ V hV hYV₀ q) := by
  obtain ⟨x, rfl⟩ := mkTil_surjective Y V hV q
  rw [actTil_mk, c23neProj_mk, c23neProj_mk, actTil_mk]
  congr 1

theorem c23ne_ker_le_pBlock {Y V₀ V : Subgroup G} (hV : IsElemAbelian 2 V) (hYV₀ : Y ≤ V₀)
    (E : Subgroup (Vtil V₀ V hV)) : imgTil Y V hV V₀ ≤ c23nePBlock Y V₀ V hV hYV₀ E := by
  intro u hu
  rw [← c23neProj_ker hV hYV₀] at hu
  rw [c23ne_mem_pBlock_iff, MonoidHom.mem_ker.1 hu]
  exact E.one_mem

theorem c23ne_mem_comap_iff {Y V₀ V : Subgroup G} (hV : IsElemAbelian 2 V) (hYV₀ : Y ≤ V₀)
    (S : Subgroup (Vtil V₀ V hV)) {v : G} (hv : v ∈ V) :
    mkTil Y V hV (IntMod.mk hV ⟨v, hv⟩) ∈ S.comap (c23neProj Y V₀ V hV hYV₀) ↔
      v ∈ preTil V₀ V hV S := by
  rw [Subgroup.mem_comap, c23neProj_mk, mem_preTil_iff_of_mem V₀ V hV S hv]

theorem c23ne_preTil_comap {Y V₀ V : Subgroup G} (hV : IsElemAbelian 2 V) (hYV₀ : Y ≤ V₀)
    (S : Subgroup (Vtil V₀ V hV)) :
    preTil Y V hV (S.comap (c23neProj Y V₀ V hV hYV₀)) = preTil V₀ V hV S := by
  ext g
  constructor
  · intro hg
    have hgV : g ∈ V := preTil_le Y V hV _ hg
    exact (c23ne_mem_comap_iff hV hYV₀ S hgV).1
      ((mem_preTil_iff_of_mem Y V hV _ hgV).1 hg)
  · intro hg
    have hgV : g ∈ V := preTil_le V₀ V hV _ hg
    exact (mem_preTil_iff_of_mem Y V hV _ hgV).2 ((c23ne_mem_comap_iff hV hYV₀ S hgV).2 hg)

private theorem c23ne_modmap_mem_cTilde_iff {M V₀ V : Subgroup G} {g : G} :
    g ∈ F11.CTilde M V₀ V ↔ g ∈ M ∧ g ∈ Subgroup.normalizer (V₀ : Set G) ∧
      ∀ v ∈ V, g * v * g⁻¹ * v⁻¹ ∈ V₀ := by
  unfold F11.CTilde
  simp only [Subgroup.mem_iInf]
  constructor
  · intro h
    have h1 := h 1 V.one_mem
    exact ⟨h1.1, h1.2.1, fun v hv => (h v hv).2.2⟩
  · rintro ⟨h1, h2, h3⟩ v hv
    exact ⟨h1, h2, h3 v hv⟩

theorem c23ne_imgTil_le_fixV {Y V₀ V : Subgroup G} (hV : IsElemAbelian 2 V) {K : Subgroup G}
    (hK₀ : K ≤ centralizer (V₀ : Set G)) : imgTil Y V hV V₀ ≤ fixV (barSub Y V hV K) := by
  intro q hq
  rw [mem_fixV]
  intro φ hφ
  obtain ⟨g, hgK, rfl⟩ := (mem_barSub Y V hV K φ).1 hφ
  obtain ⟨z, hzV₀, rfl⟩ := (mem_imgTil Y V hV V₀ q).1 hq
  rw [actTil_mk]
  congr 1
  apply IntMod.val_injective
  rw [actStab_apply_val]
  have hcomm := (Subgroup.mem_centralizer_iff.1 (hK₀ hgK)) z.val hzV₀
  rw [← hcomm]
  group

private theorem c23ne_mem_nBar_iff {D : Data G} {V₀ V L : Subgroup G}
    (hMs : D.M ≤ stabTil V₀ V) {hV : IsElemAbelian 2 V} {m : G} (hm : m ∈ D.M) :
    m ∈ nBar D.M V₀ V hV L ↔
      barSub V₀ V hV (conjSubgroup L m) = barSub V₀ V hV L := by
  rw [nBar, mem_preBarSub]
  constructor
  · rintro ⟨-, hh, hnorm⟩
    rw [s15_Infra_barSub_conjSubgroup V₀ V hV hh L]
    exact (Subgroup.mem_normalizer_iff_map_conj_eq).1 (inv_mem hnorm)
  · intro heq
    refine ⟨hm, hMs hm, ?_⟩
    have hmap : (barSub V₀ V hV L).map
        (MulAut.conj (actTil V₀ V hV ⟨m, hMs hm⟩)⁻¹).toMonoidHom = barSub V₀ V hV L := by
      rw [← s15_Infra_barSub_conjSubgroup V₀ V hV (hMs hm) L]
      exact heq
    exact (inv_mem_iff).1 ((Subgroup.mem_normalizer_iff_map_conj_eq).2 hmap)

theorem c23ne_conj_swap {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V} {x : G}
    {K₁ K₂ : Subgroup G} (hMs : D.M ≤ stabTil V₀ V)
    (hctx : C23NeCtx D V₀ V L hV x K₁ K₂) :
    conjSubgroup K₁ x = K₂ ∧ conjSubgroup K₂ x = K₁ := by
  rcases hctx.perm x hctx.hxM with ⟨h1, h2⟩ | h
  · exfalso
    apply hctx.hxn
    rw [c23ne_mem_nBar_iff hMs hctx.hxM]
    have hbar : barSub V₀ V hV (conjSubgroup L x) = barSub V₀ V hV L := by
      have h2' := s15_Infra_barSub_conjSubgroup V₀ V hV (hMs hctx.hxM) K₁
      rw [h1, hctx.bar₁] at h2'
      rw [s15_Infra_barSub_conjSubgroup V₀ V hV (hMs hctx.hxM) L]
      exact h2'.symm
    exact hbar
  · exact h

theorem c23ne_equiv_bar {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V} {x : G}
    {K₁ K₂ Y : Subgroup G} (hctx : C23NeCtx D V₀ V L hV x K₁ K₂)
    (hMs : D.M ≤ stabTil V₀ V) (hYV₀ : Y ≤ V₀) (hYM : D.M ≤ normalizer (Y : Set G))
    (hY : c23neY V K₁ K₂ = Y) {K : Subgroup G} (hKM : K ≤ D.M) (hK : K ≤ K₁ ⊔ K₂) :
    ∃ ρ : ↥(barSub Y V hV K) ≃* ↥(barSub V₀ V hV K),
      ∀ (a : ↥(barSub Y V hV K)) (q : Vtil Y V hV),
        c23neProj Y V₀ V hV hYV₀ ((a : MulAut (Vtil Y V hV)) q) =
          ((ρ a : ↥(barSub V₀ V hV K)) : MulAut (Vtil V₀ V hV))
            (c23neProj Y V₀ V hV hYV₀ q) := by
  subst hY
  have hMsV : D.M ≤ normalizer (V : Set G) := hMs.trans (stabTil_le_normalizer V₀ V)
  have hKV : K ≤ stabTil V₀ V := hKM.trans hMs
  have hKY : K ≤ stabTil (c23neY V K₁ K₂) V := hKM.trans (le_stabTil hMsV hYM)
  let fY : ↥K →* MulAut (Vtil (c23neY V K₁ K₂) V hV) :=
    (actTil (c23neY V K₁ K₂) V hV).comp (Subgroup.inclusion hKY)
  let f₀ : ↥K →* MulAut (Vtil V₀ V hV) :=
    (actTil V₀ V hV).comp (Subgroup.inclusion hKV)
  have hfr : fY.range = barSub (c23neY V K₁ K₂) V hV K := by
    ext φ
    rw [MonoidHom.mem_range, mem_barSub]
    constructor
    · rintro ⟨k, rfl⟩
      exact ⟨⟨(k : G), hKY k.2⟩, k.2, rfl⟩
    · rintro ⟨g, hgK, rfl⟩
      exact ⟨⟨(g : G), hgK⟩, by
        show actTil (c23neY V K₁ K₂) V hV (Subgroup.inclusion hKY ⟨(g : G), hgK⟩) =
          actTil (c23neY V K₁ K₂) V hV g
        congr 1⟩
  have h₀r : f₀.range = barSub V₀ V hV K := by
    ext φ
    rw [MonoidHom.mem_range, mem_barSub]
    constructor
    · rintro ⟨k, rfl⟩
      exact ⟨⟨(k : G), hKV k.2⟩, k.2, rfl⟩
    · rintro ⟨g, hgK, rfl⟩
      exact ⟨⟨(g : G), hgK⟩, by
        show actTil V₀ V hV (Subgroup.inclusion hKV ⟨(g : G), hgK⟩) = actTil V₀ V hV g
        congr 1⟩
  have hYk : ∀ k : ↥K, fY k = actTil (c23neY V K₁ K₂) V hV ⟨(k : G), hKY k.2⟩ := fun k => rfl
  have h₀k : ∀ k : ↥K, f₀ k = actTil V₀ V hV ⟨(k : G), hKV k.2⟩ := fun k => rfl
  have hmemY : ∀ k : ↥K, fY k ∈ fY.range := fun k => (MonoidHom.mem_range).2 ⟨k, rfl⟩
  have hmem₀ : ∀ k : ↥K, f₀ k ∈ f₀.range := fun k => (MonoidHom.mem_range).2 ⟨k, rfl⟩
  have hker : fY.ker = f₀.ker := by
    ext k
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, hYk k, h₀k k]
    constructor
    · intro hk
      rw [actTil_eq_one_iff]
      intro v hv
      exact hYV₀ ((actTil_eq_one_iff (c23neY V K₁ K₂) V hV ⟨(k : G), hKY k.2⟩).1 hk v hv)
    · intro hk
      have hcomm : ∀ v ∈ V, (k : G) * v * (k : G)⁻¹ * v⁻¹ ∈ V₀ :=
        (actTil_eq_one_iff V₀ V hV ⟨(k : G), hKV k.2⟩).1 hk
      rw [actTil_eq_one_iff]
      intro v hv
      have hQ : (k : G) ∈ c23neQ2 K₁ K₂ := by
        rw [← hctx.ker]
        refine ⟨?_, hK k.2⟩
        exact c23ne_modmap_mem_cTilde_iff.2 ⟨hKM k.2, (hKV k.2).2, hcomm⟩
      show (k : G) * v * (k : G)⁻¹ * v⁻¹ ∈ ⁅V, c23neQ2 K₁ K₂⁆
      rw [← Subgroup.commutator_comm]
      exact Subgroup.commutator_mem_commutator hQ hv
  let ρ : ↥(barSub (c23neY V K₁ K₂) V hV K) ≃* ↥(barSub V₀ V hV K) :=
    (MulEquiv.subgroupCongr hfr).symm.trans
      ((QuotientGroup.quotientKerEquivRange fY).symm.trans
        ((QuotientGroup.quotientMulEquivOfEq hker).trans
          ((QuotientGroup.quotientKerEquivRange f₀).trans (MulEquiv.subgroupCongr h₀r))))
  have hρ_k : ∀ (k : ↥K) (hk : fY k ∈ barSub (c23neY V K₁ K₂) V hV K),
      (ρ ⟨fY k, hk⟩).val = f₀ k := by
    intro k hk
    have hA : (MulEquiv.subgroupCongr hfr).symm
        (⟨fY k, hk⟩ : ↥(barSub (c23neY V K₁ K₂) V hV K)) =
        (⟨fY k, hmemY k⟩ : ↥fY.range) := by
      apply Subtype.ext
      rw [MulEquiv.subgroupCongr_symm_apply]
    have hB : (QuotientGroup.quotientKerEquivRange fY).symm
        (⟨fY k, hmemY k⟩ : ↥fY.range) =
        (QuotientGroup.mk k : ↥K ⧸ fY.ker) := by
      rw [MulEquiv.symm_apply_eq]
      rfl
    have hC : (QuotientGroup.quotientMulEquivOfEq hker)
        (QuotientGroup.mk k : ↥K ⧸ fY.ker) = (QuotientGroup.mk k : ↥K ⧸ f₀.ker) :=
      QuotientGroup.quotientMulEquivOfEq_mk hker k
    have hD : (QuotientGroup.quotientKerEquivRange f₀)
        (QuotientGroup.mk k : ↥K ⧸ f₀.ker) =
        (⟨f₀ k, hmem₀ k⟩ : ↥f₀.range) := rfl
    have hunfold : (ρ ⟨fY k, hk⟩).val =
        ((MulEquiv.subgroupCongr h₀r) ((QuotientGroup.quotientKerEquivRange f₀)
          ((QuotientGroup.quotientMulEquivOfEq hker)
            ((QuotientGroup.quotientKerEquivRange fY).symm
              ((MulEquiv.subgroupCongr hfr).symm ⟨fY k, hk⟩))))).val := rfl
    rw [hunfold, hA, hB, hC, hD]
    exact MulEquiv.subgroupCongr_apply h₀r _
  refine ⟨ρ, ?_⟩
  intro a q
  obtain ⟨g, hgK, hga⟩ := (mem_barSub (c23neY V K₁ K₂) V hV K a.val).1 a.2
  let k : ↥K := ⟨(g : G), hgK⟩
  have hfYk : fY k = a.val := by
    show actTil (c23neY V K₁ K₂) V hV (Subgroup.inclusion hKY k) = a.val
    rw [show Subgroup.inclusion hKY k = g from Subtype.ext rfl, hga]
  have hp : fY k ∈ barSub (c23neY V K₁ K₂) V hV K := by rw [hfYk]; exact a.2
  have hρa : (ρ ⟨fY k, hp⟩).val = f₀ k := hρ_k k hp
  rw [show a = ⟨fY k, hp⟩ from Subtype.ext hfYk.symm, hρa]
  exact c23neProj_actTil hV hYV₀ (hKV k.2) (hKY k.2) q

theorem c23ne_transport {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V} {x : G}
    {K₁ K₂ : Subgroup G} (hMs : D.M ≤ stabTil V₀ V)
    (hctx : C23NeCtx D V₀ V L hV x K₁ K₂) {Y : Subgroup G} (hYV₀ : Y ≤ V₀)
    (hMY : D.M ≤ stabTil Y V) :
    barSub Y V hV K₂ =
        (barSub Y V hV K₁).map (MulAut.conj (actTil Y V hV ⟨x, hMY hctx.hxM⟩)⁻¹).toMonoidHom ∧
      c23nePBlock Y V₀ V hV hYV₀ (wTil V₀ V hV (conjSubgroup L x)) =
        (c23nePBlock Y V₀ V hV hYV₀ (wTil V₀ V hV L)).map
          (actTil Y V hV ⟨x, hMY hctx.hxM⟩)⁻¹.toMonoidHom := by
  obtain ⟨hswap, -⟩ := c23ne_conj_swap hMs hctx
  constructor
  · calc barSub Y V hV K₂
        = barSub Y V hV (conjSubgroup K₁ x) := by rw [hswap]
      _ = (barSub Y V hV K₁).map
            (MulAut.conj (actTil Y V hV ⟨x, hMY hctx.hxM⟩)⁻¹).toMonoidHom :=
          s15_Infra_barSub_conjSubgroup Y V hV (hMY hctx.hxM) K₁
  · ext q
    rw [c23ne_mem_pBlock_iff, Subgroup.mem_map, s15_Infra_wTil_conjSubgroup V₀ V L hV
      (hMs hctx.hxM), Subgroup.mem_map]
    constructor
    · rintro ⟨t, ht, hts⟩
      refine ⟨actTil Y V hV ⟨x, hMY hctx.hxM⟩ q, ?_, ?_⟩
      · rw [c23ne_mem_pBlock_iff,
          c23neProj_actTil (Y := Y) (V₀ := V₀) (V := V) hV hYV₀
            (hMs hctx.hxM) (hMY hctx.hxM) q]
        rw [← hts]
        change (actTil V₀ V hV ⟨x, hMs hctx.hxM⟩)
          ((actTil V₀ V hV ⟨x, hMs hctx.hxM⟩)⁻¹ t) ∈ wTil V₀ V hV L
        rw [MulAut.apply_inv_self]
        exact ht
      · change (actTil Y V hV ⟨x, hMY hctx.hxM⟩)⁻¹
          ((actTil Y V hV ⟨x, hMY hctx.hxM⟩) q) = q
        exact MulAut.inv_apply_self (Vtil Y V hV) _ q
    · rintro ⟨s, hs, hsq⟩
      rw [c23ne_mem_pBlock_iff] at hs
      change (actTil Y V hV ⟨x, hMY hctx.hxM⟩)⁻¹ s = q at hsq
      have hφinv : c23neProj Y V₀ V hV hYV₀
          ((actTil Y V hV ⟨x, hMY hctx.hxM⟩)⁻¹ s) =
          (actTil V₀ V hV ⟨x, hMs hctx.hxM⟩)⁻¹ (c23neProj Y V₀ V hV hYV₀ s) := by
        have h := c23neProj_actTil (Y := Y) (V₀ := V₀) (V := V) hV hYV₀
          (hMs hctx.hxM) (hMY hctx.hxM) ((actTil Y V hV ⟨x, hMY hctx.hxM⟩)⁻¹ s)
        rw [MulAut.apply_inv_self] at h
        rw [h, MulAut.inv_apply_self]
      refine ⟨c23neProj Y V₀ V hV hYV₀ s, hs, ?_⟩
      change (actTil V₀ V hV ⟨x, hMs hctx.hxM⟩)⁻¹
        (c23neProj Y V₀ V hV hYV₀ s) = c23neProj Y V₀ V hV hYV₀ q
      rw [← hφinv, hsq]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
