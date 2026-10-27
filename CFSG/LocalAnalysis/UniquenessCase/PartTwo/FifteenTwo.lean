module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenCore
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenInfra
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenKbar
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenLin

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem s15_Two_imgTil_iSup {ι : Sort*} (V₀ V : Subgroup G) (hV : IsElemAbelian 2 V)
    (U : ι → Subgroup G) (hU : ∀ i, U i ≤ V) :
    imgTil V₀ V hV (⨆ i, U i) = ⨆ i, imgTil V₀ V hV (U i) :=
  s15_Core_imgTil_iSup V₀ V hV U hU

theorem s15_Two_eq_of_imgTil_eq_top {V₀ V U : Subgroup G} (hV : IsElemAbelian 2 V)
    (hUV : U ≤ V) (hV₀ : V₀ ≤ U) (h : imgTil V₀ V hV U = ⊤) : U = V := by
  refine le_antisymm hUV fun v hv => ?_
  have hq : mkTil V₀ V hV (IntMod.mk hV ⟨v, hv⟩) ∈ imgTil V₀ V hV U := by
    rw [h]
    trivial
  rw [mem_imgTil] at hq
  obtain ⟨x, hxU, hxq⟩ := hq
  have hmem : v * x.val⁻¹ ∈ V₀ := by
    have h1 := (mkTil_eq_iff V₀ V hV (IntMod.mk hV ⟨v, hv⟩) x).1 hxq.symm
    exact h1
  have hv_eq : v = (v * x.val⁻¹) * x.val := by group
  rw [hv_eq]
  exact U.mul_mem (hV₀ hmem) hxU

theorem s15_Two_finsum_mem_eq_ncard_mul {α : Type*} (S : Set α) (f : α → ℕ) (c : ℕ)
    (hS : S.Finite) (hf : ∀ a ∈ S, f a = c) : ∑ᶠ a ∈ S, f a = S.ncard * c := by
  rw [finsum_mem_eq_finite_toFinset_sum f hS]
  refine (Finset.sum_congr rfl fun a ha => hf a (hS.mem_toFinset.1 ha)).trans ?_
  rw [Finset.sum_const, ← Set.ncard_eq_toFinset_card S hS, smul_eq_mul]

theorem s15_Two_eq_one_of_commute {W : Type*} [CommGroup W] {ι : Type*}
    (K : ι → Subgroup (MulAut W)) (x : MulAut W)
    (hcomm : ∀ i, ∀ k ∈ K i, x * k = k * x)
    (hfix : ∀ i, ∀ k ∈ K i, ∀ w : W, k (x w * w⁻¹) = x w * w⁻¹)
    (htop : ⨆ i, commSub ⊤ (K i) = ⊤) : x = 1 := by
  have hgen : ∀ i, ∀ k ∈ K i, ∀ u : W, x (k u * u⁻¹) = k u * u⁻¹ := by
    intro i k hk u
    have hcommu : x (k u) = k (x u) := by
      simpa [MulAut.mul_apply] using congrArg (fun f : MulAut W => f u) (hcomm i k hk)
    have h1 : k (x u) / (k u) = x u / u := by
      rw [div_eq_mul_inv, div_eq_mul_inv, ← hfix i k hk u, map_mul, map_inv]
    have h2 : k (x u) / (x u) = k u / u := div_eq_div_iff_div_eq_div.mp h1
    calc x (k u * u⁻¹) = x (k u) * (x u)⁻¹ := by rw [map_mul, map_inv]
      _ = k (x u) * (x u)⁻¹ := by rw [hcommu]
      _ = k u * u⁻¹ := by
        rw [← div_eq_mul_inv, ← div_eq_mul_inv]
        exact h2
  let Fx : Subgroup W :=
    { carrier := {w : W | x w = w}
      one_mem' := map_one x
      mul_mem' := fun {a b} ha hb => by
        change x (a * b) = a * b
        rw [map_mul, ha, hb]
      inv_mem' := fun {a} ha => by
        change x a⁻¹ = a⁻¹
        rw [map_inv, ha] }
  have hcore : ∀ i, commSub ⊤ (K i) ≤ Fx := by
    intro i
    rw [commSub, Subgroup.closure_le]
    rintro c ⟨k, hk, u, -, rfl⟩
    change x (k u * u⁻¹) = k u * u⁻¹
    exact hgen i k hk u
  have htop_le : (⊤ : Subgroup W) ≤ Fx := by
    rw [← htop]
    exact iSup_le hcore
  refine MulEquiv.ext fun w => ?_
  change x w = w
  exact htop_le (Subgroup.mem_top w)

theorem s15_Two_commute_of_inf_eq_bot {W : Type*} [CommGroup W] {A Y X : Subgroup (MulAut W)}
    (hYA : Y ≤ A) (hXA : X ≤ A) (hY : (Y.subgroupOf A).Normal) (hX : (X.subgroupOf A).Normal)
    (hYX : Y ⊓ X = ⊥) {y x : MulAut W} (hy : y ∈ Y) (hx : x ∈ X) : x * y = y * x := by
  have hyA : y ∈ A := hYA hy
  have hxA : x ∈ A := hXA hx
  have hdis : Disjoint (Y.subgroupOf A) (X.subgroupOf A) := by
    rw [Subgroup.disjoint_def]
    intro z hzY hzX
    have hd : Disjoint Y X := by
      rw [disjoint_iff]
      exact hYX
    exact Subtype.ext (Subgroup.disjoint_def.mp hd
      (Subgroup.mem_subgroupOf.mp hzY) (Subgroup.mem_subgroupOf.mp hzX))
  have hcommute := Subgroup.commute_of_normal_of_disjoint (Y.subgroupOf A) (X.subgroupOf A)
    hY hX hdis ⟨y, hyA⟩ ⟨x, hxA⟩ hy hx
  exact (congrArg Subtype.val hcommute.eq).symm

theorem s15_Two_le_wSub {V₀ V : Subgroup G} (hV : IsElemAbelian 2 V) (hV₀ : V₀ ≤ V)
    (L : Subgroup G) : V₀ ≤ wSub V₀ V hV L := by
  intro g hg
  rw [wSub, mem_preTil_iff_of_mem V₀ V hV _ (hV₀ hg)]
  have h1 : mkTil V₀ V hV (IntMod.mk hV ⟨g, hV₀ hg⟩) = 1 := by
    rw [← map_one (mkTil V₀ V hV), mkTil_eq_iff]
    change g * (1 : G)⁻¹ ∈ V₀
    simpa using hg
  rw [h1]
  exact (wTil V₀ V hV L).one_mem

theorem s15_Two_wConj_eq_range (M V₀ V L : Subgroup G) (hV : IsElemAbelian 2 V) :
    wConj M V₀ V hV L = Set.range fun m : M => conjSubgroup (wSub V₀ V hV L) (m : G) := by
  ext X
  rw [wConj, Set.mem_setOf_eq, Set.mem_range]
  constructor
  · rintro ⟨m, hm, hX⟩
    exact ⟨⟨m, hm⟩, hX.symm⟩
  · rintro ⟨m, hX⟩
    exact ⟨m, m.2, hX.symm⟩

theorem s15_Two_wStarConj_eq_range (M V₀ V L : Subgroup G) (hV : IsElemAbelian 2 V) :
    wStarConj M V₀ V hV L = Set.range fun m : M =>
      imgTil (v1Sub M V₀ V hV L) V hV (conjSubgroup (wSub V₀ V hV L) (m : G)) := by
  ext X
  rw [wStarConj, Set.mem_setOf_eq, Set.mem_range]
  constructor
  · rintro ⟨m, hm, hX⟩
    exact ⟨⟨m, hm⟩, hX.symm⟩
  · rintro ⟨m, hX⟩
    exact ⟨m, m.2, hX.symm⟩

theorem s15_Two_actTil_mul_inv_mem_imgTil {D : Data G} {V₀ V L : Subgroup G}
    (h : Hyp151 D V₀ V L) {g : G}
    (hg : g ∈ F11.CTilde D.M (v1Sub D.M V₀ V h.isElemAbelian L) V) (hgs : g ∈ stabTil V₀ V)
    (w : Vtil V₀ V h.isElemAbelian) :
    actTil V₀ V h.isElemAbelian ⟨g, hgs⟩ w * w⁻¹ ∈
      imgTil V₀ V h.isElemAbelian (v1Sub D.M V₀ V h.isElemAbelian L) := by
  obtain ⟨x, rfl⟩ := mkTil_surjective V₀ V h.isElemAbelian w
  rw [actTil_mk, ← map_inv, ← map_mul, mem_imgTil]
  refine ⟨actStab V₀ V h.isElemAbelian ⟨g, hgs⟩ x * x⁻¹, ?_, rfl⟩
  rw [IntMod.val_mul, IntMod.val_inv, actStab_apply_val]
  have hM : D.M ≤ normalizer (V : Set G) := h.hyp125.pairFacts.le_normalizer
  obtain ⟨hgs₁, hact₁⟩ := ((mem_cTilde_iff (M := D.M)
    (V₀ := v1Sub D.M V₀ V h.isElemAbelian L) (V := V) h.isElemAbelian hM).1 hg).2
  exact (actTil_eq_one_iff (v1Sub D.M V₀ V h.isElemAbelian L) V h.isElemAbelian
    ⟨g, hgs₁⟩).1 hact₁ x.val x.val_mem

theorem s15_Two_barSub_cTilde_le {D : Data G} {V₀ V L : Subgroup G} (h : Hyp151 D V₀ V L) :
    barSub V₀ V h.isElemAbelian (F11.CTilde D.M (v1Sub D.M V₀ V h.isElemAbelian L) V) ≤
      Mbar D.M V₀ V h.isElemAbelian := by
  refine barSub_mono V₀ V h.isElemAbelian ?_
  intro g hg
  exact ((mem_cTilde_iff (M := D.M) (V₀ := v1Sub D.M V₀ V h.isElemAbelian L) (V := V)
    h.isElemAbelian h.hyp125.pairFacts.le_normalizer).1 hg).1

theorem s15_Two_barSub_cTilde_normal {D : Data G} {V₀ V L : Subgroup G} (h : Hyp151 D V₀ V L) :
    ((barSub V₀ V h.isElemAbelian
        (F11.CTilde D.M (v1Sub D.M V₀ V h.isElemAbelian L) V)).subgroupOf
      (Mbar D.M V₀ V h.isElemAbelian)).Normal := by
  have hM : D.M ≤ normalizer (V : Set G) := h.hyp125.pairFacts.le_normalizer
  have hM₁ : D.M ≤ normalizer (v1Sub D.M V₀ V h.isElemAbelian L : Set G) :=
    s15_Infra_le_normalizer_v1Sub h.hyp125 h.isElemAbelian
  have hconj : ∀ φ ∈ Mbar D.M V₀ V h.isElemAbelian,
      ∀ ψ ∈ barSub V₀ V h.isElemAbelian
        (F11.CTilde D.M (v1Sub D.M V₀ V h.isElemAbelian L) V),
      φ * ψ * φ⁻¹ ∈ barSub V₀ V h.isElemAbelian
        (F11.CTilde D.M (v1Sub D.M V₀ V h.isElemAbelian L) V) := by
    intro φ hφ ψ hψ
    obtain ⟨g, hgM, rfl⟩ := (mem_barSub V₀ V h.isElemAbelian D.M φ).1 hφ
    obtain ⟨c, hc, rfl⟩ := (mem_barSub V₀ V h.isElemAbelian _ ψ).1 hψ
    obtain ⟨hcM, ⟨hc₁, hc₁'⟩⟩ := (mem_cTilde_iff (M := D.M)
      (V₀ := v1Sub D.M V₀ V h.isElemAbelian L) (V := V) h.isElemAbelian hM).1 hc
    have hgcM : (g : G) * (c : G) * (g : G)⁻¹ ∈ D.M :=
      D.M.mul_mem (D.M.mul_mem hgM hcM) (D.M.inv_mem hgM)
    have hgSt : (g : G) ∈ stabTil (v1Sub D.M V₀ V h.isElemAbelian L) V :=
      le_stabTil hM hM₁ hgM
    have hgc : (g : G) * (c : G) * (g : G)⁻¹ ∈
        F11.CTilde D.M (v1Sub D.M V₀ V h.isElemAbelian L) V := by
      have hgcSt : (g : G) * (c : G) * (g : G)⁻¹ ∈
          stabTil (v1Sub D.M V₀ V h.isElemAbelian L) V := le_stabTil hM hM₁ hgcM
      refine (mem_cTilde_iff (M := D.M) (V₀ := v1Sub D.M V₀ V h.isElemAbelian L) (V := V)
        h.isElemAbelian hM).2 ⟨hgcM, hgcSt, ?_⟩
      have hsub : (⟨(g : G) * (c : G) * (g : G)⁻¹, hgcSt⟩ :
            stabTil (v1Sub D.M V₀ V h.isElemAbelian L) V) =
          (⟨(g : G), hgSt⟩ : stabTil (v1Sub D.M V₀ V h.isElemAbelian L) V) *
            (⟨(c : G), hc₁⟩ : stabTil (v1Sub D.M V₀ V h.isElemAbelian L) V) *
            ((⟨(g : G), hgSt⟩ : stabTil (v1Sub D.M V₀ V h.isElemAbelian L) V))⁻¹ :=
        Subtype.ext rfl
      rw [hsub, map_mul, map_mul, map_inv, hc₁']
      group
    have heq : actTil V₀ V h.isElemAbelian g * actTil V₀ V h.isElemAbelian c *
        (actTil V₀ V h.isElemAbelian g)⁻¹ =
        actTil V₀ V h.isElemAbelian (g * c * g⁻¹) := by
      rw [map_mul, map_mul, map_inv]
    rw [heq]
    exact actTil_mem_barSub V₀ V h.isElemAbelian hgc (g * c * g⁻¹).2
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer (s15_Two_barSub_cTilde_le h)]
  intro φ hφ
  rw [Subgroup.mem_normalizer_iff]
  intro ψ
  constructor
  · intro hψ
    exact hconj φ hφ ψ hψ
  · intro hψ
    have h2 := hconj φ⁻¹ (Subgroup.inv_mem _ hφ) (φ * ψ * φ⁻¹) hψ
    rwa [show φ⁻¹ * (φ * ψ * φ⁻¹) * (φ⁻¹)⁻¹ = ψ by group] at h2

theorem s15_Two_inf_barSub_cTilde_eq_bot {D : Data G} {V₀ V L : Subgroup G}
    (h : Hyp151 D V₀ V L) :
    (⨆ m : D.M, barSub V₀ V h.isElemAbelian (conjSubgroup L (m : G))) ⊓
      barSub V₀ V h.isElemAbelian
        (F11.CTilde D.M (v1Sub D.M V₀ V h.isElemAbelian L) V) = ⊥ := by
  have hV := h.isElemAbelian
  have hP : (⨆ m : D.M, barSub V₀ V hV (conjSubgroup L (m : G))) ⊓
        barSub V₀ V hV (F11.CTilde D.M (v1Sub D.M V₀ V hV L) V) ≤
      Mbar D.M V₀ V hV :=
    inf_le_left.trans (s15_Infra_iSup_barSub_le h)
  haveI hYN : ((⨆ m : D.M, barSub V₀ V hV (conjSubgroup L (m : G))).subgroupOf
      (Mbar D.M V₀ V hV)).Normal := s15_Infra_iSup_barSub_normal h
  haveI hXN : ((barSub V₀ V hV (F11.CTilde D.M (v1Sub D.M V₀ V hV L) V)).subgroupOf
      (Mbar D.M V₀ V hV)).Normal := s15_Two_barSub_cTilde_normal h
  have hN : (((⨆ m : D.M, barSub V₀ V hV (conjSubgroup L (m : G))) ⊓
      barSub V₀ V hV (F11.CTilde D.M (v1Sub D.M V₀ V hV L) V)).subgroupOf
      (Mbar D.M V₀ V hV)).Normal := by
    have hinf : ((⨆ m : D.M, barSub V₀ V hV (conjSubgroup L (m : G))).subgroupOf
          (Mbar D.M V₀ V hV) ⊓
        (barSub V₀ V hV (F11.CTilde D.M (v1Sub D.M V₀ V hV L) V)).subgroupOf
          (Mbar D.M V₀ V hV)).Normal := inferInstance
    convert hinf using 1
    exact Subgroup.comap_inf _ _ _
  have h2 : IsPGroup 2 ↥((⨆ m : D.M, barSub V₀ V hV (conjSubgroup L (m : G))) ⊓
      barSub V₀ V hV (F11.CTilde D.M (v1Sub D.M V₀ V hV L) V)) := by
    refine s15_Lin_isPGroup_two_of_acts_trivially
      (C := imgTil V₀ V hV (v1Sub D.M V₀ V hV L)) (s15_Infra_vtil_sq_eq_one V₀ V hV) ?_ ?_
    · refine le_trans inf_le_left ?_
      refine iSup_le fun m => ?_
      intro k hk c hc
      exact mem_fixV.mp (s15_Core_imgTil_v1Sub_le_fixV h m.2 hc) k hk
    · intro x hx w
      have hxX : x ∈ barSub V₀ V hV (F11.CTilde D.M (v1Sub D.M V₀ V hV L) V) := hx.2
      obtain ⟨g, hg, rfl⟩ := (mem_barSub V₀ V hV _ x).1 hxX
      exact s15_Two_actTil_mul_inv_mem_imgTil h hg g.2 w
  exact s15_Kbar_eq_bot_of_normal_isPGroup D h.hyp125 hP hN h2

theorem s15_Two_rk_wStarConj {D : Data G} {V₀ V L : Subgroup G} (h : Hyp151 D V₀ V L)
    (hV : IsElemAbelian 2 V) {U : Subgroup (vStar D.M V₀ V hV L)}
    (hU : U ∈ wStarConj D.M V₀ V hV L) : rk ↥U = gamma15 D.M V₀ V hV L := by
  obtain ⟨m, hm, rfl⟩ := hU
  have hm_st : (m : G) ∈ stabTil (v1Sub D.M V₀ V hV L) V :=
    le_stabTil h.hyp125.pairFacts.le_normalizer (s15_Infra_le_normalizer_v1Sub h.hyp125 hV) hm
  rw [s15_Infra_imgTil_conjSubgroup (v1Sub D.M V₀ V hV L) V (wSub V₀ V hV L) hV hm_st]
  rw [s15_Lin_rk_map]
  rfl

theorem s15_Two_iSup_commSub_eq_top (D : Data G) (h1217 : R1217 D) {V₀ V L : Subgroup G}
    (h : Hyp151 D V₀ V L) (hL : barSub V₀ V h.isElemAbelian L ≠ ⊥) :
    ⨆ m : D.M, commSub ⊤ (barSub V₀ V h.isElemAbelian (conjSubgroup L (m : G))) = ⊤ := by
  obtain ⟨X, hX0, hXY, hXM, hXn, hshape⟩ := s15_Kbar_exists_shape D h hL
  have hmain : ⨆ I ∈ irrSet X, I = ⊤ := h1217 V₀ V h.hyp125 X hX0 hXM hXn hshape
  refine le_antisymm le_top ?_
  calc (⊤ : Subgroup (Vtil V₀ V h.isElemAbelian)) = ⨆ I ∈ irrSet X, I := hmain.symm
    _ ≤ ⨆ m : D.M, commSub ⊤
          (barSub V₀ V h.isElemAbelian (conjSubgroup L (m : G))) := by
        refine iSup₂_le fun I hI => ?_
        have hIeq : I = commSub I X := (Set.mem_setOf_eq.mp hI).1.symm
        calc I = commSub I X := hIeq
          _ ≤ commSub ⊤ X := commSub_mono le_top le_rfl
          _ ≤ commSub ⊤ (⨆ m : D.M,
                barSub V₀ V h.isElemAbelian (conjSubgroup L (m : G))) :=
              commSub_mono le_rfl hXY
          _ = ⨆ m : D.M, commSub ⊤
                (barSub V₀ V h.isElemAbelian (conjSubgroup L (m : G))) :=
              s15_Lin_commSub_top_iSup _

private theorem s15_Two_iSup_conjSubgroup_wSub_eq (D : Data G) (h1217 : R1217 D)
    {V₀ V L : Subgroup G} (h : Hyp151 D V₀ V L) (hV : IsElemAbelian 2 V)
    (hL : barSub V₀ V hV L ≠ ⊥) :
    ⨆ m : D.M, conjSubgroup (wSub V₀ V hV L) (m : G) = V := by
  have hMs : D.M ≤ stabTil V₀ V :=
    le_stabTil h.hyp125.pairFacts.le_normalizer h.hyp125.pairFacts.le_normalizer₀
  have hUle : ∀ m : D.M, conjSubgroup (wSub V₀ V hV L) (m : G) ≤ V := by
    intro m
    rw [← s15_Infra_wSub_conjSubgroup V₀ V L hV (hMs m.2)]
    exact preTil_le V₀ V hV _
  refine s15_Two_eq_of_imgTil_eq_top (V₀ := V₀) (V := V)
    (U := ⨆ m : D.M, conjSubgroup (wSub V₀ V hV L) (m : G)) hV (iSup_le hUle) ?_ ?_
  · have hW₀ : V₀ ≤ wSub V₀ V hV L := s15_Two_le_wSub hV h.hyp125.pairFacts.le L
    have h1 : wSub V₀ V hV L ≤ ⨆ m : D.M, conjSubgroup (wSub V₀ V hV L) (m : G) := by
      simpa [conjSubgroup_one] using
        (le_iSup (fun m : D.M => conjSubgroup (wSub V₀ V hV L) (m : G)) (1 : D.M))
    exact hW₀.trans h1
  · rw [s15_Two_imgTil_iSup V₀ V hV
      (fun m : D.M => conjSubgroup (wSub V₀ V hV L) (m : G)) hUle]
    refine (iSup_congr ?_).trans (s15_Two_iSup_commSub_eq_top D h1217 h hL)
    intro m
    show imgTil V₀ V hV (conjSubgroup (wSub V₀ V hV L) (m : G)) =
      commSub ⊤ (barSub V₀ V hV (conjSubgroup L (m : G)))
    rw [← s15_Infra_wSub_conjSubgroup V₀ V L hV (hMs m.2), wSub, imgTil_preTil]
    rfl

theorem fifteen_two_directSum (D : Data G) (h1217 : R1217 D) {V₀ V L : Subgroup G}
    (h : Hyp151 D V₀ V L) (hV : IsElemAbelian 2 V) (hL : barSub V₀ V hV L ≠ ⊥) :
    sSupIndep (wStarConj D.M V₀ V hV L) ∧ sSup (wStarConj D.M V₀ V hV L) = ⊤ := by
  have hMs : D.M ≤ stabTil V₀ V :=
    le_stabTil h.hyp125.pairFacts.le_normalizer h.hyp125.pairFacts.le_normalizer₀
  have hUle : ∀ m : D.M, conjSubgroup (wSub V₀ V hV L) (m : G) ≤ V := by
    intro m
    rw [← s15_Infra_wSub_conjSubgroup V₀ V L hV (hMs m.2)]
    exact preTil_le V₀ V hV _
  refine ⟨sSupIndep_wStarConj D h hV hL, ?_⟩
  rw [s15_Two_wStarConj_eq_range D.M V₀ V L hV, sSup_range]
  rw [← s15_Two_imgTil_iSup (v1Sub D.M V₀ V hV L) V hV
    (fun m : D.M => conjSubgroup (wSub V₀ V hV L) (m : G)) hUle]
  rw [s15_Two_iSup_conjSubgroup_wSub_eq D h1217 h hV hL]
  exact s15_Infra_imgTil_top (v1Sub D.M V₀ V hV L) V hV

theorem fifteen_two_cent (D : Data G) (h1217 : R1217 D) {V₀ V L : Subgroup G}
    (h : Hyp151 D V₀ V L) (hV : IsElemAbelian 2 V) :
    F11.CTilde D.M (v1Sub D.M V₀ V hV L) V = F11.CTilde D.M V₀ V := by
  have hM : D.M ≤ normalizer (V : Set G) := h.hyp125.pairFacts.le_normalizer
  have hMs : D.M ≤ stabTil V₀ V :=
    le_stabTil h.hyp125.pairFacts.le_normalizer h.hyp125.pairFacts.le_normalizer₀
  by_cases hL : barSub V₀ V hV L = ⊥
  · rw [s15_Infra_v1Sub_eq_of_barSub_eq_bot h.hyp125 hV hL]
  · apply le_antisymm
    · intro g hg
      obtain ⟨hgM, -⟩ := (mem_cTilde_iff (M := D.M)
        (V₀ := v1Sub D.M V₀ V hV L) (V := V) hV hM).1 hg
      have hg₀ : g ∈ stabTil V₀ V := hMs hgM
      have hx1 : actTil V₀ V hV ⟨g, hg₀⟩ = 1 := by
        refine s15_Two_eq_one_of_commute
          (K := fun m : D.M => barSub V₀ V hV (conjSubgroup L (m : G)))
          (actTil V₀ V hV ⟨g, hg₀⟩) ?_ ?_
          (s15_Two_iSup_commSub_eq_top D h1217 h hL)
        · intro i k hk
          have hxX : actTil V₀ V hV ⟨g, hg₀⟩ ∈
              barSub V₀ V hV (F11.CTilde D.M (v1Sub D.M V₀ V hV L) V) :=
            actTil_mem_barSub V₀ V hV hg hg₀
          exact s15_Two_commute_of_inf_eq_bot
            (s15_Infra_iSup_barSub_le h) (s15_Two_barSub_cTilde_le h)
            (s15_Infra_iSup_barSub_normal h) (s15_Two_barSub_cTilde_normal h)
            (s15_Two_inf_barSub_cTilde_eq_bot h)
            (le_iSup (fun m : D.M =>
              barSub V₀ V hV (conjSubgroup L (m : G))) i hk) hxX
        · intro i k hk w
          have hw : actTil V₀ V hV ⟨g, hg₀⟩ w * w⁻¹ ∈
              imgTil V₀ V hV (v1Sub D.M V₀ V hV L) :=
            s15_Two_actTil_mul_inv_mem_imgTil h hg hg₀ w
          exact (mem_fixV.mp (s15_Core_imgTil_v1Sub_le_fixV h i.2 hw)) k hk
      exact (mem_cTilde_iff (M := D.M) (V₀ := V₀) (V := V) hV hM).2
        ⟨hgM, ⟨hg₀, hx1⟩⟩
    · intro g hg
      obtain ⟨hgM, ⟨hgs₀, hact₀⟩⟩ := (mem_cTilde_iff (M := D.M) (V₀ := V₀) (V := V)
        hV hM).1 hg
      have hM₁ : D.M ≤ normalizer (v1Sub D.M V₀ V hV L : Set G) :=
        s15_Infra_le_normalizer_v1Sub h.hyp125 hV
      refine (mem_cTilde_iff (M := D.M) (V₀ := v1Sub D.M V₀ V hV L) (V := V)
        hV hM).2 ⟨hgM, ⟨le_stabTil hM hM₁ hgM, ?_⟩⟩
      rw [actTil_eq_one_iff]
      intro v hv
      exact s15_Infra_le_v1Sub D.M V₀ V hV L
        ((actTil_eq_one_iff V₀ V hV ⟨g, hgs₀⟩).1 hact₀ v hv)

theorem iSup_wConj_eq (D : Data G) (h1217 : R1217 D) {V₀ V L : Subgroup G}
    (h : Hyp151 D V₀ V L) (hV : IsElemAbelian 2 V) (hL : barSub V₀ V hV L ≠ ⊥) :
    ⨆ X ∈ wConj D.M V₀ V hV L, X = V := by
  rw [s15_Two_wConj_eq_range D.M V₀ V L hV, iSup_range]
  exact s15_Two_iSup_conjSubgroup_wSub_eq D h1217 h hV hL

theorem mSub_eq_s15_mul_gamma15_add (D : Data G) (h1217 : R1217 D) {V₀ V L : Subgroup G}
    (h : Hyp151 D V₀ V L) (hV : IsElemAbelian 2 V) (hL : barSub V₀ V hV L ≠ ⊥) :
    mSub V = s15 D.M V₀ V hV L * gamma15 D.M V₀ V hV L + mSub (v1Sub D.M V₀ V hV L) := by
  obtain ⟨hind, hspan⟩ := fifteen_two_directSum D h1217 h hV hL
  have hV₁ : v1Sub D.M V₀ V hV L ≤ V := s15_Infra_v1Sub_le h.hyp125 hV
  have hmain : mSub V = rk ↥(⊤ : Subgroup (vStar D.M V₀ V hV L)) +
      mSub (v1Sub D.M V₀ V hV L) := by
    have h := s15_Infra_mSub_eq_rk_imgTil_add (v1Sub D.M V₀ V hV L) V V hV le_rfl
    rw [s15_Infra_imgTil_top (v1Sub D.M V₀ V hV L) V hV, inf_eq_right.mpr hV₁] at h
    exact h
  have htop : rk ↥(⊤ : Subgroup (vStar D.M V₀ V hV L)) =
      s15 D.M V₀ V hV L * gamma15 D.M V₀ V hV L := by
    calc rk ↥(⊤ : Subgroup (vStar D.M V₀ V hV L))
        = rk ↥(sSup (wStarConj D.M V₀ V hV L)) := by rw [hspan]
      _ = ∑ᶠ U ∈ wStarConj D.M V₀ V hV L, rk ↥U := s15_Lin_rk_sSup_eq_finsum hind
      _ = (wStarConj D.M V₀ V hV L).ncard * gamma15 D.M V₀ V hV L :=
          s15_Two_finsum_mem_eq_ncard_mul _ _ _ (Set.toFinite _)
            (fun U hU => s15_Two_rk_wStarConj h hV hU)
      _ = s15 D.M V₀ V hV L * gamma15 D.M V₀ V hV L := by
          rw [ncard_wStarConj D h hV]
  rw [hmain, htop]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
