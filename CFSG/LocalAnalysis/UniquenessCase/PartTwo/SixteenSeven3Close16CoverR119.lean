module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenThreeY2
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven3Close16Mbar

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]
variable {D : Data G} {V L : Subgroup G} {hV : IsElemAbelian 2 V}

private theorem close16_preBarSub_mono {Xbar Ybar : Subgroup (MulAut (Vtil ⊥ V hV))}
    (h : Xbar ≤ Ybar) :
    preBarSub D.M ⊥ V hV Xbar ≤ preBarSub D.M ⊥ V hV Ybar := by
  unfold preBarSub
  exact inf_le_inf_left _ (Subgroup.map_mono (Subgroup.comap_mono h))

private theorem close16_preBarSub_conj_mem (hMs : D.M ≤ stabTil ⊥ V)
    (Xbar : Subgroup (MulAut (Vtil ⊥ V hV)))
    (hXbar_le : Xbar ≤ Mbar D.M ⊥ V hV)
    (hXbarN : (Xbar.subgroupOf (Mbar D.M ⊥ V hV)).Normal) {m x : G} (hm : m ∈ D.M) :
    x ∈ preBarSub D.M ⊥ V hV Xbar ↔ m * x * m⁻¹ ∈ preBarSub D.M ⊥ V hV Xbar := by
  have hnorm := (Subgroup.normal_subgroupOf_iff_le_normalizer hXbar_le).1 hXbarN
  constructor
  · intro hx
    obtain ⟨hxM, hxs, hxXbar⟩ := (mem_preBarSub D.M ⊥ V hV Xbar).1 hx
    have hst : m * x * m⁻¹ ∈ stabTil ⊥ V :=
      (stabTil ⊥ V).mul_mem ((stabTil ⊥ V).mul_mem (hMs hm) hxs)
        ((stabTil ⊥ V).inv_mem (hMs hm))
    refine (mem_preBarSub D.M ⊥ V hV Xbar).2
      ⟨D.M.mul_mem (D.M.mul_mem hm hxM) (D.M.inv_mem hm), hst, ?_⟩
    have hact : actTil ⊥ V hV ⟨m * x * m⁻¹, hst⟩ =
        actTil ⊥ V hV ⟨m, hMs hm⟩ * actTil ⊥ V hV ⟨x, hxs⟩ *
          (actTil ⊥ V hV ⟨m, hMs hm⟩)⁻¹ := by
      rw [show (⟨m * x * m⁻¹, hst⟩ : stabTil ⊥ V) =
          ⟨m, hMs hm⟩ * ⟨x, hxs⟩ * (⟨m, hMs hm⟩ : stabTil ⊥ V)⁻¹ from
        Subtype.ext (by simp [mul_assoc]), map_mul, map_mul, map_inv]
    rw [hact]
    have hmem := Subgroup.mem_normalizer_iff.1
      (hnorm (actTil_mem_barSub ⊥ V hV hm (hMs hm)))
    exact (hmem (actTil ⊥ V hV ⟨x, hxs⟩)).1 hxXbar
  · intro hx
    obtain ⟨hxM, hxs, hxXbar⟩ := (mem_preBarSub D.M ⊥ V hV Xbar).1 hx
    have hx_eq : x = m⁻¹ * (m * x * m⁻¹) * m := by group
    have hxM' : x ∈ D.M := by
      rw [hx_eq]
      exact D.M.mul_mem (D.M.mul_mem (D.M.inv_mem hm) hxM) hm
    have hxs' : x ∈ stabTil ⊥ V := by
      rw [hx_eq]
      exact (stabTil ⊥ V).mul_mem
        ((stabTil ⊥ V).mul_mem ((stabTil ⊥ V).inv_mem (hMs hm)) hxs) (hMs hm)
    refine (mem_preBarSub D.M ⊥ V hV Xbar).2 ⟨hxM', hxs', ?_⟩
    have hmsi : m⁻¹ ∈ stabTil ⊥ V := (stabTil ⊥ V).inv_mem (hMs hm)
    have hact : actTil ⊥ V hV ⟨x, hxs'⟩ =
        actTil ⊥ V hV ⟨m⁻¹, hmsi⟩ * actTil ⊥ V hV ⟨m * x * m⁻¹, hxs⟩ *
          (actTil ⊥ V hV ⟨m⁻¹, hmsi⟩)⁻¹ := by
      rw [show (⟨x, hxs'⟩ : stabTil ⊥ V) =
          ⟨m⁻¹, hmsi⟩ * ⟨m * x * m⁻¹, hxs⟩ * (⟨m⁻¹, hmsi⟩ : stabTil ⊥ V)⁻¹ from
        Subtype.ext (by simp only [Subgroup.coe_mul, Subgroup.coe_inv]; group),
          map_mul, map_mul, map_inv]
    rw [hact]
    have hmem := Subgroup.mem_normalizer_iff.1
      (hnorm (actTil_mem_barSub ⊥ V hV (D.M.inv_mem hm) hmsi))
    exact (hmem (actTil ⊥ V hV ⟨m * x * m⁻¹, hxs⟩)).1 hxXbar

theorem close16_exists_X (hS : Close16Setting D V L hV) :
    ∃ X : Subgroup G, F11.CTilde D.M ⊥ V ≤ X ∧ X ≤ D.M ∧ (X.subgroupOf D.M).Normal ∧
      barSub ⊥ V hV X = lBar ⊥ V hV L := by
  have hMs : D.M ≤ stabTil ⊥ V :=
    le_stabTil hS.counterex.setting.hyp151.hyp125.pairFacts.le_normalizer
      hS.counterex.setting.hyp151.hyp125.pairFacts.le_normalizer₀
  set X : Subgroup G := preBarSub D.M ⊥ V hV (lBar ⊥ V hV L) with hXdef
  have hX_le : X ≤ D.M := by rw [hXdef]; exact inf_le_left
  have hCX : F11.CTilde D.M ⊥ V ≤ X := by
    rw [hXdef, cTilde_eq_preBarSub_bot hV
      hS.counterex.setting.hyp151.hyp125.pairFacts.le_normalizer]
    exact close16_preBarSub_mono bot_le
  have hbarX : barSub ⊥ V hV X = lBar ⊥ V hV L := by
    rw [hXdef, barSub_preBarSub]
    exact inf_eq_left.2 (close16_lbar_le_mbar hS)
  have hXnormal : (X.subgroupOf D.M).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hX_le]
    intro m hm
    rw [Subgroup.mem_normalizer_iff]
    intro x
    change x ∈ preBarSub D.M ⊥ V hV (lBar ⊥ V hV L) ↔
      m * x * m⁻¹ ∈ preBarSub D.M ⊥ V hV (lBar ⊥ V hV L)
    exact close16_preBarSub_conj_mem hMs (lBar ⊥ V hV L) (close16_lbar_le_mbar hS)
      (close16_lbar_normal hS) hm
  exact ⟨X, hCX, hX_le, hXnormal, hbarX⟩

theorem close16_layer_barImage (hS : Close16Setting D V L hV) {X : Subgroup G}
    (hXM : X ≤ D.M) (hbar : barSub ⊥ V hV X = lBar ⊥ V hV L)
    [((F11.CTilde D.M ⊥ V).subgroupOf D.M).Normal] :
    rankThreeLayer (F11.barImage11 D.M ⊥ V X) = F11.barImage11 D.M ⊥ V X := by
  have hMs : D.M ≤ stabTil ⊥ V :=
    le_stabTil hS.counterex.setting.hyp151.hyp125.pairFacts.le_normalizer
      hS.counterex.setting.hyp151.hyp125.pairFacts.le_normalizer₀
  set B : Subgroup (F11.MBar11 D.M ⊥ V) := F11.barImage11 D.M ⊥ V X with hBdef
  have hqB : CFSG.Open.IsQuasisimple ↥B := by
    obtain ⟨e, he⟩ := s15_Three_barImage_equiv (D := D) (V₀ := ⊥) (V := V) hV hMs
    have hmap : B.map e.toMonoidHom = (lBar ⊥ V hV L).subgroupOf (Mbar D.M ⊥ V hV) := by
      rw [hBdef, he X hXM, hbar]
    let eB : ↥B ≃* ↥(lBar ⊥ V hV L) :=
      ((Subgroup.equivMapOfInjective B e.toMonoidHom e.injective).trans
        (MulEquiv.subgroupCongr hmap)).trans
        (Subgroup.subgroupOfEquivOfLe (close16_lbar_le_mbar hS))
    haveI : IsSimpleGroup ↥(lBar ⊥ V hV L) := close16_lbar_simple hS
    have hnotcomm : ¬ IsMulCommutative ↥(lBar ⊥ V hV L) := by
      intro hc
      haveI : IsMulCommutative ↥(lBar ⊥ V hV L) := hc
      have hp : (Nat.card ↥(lBar ⊥ V hV L)).Prime :=
        (Group.is_simple_iff_prime_card).mp inferInstance
      rw [close16_card_lbar hS] at hp
      exact (by norm_num : ¬ Nat.Prime 20160) hp
    have hqL : CFSG.Open.IsQuasisimple ↥(lBar ⊥ V hV L) := by
      have hperf : Group.IsPerfect ↥(lBar ⊥ V hV L) :=
        TauCeti.IsSimpleGroup.isPerfect_of_not_isMulCommutative hnotcomm
      have hcenter : Subgroup.center ↥(lBar ⊥ V hV L) = ⊥ :=
        TauCeti.IsSimpleGroup.center_eq_bot_of_not_isMulCommutative hnotcomm
      refine ⟨hperf.commutator_eq_top, ?_⟩
      let e' : ↥(lBar ⊥ V hV L) ⧸ Subgroup.center ↥(lBar ⊥ V hV L) ≃* ↥(lBar ⊥ V hV L) :=
        (QuotientGroup.quotientMulEquivOfEq hcenter).trans QuotientGroup.quotientBot
      exact e'.isSimpleGroup
    exact CFSG.Open.IsQuasisimple.of_mulEquiv eB hqL
  exact le_antisymm (sSup_le fun _ hK => hK.1)
    (le_sSup ⟨le_rfl, CFSG.Open.IsSubnormal.refl B, hqB⟩)

theorem close16_apply_r119 (h127 : R127 D) (h119 : F11.R119 D) (hS : Close16Setting D V L hV) :
    ∃ X Y : Subgroup G, F11.CTilde D.M ⊥ V ≤ X ∧ X ≤ D.M ∧ (X.subgroupOf D.M).Normal ∧
      barSub ⊥ V hV X = lBar ⊥ V hV L ∧ Y ≤ X ∧ ⁅Y, Y⁆ = Y ∧ F11.O2E Y = Y ∧
      X ≤ normalizer (Y : Set G) ∧ Y ⊓ F11.CTilde D.M ⊥ V ≤ OInf Y ∧
      barSub ⊥ V hV Y = lBar ⊥ V hV L := by
  have hMs : D.M ≤ stabTil ⊥ V :=
    le_stabTil hS.counterex.setting.hyp151.hyp125.pairFacts.le_normalizer
      hS.counterex.setting.hyp151.hyp125.pairFacts.le_normalizer₀
  obtain ⟨X, hCX, hXM, hXN, hbarX⟩ := close16_exists_X hS
  let inst₀ : ((F11.CTilde D.M ⊥ V).subgroupOf D.M).Normal := s15_Three_cTilde_normal hV hMs
  haveI := inst₀
  have hlayerim : rankThreeLayer (F11.barImage11 D.M ⊥ V X) = F11.barImage11 D.M ⊥ V X :=
    close16_layer_barImage hS hXM hbarX
  obtain ⟨Y, hY, -⟩ :=
    h119 ⊥ V (Hyp125.hyp11 h127 hS.counterex.setting.hyp151.hyp125) X hCX hXM hlayerim
  have hY_le : Y ≤ D.M := hY.1.trans hXM
  have hYbar : F11.barImage11 D.M ⊥ V Y = F11.barImage11 D.M ⊥ V X := hY.2.2.2.2.2
  obtain ⟨e, he⟩ := s15_Three_barImage_equiv (D := D) (V₀ := ⊥) (V := V) hV hMs
  have hbarY : barSub ⊥ V hV Y = lBar ⊥ V hV L := by
    have hsub : (barSub ⊥ V hV Y).subgroupOf (Mbar D.M ⊥ V hV) =
        (barSub ⊥ V hV X).subgroupOf (Mbar D.M ⊥ V hV) := by
      rw [← he Y hY_le, ← he X hXM, hYbar]
    have h2 := congrArg (Subgroup.map (Subgroup.subtype (Mbar D.M ⊥ V hV))) hsub
    simp only [Subgroup.subgroupOf_map_subtype] at h2
    rw [inf_eq_left.2 (barSub_mono ⊥ V hV hY_le),
      inf_eq_left.2 (barSub_mono ⊥ V hV hXM), hbarX] at h2
    exact h2
  exact ⟨X, Y, hCX, hXM, hXN, hbarX, hY.1, hY.2.1, hY.2.2.1, hY.2.2.2.1,
    hY.2.2.2.2.1, hbarY⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
