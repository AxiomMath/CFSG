module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.ElevenNineEngine
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenThreeY2
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC23Unique
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven3Close16CoverKer
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven3Close16CoverNormal
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven3Close16CoverQuot
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenT3L4Mbar

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]
variable {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}

theorem s16t_l4_exists_hom_barSub {D : Data G} {V₀ V : Subgroup G} {hV : IsElemAbelian 2 V}
    (hM : D.M ≤ stabTil V₀ V) {X : Subgroup G} (hXM : X ≤ D.M) :
    ∃ φ : ↥X →* ↥(barSub V₀ V hV X), Function.Surjective φ ∧
      φ.ker = (X ⊓ F11.CTilde D.M V₀ V).subgroupOf X := by
  have hXs : X ≤ stabTil V₀ V := hXM.trans hM
  let ψ : ↥X →* ↥(stabTil V₀ V) := Subgroup.inclusion hXs
  let φ : ↥X →* ↥(barSub V₀ V hV X) :=
    MonoidHom.codRestrict ((actTil V₀ V hV).comp ψ) (barSub V₀ V hV X)
      (fun g => (mem_barSub V₀ V hV X _).2 ⟨ψ g, g.2, rfl⟩)
  refine ⟨φ, ?_, ?_⟩
  · rintro ⟨_, hφ⟩
    obtain ⟨g, hg, rfl⟩ := (mem_barSub V₀ V hV X _).1 hφ
    exact ⟨⟨(g : G), hg⟩, rfl⟩
  · ext g
    have hMn : D.M ≤ normalizer (V : Set G) := hM.trans (stabTil_le_normalizer V₀ V)
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf, mem_cTilde_iff hV hMn]
    have hgX : (g : G) ∈ X := g.2
    constructor
    · intro h1
      exact ⟨hgX, hXM hgX, hXs hgX, congrArg Subtype.val h1⟩
    · rintro ⟨-, -, h, h1⟩
      exact Subtype.ext h1

private theorem s16t_l4_preBarSub_mono {Xbar Ybar : Subgroup (MulAut (Vtil V₀ V hV))}
    (h : Xbar ≤ Ybar) :
    preBarSub D.M V₀ V hV Xbar ≤ preBarSub D.M V₀ V hV Ybar := by
  unfold preBarSub
  exact inf_le_inf_left _ (Subgroup.map_mono (Subgroup.comap_mono h))

private theorem s16t_l4_preBarSub_conj_mem (hMs : D.M ≤ stabTil V₀ V)
    (Xbar : Subgroup (MulAut (Vtil V₀ V hV)))
    (hXbar_le : Xbar ≤ Mbar D.M V₀ V hV)
    (hXbarN : (Xbar.subgroupOf (Mbar D.M V₀ V hV)).Normal) {m x : G} (hm : m ∈ D.M) :
    x ∈ preBarSub D.M V₀ V hV Xbar ↔ m * x * m⁻¹ ∈ preBarSub D.M V₀ V hV Xbar := by
  have hnorm := (Subgroup.normal_subgroupOf_iff_le_normalizer hXbar_le).1 hXbarN
  constructor
  · intro hx
    obtain ⟨hxM, hxs, hxXbar⟩ := (mem_preBarSub D.M V₀ V hV Xbar).1 hx
    have hst : m * x * m⁻¹ ∈ stabTil V₀ V :=
      (stabTil V₀ V).mul_mem ((stabTil V₀ V).mul_mem (hMs hm) hxs)
        ((stabTil V₀ V).inv_mem (hMs hm))
    refine (mem_preBarSub D.M V₀ V hV Xbar).2
      ⟨D.M.mul_mem (D.M.mul_mem hm hxM) (D.M.inv_mem hm), hst, ?_⟩
    have hact : actTil V₀ V hV ⟨m * x * m⁻¹, hst⟩ =
        actTil V₀ V hV ⟨m, hMs hm⟩ * actTil V₀ V hV ⟨x, hxs⟩ *
          (actTil V₀ V hV ⟨m, hMs hm⟩)⁻¹ := by
      rw [show (⟨m * x * m⁻¹, hst⟩ : stabTil V₀ V) =
          ⟨m, hMs hm⟩ * ⟨x, hxs⟩ * (⟨m, hMs hm⟩ : stabTil V₀ V)⁻¹ from
        Subtype.ext (by simp [mul_assoc]), map_mul, map_mul, map_inv]
    rw [hact]
    have hmem := Subgroup.mem_normalizer_iff.1
      (hnorm (actTil_mem_barSub V₀ V hV hm (hMs hm)))
    exact (hmem (actTil V₀ V hV ⟨x, hxs⟩)).1 hxXbar
  · intro hx
    obtain ⟨hxM, hxs, hxXbar⟩ := (mem_preBarSub D.M V₀ V hV Xbar).1 hx
    have hx_eq : x = m⁻¹ * (m * x * m⁻¹) * m := by group
    have hxM' : x ∈ D.M := by
      rw [hx_eq]
      exact D.M.mul_mem (D.M.mul_mem (D.M.inv_mem hm) hxM) hm
    have hxs' : x ∈ stabTil V₀ V := by
      rw [hx_eq]
      exact (stabTil V₀ V).mul_mem
        ((stabTil V₀ V).mul_mem ((stabTil V₀ V).inv_mem (hMs hm)) hxs) (hMs hm)
    refine (mem_preBarSub D.M V₀ V hV Xbar).2 ⟨hxM', hxs', ?_⟩
    have hmsi : m⁻¹ ∈ stabTil V₀ V := (stabTil V₀ V).inv_mem (hMs hm)
    have hact : actTil V₀ V hV ⟨x, hxs'⟩ =
        actTil V₀ V hV ⟨m⁻¹, hmsi⟩ * actTil V₀ V hV ⟨m * x * m⁻¹, hxs⟩ *
          (actTil V₀ V hV ⟨m⁻¹, hmsi⟩)⁻¹ := by
      rw [show (⟨x, hxs'⟩ : stabTil V₀ V) =
          ⟨m⁻¹, hmsi⟩ * ⟨m * x * m⁻¹, hxs⟩ * (⟨m⁻¹, hmsi⟩ : stabTil V₀ V)⁻¹ from
        Subtype.ext (by simp only [Subgroup.coe_mul, Subgroup.coe_inv]; group),
          map_mul, map_mul, map_inv]
    rw [hact]
    have hmem := Subgroup.mem_normalizer_iff.1
      (hnorm (actTil_mem_barSub V₀ V hV (D.M.inv_mem hm) hmsi))
    exact (hmem (actTil V₀ V hV ⟨m * x * m⁻¹, hxs⟩)).1 hxXbar

theorem s16t_l4_exists_X (hS : S16tL4Setting D V₀ V L hV) :
    ∃ X : Subgroup G, F11.CTilde D.M V₀ V ≤ X ∧ X ≤ D.M ∧ (X.subgroupOf D.M).Normal ∧
      barSub V₀ V hV X = lBar V₀ V hV L := by
  have hMs : D.M ≤ stabTil V₀ V :=
    le_stabTil hS.counterex.setting.hyp151.hyp125.pairFacts.le_normalizer
      hS.counterex.setting.hyp151.hyp125.pairFacts.le_normalizer₀
  set X : Subgroup G := preBarSub D.M V₀ V hV (lBar V₀ V hV L) with hXdef
  have hX_le : X ≤ D.M := by rw [hXdef]; exact inf_le_left
  have hCX : F11.CTilde D.M V₀ V ≤ X := by
    rw [hXdef, cTilde_eq_preBarSub_bot hV
      hS.counterex.setting.hyp151.hyp125.pairFacts.le_normalizer]
    exact s16t_l4_preBarSub_mono bot_le
  have hbarX : barSub V₀ V hV X = lBar V₀ V hV L := by
    rw [hXdef, barSub_preBarSub]
    exact inf_eq_left.2 (s16t_l4_lbar_le_mbar hS)
  have hXnormal : (X.subgroupOf D.M).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hX_le]
    intro m hm
    rw [Subgroup.mem_normalizer_iff]
    intro x
    change x ∈ preBarSub D.M V₀ V hV (lBar V₀ V hV L) ↔
      m * x * m⁻¹ ∈ preBarSub D.M V₀ V hV (lBar V₀ V hV L)
    exact s16t_l4_preBarSub_conj_mem hMs (lBar V₀ V hV L) (s16t_l4_lbar_le_mbar hS)
      (s16t_l4_lbar_normal hS) hm
  exact ⟨X, hCX, hX_le, hXnormal, hbarX⟩

theorem s16t_l4_layer_barImage (hS : S16tL4Setting D V₀ V L hV) {X : Subgroup G}
    (hXM : X ≤ D.M) (hbar : barSub V₀ V hV X = lBar V₀ V hV L)
    [((F11.CTilde D.M V₀ V).subgroupOf D.M).Normal] :
    rankThreeLayer (F11.barImage11 D.M V₀ V X) = F11.barImage11 D.M V₀ V X := by
  have hMs : D.M ≤ stabTil V₀ V :=
    le_stabTil hS.counterex.setting.hyp151.hyp125.pairFacts.le_normalizer
      hS.counterex.setting.hyp151.hyp125.pairFacts.le_normalizer₀
  set B : Subgroup (F11.MBar11 D.M V₀ V) := F11.barImage11 D.M V₀ V X with hBdef
  have hqB : CFSG.Open.IsQuasisimple ↥B := by
    obtain ⟨e, he⟩ := s15_Three_barImage_equiv (D := D) (V₀ := V₀) (V := V) hV hMs
    have hmap : B.map e.toMonoidHom = (lBar V₀ V hV L).subgroupOf (Mbar D.M V₀ V hV) := by
      rw [hBdef, he X hXM, hbar]
    let eB : ↥B ≃* ↥(lBar V₀ V hV L) :=
      ((Subgroup.equivMapOfInjective B e.toMonoidHom e.injective).trans
        (MulEquiv.subgroupCongr hmap)).trans
        (Subgroup.subgroupOfEquivOfLe (s16t_l4_lbar_le_mbar hS))
    haveI : IsSimpleGroup ↥(lBar V₀ V hV L) := s16t_l4_lbar_simple hS
    have hnotcomm : ¬ IsMulCommutative ↥(lBar V₀ V hV L) := by
      intro hc
      haveI : IsMulCommutative ↥(lBar V₀ V hV L) := hc
      have hp : (Nat.card ↥(lBar V₀ V hV L)).Prime :=
        (Group.is_simple_iff_prime_card).mp inferInstance
      rw [s16t_l4_card_lbar hS] at hp
      exact (by norm_num : ¬ Nat.Prime 20160) hp
    have hqL : CFSG.Open.IsQuasisimple ↥(lBar V₀ V hV L) := by
      have hperf : Group.IsPerfect ↥(lBar V₀ V hV L) :=
        TauCeti.IsSimpleGroup.isPerfect_of_not_isMulCommutative hnotcomm
      have hcenter : Subgroup.center ↥(lBar V₀ V hV L) = ⊥ :=
        TauCeti.IsSimpleGroup.center_eq_bot_of_not_isMulCommutative hnotcomm
      refine ⟨hperf.commutator_eq_top, ?_⟩
      let e' : ↥(lBar V₀ V hV L) ⧸ Subgroup.center ↥(lBar V₀ V hV L) ≃* ↥(lBar V₀ V hV L) :=
        (QuotientGroup.quotientMulEquivOfEq hcenter).trans QuotientGroup.quotientBot
      exact e'.isSimpleGroup
    exact CFSG.Open.IsQuasisimple.of_mulEquiv eB hqL
  exact le_antisymm (sSup_le fun _ hK => hK.1)
    (le_sSup ⟨le_rfl, CFSG.Open.IsSubnormal.refl B, hqB⟩)

theorem s16t_l4_apply_r119 (h127 : R127 D) (h119 : F11.R119 D) (hS : S16tL4Setting D V₀ V L hV) :
    ∃ X Y : Subgroup G, F11.CTilde D.M V₀ V ≤ X ∧ X ≤ D.M ∧ (X.subgroupOf D.M).Normal ∧
      barSub V₀ V hV X = lBar V₀ V hV L ∧ Y ≤ X ∧ ⁅Y, Y⁆ = Y ∧ F11.O2E Y = Y ∧
      X ≤ normalizer (Y : Set G) ∧ Y ⊓ F11.CTilde D.M V₀ V ≤ OInf Y ∧
      barSub V₀ V hV Y = lBar V₀ V hV L := by
  have hMs : D.M ≤ stabTil V₀ V :=
    le_stabTil hS.counterex.setting.hyp151.hyp125.pairFacts.le_normalizer
      hS.counterex.setting.hyp151.hyp125.pairFacts.le_normalizer₀
  obtain ⟨X, hCX, hXM, hXN, hbarX⟩ := s16t_l4_exists_X hS
  let inst₀ : ((F11.CTilde D.M V₀ V).subgroupOf D.M).Normal := s15_Three_cTilde_normal hV hMs
  haveI := inst₀
  have hlayerim : rankThreeLayer (F11.barImage11 D.M V₀ V X) = F11.barImage11 D.M V₀ V X :=
    s16t_l4_layer_barImage hS hXM hbarX
  obtain ⟨Y, hY, -⟩ :=
    h119 V₀ V (Hyp125.hyp11 h127 hS.counterex.setting.hyp151.hyp125) X hCX hXM hlayerim
  have hY_le : Y ≤ D.M := hY.1.trans hXM
  have hYbar : F11.barImage11 D.M V₀ V Y = F11.barImage11 D.M V₀ V X := hY.2.2.2.2.2
  obtain ⟨e, he⟩ := s15_Three_barImage_equiv (D := D) (V₀ := V₀) (V := V) hV hMs
  have hbarY : barSub V₀ V hV Y = lBar V₀ V hV L := by
    have hsub : (barSub V₀ V hV Y).subgroupOf (Mbar D.M V₀ V hV) =
        (barSub V₀ V hV X).subgroupOf (Mbar D.M V₀ V hV) := by
      rw [← he Y hY_le, ← he X hXM, hYbar]
    have h2 := congrArg (Subgroup.map (Subgroup.subtype (Mbar D.M V₀ V hV))) hsub
    simp only [Subgroup.subgroupOf_map_subtype] at h2
    rw [inf_eq_left.2 (barSub_mono V₀ V hV hY_le),
      inf_eq_left.2 (barSub_mono V₀ V hV hXM), hbarX] at h2
    exact h2
  exact ⟨X, Y, hCX, hXM, hXN, hbarX, hY.1, hY.2.1, hY.2.2.1, hY.2.2.2.1,
    hY.2.2.2.2.1, hbarY⟩

private theorem s16t_l4_isAlt_quot (hS : S16tL4Setting D V₀ V L hV) {Y : Subgroup G} (hYM : Y ≤ D.M)
    (hbarY : barSub V₀ V hV Y = lBar V₀ V hV L)
    [((Y ⊓ F11.CTilde D.M V₀ V).subgroupOf Y).Normal] :
    IsAlt (↥Y ⧸ (Y ⊓ F11.CTilde D.M V₀ V).subgroupOf Y) 8 := by
  obtain ⟨φ, hφ, hker⟩ := s16t_l4_exists_hom_barSub (hV := hV) (s16t_l4_le_stabTil hS) hYM
  obtain ⟨e⟩ := s16t_l4_lbar_isAlt hS
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    ((QuotientGroup.quotientKerEquivOfSurjective φ hφ).trans
      ((MulEquiv.subgroupCongr hbarY).trans e))⟩

theorem s16t_l4_exists_Y (h127 : R127 D) (h119 : F11.R119 D) (hS : S16tL4Setting D V₀ V L hV) :
    ∃ Y : Subgroup G, S16tL4Pack D V₀ V L hV Y := by
  obtain ⟨X, Y, hCX, hXM, hXN, hbarX, hYX, hYperf, hO2E, hXY, hYC, hbarY⟩ :=
    s16t_l4_apply_r119 h127 h119 hS
  have hMs : D.M ≤ stabTil V₀ V := s16t_l4_le_stabTil hS
  have hMn : D.M ≤ normalizer (V : Set G) := hMs.trans (stabTil_le_normalizer V₀ V)
  have hYM : Y ≤ D.M := hYX.trans hXM
  obtain ⟨φY, -, hkerY⟩ := s16t_l4_exists_hom_barSub (hV := hV) hMs hYM
  haveI hnormY : ((Y ⊓ F11.CTilde D.M V₀ V).subgroupOf Y).Normal := hkerY ▸ φY.normal_ker
  have hker : Y ⊓ F11.CTilde D.M V₀ V = pCoreOf 2 Y :=
    close16_ker_eq_pcore hYperf hO2E hYC (s16t_l4_isAlt_quot hS hYM hbarY)
  have hY2 : IsPGroup 2 ↥(Y ⊓ F11.CTilde D.M V₀ V) := by
    rw [hker]
    exact CFSG.pCore_isPGroup.map _
  have hXYC : X = Y ⊔ F11.CTilde D.M V₀ V := by
    refine le_antisymm (fun x hx => ?_) (sup_le hYX hCX)
    have hxs : x ∈ stabTil V₀ V := hMs (hXM hx)
    have hxbar := actTil_mem_barSub V₀ V hV hx hxs
    rw [hbarX, ← hbarY] at hxbar
    obtain ⟨g, hgY, hg⟩ := (mem_barSub V₀ V hV Y _).1 hxbar
    have hxc : x * (g : G)⁻¹ ∈ F11.CTilde D.M V₀ V := by
      rw [mem_cTilde_iff hV hMn]
      refine ⟨D.M.mul_mem (hXM hx) (D.M.inv_mem (hYM hgY)),
        (stabTil V₀ V).mul_mem hxs ((stabTil V₀ V).inv_mem g.2), ?_⟩
      have h1 : (⟨x * (g : G)⁻¹, (stabTil V₀ V).mul_mem hxs ((stabTil V₀ V).inv_mem g.2)⟩ :
          ↥(stabTil V₀ V)) = ⟨x, hxs⟩ * g⁻¹ := rfl
      rw [h1, map_mul, map_inv, hg, mul_inv_cancel]
    have hmem := Subgroup.mul_mem_sup hxc hgY
    rw [inv_mul_cancel_right, sup_comm] at hmem
    exact hmem
  obtain ⟨φX, hφX, hkerX⟩ := s16t_l4_exists_hom_barSub (hV := hV) hMs hXM
  haveI hsimple : IsSimpleGroup ↥(barSub V₀ V hV X) := by
    rw [hbarX]; exact s16t_l4_lbar_simple hS
  have hnc : ¬ IsMulCommutative ↥(barSub V₀ V hV X) := by
    rw [hbarX]; exact s16t_l4_lbar_not_commutative hS
  obtain ⟨hXC, hXab⟩ := close16_simple_of_hom hCX hnc φX hφX
    (by rw [hkerX, inf_eq_right.2 hCX])
  exact ⟨Y, hYM, close16_normal_of_cover (s15_Three_cTilde_normal hV hMs) hXM hXN hCX hYX hXY
    hYperf hXYC hY2 hXC hXab, hYperf, hbarY, hker⟩

theorem s16t_l4_le_centralizer_v0 (hS : S16tL4Setting D V₀ V L hV) {Y : Subgroup G}
    (hY : S16tL4Pack D V₀ V L hV Y) : Y ≤ centralizer (V₀ : Set G) :=
  ElevenNine.le_centralizer_of_perfect_of_card_le_four hY.perfect
    (hY.le.trans hS.counterex.setting.hyp151.hyp125.pairFacts.le_normalizer₀)
    (c23_card_v0_le_four D hS.counterex.setting.hyp16)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
