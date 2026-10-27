module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1WCCover
public import CFSG.LocalAnalysis.ComponentClassification.SolAltLitSol78
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2EighteenCfg2Simple
import CFSG.LocalAnalysis.GLTheoremA.CatA.SFM12Block
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1677ThreeDefs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

private theorem s168e3_cov_quasi {V₀ V : Subgroup G} {hV : IsElemAbelian 2 V}
    {Kb : Subgroup (MulAut (Vtil V₀ V hV))}
    (hKs : IsSimpleGroup ↥Kb) (hKnc : ¬ IsMulCommutative ↥Kb) :
    CFSG.Open.IsQuasisimple ↥Kb := by
  haveI : IsSimpleGroup ↥Kb := hKs
  have hperf : Group.IsPerfect ↥Kb :=
    TauCeti.IsSimpleGroup.isPerfect_of_not_isMulCommutative hKnc
  have hcenter : Subgroup.center ↥Kb = ⊥ :=
    TauCeti.IsSimpleGroup.center_eq_bot_of_not_isMulCommutative hKnc
  refine ⟨hperf.commutator_eq_top, ?_⟩
  let e' : ↥Kb ⧸ Subgroup.center ↥Kb ≃* ↥Kb :=
    (QuotientGroup.quotientMulEquivOfEq hcenter).trans QuotientGroup.quotientBot
  exact e'.isSimpleGroup

private theorem s168e3_cov_alt_mult
    (hSchur : CFSG.ComponentClassification.SolAltLit.SchurAlternatingMultiplierInput)
    {X : Type} [Group X] {n : ℕ} (hX : UC22.IsAlt X n) (hn : 8 ≤ n) :
    ∃ k : ℕ, Nat.card (CFSG.Open.griessHopfMultiplier X) = 2 ^ k := by
  obtain ⟨e⟩ := hX
  have hcard : Nat.card (CFSG.RankThree.PerfectCover.hopfMultiplier
      (alternatingGroup (Fin n))) = 2 := by
    have h := (hSchur n (by omega)).2
    rwa [if_neg (by omega : ¬ (n = 6 ∨ n = 7))] at h
  refine ⟨1, ?_⟩
  rw [Nat.card_congr (CFSG.LieType.Steinberg.CentralExt.griessHopfMultiplierCongr e).toEquiv,
    Nat.card_congr (CFSG.RankThree.PerfectCover.hopfMultiplierEquivGriess
      (alternatingGroup (Fin n))).toEquiv]
  simpa using hcard

private theorem s168e3_cov_preBarSub_mono {M V₀ V : Subgroup G} {hV : IsElemAbelian 2 V}
    {Xbar Ybar : Subgroup (MulAut (Vtil V₀ V hV))} (h : Xbar ≤ Ybar) :
    preBarSub M V₀ V hV Xbar ≤ preBarSub M V₀ V hV Ybar := by
  unfold preBarSub
  exact inf_le_inf_left _ (Subgroup.map_mono (Subgroup.comap_mono h))

private theorem s168e3_cov_layer_barImage {D : Data G} {V₀ V : Subgroup G} {hV : IsElemAbelian 2 V}
    {X : Subgroup G} {Kb : Subgroup (MulAut (Vtil V₀ V hV))}
    (hMs : D.M ≤ stabTil V₀ V) (hKM : Kb ≤ Mbar D.M V₀ V hV) (hXM : X ≤ D.M)
    (hbar : barSub V₀ V hV X = Kb) (hKq : CFSG.Open.IsQuasisimple ↥Kb)
    [((F11.CTilde D.M V₀ V).subgroupOf D.M).Normal] :
    rankThreeLayer (F11.barImage11 D.M V₀ V X) = F11.barImage11 D.M V₀ V X := by
  set B : Subgroup (F11.MBar11 D.M V₀ V) := F11.barImage11 D.M V₀ V X with hBdef
  have hqB : CFSG.Open.IsQuasisimple ↥B := by
    obtain ⟨e, he⟩ := s15_Three_barImage_equiv (D := D) (V₀ := V₀) (V := V) hV hMs
    have hmap : B.map e.toMonoidHom = Kb.subgroupOf (Mbar D.M V₀ V hV) := by
      rw [hBdef, he X hXM, hbar]
    let eB : ↥B ≃* ↥Kb :=
      ((Subgroup.equivMapOfInjective B e.toMonoidHom e.injective).trans
        (MulEquiv.subgroupCongr hmap)).trans
        (Subgroup.subgroupOfEquivOfLe hKM)
    exact CFSG.Open.IsQuasisimple.of_mulEquiv eB hKq
  exact le_antisymm (sSup_le fun _ hK => hK.1)
    (le_sSup ⟨le_rfl, CFSG.Open.IsSubnormal.refl B, hqB⟩)

private theorem s168e3_cov_preBarSub_conj_mem {D : Data G} {V₀ V : Subgroup G}
    {hV : IsElemAbelian 2 V}
    (hMs : D.M ≤ stabTil V₀ V) (Xbar : Subgroup (MulAut (Vtil V₀ V hV)))
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

private theorem s168e3_cov_layer_top_of_O2E_eq {Y : Subgroup G} (hYE : F11.O2E Y = Y) :
    CFSG.Open.rankThreeLayer (⊤ : Subgroup (Bar2 Y)) = ⊤ := by
  have hπ : Function.Surjective (QuotientGroup.mk' (CFSG.pCore 2 ↥Y)) :=
    QuotientGroup.mk'_surjective _
  have hTop : (⊤ : Subgroup ↥Y).map Y.subtype = Y := by
    rw [Subgroup.map_top, Subgroup.range_subtype]
  have hcomap : (CFSG.Open.rankThreeLayer (⊤ : Subgroup (Bar2 Y))).comap
      (QuotientGroup.mk' (CFSG.pCore 2 ↥Y)) = ⊤ := by
    apply Subgroup.map_injective Y.subtype_injective
    change F11.O2E Y = (⊤ : Subgroup ↥Y).map Y.subtype
    rw [hYE, hTop]
  have h := Subgroup.map_comap_eq_self_of_surjective hπ
    (CFSG.Open.rankThreeLayer (⊤ : Subgroup (Bar2 Y)))
  rw [hcomap, Subgroup.map_top_of_surjective _ hπ] at h
  exact h.symm

private theorem s168e3_cov_of_simple {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (h119 : F11.R119 D) (h127 : R127 D) (hset : Setting16 D V₀ V L)
    {Kb : Subgroup (MulAut (Vtil V₀ V hV))} (hKM : Kb ≤ Mbar D.M V₀ V hV)
    (hKN : (Kb.subgroupOf (Mbar D.M V₀ V hV)).Normal) (hKs : IsSimpleGroup ↥Kb)
    (hKnc : ¬ IsMulCommutative ↥Kb)
    (hmult : ∃ k : ℕ, Nat.card (CFSG.Open.griessHopfMultiplier ↥Kb) = 2 ^ k) :
    ∃ Y : Subgroup G, Y ≤ D.M ∧ (Y.subgroupOf D.M).Normal ∧ barSub V₀ V hV Y = Kb ∧
      IsPGroup 2 ↥(Y ⊓ F11.CTilde D.M V₀ V) := by
  haveI : IsSimpleGroup ↥Kb := hKs
  have hKq : CFSG.Open.IsQuasisimple ↥Kb := s168e3_cov_quasi hKs hKnc
  have hcenterK : Subgroup.center ↥Kb = ⊥ :=
    TauCeti.IsSimpleGroup.center_eq_bot_of_not_isMulCommutative hKnc
  have hzK : Odd (Nat.card (Subgroup.center ↥Kb)) := by
    rw [hcenterK, Subgroup.card_bot]
    exact odd_one
  have hMs : D.M ≤ stabTil V₀ V := s16g_le_stabTil hset
  have hMn : D.M ≤ normalizer (V : Set G) := hMs.trans (stabTil_le_normalizer V₀ V)
  set X : Subgroup G := preBarSub D.M V₀ V hV Kb with hXdef
  have hX_le : X ≤ D.M := by rw [hXdef]; exact inf_le_left
  have hCX : F11.CTilde D.M V₀ V ≤ X := by
    rw [hXdef, cTilde_eq_preBarSub_bot hV hMn]
    exact s168e3_cov_preBarSub_mono bot_le
  have hbarX : barSub V₀ V hV X = Kb := by
    rw [hXdef, barSub_preBarSub]
    exact inf_eq_left.2 hKM
  haveI : ((F11.CTilde D.M V₀ V).subgroupOf D.M).Normal :=
    s15_Three_cTilde_normal hV hMs
  have hlayerim : rankThreeLayer (F11.barImage11 D.M V₀ V X) = F11.barImage11 D.M V₀ V X :=
    s168e3_cov_layer_barImage hMs hKM hX_le hbarX hKq
  have hXnormal : (X.subgroupOf D.M).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hX_le]
    intro m hm
    rw [Subgroup.mem_normalizer_iff]
    intro x
    change x ∈ preBarSub D.M V₀ V hV Kb ↔ m * x * m⁻¹ ∈ preBarSub D.M V₀ V hV Kb
    exact s168e3_cov_preBarSub_conj_mem hMs Kb hKM hKN hm
  obtain ⟨Y, hY, -⟩ :=
    h119 V₀ V (Hyp125.hyp11 h127 hset.hyp16.hyp125) X hCX hX_le hlayerim
  have hY_le : Y ≤ D.M := hY.1.trans hX_le
  obtain ⟨e, he⟩ := s15_Three_barImage_equiv (D := D) (V₀ := V₀) (V := V) hV hMs
  have hbarY : barSub V₀ V hV Y = Kb := by
    have hsub : (barSub V₀ V hV Y).subgroupOf (Mbar D.M V₀ V hV) =
        (barSub V₀ V hV X).subgroupOf (Mbar D.M V₀ V hV) := by
      rw [← he Y hY_le, ← he X hX_le, hY.2.2.2.2.2]
    have h2 := congrArg (Subgroup.map (Subgroup.subtype (Mbar D.M V₀ V hV))) hsub
    simp only [Subgroup.subgroupOf_map_subtype] at h2
    rw [inf_eq_left.2 (barSub_mono V₀ V hV hY_le),
      inf_eq_left.2 (barSub_mono V₀ V hV hX_le), hbarX] at h2
    exact h2
  have hYs : Y ≤ stabTil V₀ V := hY_le.trans hMs
  let φ : ↥Y →* ↥(barSub V₀ V hV Y) :=
    MonoidHom.codRestrict ((actTil V₀ V hV).comp (Subgroup.inclusion hYs)) (barSub V₀ V hV Y)
      (fun g => actTil_mem_barSub V₀ V hV g.2 (hYs g.2))
  have hφ : Function.Surjective φ := by
    rintro ⟨ψ, hψ⟩
    obtain ⟨g, hg, rfl⟩ := (mem_barSub V₀ V hV Y ψ).1 hψ
    exact ⟨⟨(g : G), hg⟩, rfl⟩
  let N : Subgroup ↥Y := φ.ker
  have hNker : N = (Y ⊓ F11.CTilde D.M V₀ V).subgroupOf Y := by
    ext g
    rw [show N = φ.ker from rfl, MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf,
      mem_cTilde_iff hV hMn]
    have hgY : (g : G) ∈ Y := g.2
    constructor
    · intro h1
      exact ⟨hgY, hY_le hgY, hYs hgY, congrArg Subtype.val h1⟩
    · rintro ⟨-, -, h, h1⟩
      exact Subtype.ext h1
  haveI : N.Normal := MonoidHom.normal_ker φ
  have hNsolv : Group.IsSolvable ↥N := by
    rw [hNker]
    have hle : (Y ⊓ F11.CTilde D.M V₀ V).subgroupOf Y ≤ CFSG.solvableRadical ↥Y := by
      intro x hx
      obtain ⟨z, hz, hzx⟩ := hY.2.2.2.2.1 (Subgroup.mem_subgroupOf.mp hx)
      have hzx' : z = x := Subtype.ext hzx
      exact hzx' ▸ hz
    haveI := CFSG.SignalizerFunctorTheorem.Nonsolvable.isSolvable_solvableRadical (G := ↥Y)
    exact Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hle)
      (Subgroup.inclusion_injective hle)
  have hperfY : Group.IsPerfect ↥Y := Subgroup.isPerfect_iff.mpr hY.2.1
  have hlayerY : CFSG.Open.rankThreeLayer (⊤ : Subgroup (↥Y ⧸ CFSG.pCore 2 ↥Y)) = ⊤ :=
    s168e3_cov_layer_top_of_O2E_eq hY.2.2.1
  let eQ : ↥Y ⧸ N ≃* ↥Kb :=
    (QuotientGroup.quotientKerEquivOfSurjective φ hφ).trans (MulEquiv.subgroupCongr hbarY)
  have hN2 : IsPGroup 2 ↥N :=
    s16w_isPGroup_ker_of_two_multiplier hperfY hlayerY N hNsolv eQ hKq hzK hmult
  have hY2 : IsPGroup 2 ↥(Y ⊓ F11.CTilde D.M V₀ V) := by
    have hN2' : IsPGroup 2 ↥((Y ⊓ F11.CTilde D.M V₀ V).subgroupOf Y) := hNker ▸ hN2
    exact hN2'.of_equiv
      (Subgroup.subgroupOfEquivOfLe (inf_le_left : Y ⊓ F11.CTilde D.M V₀ V ≤ Y))
  have hXYC : X = Y ⊔ F11.CTilde D.M V₀ V := by
    refine le_antisymm (fun x hx => ?_) (sup_le hY.1 hCX)
    have hxs : x ∈ stabTil V₀ V := hMs (hX_le hx)
    have hxbar := actTil_mem_barSub V₀ V hV hx hxs
    rw [hbarX, ← hbarY] at hxbar
    obtain ⟨g, hgY, hg⟩ := (mem_barSub V₀ V hV Y _).1 hxbar
    have hxc : x * (g : G)⁻¹ ∈ F11.CTilde D.M V₀ V := by
      rw [mem_cTilde_iff hV hMn]
      refine ⟨D.M.mul_mem (hX_le hx) (D.M.inv_mem (hY_le hgY)),
        (stabTil V₀ V).mul_mem hxs ((stabTil V₀ V).inv_mem g.2), ?_⟩
      have h1 : (⟨x * (g : G)⁻¹, (stabTil V₀ V).mul_mem hxs ((stabTil V₀ V).inv_mem g.2)⟩ :
          ↥(stabTil V₀ V)) = ⟨x, hxs⟩ * g⁻¹ := rfl
      rw [h1, map_mul, map_inv, hg, mul_inv_cancel]
    have hmem := Subgroup.mul_mem_sup hxc hgY
    rw [inv_mul_cancel_right, sup_comm] at hmem
    exact hmem
  have hXs : X ≤ stabTil V₀ V := hX_le.trans hMs
  let φX : ↥X →* ↥(barSub V₀ V hV X) :=
    MonoidHom.codRestrict ((actTil V₀ V hV).comp (Subgroup.inclusion hXs)) (barSub V₀ V hV X)
      (fun g => actTil_mem_barSub V₀ V hV g.2 (hXs g.2))
  have hφX : Function.Surjective φX := by
    rintro ⟨ψ, hψ⟩
    obtain ⟨g, hg, rfl⟩ := (mem_barSub V₀ V hV X ψ).1 hψ
    exact ⟨⟨(g : G), hg⟩, rfl⟩
  have hkerX : φX.ker = (X ⊓ F11.CTilde D.M V₀ V).subgroupOf X := by
    ext g
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf, mem_cTilde_iff hV hMn]
    have hgX : (g : G) ∈ X := g.2
    constructor
    · intro h1
      exact ⟨hgX, hX_le hgX, hXs hgX, congrArg Subtype.val h1⟩
    · rintro ⟨-, -, h, h1⟩
      exact Subtype.ext h1
  haveI : IsSimpleGroup ↥(barSub V₀ V hV X) := by rw [hbarX]; exact hKs
  have hnc : ¬ IsMulCommutative ↥(barSub V₀ V hV X) := by rw [hbarX]; exact hKnc
  obtain ⟨hXC, hXab⟩ := close16_simple_of_hom hCX hnc φX hφX
    (by rw [hkerX, inf_eq_right.2 hCX])
  exact ⟨Y, hY_le, close16_normal_of_cover (s15_Three_cTilde_normal hV hMs) hX_le hXnormal hCX
    hY.1 hY.2.2.2.1 hY.2.1 hXYC hY2 hXC hXab, hbarY, hY2⟩

theorem s168e3_cover_alt {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV)
    (hSchur : CFSG.ComponentClassification.SolAltLit.SchurAlternatingMultiplierInput)
    (hs : s15 D.M V₀ V hV L = 1) {n : ℕ} (hn8 : 8 ≤ n)
    (hA : UC22.IsAlt ↥(lBar V₀ V hV L) n) :
    ∃ Y : Subgroup G, Y ≤ D.M ∧ (Y.subgroupOf D.M).Normal ∧
      barSub V₀ V hV Y = lBar V₀ V hV L ∧ IsPGroup 2 ↥(Y ⊓ F11.CTilde D.M V₀ V) := by
  have hsimple : IsSimpleGroup ↥(lBar V₀ V hV L) :=
    s16c167_cfg2_simple_alt (by omega : 5 ≤ n) hA
  have hnc : ¬ IsMulCommutative ↥(lBar V₀ V hV L) := by
    intro hc
    obtain ⟨e⟩ := hA
    obtain ⟨a, b, hab⟩ := CFSG.ComponentClassification.SolAltLit.alternating_nonabelian
      (by omega : 4 ≤ n)
    refine hab ?_
    have h := hc.is_comm.comm (e.symm a) (e.symm b)
    calc a * b = e (e.symm a) * e (e.symm b) := by simp
      _ = e (e.symm a * e.symm b) := by rw [map_mul]
      _ = e (e.symm b * e.symm a) := by rw [h]
      _ = e (e.symm b) * e (e.symm a) := by rw [map_mul]
      _ = b * a := by simp
  have hmult : ∃ k : ℕ, Nat.card (CFSG.Open.griessHopfMultiplier ↥(lBar V₀ V hV L)) = 2 ^ k :=
    s168e3_cov_alt_mult hSchur hA hn8
  have hquasi : CFSG.Open.IsQuasisimple ↥(lBar V₀ V hV L) := s168e3_cov_quasi hsimple hnc
  have hLM : lBar V₀ V hV L ≤ Mbar D.M V₀ V hV := barSub_mono V₀ V hV c.setting.hyp151.le
  have hnorm : Mbar D.M V₀ V hV ≤ Subgroup.normalizer
      (lBar V₀ V hV L : Set (MulAut (Vtil V₀ V hV))) := by
    intro g hg
    by_contra hgn
    obtain ⟨t, -, -, -, -, -, hconj, -⟩ := c.conc
    have h2 := (hconj g hg hgn).2
    have hcomm_top : commSub ⊤ (lBar V₀ V hV L) = ⊤ :=
      wTil_eq_top_of_case163_2 c.conc hs
    rw [hcomm_top] at h2
    have hfix := commSub_eq_bot_iff.1 h2
    have hbot : (lBar V₀ V hV L).map (MulAut.conj g).toMonoidHom = ⊥ := by
      rw [Subgroup.eq_bot_iff_forall]
      intro x hx
      exact MulEquiv.ext fun v => hfix (Subgroup.mem_top v) x hx
    have hbot' := (Subgroup.map_eq_bot_iff_of_injective (lBar V₀ V hV L)
      (f := (MulAut.conj g).toMonoidHom) (MulEquiv.injective (MulAut.conj g))).1 hbot
    refine CFSG.LocalAnalysis.GLTheoremA.SFM12.not_all_commute_of_quasisimple hquasi
      fun a b => ?_
    have ha : (a : MulAut (Vtil V₀ V hV)) = 1 := Subgroup.mem_bot.1 (hbot' ▸ a.2)
    exact Subtype.ext (by rw [Subgroup.coe_mul, Subgroup.coe_mul, ha, one_mul, mul_one])
  have hKN : (lBar V₀ V hV L).subgroupOf (Mbar D.M V₀ V hV) |>.Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLM).2 hnorm
  exact s168e3_cov_of_simple c.std.h119 c.std.h127 c.setting hLM hKN hsimple hnc hmult

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
