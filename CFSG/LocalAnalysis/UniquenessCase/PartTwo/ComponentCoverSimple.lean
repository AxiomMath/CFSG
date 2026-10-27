module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenThreeK2
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenSeven
public import CFSG.Assembly.OddCoreElimination.CentralizerContainmentKernel

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem s1715six_preBarSub_conj_mem {D : Data G} {V₀ V : Subgroup G}
    {hV : IsElemAbelian 2 V} (hMs : D.M ≤ stabTil V₀ V)
    (Xbar : Subgroup (MulAut (Vtil V₀ V hV)))
    (hXbar_le : Xbar ≤ Mbar D.M V₀ V hV)
    (hXbarN : (Xbar.subgroupOf (Mbar D.M V₀ V hV)).Normal) {m x : G} (hm : m ∈ D.M) :
    x ∈ preBarSub D.M V₀ V hV Xbar ↔
      m * x * m⁻¹ ∈ preBarSub D.M V₀ V hV Xbar := by
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

theorem s1715six_layer_barImage {D : Data G} {V : Subgroup G} (hV : IsElemAbelian 2 V)
    [((F11.CTilde D.M ⊥ V).subgroupOf D.M).Normal] (hMs : D.M ≤ stabTil ⊥ V)
    {C : Subgroup (MulAut (Vtil ⊥ V hV))} (hCle : C ≤ Mbar D.M ⊥ V hV)
    (hqC : CFSG.Open.IsQuasisimple ↥C) {X : Subgroup G} (hXM : X ≤ D.M)
    (hbar : barSub ⊥ V hV X = C) :
    rankThreeLayer (F11.barImage11 D.M ⊥ V X) = F11.barImage11 D.M ⊥ V X := by
  set B : Subgroup (F11.MBar11 D.M ⊥ V) := F11.barImage11 D.M ⊥ V X with hBdef
  have hqB : CFSG.Open.IsQuasisimple ↥B := by
    obtain ⟨e, he⟩ := s15_Three_barImage_equiv (D := D) (V₀ := ⊥) (V := V) hV hMs
    have hmap : B.map e.toMonoidHom = C.subgroupOf (Mbar D.M ⊥ V hV) := by
      rw [hBdef, he X hXM, hbar]
    let eB : ↥B ≃* ↥C :=
      ((Subgroup.equivMapOfInjective B e.toMonoidHom e.injective).trans
        (MulEquiv.subgroupCongr hmap)).trans
        (Subgroup.subgroupOfEquivOfLe hCle)
    exact CFSG.Open.IsQuasisimple.of_mulEquiv eB hqC
  exact le_antisymm (sSup_le fun _ hK => hK.1)
    (le_sSup ⟨le_rfl, CFSG.Open.IsSubnormal.refl B, hqB⟩)

theorem s1715six_barLift_exists {V₀ V : Subgroup G} (hV : IsElemAbelian 2 V) {Y : Subgroup G}
    (hY : Y ≤ stabTil V₀ V) (h2 : barSub V₀ V hV (pCoreOf 2 Y) = ⊥) :
    ∃ ψ : Bar2 Y →* MulAut (Vtil V₀ V hV),
      ∀ y : ↥Y, ψ (QuotientGroup.mk y) = actTil V₀ V hV ⟨y, hY y.2⟩ := by
  let f : ↥Y →* MulAut (Vtil V₀ V hV) := (actTil V₀ V hV).comp (Subgroup.inclusion hY)
  have hker : CFSG.pCore 2 ↥Y ≤ f.ker := by
    intro x hx
    rw [MonoidHom.mem_ker]
    have hxP : (x : G) ∈ pCoreOf 2 Y := ⟨x, hx, rfl⟩
    have h1 : actTil V₀ V hV ⟨(x : G), hY x.2⟩ ∈ barSub V₀ V hV (pCoreOf 2 Y) :=
      actTil_mem_barSub V₀ V hV hxP (hY x.2)
    rw [h2, Subgroup.mem_bot] at h1
    exact h1
  refine ⟨QuotientGroup.lift (CFSG.pCore 2 ↥Y) f hker, ?_⟩
  intro y
  rfl

theorem s1715six_barSub_comap_map {V₀ V : Subgroup G} (hV : IsElemAbelian 2 V) {Y : Subgroup G}
    (hY : Y ≤ stabTil V₀ V) (ψ : Bar2 Y →* MulAut (Vtil V₀ V hV))
    (hψ : ∀ y : ↥Y, ψ (QuotientGroup.mk y) = actTil V₀ V hV ⟨y, hY y.2⟩)
    (C : Subgroup (Bar2 Y)) :
    barSub V₀ V hV ((C.comap (QuotientGroup.mk' (CFSG.pCore 2 ↥Y))).map Y.subtype) =
      C.map ψ := by
  ext φ
  constructor
  · intro hφ
    obtain ⟨g, hg, rfl⟩ := (mem_barSub V₀ V hV _ φ).1 hφ
    obtain ⟨y, hyC, hyg⟩ := Subgroup.mem_map.1 hg
    refine Subgroup.mem_map.2 ⟨QuotientGroup.mk' (CFSG.pCore 2 ↥Y) y, hyC, ?_⟩
    change ψ (QuotientGroup.mk y) = actTil V₀ V hV g
    rw [hψ y]
    exact congrArg (actTil V₀ V hV) (Subtype.ext (by
      change y.1 = (g : G)
      exact hyg))
  · rintro ⟨c, hc, rfl⟩
    obtain ⟨y, hy⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥Y) c
    refine (mem_barSub V₀ V hV _ (ψ c)).2 ⟨⟨(y : G), hY y.2⟩, ?_, ?_⟩
    · refine Subgroup.mem_map.2 ⟨y, ?_, rfl⟩
      rw [Subgroup.mem_comap, hy]
      exact hc
    · change actTil V₀ V hV ⟨(y : G), hY y.2⟩ = ψ c
      rw [← hy]
      change actTil V₀ V hV ⟨(y : G), hY y.2⟩ = ψ (QuotientGroup.mk y)
      rw [hψ y]

theorem s1715six_layer_top_of_O2E_eq {Y : Subgroup G} (hYE : F11.O2E Y = Y) :
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

theorem exists_calC_cover_of_simple_normal (D : Data G) (h127 : R127 D) (h119 : F11.R119 D)
    {V : Subgroup G} (h : Hyp125 D ⊥ V)
    {C : Subgroup (MulAut (Vtil ⊥ V h.isElemAbelian))}
    (hCle : C ≤ Mbar D.M ⊥ V h.isElemAbelian)
    (hCn : (C.subgroupOf (Mbar D.M ⊥ V h.isElemAbelian)).Normal)
    (hCs : IsSimpleGroup ↥C) (hCna : ¬ IsMulCommutative ↥C) :
    ∃ K : Subgroup G, K ∈ calC D.M ∧ barSub ⊥ V h.isElemAbelian K = C ∧
      Nonempty ((Bar2 K ⧸ Subgroup.center (Bar2 K)) ≃* ↥C) := by
  have hV : IsElemAbelian 2 V := h.isElemAbelian
  have hMs : D.M ≤ stabTil ⊥ V :=
    le_stabTil h.pairFacts.le_normalizer h.pairFacts.le_normalizer₀
  have hMnorm : D.M ≤ normalizer (V : Set G) := h.pairFacts.le_normalizer
  have hCT : ((F11.CTilde D.M ⊥ V).subgroupOf D.M).Normal :=
    s15_Three_cTilde_normal hV hMs
  have : IsSimpleGroup ↥C := hCs
  have hZC : Subgroup.center ↥C = ⊥ :=
    TauCeti.IsSimpleGroup.center_eq_bot_of_not_isMulCommutative hCna
  have hqC : CFSG.Open.IsQuasisimple ↥C := by
    have hperf : Group.IsPerfect ↥C :=
      TauCeti.IsSimpleGroup.isPerfect_of_not_isMulCommutative hCna
    refine ⟨hperf.commutator_eq_top, ?_⟩
    let e : ↥C ⧸ Subgroup.center ↥C ≃* ↥C :=
      (QuotientGroup.quotientMulEquivOfEq hZC).trans QuotientGroup.quotientBot
    exact e.isSimpleGroup
  set X : Subgroup G := preBarSub D.M ⊥ V hV C with hXdef
  have hX_le : X ≤ D.M := by rw [hXdef]; exact inf_le_left
  have hCX : F11.CTilde D.M ⊥ V ≤ X := by
    rw [hXdef, cTilde_eq_preBarSub_bot hV hMnorm]
    exact s15_Seven_preBarSub_mono hV bot_le
  have hbarX : barSub ⊥ V hV X = C := by
    rw [hXdef, barSub_preBarSub]
    exact inf_eq_left.2 hCle
  have hXnormal : (X.subgroupOf D.M).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hX_le]
    intro m hm
    rw [Subgroup.mem_normalizer_iff]
    intro x
    change x ∈ preBarSub D.M ⊥ V hV C ↔ m * x * m⁻¹ ∈ preBarSub D.M ⊥ V hV C
    exact s1715six_preBarSub_conj_mem hMs C hCle hCn hm
  have hlayer : rankThreeLayer (F11.barImage11 D.M ⊥ V X) = F11.barImage11 D.M ⊥ V X :=
    s1715six_layer_barImage hV hMs hCle hqC hX_le hbarX
  obtain ⟨Y, hY, -⟩ := h119 ⊥ V (Hyp125.hyp11 h127 h) X hCX hX_le hlayer
  have hYX : Y ≤ X := hY.1
  have hYperf : ⁅Y, Y⁆ = Y := hY.2.1
  have hYE : F11.O2E Y = Y := hY.2.2.1
  have hYN : X ≤ normalizer (Y : Set G) := hY.2.2.2.1
  have hYC : Y ⊓ F11.CTilde D.M ⊥ V ≤ OInf Y := hY.2.2.2.2.1
  have hYbar : F11.barImage11 D.M ⊥ V Y = F11.barImage11 D.M ⊥ V X := hY.2.2.2.2.2
  have hY_le : Y ≤ D.M := hYX.trans hX_le
  have hYXsub : CFSG.Open.IsSubnormal Y X :=
    A3.subnormal_of_normal hYX ((Subgroup.normal_subgroupOf_iff_le_normalizer hYX).mpr hYN)
  have hXMsub : CFSG.Open.IsSubnormal X D.M := A3.subnormal_of_normal hX_le hXnormal
  have hYMsub : CFSG.Open.IsSubnormal Y D.M := A3.subnormal_trans hYXsub hXMsub
  have hbarY : barSub ⊥ V hV Y = C := by
    obtain ⟨e, he⟩ := s15_Three_barImage_equiv (D := D) (V₀ := ⊥) (V := V) hV hMs
    have hsub : (barSub ⊥ V hV Y).subgroupOf (Mbar D.M ⊥ V hV) =
        (barSub ⊥ V hV X).subgroupOf (Mbar D.M ⊥ V hV) := by
      rw [← he Y hY_le, ← he X hX_le, hYbar]
    have h2 := congrArg (Subgroup.map (Subgroup.subtype (Mbar D.M ⊥ V hV))) hsub
    simp only [Subgroup.subgroupOf_map_subtype] at h2
    rw [inf_eq_left.2 (barSub_mono ⊥ V hV hY_le),
      inf_eq_left.2 (barSub_mono ⊥ V hV hX_le), hbarX] at h2
    exact h2
  have hYs : Y ≤ stabTil ⊥ V := hY_le.trans hMs
  have h2 : barSub ⊥ V hV (pCoreOf 2 Y) = ⊥ :=
    TwelveTwentyThree.barSub_pCoreOf_eq_bot_of_isSubnormal hV hYMsub
      (barSub_pCoreOf_eq_bot_of_hyp125 h)
  obtain ⟨ψ, hψ⟩ := s1715six_barLift_exists hV hYs h2
  have hTop : (⊤ : Subgroup ↥Y).map Y.subtype = Y := by
    rw [Subgroup.map_top, Subgroup.range_subtype]
  have hYmap : (⊤ : Subgroup (Bar2 Y)).map ψ = C := by
    have h := s1715six_barSub_comap_map hV hYs ψ hψ ⊤
    rw [Subgroup.comap_top, hTop] at h
    rw [← hbarY]
    exact h.symm
  have hlayer_top : CFSG.Open.rankThreeLayer (⊤ : Subgroup (Bar2 Y)) = ⊤ :=
    s1715six_layer_top_of_O2E_eq hYE
  have hsup : C = ⨆ C' ∈ {C' : Subgroup (Bar2 Y) | CFSG.Open.IsComponentOf C' ⊤},
      C'.map ψ := by
    rw [← hYmap]
    conv_lhs => rw [← hlayer_top]
    rw [CFSG.Open.rankThreeLayer, sSup_eq_iSup]
    simp only [Subgroup.map_iSup]
  have hex : ∃ C' : Subgroup (Bar2 Y), CFSG.Open.IsComponentOf C' ⊤ ∧ C'.map ψ = C := by
    by_contra hcon
    push Not at hcon
    have hbot : ∀ C' : Subgroup (Bar2 Y),
        CFSG.Open.IsComponentOf C' ⊤ → C'.map ψ = ⊥ := by
      intro C' hC'
      by_cases hker : C' ≤ ψ.ker
      · exact (Subgroup.map_eq_bot_iff _).mpr hker
      · have hcomp := CFSG.Quasithin.B15P4.isComponentOf_map_hom ψ hC' hker
        rw [hYmap] at hcomp
        rcases CFSG.Open.IsSubnormal.eq_bot_or_eq_of_isSimpleGroup hcomp.2.1 hCs with
          h0 | htop
        · exact h0
        · exact absurd htop (hcon C' hC')
    have hCbot : C = ⊥ := by
      rw [hsup]
      refine le_bot_iff.1 (iSup_le fun C' => iSup_le fun hC' => ?_)
      rw [hbot C' hC']
    exact (Subgroup.nontrivial_iff_ne_bot C).mp inferInstance hCbot
  obtain ⟨C', hC'comp, hC'map⟩ := hex
  obtain ⟨K, hKY, hKs, hKperf, hKq, -, hKmap⟩ := s15_Three_core_of_component hC'comp
  have hYKstab : Y ≤ stabTil ⊥ V := hYMsub.le.trans hMs
  have hbarK : barSub ⊥ V hV K = C := by
    have h1 : barSub ⊥ V hV K = C'.map ψ := by
      rw [← hKmap]
      ext φ
      constructor
      · intro hφ
        obtain ⟨g, hgK, rfl⟩ := (mem_barSub ⊥ V hV K φ).1 hφ
        have hgY : (g : G) ∈ Y := hKY hgK
        refine Subgroup.mem_map.2
          ⟨QuotientGroup.mk' (CFSG.pCore 2 ↥Y) ⟨(g : G), hgY⟩, ?_, ?_⟩
        · refine Subgroup.mem_map.2 ⟨⟨(g : G), hgY⟩, ?_, rfl⟩
          exact (Subgroup.mem_subgroupOf).2 hgK
        · change ψ (QuotientGroup.mk ⟨(g : G), hgY⟩) = actTil ⊥ V hV g
          rw [hψ ⟨(g : G), hgY⟩]
      · rintro ⟨c, hc, rfl⟩
        obtain ⟨y, hy, hyc⟩ := Subgroup.mem_map.1 hc
        have hyK : (y : G) ∈ K := (Subgroup.mem_subgroupOf).1 hy
        refine (mem_barSub ⊥ V hV K (ψ c)).2
          ⟨⟨(y : G), hYKstab y.2⟩, hyK, ?_⟩
        change actTil ⊥ V hV ⟨(y : G), hYKstab y.2⟩ = ψ c
        rw [← hyc]
        change actTil ⊥ V hV ⟨(y : G), hYKstab y.2⟩ = ψ (QuotientGroup.mk y)
        rw [hψ y]
    calc barSub ⊥ V hV K = C'.map ψ := h1
      _ = C := hC'map
  have hKMsub : CFSG.Open.IsSubnormal K D.M := A3.subnormal_trans hKs hYMsub
  have hKmem : K ∈ calC D.M := ⟨hKMsub, hKperf, hKq⟩
  have hT : CFSG.Open.IsQuasisimple ↥(barSub ⊥ V hV K) := by
    rw [hbarK]
    exact hqC
  have hZ : Subgroup.center ↥(barSub ⊥ V hV K) = ⊥ := by
    rw [hbarK]
    exact hZC
  have hiso : Nonempty ((Bar2 K ⧸ Subgroup.center (Bar2 K)) ≃* ↥C) := by
    obtain ⟨eK⟩ :=
      s15_Three_cover_iso (K₀ := K) hV hMs hKY hKs hYC hYMsub.le h2 hKq hT hZ rfl
    exact ⟨eK.trans (MulEquiv.subgroupCongr hbarK)⟩
  exact ⟨K, hKmem, hbarK, hiso⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
