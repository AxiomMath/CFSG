module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenGlue
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2EighteenModOdd
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Solomon.Coordinator.InndiagProxy
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LocalAnalysis.AGLEmbedding.SeitzEqTwo.DescentE
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefs
public import CFSG.RankThree.PartTwo.KFacts.KS21Mult
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

private theorem s16h_sl28_pbb_wSub_inf_centralizer_eq_preTil (D : Data G) {V L : Subgroup G}
    (h : Setting16 D ⊥ V L) :
    wSub ⊥ V h.hyp151.isElemAbelian L ⊓ centralizer (L : Set G) =
      preTil ⊥ V h.hyp151.isElemAbelian
        (commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L) ⊓
          fixV (lBar ⊥ V h.hyp151.isElemAbelian L)) := by
  have hV := h.hyp151.isElemAbelian
  have hMs : D.M ≤ stabTil ⊥ V :=
    le_stabTil h.hyp151.hyp125.pairFacts.le_normalizer h.hyp151.hyp125.pairFacts.le_normalizer₀
  have hL : L ≤ stabTil ⊥ V := h.hyp151.le.trans hMs
  have hmain : wSub ⊥ V hV L ⊓ centralizer (L : Set G) =
      preTil ⊥ V hV (commSub ⊤ (barSub ⊥ V hV L) ⊓ fixV (barSub ⊥ V hV L)) := by
    refine le_antisymm ?_ ?_
    · intro v hv
      have hvW : v ∈ wSub ⊥ V hV L := (Subgroup.mem_inf.1 hv).1
      have hvC : v ∈ centralizer (L : Set G) := (Subgroup.mem_inf.1 hv).2
      have hvV : v ∈ V := preTil_le ⊥ V hV _ hvW
      rw [mem_preTil_iff_of_mem ⊥ V hV _ hvV, Subgroup.mem_inf]
      constructor
      · unfold wSub wTil at hvW
        rwa [mem_preTil_iff_of_mem ⊥ V hV _ hvV] at hvW
      · rw [← mem_preTil_iff_of_mem ⊥ V hV _ hvV,
          s15_Glue_mem_preTil_fixV_iff ⊥ V L hV hL hvV]
        intro e he
        rw [Subgroup.mem_bot]
        have h := (Subgroup.mem_centralizer_iff.1 hvC) e he
        calc e * v * e⁻¹ * v⁻¹ = (v * e) * e⁻¹ * v⁻¹ := by rw [h]
          _ = 1 := by group
    · intro v hv
      have hvV : v ∈ V := preTil_le ⊥ V hV _ hv
      have hmem : mkTil ⊥ V hV (IntMod.mk hV ⟨v, hvV⟩) ∈
          commSub ⊤ (barSub ⊥ V hV L) ⊓ fixV (barSub ⊥ V hV L) :=
        (mem_preTil_iff_of_mem ⊥ V hV _ hvV).1 hv
      rw [Subgroup.mem_inf] at hmem
      rw [Subgroup.mem_inf]
      constructor
      · unfold wSub wTil
        rw [mem_preTil_iff_of_mem ⊥ V hV _ hvV]
        exact hmem.1
      · rw [Subgroup.mem_centralizer_iff]
        intro l hl
        have hfix : v ∈ preTil ⊥ V hV (fixV (barSub ⊥ V hV L)) := by
          rw [mem_preTil_iff_of_mem ⊥ V hV _ hvV]
          exact hmem.2
        rw [s15_Glue_mem_preTil_fixV_iff ⊥ V L hV hL hvV] at hfix
        have h := hfix l hl
        rw [Subgroup.mem_bot] at h
        have h1 : l * v * l⁻¹ = v := mul_inv_eq_one.1 h
        calc l * v = (l * v * l⁻¹) * l := by group
          _ = v * l := by rw [h1]
  simpa [lBar] using hmain

private theorem s16h_sl28_pbb_mkTil_bot_injective {V : Subgroup G} (hV : IsElemAbelian 2 V) :
    Function.Injective (mkTil (⊥ : Subgroup G) V hV) := by
  rw [← MonoidHom.ker_eq_bot_iff]
  ext x
  rw [MonoidHom.mem_ker, Subgroup.mem_bot]
  constructor
  · intro hx
    have hx' : x ∈ modNull ⊥ V hV := (QuotientGroup.eq_one_iff (N := modNull ⊥ V hV) x).1 hx
    rw [mem_modNull] at hx'
    exact IntMod.val_injective (by simpa using hx')
  · rintro rfl
    exact map_one _

private theorem s16h_sl28_pbb_card_preTil_bot {V : Subgroup G} (hV : IsElemAbelian 2 V)
    (S : Subgroup (Vtil ⊥ V hV)) :
    Nat.card ↥(preTil ⊥ V hV S) = Nat.card ↥S := by
  unfold preTil
  rw [Subgroup.card_map_of_injective (f := valHom V hV)
    (K := S.comap (mkTil ⊥ V hV)) (fun x y h => IntMod.val_injective h)]
  rw [← Subgroup.card_map_of_injective (f := mkTil ⊥ V hV)
    (K := S.comap (mkTil ⊥ V hV)) (s16h_sl28_pbb_mkTil_bot_injective hV),
    Subgroup.map_comap_eq_self_of_surjective (mkTil_surjective ⊥ V hV) S]

theorem s16h_sl28_seven_dichotomy_of_scalar_data
    (D : Data G) {V L : Subgroup G} (h : Setting16 D ⊥ V L)
    {x : G}
    (hZ0le : wSub ⊥ V h.hyp151.isElemAbelian L ⊓
        conjSubgroup (wSub ⊥ V h.hyp151.isElemAbelian L) x ≤
      wSub ⊥ V h.hyp151.isElemAbelian L ⊓ Subgroup.centralizer (L : Set G))
    (hcard : Nat.card ↥(commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L) ⊓
        fixV (lBar ⊥ V h.hyp151.isElemAbelian L)) = 8)
    (d : MulAut (Vtil ⊥ V h.hyp151.isElemAbelian))
    (hd7 : orderOf d = 7)
    (hfpf : ∀ z ∈ commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L) ⊓
        fixV (lBar ⊥ V h.hyp151.isElemAbelian L), d z = z → z = 1)
    (hstab : ∀ z ∈ imgTil ⊥ V h.hyp151.isElemAbelian
        (wSub ⊥ V h.hyp151.isElemAbelian L ⊓
          conjSubgroup (wSub ⊥ V h.hyp151.isElemAbelian L) x),
        d z ∈ imgTil ⊥ V h.hyp151.isElemAbelian
          (wSub ⊥ V h.hyp151.isElemAbelian L ⊓
            conjSubgroup (wSub ⊥ V h.hyp151.isElemAbelian L) x)) :
    (wSub ⊥ V h.hyp151.isElemAbelian L ⊓
        conjSubgroup (wSub ⊥ V h.hyp151.isElemAbelian L) x = ⊥) ∨
      (wSub ⊥ V h.hyp151.isElemAbelian L ⊓
          conjSubgroup (wSub ⊥ V h.hyp151.isElemAbelian L) x =
        wSub ⊥ V h.hyp151.isElemAbelian L ⊓ Subgroup.centralizer (L : Set G)) := by
  classical
  have hV := h.hyp151.isElemAbelian
  set W := wSub ⊥ V hV L with hWdef
  set C := W ⊓ Subgroup.centralizer (L : Set G) with hCdef
  set Z0 := W ⊓ conjSubgroup W x with hZ0def
  set Zbar : Subgroup (Vtil ⊥ V hV) :=
    commSub ⊤ (lBar ⊥ V hV L) ⊓ fixV (lBar ⊥ V hV L) with hZbardef
  set S : Subgroup (Vtil ⊥ V hV) := imgTil ⊥ V hV Z0 with hSdef
  have hCeq : C = preTil ⊥ V hV Zbar := by
    rw [hCdef, hWdef, hZbardef]
    exact s16h_sl28_pbb_wSub_inf_centralizer_eq_preTil D h
  have hZ0lePre : Z0 ≤ preTil ⊥ V hV Zbar := hCeq ▸ hZ0le
  have hZ0leV : Z0 ≤ V := by
    rw [hZ0def, hWdef]
    exact inf_le_left.trans (preTil_le ⊥ V hV _)
  have hS_le_Zbar : S ≤ Zbar := by
    intro q hq
    rw [hSdef, mem_imgTil] at hq
    obtain ⟨z, hzZ0, rfl⟩ := hq
    have hzC : z.val ∈ C := hZ0le hzZ0
    have hzPre : z.val ∈ preTil ⊥ V hV Zbar := hCeq ▸ hzC
    obtain ⟨y, hyval, hyZ⟩ := (mem_preTil ⊥ V hV Zbar).1 hzPre
    rwa [IntMod.val_injective hyval] at hyZ
  have hcardZ0S : Nat.card ↥Z0 = Nat.card ↥S := by
    have hmap : S = (intSub V hV Z0).map (mkTil ⊥ V hV) := by
      rw [hSdef, imgTil]
    rw [hmap, Subgroup.card_map_of_injective (s16h_sl28_pbb_mkTil_bot_injective hV)]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (G := G) hZ0leV).symm.toEquiv
  have hpowZbar : Nat.card ↥Zbar = 2 ^ rk ↥Zbar :=
    card_eq_two_pow (s15_Infra_vtil_sq_eq_one ⊥ V hV) Zbar
  have hrkZbar : rk ↥Zbar = 3 := by
    have h2 : 2 ^ rk ↥Zbar = 2 ^ 3 := by
      rw [← hpowZbar, hcard]
      norm_num
    exact Nat.pow_right_injective (by norm_num) h2
  by_cases hZ0bot : Z0 = ⊥
  · exact Or.inl hZ0bot
  · right
    have hSne : S ≠ ⊥ := by
      intro hSbot
      apply hZ0bot
      have hle : Z0 ⊓ V ≤ preTil ⊥ V hV S := le_preTil_imgTil ⊥ V hV Z0
      rw [hSbot, preTil_bot] at hle
      have hZV : Z0 ⊓ V = Z0 := inf_eq_left.mpr hZ0leV
      rw [hZV] at hle
      exact le_bot_iff.mp (by simpa using hle)
    have hSmap : S.map d.toMonoidHom = S := by
      refine Subgroup.eq_of_le_of_card_ge ?_ ?_
      · intro y hy
        rw [Subgroup.mem_map] at hy
        obtain ⟨z, hz, rfl⟩ := hy
        exact hstab z hz
      · rw [Subgroup.card_map_of_injective d.injective]
    have hfixS : S ⊓ fixV (Subgroup.zpowers d) = ⊥ := by
      rw [eq_bot_iff]
      intro z hz
      have hzZ : z ∈ Zbar := hS_le_Zbar hz.1
      have hzf : d z = z :=
        CFSG.Quasithin.mem_fixV_zpowers_iff_apply.mp hz.2
      exact Subgroup.mem_bot.mpr (hfpf z hzZ hzf)
    have hthree : 3 ≤ rk ↥S :=
      s16c167_three_le_rk_of_order_seven (s15_Infra_vtil_sq_eq_one ⊥ V hV) hd7 hSmap hfixS hSne
    have hSeqZbar : S = Zbar :=
      eq_of_le_of_rk_le (s15_Infra_vtil_sq_eq_one ⊥ V hV) hS_le_Zbar (by omega)
    have hcardZ0 : Nat.card ↥Z0 = 8 := by
      rw [hcardZ0S, hSeqZbar, hcard]
    have hcardPre : Nat.card ↥(preTil ⊥ V hV Zbar) = 8 := by
      rw [s16h_sl28_pbb_card_preTil_bot hV Zbar, hcard]
    have hZ0eqPre : Z0 = preTil ⊥ V hV Zbar :=
      Subgroup.eq_of_le_of_card_ge hZ0lePre (by omega)
    exact hZ0eqPre.trans hCeq.symm

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
