module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenThreeInputs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenTwo
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenThreeA
import CFSG.LocalAnalysis.SectionRank.AmbientRank
import CFSG.LocalAnalysis.SectionRank.GroupRankTransport

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

private noncomputable def s15BarHom (D : Data G) {V₀ V : Subgroup G} (hV : IsElemAbelian 2 V)
    (hMs : D.M ≤ stabTil V₀ V) : ↥D.M →* ↥(Mbar D.M V₀ V hV) :=
  ((actTil V₀ V hV).comp (Subgroup.inclusion hMs)).codRestrict _
    (fun m => by
      change actTil V₀ V hV ⟨(m : G), hMs m.2⟩ ∈ Mbar D.M V₀ V hV
      exact actTil_mem_barSub V₀ V hV m.2 (hMs m.2))

private theorem s15BarHom_surjective (D : Data G) {V₀ V : Subgroup G} (hV : IsElemAbelian 2 V)
    (hMs : D.M ≤ stabTil V₀ V) : Function.Surjective (s15BarHom D hV hMs) := by
  intro y
  obtain ⟨g, hgM, hgy⟩ := (mem_barSub V₀ V hV D.M y).1 y.2
  refine ⟨⟨(g : G), hgM⟩, Subtype.ext ?_⟩
  show actTil V₀ V hV ⟨(g : G), hMs hgM⟩ = (y : MulAut (Vtil V₀ V hV))
  rw [show actTil V₀ V hV ⟨(g : G), hMs hgM⟩ = actTil V₀ V hV g from
    congrArg (actTil V₀ V hV) (Subtype.ext rfl)]
  exact hgy

private theorem s15BarHom_ker (D : Data G) {V₀ V : Subgroup G} (hV : IsElemAbelian 2 V)
    (hMs : D.M ≤ stabTil V₀ V) :
    (s15BarHom D hV hMs).ker = (F11.CTilde D.M V₀ V).subgroupOf D.M := by
  ext m
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf,
    mem_cTilde_iff hV (hMs.trans (stabTil_le_normalizer V₀ V))]
  constructor
  · intro hm
    refine ⟨m.2, hMs m.2, ?_⟩
    have h2 := congrArg Subtype.val hm
    change actTil V₀ V hV (Subgroup.inclusion hMs m) = 1 at h2
    rwa [show Subgroup.inclusion hMs m = (⟨(m : G), hMs m.2⟩ : stabTil V₀ V) from
      Subtype.ext rfl] at h2
  · rintro ⟨-, hst, hact⟩
    apply Subtype.ext
    show actTil V₀ V hV ⟨(m : G), hMs m.2⟩ = 1
    rw [show (⟨(m : G), hMs m.2⟩ : stabTil V₀ V) = ⟨(m : G), hst⟩ from Subtype.ext rfl]
    exact hact

theorem s15_Three_cTilde_normal {D : Data G} {V₀ V : Subgroup G} (hV : IsElemAbelian 2 V)
    (hMs : D.M ≤ stabTil V₀ V) : ((F11.CTilde D.M V₀ V).subgroupOf D.M).Normal := by
  rw [← s15BarHom_ker D hV hMs]
  exact MonoidHom.normal_ker _

private noncomputable def s15BarEquiv (D : Data G) {V₀ V : Subgroup G} (hV : IsElemAbelian 2 V)
    (hMs : D.M ≤ stabTil V₀ V) [((F11.CTilde D.M V₀ V).subgroupOf D.M).Normal] :
    F11.MBar11 D.M V₀ V ≃* ↥(Mbar D.M V₀ V hV) :=
  QuotientGroup.liftEquiv ((F11.CTilde D.M V₀ V).subgroupOf D.M)
    (s15BarHom_surjective D hV hMs) (s15BarHom_ker D hV hMs).symm

theorem s15_Three_pRank_MBar11 {D : Data G} {V₀ V : Subgroup G} (hV : IsElemAbelian 2 V)
    (hMs : D.M ≤ stabTil V₀ V) [((F11.CTilde D.M V₀ V).subgroupOf D.M).Normal] (p : ℕ) :
    CFSG.Open.pRank p (⊤ : Subgroup (F11.MBar11 D.M V₀ V)) =
      CFSG.Open.pRank p (⊤ : Subgroup ↥(Mbar D.M V₀ V hV)) := by
  have h1 := CFSG.pRank_congr_of_mulEquiv
    (Subgroup.topEquiv.trans (s15BarEquiv D hV hMs) |>.trans Subgroup.topEquiv.symm) p
  simp only [CFSG.SectionRank.pRank_coe_eq_openPRank] at h1
  exact h1

theorem s15_Three_card_MBar11 {D : Data G} {V₀ V : Subgroup G} (hV : IsElemAbelian 2 V)
    (hMs : D.M ≤ stabTil V₀ V) [((F11.CTilde D.M V₀ V).subgroupOf D.M).Normal] :
    Nat.card (F11.MBar11 D.M V₀ V) = Nat.card ↥(Mbar D.M V₀ V hV) :=
  Nat.card_congr (s15BarEquiv D hV hMs).toEquiv


section RsOne

theorem s15_Three_rs_eq_one_iff (D : Data G) (V₀ V : Subgroup G) (hV : IsElemAbelian 2 V)
    (L K₀ : Subgroup G) :
    s15Rs D V₀ V hV L K₀ = 1 ↔
      (conjSet (barSub V₀ V hV K₀) (s15NBar D V₀ V hV L)).ncard = 1 ∧
        s15 D.M V₀ V hV L = 1 := by
  unfold s15Rs
  exact mul_eq_one

theorem s15_Three_eq_of_ncard_conjSet {A : Type*} [Group A] {X K N : Subgroup A}
    (hX : IsDirectProdOfConj X K N) (h1 : (conjSet K N).ncard = 1) : X = K := by
  obtain ⟨Y, hY⟩ := Set.ncard_eq_one.1 h1
  have hK : K ∈ conjSet K N := ⟨1, N.one_mem, by ext x; simp⟩
  rw [hY, Set.mem_singleton_iff] at hK
  have h2 := hX.2.1
  rw [hY, iSup_singleton] at h2
  rw [← h2, hK]

theorem s15_Three_le_normalizer {D : Data G} {V₀ V : Subgroup G} {hV : IsElemAbelian 2 V}
    {L : Subgroup G} (hs : s15 D.M V₀ V hV L = 1) :
    Mbar D.M V₀ V hV ≤
      normalizer ((lBar V₀ V hV L : Subgroup (MulAut (Vtil V₀ V hV))) : Set _) := by
  unfold s15 at hs
  obtain ⟨a, ha⟩ := Set.ncard_eq_one.1 hs
  have hL : (barSub V₀ V hV L) ∈ {X : Subgroup (MulAut (Vtil V₀ V hV)) |
      ∃ φ ∈ Mbar D.M V₀ V hV, X = (barSub V₀ V hV L).map (MulAut.conj φ).toMonoidHom} :=
    ⟨1, Subgroup.one_mem _, by ext x; simp⟩
  intro φ hφ
  have hφL : (barSub V₀ V hV L).map (MulAut.conj φ).toMonoidHom ∈
      {X : Subgroup (MulAut (Vtil V₀ V hV)) |
        ∃ φ ∈ Mbar D.M V₀ V hV, X = (barSub V₀ V hV L).map (MulAut.conj φ).toMonoidHom} :=
    ⟨φ, hφ, rfl⟩
  rw [ha, Set.mem_singleton_iff] at hL hφL
  have hconj : (barSub V₀ V hV L).map (MulAut.conj φ).toMonoidHom = barSub V₀ V hV L :=
    hφL.trans hL.symm
  show φ ∈ normalizer ((barSub V₀ V hV L : Subgroup (MulAut (Vtil V₀ V hV))) : Set _)
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    rw [← hconj]
    exact ⟨x, hx, rfl⟩
  · intro hx
    rw [← hconj] at hx
    obtain ⟨y, hy, hyx⟩ := hx
    have : y = x := by
      have := congrArg (fun z => φ⁻¹ * z * φ) hyx
      simpa [MulAut.conj_apply, mul_assoc] using this
    rwa [← this]

theorem s15_Three_nBar_eq {D : Data G} {V₀ V : Subgroup G} {hV : IsElemAbelian 2 V}
    {L : Subgroup G} (hs : s15 D.M V₀ V hV L = 1) :
    s15NBar D V₀ V hV L = Mbar D.M V₀ V hV :=
  inf_eq_left.2 (s15_Three_le_normalizer hs)

theorem s15_Three_lBar_eq {D : Data G} {V₀ V : Subgroup G} {hV : IsElemAbelian 2 V}
    {L K₀ : Subgroup G} (hshape : s15Shape D V₀ V hV L K₀) (hrs : s15Rs D V₀ V hV L K₀ = 1) :
    lBar V₀ V hV L = barSub V₀ V hV K₀ :=
  s15_Three_eq_of_ncard_conjSet hshape.2.2.1 ((s15_Three_rs_eq_one_iff D V₀ V hV L K₀).1 hrs).1

end RsOne


section Star

variable {D : Data G} {V₀ V L : Subgroup G}

private theorem s15_Three_barSub_le_of_cTilde_eq {M V₀ V₁ V : Subgroup G} (hV : IsElemAbelian 2 V)
    (hM : M ≤ normalizer (V : Set G)) (hM₀ : M ≤ normalizer (V₀ : Set G))
    (hM₁ : M ≤ normalizer (V₁ : Set G)) (hc : F11.CTilde M V₀ V = F11.CTilde M V₁ V)
    {X Y : Subgroup G} (hX : X ≤ M) (hY : Y ≤ M)
    (hXY : barSub V₀ V hV X ≤ barSub V₀ V hV Y) :
    barSub V₁ V hV X ≤ barSub V₁ V hV Y := by
  intro φ hφ
  obtain ⟨g, hgX, rfl⟩ := (mem_barSub V₁ V hV X φ).1 hφ
  have hg0 : (g : G) ∈ stabTil V₀ V := le_stabTil hM hM₀ (hX hgX)
  obtain ⟨y, hyY, hy⟩ :=
    (mem_barSub V₀ V hV Y _).1 (hXY (actTil_mem_barSub V₀ V hV hgX hg0))
  have hy1 : (y : G) ∈ stabTil V₁ V := le_stabTil hM hM₁ (hY hyY)
  have hmem : (g : G) * (y : G)⁻¹ ∈ F11.CTilde M V₀ V := by
    rw [mem_cTilde_iff hV hM]
    refine ⟨M.mul_mem (hX hgX) (M.inv_mem (hY hyY)),
      (stabTil V₀ V).mul_mem hg0 ((stabTil V₀ V).inv_mem y.2), ?_⟩
    have : (⟨(g : G) * (y : G)⁻¹, (stabTil V₀ V).mul_mem hg0 ((stabTil V₀ V).inv_mem y.2)⟩ :
        stabTil V₀ V) = ⟨g, hg0⟩ * y⁻¹ := rfl
    rw [this, map_mul, map_inv, ← hy, mul_inv_cancel]
  rw [hc, mem_cTilde_iff hV hM] at hmem
  obtain ⟨-, h1, h1'⟩ := hmem
  have h2 : (⟨(g : G) * (y : G)⁻¹, h1⟩ : stabTil V₁ V) = g * (⟨y, hy1⟩ : stabTil V₁ V)⁻¹ := rfl
  rw [h2, map_mul, map_inv, mul_inv_eq_one] at h1'
  rw [h1']
  exact actTil_mem_barSub V₁ V hV hyY hy1

theorem s15_Three_barSub_star_iff (D : Data G) (h1217 : R1217 D) (h : Hyp151 D V₀ V L)
    {X Y : Subgroup G} (hX : X ≤ D.M) (hY : Y ≤ D.M) :
    barSub V₀ V h.isElemAbelian X = barSub V₀ V h.isElemAbelian Y ↔
      barSub (v1Sub D.M V₀ V h.isElemAbelian L) V h.isElemAbelian X =
        barSub (v1Sub D.M V₀ V h.isElemAbelian L) V h.isElemAbelian Y := by
  have hc := fifteen_two_cent D h1217 h h.isElemAbelian
  have hM := h.hyp125.pairFacts.le_normalizer
  have hM₀ := h.hyp125.pairFacts.le_normalizer₀
  have hM₁ := s15_Infra_le_normalizer_v1Sub (L := L) h.hyp125 h.isElemAbelian
  constructor
  · intro hXY
    exact le_antisymm
      (s15_Three_barSub_le_of_cTilde_eq h.isElemAbelian hM hM₀ hM₁ hc.symm hX hY hXY.le)
      (s15_Three_barSub_le_of_cTilde_eq h.isElemAbelian hM hM₀ hM₁ hc.symm hY hX hXY.ge)
  · intro hXY
    exact le_antisymm
      (s15_Three_barSub_le_of_cTilde_eq h.isElemAbelian hM hM₁ hM₀ hc hX hY hXY.le)
      (s15_Three_barSub_le_of_cTilde_eq h.isElemAbelian hM hM₁ hM₀ hc hY hX hXY.ge)

theorem s15_Three_commSub_top_lStar (h : Hyp151 D V₀ V L) (hV : IsElemAbelian 2 V) :
    commSub ⊤ (lStar D.M V₀ V hV L) = wStar D.M V₀ V hV L := by
  apply le_antisymm
  · rw [commSub, Subgroup.closure_le]
    rintro c ⟨x, hx, w, -, rfl⟩
    obtain ⟨g, hgL, rfl⟩ := (mem_barSub (v1Sub D.M V₀ V hV L) V hV L x).1 hx
    obtain ⟨y, rfl⟩ := mkTil_surjective (v1Sub D.M V₀ V hV L) V hV w
    have hg0 : (g : G) ∈ stabTil V₀ V :=
      le_stabTil h.hyp125.pairFacts.le_normalizer h.hyp125.pairFacts.le_normalizer₀ (h.le hgL)
    have hgs : actStab V₀ V hV ⟨g, hg0⟩ y = actStab (v1Sub D.M V₀ V hV L) V hV g y := by
      apply IntMod.val_injective
      rw [actStab_apply_val, actStab_apply_val]
    show _ ∈ imgTil (v1Sub D.M V₀ V hV L) V hV (wSub V₀ V hV L)
    rw [mem_imgTil]
    refine ⟨actStab (v1Sub D.M V₀ V hV L) V hV g y * y⁻¹, ?_, ?_⟩
    · rw [wSub, mem_preTil]
      refine ⟨actStab (v1Sub D.M V₀ V hV L) V hV g y * y⁻¹, rfl, ?_⟩
      rw [map_mul, map_inv, ← hgs, ← actTil_mk]
      exact Subgroup.subset_closure ⟨_, actTil_mem_barSub V₀ V hV hgL hg0, _, trivial, rfl⟩
    · rw [map_mul, map_inv, ← actTil_mk]
  · calc wStar D.M V₀ V hV L = commSub (wStar D.M V₀ V hV L) (lStar D.M V₀ V hV L) :=
        (s15_Three_commSub_wStar h hV).symm
      _ ≤ commSub ⊤ (lStar D.M V₀ V hV L) := commSub_mono le_top le_rfl

theorem s15_Three_wStar_eq_top (D : Data G) (h1217 : R1217 D) (h : Hyp151 D V₀ V L)
    (hV : IsElemAbelian 2 V) (hL : barSub V₀ V hV L ≠ ⊥) (hs : s15 D.M V₀ V hV L = 1) :
    wStar D.M V₀ V hV L = ⊤ := by
  have hcard := ncard_wStarConj D h hV
  rw [hs] at hcard
  obtain ⟨X, hX⟩ := Set.ncard_eq_one.1 hcard
  have hmem : wStar D.M V₀ V hV L ∈ wStarConj D.M V₀ V hV L := by
    have := s15_Infra_map_wStar_mem_wStarConj (L := L) h.hyp125 hV (e := 1) (Subgroup.one_mem _)
    have h1 : (wStar D.M V₀ V hV L).map (1 : MulAut (vStar D.M V₀ V hV L)).toMonoidHom =
        wStar D.M V₀ V hV L := by
      ext x
      simp [Subgroup.mem_map]
    rwa [h1] at this
  obtain ⟨-, hspan⟩ := fifteen_two_directSum D h1217 h hV hL
  rw [hX] at hspan hmem
  rw [Set.mem_singleton_iff] at hmem
  rw [sSup_singleton] at hspan
  rw [hmem]
  exact hspan


theorem s15_Three_natural_lStar (D : Data G) (h1217 : R1217 D) (h : Hyp151 D V₀ V L)
    {K₀ : Subgroup G} (hshape : s15Shape D V₀ V h.isElemAbelian L K₀)
    (hrs : s15Rs D V₀ V h.isElemAbelian L K₀ = 1) :
    s15KNat ↥(lBar V₀ V h.isElemAbelian L) (lStar D.M V₀ V h.isElemAbelian L)
      (wStar D.M V₀ V h.isElemAbelian L) := by
  have hLK := s15_Three_lBar_eq hshape hrs
  have hstar : lStar D.M V₀ V h.isElemAbelian L =
      barSub (v1Sub D.M V₀ V h.isElemAbelian L) V h.isElemAbelian K₀ :=
    (s15_Three_barSub_star_iff D h1217 h h.le (hshape.1.trans h.le)).1 hLK
  have hW : commSub ⊤ (barSub (v1Sub D.M V₀ V h.isElemAbelian L) V h.isElemAbelian K₀) =
      wStar D.M V₀ V h.isElemAbelian L := by
    rw [← hstar]
    exact s15_Three_commSub_top_lStar h h.isElemAbelian
  have hnat := hshape.2.2.2.1
  rw [hW, ← hstar, ← hLK] at hnat
  exact hnat

private theorem s15_Three_commute_star (D : Data G) (h1217 : R1217 D) (h : Hyp151 D V₀ V L)
    (hV : IsElemAbelian 2 V) {a b : G} (ha : a ∈ D.M) (hb : b ∈ D.M)
    (ha0 : a ∈ stabTil V₀ V) (hb0 : b ∈ stabTil V₀ V)
    (ha1 : a ∈ stabTil (v1Sub D.M V₀ V hV L) V) (hb1 : b ∈ stabTil (v1Sub D.M V₀ V hV L) V)
    (hab : actTil V₀ V hV ⟨a, ha0⟩ * actTil V₀ V hV ⟨b, hb0⟩ =
      actTil V₀ V hV ⟨b, hb0⟩ * actTil V₀ V hV ⟨a, ha0⟩) :
    actTil (v1Sub D.M V₀ V hV L) V hV ⟨a, ha1⟩ * actTil (v1Sub D.M V₀ V hV L) V hV ⟨b, hb1⟩ =
      actTil (v1Sub D.M V₀ V hV L) V hV ⟨b, hb1⟩ *
        actTil (v1Sub D.M V₀ V hV L) V hV ⟨a, ha1⟩ := by
  have hM := h.hyp125.pairFacts.le_normalizer
  have hc := fifteen_two_cent D h1217 h hV
  have hs0 : a * b * a⁻¹ * b⁻¹ ∈ stabTil V₀ V :=
    (stabTil V₀ V).mul_mem ((stabTil V₀ V).mul_mem ((stabTil V₀ V).mul_mem ha0 hb0)
      ((stabTil V₀ V).inv_mem ha0)) ((stabTil V₀ V).inv_mem hb0)
  have hmem : a * b * a⁻¹ * b⁻¹ ∈ F11.CTilde D.M V₀ V := by
    rw [mem_cTilde_iff hV hM]
    refine ⟨D.M.mul_mem (D.M.mul_mem (D.M.mul_mem ha hb) (D.M.inv_mem ha)) (D.M.inv_mem hb),
      hs0, ?_⟩
    have : (⟨a * b * a⁻¹ * b⁻¹, hs0⟩ : stabTil V₀ V) =
        ⁅(⟨a, ha0⟩ : stabTil V₀ V), ⟨b, hb0⟩⁆ := rfl
    rw [this, map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.2 hab
  rw [← hc, mem_cTilde_iff hV hM] at hmem
  obtain ⟨-, hs1, h1⟩ := hmem
  have : (⟨a * b * a⁻¹ * b⁻¹, hs1⟩ : stabTil (v1Sub D.M V₀ V hV L) V) =
      ⁅(⟨a, ha1⟩ : stabTil (v1Sub D.M V₀ V hV L) V), ⟨b, hb1⟩⁆ := rfl
  rw [this, map_commutatorElement] at h1
  exact commutatorElement_eq_one_iff_mul_comm.1 h1

theorem s15_Three_Mbar_centralizer (hAbs : RAbsIrr153) (D : Data G) (h1217 : R1217 D)
    (h : Hyp151 D V₀ V L) (hV : IsElemAbelian 2 V) (hL : barSub V₀ V hV L ≠ ⊥)
    (hs : s15 D.M V₀ V hV L = 1)
    (hperf : s15KNatPerf ↥(lBar V₀ V hV L) (lStar D.M V₀ V hV L) (wStar D.M V₀ V hV L)) :
    ∀ x ∈ Mbar D.M V₀ V hV, (∀ y ∈ lBar V₀ V hV L, x * y = y * x) → x = 1 := by
  intro x hx hcomm
  have hM := h.hyp125.pairFacts.le_normalizer
  have hM₀ := h.hyp125.pairFacts.le_normalizer₀
  have hM₁ := s15_Infra_le_normalizer_v1Sub (L := L) h.hyp125 hV
  have hc := fifteen_two_cent D h1217 h hV
  have htop := s15_Three_wStar_eq_top D h1217 h hV hL hs
  obtain ⟨g, hgM, rfl⟩ := (mem_barSub V₀ V hV D.M x).1 hx
  have hg1 : (g : G) ∈ stabTil (v1Sub D.M V₀ V hV L) V := le_stabTil hM hM₁ hgM
  have hcomm1 : ∀ k ∈ lStar D.M V₀ V hV L,
      actTil (v1Sub D.M V₀ V hV L) V hV ⟨g, hg1⟩ * k =
        k * actTil (v1Sub D.M V₀ V hV L) V hV ⟨g, hg1⟩ := by
    intro k hk
    obtain ⟨l, hlL, rfl⟩ := (mem_barSub (v1Sub D.M V₀ V hV L) V hV L k).1 hk
    have hl0 : (l : G) ∈ stabTil V₀ V := le_stabTil hM hM₀ (h.le hlL)
    exact s15_Three_commute_star D h1217 h hV hgM (h.le hlL) g.2 hl0 hg1 l.2
      (hcomm _ (actTil_mem_barSub V₀ V hV hlL hl0))
  have hstab : actTil (v1Sub D.M V₀ V hV L) V hV ⟨g, hg1⟩ ∈ stabSub (wStar D.M V₀ V hV L) := by
    intro u
    rw [htop]
    simp
  have hz := hAbs (vStar D.M V₀ V hV L) (s15_Infra_vtil_sq_eq_one _ V hV) ↥(lBar V₀ V hV L)
    (lStar D.M V₀ V hV L) (wStar D.M V₀ V hV L) hperf _ hstab hcomm1
  have hone : actTil (v1Sub D.M V₀ V hV L) V hV ⟨g, hg1⟩ = 1 := by
    ext z
    have hzW : z ∈ wStar D.M V₀ V hV L := by
      rw [htop]
      trivial
    simpa using hz z hzW
  have hmem : (g : G) ∈ F11.CTilde D.M (v1Sub D.M V₀ V hV L) V :=
    (mem_cTilde_iff hV hM).2 ⟨hgM, hg1, hone⟩
  rw [hc, mem_cTilde_iff hV hM] at hmem
  obtain ⟨-, hst, h0⟩ := hmem
  exact h0

end Star


section Ranks

variable {D : Data G} {V₀ V L : Subgroup G}

private theorem s15_Three_embed (hAbs : RAbsIrr153) (D : Data G) (h1217 : R1217 D)
    (h : Hyp151 D V₀ V L) (hV : IsElemAbelian 2 V) (hL : barSub V₀ V hV L ≠ ⊥)
    (hs : s15 D.M V₀ V hV L = 1)
    (hperf : s15KNatPerf ↥(lBar V₀ V hV L) (lStar D.M V₀ V hV L) (wStar D.M V₀ V hV L)) :
    ∃ f : ↥(lBar V₀ V hV L) →* ↥(Mbar D.M V₀ V hV), Function.Injective f ∧ f.range.Normal ∧
      ∀ x : ↥(Mbar D.M V₀ V hV), (∀ y, x * f y = f y * x) → x = 1 := by
  have hle : lBar V₀ V hV L ≤ Mbar D.M V₀ V hV := barSub_mono V₀ V hV h.le
  refine ⟨Subgroup.inclusion hle, Subgroup.inclusion_injective hle, ?_, ?_⟩
  · rw [Subgroup.inclusion_range]
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer hle).2 (s15_Three_le_normalizer hs)
  · intro x hx
    have := s15_Three_Mbar_centralizer hAbs D h1217 h hV hL hs hperf x.1 x.2 (fun y hy =>
      congrArg Subtype.val (hx ⟨y, hy⟩))
    exact Subtype.ext this

theorem s15_Three_rank_ListTwo (hAut : RAutRank153) (hAbs : RAbsIrr153) (D : Data G)
    (h1217 : R1217 D) (h : Hyp151 D V₀ V L) (hV : IsElemAbelian 2 V)
    (hL : barSub V₀ V hV L ≠ ⊥) (hs : s15 D.M V₀ V hV L = 1)
    (hperf : s15KNatPerf ↥(lBar V₀ V hV L) (lStar D.M V₀ V hV L) (wStar D.M V₀ V hV L))
    (hL2 : s15ListTwo ↥(lBar V₀ V hV L)) :
    (∀ p : ℕ, p.Prime → p ≠ 2 →
        CFSG.Open.pRank p (⊤ : Subgroup ↥(Mbar D.M V₀ V hV)) ≤ 1) ∧
      (IsL3 ↥(lBar V₀ V hV L) 1 → ∀ p : ℕ, p.Prime → p ∣ Nat.card ↥(Mbar D.M V₀ V hV) →
        p = 2 ∨ p = 3 ∨ p = 7) ∧
      (UC22.IsAlt ↥(lBar V₀ V hV L) 5 → ∀ p : ℕ, p.Prime → p ∣ Nat.card ↥(Mbar D.M V₀ V hV) →
        p = 2 ∨ p = 3 ∨ p = 5) := by
  obtain ⟨f, hf, hn, hc⟩ := s15_Three_embed hAbs D h1217 h hV hL hs hperf
  exact (hAut _ _ f hf hn hc).1 hL2

theorem s15_Three_rank_ListFour (hAut : RAutRank153) (hAbs : RAbsIrr153) (D : Data G)
    (h1217 : R1217 D) (h : Hyp151 D V₀ V L) (hV : IsElemAbelian 2 V)
    (hL : barSub V₀ V hV L ≠ ⊥) (hs : s15 D.M V₀ V hV L = 1)
    (hperf : s15KNatPerf ↥(lBar V₀ V hV L) (lStar D.M V₀ V hV L) (wStar D.M V₀ V hV L))
    (hL4 : s15ListFour ↥(lBar V₀ V hV L)) :
    (∀ p : ℕ, p.Prime → p ≠ 2 → p ≠ 3 →
        CFSG.Open.pRank p (⊤ : Subgroup ↥(Mbar D.M V₀ V hV)) ≤ 1) ∧
      CFSG.Open.pRank 3 (⊤ : Subgroup ↥(Mbar D.M V₀ V hV)) ≤ 3 ∧
      (¬ IsOmegaMinus ↥(lBar V₀ V hV L) 6 1 →
        CFSG.Open.pRank 3 (⊤ : Subgroup ↥(Mbar D.M V₀ V hV)) ≤ 2) := by
  obtain ⟨f, hf, hn, hc⟩ := s15_Three_embed hAbs D h1217 h hV hL hs hperf
  exact (hAut _ _ f hf hn hc).2 hL4

end Ranks

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
