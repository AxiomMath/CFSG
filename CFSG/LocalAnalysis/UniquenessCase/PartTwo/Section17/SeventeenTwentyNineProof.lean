module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenTwentyNine
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenSeventeen
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S16Setup
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.HJHolds

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem normal_Opp (p : ℕ) (X : Subgroup G) :
    ((Opp p X).subgroupOf X).Normal :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer
    (CFSG.LocalAnalysis.RankThreeUC.pElementSubgroup_le p X)).2
    (CFSG.LocalAnalysis.RankThreeUC.le_normalizer_pElementSubgroup p X)

theorem normal_of_J2_ctx
    (D : Data G) {V₀ V : Subgroup G} (h22 : R17_22At D V₀ V) (h23 : R17_23At D V₀ V)
    {L : Subgroup G} (c : Ctx17_17 D V₀ V L) :
    (L.subgroupOf D.M).Normal := by
  obtain ⟨P, hP⟩ := CFSG.ABGLocalTools.exists_isSylowOf 3 L
  rcases h22 L P (centerOf P) c hP rfl with hHe | ⟨-, -, -, hLopp, -⟩
  · exact absurd (h23 L c) (not_isSpor_He_of_isSpor_J2 (Bar2 L) hHe)
  · rw [hLopp]
    exact normal_Opp 3 D.M

theorem sig_eq_five_of_J2_ctx
    (D : Data G) {V₀ V : Subgroup G} (h22 : R17_22At D V₀ V) (h23 : R17_23At D V₀ V)
    {L : Subgroup G} (c : Ctx17_17 D V₀ V L) :
    D.sig = {5} := by
  obtain ⟨P, hP⟩ := CFSG.ABGLocalTools.exists_isSylowOf 3 L
  rcases h22 L P (centerOf P) c hP rfl with hHe | ⟨-, hsig, -⟩
  · exact absurd (h23 L c) (not_isSpor_He_of_isSpor_J2 (Bar2 L) hHe)
  · exact hsig

theorem normal_barSub_of_normal {M L V₀ V : Subgroup G} (hV : IsElemAbelian 2 V)
    (hLM : L ≤ M) (hn : (L.subgroupOf M).Normal) :
    ((barSub V₀ V hV L).subgroupOf (barSub V₀ V hV M)).Normal := by
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer (barSub_mono V₀ V hV hLM)]
  intro y hy
  obtain ⟨m, hmM, rfl⟩ := (mem_barSub V₀ V hV M y).1 hy
  rw [Subgroup.mem_normalizer_iff]
  intro z
  constructor
  · intro hz
    obtain ⟨l, hlL, rfl⟩ := (mem_barSub V₀ V hV L z).1 hz
    have hconj : (m : G) * (l : G) * (m : G)⁻¹ ∈ L := by
      have h := hn.conj_mem (⟨(l : G), hLM hlL⟩ : M) hlL ⟨(m : G), hmM⟩
      simpa [Subgroup.mem_subgroupOf] using h
    refine (mem_barSub V₀ V hV L _).2 ⟨m * l * m⁻¹, hconj, ?_⟩
    rw [map_mul, map_mul, map_inv]
  · intro hz
    obtain ⟨w, hwL, hw⟩ := (mem_barSub V₀ V hV L _).1 hz
    have hconj : (m : G)⁻¹ * (w : G) * (m : G) ∈ L := by
      have h := hn.conj_mem (⟨(w : G), hLM hwL⟩ : M) hwL ⟨(m : G)⁻¹, M.inv_mem hmM⟩
      simpa [Subgroup.mem_subgroupOf] using h
    have hmem : actTil V₀ V hV (m⁻¹ * w * m) ∈ barSub V₀ V hV L :=
      actTil_mem_barSub V₀ V hV hconj (m⁻¹ * w * m).2
    have hmz : actTil V₀ V hV (m⁻¹ * w * m) = z := by
      rw [map_mul, map_mul, map_inv, hw]
      group
    rwa [hmz] at hmem

theorem hjSetup_of_ctx17
    (D : Data G) {V₀ V : Subgroup G} (h22 : R17_22At D V₀ V) (h23 : R17_23At D V₀ V)
    (h25 : R17_25At D V₀ V) (hHJ : K_HJData) {L : Subgroup G} (c : Ctx17_17 D V₀ V L) :
    HJSetup (Vtil V₀ V c.hyp125.isElemAbelian)
      (Mbar D.M V₀ V c.hyp125.isElemAbelian)
      (barSub V₀ V c.hyp125.isElemAbelian L) := by
  let hV := c.hyp125.isElemAbelian
  have hLM : L ≤ D.M := c.mem_calC.1.le
  have hLnorm : (L.subgroupOf D.M).Normal := normal_of_J2_ctx D h22 h23 c
  have hMS : D.M ≤ stabTil V₀ V :=
    le_stabTil c.hyp125.pairFacts.le_normalizer c.hyp125.pairFacts.le_normalizer₀
  have hLS : L ≤ stabTil V₀ V := hLM.trans hMS
  have h25L := h25 L c
  have hirr : IsIrrOn (barSub V₀ V hV L) ⊤ ⊥ := h25L.1
  have hrk : rk (Vtil V₀ V hV) = 12 := h25L.2.1
  have hsq : ∀ w : Vtil V₀ V hV, w ^ 2 = 1 := s15_Infra_vtil_sq_eq_one V₀ V hV
  have hcardW : Nat.card (Vtil V₀ V hV) = 2 ^ 12 := by
    rw [← Subgroup.card_top (G := Vtil V₀ V hV),
      CFSG.Quasithin.card_eq_two_pow hsq ⊤, CFSG.Quasithin.rk_top, hrk]
  have hL1 : barSub V₀ V hV L ≠ ⊥ :=
    ne_bot_of_isIrrOn_of_two_lt_card hsq hirr (by rw [hcardW]; norm_num)
  have hpcore : barSub V₀ V hV (pCoreOf 2 L) = ⊥ :=
    TwelveTwentyThree.barSub_pCoreOf_eq_bot_of_isSubnormal hV c.mem_calC.1
      (barSub_pCoreOf_eq_bot_of_hyp125 c.hyp125)
  have hSpor : IsSpor ↥(barSub V₀ V hV L) .J2 :=
    isSpor_barSub_of_isSpor_bar2_of_pcore hV hLS hpcore hL1 (h23 L c)
  have hnorm : ((barSub V₀ V hV L).subgroupOf (barSub V₀ V hV D.M)).Normal :=
    normal_barSub_of_normal hV hLM hLnorm
  refine ⟨barSub_mono V₀ V hV hLM, hnorm, hSpor, hirr, hrk, ?_⟩
  exact (hHJ (Vtil V₀ V hV) hsq hrk (barSub V₀ V hV D.M) (barSub V₀ V hV L)
    (barSub_mono V₀ V hV hLM) hnorm hSpor hirr).1

theorem hjSetup_of_ctx
    (D : Data G) {V₀ V : Subgroup G} (h22 : R17_22At D V₀ V) (h23 : R17_23At D V₀ V)
    (h25 : R17_25At D V₀ V) (hHJ : K_HJData) {L : Subgroup G} (c : Ctx17_29 D V₀ V L) :
    HJSetup (Vtil V₀ V c.ctx.hyp125.isElemAbelian)
      (Mbar D.M V₀ V c.ctx.hyp125.isElemAbelian)
      (barSub V₀ V c.ctx.hyp125.isElemAbelian L) :=
  hjSetup_of_ctx17 D h22 h23 h25 hHJ c.ctx

theorem isSylowIn_barSub_sylow (D : Data G) {V₀ V : Subgroup G} (hV : IsElemAbelian 2 V)
    (hMS : D.M ≤ stabTil V₀ V) :
    IsSylowIn 2 (barSub V₀ V hV D.T) (Mbar D.M V₀ V hV) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let Y := Mbar D.M V₀ V hV
  have hT_M : IsSylowIn 2 D.T D.M := CFSG.ABGLocalTools.isSylowOf_iff.1 D.sylowM
  obtain ⟨Q, hQ⟩ := D.sylowM
  let φ : ↥D.M →* MulAut (Vtil V₀ V hV) :=
    (actTil V₀ V hV).comp (Subgroup.inclusion hMS)
  have hφmem : ∀ x : ↥D.M, φ x ∈ Y := fun x =>
    actTil_mem_barSub V₀ V hV x.2 (hMS x.2)
  let ψ : ↥D.M →* ↥Y := φ.codRestrict Y hφmem
  have hψ : Function.Surjective ψ := by
    intro y
    obtain ⟨x, hx, hxeq⟩ := (mem_barSub V₀ V hV D.M (y : MulAut (Vtil V₀ V hV))).1 y.2
    refine ⟨⟨(x : G), hx⟩, ?_⟩
    have hx' : ((Subgroup.inclusion hMS) ⟨(x : G), hx⟩) = x := Subtype.ext rfl
    exact Subtype.ext (by simpa [ψ, φ, hx'] using hxeq)
  let P' : Sylow 2 ↥Y := Q.mapSurjective (f := ψ) hψ
  have hP' : IsSylowIn 2 ((P' : Subgroup ↥Y).map Y.subtype) Y :=
    isSylowIn_of_card_eq (Subgroup.map_subtype_le _) (by
      rw [Subgroup.card_map_of_injective Y.subtype_injective, Sylow.card_eq_multiplicity P'])
  have hEq : ((P' : Subgroup ↥Y).map Y.subtype) = barSub V₀ V hV D.T := by
    rw [show P' = Q.mapSurjective (f := ψ) hψ from rfl,
      Sylow.coe_mapSurjective (f := ψ) hψ, Subgroup.map_map]
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      exact actTil_mem_barSub V₀ V hV (by rw [← hQ]; exact Subgroup.mem_map_of_mem _ hx)
        (hMS x.2)
    · intro z hz
      obtain ⟨g, hg, rfl⟩ := (mem_barSub V₀ V hV D.T z).1 hz
      have hgmap : (g : G) ∈ (Q : Subgroup ↥D.M).map D.M.subtype := by
        rw [hQ]
        exact hg
      obtain ⟨x, hx, hxval⟩ := Subgroup.mem_map.1 hgmap
      refine ⟨x, hx, ?_⟩
      have hsub : (⟨(x : G), hMS x.2⟩ : ↥(stabTil V₀ V)) = g := Subtype.ext hxval
      show φ x = actTil V₀ V hV g
      rw [show φ x = actTil V₀ V hV ⟨(x : G), hMS x.2⟩ from rfl, hsub]
  rwa [hEq] at hP'

theorem jTbarB_eq_thompsonJ (D : Data G) {V₀ V : Subgroup G} (hV : IsElemAbelian 2 V) :
    jTbarB D V₀ V hV = thompsonJ (barSub V₀ V hV D.T) := by
  unfold jTbarB
  rw [higherElemThompson_zero]
  exact elemThompson_map_subtype_eq_thompsonJ _

@[expose] noncomputable def p29vec (V : Subgroup G) (hV : IsElemAbelian 2 V)
    (w : Vtil ⊥ V hV) : V :=
  ⟨IntMod.val ((TwelveShort.mkTilEquiv V hV).symm w),
    IntMod.val_mem ((TwelveShort.mkTilEquiv V hV).symm w)⟩

theorem mkTil_p29vec {V : Subgroup G} (hV : IsElemAbelian 2 V) (w : Vtil ⊥ V hV) :
    mkTil ⊥ V hV (IntMod.mk hV (p29vec V hV w)) = w := by
  have hx : IntMod.mk hV (p29vec V hV w) = (TwelveShort.mkTilEquiv V hV).symm w := rfl
  rw [hx, ← TwelveShort.mkTilEquiv_apply, MulEquiv.apply_symm_apply]

theorem mkTil_mk_eq_one_iff {V : Subgroup G} (hV : IsElemAbelian 2 V) (v : V) :
    mkTil ⊥ V hV (IntMod.mk hV v) = 1 ↔ (v : G) = 1 := by
  rw [mkTil, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, mem_modNull,
    Subgroup.mem_bot]
  rfl

theorem mkTil_actStab_mk {V : Subgroup G} (hV : IsElemAbelian 2 V) (g : stabTil ⊥ V)
    (v : V) :
    mkTil ⊥ V hV (actStab ⊥ V hV g (IntMod.mk hV v)) =
      actTil ⊥ V hV g (mkTil ⊥ V hV (IntMod.mk hV v)) :=
  (actTil_mk ⊥ V hV g (IntMod.mk hV v)).symm

theorem mkTil_mk_injective {V : Subgroup G} (hV : IsElemAbelian 2 V) :
    Function.Injective (fun v : V => mkTil ⊥ V hV (IntMod.mk hV v)) := by
  intro x y h
  exact (TwelveShort.mkTilEquiv V hV).injective h

theorem centBarLB_p29vec {V L : Subgroup G} (hV : IsElemAbelian 2 V)
    (w : Vtil ⊥ V hV) :
    centBarLB ⊥ V L hV (p29vec V hV w) =
      MulAction.stabilizer (MulAut (Vtil ⊥ V hV)) w ⊓ barSub ⊥ V hV L := by
  simp only [centBarLB, mkTil_p29vec hV w]



theorem seventeen_twentynine_one_bot
    (D : Data G) {V : Subgroup G} (h22 : R17_22At D ⊥ V) (h23 : R17_23At D ⊥ V)
    (h25 : R17_25At D ⊥ V) (h26b2 : R17_26b_2At D ⊥ V) (h61 : UC6.R6_1 D)
    (hHJ : K_HJData) (hLS : K_HJLineScalars) :
    R17_29_1At D ⊥ V := by
  intro L c
  have hV : IsElemAbelian 2 V := c.ctx.hyp125.isElemAbelian
  have hMS : D.M ≤ stabTil (⊥ : Subgroup G) V :=
    le_stabTil c.ctx.hyp125.pairFacts.le_normalizer
      c.ctx.hyp125.pairFacts.le_normalizer₀
  have hLM : L ≤ D.M := c.ctx.mem_calC.1.le
  have hsetup : HJSetup (Vtil ⊥ V hV) (Mbar D.M ⊥ V hV) (barSub ⊥ V hV L) :=
    hjSetup_of_ctx D h22 h23 h25 hHJ c
  obtain ⟨v₁m, v₂m, hv₁m, hv₂m, hcover, hnonconj, hcard₁, hcont, hshape, hinv⟩ :=
    hLS (Vtil ⊥ V hV) (s15_Infra_vtil_sq_eq_one ⊥ V hV)
      (Mbar D.M ⊥ V hV) (barSub ⊥ V hV L) hsetup (barSub ⊥ V hV D.T)
      (barSub_mono ⊥ V hV D.sylowM.le) (isSylowIn_barSub_sylow D hV hMS)
  let v₁ : V := p29vec V hV v₁m
  let v₂ : V := p29vec V hV v₂m
  have hv₁m' : mkTil ⊥ V hV (IntMod.mk hV v₁) = v₁m := mkTil_p29vec hV v₁m
  have hv₂m' : mkTil ⊥ V hV (IntMod.mk hV v₂) = v₂m := mkTil_p29vec hV v₂m
  have hv₁1 : (v₁ : G) ≠ 1 := by
    intro h
    have h1 : v₁ = 1 := Subtype.ext h
    apply hv₁m
    rw [← hv₁m', h1]
    exact map_one _
  have hv₂1 : (v₂ : G) ≠ 1 := by
    intro h
    have h1 : v₂ = 1 := Subtype.ext h
    apply hv₂m
    rw [← hv₂m', h1]
    exact map_one _
  have hv12 : (v₁ : G) ≠ (v₂ : G) := by
    intro h
    have h1 : v₁ = v₂ := Subtype.ext h
    exact hnonconj ⟨1, Subgroup.one_mem _,
      by rw [MulAut.one_apply, ← hv₁m', ← hv₂m', h1]⟩
  have hcardv₂ : Nat.card ↥(MulAction.stabilizer (MulAut (Vtil ⊥ V hV)) v₂m ⊓
      barSub ⊥ V hV L) = 240 := by
    obtain ⟨e⟩ := hshape
    have hA5 : Nat.card (alternatingGroup (Fin 5)) = 60 := by
      rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
      norm_num
    rw [Nat.card_congr e.toEquiv, Nat.card_prod,
      Nat.card_congr (Multiplicative.toAdd : Multiplicative (ZMod 2 × ZMod 2) ≃ _),
      Nat.card_prod, Nat.card_zmod, hA5]
  have hcent₁ : centBarLB ⊥ V L hV v₁ =
      MulAction.stabilizer (MulAut (Vtil ⊥ V hV)) v₁m ⊓ barSub ⊥ V hV L :=
    centBarLB_p29vec hV v₁m
  have hcent₂ : centBarLB ⊥ V L hV v₂ =
      MulAction.stabilizer (MulAut (Vtil ⊥ V hV)) v₂m ⊓ barSub ⊥ V hV L :=
    centBarLB_p29vec hV v₂m
  have hdiv : 5 ∣ Nat.card ↥(MulAction.stabilizer (MulAut (Vtil ⊥ V hV)) v₂m ⊓
      Mbar D.M ⊥ V hV) := by
    have hle : (MulAction.stabilizer (MulAut (Vtil ⊥ V hV)) v₂m ⊓ barSub ⊥ V hV L) ≤
        (MulAction.stabilizer (MulAut (Vtil ⊥ V hV)) v₂m ⊓ Mbar D.M ⊥ V hV) :=
      inf_le_inf_left _ (barSub_mono ⊥ V hV hLM)
    have hdvd := Subgroup.card_dvd_of_le hle
    rw [hcardv₂] at hdvd
    exact dvd_trans (by norm_num : 5 ∣ 240) hdvd
  refine ⟨v₁, v₂, hv₁1, hv₂1, hv12, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro ⟨l, hlL, hconj⟩
    have hlS : l ∈ stabTil (⊥ : Subgroup G) V := hMS (hLM hlL)
    let g : ↥(stabTil (⊥ : Subgroup G) V) := ⟨l, hlS⟩
    have hsub : actStab ⊥ V hV g (IntMod.mk hV v₁) = IntMod.mk hV v₂ := by
      apply IntMod.val_injective
      rw [actStab_apply_val]
      exact hconj
    have hmkT : actTil ⊥ V hV g v₁m = v₂m := by
      rw [← hv₁m', ← hv₂m', ← mkTil_actStab_mk hV g v₁]
      exact congrArg (mkTil ⊥ V hV) hsub
    exact hnonconj ⟨actTil ⊥ V hV g, actTil_mem_barSub ⊥ V hV hlL hlS, hmkT⟩
  · intro v hvne
    have hwne : mkTil ⊥ V hV (IntMod.mk hV v) ≠ 1 := by
      intro h
      exact hvne ((mkTil_mk_eq_one_iff hV v).1 h)
    rcases hcover _ hwne with ⟨lbar, hlbar, heq⟩ | ⟨lbar, hlbar, heq⟩
    · obtain ⟨g, hgL, rfl⟩ := (mem_barSub ⊥ V hV L lbar).1 hlbar
      refine Or.inl ⟨(g : G), hgL, ?_⟩
      have h1 : mkTil ⊥ V hV (actStab ⊥ V hV g (IntMod.mk hV v)) = v₁m := by
        rw [mkTil_actStab_mk]; exact heq
      have h3 : actStab ⊥ V hV g (IntMod.mk hV v) = IntMod.mk hV v₁ := by
        apply mkTil_mk_injective hV
        change mkTil ⊥ V hV (actStab ⊥ V hV g (IntMod.mk hV v)) =
          mkTil ⊥ V hV (IntMod.mk hV v₁)
        rw [h1, hv₁m']
      have h4 : (actStab ⊥ V hV g (IntMod.mk hV v)).val = (v₁ : G) := by
        rw [h3]
        rfl
      rw [actStab_apply_val ⊥ V hV g (IntMod.mk hV v)] at h4
      exact h4
    · obtain ⟨g, hgL, rfl⟩ := (mem_barSub ⊥ V hV L lbar).1 hlbar
      refine Or.inr ⟨(g : G), hgL, ?_⟩
      have h1 : mkTil ⊥ V hV (actStab ⊥ V hV g (IntMod.mk hV v)) = v₂m := by
        rw [mkTil_actStab_mk]; exact heq
      have h3 : actStab ⊥ V hV g (IntMod.mk hV v) = IntMod.mk hV v₂ := by
        apply mkTil_mk_injective hV
        change mkTil ⊥ V hV (actStab ⊥ V hV g (IntMod.mk hV v)) =
          mkTil ⊥ V hV (IntMod.mk hV v₂)
        rw [h1, hv₂m']
      have h4 : (actStab ⊥ V hV g (IntMod.mk hV v)).val = (v₂ : G) := by
        rw [h3]
        rfl
      rw [actStab_apply_val ⊥ V hV g (IntMod.mk hV v)] at h4
      exact h4
  · rw [hcent₁, jTbarB_eq_thompsonJ]
    simpa [inf_comm] using hcont
  · rw [hcent₁]; exact hcard₁
  · rw [hcent₂]
    exact hshape
  · exact h26b2 L c.ctx v₂ (by simpa using hv₂1) (by rw [hv₂m']; exact hdiv)
  · have hp : 2 ≤ CFSG.Open.pRank 5 (D.M ⊓ Subgroup.centralizer ({(v₂ : G)} : Set G)) := by
      have h := h26b2 L c.ctx v₂ (by simpa using hv₂1) (by rw [hv₂m']; exact hdiv)
      rw [CFSG.Foundations.SteinbergCA.pRank_coe_eq_open_pRank Nat.prime_five
        (D.M ⊓ Subgroup.centralizer ({(v₂ : G)} : Set G))] at h
      omega
    have hsig : D.sig = {5} := sig_eq_five_of_J2_ctx D h22 h23 c.ctx
    exact centralizer_le_of_involution_of_two_le_pRank D h61 Nat.prime_five
      (by rw [hsig]; exact Set.mem_singleton 5) (hV.2 (v₂ : G) v₂.2) hv₂1 hp


theorem seventeen_twentynine_one
    (D : Data G) (V₀ V : Subgroup G) (h22 : R17_22At D V₀ V) (h23 : R17_23At D V₀ V)
    (h25 : R17_25At D V₀ V) (h26b2 : R17_26b_2At D V₀ V) (h61 : UC6.R6_1 D) :
    R17_29_1At D V₀ V := by
  have hHJ : K_HJData := k_HJData_holds
  have hLS : K_HJLineScalars := k_HJLineScalars_holds
  intro L c
  obtain ⟨cctx, h0⟩ := c
  cases h0
  exact seventeen_twentynine_one_bot D h22 h23 h25 h26b2 h61 hHJ hLS L ⟨cctx, rfl⟩

theorem seventeen_twentynine_two_bot
    (D : Data G) {V : Subgroup G} (h22 : R17_22At D ⊥ V) (h23 : R17_23At D ⊥ V)
    (h25 : R17_25At D ⊥ V) (hHJ : K_HJData) (hLS : K_HJLineScalars) :
    R17_29_2At D ⊥ V := by
  intro L c v₂ ⟨v₁, hP⟩
  have hV : IsElemAbelian 2 V := c.ctx.hyp125.isElemAbelian
  have hMS : D.M ≤ stabTil (⊥ : Subgroup G) V :=
    le_stabTil c.ctx.hyp125.pairFacts.le_normalizer
      c.ctx.hyp125.pairFacts.le_normalizer₀
  obtain ⟨-, hv₂1, -, -, -, -, -, hshape, -, -⟩ := hP
  have hsetup : HJSetup (Vtil ⊥ V hV) (Mbar D.M ⊥ V hV) (barSub ⊥ V hV L) :=
    hjSetup_of_ctx D h22 h23 h25 hHJ c
  obtain ⟨-, -, -, -, -, -, -, -, -, hinv⟩ :=
    hLS (Vtil ⊥ V hV) (s15_Infra_vtil_sq_eq_one ⊥ V hV)
      (Mbar D.M ⊥ V hV) (barSub ⊥ V hV L) hsetup (barSub ⊥ V hV D.T)
      (barSub_mono ⊥ V hV D.sylowM.le) (isSylowIn_barSub_sylow D hV hMS)
  have hcard : Nat.card ↥(MulAction.stabilizer (MulAut (Vtil ⊥ V hV))
      (mkTil ⊥ V hV (IntMod.mk hV v₂)) ⊓ barSub ⊥ V hV L) = 240 := by
    have h240 : Nat.card ↥(centBarLB ⊥ V L hV v₂) = 240 := by
      obtain ⟨e⟩ := hshape
      have hA5 : Nat.card (alternatingGroup (Fin 5)) = 60 := by
        rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
        norm_num
      rw [Nat.card_congr e.toEquiv, Nat.card_prod,
        Nat.card_congr (Multiplicative.toAdd : Multiplicative (ZMod 2 × ZMod 2) ≃ _),
        Nat.card_prod, Nat.card_zmod, hA5]
    simpa only [centBarLB] using h240
  have hne : mkTil ⊥ V hV (IntMod.mk hV v₂) ≠ 1 := by
    intro h
    exact hv₂1 ((mkTil_mk_eq_one_iff hV v₂).1 h)
  intro t ht ht2 hrk
  have hres := hinv _ hne hcard t ht ht2 hrk
  refine ⟨hres.1, ?_⟩
  rintro H hHF hHidx
  obtain ⟨lbar, hlbar, hlH⟩ := hres.2 H hHF hHidx
  obtain ⟨g, hgL, rfl⟩ := (mem_barSub ⊥ V hV L lbar).1 hlbar
  refine ⟨(g : G), hgL, actStab ⊥ V hV g (IntMod.mk hV v₂), ?_, ?_⟩
  · show (actStab ⊥ V hV g (IntMod.mk hV v₂)).val = (g : G) * (v₂ : G) * (g : G)⁻¹
    rw [actStab_apply_val]
    rfl
  · change mkTil ⊥ V hV (actStab ⊥ V hV g (IntMod.mk hV v₂)) ∈ H
    rw [mkTil_actStab_mk hV g v₂]
    exact hlH

theorem seventeen_twentynine_two
    (D : Data G) (V₀ V : Subgroup G) (h22 : R17_22At D V₀ V) (h23 : R17_23At D V₀ V)
    (h25 : R17_25At D V₀ V) :
    R17_29_2At D V₀ V := by
  have hHJ : K_HJData := k_HJData_holds
  have hLS : K_HJLineScalars := k_HJLineScalars_holds
  intro L c
  obtain ⟨cctx, h0⟩ := c
  cases h0
  exact seventeen_twentynine_two_bot D h22 h23 h25 hHJ hLS L ⟨cctx, rfl⟩


@[expose] noncomputable def gammaOneMod (W : Type) [CommGroup W] (A : Subgroup (MulAut W)) :
    Subgroup W :=
  ⨆ (a : MulAut W) (_ : a ∈ A) (_ : a ≠ 1), fixV (Subgroup.zpowers a)

theorem imgTil_mono {V₀ V : Subgroup G} (hV : IsElemAbelian 2 V)
    {U X : Subgroup G} (h : U ≤ X) :
    imgTil V₀ V hV U ≤ imgTil V₀ V hV X :=
  Subgroup.map_mono (Subgroup.subgroupOf_mono V h)

theorem fixV_actTil_eq_imgTil {V : Subgroup G} (hV : IsElemAbelian 2 V) {a : G}
    (haS : a ∈ stabTil ⊥ V) :
    fixV (Subgroup.zpowers (actTil ⊥ V hV ⟨a, haS⟩)) =
      imgTil ⊥ V hV (V ⊓ Subgroup.centralizer ({a} : Set G)) := by
  ext q
  constructor
  · intro hq
    have hq' : actTil ⊥ V hV ⟨a, haS⟩ q = q :=
      (CFSG.Quasithin.mem_fixV_zpowers_iff_apply).1 hq
    obtain ⟨y, hy⟩ := mkTil_surjective ⊥ V hV q
    refine (mem_imgTil ⊥ V hV _ q).2 ⟨y, ⟨y.val_mem, ?_⟩, hy⟩
    change y.val ∈ Subgroup.centralizer ({a} : Set G)
    rw [mem_centralizer_singleton_iff]
    have h2 : mkTil ⊥ V hV (actStab ⊥ V hV ⟨a, haS⟩ y) = mkTil ⊥ V hV y := by
      rw [show mkTil ⊥ V hV (actStab ⊥ V hV ⟨a, haS⟩ y) =
        actTil ⊥ V hV ⟨a, haS⟩ (mkTil ⊥ V hV y) from
        mkTil_actStab_mk hV ⟨a, haS⟩ y]
      rw [hy]
      exact hq'
    have h3 : actStab ⊥ V hV ⟨a, haS⟩ y = y := mkTil_mk_injective hV h2
    have h4 := congrArg (fun z : IntMod V hV => IntMod.val z) h3
    rw [actStab_apply_val] at h4
    calc y.val * a = (a * y.val * a⁻¹) * a := by rw [h4]
      _ = a * y.val := by group
  · rintro ⟨y, ⟨hyV, hya⟩, hyq⟩
    change y.val ∈ Subgroup.centralizer ({a} : Set G) at hya
    rw [mem_centralizer_singleton_iff] at hya
    rw [CFSG.Quasithin.mem_fixV_zpowers_iff_apply, ← hyq]
    have haey : a * y.val * a⁻¹ = y.val := by
      calc a * y.val * a⁻¹ = (y.val * a) * a⁻¹ := by rw [hya]
        _ = y.val := by group
    have h3 : actStab ⊥ V hV ⟨a, haS⟩ y = y := by
      apply IntMod.val_injective
      rw [actStab_apply_val, haey]
    rw [show actTil ⊥ V hV ⟨a, haS⟩ (mkTil ⊥ V hV y) =
      mkTil ⊥ V hV (actStab ⊥ V hV ⟨a, haS⟩ y) from
      (mkTil_actStab_mk hV ⟨a, haS⟩ y).symm]
    rw [h3]

theorem gammaOneMod_le_imgTil_gammaOneABarB (D : Data G) {V A : Subgroup G}
    (hV : IsElemAbelian 2 V) (hAnorm : A ≤ stabTil ⊥ V) (hAM : A ≤ D.M) :
    gammaOneMod (Vtil ⊥ V hV) (barSub ⊥ V hV A) ≤
      imgTil ⊥ V hV (gammaOneABarB D ⊥ V A) := by
  refine iSup_le fun a => iSup_le fun ha => iSup_le fun ha1 => ?_
  obtain ⟨g, hgA, hga⟩ := (mem_barSub ⊥ V hV A a).1 ha
  have hgS : (g : G) ∈ stabTil ⊥ V := hAnorm hgA
  have hgne : (g : G) ∉ F11.CTilde D.M ⊥ V := by
    rw [uc22p22u_cTilde_bot]
    rintro ⟨-, hgC⟩
    apply ha1
    rw [← hga]
    exact (actTil_eq_one_iff ⊥ V hV g).2 (fun v hv => by
      have hgv : (g : G) * v * (g : G)⁻¹ = v := by
        have hcv := Subgroup.mem_centralizer_iff.1 hgC v hv
        calc (g : G) * v * (g : G)⁻¹ = v * (g : G) * (g : G)⁻¹ := by rw [← hcv]
          _ = v := by group
      rw [Subgroup.mem_bot]
      calc (g : G) * v * (g : G)⁻¹ * v⁻¹ = v * v⁻¹ := by rw [hgv]
        _ = 1 := mul_inv_cancel v)
  have hfix := fixV_actTil_eq_imgTil hV hgS
  rw [← hga, hfix]
  exact imgTil_mono hV (le_iSup₂_of_le (g : G) hgA (le_iSup_of_le hgne le_rfl))

theorem gammaOneABarB_le_V (D : Data G) (V₀ V A : Subgroup G) :
    gammaOneABarB D V₀ V A ≤ V :=
  iSup₂_le fun _ _ => iSup_le fun _ => inf_le_left

theorem mem_commutator_of_mem_commSub_gammaOne (D : Data G) {V A : Subgroup G}
    (hV : IsElemAbelian 2 V) (hAM : A ≤ D.M) (hAnorm : A ≤ stabTil ⊥ V)
    (hΓ : gammaOneMod (Vtil ⊥ V hV) (barSub ⊥ V hV A) ≤
      imgTil ⊥ V hV (gammaOneABarB D ⊥ V A))
    {c : Vtil ⊥ V hV}
    (hc : c ∈ commSub (gammaOneMod (Vtil ⊥ V hV) (barSub ⊥ V hV A)) (barSub ⊥ V hV A))
    {x : V} (hx : mkTil ⊥ V hV (IntMod.mk hV x) = c) :
    (x : G) ∈ ⁅gammaOneABarB D ⊥ V A, A⁆ := by
  have hsq : ∀ z : Vtil ⊥ V hV, z ^ 2 = 1 := s15_Infra_vtil_sq_eq_one ⊥ V hV
  have hinv : ∀ z : Vtil ⊥ V hV, z⁻¹ = z := fun z =>
    inv_eq_of_mul_eq_one_right (by simpa [pow_two] using hsq z)
  have key : ∀ c : Vtil ⊥ V hV,
      c ∈ commSub (gammaOneMod (Vtil ⊥ V hV) (barSub ⊥ V hV A)) (barSub ⊥ V hV A) →
      ∀ x : V, mkTil ⊥ V hV (IntMod.mk hV x) = c →
        (x : G) ∈ ⁅gammaOneABarB D ⊥ V A, A⁆ := by
    intro c hc
    refine Subgroup.closure_induction
      (p := fun c _ => ∀ x : V, mkTil ⊥ V hV (IntMod.mk hV x) = c →
        (x : G) ∈ ⁅gammaOneABarB D ⊥ V A, A⁆) ?_ ?_ ?_ ?_ hc
    · intro c hcgen x hx
      obtain ⟨aM, haM, wVec, hwVec, hgen⟩ := hcgen
      obtain ⟨γ, hγmem, hγmk⟩ := (mem_imgTil ⊥ V hV _ wVec).1 (hΓ hwVec)
      have hγV : IntMod.val γ ∈ V := gammaOneABarB_le_V D ⊥ V A hγmem
      let γv : V := ⟨IntMod.val γ, hγV⟩
      have hγvmk : mkTil ⊥ V hV (IntMod.mk hV γv) = wVec := by
        have hγeq : (IntMod.mk hV γv : IntMod V hV) = γ := Subtype.ext rfl
        rw [hγeq, hγmk]
      obtain ⟨g, hgA, hga⟩ := (mem_barSub ⊥ V hV A aM).1 haM
      have hgS : (g : G) ∈ stabTil ⊥ V := hAnorm hgA
      have hγv2 : (γv : G) * (γv : G) = 1 := by
        simpa [pow_two] using hV.2 (γv : G) γv.2
      have hγvi : (γv : G)⁻¹ = (γv : G) := inv_eq_of_mul_eq_one_right hγv2
      have hgN : (g : G) ∈ Subgroup.normalizer (V : Set G) :=
        stabTil_le_normalizer ⊥ V hgS
      have hconjV : (g : G) * (γv : G) * (g : G)⁻¹ ∈ V :=
        (Subgroup.mem_normalizer_iff.1 hgN (γv : G)).1 γv.2
      let x' : V := ⟨(γv : G) * ((g : G) * (γv : G) * (g : G)⁻¹),
        V.mul_mem γv.2 hconjV⟩
      have hx'val : (x' : G) = ⁅(γv : G), (g : G)⁆ := by
        rw [commutatorElement_def, hγvi]
        show (γv : G) * ((g : G) * (γv : G) * (g : G)⁻¹) =
          (γv : G) * (g : G) * (γv : G) * (g : G)⁻¹
        group
      have hmem : (x' : G) ∈ ⁅gammaOneABarB D ⊥ V A, A⁆ := by
        rw [hx'val]
        exact Subgroup.commutator_mem_commutator hγmem hgA
      have hx'eq : mkTil ⊥ V hV (IntMod.mk hV x') = c := by
        have hx'sub : (IntMod.mk hV x' : IntMod V hV) =
            IntMod.mk hV γv * actStab ⊥ V hV g (IntMod.mk hV γv) := by
          apply IntMod.val_injective
          rw [IntMod.val_mul, actStab_apply_val]
          rfl
        rw [hx'sub, map_mul, mkTil_actStab_mk, hγvmk, hga]
        rw [← hgen, hinv wVec]
        exact mul_comm wVec (aM wVec)
      have hxx' : x = x' := mkTil_mk_injective hV (hx.trans hx'eq.symm)
      rw [hxx']
      exact hmem
    · intro x hx
      have hx1 : (x : G) = 1 := (mkTil_mk_eq_one_iff hV x).1 hx
      rw [hx1]
      exact Subgroup.one_mem _
    · intro c₁ c₂ hc₁ hc₂ ih1 ih2 x hx
      obtain ⟨x₁, hx₁⟩ := mkTil_surjective ⊥ V hV c₁
      have hx₁' : (IntMod.val x₁) ∈ ⁅gammaOneABarB D ⊥ V A, A⁆ := ih1 x₁ hx₁
      have hx₂ : mkTil ⊥ V hV (x₁⁻¹ * IntMod.mk hV x) = c₂ := by
        rw [map_mul, map_inv, hx₁, hx, hinv c₁]
        rw [← mul_assoc, show c₁ * c₁ = 1 from by simpa [pow_two] using hsq c₁]
        exact one_mul c₂
      have hx₂' : (IntMod.val (x₁⁻¹ * IntMod.mk hV x)) ∈
          ⁅gammaOneABarB D ⊥ V A, A⁆ := ih2 _ hx₂
      have hx_eq : (x : G) = (IntMod.val x₁) *
          (IntMod.val (x₁⁻¹ * IntMod.mk hV x)) := by
        rw [IntMod.val_mul, IntMod.val_inv]
        group
        rfl
      rw [hx_eq]
      exact Subgroup.mul_mem _ hx₁' hx₂'
    · intro c₁ hc₁ ih1 x hx
      have hx' : mkTil ⊥ V hV (IntMod.mk hV x) = c₁ := by
        rw [hx, hinv]
      exact ih1 x hx'
  exact key c hc x hx


theorem seventeen_twentynine_three_bot
    (D : Data G) {V : Subgroup G} (h22 : R17_22At D ⊥ V) (h23 : R17_23At D ⊥ V)
    (h25 : R17_25At D ⊥ V) (hHJ : K_HJData)
    (hΓ : K_HJGammaOne) : R17_29_3At D ⊥ V := by
  intro L c v₂ ⟨v₁, hP⟩
  have hV : IsElemAbelian 2 V := c.ctx.hyp125.isElemAbelian
  have hMS : D.M ≤ stabTil (⊥ : Subgroup G) V :=
    le_stabTil c.ctx.hyp125.pairFacts.le_normalizer
      c.ctx.hyp125.pairFacts.le_normalizer₀
  obtain ⟨-, hv₂1, -, -, -, -, -, hshape, -, -⟩ := hP
  have hsetup : HJSetup (Vtil ⊥ V hV) (Mbar D.M ⊥ V hV) (barSub ⊥ V hV L) :=
    hjSetup_of_ctx D h22 h23 h25 hHJ c
  have hcard : Nat.card ↥(MulAction.stabilizer (MulAut (Vtil ⊥ V hV))
      (mkTil ⊥ V hV (IntMod.mk hV v₂)) ⊓ barSub ⊥ V hV L) = 240 := by
    have h240 : Nat.card ↥(centBarLB ⊥ V L hV v₂) = 240 := by
      obtain ⟨e⟩ := hshape
      have hA5 : Nat.card (alternatingGroup (Fin 5)) = 60 := by
        rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
        norm_num
      rw [Nat.card_congr e.toEquiv, Nat.card_prod,
        Nat.card_congr (Multiplicative.toAdd : Multiplicative (ZMod 2 × ZMod 2) ≃ _),
        Nat.card_prod, Nat.card_zmod, hA5]
    simpa only [centBarLB] using h240
  have hne : mkTil ⊥ V hV (IntMod.mk hV v₂) ≠ 1 := by
    intro h
    exact hv₂1 ((mkTil_mk_eq_one_iff hV v₂).1 h)
  intro A hAM hAbarE hAcard hAT
  have hAnorm : A ≤ stabTil ⊥ V := hAM.trans hMS
  have hΓinc : gammaOneMod (Vtil ⊥ V hV) (barSub ⊥ V hV A) ≤
      imgTil ⊥ V hV (gammaOneABarB D ⊥ V A) :=
    gammaOneMod_le_imgTil_gammaOneABarB D hV hAnorm hAM
  obtain ⟨lbar, hlbar, hcomm⟩ :=
    hΓ (Vtil ⊥ V hV) (s15_Infra_vtil_sq_eq_one ⊥ V hV)
      (Mbar D.M ⊥ V hV) (barSub ⊥ V hV L) hsetup (barSub ⊥ V hV D.T)
      (barSub_mono ⊥ V hV D.sylowM.le) (isSylowIn_barSub_sylow D hV hMS)
      (mkTil ⊥ V hV (IntMod.mk hV v₂)) hne hcard
      (barSub ⊥ V hV A) hAT hAbarE hAcard
  obtain ⟨g, hgL, rfl⟩ := (mem_barSub ⊥ V hV L lbar).1 hlbar
  refine ⟨(g : G), hgL, actStab ⊥ V hV g (IntMod.mk hV v₂), ?_, ?_⟩
  · show (actStab ⊥ V hV g (IntMod.mk hV v₂)).val = (g : G) * (v₂ : G) * (g : G)⁻¹
    rw [actStab_apply_val]
    rfl
  · have hmkT : mkTil ⊥ V hV (actStab ⊥ V hV g (IntMod.mk hV v₂)) =
        actTil ⊥ V hV g (mkTil ⊥ V hV (IntMod.mk hV v₂)) :=
      mkTil_actStab_mk hV g v₂
    exact mem_commutator_of_mem_commSub_gammaOne D hV hAM hAnorm hΓinc hcomm hmkT

theorem seventeen_twentynine_three
    (D : Data G) (V₀ V : Subgroup G) (h22 : R17_22At D V₀ V) (h23 : R17_23At D V₀ V)
    (h25 : R17_25At D V₀ V) : R17_29_3At D V₀ V := by
  have hHJ : K_HJData := k_HJData_holds
  have hΓ : K_HJGammaOne := k_HJGammaOne_holds
  intro L c
  obtain ⟨cctx, h0⟩ := c
  cases h0
  exact seventeen_twentynine_three_bot D h22 h23 h25 hHJ hΓ L ⟨cctx, rfl⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
