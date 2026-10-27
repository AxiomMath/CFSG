module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2TwentyNineNorm
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2TwentyNineNormSchur
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2TwentyNineFrameMod
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2TwentyNineFrameCenter
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2TwentyNineFrameOuter
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2TwentyNineFramePSL
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2TwentyNineFrameProd
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2TwentyNineFrameOdd
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2EighteenCfg10
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2EighteenCfg9Idx
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2EighteenMod
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2NineteenCfg10Defs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenTwo
public import CFSG.Quasithin.EmptyFaithful.S151bModule
public import CFSG.Adapters.GeneralizedFitting
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2EighteenCfg4Frame
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2EighteenCfg9Inv
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2NineteenDefs
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Bender1970_18

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.ComponentClassification.OuterAutomorphisms
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

private theorem s16n9b_isPSL_of_isL3 {X : Type} [Group X] (h : IsL3 X 1) : IsPSL 3 2 1 X := by
  rcases h with ⟨-, h⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
  · exact h
  all_goals exact absurd h0 (by norm_num)

noncomputable def s16n9b_wStarConjAt (M V₀ V : Subgroup G) (hV : IsElemAbelian 2 V)
    (L V₁ : Subgroup G) : Set (Subgroup (Vtil V₁ V hV)) :=
  {X | ∃ m ∈ M, X = imgTil V₁ V hV (conjSubgroup (wSub V₀ V hV L) m)}

theorem s16n9b_case9_wStarConjAt_eq (D : Data G) {V₀ V L : Subgroup G} (hV : IsElemAbelian 2 V)
    (hH : Hyp151 D V₀ V L) :
    s16n9b_wStarConjAt D.M V₀ V hV L V₀ =
      conjSubs (Mbar D.M V₀ V hV) (wTil V₀ V hV L) := by
  have hMs : D.M ≤ stabTil V₀ V :=
    le_stabTil hH.hyp125.pairFacts.le_normalizer hH.hyp125.pairFacts.le_normalizer₀
  have himg : imgTil V₀ V hV (wSub V₀ V hV L) = wTil V₀ V hV L := by
    unfold wSub
    rw [imgTil_preTil]
  ext X
  constructor
  · rintro ⟨m, hm, rfl⟩
    rw [s15_Infra_imgTil_conjSubgroup V₀ V (wSub V₀ V hV L) hV (hMs hm), himg]
    exact ⟨(actTil V₀ V hV ⟨m, hMs hm⟩)⁻¹,
      (Mbar D.M V₀ V hV).inv_mem (actTil_mem_barSub V₀ V hV hm (hMs hm)), rfl⟩
  · rintro ⟨g, hg, rfl⟩
    obtain ⟨m, hm, hgm⟩ := (mem_barSub V₀ V hV D.M g).1 hg
    refine ⟨(m : G)⁻¹, D.M.inv_mem hm, ?_⟩
    have hm'inv : (m : G)⁻¹ ∈ stabTil V₀ V := (stabTil V₀ V).inv_mem m.2
    rw [s15_Infra_imgTil_conjSubgroup V₀ V (wSub V₀ V hV L) hV hm'inv, himg]
    have h1 : actTil V₀ V hV ⟨(m : G)⁻¹, hm'inv⟩ = g⁻¹ := by
      rw [show (⟨(m : G)⁻¹, hm'inv⟩ : ↥(stabTil V₀ V)) = m⁻¹ from rfl, map_inv, hgm]
    rw [h1, inv_inv]

private noncomputable def s16n9b_gammaAt (V₀ V L : Subgroup G) (hV : IsElemAbelian 2 V)
    (V₁ : Subgroup G) : ℕ :=
  rk ↥(imgTil V₁ V hV (wSub V₀ V hV L))

private theorem s16n9b_gammaAt_v1Sub (D : Data G) (V₀ V L : Subgroup G)
    (hV : IsElemAbelian 2 V) :
    gamma15 D.M V₀ V hV L = s16n9b_gammaAt V₀ V L hV (v1Sub D.M V₀ V hV L) := rfl

theorem s16n9b_case9_rk_top (D : Data G) (h1217 : R1217 D) {V₀ V L : Subgroup G}
    (hV : IsElemAbelian 2 V) (hH : Hyp151 D V₀ V L) (hV0 : V₀ ≠ ⊥)
    (hne : barSub V₀ V hV L ≠ ⊥) (hs15 : s15 D.M V₀ V hV L = 2)
    (hsum : SumOfNat (fun H U Z => BinaryNaturalSL H U Z 3 1) (lBar V₀ V hV L)
      (wTil V₀ V hV L) ⊥ 3) :
    rk ↥(⊤ : Subgroup (Vtil V₀ V hV)) = 18 := by
  have h1 := mSub_eq_s15_mul_gamma15_add D h1217 hH hV hne
  have h2 := s15_Infra_mSub_eq_rk_imgTil_add V₀ V V hV le_rfl
  rw [s15_Infra_imgTil_top V₀ V hV, inf_eq_right.mpr hH.hyp125.pairFacts.le] at h2
  have hV1 : v1Sub D.M V₀ V hV L = V₀ := v1Sub_of_ne_bot D.M V₀ V hV L hV0
  have hgamma : gamma15 D.M V₀ V hV L = 9 := by
    rw [s16n9b_gammaAt_v1Sub D V₀ V L hV, hV1]
    unfold s16n9b_gammaAt wSub
    rw [imgTil_preTil]
    exact s16c167_rk_natSum3 (s16c167_natSum3_of_sumOfNat hsum)
  rw [hV1] at h1
  rw [hs15, hgamma] at h1
  omega

theorem s16n9b_case9_conjSubs_ncard {D : Data G} {V₀ V L : Subgroup G} (hV : IsElemAbelian 2 V)
    (hind : sSupIndep (conjSubs (Mbar D.M V₀ V hV) (wTil V₀ V hV L)))
    (hsup : sSup (conjSubs (Mbar D.M V₀ V hV) (wTil V₀ V hV L)) = ⊤)
    (hrk : rk ↥(wTil V₀ V hV L) = 9) (hrktop : rk ↥(⊤ : Subgroup (Vtil V₀ V hV)) = 18) :
    (conjSubs (Mbar D.M V₀ V hV) (wTil V₀ V hV L)).ncard = 2 := by
  have hconst : ∀ I ∈ conjSubs (Mbar D.M V₀ V hV) (wTil V₀ V hV L), rk ↥I = 9 := by
    rintro I ⟨g, -, rfl⟩
    rw [rk_map_aut_eq]
    exact hrk
  have h1 : rk ↥(⊤ : Subgroup (Vtil V₀ V hV)) =
      ∑ᶠ U ∈ conjSubs (Mbar D.M V₀ V hV) (wTil V₀ V hV L), rk ↥U := by
    rw [← hsup]
    exact s15_Lin_rk_sSup_eq_finsum hind
  rw [s15_Two_finsum_mem_eq_ncard_mul _ _ 9 (Set.toFinite _) hconst] at h1
  rw [hrktop] at h1
  omega

theorem s16n9b_case9_directSum (D : Data G) (h1217 : R1217 D) {V₀ V L : Subgroup G}
    (hV : IsElemAbelian 2 V) (hH : Hyp151 D V₀ V L) (hV0 : V₀ ≠ ⊥)
    (hne : barSub V₀ V hV L ≠ ⊥) :
    sSupIndep (conjSubs (Mbar D.M V₀ V hV) (wTil V₀ V hV L)) ∧
      sSup (conjSubs (Mbar D.M V₀ V hV) (wTil V₀ V hV L)) = ⊤ := by
  obtain ⟨hind0, hsup0⟩ := fifteen_two_directSum D h1217 hH hV hne
  have hV1 : v1Sub D.M V₀ V hV L = V₀ := v1Sub_of_ne_bot D.M V₀ V hV L hV0
  have hind_at : sSupIndep (s16n9b_wStarConjAt D.M V₀ V hV L (v1Sub D.M V₀ V hV L)) :=
    hind0
  have hsup_at : sSup (s16n9b_wStarConjAt D.M V₀ V hV L (v1Sub D.M V₀ V hV L)) = ⊤ :=
    hsup0
  have hind0' : sSupIndep (s16n9b_wStarConjAt D.M V₀ V hV L V₀) :=
    (congrArg (fun V₁ => sSupIndep (s16n9b_wStarConjAt D.M V₀ V hV L V₁)) hV1).mp hind_at
  have hsup0' : sSup (s16n9b_wStarConjAt D.M V₀ V hV L V₀) = ⊤ :=
    (congrArg (fun V₁ => sSup (s16n9b_wStarConjAt D.M V₀ V hV L V₁) =
      (⊤ : Subgroup (Vtil V₁ V hV))) hV1).mp hsup_at
  rw [s16n9b_case9_wStarConjAt_eq D hV hH] at hind0' hsup0'
  exact ⟨hind0', hsup0'⟩

theorem s16n9b_case9_frame (D : Data G) (h1217 : R1217 D) {V₀ V L : Subgroup G}
    (hV : IsElemAbelian 2 V) (hc : Counterex16 D V₀ V L hV) (hV0 : V₀ ≠ ⊥)
    (h9 : Case168_9 D V₀ V hV L) :
    ∃ Z : Subgroup (MulAut (Vtil V₀ V hV)),
      Nat.card ↥Z = 7 ∧
      (∀ x ∈ Mbar D.M V₀ V hV, Z.map (MulAut.conj x).toMonoidHom = Z) ∧
      (∀ z ∈ Z, ∀ l ∈ lBar V₀ V hV L, z * l = l * z) ∧
      (∀ z ∈ Z, ∀ w ∈ wTil V₀ V hV L, z w ∈ wTil V₀ V hV L) ∧
      (∀ z ∈ Z, z ≠ 1 → ∃ w ∈ wTil V₀ V hV L, z w ≠ w) ∧
      (∀ x ∈ Mbar D.M V₀ V hV, (wTil V₀ V hV L).map x.toMonoidHom = wTil V₀ V hV L →
        (lBar V₀ V hV L).map (MulAut.conj x).toMonoidHom = lBar V₀ V hV L) := by
  have hS : Setting16 D V₀ V L := hc.setting
  obtain ⟨⟨e₀⟩, hL3, hs15, hsum, -⟩ := h9
  have e : ↥(fstarBar D.M V₀ V hV) ≃*
      (Multiplicative (ZMod 7) × ↥(lBar V₀ V hV L) × ↥(lBar V₀ V hV L)) := e₀
  have hM : D.M ≤ normalizer (V : Set G) := hS.hyp16.hyp125.pairFacts.le_normalizer
  have hL : IsPSL 3 2 1 ↥(lBar V₀ V hV L) := s16n9b_isPSL_of_isL3 hL3
  have hcls : Set.ncard {Y : Subgroup (MulAut (Vtil V₀ V hV)) |
      ∃ φ ∈ Mbar D.M V₀ V hV, Y = (barSub V₀ V hV L).map (MulAut.conj φ).toMonoidHom} = 2 := by
    unfold s15 at hs15
    exact hs15
  obtain ⟨hind0', hsup0'⟩ := s16n9b_case9_directSum D h1217 hV hS.hyp151 hV0 hc.ne_bot
  have hrk0 : rk ↥(wTil V₀ V hV L) = 9 :=
    s16c167_rk_natSum3 (s16c167_natSum3_of_sumOfNat hsum)
  have hrktop : rk ↥(⊤ : Subgroup (Vtil V₀ V hV)) = 18 :=
    s16n9b_case9_rk_top D h1217 hV hS.hyp151 hV0 hc.ne_bot hs15 hsum
  have hn2 : (conjSubs (Mbar D.M V₀ V hV) (wTil V₀ V hV L)).ncard = 2 :=
    s16n9b_case9_conjSubs_ncard hV hind0' hsup0' hrk0 hrktop
  obtain ⟨hFX, hFn, hself⟩ := s16c167_cfg10_fstar_facts (Mbar D.M V₀ V hV)
  have hSC := s16c167_isPSL_simpleCentreless hL
  have hperf := s16c167_isPSL_isPerfect hL
  have hout := s16c167_isPSL_outer_solvable hL
  have hev := s16c167_isPSL_even_card hL
  have hOutF : Group.IsSolvable (Outer ↥(Fstar (Mbar D.M V₀ V hV))) :=
    s16c167_frame_outer_cyclic_square_solvable hSC hperf hout e
  have hLX : lBar V₀ V hV L ≤ Mbar D.M V₀ V hV := barSub_mono V₀ V hV hS.hyp151.le
  have hLF : lBar V₀ V hV L ≤ Fstar (Mbar D.M V₀ V hV) :=
    s16c167_frame_le_of_perfect hFX hLX hFn hself hOutF hperf
  have hZcard : Nat.card ↥((Subgroup.center ↥(Fstar (Mbar D.M V₀ V hV))).map
      (Fstar (Mbar D.M V₀ V hV)).subtype) = 7 := by
    rw [s16c167_frame_centerF_card (F := Fstar (Mbar D.M V₀ V hV)) hSC.center e,
      Nat.card_eq_fintype_card,
      Fintype.card_multiplicative, ZMod.card]
  have hZconj := s16c167_frame_centerF_conj (X := Mbar D.M V₀ V hV)
    (F := Fstar (Mbar D.M V₀ V hV)) hFn
  refine ⟨(Subgroup.center ↥(Fstar (Mbar D.M V₀ V hV))).map
    (Fstar (Mbar D.M V₀ V hV)).subtype, hZcard, hZconj, ?_, ?_, ?_, ?_⟩
  · intro z hz l hl
    exact (s16c167_frame_mem_centerF.1 hz).2 l (hLF hl)
  · intro z hz w hw
    refine commSub_top_stable151b (X := lBar V₀ V hV L) (g := z) (fun x hx => ?_) w hw
    have h1 : x * z = z * x := ((s16c167_frame_mem_centerF.1 hz).2 x (hLF hx)).symm
    have h2 : z * x * z⁻¹ = x := by rw [← h1]; group
    rw [h2]
    exact hx
  · exact s16c167_frame_faithful_of_conj_sup (p := 7) (by norm_num) hZcard hZconj
      (U := wTil V₀ V hV L) (X := Mbar D.M V₀ V hV) hsup0'
  · intro x hx hstab
    have hmem : lBar V₀ V hV L ∈ {Y : Subgroup (MulAut (Vtil V₀ V hV)) |
        ∃ φ ∈ Mbar D.M V₀ V hV,
          Y = (lBar V₀ V hV L).map (MulAut.conj φ).toMonoidHom} :=
      ⟨1, (Mbar D.M V₀ V hV).one_mem, by ext y; simp⟩
    have hstab' : (commSub (⊤ : Subgroup (Vtil V₀ V hV)) (lBar V₀ V hV L)).map
        x.toMonoidHom = commSub (⊤ : Subgroup (Vtil V₀ V hV)) (lBar V₀ V hV L) := by
      show (wTil V₀ V hV L).map x.toMonoidHom = wTil V₀ V hV L
      exact hstab
    exact s16c167_normalizes_of_stab (X := Mbar D.M V₀ V hV) (L := lBar V₀ V hV L)
      hcls hn2 (lBar V₀ V hV L) hmem x hx hstab'

theorem s16n9b_natSum3_comm_rank {W : Type} [CommGroup W] [Finite W]
    (hW : ∀ w : W, w ^ 2 = 1) {L : Subgroup (MulAut W)} (hL : IsPSL 3 2 1 ↥L)
    {J : Subgroup W} (hJ : NatSum3 L J) {l : MulAut W} (hl : l ∈ L) (hl1 : l ≠ 1) :
    3 ≤ E3.mQuot J (J ⊓ fixV (Subgroup.zpowers l)) := by
  obtain ⟨I₀, I₁, I₂, hi₀, hi₁, hi₂, hc₀, hc₁, hc₂, h01, h012, rfl⟩ := hJ
  have hmap : ∀ {I : Subgroup W}, (∀ x ∈ L, ∀ v ∈ I, x v ∈ I) →
      I.map l.toMonoidHom = I := by
    intro I hI
    refine le_antisymm ?_ ?_
    · rintro v ⟨u, hu, rfl⟩
      exact hI l hl u hu
    · intro v hv
      exact ⟨l⁻¹ v, hI l⁻¹ (L.inv_mem hl) v hv, mulAut_apply_inv_apply l v⟩
  have hnotle : ∀ {I : Subgroup W}, XMod.IsIrr ↥L I → Nat.card ↥I = 8 →
      (∀ x ∈ L, ∀ v ∈ I, x v ∈ I) → ¬ I ≤ fixV (Subgroup.zpowers l) := by
    intro I hi hc hI hle
    have hfix : ∀ v ∈ I, l v = v := fun v hv => (mem_fixV_zpowers l v).mp (hle hv)
    exact hl1 (rank3_inj hL hI (s16c167_norm_irr_nontrivial hi hc) l hl hfix)
  exact s16c167_three_le_mQuot_of_blocks hW l h01 h012
    (hmap fun x hx v hv => hi₀.1 ⟨x, hx⟩ v hv)
    (hmap fun x hx v hv => hi₁.1 ⟨x, hx⟩ v hv)
    (hmap fun x hx v hv => hi₂.1 ⟨x, hx⟩ v hv)
    (hnotle hi₀ hc₀ fun x hx v hv => hi₀.1 ⟨x, hx⟩ v hv)
    (hnotle hi₁ hc₁ fun x hx v hv => hi₁.1 ⟨x, hx⟩ v hv)
    (hnotle hi₂ hc₂ fun x hx v hv => hi₂.1 ⟨x, hx⟩ v hv)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
