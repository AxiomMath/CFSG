module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenNineBCase9A
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2EighteenCase9
public import CFSG.RankThree.PartOne.S11d.OutAbstract

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.ComponentClassification.OuterAutomorphisms
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

@[expose] noncomputable def s16t_wStarConjAt (M V₀ V : Subgroup G) (hV : IsElemAbelian 2 V)
    (L V₁ : Subgroup G) : Set (Subgroup (Vtil V₁ V hV)) :=
  {X | ∃ m ∈ M, X = imgTil V₁ V hV (conjSubgroup (wSub V₀ V hV L) m)}

private theorem s16t_wStarConjAt_eq (D : Data G) {V₀ V L : Subgroup G} (hV : IsElemAbelian 2 V)
    (hH : Hyp151 D V₀ V L) :
    s16t_wStarConjAt D.M V₀ V hV L V₀ = conjSubs (Mbar D.M V₀ V hV) (wTil V₀ V hV L) := by
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

private noncomputable def s16t_gammaAt (V₀ V L : Subgroup G) (hV : IsElemAbelian 2 V)
    (V₁ : Subgroup G) : ℕ :=
  rk ↥(imgTil V₁ V hV (wSub V₀ V hV L))

private theorem s16t_gammaAt_v1Sub (D : Data G) (V₀ V L : Subgroup G)
    (hV : IsElemAbelian 2 V) :
    gamma15 D.M V₀ V hV L = s16t_gammaAt V₀ V L hV (v1Sub D.M V₀ V hV L) := rfl

theorem s16t_case9_directSum (D : Data G) (h1217 : R1217 D) {V₀ V L : Subgroup G}
    (hV : IsElemAbelian 2 V) (hH : Hyp151 D V₀ V L) (hv1 : v1Sub D.M V₀ V hV L = V₀)
    (hne : barSub V₀ V hV L ≠ ⊥) :
    sSupIndep (conjSubs (Mbar D.M V₀ V hV) (wTil V₀ V hV L)) ∧
      sSup (conjSubs (Mbar D.M V₀ V hV) (wTil V₀ V hV L)) = ⊤ := by
  obtain ⟨hind0, hsup0⟩ := fifteen_two_directSum D h1217 hH hV hne
  have hind_at : sSupIndep (s16t_wStarConjAt D.M V₀ V hV L (v1Sub D.M V₀ V hV L)) :=
    hind0
  have hsup_at : sSup (s16t_wStarConjAt D.M V₀ V hV L (v1Sub D.M V₀ V hV L)) = ⊤ :=
    hsup0
  have hind0' : sSupIndep (s16t_wStarConjAt D.M V₀ V hV L V₀) :=
    (congrArg (fun V₁ => sSupIndep (s16t_wStarConjAt D.M V₀ V hV L V₁)) hv1).mp hind_at
  have hsup0' : sSup (s16t_wStarConjAt D.M V₀ V hV L V₀) = ⊤ :=
    (congrArg (fun V₁ => sSup (s16t_wStarConjAt D.M V₀ V hV L V₁) =
      (⊤ : Subgroup (Vtil V₁ V hV))) hv1).mp hsup_at
  rw [s16t_wStarConjAt_eq D hV hH] at hind0' hsup0'
  exact ⟨hind0', hsup0'⟩

theorem s16t_case9_rk_top (D : Data G) (h1217 : R1217 D) {V₀ V L : Subgroup G}
    (hV : IsElemAbelian 2 V) (hH : Hyp151 D V₀ V L) (hv1 : v1Sub D.M V₀ V hV L = V₀)
    (hne : barSub V₀ V hV L ≠ ⊥) (hs15 : s15 D.M V₀ V hV L = 2)
    (hsum : SumOfNat (fun H U Z => BinaryNaturalSL H U Z 3 1) (lBar V₀ V hV L)
      (wTil V₀ V hV L) ⊥ 3) :
    rk ↥(⊤ : Subgroup (Vtil V₀ V hV)) = 18 := by
  have h1 := mSub_eq_s15_mul_gamma15_add D h1217 hH hV hne
  have h2 := s15_Infra_mSub_eq_rk_imgTil_add V₀ V V hV le_rfl
  rw [s15_Infra_imgTil_top V₀ V hV, inf_eq_right.mpr hH.hyp125.pairFacts.le] at h2
  have hgamma : gamma15 D.M V₀ V hV L = 9 := by
    rw [s16t_gammaAt_v1Sub D V₀ V L hV, hv1]
    unfold s16t_gammaAt wSub
    rw [imgTil_preTil]
    exact s16c167_rk_natSum3 (s16c167_natSum3_of_sumOfNat hsum)
  rw [hv1] at h1
  rw [hs15, hgamma] at h1
  omega

theorem s16t_case9_frame (D : Data G) (h1217 : R1217 D) {V₀ V L : Subgroup G}
    (hV : IsElemAbelian 2 V) (hc : Counterex16 D V₀ V L hV) (hv1 : v1Sub D.M V₀ V hV L = V₀)
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
  have hL : IsPSL 3 2 1 ↥(lBar V₀ V hV L) := s16c167_isPSL_of_isL3 hL3
  have hcls : Set.ncard {Y : Subgroup (MulAut (Vtil V₀ V hV)) |
      ∃ φ ∈ Mbar D.M V₀ V hV, Y = (barSub V₀ V hV L).map (MulAut.conj φ).toMonoidHom} = 2 := by
    unfold s15 at hs15
    exact hs15
  obtain ⟨hind0', hsup0'⟩ := s16t_case9_directSum D h1217 hV hS.hyp151 hv1 hc.ne_bot
  have hrk0 : rk ↥(wTil V₀ V hV L) = 9 :=
    s16c167_rk_natSum3 (s16c167_natSum3_of_sumOfNat hsum)
  have hrktop : rk ↥(⊤ : Subgroup (Vtil V₀ V hV)) = 18 :=
    s16t_case9_rk_top D h1217 hV hS.hyp151 hv1 hc.ne_bot hs15 hsum
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

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
