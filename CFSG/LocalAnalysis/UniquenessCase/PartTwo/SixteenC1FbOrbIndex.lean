module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1FbSyl
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC8Lift
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC23Unique

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

private theorem s16c1_actTil_fix_of_mem_centralizer {V₀ V : Subgroup G}
    {hV : IsElemAbelian 2 V} {x : IntMod V hV} {g : stabTil V₀ V}
    (hg : (g : G) ∈ centralizer ({x.val} : Set G)) :
    actTil V₀ V hV g (mkTil V₀ V hV x) = mkTil V₀ V hV x := by
  have hcomm : (g : G) * x.val * (g : G)⁻¹ = x.val := by
    have hc := Subgroup.mem_centralizer_singleton_iff.mp hg
    calc (g : G) * x.val * (g : G)⁻¹ = x.val * (g : G) * (g : G)⁻¹ := by rw [hc]
      _ = x.val := by group
  have hact : actStab V₀ V hV g x = x := by
    apply IntMod.val_injective
    rw [actStab_apply_val, hcomm]
  rw [actTil_mk, hact]

theorem s16c1_relIndex_T_cent_le_four {D : Data G} {V₀ V L : Subgroup G}
    {hV : IsElemAbelian 2 V} (hS : Sect16 D V₀ V L hV) {x : IntMod V hV}
    (hx : Setup1645 D V hV x)
    (hodd : Odd ((ptCent (Mbar D.M V₀ V hV) (mkTil V₀ V hV x)).relIndex (Mbar D.M V₀ V hV))) :
    (D.T ⊓ centralizer ({x.val} : Set G)).relIndex D.T ≤ 4 := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set w : Vtil V₀ V hV := mkTil V₀ V hV x with hw
  set P : Subgroup (MulAut (Vtil V₀ V hV)) :=
    ptCent (Mbar D.M V₀ V hV) w with hP
  set R : Subgroup G := preBarSub D.M V₀ V hV P with hR
  have hMs : D.M ≤ stabTil V₀ V := s16c1_M_le_stabTil hS
  have hT : IsSylowIn 2 D.T D.M := CFSG.ABGLocalTools.isSylowOf_iff.1 D.sylowM
  have hRrel : R.relIndex D.M = P.relIndex (Mbar D.M V₀ V hV) := by
    let f : ↥D.M →* MulAut (Vtil V₀ V hV) :=
      (actTil V₀ V hV).comp (Subgroup.inclusion hMs)
    have hfr : f.range = Mbar D.M V₀ V hV := by
      dsimp only [f]
      rw [MonoidHom.range_comp, Subgroup.inclusion_range]
      rfl
    have hcomap : R.subgroupOf D.M = P.comap f := by
      ext g
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_comap]
      constructor
      · intro hg
        rw [hR] at hg
        obtain ⟨-, h, hh⟩ := (mem_preBarSub D.M V₀ V hV P).1 hg
        rw [show f g = actTil V₀ V hV ⟨(g : G), hMs g.2⟩ from rfl]
        rw [show (⟨(g : G), hMs g.2⟩ : ↥(stabTil V₀ V)) = ⟨(g : G), h⟩ from Subtype.ext rfl]
        exact hh
      · intro hg
        rw [hR]
        refine (mem_preBarSub D.M V₀ V hV P).2 ⟨g.2, hMs g.2, ?_⟩
        rwa [show f g = actTil V₀ V hV ⟨(g : G), hMs g.2⟩ from rfl] at hg
    change (R.subgroupOf D.M).index = _
    rw [hcomap, Subgroup.index_comap, hfr]
  have hRodd : Odd (R.relIndex D.M) := by
    rw [hRrel]
    simpa only [← hw, ← hP] using hodd
  have hRM : R ≤ D.M := by rw [hR]; exact inf_le_left
  have hA_le_R : D.M ⊓ centralizer ({x.val} : Set G) ≤ R := by
    intro g hg
    obtain ⟨hgM, hgC⟩ := Subgroup.mem_inf.1 hg
    rw [hR]
    refine (mem_preBarSub D.M V₀ V hV P).2 ⟨hgM, hMs hgM, ?_⟩
    rw [hP]
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · exact actTil_mem_barSub V₀ V hV hgM (hMs hgM)
    · rw [MulAction.mem_stabilizer_iff, MulAut.smul_def, hw]
      exact s16c1_actTil_fix_of_mem_centralizer (g := ⟨g, hMs hgM⟩) hgC
  have hRmove : ∀ r ∈ R, r * x.val * r⁻¹ * (x.val)⁻¹ ∈ V₀ := by
    intro r hr
    rw [hR] at hr
    obtain ⟨-, h, hh⟩ := (mem_preBarSub D.M V₀ V hV P).1 hr
    have hfix : actTil V₀ V hV ⟨r, h⟩ w = w := by
      rw [hP] at hh
      have hstab := (Subgroup.mem_inf.1 hh).2
      rwa [MulAction.mem_stabilizer_iff, MulAut.smul_def] at hstab
    have h1 : mkTil V₀ V hV (actStab V₀ V hV ⟨r, h⟩ x) = mkTil V₀ V hV x := by
      rw [← actTil_mk, ← hw]
      exact hfix
    rw [mkTil_eq_iff, actStab_apply_val] at h1
    exact h1
  have hc8 : (R ⊓ centralizer ({x.val} : Set G)).relIndex R ≤ Nat.card V₀ :=
    c8_relIndex_inf_centralizer_le (Y := R) (U := V₀) (v := x.val) hRmove
  have hARC : (D.M ⊓ centralizer ({x.val} : Set G)).relIndex R ≤ 4 := by
    have hRMC : R ⊓ centralizer ({x.val} : Set G) =
        D.M ⊓ centralizer ({x.val} : Set G) :=
      le_antisymm (le_inf (inf_le_left.trans hRM) inf_le_right)
        (le_inf hA_le_R inf_le_right)
    have h4 := c23_card_v0_le_four D hS.setting.hyp16
    calc (D.M ⊓ centralizer ({x.val} : Set G)).relIndex R
        = (R ⊓ centralizer ({x.val} : Set G)).relIndex R := by rw [hRMC]
      _ ≤ Nat.card V₀ := hc8
      _ ≤ 4 := h4
  have hneM : Nat.card D.M ≠ 0 := Nat.card_ne_zero.mpr ⟨⟨1, D.M.one_mem⟩, inferInstance⟩
  have hneA : Nat.card ↥(D.M ⊓ centralizer ({x.val} : Set G)) ≠ 0 :=
    Nat.card_ne_zero.mpr
      ⟨⟨1, (D.M ⊓ centralizer ({x.val} : Set G)).one_mem⟩, inferInstance⟩
  have hb_dvd_a : Nat.card ↥(D.M ⊓ centralizer ({x.val} : Set G)) ∣ Nat.card D.M :=
    Subgroup.card_dvd_of_le inf_le_left
  have hle : (Nat.card ↥(D.M ⊓ centralizer ({x.val} : Set G))).factorization 2 ≤
      (Nat.card D.M).factorization 2 :=
    (Nat.factorization_le_iff_dvd hneA hneM).mpr hb_dvd_a 2
  have hfactor : (D.T ⊓ centralizer ({x.val} : Set G)).relIndex D.T =
      2 ^ ((Nat.card D.M).factorization 2 -
        (Nat.card ↥(D.M ⊓ centralizer ({x.val} : Set G))).factorization 2) := by
    have hrel : (D.T ⊓ centralizer ({x.val} : Set G)).relIndex D.T =
        Nat.card D.T / Nat.card ↥(D.T ⊓ centralizer ({x.val} : Set G)) := by
      have h := Subgroup.relIndex_mul_card
        (H := D.T ⊓ centralizer ({x.val} : Set G)) (K := D.T)
      rw [inf_of_le_left inf_le_left] at h
      exact Nat.eq_div_of_mul_eq_right
        (Nat.card_ne_zero.mpr
          ⟨⟨1, (D.T ⊓ centralizer ({x.val} : Set G)).one_mem⟩, inferInstance⟩)
        (by rw [mul_comm] at h; exact h)
    rw [hrel, hT.card_eq, hx.sylow.card_eq, Nat.pow_div hle (by norm_num)]
  have hfacAM : (Nat.card D.M / Nat.card ↥(D.M ⊓ centralizer ({x.val} : Set G))).factorization 2 =
      (Nat.card D.M).factorization 2 -
        (Nat.card ↥(D.M ⊓ centralizer ({x.val} : Set G))).factorization 2 := by
    rw [Nat.factorization_div hb_dvd_a, Finsupp.tsub_apply]
  have hrelAM : (D.M ⊓ centralizer ({x.val} : Set G)).relIndex D.M =
      Nat.card D.M / Nat.card ↥(D.M ⊓ centralizer ({x.val} : Set G)) := by
    have h := Subgroup.relIndex_mul_card
      (H := D.M ⊓ centralizer ({x.val} : Set G)) (K := D.M)
    rw [inf_of_le_left inf_le_left] at h
    exact Nat.eq_div_of_mul_eq_right hneA (by rw [mul_comm] at h; exact h)
  have hfacR : (R.relIndex D.M).factorization 2 = 0 :=
    Nat.factorization_eq_zero_of_not_dvd (by
      rw [← even_iff_two_dvd]
      exact Nat.not_even_iff_odd.mpr hRodd)
  have hneAR : (D.M ⊓ centralizer ({x.val} : Set G)).relIndex R ≠ 0 :=
    Subgroup.index_ne_zero_of_finite
  have hneRM : R.relIndex D.M ≠ 0 :=
    Subgroup.index_ne_zero_of_finite
  have hfacAM2 : ((D.M ⊓ centralizer ({x.val} : Set G)).relIndex D.M).factorization 2 =
      ((D.M ⊓ centralizer ({x.val} : Set G)).relIndex R).factorization 2 := by
    rw [← Subgroup.relIndex_mul_relIndex (D.M ⊓ centralizer ({x.val} : Set G)) R D.M
      hA_le_R hRM]
    rw [Nat.factorization_mul hneAR hneRM, Finsupp.add_apply, hfacR, add_zero]
  have hfacAR : ((D.M ⊓ centralizer ({x.val} : Set G)).relIndex R).factorization 2 =
      (Nat.card D.M).factorization 2 -
        (Nat.card ↥(D.M ⊓ centralizer ({x.val} : Set G))).factorization 2 := by
    rw [← hfacAM2, hrelAM, hfacAM]
  calc (D.T ⊓ centralizer ({x.val} : Set G)).relIndex D.T
      = 2 ^ ((Nat.card D.M).factorization 2 -
          (Nat.card ↥(D.M ⊓ centralizer ({x.val} : Set G))).factorization 2) := hfactor
    _ = 2 ^ (((D.M ⊓ centralizer ({x.val} : Set G)).relIndex R).factorization 2) := by
          rw [hfacAR]
    _ ≤ (D.M ⊓ centralizer ({x.val} : Set G)).relIndex R := Nat.ordProj_le 2 hneAR
    _ ≤ 4 := hARC

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
