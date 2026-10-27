module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1G47Base
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1G47Perp
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1Forty7aCommon
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Sixteen21CasesB
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1F431Lift
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1FbIndex
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1FbOrbTil
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1Kernel
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1G47Quad

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]


theorem s16c1_card_imgTil_mul {V₀ V U : Subgroup G} (hV : IsElemAbelian 2 V) (hU : U ≤ V) :
    Nat.card ↥(imgTil V₀ V hV U) * Nat.card ↥(U ⊓ V₀) = Nat.card ↥U := by
  have hker : (mkTil V₀ V hV).ker = modNull V₀ V hV := QuotientGroup.ker_mk' _
  have hcardU : Nat.card ↥(intSub V hV U) = Nat.card ↥U :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hU).toEquiv
  have hcardI : Nat.card ↥(modNull V₀ V hV ⊓ intSub V hV U) = Nat.card ↥(U ⊓ V₀) := by
    have heq : modNull V₀ V hV ⊓ intSub V hV U = intSub V hV (U ⊓ V₀) := by
      ext x
      rw [Subgroup.mem_inf, mem_modNull, mem_intSub, mem_intSub, Subgroup.mem_inf]
      tauto
    rw [heq]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_trans inf_le_left hU)).toEquiv
  have hmain := Subgroup.relIndex_mul_card (H := (mkTil V₀ V hV).ker) (K := intSub V hV U)
  rw [Subgroup.relIndex_ker, hker, hcardI, hcardU] at hmain
  exact hmain

theorem s16c1_card_vTil_le_two_mul {V₀ V U : Subgroup G} (hV : IsElemAbelian 2 V) (hV₀ : V₀ ≤ V)
    (hU : U ≤ V) (hcard : Nat.card ↥V ≤ 2 * Nat.card ↥U) :
    Nat.card (Vtil V₀ V hV) ≤ 2 * Nat.card ↥(imgTil V₀ V hV U) := by
  have h1 := s16c1_card_imgTil_mul (V₀ := V₀) hV hU
  have h2 := s16c1_card_imgTil_mul (V₀ := V₀) hV (le_refl V)
  rw [s15_Infra_imgTil_top, Subgroup.card_top, inf_eq_right.2 hV₀] at h2
  have h3 : Nat.card ↥(U ⊓ V₀) ≤ Nat.card ↥V₀ := Subgroup.card_le_of_le inf_le_right
  have hpos : 0 < Nat.card ↥V₀ := Nat.card_pos
  by_contra hlt
  push Not at hlt
  have h4 : 2 * Nat.card ↥(imgTil V₀ V hV U) * Nat.card ↥V₀ <
      Nat.card (Vtil V₀ V hV) * Nat.card ↥V₀ := Nat.mul_lt_mul_of_pos_right hlt hpos
  have h5 : Nat.card ↥(imgTil V₀ V hV U) * Nat.card ↥(U ⊓ V₀) ≤
      Nat.card ↥(imgTil V₀ V hV U) * Nat.card ↥V₀ := Nat.mul_le_mul_left _ h3
  nlinarith

theorem s16c1_stable_imgTil_uOne {V₀ V : Subgroup G} {hV : IsElemAbelian 2 V}
    (x : IntMod V hV) (L : Subgroup G) :
    StableUnder (barSub V₀ V hV (centralizer ({x.val} : Set G) ⊓ L))
      (imgTil V₀ V hV (uOne V x.val)) := by
  intro φ hφ q hq
  obtain ⟨g, hg, rfl⟩ := (mem_barSub V₀ V hV _ φ).1 hφ
  obtain ⟨y, hyU, rfl⟩ := (mem_imgTil V₀ V hV _ q).1 hq
  rw [actTil_mk]
  refine (mem_imgTil V₀ V hV _ _).2 ⟨actStab V₀ V hV g y, ?_, rfl⟩
  have hgH : (g : G) ∈ centralizer ({x.val} : Set G) := hg.1
  have hyQ : y.val ∈ conjSubgroup (pCoreOf 2 (centralizer ({x.val} : Set G))) (g : G) := by
    rw [s16c1_conjSubgroup_pCoreOf_self _ hgH]
    exact hyU.2
  have hyV : (actStab V₀ V hV g y).val ∈ V := (actStab V₀ V hV g y).val_mem
  rw [actStab_apply_val] at hyV ⊢
  exact Subgroup.mem_inf.2 ⟨hyV, mem_conjSubgroup_iff.1 hyQ⟩

theorem s16c1_barSub_xInf_eq_ptCent {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (hL : L ≤ stabTil V₀ V) (x : IntMod V hV)
    (he16 : IsE16A5 ↥(barSub V₀ V hV (xInf L x.val)))
    (h960 : Nat.card ↥(ptCent (lBar V₀ V hV L) (mkTil V₀ V hV x)) = 960) :
    barSub V₀ V hV (xInf L x.val) = ptCent (lBar V₀ V hV L) (mkTil V₀ V hV x) := by
  haveI : Finite (MulAut (Vtil V₀ V hV)) := MulEquiv.finite_left
  have hle : barSub V₀ V hV (xInf L x.val) ≤
      ptCent (lBar V₀ V hV L) (mkTil V₀ V hV x) :=
    (barSub_mono V₀ V hV (perfectCore_le _)).trans (s16c1_barSub_cent_le hL x)
  haveI : Finite ↥(ptCent (lBar V₀ V hV L) (mkTil V₀ V hV x)) := Subtype.finite
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [h960, s16c1_card_of_isE16A5 he16])

theorem s16c1_perp_le_imgTil_uOne (D : Data G) (hkit : OmegaKit) (h41 : R16_41 D)
    {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V} {x : IntMod V hV}
    (ctx : G47Ctx D V₀ V L hV x) (hcard : Nat.card ↥V = 2 * Nat.card ↥(uOne V x.val))
    {Q : Vtil V₀ V hV → ZMod 2} (hQ : IsMinusQuadF2 Q)
    (hQi : QuadInvariant Q (lBar V₀ V hV L)) :
    ∀ y : Vtil V₀ V hV, polarQ Q (mkTil V₀ V hV x) y = 0 →
      y ∈ imgTil V₀ V hV (uOne V x.val) := by
  obtain ⟨hS, hc, hx, hsing, -, he16, -, -⟩ := ctx
  have hP := hS.setting.hyp151.hyp125.pairFacts
  have hz1 : mkTil V₀ V hV x ≠ 1 := s16c1_mkTil_ne_one hS hx
  have hQz : Q (mkTil V₀ V hV x) = 0 := hsing Q hQ hQi
  have h960 : Nat.card ↥(ptCent (lBar V₀ V hV L) (mkTil V₀ V hV x)) = 960 :=
    s16c1_card_of_isE16A5 (((h41 V₀ V L hV hS hc).2 Q hQ hQi).1 _ hz1 hQz)
  have hbar := s16c1_barSub_xInf_eq_ptCent (s16c1_le_stabTil D hS) x he16 h960
  have hstab : StableUnder (ptCent (lBar V₀ V hV L) (mkTil V₀ V hV x))
      (imgTil V₀ V hV (uOne V x.val)) := by
    intro φ hφ q hq
    rw [← hbar] at hφ
    exact s16c1_stable_imgTil_uOne x L φ (barSub_mono V₀ V hV (perfectCore_le _) hφ) q hq
  have hW64 : Nat.card (Vtil V₀ V hV) = 64 := by
    have h := Sixteen21.card_vTil_of_case1 (V₀ := V₀) hV hc
    simpa using h
  have hIrr := (hkit (Vtil V₀ V hV) (lBar V₀ V hV L) hc.2.1).2.1 _ hz1 h960
  have hUcard : 64 ≤ 2 * Nat.card ↥(imgTil V₀ V hV (uOne V x.val)) := by
    have h := s16c1_card_vTil_le_two_mul (V₀ := V₀) hV hP.le
      (inf_le_left : uOne V x.val ≤ V) hcard.le
    rwa [hW64] at h
  refine s16c1_perp_le_of_stable hQ.1
    (fun w => by rw [← pow_two]; exact s15_Infra_vtil_sq_eq_one V₀ V hV w) hW64
    (C := ptCent (lBar V₀ V hV L) (mkTil V₀ V hV x)) (fun h hh w => hQi h hh.1 w) hz1 ?_
    hIrr hstab hUcard
  intro φ hφ
  simpa [MulAut.smul_def] using MulAction.mem_stabilizer_iff.mp hφ.2

theorem s16c1_cTilde_of_cent_uOne (D : Data G) (hkit : OmegaKit) (hkitB : OmegaKitB)
    (hkitC : OmegaKitC) (h41 : R16_41 D) {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    {x : IntMod V hV} (ctx : G47Ctx D V₀ V L hV x)
    (hcard : Nat.card ↥V = 2 * Nat.card ↥(uOne V x.val)) {m : G} (hmM : m ∈ D.M)
    (hm : ∀ u ∈ uOne V x.val, m * u * m⁻¹ = u) : m ∈ F11.CTilde D.M V₀ V := by
  have hS := ctx.sect
  have hc := ctx.caseOne
  obtain ⟨Q, hQ, hQi⟩ := (h41 V₀ V L hV hS hc).1
  have hP := hS.setting.hyp151.hyp125.pairFacts
  have hz1 : mkTil V₀ V hV x ≠ 1 := s16c1_mkTil_ne_one hS ctx.setup
  have hQz : Q (mkTil V₀ V hV x) = 0 := ctx.sing Q hQ hQi
  have hms : m ∈ stabTil V₀ V := le_stabTil hP.le_normalizer hP.le_normalizer₀ hmM
  have hσN : actTil V₀ V hV ⟨m, hms⟩ ∈
      normalizer (lBar V₀ V hV L : Set (MulAut (Vtil V₀ V hV))) :=
    s16c1_Mbar_le_normalizer hkitB hS hc (actTil_mem_barSub V₀ V hV hmM hms)
  have hσQ : ∀ w, Q (actTil V₀ V hV ⟨m, hms⟩ w) = Q w :=
    (hkitC (Vtil V₀ V hV) (lBar V₀ V hV L) hc.2.1).2.1 Q hQ hQi _ hσN
  have hperp := s16c1_perp_le_imgTil_uOne D hkit h41 ctx hcard hQ hQi
  have hfix : ∀ y : Vtil V₀ V hV, polarQ Q (mkTil V₀ V hV x) y = 0 →
      actTil V₀ V hV ⟨m, hms⟩ y = y := by
    intro y hy
    obtain ⟨u, hu, rfl⟩ := (mem_imgTil V₀ V hV _ y).1 (hperp y hy)
    rw [actTil_mk]
    congr 1
    apply IntMod.val_injective
    rw [actStab_apply_val]
    exact hm u.val hu
  have hone : actTil V₀ V hV ⟨m, hms⟩ = 1 :=
    s16c1_no_singular_transvection hQ.1
      (fun w => by rw [← pow_two]; exact s15_Infra_vtil_sq_eq_one V₀ V hV w) _ hσQ hz1 hQz hfix
  have htriv : ∀ v ∈ V, m * v * m⁻¹ * v⁻¹ ∈ V₀ :=
    (actTil_eq_one_iff V₀ V hV ⟨m, hms⟩).1 hone
  exact (CFSG.LocalAnalysis.WeakClosure81.mem_cTilde_iff_centralizes hV hP.le_normalizer
    hP.le_normalizer₀).2 ⟨hmM, htriv⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
