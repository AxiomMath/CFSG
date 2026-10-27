module

public import CFSG.Timmesfeld.ARS.CaseBB2
public import CFSG.Timmesfeld.RankTwo.LevisBRankOne

public section

namespace CFSG.Timmesfeld.ARS

open scoped commutatorElement Pointwise
open CFSG.LieType.Universal CFSG.LieType.Steinberg Matrix

namespace CaseB

variable {G : Type} [Group G] {R : Set (Subgroup G)} {F : Type} [Field F]
  {Ψ : SpecialLinearGroup (Fin 4) F →* G}

variable (Ψ) in
noncomputable abbrev piT [CharP F 2] : G := Ψ (pm σT)

variable (R Ψ) in
@[expose] noncomputable def xU' [Finite F] [CharP F 2] (ι : (Fin 1 → F) → G) (t : F) : G :=
  piT Ψ * xU R Ψ ι t * (piT Ψ)⁻¹

variable (R Ψ) in
noncomputable abbrev ptD [Finite F] [CharP F 2] (ι : (Fin 1 → F) → G) (a : F) : Subgroup G :=
  conjSub (xg Ψ 1 3) (xU R Ψ ι a)

section PiT

variable [CharP F 2]

theorem piT_mul_self : piT Ψ * piT Ψ = 1 := by
  rw [← map_mul, pm_mul, show σT * σT = 1 from by decide,
    show (pm 1 : SpecialLinearGroup (Fin 4) F) = 1 from Subtype.ext (by
      rw [coe_pm, SpecialLinear.signedPerm_one]
      exact Matrix.diagonal_one), map_one]

theorem piT_inv : (piT Ψ)⁻¹ = piT Ψ := inv_eq_of_mul_eq_one_left piT_mul_self

theorem piT_conj_xs {i j : Fin 4} (hij : i ≠ j) (s : F) :
    piT Ψ * xs Ψ hij s * (piT Ψ)⁻¹ = xs Ψ (σT.injective.ne hij) s := by
  rw [xs, xs, ← map_inv, ← map_mul, ← map_mul, pm_mul_transvection_mul_inv]

theorem piT_conj_xs13 (s : F) : piT Ψ * xs Ψ ne13 s * (piT Ψ)⁻¹ = xs Ψ ne02 s := by
  rw [piT_conj_xs]
  rfl

theorem piT_conj_xs02 (s : F) : piT Ψ * xs Ψ ne02 s * (piT Ψ)⁻¹ = xs Ψ ne13 s := by
  rw [piT_conj_xs]
  rfl

theorem piT_conj_hid (h : Hyp G R) (hS : Skel R Ψ) {n : G} (hn : n ∈ hid R Ψ) :
    piT Ψ * n * (piT Ψ)⁻¹ = n := by
  have e1 := conjSub_hid_swap01 h hS
  have e2 := conjSub_hid_swap23 h hS
  have hc : ∀ {g : G}, g ∈ xg Ψ 0 1 ⊔ xg Ψ 1 0 ⊔ (xg Ψ 2 3 ⊔ xg Ψ 3 2) → Commute g n := by
    intro g hg
    have hle : xg Ψ 0 1 ⊔ xg Ψ 1 0 ⊔ (xg Ψ 2 3 ⊔ xg Ψ 3 2) ≤ Subgroup.centralizer {n} := by
      refine sup_le (sup_le ?_ ?_) (sup_le ?_ ?_) <;> intro x hx <;>
        rw [Subgroup.mem_centralizer_singleton_iff]
      exacts [(commuting_hid_01 n hn x hx).symm, (commuting_hid_10 h hS n hn x hx).symm,
        (commuting_hid_23 n hn x hx).symm, (commuting_hid_32 h hS n hn x hx).symm]
    exact Subgroup.mem_centralizer_singleton_iff.1 (hle hg)
  have hmem : piT Ψ ∈ xg Ψ 0 1 ⊔ xg Ψ 1 0 ⊔ (xg Ψ 2 3 ⊔ xg Ψ 3 2) := by
    rw [piT, ← pm_mul, map_mul]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (pm_swap_mem_sup ne01))
      (Subgroup.mem_sup_right (pm_swap_mem_sup ne23))
  rw [(hc hmem).eq]
  group

theorem conjSub_xg_piT {a b : Fin 4} (hab : a ≠ b) :
    conjSub (xg Ψ a b) (piT Ψ) = xg Ψ (σT a) (σT b) := conjSub_xg σT hab

end PiT

section Slope

variable [CharP F 2] [Finite F] (h : Hyp G R) (hS : Skel R Ψ) (hP : PtHyp R Ψ)
  {ι : (Fin 1 → F) → G} (hι : LinParamU R Ψ 1 ι)
include h hS hP hι

omit h hS hP in
theorem xU'_add (s t : F) : xU' R Ψ ι (s + t) = xU' R Ψ ι s * xU' R Ψ ι t := by
  rw [xU', xU', xU', xU_add hι]
  group

omit h hS hP in
theorem xU'_zero : xU' R Ψ ι 0 = 1 := by
  rw [xU', xU_zero hι]
  group

omit [Finite F] hS hP hι in
theorem hU_perm_T' : hU R (perm Ψ σT) = conjSub (hU R Ψ) (piT Ψ) := by
  rw [hU_perm_T, conjSub_hidAt h.root σT ne03 ne12 ne02 ne31]
  congr 1

omit hS hP in
theorem xU'_mem (t : F) : xU' R Ψ ι t ∈ hU R (perm Ψ σT) := by
  rw [hU_perm_T' h]
  exact conj_mem_conjSub _ (xU_mem hι t)

omit h hS hP in
theorem ptD_zero : ptD R Ψ ι 0 = xg Ψ 1 3 := by
  rw [ptD, xU_zero hι, conjSub_one]

omit h hS hP in
theorem conjSub_ptD_xU (a b : F) : conjSub (ptD R Ψ ι a) (xU R Ψ ι b) = ptD R Ψ ι (a + b) := by
  rw [ptD, ← conjSub_mul, ← xU_add hι, add_comm]

omit hP in
theorem conjSub_02_xU (b : F) : conjSub (xg Ψ 0 2) (xU R Ψ ι b) = xg Ψ 0 2 :=
  conjSub_02_hU h hS (xU_mem hι b)

theorem conj_xU_xs13 (a s : F) :
    xU R Ψ ι a * xs Ψ ne13 s * (xU R Ψ ι a)⁻¹ =
      xs Ψ ne13 s * xs Ψ ne02 (s * a) * Lc R Ψ (xU R Ψ ι (s ^ 2 * a)) := by
  have e := commutator_xs13_xU h hS hι hP s a
  have hN := Lc_mem h hS (xU_mem hι (s ^ 2 * a))
  have hNN := mul_self_of_mem_hid h hS hN
  have hCC : xs Ψ ne02 (s * a) * xs Ψ ne02 (s * a) = 1 := by
    rw [← xs_add, CharTwo.add_self_eq_zero, xs_zero]
  have hc1 : Commute (xs Ψ ne13 s) (xs Ψ ne02 (s * a)) :=
    commuting_xg (Ψ := Ψ) ne13 ne02 (by decide) (by decide) _ (xs_mem _ _) _ (xs_mem _ _)
  have hc2 : Commute (xs Ψ ne13 s) (Lc R Ψ (xU R Ψ ι (s ^ 2 * a))) :=
    (commuting_hid_13 h hS _ hN _ (xs_mem _ _)).symm
  have hc3 : Commute (xs Ψ ne02 (s * a)) (Lc R Ψ (xU R Ψ ι (s ^ 2 * a))) :=
    (commuting_hid_02 h hS _ hN _ (xs_mem _ _)).symm
  calc xU R Ψ ι a * xs Ψ ne13 s * (xU R Ψ ι a)⁻¹ =
      (⁅xs Ψ ne13 s, xU R Ψ ι a⁆)⁻¹ * xs Ψ ne13 s := by
        rw [commutatorElement_def]
        group
    _ = (Lc R Ψ (xU R Ψ ι (s ^ 2 * a)))⁻¹ * (xs Ψ ne02 (s * a))⁻¹ * xs Ψ ne13 s := by
        rw [e]
        group
    _ = Lc R Ψ (xU R Ψ ι (s ^ 2 * a)) * xs Ψ ne02 (s * a) * xs Ψ ne13 s := by
        rw [inv_eq_of_mul_eq_one_left hNN, inv_eq_of_mul_eq_one_left hCC]
    _ = xs Ψ ne13 s * xs Ψ ne02 (s * a) * Lc R Ψ (xU R Ψ ι (s ^ 2 * a)) := by
        rw [mul_assoc, ((hc3.symm).mul_right hc2.symm).eq, ← hc1.eq]

theorem conjSub_ptD_piT {a : F} (ha : a ≠ 0) : conjSub (ptD R Ψ ι a) (piT Ψ) = ptD R Ψ ι a⁻¹ := by
  have key : ∀ s : F, piT Ψ * (xU R Ψ ι a * xs Ψ ne13 s * (xU R Ψ ι a)⁻¹) * (piT Ψ)⁻¹ =
      xU R Ψ ι a⁻¹ * xs Ψ ne13 (s * a) * (xU R Ψ ι a⁻¹)⁻¹ := by
    intro s
    rw [conj_xU_xs13 h hS hP hι, conj_xU_xs13 h hS hP hι]
    have hN := Lc_mem h hS (xU_mem hι (s ^ 2 * a))
    have e1 : piT Ψ * (xs Ψ ne13 s * xs Ψ ne02 (s * a) * Lc R Ψ (xU R Ψ ι (s ^ 2 * a))) *
        (piT Ψ)⁻¹ = (piT Ψ * xs Ψ ne13 s * (piT Ψ)⁻¹) * (piT Ψ * xs Ψ ne02 (s * a) * (piT Ψ)⁻¹) *
          (piT Ψ * Lc R Ψ (xU R Ψ ι (s ^ 2 * a)) * (piT Ψ)⁻¹) := by group
    rw [e1, piT_conj_xs13, piT_conj_xs02, piT_conj_hid h hS hN]
    have e2 : (s * a) ^ 2 * a⁻¹ = s ^ 2 * a := by field_simp
    have e3 : s * a * a⁻¹ = s := by field_simp
    rw [e2, e3]
    have hc : Commute (xs Ψ ne02 s) (xs Ψ ne13 (s * a)) :=
      commuting_xg (Ψ := Ψ) ne02 ne13 (by decide) (by decide) _ (xs_mem _ _) _ (xs_mem _ _)
    rw [hc.eq]
  ext g
  constructor
  · rintro ⟨_, ⟨c, hc, rfl⟩, rfl⟩
    obtain ⟨s, rfl⟩ := (mem_xg_iff ne13).1 hc
    change piT Ψ * (xU R Ψ ι a * xs Ψ ne13 s * (xU R Ψ ι a)⁻¹) * (piT Ψ)⁻¹ ∈ _
    rw [key]
    exact conj_mem_conjSub _ (xs_mem _ _)
  · rintro ⟨c, hc, rfl⟩
    obtain ⟨s, rfl⟩ := (mem_xg_iff ne13).1 hc
    refine ⟨xU R Ψ ι a * xs Ψ ne13 (s * a⁻¹) * (xU R Ψ ι a)⁻¹, conj_mem_conjSub _ (xs_mem _ _), ?_⟩
    change piT Ψ * (xU R Ψ ι a * xs Ψ ne13 (s * a⁻¹) * (xU R Ψ ι a)⁻¹) * (piT Ψ)⁻¹ = _
    rw [key, show s * a⁻¹ * a = s by field_simp]
    rfl

omit [Finite F] h hS hP hι in
theorem conjSub_02_piT : conjSub (xg Ψ 0 2) (piT Ψ) = xg Ψ 1 3 := by
  rw [conjSub_xg_piT ne02]
  rfl

omit [Finite F] h hS hP hι in
theorem conjSub_13_piT : conjSub (xg Ψ 1 3) (piT Ψ) = xg Ψ 0 2 := by
  rw [conjSub_xg_piT ne13]
  rfl

omit h hS hP hι in
theorem conjSub_xU' (H : Subgroup G) (b : F) :
    conjSub H (xU' R Ψ ι b) = conjSub (conjSub (conjSub H (piT Ψ)) (xU R Ψ ι b)) (piT Ψ) := by
  rw [xU', piT_inv, ← conjSub_mul, ← conjSub_mul, mul_assoc]

theorem conjSub_02_xU' {b : F} (hb : b ≠ 0) : conjSub (xg Ψ 0 2) (xU' R Ψ ι b) = ptD R Ψ ι b⁻¹ := by
  rw [conjSub_xU', conjSub_02_piT, ← ptD_zero hι, conjSub_ptD_xU hι, zero_add,
    conjSub_ptD_piT h hS hP hι hb]

omit hP in
theorem conjSub_ptD0_xU' (b : F) : conjSub (ptD R Ψ ι 0) (xU' R Ψ ι b) = ptD R Ψ ι 0 := by
  rw [conjSub_xU', ptD_zero hι, conjSub_13_piT, conjSub_02_xU h hS hι, conjSub_02_piT]

theorem conjSub_ptD_xU' {a b : F} (ha : a ≠ 0) (hab : 1 + a * b ≠ 0) :
    conjSub (ptD R Ψ ι a) (xU' R Ψ ι b) = ptD R Ψ ι (a / (1 + a * b)) := by
  have h1 : a⁻¹ + b ≠ 0 := by
    intro e
    apply hab
    have : a * (a⁻¹ + b) = 1 + a * b := by field_simp
    rw [← this, e, mul_zero]
  rw [conjSub_xU', conjSub_ptD_piT h hS hP hι ha, conjSub_ptD_xU hι,
    conjSub_ptD_piT h hS hP hι h1]
  congr 1
  field_simp

theorem conjSub_ptD_xU'_eq {a b : F} (ha : a ≠ 0) (hab : 1 + a * b = 0) :
    conjSub (ptD R Ψ ι a) (xU' R Ψ ι b) = xg Ψ 0 2 := by
  have h1 : a⁻¹ + b = 0 := by
    have : a * (a⁻¹ + b) = 1 + a * b := by field_simp
    rw [hab] at this
    exact (mul_eq_zero.1 this).resolve_left ha
  rw [conjSub_xU', conjSub_ptD_piT h hS hP hι ha, conjSub_ptD_xU hι, h1, ptD_zero hι,
    conjSub_13_piT]

omit h hS hP in
theorem xU_mul_self (t : F) : xU R Ψ ι t * xU R Ψ ι t = 1 := by
  rw [← xU_add hι, CharTwo.add_self_eq_zero, xU_zero hι]

omit h hS hP in
theorem xU'_mul_self (t : F) : xU' R Ψ ι t * xU' R Ψ ι t = 1 := by
  rw [← xU'_add hι, CharTwo.add_self_eq_zero, xU'_zero hι]

theorem rankOne_conj {t : F} (ht : t ≠ 0) (a : F) :
    xU R Ψ ι t * xU' R Ψ ι (-t⁻¹) * xU R Ψ ι t * xU R Ψ ι a *
        (xU R Ψ ι t * xU' R Ψ ι (-t⁻¹) * xU R Ψ ι t)⁻¹ = xU' R Ψ ι (-(t ^ 2)⁻¹ * a) := by
  have hR := h.root
  set w := xU R Ψ ι t * xU' R Ψ ι (-t⁻¹) * xU R Ψ ι t with hw
  by_cases ha : a = 0
  · subst ha
    rw [xU_zero hι, mul_zero, xU'_zero hι]
    group
  have hs : -t⁻¹ ≠ 0 := neg_ne_zero.2 (inv_ne_zero ht)
  have hneg : ∀ x : F, -x = x := CharTwo.neg_eq
  have hwinv : w⁻¹ = w := by
    rw [hw, _root_.mul_inv_rev, _root_.mul_inv_rev, inv_eq_of_mul_eq_one_left (xU_mul_self hι t),
      inv_eq_of_mul_eq_one_left (xU'_mul_self hι _)]
    group
  have hwC : conjSub (xg Ψ 0 2) w = ptD R Ψ ι 0 := by
    rw [hw, conjSub_mul, conjSub_mul, conjSub_02_xU h hS hι, conjSub_02_xU' h hS hP hι hs,
      conjSub_ptD_xU hι, inv_neg, inv_inv, hneg, CharTwo.add_self_eq_zero]
  have hwD : conjSub (ptD R Ψ ι a) w = ptD R Ψ ι (t ^ 2 / a) := by
    rw [hw, conjSub_mul, conjSub_mul, conjSub_ptD_xU hι]
    by_cases hat : a + t = 0
    · have hat' : a = t := by
        have := eq_neg_of_add_eq_zero_left hat
        rwa [hneg] at this
      rw [hat, conjSub_ptD0_xU' h hS hι, conjSub_ptD_xU hι, zero_add, hat', pow_two,
        mul_div_cancel_right₀ _ ht]
    · have h1 : 1 + (a + t) * -t⁻¹ ≠ 0 := by
        rw [hneg]
        intro e
        have : (1 + (a + t) * t⁻¹) * t = a := by
          field_simp
          linear_combination (CharTwo.add_self_eq_zero t)
        rw [e, zero_mul] at this
        exact ha this.symm
      rw [conjSub_ptD_xU' h hS hP hι hat h1, conjSub_ptD_xU hι]
      congr 1
      rw [hneg]
      have h4 : 1 + (a + t) * t⁻¹ = a * t⁻¹ := by
        field_simp
        linear_combination (CharTwo.add_self_eq_zero t)
      rw [h4]
      have e5 : (a + t) / (a * t⁻¹) + t = (t ^ 2 + 2 * (a * t)) / a := by
        field_simp
        ring
      rw [e5, CharTwo.two_eq_zero (R := F), zero_mul, add_zero]
  have hU'1 : w * xU R Ψ ι a * w⁻¹ ∈ hU R (perm Ψ σT) := by
    have hST := hS.perm σT
    have hPT := hP.perm hR σT
    have hwc : w ∈ cent4 Ψ := by
      have h1 : xU R Ψ ι t ∈ cent4 Ψ := hU_le_cent4 h hS (xU_mem hι t)
      have h2 : xU' R Ψ ι (-t⁻¹) ∈ cent4 Ψ := by
        rw [← cent4_perm_T]
        exact hU_le_cent4 h hST (xU'_mem h hι _)
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ h1 h2) h1
    have hmem : w * xU R Ψ ι a * w⁻¹ ∈ conjSub (hU R Ψ) w := conj_mem_conjSub w (xU_mem hι a)
    rw [hU_eq_cent4_inf h hS hP, conjSub_inf, conjSub_of_mem hwc, Sec5.conjSub_M hR, hwC,
      ptD_zero hι] at hmem
    rw [hU_eq_cent4_inf h hST hPT, cent4_perm_T, xg_perm,
      show σT 0 = 1 from by decide, show σT 2 = 3 from by decide]
    exact hmem
  have hr : -(t ^ 2)⁻¹ * a ≠ 0 := mul_ne_zero (neg_ne_zero.2 (inv_ne_zero (pow_ne_zero 2 ht))) ha
  have hL : conjSub (xg Ψ 0 2) (w * xU R Ψ ι a * w⁻¹) = ptD R Ψ ι (t ^ 2 / a) := by
    rw [conjSub_mul, conjSub_mul, hwinv, hwC, conjSub_ptD_xU hι, zero_add, hwD]
  have hRC : conjSub (xg Ψ 0 2) (xU' R Ψ ι (-(t ^ 2)⁻¹ * a)) = ptD R Ψ ι (t ^ 2 / a) := by
    rw [conjSub_02_xU' h hS hP hι hr, hneg, mul_inv, inv_inv, div_eq_mul_inv, mul_comm]
  have hST := hS.perm σT
  have hPT := hP.perm hR σT
  set g := (xU' R Ψ ι (-(t ^ 2)⁻¹ * a))⁻¹ * (w * xU R Ψ ι a * w⁻¹) with hg
  have hgU : g ∈ hU R (perm Ψ σT) :=
    Subgroup.mul_mem _ (Subgroup.inv_mem _ (xU'_mem h hι _)) hU'1
  have hgC : conjSub (xg Ψ 0 2) g = xg Ψ 0 2 := by
    rw [hg, conjSub_mul, hL, ← hRC, ← conjSub_mul, inv_mul_cancel, conjSub_one]
  have hOm : xg Ψ 0 2 ∈ Om R (perm Ψ σT) := by
    rw [Om_perm, show σT 0 = 1 from by decide, show σT 1 = 0 from by decide,
      show σT 2 = 3 from by decide, show σT 3 = 2 from by decide, Set.inter_comm]
    exact mem_Om_02 h hS
  have hne : xg Ψ 0 2 ≠ xg (perm Ψ σT) 0 2 := by
    rw [xg_perm, show σT 0 = 1 from by decide, show σT 2 = 3 from by decide]
    exact hS.xg_ne ne02 ne13 (by decide)
  have h1 := eq_one_of_conjSub_eq h hST hPT hgU hOm hne hgC
  rw [hg, inv_mul_eq_one] at h1
  exact h1.symm

variable (R Ψ) in
noncomputable def rankOneRelsU (h : Hyp G R) (hS : Skel R Ψ) (hP : PtHyp R Ψ)
    (hι : LinParamU R Ψ 1 ι) : RankOneRels G F where
  x := xU R Ψ ι
  y := xU' R Ψ ι
  x_add := xU_add hι
  y_add := xU'_add hι
  conj_x _ ht a := rankOne_conj h hS hP hι ht a

theorem exists_hom_SL2_xU :
    ∃ Θ : SpecialLinearGroup (Fin 2) F →* G,
      (∀ a, Θ (sl2Upper a) = xU R Ψ ι a) ∧ ∀ a, Θ (sl2Lower a) = xU' R Ψ ι a :=
  RankTwo.exists_hom_of_rankOneRels (rankOneRelsU R Ψ h hS hP hι)

end Slope

end CaseB

end CFSG.Timmesfeld.ARS
