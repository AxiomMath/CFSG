module

public import CFSG.Quasithin.Vol2.Ch5Sec2M23PairFacts
public import CFSG.Quasithin.Vol2.Ch5Sec2M23PlaneSem
public import CFSG.Quasithin.Recognition.M23Facts
public import CFSG.LocalAnalysis.ComponentClassification.WittDesignM22PointStabilizer
import all CFSG.Fischer.F4
public import CFSG.Quasithin.Recognition.M23FactsHeptad
public import CFSG.Sporadic.Schreier.M23Base

public section

namespace CFSG.Quasithin.H13

open MulAction CFSG.Blueprint CFSG.M23Pair CFSG.Monster.B.Classical.Plane CFSG.Fischer
  CFSG.Quasithin.Asc94 CFSG.ComponentClassification.WittDesign
  CFSG.EvenSmallLie.UnitarySix.MathieuExt
open CFSG.QuasithinUnique.Vol2Native.L239
open scoped Pointwise Matrix

@[expose] def xbar0 : Pair (Fin 23) := pair 21 22 (by decide)

abbrev Gbar : Subgroup ↥NativeSporadic.M23 := stabilizer ↥NativeSporadic.M23 xbar0

theorem m23_smul_eq (g : ↥NativeSporadic.M23) (x : Fin 23) :
    g • x = (g : Equiv.Perm (Fin 23)) x := rfl

theorem mem_Gbar_iff {g : ↥NativeSporadic.M23} :
    g ∈ Gbar ↔ ((g : Equiv.Perm (Fin 23)) 21 = 21 ∧ (g : Equiv.Perm (Fin 23)) 22 = 22) ∨
      ((g : Equiv.Perm (Fin 23)) 21 = 22 ∧ (g : Equiv.Perm (Fin 23)) 22 = 21) := by
  rw [mem_stabilizer_iff, xbar0, smul_pair, pair_eq_iff, m23_smul_eq, m23_smul_eq]

theorem apply_ne_of_mem_Gbar {g : ↥NativeSporadic.M23} (hg : g ∈ Gbar) {x : Fin 23}
    (h21 : x ≠ 21) (h22 : x ≠ 22) :
    (g : Equiv.Perm (Fin 23)) x ≠ 21 ∧ (g : Equiv.Perm (Fin 23)) x ≠ 22 := by
  have hinj := (g : Equiv.Perm (Fin 23)).injective
  rcases mem_Gbar_iff.mp hg with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨fun h => h21 (hinj (h.trans h1.symm)), fun h => h22 (hinj (h.trans h2.symm))⟩
  · exact ⟨fun h => h22 (hinj (h.trans h2.symm)), fun h => h21 (hinj (h.trans h1.symm))⟩

@[expose] def psiBarFun (g : ↥NativeSporadic.M23) (i : Fin 21) : Fin 21 :=
  lamInv ((g : Equiv.Perm (Fin 23)) (lam i))

theorem lam_psiBarFun {g : ↥NativeSporadic.M23} (hg : g ∈ Gbar) (i : Fin 21) :
    lam (psiBarFun g i) = (g : Equiv.Perm (Fin 23)) (lam i) :=
  lam_lamInv _ (apply_ne_of_mem_Gbar hg (lam_ne_21 i) (lam_ne_22 i)).1
    (apply_ne_of_mem_Gbar hg (lam_ne_21 i) (lam_ne_22 i)).2

theorem psiBarFun_one (i : Fin 21) : psiBarFun 1 i = i := lamInv_lam i

theorem psiBarFun_mul (g : ↥NativeSporadic.M23) {h : ↥NativeSporadic.M23} (hh : h ∈ Gbar)
    (i : Fin 21) : psiBarFun (g * h) i = psiBarFun g (psiBarFun h i) := by
  rw [psiBarFun, psiBarFun, lam_psiBarFun hh]
  rfl

@[expose] def psiBar : ↥Gbar →* Equiv.Perm (Fin 21) where
  toFun g :=
    { toFun := psiBarFun g
      invFun := psiBarFun (g⁻¹ : ↥Gbar)
      left_inv := fun i => by
        rw [← psiBarFun_mul _ g.2, ← Subgroup.coe_mul, inv_mul_cancel, Subgroup.coe_one,
          psiBarFun_one]
      right_inv := fun i => by
        rw [← psiBarFun_mul _ (g⁻¹).2, ← Subgroup.coe_mul, mul_inv_cancel, Subgroup.coe_one,
          psiBarFun_one] }
  map_one' := Equiv.ext fun i => psiBarFun_one i
  map_mul' g h := Equiv.ext fun i => psiBarFun_mul _ h.2 i

theorem psiBar_apply (g : ↥Gbar) (i : Fin 21) :
    psiBar g i = lamInv (((g : ↥NativeSporadic.M23) : Equiv.Perm (Fin 23)) (lam i)) := rfl

theorem lam_psiBar (g : ↥Gbar) (i : Fin 21) :
    lam (psiBar g i) = ((g : ↥NativeSporadic.M23) : Equiv.Perm (Fin 23)) (lam i) :=
  lam_psiBarFun g.2 i

theorem sign_eq_one_of_m23
    (g : ↥NativeSporadic.M23) : Equiv.Perm.sign (g : Equiv.Perm (Fin 23)) = 1 := by
  obtain ⟨-, -, hs⟩ := CFSG.Sporadic.Mathieu.fam_m23_simplicity
  set φ : ↥NativeSporadic.M23 →* ℤˣ := Equiv.Perm.sign.comp NativeSporadic.M23.subtype with hφ
  rcases hs.eq_bot_or_eq_top_of_normal φ.ker with h | h
  · exfalso
    have hinj : Function.Injective φ := (MonoidHom.ker_eq_bot_iff φ).mp h
    have h1 := Nat.card_le_card_of_injective φ hinj
    rw [CFSG.Sporadic.Schreier.m23_card, Nat.card_eq_fintype_card, Fintype.card_units_int] at h1
    omega
  · have hg : g ∈ φ.ker := h ▸ Subgroup.mem_top g
    exact hg

theorem psiBar_injective :
    Function.Injective psiBar := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro g hg
  rw [MonoidHom.mem_ker] at hg
  set σ : Equiv.Perm (Fin 23) := ((g : ↥NativeSporadic.M23) : Equiv.Perm (Fin 23)) with hσ
  have hfix : ∀ x : Fin 23, x ≠ 21 → x ≠ 22 → σ x = x := by
    intro x h1 h2
    have e1 : psiBar g (lamInv x) = lamInv x := by rw [hg]; rfl
    have e2 := lam_psiBar g (lamInv x)
    rw [e1, lam_lamInv x h1 h2] at e2
    exact e2.symm
  rw [Subgroup.mem_bot]
  rcases mem_Gbar_iff.mp g.2 with ⟨h21, h22⟩ | ⟨h21, h22⟩
  · refine Subtype.ext (Subtype.ext (Equiv.ext fun x => ?_))
    change σ x = x
    by_cases hx1 : x = 21
    · rw [hx1]; exact h21
    by_cases hx2 : x = 22
    · rw [hx2]; exact h22
    exact hfix x hx1 hx2
  · exfalso
    have hsw : σ = Equiv.swap 21 22 := by
      refine Equiv.ext fun x => ?_
      by_cases hx1 : x = 21
      · rw [hx1, Equiv.swap_apply_left]; exact h21
      by_cases hx2 : x = 22
      · rw [hx2, Equiv.swap_apply_right]; exact h22
      rw [hfix x hx1 hx2, Equiv.swap_apply_of_ne_of_ne hx1 hx2]
    have hs := sign_eq_one_of_m23 (g : ↥NativeSporadic.M23)
    rw [← hσ, hsw, Equiv.Perm.sign_swap (by decide)] at hs
    exact absurd hs (by decide)

theorem card_projLine (a : Fin 21) : (projLine a).card = 5 := by
  revert a
  decide +kernel

theorem psiBar_mem_lineAut
    (g : ↥Gbar) : psiBar g ∈ lineAut := by
  intro a
  set g' : ↥NativeSporadic.M23 := g.1 with hg'
  have hB : g' • hepL a ∈ M23Insp.data.H :=
    M23Insp.chk_H_closed.closure g' (m23Insp_hgens ▸ Subgroup.mem_top g') _ (hepL_mem a)
  have hmem : ∀ x ∈ hepL a, (g' : Equiv.Perm (Fin 23)) x ∈ g' • hepL a := fun x hx =>
    Finset.smul_mem_smul_finset hx
  have h21 : (21 : Fin 23) ∈ g' • hepL a := by
    rcases mem_Gbar_iff.mp g.2 with ⟨h1, -⟩ | ⟨-, h2⟩
    · rw [← h1]; exact hmem _ (mem_hepL_21 a)
    · rw [← h2]; exact hmem _ (mem_hepL_22 a)
  have h22 : (22 : Fin 23) ∈ g' • hepL a := by
    rcases mem_Gbar_iff.mp g.2 with ⟨-, h2⟩ | ⟨h1, -⟩
    · rw [← h2]; exact hmem _ (mem_hepL_22 a)
    · rw [← h1]; exact hmem _ (mem_hepL_21 a)
  obtain ⟨b, hb⟩ := eq_hepL_of_mem hB h21 h22
  refine ⟨b, Finset.eq_of_subset_of_card_le ?_ ?_⟩
  · intro p hp
    obtain ⟨q, hq, rfl⟩ := Finset.mem_map.mp hp
    rw [← lam_mem_hepL_iff, ← hb]
    change lam (psiBar g q) ∈ g' • hepL a
    rw [lam_psiBar]
    exact hmem _ (lam_mem_hepL_iff.mpr hq)
  · rw [Finset.card_map, card_projLine, card_projLine]

theorem isMultiplyPretransitive_m23
    {k : ℕ} (hk : k ≤ 4) :
    IsMultiplyPretransitive ↥NativeSporadic.M23 (Fin 23) k := by
  have := m23_four_transitive
  exact MulAction.isMultiplyPretransitive_of_le (G := ↥NativeSporadic.M23) (α := Fin 23) (m := k)
    (n := 4) hk (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; omega)

theorem card_fixingSubgroup_m23
    (s : Finset (Fin 23)) (hs : s.card ≤ 4) :
    Nat.card (fixingSubgroup ↥NativeSporadic.M23 (s : Set (Fin 23))) *
      (Nat.choose 23 s.card * s.card.factorial) = 10200960 := by
  have hk := isMultiplyPretransitive_m23 (k := (s : Set (Fin 23)).ncard)
    (by rw [Set.ncard_coe_finset]; exact hs)
  have hidx := IsMultiplyPretransitive.index_of_fixingSubgroup_eq (s : Set (Fin 23)) hk
  rw [Nat.card_fin, Set.ncard_coe_finset] at hidx
  rw [← hidx, Subgroup.card_mul_index, CFSG.Sporadic.Schreier.m23_card]

abbrev fix21 : Subgroup ↥NativeSporadic.M23 :=
  fixingSubgroup ↥NativeSporadic.M23 (({21, 22} : Finset (Fin 23)) : Set (Fin 23))

theorem mem_fix21_iff {g : ↥NativeSporadic.M23} :
    g ∈ fix21 ↔ (g : Equiv.Perm (Fin 23)) 21 = 21 ∧ (g : Equiv.Perm (Fin 23)) 22 = 22 := by
  rw [mem_fixingSubgroup_iff]
  simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff,
    forall_eq_or_imp, forall_eq, m23_smul_eq]

theorem fix21_le_Gbar : fix21 ≤ Gbar := fun _ hg =>
  mem_Gbar_iff.mpr (Or.inl (mem_fix21_iff.mp hg))

theorem card_fix21 :
    Nat.card fix21 = 20160 := by
  have h := card_fixingSubgroup_m23 ({21, 22} : Finset (Fin 23)) (by decide)
  have hc : ({21, 22} : Finset (Fin 23)).card = 2 := by decide
  rw [hc, show Nat.choose 23 2 * Nat.factorial 2 = 506 by decide,
    show (10200960 : ℕ) = 20160 * 506 by norm_num] at h
  exact Nat.eq_of_mul_eq_mul_right (by norm_num) h

theorem isSimpleGroup_P0 : IsSimpleGroup ↥P0 := by
  have h := (CFSG.LinearGroups.linear_projective_simple (K := F4) (n := 3) (by norm_num)
    (Or.inl le_rfl)).2.1
  have : Nontrivial ↥P0 := by
    rw [← Finite.one_lt_card_iff_nontrivial, card_range_pslPerm]
    norm_num
  exact IsSimpleGroup.isSimpleGroup_of_surjective pslPerm.rangeRestrict
    pslPerm.rangeRestrict_surjective

theorem P0_le_lineAut : P0 ≤ lineAut := by
  rintro _ ⟨g, rfl⟩
  exact pslPerm_mem_lineAut g

theorem map_fix21_eq_P0 :
    (fix21.subgroupOf Gbar).map psiBar = P0 := by
  refine eq_of_relIndex_le_six (L := lineAut) ?_ ?_ ?_ isSimpleGroup_P0 ?_
  · rintro _ ⟨g, -, rfl⟩
    exact psiBar_mem_lineAut g
  · have h := Subgroup.relIndex_mul_card (H := P0) (K := lineAut)
    rw [inf_of_le_left P0_le_lineAut, card_range_pslPerm] at h
    have := card_lineAut_le
    omega
  · rw [Subgroup.card_map_of_injective psiBar_injective,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe fix21_le_Gbar).toEquiv, card_fix21,
      card_range_pslPerm]
  · rw [card_range_pslPerm]
    decide

@[expose] def A0SL : Matrix.SpecialLinearGroup (Fin 3) F4 := ⟨A0, det_A0⟩

@[expose] def A0GL : GL (Fin 3) F4 := Matrix.SpecialLinearGroup.toGL A0SL

theorem det_A0GL : (A0GL : Matrix (Fin 3) (Fin 3) F4).det = 1 := det_A0

theorem sbar_mem_Gbar : sbar ∈ Gbar :=
  mem_Gbar_iff.mpr (Or.inr ⟨sbar_apply_21, sbar_apply_22⟩)

@[expose] def sbarG : ↥Gbar := ⟨sbar, sbar_mem_Gbar⟩

theorem psiBar_sbar :
    psiBar sbarG = planePerm (semΓ A0GL frobF4) := by
  refine Equiv.ext fun i => ?_
  rw [psiBar_apply, planePerm_semΓ]
  exact lamInv_sbar_lam i

theorem psiBar_mem_P0_iff
    (g : ↥Gbar) :
    psiBar g ∈ P0 ↔ (g : ↥NativeSporadic.M23) ∈ fix21 := by
  constructor
  · intro hg
    by_contra hf
    have hsw : ((g : ↥NativeSporadic.M23) : Equiv.Perm (Fin 23)) 21 = 22 ∧
        ((g : ↥NativeSporadic.M23) : Equiv.Perm (Fin 23)) 22 = 21 := by
      rcases mem_Gbar_iff.mp g.2 with h | h
      · exact absurd (mem_fix21_iff.mpr h) hf
      · exact h
    have hk : ((g * sbarG⁻¹ : ↥Gbar) : ↥NativeSporadic.M23) ∈ fix21 := by
      rw [mem_fix21_iff]
      have e1 : ((sbar : ↥NativeSporadic.M23) : Equiv.Perm (Fin 23))⁻¹ 21 = 22 := by
        rw [Equiv.Perm.inv_eq_iff_eq]; exact sbar_apply_22.symm
      have e2 : ((sbar : ↥NativeSporadic.M23) : Equiv.Perm (Fin 23))⁻¹ 22 = 21 := by
        rw [Equiv.Perm.inv_eq_iff_eq]; exact sbar_apply_21.symm
      change ((g : ↥NativeSporadic.M23) : Equiv.Perm (Fin 23))
          (((sbar : ↥NativeSporadic.M23) : Equiv.Perm (Fin 23))⁻¹ 21) = 21 ∧
        ((g : ↥NativeSporadic.M23) : Equiv.Perm (Fin 23))
          (((sbar : ↥NativeSporadic.M23) : Equiv.Perm (Fin 23))⁻¹ 22) = 22
      rw [e1, e2]
      exact ⟨hsw.2, hsw.1⟩
    have hP : psiBar (g * sbarG⁻¹) ∈ P0 := by
      rw [← map_fix21_eq_P0]
      exact ⟨g * sbarG⁻¹, Subgroup.mem_subgroupOf.mpr hk, rfl⟩
    have hs : psiBar sbarG ∈ P0 := by
      have e : sbarG = (g * sbarG⁻¹)⁻¹ * g := by group
      rw [e, map_mul, map_inv]
      exact P0.mul_mem (P0.inv_mem hP) hg
    rw [psiBar_sbar] at hs
    exact planePerm_semΓ_frob_not_mem A0GL hs
  · intro hg
    rw [← map_fix21_eq_P0]
    exact ⟨g, Subgroup.mem_subgroupOf.mpr hg, rfl⟩

theorem card_Gbar :
    Nat.card Gbar = 40320 := by
  have hidx : (fix21.subgroupOf Gbar).index = 2 := by
    rw [Subgroup.index_eq_two_iff]
    refine ⟨sbarG, fun b => ?_⟩
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, ← psiBar_mem_P0_iff,
      ← psiBar_mem_P0_iff, map_mul, psiBar_sbar]
    by_cases hb : psiBar b ∈ P0
    · refine Or.inr ⟨hb, fun h => planePerm_semΓ_frob_not_mem A0GL ?_⟩
      have := P0.mul_mem (P0.inv_mem hb) h
      rwa [inv_mul_cancel_left] at this
    · refine Or.inl ⟨?_, hb⟩
      rcases mem_Gbar_iff.mp b.2 with h | h
      · exact absurd ((psiBar_mem_P0_iff b).mpr (mem_fix21_iff.mpr h)) hb
      · have hk : ((b * sbarG : ↥Gbar) : ↥NativeSporadic.M23) ∈ fix21 := by
          rw [mem_fix21_iff]
          change ((b : ↥NativeSporadic.M23) : Equiv.Perm (Fin 23))
              (((sbar : ↥NativeSporadic.M23) : Equiv.Perm (Fin 23)) 21) = 21 ∧
            ((b : ↥NativeSporadic.M23) : Equiv.Perm (Fin 23))
              (((sbar : ↥NativeSporadic.M23) : Equiv.Perm (Fin 23)) 22) = 22
          rw [sbar_apply_21, sbar_apply_22]
          exact ⟨h.2, h.1⟩
        have := (psiBar_mem_P0_iff (b * sbarG)).mpr hk
        rwa [map_mul, psiBar_sbar] at this
  have h := Subgroup.card_mul_index (fix21.subgroupOf Gbar)
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe fix21_le_Gbar).toEquiv, card_fix21, hidx] at h
  omega

theorem card_fix3
    (s : Finset (Fin 23)) (hs : s.card = 3) :
    Nat.card (fixingSubgroup ↥NativeSporadic.M23 (s : Set (Fin 23))) = 960 := by
  have h := card_fixingSubgroup_m23 s (by rw [hs]; norm_num)
  rw [hs, show Nat.choose 23 3 * Nat.factorial 3 = 10626 by decide] at h
  omega

end CFSG.Quasithin.H13
