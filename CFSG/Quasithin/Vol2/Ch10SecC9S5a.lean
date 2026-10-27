module

public import CFSG.Quasithin.Vol2.Ch10SecAT1Fix
public import CFSG.Quasithin.Vol2.Ch10SecAT1Trans
public import CFSG.Quasithin.Vol2.Ch10SecC9S4e

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC

open CFSG.Open CFSG.Quasithin.H13 CFSG.QuasithinUnique CFSG.Quasithin
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

theorem le_of_case_one (hyp : Hyp10 G T L I) {n : ℕ} (h1 : Case10_1_1One T L I n)
    {Y : Subgroup G} (hY : Y ≤ fsuUL T L I) (hLY : L ≤ Subgroup.normalizer (Y : Set G)) {y : G}
    (hy : y ∈ Y) (hyC : y ∉ Subgroup.centralizer (L : Set G)) : fsuUL T L I ≤ Y := by
  obtain ⟨hab, F, _, _, _, -, -, ⟨nc⟩⟩ := SecA.exists_natCoord hyp h1
  have hLU : L ≤ Subgroup.normalizer (fsuUL T L I : Set G) := le_normalizer_fsuUL T L I
  have hyV : y ∈ fsuUL T L I := hY hy
  have hker : ∀ z : ↥(fsuUL T L I), nc.β z = 1 → (z : G) ∈ Subgroup.centralizer (L : Set G) :=
    fun z hz => Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr (SecA.le_fsuL0 T L))
      (Subgroup.mem_subgroupOf.mp ((nc.ker z).mp hz))
  have hβy : Multiplicative.toAdd (nc.β ⟨y, hyV⟩) ≠ 0 := fun h =>
    hyC (hker _ (by rw [← ofAdd_toAdd (nc.β ⟨y, hyV⟩), h]; rfl))
  have step1 : ∀ z : ↥(fsuUL T L I), ∃ y' ∈ Y, ∃ hy' : y' ∈ fsuUL T L I,
      nc.β z = nc.β ⟨y', hy'⟩ := by
    intro z
    by_cases hz : Multiplicative.toAdd (nc.β z) = 0
    · refine ⟨1, Y.one_mem, (fsuUL T L I).one_mem, ?_⟩
      have h1' : (⟨1, (fsuUL T L I).one_mem⟩ : ↥(fsuUL T L I)) = 1 := rfl
      rw [h1', map_one, ← ofAdd_toAdd (nc.β z), hz]
      rfl
    obtain ⟨A, hA⟩ := SecA.exists_SL_mulVec_single_eq hβy
    obtain ⟨B, hB⟩ := SecA.exists_SL_mulVec_single_eq hz
    obtain ⟨g, hg, hgγ⟩ := Subgroup.mem_map.mp (nc.eρ (B * A⁻¹)).2
    have hgL : (g : G) ∈ L := Subgroup.mem_subgroupOf.mp hg
    have hy'V : (g : G) * y * (g : G)⁻¹ ∈ fsuUL T L I :=
      (Subgroup.mem_normalizer_iff.mp (hLU hgL) y).mp hyV
    refine ⟨(g : G) * y * (g : G)⁻¹, (Subgroup.mem_normalizer_iff.mp (hLY hgL) y).mp hy, hy'V, ?_⟩
    have he : (⟨(g : G) * y * (g : G)⁻¹, hy'V⟩ : ↥(fsuUL T L I)) =
        ((nc.eρ (B * A⁻¹) : ↥(autOn L (fsuUL T L I))) : MulAut ↥(fsuUL T L I)) ⟨y, hyV⟩ := by
      apply Subtype.ext
      rw [← hgγ]
      exact (coe_conjAct_apply _ g ⟨y, hyV⟩).symm
    rw [he, nc.equivariant]
    apply Multiplicative.toAdd.injective
    rw [toAdd_ofAdd, ← hA, Matrix.SpecialLinearGroup.coe_mul, Matrix.mulVec_mulVec,
      mul_assoc, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
      Matrix.SpecialLinearGroup.coe_one, mul_one, hB]
  rw [← commutator_fsuUL_eq hyp, Subgroup.commutator_le]
  intro z hz l hl
  obtain ⟨y', hy'Y, hy'V, he⟩ := step1 ⟨z, hz⟩
  have hcV : y'⁻¹ * z ∈ fsuUL T L I := (fsuUL T L I).mul_mem ((fsuUL T L I).inv_mem hy'V) hz
  have hcC : y'⁻¹ * z ∈ Subgroup.centralizer (L : Set G) := by
    refine hker ⟨y'⁻¹ * z, hcV⟩ ?_
    have : (⟨y'⁻¹ * z, hcV⟩ : ↥(fsuUL T L I)) = (⟨y', hy'V⟩ : ↥(fsuUL T L I))⁻¹ * ⟨z, hz⟩ := rfl
    rw [this, map_mul, map_inv, ← he, inv_mul_cancel]
  have hcl : (y'⁻¹ * z) * l = l * (y'⁻¹ * z) := (Subgroup.mem_centralizer_iff.mp hcC l hl).symm
  have hcomm : ⁅z, l⁆ = ⁅y', l⁆ := by
    rw [commutatorElement_def, commutatorElement_def]
    calc z * l * z⁻¹ * l⁻¹ = y' * ((y'⁻¹ * z) * l) * (y'⁻¹ * z)⁻¹ * y'⁻¹ * l⁻¹ := by group
      _ = y' * (l * (y'⁻¹ * z)) * (y'⁻¹ * z)⁻¹ * y'⁻¹ * l⁻¹ := by rw [hcl]
      _ = y' * l * y'⁻¹ * l⁻¹ := by group
  rw [hcomm, commutatorElement_def, show y' * l * y'⁻¹ * l⁻¹ = y' * (l * y'⁻¹ * l⁻¹) by group]
  exact Y.mul_mem hy'Y ((Subgroup.mem_normalizer_iff.mp (hLY hl) _).mp (Y.inv_mem hy'Y))

namespace Conf

variable {J : Subgroup G} {t w : G} (c : Conf T L I t w J)
include c

theorem fsuUL_le_VI (h37 : QuasithinUnique.Vol2Native.A37ForSQTKCat)
    (h38 : QuasithinUnique.Vol2Native.A38ForSQTKCat) (h1011 : Stmt10_1_1) (h1012 : Stmt10_1_2)
    (h1027 : Stmt10_2_7) (h322 : TmpL6_3_2_2_two) (hK8a : FactK8a) (hK8b : FactK8b)
    (h3 : ¬ Case10_1_1Three T L I ∨ cV1 T L I = ⊥) : fsuUL T L I ≤ VI T L I J w := by
  have hyp := c.hyp
  set Tw := T ⊓ Subgroup.centralizer ({w} : Set G) with hTw
  have hTw1 : Tw ≤ T1 T L := c.Tw_le_T1 h37 h38
  have hLN : L ≤ Subgroup.normalizer (fsuVM T L I : Set G) :=
    (SecA.le_fsuL0 T L).trans (SecA.fsuL0_le_normalizer_fsuVM T L I)
  have hV1V : fsuUL T L I ≤ fsuVM T L I := commutator_le_left_of_le_normalizer hLN
  have hV1T : fsuUL T L I ≤ T := hV1V.trans (SecA.fsuVM_le_T hyp)
  have hT2 : IsPGroup 2 T := hyp.fsu.sylow.1
  have hTwV1 : Tw ≤ Subgroup.normalizer (fsuUL T L I : Set G) :=
    le_sup_right.trans (c.le_normalizer_fsuUL' h37 h38)
  have hLVI : L ≤ Subgroup.normalizer (VI T L I J w : Set G) :=
    c.le.trans (le_sup_left.trans (le_normalizer_VI T L I J w))
  have hTwVI : Tw ≤ Subgroup.normalizer (VI T L I J w : Set G) :=
    le_sup_right.trans (le_normalizer_VI T L I J w)
  have hLY : L ≤ Subgroup.normalizer ((VI T L I J w ⊓ fsuUL T L I : Subgroup G) : Set G) :=
    fun l hl => mem_normalizer_inf' (hLVI hl) (le_normalizer_fsuUL T L I hl)
  have hTwY : Tw ≤ Subgroup.normalizer ((VI T L I J w ⊓ fsuUL T L I : Subgroup G) : Set G) :=
    fun s hs => mem_normalizer_inf' (hTwVI hs) (hTwV1 hs)
  have hfix : fsuUL T L I ⊓ Subgroup.centralizer (Tw : Set G) ≤
      VI T L I J w ⊓ fsuUL T L I := le_inf (le_conjClosure _ _) inf_le_left
  by_cases hC : cV1 T L I = ⊥
  · have hC' : (Subgroup.centralizer (L : Set G)).subgroupOf (fsuUL T L I) = ⊥ :=
      (cV1_eq h37 h38 hyp h1011 c.ht c.htn) ▸ hC
    rcases irrG_or_case5 (modCase_of h37 h38 hyp h1011 h1027 c.ht c.htn) hC' hK8a hK8b with
      hirr | ⟨s, hs, W, -, hLW, hsup, hinf, hirrW, hni⟩
    · obtain ⟨u, huV, hu1, huC⟩ :=
        exists_mem_centralizer_ne_one hT2 hV1T inf_le_left hTwV1 hirr.1
      rcases hirr.2 _ inf_le_right hLY with h | h
      · exfalso
        have hu : u ∈ VI T L I J w ⊓ fsuUL T L I := hfix ⟨huV, huC⟩
        rw [h, Subgroup.mem_bot] at hu
        exact hu1 hu
      · exact h ▸ inf_le_left
    · have hc : ∀ a ∈ W ⊔ CFSG.conjugate W s, ∀ b ∈ W ⊔ CFSG.conjugate W s, a * b = b * a :=
        fun a ha b hb => fsuVM_comm hyp (hV1V (hsup ▸ ha)) (hV1V (hsup ▸ hb))
      have key := le_of_case5 (T := Tw) (P := T) (Y := VI T L I J w ⊓ fsuUL T L I) hc hinf hLW
        (le_normalizer_conjugate_of' hs hLW) hirrW (irrG_conjugate hirrW hs) hni
        (by rw [hsup]; exact inf_le_right) hLY hTwY (hTw1.trans inf_le_right)
        (by rw [hsup]; exact hTwV1) hT2 (by rw [hsup]; exact hV1T) inf_le_left
        (by rw [hsup]; exact hfix)
      rw [hsup] at key
      exact key.trans inf_le_left
  ·
    have h3' : ¬ Case10_1_1Three T L I := h3.resolve_right hC
    have hcv : fsuCVM T L I ≠ ⊥ := by
      intro h
      apply hC
      rw [eq_bot_iff]
      intro x hx
      have hx' : (x : G) ∈ fsuCVM T L I := ⟨hV1V x.2, Subgroup.mem_subgroupOf.mp hx⟩
      rw [h, Subgroup.mem_bot] at hx'
      exact Subgroup.mem_bot.mpr (Subtype.ext hx')
    obtain ⟨n, h1⟩ : ∃ n, Case10_1_1One T L I n := by
      by_contra h1
      exact hcv ((h1012 G T L I hyp).2.2.2.2.2.2.1 (not_or.mpr ⟨h1, h3'⟩))
    obtain ⟨x, hxV1, hxC, hxT1⟩ := SecA.exists_mem_centralizer_T1_of_case_one h37 h38 h322 hyp h1
    have hxY : x ∈ VI T L I J w ⊓ fsuUL T L I :=
      hfix ⟨hxV1, Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hTw1) hxT1⟩
    have hxL : x ∉ Subgroup.centralizer (L : Set G) := by
      intro hxL
      have : (⟨x, hxV1⟩ : ↥(fsuUL T L I)) ∈ cV1 T L I := by
        rw [cV1_eq h37 h38 hyp h1011 c.ht c.htn]
        exact Subgroup.mem_subgroupOf.mpr hxL
      exact hxC ⟨hV1V hxV1, Subgroup.mem_subgroupOf.mp this⟩
    exact (le_of_case_one hyp h1 inf_le_right hLY hxY hxL).trans inf_le_left

end Conf

end CFSG.Quasithin.Vol2.Ch10.SecC
