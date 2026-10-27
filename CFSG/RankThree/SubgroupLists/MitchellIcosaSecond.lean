module

public import CFSG.RankThree.SubgroupLists.MitchellCharacter

public section

namespace CFSG.RankThree.SubgroupLists

open Matrix CFSG.Assembly.LowTwoRank Module

local notation "V₄" => Fin 2 ⊕ Fin 2

variable {K : Type} [Field K]

section Basis

variable (h2 : (2 : K) ≠ 0) {d e f u w a : Matrix V₄ V₄ K}
  (hdM : d ∈ (cliffSpace : Submodule K _)) (heM : e ∈ (cliffSpace : Submodule K _))
  (hfM : f ∈ (cliffSpace : Submodule K _)) (huM : u ∈ (cliffSpace : Submodule K _))
  (hwM : w ∈ (cliffSpace : Submodule K _)) (haM : a ∈ (cliffSpace : Submodule K _))
  (hind : ∀ x y z : K, x • d + y • e + z • f = 0 → x = 0 ∧ y = 0 ∧ z = 0)
  (hu : cliffB u d = 0 ∧ cliffB u e = 0 ∧ cliffB u f = 0)
  (hw : cliffB w d = 0 ∧ cliffB w e = 0 ∧ cliffB w f = 0) (huw : cliffB u w = 0)
  (hQu : cliffB u u ≠ 0) (hQw : cliffB w w ≠ 0)
include h2 hdM heM hfM huM hwM haM hind hu hw huw hQu hQw

theorem exists_eq_comb_of_orth :
    ∃ x y z s t : K, a = x • d + y • e + z • f + s • u + t • w := by
  classical
  set M := (cliffSpace : Submodule K (Matrix V₄ V₄ K))
  let v : Fin 5 → M := ![⟨d, hdM⟩, ⟨e, heM⟩, ⟨f, hfM⟩, ⟨u, huM⟩, ⟨w, hwM⟩]
  have hli : LinearIndependent K v := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have hg' : g 0 • d + g 1 • e + g 2 • f + g 3 • u + g 4 • w = 0 := by
      simpa [Fin.sum_univ_five, v] using congrArg Subtype.val hg
    have hpair : ∀ Z : Matrix V₄ V₄ K, cliffB Z (g 0 • d + g 1 • e + g 2 • f + g 3 • u + g 4 • w)
        = 0 := fun Z => by rw [hg', cliffB_comm, cliffB_zero_left]
    have h3 : g 3 * cliffB u u = 0 := by
      have := hpair u
      simp only [cliffB_add_right, cliffB_smul_right, hu.1, hu.2.1, hu.2.2, huw] at this
      linear_combination this
    have h4 : g 4 * cliffB w w = 0 := by
      have := hpair w
      simp only [cliffB_add_right, cliffB_smul_right, hw.1, hw.2.1, hw.2.2] at this
      rw [cliffB_comm w u, huw] at this
      linear_combination this
    have hg3 := (mul_eq_zero.mp h3).resolve_right hQu
    have hg4 := (mul_eq_zero.mp h4).resolve_right hQw
    rw [hg3, hg4, zero_smul, zero_smul, add_zero, add_zero] at hg'
    obtain ⟨h0, h1, h2'⟩ := hind _ _ _ hg'
    intro i
    fin_cases i <;> assumption
  have hspan : Submodule.span K (Set.range v) = ⊤ :=
    hli.span_eq_top_of_card_eq_finrank' (by rw [Fintype.card_fin, finrank_cliffSpace h2])
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp
    (show (⟨a, haM⟩ : M) ∈ Submodule.span K (Set.range v) by rw [hspan]; trivial)
  refine ⟨c 0, c 1, c 2, c 3, c 4, ?_⟩
  simpa [Fin.sum_univ_five, v] using (congrArg Subtype.val hc).symm

theorem mem_span_pair_of_orth_three (ha : cliffB a d = 0 ∧ cliffB a e = 0 ∧ cliffB a f = 0) :
    ∃ x y : K, a = x • u + y • w := by
  have hwu : cliffB w u = 0 := by rw [cliffB_comm, huw]
  set x := cliffB a u / cliffB u u
  set y := cliffB a w / cliffB w w
  have hx : x * cliffB u u = cliffB a u := div_mul_cancel₀ _ hQu
  have hy : y * cliffB w w = cliffB a w := div_mul_cancel₀ _ hQw
  refine ⟨x, y, ?_⟩
  have h0 : a - x • u - y • w = 0 := by
    refine eq_zero_of_cliffB_eq_zero h2 (sub_mem (sub_mem haM (Submodule.smul_mem _ _ huM))
      (Submodule.smul_mem _ _ hwM)) fun Y hY => ?_
    obtain ⟨c₁, c₂, c₃, c₄, c₅, rfl⟩ :=
      exists_eq_comb_of_orth h2 hdM heM hfM huM hwM hY hind hu hw huw hQu hQw
    simp only [cliffB_add_right, cliffB_smul_right, cliffB_sub_left, cliffB_smul_left, ha.1, ha.2.1,
      ha.2.2, hu.1, hu.2.1, hu.2.2, hw.1, hw.2.1, hw.2.2, hwu, huw, hx, hy]
    ring
  rw [sub_sub, sub_eq_zero] at h0
  rw [h0]

theorem mem_span_three_of_orth_pair (ha : cliffB a u = 0 ∧ cliffB a w = 0) :
    ∃ x y z : K, a = x • d + y • e + z • f := by
  obtain ⟨x, y, z, s, t, rfl⟩ :=
    exists_eq_comb_of_orth h2 hdM heM hfM huM hwM haM hind hu hw huw hQu hQw
  have hwu : cliffB w u = 0 := by rw [cliffB_comm, huw]
  have h1 := ha.1
  have h2' := ha.2
  rw [cliffB_comm] at h1 h2'
  simp only [cliffB_add_right, cliffB_smul_right, hu.1, hu.2.1, hu.2.2, huw] at h1
  simp only [cliffB_add_right, cliffB_smul_right, hw.1, hw.2.1, hw.2.2, hwu] at h2'
  have hs : s = 0 := (mul_eq_zero.mp (by linear_combination h1)).resolve_right hQu
  have ht : t = 0 := (mul_eq_zero.mp (by linear_combination h2')).resolve_right hQw
  exact ⟨x, y, z, by rw [hs, ht, zero_smul, zero_smul, add_zero, add_zero]⟩

end Basis

section Quasisimple

variable [Finite K] {p : ℕ} [Fact p.Prime] [CharP K p] {G : Subgroup (GL V₄ K)}

local notation "⟪" x "⟫" => (((x : _) : GL V₄ K) : Matrix V₄ V₄ K)

theorem forall_conj_mem_of_orth (hp2 : p ≠ 2) (hGS : G ≤ StatedSp 2 K) (hq : CFSG.IsQuasisimple G)
    (hZ : ∀ z ∈ Subgroup.center G, (z : GL V₄ K) = 1 ∨ (z : GL V₄ K) = -1)
    (hneg : (-1 : GL V₄ K) ∈ G) {t : G} (ht : IsNCInv (t : GL V₄ K)) {P : Set (Matrix V₄ V₄ K)}
    (htP : ⟪t⟫ ∈ P)
    (horth : ∀ g g' : G, ⟪g * t * g⁻¹⟫ ∉ P → ⟪g' * t * g'⁻¹⟫ ∈ P →
      cliffB ⟪g * t * g⁻¹⟫ ⟪g' * t * g'⁻¹⟫ = 0) :
    ∀ g : G, ⟪g * t * g⁻¹⟫ ∈ P := by
  classical
  have h2 : (2 : K) ≠ 0 := two_ne_zero_of_charP hp2
  have hN : ∀ g : G, IsNCInv ((g * t * g⁻¹ : G) : GL V₄ K) := conj_isNCInv hGS ht
  have : Group.IsPerfect G := hq.1
  have : IsSimpleGroup (G ⧸ Subgroup.center G) := hq.2.1
  set A := Subgroup.closure {ω : G ⧸ Subgroup.center G | ∃ g : G,
    ω = QuotientGroup.mk (g * t * g⁻¹) ∧ ⟪g * t * g⁻¹⟫ ∈ P}
  have hcen : ∀ g : G, ⟪g * t * g⁻¹⟫ ∉ P →
      A ≤ Subgroup.centralizer {(QuotientGroup.mk (g * t * g⁻¹) : G ⧸ Subgroup.center G)} := by
    intro g hP
    rw [Subgroup.closure_le]
    rintro _ ⟨g', rfl, hg'⟩
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
    exact ((mk_commute_iff h2 hZ hneg (hN g) (hN g')).mpr
      (Or.inr (Or.inr (horth g g' hP hg')))).symm
  have hAnorm : A.Normal := by
    refine Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp ?_)
    rw [← closure_ncImage_eq_top hq hZ hneg ht, Subgroup.closure_le]
    intro ω hω
    obtain ⟨g, rfl⟩ := exists_eq_mk_of_mem_ncImage hω
    by_cases hP : ⟪g * t * g⁻¹⟫ ∈ P
    · exact Subgroup.le_normalizer (Subgroup.subset_closure ⟨g, rfl, hP⟩)
    · refine Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun a ha => ?_)
      exact Subgroup.mem_centralizer_singleton_iff.mp (hcen g hP ha)
  have hτ1 : (QuotientGroup.mk t : G ⧸ Subgroup.center G) ≠ 1 := by
    rw [Ne, mk_eq_one_iff hZ hneg]
    rintro (h | h)
    · exact ht.2.2.1 h
    · exact ht.2.2.2 h
  have hAtop : A = ⊤ := by
    refine hAnorm.eq_bot_or_eq_top.resolve_left fun h => hτ1 ?_
    rw [← Subgroup.mem_bot, ← h]
    exact Subgroup.subset_closure ⟨1, by simp, by simpa using htP⟩
  intro g
  by_contra hP
  have hc : (QuotientGroup.mk (g * t * g⁻¹) : G ⧸ Subgroup.center G) ∈
      Subgroup.center (G ⧸ Subgroup.center G) := by
    rw [Subgroup.mem_center_iff]
    intro ω
    exact Subgroup.mem_centralizer_singleton_iff.mp (hcen g hP (hAtop ▸ Subgroup.mem_top ω))
  rw [Group.IsPerfect.center_quotient_center_eq_bot G, Subgroup.mem_bot,
    mk_eq_one_iff hZ hneg] at hc
  rcases hc with h | h
  · exact (hN g).2.2.1 h
  · exact (hN g).2.2.2 h

theorem exists_conj_not_mem_span_three (hp2 : p ≠ 2) (hGS : G ≤ StatedSp 2 K)
    (hq : CFSG.IsQuasisimple G)
    (hZ : ∀ z ∈ Subgroup.center G, (z : GL V₄ K) = 1 ∨ (z : GL V₄ K) = -1)
    (hneg : (-1 : GL V₄ K) ∈ G) {t : G} (ht : IsNCInv (t : GL V₄ K)) (e f : G)
    (heD : ∃ g : G, e = g * t * g⁻¹) (hfD : ∃ g : G, f = g * t * g⁻¹)
    (hβ : cliffB ⟪t⟫ ⟪e⟫ * cliffB ⟪t⟫ ⟪e⟫ ≠ 1) (hfP : ∀ a b : K, ⟪f⟫ ≠ a • ⟪t⟫ + b • ⟪e⟫)
    (hγ : cliffB ⟪t⟫ ⟪f⟫ ≠ 0 ∨ cliffB ⟪e⟫ ⟪f⟫ ≠ 0) :
    ∃ g : G, (∀ a b c : K, ⟪g * t * g⁻¹⟫ ≠ a • ⟪t⟫ + b • ⟪e⟫ + c • ⟪f⟫) ∧
      (cliffB ⟪t⟫ ⟪g * t * g⁻¹⟫ ≠ 0 ∨ cliffB ⟪e⟫ ⟪g * t * g⁻¹⟫ ≠ 0) := by
  classical
  have h2 : (2 : K) ≠ 0 := two_ne_zero_of_charP hp2
  have hN : ∀ g : G, IsNCInv ((g * t * g⁻¹ : G) : GL V₄ K) := conj_isNCInv hGS ht
  have heN : IsNCInv (e : GL V₄ K) := by obtain ⟨g, hg⟩ := heD; rw [hg]; exact hN g
  have hfN : IsNCInv (f : GL V₄ K) := by obtain ⟨g, hg⟩ := hfD; rw [hg]; exact hN g
  have hM : ∀ x : G, IsNCInv (x : GL V₄ K) → ⟪x⟫ ∈ (cliffSpace : Submodule K _) := fun x hx =>
    (mem_cliffSpace_of_involution h2 hx.1 hx.2.1 hx.2.2.1 hx.2.2.2).1
  have hsq : ∀ x : G, IsNCInv (x : GL V₄ K) → cliffB ⟪x⟫ ⟪x⟫ = 1 := fun x hx =>
    cliffB_eq_one_of_mul_self h2 (by rw [← Units.val_mul, hx.2.1, Units.val_one])
  have hff : ⟪f⟫ * ⟪f⟫ = 1 := by rw [← Units.val_mul, hfN.2.1, Units.val_one]
  by_contra hcon
  push Not at hcon
  have hrefl : ∀ g : G, ⟪f * g * t * (f * g)⁻¹⟫ = (2 * cliffB ⟪f⟫ ⟪g * t * g⁻¹⟫) • ⟪f⟫ -
      ⟪g * t * g⁻¹⟫ := by
    intro g
    have e1 : (f * g * t * (f * g)⁻¹ : G) = f * (g * t * g⁻¹) * f⁻¹ := by group
    have hfinv : (f : GL V₄ K)⁻¹ = f := inv_eq_of_mul_eq_one_right hfN.2.1
    rw [← mul_mul_eq_reflection h2 (hM f hfN) hff (hM _ (hN g)), e1]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, hfinv, Units.val_mul]
  have hsub : ∀ (Z Y₁ Y₂ : Matrix V₄ V₄ K) (c : K),
      cliffB Z (c • Y₁ - Y₂) = c * cliffB Z Y₁ - cliffB Z Y₂ := fun Z Y₁ Y₂ c => by
    rw [sub_eq_add_neg, cliffB_add_right, show -Y₂ = (-1 : K) • Y₂ by simp, cliffB_smul_right,
      cliffB_smul_right]
    ring
  have hstep1 : ∀ g : G, (∀ a b c : K, ⟪g * t * g⁻¹⟫ ≠ a • ⟪t⟫ + b • ⟪e⟫ + c • ⟪f⟫) →
      cliffB ⟪f⟫ ⟪g * t * g⁻¹⟫ = 0 := by
    intro g hg
    have hnot : ∀ a b c : K, ⟪f * g * t * (f * g)⁻¹⟫ ≠ a • ⟪t⟫ + b • ⟪e⟫ + c • ⟪f⟫ := by
      intro a b c h
      refine hg (-a) (-b) (2 * cliffB ⟪f⟫ ⟪g * t * g⁻¹⟫ - c) ?_
      calc ⟪g * t * g⁻¹⟫
          = (2 * cliffB ⟪f⟫ ⟪g * t * g⁻¹⟫) • ⟪f⟫ - (a • ⟪t⟫ + b • ⟪e⟫ + c • ⟪f⟫) := by
            rw [← h, hrefl g]
            abel
        _ = (-a) • ⟪t⟫ + (-b) • ⟪e⟫ + (2 * cliffB ⟪f⟫ ⟪g * t * g⁻¹⟫ - c) • ⟪f⟫ := by module
    have h1 := (hcon (f * g) hnot).1
    have h2' := (hcon (f * g) hnot).2
    rw [hrefl, hsub, (hcon g hg).1] at h1
    rw [hrefl, hsub, (hcon g hg).2] at h2'
    have h7 : 2 * cliffB ⟪f⟫ ⟪g * t * g⁻¹⟫ = 0 := by
      rcases hγ with h | h
      · exact (mul_eq_zero.mp (by linear_combination h1)).resolve_right h
      · exact (mul_eq_zero.mp (by linear_combination h2')).resolve_right h
    exact (mul_eq_zero.mp h7).resolve_left h2
  have hall : ∀ g : G, ∃ a b c : K, ⟪g * t * g⁻¹⟫ = a • ⟪t⟫ + b • ⟪e⟫ + c • ⟪f⟫ := by
    refine forall_conj_mem_of_orth (P := {X | ∃ a b c : K, X = a • ⟪t⟫ + b • ⟪e⟫ + c • ⟪f⟫}) hp2 hGS
      hq hZ hneg ht ⟨1, 0, 0, by simp⟩ fun g g' hg hg' => ?_
    simp only [Set.mem_setOf_eq, not_exists] at hg
    obtain ⟨a, b, c, hab⟩ := hg'
    rw [hab, cliffB_add_right, cliffB_add_right, cliffB_smul_right, cliffB_smul_right,
      cliffB_smul_right, cliffB_comm _ ⟪t⟫, cliffB_comm _ ⟪e⟫, cliffB_comm _ ⟪f⟫,
      (hcon g hg).1, (hcon g hg).2, hstep1 g hg]
    ring
  obtain ⟨u, huM, huT, huE, huF, hQu⟩ := exists_orth_cliffQ_ne_zero h2 (hM t ht) (hM e heN)
    (hM f hfN) (hsq t ht) (hsq e heN) hβ hfP
  refine false_of_forall_conj_anticommute h2 hq hZ hneg ht (q := u)
    (by rintro rfl; exact hQu (cliffB_zero_left 0)) fun g => ?_
  obtain ⟨a, b, c, hab⟩ := hall g
  refine (mul_eq_neg_mul_iff h2 (hM _ (hN g)) huM).mpr ?_
  rw [hab, cliffB_add_left, cliffB_add_left, cliffB_smul_left, cliffB_smul_left, cliffB_smul_left,
    cliffB_comm ⟪t⟫ u, cliffB_comm ⟪e⟫ u, cliffB_comm ⟪f⟫ u, huT, huE, huF]
  ring

end Quasisimple

end CFSG.RankThree.SubgroupLists
