module

public import Mathlib.FieldTheory.Finite.GaloisField
public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.GroupTheory.SpecificGroups.Dihedral
public import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup
import CFSG.GH74.Uniqueness.Bender.Dickson
import CFSG.Timmesfeld.RankOne.SL2

public section

namespace CFSG.Quasithin.SimsG4

open Matrix

theorem dihedral_odd_normal_eq_top {z : ℕ} (hz : Odd z) {X : Subgroup (DihedralGroup z)}
    (hX : X.Normal) {a b : DihedralGroup z} (ha : a ∈ X) (hb : b ∈ X) (hab : a * b ≠ b * a) :
    X = ⊤ := by
  obtain ⟨i, hi⟩ : ∃ i, DihedralGroup.sr i ∈ X := by
    rcases a with i | i
    · rcases b with j | j
      · exact (hab (by rw [DihedralGroup.r_mul_r, DihedralGroup.r_mul_r, add_comm])).elim
      · exact ⟨j, hb⟩
    · exact ⟨i, ha⟩
  have hr2 : ∀ j : ZMod z, DihedralGroup.r (j + j) ∈ X := fun j => by
    have h := X.mul_mem hi (hX.conj_mem _ hi (DihedralGroup.r (-j)))
    rw [DihedralGroup.inv_r, DihedralGroup.r_mul_sr, DihedralGroup.sr_mul_r,
      DihedralGroup.sr_mul_sr] at h
    convert h using 2
    ring
  obtain ⟨w, hw⟩ := hz
  have hc : ((w + 1 : ℕ) : ZMod z) + ((w + 1 : ℕ) : ZMod z) = 1 := by
    have h0 : ((2 * w + 1 : ℕ) : ZMod z) = 0 := by
      rw [← hw]
      exact ZMod.natCast_self z
    push_cast at h0 ⊢
    linear_combination h0
  have hr : ∀ k : ZMod z, DihedralGroup.r k ∈ X := fun k => by
    have h := hr2 (k * ((w + 1 : ℕ) : ZMod z))
    rwa [← mul_add, hc, mul_one] at h
  refine eq_top_iff.2 fun g _ => ?_
  rcases g with k | k
  · exact hr k
  · have h := X.mul_mem hi (hr (k - i))
    rw [DihedralGroup.sr_mul_r] at h
    convert h using 2
    ring

theorem eq_top_of_mulEquiv_dihedral_odd {D : Type*} [Group D] {z : ℕ} (hz : Odd z)
    (e : D ≃* DihedralGroup z) {Y : Subgroup D} (hY : Y.Normal) {a b : D} (ha : a ∈ Y)
    (hb : b ∈ Y) (hab : a * b ≠ b * a) : Y = ⊤ := by
  have hmap : Y.map e.toMonoidHom = ⊤ :=
    dihedral_odd_normal_eq_top hz (hY.map e.toMonoidHom e.surjective)
      (Subgroup.mem_map_of_mem _ ha) (Subgroup.mem_map_of_mem _ hb) fun h =>
        hab (e.injective (by simpa only [map_mul, MulEquiv.coe_toMonoidHom] using h))
  refine eq_top_iff.2 fun g _ => ?_
  have hg : e g ∈ Y.map e.toMonoidHom := by
    rw [hmap]
    exact Subgroup.mem_top _
  obtain ⟨y, hy, hyg⟩ := Subgroup.mem_map.mp hg
  rwa [← e.injective hyg]

theorem eq_top_of_mulEquiv_simple {D S : Type*} [Group D] [Group S] [IsSimpleGroup S]
    (e : D ≃* S) {Y : Subgroup D} (hY : Y.Normal) (hne : Y ≠ ⊥) : Y = ⊤ :=
  haveI := e.isSimpleGroup
  haveI := hY
  (IsSimpleGroup.eq_bot_or_eq_top_of_normal Y).resolve_left hne

theorem eq_top_of_card_eq_six {D : Type*} [Group D] (hD : Nat.card D = 6) {Y : Subgroup D}
    {a b : D} (ha : a ∈ Y) (hb : b ∈ Y) (hab : a * b ≠ b * a) : Y = ⊤ := by
  have : Finite D := Nat.finite_of_card_ne_zero (by rw [hD]; norm_num)
  by_contra hY
  have hmul := Y.card_mul_index
  have h1 : Y.index ≠ 1 := fun h => hY (Subgroup.index_eq_one.mp h)
  have hpos : 0 < Nat.card Y := Nat.card_pos
  obtain ⟨c, hc⟩ : ∃ c, Nat.card Y = c := ⟨_, rfl⟩
  rw [hD, hc] at hmul
  rw [hc] at hpos
  have hle : c ≤ 6 := Nat.le_of_dvd (by norm_num) ⟨Y.index, hmul.symm⟩
  have hcyc : IsCyclic Y := by
    interval_cases c
    · exact isCyclic_of_card_dvd_prime (p := 2) (by rw [hc]; norm_num)
    · exact isCyclic_of_card_dvd_prime (p := 2) (by rw [hc])
    · exact isCyclic_of_card_dvd_prime (p := 3) (by rw [hc])
    · omega
    · omega
    · omega
  exact hab (congrArg Subtype.val
    ((IsCyclic.isMulCommutative (α := Y)).is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩))

theorem mem_of_mul_self_eq_one_of_sup {G : Type*} [Group G] {N C : Subgroup G} (hN : N.Normal)
    (hdisj : Disjoint N C) (hsup : N ⊔ C = ⊤) (hC : Odd (Nat.card C)) {g : G} (hg : g * g = 1) :
    g ∈ N := by
  obtain ⟨x, hx, c, hc, rfl⟩ :=
    (Subgroup.mem_sup_of_normal_left (hs := hN)).mp (hsup ▸ Subgroup.mem_top g : g ∈ N ⊔ C)
  have hcxc : c * x * c = x⁻¹ :=
    eq_inv_of_mul_eq_one_right (by simpa only [mul_assoc] using hg)
  have hcc : c * c = 1 := by
    refine Subgroup.disjoint_def.mp hdisj ?_ (C.mul_mem hc hc)
    have h : c * c = (c * x * c⁻¹)⁻¹ * (c * x * c) := by group
    rw [h, hcxc]
    exact N.mul_mem (N.inv_mem (hN.conj_mem x hx c)) (N.inv_mem hx)
  have hord : orderOf c ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two, hcc])
  have hordC : orderOf c ∣ Nat.card C := Subgroup.orderOf_dvd_natCard C hc
  have hc1 : c = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).1 hord with h | h
    · exact orderOf_eq_one_iff.mp h
    · rw [h] at hordC
      exact absurd (even_iff_two_dvd.mpr hordC) (Nat.not_even_iff_odd.mpr hC)
  rw [hc1, mul_one]
  exact hx

theorem sl2_subgroup_cases {F : Type} [Field F] [Finite F]
    [CharP F 2] {n : ℕ} (hn : Nat.card F = 2 ^ n)
    (M : Subgroup (SpecialLinearGroup (Fin 2) F)) :
    (∀ x ∈ M, ∀ y ∈ M, x * x = 1 → y * y = 1 → x * y = y * x) ∨
      (∃ z : ℕ, Odd z ∧ (z ∣ 2 ^ n + 1 ∨ z ∣ 2 ^ n - 1) ∧ Nonempty (M ≃* DihedralGroup z)) ∨
      (2 ∣ n ∧ Nonempty (M ≃* alternatingGroup (Fin 5))) ∨
      ∃ m : ℕ, m ≠ 0 ∧ m ∣ n ∧
        Nonempty (M ≃* ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 m)) := by
  have hn1 : 1 ≤ n := by
    by_contra h0
    have h := Finite.one_lt_card (α := F)
    rw [hn, show n = 0 by omega, pow_zero] at h
    exact lt_irrefl 1 h
  have hodd1 := CFSG.GH74.Uniqueness.Bender.odd_two_pow_sub_one n hn1
  have hodd2 := CFSG.GH74.Uniqueness.Bender.odd_two_pow_add_one n hn1
  have hg : Nat.gcd (2 ^ n - 1) 2 = 1 :=
    Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 hodd1.not_two_dvd_nat)
  let ε := (CFSG.Timmesfeld.RankOne.psl2EquivSL2 F).symm
  let eM := Subgroup.equivMapOfInjective M ε.toMonoidHom ε.injective
  have hcomm : ∀ {K : Type} [Group K] (φ : M ≃* K),
      (∀ a b : K, a * a = 1 → b * b = 1 → a * b = b * a) →
        ∀ x ∈ M, ∀ y ∈ M, x * x = 1 → y * y = 1 → x * y = y * x := by
    intro K _ φ h x hx y hy hx2 hy2
    have h1 : (⟨x, hx⟩ : M) * ⟨x, hx⟩ = 1 := Subtype.ext hx2
    have h2 : (⟨y, hy⟩ : M) * ⟨y, hy⟩ = 1 := Subtype.ext hy2
    have h3 := h (φ ⟨x, hx⟩) (φ ⟨y, hy⟩) (by rw [← map_mul, h1, map_one])
      (by rw [← map_mul, h2, map_one])
    have h4 : φ (⟨x, hx⟩ * ⟨y, hy⟩) = φ (⟨y, hy⟩ * ⟨x, hx⟩) := by
      rw [map_mul, map_mul]
      exact h3
    exact congrArg Subtype.val (φ.injective h4)
  rcases CFSG.Glauberman.Dickson.huppert_II_8_27_dickson_psl2_subgroup_classification
      (p := 2) (f := n) hn (M.map ε.toMonoidHom) with
    hEl | ⟨z, -, -, hcyc⟩ | ⟨z, hz, -, ⟨hD⟩⟩ | ⟨-, ⟨hA4⟩⟩ | ⟨h16, -⟩ | ⟨h5, ⟨hA5⟩⟩ |
      ⟨m, t, -, ht, N, C, hN, hNel, -, -, hCcard, hdisj, hsup⟩ | ⟨m, hm0, hmn, ⟨hP⟩⟩ |
      ⟨m, hm0, hmn, ⟨hPGL⟩⟩
  ·
    exact Or.inl (hcomm eM fun a b _ _ => hEl.toIsMulCommutative.is_comm.comm a b)
  ·
    have : IsCyclic (M.map ε.toMonoidHom) := hcyc
    exact Or.inl (hcomm eM fun a b _ _ => IsCyclic.isMulCommutative.is_comm.comm a b)
  ·
    rw [hn, hg, Nat.div_one, Nat.div_one] at hz
    exact Or.inr (Or.inl ⟨z, hz.elim (Odd.of_dvd_nat hodd1) (Odd.of_dvd_nat hodd2), hz.symm,
      ⟨eM.trans hD⟩⟩)
  ·
    exact Or.inl (hcomm (eM.trans hA4) CFSG.GH74.Uniqueness.Bender.A4_involutions_commute)
  ·
    exact absurd h16 (CFSG.GH74.Uniqueness.Bender.not_sixteen_dvd n hn1)
  ·
    refine Or.inr (Or.inr (Or.inl ⟨?_, ⟨eM.trans hA5⟩⟩))
    exact even_iff_two_dvd.mp
      (CFSG.GH74.Uniqueness.Bender.even_of_five_dvd n (h5.resolve_left (by norm_num)))
  ·
    have hCodd : Odd (Nat.card C) := hCcard ▸
      Odd.of_dvd_nat hodd1 (ht.trans (Nat.div_dvd_of_dvd (Nat.gcd_dvd_left _ _)))
    refine Or.inl (hcomm eM fun a b ha hb => ?_)
    have haN := mem_of_mul_self_eq_one_of_sup hN hdisj hsup hCodd ha
    have hbN := mem_of_mul_self_eq_one_of_sup hN hdisj hsup hCodd hb
    exact congrArg Subtype.val (hNel.toIsMulCommutative.is_comm.comm (⟨a, haN⟩ : N) ⟨b, hbN⟩)
  ·
    exact Or.inr (Or.inr (Or.inr ⟨m, hm0, hmn, ⟨eM.trans hP⟩⟩))
  ·
    obtain ⟨e⟩ := CFSG.GH74.Uniqueness.Bender.nonempty_pgl2_mulEquiv_psl2 m
      (Nat.one_le_iff_ne_zero.mpr hm0)
    exact Or.inr (Or.inr (Or.inr ⟨m, hm0, (dvd_mul_left m 2).trans hmn,
      ⟨(eM.trans hPGL).trans e⟩⟩))

theorem sl2_invol_subgroup {F : Type} [Field F] [Finite F]
    [CharP F 2] (n : ℕ) (hn : Nat.card F = 2 ^ n)
    (T : Set (Matrix.SpecialLinearGroup (Fin 2) F)) (hT : ∀ t ∈ T, t * t = 1)
    (hnc : ∃ s ∈ T, ∃ t ∈ T, s * t ≠ t * s) :
    ((∃ k : ℕ, k ∣ n ∧ Nonempty (↥(Subgroup.closure T) ≃*
          Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 k))) ∨
      ∃ m : ℕ, (m ∣ 2 ^ n + 1 ∨ m ∣ 2 ^ n - 1) ∧
        Nonempty (↥(Subgroup.closure T) ≃* DihedralGroup m)) ∧
    Subgroup.normalizer (Subgroup.closure T : Set (Matrix.SpecialLinearGroup (Fin 2) F)) =
      Subgroup.closure T := by
  obtain ⟨s, hs, t, ht, hst⟩ := hnc
  have hsX : s ∈ Subgroup.closure T := Subgroup.subset_closure hs
  have htX : t ∈ Subgroup.closure T := Subgroup.subset_closure ht
  refine ⟨?_, ?_⟩
  · rcases sl2_subgroup_cases hn (Subgroup.closure T) with hc | ⟨z, -, hz, ⟨e⟩⟩ |
      ⟨h2, ⟨e⟩⟩ | ⟨m, -, hmn, ⟨e⟩⟩
    · exact absurd (hc s hsX t htX (hT s hs) (hT t ht)) hst
    · exact Or.inr ⟨z, hz, ⟨e⟩⟩
    ·
      open CFSG.ProperTwoGeneratedCore.BenderFacts in
      obtain ⟨e5⟩ := nonempty_psl2Binary_two_mulEquiv_alternatingGroup_five
      exact Or.inl ⟨2, h2,
        ⟨(e.trans e5.symm).trans (CFSG.Timmesfeld.RankOne.psl2EquivSL2 (GaloisField 2 2))⟩⟩
    · exact Or.inl ⟨m, hmn, ⟨e.trans (CFSG.Timmesfeld.RankOne.psl2EquivSL2 (GaloisField 2 m))⟩⟩
  · set X := Subgroup.closure T
    set N := Subgroup.normalizer (X : Set (Matrix.SpecialLinearGroup (Fin 2) F))
    have hXN : X ≤ N := Subgroup.le_normalizer
    refine le_antisymm (Subgroup.subgroupOf_eq_top.mp ?_) hXN
    have hY : (X.subgroupOf N).Normal := Subgroup.normal_in_normalizer
    have hsY : (⟨s, hXN hsX⟩ : N) ∈ X.subgroupOf N := Subgroup.mem_subgroupOf.mpr hsX
    have htY : (⟨t, hXN htX⟩ : N) ∈ X.subgroupOf N := Subgroup.mem_subgroupOf.mpr htX
    have hstN : (⟨s, hXN hsX⟩ : N) * ⟨t, hXN htX⟩ ≠ ⟨t, hXN htX⟩ * ⟨s, hXN hsX⟩ :=
      fun h => hst (congrArg Subtype.val h)
    have hne : X.subgroupOf N ≠ ⊥ := by
      intro hbot
      have h1 := hsY
      rw [hbot, Subgroup.mem_bot] at h1
      exact hstN (by rw [h1, one_mul, mul_one])
    rcases sl2_subgroup_cases hn N with hc | ⟨z, hz, -, ⟨e⟩⟩ | ⟨-, ⟨e⟩⟩ | ⟨m, hm0, -, ⟨e⟩⟩
    · exact absurd (hc s (hXN hsX) t (hXN htX) (hT s hs) (hT t ht)) hst
    · exact eq_top_of_mulEquiv_dihedral_odd hz e hY hsY htY hstN
    · exact eq_top_of_mulEquiv_simple e hY hne
    · by_cases hm1 : m = 1
      · subst hm1
        refine eq_top_of_card_eq_six ?_ hsY htY hstN
        rw [Nat.card_congr e.toEquiv, CFSG.GH74.Uniqueness.Bender.card_psl2_even 1 le_rfl]
        norm_num
      · have : IsSimpleGroup (ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 m)) :=
          ProjectiveSpecialLinearGroup.rank_two_simple (by
            rw [GaloisField.card 2 m hm0]
            calc 4 = 2 ^ 2 := by norm_num
              _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) (by omega))
        exact eq_top_of_mulEquiv_simple e hY hne

end CFSG.Quasithin.SimsG4
