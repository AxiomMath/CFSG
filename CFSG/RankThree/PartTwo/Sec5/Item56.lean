module

public import CFSG.RankThree.PartTwo.Sec5.Item55
import CFSG.RankThree.PartTwo.Source.MinimalFaithfulCentralProduct

public section

namespace CFSG.RankThree.PartTwo.Sec5

open CFSG

universe u

variable {G : Type u} [Group G] [Finite G]

omit [Finite G] in
@[expose] def Statement51 (A S : Subgroup G) : Prop :=
  (Nat.card (A ⊓ Subgroup.centralizer (S : Set G) : Subgroup G) = 9 ∧
      S ⊓ Subgroup.centralizer (A : Set G) = ⊥ ∧
      CFSG.Assembly.IsElemAbelian 2 (omegaOneSub S) ∧ Nat.card (omegaOneSub S) = 4) ∨
    ∀ W : Subgroup G, W ≤ S → A ≤ Subgroup.normalizer (W : Set G) → IsMulCommutative W →
      IsCyclic W

omit [Finite G] in
structure IsNormalFourGroup (A S U : Subgroup G) : Prop where
  le : U ≤ S
  elemAbelian : CFSG.Assembly.IsElemAbelian 2 U
  card_eq : Nat.card U = 4
  le_normalizer_left : S ≤ Subgroup.normalizer (U : Set G)
  le_normalizer_right : A ≤ Subgroup.normalizer (U : Set G)

omit [Finite G] in
theorem eq_one_or_eq_of_mem_zpowers {w y : G} (hw : orderOf w = 2)
    (hy : y ∈ Subgroup.zpowers w) : y = 1 ∨ y = w := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  rw [← zpow_mod_orderOf, hw]
  rcases Int.emod_two_eq_zero_or_one k with h | h
  · left
    rw [show k % ((2 : ℕ) : ℤ) = 0 by exact_mod_cast h, zpow_zero]
  · right
    rw [show k % ((2 : ℕ) : ℤ) = 1 by exact_mod_cast h, zpow_one]

theorem le_centralizer_of_card_eq_two {A W : Subgroup G} (hW : Nat.card W = 2)
    (hAW : A ≤ Subgroup.normalizer (W : Set G)) : W ≤ Subgroup.centralizer (A : Set G) := by
  obtain ⟨w, hwW, hw1, rfl⟩ := exists_eq_zpowers_of_card_eq_prime Nat.prime_two hW
  have hord : orderOf w = 2 := by rw [← Nat.card_zpowers]; exact hW
  rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
  intro a ha
  have hconj : a * w * a⁻¹ ∈ Subgroup.zpowers w :=
    (Subgroup.mem_normalizer_iff.mp (hAW ha) w).mp hwW
  rcases eq_one_or_eq_of_mem_zpowers hord hconj with h1 | h1
  · exact absurd (by simpa using h1) hw1
  · calc a * w = a * w * a⁻¹ * a := by group
      _ = w * a := by rw [h1]

omit [Finite G] in
theorem isKleinFour_of_isElemAbelian {U : Subgroup G} (hU : CFSG.Assembly.IsElemAbelian 2 U)
    (hU4 : Nat.card U = 4) : IsKleinFour U := by
  refine ⟨hU4, ?_⟩
  have hdvd : Monoid.exponent U ∣ 2 := Monoid.exponent_dvd_of_forall_pow_eq_one fun x =>
    Subtype.ext (by simpa using hU.2 x x.2)
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
  · have : Subsingleton U := Monoid.exp_eq_one_iff.mp h
    have := Finite.card_le_one_iff_subsingleton.mpr this
    rw [hU4] at this
    norm_num at this
  · exact h

omit [Finite G] in
theorem eq_mul_of_fourGroup {U : Subgroup G} (hU : CFSG.Assembly.IsElemAbelian 2 U)
    (hU4 : Nat.card U = 4) {v w x : G} (hv : v ∈ U) (hw : w ∈ U) (hx : x ∈ U) (hv1 : v ≠ 1)
    (hw1 : w ≠ 1) (hvw : v ≠ w) (hx1 : x ≠ 1) (hxv : x ≠ v) (hxw : x ≠ w) : x = v * w := by
  have := isKleinFour_of_isElemAbelian hU hU4
  have h := IsKleinFour.eq_mul_of_ne_all (G := U) (x := ⟨v, hv⟩) (y := ⟨w, hw⟩) (z := ⟨x, hx⟩)
    (fun h => hv1 (congrArg Subtype.val h)) (fun h => hw1 (congrArg Subtype.val h))
    (fun h => hvw (congrArg Subtype.val h)) (fun h => hx1 (congrArg Subtype.val h))
    (fun h => hxv (congrArg Subtype.val h)) (fun h => hxw (congrArg Subtype.val h))
  exact congrArg Subtype.val h

omit [Finite G] in
theorem exists_ne_of_fourGroup {U : Subgroup G} (hU4 : Nat.card U = 4) (v : G) :
    ∃ w ∈ U, w ≠ 1 ∧ w ≠ v := by
  by_contra! hno
  have hsub : (U : Set G) ⊆ {1, v} := fun x hx => by
    by_cases hx1 : x = 1
    · exact Or.inl hx1
    · exact Or.inr (hno x hx hx1)
  have hcard : Nat.card U ≤ 2 := by
    calc Nat.card U = Nat.card (U : Set G) := rfl
      _ ≤ Nat.card ({1, v} : Set G) := Nat.card_mono (Set.toFinite _) hsub
      _ ≤ 2 := by
        rw [Nat.card_coe_set_eq]
        exact (Set.ncard_insert_le 1 {v}).trans (by rw [Set.ncard_singleton])
  omega

omit [Finite G] in
theorem mem_centralizer_of_fourGroup {U : Subgroup G} (hU : CFSG.Assembly.IsElemAbelian 2 U)
    (hU4 : Nat.card U = 4) {g v : G} (hg : g ∈ Subgroup.normalizer (U : Set G))
    (hg3 : g ^ 3 = 1) (hv : v ∈ U) (hv1 : v ≠ 1) (hgv : g * v = v * g) :
    g ∈ Subgroup.centralizer (U : Set G) := by
  obtain ⟨w, hw, hw1, hwv⟩ := exists_ne_of_fourGroup hU4 v
  have hv2 : v * v = 1 := by rw [← pow_two]; exact hU.2 v hv
  have hall : ∀ x ∈ U, x = 1 ∨ x = v ∨ x = w ∨ x = v * w := by
    intro x hx
    by_cases h1 : x = 1
    · exact Or.inl h1
    by_cases h2 : x = v
    · exact Or.inr (Or.inl h2)
    by_cases h3 : x = w
    · exact Or.inr (Or.inr (Or.inl h3))
    exact Or.inr (Or.inr (Or.inr
      (eq_mul_of_fourGroup hU hU4 hv hw hx hv1 hw1 (Ne.symm hwv) h1 h2 h3)))
  have hconj : ∀ x ∈ U, g * x * g⁻¹ ∈ U := fun x hx =>
    (Subgroup.mem_normalizer_iff.mp hg x).mp hx
  have hgv' : g * v * g⁻¹ = v := by rw [hgv, mul_inv_cancel_right]
  have hgw : g * w * g⁻¹ = w := by
    rcases hall _ (hconj w hw) with h | h | h | h
    · exact absurd (by simpa using h) hw1
    · exact absurd (mul_left_cancel (mul_right_cancel (h.trans hgv'.symm))) hwv
    · exact h
    ·
      have h2 : g * (v * w) * g⁻¹ = w := by
        calc g * (v * w) * g⁻¹ = (g * v * g⁻¹) * (g * w * g⁻¹) := by group
          _ = v * (v * w) := by rw [hgv', h]
          _ = w := by rw [← mul_assoc, hv2, one_mul]
      have hg3' : g * g * g = 1 := by rw [← pow_three']; exact hg3
      have h3 : (g * g * g) * w * (g * g * g)⁻¹ = v * w := by
        calc (g * g * g) * w * (g * g * g)⁻¹ = g * (g * (g * w * g⁻¹) * g⁻¹) * g⁻¹ := by
              group
          _ = v * w := by rw [h, h2, h]
      rw [hg3', one_mul, inv_one, mul_one] at h3
      exact absurd (by simpa using (congrArg (· * w⁻¹) h3).symm) hv1
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  have hx' : g * x * g⁻¹ = x := by
    rcases hall x hx with rfl | rfl | rfl | rfl
    · group
    · exact hgv'
    · exact hgw
    · calc g * (v * w) * g⁻¹ = (g * v * g⁻¹) * (g * w * g⁻¹) := by group
        _ = v * w := by rw [hgv', hgw]
  calc x * g = g * x * g⁻¹ * g := by rw [hx']
    _ = g * x := by group

theorem card_filter_pow_two_pow_le {B : Type*} [Group B] [Fintype B] [DecidableEq B]
    (hcomm : ∀ a b : B, a * b = b * a)
    (h1 : (Finset.univ.filter fun x : B => x ^ 2 = 1).card ≤ 2) (j : ℕ) :
    (Finset.univ.filter fun x : B => x ^ 2 ^ j = 1).card ≤ 2 ^ j := by
  induction j with
  | zero =>
    rw [pow_zero]
    refine le_of_eq ?_
    rw [Finset.card_eq_one]
    exact ⟨1, by ext x; simp⟩
  | succ j ih =>
    set T := Finset.univ.filter fun x : B => x ^ 2 ^ (j + 1) = 1
    have himg : T.image (fun x => x ^ 2) ⊆ Finset.univ.filter fun x : B => x ^ 2 ^ j = 1 := by
      intro y hy
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
      simp only [T, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
      rw [← pow_mul, ← pow_succ']
      exact hx
    have hfib : ∀ y ∈ T.image (fun x => x ^ 2), (T.filter fun x => x ^ 2 = y).card ≤ 2 := by
      intro y hy
      obtain ⟨x₀, -, rfl⟩ := Finset.mem_image.mp hy
      refine le_trans ?_ h1
      refine Finset.card_le_card_of_injOn (fun x => x * x₀⁻¹) ?_ ?_
      · intro x hx
        simp only [Finset.coe_filter, Set.mem_ofPred_eq, Finset.mem_univ, true_and] at hx ⊢
        rw [Commute.mul_pow (hcomm x x₀⁻¹), hx.2, inv_pow, mul_inv_cancel]
      · intro x _ y _ hxy
        simpa using hxy
    calc T.card ≤ 2 * (T.image fun x => x ^ 2).card := Finset.card_le_mul_card_image T 2 hfib
      _ ≤ 2 * 2 ^ j := Nat.mul_le_mul_left 2 ((Finset.card_le_card himg).trans ih)
      _ = 2 ^ (j + 1) := by rw [pow_succ, mul_comm]

theorem isCyclic_of_card_sq_eq_one_le {B : Type*} [Group B] [Finite B] (hB : IsPGroup 2 B)
    (hcomm : ∀ a b : B, a * b = b * a) (h1 : Nat.card {x : B // x ^ 2 = 1} ≤ 2) :
    IsCyclic B := by
  classical
  have : Fintype B := Fintype.ofFinite B
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype] at h1
  refine isCyclic_of_card_pow_eq_one_le fun n hn => ?_
  have hsub : (Finset.univ.filter fun x : B => x ^ n = 1) ⊆
      Finset.univ.filter fun x : B => x ^ 2 ^ n.factorization 2 = 1 := by
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    obtain ⟨k, hk⟩ := hB x
    have hord : orderOf x ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk
    obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hord
    have hn' : 2 ^ i ∣ n := hi ▸ orderOf_dvd_of_pow_eq_one hx
    have hle : i ≤ n.factorization 2 :=
      (Nat.prime_two.pow_dvd_iff_le_factorization hn.ne').mp hn'
    rw [← orderOf_dvd_iff_pow_eq_one, hi]
    exact Nat.pow_dvd_pow 2 hle
  calc (Finset.univ.filter fun x : B => x ^ n = 1).card
      ≤ (Finset.univ.filter fun x : B => x ^ 2 ^ n.factorization 2 = 1).card :=
        Finset.card_le_card hsub
    _ ≤ 2 ^ n.factorization 2 := card_filter_pow_two_pow_le hcomm h1 _
    _ ≤ n := Nat.le_of_dvd hn (Nat.ordProj_dvd n 2)

theorem exists_elemAbelian_of_not_isCyclic {W : Subgroup G} (hW : IsMulCommutative W)
    (hW2 : IsPGroup 2 W) (hcyc : ¬ IsCyclic W) :
    ∃ V : Subgroup G, V ≤ W ∧ CFSG.Assembly.IsElemAbelian 2 V ∧ 4 ≤ Nat.card V ∧
      Subgroup.normalizer (W : Set G) ≤ Subgroup.normalizer (V : Set G) := by
  have hcommW : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hW.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  let V : Subgroup G :=
    { carrier := {x | x ∈ W ∧ x ^ 2 = 1}
      one_mem' := ⟨W.one_mem, one_pow 2⟩
      mul_mem' := fun {x y} hx hy => ⟨W.mul_mem hx.1 hy.1, by
        rw [Commute.mul_pow (hcommW x hx.1 y hy.1), hx.2, hy.2, one_mul]⟩
      inv_mem' := fun {x} hx => ⟨W.inv_mem hx.1, by rw [inv_pow, hx.2, inv_one]⟩ }
  have hmem : ∀ x, x ∈ V ↔ x ∈ W ∧ x ^ 2 = 1 := fun x => Iff.rfl
  have hVW : V ≤ W := fun x hx => ((hmem x).mp hx).1
  refine ⟨V, hVW, ⟨⟨⟨fun x y => Subtype.ext (hcommW x (hVW x.2) y (hVW y.2))⟩⟩,
    fun x hx => ((hmem x).mp hx).2⟩, ?_, ?_⟩
  · have e : V ≃ {x : W // x ^ 2 = 1} :=
      { toFun := fun x => ⟨⟨x, hVW x.2⟩, Subtype.ext ((hmem x).mp x.2).2⟩
        invFun := fun x => ⟨x.1, (hmem _).mpr ⟨x.1.2, congrArg Subtype.val x.2⟩⟩
        left_inv := fun x => rfl
        right_inv := fun x => rfl }
    have h3 : 2 < Nat.card V := by
      rw [Nat.card_congr e]
      by_contra hle
      push Not at hle
      exact hcyc (isCyclic_of_card_sq_eq_one_le hW2 (fun a b => hW.is_comm.comm a b) hle)
    obtain ⟨k, hk⟩ := (hW2.to_le hVW).exists_card_eq
    rw [hk] at h3 ⊢
    have hk2 : 2 ≤ k := by
      by_contra hlt
      push Not at hlt
      interval_cases k <;> norm_num at h3
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk2
  · intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro x
    rw [hmem, hmem]
    constructor
    · rintro ⟨hxW, hx2⟩
      exact ⟨(Subgroup.mem_normalizer_iff.mp hg x).mp hxW, by
        rw [conj_pow, hx2, mul_one, mul_inv_cancel]⟩
    · rintro ⟨hxW, hx2⟩
      refine ⟨(Subgroup.mem_normalizer_iff.mp hg x).mpr hxW, ?_⟩
      rw [conj_pow] at hx2
      simpa using hx2

omit [Finite G] in
theorem normalizer_le_normalizer_omegaOneSub (N : Subgroup G) :
    Subgroup.normalizer (N : Set G) ≤ Subgroup.normalizer (omegaOneSub N : Set G) := by
  rw [omegaOneSub_eq_closure]
  have key : ∀ g ∈ Subgroup.normalizer (N : Set G),
      ∀ x ∈ Subgroup.closure {x : G | x ∈ N ∧ x ^ 2 = 1},
        g * x * g⁻¹ ∈ Subgroup.closure {x : G | x ∈ N ∧ x ^ 2 = 1} := by
    intro g hg x hx
    induction hx using Subgroup.closure_induction with
    | mem y hy =>
      exact Subgroup.subset_closure ⟨(Subgroup.mem_normalizer_iff.mp hg y).mp hy.1, by
        rw [conj_pow, hy.2, mul_one, mul_inv_cancel]⟩
    | one =>
      rw [mul_one, mul_inv_cancel]
      exact Subgroup.one_mem _
    | mul a b _ _ ha hb =>
      have := Subgroup.mul_mem _ ha hb
      rwa [show g * a * g⁻¹ * (g * b * g⁻¹) = g * (a * b) * g⁻¹ by group] at this
    | inv a _ ha =>
      have := Subgroup.inv_mem _ ha
      rwa [show (g * a * g⁻¹)⁻¹ = g * a⁻¹ * g⁻¹ by group] at this
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨key g hg x, fun hx => ?_⟩
  have := key g⁻¹ (Subgroup.inv_mem _ hg) _ hx
  rwa [show g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x by group] at this

variable {A S U : Subgroup G}

theorem inf_centralizer_fourGroup_eq_bot (h : SectionFiveHyp A S)
    (hU : IsNormalFourGroup A S U) : U ⊓ Subgroup.centralizer (A : Set G) = ⊥ := by
  rcases Subgroup.bot_or_exists_ne_one (U ⊓ Subgroup.centralizer (A : Set G)) with
    hb | ⟨v, hv, hv1⟩
  · exact hb
  exfalso
  have hUA : U ≤ Subgroup.centralizer (A : Set G) := by
    rw [Subgroup.le_centralizer_iff]
    intro a ha
    exact mem_centralizer_of_fourGroup hU.elemAbelian hU.card_eq (hU.le_normalizer_right ha)
      (h.elemAbelian.2 a ha) hv.1 hv1 (Subgroup.mem_centralizer_iff.mp hv.2 a ha)
  exact no_fourGroup_centralizer h (le_inf hU.le hUA) hU.elemAbelian hU.card_eq

theorem card_inf_centralizer_fourGroup (h : SectionFiveHyp A S)
    (hU : IsNormalFourGroup A S U) :
    Nat.card (A ⊓ Subgroup.centralizer (U : Set G) : Subgroup G) = 9 := by
  have hcop : Nat.Coprime 3 (Nat.card U) := by rw [hU.card_eq]; norm_num
  obtain ⟨H, hHA, hH9, v, hv, hv1⟩ : ∃ H : Subgroup G, H ≤ A ∧ Nat.card H = 3 ^ 2 ∧
      ∃ v ∈ U ⊓ Subgroup.centralizer (H : Set G), v ≠ 1 := by
    by_contra hno
    push Not at hno
    have hUbot : U ≤ ⊥ := le_of_forall_inf_centralizer_sub_le (k := 2) Nat.prime_three
      h.elemAbelian (by norm_num [h.card_eq]) hU.le_normalizer_right hcop
      fun H hHA hH v hv => Subgroup.mem_bot.mpr (hno H hHA hH v hv)
    have h4 := hU.card_eq
    rw [le_bot_iff.mp hUbot, Subgroup.card_bot] at h4
    norm_num at h4
  have hHU : H ≤ A ⊓ Subgroup.centralizer (U : Set G) := fun x hx =>
    Subgroup.mem_inf.mpr ⟨hHA hx, mem_centralizer_of_fourGroup hU.elemAbelian hU.card_eq
      (hU.le_normalizer_right (hHA hx)) (h.elemAbelian.2 x (hHA hx)) hv.1 hv1
      (Subgroup.mem_centralizer_iff.mp hv.2 x hx)⟩
  have h9 : 9 ∣ Nat.card (A ⊓ Subgroup.centralizer (U : Set G) : Subgroup G) := by
    have := Subgroup.card_dvd_of_le hHU
    rwa [hH9] at this
  have h27 : Nat.card (A ⊓ Subgroup.centralizer (U : Set G) : Subgroup G) ∣ 3 ^ 3 := by
    have := Subgroup.card_dvd_of_le (inf_le_left : A ⊓ Subgroup.centralizer (U : Set G) ≤ A)
    rwa [h.card_eq] at this
  have hne : Nat.card (A ⊓ Subgroup.centralizer (U : Set G) : Subgroup G) ≠ 27 := by
    intro h27'
    have hAeq : A ⊓ Subgroup.centralizer (U : Set G) = A :=
      Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h27', h.card_eq])
    have hUA : U ≤ Subgroup.centralizer (A : Set G) :=
      Subgroup.le_centralizer_iff.mpr (inf_eq_left.mp hAeq)
    have hbot := inf_centralizer_fourGroup_eq_bot h hU
    rw [inf_eq_left.mpr hUA] at hbot
    have h4 := hU.card_eq
    rw [hbot, Subgroup.card_bot] at h4
    norm_num at h4
  obtain ⟨i, hi, hcard⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp h27
  rw [hcard] at h9 hne ⊢
  interval_cases i
  · norm_num at h9
  · norm_num at h9
  · norm_num
  · norm_num at hne

theorem exists_conj_eq_of_fourGroup (h : SectionFiveHyp A S)
    (hU : IsNormalFourGroup A S U) {v w : G} (hv : v ∈ U) (hv1 : v ≠ 1) (hw : w ∈ U)
    (hw1 : w ≠ 1) : ∃ a ∈ A, a * v * a⁻¹ = w := by
  have hB := card_inf_centralizer_fourGroup h hU
  obtain ⟨a, ha, haU⟩ : ∃ a ∈ A, a ∉ Subgroup.centralizer (U : Set G) := by
    by_contra! hno
    rw [inf_eq_left.mpr (fun a ha => hno a ha), h.card_eq] at hB
    norm_num at hB
  have ha3 : a ^ 3 = 1 := h.elemAbelian.2 a ha
  have haN := hU.le_normalizer_right ha
  have hav : a * v ≠ v * a := fun hc =>
    haU (mem_centralizer_of_fourGroup hU.elemAbelian hU.card_eq haN ha3 hv hv1 hc)
  have hx₁U : a * v * a⁻¹ ∈ U := (Subgroup.mem_normalizer_iff.mp haN v).mp hv
  have hx₂U : a⁻¹ * v * a ∈ U := by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ haN) v).mp hv
    rwa [inv_inv] at this
  have hx₁1 : a * v * a⁻¹ ≠ 1 := fun h' => hv1 (by simpa using h')
  have hx₂1 : a⁻¹ * v * a ≠ 1 := fun h' => hv1 (by
    have e : v = a * (a⁻¹ * v * a) * a⁻¹ := by group
    rw [e, h']
    group)
  have hx₁v : a * v * a⁻¹ ≠ v := fun h' => hav (by
    calc a * v = a * v * a⁻¹ * a := by group
      _ = v * a := by rw [h'])
  have hx₂v : a⁻¹ * v * a ≠ v := fun h' => hav (by
    calc a * v = a * (a⁻¹ * v * a) := by rw [h']
      _ = v * a := by group)
  have hx₁₂ : a⁻¹ * v * a ≠ a * v * a⁻¹ := by
    intro h'
    apply hx₂v
    have ha2 : a * a = a⁻¹ := by
      rw [eq_inv_iff_mul_eq_one, ← pow_three']
      exact ha3
    have e1 : v = a * a * v * (a * a)⁻¹ := by
      calc v = a * (a⁻¹ * v * a) * a⁻¹ := by group
        _ = a * (a * v * a⁻¹) * a⁻¹ := by rw [h']
        _ = a * a * v * (a * a)⁻¹ := by group
    rw [ha2, inv_inv] at e1
    exact e1.symm
  by_cases hwv : w = v
  · exact ⟨1, Subgroup.one_mem _, by rw [hwv]; group⟩
  by_cases hwx₁ : w = a * v * a⁻¹
  · exact ⟨a, ha, hwx₁.symm⟩
  refine ⟨a⁻¹, Subgroup.inv_mem _ ha, ?_⟩
  have e1 := eq_mul_of_fourGroup hU.elemAbelian hU.card_eq hv hx₁U hw hv1 hx₁1 (Ne.symm hx₁v)
    hw1 hwv hwx₁
  have e2 := eq_mul_of_fourGroup hU.elemAbelian hU.card_eq hv hx₁U hx₂U hv1 hx₁1
    (Ne.symm hx₁v) hx₂1 hx₂v hx₁₂
  rw [inv_inv, e1, ← e2]

theorem le_centralizer_fourGroup (h : SectionFiveHyp A S)
    (hU : IsNormalFourGroup A S U) : U ≤ Subgroup.centralizer (S : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Group.IsNilpotent S := h.isPGroup.isNilpotent
  have : (U.subgroupOf S).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hU.le).mpr hU.le_normalizer_left
  have hne : U.subgroupOf S ≠ ⊥ := by
    intro hb
    rw [Subgroup.subgroupOf_eq_bot] at hb
    have h4 := hU.card_eq
    rw [le_bot_iff.mp (hb le_rfl hU.le), Subgroup.card_bot] at h4
    norm_num at h4
  obtain ⟨x, hx, hx1⟩ := (Subgroup.bot_or_exists_ne_one _).resolve_left
    (Group.IsNilpotent.inf_center_ne_bot_of_normal hne)
  have hyU : (x : G) ∈ U := Subgroup.mem_subgroupOf.mp (Subgroup.mem_inf.mp hx).1
  have hyS : (x : G) ∈ Subgroup.centralizer (S : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp (Subgroup.mem_inf.mp hx).2 ⟨s, hs⟩)
  have hy1 : (x : G) ≠ 1 := fun h' => hx1 (Subtype.ext h')
  have hyK : (x : G) ∈ U ⊓ Subgroup.centralizer (S : Set G) := Subgroup.mem_inf.mpr ⟨hyU, hyS⟩
  have hAK : A ≤ Subgroup.normalizer
      ((U ⊓ Subgroup.centralizer (S : Set G) : Subgroup G) : Set G) := fun a ha =>
    Subgroup.inf_normalizer_le_normalizer_inf
      ⟨hU.le_normalizer_right ha, normalizer_le_normalizer_centralizer S (h.le_normalizer ha)⟩
  have hKdvd : Nat.card (U ⊓ Subgroup.centralizer (S : Set G) : Subgroup G) ∣ 2 ^ 2 := by
    have := Subgroup.card_dvd_of_le (inf_le_left : U ⊓ Subgroup.centralizer (S : Set G) ≤ U)
    rwa [hU.card_eq] at this
  obtain ⟨i, hi, hKi⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hKdvd
  interval_cases i
  · rw [pow_zero, Subgroup.card_eq_one] at hKi
    rw [hKi] at hyK
    exact absurd (Subgroup.mem_bot.mp hyK) hy1
  · have hKA := le_centralizer_of_card_eq_two (by rw [hKi]; norm_num) hAK
    have hmem : (x : G) ∈ U ⊓ Subgroup.centralizer (A : Set G) :=
      Subgroup.mem_inf.mpr ⟨hyU, hKA hyK⟩
    rw [inf_centralizer_fourGroup_eq_bot h hU] at hmem
    exact absurd (Subgroup.mem_bot.mp hmem) hy1
  · exact inf_eq_left.mp (Subgroup.eq_of_le_of_card_ge inf_le_left
      (by rw [hKi, hU.card_eq]; norm_num))

theorem rank3II_5_6_of_ih (h : SectionFiveHyp A S)
    (ih : ∀ S' : Subgroup G, S' < S → SectionFiveHyp A S' → Statement51 A S') :
    (∀ W : Subgroup G, W ≤ S → A ≤ Subgroup.normalizer (W : Set G) → IsMulCommutative W →
      IsCyclic W) ∨ ∃ U : Subgroup G, IsNormalFourGroup A S U := by
  by_cases h2 : ∀ W : Subgroup G, W ≤ S → A ≤ Subgroup.normalizer (W : Set G) →
      IsMulCommutative W → IsCyclic W
  · exact Or.inl h2
  right
  push Not at h2
  obtain ⟨W, hWS, hAW, hWc, hWcyc⟩ := h2
  have hS2 := h.isPGroup
  obtain ⟨V, hVW, hVel, hV4, hVnorm⟩ :=
    exists_elemAbelian_of_not_isCyclic hWc (hS2.to_le hWS) hWcyc
  have hAV : A ≤ Subgroup.normalizer (V : Set G) := hAW.trans hVnorm
  have hVS : V ≤ S := hVW.trans hWS
  have hVA : ¬ V ≤ Subgroup.centralizer (A : Set G) := by
    intro hVA
    obtain ⟨k, hk⟩ := (hS2.to_le hVS).exists_card_eq
    have hk2 : 2 ≤ k := by
      by_contra hlt
      push Not at hlt
      rw [hk] at hV4
      interval_cases k <;> norm_num at hV4
    have h1 := le_pRank_of_elemAbelian Nat.prime_two (le_inf hVS hVA) hVel hk
    have h2 := rank3II_5_4 h
    omega
  obtain ⟨U, ⟨hUV, hAU, hUA⟩, hmin⟩ := Source.exists_minimal_subgroup
    (fun U : Subgroup G => U ≤ V ∧ A ≤ Subgroup.normalizer (U : Set G) ∧
      ¬ U ≤ Subgroup.centralizer (A : Set G)) ⟨le_rfl, hAV, hVA⟩
  have hUS : U ≤ S := hUV.trans hVS
  have hUel : CFSG.Assembly.IsElemAbelian 2 U := isElemAbelian_of_le hVel hUV
  have hAcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (h.elemAbelian.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hcopU : Nat.Coprime 3 (Nat.card U) := by
    obtain ⟨k, hk⟩ := (hS2.to_le hUS).exists_card_eq
    rw [hk]
    exact Nat.Coprime.pow_right k (by norm_num)
  obtain ⟨H, hHA, hH9, hUH⟩ : ∃ H : Subgroup G, H ≤ A ∧ Nat.card H = 3 ^ 2 ∧
      U ≤ Subgroup.centralizer (H : Set G) := by
    by_contra hno
    push Not at hno
    apply hUA
    refine le_of_forall_inf_centralizer_sub_le (k := 2) Nat.prime_three h.elemAbelian
      (by norm_num [h.card_eq]) hAU hcopU fun H hHA hH => ?_
    by_contra hK
    have hAK : A ≤ Subgroup.normalizer
        ((U ⊓ Subgroup.centralizer (H : Set G) : Subgroup G) : Set G) := fun a ha =>
      Subgroup.inf_normalizer_le_normalizer_inf ⟨hAU ha, Subgroup.le_normalizer
        (Subgroup.mem_centralizer_iff.mpr fun x hx => hAcomm x (hHA hx) a ha)⟩
    have heq := hmin _ inf_le_left ⟨inf_le_left.trans hUV, hAK, hK⟩
    exact hno H hHA hH (inf_eq_left.mp heq)
  obtain ⟨m, hm⟩ := (hS2.to_le hUS).exists_card_eq
  have hm2 : m ≤ 2 := by
    have h55 := rank3II_5_5 h hHA (by rw [hH9]; norm_num)
    have := le_pRank_of_elemAbelian Nat.prime_two (le_inf hUS hUH) hUel hm
    omega
  have hU4 : Nat.card U = 4 := by
    interval_cases m
    · rw [pow_zero, Subgroup.card_eq_one] at hm
      exact absurd (by rw [hm]; exact bot_le) hUA
    · exact absurd (le_centralizer_of_card_eq_two (by rw [hm]; norm_num) hAU) hUA
    · rw [hm]; norm_num
  have hSU : S ≤ Subgroup.normalizer (U : Set G) := by
    by_contra hSU
    have hNS : S ⊓ Subgroup.normalizer (U : Set G) < S :=
      lt_of_le_of_ne inf_le_left fun heq => hSU (inf_eq_left.mp heq)
    have hUN : U ≤ S ⊓ Subgroup.normalizer (U : Set G) := le_inf hUS Subgroup.le_normalizer
    have hAN : A ≤ Subgroup.normalizer
        ((S ⊓ Subgroup.normalizer (U : Set G) : Subgroup G) : Set G) := fun a ha =>
      Subgroup.inf_normalizer_le_normalizer_inf
        ⟨h.le_normalizer ha, Subgroup.le_normalizer (hAU ha)⟩
    have hc : ⁅CFSG.pCore 3 G, S ⊓ Subgroup.normalizer (U : Set G)⁆ ≠ ⊥ := by
      intro hc
      have hle : S ⊓ Subgroup.normalizer (U : Set G) ≤
          S ⊓ Subgroup.centralizer (CFSG.pCore 3 G : Set G) := by
        refine le_inf inf_le_left ?_
        rw [← Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.commutator_comm]
        exact hc
      rw [rank3II_5_3 h] at hle
      have h4 := hU4
      rw [le_bot_iff.mp (hUN.trans hle), Subgroup.card_bot] at h4
      norm_num at h4
    have h51 := ih _ hNS (h.mono inf_le_left hAN hc)
    unfold Statement51 at h51
    rcases h51 with ⟨-, -, -, hΩ4⟩ | hcyc
    · have hUΩ : U ≤ omegaOneSub (S ⊓ Subgroup.normalizer (U : Set G)) := by
        rw [omegaOneSub_eq_closure]
        intro x hx
        exact Subgroup.subset_closure ⟨hUN hx, hUel.2 x hx⟩
      have hΩU := (Subgroup.eq_of_le_of_card_ge hUΩ (by rw [hΩ4, hU4])).symm
      obtain ⟨g, hg, hgN⟩ := IsConcreteLE.exists_of_lt (lt_inf_normalizer_of_lt hS2 hNS)
      apply hgN
      refine Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp hg).1, ?_⟩
      rw [← hΩU]
      exact normalizer_le_normalizer_omegaOneSub _ (Subgroup.mem_inf.mp hg).2
    · have := isKleinFour_of_isElemAbelian hUel hU4
      exact IsKleinFour.not_isCyclic (hcyc U hUN hAU hUel.1)
  exact ⟨U, ⟨hUS, hUel, hU4, hSU, hAU⟩⟩

end CFSG.RankThree.PartTwo.Sec5
