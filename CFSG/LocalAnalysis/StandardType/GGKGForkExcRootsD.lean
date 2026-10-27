module

public import CFSG.HardMathSupport.Timmesfeld.Torality.FamilyBruhat
public import CFSG.LieType.Chevalley.KernelComponentRoots
public import CFSG.LocalAnalysis.StandardType.GGKGForkExcRootsA

public section

namespace CFSG.StandardType

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.HardMathSupport.Timmesfeld.Torality
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

private def ggKGEd_zetaUnit {k : Type} [Field k] {p : ℕ} (ζ : k)
    (hζ : IsPrimitiveRoot ζ p) (hp : p.Prime) : kˣ :=
  Units.mk0 ζ (hζ.ne_zero hp.ne_zero)

private lemma ggKGEd_zetaUnit_zpow_eq_one_iff {k : Type} [Field k] {p : ℕ} {ζ : k}
    (hζ : IsPrimitiveRoot ζ p) (hp : p.Prime) (n : ℤ) :
    (ggKGEd_zetaUnit ζ hζ hp) ^ n = 1 ↔ (p : ℤ) ∣ n := by
  rw [← Units.val_eq_one, Units.val_zpow_eq_zpow_val]
  change (ζ ^ n : k) = 1 ↔ (p : ℤ) ∣ n
  exact hζ.zpow_eq_one_iff_dvd n

private lemma ggKGEd_prod_zpow_sum {G : Type*} [CommGroup G] {ι : Type*} (s : Finset ι)
    (x : G) (g : ι → ℤ) : (∏ i ∈ s, x ^ g i) = x ^ (∑ i ∈ s, g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, ih, zpow_add]

private lemma ggKGEd_rootChar_zetaUnit {τ : Tag} {k : Type} [Field k]
    (ζu : kˣ) (e v : Fin τ.rank → ℤ) :
    rootChar (fun i => ζu ^ e i) v = ζu ^ (∑ i, e i * v i) := by
  rw [rootChar]
  simp_rw [← zpow_mul]
  exact ggKGEd_prod_zpow_sum Finset.univ ζu (fun i => e i * v i)

private lemma ggKGEd_zetaVec_rootChar_eq_one_iff {τ : Tag} {k : Type} [Field k] {p : ℕ}
    {ζ : k} (hζ : IsPrimitiveRoot ζ p) (hp : p.Prime) (e v : Fin τ.rank → ℤ) :
    rootChar (fun i => ggKGEd_zetaUnit ζ hζ hp ^ e i) v = 1 ↔
      (p : ℤ) ∣ ∑ i, e i * v i := by
  rw [ggKGEd_rootChar_zetaUnit, ggKGEd_zetaUnit_zpow_eq_one_iff]

private lemma ggKGEd_zetaVec_pow_eq_one {τ : Tag} {k : Type} [Field k] {p : ℕ} {ζ : k}
    (hζ : IsPrimitiveRoot ζ p) (hp : p.Prime) (e : Fin τ.rank → ℤ) (i : Fin τ.rank) :
    (ggKGEd_zetaUnit ζ hζ hp ^ e i) ^ p = 1 := by
  rw [← zpow_natCast, ← zpow_mul, ggKGEd_zetaUnit_zpow_eq_one_iff]
  exact ⟨e i, by ring⟩

private lemma ggKGEd_sum_single_mul {τ : Tag} (j : Fin τ.rank) (v : Fin τ.rank → ℤ) :
    (∑ k, (Pi.single j 1 : Fin τ.rank → ℤ) k * v k) = v j := by
  rw [Finset.sum_eq_single j]
  · simp
  · intro k _ hk
    simp [Pi.single_apply, hk]
  · intro hj
    exact absurd (Finset.mem_univ j) hj

private lemma ggKGEd_sum_add_single_mul {τ : Tag} (i i' : Fin τ.rank) (v : Fin τ.rank → ℤ) :
    (∑ k, (((Pi.single i 1 : Fin τ.rank → ℤ) + (Pi.single i' 1 : Fin τ.rank → ℤ))) k * v k) =
      v i + v i' := by
  simp only [Pi.add_apply, add_mul]
  rw [Finset.sum_add_distrib, ggKGEd_sum_single_mul, ggKGEd_sum_single_mul]

private lemma ggKGEd_dvd_of_kernel {k : Type} [Field k] {p : ℕ} (hp : p.Prime)
    {ζ : k} (hζ : IsPrimitiveRoot ζ p) {ι : Type}
    (a : ι → Fin (Tag.rank .E6) → kˣ)
    (hall : ∀ b : Fin (Tag.rank .E6) → kˣ, (∀ j, b j ^ p = 1) →
      b ⟨0, by decide⟩ = b ⟨5, by decide⟩ → b ⟨2, by decide⟩ = b ⟨4, by decide⟩ → ∃ i, a i = b)
    {β : Fin (Tag.rank .E6) → ℤ} (hβ : ∀ i, rootChar (a i) β = 1)
    (e : Fin (Tag.rank .E6) → ℤ)
    (hfix0 : e ⟨0, by decide⟩ = e ⟨5, by decide⟩)
    (hfix2 : e ⟨2, by decide⟩ = e ⟨4, by decide⟩) :
    (p : ℤ) ∣ ∑ j, e j * β j := by
  let ζu := ggKGEd_zetaUnit ζ hζ hp
  let b : Fin (Tag.rank .E6) → kˣ := fun j => ζu ^ e j
  have hbpow : ∀ j, b j ^ p = 1 := fun j => ggKGEd_zetaVec_pow_eq_one hζ hp e j
  have hb05 : b ⟨0, by decide⟩ = b ⟨5, by decide⟩ := by
    dsimp only [b]
    rw [hfix0]
  have hb24 : b ⟨2, by decide⟩ = b ⟨4, by decide⟩ := by
    dsimp only [b]
    rw [hfix2]
  obtain ⟨i, hi⟩ := hall b hbpow hb05 hb24
  have h1 : rootChar b β = 1 := by
    have := hβ i
    rwa [hi] at this
  exact (ggKGEd_zetaVec_rootChar_eq_one_iff hζ hp e β).1 h1

private lemma ggKGEd_dvd_of_stab {k : Type} [Field k] {p : ℕ} (hp : p.Prime)
    {ζ : k} (hζ : IsPrimitiveRoot ζ p) {ι : Type}
    (a : ι → Fin (Tag.rank .E6) → kˣ)
    (hall : ∀ b : Fin (Tag.rank .E6) → kˣ, (∀ j, b j ^ p = 1) →
      b ⟨0, by decide⟩ = b ⟨5, by decide⟩ → b ⟨2, by decide⟩ = b ⟨4, by decide⟩ → ∃ i, a i = b)
    {w : WeylGroup .E6} (hw : w ∈ familyStabilizer a)
    (v : Fin (Tag.rank .E6) → ℤ) (e : Fin (Tag.rank .E6) → ℤ)
    (hfix0 : e ⟨0, by decide⟩ = e ⟨5, by decide⟩)
    (hfix2 : e ⟨2, by decide⟩ = e ⟨4, by decide⟩) :
    (p : ℤ) ∣ ∑ j, e j * ((w • v) j - v j) := by
  let ζu := ggKGEd_zetaUnit ζ hζ hp
  let b : Fin (Tag.rank .E6) → kˣ := fun j => ζu ^ e j
  have hbpow : ∀ j, b j ^ p = 1 := fun j => ggKGEd_zetaVec_pow_eq_one hζ hp e j
  have hb05 : b ⟨0, by decide⟩ = b ⟨5, by decide⟩ := by
    dsimp only [b]
    rw [hfix0]
  have hb24 : b ⟨2, by decide⟩ = b ⟨4, by decide⟩ := by
    dsimp only [b]
    rw [hfix2]
  obtain ⟨i, hi⟩ := hall b hbpow hb05 hb24
  have heq : rootChar b (w • v) = rootChar b v := by
    have := hw i v
    rwa [hi] at this
  have hL : rootChar b (w • v) = ζu ^ (∑ j, e j * (w • v) j) :=
    ggKGEd_rootChar_zetaUnit ζu e (w • v)
  have hR : rootChar b v = ζu ^ (∑ j, e j * v j) := ggKGEd_rootChar_zetaUnit ζu e v
  rw [hL, hR] at heq
  have hz : ζu ^ ((∑ j, e j * (w • v) j) - (∑ j, e j * v j)) = 1 := by
    rw [zpow_sub, heq]
    group
  have hdvd := (ggKGEd_zetaUnit_zpow_eq_one_iff hζ hp _).1 hz
  have heqsum : (∑ j, e j * ((w • v) j - v j)) =
      (∑ j, e j * (w • v) j) - (∑ j, e j * v j) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [heqsum]
  exact hdvd

private lemma ggKGEd_e6_check : e6Certificate.check = true := by decide

private lemma ggKGEd_e6_checkSigns : e6Certificate.checkSigns = true := by decide

private lemma ggKGEd_e6_root_nonneg_or_nonpos {β : Fin (Tag.rank .E6) → ℤ}
    (hβ : IsRoot .E6 β) : (∀ j, 0 ≤ β j) ∨ ∀ j, β j ≤ 0 := by
  obtain ⟨k, hk, rfl⟩ := RootCertificate.exists_root_eq ggKGEd_e6_check hβ
  have h := ggKGEd_e6_checkSigns
  simp only [RootCertificate.checkSigns, List.all_eq_true, List.mem_range, Bool.and_eq_true,
    Bool.or_eq_true, List.mem_finRange, true_implies, decide_eq_true_eq] at h
  exact (h k hk).1

private lemma ggKGEd_e6_root_ne_zero {β : Fin (Tag.rank .E6) → ℤ} (hβ : IsRoot .E6 β) :
    β ≠ 0 := by
  obtain ⟨k, hk, rfl⟩ := RootCertificate.exists_root_eq ggKGEd_e6_check hβ
  have h := ggKGEd_e6_checkSigns
  simp only [RootCertificate.checkSigns, List.all_eq_true, List.mem_range, Bool.and_eq_true,
    List.any_eq_true, List.mem_finRange, true_and, decide_eq_true_eq] at h
  obtain ⟨j, hj⟩ := (h k hk).2
  exact fun h0 => hj (congrFun h0 j)

private def ggKGEd_pi (v : Fin (Tag.rank .E6) → ℤ) : Fin 4 → ℤ :=
  ![v ⟨0, by decide⟩ + v ⟨5, by decide⟩, v ⟨1, by decide⟩,
    v ⟨2, by decide⟩ + v ⟨4, by decide⟩, v ⟨3, by decide⟩]

private lemma ggKGEd_pi_apply_zero (v : Fin (Tag.rank .E6) → ℤ) :
    ggKGEd_pi v ⟨0, by decide⟩ = v ⟨0, by decide⟩ + v ⟨5, by decide⟩ := rfl

private lemma ggKGEd_pi_apply_one (v : Fin (Tag.rank .E6) → ℤ) :
    ggKGEd_pi v ⟨1, by decide⟩ = v ⟨1, by decide⟩ := rfl

private lemma ggKGEd_pi_apply_two (v : Fin (Tag.rank .E6) → ℤ) :
    ggKGEd_pi v ⟨2, by decide⟩ = v ⟨2, by decide⟩ + v ⟨4, by decide⟩ := rfl

private lemma ggKGEd_pi_apply_three (v : Fin (Tag.rank .E6) → ℤ) :
    ggKGEd_pi v ⟨3, by decide⟩ = v ⟨3, by decide⟩ := rfl

private lemma ggKGEd_e6_pi_abs_le (k : ℕ) (hk : k < e6Certificate.roots.length) :
    |ggKGEd_pi (e6Certificate.root k) ⟨0, by decide⟩| ≤ 4 ∧
    |ggKGEd_pi (e6Certificate.root k) ⟨1, by decide⟩| ≤ 4 ∧
    |ggKGEd_pi (e6Certificate.root k) ⟨2, by decide⟩| ≤ 4 ∧
    |ggKGEd_pi (e6Certificate.root k) ⟨3, by decide⟩| ≤ 4 := by
  have h : ((List.range e6Certificate.roots.length).all fun k =>
      decide (|ggKGEd_pi (e6Certificate.root k) ⟨0, by decide⟩| ≤ 4) &&
      (decide (|ggKGEd_pi (e6Certificate.root k) ⟨1, by decide⟩| ≤ 4) &&
      (decide (|ggKGEd_pi (e6Certificate.root k) ⟨2, by decide⟩| ≤ 4) &&
      decide (|ggKGEd_pi (e6Certificate.root k) ⟨3, by decide⟩| ≤ 4)))) = true := by decide
  have h' : ∀ k' ∈ List.range e6Certificate.roots.length,
      (decide (|ggKGEd_pi (e6Certificate.root k') ⟨0, by decide⟩| ≤ 4) &&
      (decide (|ggKGEd_pi (e6Certificate.root k') ⟨1, by decide⟩| ≤ 4) &&
      (decide (|ggKGEd_pi (e6Certificate.root k') ⟨2, by decide⟩| ≤ 4) &&
      decide (|ggKGEd_pi (e6Certificate.root k') ⟨3, by decide⟩| ≤ 4)))) = true :=
    List.all_eq_true.1 h
  have hk' := h' k (List.mem_range.2 hk)
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hk'
  exact ⟨hk'.1, hk'.2.1, hk'.2.2.1, hk'.2.2.2⟩

private lemma ggKGEd_e6_pi_abs_le_root {β : Fin (Tag.rank .E6) → ℤ} (hβ : IsRoot .E6 β) :
    |ggKGEd_pi β ⟨0, by decide⟩| ≤ 4 ∧
    |ggKGEd_pi β ⟨1, by decide⟩| ≤ 4 ∧
    |ggKGEd_pi β ⟨2, by decide⟩| ≤ 4 ∧
    |ggKGEd_pi β ⟨3, by decide⟩| ≤ 4 := by
  obtain ⟨k, hk, rfl⟩ := RootCertificate.exists_root_eq ggKGEd_e6_check hβ
  exact ggKGEd_e6_pi_abs_le k hk

private lemma ggKGEd_e6_pi_sub_abs_le (k : ℕ) (hk : k < e6Certificate.roots.length)
    (i : Fin (Tag.rank .E6)) (t : Fin 4) :
    |ggKGEd_pi (e6Certificate.root k - Pi.single i 1) t| ≤ 5 := by
  have h : ((List.range e6Certificate.roots.length).all fun k =>
      (List.finRange (Tag.rank .E6)).all fun i =>
      (List.finRange 4).all fun t =>
        decide (|ggKGEd_pi (e6Certificate.root k - Pi.single i 1) t| ≤ 5)) = true := by
    decide
  have h0 : ∀ k' ∈ List.range e6Certificate.roots.length,
      ((List.finRange (Tag.rank .E6)).all fun i =>
        (List.finRange 4).all fun t =>
          decide (|ggKGEd_pi (e6Certificate.root k' - Pi.single i 1) t| ≤ 5)) = true :=
    List.all_eq_true.1 h
  have h1 := h0 k (List.mem_range.2 hk)
  have h2 : ∀ i' ∈ List.finRange (Tag.rank .E6),
      ((List.finRange 4).all fun t =>
        decide (|ggKGEd_pi (e6Certificate.root k - Pi.single i' 1) t| ≤ 5)) = true :=
    List.all_eq_true.1 h1
  have h3 := h2 i (by simp)
  have h4 : ∀ t' ∈ List.finRange 4,
      decide (|ggKGEd_pi (e6Certificate.root k - Pi.single i 1) t'| ≤ 5) = true :=
    List.all_eq_true.1 h3
  exact of_decide_eq_true (h4 t (by simp))

private lemma ggKGEd_e6_pi_sub_abs_le_root {β : Fin (Tag.rank .E6) → ℤ} (hβ : IsRoot .E6 β)
    (i : Fin (Tag.rank .E6)) (t : Fin 4) :
    |ggKGEd_pi (β - Pi.single i 1) t| ≤ 5 := by
  obtain ⟨k, hk, rfl⟩ := RootCertificate.exists_root_eq ggKGEd_e6_check hβ
  exact ggKGEd_e6_pi_sub_abs_le k hk i t

private lemma ggKGEd_e6_mod5_pos (k : ℕ) (hk : k < e6Certificate.roots.length)
    (i : Fin (Tag.rank .E6))
    (hd : ∀ t : Fin 4, (5 : ℤ) ∣ ggKGEd_pi (e6Certificate.root k - Pi.single i 1) t) :
    ∀ j : Fin (Tag.rank .E6), 0 ≤ e6Certificate.root k j := by
  have h : ((List.range e6Certificate.roots.length).all fun k =>
      (List.finRange (Tag.rank .E6)).all fun i =>
        (!((List.finRange 4).all fun t =>
            decide ((5 : ℤ) ∣ ggKGEd_pi (e6Certificate.root k - Pi.single i 1) t))) ||
          ((List.finRange (Tag.rank .E6)).all fun j =>
            decide (0 ≤ e6Certificate.root k j))) = true := by
    decide
  have h0 : ∀ k' ∈ List.range e6Certificate.roots.length,
      ((List.finRange (Tag.rank .E6)).all fun i =>
        (!((List.finRange 4).all fun t =>
            decide ((5 : ℤ) ∣ ggKGEd_pi (e6Certificate.root k' - Pi.single i 1) t))) ||
          ((List.finRange (Tag.rank .E6)).all fun j =>
            decide (0 ≤ e6Certificate.root k' j))) = true :=
    List.all_eq_true.1 h
  have h1 := h0 k (List.mem_range.2 hk)
  have h2 : ∀ i' ∈ List.finRange (Tag.rank .E6),
      ((!(List.finRange 4).all fun t =>
          decide ((5 : ℤ) ∣ ggKGEd_pi (e6Certificate.root k - Pi.single i' 1) t)) ||
        ((List.finRange (Tag.rank .E6)).all fun j =>
          decide (0 ≤ e6Certificate.root k j))) = true :=
    List.all_eq_true.1 h1
  have h3 := h2 i (by simp)
  rw [Bool.or_eq_true] at h3
  rcases h3 with hneg | hpos
  · exfalso
    have hfalse : ((List.finRange 4).all fun t =>
        decide ((5 : ℤ) ∣ ggKGEd_pi (e6Certificate.root k - Pi.single i 1) t)) = false := by
      simpa using hneg
    have htrue : ((List.finRange 4).all fun t =>
        decide ((5 : ℤ) ∣ ggKGEd_pi (e6Certificate.root k - Pi.single i 1) t)) = true := by
      rw [List.all_eq_true]
      intro t _
      exact decide_eq_true (hd t)
    rw [htrue] at hfalse
    exact Bool.noConfusion hfalse
  · have hpos' : ∀ j' ∈ List.finRange (Tag.rank .E6),
        decide (0 ≤ e6Certificate.root k j') = true := List.all_eq_true.1 hpos
    intro j
    exact of_decide_eq_true (hpos' j (by simp))

private lemma ggKGEd_e6_mod5_pos_root {β : Fin (Tag.rank .E6) → ℤ} (hβ : IsRoot .E6 β)
    (i : Fin (Tag.rank .E6))
    (hd : ∀ t : Fin 4, (5 : ℤ) ∣ ggKGEd_pi (β - Pi.single i 1) t) :
    ∀ j, 0 ≤ β j := by
  obtain ⟨k, hk, rfl⟩ := RootCertificate.exists_root_eq ggKGEd_e6_check hβ
  exact ggKGEd_e6_mod5_pos k hk i hd

private lemma ggKGEd_eq_zero_of_dvd_of_abs_lt {p : ℕ} {x : ℤ}
    (hdvd : (p : ℤ) ∣ x) (hx : |x| < (p : ℤ)) : x = 0 := by
  have hdvd' : (p : ℤ) ∣ |x| := by
    rcases abs_choice x with h | h
    · rw [h]; exact hdvd
    · rw [h]; exact dvd_neg.mpr hdvd
  have hge : (0 : ℤ) ≤ |x| := abs_nonneg x
  have hzero : |x| = 0 := Int.eq_zero_of_dvd_of_nonneg_of_lt hge hx hdvd'
  exact abs_eq_zero.1 hzero

private lemma ggKGEd_eq_zero_of_dvd_of_abs_le {p : ℕ} (hp5 : 5 ≤ p) {x : ℤ}
    (hdvd : (p : ℤ) ∣ x) (hx : |x| ≤ 4) : x = 0 := by
  apply ggKGEd_eq_zero_of_dvd_of_abs_lt hdvd
  have hpz : (5 : ℤ) ≤ (p : ℤ) := by exact_mod_cast hp5
  linarith

private lemma ggKGEd_five_dvd_of_dvd_of_abs_le {p : ℕ} (hp5 : 5 ≤ p) {x : ℤ}
    (hdvd : (p : ℤ) ∣ x) (hx : |x| ≤ 5) : (5 : ℤ) ∣ x := by
  by_cases hp : p = 5
  · subst hp; exact hdvd
  · have hpz : (5 : ℤ) < (p : ℤ) := by
      have h : (5 : ℤ) ≤ (p : ℤ) := by exact_mod_cast hp5
      omega
    rw [ggKGEd_eq_zero_of_dvd_of_abs_lt hdvd (lt_of_le_of_lt hx hpz)]
    exact dvd_zero 5

private lemma ggKGEd_nonneg_of_height_pos {β : Fin (Tag.rank .E6) → ℤ} (hβ : IsRoot .E6 β)
    (h : 0 < height β) : ∀ j, 0 ≤ β j := by
  rcases ggKGEd_e6_root_nonneg_or_nonpos hβ with hpos | hneg
  · exact hpos
  · exfalso
    have : height β ≤ 0 := Finset.sum_nonpos fun j _ => hneg j
    linarith

private lemma ggKGEd_eq_one_of_forall_nonneg {w : WeylGroup .E6}
    (h : ∀ i, 0 ≤ w • (Pi.single i 1 : Fin (Tag.rank .E6) → ℤ)) : w = 1 := by
  by_contra hw
  obtain ⟨i, hi⟩ := (coxeterSystem .E6).exists_rightDescent_of_ne_one hw
  exact CFSG.LieType.RootSystem.weylAction_single_ne_zero _ w i
    (le_antisymm ((CFSG.LieType.RootSystem.isRightDescent_iff _ w i).1 hi) (h i))

private lemma ggKGEd_eq_one_of_forall_height_pos {w : WeylGroup .E6}
    (h : ∀ i, 0 < height (w • (Pi.single i 1 : Fin (Tag.rank .E6) → ℤ))) : w = 1 :=
  ggKGEd_eq_one_of_forall_nonneg fun i =>
    ggKGEd_nonneg_of_height_pos (IsRoot.smul (IsRoot.basis i) w) (h i)

theorem ggKGExc_familyKernel_phi {k : Type} [Field k] {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    {ζ : k} (hζ : IsPrimitiveRoot ζ p) {ι : Type} (a : ι → Fin (Tag.rank .E6) → kˣ)
    (hall : ∀ b : Fin (Tag.rank .E6) → kˣ, (∀ j, b j ^ p = 1) →
      b ⟨0, by decide⟩ = b ⟨5, by decide⟩ → b ⟨2, by decide⟩ = b ⟨4, by decide⟩ → ∃ i, a i = b) :
    familyKernel a = ∅ := by
  ext β
  simp only [Set.mem_empty_iff_false, iff_false]
  rintro ⟨hβroot, hβker⟩
  have hd0 : (p : ℤ) ∣ β ⟨0, by decide⟩ + β ⟨5, by decide⟩ := by
    have := ggKGEd_dvd_of_kernel hp hζ a hall hβker
      ((Pi.single (⟨0, by decide⟩ : Fin (Tag.rank .E6)) 1 : Fin (Tag.rank .E6) → ℤ) +
        (Pi.single (⟨5, by decide⟩ : Fin (Tag.rank .E6)) 1 : Fin (Tag.rank .E6) → ℤ))
      (by decide) (by decide)
    rwa [ggKGEd_sum_add_single_mul] at this
  have hd1 : (p : ℤ) ∣ β ⟨1, by decide⟩ := by
    have := ggKGEd_dvd_of_kernel hp hζ a hall hβker
      (Pi.single (⟨1, by decide⟩ : Fin (Tag.rank .E6)) 1) (by decide) (by decide)
    rwa [ggKGEd_sum_single_mul] at this
  have hd2 : (p : ℤ) ∣ β ⟨2, by decide⟩ + β ⟨4, by decide⟩ := by
    have := ggKGEd_dvd_of_kernel hp hζ a hall hβker
      ((Pi.single (⟨2, by decide⟩ : Fin (Tag.rank .E6)) 1 : Fin (Tag.rank .E6) → ℤ) +
        (Pi.single (⟨4, by decide⟩ : Fin (Tag.rank .E6)) 1 : Fin (Tag.rank .E6) → ℤ))
      (by decide) (by decide)
    rwa [ggKGEd_sum_add_single_mul] at this
  have hd3 : (p : ℤ) ∣ β ⟨3, by decide⟩ := by
    have := ggKGEd_dvd_of_kernel hp hζ a hall hβker
      (Pi.single (⟨3, by decide⟩ : Fin (Tag.rank .E6)) 1) (by decide) (by decide)
    rwa [ggKGEd_sum_single_mul] at this
  obtain ⟨hb0, hb1, hb2, hb3⟩ := ggKGEd_e6_pi_abs_le_root hβroot
  rw [ggKGEd_pi_apply_zero] at hb0
  rw [ggKGEd_pi_apply_one] at hb1
  rw [ggKGEd_pi_apply_two] at hb2
  rw [ggKGEd_pi_apply_three] at hb3
  have hz0 : β ⟨0, by decide⟩ + β ⟨5, by decide⟩ = 0 :=
    ggKGEd_eq_zero_of_dvd_of_abs_le hp5 hd0 hb0
  have hz1 : β ⟨1, by decide⟩ = 0 := ggKGEd_eq_zero_of_dvd_of_abs_le hp5 hd1 hb1
  have hz2 : β ⟨2, by decide⟩ + β ⟨4, by decide⟩ = 0 :=
    ggKGEd_eq_zero_of_dvd_of_abs_le hp5 hd2 hb2
  have hz3 : β ⟨3, by decide⟩ = 0 := ggKGEd_eq_zero_of_dvd_of_abs_le hp5 hd3 hb3
  apply ggKGEd_e6_root_ne_zero hβroot
  funext j
  simp only [Pi.zero_apply]
  rcases ggKGEd_e6_root_nonneg_or_nonpos hβroot with hnn | hnp
  · fin_cases j
    · have h0 := hnn ⟨0, by decide⟩
      have h5 := hnn ⟨5, by decide⟩
      linarith
    · exact hz1
    · have h2 := hnn ⟨2, by decide⟩
      have h4 := hnn ⟨4, by decide⟩
      linarith
    · exact hz3
    · have h2 := hnn ⟨2, by decide⟩
      have h4 := hnn ⟨4, by decide⟩
      linarith
    · have h0 := hnn ⟨0, by decide⟩
      have h5 := hnn ⟨5, by decide⟩
      linarith
  · fin_cases j
    · have h0 := hnp ⟨0, by decide⟩
      have h5 := hnp ⟨5, by decide⟩
      linarith
    · exact hz1
    · have h2 := hnp ⟨2, by decide⟩
      have h4 := hnp ⟨4, by decide⟩
      linarith
    · exact hz3
    · have h2 := hnp ⟨2, by decide⟩
      have h4 := hnp ⟨4, by decide⟩
      linarith
    · have h0 := hnp ⟨0, by decide⟩
      have h5 := hnp ⟨5, by decide⟩
      linarith

theorem ggKGExc_familyStabilizer_phi {k : Type} [Field k] {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    {ζ : k} (hζ : IsPrimitiveRoot ζ p) {ι : Type} (a : ι → Fin (Tag.rank .E6) → kˣ)
    (hall : ∀ b : Fin (Tag.rank .E6) → kˣ, (∀ j, b j ^ p = 1) →
      b ⟨0, by decide⟩ = b ⟨5, by decide⟩ → b ⟨2, by decide⟩ = b ⟨4, by decide⟩ → ∃ i, a i = b) :
    familyStabilizer a = {1} := by
  ext w
  simp only [Set.mem_singleton_iff]
  constructor
  · intro hw
    apply ggKGEd_eq_one_of_forall_height_pos
    intro i
    let β : Fin (Tag.rank .E6) → ℤ := w • (Pi.single i 1)
    have hβroot : IsRoot .E6 β := IsRoot.smul (IsRoot.basis i) w
    change 0 < height β
    have hdpi : ∀ t : Fin 4, (p : ℤ) ∣ ggKGEd_pi (β - Pi.single i 1) t := by
      have h0 := ggKGEd_dvd_of_stab hp hζ a hall hw (Pi.single i 1)
        ((Pi.single (⟨0, by decide⟩ : Fin (Tag.rank .E6)) 1 : Fin (Tag.rank .E6) → ℤ) +
          (Pi.single (⟨5, by decide⟩ : Fin (Tag.rank .E6)) 1 : Fin (Tag.rank .E6) → ℤ))
        (by decide) (by decide)
      have h1 := ggKGEd_dvd_of_stab hp hζ a hall hw (Pi.single i 1)
        (Pi.single (⟨1, by decide⟩ : Fin (Tag.rank .E6)) 1) (by decide) (by decide)
      have h2 := ggKGEd_dvd_of_stab hp hζ a hall hw (Pi.single i 1)
        ((Pi.single (⟨2, by decide⟩ : Fin (Tag.rank .E6)) 1 : Fin (Tag.rank .E6) → ℤ) +
          (Pi.single (⟨4, by decide⟩ : Fin (Tag.rank .E6)) 1 : Fin (Tag.rank .E6) → ℤ))
        (by decide) (by decide)
      have h3 := ggKGEd_dvd_of_stab hp hζ a hall hw (Pi.single i 1)
        (Pi.single (⟨3, by decide⟩ : Fin (Tag.rank .E6)) 1) (by decide) (by decide)
      have H0 : (p : ℤ) ∣ ggKGEd_pi (β - Pi.single i 1) ⟨0, by decide⟩ := by
        rw [ggKGEd_sum_add_single_mul] at h0
        rw [ggKGEd_pi_apply_zero]
        simpa [β, Pi.sub_apply] using h0
      have H1 : (p : ℤ) ∣ ggKGEd_pi (β - Pi.single i 1) ⟨1, by decide⟩ := by
        rw [ggKGEd_sum_single_mul] at h1
        rw [ggKGEd_pi_apply_one]
        simpa [β, Pi.sub_apply] using h1
      have H2 : (p : ℤ) ∣ ggKGEd_pi (β - Pi.single i 1) ⟨2, by decide⟩ := by
        rw [ggKGEd_sum_add_single_mul] at h2
        rw [ggKGEd_pi_apply_two]
        simpa [β, Pi.sub_apply] using h2
      have H3 : (p : ℤ) ∣ ggKGEd_pi (β - Pi.single i 1) ⟨3, by decide⟩ := by
        rw [ggKGEd_sum_single_mul] at h3
        rw [ggKGEd_pi_apply_three]
        simpa [β, Pi.sub_apply] using h3
      intro t
      fin_cases t
      · exact H0
      · exact H1
      · exact H2
      · exact H3
    have hfive : ∀ t : Fin 4, (5 : ℤ) ∣ ggKGEd_pi (β - Pi.single i 1) t := fun t =>
      ggKGEd_five_dvd_of_dvd_of_abs_le hp5 (hdpi t)
        (ggKGEd_e6_pi_sub_abs_le_root hβroot i t)
    have hnn : ∀ j, 0 ≤ β j := ggKGEd_e6_mod5_pos_root hβroot i hfive
    have hβne : β ≠ 0 := ggKGEd_e6_root_ne_zero hβroot
    rw [height]
    apply Finset.sum_pos'
    · intro j _
      exact hnn j
    · by_contra h
      apply hβne
      funext j
      simp only [Pi.zero_apply]
      by_contra hj
      exact h ⟨j, Finset.mem_univ j, lt_of_le_of_ne (hnn j) (Ne.symm hj)⟩
  · rintro rfl
    intro i v
    rw [one_smul]

end CFSG.StandardType
