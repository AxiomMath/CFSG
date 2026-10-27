module

public import CFSG.OddTranspositions.PartFour.Fourteen.TableE1Five

public section

namespace CFSG.OddTranspositions.PartFour

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace FivePlane

open TableE1Five

private theorem fact_prime_five : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩

attribute [local instance] fact_prime_five

private theorem five_eq_zero : (5 : ZMod 5) = 0 := by decide

variable {n : ℕ} {b : LinearMap.BilinForm (ZMod 5) (Fin n → ZMod 5)}

private theorem pow_three_eq_one_of_braid {H : Type*} [Group H] {a c : H} (ha : a * a = 1)
    (hc : c * c = 1) (h : a * c * a = c * a * c) : (a * c) ^ 3 = 1 := by
  have ha' : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  have hc' : c⁻¹ = c := inv_eq_of_mul_eq_one_right hc
  calc (a * c) ^ 3 = (a * c * a) * (c * a * c) := by
        simp only [pow_succ, pow_zero, one_mul, mul_assoc]
    _ = (c * a * c) * (c⁻¹ * a⁻¹ * c⁻¹) := by rw [h, ha', hc']
    _ = 1 := by group

private theorem pow_five_eq_one_of_braid {H : Type*} [Group H] {a c : H} (ha : a * a = 1)
    (hc : c * c = 1) (h : a * c * a * c * a = c * a * c * a * c) : (a * c) ^ 5 = 1 := by
  have ha' : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  have hc' : c⁻¹ = c := inv_eq_of_mul_eq_one_right hc
  calc (a * c) ^ 5 = (a * c * a * c * a) * (c * a * c * a * c) := by
        simp only [pow_succ, pow_zero, one_mul, mul_assoc]
    _ = (c * a * c * a * c) * (c⁻¹ * a⁻¹ * c⁻¹ * a⁻¹ * c⁻¹) := by rw [h, ha', hc']
    _ = 1 := by group

private theorem refl_mul_refl_mul_refl_eq_refl_act (hsym : ∀ x y, b x y = b y x)
    (x y : Fin n → ZMod 5) :
    refl b x * refl b y * refl b x = refl b (act (refl b x) y) := by
  rw [← conj_refl (refl_mem_isomGroup hsym x) y, refl_inv]

private theorem refl_mul_refl_five_eq_refl_act (hsym : ∀ x y, b x y = b y x)
    (x y : Fin n → ZMod 5) :
    refl b x * refl b y * refl b x * refl b y * refl b x =
      refl b (act (refl b x * refl b y) x) := by
  rw [← conj_refl ((isomGroup b).mul_mem (refl_mem_isomGroup hsym x)
    (refl_mem_isomGroup hsym y)), _root_.mul_inv_rev, refl_inv, refl_inv]
  group

theorem refl_mul_refl_pow_three (hsym : ∀ x y, b x y = b y x) {p q : Fin n → ZMod 5}
    (hp : b p p = 1) (hq : b q q = 1) (hpq : b p q = 2 ∨ b p q = -2) :
    (refl b p * refl b q) ^ 3 = 1 := by
  have hbraid : refl b p * refl b q * refl b p = refl b q * refl b p * refl b q := by
    rw [refl_mul_refl_mul_refl_eq_refl_act hsym p q,
      refl_mul_refl_mul_refl_eq_refl_act hsym q p]
    rcases hpq with h | h
    · congr 1
      rw [act_refl hp, act_refl hq, hsym q p, h]
      linear_combination (norm := module) five_eq_zero • (q - p)
    · rw [← refl_neg (act (refl b q) p)]
      congr 1
      rw [act_refl hp, act_refl hq, hsym q p, h]
      linear_combination (norm := module) five_eq_zero • (p + q)
  exact pow_three_eq_one_of_braid (refl_mul_self p) (refl_mul_self q) hbraid

theorem refl_mul_refl_pow_five (hsym : ∀ x y, b x y = b y x) {p q : Fin n → ZMod 5}
    (hp : b p p = 1) (hq : b q q = 1) (hpq : b p q = 1 ∨ b p q = -1) :
    (refl b p * refl b q) ^ 5 = 1 := by
  have hbraid : refl b p * refl b q * refl b p * refl b q * refl b p =
      refl b q * refl b p * refl b q * refl b p * refl b q := by
    rw [refl_mul_refl_five_eq_refl_act hsym p q,
      refl_mul_refl_five_eq_refl_act hsym q p]
    rcases hpq with h | h
    · congr 1
      simp only [act_mul, act_refl hp, act_refl hq, LinearMap.BilinForm.add_left,
        LinearMap.BilinForm.smul_left, hp, hq, hsym q p, h]
      linear_combination (norm := module) five_eq_zero • (p - q)
    · rw [← refl_neg (act (refl b q * refl b p) q)]
      congr 1
      simp only [act_mul, act_refl hp, act_refl hq, LinearMap.BilinForm.add_left,
        LinearMap.BilinForm.smul_left, hp, hq, hsym q p, h]
      linear_combination (norm := module) five_eq_zero • (p + q)
  exact pow_five_eq_one_of_braid (refl_mul_self p) (refl_mul_self q) hbraid

private theorem norm_eq_one_of_eq_smul_pair (hsym : ∀ x y, b x y = b y x)
    {p q x : Fin n → ZMod 5} (hp : b p p = 1) (hq : b q q = 1) (hx : b x x = 1)
    {l m : ZMod 5} (hxlm : x = l • p + m • q) :
    l * l + 2 * b p q * l * m + m * m = 1 := by
  have h := hx
  rw [hxlm] at h
  simp only [LinearMap.BilinForm.add_left, LinearMap.BilinForm.add_right,
    LinearMap.BilinForm.smul_left, LinearMap.BilinForm.smul_right, hp, hq, hsym q p] at h
  linear_combination h

theorem eq_of_mem_pair_of_sq_ne_one (hsym : ∀ x y, b x y = b y x) {p q x : Fin n → ZMod 5}
    (hp : b p p = 1) (hq : b q q = 1) (hpq : b p q ^ 2 ≠ 1) (hpq0 : b p q ≠ 0)
    (hx : b x x = 1) {l m : ZMod 5} (hxlm : x = l • p + m • q) :
    x = p ∨ x = -p ∨ x = q ∨ x = -q ∨ x = q - (2 * b p q) • p ∨ x = -(q - (2 * b p q) • p) := by
  have hxx := norm_eq_one_of_eq_smul_pair hsym hp hq hx hxlm
  have hkey : ∀ β l m : ZMod 5, β ^ 2 ≠ 1 → β ≠ 0 →
      l * l + 2 * β * l * m + m * m = 1 →
      (l = 1 ∧ m = 0) ∨ (l = -1 ∧ m = 0) ∨ (l = 0 ∧ m = 1) ∨
        (l = 0 ∧ m = -1) ∨ (l = -2 * β ∧ m = 1) ∨ (l = 2 * β ∧ m = -1) := by
    decide
  rcases hkey (b p q) l m hpq hpq0 hxx with
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · left
    rw [hxlm]
    simp
  · right; left
    rw [hxlm]
    simp
  · right; right; left
    rw [hxlm]
    simp
  · right; right; right; left
    rw [hxlm]
    simp
  · right; right; right; right; left
    rw [hxlm]
    module
  · right; right; right; right; right
    rw [hxlm]
    module

theorem eq_of_mem_pair_of_sq_eq_one (hsym : ∀ x y, b x y = b y x) {p q x : Fin n → ZMod 5}
    (hp : b p p = 1) (hq : b q q = 1) (hpq : b p q ^ 2 = 1) (hx : b x x = 1) {l m : ZMod 5}
    (hxlm : x = l • p + m • q) :
    ∃ t : ZMod 5, x = p + t • (p - b p q • q) ∨ x = -(p + t • (p - b p q • q)) := by
  have hβ : b p q * b p q = 1 := by
    rwa [pow_two] at hpq
  have hxx := norm_eq_one_of_eq_smul_pair hsym hp hq hx hxlm
  have hs : (l + b p q * m) * (l + b p q * m) = 1 := by
    calc (l + b p q * m) * (l + b p q * m)
        = l * l + 2 * b p q * l * m + (b p q * b p q) * (m * m) := by ring
      _ = l * l + 2 * b p q * l * m + 1 * (m * m) := by rw [hβ]
      _ = 1 := by simpa using hxx
  have hlin := mul_self_eq_one_iff.mp hs
  have hmm₁ : (-b p q * m) * b p q = -m := by
    linear_combination (-m) * hβ
  have hmm₂ : (b p q * m) * b p q = m := by
    linear_combination m * hβ
  rcases hlin with hlin | hlin
  · refine ⟨-b p q * m, Or.inl ?_⟩
    have hl : l = 1 - b p q * m := by linear_combination hlin
    have hR : p + (-b p q * m) • (p - b p q • q) =
        (1 - b p q * m) • p + m • q := by
      rw [smul_sub, smul_smul, hmm₁]
      module
    rw [hxlm, hl]
    exact hR.symm
  · refine ⟨b p q * m, Or.inr ?_⟩
    have hl : l = -1 - b p q * m := by linear_combination hlin
    have hR : p + (b p q * m) • (p - b p q • q) =
        -((-1 - b p q * m) • p + m • q) := by
      rw [smul_sub, smul_smul, hmm₂]
      module
    rw [hxlm, hl, hR, neg_neg]


private theorem ncard_le_one_of_mem_pair_class {α : Type*} {f : α → Fin n → ZMod 5}
    {S T : Set α} {v : Fin n → ZMod 5} (hT : T.Finite) (hTS : T ⊆ S)
    (hinj : ∀ z ∈ S, ∀ z' ∈ S, f z' = f z ∨ f z' = -f z → z' = z)
    (h : ∀ z ∈ T, f z = v ∨ f z = -v) : T.ncard ≤ 1 := by
  refine (Set.ncard_le_one hT).2 ?_
  intro z hz z' hz'
  have hrel : f z' = f z ∨ f z' = -f z := by
    rcases h z hz with hz1 | hz1 <;> rcases h z' hz' with hz2 | hz2
    · left; rw [hz1, hz2]
    · right; rw [hz1, hz2]
    · right; rw [hz1, hz2, neg_neg]
    · left; rw [hz1, hz2]
  exact (hinj z (hTS hz) z' (hTS hz') hrel).symm

private theorem ncard_le_five_of_mem_pair_of_sq_eq_one {α : Type*}
    (hsym : ∀ x y, b x y = b y x) {p q : Fin n → ZMod 5}
    (hp : b p p = 1) (hq : b q q = 1) (hβ : b p q ^ 2 = 1) {S : Set α}
    {f : α → Fin n → ZMod 5}
    (hf : ∀ z ∈ S, b (f z) (f z) = 1 ∧ ∃ l m : ZMod 5, f z = l • p + m • q)
    (hinj : ∀ z ∈ S, ∀ z' ∈ S, f z' = f z ∨ f z' = -f z → z' = z) :
    S.ncard ≤ 5 := by
  let e : Fin n → ZMod 5 := p - b p q • q
  have hex : ∀ z : S, ∃ t : ZMod 5,
      f z.1 = p + t • e ∨ f z.1 = -(p + t • e) := by
    intro z
    obtain ⟨hz1, l, m, hzlm⟩ := hf z.1 z.2
    exact eq_of_mem_pair_of_sq_eq_one hsym hp hq hβ hz1 hzlm
  let T : S → ZMod 5 := fun z => Classical.choose (hex z)
  have hT : ∀ z : S, f z.1 = p + T z • e ∨ f z.1 = -(p + T z • e) := fun z =>
    Classical.choose_spec (hex z)
  have hTinj : Function.Injective T := by
    intro z z' hzz
    have hrel : f z'.1 = f z.1 ∨ f z'.1 = -f z.1 := by
      rcases hT z with hz | hz <;> rcases hT z' with hz' | hz'
      · left; rw [hz', hz, hzz]
      · right; rw [hz', hz, hzz]
      · right; rw [hz', hz, hzz, neg_neg]
      · left; rw [hz', hz, hzz]
    exact Subtype.ext (hinj z.1 z.2 z'.1 z'.2 hrel).symm
  have hle : (Set.univ : Set S).ncard ≤ (Set.univ : Set (ZMod 5)).ncard :=
    Set.ncard_le_ncard_of_injOn T (fun _ _ => Set.mem_univ _) hTinj.injOn Set.finite_univ
  have hS : (Set.univ : Set S).ncard = S.ncard := by
    rw [Set.ncard_univ, Nat.card_coe_set_eq]
  have hZ : (Set.univ : Set (ZMod 5)).ncard = 5 := by
    rw [Set.ncard_univ, Nat.card_zmod]
  rwa [hS, hZ] at hle

private theorem ncard_le_three_of_mem_pair_of_sq_ne_one {α : Type*}
    (hsym : ∀ x y, b x y = b y x) {p q : Fin n → ZMod 5}
    (hp : b p p = 1) (hq : b q q = 1) (hpq0 : b p q ≠ 0) (hβ : b p q ^ 2 ≠ 1)
    {S : Set α} {f : α → Fin n → ZMod 5}
    (hf : ∀ z ∈ S, b (f z) (f z) = 1 ∧ ∃ l m : ZMod 5, f z = l • p + m • q)
    (hinj : ∀ z ∈ S, ∀ z' ∈ S, f z' = f z ∨ f z' = -f z → z' = z) :
    S.ncard ≤ 3 := by
  let third : Fin n → ZMod 5 := q - (2 * b p q) • p
  have hclass : ∀ z ∈ S, f z = p ∨ f z = -p ∨ f z = q ∨ f z = -q ∨
      f z = third ∨ f z = -third := by
    intro z hz
    obtain ⟨hz1, l, m, hzlm⟩ := hf z hz
    simpa only [third] using eq_of_mem_pair_of_sq_ne_one hsym hp hq hβ hpq0 hz1 hzlm
  by_cases hS : S.Finite
  · let A : Set α := {z | z ∈ S ∧ (f z = p ∨ f z = -p)}
    let B : Set α := {z | z ∈ S ∧ (f z = q ∨ f z = -q)}
    let C : Set α := {z | z ∈ S ∧ (f z = third ∨ f z = -third)}
    have hsub : S ⊆ A ∪ B ∪ C := by
      intro z hz
      rcases hclass z hz with h | h | h | h | h | h
      · exact Or.inl (Or.inl ⟨hz, Or.inl h⟩)
      · exact Or.inl (Or.inl ⟨hz, Or.inr h⟩)
      · exact Or.inl (Or.inr ⟨hz, Or.inl h⟩)
      · exact Or.inl (Or.inr ⟨hz, Or.inr h⟩)
      · exact Or.inr ⟨hz, Or.inl h⟩
      · exact Or.inr ⟨hz, Or.inr h⟩
    have hAf : A.Finite := hS.subset fun z hz => hz.1
    have hBf : B.Finite := hS.subset fun z hz => hz.1
    have hCf : C.Finite := hS.subset fun z hz => hz.1
    have hA : A.ncard ≤ 1 :=
      ncard_le_one_of_mem_pair_class hAf (fun z hz => hz.1) hinj (fun z hz => hz.2)
    have hB : B.ncard ≤ 1 :=
      ncard_le_one_of_mem_pair_class hBf (fun z hz => hz.1) hinj (fun z hz => hz.2)
    have hC : C.ncard ≤ 1 :=
      ncard_le_one_of_mem_pair_class hCf (fun z hz => hz.1) hinj (fun z hz => hz.2)
    have hcover : S.ncard ≤ (A ∪ B ∪ C).ncard :=
      Set.ncard_le_ncard hsub ((hAf.union hBf).union hCf)
    have hunion : (A ∪ B ∪ C).ncard ≤ A.ncard + B.ncard + C.ncard := by
      calc (A ∪ B ∪ C).ncard = ((A ∪ B) ∪ C).ncard := rfl
        _ ≤ (A ∪ B).ncard + C.ncard := Set.ncard_union_le _ _
        _ ≤ (A.ncard + B.ncard) + C.ncard := by
            exact Nat.add_le_add_right (Set.ncard_union_le A B) _
    calc S.ncard ≤ (A ∪ B ∪ C).ncard := hcover
      _ ≤ A.ncard + B.ncard + C.ncard := hunion
      _ ≤ 3 := by omega
  · have h0 : S.ncard = 0 := Set.Infinite.ncard (show S.Infinite from hS)
    omega

theorem ncard_le_of_mem_pair {α : Type*} (hsym : ∀ x y, b x y = b y x) {p q : Fin n → ZMod 5}
    (hp : b p p = 1) (hq : b q q = 1) (hpq0 : b p q ≠ 0) {S : Set α} {f : α → Fin n → ZMod 5}
    (hf : ∀ z ∈ S, b (f z) (f z) = 1 ∧ ∃ l m : ZMod 5, f z = l • p + m • q)
    (hinj : ∀ z ∈ S, ∀ z' ∈ S, f z' = f z ∨ f z' = -f z → z' = z) :
    S.ncard ≤ if b p q ^ 2 = 1 then 5 else 3 := by
  by_cases hβ : b p q ^ 2 = 1
  · rw [if_pos hβ]
    exact ncard_le_five_of_mem_pair_of_sq_eq_one hsym hp hq hβ hf hinj
  · rw [if_neg hβ]
    exact ncard_le_three_of_mem_pair_of_sq_ne_one hsym hp hq hpq0 hβ hf hinj


private theorem b_pair_ne_zero_of_mem_pair (hsym : ∀ x y, b x y = b y x)
    {p q x : Fin n → ZMod 5} (hp : b p p = 1) (hq : b q q = 1) (hpq0 : b p q ≠ 0)
    (hx : b x x = 1) {l m : ZMod 5} (hxlm : x = l • p + m • q) (hxp : x ≠ p)
    (hxp' : x ≠ -p) : b p x ≠ 0 := by
  by_cases hβ : b p q ^ 2 = 1
  · have hβ' : b p q * b p q = 1 := by rwa [pow_two] at hβ
    obtain ⟨t, ht⟩ := eq_of_mem_pair_of_sq_eq_one hsym hp hq hβ hx hxlm
    have hbpe : b p (p - b p q • q) = 0 := by
      rw [LinearMap.BilinForm.sub_right, LinearMap.BilinForm.smul_right, hp, hβ', sub_self]
    have hnorm : b p (p + t • (p - b p q • q)) = 1 := by
      rw [LinearMap.BilinForm.add_right, LinearMap.BilinForm.smul_right, hp, hbpe, mul_zero,
        add_zero]
    rcases ht with ht | ht <;> rw [ht]
    · rw [hnorm]
      exact one_ne_zero
    · rw [LinearMap.BilinForm.neg_right, hnorm]
      exact neg_ne_zero.mpr one_ne_zero
  · have hsix := eq_of_mem_pair_of_sq_ne_one hsym hp hq hβ hpq0 hx hxlm
    have hval3 : b p (q - (2 * b p q) • p) = -b p q := by
      rw [LinearMap.BilinForm.sub_right, LinearMap.BilinForm.smul_right, hp, mul_one]
      ring
    have hval3' : b p (-(q - (2 * b p q) • p)) = b p q := by
      rw [LinearMap.BilinForm.neg_right, hval3, neg_neg]
    rcases hsix with h | h | h | h | h | h
    · exact absurd h hxp
    · exact absurd h hxp'
    · rw [h]
      exact hpq0
    · rw [h, LinearMap.BilinForm.neg_right]
      exact neg_ne_zero.mpr hpq0
    · rw [h, hval3]
      exact neg_ne_zero.mpr hpq0
    · rw [h, hval3']
      exact hpq0

private theorem mem_pair_of_sq_eq_one_left {p q x : Fin n → ZMod 5} {t : ZMod 5}
    (hu : t * b p q ≠ 0) (ht : x = p + t • (p - b p q • q)) :
    ∃ l' m' : ZMod 5, q = l' • p + m' • x := by
  refine ⟨(t * b p q)⁻¹ * (1 + t), -(t * b p q)⁻¹, ?_⟩
  have hxexp : x = (1 + t) • p - (t * b p q) • q := by
    rw [ht, smul_sub, smul_smul]
    module
  have hmul : (t * b p q) • q = (1 + t) • p - x := by
    rw [hxexp]
    module
  calc q = ((t * b p q)⁻¹ * (t * b p q)) • q := by
        rw [inv_mul_cancel₀ hu, one_smul]
    _ = (t * b p q)⁻¹ • ((t * b p q) • q) := by rw [smul_smul]
    _ = (t * b p q)⁻¹ • ((1 + t) • p - x) := by rw [hmul]
    _ = ((t * b p q)⁻¹ * (1 + t)) • p + (-(t * b p q)⁻¹) • x := by
        rw [smul_sub, smul_smul]
        module

private theorem mem_pair_of_sq_eq_one_right {p q x : Fin n → ZMod 5} {t : ZMod 5}
    (hu : t * b p q ≠ 0) (ht : x = -(p + t • (p - b p q • q))) :
    ∃ l' m' : ZMod 5, q = l' • p + m' • x := by
  refine ⟨(t * b p q)⁻¹ * (1 + t), (t * b p q)⁻¹, ?_⟩
  have hxexp : x = -((1 + t) • p) + (t * b p q) • q := by
    rw [ht, smul_sub, smul_smul]
    module
  have hmul : (t * b p q) • q = x + (1 + t) • p := by
    rw [hxexp]
    module
  calc q = ((t * b p q)⁻¹ * (t * b p q)) • q := by
        rw [inv_mul_cancel₀ hu, one_smul]
    _ = (t * b p q)⁻¹ • ((t * b p q) • q) := by rw [smul_smul]
    _ = (t * b p q)⁻¹ • (x + (1 + t) • p) := by rw [hmul]
    _ = ((t * b p q)⁻¹ * (1 + t)) • p + (t * b p q)⁻¹ • x := by
        rw [smul_add, smul_smul]
        module

private theorem mem_pair_of_mem_pair_of_sq_eq_one (hsym : ∀ x y, b x y = b y x)
    {p q x : Fin n → ZMod 5} (hp : b p p = 1) (hq : b q q = 1)
    (hβ : b p q ^ 2 = 1) (hx : b x x = 1) {l m : ZMod 5}
    (hxlm : x = l • p + m • q) (hxp : x ≠ p) (hxp' : x ≠ -p) :
    ∃ l' m' : ZMod 5, q = l' • p + m' • x := by
  have hβ' : b p q * b p q = 1 := by rwa [pow_two] at hβ
  have hβne : b p q ≠ 0 := by
    rcases mul_self_eq_one_iff.mp hβ' with h | h <;> rw [h] <;> decide
  obtain ⟨t, ht⟩ := eq_of_mem_pair_of_sq_eq_one hsym hp hq hβ hx hxlm
  have htne : t ≠ 0 := by
    intro ht0
    rcases ht with ht | ht
    · apply hxp
      rw [ht, ht0, zero_smul, add_zero]
    · apply hxp'
      rw [ht, ht0, zero_smul, add_zero]
  rcases ht with ht | ht
  · exact mem_pair_of_sq_eq_one_left (mul_ne_zero htne hβne) ht
  · exact mem_pair_of_sq_eq_one_right (mul_ne_zero htne hβne) ht

private theorem mem_pair_of_mem_pair_of_sq_ne_one (hsym : ∀ x y, b x y = b y x)
    {p q x : Fin n → ZMod 5} (hp : b p p = 1) (hq : b q q = 1) (hpq0 : b p q ≠ 0)
    (hβ : b p q ^ 2 ≠ 1) (hx : b x x = 1) {l m : ZMod 5}
    (hxlm : x = l • p + m • q) (hxp : x ≠ p) (hxp' : x ≠ -p) :
    ∃ l' m' : ZMod 5, q = l' • p + m' • x := by
  have hsix := eq_of_mem_pair_of_sq_ne_one hsym hp hq hβ hpq0 hx hxlm
  rcases hsix with h | h | h | h | h | h
  · exact absurd h hxp
  · exact absurd h hxp'
  · exact ⟨0, 1, by rw [h]; simp⟩
  · exact ⟨0, -1, by rw [h]; simp⟩
  · exact ⟨2 * b p q, 1, by rw [h]; module⟩
  · exact ⟨2 * b p q, -1, by rw [h]; module⟩

private theorem mem_pair_of_mem_pair (hsym : ∀ x y, b x y = b y x)
    {p q x : Fin n → ZMod 5} (hp : b p p = 1) (hq : b q q = 1) (hpq0 : b p q ≠ 0)
    (hx : b x x = 1) {l m : ZMod 5} (hxlm : x = l • p + m • q) (hxp : x ≠ p)
    (hxp' : x ≠ -p) : ∃ l' m' : ZMod 5, q = l' • p + m' • x := by
  by_cases hβ : b p q ^ 2 = 1
  · exact mem_pair_of_mem_pair_of_sq_eq_one hsym hp hq hβ hx hxlm hxp hxp'
  · exact mem_pair_of_mem_pair_of_sq_ne_one hsym hp hq hpq0 hβ hx hxlm hxp hxp'

theorem ne_zero_and_mem_pair_of_mem_pair (hsym : ∀ x y, b x y = b y x) {p q x : Fin n → ZMod 5}
    (hp : b p p = 1) (hq : b q q = 1) (hpq0 : b p q ≠ 0) (hx : b x x = 1) {l m : ZMod 5}
    (hxlm : x = l • p + m • q) (hxp : x ≠ p) (hxp' : x ≠ -p) :
    b p x ≠ 0 ∧ ∃ l' m' : ZMod 5, q = l' • p + m' • x := by
  exact ⟨b_pair_ne_zero_of_mem_pair hsym hp hq hpq0 hx hxlm hxp hxp',
    mem_pair_of_mem_pair hsym hp hq hpq0 hx hxlm hxp hxp'⟩

end FivePlane

end CFSG.OddTranspositions.PartFour
