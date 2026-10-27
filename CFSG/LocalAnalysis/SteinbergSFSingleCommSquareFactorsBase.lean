module

public import CFSG.LocalAnalysis.SteinbergSFFullCenterWeylOvergroups

public section

namespace CFSG.LocalAnalysis.SymplecticFourStandard

namespace SingleComm

open Subgroup GomiFusion RootAxisTwoCore FullCenter FullCenterRadical FullCenterParabolic
  FullCenterTorus FullCenterWeyl
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain CFSG.QuasithinUnique.Setup.X7b
  CFSG.RankThree.PartOne.KCRootAxis
open scoped Matrix Pointwise

section General

variable {G : Type*} [Group G]

def commSub (X U : Subgroup G) (hXU : X ≤ normalizer (U : Set G)) (x : G) : Subgroup G where
  carrier := {y | y ∈ X ∧ x * y * x⁻¹ * y⁻¹ ∈ U}
  mul_mem' := by
    rintro y y' ⟨hy, h1⟩ ⟨hy', h2⟩
    refine ⟨mul_mem hy hy', ?_⟩
    have h3 := (mem_normalizer_iff.mp (hXU hy) _).mp h2
    have e : x * (y * y') * x⁻¹ * (y * y')⁻¹ =
        (x * y * x⁻¹ * y⁻¹) * (y * (x * y' * x⁻¹ * y'⁻¹) * y⁻¹) := by group
    rw [e]
    exact mul_mem h1 h3
  one_mem' := ⟨one_mem _, by rw [mul_one, mul_inv_cancel, inv_one, mul_one]; exact one_mem _⟩
  inv_mem' := by
    rintro y ⟨hy, h1⟩
    refine ⟨inv_mem hy, ?_⟩
    have h3 := (mem_normalizer_iff.mp (hXU (inv_mem hy)) _).mp (inv_mem h1)
    have e : x * y⁻¹ * x⁻¹ * y⁻¹⁻¹ = y⁻¹ * (x * y * x⁻¹ * y⁻¹)⁻¹ * y⁻¹⁻¹ := by group
    rw [e]
    exact h3

theorem mem_commSub {X U : Subgroup G} {hXU : X ≤ normalizer (U : Set G)} {x y : G} :
    y ∈ commSub X U hXU x ↔ y ∈ X ∧ x * y * x⁻¹ * y⁻¹ ∈ U :=
  Iff.rfl

theorem commSub_le {X U : Subgroup G} {hXU : X ≤ normalizer (U : Set G)} {x : G} :
    commSub X U hXU x ≤ X := fun _ hy => hy.1

theorem comm_mem_symm {U : Subgroup G} {x y : G} (h : x * y * x⁻¹ * y⁻¹ ∈ U) :
    y * x * y⁻¹ * x⁻¹ ∈ U := by
  have := inv_mem h
  rwa [show (x * y * x⁻¹ * y⁻¹)⁻¹ = y * x * y⁻¹ * x⁻¹ by group] at this

theorem kappa'_inv_mul (t x x' : G) :
    x * (t⁻¹ * ((x⁻¹ * x') * t * (x⁻¹ * x')⁻¹)) * x⁻¹ =
      (t⁻¹ * (x * t * x⁻¹))⁻¹ * (t⁻¹ * (x' * t * x'⁻¹)) := by
  group

theorem exists_coset_injective {X Y M L : Subgroup G} {t : G}
    (hXL : ∀ x ∈ X, ∀ l ∈ L, x * l * x⁻¹ ∈ L)
    (hXM : ∀ x ∈ X, t⁻¹ * (x * t * x⁻¹) ∈ M)
    (hY : ∀ x ∈ X, x ∈ Y ↔ t⁻¹ * (x * t * x⁻¹) ∈ L) :
    ∃ f : X ⧸ Y.subgroupOf X → M ⧸ L.subgroupOf M, Function.Injective f ∧
      ∀ x : X, f (x : X ⧸ Y.subgroupOf X) =
        ((⟨t⁻¹ * ((x : G) * t * (x : G)⁻¹), hXM x x.2⟩ : M) : M ⧸ L.subgroupOf M) := by
  set κ : X → M := fun x => ⟨t⁻¹ * ((x : G) * t * (x : G)⁻¹), hXM x x.2⟩ with hκ
  have key : ∀ x x' : X, ((κ x)⁻¹ * κ x' : M) ∈ L.subgroupOf M ↔
      (x⁻¹ * x' : X) ∈ Y.subgroupOf X := by
    intro x x'
    rw [mem_subgroupOf, mem_subgroupOf]
    have hxx' : ((x⁻¹ * x' : X) : G) ∈ X := (x⁻¹ * x').2
    rw [hY _ hxx']
    have e := kappa'_inv_mul t (x : G) (x' : G)
    simp only [coe_mul, coe_inv] at e ⊢
    rw [hκ]
    simp only
    rw [← e]
    constructor
    · intro h
      have := hXL _ (inv_mem x.2) _ h
      rwa [show (x : G)⁻¹ * ((x : G) * (t⁻¹ * (((x : G)⁻¹ * x') * t * ((x : G)⁻¹ * x')⁻¹)) *
        (x : G)⁻¹) * (x : G)⁻¹⁻¹ = t⁻¹ * (((x : G)⁻¹ * x') * t * ((x : G)⁻¹ * x')⁻¹) by group]
        at this
    · intro h
      exact hXL _ x.2 _ h
  refine ⟨Quotient.lift (fun x : X => ((κ x : M) : M ⧸ L.subgroupOf M)) ?_, ?_, fun x => rfl⟩
  · intro a b hab
    rw [QuotientGroup.eq, key]
    exact QuotientGroup.leftRel_apply.mp hab
  · intro a b hab
    induction a using QuotientGroup.induction_on with
    | H x =>
      induction b using QuotientGroup.induction_on with
      | H x' =>
        change ((κ x : M) : M ⧸ L.subgroupOf M) = κ x' at hab
        rw [QuotientGroup.eq, key] at hab
        exact QuotientGroup.eq.mpr hab

theorem relIndex_le_of_coset [Finite G] {X Y M L : Subgroup G} {t : G}
    (hXL : ∀ x ∈ X, ∀ l ∈ L, x * l * x⁻¹ ∈ L)
    (hXM : ∀ x ∈ X, t⁻¹ * (x * t * x⁻¹) ∈ M)
    (hY : ∀ x ∈ X, x ∈ Y ↔ t⁻¹ * (x * t * x⁻¹) ∈ L) :
    Y.relIndex X ≤ L.relIndex M := by
  obtain ⟨f, hf, -⟩ := exists_coset_injective hXL hXM hY
  exact Nat.card_le_card_of_injective f hf

theorem relIndex_eq_of_coset [Finite G] {X Y M L : Subgroup G} {t : G}
    (hXL : ∀ x ∈ X, ∀ l ∈ L, x * l * x⁻¹ ∈ L)
    (hXM : ∀ x ∈ X, t⁻¹ * (x * t * x⁻¹) ∈ M)
    (hY : ∀ x ∈ X, x ∈ Y ↔ t⁻¹ * (x * t * x⁻¹) ∈ L)
    (hsurj : ∀ m ∈ M, ∃ x ∈ X, (t⁻¹ * (x * t * x⁻¹))⁻¹ * m ∈ L) :
    Y.relIndex X = L.relIndex M := by
  obtain ⟨f, hf, hfx⟩ := exists_coset_injective hXL hXM hY
  refine Nat.card_eq_of_bijective f ⟨hf, fun q => ?_⟩
  induction q using QuotientGroup.induction_on with
  | H m =>
    obtain ⟨x, hx, hxm⟩ := hsurj m m.2
    refine ⟨((⟨x, hx⟩ : X) : X ⧸ Y.subgroupOf X), ?_⟩
    rw [hfx, QuotientGroup.eq, mem_subgroupOf]
    exact hxm

theorem coset_of_sub [Finite G] {X Y M L R : Subgroup G} {t : G}
    (hXL : ∀ x ∈ X, ∀ l ∈ L, x * l * x⁻¹ ∈ L)
    (hXM : ∀ x ∈ X, t⁻¹ * (x * t * x⁻¹) ∈ M)
    (hY : ∀ x ∈ X, x ∈ Y ↔ t⁻¹ * (x * t * x⁻¹) ∈ L)
    (hRX : R ≤ X) (hR : L.relIndex M ≤ (Y ⊓ R).relIndex R) :
    Y.relIndex X = L.relIndex M ∧ ∀ x ∈ X, ∃ y ∈ Y, ∃ r ∈ R, x = y * r := by
  obtain ⟨f, hf, hfx⟩ := exists_coset_injective hXL hXM hY
  obtain ⟨fR, hfR, hfRx⟩ := exists_coset_injective (X := R) (Y := Y ⊓ R)
    (fun x hx => hXL x (hRX hx)) (fun x hx => hXM x (hRX hx))
    (fun x hx => by rw [mem_inf, hY x (hRX hx)]; exact ⟨fun h => h.1, fun h => ⟨h, hx⟩⟩)
  have hbij : Function.Bijective fR := by
    refine (Function.Injective.bijective_of_nat_card_le hfR ?_)
    exact hR
  have hsurj : ∀ m : M, ∃ r : R, fR (r : R ⧸ (Y ⊓ R).subgroupOf R) =
      (m : M ⧸ L.subgroupOf M) := by
    intro m
    obtain ⟨q, hq⟩ := hbij.2 (m : M ⧸ L.subgroupOf M)
    induction q using QuotientGroup.induction_on with
    | H r => exact ⟨r, hq⟩
  have hX : ∀ x ∈ X, ∃ r ∈ R, x⁻¹ * r ∈ Y := by
    intro x hx
    obtain ⟨r, hr⟩ := hsurj ⟨_, hXM x hx⟩
    rw [hfRx] at hr
    have h1 : f ((⟨r, hRX r.2⟩ : X) : X ⧸ Y.subgroupOf X) = f ((⟨x, hx⟩ : X) : X ⧸ _) := by
      rw [hfx, hfx]
      exact hr
    have h2 := hf h1
    rw [QuotientGroup.eq, mem_subgroupOf] at h2
    refine ⟨r, r.2, ?_⟩
    have := inv_mem h2
    simpa using this
  refine ⟨?_, fun x hx => ?_⟩
  · refine relIndex_eq_of_coset hXL hXM hY fun m hm => ?_
    obtain ⟨r, hr⟩ := hsurj ⟨m, hm⟩
    rw [hfRx, QuotientGroup.eq, mem_subgroupOf] at hr
    exact ⟨r, hRX r.2, hr⟩
  · obtain ⟨r, hr, hxr⟩ := hX x⁻¹ (inv_mem hx)
    exact ⟨x⁻¹⁻¹ * r, hxr, r⁻¹, inv_mem hr, by group⟩

theorem mem_of_two_pow {R J : Subgroup G} (hJR : J ≤ normalizer (R : Set G)) {m : ℕ}
    (hm : Odd m) (hJm : ∀ j ∈ J, j ^ m = 1) {s : G} (hs : s ∈ R ⊔ J) {e : ℕ}
    (hse : s ^ 2 ^ e = 1) : s ∈ R := by
  rw [← SetLike.mem_coe, coe_mul_of_right_le_normalizer_left R J hJR] at hs
  obtain ⟨r, hr, j, hj, rfl⟩ := hs
  have hpow : ∀ N : ℕ, ∃ r' ∈ R, (r * j) ^ N = r' * j ^ N := by
    intro N
    induction N with
    | zero => exact ⟨1, one_mem _, by simp⟩
    | succ N ih =>
      obtain ⟨r', hr', hN⟩ := ih
      have hjr : j ^ N * r * (j ^ N)⁻¹ ∈ R :=
        (mem_normalizer_iff.mp (hJR (pow_mem hj N)) r).mp hr
      refine ⟨r' * (j ^ N * r * (j ^ N)⁻¹), mul_mem hr' hjr, ?_⟩
      rw [pow_succ, hN, pow_succ]
      group
  obtain ⟨r', hr', h1⟩ := hpow (2 ^ e)
  rw [hse] at h1
  have hjR : j ^ 2 ^ e ∈ R := by
    rw [eq_inv_of_mul_eq_one_right h1.symm]
    exact inv_mem hr'
  have hodd : Odd (orderOf j) := Odd.of_dvd_nat hm (orderOf_dvd_of_pow_eq_one (hJm j hj))
  have hcop : Nat.Coprime (2 ^ e) (orderOf j) :=
    Nat.Coprime.pow_left e (Nat.coprime_two_left.mpr hodd)
  obtain ⟨k, hk⟩ := exists_pow_eq_self_of_coprime hcop
  rw [← hk]
  exact mul_mem hr (pow_mem hjR k)

theorem conj_mem_pCore_normalizer {p : ℕ} {B B' : Subgroup G} {g : G}
    (hBB' : ∀ b ∈ B, g * b * g⁻¹ ∈ B') (hB'B : ∀ b ∈ B', g⁻¹ * b * g ∈ B) {x : G}
    (hx : x ∈ (CFSG.pCore p (normalizer (B : Set G))).map (normalizer (B : Set G)).subtype) :
    g * x * g⁻¹ ∈ (CFSG.pCore p (normalizer (B' : Set G))).map
      (normalizer (B' : Set G)).subtype := by
  set N := normalizer (B : Set G) with hN
  set N' := normalizer (B' : Set G) with hN'
  set E := (CFSG.pCore p N).map N.subtype with hE
  have hNN' : ∀ n ∈ N, g * n * g⁻¹ ∈ N' := by
    intro n hn
    rw [hN', mem_normalizer_iff]
    intro b
    constructor
    · intro hb
      have h1 := hB'B b hb
      have h2 := (mem_normalizer_iff.mp hn _).mp h1
      have h3 := hBB' _ h2
      rwa [show g * (n * (g⁻¹ * b * g) * n⁻¹) * g⁻¹ = g * n * g⁻¹ * b * (g * n * g⁻¹)⁻¹ by
        group] at h3
    · intro hb
      have h1 := hB'B _ hb
      rw [show g⁻¹ * (g * n * g⁻¹ * b * (g * n * g⁻¹)⁻¹) * g = n * (g⁻¹ * b * g) * n⁻¹ by
        group] at h1
      have h2 := (mem_normalizer_iff.mp hn _).mpr h1
      have h3 := hBB' _ h2
      rwa [show g * (g⁻¹ * b * g) * g⁻¹ = b by group] at h3
  have hN'N : ∀ n ∈ N', g⁻¹ * n * g ∈ N := by
    intro n hn
    rw [hN, mem_normalizer_iff]
    intro b
    constructor
    · intro hb
      have h1 := hBB' b hb
      have h2 := (mem_normalizer_iff.mp hn _).mp h1
      have h3 := hB'B _ h2
      rwa [show g⁻¹ * (n * (g * b * g⁻¹) * n⁻¹) * g = g⁻¹ * n * g * b * (g⁻¹ * n * g)⁻¹ by
        group] at h3
    · intro hb
      have h1 := hBB' _ hb
      rw [show g * (g⁻¹ * n * g * b * (g⁻¹ * n * g)⁻¹) * g⁻¹ = n * (g * b * g⁻¹) * n⁻¹ by
        group] at h1
      have h2 := (mem_normalizer_iff.mp hn _).mpr h1
      have h3 := hB'B _ h2
      rwa [show g⁻¹ * (g * b * g⁻¹) * g = b by group] at h3
  let S : Subgroup N' :=
    { carrier := {y | g⁻¹ * (y : G) * g ∈ E}
      mul_mem' := by
        intro a b ha hb
        change g⁻¹ * ((a : G) * b) * g ∈ E
        rw [show g⁻¹ * ((a : G) * b) * g = (g⁻¹ * a * g) * (g⁻¹ * b * g) by group]
        exact mul_mem ha hb
      one_mem' := by
        change g⁻¹ * (1 : G) * g ∈ E
        rw [mul_one, inv_mul_cancel]
        exact one_mem _
      inv_mem' := by
        intro a ha
        change g⁻¹ * ((a : G)⁻¹) * g ∈ E
        rw [show g⁻¹ * ((a : G)⁻¹) * g = (g⁻¹ * a * g)⁻¹ by group]
        exact inv_mem ha }
  have hSn : S.Normal := ⟨fun a ha n => by
    change g⁻¹ * ((n : G) * a * (n : G)⁻¹) * g ∈ E
    have hn := hN'N _ n.2
    rw [show g⁻¹ * ((n : G) * a * (n : G)⁻¹) * g =
      (g⁻¹ * n * g) * (g⁻¹ * a * g) * (g⁻¹ * n * g)⁻¹ by group]
    exact conj_mem_pCore_map hn ha⟩
  have hSp : IsPGroup p S := by
    intro a
    obtain ⟨e, he, he'⟩ := (show g⁻¹ * ((a : N') : G) * g ∈ E from a.2)
    obtain ⟨k, hk⟩ := CFSG.pCore_isPGroup (p := p) (G := N) ⟨e, he⟩
    refine ⟨k, Subtype.ext (Subtype.ext ?_)⟩
    have h1 := congrArg (fun y : CFSG.pCore p N => ((y : N) : G)) hk
    simp only [SubgroupClass.coe_pow, OneMemClass.coe_one] at h1
    simp only [SubgroupClass.coe_pow, OneMemClass.coe_one]
    have he'' : ((a : N') : G) = g * (e : G) * g⁻¹ := by
      rw [show (e : G) = N.subtype e from rfl, he']
      group
    rw [he'', show g * (e : G) * g⁻¹ = (MulAut.conj g) (e : G) by rfl, ← map_pow, h1, map_one]
  have hle : S ≤ CFSG.pCore p N' := le_sSup ⟨hSn, hSp⟩
  have hgx : g * x * g⁻¹ ∈ N' := hNN' x (map_subtype_le _ hx)
  have hmem : (⟨g * x * g⁻¹, hgx⟩ : N') ∈ S := by
    change g⁻¹ * (g * x * g⁻¹) * g ∈ E
    rw [show g⁻¹ * (g * x * g⁻¹) * g = x by group]
    exact hx
  exact ⟨_, hle hmem, rfl⟩

end General

section Model

variable {K : Type} [Field K] [CharP K 2]

theorem uElt_comm (a b c d a' b' c' d' : K) :
    uElt a b c d * uElt a' b' c' d' * (uElt a b c d)⁻¹ * (uElt a' b' c' d')⁻¹ =
      uElt 0 (a * d' + a' * d) (a ^ 2 * d' + a' ^ 2 * d) 0 := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  rw [uElt_inv, uElt_inv, uElt_mul, uElt_mul, uElt_mul]
  congr 1
  · linear_combination (a + a') * h2
  · linear_combination (b + b' + a * d' + a * d + d' * a') * h2
  · linear_combination (c + c' + 2 * a * b' + 3 * a * a' * d' + 2 * a * a' * d + a * b +
      a ^ 2 * d + b' * a' + 2 * a' * b + a' ^ 2 * d') * h2
  · linear_combination (d + d') * h2

theorem uElt_mem_center_iff {a b c d : K} :
    uElt a b c d ∈ antiUnipotentCenter K ↔ a = 0 ∧ d = 0 := by
  constructor
  · rintro ⟨b', c', h⟩
    obtain ⟨ha, -, -, hd⟩ := uElt_inj h
    exact ⟨ha, hd⟩
  · rintro ⟨rfl, rfl⟩
    exact ⟨b, c, rfl⟩

theorem uElt_mem_radA1_iff {a b c d : K} : uElt a b c d ∈ radA1 K ↔ a = 0 := by
  constructor
  · rintro ⟨b', c', d', h⟩
    exact (uElt_inj h).1
  · rintro rfl
    exact ⟨b, c, d, rfl⟩

theorem uElt_mem_radA2_iff {a b c d : K} : uElt a b c d ∈ radA2 K ↔ d = 0 := by
  constructor
  · rintro ⟨a', b', c', h⟩
    exact (uElt_inj h).2.2.2
  · rintro rfl
    exact ⟨a, b, c, rfl⟩

theorem uElt_mem_rootU_iff (i : Axis) {x y : K} :
    uElt 0 x y 0 ∈ rootU K i ↔ (i = Axis.one ∧ y = 0) ∨ (i = Axis.two ∧ x = 0) := by
  cases i
  · show uElt 0 x y 0 ∈ rootU₁ K ↔ _
    constructor
    · rintro ⟨b, h⟩
      exact Or.inl ⟨rfl, (uElt_inj h).2.2.1⟩
    · rintro (⟨-, rfl⟩ | ⟨h, -⟩)
      · exact ⟨x, rfl⟩
      · cases h
  · show uElt 0 x y 0 ∈ rootU₂ K ↔ _
    constructor
    · rintro ⟨c, h⟩
      exact Or.inr ⟨rfl, (uElt_inj h).2.1⟩
    · rintro (⟨h, -⟩ | ⟨-, rfl⟩)
      · cases h
      · exact ⟨y, rfl⟩

theorem uElt_sq_mem_rootU_iff (i : Axis) {a b c d : K} :
    uElt a b c d * uElt a b c d ∈ rootU K i ↔ a = 0 ∨ d = 0 := by
  rw [uElt_mul_self, uElt_mem_rootU_iff]
  cases i
  · simp only [true_and, reduceCtorEq, false_and, or_false]
    constructor
    · intro h
      rcases mul_eq_zero.mp h with h | h
      · exact Or.inl (pow_eq_zero_iff two_ne_zero |>.mp h)
      · exact Or.inr h
    · rintro (rfl | rfl) <;> simp
  · simp only [reduceCtorEq, false_and, true_and, false_or]
    exact mul_eq_zero

end Model

section Coord

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [CharP K 2]
  [Finite K] {n : ℕ} {φ : L ≃* antiSp K} {t : G}

local notation "𝐏" => pull φ (antiUnipotent K)
local notation "𝐙" => pull φ (antiUnipotentCenter K)
local notation "𝐀[" i "]" => pull φ (rootA K i)
local notation "𝐔[" i "]" => pull φ (rootU K i)
local notation "𝐮[" a "," b "," c "," d "]" => ((φ.symm (uElt a b c d) : L) : G)

omit [Finite G] [Finite K] in
theorem uElt_mem_P (a b c d : K) : 𝐮[a, b, c, d] ∈ 𝐏 :=
  symm_mem_pull.mpr (uElt_mem_antiUnipotent a b c d)

omit [Finite G] [Finite K] in
theorem exists_uElt_eq {p : G} (hp : p ∈ 𝐏) : ∃ a b c d : K, 𝐮[a, b, c, d] = p := by
  obtain ⟨x, ⟨a, b, c, d, rfl⟩, rfl⟩ := exists_eq_symm_of_mem_pull hp
  exact ⟨a, b, c, d, rfl⟩

omit [Finite G] [Finite K] in
theorem uElt_mul_G (a b c d A B C D : K) :
    𝐮[a, b, c, d] * 𝐮[A, B, C, D] =
      𝐮[a + A, b + B + a * D, c + C + a * B + a * A * D + b * A, d + D] := by
  rw [← coe_mul, ← map_mul, uElt_mul]

omit [Finite G] [Finite K] in
theorem uElt_comm_G (a b c d a' b' c' d' : K) :
    𝐮[a, b, c, d] * 𝐮[a', b', c', d'] * (𝐮[a, b, c, d])⁻¹ * (𝐮[a', b', c', d'])⁻¹ =
      𝐮[0, a * d' + a' * d, a ^ 2 * d' + a' ^ 2 * d, 0] := by
  rw [← uElt_comm a b c d a' b' c' d']
  simp only [map_mul, map_inv, coe_mul, coe_inv]

omit [Finite G] [Finite K] in
theorem uElt_mem_ZP_iff {a b c d : K} : 𝐮[a, b, c, d] ∈ 𝐙 ↔ a = 0 ∧ d = 0 := by
  rw [symm_mem_pull]
  exact uElt_mem_center_iff

omit [Finite G] [Finite K] in
theorem uElt_mem_A_one_iff {a b c d : K} : 𝐮[a, b, c, d] ∈ 𝐀[Axis.one] ↔ a = 0 := by
  rw [symm_mem_pull]
  exact uElt_mem_radA1_iff

omit [Finite G] [Finite K] in
theorem uElt_mem_A_two_iff {a b c d : K} : 𝐮[a, b, c, d] ∈ 𝐀[Axis.two] ↔ d = 0 := by
  rw [symm_mem_pull]
  exact uElt_mem_radA2_iff

omit [Finite G] [Finite K] in
theorem uElt_mem_U_iff (i : Axis) {x y : K} :
    𝐮[0, x, y, 0] ∈ 𝐔[i] ↔ (i = Axis.one ∧ y = 0) ∨ (i = Axis.two ∧ x = 0) := by
  rw [symm_mem_pull]
  exact uElt_mem_rootU_iff i

omit [Finite G] [Finite K] in
theorem sq_mem_U_iff (i : Axis) {p : G} (hp : p ∈ 𝐏) :
    p * p ∈ 𝐔[i] ↔ p ∈ 𝐀[Axis.one] ∨ p ∈ 𝐀[Axis.two] := by
  obtain ⟨a, b, c, d, rfl⟩ := exists_uElt_eq hp
  rw [uElt_mem_A_one_iff, uElt_mem_A_two_iff, ← coe_mul, ← map_mul, symm_mem_pull]
  exact uElt_sq_mem_rootU_iff i

omit [Finite G] [Finite K] in
theorem exists_test (i : Axis) {p : G} (hp : p ∈ 𝐏) (hpZ : p ∉ 𝐙) :
    ∃ e : K → G, (∀ ν, e ν ∈ 𝐏) ∧ (∀ ν μ, (e ν)⁻¹ * e μ = e (ν + μ)) ∧
      ∀ ν, p * e ν * p⁻¹ * (e ν)⁻¹ ∈ 𝐔[i] → ν = 0 := by
  obtain ⟨a, b, c, d, rfl⟩ := exists_uElt_eq hp
  rw [uElt_mem_ZP_iff] at hpZ
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  by_cases hd : d = 0
  · subst hd
    have ha : a ≠ 0 := fun ha => hpZ ⟨ha, rfl⟩
    refine ⟨fun ν => 𝐮[0, 0, 0, ν], fun ν => uElt_mem_P _ _ _ _, fun ν μ => ?_, fun ν hν => ?_⟩
    · rw [← coe_inv, ← map_inv, uElt_inv, ← coe_mul, ← map_mul, uElt_mul]
      congr 2
      congr 1 <;> ring
    · rw [uElt_comm_G, uElt_mem_U_iff] at hν
      rcases hν with ⟨-, h⟩ | ⟨-, h⟩
      · have h' : a ^ 2 * ν = 0 := by linear_combination h
        exact (mul_eq_zero.mp h').resolve_left (pow_ne_zero 2 ha)
      · have h' : a * ν = 0 := by linear_combination h
        exact (mul_eq_zero.mp h').resolve_left ha
  · refine ⟨fun ν => 𝐮[ν, 0, 0, 0], fun ν => uElt_mem_P _ _ _ _, fun ν μ => ?_, fun ν hν => ?_⟩
    · rw [← coe_inv, ← map_inv, uElt_inv, ← coe_mul, ← map_mul, uElt_mul]
      congr 2
      congr 1 <;> ring
    · rw [uElt_comm_G, uElt_mem_U_iff] at hν
      rcases hν with ⟨-, h⟩ | ⟨-, h⟩
      · have h' : ν ^ 2 * d = 0 := by linear_combination h
        exact pow_eq_zero_iff two_ne_zero |>.mp ((mul_eq_zero.mp h').resolve_right hd)
      · have h' : ν * d = 0 := by linear_combination h
        exact (mul_eq_zero.mp h').resolve_right hd

end Coord

theorem swap_swap (i : Axis) : i.swap.swap = i := by cases i <;> rfl

theorem swap_ne (i : Axis) : i.swap ≠ i := by cases i <;> exact fun h => by cases h

theorem eq_or_eq_swap (i k : Axis) : k = i ∨ k = i.swap := by
  cases i <;> cases k
  · exact Or.inl rfl
  · exact Or.inr rfl
  · exact Or.inr rfl
  · exact Or.inl rfl

theorem eq_of_swap_iff {i k m : Axis} (h : m = i.swap ↔ k = i.swap) : m = k := by
  cases i <;> cases k <;> cases m <;>
    first
    | rfl
    | exact absurd (h.mp rfl) (fun h' => by cases h')
    | exact absurd (h.mpr rfl) (fun h' => by cases h')

section Setting

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [CharP K 2]
  [Finite K] {n : ℕ} {φ : L ≃* antiSp K} {t : G}

local notation "𝐏" => pull φ (antiUnipotent K)
local notation "𝐐" => (pull φ (antiUnipotent K) ⊔ zpowers t : Subgroup G)
local notation "𝐙" => pull φ (antiUnipotentCenter K)
local notation "𝐁[" i "]" => (zpowers t ⊔ pull φ (rootA K i) : Subgroup G)
local notation "𝐀[" i "]" => pull φ (rootA K i)
local notation "𝐔[" i "]" => pull φ (rootU K i)
local notation "𝐍[" i "]" => normalizer (((zpowers t ⊔ pull φ (rootA K i) : Subgroup G) :
  Subgroup G) : Set G)
local notation "𝐌[" i "]" => normalizer (((zpowers t ⊔ pull φ (rootU K i) : Subgroup G) :
  Subgroup G) : Set G)
set_option quotPrecheck false in
local notation "𝐃[" i "]" => (CFSG.pCore 2 (normalizer
  (((zpowers t ⊔ pull φ (rootU K i) : Subgroup G) : Subgroup G) : Set G))).map
  (normalizer (((zpowers t ⊔ pull φ (rootU K i) : Subgroup G) : Subgroup G) : Set G)).subtype
set_option quotPrecheck false in
local notation "𝐄[" i "]" => (CFSG.pCore 2 (normalizer
  (((zpowers t ⊔ pull φ (rootA K i) : Subgroup G) : Subgroup G) : Set G))).map
  (normalizer (((zpowers t ⊔ pull φ (rootA K i) : Subgroup G) : Subgroup G) : Set G)).subtype
set_option quotPrecheck false in
local notation "𝐐[" i "]" => (pull φ (antiUnipotent K) ⊔ zpowers t ⊔ 𝐃[i] : Subgroup G)
set_option quotPrecheck false in
local notation "𝐑[" i "]" => (pull φ (antiUnipotent K) ⊔ zpowers t ⊔ 𝐄[i] : Subgroup G)
set_option quotPrecheck false in
local notation "𝐇" => (𝐐[Axis.one] ⊔ 𝐐[Axis.two] : Subgroup G)
set_option quotPrecheck false in
local notation "𝐄₀" => (𝐄[Axis.one] ⊓ 𝐄[Axis.two] : Subgroup G)
set_option quotPrecheck false in
local notation "𝐂" => centralizer ({t} : Set G)
local notation "𝐉" => pull φ (diagTorus K)
set_option quotPrecheck false in
local notation "𝐅" => closure {x : G | ∃ e ∈ 𝐄₀, ∃ j ∈ pull φ (diagTorus K),
  x = e⁻¹ * (j⁻¹ * e * j)}
local notation "𝐉[" i "]" => pull φ (axisTorus K i)
set_option quotPrecheck false in
local notation "𝐖[" i "]" => (𝐅 ⊓ centralizer (𝐉[i] : Set G) : Subgroup G)
set_option quotPrecheck false in
local notation "𝐊[" i "]" => (𝐀[i] ⊔ (𝐅 ⊓ 𝐃[i]) : Subgroup G)
set_option quotPrecheck false in
local notation "𝐊⋆" => (𝐊[Axis.one] ⊔ 𝐊[Axis.two] : Subgroup G)
set_option quotPrecheck false in
local notation "𝐋[" i "]" => (𝐅 ⊔ 𝐀[i] : Subgroup G)
set_option quotPrecheck false in
local notation "𝐍ₕ[" i "]" => (normalizer ((𝐇 : Subgroup G) : Set G) ⊓
  normalizer (𝐔[i] : Set G) : Subgroup G)

theorem H_le_normalizer_U (h : FCHyp L K n φ t) (i : Axis) :
    𝐇 ≤ normalizer (𝐔[i] : Set G) := fun _ hx =>
  mem_normalizer_of_conj_le fun u hu => by rw [h.H_centralizes_U i hx hu]; exact hu

theorem P_le_normalizer_U (h : FCHyp L K n φ t) (i : Axis) : 𝐏 ≤ normalizer (𝐔[i] : Set G) :=
  P_le_H.trans (H_le_normalizer_U h i)

theorem comm_U (h : FCHyp L K n φ t) (i : Axis) {x : G} (hx : x ∈ 𝐇) {u : G}
    (hu : u ∈ 𝐔[i]) : x * u = u * x := by
  have := h.H_centralizes_U i hx hu
  calc x * u = x * u * x⁻¹ * x := by group
    _ = u * x := by rw [this]

theorem card_commSub_P_le (h : FCHyp L K n φ t) (i : Axis) {p : G} (hp : p ∈ 𝐏) (hpZ : p ∉ 𝐙) :
    Nat.card (commSub 𝐏 𝐔[i] (P_le_normalizer_U h i) p) ≤ Nat.card K ^ 3 := by
  obtain ⟨e, heP, hemul, hecomm⟩ := exists_test i hp hpZ
  set S := commSub 𝐏 𝐔[i] (P_le_normalizer_U h i) p with hS
  let f : K → (𝐏 ⧸ S.subgroupOf 𝐏) := fun ν => ((⟨e ν, heP ν⟩ : 𝐏) : 𝐏 ⧸ S.subgroupOf 𝐏)
  have hf : Function.Injective f := by
    intro ν μ hνμ
    rw [QuotientGroup.eq, mem_subgroupOf] at hνμ
    simp only [coe_mul, coe_inv] at hνμ
    rw [hemul] at hνμ
    exact CharTwo.add_eq_zero.mp (hecomm _ hνμ.2)
  have h1 : Nat.card K ≤ S.relIndex 𝐏 := Nat.card_le_card_of_injective f hf
  have h2 := relIndex_mul_card S 𝐏
  rw [inf_of_le_left commSub_le, card_pull, (card_radicals (K := K)).1] at h2
  have hq : 0 < Nat.card K := Nat.card_pos
  have h3 : Nat.card K * Nat.card S ≤ Nat.card K * Nat.card K ^ 3 := by
    calc Nat.card K * Nat.card S ≤ S.relIndex 𝐏 * Nat.card S := Nat.mul_le_mul_right _ h1
      _ = Nat.card K * Nat.card K ^ 3 := by rw [h2]; ring
  exact Nat.le_of_mul_le_mul_left h3 hq

theorem Ks_eq_L (h : FCHyp L K n φ t) : 𝐊⋆ = 𝐋[Axis.one] ⊔ 𝐋[Axis.two] := by
  rw [Ks_eq h, P_eq_A_sup_A]
  apply le_antisymm
  · exact sup_le (le_sup_left.trans le_sup_left)
      (sup_le (le_sup_right.trans le_sup_left) (le_sup_right.trans le_sup_right))
  · exact sup_le (sup_le le_sup_left (le_sup_left.trans le_sup_right))
      (sup_le le_sup_left (le_sup_right.trans le_sup_right))

theorem L_le_Ks (h : FCHyp L K n φ t) (k : Axis) : 𝐋[k] ≤ 𝐊⋆ := by
  rw [Ks_eq_L h]
  cases k
  · exact le_sup_left
  · exact le_sup_right

theorem F_le_Ks (h : FCHyp L K n φ t) : 𝐅 ≤ 𝐊⋆ := (F_le_L Axis.one).trans (L_le_Ks h _)

theorem P_le_Ks (h : FCHyp L K n φ t) : 𝐏 ≤ 𝐊⋆ := by
  rw [Ks_eq h]
  exact le_sup_right

theorem exists_F_mul_P (h : FCHyp L K n φ t) {x : G} (hx : x ∈ 𝐊⋆) :
    ∃ f ∈ 𝐅, ∃ p ∈ 𝐏, f * p = x := by
  rw [← SetLike.mem_coe, ← F_mul_P h] at hx
  obtain ⟨f, hf, p, hp, rfl⟩ := hx
  exact ⟨f, hf, p, hp, rfl⟩

theorem exists_W_mul (h : FCHyp L K n φ t) (i : Axis) {f : G} (hf : f ∈ 𝐅) :
    ∃ w ∈ 𝐖[i], ∃ w' ∈ 𝐖[i.swap], w * w' = f := by
  rw [← SetLike.mem_coe, ← W_mul_W h] at hf
  obtain ⟨x, hx, y, hy, rfl⟩ := hf
  cases i
  · exact ⟨x, hx, y, hy, rfl⟩
  · exact ⟨y, hy, x, hx, (W_comm h hx hy).symm⟩

theorem exists_L_decomp (h : FCHyp L K n φ t) (i k : Axis) {y : G} (hy : y ∈ 𝐋[k]) :
    ∃ w ∈ 𝐖[i], ∃ w' ∈ 𝐖[i.swap], ∃ a ∈ 𝐀[k], w * w' * a = y := by
  rw [← SetLike.mem_coe, ← L_mul h] at hy
  obtain ⟨f, hf, a, ha, rfl⟩ := hy
  obtain ⟨w, hw, w', hw', rfl⟩ := exists_W_mul h i hf
  exact ⟨w, hw, w', hw', a, ha, rfl⟩

theorem W_sq_mem_U (h : FCHyp L K n φ t) (k : Axis) {w : G} (hw : w ∈ 𝐖[k]) :
    w * w ∈ 𝐔[k] := by
  obtain ⟨-, lam, hlam, -⟩ := square_map h k
  obtain ⟨a, ha⟩ := exists_coordG_eq φ k (kappa_mem_U h k (mem_inf.mp (W_le_Fi h k hw)).2)
  rw [hlam w hw a ha.symm]
  exact coordG_mem φ k _

omit [Finite G] [Finite K] in
theorem A_mul_self (h : FCHyp L K n φ t) (k : Axis) {a : G} (ha : a ∈ 𝐀[k]) : a * a = 1 :=
  h.B_mul_self k (mem_sup_right ha)

theorem A_swap_comm_F (h : FCHyp L K n φ t) (i : Axis) (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥)
    {a : G} (ha : a ∈ 𝐀[i.swap]) {f : G} (hf : f ∈ 𝐅) : a * f = f * a := by
  have hc : ∀ x ∈ 𝐅 ⊓ 𝐃[i], a * x = x * a := fun x hx =>
    (mem_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hbot ha) x hx).symm
  have hc' : ∀ x ∈ 𝐅 ⊓ 𝐃[i.swap], a * x = x * a := fun x hx => A_comm_D h i.swap ha hx.2
  obtain ⟨w, hw, w', hw', rfl⟩ := exists_W_mul h i hf
  exact (Commute.mul_right (hc w (W_le_Fi h i hw)) (hc' w' (W_le_Fi h i.swap hw'))).eq

theorem L_swap_comm (h : FCHyp L K n φ t) (i : Axis) (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥)
    {x y : G} (hx : x ∈ 𝐋[i.swap]) (hy : y ∈ 𝐋[i.swap]) : x * y = y * x := by
  rw [← SetLike.mem_coe, ← L_mul h] at hx hy
  obtain ⟨f, hf, a, ha, rfl⟩ := hx
  obtain ⟨g, hg, b, hb, rfl⟩ := hy
  have h1 : Commute f g := F_comm h hf hg
  have h2 : Commute f b := (A_swap_comm_F h i hbot hb hf).symm
  have h3 : Commute a g := A_swap_comm_F h i hbot ha hg
  have h4 : Commute a b := A_mul_comm h i.swap ha hb
  exact (Commute.mul_left (Commute.mul_right h1 h2) (Commute.mul_right h3 h4)).eq

theorem L_comm_mod (h : FCHyp L K n φ t) (i : Axis) {x y : G} (hx : x ∈ 𝐋[i])
    (hy : y ∈ 𝐋[i]) : x * y * x⁻¹ * y⁻¹ ∈ 𝐔[i] := by
  obtain ⟨-, hn, hc⟩ := L_quot_comm h i
  have e := hc.is_comm.comm ((⟨x, hx⟩ : 𝐋[i]) : 𝐋[i] ⧸ (𝐔[i]).subgroupOf 𝐋[i])
    ((⟨y, hy⟩ : 𝐋[i]) : 𝐋[i] ⧸ (𝐔[i]).subgroupOf 𝐋[i])
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, mem_subgroupOf] at e
  simp only [coe_mul, coe_inv] at e
  have hxy : x * y ∈ 𝐇 := mul_mem ((L_le_Hi h i).trans inf_le_left hx)
    ((L_le_Hi h i).trans inf_le_left hy)
  have h1 := (mem_normalizer_iff.mp (H_le_normalizer_U h i hxy) _).mp (inv_mem e)
  rwa [show x * y * ((x * y)⁻¹ * (y * x))⁻¹ * (x * y)⁻¹ = x * y * x⁻¹ * y⁻¹ by group] at h1

theorem L_comm_mod_U (h : FCHyp L K n φ t) (i : Axis) (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥)
    (k : Axis) {x y : G} (hx : x ∈ 𝐋[k]) (hy : y ∈ 𝐋[k]) : x * y * x⁻¹ * y⁻¹ ∈ 𝐔[i] := by
  rcases eq_or_eq_swap i k with rfl | rfl
  · exact L_comm_mod h k hx hy
  · rw [L_swap_comm h i hbot hx hy, mul_inv_cancel_right, mul_inv_cancel]
    exact one_mem _

theorem P_comm_F_mod (h : FCHyp L K n φ t) (i : Axis) (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥)
    {p : G} (hp : p ∈ 𝐏) {f : G} (hf : f ∈ 𝐅) : p * f * p⁻¹ * f⁻¹ ∈ 𝐔[i] := by
  set T := commSub 𝐇 𝐔[i] (H_le_normalizer_U h i) f with hT
  have hAi : 𝐀[i] ≤ T := fun a ha => ⟨A_le_H h i ha, comm_mem_symm (by
    have := commutator_le.mp (commutator_A_F h i) a ha f hf
    rwa [commutatorElement_def] at this)⟩
  have hAj : 𝐀[i.swap] ≤ T := fun a ha => ⟨A_le_H h i.swap ha, by
    rw [← A_swap_comm_F h i hbot ha hf, mul_inv_cancel_right, mul_inv_cancel]
    exact one_mem _⟩
  have hPT : 𝐏 ≤ T := by
    rw [P_eq_A_sup_A]
    cases i
    · exact sup_le hAi hAj
    · exact sup_le hAj hAi
  exact comm_mem_symm (hPT hp).2

theorem Ks_comm_F_mod (h : FCHyp L K n φ t) (i : Axis) (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥)
    {x : G} (hx : x ∈ 𝐊⋆) {f : G} (hf : f ∈ 𝐅) : x * f * x⁻¹ * f⁻¹ ∈ 𝐔[i] := by
  have hle : 𝐊⋆ ≤ commSub 𝐇 𝐔[i] (H_le_normalizer_U h i) f := by
    rw [Ks_eq h]
    refine sup_le (fun g hg => ⟨F_le_H h hg, ?_⟩)
      (fun p hp => ⟨P_le_H hp, comm_mem_symm (P_comm_F_mod h i hbot hp hf)⟩)
    rw [F_comm h hf hg, mul_inv_cancel_right, mul_inv_cancel]
    exact one_mem _
  exact comm_mem_symm (hle hx).2

theorem F_le_commSub (h : FCHyp L K n φ t) (i : Axis) (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥)
    {x : G} (hx : x ∈ 𝐊⋆) : 𝐅 ≤ commSub 𝐇 𝐔[i] (H_le_normalizer_U h i) x := fun _ hf =>
  ⟨F_le_H h hf, Ks_comm_F_mod h i hbot hx hf⟩

theorem card_le_of_comm_mod (h : FCHyp L K n φ t) (i : Axis)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) {S : Subgroup G} (hSK : S ≤ 𝐊⋆)
    (hS : ∀ x ∈ S, ∀ y ∈ S, x * y * x⁻¹ * y⁻¹ ∈ 𝐔[i]) :
    Nat.card S ≤ Nat.card K * Nat.card (S ⊓ 𝐅 : Subgroup G) := by
  set S'' := (S ⊔ 𝐅) ⊓ 𝐏 with hS''
  have hSN : S ≤ normalizer (𝐅 : Set G) :=
    hSK.trans ((Ks_le_H h).trans (H_le_normalizer_F h))
  have hSFK : S ⊔ 𝐅 ≤ 𝐊⋆ := sup_le hSK (F_le_Ks h)
  have hcomm : ∀ x ∈ S ⊔ 𝐅, ∀ y ∈ S ⊔ 𝐅, x * y * x⁻¹ * y⁻¹ ∈ 𝐔[i] := by
    have hSF : ((S ⊔ 𝐅 : Subgroup G) : Set G) = (𝐅 : Set G) * (S : Set G) := by
      rw [sup_comm S 𝐅]
      exact coe_mul_of_right_le_normalizer_left 𝐅 S hSN
    intro x hx y hy
    have hyK := hSFK hy
    rw [← SetLike.mem_coe, hSF] at hx hy
    obtain ⟨f, hf, s, hs, rfl⟩ := hx
    obtain ⟨f', hf', s', hs', rfl⟩ := hy
    have hsy : s ∈ commSub 𝐇 𝐔[i] (H_le_normalizer_U h i) (f' * s') := by
      have h1 : f' * s' ∈ commSub 𝐇 𝐔[i] (H_le_normalizer_U h i) s :=
        mul_mem (F_le_commSub h i hbot (hSK hs) hf') ⟨Ks_le_H h (hSK hs'), hS s hs s' hs'⟩
      exact ⟨Ks_le_H h (hSK hs), comm_mem_symm h1.2⟩
    have h2 : f * s ∈ commSub 𝐇 𝐔[i] (H_le_normalizer_U h i) (f' * s') :=
      mul_mem (F_le_commSub h i hbot hyK hf) hsy
    exact comm_mem_symm h2.2
  have hS''card : Nat.card S'' ≤ Nat.card K ^ 3 := by
    by_cases hZ : S'' ≤ 𝐙
    · calc Nat.card S'' ≤ Nat.card 𝐙 := card_le_of_le hZ
        _ = Nat.card K ^ 2 := FCHyp.card_ZP
        _ ≤ Nat.card K ^ 3 := Nat.pow_le_pow_right Nat.card_pos (by norm_num)
    · obtain ⟨p, hpS, hpZ⟩ := IsConcreteLE.not_le_iff_exists.mp hZ
      have hle : S'' ≤ commSub 𝐏 𝐔[i] (P_le_normalizer_U h i) p := fun y hy =>
        ⟨(mem_inf.mp hy).2, hcomm p (mem_inf.mp hpS).1 y (mem_inf.mp hy).1⟩
      exact (card_le_of_le hle).trans (card_commSub_P_le h i (mem_inf.mp hpS).2 hpZ)
  have hsup : S ⊔ 𝐅 = 𝐅 ⊔ S'' := by
    apply le_antisymm
    · intro x hx
      obtain ⟨f, hf, p, hp, rfl⟩ := exists_F_mul_P h (hSFK hx)
      have hpS : p ∈ S'' := mem_inf.mpr ⟨by simpa using mul_mem (inv_mem (mem_sup_right hf)) hx,
        hp⟩
      exact mul_mem (mem_sup_left hf) (mem_sup_right hpS)
    · exact sup_le le_sup_right inf_le_left
  have hinf : 𝐅 ⊓ S'' = 𝐙 := by
    apply le_antisymm
    · intro x hx
      rw [← F_inf_P h]
      exact mem_inf.mpr ⟨(mem_inf.mp hx).1, (mem_inf.mp (mem_inf.mp hx).2).2⟩
    · exact le_inf (ZP_le_F h) (le_inf ((ZP_le_F h).trans le_sup_right) Setup.ZP_le_PG)
  have hS''N : S'' ≤ normalizer (𝐅 : Set G) := inf_le_right.trans (P_le_H.trans
    (H_le_normalizer_F h))
  have h1 := card_sup_mul_card_inf 𝐅 S hSN
  have h2 := card_sup_mul_card_inf 𝐅 S'' hS''N
  rw [show 𝐅 ⊔ S = 𝐅 ⊔ S'' by rw [sup_comm 𝐅 S, hsup], inf_comm 𝐅 S] at h1
  rw [hinf, FCHyp.card_ZP] at h2
  set a := Nat.card S with ha
  set b := Nat.card (S ⊓ 𝐅 : Subgroup G) with hb
  set c := Nat.card S'' with hc
  set X := Nat.card (𝐅 ⊔ S'' : Subgroup G) with hX
  set f := Nat.card 𝐅 with hf
  set q := Nat.card K with hq
  have hf0 : 0 < f := Nat.card_pos
  have hq0 : 0 < q := Nat.card_pos
  have key : f * (a * q ^ 2) ≤ f * (q * b * q ^ 2) := by
    have e1 : f * (a * q ^ 2) = X * q ^ 2 * b := by rw [← mul_assoc, ← h1]; ring
    rw [e1, h2]
    calc f * c * b ≤ f * q ^ 3 * b := by gcongr
      _ = f * (q * b * q ^ 2) := by ring
  have key' := Nat.le_of_mul_le_mul_left key hf0
  exact Nat.le_of_mul_le_mul_right key' (by positivity)

theorem le_Ks_of_comm_mod (h : FCHyp L K n φ t) (i : Axis) (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥)
    {Y : Subgroup G} (hYH : Y ≤ 𝐇) (hY : ∀ x ∈ Y, ∀ y ∈ Y, x * y * x⁻¹ * y⁻¹ ∈ 𝐔[i])
    (hcard : Nat.card K ^ 5 ≤ Nat.card Y) : Y ≤ 𝐊⋆ := by
  by_contra hYK
  obtain ⟨y₀, hy₀Y, hy₀K⟩ := IsConcreteLE.not_le_iff_exists.mp hYK
  have htt := h.setup.t_mul_t
  have htN : t ∈ normalizer (𝐊⋆ : Set G) :=
    mem_normalizer_of_conj_le fun _ hk => conj_H_mem_Ks h t_mem_H hk
  have hor : ∀ y ∈ Y, y ∈ 𝐊⋆ ∨ t * y ∈ 𝐊⋆ := fun y hy =>
    mem_or_mul_mem htt htN (by rw [(Ks_sup_t h).2]; exact hYH hy)
  have hty₀ : t * y₀ ∈ 𝐊⋆ := (hor y₀ hy₀Y).resolve_left hy₀K
  have hidx : 𝐊⋆.relIndex Y ≤ 2 := relIndex_le_two ⟨y₀, hy₀Y, fun b hb => by
    by_cases hbK : b ∈ 𝐊⋆
    · exact Or.inr hbK
    · exact Or.inl ((mul_mem_iff_of htt htN (hor b hb) (hor y₀ hy₀Y)).mpr
        (iff_of_false hbK hy₀K))⟩
  have h1 := relIndex_mul_card 𝐊⋆ Y
  have h2 := card_le_of_comm_mod h i hbot (inf_le_left : 𝐊⋆ ⊓ Y ≤ 𝐊⋆)
    (fun x hx y hy => hY x hx.2 y hy.2)
  have hSF : 𝐊⋆ ⊓ Y ⊓ 𝐅 ≤ 𝐅 ⊓ 𝐃[i] := by
    intro f hf
    obtain ⟨⟨-, hfY⟩, hfF⟩ := hf
    have hT1 : y₀ ∈ commSub 𝐇 𝐔[i] (H_le_normalizer_U h i) f := ⟨hYH hy₀Y, hY f hfY y₀ hy₀Y⟩
    have hT2 : t * y₀ ∈ commSub 𝐇 𝐔[i] (H_le_normalizer_U h i) f :=
      ⟨Ks_le_H h hty₀, comm_mem_symm (Ks_comm_F_mod h i hbot hty₀ hfF)⟩
    have hT3 : t ∈ commSub 𝐇 𝐔[i] (H_le_normalizer_U h i) f := by
      have := mul_mem hT2 (inv_mem hT1)
      rwa [mul_inv_cancel_right] at this
    have hT4 : f⁻¹ ∈ commSub 𝐇 𝐔[i] (H_le_normalizer_U h i) t :=
      inv_mem ⟨F_le_H h hfF, comm_mem_symm hT3.2⟩
    have hκ : t⁻¹ * (f⁻¹ * t * f) ∈ 𝐔[i] := by
      have e : t⁻¹ * (f⁻¹ * t * f) = t * f⁻¹ * t⁻¹ * f⁻¹⁻¹ := by
        rw [inv_inv, h.twoCore.t_inv]
        group
      rw [e]
      exact hT4.2
    exact mem_inf.mpr ⟨hfF, mem_D_of_kappa h i (F_le_E h i hfF) hκ⟩
  have h3 : Nat.card (𝐊⋆ ⊓ Y ⊓ 𝐅 : Subgroup G) ≤ Nat.card K ^ 3 :=
    (card_le_of_le hSF).trans (card_Fi h i).le
  have h5 : Nat.card Y ≤ 2 * (Nat.card K * Nat.card K ^ 3) := by
    rw [← h1]
    calc 𝐊⋆.relIndex Y * Nat.card (𝐊⋆ ⊓ Y : Subgroup G) ≤ 2 * Nat.card (𝐊⋆ ⊓ Y : Subgroup G) :=
          Nat.mul_le_mul_right _ hidx
      _ ≤ 2 * (Nat.card K * Nat.card (𝐊⋆ ⊓ Y ⊓ 𝐅 : Subgroup G)) := Nat.mul_le_mul_left _ h2
      _ ≤ 2 * (Nat.card K * Nat.card K ^ 3) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ h3)
  have h6 : 2 * (Nat.card K * Nat.card K ^ 3) < Nat.card K ^ 5 := by
    have h4 := h.four_le_card
    have hq4 : 0 < Nat.card K ^ 4 := by positivity
    calc 2 * (Nat.card K * Nat.card K ^ 3) = 2 * Nat.card K ^ 4 := by ring
      _ < Nat.card K * Nat.card K ^ 4 := Nat.mul_lt_mul_of_pos_right (by omega) hq4
      _ = Nat.card K ^ 5 := by ring
  omega

theorem Nhat_le_normalizer_Ks (h : FCHyp L K n φ t) (i : Axis)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) : 𝐍ₕ[i] ≤ normalizer (𝐊⋆ : Set G) := by
  intro g hg
  obtain ⟨hgH, hgU⟩ := mem_inf.mp hg
  have hL : ∀ k : Axis, 𝐋[k] ≤ 𝐊⋆.comap (MulAut.conj g).toMonoidHom := by
    intro k
    set Y := 𝐋[k].map (MulAut.conj g).toMonoidHom with hY
    have hLH : 𝐋[k] ≤ 𝐇 := (L_le_Hi h k).trans inf_le_left
    have hYH : Y ≤ 𝐇 := by
      rintro _ ⟨x, hx, rfl⟩
      exact (mem_normalizer_iff.mp hgH x).mp (hLH hx)
    have hYc : ∀ x ∈ Y, ∀ y ∈ Y, x * y * x⁻¹ * y⁻¹ ∈ 𝐔[i] := by
      rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      have h1 := (mem_normalizer_iff.mp hgU _).mp (L_comm_mod_U h i hbot k hx hy)
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      rwa [show g * x * g⁻¹ * (g * y * g⁻¹) * (g * x * g⁻¹)⁻¹ * (g * y * g⁻¹)⁻¹ =
        g * (x * y * x⁻¹ * y⁻¹) * g⁻¹ by group]
    have hYcard : Nat.card K ^ 5 ≤ Nat.card Y := by
      rw [hY, card_map_of_injective (MulAut.conj g).injective, card_L h k]
    intro x hx
    exact le_Ks_of_comm_mod h i hbot hYH hYc hYcard ⟨x, hx, rfl⟩
  refine mem_normalizer_of_conj_le fun x hx => ?_
  rw [Ks_eq_L h] at hx
  exact sup_le (hL _) (hL _) hx

theorem mem_F_of_comm_mod (h : FCHyp L K n φ t) (i : Axis) (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥)
    {x : G} (hx : x ∈ 𝐊⋆) (hc : ∀ y ∈ 𝐊⋆, x * y * x⁻¹ * y⁻¹ ∈ 𝐔[i]) : x ∈ 𝐅 := by
  obtain ⟨f, hf, p, hp, rfl⟩ := exists_F_mul_P h hx
  by_contra hfp
  have hpZ : p ∉ 𝐙 := fun hpZ => hfp (mul_mem hf (ZP_le_F h hpZ))
  have hle : 𝐏 ≤ commSub 𝐏 𝐔[i] (P_le_normalizer_U h i) p := by
    intro y hy
    have hyK := P_le_Ks h hy
    have h1 : f * p ∈ commSub 𝐇 𝐔[i] (H_le_normalizer_U h i) y :=
      ⟨Ks_le_H h hx, comm_mem_symm (hc y hyK)⟩
    have h2 : p ∈ commSub 𝐇 𝐔[i] (H_le_normalizer_U h i) y := by
      have := mul_mem (inv_mem (F_le_commSub h i hbot hyK hf)) h1
      rwa [inv_mul_cancel_left] at this
    exact ⟨hy, comm_mem_symm h2.2⟩
  have h1 := card_le_of_le hle
  rw [card_pull, (card_radicals (K := K)).1] at h1
  have h2 := card_commSub_P_le h i hp hpZ
  have h3 : Nat.card K ^ 3 < Nat.card K ^ 4 :=
    Nat.pow_lt_pow_right (by have := h.four_le_card; omega) (by norm_num)
  omega

theorem Nhat_le_normalizer_F (h : FCHyp L K n φ t) (i : Axis)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) : 𝐍ₕ[i] ≤ normalizer (𝐅 : Set G) := by
  intro g hg
  have hgK := Nhat_le_normalizer_Ks h i hbot hg
  have hgU := (mem_inf.mp hg).2
  refine mem_normalizer_of_conj_le fun f hf => ?_
  refine mem_F_of_comm_mod h i hbot ((mem_normalizer_iff.mp hgK f).mp (F_le_Ks h hf))
    fun y hy => ?_
  have hy' : g⁻¹ * y * g ∈ 𝐊⋆ := by
    have := (mem_normalizer_iff.mp (inv_mem hgK) y).mp hy
    rwa [inv_inv] at this
  have h1 := (mem_normalizer_iff.mp hgU _).mp (comm_mem_symm (Ks_comm_F_mod h i hbot hy' hf))
  rwa [show g * (f * (g⁻¹ * y * g) * f⁻¹ * (g⁻¹ * y * g)⁻¹) * g⁻¹ =
    g * f * g⁻¹ * y * (g * f * g⁻¹)⁻¹ * y⁻¹ by group] at h1

theorem card_commSub_Ks_le (h : FCHyp L K n φ t) (i : Axis)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) {x : G} (hx : x ∈ 𝐊⋆) (hxF : x ∉ 𝐅) :
    Nat.card (commSub 𝐇 𝐔[i] (H_le_normalizer_U h i) x ⊓ 𝐊⋆ : Subgroup G) ≤
      Nat.card K ^ 5 := by
  obtain ⟨f, hf, p, hp, rfl⟩ := exists_F_mul_P h hx
  have hpZ : p ∉ 𝐙 := fun hpZ => hxF (mul_mem hf (ZP_le_F h hpZ))
  set T := commSub 𝐇 𝐔[i] (H_le_normalizer_U h i) (f * p) ⊓ 𝐊⋆ with hT
  have hFT : 𝐅 ≤ T := le_inf (F_le_commSub h i hbot hx) (F_le_Ks h)
  have hTP : T ⊓ 𝐏 ≤ commSub 𝐏 𝐔[i] (P_le_normalizer_U h i) p := by
    intro y hy
    obtain ⟨⟨hyc, -⟩, hyP⟩ := hy
    have h1 : f * p ∈ commSub 𝐇 𝐔[i] (H_le_normalizer_U h i) y :=
      ⟨Ks_le_H h hx, comm_mem_symm hyc.2⟩
    have h2 : p ∈ commSub 𝐇 𝐔[i] (H_le_normalizer_U h i) y := by
      have := mul_mem (inv_mem (F_le_commSub h i hbot (P_le_Ks h hyP) hf)) h1
      rwa [inv_mul_cancel_left] at this
    exact ⟨hyP, comm_mem_symm h2.2⟩
  have hsup : 𝐅 ⊔ (T ⊓ 𝐏) = T := by
    refine le_antisymm (sup_le hFT inf_le_left) fun y hy => ?_
    obtain ⟨f', hf', p', hp', rfl⟩ := exists_F_mul_P h hy.2
    have hp'T : p' ∈ T := by simpa using mul_mem (inv_mem (hFT hf')) hy
    exact mul_mem (mem_sup_left hf') (mem_sup_right ⟨hp'T, hp'⟩)
  have hinf : 𝐅 ⊓ (T ⊓ 𝐏) = 𝐙 := by
    apply le_antisymm
    · intro y hy
      rw [← F_inf_P h]
      exact ⟨hy.1, hy.2.2⟩
    · exact le_inf (ZP_le_F h) (le_inf ((ZP_le_F h).trans hFT) Setup.ZP_le_PG)
  have hN : T ⊓ 𝐏 ≤ normalizer (𝐅 : Set G) :=
    inf_le_right.trans (P_le_H.trans (H_le_normalizer_F h))
  have h1 := card_sup_mul_card_inf 𝐅 (T ⊓ 𝐏) hN
  rw [hsup, hinf, FCHyp.card_ZP, card_F h] at h1
  have h2 := (card_le_of_le hTP).trans (card_commSub_P_le h i hp hpZ)
  have hq : 0 < Nat.card K ^ 2 := by have : 0 < Nat.card K := Nat.card_pos; positivity
  have h3 : Nat.card T * Nat.card K ^ 2 ≤ Nat.card K ^ 5 * Nat.card K ^ 2 := by
    rw [h1]
    calc Nat.card K ^ 4 * Nat.card (T ⊓ 𝐏 : Subgroup G) ≤ Nat.card K ^ 4 * Nat.card K ^ 3 :=
          Nat.mul_le_mul_left _ h2
      _ = Nat.card K ^ 5 * Nat.card K ^ 2 := by ring
  exact Nat.le_of_mul_le_mul_right h3 hq

theorem conj_R_mem_Ks (h : FCHyp L K n φ t) (i : Axis) {r : G} (hr : r ∈ 𝐑[i]) {y : G}
    (hy : y ∈ 𝐊⋆) : r * y * r⁻¹ ∈ 𝐊⋆ := by
  have hKR := Ks_normal_R h i
  exact mem_subgroupOf.mp (hKR.2.conj_mem ⟨y, hKR.1 hy⟩ (mem_subgroupOf.mpr hy) ⟨r, hr⟩)

theorem R_le_normalizer_L_swap (h : FCHyp L K n φ t) (i : Axis)
    (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥) (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) :
    𝐑[i] ≤ normalizer (𝐋[i.swap] : Set G) := by
  intro r hr
  refine mem_normalizer_of_conj_le fun x hx => ?_
  by_contra hxL
  set Y := 𝐋[i.swap].map (MulAut.conj r).toMonoidHom with hY
  have hYK : Y ≤ 𝐊⋆ := by
    rintro _ ⟨y, hy, rfl⟩
    exact conj_R_mem_Ks h i hr (L_le_Ks h _ hy)
  have hYc : ∀ x ∈ Y, ∀ y ∈ Y, x * y = y * x := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [show r * x * r⁻¹ * (r * y * r⁻¹) = r * (x * y) * r⁻¹ by group,
      L_swap_comm h i hbot hx hy]
    group
  have hYcard : Nat.card Y = Nat.card K ^ 5 := by
    rw [hY, card_map_of_injective (MulAut.conj r).injective, card_L h]
  have hYcm : ∀ x ∈ Y, ∀ y ∈ Y, x * y * x⁻¹ * y⁻¹ ∈ 𝐔[i] := fun x hx y hy => by
    rw [hYc x hx y hy, mul_inv_cancel_right, mul_inv_cancel]
    exact one_mem _
  have hFY : 𝐅 ≤ Y := by
    have h1 := card_le_of_comm_mod h i hbot hYK hYcm
    rw [hYcard] at h1
    have hq : 0 < Nat.card K := Nat.card_pos
    have h2 : Nat.card K ^ 4 ≤ Nat.card (Y ⊓ 𝐅 : Subgroup G) := by
      have : Nat.card K * Nat.card K ^ 4 ≤ Nat.card K * Nat.card (Y ⊓ 𝐅 : Subgroup G) := by
        calc Nat.card K * Nat.card K ^ 4 = Nat.card K ^ 5 := by ring
          _ ≤ _ := h1
      exact Nat.le_of_mul_le_mul_left this hq
    have h3 : Y ⊓ 𝐅 = 𝐅 := eq_of_le_of_card_ge inf_le_right (by rw [card_F h]; exact h2)
    rw [← h3]
    exact inf_le_left
  have hinf : Y ⊓ 𝐋[i.swap] ≤ 𝐅 := by
    intro y hy
    by_contra hyF
    have hyK : y ∈ 𝐊⋆ := hYK hy.1
    have hT := card_commSub_Ks_le h i hbot hyK hyF
    have hYT : Y ≤ commSub 𝐇 𝐔[i] (H_le_normalizer_U h i) y ⊓ 𝐊⋆ := fun z hz =>
      ⟨⟨Ks_le_H h (hYK hz), hYcm y hy.1 z hz⟩, hYK hz⟩
    have hLT : 𝐋[i.swap] ≤ commSub 𝐇 𝐔[i] (H_le_normalizer_U h i) y ⊓ 𝐊⋆ := fun z hz =>
      ⟨⟨Ks_le_H h (L_le_Ks h _ hz), by
        rw [L_swap_comm h i hbot hy.2 hz, mul_inv_cancel_right, mul_inv_cancel]
        exact one_mem _⟩, L_le_Ks h _ hz⟩
    have e1 := eq_of_le_of_card_ge hYT (hT.trans hYcard.ge)
    have e2 := eq_of_le_of_card_ge hLT (hT.trans (card_L h _).ge)
    apply hxL
    have hrx : (MulAut.conj r).toMonoidHom x ∈ Y := ⟨x, hx, rfl⟩
    rw [e1, ← e2] at hrx
    exact hrx
  have hLY : 𝐋[i.swap] ⊓ Y = 𝐅 :=
    le_antisymm (by rw [inf_comm 𝐋[i.swap] Y]; exact hinf) (le_inf (F_le_L _) hFY)
  have hsup : 𝐋[i.swap] ⊔ Y = 𝐊⋆ := by
    have hN : Y ≤ normalizer (𝐋[i.swap] : Set G) := fun y hy =>
      mem_normalizer_of_conj_le fun z hz => conj_H_mem_L h _ (Ks_le_H h (hYK hy)) hz
    have h1 := card_sup_mul_card_inf 𝐋[i.swap] Y hN
    rw [hLY, card_F h, card_L h, hYcard] at h1
    refine eq_of_le_of_card_ge (sup_le (L_le_Ks h _) hYK) ?_
    rw [card_Ks h]
    have hq : 0 < Nat.card K ^ 4 := by have : 0 < Nat.card K := Nat.card_pos; positivity
    have : Nat.card K ^ 6 * Nat.card K ^ 4 =
        Nat.card (𝐋[i.swap] ⊔ Y : Subgroup G) * Nat.card K ^ 4 := by rw [h1]; ring
    exact (Nat.eq_of_mul_eq_mul_right hq this).le
  have hcent : 𝐊⋆ ≤ centralizer (𝐅 : Set G) := by
    rw [← hsup]
    exact sup_le (fun y hy => mem_centralizer_iff.mpr fun f hf =>
      L_swap_comm h i hbot (F_le_L _ hf) hy)
      (fun y hy => mem_centralizer_iff.mpr fun f hf => hYc f (hFY hf) y hy)
  apply hne
  rw [commutator_eq_bot_iff_le_centralizer]
  intro a ha
  rw [mem_centralizer_iff]
  intro f hf
  exact mem_centralizer_iff.mp (hcent ((A_le_L i).trans (L_le_Ks h i) ha)) f hf.1

omit [Finite G] in
theorem sq_of_comm {x y z : G} (h1 : x * y = y * x) (h2 : x * z = z * x) (h3 : y * z = z * y) :
    x * y * z * (x * y * z) = x * x * (y * y) * (z * z) := by
  calc x * y * z * (x * y * z) = x * y * (z * x) * y * z := by group
    _ = x * y * (x * z) * y * z := by rw [← h2]
    _ = x * (y * x) * z * y * z := by group
    _ = x * (x * y) * z * y * z := by rw [← h1]
    _ = x * x * y * (z * y) * z := by group
    _ = x * x * y * (y * z) * z := by rw [← h3]
    _ = x * x * (y * y) * (z * z) := by group

theorem sq_L_swap (h : FCHyp L K n φ t) (i : Axis) (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥)
    {y : G} (hy : y ∈ 𝐋[i.swap]) :
    ∃ w ∈ 𝐖[i], ∃ w' ∈ 𝐖[i.swap], ∃ a ∈ 𝐀[i.swap], w * w' * a = y ∧
      y * y = w * w * (w' * w') := by
  obtain ⟨w, hw, w', hw', a, ha, rfl⟩ := exists_L_decomp h i i.swap hy
  have hwL : w ∈ 𝐋[i.swap] := F_le_L _ (W_le_F i hw)
  have hw'L : w' ∈ 𝐋[i.swap] := F_le_L _ (W_le_F _ hw')
  have haL : a ∈ 𝐋[i.swap] := A_le_L _ ha
  refine ⟨w, hw, w', hw', a, ha, rfl, ?_⟩
  rw [sq_of_comm (L_swap_comm h i hbot hwL hw'L) (L_swap_comm h i hbot hwL haL)
    (L_swap_comm h i hbot hw'L haL), A_mul_self h _ ha, mul_one]

theorem mem_U_of_sq_eq_one (h : FCHyp L K n φ t) (k : Axis) {lam : K}
    (hlam : ∀ w ∈ 𝐖[k], ∀ a : K, t⁻¹ * (w⁻¹ * t * w) = coordG φ k a →
      w * w = coordG φ k (lam * a)) (hlam0 : lam ≠ 0) {v : G} (hv : v ∈ 𝐖[k])
    (hvv : v * v = 1) : v ∈ 𝐔[k] := by
  obtain ⟨a, ha⟩ := exists_coordG_eq φ k (kappa_mem_U h k (mem_inf.mp (W_le_Fi h k hv)).2)
  have h1 := hlam v hv a ha.symm
  rw [hvv, ← coordG_zero φ k] at h1
  have h2 : a = 0 := (mul_eq_zero.mp (coordG_injective φ k h1).symm).resolve_left hlam0
  rw [h2, coordG_zero] at ha
  rw [← W_inf_C h k]
  exact mem_inf.mpr ⟨hv, kappa_eq_one_iff.mp ha.symm⟩

theorem sq_W_swap (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) {w : G} (hw : w ∈ 𝐖[i.swap]) : w * w = 1 := by
  obtain ⟨-, lamj, hlamj, -, -, hnej⟩ := square_map h i.swap
  obtain ⟨-, lami, hlami, -⟩ := square_map h i
  by_contra hw1
  have hlamj0 : lamj ≠ 0 := by
    rintro rfl
    obtain ⟨a, ha⟩ :=
      exists_coordG_eq φ i.swap (kappa_mem_U h i.swap (mem_inf.mp (W_le_Fi h i.swap hw)).2)
    exact hw1 (by rw [hlamj w hw a ha.symm, zero_mul, coordG_zero])
  have hRL := R_le_normalizer_L_swap h i hne hbot
  by_cases hlami0 : lami = 0
  · have hsqi : ∀ v ∈ 𝐖[i], v * v = 1 := fun v hv => by
      obtain ⟨a, ha⟩ := exists_coordG_eq φ i (kappa_mem_U h i (mem_inf.mp (W_le_Fi h i hv)).2)
      rw [hlami v hv a ha.symm, hlami0, zero_mul, coordG_zero]
    obtain ⟨hcl, -⟩ := hnej hlamj0
    have hUN : ∀ r ∈ 𝐑[i], ∀ u ∈ 𝐔[i.swap], r * u * r⁻¹ ∈ 𝐔[i.swap] := by
      intro r hr u hu
      rw [← hcl] at hu ⊢
      have hle : closure {x : G | ∃ y ∈ 𝐖[i.swap], x = y * y} ≤
          (closure {x : G | ∃ y ∈ 𝐖[i.swap], x = y * y}).comap (MulAut.conj r).toMonoidHom := by
        rw [closure_le]
        rintro _ ⟨y, hy, rfl⟩
        have hyL : r * y * r⁻¹ ∈ 𝐋[i.swap] :=
          (mem_normalizer_iff.mp (hRL hr) y).mp (F_le_L _ (W_le_F _ hy))
        obtain ⟨v, hv, v', hv', a, -, -, hsq⟩ := sq_L_swap h i hbot hyL
        show r * (y * y) * r⁻¹ ∈ Subgroup.closure _
        rw [show r * (y * y) * r⁻¹ = (r * y * r⁻¹) * (r * y * r⁻¹) by group, hsq, hsqi v hv,
          one_mul]
        exact subset_closure ⟨v', hv', rfl⟩
      exact hle hu
    have hUR : 𝐔[i.swap] ≤ 𝐑[i] :=
      (pull_mono φ (rootU_le_center _)).trans (Setup.ZP_le_PG.trans (le_sup_left.trans le_sup_left))
    have hn : ((𝐔[i.swap]).subgroupOf 𝐑[i]).Normal :=
      ⟨fun u hu r => mem_subgroupOf.mpr (hUN r r.2 u (mem_subgroupOf.mp hu))⟩
    have hne' : (𝐔[i.swap]).subgroupOf 𝐑[i] ≠ ⊥ := by
      intro hbot'
      have h1 : (⟨coordG φ i.swap 1, hUR (coordG_mem φ i.swap 1)⟩ : 𝐑[i]) ∈
          (𝐔[i.swap]).subgroupOf 𝐑[i] := mem_subgroupOf.mpr (coordG_mem φ i.swap 1)
      rw [hbot', mem_bot] at h1
      have h2 := congrArg Subtype.val h1
      rw [OneMemClass.coe_one, ← coordG_zero φ i.swap] at h2
      exact one_ne_zero (coordG_injective φ i.swap h2)
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hnil : Group.IsNilpotent 𝐑[i] := (R_isPGroup h i).isNilpotent
    have h1 := Group.IsNilpotent.inf_center_ne_bot_of_normal hne'
    obtain ⟨⟨u, hu⟩, hu1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp h1
    obtain ⟨-, hZR, -⟩ := centers_of_ne_bot h i hne
    have huZ : (u : G) ∈ 𝐔[i] := by
      rw [← hZR]
      exact ⟨u, (mem_inf.mp hu).2, rfl⟩
    have huj : (u : G) ∈ 𝐔[i.swap] := mem_subgroupOf.mp (mem_inf.mp hu).1
    have h2 : (u : G) ∈ 𝐔[i] ⊓ 𝐔[i.swap] := mem_inf.mpr ⟨huZ, huj⟩
    rw [U_inf_U_swap i, mem_bot] at h2
    exact hu1 (Subtype.ext (Subtype.ext h2))
  · have hinv : ∀ y ∈ 𝐋[i.swap], y * y = 1 → y ∈ 𝐀[i.swap] := by
      intro y hy hyy
      obtain ⟨v, hv, v', hv', a, ha, rfl, hsq⟩ := sq_L_swap h i hbot hy
      rw [hsq] at hyy
      have h1 : v * v ∈ 𝐔[i] := W_sq_mem_U h i hv
      have h2 : v' * v' ∈ 𝐔[i.swap] := W_sq_mem_U h _ hv'
      have h3 : v * v = (v' * v')⁻¹ := eq_inv_of_mul_eq_one_left hyy
      have h4 : v * v ∈ 𝐔[i] ⊓ 𝐔[i.swap] := mem_inf.mpr ⟨h1, h3 ▸ inv_mem h2⟩
      rw [U_inf_U_swap i, mem_bot] at h4
      have h5 : v' * v' = 1 := by rw [h4, one_mul] at hyy; exact hyy
      have hvU := mem_U_of_sq_eq_one h i hlami hlami0 hv h4
      have hv'U := mem_U_of_sq_eq_one h i.swap hlamj hlamj0 hv' h5
      have hUA : ∀ k, 𝐔[k] ≤ 𝐀[i.swap] := fun k =>
        pull_mono φ ((rootU_le_center k).trans (center_le_rootA _))
      exact mul_mem (mul_mem (hUA _ hvU) (hUA _ hv'U)) ha
    have hRA : 𝐑[i] ≤ normalizer (𝐀[i.swap] : Set G) := fun r hr =>
      mem_normalizer_of_conj_le fun a ha => by
        refine hinv _ ((mem_normalizer_iff.mp (hRL hr) a).mp (A_le_L _ ha)) ?_
        rw [show r * a * r⁻¹ * (r * a * r⁻¹) = r * (a * a) * r⁻¹ by group, A_mul_self h _ ha,
          mul_one, mul_inv_cancel]
    have h1 := R_inf_normalizer_A h i
    rw [inf_of_le_left hRA] at h1
    have h2 := card_R h i
    rw [h1, h.H_facts.2.2] at h2
    have hq : Nat.card K ^ 6 < Nat.card K ^ 7 :=
      Nat.pow_lt_pow_right (by have := h.four_le_card; omega) (by norm_num)
    omega

theorem F_sq_mem_U (h : FCHyp L K n φ t) (i : Axis) (hj : ∀ w ∈ 𝐖[i.swap], w * w = 1)
    {f : G} (hf : f ∈ 𝐅) : f * f ∈ 𝐔[i] := by
  obtain ⟨w, hw, w', hw', rfl⟩ := exists_W_mul h i hf
  have hc : w * w' = w' * w := F_comm h (W_le_F _ hw) (W_le_F _ hw')
  rw [show w * w' * (w * w') = w * (w' * w) * w' by group, ← hc,
    show w * (w * w') * w' = w * w * (w' * w') by group, hj w' hw', mul_one]
  exact W_sq_mem_U h i hw

theorem sq_mem_U_iff_L (h : FCHyp L K n φ t) (i : Axis) (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥)
    (hj : ∀ w ∈ 𝐖[i.swap], w * w = 1) {x : G} (hx : x ∈ 𝐊⋆) :
    x * x ∈ 𝐔[i] ↔ x ∈ 𝐋[Axis.one] ∨ x ∈ 𝐋[Axis.two] := by
  obtain ⟨f, hf, p, hp, rfl⟩ := exists_F_mul_P h hx
  have hc := P_comm_F_mod h i hbot hp hf
  have hcf : (p * f * p⁻¹ * f⁻¹) * f = f * (p * f * p⁻¹ * f⁻¹) :=
    (comm_U h i (F_le_H h hf) hc).symm
  have e : f * p * (f * p) = (p * f * p⁻¹ * f⁻¹) * (f * f) * (p * p) := by
    calc f * p * (f * p) = f * ((p * f * p⁻¹ * f⁻¹) * f * p) * p := by group
      _ = (f * (p * f * p⁻¹ * f⁻¹)) * f * p * p := by group
      _ = ((p * f * p⁻¹ * f⁻¹) * f) * f * p * p := by rw [hcf]
      _ = (p * f * p⁻¹ * f⁻¹) * (f * f) * (p * p) := by group
  have hcU : (p * f * p⁻¹ * f⁻¹) * (f * f) ∈ 𝐔[i] := mul_mem hc (F_sq_mem_U h i hj hf)
  have hiff : f * p * (f * p) ∈ 𝐔[i] ↔ p * p ∈ 𝐔[i] := by
    rw [e]
    constructor
    · intro h1
      have := mul_mem (inv_mem hcU) h1
      rwa [← mul_assoc, inv_mul_cancel, one_mul] at this
    · exact mul_mem hcU
  have hk : ∀ k, p ∈ 𝐀[k] ↔ f * p ∈ 𝐋[k] := by
    intro k
    refine ⟨fun hpA => mul_mem (F_le_L k hf) (A_le_L k hpA), fun hfp => ?_⟩
    rw [← SetLike.mem_coe, ← L_mul h] at hfp
    obtain ⟨f', hf', a, ha, hfa⟩ := hfp
    have hfa : f' * a = f * p := hfa
    have hz : p * a⁻¹ ∈ 𝐙 := by
      rw [← F_inf_P h]
      have e1 : p * a⁻¹ = f⁻¹ * f' := by
        rw [show f⁻¹ * f' = f⁻¹ * (f' * a) * a⁻¹ by group, hfa]
        group
      refine mem_inf.mpr ⟨by rw [e1]; exact mul_mem (inv_mem hf) hf', ?_⟩
      exact mul_mem hp (inv_mem (pull_mono φ (rootA_le_antiUnipotent k) ha))
    rw [show p = p * a⁻¹ * a by group]
    exact mul_mem (pull_mono φ (center_le_rootA k) hz) ha
  rw [hiff, sq_mem_U_iff i hp, hk, hk]

omit [Finite G] [Finite K] in
theorem L_noncomm (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥) :
    ¬ ∀ x ∈ 𝐋[i], ∀ y ∈ 𝐋[i], x * y = y * x := by
  intro hc
  apply hne
  rw [commutator_eq_bot_iff_le_centralizer]
  intro a ha
  rw [mem_centralizer_iff]
  intro f hf
  exact hc f (F_le_L i hf.1) a (A_le_L i ha)

theorem L_comm_iff (h : FCHyp L K n φ t) (i : Axis) (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥)
    (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) (m : Axis) :
    (∀ x ∈ 𝐋[m], ∀ y ∈ 𝐋[m], x * y = y * x) ↔ m = i.swap := by
  rcases eq_or_eq_swap i m with rfl | rfl
  · exact iff_of_false (L_noncomm m hne) (swap_ne m).symm
  · exact iff_of_true (fun x hx y hy => L_swap_comm h i hbot hx hy) rfl

theorem Nhat_le_normalizer_L (h : FCHyp L K n φ t) (i : Axis)
    (hne : ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ ≠ ⊥) (hbot : ⁅𝐀[i.swap], 𝐅 ⊓ 𝐃[i]⁆ = ⊥) (k : Axis) :
    𝐍ₕ[i] ≤ normalizer (𝐋[k] : Set G) := by
  have hj := fun w hw => sq_W_swap h i hne hbot (w := w) hw
  intro g hg
  have hgU := (mem_inf.mp hg).2
  have hgK := Nhat_le_normalizer_Ks h i hbot hg
  set Y := 𝐋[k].map (MulAut.conj g).toMonoidHom with hY
  have hYK : Y ≤ 𝐊⋆ := by
    rintro _ ⟨x, hx, rfl⟩
    exact (mem_normalizer_iff.mp hgK x).mp (L_le_Ks h k hx)
  have hLsq : ∀ x ∈ 𝐋[k], x * x ∈ 𝐔[i] := fun x hx =>
    (sq_mem_U_iff_L h i hbot hj (L_le_Ks h k hx)).mpr (by
      cases k
      · exact Or.inl hx
      · exact Or.inr hx)
  have hYsq : ∀ y ∈ Y, y * y ∈ 𝐔[i] := by
    rintro _ ⟨x, hx, rfl⟩
    have := (mem_normalizer_iff.mp hgU _).mp (hLsq x hx)
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rwa [show g * x * g⁻¹ * (g * x * g⁻¹) = g * (x * x) * g⁻¹ by group]
  have hYL : Y ≤ 𝐋[Axis.one] ∨ Y ≤ 𝐋[Axis.two] := SubgroupClass.subset_union.mp fun y hy =>
    (sq_mem_U_iff_L h i hbot hj (hYK hy)).mp (hYsq y hy)
  have hYcard : Nat.card Y = Nat.card K ^ 5 := by
    rw [hY, card_map_of_injective (MulAut.conj g).injective, card_L h]
  obtain ⟨m, hYm⟩ : ∃ m, Y = 𝐋[m] := by
    rcases hYL with hYL | hYL
    · exact ⟨_, eq_of_le_of_card_ge hYL (by rw [card_L h, hYcard])⟩
    · exact ⟨_, eq_of_le_of_card_ge hYL (by rw [card_L h, hYcard])⟩
  have hab : (∀ x ∈ Y, ∀ y ∈ Y, x * y = y * x) ↔ (∀ x ∈ 𝐋[k], ∀ y ∈ 𝐋[k], x * y = y * x) := by
    constructor
    · intro hc x hx y hy
      have := hc _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at this
      have e : g * (x * y) * g⁻¹ = g * (y * x) * g⁻¹ := by
        rw [show g * (x * y) * g⁻¹ = g * x * g⁻¹ * (g * y * g⁻¹) by group, this]
        group
      simpa using e
    · rintro hc _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      rw [show g * x * g⁻¹ * (g * y * g⁻¹) = g * (x * y) * g⁻¹ by group, hc x hx y hy]
      group
  have hmk : m = k := by
    refine eq_of_swap_iff (i := i) ?_
    rw [← L_comm_iff h i hne hbot m, ← L_comm_iff h i hne hbot k, ← hYm]
    exact hab
  refine mem_normalizer_of_conj_le fun x hx => ?_
  have : (MulAut.conj g).toMonoidHom x ∈ Y := ⟨x, hx, rfl⟩
  rw [hYm, hmk] at this
  exact this

end Setting

end SingleComm

end CFSG.LocalAnalysis.SymplecticFourStandard
