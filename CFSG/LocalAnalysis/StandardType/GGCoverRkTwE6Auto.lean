module

public import CFSG.LocalAnalysis.StandardType.GGWPlusTwE6
public import CFSG.LocalAnalysis.StandardType.GGWPlusTwE6Quot
public import CFSG.LocalAnalysis.StandardType.GGWPlusE6Auto
public import CFSG.LocalAnalysis.StandardType.GGE6ThreeModelHoldsT
public import CFSG.LocalAnalysis.StandardType.GGRawAutRestTwE6
public import CFSG.LocalAnalysis.StandardType.GGCoverRkTwE6Frame

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB
open CFSG.StandardType.E6ThreeModel TableBExc.E6Three
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

private lemma conj_apply_apply {R : Type*} [Group R] (f : MulAut R) (r : R) :
    MulAut.conj (f r) = f * MulAut.conj r * f⁻¹ := by
  ext x
  simp only [MulAut.conj_apply, MulAut.mul_apply, map_mul, map_inv, MulAut.inv_apply,
    MulEquiv.apply_symm_apply]

private def conjHom {G : Type*} [Group G] (γ : G) : G →* G where
  toFun z := γ * z * γ⁻¹
  map_one' := by simp
  map_mul' := by intro x y; group

private lemma conjHom_injective {G : Type*} [Group G] (γ : G) :
    Function.Injective (conjHom γ) := by
  intro x y h
  simpa [conjHom] using h

private def conjSub {G : Type*} [Group G] (γ : G) (A : Subgroup G) : Subgroup G :=
  A.map (conjHom γ)

private lemma mem_conjSub {G : Type*} [Group G] (γ : G) (A : Subgroup G) {z : G} :
    z ∈ conjSub γ A ↔ ∃ a ∈ A, γ * a * γ⁻¹ = z := by
  change z ∈ A.map (conjHom γ) ↔ _
  rw [Subgroup.mem_map]
  simp only [conjHom, MonoidHom.coe_mk, OneHom.coe_mk]

private lemma card_conjSub {G : Type*} [Group G] (γ : G) (A : Subgroup G) :
    Nat.card (conjSub γ A) = Nat.card A :=
  Subgroup.card_map_of_injective (conjHom_injective γ)

private lemma mem_ad_image_univ {R : Type} [Group R] (D : FrameData R) {z : MulAut R} :
    z ∈ D.ad '' (Set.univ : Set (Fin Tag.E6.rank → ZMod 3)) ↔ z ∈ D.diag.range := by
  rw [Set.mem_image]
  constructor
  · rintro ⟨v, -, hv⟩
    exact ⟨Multiplicative.ofAdd v, hv⟩
  · rintro ⟨w, hw⟩
    exact ⟨Multiplicative.toAdd w, Set.mem_univ _, by rw [← hw]; rfl⟩

private lemma card_ad_range {R : Type} [Group R] (D : FrameData R) (hD : D.Good) :
    Nat.card D.diag.range = 3 ^ 6 := by
  rw [← Subgroup.map_top D.diag, Subgroup.card_map_of_injective hD.faithful,
    Subgroup.card_top, Nat.card_congr Multiplicative.toAdd, TableBExc.E6Three.card_top]

private lemma ad_injective {R : Type} [Group R] (D : FrameData R) (hD : D.Good) :
    Function.Injective D.ad := by
  intro x y h
  have h' : Multiplicative.ofAdd x = Multiplicative.ofAdd y := hD.faithful h
  exact Multiplicative.ofAdd.injective h'

private lemma zmod3_pow_three_pow (c : ZMod 3) (k : ℕ) : c ^ (3 ^ k) = c := by
  have h := FiniteField.pow_card_pow (K := ZMod 3) k c
  simpa [ZMod.card] using h

private lemma zmod3_sq_eq_one_of_ne_zero {c : ZMod 3} (hc : c ≠ 0) : c * c = 1 := by
  have h := FiniteField.pow_card_sub_one_eq_one (K := ZMod 3) c hc
  simpa [ZMod.card, pow_two] using h

private lemma smul_adAct_iterate (c : ZMod 3) (u : WeylGroup .E6) (m : ℕ) :
    (fun x : Fin Tag.E6.rank → ZMod 3 => c • adAct .E6 3 u x)^[m] =
      fun x => c ^ m • adAct .E6 3 (u ^ m) x := by
  induction m with
  | zero =>
    funext x
    simp only [Function.iterate_zero, id_eq, pow_zero, one_smul]
    exact (adAct_one x).symm
  | succ m ih =>
    funext x
    rw [Function.iterate_succ_apply', ih]
    show c • adAct .E6 3 u (c ^ m • adAct .E6 3 (u ^ m) x) =
      c ^ (m + 1) • adAct .E6 3 (u ^ (m + 1)) x
    rw [adAct_smul, ← adAct_mul, smul_smul, ← pow_succ', ← pow_succ']

private theorem action_of_pElt
    {K : Type} [Field K] [Finite K] (n : ℕ)
    (D : FrameData (TwE6Delta.RecipeR K n)) (hD : D.Good)
    {S : Set (Fin Tag.E6.rank → ZMod 3)}
    (hS : S = Set.univ ∨ S = (NoOffRest.hypE6 : Set (Fin Tag.E6.rank → ZMod 3)))
    {a' : MulAut (TwE6Delta.RecipeR K n)} {k : ℕ} (hk : a' ^ 3 ^ k = 1)
    {c : ZMod 3} (hc : c ≠ 0) {u : WeylGroup .E6}
    (ha : ∀ x ∈ S, a' * D.ad x * a'⁻¹ = D.ad (c • adAct .E6 3 u x))
    (hstab : ∀ x ∈ S, c • adAct .E6 3 u x ∈ S) :
    ∃ u' : WeylGroup .E6,
      ∀ x ∈ S, a' * D.ad x * a'⁻¹ = D.ad (adAct .E6 3 u' x) := by
  classical
  let φ : (Fin Tag.E6.rank → ZMod 3) → (Fin Tag.E6.rank → ZMod 3) :=
    fun x => c • adAct .E6 3 u x
  have hφstab : ∀ x ∈ S, φ x ∈ S := hstab
  have hφa : ∀ x ∈ S, a' * D.ad x * a'⁻¹ = D.ad (φ x) := ha
  have hiter : ∀ j : ℕ, ∀ x ∈ S,
      φ^[j] x ∈ S ∧ a' ^ j * D.ad x * (a' ^ j)⁻¹ = D.ad (φ^[j] x) := by
    intro j
    induction j with
    | zero =>
      intro x hx
      exact ⟨by simpa using hx, by simp⟩
    | succ j ih =>
      intro x hx
      obtain ⟨hmemj, hrelj⟩ := ih x hx
      obtain ⟨hmemj', hrelj'⟩ := ih (φ^[j] x) hmemj
      refine ⟨?_, ?_⟩
      · rw [Function.iterate_succ_apply']; exact hφstab (φ^[j] x) hmemj
      · calc a' ^ (j + 1) * D.ad x * (a' ^ (j + 1))⁻¹
            = (a' ^ j * a') * D.ad x * (a' ^ j * a')⁻¹ := by rw [pow_succ]
          _ = a' * (a' ^ j * D.ad x * (a' ^ j)⁻¹) * a'⁻¹ := by group
          _ = a' * D.ad (φ^[j] x) * a'⁻¹ := by rw [hrelj]
          _ = D.ad (φ (φ^[j] x)) := hφa (φ^[j] x) hmemj
          _ = D.ad (φ^[j + 1] x) := by rw [Function.iterate_succ_apply']
  have hfix : ∀ x ∈ S, φ^[3 ^ k] x = x := by
    intro x hx
    obtain ⟨-, hrel⟩ := hiter (3 ^ k) x hx
    rw [hk, one_mul, inv_one, mul_one] at hrel
    exact (ad_injective D hD hrel).symm
  have hiter_formula : φ^[3 ^ k] =
      fun x => c ^ (3 ^ k) • adAct .E6 3 (u ^ (3 ^ k)) x :=
    smul_adAct_iterate c u (3 ^ k)
  have hpow : c ^ (3 ^ k) = c := zmod3_pow_three_pow c k
  have hcc : c * c = 1 := zmod3_sq_eq_one_of_ne_zero hc
  have hadAct : ∀ x ∈ S, adAct .E6 3 (u ^ (3 ^ k)) x = c • x := by
    intro x hx
    have h1 : c ^ (3 ^ k) • adAct .E6 3 (u ^ (3 ^ k)) x = x := by
      have h := hfix x hx
      rw [hiter_formula] at h
      exact h
    rw [hpow] at h1
    have h2 := congrArg (fun y => c • y) h1
    simpa [smul_smul, hcc] using h2
  refine ⟨u ^ (3 ^ k) * u, ?_⟩
  intro x hx
  have key : φ x = adAct .E6 3 (u ^ (3 ^ k) * u) x := by
    have hmem := hφstab x hx
    have h1 : adAct .E6 3 (u ^ (3 ^ k)) (φ x) = c • φ x := hadAct (φ x) hmem
    have h2 : adAct .E6 3 (u ^ (3 ^ k)) (φ x) =
        c • adAct .E6 3 (u ^ (3 ^ k) * u) x := by
      show adAct .E6 3 (u ^ (3 ^ k)) (c • adAct .E6 3 u x) =
        c • adAct .E6 3 (u ^ (3 ^ k) * u) x
      rw [adAct_smul, ← adAct_mul]
    have h3 : c • φ x = c • adAct .E6 3 (u ^ (3 ^ k) * u) x := by rw [← h1, h2]
    have h4 := congrArg (fun y => c • y) h3
    simpa [smul_smul, hcc] using h4
  rw [hφa x hx, key]

private theorem exists_inner_realizing
    {K : Type} [Field K] [Finite K] (n : ℕ)
    (D : FrameData (TwE6Delta.RecipeR K n)) (hD : D.Good)
    {S : Set (Fin Tag.E6.rank → ZMod 3)}
    (hS : S = Set.univ ∨ S = (NoOffRest.hypE6 : Set (Fin Tag.E6.rank → ZMod 3)))
    (u' : WeylGroup .E6) :
    ∃ ρ' : TwE6Delta.RecipeR K n,
      ∀ x ∈ S, MulAut.conj ρ' * D.ad x * (MulAut.conj ρ')⁻¹ =
        D.ad (adAct .E6 3 u' x) := by
  classical
  refine weyl_induction (fun u => ∃ ρ' : TwE6Delta.RecipeR K n,
      ∀ x ∈ S, MulAut.conj ρ' * D.ad x * (MulAut.conj ρ')⁻¹ =
        D.ad (adAct .E6 3 u x)) ?_ ?_ u'
  · exact ⟨1, by intro x hx; simp [adAct_one]⟩
  · intro i u ⟨ρ', hρ'⟩
    refine ⟨D.nb i * ρ', ?_⟩
    intro x hx
    calc MulAut.conj (D.nb i * ρ') * D.ad x * (MulAut.conj (D.nb i * ρ'))⁻¹
        = MulAut.conj (D.nb i) *
            (MulAut.conj ρ' * D.ad x * (MulAut.conj ρ')⁻¹) *
            (MulAut.conj (D.nb i))⁻¹ := by rw [map_mul]; group
      _ = MulAut.conj (D.nb i) * D.ad (adAct .E6 3 u x) * (MulAut.conj (D.nb i))⁻¹ := by
            rw [hρ' x hx]
      _ = D.ad (adRefl .E6 3 i (adAct .E6 3 u x)) := hD.weyl.2.2.1 i (adAct .E6 3 u x)
      _ = D.ad (adAct .E6 3 (simple .E6 i * u) x) := by rw [adAct_mul, adAct_simple]

theorem exists_rho_commute_of_normalizes_twE6
    {K : Type} [Field K] [Finite K] (n : ℕ) (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2)
    (h3 : 3 ∣ 2 ^ n + 1) {A : Subgroup (MulAut (TwE6Delta.RecipeR K n))} (hA : IsElemAbelian 3 A)
    (hI : (A : Set (MulAut (TwE6Delta.RecipeR K n))) ⊆ TwE6Delta.RecipeI K n) (hr : Nat.card A = 3 ^ 6) {a : MulAut (TwE6Delta.RecipeR K n)} {k : ℕ} (hk : a ^ 3 ^ k = 1)
    (hN : a ∈ Subgroup.normalizer (A : Set (MulAut (TwE6Delta.RecipeR K n)))) :
    ∃ ρ : TwE6Delta.RecipeR K n, ∀ x ∈ A, Commute ((MulAut.conj ρ)⁻¹ * a) x := by
  classical
  obtain ⟨D, -, hDgood, hDH, -, -, -, -, -, -, -⟩ := exists_langFrame_recipeR n hn hK h3
  haveI : Finite (TwE6Delta.RecipeR K n) := TwE6Delta.finite_recipeR hK
  have hAH : A ≤ D.H := fun x hx => by
    change x ∈ (D.H : Set (MulAut (TwE6Delta.RecipeR K n)))
    rw [hDH]
    exact hI hx
  obtain ⟨γ, -, hγconj⟩ := hDgood.shape A hAH hA (by rw [hr]; norm_num)
  have hAleV : conjSub γ A ≤ D.diag.range := fun z hz => by
    obtain ⟨a, ha, rfl⟩ := (mem_conjSub γ A).mp hz
    exact hγconj a ha
  have hcase : conjSub γ A = D.diag.range := by
    refine Subgroup.eq_of_le_of_card_ge hAleV ?_
    rw [card_ad_range D hDgood, card_conjSub, hr]
  have hiff : ∀ z : MulAut (TwE6Delta.RecipeR K n),
      z ∈ conjSub γ A ↔ z ∈ D.ad '' (Set.univ : Set (Fin Tag.E6.rank → ZMod 3)) := by
    intro z
    rw [hcase]
    exact (mem_ad_image_univ D).symm
  let a' : MulAut (TwE6Delta.RecipeR K n) := γ * a * γ⁻¹
  have ha'pow : a' ^ 3 ^ k = 1 := by
    have hconjpow : ∀ m : ℕ, (γ * a * γ⁻¹) ^ m = γ * a ^ m * γ⁻¹ := by
      intro m
      induction m with
      | zero => simp
      | succ m ih => rw [pow_succ, ih, pow_succ]; group
    show a' ^ (3 ^ k) = 1
    rw [show a' = γ * a * γ⁻¹ from rfl, hconjpow, hk]
    group
  have hy : ∀ x ∈ (Set.univ : Set (Fin Tag.E6.rank → ZMod 3)),
      ∃ y ∈ (Set.univ : Set (Fin Tag.E6.rank → ZMod 3)),
        a' * D.ad x * a'⁻¹ = D.ad y := by
    intro x hx
    have hz : D.ad x ∈ conjSub γ A := (hiff (D.ad x)).mpr ⟨x, hx, rfl⟩
    obtain ⟨xA, hxA, hxAeq⟩ := (mem_conjSub γ A).mp hz
    have hmem : a * xA * a⁻¹ ∈ A :=
      (Subgroup.mem_set_normalizer_iff.mp hN xA).mp hxA
    have hz2 : a' * D.ad x * a'⁻¹ ∈ conjSub γ A := by
      rw [← hxAeq]
      refine (mem_conjSub γ A).mpr ⟨a * xA * a⁻¹, hmem, ?_⟩
      show γ * (a * xA * a⁻¹) * γ⁻¹ =
        (γ * a * γ⁻¹) * (γ * xA * γ⁻¹) * (γ * a * γ⁻¹)⁻¹
      group
    obtain ⟨y, -, hyeq⟩ := (hiff (a' * D.ad x * a'⁻¹)).mp hz2
    exact ⟨y, Set.mem_univ _, hyeq.symm⟩
  obtain ⟨c, u, hc, haut⟩ := hDgood.aut a' Set.univ (Or.inl rfl) hy
  have hstab : ∀ x ∈ (Set.univ : Set (Fin Tag.E6.rank → ZMod 3)),
      c • adAct .E6 3 u x ∈ (Set.univ : Set (Fin Tag.E6.rank → ZMod 3)) :=
    fun x _ => Set.mem_univ _
  obtain ⟨u', hu'⟩ := action_of_pElt n D hDgood (Or.inl rfl) ha'pow hc haut hstab
  obtain ⟨ρ', hρ'⟩ := exists_inner_realizing n D hDgood (Or.inl rfl) u'
  let ρg : TwE6Delta.RecipeR K n := (γ⁻¹ : MulAut (TwE6Delta.RecipeR K n)) ρ'
  have hρg : MulAut.conj ρg = γ⁻¹ * MulAut.conj ρ' * γ := by
    show MulAut.conj ((γ⁻¹ : MulAut (TwE6Delta.RecipeR K n)) ρ') = _
    rw [conj_apply_apply (γ⁻¹) ρ', inv_inv]
  refine ⟨ρg, ?_⟩
  intro x hx
  have hz : γ * x * γ⁻¹ ∈ conjSub γ A := (mem_conjSub γ A).mpr ⟨x, hx, rfl⟩
  obtain ⟨y, -, hyeq⟩ := (hiff (γ * x * γ⁻¹)).mp hz
  have hmid : MulAut.conj ρ' * (γ * x * γ⁻¹) * (MulAut.conj ρ')⁻¹ =
      γ * (a * x * a⁻¹) * γ⁻¹ := by
    have h1 : MulAut.conj ρ' * (γ * x * γ⁻¹) * (MulAut.conj ρ')⁻¹ =
        D.ad (adAct .E6 3 u' y) := by rw [← hyeq]; exact hρ' y (Set.mem_univ y)
    have h2 : a' * (γ * x * γ⁻¹) * a'⁻¹ = D.ad (adAct .E6 3 u' y) := by
      rw [← hyeq]; exact hu' y (Set.mem_univ y)
    rw [h1, ← h2]
    show (γ * a * γ⁻¹) * (γ * x * γ⁻¹) * (γ * a * γ⁻¹)⁻¹ = γ * (a * x * a⁻¹) * γ⁻¹
    group
  have hconj : MulAut.conj ρg * x * (MulAut.conj ρg)⁻¹ = a * x * a⁻¹ := by
    rw [hρg]
    calc (γ⁻¹ * MulAut.conj ρ' * γ) * x * (γ⁻¹ * MulAut.conj ρ' * γ)⁻¹
        = γ⁻¹ * (MulAut.conj ρ' * (γ * x * γ⁻¹) * (MulAut.conj ρ')⁻¹) * γ := by group
      _ = γ⁻¹ * (γ * (a * x * a⁻¹) * γ⁻¹) * γ := by rw [hmid]
      _ = a * x * a⁻¹ := by group
  show Commute ((MulAut.conj ρg)⁻¹ * a) x
  change (MulAut.conj ρg)⁻¹ * a * x = x * ((MulAut.conj ρg)⁻¹ * a)
  calc (MulAut.conj ρg)⁻¹ * a * x
      = (MulAut.conj ρg)⁻¹ * (a * x * a⁻¹) * a := by group
    _ = (MulAut.conj ρg)⁻¹ * (MulAut.conj ρg * x * (MulAut.conj ρg)⁻¹) * a := by rw [hconj]
    _ = x * ((MulAut.conj ρg)⁻¹ * a) := by group

end CFSG.StandardType
