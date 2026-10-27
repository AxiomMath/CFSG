module

public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentySpCoord
public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerOrth
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyOrthTorusBasic
public import CFSG.LocalAnalysis.StandardType.GGTBJCoordRefl

public section

namespace CFSG.StandardType

open CFSG Multiplicative SpCoord NbrOrth

private theorem exists_mem_of_card_centralizer_le {p r : ℕ} (hp : p.Prime) {G : Type} [Group G]
    (τ : (Fin r → Multiplicative (ZMod p)) →* G) (f₀ : Fin r → Multiplicative (ZMod p))
    (J : Subgroup G) (P : Fin r → Prop)
    (hcent : ∀ f : Fin r → Multiplicative (ZMod p),
      (∃ m : ZMod p, ∀ i, P i → toAdd (f i) = m * toAdd (f₀ i)) →
        ∀ j ∈ J, τ f * j = j * τ f)
    (hcount : p ^ 2 * Nat.card {f : Fin r → Multiplicative (ZMod p) //
      ∀ j ∈ J, τ f * j = j * τ f} ≤ p ^ r) :
    ∃ i, P i := by
  classical
  haveI : NeZero p := ⟨hp.ne_zero⟩
  let C : Set (Fin r → Multiplicative (ZMod p)) := {f | ∀ j ∈ J, τ f * j = j * τ f}
  have hcount' : p ^ 2 * Nat.card {f // f ∈ C} ≤ p ^ r := hcount
  by_contra hPempty
  have hPfalse : ∀ i, ¬P i := fun i hi => hPempty ⟨i, hi⟩
  have huniv : ∀ f : Fin r → Multiplicative (ZMod p), f ∈ C := by
    intro f
    exact hcent f ⟨0, fun i hi => absurd hi (hPfalse i)⟩
  have hle1 : Nat.card (Fin r → Multiplicative (ZMod p)) ≤ Nat.card {f // f ∈ C} :=
    Nat.card_le_card_of_injective (fun f => ⟨f, huniv f⟩)
      (fun a b hab => Subtype.ext_iff.mp hab)
  have hle2 : Nat.card {f // f ∈ C} ≤ Nat.card (Fin r → Multiplicative (ZMod p)) :=
    Nat.card_le_card_of_injective Subtype.val Subtype.val_injective
  have hcardC : Nat.card {f // f ∈ C} = p ^ r := by
    rw [← ggTBJSpC_card_coord p r]
    exact le_antisymm hle2 hle1
  rw [hcardC] at hcount'
  have hpm_pos : 0 < p ^ r := pow_pos hp.pos r
  have hle : p ^ 2 ≤ 1 := Nat.le_of_mul_le_mul_right (by
    calc p ^ 2 * p ^ r ≤ p ^ r := hcount'
      _ = 1 * p ^ r := by ring) hpm_pos
  have hp2' : 4 ≤ p ^ 2 := by nlinarith [hp.two_le]
  omega

private theorem le_card_of_pow_le {p r n : ℕ} (hp : p.Prime) {I : Finset (Fin r)}
    (hI : I.card ≤ r) (h : p ^ (n + (r - I.card)) ≤ p ^ r) : n ≤ I.card := by
  have h' := (Nat.pow_le_pow_iff_right hp.one_lt).mp h
  omega

private theorem two_le_card_class_of_centralizer {p r : ℕ} (hp : p.Prime) {G : Type} [Group G]
    (τ : (Fin r → Multiplicative (ZMod p)) →* G) (f₀ : Fin r → Multiplicative (ZMod p))
    (J : Subgroup G) (P : Fin r → Prop)
    (hcent : ∀ f : Fin r → Multiplicative (ZMod p),
      (∃ m : ZMod p, ∀ i, P i → toAdd (f i) = m * toAdd (f₀ i)) →
        ∀ j ∈ J, τ f * j = j * τ f)
    (hcount : p ^ 2 * Nat.card {f : Fin r → Multiplicative (ZMod p) //
      ∀ j ∈ J, τ f * j = j * τ f} ≤ p ^ r) :
    2 ≤ Nat.card {i : Fin r // P i} := by
  classical
  haveI : NeZero p := ⟨hp.ne_zero⟩
  let C : Set (Fin r → Multiplicative (ZMod p)) := {f | ∀ j ∈ J, τ f * j = j * τ f}
  let I : Finset (Fin r) := Finset.univ.filter P
  have hcardI : Nat.card {i : Fin r // P i} = I.card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hcount_le : ∀ f : Fin r → Multiplicative (ZMod p),
      (∀ i, P i → f i = 1) → f ∈ C := by
    intro f hf
    exact hcent f ⟨0, fun i hi => by rw [hf i hi, zero_mul, toAdd_one]⟩
  let e : ({i // i ∉ I} → Multiplicative (ZMod p)) → {f // f ∈ C} :=
    fun g => ⟨fun i => if h : i ∈ I then 1 else g ⟨i, h⟩, hcount_le _ (by
      intro i hi
      have hmem : i ∈ I := Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩
      simp [hmem])⟩
  have he : Function.Injective e := by
    intro g g' hgg
    funext x
    simpa [e, x.2] using congrFun (congrArg Subtype.val hgg) x.1
  have hcard2 : Nat.card ({i // i ∉ I} → Multiplicative (ZMod p)) = p ^ (r - I.card) := by
    rw [Nat.card_fun, ggTBJSpC_card_subtype_notMem,
      Nat.card_congr (Multiplicative.toAdd : Multiplicative (ZMod p) ≃ ZMod p), Nat.card_zmod]
  have hcard1 : p ^ (r - I.card) ≤ Nat.card {f // f ∈ C} := by
    rw [← hcard2]
    exact Nat.card_le_card_of_injective e he
  have hle : p ^ (2 + (r - I.card)) ≤ p ^ r := by
    rw [pow_add]
    exact (Nat.mul_le_mul_left _ hcard1).trans hcount
  rw [hcardI]
  exact le_card_of_pow_le hp (by simpa using Finset.card_le_univ I) hle

private theorem exists_coord_ne_zero_of_ne_zero {p r : ℕ} (hp : p.Prime) {G : Type} [Group G]
    (τ : (Fin r → Multiplicative (ZMod p)) →* G) (f₀ : Fin r → Multiplicative (ZMod p))
    (J : Subgroup G) (a : ZMod p) (P : Fin r → Prop) (ha : a ≠ 0)
    (hP : ∀ i, P i → toAdd (f₀ i) = a ∨ toAdd (f₀ i) = -a)
    (hcent : ∀ f : Fin r → Multiplicative (ZMod p),
      (∃ m : ZMod p, ∀ i, P i → toAdd (f i) = m * toAdd (f₀ i)) →
        ∀ j ∈ J, τ f * j = j * τ f)
    (hcount : p ^ 2 * Nat.card {f : Fin r → Multiplicative (ZMod p) //
      ∀ j ∈ J, τ f * j = j * τ f} ≤ p ^ r) :
    ∃ i, P i ∧ toAdd (f₀ i) ≠ 0 := by
  obtain ⟨i₀, hi₀P⟩ := exists_mem_of_card_centralizer_le hp τ f₀ J P hcent hcount
  refine ⟨i₀, hi₀P, ?_⟩
  rcases hP i₀ hi₀P with h | h
  · rwa [h]
  · rw [h]
    exact neg_ne_zero.mpr ha

private theorem three_le_card_class_of_ne_zero {p r : ℕ} (hp : p.Prime) {G : Type} [Group G]
    (τ : (Fin r → Multiplicative (ZMod p)) →* G) (f₀ : Fin r → Multiplicative (ZMod p))
    (J : Subgroup G) (a : ZMod p) (P : Fin r → Prop) (ha : a ≠ 0)
    (hP : ∀ i, P i → toAdd (f₀ i) = a ∨ toAdd (f₀ i) = -a)
    (hcent : ∀ f : Fin r → Multiplicative (ZMod p),
      (∃ m : ZMod p, ∀ i, P i → toAdd (f i) = m * toAdd (f₀ i)) →
        ∀ j ∈ J, τ f * j = j * τ f)
    (hcount : p ^ 2 * Nat.card {f : Fin r → Multiplicative (ZMod p) //
      ∀ j ∈ J, τ f * j = j * τ f} ≤ p ^ r) :
    3 ≤ Nat.card {i : Fin r // P i} := by
  classical
  haveI : Fact p.Prime := Fact.mk hp
  haveI : NeZero p := ⟨hp.ne_zero⟩
  let C : Set (Fin r → Multiplicative (ZMod p)) := {f | ∀ j ∈ J, τ f * j = j * τ f}
  let I : Finset (Fin r) := Finset.univ.filter P
  have hcardI : Nat.card {i : Fin r // P i} = I.card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  obtain ⟨i₀, hi₀P, ht₀⟩ :=
    exists_coord_ne_zero_of_ne_zero hp τ f₀ J a P ha hP hcent hcount
  have hi₀ : i₀ ∈ I := by simpa [I] using hi₀P
  let e : ZMod p × ({i // i ∉ I} → Multiplicative (ZMod p)) → {f // f ∈ C} :=
    fun cg => ⟨fun i => if h : i ∈ I then ofAdd (cg.1 * toAdd (f₀ i)) else cg.2 ⟨i, h⟩,
      hcent _ ⟨cg.1, fun i hi => by simp [show i ∈ I by simpa [I] using hi]⟩⟩
  have hcard2 : Nat.card (ZMod p × ({i // i ∉ I} → Multiplicative (ZMod p))) =
      p ^ (1 + (r - I.card)) := by
    rw [Nat.card_prod, Nat.card_fun, ggTBJSpC_card_subtype_notMem,
      Nat.card_congr (Multiplicative.toAdd : Multiplicative (ZMod p) ≃ ZMod p),
      Nat.card_zmod, pow_add, pow_one]
  have hcard1 : p ^ (1 + (r - I.card)) ≤ Nat.card {f // f ∈ C} := by
    rw [← hcard2]
    refine Nat.card_le_card_of_injective e ?_
    rintro ⟨m, g⟩ ⟨m', g'⟩ hgg
    have h1 := congrFun (congrArg Subtype.val hgg)
    have hm : m = m' := mul_right_cancel₀ ht₀ (by
      simpa [e, hi₀] using congrArg Multiplicative.toAdd (h1 i₀))
    have hg : g = g' := by
      funext x
      simpa [e, x.2] using h1 x.1
    rw [hm, hg]
  have hle : p ^ (3 + (r - I.card)) ≤ p ^ r := by
    rw [show 3 + (r - I.card) = 2 + (1 + (r - I.card)) by omega, pow_add]
    exact (Nat.mul_le_mul_left _ hcard1).trans hcount
  rw [hcardI]
  exact le_card_of_pow_le hp (by simpa using Finset.card_le_univ I) hle

private theorem permAut_swap_dinv {p r : ℕ} {x y : Fin r} (hxy : x ≠ y)
    (f : Fin r → Multiplicative (ZMod p)) :
    SpCoord.permAut (Equiv.swap x y) (dinv x y f) = ggTBJSpC_invSwapAut p r x y f := by
  funext i
  rw [SpCoord.permAut_apply, Function.comp_apply, Equiv.swap_inv,
    ggTBJSpC_invSwapAut_apply hxy]
  by_cases hix : i = x
  · subst hix
    rw [Equiv.swap_apply_left, ite_eq_left rfl, OrthNs.dinv_apply_eq]
    simp [hxy]
  · by_cases hiy : i = y
    · subst hiy
      rw [Equiv.swap_apply_right, ite_eq_right hxy.symm, ite_eq_left rfl, OrthNs.dinv_apply_eq]
      simp [hxy]
    · rw [Equiv.swap_apply_of_ne_of_ne hix hiy, ite_eq_right hix, ite_eq_right hiy,
        OrthNs.dinv_apply_eq]
      simp [hxy, hix, hiy]

private theorem invSwapAut_swap {p r : ℕ} {x y : Fin r} :
    ggTBJSpC_invSwapAut p r y x = ggTBJSpC_invSwapAut p r x y := by
  rw [ggTBJSpC_invSwapAut, ggTBJSpC_invSwapAut, SpCoord.sgnAut_mul_comm y x,
    Equiv.swap_comm y x]

theorem exists_conj_reflAut {p r : ℕ} {G : Type} [Group G]
    (τ : (Fin r → Multiplicative (ZMod p)) →* G) (f₀ : Fin r → Multiplicative (ZMod p))
    (J : Subgroup G) (a : ZMod p) (P : Fin r → Prop)
    (hP : ∀ i, P i → toAdd (f₀ i) = a ∨ toAdd (f₀ i) = -a)
    (hswap : ∀ i k : Fin r, i ≠ k → P i → P k → toAdd (f₀ i) = toAdd (f₀ k) →
      ∃ n ∈ J, ∀ f, n * τ f * n⁻¹ = τ (permAut (Equiv.swap i k) f))
    (hmixed : ∀ i k : Fin r, P i → P k → toAdd (f₀ i) = a → toAdd (f₀ k) = -a →
      ∃ n ∈ J, ∀ f, n * τ f * n⁻¹ = τ (permAut (Equiv.swap i k) (dinv i k f)))
    {x y : Fin r} (hx : P x) (hy : P y) (hxy : x ≠ y) :
    ∃ n ∈ J, ∀ f, n * τ f * n⁻¹ =
      τ (ggTBJSpC_reflAut p r (fun i => toAdd (f₀ i)) x y f) := by
  classical
  by_cases h : toAdd (f₀ x) = toAdd (f₀ y)
  · obtain ⟨n, hn, hconj⟩ := hswap x y hxy hx hy h
    refine ⟨n, hn, fun f => ?_⟩
    rw [hconj f, show ggTBJSpC_reflAut p r (fun i => toAdd (f₀ i)) x y f =
      SpCoord.permAut (Equiv.swap x y) f from ggTBJSpC_reflAut_apply_same h f]
  · rcases hP x hx with hx' | hx' <;> rcases hP y hy with hy' | hy'
    · exact absurd (hx'.trans hy'.symm) h
    · obtain ⟨n, hn, hconj⟩ := hmixed x y hx hy hx' hy'
      refine ⟨n, hn, fun f => ?_⟩
      rw [hconj f, permAut_swap_dinv hxy, show ggTBJSpC_reflAut p r
        (fun i => toAdd (f₀ i)) x y f = ggTBJSpC_invSwapAut p r x y f from
        ggTBJSpC_reflAut_apply_mixed h f]
    · obtain ⟨n, hn, hconj⟩ := hmixed y x hy hx hy' hx'
      refine ⟨n, hn, fun f => ?_⟩
      rw [hconj f, permAut_swap_dinv hxy.symm, invSwapAut_swap, show ggTBJSpC_reflAut p r
        (fun i => toAdd (f₀ i)) x y f = ggTBJSpC_invSwapAut p r x y f from
        ggTBJSpC_reflAut_apply_mixed h f]
    · exact absurd (hx'.trans hy'.symm) h

private theorem permAut_swap_mul_sgnAut_ne {p r : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {i k : Fin r} (hik : i ≠ k) :
    (SpCoord.permAut (Equiv.swap i k) * SpCoord.sgnAut i :
      MulAut (Fin r → Multiplicative (ZMod p))) ≠
      SpCoord.sgnAut i * SpCoord.permAut (Equiv.swap i k) := by
  intro hconj
  let f₀' : Fin r → Multiplicative (ZMod p) :=
    Pi.mulSingle i (Multiplicative.ofAdd (1 : ZMod p))
  have h := congrFun (congrArg (fun s : MulAut (Fin r → Multiplicative (ZMod p)) =>
    s f₀') hconj) k
  simp only [MulAut.mul_apply] at h
  simp only [SpCoord.permAut_apply, SpCoord.sgnAut_apply, Function.comp_apply,
    Equiv.swap_inv, Equiv.swap_apply_right, Function.update_self,
    Function.update_of_ne (Ne.symm hik), f₀', Pi.mulSingle_eq_same] at h
  exact ggTBJSpC_ofAdd_one_inv_ne_self hp hp2 h

private theorem exists_conj_transposition_sgnAut_of_eq_zero {p r : ℕ} (hp : p.Prime)
    {G : Type} [Group G] (τ : (Fin r → Multiplicative (ZMod p)) →* G)
    (f₀ : Fin r → Multiplicative (ZMod p)) (J : Subgroup G) (a : ZMod p) (P : Fin r → Prop)
    (ha : a = 0) (hP : ∀ i, P i → toAdd (f₀ i) = a ∨ toAdd (f₀ i) = -a)
    (hswap : ∀ i k : Fin r, i ≠ k → P i → P k → toAdd (f₀ i) = toAdd (f₀ k) →
      ∃ n ∈ J, ∀ f, n * τ f * n⁻¹ = τ (permAut (Equiv.swap i k) f))
    (hsign : a = 0 → 2 ≤ Nat.card {i : Fin r // P i} → ∀ i : Fin r, P i →
      ∃ n ∈ J, ∀ f, n * τ f * n⁻¹ = τ (sgnAut i f))
    (hcent : ∀ f : Fin r → Multiplicative (ZMod p),
      (∃ m : ZMod p, ∀ i, P i → toAdd (f i) = m * toAdd (f₀ i)) →
        ∀ j ∈ J, τ f * j = j * τ f)
    (hcount : p ^ 2 * Nat.card {f : Fin r → Multiplicative (ZMod p) //
      ∀ j ∈ J, τ f * j = j * τ f} ≤ p ^ r) :
    ∃ (i k : Fin r) (n₁ n₂ : G), i ≠ k ∧ n₁ ∈ J ∧ n₂ ∈ J ∧
      (∀ f, n₁ * τ f * n₁⁻¹ = τ (permAut (Equiv.swap i k) f)) ∧
      (∀ f, n₂ * τ f * n₂⁻¹ = τ (sgnAut i f)) := by
  classical
  let I : Finset (Fin r) := Finset.univ.filter P
  have hcardI : Nat.card {i : Fin r // P i} = I.card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hI2 : 2 ≤ I.card := by
    have h := two_le_card_class_of_centralizer hp τ f₀ J P hcent hcount
    rwa [hcardI] at h
  obtain ⟨i, hi, k, hk, hik⟩ := Finset.one_lt_card.mp (by omega : 1 < I.card)
  have hiP : P i := (Finset.mem_filter.mp hi).2
  have hkP : P k := (Finset.mem_filter.mp hk).2
  have ht_eq : ∀ {j : Fin r}, P j → toAdd (f₀ j) = 0 := by
    intro j hj
    rcases hP j hj with h | h
    · simpa [ha] using h
    · simpa [ha] using h
  obtain ⟨n₁, hn₁, hconj₁⟩ := hswap i k hik hiP hkP (by rw [ht_eq hiP, ht_eq hkP])
  have hnat : 2 ≤ Nat.card {i : Fin r // P i} := by rwa [hcardI]
  obtain ⟨n₂, hn₂, hconj₂⟩ := hsign ha hnat i hiP
  exact ⟨i, k, n₁, n₂, hik, hn₁, hn₂, hconj₁, hconj₂⟩

private theorem exists_noncommuting_reflections_of_eq_zero {p r : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {G : Type} [Group G]
    (τ : (Fin r → Multiplicative (ZMod p)) →* G) (f₀ : Fin r → Multiplicative (ZMod p))
    (J : Subgroup G) (a : ZMod p) (P : Fin r → Prop) (ha : a = 0)
    (hP : ∀ i, P i → toAdd (f₀ i) = a ∨ toAdd (f₀ i) = -a)
    (hswap : ∀ i k : Fin r, i ≠ k → P i → P k → toAdd (f₀ i) = toAdd (f₀ k) →
      ∃ n ∈ J, ∀ f, n * τ f * n⁻¹ = τ (permAut (Equiv.swap i k) f))
    (hsign : a = 0 → 2 ≤ Nat.card {i : Fin r // P i} → ∀ i : Fin r, P i →
      ∃ n ∈ J, ∀ f, n * τ f * n⁻¹ = τ (sgnAut i f))
    (hcent : ∀ f : Fin r → Multiplicative (ZMod p),
      (∃ m : ZMod p, ∀ i, P i → toAdd (f i) = m * toAdd (f₀ i)) →
        ∀ j ∈ J, τ f * j = j * τ f)
    (hcount : p ^ 2 * Nat.card {f : Fin r → Multiplicative (ZMod p) //
      ∀ j ∈ J, τ f * j = j * τ f} ≤ p ^ r) :
    ∃ (n₁ n₂ : G) (s₁ s₂ : MulAut (Fin r → Multiplicative (ZMod p))),
      n₁ ∈ J ∧ n₂ ∈ J ∧ (∀ f, n₁ * τ f * n₁⁻¹ = τ (s₁ f)) ∧
      (∀ f, n₂ * τ f * n₂⁻¹ = τ (s₂ f)) ∧ s₁ ^ 2 = 1 ∧ s₂ ^ 2 = 1 ∧
      Nat.card {f : Fin r → Multiplicative (ZMod p) // s₁ f = f} * p = p ^ r ∧
      Nat.card {f : Fin r → Multiplicative (ZMod p) // s₂ f = f} * p = p ^ r ∧
      s₁ * s₂ ≠ s₂ * s₁ := by
  classical
  obtain ⟨i, k, n₁, n₂, hik, hn₁, hn₂, hconj₁, hconj₂⟩ :=
    exists_conj_transposition_sgnAut_of_eq_zero hp τ f₀ J a P ha hP hswap hsign hcent hcount
  have hfix₁ : Nat.card {f : Fin r → Multiplicative (ZMod p) //
      SpCoord.permAut (Equiv.swap i k) f = f} * p = p ^ r := by
    have hcard := SpCoord.card_fix_permAut_swap (p := p) (k := r) hp hp2 hik
    rwa [ggTBJSpC_card_coord] at hcard
  have hfix₂ : Nat.card {f : Fin r → Multiplicative (ZMod p) //
      SpCoord.sgnAut i f = f} * p = p ^ r := by
    have hcard := SpCoord.card_fix_sgnAut (p := p) (k := r) hp hp2 i
    rwa [ggTBJSpC_card_coord] at hcard
  exact ⟨n₁, n₂, SpCoord.permAut (Equiv.swap i k), SpCoord.sgnAut i, hn₁, hn₂,
    hconj₁, hconj₂, SpCoord.permAut_swap_sq i k, SpCoord.sgnAut_sq i, hfix₁, hfix₂,
    permAut_swap_mul_sgnAut_ne hp hp2 hik⟩

private theorem exists_noncommuting_reflections_of_ne_zero {p r : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {G : Type} [Group G]
    (τ : (Fin r → Multiplicative (ZMod p)) →* G) (f₀ : Fin r → Multiplicative (ZMod p))
    (J : Subgroup G) (a : ZMod p) (P : Fin r → Prop) (ha : a ≠ 0)
    (hP : ∀ i, P i → toAdd (f₀ i) = a ∨ toAdd (f₀ i) = -a)
    (hswap : ∀ i k : Fin r, i ≠ k → P i → P k → toAdd (f₀ i) = toAdd (f₀ k) →
      ∃ n ∈ J, ∀ f, n * τ f * n⁻¹ = τ (permAut (Equiv.swap i k) f))
    (hmixed : ∀ i k : Fin r, P i → P k → toAdd (f₀ i) = a → toAdd (f₀ k) = -a →
      ∃ n ∈ J, ∀ f, n * τ f * n⁻¹ = τ (permAut (Equiv.swap i k) (dinv i k f)))
    (hcent : ∀ f : Fin r → Multiplicative (ZMod p),
      (∃ m : ZMod p, ∀ i, P i → toAdd (f i) = m * toAdd (f₀ i)) →
        ∀ j ∈ J, τ f * j = j * τ f)
    (hcount : p ^ 2 * Nat.card {f : Fin r → Multiplicative (ZMod p) //
      ∀ j ∈ J, τ f * j = j * τ f} ≤ p ^ r) :
    ∃ (n₁ n₂ : G) (s₁ s₂ : MulAut (Fin r → Multiplicative (ZMod p))),
      n₁ ∈ J ∧ n₂ ∈ J ∧ (∀ f, n₁ * τ f * n₁⁻¹ = τ (s₁ f)) ∧
      (∀ f, n₂ * τ f * n₂⁻¹ = τ (s₂ f)) ∧ s₁ ^ 2 = 1 ∧ s₂ ^ 2 = 1 ∧
      Nat.card {f : Fin r → Multiplicative (ZMod p) // s₁ f = f} * p = p ^ r ∧
      Nat.card {f : Fin r → Multiplicative (ZMod p) // s₂ f = f} * p = p ^ r ∧
      s₁ * s₂ ≠ s₂ * s₁ := by
  classical
  let I : Finset (Fin r) := Finset.univ.filter P
  have hcardI : Nat.card {i : Fin r // P i} = I.card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hI3 : 3 ≤ I.card := by
    have h := three_le_card_class_of_ne_zero hp τ f₀ J a P ha hP hcent hcount
    rwa [hcardI] at h
  obtain ⟨u, hu, v, hv, w, hw, huv, huw, hvw⟩ :=
    Finset.two_lt_card.mp (by omega : 2 < I.card)
  have huP : P u := (Finset.mem_filter.mp hu).2
  have hvP : P v := (Finset.mem_filter.mp hv).2
  have hwP : P w := (Finset.mem_filter.mp hw).2
  obtain ⟨n₁, hn₁, hconj₁⟩ :=
    exists_conj_reflAut τ f₀ J a P hP hswap hmixed huP hvP huv
  obtain ⟨n₂, hn₂, hconj₂⟩ :=
    exists_conj_reflAut τ f₀ J a P hP hswap hmixed hvP hwP hvw
  exact ⟨n₁, n₂, ggTBJSpC_reflAut p r (fun i => toAdd (f₀ i)) u v,
    ggTBJSpC_reflAut p r (fun i => toAdd (f₀ i)) v w, hn₁, hn₂, hconj₁, hconj₂,
    ggTBJSpC_reflAut_sq huv, ggTBJSpC_reflAut_sq hvw,
    ggTBJSpC_reflAut_card_fix hp hp2 huv, ggTBJSpC_reflAut_card_fix hp hp2 hvw,
    ggTBJSpC_reflAut_noncomm hp huv hvw huw⟩

private theorem exists_noncommuting_reflections_of_eq_zero_of_three_le {p r : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) {G : Type} [Group G]
    (τ : (Fin r → Multiplicative (ZMod p)) →* G) (f₀ : Fin r → Multiplicative (ZMod p))
    (J : Subgroup G) (a : ZMod p) (P : Fin r → Prop) (ha : a = 0)
    (hP : ∀ i, P i → toAdd (f₀ i) = a ∨ toAdd (f₀ i) = -a)
    (hswap : ∀ i k : Fin r, i ≠ k → P i → P k → toAdd (f₀ i) = toAdd (f₀ k) →
      ∃ n ∈ J, ∀ f, n * τ f * n⁻¹ = τ (permAut (Equiv.swap i k) f))
    (h3 : 3 ≤ Nat.card {i : Fin r // P i}) :
    ∃ (n₁ n₂ : G) (s₁ s₂ : MulAut (Fin r → Multiplicative (ZMod p))),
      n₁ ∈ J ∧ n₂ ∈ J ∧ (∀ f, n₁ * τ f * n₁⁻¹ = τ (s₁ f)) ∧
      (∀ f, n₂ * τ f * n₂⁻¹ = τ (s₂ f)) ∧ s₁ ^ 2 = 1 ∧ s₂ ^ 2 = 1 ∧
      Nat.card {f : Fin r → Multiplicative (ZMod p) // s₁ f = f} * p = p ^ r ∧
      Nat.card {f : Fin r → Multiplicative (ZMod p) // s₂ f = f} * p = p ^ r ∧
      s₁ * s₂ ≠ s₂ * s₁ := by
  classical
  let I : Finset (Fin r) := Finset.univ.filter P
  have hcardI : Nat.card {i : Fin r // P i} = I.card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  obtain ⟨u, hu, v, hv, w, hw, huv, huw, hvw⟩ :=
    Finset.two_lt_card.mp (by omega : 2 < I.card)
  have huP : P u := (Finset.mem_filter.mp hu).2
  have hvP : P v := (Finset.mem_filter.mp hv).2
  have hwP : P w := (Finset.mem_filter.mp hw).2
  have ht_eq : ∀ {j : Fin r}, P j → toAdd (f₀ j) = 0 := by
    intro j hj
    rcases hP j hj with h | h
    · simpa [ha] using h
    · simpa [ha] using h
  obtain ⟨n₁, hn₁, hconj₁⟩ := hswap u v huv huP hvP (by rw [ht_eq huP, ht_eq hvP])
  obtain ⟨n₂, hn₂, hconj₂⟩ := hswap v w hvw hvP hwP (by rw [ht_eq hvP, ht_eq hwP])
  let t : Fin r → ZMod p := fun _ => 0
  have hs : ∀ x y : Fin r, ggTBJSpC_reflAut p r t x y = SpCoord.permAut (Equiv.swap x y) :=
    fun x y => MulEquiv.ext fun f => ggTBJSpC_reflAut_apply_same (t := t) (u := x) (w := y) rfl f
  refine ⟨n₁, n₂, ggTBJSpC_reflAut p r t u v, ggTBJSpC_reflAut p r t v w, hn₁, hn₂,
    fun f => by rw [hconj₁ f, hs], fun f => by rw [hconj₂ f, hs],
    ggTBJSpC_reflAut_sq huv, ggTBJSpC_reflAut_sq hvw,
    ggTBJSpC_reflAut_card_fix hp hp2 huv, ggTBJSpC_reflAut_card_fix hp hp2 hvw,
    ggTBJSpC_reflAut_noncomm hp huv hvw huw⟩

theorem ggTBJ_om_core {p r : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {G : Type} [Group G]
    (τ : (Fin r → Multiplicative (ZMod p)) →* G) (f₀ : Fin r → Multiplicative (ZMod p))
    (J : Subgroup G) (a : ZMod p) (P : Fin r → Prop)
    (hP : ∀ i, P i → (toAdd (f₀ i) = a ∨ toAdd (f₀ i) = -a))
    (hswap : ∀ i k : Fin r, i ≠ k → P i → P k → toAdd (f₀ i) = toAdd (f₀ k) →
      ∃ n ∈ J, ∀ f, n * τ f * n⁻¹ = τ (permAut (Equiv.swap i k) f))
    (hmixed : a ≠ 0 → ∀ i k : Fin r, P i → P k → toAdd (f₀ i) = a → toAdd (f₀ k) = -a →
      ∃ n ∈ J, ∀ f, n * τ f * n⁻¹ = τ (permAut (Equiv.swap i k) (dinv i k f)))
    (hsign : a = 0 → 2 ≤ Nat.card {i : Fin r // P i} → ∀ i : Fin r, P i →
      ∃ n ∈ J, ∀ f, n * τ f * n⁻¹ = τ (sgnAut i f))
    (hcent : ∀ f : Fin r → Multiplicative (ZMod p),
      (∃ m : ZMod p, ∀ i, P i → toAdd (f i) = m * toAdd (f₀ i)) →
        ∀ j ∈ J, τ f * j = j * τ f)
    (hcount : p ^ 2 * Nat.card {f : Fin r → Multiplicative (ZMod p) //
      ∀ j ∈ J, τ f * j = j * τ f} ≤ p ^ r) :
    ∃ (n₁ n₂ : G) (s₁ s₂ : MulAut (Fin r → Multiplicative (ZMod p))),
      n₁ ∈ J ∧ n₂ ∈ J ∧ (∀ f, n₁ * τ f * n₁⁻¹ = τ (s₁ f)) ∧
      (∀ f, n₂ * τ f * n₂⁻¹ = τ (s₂ f)) ∧ s₁ ^ 2 = 1 ∧ s₂ ^ 2 = 1 ∧
      Nat.card {f : Fin r → Multiplicative (ZMod p) // s₁ f = f} * p = p ^ r ∧
      Nat.card {f : Fin r → Multiplicative (ZMod p) // s₂ f = f} * p = p ^ r ∧
      s₁ * s₂ ≠ s₂ * s₁ := by
  classical
  by_cases ha : a = 0
  · exact exists_noncommuting_reflections_of_eq_zero hp hp2 τ f₀ J a P ha hP hswap
      hsign hcent hcount
  · exact exists_noncommuting_reflections_of_ne_zero hp hp2 τ f₀ J a P ha hP hswap
      (hmixed ha) hcent hcount

theorem ggTBJ_om_core_nf {p r : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {G : Type} [Group G]
    (τ : (Fin r → Multiplicative (ZMod p)) →* G) (f₀ : Fin r → Multiplicative (ZMod p))
    (J : Subgroup G) (a : ZMod p) (P : Fin r → Prop)
    (hP : ∀ i, P i → (toAdd (f₀ i) = a ∨ toAdd (f₀ i) = -a))
    (hswap : ∀ i k : Fin r, i ≠ k → P i → P k → toAdd (f₀ i) = toAdd (f₀ k) →
      ∃ n ∈ J, ∀ f, n * τ f * n⁻¹ = τ (permAut (Equiv.swap i k) f))
    (hmixed : a ≠ 0 → ∀ i k : Fin r, P i → P k → toAdd (f₀ i) = a → toAdd (f₀ k) = -a →
      ∃ n ∈ J, ∀ f, n * τ f * n⁻¹ = τ (permAut (Equiv.swap i k) (dinv i k f)))
    (h3 : a = 0 → 3 ≤ Nat.card {i : Fin r // P i})
    (hcent : ∀ f : Fin r → Multiplicative (ZMod p),
      (∃ m : ZMod p, ∀ i, P i → toAdd (f i) = m * toAdd (f₀ i)) →
        ∀ j ∈ J, τ f * j = j * τ f)
    (hcount : p ^ 2 * Nat.card {f : Fin r → Multiplicative (ZMod p) //
      ∀ j ∈ J, τ f * j = j * τ f} ≤ p ^ r) :
    ∃ (n₁ n₂ : G) (s₁ s₂ : MulAut (Fin r → Multiplicative (ZMod p))),
      n₁ ∈ J ∧ n₂ ∈ J ∧ (∀ f, n₁ * τ f * n₁⁻¹ = τ (s₁ f)) ∧
      (∀ f, n₂ * τ f * n₂⁻¹ = τ (s₂ f)) ∧ s₁ ^ 2 = 1 ∧ s₂ ^ 2 = 1 ∧
      Nat.card {f : Fin r → Multiplicative (ZMod p) // s₁ f = f} * p = p ^ r ∧
      Nat.card {f : Fin r → Multiplicative (ZMod p) // s₂ f = f} * p = p ^ r ∧
      s₁ * s₂ ≠ s₂ * s₁ := by
  classical
  by_cases ha : a = 0
  · exact exists_noncommuting_reflections_of_eq_zero_of_three_le hp hp2 τ f₀ J a P ha hP
      hswap (h3 ha)
  · exact exists_noncommuting_reflections_of_ne_zero hp hp2 τ f₀ J a P ha hP hswap
      (hmixed ha) hcent hcount

end CFSG.StandardType

end
