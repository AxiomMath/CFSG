module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveThirteenEight
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveThirteenSylow

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveThirteen

open Equiv Equiv.Perm MulAction Subgroup CFSG.Open CFSG.ABGLocalTools
open scoped Pointwise

variable {Ω : Type} [Fintype Ω] [DecidableEq Ω]

private theorem card_fibreStab {ι : Type} [Fintype ι] [DecidableEq ι] (f : Ω → ι) :
    Nat.card (fibreStab f) = ∏ i, (Fintype.card {a // f a = i}).factorial := by
  rw [← DomMulAct.stabilizer_card f, ← Nat.card_eq_fintype_card]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun g =>
    ⟨fun h => funext h, fun h x => congrFun h x⟩)

private theorem swap_mem_fibreStab {ι : Type} {f : Ω → ι} {p q : Ω} (h : f p = f q) :
    swap p q ∈ fibreStab f := fun z => by
  rcases eq_or_ne z p with rfl | hp
  · rw [swap_apply_left, h]
  rcases eq_or_ne z q with rfl | hq
  · rw [swap_apply_right, h]
  · rw [swap_apply_of_ne_of_ne hp hq]

private theorem swap_apply_of_ne_fibre {ι : Type} {f : Ω → ι} {i : ι} {a b : Ω} (ha : f a = i)
    (hb : f b = i) (x : Ω) (hx : f x ≠ i) : swap a b x = x :=
  swap_apply_of_ne_of_ne (fun h => hx (h ▸ ha)) (fun h => hx (h ▸ hb))

private theorem commute_of_fixOut {ι : Type} {f : Ω → ι} {i j : ι} (hij : i ≠ j)
    {g h : Perm Ω} (hg : g ∈ fibreStab f) (hh : h ∈ fibreStab f)
    (hgi : ∀ x, f x ≠ i → g x = x) (hhj : ∀ x, f x ≠ j → h x = x) : g * h = h * g := by
  ext x
  simp only [Perm.mul_apply]
  by_cases hx : f x = i
  · have h1 : h x = x := hhj x (by rw [hx]; exact hij)
    have h2 : h (g x) = g x := hhj (g x) (by rw [hg x, hx]; exact hij)
    rw [h1, h2]
  · have h1 : g x = x := hgi x hx
    have h2 : g (h x) = h x := hgi (h x) (by rw [hh x]; exact hx)
    rw [h1, h2]

private theorem exists_three_of_card {f : Ω → Fin 4} {i : Fin 4}
    (h : Nat.card {x // f x = i} = 4) :
    ∃ u v w : Ω, f u = i ∧ f v = i ∧ f w = i ∧ u ≠ v ∧ u ≠ w ∧ v ≠ w := by
  have h' : Fintype.card {x // f x = i} = 4 := by rw [← Nat.card_eq_fintype_card]; exact h
  let e := Fintype.equivFinOfCardEq h'
  refine ⟨e.symm 0, e.symm 1, e.symm 2, (e.symm 0).2, (e.symm 1).2, (e.symm 2).2, ?_, ?_, ?_⟩ <;>
    intro hh <;> exact absurd (e.symm.injective (Subtype.ext hh)) (by decide)

private theorem exists_two_of_card {f : Ω → Fin 4} {i : Fin 4}
    (h : Nat.card {x // f x = i} = 2) : ∃ r r' : Ω, f r = i ∧ f r' = i ∧ r ≠ r' := by
  have h' : Fintype.card {x // f x = i} = 2 := by rw [← Nat.card_eq_fintype_card]; exact h
  let e := Fintype.equivFinOfCardEq h'
  refine ⟨e.symm 0, e.symm 1, (e.symm 0).2, (e.symm 1).2, ?_⟩
  intro hh
  exact absurd (e.symm.injective (Subtype.ext hh)) (by decide)

private theorem zpow_eq_one_of_apply {u v w : Ω} (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w)
    {m : ℤ} (hm : ((swap u v * swap u w) ^ m) u = u) : (swap u v * swap u w) ^ m = 1 := by
  have h3 : (swap u v * swap u w) ^ (3 : ℕ) = 1 := by
    rw [← (isThreeCycle_swap_mul_swap_same huv huw hvw).orderOf]
    exact pow_orderOf_eq_one _
  rw [zpow_eq_zpow_emod' m h3] at hm ⊢
  have : m % ((3 : ℕ) : ℤ) = 0 ∨ m % ((3 : ℕ) : ℤ) = 1 ∨ m % ((3 : ℕ) : ℤ) = 2 := by omega
  have hcu : (swap u v * swap u w) u = w := by
    rw [Perm.mul_apply, swap_apply_left, swap_apply_of_ne_of_ne huw.symm hvw.symm]
  have hcw : (swap u v * swap u w) w = v := by
    rw [Perm.mul_apply, swap_apply_right, swap_apply_left]
  rcases this with h0 | h1 | h2
  · rw [h0, zpow_zero]
  · rw [h1, zpow_one, hcu] at hm
    exact absurd hm.symm huw
  · rw [h2, show ((2 : ℤ)) = ((2 : ℕ) : ℤ) from rfl, zpow_natCast, pow_two, Perm.mul_apply,
      hcu, hcw] at hm
    exact absurd hm.symm huv

private theorem exists_zpow_mul_zpow {G : Type} [Group G] {c₁ c₂ w : G} (hc : c₁ * c₂ = c₂ * c₁)
    (hw : w ∈ closure ({c₁, c₂} : Set G)) : ∃ m n : ℤ, c₁ ^ m * c₂ ^ n = w := by
  have hcomm : Commute c₁ c₂ := hc
  have hle : zpowers c₁ ≤ normalizer ((zpowers c₂ : Subgroup G) : Set G) := by
    refine le_trans ?_ (centralizer_le_normalizer _)
    rw [zpowers_le, mem_centralizer_iff]
    intro y hy
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hy
    exact (hcomm.symm.zpow_left k).eq
  have hcl : closure ({c₁, c₂} : Set G) = zpowers c₁ ⊔ zpowers c₂ := by
    rw [← Set.singleton_union, Subgroup.closure_union, ← zpowers_eq_closure, ← zpowers_eq_closure]
  rw [hcl] at hw
  have hw' : w ∈ ((zpowers c₁ ⊔ zpowers c₂ : Subgroup G) : Set G) := hw
  rw [coe_mul_of_left_le_normalizer_right _ _ hle] at hw'
  obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_mul.1 hw'
  obtain ⟨m, rfl⟩ := mem_zpowers_iff.1 ha
  obtain ⟨n, rfl⟩ := mem_zpowers_iff.1 hb
  exact ⟨m, n, rfl⟩

theorem exists_irr {Γ T : Subgroup (Perm Ω)} (hA : alternatingGroup Ω ≤ Γ)
    (hT : IsSylowOf 2 T Γ) (h8 : 8 ≤ Fintype.card Ω) (h11 : Fintype.card Ω ≤ 11)
    (hΓ : ¬ Γ ≤ alternatingGroup Ω ∨ 10 ≤ Fintype.card Ω) :
    ∃ P : Subgroup (Perm Ω), P ≤ Γ ∧ IsElemAbelian 3 P ∧ Nat.card P = 9 ∧
      (P : Set (Perm Ω)) * (T : Set (Perm Ω)) = (T : Set (Perm Ω)) * (P : Set (Perm Ω)) ∧
      ∀ W : Subgroup (Perm Ω), W ≤ P →
        normalizer (P : Set (Perm Ω)) ⊓ T ≤ normalizer (W : Set (Perm Ω)) → W = ⊥ ∨ W = P := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨f, hTf, hc0, hc1, hc2, hc3, hc2', t, htT, ht⟩ := exists_labelling hA hT h8 h11
  obtain ⟨u, v, w, hu, hv, hw, huv, huw, hvw⟩ := exists_three_of_card hc0
  obtain ⟨u', v', w', hu', hv', hw', huv', huw', hvw'⟩ := exists_three_of_card hc1
  set c₁ : Perm Ω := swap u v * swap u w with hc₁def
  set c₂ : Perm Ω := swap u' v' * swap u' w' with hc₂def
  have h3c₁ : c₁.IsThreeCycle := isThreeCycle_swap_mul_swap_same huv huw hvw
  have h3c₂ : c₂.IsThreeCycle := isThreeCycle_swap_mul_swap_same huv' huw' hvw'
  have h₁ : c₁ ^ 3 = 1 := by rw [← h3c₁.orderOf]; exact pow_orderOf_eq_one _
  have h₂ : c₂ ^ 3 = 1 := by rw [← h3c₂.orderOf]; exact pow_orderOf_eq_one _
  have hc₁f : c₁ ∈ fibreStab f :=
    mul_mem (swap_mem_fibreStab (hu.trans hv.symm)) (swap_mem_fibreStab (hu.trans hw.symm))
  have hc₂f : c₂ ∈ fibreStab f :=
    mul_mem (swap_mem_fibreStab (hu'.trans hv'.symm)) (swap_mem_fibreStab (hu'.trans hw'.symm))
  have hc₁fix : ∀ x, f x ≠ 0 → c₁ x = x := fun x hx => by
    rw [hc₁def, Perm.mul_apply, swap_apply_of_ne_fibre hu hw x hx,
      swap_apply_of_ne_fibre hu hv x hx]
  have hc₂fix : ∀ x, f x ≠ 1 → c₂ x = x := fun x hx => by
    rw [hc₂def, Perm.mul_apply, swap_apply_of_ne_fibre hu' hw' x hx,
      swap_apply_of_ne_fibre hu' hv' x hx]
  have h01 : (0 : Fin 4) ≠ 1 := by decide
  have hc : c₁ * c₂ = c₂ * c₁ := commute_of_fixOut h01 hc₁f hc₂f hc₁fix hc₂fix
  set C : Subgroup (Perm Ω) := closure {c₁, c₂} with hCdef
  have hc₁C : c₁ ∈ C := subset_closure (Set.mem_insert c₁ {c₂})
  have hc₂C : c₂ ∈ C := subset_closure (Set.mem_insert_of_mem c₁ rfl)
  set J : Subgroup (Perm Ω) := fibreStab f ⊓ Γ with hJdef
  have hCJ : C ≤ J := by
    rw [hCdef, closure_le]
    rintro x (rfl | rfl)
    · exact ⟨hc₁f, hA h3c₁.mem_alternatingGroup⟩
    · exact ⟨hc₂f, hA h3c₂.mem_alternatingGroup⟩
  have hTJ : T ≤ normalizer (J : Set (Perm Ω)) :=
    le_trans (le_inf hTf (hT.le.trans le_normalizer)) inf_normalizer_le_normalizer_inf
  have hD : Nat.card (fibreStab f) ∣ 1152 := by
    rw [card_fibreStab f, Fin.prod_univ_four]
    simp only [Fintype.card_eq_nat_card]
    rw [hc0, hc1]
    calc Nat.factorial 4 * Nat.factorial 4 * (Nat.card {a // f a = 2}).factorial *
          (Nat.card {a // f a = 3}).factorial
        ∣ Nat.factorial 4 * Nat.factorial 4 * Nat.factorial 2 * Nat.factorial 1 :=
          mul_dvd_mul (mul_dvd_mul_left _ (Nat.factorial_dvd_factorial hc2))
            (Nat.factorial_dvd_factorial hc3)
      _ = 1152 := by decide
  have hJ1152 : Nat.card J ∣ 1152 := (card_dvd_of_le inf_le_left).trans hD
  have h23 : ∀ p : ℕ, p.Prime → p ∣ Nat.card J → p = 2 ∨ p = 3 := by
    intro p hp hpJ
    have h : p ∣ 2 ^ 7 * 3 ^ 2 := hpJ.trans hJ1152
    rcases (Nat.Prime.dvd_mul hp).1 h with h | h
    · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h))
    · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 (hp.dvd_of_dvd_pow h))
  have hJ27 : ¬ 27 ∣ Nat.card J := fun h => absurd (h.trans hJ1152) (by decide)
  have hCcomm : ∀ a ∈ C, ∀ b ∈ C, a * b = b * a := by
    intro a ha b hb
    obtain ⟨m, n, rfl⟩ := exists_zpow_mul_zpow hc ha
    obtain ⟨m', n', rfl⟩ := exists_zpow_mul_zpow hc hb
    have hcomm : Commute c₁ c₂ := hc
    have e1 : Commute (c₁ ^ m) (c₁ ^ m') := Commute.zpow_zpow_self c₁ m m'
    have e2 : Commute (c₂ ^ n) (c₂ ^ n') := Commute.zpow_zpow_self c₂ n n'
    have e3 : Commute (c₁ ^ m) (c₂ ^ n') := hcomm.zpow_zpow m n'
    have e4 : Commute (c₂ ^ n) (c₁ ^ m') := (hcomm.zpow_zpow m' n).symm
    calc c₁ ^ m * c₂ ^ n * (c₁ ^ m' * c₂ ^ n') = c₁ ^ m * (c₂ ^ n * c₁ ^ m') * c₂ ^ n' := by
          simp only [mul_assoc]
      _ = c₁ ^ m * (c₁ ^ m' * c₂ ^ n) * c₂ ^ n' := by rw [e4.eq]
      _ = (c₁ ^ m * c₁ ^ m') * (c₂ ^ n * c₂ ^ n') := by simp only [mul_assoc]
      _ = (c₁ ^ m' * c₁ ^ m) * (c₂ ^ n' * c₂ ^ n) := by rw [e1.eq, e2.eq]
      _ = c₁ ^ m' * (c₁ ^ m * c₂ ^ n') * c₂ ^ n := by simp only [mul_assoc]
      _ = c₁ ^ m' * (c₂ ^ n' * c₁ ^ m) * c₂ ^ n := by rw [e3.eq]
      _ = c₁ ^ m' * c₂ ^ n' * (c₁ ^ m * c₂ ^ n) := by simp only [mul_assoc]
  have hCexp : ∀ x ∈ C, x ^ 3 = 1 := by
    intro x hx
    obtain ⟨m, n, rfl⟩ := exists_zpow_mul_zpow hc hx
    have hcomm : Commute (c₁ ^ m) (c₂ ^ n) := (show Commute c₁ c₂ from hc).zpow_zpow m n
    rw [hcomm.mul_pow, ← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, mul_comm m,
      mul_comm n, zpow_mul, zpow_mul, zpow_natCast, zpow_natCast, h₁, h₂, one_zpow, one_zpow,
      mul_one]
  have hCe : IsElemAbelian 3 C :=
    ⟨⟨⟨fun a b => Subtype.ext (hCcomm a a.2 b b.2)⟩⟩, hCexp⟩
  have hC3 : IsPGroup 3 C := fun x => ⟨1, Subtype.ext (by simpa using hCexp x x.2)⟩
  have hfixu : ∀ z ∈ C, z u = u → z ∈ zpowers c₂ := by
    intro z hz hzu
    obtain ⟨m, n, rfl⟩ := exists_zpow_mul_zpow hc hz
    have h2u : (c₂ ^ n) u = u :=
      zpow_apply_eq_self_of_apply_eq_self (hc₂fix u (by rw [hu]; exact h01)) n
    rw [Perm.mul_apply, h2u] at hzu
    rw [hc₁def] at hzu ⊢
    rw [zpow_eq_one_of_apply huv huw hvw hzu, one_mul]
    exact zpow_mem (mem_zpowers c₂) n
  have hfixu' : ∀ z ∈ C, z u' = u' → z ∈ zpowers c₁ := by
    intro z hz hzu
    obtain ⟨m, n, rfl⟩ := exists_zpow_mul_zpow hc hz
    have hf2 : f ((c₂ ^ n) u') = 1 := by rw [(zpow_mem hc₂f n) u', hu']
    have h1u : (c₁ ^ m) ((c₂ ^ n) u') = (c₂ ^ n) u' :=
      zpow_apply_eq_self_of_apply_eq_self (hc₁fix _ (by rw [hf2]; exact h01.symm)) m
    rw [Perm.mul_apply, h1u] at hzu
    rw [hc₂def] at hzu
    have := zpow_eq_one_of_apply huv' huw' hvw' hzu
    rw [← hc₂def] at this
    rw [this, mul_one]
    exact zpow_mem (mem_zpowers c₁) m
  have hc₁u : c₁ u ≠ u := by
    rw [hc₁def, Perm.mul_apply, swap_apply_left, swap_apply_of_ne_of_ne huw.symm hvw.symm]
    exact huw.symm
  have hC9 : Nat.card C = 9 := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hC3
    have hk3 : k < 3 := by
      by_contra hk3
      have : 27 ∣ Nat.card J := by
        refine dvd_trans ?_ (card_dvd_of_le hCJ)
        rw [hk]
        exact (Nat.pow_dvd_pow 3 (not_lt.1 hk3) : 3 ^ 3 ∣ 3 ^ k)
      exact hJ27 this
    have hk2 : 2 ≤ k := by
      by_contra hk2
      have hZ : zpowers c₂ ≤ C := zpowers_le.2 hc₂C
      have hcard : Nat.card C ≤ Nat.card (zpowers c₂) := by
        rw [Nat.card_zpowers, h3c₂.orderOf, hk]
        calc 3 ^ k ≤ 3 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
          _ = 3 := by norm_num
      have hEq := eq_of_le_of_card_ge hZ hcard
      have : c₁ ∈ zpowers c₂ := hEq ▸ hc₁C
      obtain ⟨n, hn⟩ := mem_zpowers_iff.1 this
      apply hc₁u
      rw [← hn]
      exact zpow_apply_eq_self_of_apply_eq_self (hc₂fix u (by rw [hu]; exact h01)) n
    rw [hk, show k = 2 by omega]
    norm_num
  have hCsyl : IsSylowOf 3 C J := by
    refine isSylowOf_of_card hCJ ?_
    have hJ0 : Nat.card J ≠ 0 := Nat.card_pos.ne'
    have h9 : 3 ^ 2 ∣ Nat.card J := by
      rw [show (3 : ℕ) ^ 2 = Nat.card C from hC9.symm]
      exact card_dvd_of_le hCJ
    have hle : 2 ≤ (Nat.card J).factorization 3 :=
      (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three hJ0).1 h9
    have hlt : ¬ 3 ≤ (Nat.card J).factorization 3 := fun h =>
      hJ27 ((Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three hJ0).2 h)
    rw [hC9, show (Nat.card J).factorization 3 = 2 by omega]
    norm_num
  obtain ⟨hJT, hCT⟩ := coe_sup_eq_mul hT inf_le_right hTJ h23 hCsyl
  have hmemJT : ∀ x ∈ J, ∀ y ∈ T, x * y ∈ ((J ⊔ T : Subgroup (Perm Ω)) : Set (Perm Ω)) :=
    fun x hx y hy => (J ⊔ T).mul_mem (le_sup_left (a := J) hx) (le_sup_right (b := T) hy)
  obtain ⟨j, hjJ, hjt⟩ := exists_inv_mul_mem_normalizer hCsyl (hTJ htT)
  have hjt' := hmemJT _ (J.inv_mem hjJ) _ htT
  rw [hJT] at hjt'
  obtain ⟨c, hcC, t₁, ht₁T, hct⟩ := Set.mem_mul.1 hjt'
  have ht₁ : t₁ = c⁻¹ * (j⁻¹ * t) := by rw [← hct, inv_mul_cancel_left]
  have ht₁N : t₁ ∈ normalizer (C : Set (Perm Ω)) := by
    rw [ht₁]
    exact mul_mem (le_normalizer (C.inv_mem hcC)) hjt
  have hf₁ : ∀ x, f (t₁ x) = f (t x) := by
    intro x
    have hmem : c⁻¹ * j⁻¹ ∈ fibreStab f := (J.mul_mem (hCJ (C.inv_mem hcC)) (J.inv_mem hjJ)).1
    rw [ht₁, ← mul_assoc]
    exact hmem (t x)
  have hinv : ∀ x, t₁ (t₁⁻¹ x) = x := fun x => t₁.apply_symm_apply x
  have hf₁' : ∀ x, f x = 0 → f (t₁⁻¹ x) = 1 := by
    intro x hx
    have := (ht (t₁⁻¹ x)).1
    rw [← hf₁, hinv] at this
    exact this.1 hx
  have hf₁'' : ∀ x, f x = 1 → f (t₁⁻¹ x) = 0 := by
    intro x hx
    have := (ht (t₁⁻¹ x)).2
    rw [← hf₁, hinv] at this
    exact this.1 hx
  have h11 : t₁ * c₁ * t₁⁻¹ ∈ zpowers c₂ := by
    refine hfixu _ ((mem_normalizer_iff.1 ht₁N c₁).1 hc₁C) ?_
    rw [Perm.mul_apply, Perm.mul_apply, hc₁fix _ (by rw [hf₁' u hu]; exact h01.symm),
      hinv]
  have h12 : t₁ * c₂ * t₁⁻¹ ∈ zpowers c₁ := by
    refine hfixu' _ ((mem_normalizer_iff.1 ht₁N c₂).1 hc₂C) ?_
    rw [Perm.mul_apply, Perm.mul_apply, hc₂fix _ (by rw [hf₁'' u' hu']; exact h01),
      hinv]
  obtain ⟨ρ, hρf, hρfix, hτΓ⟩ : ∃ ρ : Perm Ω, ρ ∈ fibreStab f ∧ (∀ x, f x ≠ 2 → ρ x = x) ∧
      swap u v * ρ ∈ Γ := by
    rcases hΓ with hΓ | h10
    · obtain ⟨g, hgΓ, hgA⟩ := SetLike.not_le_iff_exists.1 hΓ
      have hsg : Perm.sign g = -1 := by
        rcases Int.units_eq_one_or (Perm.sign g) with h | h
        · exact absurd (mem_alternatingGroup.2 h) hgA
        · exact h
      have hgs : g⁻¹ * swap u v ∈ alternatingGroup Ω := by
        rw [mem_alternatingGroup, Perm.sign_mul, Perm.sign_inv, hsg, sign_swap huv]
        decide
      refine ⟨1, one_mem _, fun x _ => rfl, ?_⟩
      rw [mul_one, ← mul_inv_cancel_left g (swap u v)]
      exact Γ.mul_mem hgΓ (hA hgs)
    · obtain ⟨r, r', hr, hr', hrr'⟩ := exists_two_of_card (hc2' h10)
      refine ⟨swap r r', swap_mem_fibreStab (hr.trans hr'.symm),
        fun x hx => swap_apply_of_ne_fibre hr hr' x hx, hA ?_⟩
      rw [mem_alternatingGroup, Perm.sign_mul, sign_swap huv, sign_swap hrr']
      decide
  set τ : Perm Ω := swap u v * ρ with hτdef
  have hsf : swap u v ∈ fibreStab f := swap_mem_fibreStab (hu.trans hv.symm)
  have hsfix : ∀ x, f x ≠ 0 → swap u v x = x := fun x hx => swap_apply_of_ne_fibre hu hv x hx
  have hτJ : τ ∈ J := ⟨mul_mem hsf hρf, hτΓ⟩
  have hconj : ∀ g : Perm Ω, ρ * g = g * ρ → τ * g * τ⁻¹ = swap u v * g * (swap u v)⁻¹ := by
    intro g hg
    rw [hτdef, mul_inv_rev, mul_assoc (swap u v) ρ g, hg]
    group
  have h20 : (2 : Fin 4) ≠ 0 := by decide
  have h21' : (2 : Fin 4) ≠ 1 := by decide
  have hτ1 : τ * c₁ * τ⁻¹ = c₁⁻¹ := by
    rw [hconj c₁ (commute_of_fixOut h20 hρf hc₁f hρfix hc₁fix), hc₁def]
    simp only [Equiv.swap_mul_self_mul, mul_inv_rev, Equiv.swap_inv]
  have hτ2 : τ * c₂ * τ⁻¹ = c₂ := by
    rw [hconj c₂ (commute_of_fixOut h21' hρf hc₂f hρfix hc₂fix),
      commute_of_fixOut h01 hsf hc₂f hsfix hc₂fix, mul_inv_cancel_right]
  have hτN : τ ∈ normalizer (C : Set (Perm Ω)) := by
    refine mem_normalizer_fintype fun z hz => ?_
    obtain ⟨m, n, rfl⟩ := exists_zpow_mul_zpow hc hz
    have e1 : τ * (c₁ ^ m * c₂ ^ n) * τ⁻¹ = (τ * c₁ ^ m * τ⁻¹) * (τ * c₂ ^ n * τ⁻¹) := by
      simp only [mul_assoc, inv_mul_cancel_left]
    rw [e1, ← conj_zpow, ← conj_zpow, hτ1, hτ2]
    exact C.mul_mem (C.zpow_mem (C.inv_mem hc₁C) m) (C.zpow_mem hc₂C n)
  have hτJT := hmemJT τ hτJ 1 (T.one_mem)
  rw [mul_one, hJT] at hτJT
  obtain ⟨d, hdC, t₂, ht₂T, hdt⟩ := Set.mem_mul.1 hτJT
  have ht₂ : t₂ = d⁻¹ * τ := by rw [← hdt, inv_mul_cancel_left]
  have ht₂N : t₂ ∈ normalizer (C : Set (Perm Ω)) := by
    rw [ht₂]
    exact mul_mem (le_normalizer (C.inv_mem hdC)) hτN
  have hconjd : ∀ g ∈ C, t₂ * g * t₂⁻¹ = τ * g * τ⁻¹ := by
    intro g hg
    have hτg : τ * g * τ⁻¹ ∈ C := (mem_normalizer_iff.1 hτN g).1 hg
    rw [ht₂, mul_inv_rev, inv_inv]
    calc d⁻¹ * τ * g * (τ⁻¹ * d) = d⁻¹ * (τ * g * τ⁻¹) * d := by group
      _ = τ * g * τ⁻¹ := by
        rw [mul_assoc, ← hCcomm d hdC _ hτg, inv_mul_cancel_left]
  have h21 : t₂ * c₁ * t₂⁻¹ = c₁⁻¹ := by rw [hconjd c₁ hc₁C, hτ1]
  have h22 : t₂ * c₂ * t₂⁻¹ = c₂ := by rw [hconjd c₂ hc₂C, hτ2]
  refine ⟨C, hCJ.trans inf_le_right, hCe, hC9, hCT, ?_⟩
  exact irrOn_of_witnesses (N := normalizer (C : Set (Perm Ω)) ⊓ T) h₁ h₂ hc ⟨ht₁N, ht₁T⟩
    ⟨ht₂N, ht₂T⟩ h21 h22 h11 h12

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveThirteen
