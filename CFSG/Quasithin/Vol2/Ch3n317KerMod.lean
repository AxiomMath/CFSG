module

public import CFSG.Quasithin.Vol2.Ch3n317A5
public import CFSG.Quasithin.Vol2.Ch10SecEA5b

public section

open Equiv

namespace CFSG.Quasithin.Ch3n317Ker

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.Ch3n317A5
open CFSG.QuasithinUnique.A5.Delta5 (pact vact isEven mem_evenWeight_iff vact_mul vact_faithful)

theorem card_evenWeight_five : Nat.card ↥(evenWeight 5) = 16 := by
  classical
  rw [Nat.card_congr (Equiv.subtypeEquivRight (fun x : Fin 5 → ZMod 2 => mem_evenWeight_iff x)),
    Nat.card_eq_fintype_card, Fintype.card_subtype]
  decide +kernel

theorem eq_zero_of_fix : ∀ x : Fin 5 → ZMod 2, isEven x →
    pact (swap 0 1 * swap 1 2) x = x → pact (swap 2 3 * swap 3 4) x = x → x = 0 := by
  decide +kernel

@[expose] def fourSet (a b c d : Fin 5) : Finset (Perm (Fin 5)) :=
  {1, swap a b, swap c d, swap a b * swap c d}

theorem fourSet_facts : ∀ a b c d : Fin 5, a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d →
    (fourSet a b c d).card = 4 ∧ (∀ σ ∈ fourSet a b c d, ∀ τ ∈ fourSet a b c d, σ * τ = τ * σ) ∧
      (∀ σ ∈ fourSet a b c d, σ * σ = 1) ∧
      (Finset.univ.filter fun f : Fin 5 → ZMod 2 =>
        isEven f ∧ pact (swap a b) f = f ∧ pact (swap c d) f = f).card = 4 := by
  decide +kernel

theorem gen_facts : ∀ a b c d : Fin 5, a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d →
    ∃ e : Fin 5, (swap b e * swap b c) * swap a b = swap a c * (swap b e * swap b c) ∧
      (swap b e * swap b c) * swap c d = swap d e * (swap b e * swap b c) ∧
      (swap b e * swap b c) ^ 3 = 1 ∧ swap b e * swap b c ≠ 1 ∧
      (swap a b * swap a c * swap c d * swap d e) ^ 5 = 1 ∧
      swap a b * swap a c * swap c d * swap d e ≠ 1 ∧
      (swap a b * swap a c * swap c d * swap d e).support = Finset.univ := by
  decide +kernel

section Comp

variable {W : Type*} [CommGroup W] {L : Subgroup (MulAut W)}

@[expose] def IsEquiv5 (θ : ↥L ≃* Perm (Fin 5))
    (β : ↥(commV L) ≃* Multiplicative (evenWeight 5)) : Prop :=
  ∀ (h : ↥L) (u : ↥(commV L)) (hu : (h : MulAut W) (u : W) ∈ commV L) (i : Fin 5),
    ((Multiplicative.toAdd (β ⟨(h : MulAut W) u, hu⟩) : evenWeight 5) : Fin 5 → ZMod 2) i =
      ((Multiplicative.toAdd (β u) : evenWeight 5) : Fin 5 → ZMod 2) ((θ h)⁻¹ i)

variable {θ : ↥L ≃* Perm (Fin 5)} {β : ↥(commV L) ≃* Multiplicative (evenWeight 5)}

theorem card_commV (β : ↥(commV L) ≃* Multiplicative (evenWeight 5)) :
    Nat.card ↥(commV L) = 16 := by
  rw [Nat.card_congr β.toEquiv, Nat.card_congr Multiplicative.toAdd, card_evenWeight_five]

theorem apply_eq_iff (hβ : IsEquiv5 θ β) {x : MulAut W} (hx : x ∈ L) (u : ↥(commV L)) :
    x (u : W) = u ↔
      vact (θ ⟨x, hx⟩) (Multiplicative.toAdd (β u)) = Multiplicative.toAdd (β u) := by
  have hc : ((Multiplicative.toAdd (β ⟨x u, commV_invariant L x hx u u.2⟩) : evenWeight 5) :
      Fin 5 → ZMod 2) =
        pact (θ ⟨x, hx⟩) ((Multiplicative.toAdd (β u) : evenWeight 5) : Fin 5 → ZMod 2) :=
    Vol2.Ch10.SecE.coord_apply θ β hβ ⟨x, hx⟩ u
  constructor
  · intro h
    have e : (⟨x u, commV_invariant L x hx u u.2⟩ : ↥(commV L)) = u := Subtype.ext h
    apply Subtype.ext
    change pact (θ ⟨x, hx⟩) _ = _
    rw [← hc, e]
  · intro h
    have h1 : (⟨x u, commV_invariant L x hx u u.2⟩ : ↥(commV L)) = u := by
      apply β.injective
      apply Multiplicative.toAdd.injective
      apply Subtype.ext
      rw [hc]
      exact congrArg Subtype.val h
    exact congrArg Subtype.val h1

theorem fixV_oTwoUpper_inf (hβ : IsEquiv5 θ β) : fixV (oTwoUpper L) ⊓ commV L = ⊥ := by
  rw [eq_bot_iff]
  rintro w ⟨hwf, hwc⟩
  have h3 : ∀ σ : Perm (Fin 5), σ ^ 3 = 1 → σ ≠ 1 →
      ((θ.symm σ : ↥L) : MulAut W) ∈ oTwoUpper L := by
    intro σ hσ3 hσ1
    refine mem_oTwoUpper_of_odd (θ.symm σ).2 ?_
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, orderOf_eq_prime hσ3 hσ1]
    decide
  have hfix : ∀ σ : Perm (Fin 5), σ ^ 3 = 1 → σ ≠ 1 →
      pact σ ((Multiplicative.toAdd (β ⟨w, hwc⟩) : evenWeight 5) : Fin 5 → ZMod 2) =
        ((Multiplicative.toAdd (β ⟨w, hwc⟩) : evenWeight 5) : Fin 5 → ZMod 2) := by
    intro σ hσ3 hσ1
    have hx := hwf _ (h3 σ hσ3 hσ1)
    have h1 := (apply_eq_iff hβ (θ.symm σ).2 ⟨w, hwc⟩).mp hx
    have e : θ ⟨((θ.symm σ : ↥L) : MulAut W), (θ.symm σ).2⟩ = σ := by simp
    rw [e] at h1
    exact congrArg Subtype.val h1
  have h0 := eq_zero_of_fix _ (Multiplicative.toAdd (β ⟨w, hwc⟩)).2
    (hfix _ (by decide) (by decide)) (hfix _ (by decide) (by decide))
  have h1 : β ⟨w, hwc⟩ = β 1 := by
    rw [map_one]
    apply Multiplicative.toAdd.injective
    apply Subtype.ext
    rw [h0]
    rfl
  exact congrArg Subtype.val (β.injective h1)

theorem exists_apply_ne (hβ : IsEquiv5 θ β) {x : MulAut W} (hx : x ∈ L) (hx1 : x ≠ 1) :
    ∃ w ∈ commV L, x w ≠ w := by
  by_contra hall
  push Not at hall
  apply hx1
  have h : θ ⟨x, hx⟩ = 1 := vact_faithful fun e => by
    have h1 := (apply_eq_iff hβ hx (β.symm (Multiplicative.ofAdd e))).mp
      (hall _ (β.symm (Multiplicative.ofAdd e)).2)
    simpa using h1
  have h2 : (⟨x, hx⟩ : ↥L) = 1 := by
    rw [← map_one θ] at h
    exact θ.injective h
  exact congrArg Subtype.val h2

theorem card_fixV_inf (hβ : IsEquiv5 θ β) {B : Subgroup (MulAut W)} (hBL : B ≤ L) :
    Nat.card ↥(fixV B ⊓ commV L) =
      Nat.card {e : evenWeight 5 // ∀ x (hx : x ∈ B), vact (θ ⟨x, hBL hx⟩) e = e} := by
  refine Nat.card_congr
    { toFun := fun u => ⟨Multiplicative.toAdd (β ⟨u.1, u.2.2⟩), fun x hx =>
        (apply_eq_iff hβ (hBL hx) ⟨u.1, u.2.2⟩).mp (u.2.1 x hx)⟩
      invFun := fun e => ⟨((β.symm (Multiplicative.ofAdd e.1) : ↥(commV L)) : W),
        fun x hx => (apply_eq_iff hβ (hBL hx) _).mpr (by simpa using e.2 x hx),
        (β.symm (Multiplicative.ofAdd e.1)).2⟩
      left_inv := fun u => by
        apply Subtype.ext
        simp
      right_inv := fun e => by
        apply Subtype.ext
        simp }

@[expose] def A5Comp (L P : Subgroup (MulAut W)) : Prop :=
  ∃ (θ : ↥L ≃* Perm (Fin 5)) (β : ↥(commV L) ≃* Multiplicative (evenWeight 5)), IsEquiv5 θ β ∧
    ∃ a b c d : Fin 5, a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧
      ∀ x : MulAut W, x ∈ P ↔ ∃ hx : x ∈ L, θ ⟨x, hx⟩ ∈ fourSet a b c d

variable {P : Subgroup (MulAut W)}

theorem A5Comp.le (h : A5Comp L P) : P ≤ L := by
  obtain ⟨θ, β, -, a, b, c, d, -, -, -, -, -, -, hP⟩ := h
  intro x hx
  exact ((hP x).mp hx).1

theorem A5Comp.fixV_oTwoUpper_inf (h : A5Comp L P) : fixV (oTwoUpper L) ⊓ commV L = ⊥ := by
  obtain ⟨θ, β, hβ, -⟩ := h
  exact Ch3n317Ker.fixV_oTwoUpper_inf hβ

theorem A5Comp.card_commV (h : A5Comp L P) : Nat.card ↥(commV L) = 16 := by
  obtain ⟨θ, β, -⟩ := h
  exact Ch3n317Ker.card_commV β

theorem A5Comp.fix_of_commute (h : A5Comp L P) {g : MulAut W} (hg : ∀ k ∈ L, g * k = k * g)
    {w : W} (hw : w ∈ commV L) : g w = w := by
  obtain ⟨θ, β, hβ, -⟩ := h
  exact Vol2.Ch10.SecE.fix_commV_of_commute hβ hg hw

theorem A5Comp.card_P (h : A5Comp L P) : Nat.card P = 4 := by
  classical
  obtain ⟨θ, β, -, a, b, c, d, hab, hac, had, hbc, hbd, hcd, hP⟩ := h
  have e : Nat.card P = Nat.card ↥(fourSet a b c d) := by
    refine Nat.card_congr
      { toFun := fun x => ⟨θ ⟨x.1, ((hP x.1).mp x.2).1⟩, ((hP x.1).mp x.2).2⟩
        invFun := fun σ => ⟨((θ.symm σ.1 : ↥L) : MulAut W), (hP _).mpr ⟨(θ.symm σ.1).2, by
          simp⟩⟩
        left_inv := fun x => by
          apply Subtype.ext
          simp
        right_inv := fun σ => by
          apply Subtype.ext
          simp }
  rw [e, Nat.card_eq_fintype_card, Fintype.card_coe]
  exact (fourSet_facts a b c d hab hac had hbc hbd hcd).1

theorem A5Comp.comm (h : A5Comp L P) : ∀ x ∈ P, ∀ y ∈ P, x * y = y * x := by
  obtain ⟨θ, β, -, a, b, c, d, hab, hac, had, hbc, hbd, hcd, hP⟩ := h
  intro x hx y hy
  obtain ⟨hxL, hx'⟩ := (hP x).mp hx
  obtain ⟨hyL, hy'⟩ := (hP y).mp hy
  have h1 := (fourSet_facts a b c d hab hac had hbc hbd hcd).2.1 _ hx' _ hy'
  have h2 : θ (⟨x, hxL⟩ * ⟨y, hyL⟩) = θ (⟨y, hyL⟩ * ⟨x, hxL⟩) := by
    rw [map_mul, map_mul, h1]
  exact congrArg Subtype.val (θ.injective h2)

theorem A5Comp.card_fixV_P (h : A5Comp L P) : Nat.card ↥(fixV P ⊓ commV L) = 4 := by
  classical
  have hPL := h.le
  obtain ⟨θ, β, hβ, a, b, c, d, hab, hac, had, hbc, hbd, hcd, hP⟩ := h
  rw [card_fixV_inf hβ hPL]
  have hab' : ((θ.symm (swap a b) : ↥L) : MulAut W) ∈ P :=
    (hP _).mpr ⟨(θ.symm _).2, by simp [fourSet]⟩
  have hcd' : ((θ.symm (swap c d) : ↥L) : MulAut W) ∈ P :=
    (hP _).mpr ⟨(θ.symm _).2, by simp [fourSet]⟩
  have e : Nat.card {e : evenWeight 5 // ∀ x (hx : x ∈ P), vact (θ ⟨x, hPL hx⟩) e = e} =
      Nat.card {e : evenWeight 5 // vact (swap a b) e = e ∧ vact (swap c d) e = e} := by
    refine Nat.card_congr (Equiv.subtypeEquivRight fun e => ?_)
    constructor
    · intro he
      have h1 := he _ hab'
      have h2 := he _ hcd'
      simp only [Subtype.coe_eta, MulEquiv.apply_symm_apply] at h1 h2
      exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩ x hx
      obtain ⟨hxL', hx'⟩ := (hP x).mp hx
      simp only [fourSet, Finset.mem_insert, Finset.mem_singleton] at hx'
      rcases hx' with h0 | h0 | h0 | h0
      · rw [h0]
        rfl
      · rw [h0]
        exact h1
      · rw [h0]
        exact h2
      · rw [h0, vact_mul, h2, h1]
  rw [e]
  have e2 : Nat.card {e : evenWeight 5 // vact (swap a b) e = e ∧ vact (swap c d) e = e} =
      (Finset.univ.filter fun f : Fin 5 → ZMod 2 =>
        isEven f ∧ pact (swap a b) f = f ∧ pact (swap c d) f = f).card := by
    rw [← Fintype.card_coe, ← Nat.card_eq_fintype_card]
    refine Nat.card_congr
      { toFun := fun w => ⟨w.1.1, by
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨w.1.2, congrArg Subtype.val w.2.1, congrArg Subtype.val w.2.2⟩⟩
        invFun := fun f => ⟨⟨f.1, by
          have := f.2
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at this
          exact this.1⟩, by
          have := f.2
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at this
          exact ⟨Subtype.ext this.2.1, Subtype.ext this.2.2⟩⟩
        left_inv := fun w => rfl
        right_inv := fun f => rfl }
  rw [e2]
  exact (fourSet_facts a b c d hab hac had hbc hbd hcd).2.2.2

theorem A5Comp.card_mul_card_le (h : A5Comp L P) {B : Subgroup (MulAut W)} (hBP : B ≤ P) :
    Nat.card B * Nat.card ↥(fixV B ⊓ commV L) ≤ 16 := by
  have hPL := h.le
  have h16 := h.card_commV
  have h4 := h.card_P
  have hF4 := h.card_fixV_P
  have : Finite ↥(commV L) := Nat.finite_of_card_ne_zero (by rw [h16]; norm_num)
  have : Finite ↥P := Nat.finite_of_card_ne_zero (by rw [h4]; norm_num)
  by_cases hB : B = ⊥
  · subst hB
    have e : fixV (⊥ : Subgroup (MulAut W)) ⊓ commV L = commV L := by
      refine inf_eq_right.mpr fun w _ => ?_
      intro x hx
      rw [Subgroup.mem_bot.mp hx]
      rfl
    rw [e, h16, Subgroup.card_bot]
  · obtain ⟨⟨x, hxB⟩, hx1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hB
    have hx1' : x ≠ 1 := fun h1 => hx1 (Subtype.ext h1)
    obtain ⟨θ, β, hβ, -⟩ := h
    obtain ⟨w, hwc, hxw⟩ := exists_apply_ne hβ (hPL (hBP hxB)) hx1'
    have hdvd : Nat.card ↥(fixV B ⊓ commV L) ∣ 16 := by
      rw [← h16]
      exact Subgroup.card_dvd_of_le inf_le_right
    have hne : Nat.card ↥(fixV B ⊓ commV L) ≠ 16 := by
      intro heq
      rw [← h16] at heq
      have hle : commV L ≤ fixV B ⊓ commV L :=
        (Subgroup.eq_of_le_of_card_ge inf_le_right (le_of_eq heq.symm)).symm.le
      exact hxw ((hle hwc).1 x hxB)
    have h8 : Nat.card ↥(fixV B ⊓ commV L) ≤ 8 := by
      have hle := Nat.le_of_dvd (by norm_num) hdvd
      have : Nat.card ↥(fixV B ⊓ commV L) < 16 := lt_of_le_of_ne hle hne
      interval_cases hc : Nat.card ↥(fixV B ⊓ commV L) <;> omega
    have hBd : Nat.card B ∣ 4 := by
      rw [← h4]
      exact Subgroup.card_dvd_of_le hBP
    have hB4 := Nat.le_of_dvd (by norm_num) hBd
    have hB1 : Nat.card B ≠ 1 := fun h1 => hB (Subgroup.eq_bot_of_card_eq B h1)
    have hB0 : 0 < Nat.card B := by
      have : Finite ↥B := Finite.of_injective _ (Subgroup.inclusion_injective hBP)
      exact Nat.card_pos
    interval_cases hc : Nat.card B
    · exact absurd rfl hB1
    · omega
    · norm_num at hBd
    · have hBP' : B = P := Subgroup.eq_of_le_of_card_ge hBP (by rw [h4, hc])
      subst hBP'
      rw [hF4]

theorem A5Comp.exists_gen (h : A5Comp L P) : ∃ g ∈ oTwoUpper L, L ≤ P ⊔ B1.conjAut g P := by
  obtain ⟨θ, β, -, a, b, c, d, hab, hac, had, hbc, hbd, hcd, hP⟩ := h
  obtain ⟨e, h1, h2, h3, h3', h5, h5', hsupp⟩ := gen_facts a b c d hab hac had hbc hbd hcd
  set φ : Perm (Fin 5) →* MulAut W := L.subtype.comp θ.symm.toMonoidHom with hφ
  have hφmem : ∀ σ, φ σ ∈ L := fun σ => (θ.symm σ).2
  have hφθ : ∀ σ, θ ⟨φ σ, hφmem σ⟩ = σ := fun σ => by simp [hφ]
  have hPmem : ∀ σ ∈ fourSet a b c d, φ σ ∈ P := fun σ hσ =>
    (hP _).mpr ⟨hφmem σ, by rw [hφθ]; exact hσ⟩
  set g₀ := swap b e * swap b c with hg₀
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine ⟨φ g₀, mem_oTwoUpper_of_odd (hφmem g₀) ?_, ?_⟩
  · have e1 : orderOf (φ g₀) = orderOf g₀ := by
      rw [hφ, MonoidHom.comp_apply, Subgroup.coe_subtype, Subgroup.orderOf_coe,
        MulEquiv.coe_toMonoidHom, MulEquiv.orderOf_eq]
    rw [e1, orderOf_eq_prime h3 h3']
    decide
  · have hL : L = (⊤ : Subgroup (Perm (Fin 5))).map φ := by
      rw [← MonoidHom.range_eq_map]
      ext x
      rw [MonoidHom.mem_range]
      constructor
      · intro hx
        exact ⟨θ ⟨x, hx⟩, by simp [hφ]⟩
      · rintro ⟨σ, rfl⟩
        exact hφmem σ
    have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    have hcyc : (swap a b * swap a c * swap c d * swap d e).IsCycle :=
      Perm.isCycle_of_prime_order'' (by simp; norm_num) (by
        rw [orderOf_eq_prime h5 h5']
        simp)
    have htop : Subgroup.closure ({swap a b * swap a c * swap c d * swap d e, swap a b} :
        Set (Perm (Fin 5))) = ⊤ :=
      Perm.closure_prime_cycle_swap (by simp; norm_num) hcyc hsupp ⟨a, b, hab, rfl⟩
    have hconj : ∀ σ τ : Perm (Fin 5), g₀ * σ = τ * g₀ → σ ∈ fourSet a b c d →
        φ τ ∈ B1.conjAut (φ g₀) P := by
      intro σ τ hστ hσ
      rw [B1.mem_conjAut]
      have e2 : σ = g₀⁻¹ * τ * g₀ := by rw [mul_assoc, ← hστ]; group
      rw [← map_inv, ← map_mul, ← map_mul, ← e2]
      exact hPmem σ hσ
    have hab4 : swap a b ∈ fourSet a b c d := by simp [fourSet]
    have hcd4 : swap c d ∈ fourSet a b c d := by simp [fourSet]
    rw [hL, ← htop, MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨τ, hτ, rfl⟩
    rcases hτ with rfl | rfl
    · rw [map_mul φ (swap a b * swap a c * swap c d), map_mul φ (swap a b * swap a c),
        map_mul φ (swap a b)]
      refine Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ ?_ ?_) ?_) ?_
      · exact Subgroup.mem_sup_left (hPmem _ hab4)
      · exact Subgroup.mem_sup_right (hconj _ _ h1 hab4)
      · exact Subgroup.mem_sup_left (hPmem _ hcd4)
      · exact Subgroup.mem_sup_right (hconj _ _ h2 hcd4)
    · exact Subgroup.mem_sup_left (hPmem _ hab4)

end Comp

theorem le_normalizer_oTwoUpper {X : Type*} [Group X] (L : Subgroup X) :
    L ≤ Subgroup.normalizer (oTwoUpper L : Set X) := by
  have key : ∀ l ∈ L, ∀ x ∈ oTwoUpper L, l * x * l⁻¹ ∈ oTwoUpper L := by
    intro l hl x hx
    induction hx using Subgroup.closure_induction with
    | mem y hy =>
      refine Subgroup.subset_closure ⟨L.mul_mem (L.mul_mem hl hy.1) (L.inv_mem hl), ?_⟩
      have e : orderOf (l * y * l⁻¹) = orderOf y := by
        have := MulEquiv.orderOf_eq (MulAut.conj l) y
        simpa using this
      rw [e]
      exact hy.2
    | one => simp
    | mul a b _ _ ha hb =>
      have e : l * (a * b) * l⁻¹ = (l * a * l⁻¹) * (l * b * l⁻¹) := by group
      rw [e]
      exact Subgroup.mul_mem _ ha hb
    | inv a _ ha =>
      have e : l * a⁻¹ * l⁻¹ = (l * a * l⁻¹)⁻¹ := by group
      rw [e]
      exact Subgroup.inv_mem _ ha
  intro l hl
  exact B6.mem_normalizer_of_forall_mem (key l hl) fun x hx => by
    have := key l⁻¹ (L.inv_mem hl) x hx
    simpa using this

section Global

variable {W : Type*} [CommGroup W] [Finite W]

omit [Finite W] in
theorem mem_fixV_sup {A B : Subgroup (MulAut W)} {w : W} (hA : w ∈ fixV A) (hB : w ∈ fixV B) :
    w ∈ fixV (A ⊔ B) :=
  CFSG.Quasithin.FixVLat.mem_fixV_sup hA hB

omit [Finite W] in
theorem fixV_anti {A B : Subgroup (MulAut W)} (h : A ≤ B) : fixV B ≤ fixV A :=
  fun _ hw x hx => hw x (h hx)

omit [Finite W] in
theorem fix_fixV {L K : Subgroup (MulAut W)} (hLK : L ≤ Subgroup.normalizer (K : Set (MulAut W)))
    (hOK : oTwoUpper L ≤ K) (h0 : fixV (oTwoUpper L) ⊓ commV L = ⊥) :
    ∀ l ∈ L, ∀ d ∈ fixV K, l d = d := by
  intro l hl d hd
  have hw : l d * d⁻¹ ∈ commV L := Subgroup.subset_closure ⟨l, hl, d, rfl⟩
  have hwf : l d * d⁻¹ ∈ fixV K := by
    intro k hk
    have hk' : l⁻¹ * k * l ∈ K := by
      have := (Subgroup.mem_normalizer_iff.mp (hLK (L.inv_mem hl)) k).mp hk
      simpa using this
    have h1 : k (l d) = l d := by
      have h2 : (l⁻¹ * k * l) d = d := hd _ hk'
      have e : k (l d) = l ((l⁻¹ * k * l) d) := by simp [MulAut.mul_apply]
      rw [e, h2]
    rw [map_mul, map_inv, h1, hd k hk]
  have hm : l d * d⁻¹ ∈ fixV (oTwoUpper L) ⊓ commV L := ⟨fun k hk => hwf k (hOK hk), hw⟩
  rw [h0] at hm
  exact mul_inv_eq_one.mp (Subgroup.mem_bot.mp hm)

omit [Finite W] in
theorem card_sup_of_inf {A B : Subgroup W} (h : A ⊓ B = ⊥) :
    Nat.card ↥(A ⊔ B) = Nat.card A * Nat.card B := by
  have e := B2F.card_sup_mul_card_inf_of_commute (A := A) (B := B) fun a _ b _ => mul_comm a b
  rwa [h, Subgroup.card_bot, mul_one] at e

omit [Finite W] in
theorem one_comp {L P : Subgroup (MulAut W)} (h : A5Comp L P)
    (hspan : fixV (oTwoUpper L) ⊔ commV L = ⊤) :
    Nat.card W ≤ 4 * Nat.card (fixV P) ∧ 16 * Nat.card (fixV (oTwoUpper L)) ≤ Nat.card W ∧
      ∀ B ≤ P, Nat.card B * Nat.card (fixV B) ≤ Nat.card W := by
  set D := fixV (oTwoUpper L) with hD
  set U := commV L with hU
  have h0 : D ⊓ U = ⊥ := h.fixV_oTwoUpper_inf
  have hW : Nat.card W = Nat.card D * 16 := by
    have e := card_sup_of_inf h0
    rw [hspan, Subgroup.card_top, h.card_commV] at e
    exact e
  have hfixD : ∀ l ∈ L, ∀ d ∈ D, l d = d := fix_fixV (le_normalizer_oTwoUpper L) le_rfl h0
  have hdec : ∀ B ≤ P, Nat.card (fixV B) = Nat.card D * Nat.card ↥(fixV B ⊓ U) := by
    intro B hBP
    have hBL := hBP.trans h.le
    have he : fixV B = D ⊔ (fixV B ⊓ U) := by
      apply le_antisymm
      · intro v hv
        have hv' : v ∈ D ⊔ U := by rw [hspan]; exact Subgroup.mem_top v
        obtain ⟨d, hd, u, hu, rfl⟩ := Subgroup.mem_sup.mp hv'
        refine Subgroup.mul_mem_sup hd ⟨fun x hx => ?_, hu⟩
        have h1 := hv x hx
        rw [map_mul, hfixD x (hBL hx) d hd] at h1
        exact mul_left_cancel h1
      · exact sup_le (fun d hd x hx => hfixD x (hBL hx) d hd) inf_le_left
    have hi : D ⊓ (fixV B ⊓ U) = ⊥ := eq_bot_iff.mpr fun x hx => h0 ▸ ⟨hx.1, hx.2.2⟩
    rw [he, card_sup_of_inf hi, ← he]
  refine ⟨?_, ?_, fun B hBP => ?_⟩
  · rw [hW, hdec P le_rfl, h.card_fixV_P]
    omega
  · rw [hW]
    omega
  · rw [hdec B hBP, hW]
    have := h.card_mul_card_le hBP
    calc Nat.card B * (Nat.card D * Nat.card ↥(fixV B ⊓ U)) =
        Nat.card D * (Nat.card B * Nat.card ↥(fixV B ⊓ U)) := by ring
      _ ≤ Nat.card D * 16 := Nat.mul_le_mul_left _ this

theorem two_comp {L₁ L₂ P₁ P₂ : Subgroup (MulAut W)} (h₁ : A5Comp L₁ P₁) (h₂ : A5Comp L₂ P₂)
    (hcomm : ∀ a ∈ L₁, ∀ b ∈ L₂, a * b = b * a) (hind : L₁ ⊓ L₂ = ⊥)
    (hspan : fixV (oTwoUpper L₁ ⊔ oTwoUpper L₂) ⊔ (commV L₁ ⊔ commV L₂) = ⊤)
    (hdir₁ : commV L₁ ⊓ (fixV (oTwoUpper L₁ ⊔ oTwoUpper L₂) ⊔ commV L₂) ≤
      fixV (oTwoUpper L₁ ⊔ oTwoUpper L₂))
    (hdir₂ : commV L₂ ⊓ (fixV (oTwoUpper L₁ ⊔ oTwoUpper L₂) ⊔ commV L₁) ≤
      fixV (oTwoUpper L₁ ⊔ oTwoUpper L₂)) :
    Nat.card W ≤ 16 * Nat.card (fixV (P₁ ⊔ P₂)) ∧
      256 * Nat.card (fixV (oTwoUpper L₁ ⊔ oTwoUpper L₂)) ≤ Nat.card W ∧
      ∀ B ≤ P₁ ⊔ P₂, Nat.card B * Nat.card (fixV B) ≤ Nat.card W := by
  set K := oTwoUpper L₁ ⊔ oTwoUpper L₂ with hK
  set D := fixV K with hD
  set U₁ := commV L₁ with hU₁
  set U₂ := commV L₂ with hU₂
  have hD₁ : D ⊓ U₁ = ⊥ := eq_bot_iff.mpr fun x hx =>
    h₁.fixV_oTwoUpper_inf ▸ ⟨fixV_anti le_sup_left hx.1, hx.2⟩
  have hD₂ : D ⊓ U₂ = ⊥ := eq_bot_iff.mpr fun x hx =>
    h₂.fixV_oTwoUpper_inf ▸ ⟨fixV_anti le_sup_right hx.1, hx.2⟩
  have hU : U₁ ⊓ U₂ = ⊥ := eq_bot_iff.mpr fun x hx => by
    have h1 : x ∈ D := hdir₁ ⟨hx.1, Subgroup.mem_sup_right hx.2⟩
    exact hD₁ ▸ ⟨h1, hx.1⟩
  have hDU : (D ⊔ U₁) ⊓ U₂ = ⊥ := eq_bot_iff.mpr fun x hx => by
    have h1 : x ∈ D := hdir₂ ⟨hx.2, hx.1⟩
    exact hD₂ ▸ ⟨h1, hx.2⟩
  have hW : Nat.card W = Nat.card D * 16 * 16 := by
    have e := card_sup_of_inf hDU
    rw [sup_assoc, hspan, Subgroup.card_top, card_sup_of_inf hD₁, h₁.card_commV,
      h₂.card_commV] at e
    exact e
  have hL₁K : L₁ ≤ Subgroup.normalizer (K : Set (MulAut W)) :=
    B2F.le_normalizer_sup (le_normalizer_oTwoUpper L₁) fun a ha =>
      Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun b hb =>
        (hcomm a ha b (oTwoUpper_le L₂ hb)).symm)
  have hL₂K : L₂ ≤ Subgroup.normalizer (K : Set (MulAut W)) :=
    B2F.le_normalizer_sup (fun b hb =>
      Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun a ha =>
        hcomm a (oTwoUpper_le L₁ ha) b hb)) (le_normalizer_oTwoUpper L₂)
  have hfixD₁ : ∀ l ∈ L₁, ∀ d ∈ D, l d = d :=
    fix_fixV hL₁K le_sup_left h₁.fixV_oTwoUpper_inf
  have hfixD₂ : ∀ l ∈ L₂, ∀ d ∈ D, l d = d :=
    fix_fixV hL₂K le_sup_right h₂.fixV_oTwoUpper_inf
  have hfixU₁ : ∀ l ∈ L₂, ∀ u ∈ U₁, l u = u := fun l hl u hu =>
    h₁.fix_of_commute (fun k hk => (hcomm k hk l hl).symm) hu
  have hfixU₂ : ∀ l ∈ L₁, ∀ u ∈ U₂, l u = u := fun l hl u hu =>
    h₂.fix_of_commute (fun k hk => hcomm l hl k hk) hu
  have hact : ∀ b ∈ L₁ ⊔ L₂, (∀ d ∈ D, b d = d) ∧ (∀ u ∈ U₁, b u ∈ U₁) ∧
      (∀ u ∈ U₂, b u ∈ U₂) := by
    intro b hb
    obtain ⟨l₁, hl₁, l₂, hl₂, rfl⟩ := exists_mul_of_mem_sup hcomm hb
    refine ⟨fun d hd => ?_, fun u hu => ?_, fun u hu => ?_⟩
    · rw [MulAut.mul_apply, hfixD₂ l₂ hl₂ d hd, hfixD₁ l₁ hl₁ d hd]
    · rw [MulAut.mul_apply, hfixU₁ l₂ hl₂ u hu]
      exact commV_invariant L₁ l₁ hl₁ u hu
    · rw [MulAut.mul_apply, hfixU₂ l₁ hl₁ _ (commV_invariant L₂ l₂ hl₂ u hu)]
      exact commV_invariant L₂ l₂ hl₂ u hu
  have hdec : ∀ B ≤ L₁ ⊔ L₂, Nat.card (fixV B) =
      Nat.card D * Nat.card ↥(fixV B ⊓ U₁) * Nat.card ↥(fixV B ⊓ U₂) := by
    intro B hBL
    have he : fixV B = D ⊔ (fixV B ⊓ U₁) ⊔ (fixV B ⊓ U₂) := by
      apply le_antisymm
      · intro v hv
        have hv' : v ∈ D ⊔ U₁ ⊔ U₂ := by rw [sup_assoc, hspan]; exact Subgroup.mem_top v
        obtain ⟨y, hy, u₂, hu₂, rfl⟩ := Subgroup.mem_sup.mp hv'
        obtain ⟨d, hd, u₁, hu₁, rfl⟩ := Subgroup.mem_sup.mp hy
        have key : ∀ x ∈ B, x u₁ = u₁ ∧ x u₂ = u₂ := by
          intro x hx
          obtain ⟨hxD, hxU₁, hxU₂⟩ := hact x (hBL hx)
          have h1 := hv x hx
          rw [map_mul, map_mul, hxD d hd, mul_assoc, mul_assoc] at h1
          have h2 := mul_left_cancel h1
          have h3 : x u₁ * u₁⁻¹ ∈ U₁ ⊓ U₂ := by
            refine ⟨U₁.mul_mem (hxU₁ u₁ hu₁) (U₁.inv_mem hu₁), ?_⟩
            have e : x u₁ * u₁⁻¹ = u₂ * (x u₂)⁻¹ := by
              calc x u₁ * u₁⁻¹ = (x u₁ * x u₂) * (x u₂)⁻¹ * u₁⁻¹ := by
                    rw [mul_inv_cancel_right]
                _ = (u₁ * u₂) * (x u₂)⁻¹ * u₁⁻¹ := by rw [h2]
                _ = u₂ * (x u₂)⁻¹ * (u₁ * u₁⁻¹) := by ac_rfl
                _ = u₂ * (x u₂)⁻¹ := by rw [mul_inv_cancel, mul_one]
            rw [e]
            exact U₂.mul_mem hu₂ (U₂.inv_mem (hxU₂ u₂ hu₂))
          rw [hU] at h3
          have h4 : x u₁ = u₁ := mul_inv_eq_one.mp (Subgroup.mem_bot.mp h3)
          refine ⟨h4, ?_⟩
          rw [h4] at h2
          exact mul_left_cancel h2
        refine Subgroup.mul_mem_sup (Subgroup.mul_mem_sup hd ⟨fun x hx => (key x hx).1, hu₁⟩)
          ⟨fun x hx => (key x hx).2, hu₂⟩
      · refine sup_le (sup_le (fun d hd x hx => (hact x (hBL hx)).1 d hd) inf_le_left)
          inf_le_left
    have hi₁ : D ⊓ (fixV B ⊓ U₁) = ⊥ := eq_bot_iff.mpr fun x hx => hD₁ ▸ ⟨hx.1, hx.2.2⟩
    have hi₂ : (D ⊔ (fixV B ⊓ U₁)) ⊓ (fixV B ⊓ U₂) = ⊥ := eq_bot_iff.mpr fun x hx =>
      hDU ▸ ⟨sup_le_sup_left inf_le_right D hx.1, hx.2.2⟩
    rw [he, card_sup_of_inf hi₂, card_sup_of_inf hi₁, ← he]
  have hP₁L := h₁.le
  have hP₂L := h₂.le
  have hPL : P₁ ⊔ P₂ ≤ L₁ ⊔ L₂ := sup_le_sup hP₁L hP₂L
  have hcommP : ∀ a ∈ P₁, ∀ b ∈ P₂, a * b = b * a := fun a ha b hb =>
    hcomm a (hP₁L ha) b (hP₂L hb)
  have hXcomm : ∀ x ∈ P₁ ⊔ P₂, ∀ y ∈ P₁ ⊔ P₂, x * y = y * x := by
    intro x hx y hy
    obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_of_mem_sup hcommP hx
    obtain ⟨a', ha', b', hb', rfl⟩ := exists_mul_of_mem_sup hcommP hy
    have e1 := h₁.comm a ha a' ha'
    have e2 := h₂.comm b hb b' hb'
    have e3 := hcommP a ha b' hb'
    have e4 := hcommP a' ha' b hb
    calc a * b * (a' * b') = a * (b * a') * b' := by group
      _ = a * (a' * b) * b' := by rw [← e4]
      _ = (a * a') * (b * b') := by group
      _ = (a' * a) * (b' * b) := by rw [e1, e2]
      _ = a' * (a * b') * b := by group
      _ = a' * (b' * a) * b := by rw [e3]
      _ = a' * b' * (a * b) := by group
  refine ⟨?_, ?_, fun B hBP => ?_⟩
  ·
    have h1 : fixV P₁ ⊓ U₁ ≤ fixV (P₁ ⊔ P₂) ⊓ U₁ := fun u hu =>
      ⟨mem_fixV_sup hu.1 fun x hx => hfixU₁ x (hP₂L hx) u hu.2, hu.2⟩
    have h2 : fixV P₂ ⊓ U₂ ≤ fixV (P₁ ⊔ P₂) ⊓ U₂ := fun u hu =>
      ⟨mem_fixV_sup (fun x hx => hfixU₂ x (hP₁L hx) u hu.2) hu.1, hu.2⟩
    have c1 := Subgroup.card_le_of_le h1
    have c2 := Subgroup.card_le_of_le h2
    rw [h₁.card_fixV_P] at c1
    rw [h₂.card_fixV_P] at c2
    rw [hW, hdec _ hPL]
    have := Nat.mul_le_mul c1 c2
    nlinarith
  · rw [hW]
    omega
  ·
    set B₁ := B ⊓ P₁ with hB₁
    set B₂ := (B ⊔ P₁) ⊓ P₂ with hB₂
    have hBP₁ : ∀ a ∈ B, ∀ b ∈ P₁, a * b = b * a := fun a ha b hb =>
      hXcomm a (hBP ha) b (Subgroup.mem_sup_left hb)
    have e1 := B2F.card_sup_mul_card_inf_of_commute hBP₁
    have hmod : B ⊔ P₁ = B₂ ⊔ P₁ := by
      apply le_antisymm
      · refine sup_le (fun b hb => ?_) le_sup_right
        obtain ⟨p₁, hp₁, p₂, hp₂, rfl⟩ := exists_mul_of_mem_sup hcommP (hBP hb)
        have hp₂B : p₂ ∈ B₂ := by
          refine ⟨?_, hp₂⟩
          have e : p₂ = p₁⁻¹ * (p₁ * p₂) := by group
          rw [e]
          exact Subgroup.mul_mem _ (Subgroup.mem_sup_right (P₁.inv_mem hp₁))
            (Subgroup.mem_sup_left hb)
        exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hp₁) (Subgroup.mem_sup_left hp₂B)
      · exact sup_le inf_le_left le_sup_right
    have hB₂P₁ : B₂ ⊓ P₁ = ⊥ := by
      rw [eq_bot_iff, ← hind]
      exact fun x hx => ⟨hP₁L hx.2, hP₂L hx.1.2⟩
    have hB₂comm : ∀ a ∈ B₂, ∀ b ∈ P₁, a * b = b * a := fun a ha b hb =>
      (hcommP b hb a ha.2).symm
    have e2 := B2F.card_sup_mul_card_inf_of_commute hB₂comm
    rw [hB₂P₁, Subgroup.card_bot, mul_one, ← hmod] at e2
    have hP₁4 := h₁.card_P
    have hcardB : Nat.card B = Nat.card B₁ * Nat.card B₂ := by
      rw [e2] at e1
      have : Nat.card B₂ * Nat.card P₁ * Nat.card B₁ = Nat.card B * Nat.card P₁ := by
        rw [← e1]
      rw [hP₁4] at this
      nlinarith
    have hf₁ : fixV B ⊓ U₁ ≤ fixV B₁ ⊓ U₁ := inf_le_inf_right _ (fixV_anti inf_le_left)
    have hf₂ : fixV B ⊓ U₂ ≤ fixV B₂ ⊓ U₂ := by
      intro u hu
      refine ⟨fun x hx => ?_, hu.2⟩
      have h1 : u ∈ fixV (B ⊔ P₁) :=
        mem_fixV_sup hu.1 fun y hy => hfixU₂ y (hP₁L hy) u hu.2
      exact h1 x hx.1
    have c1 := h₁.card_mul_card_le (inf_le_right : B₁ ≤ P₁)
    have c2 := h₂.card_mul_card_le (inf_le_right : B₂ ≤ P₂)
    have d1 := Subgroup.card_le_of_le hf₁
    have d2 := Subgroup.card_le_of_le hf₂
    rw [hdec B (hBP.trans hPL), hcardB, hW]
    calc Nat.card B₁ * Nat.card B₂ *
        (Nat.card D * Nat.card ↥(fixV B ⊓ U₁) * Nat.card ↥(fixV B ⊓ U₂)) ≤
        Nat.card B₁ * Nat.card B₂ *
          (Nat.card D * Nat.card ↥(fixV B₁ ⊓ U₁) * Nat.card ↥(fixV B₂ ⊓ U₂)) := by
          gcongr
      _ = Nat.card D * (Nat.card B₁ * Nat.card ↥(fixV B₁ ⊓ U₁)) *
          (Nat.card B₂ * Nat.card ↥(fixV B₂ ⊓ U₂)) := by ring
      _ ≤ Nat.card D * 16 * 16 := by gcongr

omit [Finite W] in
theorem gen_two {L₁ L₂ P₁ P₂ : Subgroup (MulAut W)} (h₁ : A5Comp L₁ P₁) (h₂ : A5Comp L₂ P₂)
    (hcomm : ∀ a ∈ L₁, ∀ b ∈ L₂, a * b = b * a) :
    ∃ g ∈ oTwoUpper L₁ ⊔ oTwoUpper L₂,
      L₁ ⊔ L₂ ≤ (P₁ ⊔ P₂) ⊔ B1.conjAut g (P₁ ⊔ P₂) := by
  obtain ⟨g₁, hg₁, hL₁⟩ := h₁.exists_gen
  obtain ⟨g₂, hg₂, hL₂⟩ := h₂.exists_gen
  have hg₁L : g₁ ∈ L₁ := oTwoUpper_le L₁ hg₁
  have hg₂L : g₂ ∈ L₂ := oTwoUpper_le L₂ hg₂
  refine ⟨g₁ * g₂, Subgroup.mul_mem _ (Subgroup.mem_sup_left hg₁) (Subgroup.mem_sup_right hg₂),
    sup_le (hL₁.trans (sup_le_sup le_sup_left ?_)) (hL₂.trans (sup_le_sup le_sup_right ?_))⟩
  · intro y hy
    rw [B1.mem_conjAut] at hy ⊢
    have hP₁L := h₁.le
    have hc : g₂⁻¹ * (g₁⁻¹ * y * g₁) * g₂ = g₁⁻¹ * y * g₁ := by
      have e := hcomm _ (hP₁L hy) _ hg₂L
      calc g₂⁻¹ * (g₁⁻¹ * y * g₁) * g₂ = g₂⁻¹ * ((g₁⁻¹ * y * g₁) * g₂) := by group
        _ = g₂⁻¹ * (g₂ * (g₁⁻¹ * y * g₁)) := by rw [e]
        _ = g₁⁻¹ * y * g₁ := by group
    have e2 : (g₁ * g₂)⁻¹ * y * (g₁ * g₂) = g₂⁻¹ * (g₁⁻¹ * y * g₁) * g₂ := by group
    rw [e2, hc]
    exact Subgroup.mem_sup_left hy
  · intro y hy
    rw [B1.mem_conjAut] at hy ⊢
    have hP₂L := h₂.le
    have hyL : y ∈ L₂ := by
      have e : y = g₂ * (g₂⁻¹ * y * g₂) * g₂⁻¹ := by group
      rw [e]
      exact L₂.mul_mem (L₂.mul_mem hg₂L (hP₂L hy)) (L₂.inv_mem hg₂L)
    have hc : g₁⁻¹ * y * g₁ = y := by
      have e := hcomm _ hg₁L _ hyL
      calc g₁⁻¹ * y * g₁ = g₁⁻¹ * (y * g₁) := by group
        _ = g₁⁻¹ * (g₁ * y) := by rw [e]
        _ = y := by group
    have e2 : (g₁ * g₂)⁻¹ * y * (g₁ * g₂) = g₂⁻¹ * (g₁⁻¹ * y * g₁) * g₂ := by group
    rw [e2, hc]
    exact Subgroup.mem_sup_right hy

theorem counts {I : Finset (Subgroup (MulAut W))} {P : Subgroup (MulAut W) → Subgroup (MulAut W)}
    (hI : I.card = 1 ∨ I.card = 2)
    (hcomm : ∀ L ∈ I, ∀ L' ∈ I, L ≠ L' → ∀ a ∈ L, ∀ b ∈ L', a * b = b * a)
    (hind : ∀ L ∈ I, L ⊓ ⨆ L' ∈ I, ⨆ (_ : L' ≠ L), L' = ⊥)
    (hc : ∀ L ∈ I, A5Comp L (P L))
    (hspan : fixV (⨆ L ∈ I, oTwoUpper L) ⊔ ⨆ L ∈ I, commV L = ⊤)
    (hdir : ∀ L ∈ I, commV L ⊓
        (fixV (⨆ L ∈ I, oTwoUpper L) ⊔ ⨆ L' ∈ I, ⨆ (_ : L' ≠ L), commV L') ≤
      fixV (⨆ L ∈ I, oTwoUpper L)) :
    Nat.card W * Nat.card (fixV (⨆ L ∈ I, oTwoUpper L)) ≤
        Nat.card (fixV (⨆ L ∈ I, P L)) ^ 2 ∧
      (∀ B ≤ ⨆ L ∈ I, P L, Nat.card B * Nat.card (fixV B) ≤ Nat.card W) ∧
      ∃ g ∈ ⨆ L ∈ I, oTwoUpper L,
        (⨆ L ∈ I, L) ≤ (⨆ L ∈ I, P L) ⊔ B1.conjAut g (⨆ L ∈ I, P L) := by
  classical
  rcases card_cases hI with ⟨L, rfl⟩ | ⟨L₁, L₂, hne, rfl⟩
  · simp only [Finset.iSup_singleton] at hspan ⊢
    have hcL := hc L (Finset.mem_singleton_self L)
    obtain ⟨hA, hB, hC⟩ := one_comp hcL hspan
    refine ⟨?_, hC, hcL.exists_gen⟩
    nlinarith
  · have h1 : L₁ ∈ ({L₁, L₂} : Finset (Subgroup (MulAut W))) := Finset.mem_insert_self _ _
    have h2 : L₂ ∈ ({L₁, L₂} : Finset (Subgroup (MulAut W))) :=
      Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
    have hdir₁ := hdir L₁ h1
    have hdir₂ := hdir L₂ h2
    have hind₁ := hind L₁ h1
    have e₁ : ∀ {β : Type _} [CompleteLattice β] (f : Subgroup (MulAut W) → β),
        (⨆ L' ∈ ({L₁, L₂} : Finset (Subgroup (MulAut W))), ⨆ (_ : L' ≠ L₁), f L') = f L₂ := by
      intro β _ f
      rw [Finset.iSup_insert, Finset.iSup_singleton]
      simp [Ne.symm hne]
    have e₂ : ∀ {β : Type _} [CompleteLattice β] (f : Subgroup (MulAut W) → β),
        (⨆ L' ∈ ({L₁, L₂} : Finset (Subgroup (MulAut W))), ⨆ (_ : L' ≠ L₂), f L') = f L₁ := by
      intro β _ f
      rw [Finset.iSup_insert, Finset.iSup_singleton]
      simp [hne]
    rw [e₁] at hdir₁ hind₁
    rw [e₂] at hdir₂
    simp only [Finset.iSup_insert, Finset.iSup_singleton] at hspan hdir₁ hdir₂ ⊢
    have hc₁ := hc L₁ h1
    have hc₂ := hc L₂ h2
    have hcomm' := hcomm L₁ h1 L₂ h2 hne
    obtain ⟨hA, hB, hC⟩ := two_comp hc₁ hc₂ hcomm' hind₁ hspan hdir₁ hdir₂
    refine ⟨?_, hC, gen_two hc₁ hc₂ hcomm'⟩
    nlinarith

end Global

end CFSG.Quasithin.Ch3n317Ker
