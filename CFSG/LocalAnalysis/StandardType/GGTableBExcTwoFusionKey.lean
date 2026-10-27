module

public import CFSG.LocalAnalysis.StandardType.GGTableBExcThreeKey

public section

namespace CFSG.StandardType

open CFSG.Assembly TableBExc.Three

namespace TableBExcTwoFusion

variable {n : ℕ} {π : Equiv.Perm (Fin n)} {hπ : π ^ 3 = 1}

theorem zmod3_eq_one_or_two : ∀ a : ZMod 3, a ≠ 0 → a = 1 ∨ a = 2 := by decide

theorem zmod3_eq_mul : ∀ a b : ZMod 3, a ≠ 0 → b ≠ 0 →
    b = ((1 : ℕ) : ZMod 3) * a ∨ b = ((2 : ℕ) : ZMod 3) * a := by decide

section Key

variable {M : Type*} [Group M] {V : Type*} [Finite V] (ρ : M →* Equiv.Perm V)
  (F : Model π hπ →* M)

omit [Finite V] in
theorem fix_of_mem_zpowers {y z : Model π hπ} (hz : z ∈ Subgroup.zpowers y) {x : V}
    (hx : ρ (F y) x = x) : ρ (F z) x = x := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
  rw [map_zpow, map_zpow]
  exact Equiv.Perm.zpow_apply_eq_self_of_apply_eq_self hx k

theorem card_mul_fixAllCard_lt_or_single {T B₁ B₅ m : ℕ}
    (h₁ : ∀ v : Multiplicative (Fin n → ZMod 3), v * shiftAut π v * (shiftAut π ^ 2) v = 1 →
      ∃ w, fixCard ρ F ⟨w * v * (shiftAut π w)⁻¹, .ofAdd 1⟩ ≤ B₁)
    (hK : Nat.card {w : Multiplicative (Fin n → ZMod 3) // shiftAut π w = w} ≤ 3 ^ m)
    (h₅ : Nat.card {x : V // ∀ w : Multiplicative (Fin n → ZMod 3), shiftAut π w = w →
      ρ (F (SemidirectProduct.inl w)) x = x} ≤ B₅)
    (hII : ∀ A : Subgroup (Model π hπ), (∀ y ∈ A, y.right = 1) → (∀ y ∈ A, y ^ 3 = 1) →
      (∀ y ∈ A, ∀ z ∈ A, y * z = z * y) → (∃ y ∈ A, 2 ≤ (supp y.left).card) →
      Nat.card A * fixAllCard ρ F A < T)
    (hT₁ : 3 ^ m * B₁ < T) (hT₅ : 3 * 3 ^ m * B₅ < T) {A : Subgroup (Model π hπ)}
    (hA3 : ∀ y ∈ A, y ^ 3 = 1) (hAc : ∀ y ∈ A, ∀ z ∈ A, y * z = z * y) (hA : A ≠ ⊥) :
    Nat.card A * fixAllCard ρ F A < T ∨
      ∃ i, Nat.card A ≤ 3 ∧
        fixAllCard ρ F A ≤ fixCard ρ F (SemidirectProduct.inl (.ofAdd (Pi.single i 1))) ∧
        ∀ x, ρ (F (SemidirectProduct.inl (.ofAdd (Pi.single i 1)))) x = x →
          ∀ y ∈ A, ρ (F y) x = x := by
  classical
  have := finite_model (π := π) (hπ := hπ)
  have := Fact.mk Nat.prime_three
  by_cases hI : ∃ y ∈ A, y.right ≠ 1
  ·
    left
    obtain ⟨y, hyA, hy1⟩ := hI
    obtain ⟨y₁, hy₁A, hy₁⟩ := exists_right_eq_ofAdd_one hyA hy1
    have he : y₁ = ⟨y₁.left, .ofAdd 1⟩ := SemidirectProduct.ext rfl hy₁
    have hv3 : y₁.left * shiftAut π y₁.left * (shiftAut π ^ 2) y₁.left = 1 := by
      rw [← left_cube (hπ := hπ), ← he, hA3 y₁ hy₁A, SemidirectProduct.one_left]
    set r : A →* Multiplicative (ZMod 3) := SemidirectProduct.rightHom.comp A.subtype with hr
    have h1 := TableB.card_range_mul_card_ker r
    have h2 : Nat.card r.range ≤ 3 := by
      calc Nat.card r.range ≤ Nat.card (Multiplicative (ZMod 3)) := Subgroup.card_le_card_group _
        _ = 3 := by rw [Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
    have hker : ∀ z : r.ker, ((z : A) : Model π hπ).right = 1 := fun z => z.2
    let ι : r.ker → {w : Multiplicative (Fin n → ZMod 3) // shiftAut π w = w} := fun z =>
      ⟨((z : A) : Model π hπ).left, by
        apply shiftAut_eq_of_comm (v := y₁.left)
        have e1 : ((z : A) : Model π hπ) = ⟨((z : A) : Model π hπ).left, 1⟩ :=
          SemidirectProduct.ext rfl (hker z)
        rw [← e1, ← he]
        exact hAc _ (z : A).2 _ hy₁A⟩
    have hι : Function.Injective ι := by
      intro a b hab
      have hab' : ((a : A) : Model π hπ).left = ((b : A) : Model π hπ).left :=
        congrArg Subtype.val hab
      exact Subtype.ext (Subtype.ext (SemidirectProduct.ext hab' ((hker a).trans (hker b).symm)))
    by_cases hfull : ∀ w : {w : Multiplicative (Fin n → ZMod 3) // shiftAut π w = w},
        (SemidirectProduct.inl w.1 : Model π hπ) ∈ A
    ·
      have hcardA : Nat.card A ≤ 3 * 3 ^ m := by
        have h3 : Nat.card r.ker ≤ 3 ^ m := (Nat.card_le_card_of_injective ι hι).trans hK
        calc Nat.card A = Nat.card r.range * Nat.card r.ker := h1.symm
          _ ≤ 3 * 3 ^ m := Nat.mul_le_mul h2 h3
      have hfix : fixAllCard ρ F A ≤ B₅ := by
        refine le_trans (Nat.card_le_card_of_injective
          (fun x => (⟨x.1, fun w hw => x.2 _ (hfull ⟨w, hw⟩)⟩ : {x : V //
            ∀ w : Multiplicative (Fin n → ZMod 3), shiftAut π w = w →
              ρ (F (SemidirectProduct.inl w)) x = x}))
          fun a b hab => Subtype.ext (by simpa using congrArg Subtype.val hab)) h₅
      calc Nat.card A * fixAllCard ρ F A ≤ (3 * 3 ^ m) * B₅ := Nat.mul_le_mul hcardA hfix
        _ < T := hT₅
    ·
      push Not at hfull
      obtain ⟨w₀, hw₀⟩ := hfull
      have hlt : Nat.card r.ker < 3 ^ m := by
        refine lt_of_lt_of_le ?_ hK
        by_contra hcon
        obtain ⟨z, hz⟩ := (hι.bijective_of_nat_card_le (not_lt.mp hcon)).2 w₀
        apply hw₀
        have hz' : ((z : A) : Model π hπ) = SemidirectProduct.inl w₀.1 :=
          SemidirectProduct.ext (congrArg Subtype.val hz) (hker z)
        rw [← hz']
        exact (z : A).2
      have hpk : IsPGroup 3 r.ker := fun z => ⟨1, by
        rw [pow_one]
        exact Subtype.ext (Subtype.ext (hA3 _ (z : A).2))⟩
      obtain ⟨j, hj⟩ := (IsPGroup.iff_card).mp hpk
      have hjm : 3 * Nat.card r.ker ≤ 3 ^ m := by
        rw [hj] at hlt ⊢
        rw [← pow_succ']
        exact Nat.pow_le_pow_right (by norm_num) ((Nat.pow_lt_pow_iff_right (by norm_num)).mp hlt)
      have hcardA : Nat.card A ≤ 3 ^ m := by
        calc Nat.card A = Nat.card r.range * Nat.card r.ker := h1.symm
          _ ≤ 3 * Nat.card r.ker := Nat.mul_le_mul_right _ h2
          _ ≤ 3 ^ m := hjm
      obtain ⟨w, hw⟩ := h₁ _ hv3
      have hfix : fixAllCard ρ F A ≤ B₁ := by
        rw [← fixAllCard_map_conj ρ F A (SemidirectProduct.inl w)]
        refine le_trans (fixAllCard_le ρ F ⟨y₁, hy₁A, rfl⟩) ?_
        rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, he, inl_conj_eq]
        exact hw
      calc Nat.card A * fixAllCard ρ F A ≤ 3 ^ m * B₁ := Nat.mul_le_mul hcardA hfix
        _ < T := hT₁
  ·
    push Not at hI
    by_cases hII' : ∃ y ∈ A, 2 ≤ (supp y.left).card
    · exact Or.inl (hII A hI hA3 hAc hII')
    · right
      push Not at hII'
      obtain ⟨⟨y, hyA⟩, hy1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hA
      have hyl : y.left ≠ 1 := fun h => hy1 (Subtype.ext (show y = 1 by
        rw [eq_inl_of_right_eq_one (hI y hyA), h, map_one]))
      obtain ⟨i, hi⟩ : ∃ i, y.left.toAdd i ≠ 0 := by
        by_contra hcon
        push Not at hcon
        exact hyl (Multiplicative.toAdd.injective (funext hcon))
      have hsupp : supp y.left = {i} :=
        (Finset.eq_of_subset_of_card_le (Finset.singleton_subset_iff.mpr (mem_supp.mpr hi))
          (by rw [Finset.card_singleton]; have := hII' y hyA; omega)).symm
      set a := y.left.toAdd i with ha
      have hy : y = SemidirectProduct.inl (.ofAdd (Pi.single i a)) := by
        rw [eq_inl_of_right_eq_one (hI y hyA), ← eq_single_of_supp hsupp]
      have hAy : A ≤ Subgroup.zpowers y := by
        intro z hz
        have hzl : z = SemidirectProduct.inl z.left := eq_inl_of_right_eq_one (hI z hz)
        by_cases hz1 : z.left = 1
        · rw [hzl, hz1, map_one]
          exact one_mem _
        obtain ⟨j, hj⟩ : ∃ j, z.left.toAdd j ≠ 0 := by
          by_contra hcon
          push Not at hcon
          exact hz1 (Multiplicative.toAdd.injective (funext hcon))
        have hzsupp : supp z.left = {j} :=
          (Finset.eq_of_subset_of_card_le (Finset.singleton_subset_iff.mpr (mem_supp.mpr hj))
            (by rw [Finset.card_singleton]; have := hII' z hz; omega)).symm
        by_cases hji : j = i
        · subst hji
          have hk' : ∃ k : ℕ, z.left.toAdd j = (k : ZMod 3) * a := by
            rcases zmod3_eq_mul a (z.left.toAdd j) hi hj with h | h
            · exact ⟨1, h⟩
            · exact ⟨2, h⟩
          obtain ⟨k, hk⟩ := hk'
          refine ⟨k, ?_⟩
          show y ^ (k : ℤ) = z
          rw [zpow_natCast, hy, hzl, ← map_pow, eq_single_of_supp hzsupp, hk]
          congr 1
          apply Multiplicative.toAdd.injective
          rw [toAdd_pow, toAdd_ofAdd, toAdd_ofAdd, nsmul_single]
        · exfalso
          have hyz : (y * z).left = y.left * z.left := by
            rw [SemidirectProduct.mul_left, hI y hyA, map_one, MulAut.one_apply]
          have h2 : 2 ≤ (supp (y * z).left).card := by
            refine two_le_card_supp (Ne.symm hji) ?_ ?_
            · rw [hyz, toAdd_mul, Pi.add_apply]
              have : z.left.toAdd i = 0 := by
                by_contra hne
                have : i ∈ supp z.left := mem_supp.mpr hne
                rw [hzsupp, Finset.mem_singleton] at this
                exact hji this.symm
              rw [this, add_zero]
              exact hi
            · rw [hyz, toAdd_mul, Pi.add_apply]
              have : y.left.toAdd j = 0 := by
                by_contra hne
                have : j ∈ supp y.left := mem_supp.mpr hne
                rw [hsupp, Finset.mem_singleton] at this
                exact hji this
              rw [this, zero_add]
              exact hj
          have := hII' _ (mul_mem hyA hz)
          omega
      have hcardA : Nat.card A ≤ 3 := by
        calc Nat.card A ≤ Nat.card (Subgroup.zpowers y) := Subgroup.card_le_of_le hAy
          _ = orderOf y := Nat.card_zpowers y
          _ ≤ 3 := orderOf_le_of_pow_eq_one (by norm_num) (hA3 y hyA)
      set g := (SemidirectProduct.inl (.ofAdd (Pi.single i 1)) : Model π hπ) with hg
      have hyg : y = g ∨ y = g ^ 2 := by
        rcases zmod3_eq_one_or_two a hi with h1 | h1
        · left
          rw [hy, h1]
        · right
          rw [hy, hg, ← map_pow]
          congr 1
          apply Multiplicative.toAdd.injective
          rw [toAdd_pow, toAdd_ofAdd, toAdd_ofAdd, nsmul_single, h1]
          rfl
      have hg3 : g ^ 3 = 1 := by
        rw [hg, ← map_pow, CFSG.RankThree.CentralCover.pow_eq_one_of_zmod, map_one]
      refine ⟨i, hcardA, ?_, ?_⟩
      · refine le_trans (fixAllCard_le ρ F hyA) ?_
        rcases hyg with h | h
        · rw [h]
        · rw [h, fixCard_sq ρ F hg3]
      · intro x hx z hz
        have hyx : ρ (F y) x = x := by
          rcases hyg with h | h
          · rw [h]
            exact hx
          · rw [h, map_pow, map_pow]
            exact Equiv.Perm.pow_apply_eq_self_of_apply_eq_self hx 2
        exact fix_of_mem_zpowers ρ F (hAy hz) hyx

omit [Finite V] in
theorem card_mul_card_fix_lt_or_single_of_model (hF : Function.Injective F) {T : ℕ}
    (hKey : ∀ A' : Subgroup (Model π hπ), (∀ y ∈ A', y ^ 3 = 1) →
      (∀ y ∈ A', ∀ z ∈ A', y * z = z * y) → A' ≠ ⊥ →
      Nat.card A' * fixAllCard ρ F A' < T ∨
        ∃ i, Nat.card A' ≤ 3 ∧
          fixAllCard ρ F A' ≤ fixCard ρ F (SemidirectProduct.inl (.ofAdd (Pi.single i 1))) ∧
          ∀ x, ρ (F (SemidirectProduct.inl (.ofAdd (Pi.single i 1)))) x = x →
            ∀ y ∈ A', ρ (F y) x = x)
    {A : Subgroup M} (hAS : A ≤ F.range) (hA : IsElemAbelian 3 A) (hA1 : A ≠ ⊥) :
    Nat.card A * Nat.card {x : V // ∀ a ∈ A, ρ a x = x} < T ∨
      ∃ i, Nat.card A ≤ 3 ∧
        Nat.card {x : V // ∀ a ∈ A, ρ a x = x} ≤
          fixCard ρ F (SemidirectProduct.inl (.ofAdd (Pi.single i 1))) ∧
        ∀ x, ρ (F (SemidirectProduct.inl (.ofAdd (Pi.single i 1)))) x = x →
          ∀ a ∈ A, ρ a x = x := by
  have hmap : (A.comap F).map F = A := Subgroup.map_comap_eq_self hAS
  have hcard : Nat.card (A.comap F) = Nat.card A := by
    conv_rhs => rw [← hmap]
    exact (Subgroup.card_map_of_injective hF).symm
  have hfix : fixAllCard ρ F (A.comap F) = Nat.card {x : V // ∀ a ∈ A, ρ a x = x} := by
    refine Nat.card_congr (Equiv.subtypeEquivRight fun x => ?_)
    constructor
    · intro h a ha
      obtain ⟨y, rfl⟩ := hAS ha
      exact h y ha
    · intro h y hy
      exact h (F y) hy
  have hK := hKey (A.comap F) (fun y hy => hF (by rw [map_pow, map_one]; exact hA.2 _ hy))
    (fun y hy z hz => hF (by rw [map_mul, map_mul]; exact TableB.IsElemAbelian.comm hA hy hz))
    (fun hbot => hA1 (by rw [← hmap, hbot, Subgroup.map_bot]))
  rw [hcard, hfix] at hK
  rcases hK with h | ⟨i, h1, h2, h3⟩
  · exact Or.inl h
  · refine Or.inr ⟨i, h1, h2, fun x hx a ha => ?_⟩
    obtain ⟨y, rfl⟩ := hAS ha
    exact h3 x hx y ha

end Key

end TableBExcTwoFusion

end CFSG.StandardType
