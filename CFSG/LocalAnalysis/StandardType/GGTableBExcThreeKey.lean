module

public import CFSG.LocalAnalysis.StandardType.GGTableBExcThreeModel

public section

namespace CFSG.StandardType

namespace TableBExc.Three

variable {n : ℕ} {π : Equiv.Perm (Fin n)} {hπ : π ^ 3 = 1}

theorem finite_model : Finite (Model π hπ) :=
  Finite.of_equiv _ SemidirectProduct.equivProd.symm

section Fix

variable {M : Type*} [Group M] {V : Type*} (ρ : M →* Equiv.Perm V) (F : Model π hπ →* M)

@[expose] noncomputable def fixCard (y : Model π hπ) : ℕ := Nat.card {x : V // ρ (F y) x = x}

@[expose] noncomputable def fixAllCard (A : Subgroup (Model π hπ)) : ℕ :=
  Nat.card {x : V // ∀ y ∈ A, ρ (F y) x = x}

theorem fixAllCard_le [Finite V] {A : Subgroup (Model π hπ)} {y : Model π hπ} (hy : y ∈ A) :
    fixAllCard ρ F A ≤ fixCard ρ F y :=
  Nat.card_le_card_of_injective (fun x => ⟨x.1, x.2 y hy⟩) fun a b hab =>
    Subtype.ext (by simpa using congrArg Subtype.val hab)

omit [Group M] in
theorem perm_conj_apply_eq_iff (a b : Equiv.Perm V) (x : V) :
    (b * a * b⁻¹) x = x ↔ a (b⁻¹ x) = b⁻¹ x := by
  rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply]
  constructor
  · intro h
    conv_rhs => rw [← h]
    simp
  · intro h
    rw [h]
    simp

theorem fixCard_conj (z y : Model π hπ) : fixCard ρ F (z * y * z⁻¹) = fixCard ρ F y := by
  have key : ∀ x : V, ρ (F (z * y * z⁻¹)) x = x ↔ ρ (F y) ((ρ (F z))⁻¹ x) = (ρ (F z))⁻¹ x :=
    fun x => by rw [map_mul, map_mul, map_inv, map_mul, map_mul, map_inv, perm_conj_apply_eq_iff]
  exact Nat.card_congr
    { toFun := fun x => ⟨(ρ (F z))⁻¹ x.1, (key x.1).mp x.2⟩
      invFun := fun x => ⟨ρ (F z) x.1, (key _).mpr (by simpa using x.2)⟩
      left_inv := fun x => Subtype.ext (by simp)
      right_inv := fun x => Subtype.ext (by simp) }

theorem fixAllCard_map_conj (A : Subgroup (Model π hπ)) (z : Model π hπ) :
    fixAllCard ρ F (A.map (MulAut.conj z).toMonoidHom) = fixAllCard ρ F A := by
  have key : ∀ (x : V) (y : Model π hπ), ρ (F ((MulAut.conj z).toMonoidHom y)) x = x ↔
      ρ (F y) ((ρ (F z))⁻¹ x) = (ρ (F z))⁻¹ x := fun x y => by
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul, map_mul, map_inv, map_mul, map_mul,
      map_inv, perm_conj_apply_eq_iff]
  exact Nat.card_congr
    { toFun := fun x => ⟨(ρ (F z))⁻¹ x.1, fun y hy => (key x.1 y).mp (x.2 _ ⟨y, hy, rfl⟩)⟩
      invFun := fun x => ⟨ρ (F z) x.1, by
        rintro _ ⟨y, hy, rfl⟩
        exact (key _ y).mpr (by simpa using x.2 y hy)⟩
      left_inv := fun x => Subtype.ext (by simp)
      right_inv := fun x => Subtype.ext (by simp) }

theorem fixCard_sq {y : Model π hπ} (hy : y ^ 3 = 1) : fixCard ρ F (y ^ 2) = fixCard ρ F y := by
  have hs : (ρ (F y)) ^ 3 = 1 := by rw [← map_pow, ← map_pow, hy, map_one, map_one]
  refine Nat.card_congr (Equiv.subtypeEquivRight fun x => ?_)
  rw [map_pow, map_pow]
  constructor
  · intro h
    calc ρ (F y) x = ρ (F y) ((ρ (F y) ^ 2) x) := by rw [h]
      _ = (ρ (F y) ^ 3) x := by rw [pow_succ' (ρ (F y)) 2]; rfl
      _ = x := by rw [hs]; rfl
  · intro h
    rw [pow_two, Equiv.Perm.mul_apply, h, h]

end Fix

section Comp

theorem left_cube (v : Multiplicative (Fin n → ZMod 3)) :
    ((⟨v, .ofAdd 1⟩ : Model π hπ) ^ 3).left = v * shiftAut π v * (shiftAut π ^ 2) v := by
  rw [pow_succ, pow_two, SemidirectProduct.mul_left, SemidirectProduct.mul_left,
    SemidirectProduct.mul_right, phi_ofAdd_one, ← ofAdd_add,
    show (1 + 1 : ZMod 3) = 2 from rfl, phi_ofAdd_two]

theorem inl_conj_eq (w v : Multiplicative (Fin n → ZMod 3)) :
    SemidirectProduct.inl w * (⟨v, .ofAdd 1⟩ : Model π hπ) * (SemidirectProduct.inl w)⁻¹ =
      ⟨w * v * (shiftAut π w)⁻¹, .ofAdd 1⟩ := by
  refine SemidirectProduct.ext ?_ ?_
  · simp only [SemidirectProduct.mul_left, SemidirectProduct.mul_right, SemidirectProduct.inv_left,
      SemidirectProduct.left_inl, SemidirectProduct.right_inl, map_one, MulAut.one_apply, one_mul,
      phi_ofAdd_one]
    exact congrArg _ (map_inv (shiftAut π) w)
  · simp [SemidirectProduct.mul_right, SemidirectProduct.inv_right]

theorem inr_conj_inl (k : ℕ) (v : Multiplicative (Fin n → ZMod 3)) :
    SemidirectProduct.inr (.ofAdd (k : ZMod 3)) * SemidirectProduct.inl v *
        (SemidirectProduct.inr (.ofAdd (k : ZMod 3)))⁻¹ =
      (SemidirectProduct.inl ((shiftAut π ^ k) v) : Model π hπ) := by
  rw [← map_inv, ← SemidirectProduct.inl_aut, phi_ofAdd_natCast]

theorem shiftAut_eq_of_comm {v w : Multiplicative (Fin n → ZMod 3)}
    (h : (⟨w, 1⟩ : Model π hπ) * ⟨v, .ofAdd 1⟩ = ⟨v, .ofAdd 1⟩ * ⟨w, 1⟩) : shiftAut π w = w := by
  have h1 := congrArg SemidirectProduct.left h
  rw [SemidirectProduct.mul_left, SemidirectProduct.mul_left, map_one, MulAut.one_apply,
    phi_ofAdd_one, mul_comm w v] at h1
  exact (mul_left_cancel h1).symm

end Comp

theorem nsmul_single (k : ℕ) (i : Fin n) (a : ZMod 3) :
    k • (Pi.single i a : Fin n → ZMod 3) = Pi.single i ((k : ZMod 3) * a) := by
  funext t
  by_cases ht : t = i
  · subst ht
    simp [nsmul_eq_mul]
  · simp [ht]

@[expose] def supp (v : Multiplicative (Fin n → ZMod 3)) : Finset (Fin n) :=
  Finset.univ.filter fun i => v.toAdd i ≠ 0

theorem mem_supp {v : Multiplicative (Fin n → ZMod 3)} {i : Fin n} :
    i ∈ supp v ↔ v.toAdd i ≠ 0 := by
  simp [supp]

theorem two_le_card_supp {v : Multiplicative (Fin n → ZMod 3)} {i j : Fin n} (hij : i ≠ j)
    (hi : v.toAdd i ≠ 0) (hj : v.toAdd j ≠ 0) : 2 ≤ (supp v).card := by
  have hsub : ({i, j} : Finset (Fin n)) ⊆ supp v := by
    intro k hk
    rcases Finset.mem_insert.mp hk with rfl | hk
    · exact mem_supp.mpr hi
    · rw [Finset.mem_singleton.mp hk]
      exact mem_supp.mpr hj
  calc 2 = ({i, j} : Finset (Fin n)).card := (Finset.card_pair hij).symm
    _ ≤ _ := Finset.card_le_card hsub

theorem eq_single_of_supp {v : Multiplicative (Fin n → ZMod 3)} {i : Fin n}
    (h : supp v = {i}) : v = .ofAdd (Pi.single i (v.toAdd i)) := by
  apply Multiplicative.toAdd.injective
  funext j
  rw [toAdd_ofAdd]
  by_cases hj : j = i
  · subst hj
    simp
  · rw [Pi.single_eq_of_ne hj]
    by_contra hne
    have : j ∈ supp v := mem_supp.mpr hne
    rw [h, Finset.mem_singleton] at this
    exact hj this

section Key

variable {M : Type*} [Group M] {V : Type*} [Finite V] (ρ : M →* Equiv.Perm V)
  (F : Model π hπ →* M)

theorem exists_right_eq_ofAdd_one {A : Subgroup (Model π hπ)} {y : Model π hπ} (hy : y ∈ A)
    (hy1 : y.right ≠ 1) : ∃ y₁ ∈ A, y₁.right = .ofAdd 1 := by
  obtain ⟨m, hm⟩ := Multiplicative.ofAdd.surjective y.right
  have hm0 : m ≠ 0 := fun h0 => hy1 (by rw [← hm, h0, ofAdd_zero])
  have h12 : ∀ m : ZMod 3, m ≠ 0 → m = 1 ∨ m = 2 := by decide
  rcases h12 m hm0 with rfl | rfl
  · exact ⟨y, hy, hm.symm⟩
  · refine ⟨y ^ 2, pow_mem hy 2, ?_⟩
    rw [pow_two, SemidirectProduct.mul_right, ← hm, ← ofAdd_add]
    exact congrArg _ (by decide)

theorem card_le_of_right_eq {A : Subgroup (Model π hπ)} (hAc : ∀ y ∈ A, ∀ z ∈ A, y * z = z * y)
    {y₁ : Model π hπ} (hy₁ : y₁ ∈ A) (hr : y₁.right = .ofAdd 1) {K₁ : ℕ}
    (hK : Nat.card {w : Multiplicative (Fin n → ZMod 3) // shiftAut π w = w} ≤ K₁) :
    Nat.card A ≤ 3 * K₁ := by
  have := finite_model (π := π) (hπ := hπ)
  set r : A →* Multiplicative (ZMod 3) := SemidirectProduct.rightHom.comp A.subtype
  have h1 := TableB.card_range_mul_card_ker r
  have h2 : Nat.card r.range ≤ 3 := by
    calc Nat.card r.range ≤ Nat.card (Multiplicative (ZMod 3)) := Subgroup.card_le_card_group _
      _ = 3 := by rw [Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
  have hker : ∀ z : r.ker, ((z : A) : Model π hπ).right = 1 := fun z => z.2
  have h3 : Nat.card r.ker ≤ K₁ := by
    refine le_trans (Nat.card_le_card_of_injective
      (fun z : r.ker => (⟨((z : A) : Model π hπ).left, ?_⟩ :
        {w : Multiplicative (Fin n → ZMod 3) // shiftAut π w = w})) ?_) hK
    · apply shiftAut_eq_of_comm (v := y₁.left)
      have e1 : ((z : A) : Model π hπ) = ⟨((z : A) : Model π hπ).left, 1⟩ :=
        SemidirectProduct.ext rfl (hker z)
      have e2 : y₁ = ⟨y₁.left, .ofAdd 1⟩ := SemidirectProduct.ext rfl hr
      rw [← e1, ← e2]
      exact hAc _ (z : A).2 _ hy₁
    · intro a b hab
      have hab' : ((a : A) : Model π hπ).left = ((b : A) : Model π hπ).left :=
        congrArg Subtype.val hab
      exact Subtype.ext (Subtype.ext (SemidirectProduct.ext hab' ((hker a).trans (hker b).symm)))
  calc Nat.card A = Nat.card r.range * Nat.card r.ker := h1.symm
    _ ≤ 3 * K₁ := Nat.mul_le_mul h2 h3

theorem eq_inl_of_right_eq_one {y : Model π hπ} (hy : y.right = 1) :
    y = SemidirectProduct.inl y.left :=
  SemidirectProduct.ext rfl hy

theorem card_range_inl :
    Nat.card (SemidirectProduct.inl : Multiplicative (Fin n → ZMod 3) →* Model π hπ).range =
      3 ^ n := by
  rw [← Nat.card_congr (MonoidHom.ofInjective SemidirectProduct.inl_injective).toEquiv,
    Nat.card_congr Multiplicative.toAdd, Nat.card_fun, Nat.card_zmod, Nat.card_fin]

theorem card_mul_fixAllCard_lt {T B₁ B₂ B₃ B₄ K₁ : ℕ}
    (h₁ : ∀ v : Multiplicative (Fin n → ZMod 3), v * shiftAut π v * (shiftAut π ^ 2) v = 1 →
      ∃ w, fixCard ρ F ⟨w * v * (shiftAut π w)⁻¹, .ofAdd 1⟩ ≤ B₁)
    (hK : Nat.card {w : Multiplicative (Fin n → ZMod 3) // shiftAut π w = w} ≤ K₁)
    (h₂ : ∀ v, 2 ≤ (supp v).card → fixCard ρ F (SemidirectProduct.inl v) ≤ B₂)
    (h₃ : ∀ i, fixCard ρ F (SemidirectProduct.inl (.ofAdd (Pi.single i 1))) ≤ B₃)
    (h₄ : Nat.card {x : V // ∀ v, ρ (F (SemidirectProduct.inl v)) x = x} ≤ B₄)
    (hT₁ : 3 * K₁ * B₁ < T) (hT₂ : 3 ^ n * B₂ < 3 * T) (hT₃ : 3 * B₃ < T)
    (hT₄ : 3 ^ n * B₄ < T) {A : Subgroup (Model π hπ)} (hA3 : ∀ y ∈ A, y ^ 3 = 1)
    (hAc : ∀ y ∈ A, ∀ z ∈ A, y * z = z * y) (hA : A ≠ ⊥) :
    Nat.card A * fixAllCard ρ F A < T := by
  classical
  have := finite_model (π := π) (hπ := hπ)
  by_cases hI : ∃ y ∈ A, y.right ≠ 1
  ·
    obtain ⟨y, hyA, hy1⟩ := hI
    obtain ⟨y₁, hy₁A, hy₁⟩ := exists_right_eq_ofAdd_one hyA hy1
    have he : y₁ = ⟨y₁.left, .ofAdd 1⟩ := SemidirectProduct.ext rfl hy₁
    have hv3 : y₁.left * shiftAut π y₁.left * (shiftAut π ^ 2) y₁.left = 1 := by
      rw [← left_cube (hπ := hπ), ← he, hA3 y₁ hy₁A, SemidirectProduct.one_left]
    obtain ⟨w, hw⟩ := h₁ _ hv3
    have hcardA := card_le_of_right_eq hAc hy₁A hy₁ hK
    have hfix : fixAllCard ρ F A ≤ B₁ := by
      rw [← fixAllCard_map_conj ρ F A (SemidirectProduct.inl w)]
      refine le_trans (fixAllCard_le ρ F ⟨y₁, hy₁A, rfl⟩) ?_
      rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      rw [he, inl_conj_eq]
      exact hw
    calc Nat.card A * fixAllCard ρ F A ≤ (3 * K₁) * B₁ := Nat.mul_le_mul hcardA hfix
      _ < T := hT₁
  ·
    push Not at hI
    set Ninl := (SemidirectProduct.inl : Multiplicative (Fin n → ZMod 3) →* Model π hπ).range
    have hAN : A ≤ Ninl := fun y hy => ⟨y.left, (eq_inl_of_right_eq_one (hI y hy)).symm⟩
    by_cases hII : ∃ y ∈ A, 2 ≤ (supp y.left).card
    · obtain ⟨y, hyA, hy2⟩ := hII
      have hfix : fixAllCard ρ F A ≤ B₂ := by
        refine le_trans (fixAllCard_le ρ F hyA) ?_
        rw [eq_inl_of_right_eq_one (hI y hyA)]
        exact h₂ _ hy2
      by_cases hfull : A = Ninl
      · have hcard : Nat.card A = 3 ^ n := by rw [hfull, card_range_inl]
        have hfix4 : fixAllCard ρ F A ≤ B₄ := by
          refine le_of_eq_of_le (Nat.card_congr (Equiv.subtypeEquivRight fun x => ?_)) h₄
          rw [hfull]
          constructor
          · intro h v
            exact h _ ⟨v, rfl⟩
          · rintro h _ ⟨v, rfl⟩
            exact h v
        calc Nat.card A * fixAllCard ρ F A ≤ 3 ^ n * B₄ := by
              rw [hcard]
              exact Nat.mul_le_mul_left _ hfix4
          _ < T := hT₄
      · have hdvd : Nat.card A ∣ 3 ^ n := card_range_inl (π := π) (hπ := hπ) ▸
          Subgroup.card_dvd_of_le hAN
        have hne : Nat.card A ≠ 3 ^ n := fun h => hfull
          (Subgroup.eq_of_le_of_card_ge hAN (by rw [h, card_range_inl]))
        obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
        have hk3 : 3 * Nat.card A ≤ 3 ^ n := by
          have hkn : k < n := lt_of_le_of_ne hk fun h => hne (by rw [hk', h])
          rw [hk', ← pow_succ']
          exact Nat.pow_le_pow_right (by norm_num) hkn
        have : 3 * (Nat.card A * fixAllCard ρ F A) < 3 * T :=
          calc 3 * (Nat.card A * fixAllCard ρ F A) = (3 * Nat.card A) * fixAllCard ρ F A := by
                ring
            _ ≤ 3 ^ n * B₂ := Nat.mul_le_mul hk3 hfix
            _ < 3 * T := hT₂
        omega
    · push Not at hII
      obtain ⟨⟨y, hyA⟩, hy1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hA
      have hyl : y.left ≠ 1 := fun h => hy1 (Subtype.ext (show y = 1 by
        rw [eq_inl_of_right_eq_one (hI y hyA), h, map_one]))
      obtain ⟨i, hi⟩ : ∃ i, y.left.toAdd i ≠ 0 := by
        by_contra hcon
        push Not at hcon
        exact hyl (Multiplicative.toAdd.injective (funext hcon))
      have hsupp : supp y.left = {i} :=
        (Finset.eq_of_subset_of_card_le (Finset.singleton_subset_iff.mpr (mem_supp.mpr hi))
          (by rw [Finset.card_singleton]; have := hII y hyA; omega)).symm
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
            (by rw [Finset.card_singleton]; have := hII z hz; omega)).symm
        by_cases hji : j = i
        · subst hji
          have hk : ∀ a b : ZMod 3, a ≠ 0 → b ≠ 0 → b = ((1 : ℕ) : ZMod 3) * a ∨
              b = ((2 : ℕ) : ZMod 3) * a := by decide
          have hk' : ∃ k : ℕ, z.left.toAdd j = (k : ZMod 3) * a := by
            rcases hk a (z.left.toAdd j) hi hj with h | h
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
          have := hII _ (mul_mem hyA hz)
          omega
      have hcardA : Nat.card A ≤ 3 := by
        have hfinz : Finite (Subgroup.zpowers y) := inferInstance
        calc Nat.card A ≤ Nat.card (Subgroup.zpowers y) := Subgroup.card_le_of_le hAy
          _ = orderOf y := Nat.card_zpowers y
          _ ≤ 3 := orderOf_le_of_pow_eq_one (by norm_num) (hA3 y hyA)
      have hfix : fixAllCard ρ F A ≤ B₃ := by
        refine le_trans (fixAllCard_le ρ F hyA) ?_
        have h12 : ∀ a : ZMod 3, a ≠ 0 → a = 1 ∨ a = 2 := by decide
        rcases h12 a hi with h1 | h1
        · rw [hy, h1]
          exact h₃ i
        · have e : SemidirectProduct.inl (.ofAdd (Pi.single i a)) =
              (SemidirectProduct.inl (.ofAdd (Pi.single i 1)) : Model π hπ) ^ 2 := by
            rw [← map_pow]
            congr 1
            apply Multiplicative.toAdd.injective
            rw [toAdd_pow, toAdd_ofAdd, toAdd_ofAdd, nsmul_single, h1]
            rfl
          rw [hy, e, fixCard_sq ρ F (by rw [← map_pow]; exact
            (by rw [← map_one SemidirectProduct.inl]; congr 1; exact
              CFSG.RankThree.CentralCover.pow_eq_one_of_zmod _))]
          exact h₃ i
      calc Nat.card A * fixAllCard ρ F A ≤ 3 * B₃ := Nat.mul_le_mul hcardA hfix
        _ < T := hT₃

omit [Finite V] in
theorem fixCard_inl_le_of_rot {v : Multiplicative (Fin n → ZMod 3)} {B : ℕ} (k e : ℕ)
    (he : e = 1 ∨ e = 2)
    (h : fixCard ρ F (SemidirectProduct.inl ((shiftAut π ^ k) (v ^ e))) ≤ B) :
    fixCard ρ F (SemidirectProduct.inl v) ≤ B := by
  have h3 : (SemidirectProduct.inl v : Model π hπ) ^ 3 = 1 := by
    rw [← map_pow, CFSG.RankThree.CentralCover.pow_eq_one_of_zmod, map_one]
  have h1 : fixCard ρ F (SemidirectProduct.inl v) =
      fixCard ρ F ((SemidirectProduct.inl v : Model π hπ) ^ e) := by
    rcases he with rfl | rfl
    · rw [pow_one]
    · exact (fixCard_sq ρ F h3).symm
  rw [h1, ← fixCard_conj ρ F (SemidirectProduct.inr (.ofAdd (k : ZMod 3))), ← map_pow,
    inr_conj_inl]
  exact h

omit [Finite V] in
theorem card_mul_card_fix_lt_of_model (hF : Function.Injective F) {T : ℕ}
    (hKey : ∀ A' : Subgroup (Model π hπ), (∀ y ∈ A', y ^ 3 = 1) →
      (∀ y ∈ A', ∀ z ∈ A', y * z = z * y) → A' ≠ ⊥ → Nat.card A' * fixAllCard ρ F A' < T)
    {A : Subgroup M} (hAS : A ≤ F.range) (hA : CFSG.Assembly.IsElemAbelian 3 A) (hA1 : A ≠ ⊥) :
    Nat.card A * Nat.card {x : V // ∀ a ∈ A, ρ a x = x} < T := by
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
  rw [← hcard, ← hfix]
  refine hKey _ (fun y hy => hF ?_) (fun y hy z hz => hF ?_) fun hbot => hA1 ?_
  · rw [map_pow, map_one]
    exact hA.2 _ hy
  · rw [map_mul, map_mul]
    exact TableB.IsElemAbelian.comm hA hy hz
  · rw [← hmap, hbot, Subgroup.map_bot]

end Key

theorem fixCard_torusPerm_eq {τ : CFSG.Blueprint.Chevalley.Tag}
    (hsymm : ∀ i j, τ.cartan i j = τ.cartan j i)
    (F : Model π hπ →* CFSG.LieType.Chevalley.WeylGroup τ) (y : Model π hπ)
    (ω : List (Fin τ.rank)) (h : F y = (CFSG.LieType.Chevalley.coxeterSystem τ).wordProd ω) :
    fixCard (torusPerm τ 3) F y = Nat.card {x : Fin τ.rank → ZMod 3 // torusWord τ 3 ω x = x} := by
  refine Nat.card_congr (Equiv.subtypeEquivRight fun x => ?_)
  rw [torusPerm_apply, h, torusWord_eq_torusAct hsymm]

end TableBExc.Three

end CFSG.StandardType
