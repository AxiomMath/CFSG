module

public import CFSG.LocalAnalysis.StandardType.GGTableBExcTwoFusionKey

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley TableBExc TableBExc.Three
  TableBExcTwoFusion

namespace TableBExcTwoTB

@[expose] def rootPairing (τ : Tag) (α : Fin τ.rank → ℤ) (x : Fin τ.rank → ZMod 3) : ZMod 3 :=
  ∑ k, ((∑ j, τ.cartan k j * α j : ℤ) : ZMod 3) * x k

@[expose] def HalfOffender (τ : Tag) (S : Subgroup (WeylGroup τ)) : Prop :=
  ∀ A : Subgroup (WeylGroup τ), A ≤ S → IsElemAbelian 3 A → A ≠ ⊥ →
    3 ^ (τ.rank - 1) ≤ Nat.card A *
      Nat.card {x : Fin τ.rank → ZMod 3 // ∀ a ∈ A, torusAct τ 3 a x = x} →
    ∃ w : WeylGroup τ, A = Subgroup.zpowers w ∧
      w ∈ Subgroup.closure {r : WeylGroup τ | ∃ (u : WeylGroup τ) (j : Fin τ.rank),
        (∀ x : Fin τ.rank → ZMod 3, (∀ a ∈ A, torusAct τ 3 a x = x) →
          rootPairing τ (u • (Pi.single j 1 : Fin τ.rank → ℤ)) x = 0) ∧
        r = u * simple τ j * u⁻¹}

theorem rootPairing_eq_zero_of_fixed {τ : Tag} (ω : List (Fin τ.rank)) (α : Fin τ.rank → ℤ)
    (μ : Fin τ.rank → ZMod 3)
    (h : ∀ j : Fin τ.rank, rootPairing τ α (Pi.single j 1) =
      ∑ r, μ r * (torusWord τ 3 ω (Pi.single j 1) r - if r = j then 1 else 0))
    {x : Fin τ.rank → ZMod 3} (hx : torusWord τ 3 ω x = x) : rootPairing τ α x = 0 := by
  let f : (Fin τ.rank → ZMod 3) →ₗ[ZMod 3] ZMod 3 :=
    { toFun := rootPairing τ α
      map_add' := fun u v => by
        simp only [rootPairing, Pi.add_apply, mul_add, Finset.sum_add_distrib]
      map_smul' := fun c u => by
        simp only [rootPairing, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by ring }
  let Λ : (Fin τ.rank → ZMod 3) →ₗ[ZMod 3] ZMod 3 :=
    ∑ j, μ j • (LinearMap.proj (R := ZMod 3) (φ := fun _ : Fin τ.rank => ZMod 3) j)
  let W : (Fin τ.rank → ZMod 3) →ₗ[ZMod 3] (Fin τ.rank → ZMod 3) := torusWordLin τ 3 ω
  have hfg : f + Λ = Λ.comp W := by
    refine LinearMap.pi_ext' fun b => LinearMap.ext_ring ?_
    have hb := h b
    simp only [LinearMap.add_apply, LinearMap.coe_comp, Function.comp_apply,
      LinearMap.coe_single, f, Λ, W, torusWordLin_apply, LinearMap.coe_mk, AddHom.coe_mk,
      LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.coe_proj, Function.eval,
      smul_eq_mul, Pi.single_apply] at hb ⊢
    show rootPairing τ α (Pi.single b 1) + _ = _
    rw [hb, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hx' := congrArg (fun L => L x) hfg
  simp only [LinearMap.add_apply, LinearMap.coe_comp, Function.comp_apply, W,
    torusWordLin_apply, hx] at hx'
  have : rootPairing τ α x + Λ x = Λ x := hx'
  simpa using this

section Words

theorem wordProd_smul_foldr {τ : Tag} (ω : List (Fin τ.rank)) (v : Fin τ.rank → ℤ) :
    (coxeterSystem τ).wordProd ω • v = ω.foldr (fun i v => reflect τ i v) v := by
  induction ω with
  | nil => simp
  | cons i ω ih =>
    rw [CoxeterSystem.wordProd_cons, mul_smul, ih, simple_smul]
    rfl

theorem palindrome_mem_closure {τ : Tag} {C : Set (Fin τ.rank → ZMod 3)} (u : List (Fin τ.rank))
    (j : Fin τ.rank)
    (h : ∀ x ∈ C,
      rootPairing τ ((coxeterSystem τ).wordProd u • (Pi.single j 1 : Fin τ.rank → ℤ)) x = 0) :
    (coxeterSystem τ).wordProd (u ++ [j] ++ u.reverse) ∈
      Subgroup.closure {r : WeylGroup τ | ∃ (u' : WeylGroup τ) (j' : Fin τ.rank),
        (∀ x ∈ C, rootPairing τ (u' • (Pi.single j' 1 : Fin τ.rank → ℤ)) x = 0) ∧
          r = u' * simple τ j' * u'⁻¹} := by
  rw [CoxeterSystem.wordProd_append, CoxeterSystem.wordProd_append,
    CoxeterSystem.wordProd_reverse, CoxeterSystem.wordProd_singleton]
  exact Subgroup.subset_closure ⟨_, j, h, rfl⟩

end Words

section Key

variable {n : ℕ} {π : Equiv.Perm (Fin n)} {hπ : π ^ 3 = 1} {M : Type*} [Group M] {V : Type*}
  [Finite V] (ρ : M →* Equiv.Perm V) (F : Model π hπ →* M)

theorem card_mul_fixAllCard_lt_or_zpowers {T B₁ B₅ m : ℕ}
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
      ∃ i, A = Subgroup.zpowers (SemidirectProduct.inl (.ofAdd (Pi.single i 1))) ∧
        Nat.card A ≤ 3 ∧
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
      have hgA : g ∈ A := by
        rcases hyg with h | h
        · exact h ▸ hyA
        · have : g = y ^ 2 := by
            rw [h, ← pow_mul, show 2 * 2 = 3 + 1 by norm_num, pow_add, hg3, one_mul, pow_one]
          exact this ▸ pow_mem hyA 2
      have hyzg : y ∈ Subgroup.zpowers g := by
        rcases hyg with h | h
        · exact h ▸ Subgroup.mem_zpowers g
        · exact h ▸ pow_mem (Subgroup.mem_zpowers g) 2
      have hAeq : A = Subgroup.zpowers g := le_antisymm
        (hAy.trans ((Subgroup.zpowers_le).mpr hyzg)) ((Subgroup.zpowers_le).mpr hgA)
      refine ⟨i, hAeq, hcardA, ?_, ?_⟩
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
theorem card_mul_card_fix_lt_or_zpowers_of_model (hF : Function.Injective F) {T : ℕ}
    (hKey : ∀ A' : Subgroup (Model π hπ), (∀ y ∈ A', y ^ 3 = 1) →
      (∀ y ∈ A', ∀ z ∈ A', y * z = z * y) → A' ≠ ⊥ →
      Nat.card A' * fixAllCard ρ F A' < T ∨
        ∃ i, A' = Subgroup.zpowers (SemidirectProduct.inl (.ofAdd (Pi.single i 1))) ∧
          Nat.card A' ≤ 3 ∧
          fixAllCard ρ F A' ≤ fixCard ρ F (SemidirectProduct.inl (.ofAdd (Pi.single i 1))) ∧
          ∀ x, ρ (F (SemidirectProduct.inl (.ofAdd (Pi.single i 1)))) x = x →
            ∀ y ∈ A', ρ (F y) x = x)
    {A : Subgroup M} (hAS : A ≤ F.range) (hA : IsElemAbelian 3 A) (hA1 : A ≠ ⊥) :
    Nat.card A * Nat.card {x : V // ∀ a ∈ A, ρ a x = x} < T ∨
      ∃ i, A = Subgroup.zpowers (F (SemidirectProduct.inl (.ofAdd (Pi.single i 1)))) ∧
        Nat.card A ≤ 3 ∧
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
  rcases hK with h | ⟨i, h0, h1, h2, h3⟩
  · exact Or.inl h
  · refine Or.inr ⟨i, ?_, h1, h2, fun x hx a ha => ?_⟩
    · rw [← hmap, h0, MonoidHom.map_zpowers]
    · obtain ⟨y, rfl⟩ := hAS ha
      exact h3 x hx y ha

end Key

end TableBExcTwoTB

end CFSG.StandardType

end
