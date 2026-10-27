module

public import CFSG.Quasithin.Background.SmithB42LnL4Datum

public section

namespace CFSG.Quasithin.B42Ln

open Matrix CFSG.Quasithin.SmithCurtis

theorem one_ne_x4 (s : Fin 3) : (1 : G4) ≠ x4 s := fun h => x4_ne_one s h.symm

abbrev x4X (s : Fin 3) : ↥(X4 s) := ⟨x4 s, Or.inr rfl⟩

theorem card_X4 (s : Fin 3) : Nat.card ↥(X4 s) = 2 := by
  classical
  have e : ↥(X4 s) ≃ Bool :=
    { toFun := fun x => decide ((x : G4) = x4 s)
      invFun := fun b => if b then x4X s else 1
      left_inv := fun x => by
        rcases mem_X4_cases x.2 with h | h
        · have h' : (x : G4) ≠ x4 s := fun h2 => one_ne_x4 s (h.symm.trans h2)
          simp only [h', decide_false, Bool.false_eq_true, ↓reduceIte]
          exact Subtype.ext h.symm
        · simp only [h, decide_true, ↓reduceIte]
          exact Subtype.ext h.symm
      right_inv := fun b => by
        cases b
        · simp only [Bool.false_eq_true, ↓reduceIte, OneMemClass.coe_one, decide_eq_false_iff_not]
          exact one_ne_x4 s
        · simp }
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_bool]

theorem sum_X4 {M : Type*} [AddCommMonoid M] (s : Fin 3) [Fintype ↥(X4 s)]
    (f : ↥(X4 s) → M) : ∑ x, f x = f 1 + f (x4X s) := by
  refine Fintype.sum_eq_add 1 (x4X s) (fun h => one_ne_x4 s (congrArg Subtype.val h))
    fun x hx => ?_
  rcases mem_X4_cases x.2 with h | h
  · exact absurd (Subtype.ext h) hx.1
  · exact absurd (Subtype.ext h) hx.2

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] (ρ : Representation (ZMod 2) G4 V)

theorem heckeT4 (s : Fin 3) (v : V) :
    datum4.heckeT ρ s v = ρ (n4 s) v + ρ (x4 s * n4 s) v := by
  have : Fintype ↥(datum4.X s) := Fintype.ofFinite _
  rw [datum4.heckeT_apply ρ s v]
  have h := @sum_X4 V _ s this (fun x => ρ ((x : G4) * n4 s) v)
  rw [OneMemClass.coe_one, one_mul] at h
  exact h

theorem card_datum4_X (s : Fin 3) : Nat.card ↥(datum4.X s) = 2 := card_X4 s

theorem sum_erase_X4_const {M : Type*} [AddCommMonoid M] (s : Fin 3) (m : M)
    (inst : Fintype ↥(datum4.X s)) (dec : DecidableEq ↥(datum4.X s)) :
    @Finset.sum _ _ _ (@Finset.erase _ dec (@Finset.univ _ inst) 1) (fun _ => m) = m := by
  rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
    ← Nat.card_eq_fintype_card, card_datum4_X]
  simp

theorem dScalar4 (χ : G4 → ZMod 2) (s : Fin 3) : datum4.dScalar χ s = χ 1 := by
  classical
  unfold CurtisDatum.dScalar
  dsimp only
  simp only [show ∀ x, datum4.phi s x = 1 from fun _ => rfl]
  exact sum_erase_X4_const s (χ 1) _ _

theorem d'Scalar4 (χ : G4 → ZMod 2) (s : Fin 3) : datum4.d'Scalar χ s = χ 1 := by
  classical
  unfold CurtisDatum.d'Scalar
  dsimp only
  simp only [show ∀ x, datum4.psi s x = 1 from fun _ => rfl]
  exact sum_erase_X4_const s (χ 1) _ _

abbrev IsType4 (y : V) (μ : Fin 3 → ZMod 2) : Prop := datum4.IsCurtisType ρ y (fun _ => 1) μ

theorem splitOver4 : SplitOver (ZMod 2) (datum4.H) := by
  intro h hh
  rw [datum4_H, Subgroup.mem_bot] at hh
  exact ⟨1, by rw [hh, one_pow], [1], by simp⟩

theorem isType4_of_isCurtisType {y : V} {χ : G4 → ZMod 2} {μ : Fin 3 → ZMod 2}
    (ht : datum4.IsCurtisType ρ y χ μ) : IsType4 ρ y μ := by
  refine ⟨ht.1, ht.2.1, fun h hh => ?_, ht.2.2.2⟩
  rw [datum4_H, Subgroup.mem_bot] at hh
  rw [hh, map_one, one_smul]
  rfl

theorem exists_isType4 [Finite V] {ρ : Representation (ZMod 2) G4 V} (hρ : IsSimpleRep ρ) :
    ∃ y : V, ∃ μ : Fin 3 → ZMod 2, IsType4 ρ y μ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨y, χ, μ, ht⟩ := datum4.exists_isCurtisType splitOver4 hρ
  exact ⟨y, μ, isType4_of_isCurtisType ρ ht⟩

theorem mu_eq_zero_or_one {y : V} {μ : Fin 3 → ZMod 2} (ht : IsType4 ρ y μ) (s : Fin 3) :
    μ s = 0 ∨ μ s = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases ht.mu_eq s with h | h
  · exact Or.inl h
  · exact Or.inr (h.trans (d'Scalar4 _ s))

theorem mu_eq_zero_of_fixed {y : V} {μ : Fin 3 → ZMod 2} (ht : IsType4 ρ y μ) {s : Fin 3}
    (hs : ρ (n4 s) y = y) : μ s = 0 := by
  have h := ht.2.2.2 s
  rw [heckeT4, hs, map_mul, Module.End.mul_apply, hs, ht.1 (x4 s) (x4_mem s)] at h
  have h2 : μ s • y = 0 := by
    rw [← h, ← two_smul (ZMod 2) y, show (2 : ZMod 2) = 0 from rfl, zero_smul]
  exact (smul_eq_zero.1 h2).resolve_right ht.2.1

@[expose] def coinv4 (μ : Fin 3 → ZMod 2) (ω : List (Fin 3)) : ZMod 2 :=
  (ω.map fun s => μ s - 1).prod

theorem form_nW4 {f : Module.Dual (ZMod 2) V} (hf : ∀ z ∈ augSub ρ L4, f z = 0) {y : V}
    {μ : Fin 3 → ZMod 2} (ht : IsType4 ρ y μ) (hfy : f y = 1) {ω : List (Fin 3)}
    (hω : cs4.IsReduced ω) : f (ρ (nW4 (cs4.wordProd ω)) y) = coinv4 μ ω := by
  have h1 := datum4.coinv_formula ρ hω ht.1
  rw [datum4.coinvOp_eigen ρ ht.2.2.1 ht.2.2.2] at h1
  have h2 := hf _ h1
  rw [map_sub, map_smul, hfy, smul_eq_mul, mul_one] at h2
  have h3 := eq_of_sub_eq_zero h2
  rw [show datum4.nW (cs4.wordProd ω) = nW4 (cs4.wordProd ω) from rfl] at h3
  rw [h3]
  unfold CurtisDatum.coinvScalar coinv4
  congr 1
  refine List.map_congr_left fun s _ => ?_
  rw [dScalar4]

theorem coinv4_eq_zero {μ : Fin 3 → ZMod 2} {ω : List (Fin 3)} {s : Fin 3} (hs : s ∈ ω)
    (hμ : μ s = 1) : coinv4 μ ω = 0 := by
  apply List.prod_eq_zero
  rw [List.mem_map]
  exact ⟨s, hs, by rw [hμ, sub_self]⟩

theorem piW4_wordProd (ω : List (Fin 3)) : piW4 (cs4.wordProd ω) = (ω.map sw).prod := by
  induction ω with
  | nil => rw [CoxeterSystem.wordProd_nil, map_one, List.map_nil, List.prod_nil]
  | cons s ω ih =>
    rw [CoxeterSystem.wordProd_cons, map_mul, piW4_simple, ih, List.map_cons, List.prod_cons]

theorem prod_sw_of_forall {c : Fin 3} {ω : List (Fin 3)} (h : ∀ s ∈ ω, s = c) :
    (ω.map sw).prod = 1 ∨ (ω.map sw).prod = sw c := by
  induction ω with
  | nil => exact Or.inl rfl
  | cons s ω ih =>
    rw [h s List.mem_cons_self, List.map_cons, List.prod_cons]
    rcases ih fun t ht => h t (List.mem_cons_of_mem _ ht) with h1 | h1
    · rw [h1, mul_one]
      exact Or.inr rfl
    · rw [h1, sw_mul_self]
      exact Or.inl rfl

@[expose] def cosetW : Fin 3 → Fin 12 → List (Fin 3) :=
  ![![[], [1], [2], [0, 1], [1, 2], [2, 1], [0, 1, 2], [0, 2, 1], [1, 2, 1], [0, 1, 2, 1],
      [1, 0, 2, 1], [0, 1, 0, 2, 1]],
    ![[], [0], [2], [0, 2], [1, 0], [1, 2], [0, 1, 2], [1, 0, 2], [2, 1, 0], [0, 1, 0, 2],
      [1, 2, 1, 0], [0, 1, 2, 1, 0]],
    ![[], [0], [1], [0, 1], [1, 0], [2, 1], [0, 1, 0], [0, 2, 1], [2, 1, 0], [0, 2, 1, 0],
      [1, 0, 2, 1], [1, 0, 2, 1, 0]]]

theorem cosetW_spec : ∀ (c : Fin 3) (i j : Fin 12), i ≠ j →
    ((cosetW c j).map sw).prod⁻¹ * ((cosetW c i).map sw).prod ≠ 1 ∧
      ((cosetW c j).map sw).prod⁻¹ * ((cosetW c i).map sw).prod ≠ sw c := by
  decide

theorem exists_third : ∀ a b : Fin 3, a ≠ b → ∃ c : Fin 3, ∀ s : Fin 3, s ≠ a → s ≠ b → s = c := by
  decide

theorem form_cosetW {f : Module.Dual (ZMod 2) V} (hf : ∀ z ∈ augSub ρ L4, f z = 0) {y : V}
    {μ : Fin 3 → ZMod 2} (ht : IsType4 ρ y μ) (hfy : f y = 1) {a b c : Fin 3}
    (ha : μ a = 1) (hb : μ b = 1) (hc : ∀ s : Fin 3, s ≠ a → s ≠ b → s = c) (i j : Fin 12) :
    f (ρ (nW4 (cs4.wordProd (cosetW c j)))⁻¹ (ρ (nW4 (cs4.wordProd (cosetW c i))) y)) =
      if i = j then 1 else 0 := by
  rw [← map_inv, ← Module.End.mul_apply, ← map_mul, ← map_mul]
  obtain ⟨ω, hω, hw⟩ := cs4.exists_isReduced
    ((cs4.wordProd (cosetW c j))⁻¹ * cs4.wordProd (cosetW c i))
  rw [hw, form_nW4 ρ hf ht hfy hω]
  split_ifs with hij
  · subst hij
    rw [inv_mul_cancel] at hw
    have h0 : ω = [] := by
      have := hω
      rw [CoxeterSystem.IsReduced, ← hw, CoxeterSystem.length_one] at this
      exact List.eq_nil_of_length_eq_zero this.symm
    rw [h0]
    rfl
  · by_contra hne
    apply (cosetW_spec c i j hij).elim
    have hall : ∀ s ∈ ω, s = c := by
      intro s hs
      refine hc s (fun h => hne ?_) (fun h => hne ?_)
      · exact coinv4_eq_zero (h ▸ hs) ha
      · exact coinv4_eq_zero (h ▸ hs) hb
    have hπ := congrArg piW4 hw
    rw [map_mul, map_inv, piW4_wordProd, piW4_wordProd, piW4_wordProd] at hπ
    rw [hπ]
    rcases prod_sw_of_forall hall with h1 | h1
    · exact fun h2 _ => h2 h1
    · exact fun _ h3 => h3 h1

theorem twelve_le_finrank [Finite V] {ρ : Representation (ZMod 2) G4 V} (hρ : IsSimpleRep ρ)
    {y : V} {μ : Fin 3 → ZMod 2} (ht : IsType4 ρ y μ) {a b : Fin 3} (hab : a ≠ b) (ha : μ a = 1)
    (hb : μ b = 1) : 12 ≤ Module.finrank (ZMod 2) V := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨c, hc⟩ := exists_third a b hab
  obtain ⟨f, hf, hfy⟩ := datum4.exists_form hρ ht.1 ht.2.1
  have hval := form_cosetW ρ hf ht hfy ha hb hc
  have hli : LinearIndependent (ZMod 2) fun i : Fin 12 =>
      ρ (nW4 (cs4.wordProd (cosetW c i))) y := by
    rw [Fintype.linearIndependent_iff]
    intro g hg j
    have h1 := congrArg (fun z => f (ρ (nW4 (cs4.wordProd (cosetW c j)))⁻¹ z)) hg
    simp only [map_sum, map_smul, smul_eq_mul, hval, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true, map_zero] at h1
    exact h1
  simpa using hli.fintype_card_le_finrank

end CFSG.Quasithin.B42Ln
