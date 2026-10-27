module

public import CFSG.LocalAnalysis.QuasithinUnique.PushingUp.Blocks

public section

namespace CFSG.Quasithin.A5Model

open Equiv CFSG.QuasithinUnique

abbrev Ev : AddSubgroup (Fin 5 → ZMod 2) := evenWeight 5

instance : DecidablePred (· ∈ Ev) := fun x =>
  decidable_of_iff (∑ i, x i = 0) (by simp [Ev, evenWeight, AddMonoidHom.mem_ker])

theorem mem_Ev {x : Fin 5 → ZMod 2} : x ∈ Ev ↔ ∑ i, x i = 0 := by
  simp [Ev, evenWeight, AddMonoidHom.mem_ker]

abbrev W5 : Type := Multiplicative ↥Ev

@[expose] def pw (σ : Perm (Fin 5)) (x : ↥Ev) : ↥Ev :=
  ⟨fun i => (x : Fin 5 → ZMod 2) (σ⁻¹ i), by
    have hx : ∑ i, (x : Fin 5 → ZMod 2) i = 0 := mem_Ev.1 x.2
    refine mem_Ev.2 ?_
    rw [Equiv.sum_comp σ⁻¹ (fun i => (x : Fin 5 → ZMod 2) i)]
    exact hx⟩

theorem pw_coe (σ : Perm (Fin 5)) (x : ↥Ev) (i : Fin 5) :
    ((pw σ x : ↥Ev) : Fin 5 → ZMod 2) i = (x : Fin 5 → ZMod 2) (σ⁻¹ i) := rfl

theorem pw_add (σ : Perm (Fin 5)) (x y : ↥Ev) : pw σ (x + y) = pw σ x + pw σ y := rfl

theorem pw_zero (σ : Perm (Fin 5)) : pw σ 0 = 0 := rfl

theorem pw_one (x : ↥Ev) : pw 1 x = x := rfl

theorem pw_mul (σ τ : Perm (Fin 5)) (x : ↥Ev) : pw (σ * τ) x = pw σ (pw τ x) := rfl

@[expose] def pact : Perm (Fin 5) →* MulAut W5 where
  toFun σ :=
    { toFun := fun x => Multiplicative.ofAdd (pw σ (Multiplicative.toAdd x))
      invFun := fun x => Multiplicative.ofAdd (pw σ⁻¹ (Multiplicative.toAdd x))
      left_inv := fun x => by
        apply Multiplicative.toAdd.injective
        exact Subtype.ext (funext fun i => by simp [pw])
      right_inv := fun x => by
        apply Multiplicative.toAdd.injective
        exact Subtype.ext (funext fun i => by simp [pw])
      map_mul' := fun x y => rfl }
  map_one' := by
    ext x
    rfl
  map_mul' := fun σ τ => by
    ext x
    rfl

theorem toAdd_pact (σ : Perm (Fin 5)) (x : W5) :
    Multiplicative.toAdd (pact σ x) = pw σ (Multiplicative.toAdd x) := rfl

theorem pact_ofAdd (σ : Perm (Fin 5)) (x : ↥Ev) :
    pact σ (Multiplicative.ofAdd x) = Multiplicative.ofAdd (pw σ x) := rfl

theorem pw_faithful : ∀ σ : Perm (Fin 5), (∀ x : ↥Ev, pw σ x = x) → σ = 1 := by
  set_option maxRecDepth 100000 in decide

theorem pact_injective : Function.Injective pact := by
  rw [injective_iff_map_eq_one]
  intro σ hσ
  apply pw_faithful
  intro x
  have := DFunLike.congr_fun hσ (Multiplicative.ofAdd x)
  exact Multiplicative.ofAdd.injective this

@[expose] def wA (i : Fin 5) : ↥Ev :=
  ⟨fun k => if k = i then 0 else 1, by revert i; decide⟩

@[expose] def e2 (a b : Fin 5) : ↥Ev :=
  ⟨Pi.single a 1 + Pi.single b 1, by revert a b; decide⟩

@[expose] def W4 : W5 := Multiplicative.ofAdd (wA 4)

theorem pw_wA : ∀ (σ : Perm (Fin 5)) (i : Fin 5), pw σ (wA i) = wA (σ i) := by
  set_option maxRecDepth 100000 in decide

theorem wA_inj : ∀ i j : Fin 5, wA i = wA j → i = j := by
  set_option maxRecDepth 100000 in decide

theorem exists_sum_wA : ∀ x : ↥Ev, ∃ s : Finset (Fin 5), x = ∑ i ∈ s, wA i := by
  set_option maxRecDepth 100000 in decide

theorem pw_e2 : ∀ (σ : Perm (Fin 5)) (a b : Fin 5), pw σ (e2 a b) = e2 (σ a) (σ b) := by
  set_option maxRecDepth 100000 in decide

theorem eq_zero_or_e2_or_wA :
    ∀ x : ↥Ev, x = 0 ∨ (∃ a b : Fin 5, a ≠ b ∧ x = e2 a b) ∨ ∃ i : Fin 5, x = wA i := by
  set_option maxRecDepth 100000 in decide

theorem perm_of_pw_e2 :
    ∀ (σ : Perm (Fin 5)) (a b : Fin 5), a ≠ b → pw σ (e2 a b) = e2 a b →
      (σ a = a ∧ σ b = b) ∨ (σ a = b ∧ σ b = a) := by
  set_option maxRecDepth 100000 in decide

theorem pw_wA_eq_iff : ∀ (σ : Perm (Fin 5)) (i : Fin 5), pw σ (wA i) = wA i ↔ σ i = i := by
  set_option maxRecDepth 100000 in decide

theorem pw_sub_coe (σ : Perm (Fin 5)) (x : ↥Ev) (i : Fin 5) :
    ((x - pw σ x : ↥Ev) : Fin 5 → ZMod 2) i =
      (x : Fin 5 → ZMod 2) i - (x : Fin 5 → ZMod 2) (σ⁻¹ i) := rfl

private theorem B1 : ∀ x : ↥Ev, x ≠ 0 →
    ∃ σ : Perm (Fin 5), σ.sign = 1 ∧ (pw σ x = e2 0 1 ∨ pw σ x = wA 4) := by
  set_option maxRecDepth 100000 in decide

private theorem B2 : e2 0 1 = pw (swap 0 4 * swap 1 2) (wA 4) + pw (swap 1 4 * swap 2 3) (wA 4) ∧
    (swap 0 4 * swap 1 2 : Perm (Fin 5)).sign = 1 ∧ (swap 1 4 * swap 2 3 : Perm (Fin 5)).sign = 1 := by
  set_option maxRecDepth 100000 in decide

private theorem B2' : wA 4 = e2 0 1 + pw (swap 0 2 * swap 1 3) (e2 0 1) ∧
    (swap 0 2 * swap 1 3 : Perm (Fin 5)).sign = 1 := by
  set_option maxRecDepth 100000 in decide

private theorem B3 : ∀ z : ↥Ev, z = 0 ∨ (∃ σ : Perm (Fin 5), σ.sign = 1 ∧ z = pw σ (e2 0 1)) ∨
    (∃ σ : Perm (Fin 5), σ.sign = 1 ∧ z = pw σ (wA 4)) := by
  set_option maxRecDepth 100000 in decide

theorem irreducible (Y : Subgroup W5)
    (hY : ∀ σ ∈ alternatingGroup (Fin 5), ∀ y ∈ Y, pact σ y ∈ Y) : Y = ⊥ ∨ Y = ⊤ := by
  by_cases hbot : Y = ⊥
  · exact Or.inl hbot
  right
  obtain ⟨⟨y, hyY⟩, hy1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hbot
  have hy0 : Multiplicative.toAdd y ≠ 0 := fun h =>
    hy1 (Subtype.ext (Multiplicative.toAdd.injective (by simpa using h)))
  have hmem : ∀ σ : Perm (Fin 5), σ.sign = 1 → ∀ x : ↥Ev, Multiplicative.ofAdd x ∈ Y →
      Multiplicative.ofAdd (pw σ x) ∈ Y := fun σ hσ x hx =>
    hY σ (Equiv.Perm.mem_alternatingGroup.2 hσ) _ hx
  have hadd : ∀ x z : ↥Ev, Multiplicative.ofAdd x ∈ Y → Multiplicative.ofAdd z ∈ Y →
      Multiplicative.ofAdd (x + z) ∈ Y := fun x z hx hz => by
    rw [ofAdd_add]
    exact Y.mul_mem hx hz
  obtain ⟨σ, hσ, hσy⟩ := B1 _ hy0
  have h1 : Multiplicative.ofAdd (pw σ (Multiplicative.toAdd y)) ∈ Y :=
    hmem σ hσ _ (by simpa using hyY)
  have hboth : Multiplicative.ofAdd (e2 0 1) ∈ Y ∧ Multiplicative.ofAdd (wA 4) ∈ Y := by
    obtain ⟨hb2, hs1, hs2⟩ := B2
    obtain ⟨hb2', hs'⟩ := B2'
    rcases hσy with h | h
    · rw [h] at h1
      refine ⟨h1, ?_⟩
      rw [hb2']
      exact hadd _ _ h1 (hmem _ hs' _ h1)
    · rw [h] at h1
      refine ⟨?_, h1⟩
      rw [hb2]
      exact hadd _ _ (hmem _ hs1 _ h1) (hmem _ hs2 _ h1)
  rw [eq_top_iff]
  intro g _
  have hg : g = Multiplicative.ofAdd (Multiplicative.toAdd g) := rfl
  rw [hg]
  rcases B3 (Multiplicative.toAdd g) with h | ⟨τ, hτ, h⟩ | ⟨τ, hτ, h⟩
  · rw [h]
    exact Y.one_mem
  · rw [h]
    exact hmem τ hτ _ hboth.1
  · rw [h]
    exact hmem τ hτ _ hboth.2

@[expose] def orbA (y : W5) : Finset W5 :=
  (Finset.univ : Finset (alternatingGroup (Fin 5))).image
    fun σ : alternatingGroup (Fin 5) => pact (σ : Perm (Fin 5)) y

theorem orbA_card_wA : ∀ i : Fin 5, (orbA (Multiplicative.ofAdd (wA i))).card = 5 := by
  set_option maxRecDepth 100000 in decide

theorem eq_wA_of_card_orbA :
    ∀ y : W5, (orbA y).card = 5 → ∃ i : Fin 5, y = Multiplicative.ofAdd (wA i) := by
  set_option maxRecDepth 100000 in decide

theorem pact_wA (σ : Perm (Fin 5)) (i : Fin 5) :
    pact σ (Multiplicative.ofAdd (wA i)) = Multiplicative.ofAdd (wA (σ i)) := by
  rw [pact_ofAdd, pw_wA]

theorem exists_pact_of_normalizes (ρ : MulAut W5)
    (h1 : ∀ σ ∈ alternatingGroup (Fin 5), ∃ τ ∈ alternatingGroup (Fin 5),
      ∀ x, ρ (pact σ x) = pact τ (ρ x))
    (h2 : ∀ τ ∈ alternatingGroup (Fin 5), ∃ σ ∈ alternatingGroup (Fin 5),
      ∀ x, ρ (pact σ x) = pact τ (ρ x)) :
    ∃ π : Perm (Fin 5), ∀ x, ρ x = pact π x := by
  classical
  have horb : ∀ y : W5, orbA (ρ y) = (orbA y).image ρ := by
    intro y
    ext t
    simp only [orbA, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨τ, rfl⟩
      obtain ⟨σ, hσ, hστ⟩ := h2 τ.1 τ.2
      exact ⟨pact σ y, ⟨⟨σ, hσ⟩, rfl⟩, hστ y⟩
    · rintro ⟨s, ⟨σ, rfl⟩, rfl⟩
      obtain ⟨τ, hτ, hστ⟩ := h1 σ.1 σ.2
      exact ⟨⟨τ, hτ⟩, (hστ y).symm⟩
  have hw : ∀ i : Fin 5, ∃ j : Fin 5,
      ρ (Multiplicative.ofAdd (wA i)) = Multiplicative.ofAdd (wA j) := by
    intro i
    apply eq_wA_of_card_orbA
    rw [horb, Finset.card_image_of_injective _ ρ.injective]
    exact orbA_card_wA i
  choose π hπ using hw
  have hπinj : Function.Injective π := by
    intro i j hij
    apply wA_inj
    have : ρ (Multiplicative.ofAdd (wA i)) = ρ (Multiplicative.ofAdd (wA j)) := by
      rw [hπ i, hπ j, hij]
    exact Multiplicative.ofAdd.injective (ρ.injective this)
  have hπbij : Function.Bijective π := Finite.injective_iff_bijective.1 hπinj
  refine ⟨Equiv.ofBijective π hπbij, fun x => ?_⟩
  obtain ⟨s, hs⟩ := exists_sum_wA (Multiplicative.toAdd x)
  have hx : x = ∏ i ∈ s, Multiplicative.ofAdd (wA i) := by
    have : x = Multiplicative.ofAdd (Multiplicative.toAdd x) := rfl
    rw [this, hs, ofAdd_sum]
  rw [hx, map_prod, map_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [hπ i, pact_wA]
  rfl

abbrev A5 : Type := ↥(alternatingGroup (Fin 5))

@[expose] def pa : Perm (Fin 5) := swap 0 1 * swap 2 3

@[expose] def pb : Perm (Fin 5) := swap 0 2 * swap 1 3

@[expose] def pc : Perm (Fin 5) := swap 0 3 * swap 1 2

@[expose] def c3p : Perm (Fin 5) := swap 0 1 * swap 1 2

theorem klein_mul : ∀ σ τ : Perm (Fin 5), (σ = 1 ∨ σ = pa ∨ σ = pb ∨ σ = pc) →
    (τ = 1 ∨ τ = pa ∨ τ = pb ∨ τ = pc) → (σ * τ = 1 ∨ σ * τ = pa ∨ σ * τ = pb ∨ σ * τ = pc) := by
  rintro σ τ (rfl | rfl | rfl | rfl) (rfl | rfl | rfl | rfl) <;> decide

theorem klein_inv : ∀ σ : Perm (Fin 5), (σ = 1 ∨ σ = pa ∨ σ = pb ∨ σ = pc) →
    (σ⁻¹ = 1 ∨ σ⁻¹ = pa ∨ σ⁻¹ = pb ∨ σ⁻¹ = pc) := by
  rintro σ (rfl | rfl | rfl | rfl) <;> decide

theorem sign_klein : ∀ σ : Perm (Fin 5), (σ = 1 ∨ σ = pa ∨ σ = pb ∨ σ = pc) →
    σ.sign = 1 := by
  rintro σ (rfl | rfl | rfl | rfl) <;> decide

@[expose] def K4 : Subgroup A5 where
  carrier := {σ | (σ : Perm (Fin 5)) = 1 ∨ (σ : Perm (Fin 5)) = pa ∨ (σ : Perm (Fin 5)) = pb ∨
    (σ : Perm (Fin 5)) = pc}
  one_mem' := Or.inl rfl
  mul_mem' := fun {_ _} h h' => klein_mul _ _ h h'
  inv_mem' := fun {_} h => klein_inv _ h

theorem mem_K4 {σ : A5} : σ ∈ K4 ↔
    (σ : Perm (Fin 5)) = 1 ∨ (σ : Perm (Fin 5)) = pa ∨ (σ : Perm (Fin 5)) = pb ∨
      (σ : Perm (Fin 5)) = pc := Iff.rfl

instance : DecidablePred (· ∈ K4) := fun σ =>
  inferInstanceAs (Decidable ((σ : Perm (Fin 5)) = 1 ∨ (σ : Perm (Fin 5)) = pa ∨
    (σ : Perm (Fin 5)) = pb ∨ (σ : Perm (Fin 5)) = pc))

@[expose] def A4s : Subgroup A5 where
  carrier := {σ | (σ : Perm (Fin 5)) 4 = 4}
  one_mem' := rfl
  mul_mem' := fun {σ τ} h h' => by
    show (σ : Perm (Fin 5)) ((τ : Perm (Fin 5)) 4) = 4
    rw [h', h]
  inv_mem' := fun {σ} h => by
    show (σ : Perm (Fin 5))⁻¹ 4 = 4
    rw [Equiv.Perm.inv_eq_iff_eq]
    exact h.symm

theorem mem_A4s {σ : A5} : σ ∈ A4s ↔ (σ : Perm (Fin 5)) 4 = 4 := Iff.rfl

instance : DecidablePred (· ∈ A4s) := fun σ => inferInstanceAs (Decidable ((σ : Perm (Fin 5)) 4 = 4))

theorem K4_le_A4s : K4 ≤ A4s := by
  intro σ h
  rw [mem_A4s]
  rcases mem_K4.1 h with h | h | h | h <;> rw [h] <;> decide

@[expose] def c3A : A5 := ⟨c3p, by rw [Equiv.Perm.mem_alternatingGroup]; decide⟩

theorem c3A_mem : c3A ∈ A4s := by
  rw [mem_A4s]
  decide

theorem c3A_pow : c3A ^ 3 = 1 := by
  apply Subtype.ext
  show c3p ^ 3 = 1
  decide

theorem perm_mem_K4_of_comm : ∀ π : Perm (Fin 5), π 4 = 4 →
    (∀ x : ↥Ev, (x : Fin 5 → ZMod 2) 4 = 0 → pw π x - x = 0 ∨ pw π x - x = wA 4) →
      (π = 1 ∨ π = pa ∨ π = pb ∨ π = pc) := by
  set_option maxRecDepth 100000 in decide

theorem K4_norm : ∀ σ : A5, σ ∈ A4s → ∀ k ∈ K4, σ * k * σ⁻¹ ∈ K4 := by
  set_option maxRecDepth 100000 in decide

theorem mem_K4_of_pow_four : ∀ σ : A5, σ ∈ A4s → σ ^ 4 = 1 → σ ∈ K4 := by
  set_option maxRecDepth 100000 in decide

theorem A4s_pow_twelve : ∀ σ : A5, σ ∈ A4s → σ ^ 12 = 1 := by
  set_option maxRecDepth 100000 in decide

theorem K4_gen_aux : ∀ x : A5, x ∈ K4 → x ≠ 1 → ∀ y : A5, y ∈ K4 →
    (y = 1 ∨ y = x ∨ y = c3A * x * c3A⁻¹ ∨ y = x * (c3A * x * c3A⁻¹)) := by
  set_option maxRecDepth 100000 in decide

theorem K4_irred (X : Subgroup A5) (hX : X ≤ K4) (hc : ∀ x ∈ X, c3A * x * c3A⁻¹ ∈ X) :
    X = ⊥ ∨ X = K4 := by
  by_cases hbot : X = ⊥
  · exact Or.inl hbot
  right
  obtain ⟨⟨x, hxX⟩, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hbot
  refine le_antisymm hX fun y hy => ?_
  have hx1' : x ≠ 1 := fun h => hx1 (Subtype.ext h)
  rcases K4_gen_aux x (hX hxX) hx1' y hy with h | h | h | h
  · rw [h]; exact X.one_mem
  · rw [h]; exact hxX
  · rw [h]; exact hc x hxX
  · rw [h]; exact X.mul_mem hxX (hc x hxX)

theorem K4_comm_cover : ∀ k : A5, k ∈ K4 → ∃ k' : A5, k' ∈ K4 ∧ k = k' * c3A * k'⁻¹ * c3A⁻¹ := by
  set_option maxRecDepth 100000 in decide

theorem card_A5 : Nat.card A5 = 60 := by
  rw [Nat.card_eq_fintype_card]
  set_option maxRecDepth 100000 in decide

theorem card_K4 : Nat.card ↥K4 = 4 := by
  rw [Nat.card_eq_fintype_card]
  set_option maxRecDepth 100000 in decide

theorem K4_index_odd : ¬ 2 ∣ K4.index := by
  have h := K4.card_mul_index
  rw [card_K4, card_A5] at h
  omega

theorem exists_sub_pw_of_e2 : ∀ a b : Fin 5, a ≠ b → a ≠ 4 → b ≠ 4 →
    ∃ x : ↥Ev, ∃ σ : A5, σ ∈ A4s ∧ σ ^ 3 = 1 ∧ e2 a b = x - pw (σ : Perm (Fin 5)) x := by
  set_option maxRecDepth 100000 in decide

theorem eq_of_coord_four_eq_zero : ∀ z : ↥Ev, (z : Fin 5 → ZMod 2) 4 = 0 →
    z = 0 ∨ (∃ a b : Fin 5, a ≠ b ∧ a ≠ 4 ∧ b ≠ 4 ∧ z = e2 a b) ∨ z = e2 0 1 + e2 2 3 := by
  set_option maxRecDepth 100000 in decide

@[expose] def dbl (a b c d : Fin 5) : Perm (Fin 5) := swap a b * swap c d

@[expose] def kl : Fin 5 → List (Perm (Fin 5)) :=
  ![[1, dbl 1 2 3 4, dbl 1 3 2 4, dbl 1 4 2 3],
    [1, dbl 0 2 3 4, dbl 0 3 2 4, dbl 0 4 2 3],
    [1, dbl 0 1 3 4, dbl 0 3 1 4, dbl 0 4 1 3],
    [1, dbl 0 1 2 4, dbl 0 2 1 4, dbl 0 4 1 2],
    [1, dbl 0 1 2 3, dbl 0 2 1 3, dbl 0 3 1 2]]

theorem kl_four : ∀ σ : Perm (Fin 5), σ ∈ kl 4 ↔ (σ = 1 ∨ σ = pa ∨ σ = pb ∨ σ = pc) := by
  intro σ
  simp [kl, dbl, pa, pb, pc]

theorem conj_mem_kl : ∀ x : Perm (Fin 5), ∀ k ∈ kl 4, x⁻¹ * k * x ∈ kl (x⁻¹ 4) := by
  set_option maxRecDepth 100000 in decide

theorem kl_gen : ∀ p : Fin 5, p ≠ 4 → ∀ σ : Perm (Fin 5), σ.sign = 1 →
    ∃ a₁ ∈ kl 4, ∃ b₁ ∈ kl p, ∃ a₂ ∈ kl 4, ∃ b₂ ∈ kl p, σ = a₁ * b₁ * a₂ * b₂ := by
  set_option maxRecDepth 100000 in decide

@[expose] def pactA : A5 →* MulAut W5 := pact.comp (alternatingGroup (Fin 5)).subtype

theorem pactA_injective : Function.Injective pactA := fun _ _ h =>
  Subtype.ext (pact_injective h)

theorem pactA_apply (σ : A5) (x : W5) : pactA σ x = pact (σ : Perm (Fin 5)) x := rfl

theorem A4s_prod_three : ∀ σ : A5, σ ∈ A4s →
    ∃ α β : A5, α ∈ A4s ∧ β ∈ A4s ∧ α ^ 3 = 1 ∧ β ^ 3 = 1 ∧ σ = α * β := by
  set_option maxRecDepth 100000 in decide

theorem Ev_add_self : ∀ x : ↥Ev, x + x = 0 := by
  set_option maxRecDepth 100000 in decide

theorem pact_W4 {σ : Perm (Fin 5)} (hσ : σ 4 = 4) : pact σ W4 = W4 := by
  unfold W4
  rw [pact_wA, hσ]

theorem W4_ne_one : W4 ≠ 1 := by
  intro h
  have : wA 4 = 0 := Multiplicative.ofAdd.injective h
  revert this
  decide

theorem fix_four_of_pact_W4 {σ : Perm (Fin 5)} (h : pact σ W4 = W4) : σ 4 = 4 :=
  (pw_wA_eq_iff σ 4).1 (Multiplicative.ofAdd.injective h)

theorem kl_conj_cover : ∀ x : Perm (Fin 5), ∀ b ∈ kl (x⁻¹ 4), ∃ k ∈ kl 4, b = x⁻¹ * k * x := by
  set_option maxRecDepth 100000 in decide

end CFSG.Quasithin.A5Model
