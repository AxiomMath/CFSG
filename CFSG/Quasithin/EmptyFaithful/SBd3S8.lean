module

public import CFSG.Quasithin.EmptyFaithful.SBd3S8Enum
public import CFSG.Quasithin.EmptyFaithful.SBd3Transport
public import CFSG.Quasithin.Background.B6Defs

public section

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits

namespace CFSG.Quasithin.SBd3S8

open Equiv

attribute [local instance] decEqS8

set_option maxRecDepth 100000

theorem perm_inv_apply_self (g : S8) (x : Fin 8) : g⁻¹ (g x) = x := g.symm_apply_apply x

theorem gtab_mem_Tstd : ∀ a : Fin 8, gtab a ∈ Tstd := by decide +kernel

theorem gtab_zero : ∀ a : Fin 8, gtab a 0 = a := by decide +kernel

theorem swap01_mem_Tstd : Equiv.swap (0 : Fin 8) 1 ∈ Tstd := by decide +kernel

@[expose] def BlockCond (g : S8) (C : Finset (Fin 8)) : Prop :=
  (g 0 ∈ C → C.image g = C) ∧ (g 0 ∉ C → Disjoint (C.image g) C)

instance (g : S8) (C : Finset (Fin 8)) : Decidable (BlockCond g C) := by
  unfold BlockCond; infer_instance

theorem blockClass : ∀ C : Finset (Fin 8), 0 ∈ C → 1 ∈ C → (∀ a : Fin 8, BlockCond (gtab a) C) →
    C = {0, 1} ∨ C = {0, 1, 2, 3} ∨ C = Finset.univ := by decide +kernel

theorem cls2 : ∀ a b : Fin 8, (b ∈ ({0, 1} : Finset (Fin 8)).image (gtab a)) ↔ blk2 a = blk2 b := by
  decide +kernel

theorem cls4 : ∀ a b : Fin 8,
    (b ∈ ({0, 1, 2, 3} : Finset (Fin 8)).image (gtab a)) ↔ blk4 a = blk4 b := by
  decide +kernel

theorem classification (N : Subgroup S8) (hT : Tstd ≤ N) : N = ⊤ ∨ N ≤ W4 ∨ N ≤ W2 := by
  classical
  let R : Fin 8 → Fin 8 → Prop := fun i j => i = j ∨ Equiv.swap i j ∈ N
  have Rsymm : ∀ i j, R i j → R j i := by
    rintro i j (h | h)
    · exact Or.inl h.symm
    · exact Or.inr (by rwa [Equiv.swap_comm])
  have Rinv : ∀ g ∈ N, ∀ i j, R i j → R (g i) (g j) := by
    rintro g hg i j (h | h)
    · exact Or.inl (by rw [h])
    · right
      rw [Equiv.swap_apply_apply g i j]
      exact N.mul_mem (N.mul_mem hg h) (N.inv_mem hg)
  have Rtrans : ∀ i j k, R i j → R j k → R i k := by
    rintro i j k (rfl | h1) (rfl | h2)
    · exact Or.inl rfl
    · exact Or.inr h2
    · exact Or.inr h1
    · by_cases hik : i = k
      · exact Or.inl hik
      by_cases hij : i = j
      · subst hij
        exact Or.inr h2
      right
      have e := Equiv.swap_mul_swap_mul_swap (x := i) (y := j) (z := k) hij hik
      rw [Equiv.swap_comm k i] at e
      rw [← e]
      exact N.mul_mem (N.mul_mem h2 h1) h2
  let C : Finset (Fin 8) := Finset.univ.filter (fun j => R 0 j)
  have hC : ∀ j, j ∈ C ↔ R 0 j := fun j => by simp [C]
  have h0 : (0 : Fin 8) ∈ C := (hC 0).2 (Or.inl rfl)
  have h1 : (1 : Fin 8) ∈ C := (hC 1).2 (Or.inr (hT swap01_mem_Tstd))
  have hblock : ∀ a : Fin 8, BlockCond (gtab a) C := by
    intro a
    have hgN : gtab a ∈ N := hT (gtab_mem_Tstd a)
    constructor
    · intro hg0
      have hsub : C.image (gtab a) ⊆ C := by
        intro x hx
        obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hx
        have h2 := Rinv _ hgN _ _ ((hC j).1 hj)
        exact (hC _).2 (Rtrans _ _ _ ((hC _).1 hg0) h2)
      exact Finset.eq_of_subset_of_card_le hsub
        (by rw [Finset.card_image_of_injective _ (gtab a).injective])
    · intro hg0
      rw [Finset.disjoint_left]
      intro x hx hxC
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hx
      have h2 := Rinv _ hgN _ _ ((hC j).1 hj)
      apply hg0
      exact (hC _).2 (Rtrans _ _ _ ((hC _).1 hxC) (Rsymm _ _ h2))
  have key : ∀ a b : Fin 8, R a b ↔ b ∈ C.image (gtab a) := by
    intro a b
    have hgN : gtab a ∈ N := hT (gtab_mem_Tstd a)
    constructor
    · intro hab
      have h2 := Rinv _ (N.inv_mem hgN) _ _ hab
      have e0 : (gtab a)⁻¹ a = 0 := by
        have := perm_inv_apply_self (gtab a) 0
        rwa [gtab_zero a] at this
      rw [e0] at h2
      refine Finset.mem_image.mpr ⟨(gtab a)⁻¹ b, (hC _).2 h2, ?_⟩
      exact perm_apply_inv_self _ _
    · intro hb
      obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hb
      have h2 := Rinv _ hgN _ _ ((hC c).1 hc)
      rwa [gtab_zero a] at h2
  rcases blockClass C h0 h1 hblock with hC2 | hC4 | hCu
  · right; right
    intro g hg i j
    have hiff : ∀ a b, R a b ↔ blk2 a = blk2 b := fun a b => by
      rw [key, hC2, cls2]
    constructor
    · intro h
      exact (hiff _ _).1 (Rinv g hg _ _ ((hiff _ _).2 h))
    · intro h
      have := Rinv g⁻¹ (N.inv_mem hg) _ _ ((hiff _ _).2 h)
      rw [perm_inv_apply_self, perm_inv_apply_self] at this
      exact (hiff _ _).1 this
  · right; left
    intro g hg i j
    have hiff : ∀ a b, R a b ↔ blk4 a = blk4 b := fun a b => by
      rw [key, hC4, cls4]
    constructor
    · intro h
      exact (hiff _ _).1 (Rinv g hg _ _ ((hiff _ _).2 h))
    · intro h
      have := Rinv g⁻¹ (N.inv_mem hg) _ _ ((hiff _ _).2 h)
      rw [perm_inv_apply_self, perm_inv_apply_self] at this
      exact (hiff _ _).1 this
  · left
    have hall : ∀ i j, R i j := fun i j =>
      Rtrans _ _ _ (Rsymm _ _ ((hC i).1 (by rw [hCu]; exact Finset.mem_univ _)))
        ((hC j).1 (by rw [hCu]; exact Finset.mem_univ _))
    have hN : ∀ g : S8, g ∈ N := fun g => by
      induction g using Equiv.Perm.swap_induction_on with
      | one => exact N.one_mem
      | swap_mul f x y hxy ih =>
        refine N.mul_mem ?_ ih
        rcases hall x y with h | h
        · exact absurd h hxy
        · exact h
    exact eq_top_iff.2 fun g _ => hN g

theorem eq_alternatingGroup_of_perfect_normal {K : Subgroup S8} (hn : K.Normal)
    (hperf : ⁅K, K⁆ = K) (hbot : K ≠ ⊥) : K = alternatingGroup (Fin 8) := by
  have hcomm : ⁅(⊤ : Subgroup S8), ⊤⁆ = alternatingGroup (Fin 8) :=
    alternatingGroup.commutator_perm_eq (by simp)
  have hle : K ≤ alternatingGroup (Fin 8) := by
    rw [← hcomm, ← hperf]
    exact Subgroup.commutator_mono le_top le_top
  have hsimple : IsSimpleGroup (alternatingGroup (Fin 8)) :=
    alternatingGroup.isSimpleGroup (by simp)
  have hKn : (K.subgroupOf (alternatingGroup (Fin 8))).Normal := hn.subgroupOf _
  rcases hsimple.eq_bot_or_eq_top_of_normal (K.subgroupOf (alternatingGroup (Fin 8))) with h | h
  · exfalso
    apply hbot
    rw [eq_bot_iff]
    intro x hx
    have : (⟨x, hle hx⟩ : ↥(alternatingGroup (Fin 8))) ∈ K.subgroupOf (alternatingGroup (Fin 8)) :=
      hx
    rw [h, Subgroup.mem_bot] at this
    have := congrArg Subtype.val this
    simpa using this
  · exact le_antisymm hle (Subgroup.subgroupOf_eq_top.mp h)

theorem normal_le_alternating {K : Subgroup S8} (hn : K.Normal) (hle : K ≤ alternatingGroup (Fin 8)) :
    K = ⊥ ∨ K = alternatingGroup (Fin 8) := by
  have hsimple : IsSimpleGroup (alternatingGroup (Fin 8)) :=
    alternatingGroup.isSimpleGroup (by simp)
  have hKn : (K.subgroupOf (alternatingGroup (Fin 8))).Normal := hn.subgroupOf _
  rcases hsimple.eq_bot_or_eq_top_of_normal (K.subgroupOf (alternatingGroup (Fin 8))) with h | h
  · left
    rw [eq_bot_iff]
    intro x hx
    have : (⟨x, hle hx⟩ : ↥(alternatingGroup (Fin 8))) ∈ K.subgroupOf (alternatingGroup (Fin 8)) :=
      hx
    rw [h, Subgroup.mem_bot] at this
    have := congrArg Subtype.val this
    simpa using this
  · right
    exact le_antisymm hle (Subgroup.subgroupOf_eq_top.mp h)

@[expose] def c0 : S8 := Equiv.swap 0 1 * Equiv.swap 1 4

@[expose] def q0 : S8 := Equiv.swap 1 2 * Equiv.swap 5 6

theorem c0_facts : Equiv.Perm.sign c0 = 1 ∧ ¬ PW4 c0 ∧ ¬ PAff c0 := by decide +kernel

theorem q0_facts : Equiv.Perm.sign q0 = 1 ∧ PAff q0 ∧ ¬ PW2 q0 := by decide +kernel

theorem K_eq_Q4 {K : Subgroup S8} (hK : IsMaxParabolic2 (alternatingGroup (Fin 8)) K)
    (hT : Tstd ≤ Subgroup.normalizer (K : Set S8)) : K = alternatingGroup (Fin 8) ⊓ W4 := by
  obtain ⟨⟨hKA, S₀, hS₀, hS₀K⟩, hKne, hKmax⟩ := hK
  have hmax' : ∀ Q : Subgroup S8, K ≤ Q → Q ≤ alternatingGroup (Fin 8) → Q = K ∨
      Q = alternatingGroup (Fin 8) := by
    intro Q hKQ hQA
    by_cases hQ : Q = alternatingGroup (Fin 8)
    · exact Or.inr hQ
    · exact Or.inl (hKmax Q ⟨hQA, S₀, hS₀, fun x hx => hKQ (hS₀K hx)⟩ hQ hKQ)
  have hS0K : S₀ ≤ K := fun s hs => hS₀K ⟨hS₀.1 hs, Subgroup.le_normalizer hs⟩
  have hS0 : S₀ ≠ ⊥ := by
    intro h
    have h1 := hS₀.2.2
    rw [h, Subgroup.bot_subgroupOf, Subgroup.index_bot] at h1
    apply h1
    rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
    decide
  have hK1 : K ≠ ⊥ := fun h => hS0 (le_bot_iff.1 (h ▸ hS0K))
  rcases classification _ hT with hN | hN | hN
  · exfalso
    have hKn : K.Normal := Subgroup.normalizer_eq_top_iff.mp hN
    rcases normal_le_alternating hKn hKA with h | h
    · exact hK1 h
    · exact hKne h
  · have hKW : K ≤ W4 := Subgroup.le_normalizer.trans hN
    rcases hmax' _ (le_inf hKA hKW) inf_le_left with h | h
    · exact h.symm
    · exfalso
      have : c0 ∈ alternatingGroup (Fin 8) ⊓ W4 := by
        rw [h]
        exact Equiv.Perm.mem_alternatingGroup.2 c0_facts.1
      exact c0_facts.2.1 this.2
  · exfalso
    have hKW : K ≤ W2 := Subgroup.le_normalizer.trans hN
    have hKQ : K ≤ alternatingGroup (Fin 8) ⊓ Aff := fun k hk =>
      ⟨hKA hk, even_W2_le_Aff k (hKW hk) (Equiv.Perm.mem_alternatingGroup.1 (hKA hk))⟩
    rcases hmax' _ hKQ inf_le_left with h | h
    · have hq : q0 ∈ alternatingGroup (Fin 8) ⊓ Aff :=
        ⟨Equiv.Perm.mem_alternatingGroup.2 q0_facts.1, q0_facts.2.1⟩
      rw [h] at hq
      exact q0_facts.2.2 (hKW hq)
    · have : c0 ∈ alternatingGroup (Fin 8) ⊓ Aff := by
        rw [h]
        exact Equiv.Perm.mem_alternatingGroup.2 c0_facts.1
      exact c0_facts.2.2 this.2

@[expose] def Hs : List S8 :=
  (List.range 3).flatMap fun i =>
    (List.range 3).flatMap fun j => [a1 ^ i * a3 ^ j, a1 ^ i * a3 ^ j * vv]

@[expose] def eqT (f g : S8) : Bool := tupleOf f == tupleOf g

theorem eqT_iff {f g : S8} : eqT f g = true ↔ f = g :=
  ⟨fun h => eq_of_tupleOf_eq (beq_iff_eq.1 h), fun h => by simp [eqT, h]⟩

@[expose] def conjT (e : S8) : List (List (Fin 8)) := Hs.map fun h => tupleOf (h * e * h⁻¹)

@[expose] def orbChk (e : S8) : Bool :=
  eqT e 1 || Elist.all fun f =>
    (tupleOf f == idT) || (conjT e).any (· == tupleOf f) ||
      (conjT e).any fun u => (conjT e).any fun v => compT u v == tupleOf f

theorem orbit_check_all : Elist.all orbChk = true := by decide +kernel

theorem orbit_check : ∀ e ∈ Elist, e ≠ 1 → ∀ f ∈ Elist, f = 1 ∨ (∃ h ∈ Hs, f = h * e * h⁻¹) ∨
    ∃ h₁ ∈ Hs, ∃ h₂ ∈ Hs, f = (h₁ * e * h₁⁻¹) * (h₂ * e * h₂⁻¹) := by
  intro e he hne f hf
  have h := List.all_eq_true.1 orbit_check_all e he
  simp only [orbChk, Bool.or_eq_true, eqT_iff, List.all_eq_true, List.any_eq_true,
    beq_iff_eq] at h
  rcases h with h | h
  · exact absurd h hne
  · rcases h f hf with (h | ⟨u, hu, e'⟩) | ⟨u, hu, v, hv, e'⟩
    · exact Or.inl (eq_of_tupleOf_eq h)
    · obtain ⟨h, hh, rfl⟩ := List.mem_map.1 hu
      exact Or.inr (Or.inl ⟨h, hh, (eq_of_tupleOf_eq e').symm⟩)
    · obtain ⟨h₁, hh₁, rfl⟩ := List.mem_map.1 hu
      obtain ⟨h₂, hh₂, rfl⟩ := List.mem_map.1 hv
      rw [← tupleOf_mul] at e'
      exact Or.inr (Or.inr ⟨h₁, hh₁, h₂, hh₂, (eq_of_tupleOf_eq e').symm⟩)

theorem a_facts_b : (aGens.all fun a => decide (Equiv.Perm.sign a = 1 ∧ PW4 a ∧ a ^ 3 = 1 ∧ a ≠ 1)) =
    true := by decide +kernel

theorem a_facts : ∀ a ∈ aGens, Equiv.Perm.sign a = 1 ∧ PW4 a ∧ a ^ 3 = 1 ∧ a ≠ 1 := fun a ha =>
  of_decide_eq_true (List.all_eq_true.1 a_facts_b a ha)

theorem vv_mem_Tstd : vv ∈ Tstd := by decide +kernel

theorem Hs_mem {H : Subgroup S8} (h1 : a1 ∈ H) (h3 : a3 ∈ H) (hv : vv ∈ H) :
    ∀ h ∈ Hs, h ∈ H := by
  intro h hh
  simp only [Hs, List.mem_flatMap, List.mem_range, List.mem_cons, List.not_mem_nil,
    or_false] at hh
  obtain ⟨i, -, j, -, rfl | rfl⟩ := hh
  · exact H.mul_mem (H.pow_mem h1 i) (H.pow_mem h3 j)
  · exact H.mul_mem (H.mul_mem (H.pow_mem h1 i) (H.pow_mem h3 j)) hv

theorem pow128_of_isPGroup {Q : Subgroup S8} (hQ : IsPGroup 2 ↥Q) {x : S8} (hx : x ∈ Q) :
    x ^ 128 = 1 := by
  obtain ⟨k, hk⟩ := hQ ⟨x, hx⟩
  have h1 : x ^ 2 ^ k = 1 := by
    have := congrArg Subtype.val hk
    simpa using this
  have h2 : orderOf x ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one h1
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h2
  have h3 : orderOf x ∣ 40320 := card_S8 ▸ orderOf_dvd_natCard x
  rw [hj] at h3
  have hj7 : j ≤ 7 := by
    by_contra hlt
    push Not at hlt
    have : 2 ^ 8 ∣ 40320 := (pow_dvd_pow 2 hlt).trans h3
    norm_num at this
  have : orderOf x ∣ 128 := by
    rw [hj]
    exact pow_dvd_pow 2 hj7
  exact orderOf_dvd_iff_pow_eq_one.1 this

theorem Q4_irreducible {D : Subgroup S8}
    (hD1 : D ≤ pCoreOf 2 (oPrimeResidualOf 3 (alternatingGroup (Fin 8) ⊓ W4) ⊔ Tstd))
    (hD2 : oPrimeResidualOf 3 (alternatingGroup (Fin 8) ⊓ W4) ⊔ Tstd ≤
      Subgroup.normalizer (D : Set S8)) :
    D = ⊥ ∨ D = pCoreOf 2 (oPrimeResidualOf 3 (alternatingGroup (Fin 8) ⊓ W4) ⊔ Tstd) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set X₃ := oPrimeResidualOf 3 (alternatingGroup (Fin 8) ⊓ W4) with hX₃
  set H := X₃ ⊔ Tstd with hH
  set Q := pCoreOf 2 H with hQ
  have hX₃le : X₃ ≤ alternatingGroup (Fin 8) ⊓ W4 :=
    (Subgroup.closure_le _).2 fun x hx => hx.1
  have hHW4 : H ≤ W4 := sup_le (hX₃le.trans inf_le_right) (inf_le_right : Tstd ≤ W4)
  have ha : ∀ a ∈ aGens, a ∈ X₃ := by
    intro a ha
    obtain ⟨hs, hw, h3, h1⟩ := a_facts a ha
    refine Subgroup.subset_closure ⟨⟨Equiv.Perm.mem_alternatingGroup.2 hs, hw⟩, 1, ?_⟩
    rw [pow_one]
    exact orderOf_eq_prime h3 h1
  have haH : ∀ a ∈ aGens, a ∈ H := fun a h => Subgroup.mem_sup_left (ha a h)
  have hvH : vv ∈ H := Subgroup.mem_sup_right vv_mem_Tstd
  have hQ2 : IsPGroup 2 ↥Q := pCoreOf_isPGroup 2 H
  have hQE : ∀ x ∈ Q, x ∈ Elist := by
    intro x hx
    have hxH : x ∈ H := pCoreOf_le 2 H hx
    refine two_element_mem_Elist x (hHW4 hxH) (pow128_of_isPGroup hQ2 hx) ?_
    intro a haL
    have haH' := haH a haL
    have hconj : a * x⁻¹ * a⁻¹ ∈ Q :=
      (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 H haH') x⁻¹).1 (Q.inv_mem hx)
    have hc : x * a * x⁻¹ * a⁻¹ ∈ Q := by
      have e : x * a * x⁻¹ * a⁻¹ = x * (a * x⁻¹ * a⁻¹) := by group
      rw [e]
      exact Q.mul_mem hx hconj
    exact pow128_of_isPGroup hQ2 hc
  have hHs : ∀ h ∈ Hs, h ∈ H :=
    Hs_mem (haH a1 (by simp [aGens])) (haH a3 (by simp [aGens])) hvH
  have conjD : ∀ h ∈ H, ∀ d ∈ D, h * d * h⁻¹ ∈ D := fun h hh d hd =>
    (Subgroup.mem_normalizer_iff.mp (hD2 hh) d).1 hd
  by_cases hD : D = ⊥
  · exact Or.inl hD
  · right
    obtain ⟨d, hdD, hd1⟩ : ∃ d ∈ D, d ≠ 1 := by
      by_contra hcon
      push Not at hcon
      exact hD ((Subgroup.eq_bot_iff_forall _).2 fun x hx => hcon x hx)
    have hdE : d ∈ Elist := hQE d (hD1 hdD)
    have hallf : ∀ f ∈ Elist, f ∈ D := by
      intro f hf
      rcases orbit_check d hdE hd1 f hf with h | ⟨h, hh, rfl⟩ | ⟨h₁, hh₁, h₂, hh₂, rfl⟩
      · rw [h]
        exact D.one_mem
      · exact conjD h (hHs h hh) d hdD
      · exact D.mul_mem (conjD h₁ (hHs h₁ hh₁) d hdD) (conjD h₂ (hHs h₂ hh₂) d hdD)
    exact le_antisymm hD1 fun x hx => hallf x (hQE x hx)

theorem s8_std {K D : Subgroup S8} (hK : IsMaxParabolic2 (alternatingGroup (Fin 8)) K)
    (hT : Tstd ≤ Subgroup.normalizer (K : Set S8))
    (hD1 : D ≤ pCoreOf 2 (oPrimeResidualOf 3 K ⊔ Tstd))
    (hD2 : oPrimeResidualOf 3 K ⊔ Tstd ≤ Subgroup.normalizer (D : Set S8)) :
    D = ⊥ ∨ D = pCoreOf 2 (oPrimeResidualOf 3 K ⊔ Tstd) := by
  have hKQ4 : K = alternatingGroup (Fin 8) ⊓ W4 := K_eq_Q4 hK hT
  subst hKQ4
  exact Q4_irreducible hD1 hD2

theorem pCoreOf_map_XS (c : S8 ≃* S8) (K Sb : Subgroup S8) :
    pCoreOf 2 (oPrimeResidualOf 3 (K.map c.toMonoidHom) ⊔ Sb.map c.toMonoidHom) =
      (pCoreOf 2 (oPrimeResidualOf 3 K ⊔ Sb)).map c.toMonoidHom := by
  rw [← SBd3T.map_oPrimeResidualOf c.toMonoidHom 3 Nat.prime_three K, ← Subgroup.map_sup,
    pCoreOf_map_mulEquiv]

theorem s8_irreducible {Λ K Sb D : Subgroup S8} (hΛn : Λ.Normal) (hΛp : ⁅Λ, Λ⁆ = Λ)
    (hΛ1 : Λ ≠ ⊥) (hK : IsMaxParabolic2 Λ K) (hS : IsSylowTwoOf Sb ⊤)
    (hSK : Sb ≤ Subgroup.normalizer (K : Set S8))
    (hD1 : D ≤ pCoreOf 2 (oPrimeResidualOf 3 K ⊔ Sb))
    (hD2 : oPrimeResidualOf 3 K ⊔ Sb ≤ Subgroup.normalizer (D : Set S8)) :
    D = ⊥ ∨ D = pCoreOf 2 (oPrimeResidualOf 3 K ⊔ Sb) := by
  have hΛA : Λ = alternatingGroup (Fin 8) := eq_alternatingGroup_of_perfect_normal hΛn hΛp hΛ1
  subst hΛA
  obtain ⟨g, -, hg⟩ := B6.isSylowTwoOf_exists_conj isSylowTwoOf_Tstd hS
  let c : S8 ≃* S8 := MulAut.conj g⁻¹
  have hcinj : Function.Injective c.toMonoidHom := c.injective
  have hSb : Sb.map c.toMonoidHom = Tstd := by
    rw [hg]
    show (Tstd.map (MulAut.conj g).toMonoidHom).map (MulAut.conj g⁻¹).toMonoidHom = Tstd
    rw [Subgroup.map_map]
    have : (MulAut.conj g⁻¹).toMonoidHom.comp (MulAut.conj g).toMonoidHom = MonoidHom.id S8 := by
      ext x
      simp
    rw [this, Subgroup.map_id]
  have hA : (alternatingGroup (Fin 8)).map c.toMonoidHom = alternatingGroup (Fin 8) :=
    B6.conjSub_eq_self (g := g⁻¹) (by rw [Subgroup.normalizer_eq_top]; exact Subgroup.mem_top _)
  have hK' : IsMaxParabolic2 (alternatingGroup (Fin 8)) (K.map c.toMonoidHom) := by
    have := (SBd3T.isMaxParabolic2_map_iff c.toMonoidHom hcinj _ _).2 hK
    rwa [hA] at this
  have hT : Tstd ≤ Subgroup.normalizer ((K.map c.toMonoidHom : Subgroup S8) : Set S8) := by
    rw [← hSb]
    exact (SBd3T.map_le_normalizer_map_iff c.toMonoidHom hcinj _ _).2 hSK
  have hD1' : D.map c.toMonoidHom ≤
      pCoreOf 2 (oPrimeResidualOf 3 (K.map c.toMonoidHom) ⊔ Tstd) := by
    rw [← hSb, pCoreOf_map_XS]
    exact Subgroup.map_mono hD1
  have hD2' : oPrimeResidualOf 3 (K.map c.toMonoidHom) ⊔ Tstd ≤
      Subgroup.normalizer ((D.map c.toMonoidHom : Subgroup S8) : Set S8) := by
    rw [← hSb, ← SBd3T.map_oPrimeResidualOf c.toMonoidHom 3 Nat.prime_three K,
      ← Subgroup.map_sup]
    exact (SBd3T.map_le_normalizer_map_iff c.toMonoidHom hcinj _ _).2 hD2
  rcases s8_std hK' hT hD1' hD2' with h | h
  · left
    apply Subgroup.map_injective hcinj
    rw [h, Subgroup.map_bot]
  · right
    apply Subgroup.map_injective hcinj
    rw [h, ← hSb, pCoreOf_map_XS]

end CFSG.Quasithin.SBd3S8
