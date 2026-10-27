module

public import CFSG.LocalAnalysis.StandardType.GGSixStepTwoCoordContraryCore

public section

namespace CFSG.StandardType

namespace CoordShape

open Multiplicative

variable {s p : ℕ}

@[expose] def JointAligned (O : Subgroup (ZMod p)ˣ) (T : Set (Fin s → ZMod p)) : Prop :=
  ∀ i j, ∀ u ∈ O, (∀ t ∈ T, t i = u * t j) → ∀ t ∈ T, t i = t j

theorem exists_jointAligned (O : Subgroup (ZMod p)ˣ) (T : Set (Fin s → ZMod p)) :
    ∃ η : Fin s → (ZMod p)ˣ, (∀ i, η i ∈ O) ∧
      JointAligned O ((fun t i => (η i : ZMod p) * t i) '' T) := by
  classical
  set orb : Fin s → Finset (Fin s) := fun i =>
    Finset.univ.filter fun j => ∃ u ∈ O, ∀ t ∈ T, t j = (u : ZMod p) * t i with horb
  have hself : ∀ i, i ∈ orb i := fun i => by
    simp only [horb, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨1, O.one_mem, fun t _ => by rw [Units.val_one, one_mul]⟩
  set f : Fin s → Fin s := fun i => (orb i).min' ⟨i, hself i⟩ with hf
  have hfmem : ∀ i, ∃ u ∈ O, ∀ t ∈ T, t (f i) = (u : ZMod p) * t i := fun i => by
    have h := Finset.min'_mem (orb i) ⟨i, hself i⟩
    simp only [horb, Finset.mem_filter, Finset.mem_univ, true_and] at h
    exact h
  choose η hηO hη using hfmem
  have hforb : ∀ i j, (∃ w ∈ O, ∀ t ∈ T, t i = (w : ZMod p) * t j) → f i = f j := by
    intro i j ⟨w, hwO, hw⟩
    have horbeq : orb i = orb j := by
      ext k
      simp only [horb, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨v, hvO, hv⟩
        exact ⟨v * w, O.mul_mem hvO hwO, fun t ht => by
          rw [hv t ht, hw t ht, Units.val_mul, mul_assoc]⟩
      · rintro ⟨v, hvO, hv⟩
        refine ⟨v * w⁻¹, O.mul_mem hvO (O.inv_mem hwO), fun t ht => ?_⟩
        rw [hv t ht, hw t ht, Units.val_mul, mul_assoc, ← mul_assoc ((w⁻¹ : (ZMod p)ˣ) : ZMod p),
          ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul]
    simp only [hf, horbeq]
  refine ⟨η, hηO, fun i j u huO hij t' ht' => ?_⟩
  obtain ⟨t, ht, rfl⟩ := ht'
  simp only
  have hrel : ∃ w ∈ O, ∀ t ∈ T, t i = (w : ZMod p) * t j := by
    refine ⟨(η i)⁻¹ * u * η j, O.mul_mem (O.mul_mem (O.inv_mem (hηO i)) huO) (hηO j),
      fun t₁ ht₁ => ?_⟩
    have h1 := hij _ ⟨t₁, ht₁, rfl⟩
    simp only at h1
    calc t₁ i = (((η i)⁻¹ : (ZMod p)ˣ) : ZMod p) * ((η i : ZMod p) * t₁ i) := by
          rw [← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul]
      _ = (((η i)⁻¹ * u * η j : (ZMod p)ˣ) : ZMod p) * t₁ j := by
          rw [h1, Units.val_mul, Units.val_mul]
          ring
  rw [← hη i t ht, ← hη j t ht, hforb i j hrel]

theorem exists_sep [Fact p.Prime] {O : Subgroup (ZMod p)ˣ} {T : Set (Fin s → ZMod p)}
    (hT : ∀ t ∈ T, ∀ t₀ ∈ T, ∀ a : ZMod p, t - a • t₀ ∈ T) (hal : JointAligned O T)
    {i j : Fin s} {t₀ : Fin s → ZMod p} (ht₀ : t₀ ∈ T) (hj : t₀ j ≠ 0)
    (hij : ¬ ∀ t ∈ T, t i = t j) :
    ∃ t ∈ T, (t j ≠ 0 ∧ ∀ u ∈ O, t i ≠ u * t j) ∨ (t j = 0 ∧ t i ≠ 0) := by
  by_contra hno
  push Not at hno
  obtain ⟨u, huO, hu⟩ := (hno t₀ ht₀).1 hj
  apply hij
  refine hal i j u huO fun t ht => ?_
  set a : ZMod p := t j / t₀ j with ha
  have h1 := (hno _ (hT t ht t₀ ht₀ a)).2 (by
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, ha]
    rw [div_mul_cancel₀ _ hj, sub_self])
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at h1
  rw [sub_eq_zero] at h1
  rw [h1, hu, ha, mul_left_comm, div_mul_cancel₀ _ hj]

theorem sub_smul_mem {G : Type} [Group G] [NeZero p] {ι : Multiplicative (Fin s → ZMod p) →* G}
    {E : Subgroup G} {t t₀ : Fin s → ZMod p} (ht : ι (ofAdd t) ∈ E) (ht₀ : ι (ofAdd t₀) ∈ E)
    (a : ZMod p) : ι (ofAdd (t - a • t₀)) ∈ E := by
  rw [ofAdd_sub, map_div]
  exact E.div_mem ht (StepTwoToral.ofAdd_smul_mem ht₀ a)

open Classical in
@[expose] noncomputable def jointSupp (T : Set (Fin s → ZMod p)) : Fin s → ZMod p :=
  fun i => if ∀ t ∈ T, t i = 0 then 0 else 1

open Classical in
@[expose] noncomputable def jointClass (T : Set (Fin s → ZMod p)) (j : Fin s) : Fin s → ZMod p :=
  fun i => if ∀ t ∈ T, t i = t j then 1 else 0

variable {T : Set (Fin s → ZMod p)}

theorem jointSupp_eq_zero_iff [Fact p.Prime] {i : Fin s} :
    jointSupp T i = 0 ↔ ∀ t ∈ T, t i = 0 := by
  unfold jointSupp
  split_ifs with h
  · exact ⟨fun _ => h, fun _ => rfl⟩
  · exact ⟨fun h1 => absurd h1 one_ne_zero, fun h1 => absurd h1 h⟩

theorem jointSupp_zero_or_one (i : Fin s) : jointSupp T i = 0 ∨ jointSupp T i = 1 := by
  unfold jointSupp
  split_ifs
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem jointSupp_eq_of {i j : Fin s} (hij : ∀ t ∈ T, t i = t j) :
    jointSupp T i = jointSupp T j := by
  have h : (∀ t ∈ T, t i = 0) ↔ ∀ t ∈ T, t j = 0 :=
    ⟨fun h t ht => (hij t ht).symm.trans (h t ht), fun h t ht => (hij t ht).trans (h t ht)⟩
  unfold jointSupp
  by_cases hi : ∀ t ∈ T, t i = 0
  · rw [ite_eq_left hi, ite_eq_left (h.mp hi)]
  · rw [ite_eq_right hi, ite_eq_right fun h' => hi (h.mpr h')]

theorem jointClass_eq_one_iff [Fact p.Prime] {i j : Fin s} :
    jointClass T j i = 1 ↔ ∀ t ∈ T, t i = t j := by
  unfold jointClass
  split_ifs with h
  · exact ⟨fun _ => h, fun _ => rfl⟩
  · exact ⟨fun h1 => absurd h1.symm one_ne_zero, fun h1 => absurd h1 h⟩

theorem jointClass_zero_or_one (j i : Fin s) : jointClass T j i = 0 ∨ jointClass T j i = 1 := by
  unfold jointClass
  split_ifs
  · exact Or.inr rfl
  · exact Or.inl rfl

theorem jointClass_eq_of {j i k : Fin s} (hik : ∀ t ∈ T, t i = t k) :
    jointClass T j i = jointClass T j k := by
  have h : (∀ t ∈ T, t i = t j) ↔ ∀ t ∈ T, t k = t j :=
    ⟨fun h t ht => (hik t ht).symm.trans (h t ht), fun h t ht => (hik t ht).trans (h t ht)⟩
  unfold jointClass
  by_cases hi : ∀ t ∈ T, t i = t j
  · rw [ite_eq_left hi, ite_eq_left (h.mp hi)]
  · rw [ite_eq_right hi, ite_eq_right fun h' => hi (h.mpr h')]

theorem jointClass_eq_zero_of_zero {j i : Fin s} {t₀ : Fin s → ZMod p} (ht₀ : t₀ ∈ T)
    (hj : t₀ j ≠ 0) (hi : ∀ t ∈ T, t i = 0) : jointClass T j i = 0 := by
  unfold jointClass
  exact ite_eq_right fun h => hj ((h t₀ ht₀).symm.trans (hi t₀ ht₀))

theorem pow_four_le_of_dual {G : Type} [Group G] [Finite G]
    {ι : Multiplicative (Fin s → ZMod p) →* G} (hinj : Function.Injective ι) {H : Subgroup G}
    (w : Fin 4 → Fin s → ZMod p) (c : Fin 4 → Fin s)
    (hwc : ∀ a b, w a (c b) = if a = b then 1 else 0)
    (hH : ∀ x : Fin 4 → ZMod p, ι (ofAdd (∑ a, x a • w a)) ∈ H) : p ^ 4 ≤ Nat.card H := by
  have heval : ∀ (x : Fin 4 → ZMod p) b, (∑ a, x a • w a) (c b) = x b := by
    intro x b
    rw [Finset.sum_apply]
    simp [hwc]
  have hf : Function.Injective fun x : Fin 4 → ZMod p =>
      (⟨ι (ofAdd (∑ a, x a • w a)), hH x⟩ : H) := by
    intro x y hxy
    have h1 := ofAdd.injective (hinj (congrArg Subtype.val hxy))
    funext b
    have h2 := congrFun h1 (c b)
    rwa [heval, heval] at h2
  have h := Nat.card_le_card_of_injective _ hf
  rwa [Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card (α := Fin 4), Fintype.card_fin] at h

theorem coordShape_of_le_three {G : Type} [Group G] (O : Subgroup (ZMod p)ˣ)
    (ι : Multiplicative (Fin s → ZMod p) →* G) (E : Subgroup G) (hs0 : 0 < s) (hs3 : s ≤ 3) :
    StepTwoToral.GGStepTwoCoordShape p s O ι E := by
  right
  refine ⟨⟨0, hs0⟩, ⟨1 % s, Nat.mod_lt _ hs0⟩, 1, fun _ => O.one_mem,
    fun t _ => ⟨t ⟨s - 1, by omega⟩, fun i hi hi' => ?_⟩⟩
  have h1 : i.val ≠ 0 := fun h => hi (Fin.ext h)
  have h2 : i.val ≠ 1 % s := fun h => hi' (Fin.ext h)
  have h3 := i.isLt
  have h4 : i.val = s - 1 := by
    interval_cases s <;> omega
  rw [Pi.one_apply, Units.val_one, one_mul]
  exact congrArg t (Fin.ext h4)

theorem coordShape_of_mul {G : Type} [Group G] {O : Subgroup (ZMod p)ˣ}
    {ι ι' : Multiplicative (Fin s → ZMod p) →* G} {η : Fin s → (ZMod p)ˣ} (hηO : ∀ i, η i ∈ O)
    (hι : ∀ t, ι' (ofAdd fun i => (η i : ZMod p) * t i) = ι (ofAdd t)) {E : Subgroup G}
    (h : StepTwoToral.GGStepTwoCoordShape p s O ι' E) :
    StepTwoToral.GGStepTwoCoordShape p s O ι E := by
  rcases h with ⟨k, hk⟩ | ⟨j, j', ε, hε, hal⟩
  · left
    refine ⟨k, fun t ht => ?_⟩
    have h1 := hk _ (by rw [hι]; exact ht)
    exact ((η k).isUnit.mul_right_eq_zero).mp h1
  · right
    refine ⟨j, j', fun i => (η i)⁻¹ * ε i, fun i => O.mul_mem (O.inv_mem (hηO i)) (hε i),
      fun t ht => ?_⟩
    obtain ⟨c, hc⟩ := hal _ (by rw [hι]; exact ht)
    refine ⟨c, fun i hij hij' => ?_⟩
    have h1 := hc i hij hij'
    rw [Units.val_mul, mul_assoc, ← h1, ← mul_assoc, ← Units.val_mul, inv_mul_cancel,
      Units.val_one, one_mul]

theorem setOf_mem_eq_image {G : Type} [Group G] {ι ι' : Multiplicative (Fin s → ZMod p) →* G}
    {η : Fin s → (ZMod p)ˣ} (hι : ∀ t, ι' (ofAdd fun i => (η i : ZMod p) * t i) = ι (ofAdd t))
    (E : Subgroup G) :
    {t' | ι' (ofAdd t') ∈ E} = (fun t i => (η i : ZMod p) * t i) '' {t | ι (ofAdd t) ∈ E} := by
  ext t'
  rw [Set.mem_image]
  have heq : (fun i => (η i : ZMod p) * ((((η i)⁻¹ : (ZMod p)ˣ) : ZMod p) * t' i)) = t' := by
    funext i
    rw [← mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mul]
  constructor
  · intro h
    refine ⟨fun i => (((η i)⁻¹ : (ZMod p)ˣ) : ZMod p) * t' i, ?_, heq⟩
    show ι (ofAdd fun i => (((η i)⁻¹ : (ZMod p)ˣ) : ZMod p) * t' i) ∈ E
    rw [← hι, heq]
    exact h
  · rintro ⟨t, ht, rfl⟩
    show ι' (ofAdd fun i => (η i : ZMod p) * t i) ∈ E
    rw [hι]
    exact ht

end CoordShape

end CFSG.StandardType
