module

public import CFSG.Timmesfeld.Bridge.RootStructR2HigmanLin
public import CFSG.Timmesfeld.ARS.NaturalModule

public section

namespace CFSG.Timmesfeld.Bridge.Higman

open CFSG.Timmesfeld.RankOne CFSG.Timmesfeld.ARS
open scoped Matrix MatrixGroups commutatorElement

variable {G : Type*} [Group G] {K : Type*} [Field K]

structure IsNaturalQuotient {X : Subgroup G} (φ : ↥X ≃* SL(2, K)) (N N₀ : Subgroup G)
    (θ : (Fin 2 → K) → G) : Prop where
  mem : ∀ v, θ v ∈ N
  map_add : ∀ v w, (θ v * θ w)⁻¹ * θ (v + w) ∈ N₀
  eq_zero_of_mem : ∀ v, θ v ∈ N₀ → v = 0
  exists_eq : ∀ n ∈ N, ∃ v, (θ v)⁻¹ * n ∈ N₀
  map_mulVec : ∀ (x : X) (v : Fin 2 → K),
    (θ ((φ x : Matrix (Fin 2) (Fin 2) K) *ᵥ v))⁻¹ * ((x : G) * θ v * (x : G)⁻¹) ∈ N₀

structure IsNaturalExtension {X : Subgroup G} (φ : ↥X ≃* SL(2, K)) (N N₀ : Subgroup G)
    (θ₀ θ₁ : (Fin 2 → K) → G) : Prop where
  le : N₀ ≤ N
  normal : ∀ n ∈ N, ∀ y ∈ N₀, n * y * n⁻¹ ∈ N₀
  conj_mem : ∀ x ∈ X, ∀ n ∈ N, x * n * x⁻¹ ∈ N
  natural : IsNaturalModule φ θ₀
  range : ∀ y, y ∈ N₀ ↔ ∃ v, θ₀ v = y
  quotient : IsNaturalQuotient φ N N₀ θ₁

theorem exists_ne_zero_ne_one [Finite K] (hK : 2 < Nat.card K) : ∃ t : K, t ≠ 0 ∧ t ≠ 1 := by
  classical
  have := Fintype.ofFinite K
  by_contra hcon
  have hsub : (Finset.univ : Finset K) ⊆ {0, 1} := fun t _ => by
    by_cases ht : t = 0
    · simp [ht]
    · by_cases ht' : t = 1
      · simp [ht']
      · exact absurd ⟨t, ht, ht'⟩ hcon
  have := Finset.card_le_card hsub
  rw [Finset.card_univ, ← Nat.card_eq_fintype_card] at this
  have h2 : ({0, 1} : Finset K).card ≤ 2 := Finset.card_le_two
  omega

namespace IsNaturalExtension

variable {X N N₀ : Subgroup G} {φ : ↥X ≃* SL(2, K)} {θ₀ θ₁ : (Fin 2 → K) → G}
  (h : IsNaturalExtension φ N N₀ θ₀ θ₁)
include h

theorem θ₀_mem (v : Fin 2 → K) : θ₀ v ∈ N₀ := (h.range _).mpr ⟨v, rfl⟩

theorem θ₀_mul_self [CharP K 2] (v : Fin 2 → K) : θ₀ v * θ₀ v = 1 := by
  rw [← h.natural.map_add, CharTwo.add_self_eq_zero, h.natural.map_zero]

theorem commute_θ₀ (v w : Fin 2 → K) : Commute (θ₀ v) (θ₀ w) := by
  show θ₀ v * θ₀ w = θ₀ w * θ₀ v
  rw [← h.natural.map_add, ← h.natural.map_add, add_comm]

omit h in
noncomputable def Ψ (θ₀ : (Fin 2 → K) → G) : G → (Fin 2 → K) := Function.invFun θ₀

theorem θ₀_Ψ {y : G} (hy : y ∈ N₀) : θ₀ (Ψ θ₀ y) = y := by
  obtain ⟨v, rfl⟩ := (h.range y).mp hy
  exact Function.invFun_eq ⟨v, rfl⟩

theorem Ψ_θ₀ (v : Fin 2 → K) : Ψ θ₀ (θ₀ v) = v :=
  Function.leftInverse_invFun h.natural.injective v

theorem Ψ_injOn {y y' : G} (hy : y ∈ N₀) (hy' : y' ∈ N₀) (he : Ψ θ₀ y = Ψ θ₀ y') : y = y' := by
  rw [← h.θ₀_Ψ hy, ← h.θ₀_Ψ hy', he]

theorem Ψ_mul {y y' : G} (hy : y ∈ N₀) (hy' : y' ∈ N₀) :
    Ψ θ₀ (y * y') = Ψ θ₀ y + Ψ θ₀ y' := by
  conv_lhs => rw [← h.θ₀_Ψ hy, ← h.θ₀_Ψ hy', ← h.natural.map_add]
  exact h.Ψ_θ₀ _

theorem Ψ_inv {y : G} (hy : y ∈ N₀) : Ψ θ₀ y⁻¹ = -Ψ θ₀ y := by
  conv_lhs => rw [← h.θ₀_Ψ hy, ← h.natural.map_neg]
  exact h.Ψ_θ₀ _

theorem Ψ_eq_zero {y : G} (hy : y ∈ N₀) (h0 : Ψ θ₀ y = 0) : y = 1 := by
  rw [← h.θ₀_Ψ hy, h0, h.natural.map_zero]

theorem conj_mem_N₀ {x : G} (hx : x ∈ X) {y : G} (hy : y ∈ N₀) : x * y * x⁻¹ ∈ N₀ := by
  obtain ⟨v, rfl⟩ := (h.range y).mp hy
  have := h.natural.map_mulVec ⟨x, hx⟩ v
  rw [← this]
  exact h.θ₀_mem _

theorem Ψ_conj {x : G} (hx : x ∈ X) {y : G} (hy : y ∈ N₀) :
    Ψ θ₀ (x * y * x⁻¹) = (φ ⟨x, hx⟩ : Matrix (Fin 2) (Fin 2) K) *ᵥ Ψ θ₀ y := by
  conv_lhs => rw [← h.θ₀_Ψ hy, ← h.natural.map_mulVec ⟨x, hx⟩ (Ψ θ₀ y)]
  exact h.Ψ_θ₀ _

theorem mul_self_of_mem_N₀ [CharP K 2] {y : G} (hy : y ∈ N₀) : y * y = 1 := by
  obtain ⟨v, rfl⟩ := (h.range y).mp hy
  exact h.θ₀_mul_self v

theorem commute_of_mem_N₀ {y y' : G} (hy : y ∈ N₀) (hy' : y' ∈ N₀) : Commute y y' := by
  obtain ⟨v, rfl⟩ := (h.range y).mp hy
  obtain ⟨w, rfl⟩ := (h.range y').mp hy'
  exact h.commute_θ₀ v w

theorem θ₁_zero_mem : θ₁ 0 ∈ N₀ := by
  have := h.quotient.map_add 0 0
  simp only [add_zero, mul_inv_rev, mul_assoc, inv_mul_cancel, mul_one] at this
  simpa using N₀.inv_mem this

theorem class_unique {n : G} {v w : Fin 2 → K} (hv : (θ₁ v)⁻¹ * n ∈ N₀)
    (hw : (θ₁ w)⁻¹ * n ∈ N₀) : v = w := by
  have h1 : (θ₁ v)⁻¹ * θ₁ w ∈ N₀ := by
    have := N₀.mul_mem hv (N₀.inv_mem hw)
    simpa [mul_assoc] using this
  have h2 := h.quotient.map_add v (w - v)
  rw [add_sub_cancel] at h2
  have h3 : (θ₁ (w - v))⁻¹ ∈ N₀ := by
    have := N₀.mul_mem h2 (N₀.inv_mem h1)
    simpa [mul_assoc] using this
  have h4 := h.quotient.eq_zero_of_mem _ (by simpa using N₀.inv_mem h3)
  exact (sub_eq_zero.mp h4).symm

open Classical in
omit h in
noncomputable def cls (N N₀ : Subgroup G) (θ₁ : (Fin 2 → K) → G) (n : G) : Fin 2 → K :=
  if hn : ∃ v, n ∈ N ∧ (θ₁ v)⁻¹ * n ∈ N₀ then Classical.choose hn else 0

theorem cls_spec {n : G} (hn : n ∈ N) : (θ₁ (cls N N₀ θ₁ n))⁻¹ * n ∈ N₀ := by
  have hex : ∃ v, n ∈ N ∧ (θ₁ v)⁻¹ * n ∈ N₀ := by
    obtain ⟨v, hv⟩ := h.quotient.exists_eq n hn
    exact ⟨v, hn, hv⟩
  rw [cls]
  split
  · next h' => exact (Classical.choose_spec h').2
  · next h' => exact absurd hex h'

theorem cls_eq {n : G} (hn : n ∈ N) {v : Fin 2 → K} (hv : (θ₁ v)⁻¹ * n ∈ N₀) :
    cls N N₀ θ₁ n = v :=
  h.class_unique (h.cls_spec hn) hv

theorem cls_θ₁ (v : Fin 2 → K) : cls N N₀ θ₁ (θ₁ v) = v :=
  h.cls_eq (h.quotient.mem v) (by rw [inv_mul_cancel]; exact N₀.one_mem)

theorem cls_of_mem_N₀ {y : G} (hy : y ∈ N₀) : cls N N₀ θ₁ y = 0 :=
  h.cls_eq (h.le hy) (N₀.mul_mem (N₀.inv_mem h.θ₁_zero_mem) hy)

theorem mem_N₀_of_cls {n : G} (hn : n ∈ N) (h0 : cls N N₀ θ₁ n = 0) : n ∈ N₀ := by
  have := h.cls_spec hn
  rw [h0] at this
  have h2 := N₀.mul_mem h.θ₁_zero_mem this
  simpa using h2

theorem cls_mul {n n' : G} (hn : n ∈ N) (hn' : n' ∈ N) :
    cls N N₀ θ₁ (n * n') = cls N N₀ θ₁ n + cls N N₀ θ₁ n' := by
  have hy := h.cls_spec hn
  have hy' := h.cls_spec hn'
  refine h.cls_eq (N.mul_mem hn hn') ?_
  generalize cls N N₀ θ₁ n = v at hy ⊢
  generalize cls N N₀ θ₁ n' = w at hy' ⊢
  have h1 : (θ₁ (v + w))⁻¹ * (θ₁ v * θ₁ w) ∈ N₀ := by
    have := N₀.inv_mem (h.quotient.map_add v w)
    simpa using this
  have h2 : (θ₁ w)⁻¹ * ((θ₁ v)⁻¹ * n) * θ₁ w ∈ N₀ := by
    have := h.normal _ (N.inv_mem (h.quotient.mem w)) _ hy
    simpa using this
  have := N₀.mul_mem (N₀.mul_mem h1 h2) hy'
  convert this using 1
  group

theorem cls_inv {n : G} (hn : n ∈ N) : cls N N₀ θ₁ n⁻¹ = -cls N N₀ θ₁ n := by
  have := h.cls_mul hn (N.inv_mem hn)
  rw [mul_inv_cancel, h.cls_of_mem_N₀ N₀.one_mem] at this
  exact (neg_eq_of_add_eq_zero_right this.symm).symm

theorem cls_conj {x : G} (hx : x ∈ X) {n : G} (hn : n ∈ N) :
    cls N N₀ θ₁ (x * n * x⁻¹) =
      (φ ⟨x, hx⟩ : Matrix (Fin 2) (Fin 2) K) *ᵥ cls N N₀ θ₁ n := by
  have hy := h.cls_spec hn
  refine h.cls_eq (h.conj_mem x hx n hn) ?_
  generalize cls N N₀ θ₁ n = v at hy ⊢
  have h1 := h.quotient.map_mulVec ⟨x, hx⟩ v
  have h2 := h.conj_mem_N₀ hx hy
  have := N₀.mul_mem h1 h2
  convert this using 1
  group

theorem mul_self_mem [CharP K 2] {n : G} (hn : n ∈ N) : n * n ∈ N₀ :=
  h.mem_N₀_of_cls (N.mul_mem hn hn) (by rw [h.cls_mul hn hn, CharTwo.add_self_eq_zero])

theorem pow_four [CharP K 2] {n : G} (hn : n ∈ N) : n ^ 4 = 1 := by
  rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, pow_two, h.mul_self_of_mem_N₀ (h.mul_self_mem hn)]

@[reducible] noncomputable def conjAction : MulAction ↥N ↥N₀ where
  smul n y := ⟨(n : G) * y * (n : G)⁻¹, h.normal n n.2 y y.2⟩
  one_smul y := Subtype.ext (show ((1 : ↥N) : G) * (y : G) * ((1 : ↥N) : G)⁻¹ = y by simp)
  mul_smul n m y := Subtype.ext (show ((n * m : ↥N) : G) * (y : G) * ((n * m : ↥N) : G)⁻¹ =
    (n : G) * ((m : G) * y * (m : G)⁻¹) * (n : G)⁻¹ by simp [mul_assoc])

theorem commute_of_mem_N₀_mem_N [Finite K] [CharP K 2] {y : G} (hy : y ∈ N₀) {n : G}
    (hn : n ∈ N) : Commute n y := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let _ := h.conjAction
  have hP : IsPGroup 2 ↥N := fun g => ⟨2, Subtype.ext (by
    simpa using h.pow_four g.2)⟩
  have hfin : Finite ↥N₀ := by
    have : (N₀ : Set G) = Set.range θ₀ := by
      ext y
      exact h.range y
    rw [← SetLike.coe_sort_coe, this]
    exact Set.finite_range θ₀
  have hcard : 2 ∣ Nat.card ↥N₀ := by
    have : (N₀ : Set G) = Set.range θ₀ := by
      ext y
      exact h.range y
    rw [h.natural.card_eq this]
    have : 2 ∣ Nat.card K := by
      have := Fintype.ofFinite K
      rw [Nat.card_eq_fintype_card]
      exact Nat.dvd_of_mod_eq_zero (FiniteField.even_card_of_char_two (ringChar.eq K 2))
    exact dvd_pow this two_ne_zero
  have hone : (1 : ↥N₀) ∈ MulAction.fixedPoints ↥N ↥N₀ := fun g => Subtype.ext (by
    show (g : G) * 1 * (g : G)⁻¹ = 1
    simp)
  obtain ⟨b, hb, hb1⟩ := hP.exists_fixed_point_of_prime_dvd_card_of_fixed_point _ hcard hone
  let W : AddSubgroup (Fin 2 → K) :=
    { carrier := {v | ∀ n ∈ N, n * θ₀ v * n⁻¹ = θ₀ v}
      add_mem' := fun {v w} hv hw n hn => by
        simp only [Set.mem_ofPred_eq] at hv hw ⊢
        rw [h.natural.map_add, show n * (θ₀ v * θ₀ w) * n⁻¹ =
          (n * θ₀ v * n⁻¹) * (n * θ₀ w * n⁻¹) by group, hv n hn, hw n hn]
      zero_mem' := fun n _ => by simp [h.natural.map_zero]
      neg_mem' := fun {v} hv n hn => by
        simp only [Set.mem_ofPred_eq] at hv ⊢
        rw [h.natural.map_neg, show n * (θ₀ v)⁻¹ * n⁻¹ = (n * θ₀ v * n⁻¹)⁻¹ by group,
          hv n hn] }
  have hW : W = ⊤ := by
    refine addSubgroup_eq_top ?_ ?_
    · intro g v hv n hn
      obtain ⟨x, rfl⟩ := φ.surjective g
      rw [h.natural.map_mulVec x v]
      have hn' : (x : G)⁻¹ * n * x ∈ N := by
        have := h.conj_mem _ (X.inv_mem x.2) n hn
        simpa using this
      have := hv _ hn'
      calc n * ((x : G) * θ₀ v * (x : G)⁻¹) * n⁻¹ =
          (x : G) * (((x : G)⁻¹ * n * x) * θ₀ v * ((x : G)⁻¹ * n * x)⁻¹) * (x : G)⁻¹ := by
            group
        _ = (x : G) * θ₀ v * (x : G)⁻¹ := by rw [this]
    · intro hbot
      apply hb1
      apply Subtype.ext
      have hbW : Ψ θ₀ (b : G) ∈ W := by
        intro n hn
        rw [h.θ₀_Ψ b.2]
        have := congrArg Subtype.val (hb ⟨n, hn⟩)
        exact this
      rw [hbot, AddSubgroup.mem_bot] at hbW
      exact (h.Ψ_eq_zero b.2 hbW).symm
  obtain ⟨v, rfl⟩ := (h.range y).mp hy
  have hv : v ∈ W := by rw [hW]; trivial
  have := hv n hn
  show n * θ₀ v = θ₀ v * n
  calc n * θ₀ v = n * θ₀ v * n⁻¹ * n := by group
    _ = θ₀ v * n := by rw [this]

theorem commutatorElement_mem_N₀ [CharP K 2] {n n' : G} (hn : n ∈ N) (hn' : n' ∈ N) :
    ⁅n, n'⁆ ∈ N₀ := by
  have hm : ⁅n, n'⁆ ∈ N := by
    rw [commutatorElement_def]
    exact N.mul_mem (N.mul_mem (N.mul_mem hn hn') (N.inv_mem hn)) (N.inv_mem hn')
  refine h.mem_N₀_of_cls hm ?_
  rw [commutatorElement_def, h.cls_mul (N.mul_mem (N.mul_mem hn hn') (N.inv_mem hn))
    (N.inv_mem hn'), h.cls_mul (N.mul_mem hn hn') (N.inv_mem hn), h.cls_mul hn hn',
    h.cls_inv hn, h.cls_inv hn']
  abel

theorem commutatorElement_mul_left_N₀ [Finite K] [CharP K 2] {n n' y : G}
    (hn' : n' ∈ N) (hy : y ∈ N₀) : ⁅n * y, n'⁆ = ⁅n, n'⁆ := by
  have hc := h.commute_of_mem_N₀_mem_N hy hn'
  rw [commutatorElement_def, commutatorElement_def, mul_assoc n y n', ← hc.eq]
  group

theorem commutatorElement_mul_right_N₀ [Finite K] [CharP K 2] {n n' y : G} (hn : n ∈ N)
    (hy : y ∈ N₀) : ⁅n, n' * y⁆ = ⁅n, n'⁆ := by
  rw [← commutatorElement_inv, h.commutatorElement_mul_left_N₀ hn hy, commutatorElement_inv]

theorem commutatorElement_mul_left_N [Finite K] [CharP K 2] {n m n' : G} (hn : n ∈ N)
    (hm : m ∈ N) (hn' : n' ∈ N) : ⁅n * m, n'⁆ = ⁅m, n'⁆ * ⁅n, n'⁆ := by
  rw [commutatorElement_mul_left_eq_conj_mul]
  have hc := h.commute_of_mem_N₀_mem_N (h.commutatorElement_mem_N₀ hm hn') hn
  rw [hc.eq, mul_inv_cancel_right]

theorem commutatorElement_mul_right_N [Finite K] [CharP K 2] {n n' m : G} (hn : n ∈ N)
    (hn' : n' ∈ N) (hm : m ∈ N) : ⁅n, n' * m⁆ = ⁅n, n'⁆ * ⁅n, m⁆ := by
  rw [commutatorElement_mul_right_eq_mul_conj]
  have hc := h.commute_of_mem_N₀_mem_N (h.commutatorElement_mem_N₀ hn hm) hn'
  rw [mul_assoc ⁅n, n'⁆ n', hc.eq, ← mul_assoc, mul_inv_cancel_right]

theorem θ₁_add [CharP K 2] (v w : Fin 2 → K) :
    ∃ y ∈ N₀, θ₁ (v + w) = θ₁ v * θ₁ w * y :=
  ⟨_, h.quotient.map_add v w, by group⟩

theorem θ₁_conj {x : G} (hx : x ∈ X) (v : Fin 2 → K) :
    ∃ y ∈ N₀, (x : G) * θ₁ v * x⁻¹ =
      θ₁ ((φ ⟨x, hx⟩ : Matrix (Fin 2) (Fin 2) K) *ᵥ v) * y :=
  ⟨_, h.quotient.map_mulVec ⟨x, hx⟩ v, by group⟩

theorem commute [Finite K] [CharP K 2] (hK : 2 < Nat.card K) {n n' : G} (hn : n ∈ N)
    (hn' : n' ∈ N) : Commute n n' := by
  classical
  obtain ⟨t₀, ht₀, ht₁⟩ := exists_ne_zero_ne_one hK
  set β : (Fin 2 → K) → (Fin 2 → K) → (Fin 2 → K) := fun v w => Ψ θ₀ ⁅θ₁ v, θ₁ w⁆ with hβ
  have hm : ∀ v, θ₁ v ∈ N := h.quotient.mem
  have hβ0 : ∀ v w, β v w = 0 := by
    refine bilinear_eq_zero ht₀ ht₁ β ?_ ?_ ?_
    · intro v v' w
      obtain ⟨y, hy, he⟩ := h.θ₁_add v v'
      simp only [hβ]
      rw [he, h.commutatorElement_mul_left_N₀ (hm w) hy,
        h.commutatorElement_mul_left_N (hm v) (hm v') (hm w),
        h.Ψ_mul (h.commutatorElement_mem_N₀ (hm v') (hm w))
          (h.commutatorElement_mem_N₀ (hm v) (hm w)), add_comm]
    · intro v w w'
      obtain ⟨y, hy, he⟩ := h.θ₁_add w w'
      simp only [hβ]
      rw [he, h.commutatorElement_mul_right_N₀ (hm v) hy,
        h.commutatorElement_mul_right_N (hm v) (hm w) (hm w'),
        h.Ψ_mul (h.commutatorElement_mem_N₀ (hm v) (hm w))
          (h.commutatorElement_mem_N₀ (hm v) (hm w'))]
    · intro g v w
      obtain ⟨x, rfl⟩ := φ.surjective g
      obtain ⟨y, hy, he⟩ := h.θ₁_conj x.2 v
      obtain ⟨y', hy', he'⟩ := h.θ₁_conj x.2 w
      simp only [hβ]
      have hx : φ ⟨(x : G), x.2⟩ = φ x := rfl
      rw [hx] at he he'
      have e1 : θ₁ ((φ x : Matrix (Fin 2) (Fin 2) K) *ᵥ v) =
          (x : G) * θ₁ v * (x : G)⁻¹ * y⁻¹ := by rw [he]; group
      have e2 : θ₁ ((φ x : Matrix (Fin 2) (Fin 2) K) *ᵥ w) =
          (x : G) * θ₁ w * (x : G)⁻¹ * y'⁻¹ := by rw [he']; group
      rw [e1, e2, h.commutatorElement_mul_left_N₀
          (N.mul_mem (h.conj_mem _ x.2 _ (hm w)) (N.inv_mem (h.le hy'))) (N₀.inv_mem hy),
        h.commutatorElement_mul_right_N₀ (h.conj_mem _ x.2 _ (hm v)) (N₀.inv_mem hy')]
      have e3 : ⁅(x : G) * θ₁ v * (x : G)⁻¹, (x : G) * θ₁ w * (x : G)⁻¹⁆ =
          (x : G) * ⁅θ₁ v, θ₁ w⁆ * (x : G)⁻¹ := by
        simp only [commutatorElement_def]
        group
      rw [e3, h.Ψ_conj x.2 (h.commutatorElement_mem_N₀ (hm v) (hm w))]
  have hcθ : ∀ v w, Commute (θ₁ v) (θ₁ w) := by
    intro v w
    have h1 := h.Ψ_eq_zero (h.commutatorElement_mem_N₀ (hm v) (hm w)) (hβ0 v w)
    exact commutatorElement_eq_one_iff_commute.mp h1
  have hdec : ∀ m ∈ N, ∃ v, ∃ y ∈ N₀, m = θ₁ v * y := by
    intro m hm'
    obtain ⟨v, hv⟩ := h.quotient.exists_eq m hm'
    exact ⟨v, _, hv, by group⟩
  obtain ⟨v, y, hy, rfl⟩ := hdec n hn
  obtain ⟨w, y', hy', rfl⟩ := hdec n' hn'
  have c1 := h.commute_of_mem_N₀_mem_N hy (hm w)
  have c2 := h.commute_of_mem_N₀_mem_N hy' (hm v)
  have c3 := h.commute_of_mem_N₀ hy hy'
  exact ((hcθ v w).mul_right c2).mul_left (c1.symm.mul_right c3)

section Squaring

variable [Finite K] [CharP K 2]

theorem exists_lift (hK : 2 < Nat.card K) {l : K} (hl : l ≠ 0) (u : K) :
    ∃ α ∈ N, cls N N₀ θ₁ α = ![u, 0] ∧
      (φ.symm (upperElt K l) : G) * α * (φ.symm (upperElt K l) : G)⁻¹ = α := by
  set g : G := (φ.symm (upperElt K l) : G) with hg
  have hgX : g ∈ X := (φ.symm (upperElt K l)).2
  have hφg : φ ⟨g, hgX⟩ = upperElt K l := by simp [hg]
  have hab : ∀ {m m' : G}, m ∈ N → m' ∈ N → Commute m m' := fun hm hm' => h.commute hK hm hm'
  set n₀ := θ₁ ![u, 0] with hn₀
  have hn₀N : n₀ ∈ N := h.quotient.mem _
  set d := g * n₀ * g⁻¹ * n₀⁻¹ with hd
  have hdN : d ∈ N := N.mul_mem (h.conj_mem g hgX n₀ hn₀N) (N.inv_mem hn₀N)
  have hcd : cls N N₀ θ₁ d = 0 := by
    rw [hd, h.cls_mul (h.conj_mem g hgX n₀ hn₀N) (N.inv_mem hn₀N), h.cls_conj hgX hn₀N,
      h.cls_inv hn₀N, hφg, hn₀, h.cls_θ₁, upperElt_mulVec]
    ext i
    fin_cases i <;> simp
  have hdN₀ : d ∈ N₀ := h.mem_N₀_of_cls hdN hcd
  have hgd : g * d * g⁻¹ = d⁻¹ := by
    have hgg : g * g = 1 := by
      rw [hg, ← Subgroup.coe_mul, ← map_mul, upperElt_mul, CharTwo.add_self_eq_zero,
        upperElt_zero, map_one, Subgroup.coe_one]
    have hgi : g⁻¹ = g := inv_eq_of_mul_eq_one_right hgg
    rw [hd, hgi]
    calc g * (g * n₀ * g * n₀⁻¹) * g = (g * g) * n₀ * g * n₀⁻¹ * g := by group
      _ = n₀ * g * n₀⁻¹ * g := by rw [hgg, one_mul]
      _ = (g * n₀ * g * n₀⁻¹)⁻¹ := by
        rw [show (g * n₀ * g * n₀⁻¹)⁻¹ = n₀ * g⁻¹ * n₀⁻¹ * g⁻¹ by group, hgi]
  have hΨd1 : Ψ θ₀ d 1 = 0 := by
    have e1 := h.Ψ_conj hgX hdN₀
    rw [hgd, h.Ψ_inv hdN₀, hφg, upperElt_mulVec] at e1
    have e2 := congrFun e1 0
    simp only [Pi.neg_apply, Matrix.cons_val_zero, CharTwo.neg_eq] at e2
    have e3 : l * Ψ θ₀ d 1 = 0 := left_eq_add.mp e2
    rcases mul_eq_zero.mp e3 with h0 | h0
    · exact absurd h0 hl
    · exact h0
  set w := Ψ θ₀ d 0 with hw
  set m := θ₀ ![0, w / l] with hm
  have hmN₀ : m ∈ N₀ := h.θ₀_mem _
  have hgm : g * m * g⁻¹ * m⁻¹ = d := by
    refine h.Ψ_injOn (N₀.mul_mem (h.conj_mem_N₀ hgX hmN₀) (N₀.inv_mem hmN₀)) hdN₀ ?_
    rw [h.Ψ_mul (h.conj_mem_N₀ hgX hmN₀) (N₀.inv_mem hmN₀), h.Ψ_conj hgX hmN₀,
      h.Ψ_inv hmN₀, hφg, hm, h.Ψ_θ₀, upperElt_mulVec, eq_vec (Ψ θ₀ d), hΨd1, ← hw]
    ext i
    fin_cases i <;> simp [mul_div_cancel₀ _ hl]
  refine ⟨n₀ * m⁻¹, N.mul_mem hn₀N (N.inv_mem (h.le hmN₀)), ?_, ?_⟩
  · rw [h.cls_mul hn₀N (N.inv_mem (h.le hmN₀)), h.cls_inv (h.le hmN₀), h.cls_of_mem_N₀ hmN₀,
      neg_zero, add_zero, hn₀, h.cls_θ₁]
  · have hc1 := hab (h.conj_mem g hgX _ (h.le hmN₀)) hn₀N
    have hc2 := hab (N.inv_mem (h.le hmN₀)) hn₀N
    calc g * (n₀ * m⁻¹) * g⁻¹ = (g * n₀ * g⁻¹) * (g * m * g⁻¹)⁻¹ := by group
      _ = d * n₀ * (g * m * g⁻¹)⁻¹ := by rw [hd]; group
      _ = (g * m * g⁻¹ * m⁻¹) * n₀ * (g * m * g⁻¹)⁻¹ := by rw [hgm]
      _ = n₀ * m⁻¹ := by
        have := (hab (h.conj_mem g hgX _ (h.le hmN₀)) hn₀N)
        calc g * m * g⁻¹ * m⁻¹ * n₀ * (g * m * g⁻¹)⁻¹ =
            (g * m * g⁻¹) * (m⁻¹ * n₀) * (g * m * g⁻¹)⁻¹ := by group
          _ = (m⁻¹ * n₀) * (g * m * g⁻¹) * (g * m * g⁻¹)⁻¹ := by
              rw [(hab (h.conj_mem g hgX _ (h.le hmN₀))
                (N.mul_mem (N.inv_mem (h.le hmN₀)) hn₀N)).eq]
          _ = n₀ * m⁻¹ := by rw [mul_inv_cancel_right, hc2.eq]

theorem exists_sq_eq (hK : 2 < Nat.card K) :
    ∃ c : K, ∀ m ∈ N, Ψ θ₀ (m * m) = c • cls N N₀ θ₁ m := by
  have hab : ∀ {m m' : G}, m ∈ N → m' ∈ N → Commute m m' := fun hm hm' => h.commute hK hm hm'
  have hm := h.quotient.mem
  have hsq_mem : ∀ v, θ₁ v * θ₁ v ∈ N₀ := fun v => h.mul_self_mem (hm v)
  have hsqy : ∀ {m y : G}, m ∈ N → y ∈ N₀ → (m * y) * (m * y) = m * m := by
    intro m y hm' hy
    have hc := hab hm' (h.le hy)
    calc m * y * (m * y) = m * (y * m) * y := by group
      _ = m * m * (y * y) := by rw [← hc.eq]; group
      _ = m * m := by rw [h.mul_self_of_mem_N₀ hy, mul_one]
  set s : (Fin 2 → K) → (Fin 2 → K) := fun v => Ψ θ₀ (θ₁ v * θ₁ v) with hs
  have hadd : ∀ v w, s (v + w) = s v + s w := by
    intro v w
    obtain ⟨y, hy, he⟩ := h.θ₁_add v w
    simp only [hs]
    rw [he, hsqy (N.mul_mem (hm v) (hm w)) hy]
    have hc := hab (hm v) (hm w)
    rw [show θ₁ v * θ₁ w * (θ₁ v * θ₁ w) = θ₁ v * θ₁ v * (θ₁ w * θ₁ w) by
      calc θ₁ v * θ₁ w * (θ₁ v * θ₁ w) = θ₁ v * (θ₁ w * θ₁ v) * θ₁ w := by group
        _ = θ₁ v * θ₁ v * (θ₁ w * θ₁ w) := by rw [← hc.eq]; group]
    exact h.Ψ_mul (hsq_mem v) (hsq_mem w)
  have hequiv : ∀ (g : SL(2, K)) v, s ((g : Matrix (Fin 2) (Fin 2) K) *ᵥ v) =
      (g : Matrix (Fin 2) (Fin 2) K) *ᵥ s v := by
    intro g v
    obtain ⟨x, rfl⟩ := φ.surjective g
    obtain ⟨y, hy, he⟩ := h.θ₁_conj x.2 v
    have hx : φ ⟨(x : G), x.2⟩ = φ x := rfl
    rw [hx] at he
    simp only [hs]
    have e1 : θ₁ ((φ x : Matrix (Fin 2) (Fin 2) K) *ᵥ v) =
        (x : G) * θ₁ v * (x : G)⁻¹ * y⁻¹ := by rw [he]; group
    rw [e1, hsqy (h.conj_mem _ x.2 _ (hm v)) (N₀.inv_mem hy),
      show (x : G) * θ₁ v * (x : G)⁻¹ * ((x : G) * θ₁ v * (x : G)⁻¹) =
        (x : G) * (θ₁ v * θ₁ v) * (x : G)⁻¹ by group]
    exact h.Ψ_conj x.2 (hsq_mem v)
  obtain ⟨c, hc⟩ := additive_eq_smul s hadd hequiv
  refine ⟨c, fun m hm' => ?_⟩
  have hy := h.cls_spec hm'
  calc Ψ θ₀ (m * m) = Ψ θ₀ ((θ₁ (cls N N₀ θ₁ m) * ((θ₁ (cls N N₀ θ₁ m))⁻¹ * m)) *
        (θ₁ (cls N N₀ θ₁ m) * ((θ₁ (cls N N₀ θ₁ m))⁻¹ * m))) := by rw [mul_inv_cancel_left]
    _ = s (cls N N₀ θ₁ m) := by rw [hsqy (hm _) hy]
    _ = c • cls N N₀ θ₁ m := hc _

omit [Finite K] [CharP K 2] in
theorem commutatorElement_mem {g : G} (hg : g ∈ X) {n : G} (hn : n ∈ N) : ⁅g, n⁆ ∈ N := by
  rw [commutatorElement_def]
  exact N.mul_mem (h.conj_mem g hg n hn) (N.inv_mem hn)

omit [Finite K] [CharP K 2] in
theorem cls_commutatorElement {l : K} {n : G} (hn : n ∈ N) :
    cls N N₀ θ₁ ⁅(φ.symm (upperElt K l) : G), n⁆ = ![l * cls N N₀ θ₁ n 1, 0] := by
  have hgX := (φ.symm (upperElt K l)).2
  rw [commutatorElement_def, h.cls_mul (h.conj_mem _ hgX n hn) (N.inv_mem hn),
    h.cls_conj hgX hn, h.cls_inv hn]
  simp only [Subtype.coe_eta, MulEquiv.apply_symm_apply]
  rw [upperElt_mulVec, eq_vec (cls N N₀ θ₁ n)]
  ext i
  fin_cases i <;> simp

omit [Finite K] [CharP K 2] in
theorem Ψ_commutatorElement {l : K} {y : G} (hy : y ∈ N₀) :
    ⁅(φ.symm (upperElt K l) : G), y⁆ ∈ N₀ ∧
      Ψ θ₀ ⁅(φ.symm (upperElt K l) : G), y⁆ = ![l * Ψ θ₀ y 1, 0] := by
  have hgX := (φ.symm (upperElt K l)).2
  have hmem : (φ.symm (upperElt K l) : G) * y * (φ.symm (upperElt K l) : G)⁻¹ ∈ N₀ :=
    h.conj_mem_N₀ hgX hy
  refine ⟨by rw [commutatorElement_def]; exact N₀.mul_mem hmem (N₀.inv_mem hy), ?_⟩
  rw [commutatorElement_def, h.Ψ_mul hmem (N₀.inv_mem hy), h.Ψ_conj hgX hy, h.Ψ_inv hy]
  simp only [Subtype.coe_eta, MulEquiv.apply_symm_apply]
  rw [upperElt_mulVec, eq_vec (Ψ θ₀ y)]
  ext i
  fin_cases i <;> simp

theorem commutatorElement_mul_N (hK : 2 < Nat.card K) {g : G} (hg : g ∈ X) {n n' : G}
    (hn : n ∈ N) (hn' : n' ∈ N) : ⁅g, n * n'⁆ = ⁅g, n⁆ * ⁅g, n'⁆ := by
  have hc : Commute n⁻¹ (g * n' * g⁻¹ * n'⁻¹) :=
    h.commute hK (N.inv_mem hn) (h.commutatorElement_mem hg hn')
  simp only [commutatorElement_def]
  calc g * (n * n') * g⁻¹ * (n * n')⁻¹ =
      g * n * g⁻¹ * ((g * n' * g⁻¹ * n'⁻¹) * n⁻¹) := by group
    _ = g * n * g⁻¹ * (n⁻¹ * (g * n' * g⁻¹ * n'⁻¹)) := by rw [hc.eq]
    _ = g * n * g⁻¹ * n⁻¹ * (g * n' * g⁻¹ * n'⁻¹) := by group

omit [Finite K] in
theorem commutatorElement_commutatorElement_self {g : G} (hg : g ∈ X) (hgg : g * g = 1)
    {n : G} (hn : n ∈ N) : ⁅g, ⁅g, n⁆⁆ = ⁅g, n⁆ * ⁅g, n⁆ := by
  have hgi : g⁻¹ = g := inv_eq_of_mul_eq_one_right hgg
  have hd := h.commutatorElement_mem hg hn
  have hdd := h.mul_self_of_mem_N₀ (h.mul_self_mem hd)
  have e1 : g * ⁅g, n⁆ * g⁻¹ = ⁅g, n⁆⁻¹ := by
    simp only [commutatorElement_def, hgi]
    calc g * (g * n * g * n⁻¹) * g = (g * g) * n * g * n⁻¹ * g := by group
      _ = n * g * n⁻¹ * g := by rw [hgg, one_mul]
      _ = (g * n * g * n⁻¹)⁻¹ := by
        rw [show (g * n * g * n⁻¹)⁻¹ = n * g⁻¹ * n⁻¹ * g⁻¹ by group, hgi]
  calc ⁅g, ⁅g, n⁆⁆ = g * ⁅g, n⁆ * g⁻¹ * ⁅g, n⁆⁻¹ := commutatorElement_def _ _
    _ = (⁅g, n⁆ * ⁅g, n⁆)⁻¹ := by rw [e1, mul_inv_rev]
    _ = ⁅g, n⁆ * ⁅g, n⁆ := inv_eq_of_mul_eq_one_left hdd

theorem commutatorElement_comm (hK : 2 < Nat.card K) {g g' : G} (hg : g ∈ X) (hg' : g' ∈ X)
    (hgg' : g * g' = g' * g) {n : G} (hn : n ∈ N) : ⁅g, ⁅g', n⁆⁆ = ⁅g', ⁅g, n⁆⁆ := by
  have hab : ∀ {m m' : G}, m ∈ N → m' ∈ N → Commute m m' := fun hm hm' => h.commute hK hm hm'
  set A := g * n * g⁻¹ with hA
  set B := g' * n * g'⁻¹ with hB
  set C := (g * g') * n * (g * g')⁻¹ with hC
  have hAN : A ∈ N := h.conj_mem g hg n hn
  have hBN : B ∈ N := h.conj_mem g' hg' n hn
  have hCN : C ∈ N := h.conj_mem _ (X.mul_mem hg hg') n hn
  have e1 : ⁅g, ⁅g', n⁆⁆ = C * A⁻¹ * (n * B⁻¹) := by
    simp only [commutatorElement_def, hA, hB, hC]
    group
  have e2 : ⁅g', ⁅g, n⁆⁆ = C * B⁻¹ * (n * A⁻¹) := by
    simp only [commutatorElement_def, hA, hB, hC]
    rw [hgg']
    group
  rw [e1, e2]
  have c1 : Commute A⁻¹ (n * B⁻¹) := hab (N.inv_mem hAN) (N.mul_mem hn (N.inv_mem hBN))
  have c2 : Commute n B⁻¹ := hab hn (N.inv_mem hBN)
  calc C * A⁻¹ * (n * B⁻¹) = C * ((n * B⁻¹) * A⁻¹) := by rw [mul_assoc, c1.eq]
    _ = C * ((B⁻¹ * n) * A⁻¹) := by rw [c2.eq]
    _ = C * B⁻¹ * (n * A⁻¹) := by group

theorem mul_self_eq_one (hK : 2 < Nat.card K) {n : G} (hn : n ∈ N) : n * n = 1 := by
  obtain ⟨c, hc⟩ := h.exists_sq_eq hK
  by_cases hc0 : c = 0
  · have := hc n hn
    rw [hc0, zero_smul] at this
    exact h.Ψ_eq_zero (h.mul_self_mem hn) this
  exfalso
  obtain ⟨μ, hμ0, hμ1⟩ := exists_ne_zero_ne_one hK
  set a : G := (φ.symm (upperElt K 1) : G) with ha
  set b : G := (φ.symm (upperElt K μ) : G) with hb
  have haX : a ∈ X := (φ.symm (upperElt K 1)).2
  have hbX : b ∈ X := (φ.symm (upperElt K μ)).2
  have haa : a * a = 1 := by
    rw [ha, ← Subgroup.coe_mul, ← map_mul, upperElt_mul, CharTwo.add_self_eq_zero,
      upperElt_zero, map_one, Subgroup.coe_one]
  have hbb : b * b = 1 := by
    rw [hb, ← Subgroup.coe_mul, ← map_mul, upperElt_mul, CharTwo.add_self_eq_zero,
      upperElt_zero, map_one, Subgroup.coe_one]
  have hab' : a * b = b * a := by
    rw [ha, hb, ← Subgroup.coe_mul, ← Subgroup.coe_mul, ← map_mul, ← map_mul, upperElt_mul,
      upperElt_mul, add_comm]
  choose cA hcAN hcA hcA' using fun u => h.exists_lift hK (l := 1) one_ne_zero u
  choose cB hcBN hcB hcB' using fun u => h.exists_lift hK (l := μ) hμ0 u
  have hfixA : ∀ u, ⁅a, cA u⁆ = 1 := fun u => by
    rw [commutatorElement_def, hcA' u, mul_inv_cancel]
  have hfixB : ∀ u, ⁅b, cB u⁆ = 1 := fun u => by
    rw [commutatorElement_def, hcB' u, mul_inv_cancel]
  have hwN₀ : ∀ u, cA u * (cB u)⁻¹ ∈ N₀ := fun u =>
    h.mem_N₀_of_cls (N.mul_mem (hcAN u) (N.inv_mem (hcBN u))) (by
      rw [h.cls_mul (hcAN u) (N.inv_mem (hcBN u)), h.cls_inv (hcBN u), hcA, hcB, add_neg_cancel])
  set Γ : K → K := fun u => Ψ θ₀ (cA u * (cB u)⁻¹) 1 with hΓ
  have key : ∀ u, Γ (μ * u) = μ * Γ u + c * (1 + μ) * u := by
    intro u
    set y := θ₁ ![0, u] with hy
    have hyN : y ∈ N := h.quotient.mem _
    have hcy : cls N N₀ θ₁ y = ![0, u] := h.cls_θ₁ _
    set p := ⁅a, y⁆ with hp
    set r := ⁅b, y⁆ with hr
    have hpN : p ∈ N := h.commutatorElement_mem haX hyN
    have hrN : r ∈ N := h.commutatorElement_mem hbX hyN
    have hcp : cls N N₀ θ₁ p = ![u, 0] := by
      rw [hp, ha, h.cls_commutatorElement hyN, hcy]
      simp
    have hcr : cls N N₀ θ₁ r = ![μ * u, 0] := by
      rw [hr, hb, h.cls_commutatorElement hyN, hcy]
      simp
    set z := p * (cA u)⁻¹ with hz
    set z' := r * (cB (μ * u))⁻¹ with hz'
    have hzN₀ : z ∈ N₀ := h.mem_N₀_of_cls (N.mul_mem hpN (N.inv_mem (hcAN u))) (by
      rw [h.cls_mul hpN (N.inv_mem (hcAN u)), h.cls_inv (hcAN u), hcp, hcA, add_neg_cancel])
    have hz'N₀ : z' ∈ N₀ := h.mem_N₀_of_cls (N.mul_mem hrN (N.inv_mem (hcBN (μ * u)))) (by
      rw [h.cls_mul hrN (N.inv_mem (hcBN _)), h.cls_inv (hcBN _), hcr, hcB, add_neg_cancel])
    have hpz : p = z * cA u := by rw [hz, inv_mul_cancel_right]
    have hrz : r = z' * cB (μ * u) := by rw [hz', inv_mul_cancel_right]
    have hz1 : Ψ θ₀ z 1 = c * u := by
      have e1 : ⁅a, p⁆ = ⁅a, z⁆ := by
        rw [hpz, h.commutatorElement_mul_N hK haX (h.le hzN₀) (hcAN u), hfixA, mul_one]
      have e2 := h.commutatorElement_commutatorElement_self haX haa hyN
      rw [← hp, e1] at e2
      have e3 := congrFun (congrArg (Ψ θ₀) e2) 0
      rw [hc p hpN, hcp, (h.Ψ_commutatorElement (l := 1) hzN₀).2] at e3
      simpa using e3
    have hz'1 : Ψ θ₀ z' 1 = c * u := by
      have e1 : ⁅b, r⁆ = ⁅b, z'⁆ := by
        rw [hrz, h.commutatorElement_mul_N hK hbX (h.le hz'N₀) (hcBN _), hfixB, mul_one]
      have e2 := h.commutatorElement_commutatorElement_self hbX hbb hyN
      rw [← hr, e1] at e2
      have e3 := congrFun (congrArg (Ψ θ₀) e2) 0
      rw [hc r hrN, hcr, (h.Ψ_commutatorElement (l := μ) hz'N₀).2] at e3
      simp only [Matrix.cons_val_zero, Pi.smul_apply, smul_eq_mul] at e3
      have : μ * (Ψ θ₀ z' 1 - c * u) = 0 := by rw [mul_sub, e3]; ring
      rcases mul_eq_zero.mp this with h0 | h0
      · exact absurd h0 hμ0
      · exact sub_eq_zero.mp h0
    have hw₂ : cB (μ * u) * (cA (μ * u))⁻¹ ∈ N₀ := by
      have := N₀.inv_mem (hwN₀ (μ * u))
      simpa using this
    have hΓ₂ : Ψ θ₀ (cB (μ * u) * (cA (μ * u))⁻¹) 1 = Γ (μ * u) := by
      have : cB (μ * u) * (cA (μ * u))⁻¹ = (cA (μ * u) * (cB (μ * u))⁻¹)⁻¹ := by group
      rw [this, h.Ψ_inv (hwN₀ _)]
      simp [hΓ, CharTwo.neg_eq]
    have har : Ψ θ₀ ⁅a, r⁆ 0 = c * u + Γ (μ * u) := by
      have e1 : cB (μ * u) = (cB (μ * u) * (cA (μ * u))⁻¹) * cA (μ * u) := by group
      rw [hrz, h.commutatorElement_mul_N hK haX (h.le hz'N₀) (hcBN _)]
      conv_lhs => rw [e1, h.commutatorElement_mul_N hK haX (h.le hw₂) (hcAN _), hfixA,
        mul_one]
      rw [h.Ψ_mul (h.Ψ_commutatorElement (l := 1) hz'N₀).1
        (h.Ψ_commutatorElement (l := 1) hw₂).1, (h.Ψ_commutatorElement (l := 1) hz'N₀).2,
        (h.Ψ_commutatorElement (l := 1) hw₂).2, hz'1, hΓ₂]
      simp
    have hbp : Ψ θ₀ ⁅b, p⁆ 0 = μ * (c * u) + μ * Γ u := by
      have e1 : cA u = (cA u * (cB u)⁻¹) * cB u := by group
      rw [hpz, h.commutatorElement_mul_N hK hbX (h.le hzN₀) (hcAN _)]
      conv_lhs => rw [e1, h.commutatorElement_mul_N hK hbX (h.le (hwN₀ u)) (hcBN _), hfixB,
        mul_one]
      rw [h.Ψ_mul (h.Ψ_commutatorElement (l := μ) hzN₀).1
        (h.Ψ_commutatorElement (l := μ) (hwN₀ u)).1, (h.Ψ_commutatorElement (l := μ) hzN₀).2,
        (h.Ψ_commutatorElement (l := μ) (hwN₀ u)).2, hz1]
      simp [hΓ]
    have hcomm := h.commutatorElement_comm hK haX hbX hab' hyN
    rw [← hp, ← hr] at hcomm
    have E : c * u + Γ (μ * u) = μ * (c * u) + μ * Γ u := by rw [← har, ← hbp, hcomm]
    have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
    linear_combination E - c * u * h2
  have := Fintype.ofFinite K
  exact hμ1 (eq_one_of_map_mul hμ0 hc0 Γ key)

end Squaring

end IsNaturalExtension

theorem commutatorElement_mul_left_of_commute {a y b : G} (hyb : Commute y b) :
    ⁅a * y, b⁆ = ⁅a, b⁆ := by
  rw [commutatorElement_def, commutatorElement_def, mul_assoc a y b, hyb.eq]
  group

theorem commutatorElement_mul_right_of_commute {a b y : G} (hya : Commute y a) :
    ⁅a, b * y⁆ = ⁅a, b⁆ := by
  rw [← commutatorElement_inv, commutatorElement_mul_left_of_commute hya, commutatorElement_inv]

theorem commutatorElement_mul_left_of_commute' {a a' b : G} (hc : Commute a ⁅a', b⁆) :
    ⁅a * a', b⁆ = ⁅a', b⁆ * ⁅a, b⁆ := by
  rw [commutatorElement_mul_left_eq_conj_mul, hc.eq, mul_inv_cancel_right]

theorem commutatorElement_mul_right_of_commute' {a b b' : G} (hc : Commute b ⁅a, b'⁆) :
    ⁅a, b * b'⁆ = ⁅a, b⁆ * ⁅a, b'⁆ := by
  rw [commutatorElement_mul_right_eq_mul_conj, mul_assoc ⁅a, b⁆ b, hc.eq, ← mul_assoc,
    mul_inv_cancel_right]

theorem elementary_of_family [Finite K] [CharP K 2] (hK : 2 < Nat.card K) {X N₀ : Subgroup G}
    {φ : ↥X ≃* SL(2, K)} {θ₀ : (Fin 2 → K) → G} {ι : Type*} {N : ι → Subgroup G}
    {θ : ι → (Fin 2 → K) → G} (h : ∀ i, IsNaturalExtension φ (N i) N₀ θ₀ (θ i))
    (hcomm : ∀ i j, ∀ n ∈ N i, ∀ n' ∈ N j, ⁅n, n'⁆ ∈ N₀) :
    (∀ n ∈ ⨆ i, N i, ∀ n' ∈ ⨆ i, N i, Commute n n') ∧ ∀ n ∈ ⨆ i, N i, n * n = 1 := by
  obtain ⟨t₀, ht₀, ht₁⟩ := exists_ne_zero_ne_one hK
  have hij : ∀ i j, ∀ n ∈ N i, ∀ n' ∈ N j, Commute n n' := by
    intro i j
    have hi := h i
    have hj := h j
    have hm : ∀ v, θ i v ∈ N i := hi.quotient.mem
    have hm' : ∀ w, θ j w ∈ N j := hj.quotient.mem
    have hcen : ∀ k, ∀ {y n : G}, y ∈ N₀ → n ∈ N k → Commute n y := fun k _ _ hy hn =>
      (h k).commute_of_mem_N₀_mem_N hy hn
    set β : (Fin 2 → K) → (Fin 2 → K) → (Fin 2 → K) :=
      fun v w => IsNaturalExtension.Ψ θ₀ ⁅θ i v, θ j w⁆ with hβ
    have hβ0 : ∀ v w, β v w = 0 := by
      refine bilinear_eq_zero ht₀ ht₁ β ?_ ?_ ?_
      · intro v v' w
        obtain ⟨y, hy, he⟩ := hi.θ₁_add v v'
        simp only [hβ]
        rw [he, commutatorElement_mul_left_of_commute (hcen j hy (hm' w)).symm,
          commutatorElement_mul_left_of_commute'
            (hcen i (hcomm i j _ (hm v') _ (hm' w)) (hm v)),
          hi.Ψ_mul (hcomm i j _ (hm v') _ (hm' w)) (hcomm i j _ (hm v) _ (hm' w)), add_comm]
      · intro v w w'
        obtain ⟨y, hy, he⟩ := hj.θ₁_add w w'
        simp only [hβ]
        rw [he, commutatorElement_mul_right_of_commute (hcen i hy (hm v)).symm,
          commutatorElement_mul_right_of_commute'
            (hcen j (hcomm i j _ (hm v) _ (hm' w')) (hm' w)),
          hi.Ψ_mul (hcomm i j _ (hm v) _ (hm' w)) (hcomm i j _ (hm v) _ (hm' w'))]
      · intro g v w
        obtain ⟨x, rfl⟩ := φ.surjective g
        obtain ⟨y, hy, he⟩ := hi.θ₁_conj x.2 v
        obtain ⟨y', hy', he'⟩ := hj.θ₁_conj x.2 w
        simp only [hβ]
        have hx : φ ⟨(x : G), x.2⟩ = φ x := rfl
        rw [hx] at he he'
        have e1 : θ i ((φ x : Matrix (Fin 2) (Fin 2) K) *ᵥ v) =
            (x : G) * θ i v * (x : G)⁻¹ * y⁻¹ := by rw [he]; group
        have e2 : θ j ((φ x : Matrix (Fin 2) (Fin 2) K) *ᵥ w) =
            (x : G) * θ j w * (x : G)⁻¹ * y'⁻¹ := by rw [he']; group
        have hxw : (x : G) * θ j w * (x : G)⁻¹ ∈ N j := hj.conj_mem _ x.2 _ (hm' w)
        have hxv : (x : G) * θ i v * (x : G)⁻¹ ∈ N i := hi.conj_mem _ x.2 _ (hm v)
        rw [e1, e2, commutatorElement_mul_left_of_commute
            (hcen j (N₀.inv_mem hy) ((N j).mul_mem hxw ((N j).inv_mem (hj.le hy')))).symm,
          commutatorElement_mul_right_of_commute (hcen i (N₀.inv_mem hy') hxv).symm]
        have e3 : ⁅(x : G) * θ i v * (x : G)⁻¹, (x : G) * θ j w * (x : G)⁻¹⁆ =
            (x : G) * ⁅θ i v, θ j w⁆ * (x : G)⁻¹ := by
          simp only [commutatorElement_def]
          group
        rw [e3, hi.Ψ_conj x.2 (hcomm i j _ (hm v) _ (hm' w))]
    have hcθ : ∀ v w, Commute (θ i v) (θ j w) := fun v w =>
      commutatorElement_eq_one_iff_commute.mp
        (hi.Ψ_eq_zero (hcomm i j _ (hm v) _ (hm' w)) (hβ0 v w))
    intro n hn n' hn'
    obtain ⟨v, hv⟩ := hi.quotient.exists_eq n hn
    obtain ⟨w, hw⟩ := hj.quotient.exists_eq n' hn'
    have en : n = θ i v * ((θ i v)⁻¹ * n) := by group
    have en' : n' = θ j w * ((θ j w)⁻¹ * n') := by group
    rw [en, en']
    have c1 := hcen j hv (hm' w)
    have c2 := hcen i hw (hm v)
    have c3 := hi.commute_of_mem_N₀ hv hw
    exact ((hcθ v w).mul_right c2).mul_left (c1.symm.mul_right c3)
  set S : Set G := ⋃ i, (N i : Set G) with hS
  have hSS : ∀ x ∈ S, ∀ y ∈ S, Commute x y := by
    intro x hx y hy
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hy
    exact hij i j x hi y hj
  rw [Subgroup.iSup_eq_closure]
  have hC : Subgroup.closure S ≤ Subgroup.centralizer S := by
    rw [Subgroup.closure_le]
    intro x hx
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    intro y hy
    exact (hSS y hy x hx).eq
  have hcl : ∀ x ∈ Subgroup.closure S, ∀ y ∈ Subgroup.closure S, Commute x y := by
    intro x hx y hy
    have hy' := hC hy
    have hle : Subgroup.closure S ≤ Subgroup.centralizer {y} := by
      rw [Subgroup.closure_le]
      intro z hz
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
      exact Subgroup.mem_centralizer_iff.mp hy' z hz
    have := Subgroup.mem_centralizer_singleton_iff.mp (hle hx)
    show x * y = y * x
    exact this
  refine ⟨hcl, fun n hn => ?_⟩
  induction hn using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
    exact (h i).mul_self_eq_one hK hi
  | one => exact mul_one 1
  | mul x y hx hy ihx ihy =>
    have hc := hcl x hx y hy
    calc x * y * (x * y) = x * (y * x) * y := by group
      _ = x * x * (y * y) := by rw [← hc.eq]; group
      _ = 1 := by rw [ihx, ihy, mul_one]
  | inv x _ ih => rw [← mul_inv_rev, ih, inv_one]

end CFSG.Timmesfeld.Bridge.Higman
