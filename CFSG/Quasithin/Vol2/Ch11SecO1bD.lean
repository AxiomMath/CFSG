module

public import CFSG.Quasithin.Vol2.Ch11SecBK7N

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecO1b

open CFSG.Quasithin CFSG.Quasithin.H13 KGNat SecA
open CFSG.Open (pCoreOf)
open scoped IsMulCommutative commutatorElement

variable {G : Type} [Group G] {V : Subgroup G}

theorem commutator_coe_eq {x : G} (hx : x ∈ Subgroup.normalizer (V : Set G)) (v : ↥V) :
    ⁅(v : G), x⁆ = (((SecA.conjV V x hx v * v⁻¹)⁻¹ : ↥V) : G) :=
  SecB.K7.commutator_eq_inv hx v

theorem comm_le_of {U X P : Subgroup G} (hU : U ≤ V)
    (hXV : X ≤ Subgroup.normalizer (V : Set G))
    (h : ∀ (u : ↥V), (u : G) ∈ U → ∀ x (hx : x ∈ X),
      ((SecA.conjV V x (hXV hx) u * u⁻¹ : ↥V) : G) ∈ P) : ⁅U, X⁆ ≤ P := by
  rw [Subgroup.commutator_le]
  intro u hu x hx
  rw [commutator_coe_eq (hXV hx) ⟨u, hU hu⟩, Subgroup.coe_inv]
  exact P.inv_mem (h ⟨u, hU hu⟩ hu x hx)

variable {K M : Type} [Field K] [AddCommGroup M] [Module K M]
  {f : ↥V → M}

theorem kstable_comm (hmul : ∀ a b : ↥V, f (a * b) = f a + f b) {U X : Subgroup G} (hU : U ≤ V)
    (hUs : ∀ v : ↥V, (v : G) ∈ U → ∀ c : K, ∃ v' : ↥V, (v' : G) ∈ U ∧ f v' = c • f v)
    (hXV : X ≤ Subgroup.normalizer (V : Set G))
    (hlin : ∀ x (hx : x ∈ X), ∃ A : M →ₗ[K] M, ∀ w, f (SecA.conjV V x (hXV hx) w) = A (f w)) :
    ∀ y ∈ ⁅U, X⁆, ∃ hy : y ∈ V, ∀ c : K, ∃ v' : ↥V, (v' : G) ∈ ⁅U, X⁆ ∧
      f v' = c • f ⟨y, hy⟩ := by
  have hf1 : f 1 = 0 := by
    have h := hmul 1 1
    rw [mul_one] at h
    exact left_eq_add.mp h
  have hfinv : ∀ a : ↥V, f a⁻¹ = - f a := fun a => by
    have h := hmul a a⁻¹
    rw [mul_inv_cancel, hf1] at h
    exact eq_neg_of_add_eq_zero_right h.symm
  intro y hy
  rw [Subgroup.commutator_def] at hy ⊢
  induction hy using Subgroup.closure_induction with
  | mem y hy =>
    obtain ⟨u, hu, x, hx, rfl⟩ := hy
    have e2 : ⁅u, x⁆ = (((SecA.conjV V x (hXV hx) ⟨u, hU hu⟩ * ⟨u, hU hu⟩⁻¹)⁻¹ : ↥V) : G) :=
      commutator_coe_eq (hXV hx) ⟨u, hU hu⟩
    have hmem : ⁅u, x⁆ ∈ V := by
      rw [e2]
      exact Subtype.coe_prop _
    refine ⟨hmem, fun c => ?_⟩
    obtain ⟨A, hA⟩ := hlin x hx
    obtain ⟨u', hu', e⟩ := hUs ⟨u, hU hu⟩ hu c
    refine ⟨(SecA.conjV V x (hXV hx) u' * u'⁻¹)⁻¹, ?_, ?_⟩
    · rw [← commutator_coe_eq (hXV hx) u']
      exact Subgroup.subset_closure ⟨u', hu', x, hx, rfl⟩
    · have e3 : (⟨⁅u, x⁆, hmem⟩ : ↥V) =
          (SecA.conjV V x (hXV hx) ⟨u, hU hu⟩ * ⟨u, hU hu⟩⁻¹)⁻¹ := Subtype.ext e2
      rw [e3, hfinv, hfinv, hmul, hmul, hfinv, hfinv, hA, hA, e, map_smul]
      simp only [smul_add, smul_neg, neg_add_rev]
  | one =>
    refine ⟨V.one_mem, fun c => ⟨1, Subgroup.one_mem _, ?_⟩⟩
    rw [hf1, show (⟨1, V.one_mem⟩ : ↥V) = 1 from rfl, hf1, smul_zero]
  | mul y z _ _ hy hz =>
    obtain ⟨hyV, hy⟩ := hy
    obtain ⟨hzV, hz⟩ := hz
    refine ⟨V.mul_mem hyV hzV, fun c => ?_⟩
    obtain ⟨y', hy', e1⟩ := hy c
    obtain ⟨z', hz', e2⟩ := hz c
    refine ⟨y' * z', Subgroup.mul_mem _ hy' hz', ?_⟩
    rw [hmul, e1, e2, show (⟨y * z, V.mul_mem hyV hzV⟩ : ↥V) = ⟨y, hyV⟩ * ⟨z, hzV⟩ from rfl,
      hmul, smul_add]
  | inv y _ hy =>
    obtain ⟨hyV, hy⟩ := hy
    refine ⟨V.inv_mem hyV, fun c => ?_⟩
    obtain ⟨y', hy', e⟩ := hy c
    refine ⟨y'⁻¹, Subgroup.inv_mem _ hy', ?_⟩
    rw [hfinv, e, show (⟨y⁻¹, V.inv_mem hyV⟩ : ↥V) = (⟨y, hyV⟩ : ↥V)⁻¹ from rfl, hfinv,
      smul_neg]

theorem eq_of_kstable_le (hmul : ∀ a b : ↥V, f (a * b) = f a + f b)
    (hinj : Function.Injective f) {P V₁ : Subgroup G} (hV₁V : V₁ ≤ V) {y₁ : M}
    (hV₁ : ∀ v : ↥V, (v : G) ∈ V₁ ↔ ∃ c : K, f v = c • y₁) (hPV₁ : P ≤ V₁) (hP : P ≠ ⊥)
    (hPs : ∀ y ∈ P, ∃ hy : y ∈ V, ∀ c : K, ∃ v' : ↥V, (v' : G) ∈ P ∧ f v' = c • f ⟨y, hy⟩) :
    P = V₁ := by
  have hf1 : f 1 = 0 := by
    have h := hmul 1 1
    rw [mul_one] at h
    exact left_eq_add.mp h
  obtain ⟨p, hp, hp1⟩ := (Subgroup.bot_or_exists_ne_one P).resolve_left hP
  obtain ⟨hpV, hps⟩ := hPs p hp
  obtain ⟨c₀, hc₀⟩ := (hV₁ ⟨p, hpV⟩).mp (hPV₁ hp)
  have hc₀0 : c₀ ≠ 0 := by
    rintro rfl
    rw [zero_smul, ← hf1] at hc₀
    exact hp1 (congrArg Subtype.val (hinj hc₀))
  refine le_antisymm hPV₁ fun x hx => ?_
  obtain ⟨d, hd⟩ := (hV₁ ⟨x, hV₁V hx⟩).mp hx
  obtain ⟨p', hp', e⟩ := hps (d / c₀)
  have : p' = ⟨x, hV₁V hx⟩ := hinj (by rw [e, hc₀, smul_smul, div_mul_cancel₀ _ hc₀0, hd])
  rw [← show ((p' : ↥V) : G) = x from congrArg Subtype.val this]
  exact hp'

theorem relIndex_le_two [Finite G] (hW : CFSG.Open.IsElemAbelian 2 V) {V₃ B : Subgroup G}
    (hV₃ : V₃ ≤ V) (hB : E3.mQuot V₃ B ≤ 1) : B.relIndex V₃ ≤ 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp : IsPGroup 2 ↥V₃ := fun v => ⟨1, by
    rw [pow_one]
    exact Subtype.ext (hW.2 v (hV₃ v.2))⟩
  obtain ⟨N, hN⟩ := IsPGroup.iff_card.mp hp
  have hdvd : B.relIndex V₃ ∣ 2 ^ N := by
    rw [← hN]
    exact Subgroup.relIndex_dvd_card B V₃
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  rw [E3.mQuot, hk, padicValNat.prime_pow] at hB
  rw [hk]
  calc 2 ^ k ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) hB
    _ = 2 := pow_one 2

end CFSG.Quasithin.Vol2.Ch11.SecO1b
