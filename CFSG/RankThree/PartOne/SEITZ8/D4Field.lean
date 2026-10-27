module

import CFSG.RankThree.Chevalley.SteinbergBTTrialityCanonicalField
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LieType.Chevalley.DiagramCoordinateFixedStructure
public import CFSG.RankThree.PartOne.SEITZ8.D4Span

public section

namespace CFSG.RankThree.PartOne.SEITZ8

open CFSG.LieType.Steinberg.TwistedD4

variable {K : Type} [Field K]

theorem span_of_card [Finite K] (F k : Subfield K) {Q p : ℕ} (hQ : 2 ≤ Q) (hp : p.Prime)
    (hp3 : p ≠ 3) (hF : Nat.card F = Q ^ p) (hk : Nat.card k = Q ^ 3)
    (hK : Nat.card K = Q ^ (3 * p)) :
    ∀ x : K, x ∈ AddSubgroup.closure {y | ∃ e ∈ F, ∃ a ∈ k, y = e * a} := by
  classical
  let W : Submodule F K := Submodule.span F (k : Set K)
  have hWk : ∀ a ∈ k, ∀ x ∈ W, a * x ∈ W := by
    intro a ha x hx
    induction hx using Submodule.span_induction with
    | mem y hy => exact Submodule.subset_span (k.mul_mem ha hy)
    | zero => simp
    | add y z _ _ hy hz =>
      rw [mul_add]
      exact W.add_mem hy hz
    | smul c y _ hy =>
      have e : a * (c • y) = c • (a * y) := by
        rw [Algebra.smul_def, Algebra.smul_def]
        ring
      rw [e]
      exact W.smul_mem c hy
  let Wk : Submodule k K :=
    { carrier := W
      add_mem' := W.add_mem
      zero_mem' := W.zero_mem
      smul_mem' := fun a x hx => hWk a a.2 x hx }
  have hcardW : Nat.card W = Nat.card F ^ Module.finrank F W := Module.natCard_eq_pow_finrank
  have hcardWk : Nat.card Wk = Nat.card k ^ Module.finrank k Wk := Module.natCard_eq_pow_finrank
  have hWWk : Nat.card W = Nat.card Wk := Nat.card_congr (Equiv.refl _)
  have hcardK : Nat.card K = Nat.card F ^ Module.finrank F K := Module.natCard_eq_pow_finrank
  have hrK : Module.finrank F K = 3 := by
    rw [hK, hF, ← pow_mul] at hcardK
    have h1 : 3 * p = p * Module.finrank F K := Nat.pow_right_injective hQ hcardK
    exact (Nat.eq_of_mul_eq_mul_left hp.pos ((mul_comm 3 p).symm.trans h1)).symm
  have hle : Module.finrank F W ≤ 3 := hrK ▸ Submodule.finrank_le W
  have hr0 : 0 < Module.finrank F W := by
    rw [Module.finrank_pos_iff_exists_ne_zero]
    exact ⟨⟨1, Submodule.subset_span k.one_mem⟩, fun h => one_ne_zero (congrArg Subtype.val h)⟩
  have heq : Q ^ (p * Module.finrank F W) = Q ^ (3 * Module.finrank k Wk) := by
    rw [pow_mul, pow_mul, ← hF, ← hk, ← hcardW, ← hcardWk, hWWk]
  have hpr : p * Module.finrank F W = 3 * Module.finrank k Wk := Nat.pow_right_injective hQ heq
  have hr3 : Module.finrank F W = 3 := by
    have h3 : 3 ∣ p * Module.finrank F W := ⟨_, hpr⟩
    rcases (Nat.Prime.dvd_mul Nat.prime_three).1 h3 with h | h
    · exact absurd ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).1 h).symm hp3
    · omega
  have hWtop : W = ⊤ := Submodule.eq_top_of_finrank_eq (hr3.trans hrK.symm)
  intro x
  have hx : x ∈ W := hWtop ▸ Submodule.mem_top
  let C : AddSubgroup K := AddSubgroup.closure {y | ∃ e ∈ F, ∃ a ∈ k, y = e * a}
  have hCmul : ∀ (c : F) (y : K), y ∈ C → (c : K) * y ∈ C := by
    intro c y hy
    induction hy using AddSubgroup.closure_induction with
    | mem z hz =>
      obtain ⟨e, he, a, ha, rfl⟩ := hz
      exact AddSubgroup.subset_closure ⟨(c : K) * e, F.mul_mem c.2 he, a, ha, by ring⟩
    | zero => simp
    | add z w _ _ hz hw =>
      rw [mul_add]
      exact C.add_mem hz hw
    | neg z _ hz =>
      rw [mul_neg]
      exact C.neg_mem hz
  induction hx using Submodule.span_induction with
  | mem y hy => exact AddSubgroup.subset_closure ⟨1, F.one_mem, y, hy, (one_mul y).symm⟩
  | zero => exact C.zero_mem
  | add y z _ _ hy hz => exact C.add_mem hy hz
  | smul c y _ hy => exact hCmul c y hy

section FieldData

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

variable [Finite K]

omit [Finite K] in
theorem card_fixedField {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = (2 ^ f) ^ 3) {σ : K →+* K}
    (hσ : ∀ c, σ c = c ^ 2 ^ f) : Nat.card (fixedField σ) = 2 ^ f := by
  obtain ⟨σ₀, -, -, -, -, k, hk, hkc, -⟩ :=
    finite_graph_field_parameter_fields TwistTag.D4 Nat.prime_two hf K hK
  have hfk : fixedField σ = k := by
    apply SetLike.coe_injective
    rw [hk]
    ext c
    simp [fixedField, RingHom.eqLocusField, hσ]
  rw [hfk]
  exact hkc

theorem sigma_pow_on_fix {f0 p : ℕ} {k : Subfield K} (hk : Nat.card k = 2 ^ (3 * f0))
    {a : K} (ha : a ∈ k) : a ^ 2 ^ (f0 * p) = a ^ (2 ^ f0) ^ (p % 3) := by
  have h1 : a ^ 2 ^ (3 * f0) = a :=
    CFSG.RankThree.Chevalley.SteinbergBT.pow_card_eq_self_of_mem hk ha
  have h2 : ∀ m : ℕ, a ^ (2 ^ (3 * f0)) ^ m = a := by
    intro m
    induction m with
    | zero => simp
    | succ m ih => rw [pow_succ, pow_mul, ih, h1]
  have e : 2 ^ (f0 * p) = (2 ^ (3 * f0)) ^ (p / 3) * (2 ^ f0) ^ (p % 3) := by
    rw [← pow_mul, ← pow_mul, ← pow_add]
    congr 1
    calc f0 * p = f0 * (3 * (p / 3) + p % 3) := by rw [Nat.div_add_mod]
      _ = 3 * f0 * (p / 3) + f0 * (p % 3) := by ring
  rw [e, pow_mul, h2]

theorem field_data {f0 p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hf0 : 2 ≤ f0)
    (hK : Nat.card K = 2 ^ (3 * f0 * p)) {σ δ : K ≃+* K}
    (hσ : ∀ c, σ c = c ^ 2 ^ (f0 * p)) (hδ : ∀ c, δ c = c ^ 2 ^ (3 * f0)) :
    ∃ (k : Subfield K) (F0 : Subfield (fixedField σ.toRingHom)),
      (∀ c ∈ k, δ c = c) ∧ Rat3 σ.toRingHom k ∧
      (∀ c : fixedField σ.toRingHom, c ∈ F0 ↔ (c : K) ∈ k) ∧
      Nat.card (fixedField σ.toRingHom) = Nat.card F0 ^ p ∧ 4 ∣ Nat.card F0 ∧
      (∀ x : K, x ∈ AddSubgroup.closure {y | ∃ e : K, σ e = e ∧ ∃ a ∈ k, y = e * a}) := by
  classical
  have hp3 : Nat.Coprime p 3 := (Nat.coprime_primes hp Nat.prime_three).2 (by omega)
  obtain ⟨-, -, -, hk, hord⟩ := CFSG.RankThree.Chevalley.triality_canonical_field_facts
    Nat.prime_two (by omega : 1 ≤ f0) hp.two_le hp3 hK hσ hδ
  set k : Subfield K := fixSubfield δ with hkdef
  have hcardF : Nat.card (fixedField σ.toRingHom) = 2 ^ (f0 * p) :=
    card_fixedField (by nlinarith) (by rw [hK, ← pow_mul]; congr 1; ring) (fun c => hσ c)
  set F0 : Subfield (fixedField σ.toRingHom) := k.comap (fixedField σ.toRingHom).subtype
    with hF0def
  have hF0mem : ∀ c : fixedField σ.toRingHom, c ∈ F0 ↔ (c : K) ∈ k := fun c => Iff.rfl
  set σ0 := fixSubfieldRestrict σ δ with hσ0
  have hS := (CFSG.RankThree.Chevalley.SteinbergBT.card_fixSubfield Nat.prime_two
    (by omega : 1 ≤ 3 * f0) hk σ0).2
  rw [hord, Nat.mul_div_cancel_left f0 (by norm_num : 0 < 3)] at hS
  have hF0card : Nat.card F0 = 2 ^ f0 := by
    rw [← hS]
    exact Nat.card_congr ⟨fun x => ⟨⟨x.1.1, x.2⟩, Subtype.ext x.1.2⟩,
      fun y => ⟨⟨y.1.1, congrArg Subtype.val y.2⟩, y.1.2⟩, fun x => rfl, fun y => rfl⟩
  have hcard : Nat.card (fixedField σ.toRingHom) = Nat.card F0 ^ p := by
    rw [hcardF, hF0card, ← pow_mul]
  have hfour : 4 ∣ Nat.card F0 := by
    rw [hF0card]
    calc 4 = 2 ^ 2 := by norm_num
      _ ∣ 2 ^ f0 := pow_dvd_pow 2 hf0
  have hstab : ∀ a ∈ k, σ.toRingHom a ∈ k := fun a ha => by
    have ha' : δ a = a := ha
    have e : σ a = a ^ 2 ^ (f0 * p) := hσ a
    show δ (σ a) = σ a
    rw [e, map_pow, ha']
  have hkcard : Nat.card k = (2 ^ f0) ^ 3 := by rw [hk, ← pow_mul, mul_comm]
  have hj : p % 3 = 1 ∨ p % 3 = 2 := by
    have h0 : p % 3 ≠ 0 := fun h => by
      have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).1 (Nat.dvd_of_mod_eq_zero h)
      omega
    omega
  have hσk : ∀ a : k, (RingHom.restrict σ.toRingHom k k hstab) a = a ^ (2 ^ f0) ^ (p % 3) := by
    intro a
    apply Subtype.ext
    show σ (a : K) = ((a ^ (2 ^ f0) ^ (p % 3) : k) : K)
    rw [hσ, sigma_pow_on_fix hk a.2]
    rfl
  have hind : MonoInd k (RingHom.restrict σ.toRingHom k k hstab) := by
    have : Fintype k := Fintype.ofFinite k
    exact monoInd_of_frobenius (RingHom.restrict σ.toRingHom k k hstab) (q := 2 ^ f0)
      (by calc 2 = 2 ^ 1 := by norm_num
            _ ≤ 2 ^ f0 := Nat.pow_le_pow_right (by norm_num) (by omega))
      (by rw [← Nat.card_eq_fintype_card, hkcard]) hj hσk
  have hspan := span_of_card (fixedField σ.toRingHom) k (Q := 2 ^ f0) (p := p)
    (by calc 2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ f0 := Nat.pow_le_pow_right (by norm_num) (by omega)) hp (by omega)
    (by rw [hcardF, ← pow_mul]) hkcard (by rw [hK, ← pow_mul]; congr 1; ring)
  exact ⟨k, F0, fun c hc => hc, ⟨hstab, hind⟩, hF0mem, hcard, hfour, hspan⟩

end FieldData

end CFSG.RankThree.PartOne.SEITZ8
