module

public import CFSG.RankThree.PartOne.KS.PlaneOddGeneric
public import CFSG.RankThree.PartOne.KS.Assembly

public section

namespace CFSG.RankThree.PartOne

open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)

@[expose] def ConjWitness (A : Type) [Group A] (p : ℕ) : Prop :=
  ∀ (v : MulAut A) (x : A), orderOf v = 2 → orderOf x = p → v * MulAut.conj x = MulAut.conj x * v →
    ∃ l : List A, (∀ g ∈ l, g * x = x * g) ∧
      p ∣ orderOf ((l.map fun g => MulAut.conj g * v * (MulAut.conj g)⁻¹).prod)

theorem ConjWitness.of_mulEquiv {A A' : Type} [Group A] [Group A'] {p : ℕ} (e : A ≃* A')
    (h : ConjWitness A' p) : ConjWitness A p := by
  intro v x hv hx hc
  set φ : MulAut A ≃* MulAut A' := MulAut.congr e with hφ
  have hconj : ∀ y : A, φ (MulAut.conj y) = MulAut.conj (e y) := fun y => by
    ext z
    simp [hφ, MulAut.congr_apply, MulAut.conj_apply]
  have hv' : orderOf (φ v) = 2 := by rw [MulEquiv.orderOf_eq]; exact hv
  have hx' : orderOf (e x) = p := by rw [MulEquiv.orderOf_eq]; exact hx
  have hc' : φ v * MulAut.conj (e x) = MulAut.conj (e x) * φ v := by
    rw [← hconj, ← map_mul, ← map_mul, hc]
  obtain ⟨l, hl, hord⟩ := h (φ v) (e x) hv' hx' hc'
  refine ⟨l.map e.symm, ?_, ?_⟩
  · intro g hg
    obtain ⟨g', hg', rfl⟩ := List.mem_map.mp hg
    have := hl g' hg'
    apply e.injective
    simpa using this
  · have h1 : φ (((l.map e.symm).map fun g => MulAut.conj g * v * (MulAut.conj g)⁻¹).prod) =
        (l.map fun g => MulAut.conj g * φ v * (MulAut.conj g)⁻¹).prod := by
      rw [map_list_prod, List.map_map, List.map_map]
      congr 1
      apply List.map_congr_left
      intro g _
      simp only [Function.comp, map_mul, map_inv, hconj, MulEquiv.apply_symm_apply]
    rw [← MulEquiv.orderOf_eq φ, h1]
    exact hord

theorem isPGroup_le_inner_of_not_dvd_card_outer {T : Type} [Group T] [Finite T] {p : ℕ}
    (hp : p.Prime) (h : ¬ p ∣ Nat.card (Outer T)) :
    ∀ S : Subgroup (MulAut T), IsPGroup p S → S ≤ (MulAut.conj : T →* MulAut T).range := by
  intro S hS a ha
  have hfin : Finite (MulAut T) := Finite.of_injective _ (DFunLike.coe_injective (F := MulAut T))
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨k, hk⟩ := hS ⟨a, ha⟩
  have hak : a ^ p ^ k = 1 := by
    have := congrArg Subtype.val hk
    rwa [Subgroup.coe_pow, Subgroup.coe_one] at this
  have h1 : orderOf (QuotientGroup.mk' (inner T) a) ∣ p ^ k :=
    orderOf_dvd_of_pow_eq_one (by rw [← map_pow, hak, map_one])
  have h2 : orderOf (QuotientGroup.mk' (inner T) a) ∣ Nat.card (Outer T) :=
    orderOf_dvd_natCard _
  have hcop : Nat.Coprime (p ^ k) (Nat.card (Outer T)) :=
    Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hp).2 h)
  have h3 := Nat.eq_one_of_dvd_coprimes hcop h1 h2
  rw [orderOf_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h3
  exact h3

theorem planeLocalCoreOdd_of_conjWitness {T A : Type} [Group T] [Finite T] [IsSimpleGroup T]
    [Group A] (hnab : ∃ a b : T, a * b ≠ b * a) (e : T ≃* A) {p : ℕ} (hp : p.Prime)
    (hout : ¬ p ∣ Nat.card (Outer T)) (h : ConjWitness A p) : PlaneLocalCoreOdd p T :=
  planeLocalCoreOdd_of_conjugate_witnesses hp (isPGroup_le_inner_of_not_dvd_card_outer hp hout)
    (conj_injective_of_center_eq_bot (center_eq_bot_of_simple hnab)) (h.of_mulEquiv e)

theorem sporadicPlaneOdd_of_conjWitness {A : Type} [Group A] (S : Finset ℕ)
    (hW : ∀ q ∈ S, q.Prime → ConjWitness A q)
    (hOut : ∀ (T : Type) [Group T] [Finite T] [IsSimpleGroup T], (∃ a b : T, a * b ≠ b * a) →
      Nonempty (T ≃* A) → ∀ q ∈ S, q.Prime → ¬ q ∣ Nat.card (Outer T))
    (hno : ∀ (T : Type) [Group T] [Finite T] [IsSimpleGroup T], (∃ a b : T, a * b ≠ b * a) →
      Nonempty (T ≃* A) → ∀ p : ℕ, p.Prime → 3 < p → p ∉ S → ¬ p ^ 2 ∣ Nat.card (MulAut T)) :
    SporadicPlaneOdd A := by
  intro T _ _ _ hnab hTA p hp hp3
  by_cases hpS : p ∈ S
  · obtain ⟨e⟩ := hTA
    exact planeLocalCoreOdd_of_conjWitness hnab e hp (hOut T hnab ⟨e⟩ p hpS hp) (hW p hpS hp)
  · exact planeLocalCoreOdd_of_not_sq_dvd (hno T hnab hTA p hp hp3 hpS)

end CFSG.RankThree.PartOne
