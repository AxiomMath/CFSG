module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsLieCoprime
public import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.Quasithin.H13.CTK

open CFSG.QuasithinUnique.Vol2Native.L239.Lie
open scoped commutatorElement

variable {S : Type} [Group S]

theorem commutatorElement_mul_right' (q k r : S) :
    ⁅q, k * r⁆ = ⁅q, k⁆ * (k * ⁅q, r⁆ * k⁻¹) := by
  simp only [commutatorElement_def]; group

theorem commutator_le_of_decomp {Q K B Z : Subgroup S}
    (hKQ : K ≤ Subgroup.normalizer (Q : Set S))
    (hL : ∀ b ∈ B, ∃ k ∈ K, ∃ r ∈ Q, b = k * r)
    (hZ : ∀ q ∈ Q, ∀ k ∈ K, ⁅q, k⁆ ∈ Z) : ⁅Q, B⁆ ≤ Z ⊔ ⁅Q, Q⁆ := by
  refine Subgroup.commutator_le.2 fun q hq b hb => ?_
  obtain ⟨k, hk, r, hr, rfl⟩ := hL b hb
  rw [commutatorElement_mul_right']
  refine Subgroup.mul_mem _ (Subgroup.mem_sup_left (hZ q hq k hk)) (Subgroup.mem_sup_right ?_)
  have hkq : ∀ x ∈ Q, k * x * k⁻¹ ∈ Q := fun x hx =>
    (Subgroup.mem_normalizer_iff.1 (hKQ hk) x).1 hx
  have : k * ⁅q, r⁆ * k⁻¹ = ⁅k * q * k⁻¹, k * r * k⁻¹⁆ := by
    simp only [commutatorElement_def]; group
  rw [this]
  exact Subgroup.commutator_mem_commutator (hkq q hq) (hkq r hr)

section Finite

variable [Finite S]

theorem commutator_mem_of_relIndex_le_two {Q Q' : Subgroup S} (h2 : Q'.relIndex Q ≤ 2) {x : S}
    (hxQ : x ∈ Subgroup.normalizer (Q : Set S)) (hxQ' : x ∈ Subgroup.normalizer (Q' : Set S))
    {q : S} (hq : q ∈ Q) : ⁅q, x⁆ ∈ Q' := by
  have hxq : x * q * x⁻¹ ∈ Q := (Subgroup.mem_normalizer_iff.1 hxQ q).1 hq
  have hcomm : ⁅q, x⁆ = q * (x * q * x⁻¹)⁻¹ := by simp only [commutatorElement_def]; group
  by_cases hqQ' : q ∈ Q'
  · have : x * q * x⁻¹ ∈ Q' := (Subgroup.mem_normalizer_iff.1 hxQ' q).1 hqQ'
    rw [hcomm]
    exact Q'.mul_mem hqQ' (Q'.inv_mem this)
  · have hxqQ' : x * q * x⁻¹ ∉ Q' := fun h => hqQ' ((Subgroup.mem_normalizer_iff.1 hxQ' q).2 h)
    have hne : Q'.relIndex Q ≠ 0 := Subgroup.index_ne_zero_of_finite
    have hne1 : Q'.relIndex Q ≠ 1 := fun h1 => hqQ' ((Subgroup.relIndex_eq_one.1 h1) hq)
    have h2' : Q'.relIndex Q = 2 := by omega
    obtain ⟨a, ha⟩ := Subgroup.index_eq_two_iff.1 h2'
    have h1 := ha ⟨q, hq⟩
    have h3 := ha ⟨x * q * x⁻¹, hxq⟩
    have hq1 : q * (a : S) ∈ Q' := by
      rcases h1 with ⟨h, -⟩ | ⟨h, -⟩
      · exact h
      · exact absurd (Subgroup.mem_subgroupOf.1 h) hqQ'
    have hq2 : (x * q * x⁻¹) * (a : S) ∈ Q' := by
      rcases h3 with ⟨h, -⟩ | ⟨h, -⟩
      · exact h
      · exact absurd (Subgroup.mem_subgroupOf.1 h) hxqQ'
    rw [hcomm]
    have := Q'.mul_mem hq1 (Q'.inv_mem hq2)
    simpa [mul_assoc] using this

theorem le_normalizer_of_relIndex_le_two {Q Q' : Subgroup S} (hQ'Q : Q' ≤ Q)
    (h2 : Q'.relIndex Q ≤ 2) : Q ≤ Subgroup.normalizer (Q' : Set S) := by
  rw [← Subgroup.normal_subgroupOf_iff_le_normalizer hQ'Q]
  have hne : Q'.relIndex Q ≠ 0 := Subgroup.index_ne_zero_of_finite
  by_cases h1 : Q'.relIndex Q = 1
  · have : Q ≤ Q' := Subgroup.relIndex_eq_one.1 h1
    have heq : Q'.subgroupOf Q = ⊤ := by
      rw [Subgroup.subgroupOf_eq_top]
      exact this
    rw [heq]
    infer_instance
  · have : (Q'.subgroupOf Q).index = 2 := by
      have : Q'.relIndex Q = 2 := by omega
      exact this
    exact Subgroup.normal_of_index_eq_two this

theorem abelian_of_levi_decomp {Q B K V N : Subgroup S}
    (hQ2 : IsPGroup 2 Q) (hKQ : K ≤ Subgroup.normalizer (Q : Set S))
    (hKN : K ≤ N) (hNK : N ≤ Subgroup.normalizer (K : Set S))
    (hKQV : K ⊓ Q ≤ V) (hV : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a)
    (hidx : (Q ⊓ N).relIndex Q ≤ 2)
    (hQB : Q ≤ ⁅Q, B⁆) (hL : ∀ b ∈ B, ∃ k ∈ K, ∃ r ∈ Q, b = k * r) :
    ∀ x ∈ Q, ∀ y ∈ Q, x * y = y * x := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQQ : Q ≤ Subgroup.normalizer (Q : Set S) := Subgroup.le_normalizer
  have hKQ' : K ≤ Subgroup.normalizer ((Q ⊓ N : Subgroup S) : Set S) := fun k hk =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨hKQ hk, Subgroup.le_normalizer (hKN hk)⟩
  have h1 : ∀ q ∈ Q, ∀ k ∈ K, ⁅q, k⁆ ∈ Q ⊓ N := fun q hq k hk =>
    commutator_mem_of_relIndex_le_two hidx (hKQ hk) (hKQ' hk) hq
  have h2 : Q ≤ (Q ⊓ N) ⊔ ⁅Q, Q⁆ := hQB.trans (commutator_le_of_decomp hKQ hL h1)
  have h3 : Q ≤ Q ⊓ N :=
    le_of_le_sup_commutator_of_isPGroup (Y := Q) (N := Q) (Z := Q ⊓ N) hQ2 le_rfl inf_le_left
      (le_normalizer_of_relIndex_le_two inf_le_left hidx) h2
  have hQN : Q ≤ N := fun x hx => (h3 hx).2
  have h4 : ∀ q ∈ Q, ∀ k ∈ K, ⁅q, k⁆ ∈ K ⊓ Q := by
    intro q hq k hk
    have hqK : q * k * q⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.1 (hNK (hQN hq)) k).1 hk
    have hkq : k * q⁻¹ * k⁻¹ ∈ Q := (Subgroup.mem_normalizer_iff.1 (hKQ hk) q⁻¹).1 (Q.inv_mem hq)
    refine ⟨?_, ?_⟩
    · have : ⁅q, k⁆ = (q * k * q⁻¹) * k⁻¹ := by simp [commutatorElement_def, mul_assoc]
      rw [this]
      exact K.mul_mem hqK (K.inv_mem hk)
    · have : ⁅q, k⁆ = q * (k * q⁻¹ * k⁻¹) := by simp [commutatorElement_def, mul_assoc]
      rw [this]
      exact Q.mul_mem hq hkq
  have h5 : Q ≤ (K ⊓ Q) ⊔ ⁅Q, Q⁆ := hQB.trans (commutator_le_of_decomp hKQ hL h4)
  have hZn : Q ≤ Subgroup.normalizer ((K ⊓ Q : Subgroup S) : Set S) := fun x hx =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨hNK (hQN hx), hQQ hx⟩
  have h6 : Q ≤ K ⊓ Q :=
    le_of_le_sup_commutator_of_isPGroup (Y := Q) (N := Q) (Z := K ⊓ Q) hQ2 le_rfl inf_le_right
      hZn h5
  intro x hx y hy
  exact hV x (hKQV (h6 hx)) y (hKQV (h6 hy))

end Finite

end CFSG.Quasithin.H13.CTK
