module

public import CFSG.Quasithin.Background.E5Two

public section

namespace CFSG.Quasithin
namespace E5

open CFSG.Open CFSG.QuasithinUnique
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem pow_mul_mul_pow_inv {u q w : G} (hxw : u * w = w * u) (hstep : u * q * u⁻¹ = w * q)
    (m : ℕ) : u ^ m * q * (u ^ m)⁻¹ = w ^ m * q := by
  induction m with
  | zero => simp
  | succ n ih =>
    have hxwn : u * w ^ n = w ^ n * u := (Commute.pow_right hxw n).eq
    calc u ^ (n + 1) * q * (u ^ (n + 1))⁻¹ = u * (u ^ n * q * (u ^ n)⁻¹) * u⁻¹ := by group
      _ = u * (w ^ n * q) * u⁻¹ := by rw [ih]
      _ = w ^ n * (u * q * u⁻¹) := by
        rw [← mul_assoc u, hxwn]; group
      _ = w ^ (n + 1) * q := by rw [hstep]; group

theorem le_centralizer_of_stab {U Q Q₀ : Subgroup G} (hU : twoResidual U = U)
    (hQ : IsPGroup 2 Q) (hUQ : U ≤ Subgroup.normalizer (Q : Set G))
    (hUC : U ≤ Subgroup.centralizer (Q₀ : Set G)) (hQ₀ : Q₀ ≤ Q)
    (hcomm : ∀ u ∈ U, ∀ q ∈ Q, ⁅u, q⁆ ∈ Q₀) :
    U ≤ Subgroup.centralizer (Q : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hle : twoResidual U ≤ U ⊓ Subgroup.centralizer (Q : Set G) := by
    refine twoResidual_le_of_isTwoQuotient inf_le_left ?_ ?_
    · intro x hx
      rw [Subgroup.mem_normalizer_iff]
      intro y
      have hxN : x ∈ Subgroup.normalizer (U : Set G) := Subgroup.le_normalizer hx
      have hxC : x ∈ Subgroup.normalizer (Subgroup.centralizer (Q : Set G) : Set G) :=
        mem_normalizer_centralizer (hUQ hx)
      constructor
      · rintro ⟨hy1, hy2⟩
        exact ⟨(Subgroup.mem_normalizer_iff.1 hxN y).1 hy1,
          (Subgroup.mem_normalizer_iff.1 hxC y).1 hy2⟩
      · rintro ⟨hy1, hy2⟩
        exact ⟨(Subgroup.mem_normalizer_iff.1 hxN y).2 hy1,
          (Subgroup.mem_normalizer_iff.1 hxC y).2 hy2⟩
    · intro u hu
      obtain ⟨n, hn⟩ := hQ.exists_card_eq
      refine ⟨n, Subgroup.mem_inf.2 ⟨U.pow_mem hu _, ?_⟩⟩
      rw [Subgroup.mem_centralizer_iff]
      intro q hq
      have hd : ⁅u, q⁆ ∈ Q₀ := hcomm u hu q hq
      have hdQ : ⁅u, q⁆ ∈ Q := hQ₀ hd
      have h1 : ⁅u, q⁆ ^ 2 ^ n = 1 := by
        have := pow_card_eq_one' (x := (⟨⁅u, q⁆, hdQ⟩ : ↥Q))
        rw [hn] at this
        exact congrArg Subtype.val this
      have hstep : u * q * u⁻¹ = ⁅u, q⁆ * q := by
        rw [commutatorElement_def]; group
      have hxw : u * ⁅u, q⁆ = ⁅u, q⁆ * u := (Subgroup.mem_centralizer_iff.1 (hUC hu) _ hd).symm
      have h2 := pow_mul_mul_pow_inv hxw hstep (2 ^ n)
      rw [h1, one_mul] at h2
      calc q * u ^ 2 ^ n = (u ^ 2 ^ n * q * (u ^ 2 ^ n)⁻¹) * u ^ 2 ^ n := by rw [h2]
        _ = u ^ 2 ^ n * q := by group
  rw [hU] at hle
  exact hle.trans inf_le_right

omit [Finite G] in
theorem le_normalizer_stabilizer {K Q W : Subgroup G}
    (hKQ : K ≤ Subgroup.normalizer (Q : Set G)) (hKW : K ≤ Subgroup.normalizer (W : Set G)) :
    K ≤ Subgroup.normalizer
      ((K ⊓ Subgroup.centralizer (W : Set G) ⊓ quotStab Q W : Subgroup G) : Set G) := by
  intro k hk
  rw [Subgroup.mem_normalizer_iff]
  have key : ∀ k ∈ K, ∀ x ∈ K ⊓ Subgroup.centralizer (W : Set G) ⊓ quotStab Q W,
      k * x * k⁻¹ ∈ K ⊓ Subgroup.centralizer (W : Set G) ⊓ quotStab Q W := by
    intro k hk x ⟨⟨hxK, hxC⟩, hxN, hxS⟩
    refine ⟨⟨K.mul_mem (K.mul_mem hk hxK) (K.inv_mem hk), ?_⟩, ?_, ?_⟩
    · exact (Subgroup.mem_normalizer_iff.1 (mem_normalizer_centralizer (hKW hk)) x).1 hxC
    · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (hKW hk) hxN) (Subgroup.inv_mem _ (hKW hk))
    · intro q hq
      have hq' : k⁻¹ * q * k⁻¹⁻¹ ∈ Q :=
        (Subgroup.mem_normalizer_iff.1 (hKQ (K.inv_mem hk)) q).1 hq
      have e : ⁅k * x * k⁻¹, q⁆ = k * ⁅x, k⁻¹ * q * k⁻¹⁻¹⁆ * k⁻¹ := by
        simp only [commutatorElement_def]; group
      rw [e]
      exact (Subgroup.mem_normalizer_iff.1 (hKW hk) _).1 (hxS _ hq')
  intro x
  refine ⟨fun hx => key k hk x hx, fun hx => ?_⟩
  have := key k⁻¹ (K.inv_mem hk) _ hx
  simpa [mul_assoc] using this

theorem twoResidual_stabilizer_le {K Q W : Subgroup G} (hWQ : W ≤ Q) (hQ : IsPGroup 2 Q)
    (hKQ : K ≤ Subgroup.normalizer (Q : Set G)) :
    twoResidual (K ⊓ Subgroup.centralizer (W : Set G) ⊓ quotStab Q W) ≤
      Subgroup.centralizer (Q : Set G) := by
  set X := K ⊓ Subgroup.centralizer (W : Set G) ⊓ quotStab Q W with hXdef
  have hXK : X ≤ K := inf_le_left.trans inf_le_left
  have hle : twoResidual X ≤ X ⊓ Subgroup.centralizer (Q : Set G) := by
    refine twoResidual_le_of_isTwoQuotient inf_le_left ?_ ?_
    · intro x hx
      rw [Subgroup.mem_normalizer_iff]
      intro y
      have hxN : x ∈ Subgroup.normalizer (X : Set G) := Subgroup.le_normalizer hx
      have hxC : x ∈ Subgroup.normalizer (Subgroup.centralizer (Q : Set G) : Set G) :=
        mem_normalizer_centralizer (hKQ (hXK hx))
      constructor
      · rintro ⟨hy1, hy2⟩
        exact ⟨(Subgroup.mem_normalizer_iff.1 hxN y).1 hy1,
          (Subgroup.mem_normalizer_iff.1 hxC y).1 hy2⟩
      · rintro ⟨hy1, hy2⟩
        exact ⟨(Subgroup.mem_normalizer_iff.1 hxN y).2 hy1,
          (Subgroup.mem_normalizer_iff.1 hxC y).2 hy2⟩
    · intro y hy
      obtain ⟨k, m, hm, hkm⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos y).ne'
      refine ⟨k, X.pow_mem hy _, ?_⟩
      have hord : orderOf (y ^ 2 ^ k) = m := by
        rw [orderOf_pow_of_dvd (by positivity) (hkm ▸ dvd_mul_right _ _), hkm,
          Nat.mul_div_cancel_left _ (by positivity)]
      have hyX := X.pow_mem hy (2 ^ k)
      exact mem_centralizer_of_odd hWQ hQ hyX.1.2 hyX.2 (hord ▸ hm)
  exact hle.trans inf_le_right

end E5
end CFSG.Quasithin
