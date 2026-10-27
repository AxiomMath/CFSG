module

public import CFSG.Quasithin.Background.SmithB42L2Base
public import CFSG.Quasithin.Background.C1PackSL2

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.Assembly.LowTwoRank
open scoped MatrixGroups

theorem burnsideC121_p4_psl_equiv {G : Type} [Group G] {n : ℕ} (h : IsPSL 2 2 n G) :
    2 ≤ n ∧ ∃ (K : Type) (_ : Field K) (_ : Fintype K), Fintype.card K = 2 ^ n ∧
      Nonempty (G ≃* SL(2, K)) := by
  obtain ⟨hadm, K, hK, hKfin, hcard, ⟨e⟩⟩ := h
  obtain ⟨-, hn1, -, hne, -⟩ := hadm
  have hn2 : 2 ≤ n := by
    by_contra hlt
    have hn : n = 1 := by omega
    subst hn
    exact hne rfl
  let _ : Fintype K := Fintype.ofFinite K
  have hc : Fintype.card K = 2 ^ n := by rw [← Nat.card_eq_fintype_card, hcard]
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP K 2 := charP_of_card_eq_prime_pow hc
  exact ⟨hn2, K, hK, inferInstance, hc,
    ⟨e.trans ((projectiveSpecialLinearGroupEquivStatedProj 2 K).symm.trans
      ((QuotientGroup.quotientMulEquivOfEq B42L2.center_sl2_eq_bot).trans
        QuotientGroup.quotientBot))⟩⟩

theorem burnsideC121_p4_perm3_gen : ∀ σ τ : Equiv.Perm (Fin 3), σ ≠ 1 → τ ^ 3 = 1 →
    ∃ g h : Equiv.Perm (Fin 3), τ = g * σ * g⁻¹ * (h * σ * h⁻¹) ∨ τ = g * σ * g⁻¹ := by
  decide

theorem burnsideC121_p4_cube_of_odd {G : Type*} [Group G] [Finite G] (h6 : Nat.card G = 6)
    {x : G} (hx : Odd (orderOf x)) : x ^ 3 = 1 := by
  have hd : orderOf x ∣ 2 * 3 := by
    rw [show 2 * 3 = 6 by norm_num, ← h6]
    exact orderOf_dvd_natCard x
  have hc : Nat.Coprime (orderOf x) 2 := (Nat.coprime_two_left.2 hx).symm
  exact orderOf_dvd_iff_pow_eq_one.1 (hc.dvd_of_dvd_mul_left hd)

theorem burnsideC121_p4_sl2F2_cube {x : C1Pack.SL2F2} (hx : Odd (orderOf x)) : x ^ 3 = 1 :=
  burnsideC121_p4_cube_of_odd C1Pack.card_sl2F2 hx

theorem burnsideC121_p4_card_perm3 : Nat.card (Equiv.Perm (Fin 3)) = 6 := by
  rw [Nat.card_perm, Nat.card_fin]
  rfl

theorem burnsideC121_p4_s3_normal {G : Type} [Group G] (e : G ≃* Equiv.Perm (Fin 3))
    (N : Subgroup G) (hN : N.Normal) : N = ⊥ ∨ ∀ τ : G, Odd (orderOf τ) → τ ∈ N := by
  by_cases hb : N = ⊥
  · exact Or.inl hb
  right
  intro τ hτ
  obtain ⟨⟨σ, hσN⟩, hσ1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hb
  have hσ1' : e σ ≠ 1 := by
    intro h
    apply hσ1
    exact Subtype.ext (e.injective (h.trans (map_one e).symm))
  have hfin : Finite (Equiv.Perm (Fin 3)) := inferInstance
  have hτ3 : (e τ) ^ 3 = 1 := by
    have hoe : orderOf (e τ) = orderOf τ := MulEquiv.orderOf_eq e τ
    exact burnsideC121_p4_cube_of_odd burnsideC121_p4_card_perm3 (hoe ▸ hτ)
  obtain ⟨g, h, hgh⟩ := burnsideC121_p4_perm3_gen (e σ) (e τ) hσ1' hτ3
  have hconj : ∀ k : Equiv.Perm (Fin 3), e.symm k * σ * (e.symm k)⁻¹ ∈ N :=
    fun k => hN.conj_mem σ hσN (e.symm k)
  rcases hgh with hgh | hgh
  · have : τ = e.symm g * σ * (e.symm g)⁻¹ * (e.symm h * σ * (e.symm h)⁻¹) := by
      apply e.injective
      simp only [map_mul, map_inv, MulEquiv.apply_symm_apply]
      exact hgh
    rw [this]
    exact N.mul_mem (hconj g) (hconj h)
  · have : τ = e.symm g * σ * (e.symm g)⁻¹ := by
      apply e.injective
      simp only [map_mul, map_inv, MulEquiv.apply_symm_apply]
      exact hgh
    rw [this]
    exact hconj g

end CFSG.Quasithin
