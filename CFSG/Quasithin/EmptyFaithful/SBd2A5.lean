module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Delta5

public section

namespace CFSG.Quasithin

namespace SBd2

open CFSG.QuasithinUnique CFSG.QuasithinUnique.A5.Delta5 Equiv
open scoped Pointwise

private def v4set : Finset (Perm (Fin 5)) :=
  {1, swap 0 1 * swap 2 3, swap 0 2 * swap 1 3, swap 0 3 * swap 1 2}

private theorem v4set_one : (1 : Perm (Fin 5)) ∈ v4set := by decide +kernel

private theorem v4set_mul : ∀ a ∈ v4set, ∀ b ∈ v4set, a * b ∈ v4set := by decide +kernel

private theorem v4set_inv : ∀ a ∈ v4set, a⁻¹ ∈ v4set := by decide +kernel

private theorem v4set_alt : ∀ a ∈ v4set, Perm.sign a = 1 := by decide +kernel

private def v4 : Subgroup Alt5 where
  carrier := {x | (x : Perm (Fin 5)) ∈ v4set}
  mul_mem' := fun {a b} ha hb => v4set_mul a ha b hb
  one_mem' := v4set_one
  inv_mem' := fun {a} ha => v4set_inv a ha

private theorem v4_card : Nat.card v4 = 4 := by
  show Nat.card {x : Alt5 // (x : Perm (Fin 5)) ∈ v4set} = 4
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  decide +kernel

private theorem exists_conj_v4 (Q : Subgroup Alt5) (hQ : Nat.card Q = 4) :
    ∃ g : Alt5, ∀ x : Alt5, x ∈ Q ↔ g⁻¹ * x * g ∈ v4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hf : (Nat.card Alt5).factorization 2 = 2 := by
    rw [a5_card]; decide +kernel
  let PQ : Sylow 2 Alt5 := Sylow.ofCard Q (by rw [hQ, hf]; norm_num)
  let PV : Sylow 2 Alt5 := Sylow.ofCard v4 (by rw [v4_card, hf]; norm_num)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Alt5 PV PQ
  refine ⟨g, fun x => ?_⟩
  have h1 : ((g • PV : Sylow 2 Alt5) : Subgroup Alt5) = (PQ : Subgroup Alt5) := by rw [hg]
  rw [Sylow.coe_subgroup_smul] at h1
  have e : (x ∈ (PQ : Subgroup Alt5)) ↔ x ∈ MulAut.conj g • (PV : Subgroup Alt5) := by rw [← h1]
  have hPQ : (PQ : Subgroup Alt5) = Q := Sylow.coe_ofCard _ _
  have hPV : (PV : Subgroup Alt5) = v4 := Sylow.coe_ofCard _ _
  rw [hPQ, hPV, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at e
  rw [e]
  simp [mul_assoc]

private def gA : Perm (Fin 5) := swap 0 1 * swap 2 3

private def gC : Perm (Fin 5) := c[0, 1, 2]

private theorem gA_mem : gA ∈ v4set := by decide +kernel

private theorem gC_alt : Perm.sign gC = 1 := by decide +kernel

private theorem gC_norm : ∀ x ∈ v4set, gC * x * gC⁻¹ ∈ v4set := by decide +kernel

private theorem key_finite : ∀ x y : Fin 5 → ZMod 2,
    (isEven x ∧ isEven y ∧ x ≠ 0 ∧ y ≠ 0 ∧ x ≠ y ∧
      (pact gA x = x ∨ pact gA x = y ∨ pact gA x = x + y) ∧
      (pact gA y = x ∨ pact gA y = y ∨ pact gA y = x + y) ∧
      (pact gC x = x ∨ pact gC x = y ∨ pact gC x = x + y) ∧
      (pact gC y = x ∨ pact gC y = y ∨ pact gC y = x + y)) → False := by
  decide +kernel

theorem pact_zero_vec (σ : Perm (Fin 5)) : pact σ (0 : Fin 5 → ZMod 2) = 0 := by
  funext i
  rfl

theorem pact_inv_pact_vec (σ : Perm (Fin 5)) (x : Fin 5 → ZMod 2) : pact σ⁻¹ (pact σ x) = x := by
  rw [← pact_mul, inv_mul_cancel, pact_one]

theorem pact_injective_vec (σ : Perm (Fin 5)) : Function.Injective (pact σ) := fun x y h => by
  have := congrArg (pact σ⁻¹) h
  rwa [pact_inv_pact_vec, pact_inv_pact_vec] at this

private theorem isEven_pact (σ : Perm (Fin 5)) {x : Fin 5 → ZMod 2} (hx : isEven x) :
    isEven (pact σ x) :=
  (mem_evenWeight_iff _).mp (pact_mem σ ((mem_evenWeight_iff _).mpr hx))

theorem no_invariant_pair {Q : Subgroup Alt5} (hQ : Nat.card Q = 4) {x y : Fin 5 → ZMod 2}
    (hx : isEven x) (hy : isEven y) (hx0 : x ≠ 0) (hy0 : y ≠ 0) (hxy : x ≠ y)
    (hinv : ∀ σ : Alt5, (∀ q ∈ Q, σ * q * σ⁻¹ ∈ Q) →
      (pact (σ : Perm (Fin 5)) x = x ∨ pact (σ : Perm (Fin 5)) x = y ∨
        pact (σ : Perm (Fin 5)) x = x + y) ∧
      (pact (σ : Perm (Fin 5)) y = x ∨ pact (σ : Perm (Fin 5)) y = y ∨
        pact (σ : Perm (Fin 5)) y = x + y)) : False := by
  obtain ⟨g, hg⟩ := exists_conj_v4 Q hQ
  set x' : Fin 5 → ZMod 2 := pact ((g⁻¹ : Alt5) : Perm (Fin 5)) x with hx'
  set y' : Fin 5 → ZMod 2 := pact ((g⁻¹ : Alt5) : Perm (Fin 5)) y with hy'
  have key : ∀ σ' : Alt5, (∀ z ∈ v4set, (σ' : Perm (Fin 5)) * z * (σ' : Perm (Fin 5))⁻¹ ∈ v4set) →
      (pact (σ' : Perm (Fin 5)) x' = x' ∨ pact (σ' : Perm (Fin 5)) x' = y' ∨
        pact (σ' : Perm (Fin 5)) x' = x' + y') ∧
      (pact (σ' : Perm (Fin 5)) y' = x' ∨ pact (σ' : Perm (Fin 5)) y' = y' ∨
        pact (σ' : Perm (Fin 5)) y' = x' + y') := by
    intro σ' hσ'
    have hnorm : ∀ q ∈ Q, (g * σ' * g⁻¹) * q * (g * σ' * g⁻¹)⁻¹ ∈ Q := by
      intro q hq
      have h1 : g⁻¹ * q * g ∈ v4 := (hg q).mp hq
      have h2 : (σ' : Perm (Fin 5)) * ((g⁻¹ * q * g : Alt5) : Perm (Fin 5)) *
          (σ' : Perm (Fin 5))⁻¹ ∈ v4set := hσ' _ h1
      have h3 : σ' * (g⁻¹ * q * g) * σ'⁻¹ ∈ v4 := by
        show ((σ' * (g⁻¹ * q * g) * σ'⁻¹ : Alt5) : Perm (Fin 5)) ∈ v4set
        simpa using h2
      rw [hg]
      have e : g⁻¹ * ((g * σ' * g⁻¹) * q * (g * σ' * g⁻¹)⁻¹) * g = σ' * (g⁻¹ * q * g) * σ'⁻¹ := by
        group
      rw [e]
      exact h3
    obtain ⟨h1, h2⟩ := hinv _ hnorm
    have hσ : ∀ w : Fin 5 → ZMod 2,
        pact (σ' : Perm (Fin 5)) (pact ((g⁻¹ : Alt5) : Perm (Fin 5)) w) =
          pact ((g⁻¹ : Alt5) : Perm (Fin 5)) (pact ((g * σ' * g⁻¹ : Alt5) : Perm (Fin 5)) w) := by
      intro w
      rw [← pact_mul, ← pact_mul]
      congr 1
      simp [mul_assoc]
    have hadd : pact ((g⁻¹ : Alt5) : Perm (Fin 5)) (x + y) = x' + y' := pact_add _ _ _
    constructor
    · rw [hσ]
      rcases h1 with h | h | h
      · exact Or.inl (by rw [h])
      · exact Or.inr (Or.inl (by rw [h]))
      · exact Or.inr (Or.inr (by rw [h, hadd]))
    · rw [hσ]
      rcases h2 with h | h | h
      · exact Or.inl (by rw [h])
      · exact Or.inr (Or.inl (by rw [h]))
      · exact Or.inr (Or.inr (by rw [h, hadd]))
  have hA := key ⟨gA, Perm.mem_alternatingGroup.mpr (v4set_alt _ gA_mem)⟩
    (by intro z hz; exact (by decide +kernel : ∀ z ∈ v4set, gA * z * gA⁻¹ ∈ v4set) z hz)
  have hC := key ⟨gC, Perm.mem_alternatingGroup.mpr gC_alt⟩ gC_norm
  have hx'0 : x' ≠ 0 := by
    intro h
    apply hx0
    have := congrArg (pact ((g : Alt5) : Perm (Fin 5))) h
    rw [hx'] at this
    have e : pact ((g : Alt5) : Perm (Fin 5)) (pact ((g⁻¹ : Alt5) : Perm (Fin 5)) x) = x := by
      rw [← pact_mul]
      simp [pact_one]
    rw [e, pact_zero_vec] at this
    exact this
  have hy'0 : y' ≠ 0 := by
    intro h
    apply hy0
    have := congrArg (pact ((g : Alt5) : Perm (Fin 5))) h
    rw [hy'] at this
    have e : pact ((g : Alt5) : Perm (Fin 5)) (pact ((g⁻¹ : Alt5) : Perm (Fin 5)) y) = y := by
      rw [← pact_mul]
      simp [pact_one]
    rw [e, pact_zero_vec] at this
    exact this
  have hxy' : x' ≠ y' := by
    intro h
    apply hxy
    have := congrArg (pact ((g : Alt5) : Perm (Fin 5))) h
    rw [hx', hy'] at this
    have e : ∀ w : Fin 5 → ZMod 2, pact ((g : Alt5) : Perm (Fin 5))
        (pact ((g⁻¹ : Alt5) : Perm (Fin 5)) w) = w := by
      intro w
      rw [← pact_mul]
      simp [pact_one]
    rw [e, e] at this
    exact this
  exact key_finite x' y' ⟨isEven_pact _ hx, isEven_pact _ hy, hx'0, hy'0, hxy', hA.1, hA.2, hC.1, hC.2⟩

end SBd2

end CFSG.Quasithin
