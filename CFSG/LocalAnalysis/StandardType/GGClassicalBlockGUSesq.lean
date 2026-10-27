module

public import CFSG.LocalAnalysis.StandardType.GGClassicalBlockDefs
public import CFSG.LieType.SemisimpleCentralizers.HeldUCDTransfer
public import CFSG.CGT.PushingUpLit.SolKNA.R4.RonanResS26FieldAut
public import CFSG.LieType.SemisimpleCentralizers.HeldUCDField

public section

namespace CFSG.StandardType.ClassicalBlocks

open CFSG.LocalAnalysis.ComponentInitial
open CFSG.LieType.SemisimpleCentralizers CFSG.CGT.PushingUpLit.SolKNA.R4
open Matrix

theorem nonempty_sesqUnitaryGroup_mulEquiv_GUFull {K : Type} [Field K] [Finite K] [CharP K 2]
    {W : Type} [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    (ρ : K ≃+* K) (hρ : ∀ x, ρ (ρ x) = x) (hρ1 : ∃ x, ρ x ≠ x)
    (B : W →ₛₗ[(ρ : K →+* K)] W →ₗ[K] K) (hB : ∀ x y, ρ (B x y) = B y x)
    (hBl : ∀ x, (∀ y, B x y = 0) → x = 0) :
    ∃ i : ℕ, Nat.card K = (2 ^ i) ^ 2 ∧
      Nonempty (↥(sesqUnitaryGroup B) ≃* ↥(GUFull (Module.finrank K W) (2 ^ i) K)) := by
  have hρ2 : ρ * ρ = 1 := by
    ext x
    exact hρ x
  have hρne : ρ ≠ 1 := by
    rintro h
    obtain ⟨x, hx⟩ := hρ1
    exact hx (by simpa using congrArg (fun f : K ≃+* K => f x) h)
  obtain ⟨q, hqq, hqpow⟩ := RonanRes.fieldAut_invol_eq_pow hρ2 hρne
  letI : Module (ZMod 2) K := (ZMod.castHom (dvd_refl 2) K).toModule
  have hcard2 : 2 ^ Module.finrank (ZMod 2) K = Nat.card K := FiniteField.pow_finrank_eq_natCard 2 K
  have hdvd : q ∣ 2 ^ Module.finrank (ZMod 2) K := ⟨q, by rw [hcard2]; exact hqq.symm⟩
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  have hcard_i : Nat.card K = (2 ^ i) ^ 2 := by rw [← hqq, hi, pow_two]
  have h1 : 1 < Nat.card K := Finite.one_lt_card
  have hi1 : 1 ≤ i := by
    rcases i with _ | i
    · simp only [pow_zero, one_pow] at hcard_i
      omega
    · omega
  have hpow : ∀ x : K, ρ x = x ^ (2 ^ i) := fun x => by rw [hqpow x, hi]
  have hUFD : UnitaryFieldData 2 i K :=
    { prime := Nat.prime_two, one_le := hi1,
      card := by rw [hcard_i, ← pow_mul, Nat.mul_comm i 2] }
  have hbar : ∀ x : K, hUFD.bar x = ρ x := fun x => by
    rw [hUFD.bar_apply]
    exact (hpow x).symm
  have hnorm : ∀ d : K, ρ d = d → d ≠ 0 → ∃ c : K, ρ c * c = d := by
    intro d hd _
    have hdmem : d ∈ hUFD.fixedField := by
      rw [hUFD.mem_fixedField, hbar]; exact hd
    obtain ⟨c, hc⟩ := hUFD.normHom_surjective ⟨d, hdmem⟩
    have hcval : hUFD.norm c = d := by simpa using congrArg Subtype.val hc
    refine ⟨c, ?_⟩
    rw [← hcval]
    calc ρ c * c = c * ρ c := mul_comm _ _
      _ = c * hUFD.bar c := by rw [hbar]
      _ = hUFD.norm c := rfl
  obtain ⟨c₀, hc₀⟩ := hρ1
  obtain ⟨e, he⟩ := exists_orthonormal_basis_of_norm (B := B) ⟨hB⟩ hBl hc₀ hnorm
  obtain ⟨iso⟩ := HeldUCD.nonempty_mulEquiv_heldGU (d := Module.finrank K W) ρ hρ B e he
  have heq : Held.heldGU (Module.finrank K W) K ρ hρ
      = GUFull (Module.finrank K W) (2 ^ i) K := by
    have hset : (Held.heldGU (Module.finrank K W) K ρ hρ :
        Set (GL (Fin (Module.finrank K W)) K)) =
        {A : GL (Fin (Module.finrank K W)) K |
          ((A : Matrix (Fin (Module.finrank K W)) (Fin (Module.finrank K W)) K).map
          (· ^ (2 ^ i)))ᵀ *
          (A : Matrix (Fin (Module.finrank K W)) (Fin (Module.finrank K W)) K) = 1} := by
      ext A
      rw [SetLike.mem_coe, Held.mem_heldGU, Set.mem_ofPred_eq]
      have hmap : (A : Matrix (Fin (Module.finrank K W)) (Fin (Module.finrank K W)) K).map
          ρ = (A : Matrix (Fin (Module.finrank K W))
            (Fin (Module.finrank K W)) K).map (· ^ (2 ^ i)) := by
        ext a b
        exact hpow _
      rw [hmap]
    rw [GUFull, ← hset, Subgroup.closure_eq]
  exact ⟨i, hcard_i, ⟨iso.trans (MulEquiv.subgroupCongr heq)⟩⟩

end CFSG.StandardType.ClassicalBlocks
