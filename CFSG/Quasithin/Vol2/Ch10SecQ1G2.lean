module

public import CFSG.Quasithin.Vol2.Ch10SecQ1SL3Hom
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L238BridgeAlt57G2Eq

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecA

namespace C10P01

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall Matrix
open CFSG.QuasithinUnique.Bridge CFSG.QuasithinUnique.Bridge.Alt57Model

variable {K : Type} [Field K] [CharP K 2]

theorem psi_g2X_eq {X : Type} [Group X] (ψ : ↥(cayleyGroup K) →* X)
    (hA : ∀ A : SL3 K, ψ (g2A A) = 1) (a : Fin 3 → K) (ha : a ≠ 0) :
    ψ (g2X a) = ψ (g2X (e0 : Fin 3 → K)) := by
  obtain ⟨B, hB⟩ := MulAction.mem_orbit_iff.mp (mulVec3_e0_mem_orbit a ha)
  have h := congrArg ψ (g2A_mul_g2X B (e0 : Fin 3 → K))
  rw [map_mul, map_mul, hA B, one_mul, mul_one] at h
  have hBa : (B : Matrix (Fin 3) (Fin 3) K) *ᵥ (e0 : Fin 3 → K) = a := hB
  rw [hBa] at h
  exact h.symm

theorem psi_g2Y_eq {X : Type} [Group X] (ψ : ↥(cayleyGroup K) →* X)
    (hA : ∀ A : SL3 K, ψ (g2A A) = 1) (b : Fin 3 → K) (hb : b ≠ 0) :
    ψ (g2Y b) = ψ (g2Y (e0 : Fin 3 → K)) := by
  obtain ⟨B, hB⟩ := MulAction.mem_orbit_iff.mp (mulVec3_e0_mem_orbit b hb)
  set B' : SL3 K := invTransposeFun B
  have hB' : (adjugate (B' : Matrix (Fin 3) (Fin 3) K))ᵀ = (B : Matrix (Fin 3) (Fin 3) K) := by
    change (adjugate ((B⁻¹ : SL3 K) : Matrix (Fin 3) (Fin 3) K)ᵀ)ᵀ = _
    rw [← adjugate_transpose, transpose_transpose]
    change adjugate (adjugate (B : Matrix (Fin 3) (Fin 3) K)) = _
    rw [adjugate_adjugate _ (by simp), B.2]
    simp
  have h := congrArg ψ (g2A_mul_g2Y B' (e0 : Fin 3 → K))
  rw [map_mul, map_mul, hA B', one_mul, mul_one, hB'] at h
  have hBb : (B : Matrix (Fin 3) (Fin 3) K) *ᵥ (e0 : Fin 3 → K) = b := hB
  rw [hBb] at h
  exact h.symm

theorem cayley_hom_trivial [Finite K] (h4 : 4 ≤ Nat.card K) {X : Type} [Group X]
    (ψ : ↥(cayleyGroup K) →* X) (hA : ∀ A : SL3 K, ψ (g2A A) = 1) :
    ∀ g : ↥(cayleyGroup K), ψ g = 1 := by
  obtain ⟨c, hc0, hc1⟩ := exists_ne_zero_one h4
  have hc10 : (1 + c) ≠ 0 := fun h => hc1 (CharTwo.add_eq_zero.1 h).symm
  have hne1 : c • (e0 : Fin 3 → K) ≠ 0 := fun h0 => hc0 (by simpa [e0] using congrFun h0 0)
  have hne2 : (1 + c) • (e0 : Fin 3 → K) ≠ 0 := fun h0 =>
    hc10 (by simpa [e0] using congrFun h0 0)
  have hξ : ψ (g2X (e0 : Fin 3 → K)) = 1 := by
    have h := congrArg ψ (g2X_smul_mul (e0 : Fin 3 → K) 1 c)
    rw [map_mul, one_smul, psi_g2X_eq ψ hA _ hne1, psi_g2X_eq ψ hA _ hne2] at h
    exact mul_left_cancel (a := ψ (g2X (e0 : Fin 3 → K))) (h.trans (mul_one _).symm)
  have hX : ∀ a : Fin 3 → K, ψ (g2X a) = 1 := by
    intro a
    by_cases ha : a = 0
    · rw [ha, g2X_zero, map_one]
    · rw [psi_g2X_eq ψ hA a ha, hξ]
  have hη : ψ (g2Y (e0 : Fin 3 → K)) = 1 := by
    have h := congrArg ψ (g2Y_smul_mul (e0 : Fin 3 → K) 1 c)
    rw [map_mul, one_smul, psi_g2Y_eq ψ hA _ hne1, psi_g2Y_eq ψ hA _ hne2] at h
    exact mul_left_cancel (a := ψ (g2Y (e0 : Fin 3 → K))) (h.trans (mul_one _).symm)
  have hY : ∀ b : Fin 3 → K, ψ (g2Y b) = 1 := by
    intro b
    by_cases hb : b = 0
    · rw [hb, g2Y_zero, map_one]
    · rw [psi_g2Y_eq ψ hA b hb, hη]
  have hle : Subgroup.closure (gensG2 K) ≤ ψ.ker.map (cayleyGroup K).subtype := by
    rw [Subgroup.closure_le]
    rintro g (⟨a, rfl⟩ | ⟨b, rfl⟩ | ⟨A, rfl⟩)
    · exact ⟨g2X a, MonoidHom.mem_ker.2 (hX a), rfl⟩
    · exact ⟨g2Y b, MonoidHom.mem_ker.2 (hY b), rfl⟩
    · exact ⟨g2A A, MonoidHom.mem_ker.2 (hA A), rfl⟩
  intro g
  have hg : (g : quasithinZorn K ≃ₗ[K] quasithinZorn K) ∈ Subgroup.closure (gensG2 K) := by
    rw [← cayleyGroup_eq_closure]
    exact g.2
  obtain ⟨k, hk, hkg⟩ := hle hg
  have : k = g := Subtype.ext hkg
  rw [← this]
  exact MonoidHom.mem_ker.1 hk

end C10P01

open C10P01

theorem factB4aG2_holds :
    FactB4aG2 := by
  intro K _ _ n hn hK X _ hX π hπ
  have : CharP K 2 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    Nat.prime_two (by omega) hK
  have h4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have := nontrivial_of_isShapeGroup hX
  let e : ↥(Explicit.cayleyGroup K) ≃* ↥(CFSG.Open.quasithinG2 K) :=
    MulEquiv.subgroupCongr CFSG.QuasithinUnique.Bridge.Alt57Model.quasithinG2_eq_cayleyGroup.symm
  let ψ : ↥(Explicit.cayleyGroup K) →* X := π.comp e.toMonoidHom
  have hA := sl3_hom_trivial hK hn hX (ψ.comp JonesParshall.g2A)
  have hall := cayley_hom_trivial h4 ψ hA
  obtain ⟨x, hx⟩ := exists_ne (1 : X)
  obtain ⟨g, rfl⟩ := hπ x
  apply hx
  have h1 := hall (e.symm g)
  simpa [ψ] using h1

end CFSG.Quasithin.Vol2.Ch10.SecA
