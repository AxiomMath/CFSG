module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5P52A
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5P52B

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

namespace FanTree

variable (F : FanTree Γ G)
include F

theorem fan52_ray {v : ℕ → V} (hadj : ∀ j, Γ.Adj (v j) (v (j + 1)))
    (hnb : ∀ j, v j ≠ v (j + 2)) {m : ℕ} (hm : 1 ≤ m) {z : G} (hzz : z * z = 1)
    (hzfix : ∀ j, j ≤ m → z • v j = v j)
    (hzc : ∀ g : G, g • v (m - 1) = v (m - 1) → g • v m = v m → g * z = z * g)
    (hzK : z ∉ nbrStab Γ G (v 0)) {x : G} (hx : x ∈ MulAction.stabilizer G (v 0))
    (hxo : orderOf x = Fan86.valence Γ (v 0)) (f : ℕ → ℕ)
    (hf : ∀ j, 1 ≤ j → j < m → (nbrStab Γ G (v j)).relIndex
      (MulAction.stabilizer G (v j) ⊓ MulAction.stabilizer G (v (j - 1))) ≤ f j) :
    (Subgroup.centralizer ({x} : Set G)).relIndex (nbrStab Γ G (v 0)) ≤
      (∏ j ∈ Finset.Ico 1 m, f j) ^ 2 := by
  have hp := F.valence_isPrime (v 0)
  have hz0 : z ∈ MulAction.stabilizer G (v 0) := MulAction.mem_stabilizer_iff.2 (hzfix 0 (by omega))
  obtain ⟨x₀, hx₀, ho₀, hinv⟩ := F.exists_inverted hz0 hzz ⟨v 1, hadj 0, hzfix 1 hm⟩ hzK hx hxo
  have hle₁ := F.centralizer_relIndex_le hx₀ hx ho₀ hxo
  set K := nbrStab Γ G (v 0) with hK
  have hKfin : Finite K := F.finite_nbrStab (v 0)
  have hx₀v : x₀ • v 0 = v 0 := MulAction.mem_stabilizer_iff.1 hx₀
  have hx₀v' : x₀⁻¹ • v 0 = v 0 := by rw [inv_smul_eq_iff]; exact hx₀v.symm
  set V1 : Subgroup G := K ⊓ MulAction.stabilizer G (v m) with hV1
  set W1 : Subgroup G := K ⊓ MulAction.stabilizer G (x₀ • v m) with hW1
  have hV1z : ∀ u ∈ V1, u * z = z * u := by
    intro u hu
    have h0 : u • v 0 = v 0 := MulAction.mem_stabilizer_iff.1 (F.nbrStab_le_stabilizer _ hu.1)
    have hm' : u • v m = v m := MulAction.mem_stabilizer_iff.1 hu.2
    exact hzc u (F.ray_fixes hadj hnb h0 hm' (m - 1) (by omega)) hm'
  have hUC : V1 ⊓ W1 ≤ Subgroup.centralizer ({x₀} : Set G) := by
    rintro u ⟨hu1, hu2⟩
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    rw [hy]
    have hu'1 : x₀⁻¹ * u * x₀ ∈ V1 := by
      refine ⟨by simpa using nbrStab_conj_mem F hx₀v' hu1.1, MulAction.mem_stabilizer_iff.2 ?_⟩
      have := MulAction.mem_stabilizer_iff.1 hu2.2
      rw [mul_smul, mul_smul, this, inv_smul_smul]
    have hzu := hV1z u hu1
    have hzu' := hV1z _ hu'1
    have e1 : z * x₀⁻¹ = x₀ * z := by
      have h1 : z * x₀⁻¹ * z⁻¹ = x₀ := by
        have := congrArg (·⁻¹) hinv
        simpa [mul_inv_rev, mul_assoc] using this
      calc z * x₀⁻¹ = (z * x₀⁻¹ * z⁻¹) * z := by group
        _ = x₀ * z := by rw [h1]
    have e2 : z * x₀ = x₀⁻¹ * z := by
      calc z * x₀ = (z * x₀ * z⁻¹) * z := by group
        _ = x₀⁻¹ * z := by rw [hinv]
    have key : x₀⁻¹ * u * x₀ = x₀ * u * x₀⁻¹ := by
      refine mul_right_cancel (b := z) ?_
      calc x₀⁻¹ * u * x₀ * z = z * (x₀⁻¹ * u * x₀) := hzu'
        _ = (z * x₀⁻¹) * u * x₀ := by group
        _ = x₀ * z * u * x₀ := by rw [e1]
        _ = x₀ * (z * u) * x₀ := by group
        _ = x₀ * (u * z) * x₀ := by rw [← hzu]
        _ = x₀ * u * (z * x₀) := by group
        _ = x₀ * u * (x₀⁻¹ * z) := by rw [e2]
        _ = x₀ * u * x₀⁻¹ * z := by group
    have hsq : x₀ ^ 2 * u = u * x₀ ^ 2 := by
      have h2 : x₀ * (x₀⁻¹ * u * x₀) * x₀ = x₀ * (x₀ * u * x₀⁻¹) * x₀ := by rw [key]
      rw [pow_two]
      calc x₀ * x₀ * u = x₀ * (x₀ * u * x₀⁻¹) * x₀ := by group
        _ = x₀ * (x₀⁻¹ * u * x₀) * x₀ := h2.symm
        _ = u * (x₀ * x₀) := by group
    have hp2 : Fan86.valence Γ (v 0) ≠ 2 := by
      have := F.valence (v 0)
      change Nat.card _ = 3 ∨ Nat.card _ = 5 at this
      change Nat.card _ ≠ 2
      omega
    have hcop : Nat.Coprime 2 (orderOf x₀) := by
      rw [ho₀]
      exact (Nat.coprime_primes Nat.prime_two hp).2 (Ne.symm hp2)
    obtain ⟨n, hn⟩ := exists_pow_eq_self_of_coprime hcop
    have hc : Commute x₀ u := by
      rw [← hn]
      exact (show Commute (x₀ ^ 2) u from hsq).pow_left n
    exact hc.eq
  have hUfin : (V1 ⊓ W1).relIndex K ≠ 0 := relIndex_ne_zero_of_finite _ _
  have hle₂ : (Subgroup.centralizer ({x₀} : Set G)).relIndex K ≤ (V1 ⊓ W1).relIndex K :=
    Subgroup.relIndex_le_of_le_left hUC hUfin
  have hle₃ : (V1 ⊓ W1).relIndex K ≤ V1.relIndex K * W1.relIndex K := Subgroup.relIndex_inf_le
  have hW : W1.relIndex K = V1.relIndex K := by
    set f : G →* G := (MulAut.conj x₀).toMonoidHom with hfdef
    have hinj : Function.Injective f := (MulAut.conj x₀).injective
    have hKf : K.map f = K := by
      have := F.nbrStab_smul x₀ (v 0)
      rw [hx₀v] at this
      exact this.symm
    have hmap : V1.map f = W1 := by
      rw [hV1, hW1, Subgroup.map_inf _ _ f hinj, hKf,
        MulAction.stabilizer_smul_eq_stabilizer_map_conj]
    rw [← hmap]
    have := Subgroup.relIndex_map_map_of_injective V1 K hinj
    rw [hKf] at this
    exact this
  have hV : V1.relIndex K ≤ ∏ j ∈ Finset.Ico 1 m, f j :=
    F.relIndex_chain hadj hnb f hf m hm le_rfl
  calc (Subgroup.centralizer ({x} : Set G)).relIndex K
      ≤ (Subgroup.centralizer ({x₀} : Set G)).relIndex K := hle₁
    _ ≤ (V1 ⊓ W1).relIndex K := hle₂
    _ ≤ V1.relIndex K * W1.relIndex K := hle₃
    _ = V1.relIndex K ^ 2 := by rw [hW, pow_two]
    _ ≤ (∏ j ∈ Finset.Ico 1 m, f j) ^ 2 := Nat.pow_le_pow_left hV 2

end FanTree

end CFSG.Quasithin.Fan86
