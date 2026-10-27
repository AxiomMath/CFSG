module

public import CFSG.RankThree.PartTwo.Sec21.FF79Lemma43KFacts
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.AutAlternating

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF79

open Equiv Equiv.Perm Subgroup

set_option synthInstance.maxSize 2000 in
set_option synthInstance.maxHeartbeats 200000 in
theorem ff79A5_finite_check :
    ∀ π : Perm (Fin 5), π * π = 1 → ∀ γ : Perm (Fin 5), sign γ = 1 → γ ^ 3 = 1 → γ ≠ 1 →
      π * γ = γ * π → ∀ k : Perm (Fin 5), sign k = 1 → k ^ 4 = 1 → k ≠ 1 → π * k = k * π →
        ∃ c : Perm (Fin 5), sign c = 1 ∧ π * c = c * π ∧ (c * k * c⁻¹ * k⁻¹) ^ 4 ≠ 1 := by
  decide +kernel

theorem ff79A5_two_el_pow_four {x : alternatingGroup (Fin 5)} (h : Is2El x) : x ^ 4 = 1 := by
  obtain ⟨m, hm⟩ := h
  have h1 : orderOf x ∣ 2 ^ m := orderOf_dvd_of_pow_eq_one hm
  have h2 : orderOf x ∣ 60 := by
    have := orderOf_dvd_natCard x
    rwa [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin] at this
  obtain ⟨j, hj, hj'⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h1
  have hj3 : j ≤ 2 := by
    by_contra hc
    have h8 : 2 ^ 3 ∣ 2 ^ j := pow_dvd_pow 2 (by omega)
    rw [← hj'] at h8
    have := h8.trans h2
    omega
  rw [← orderOf_dvd_iff_pow_eq_one, hj']
  calc 2 ^ j ∣ 2 ^ 2 := pow_dvd_pow 2 hj3
    _ = 4 := by norm_num

theorem ff79KO2A5_holds : FF79KO2A5 := by
  intro φ hφ γ hγ hφγ k hφk hk1 hk2
  obtain ⟨π, rfl⟩ := (CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 5
    (by norm_num) (by norm_num)).2 φ
  have hinj := (CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 5
    (by norm_num) (by norm_num)).1
  have hππ : π * π = 1 := by
    apply hinj
    rw [map_mul, map_one]
    exact hφ
  have hcomm : ∀ x : alternatingGroup (Fin 5), MulAut.conjNormal π x = x →
      π * (x : Perm (Fin 5)) = (x : Perm (Fin 5)) * π := by
    intro x hx
    have := congrArg (fun a : alternatingGroup (Fin 5) => (a : Perm (Fin 5))) hx
    simp only [MulAut.conjNormal_apply] at this
    exact mul_inv_eq_iff_eq_mul.mp this
  have hγ3 : (γ : Perm (Fin 5)) ^ 3 = 1 := by
    have := pow_orderOf_eq_one γ
    rw [hγ] at this
    exact congrArg Subtype.val this
  have hγ1 : (γ : Perm (Fin 5)) ≠ 1 := by
    intro h
    have : γ = 1 := Subtype.ext h
    rw [this, orderOf_one] at hγ
    omega
  have hk4 : (k : Perm (Fin 5)) ^ 4 = 1 := congrArg Subtype.val (ff79A5_two_el_pow_four hk2)
  have hk1' : (k : Perm (Fin 5)) ≠ 1 := fun h => hk1 (Subtype.ext h)
  obtain ⟨c, hcs, hcπ, hc4⟩ := ff79A5_finite_check π hππ γ
    (mem_alternatingGroup.mp γ.2) hγ3 hγ1 (hcomm γ hφγ) k (mem_alternatingGroup.mp k.2)
    hk4 hk1' (hcomm k hφk)
  refine ⟨⟨c, mem_alternatingGroup.mpr hcs⟩, ?_, ?_⟩
  · apply Subtype.ext
    rw [MulAut.conjNormal_apply]
    exact mul_inv_eq_iff_eq_mul.mpr hcπ
  · intro h
    exact hc4 (congrArg Subtype.val (ff79A5_two_el_pow_four h))

end CFSG.RankThree.PartTwo.Sec21.FF79
