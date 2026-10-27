module

public import CFSG.LocalAnalysis.WeakClosure81.ThreeOneMatching
public import CFSG.LocalAnalysis.WeakClosure81.ThreeOneTrans
public import CFSG.LocalAnalysis.WeakClosure81.ThreeOneCycle
public import CFSG.LocalAnalysis.WeakClosure81.ThreeOneSmall
public import CFSG.LocalAnalysis.WeakClosure81.ThreeOneSeven
public import CFSG.LocalAnalysis.ComponentClassification.SymmetricLocalBasic

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin Equiv CFSG.LocalAnalysis.UniquenessCase.UC22

namespace ThreeOne

theorem overgroups_of_apply_ne
    {n : ℕ} (hn : 4 < n) {σ : Perm (Fin n)}
    (hσ : ∀ x, σ (σ x) = x) {α : Fin n} (hα : σ α = α) (hfix : ∀ x, x ≠ α → σ x ≠ x)
    {H T K : Subgroup (Perm (Fin n))} (hA : alternatingGroup (Fin n) ≤ H)
    (hT : IsSylowIn 2 T ⊤) (hTσ : T ≤ Subgroup.centralizer {σ})
    (hXK : H ⊓ Subgroup.centralizer {σ} ≤ K) (hKH : K ≤ H) {k : Perm (Fin n)} (hk : k ∈ K)
    (hkα : k α ≠ α) :
    K = H ∨ (Nonempty (↥H ≃* alternatingGroup (Fin 7)) ∧ IsL3 ↥K 1) := by
  have hodd : Odd n := by
    simpa using odd_card_of_apply_eq (Ω := Fin n) hσ hα hfix
  have h2trans : MulAction.IsMultiplyPretransitive K (Fin n) 2 :=
    isMultiplyPretransitive_of_apply_ne hσ hα hfix
      (by rw [Fintype.card_fin]; omega) hA hXK hk hkα
  have hprim : MulAction.IsPreprimitive K (Fin n) :=
    MulAction.isPreprimitive_of_is_two_pretransitive h2trans
  rcases CFSG.ComponentClassification.SymmetricLocal.eq_alternatingGroup_or_eq_top hA with
    hH | hH
  · subst H
    have hsplit : n = 5 ∨ n = 7 ∨ 9 ≤ n := by
      obtain ⟨m, hm⟩ := hodd
      rcases lt_or_ge m 4 with hm4 | hm4
      · have hm2 : 2 ≤ m := by omega
        interval_cases m
        · exact Or.inl (by omega)
        · exact Or.inr (Or.inl (by omega))
      · exact Or.inr (Or.inr (by omega))
    rcases hsplit with hn5 | hn7 | hn9
    · subst hn5
      have h20 : 20 ∣ Nat.card K := by
        have h := card_mul_pred_dvd_card (Ω := Fin 5) (K := K) (by simp) h2trans
        simp only [Fintype.card_fin] at h
        norm_num at h
        exact h
      have hcardA5 : Nat.card (alternatingGroup (Fin 5)) = 60 := by
        rw [nat_card_alternatingGroup, Nat.card_fin]
        norm_num
      have hKdvd : Nat.card K ∣ 60 := by
        have h := Subgroup.card_dvd_of_le hKH
        rwa [hcardA5] at h
      have hm : Nat.card K = 20 ∨ Nat.card K = 60 := by
        obtain ⟨a, ha⟩ := h20
        obtain ⟨b, hb⟩ := hKdvd
        have hab : a * b = 3 := by
          refine Nat.mul_left_cancel (by norm_num : 0 < 20) ?_
          rw [← Nat.mul_assoc, ← ha, ← hb]
        have hadvd : a ∣ 3 := ⟨b, hab.symm⟩
        rcases (Nat.dvd_prime Nat.prime_three).mp hadvd with ha1 | ha3
        · left; rw [ha, ha1]
        · right; rw [ha, ha3]
      rcases hm with hm20 | hm60
      · exfalso
        have hne : K ≠ alternatingGroup (Fin 5) := by
          intro h
          have h60 : Nat.card K = 60 := by rw [h, hcardA5]
          omega
        have hf := card_alternatingGroup_dvd_factorial (Ω := Fin 5) (K := K)
          (by simp) hKH hne
        have hrel : K.relIndex (alternatingGroup (Fin 5)) = 3 := by
          have hrc := Subgroup.relIndex_mul_card (H := K) (K := alternatingGroup (Fin 5))
          rw [inf_eq_left.mpr hKH, hcardA5, hm20] at hrc
          omega
        rw [hrel, hcardA5] at hf
        norm_num at hf
      · left
        exact Subgroup.eq_of_le_of_card_ge (H := K) (K := alternatingGroup (Fin 5)) hKH
          (by rw [hcardA5, hm60])
    · subst hn7
      have h42 : 42 ∣ Nat.card K := by
        have h := card_mul_pred_dvd_card (Ω := Fin 7) (K := K) (by simp) h2trans
        simp only [Fintype.card_fin] at h
        norm_num at h
        exact h
      have hPerm7 : Nat.card (Perm (Fin 7)) = 2 ^ 4 * 315 := by
        rw [Nat.card_perm, Nat.card_fin]
        decide
      have hTcard : Nat.card T = 16 := by
        have h := card_eq_of_isSylowIn_top (G := Perm (Fin 7)) hT (k := 4) (m := 315) hPerm7
          (by norm_num)
        norm_num at h
        exact h
      have hSylowA7 : IsSylowIn 2 (T ⊓ alternatingGroup (Fin 7)) (alternatingGroup (Fin 7)) :=
        isSylowIn_inf_alternatingGroup hT
      have h8 : Nat.card ↥(T ⊓ alternatingGroup (Fin 7)) = 8 := by
        have h := two_mul_card_inf_alternatingGroup (Ω := Fin 7) hT (by simp)
        rw [hTcard] at h
        omega
      have hSK : T ⊓ alternatingGroup (Fin 7) ≤ K := by
        intro x hx
        rw [Subgroup.mem_inf] at hx
        exact hXK (Subgroup.mem_inf.mpr ⟨hx.2, hTσ hx.1⟩)
      have h8dvd : 8 ∣ Nat.card K := by
        have h := Subgroup.card_dvd_of_le hSK
        rwa [h8] at h
      have h168dvd : 168 ∣ Nat.card K := by
        have h := Nat.lcm_dvd h42 h8dvd
        rwa [show Nat.lcm 42 8 = 168 from by decide] at h
      have hcardA7 : Nat.card (alternatingGroup (Fin 7)) = 2520 := by
        rw [nat_card_alternatingGroup, Nat.card_fin]
        norm_num
      have hsix := card_mem_of_le_alternatingGroup_seven (S := T ⊓ alternatingGroup (Fin 7))
        (K := K) hKH hSylowA7 hSK
      rcases hsix with h | h | h | h | h | h | h
      · exfalso; rw [h] at h168dvd; norm_num at h168dvd
      · exfalso; rw [h] at h168dvd; norm_num at h168dvd
      · exfalso; rw [h] at h168dvd; norm_num at h168dvd
      · exfalso; rw [h] at h168dvd; norm_num at h168dvd
      · right
        exact ⟨⟨MulEquiv.refl _⟩, isL3_of_card_eq_168 hKH hSylowA7 hSK h⟩
      · exfalso; rw [h] at h168dvd; norm_num at h168dvd
      · left
        exact Subgroup.eq_of_le_of_card_ge (H := K) (K := alternatingGroup (Fin 7)) hKH
          (by omega)
    · left
      obtain ⟨c, hcK, hc3⟩ :=
        exists_isThreeCycle_mem_of_apply_ne hσ hα hfix (by simpa using hn9) hA hXK hk hkα
      exact le_antisymm hKH
        (Equiv.Perm.alternatingGroup_le_of_isPreprimitive_of_isThreeCycle_mem hprim hc3 hcK)
  · left
    have hswap : swap (k α) (σ (k α)) ∈ K := by
      apply hXK
      rw [hH]
      exact Subgroup.mem_inf.mpr ⟨Subgroup.mem_top _, swap_apply_mem_centralizer hσ (k α)⟩
    have hKtop : K = ⊤ :=
      Equiv.Perm.subgroup_eq_top_of_isPreprimitive_of_isSwap_mem hprim (swap (k α) (σ (k α)))
        ⟨k α, σ (k α), (hfix (k α) hkα).symm, rfl⟩ hswap
    exact hKtop.trans hH.symm

end ThreeOne

end CFSG.LocalAnalysis.WeakClosure81

end
