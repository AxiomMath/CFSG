module

public import CFSG.LocalAnalysis.WeakClosure81.ThreeOneMatching
public import CFSG.LocalAnalysis.WeakClosure81.ThreeOneTrans
public import CFSG.LocalAnalysis.WeakClosure81.ThreeOneCycle
public import CFSG.LocalAnalysis.WeakClosure81.ThreeOneEvenEight
public import CFSG.LocalAnalysis.ComponentClassification.SymmetricLocalBasic

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin Equiv

namespace ThreeOne

private lemma eq_120_or_360_of_dvd {k : ℕ} (h120 : 120 ∣ k) (h360 : k ∣ 360) :
    k = 120 ∨ k = 360 := by
  obtain ⟨a, rfl⟩ := h120
  have ha3 : a ≤ 3 := by
    have hle := Nat.le_of_dvd (by norm_num : 0 < 360) h360
    omega
  have ha1 : 1 ≤ a := by
    rcases Nat.eq_zero_or_pos a with h | h
    · exfalso; rw [h] at h360; norm_num at h360
    · exact h
  interval_cases a
  · left; norm_num
  · exfalso; norm_num at h360
  · right; norm_num

theorem overgroups_of_forall_apply_ne {Ω : Type} [Fintype Ω]
    [DecidableEq Ω] (h6 : 6 ≤ Fintype.card Ω) {σ : Perm Ω} (hσ : ∀ x, σ (σ x) = x)
    (hfix : ∀ x, σ x ≠ x) {H T K : Subgroup (Perm Ω)} (hA : alternatingGroup Ω ≤ H)
    (hT : IsSylowIn 2 T ⊤) (hTσ : T ≤ Subgroup.centralizer {σ})
    (hXK : H ⊓ Subgroup.centralizer {σ} ≤ K) (hKH : K ≤ H) :
    K = H ∨ K = H ⊓ Subgroup.centralizer {σ} ∨
      (Fintype.card Ω = 8 ∧ H = alternatingGroup Ω ∧ IsE8L3 K) := by
  classical
  by_cases hKC : K ≤ Subgroup.centralizer {σ}
  · exact Or.inr (Or.inl (le_antisymm (le_inf hKH hKC) hXK))
  · have hKtrans : MulAction.IsMultiplyPretransitive K Ω 2 :=
      isMultiplyPretransitive_of_not_le_centralizer hσ hfix h6 hA hXK hKC
    have hprim : MulAction.IsPreprimitive K Ω :=
      MulAction.isPreprimitive_of_is_two_pretransitive hKtrans
    rcases CFSG.ComponentClassification.SymmetricLocal.eq_alternatingGroup_or_eq_top hA with
      hH | hH
    · have hKAlt : K ≤ alternatingGroup Ω := by rw [← hH]; exact hKH
      by_cases h10 : 10 ≤ Fintype.card Ω
      · obtain ⟨c, hcK, hc3⟩ :=
          exists_isThreeCycle_mem_of_not_le_centralizer hσ hfix h10 hA hXK hKC
        have hAle : alternatingGroup Ω ≤ K :=
          Equiv.Perm.alternatingGroup_le_of_isPreprimitive_of_isThreeCycle_mem hprim hc3 hcK
        exact Or.inl (by rw [hH]; exact le_antisymm hKAlt hAle)
      · have heven : Even (Fintype.card Ω) := even_card_of_forall_apply_ne hσ hfix
        have hlt : Fintype.card Ω < 10 := by omega
        obtain ⟨m, hm⟩ := heven
        have hm34 : m = 3 ∨ m = 4 := by omega
        rcases hm34 with hm3 | hm4
        · have h6eq : Fintype.card Ω = 6 := by omega
          haveI : Nontrivial Ω := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
          have h5 : 5 ≤ Fintype.card Ω := by omega
          have hcardA : Nat.card (alternatingGroup Ω) = 360 := by
            rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, h6eq]
            norm_num
          have hcardPerm : Nat.card (Perm Ω) = 2 ^ 4 * 45 := by
            rw [Nat.card_perm, Nat.card_eq_fintype_card, h6eq]
            norm_num
          have hcardT : Nat.card T = 16 := by
            have := card_eq_of_isSylowIn_top hT hcardPerm (by norm_num : ¬ 2 ∣ 45)
            simpa using this
          have hcardInf : Nat.card ↥(T ⊓ alternatingGroup Ω) = 8 := by
            have := two_mul_card_inf_alternatingGroup hT (by omega : 2 ≤ Fintype.card Ω)
            rw [hcardT] at this
            omega
          have hle : T ⊓ alternatingGroup Ω ≤ H ⊓ Subgroup.centralizer {σ} :=
            le_inf (le_trans inf_le_right hA) (le_trans inf_le_left hTσ)
          have h8dvd : 8 ∣ Nat.card K := by
            have := Subgroup.card_dvd_of_le (le_trans hle hXK)
            rwa [hcardInf] at this
          have h30dvd : 30 ∣ Nat.card K := by
            have := card_mul_pred_dvd_card (Ω := Ω) (by omega : 2 ≤ Fintype.card Ω) hKtrans
            rw [h6eq] at this
            norm_num at this
            simpa using this
          have h120dvd : 120 ∣ Nat.card K := by
            have hlcm : Nat.lcm 30 8 = 120 := by decide
            simpa [hlcm] using Nat.lcm_dvd h30dvd h8dvd
          have h360dvd : Nat.card K ∣ 360 := by
            have := Subgroup.card_dvd_of_le hKAlt
            rwa [hcardA] at this
          rcases eq_120_or_360_of_dvd h120dvd h360dvd with hk | hk
          · have hrel : K.relIndex (alternatingGroup Ω) * Nat.card K =
                Nat.card (alternatingGroup Ω) := by
              have h := Subgroup.relIndex_mul_card (H := K) (K := alternatingGroup Ω)
              rwa [inf_of_le_left hKAlt] at h
            rw [hcardA] at hrel
            have hne : K ≠ alternatingGroup Ω := by
              intro heq
              rw [heq, hcardA] at hk
              omega
            have hfact := card_alternatingGroup_dvd_factorial h5 hKAlt hne
            rw [hcardA] at hfact
            rw [hk] at hrel
            have hr : K.relIndex (alternatingGroup Ω) = 3 := by omega
            rw [hr] at hfact
            exact absurd hfact (by norm_num)
          · have hKeq : K = alternatingGroup Ω :=
              Subgroup.eq_of_le_of_card_ge hKAlt (by rw [hk, hcardA])
            exact Or.inl (by rw [hH, hKeq])
        · have h8eq : Fintype.card Ω = 8 := by omega
          have hS : IsSylowIn 2 (T ⊓ alternatingGroup Ω) (alternatingGroup Ω) :=
            isSylowIn_inf_alternatingGroup hT
          have hle : T ⊓ alternatingGroup Ω ≤ H ⊓ Subgroup.centralizer {σ} :=
            le_inf (le_trans inf_le_right hA) (le_trans inf_le_left hTσ)
          have hSK : T ⊓ alternatingGroup Ω ≤ K := le_trans hle hXK
          rcases eq_alternatingGroup_or_isE8L3 h8eq hKAlt hS hSK hKtrans with heq | hE
          · exact Or.inl (by rw [hH, heq])
          · exact Or.inr (Or.inr ⟨h8eq, hH, hE⟩)
    · haveI : Nonempty Ω := Fintype.card_pos_iff.mp (by omega)
      let a : Ω := Classical.choice (inferInstance : Nonempty Ω)
      have hswapK : swap a (σ a) ∈ K :=
        hXK (Subgroup.mem_inf.mpr
          ⟨by rw [hH]; exact Subgroup.mem_top _, swap_apply_mem_centralizer hσ a⟩)
      have hswap : (swap a (σ a)).IsSwap := ⟨a, σ a, (hfix a).symm, rfl⟩
      have htop : K = ⊤ :=
        Equiv.Perm.subgroup_eq_top_of_isPreprimitive_of_isSwap_mem hprim (swap a (σ a))
          hswap hswapK
      exact Or.inl (htop.trans hH.symm)

end ThreeOne

end CFSG.LocalAnalysis.WeakClosure81

end
