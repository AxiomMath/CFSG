module

public import CFSG.LocalAnalysis.StandardType.GGHalfFiveTorusSupp
public import CFSG.LocalAnalysis.StandardType.GGHalfFiveRes
public import CFSG.LocalAnalysis.StandardType.GGHalfCentSupp
public import CFSG.LocalAnalysis.StandardType.GGHalfWeylTorusCoord

public section

namespace CFSG.StandardType.GGHalf

open CFSG.LieType.Universal.SpecialLinear Matrix

open TorusSupp

private theorem exists_zpowers_omegaBlock_of_mem_halfTorus_supp_two
    {t : SpecialLinearGroup (Fin 6) F2} (ht : t ∈ halfTorus 5) (h2 : supp t = 2) :
    ∃ k' : Fin 5, (k' = 0 ∨ k' = 2 ∨ k' = 4) ∧
      (t = omegaBlock 5 k' ∨ t = (omegaBlock 5 k')⁻¹) := by
  obtain ⟨Φ, hΦ⟩ := exists_torusCoord 5
  have hΦ' := torusCoord_gen_eq Φ hΦ
  let v : Fin 3 → Multiplicative (ZMod 3) := Φ.symm ⟨t, ht⟩
  have hvt : (Φ v : ↥(halfTorus 5)) = ⟨t, ht⟩ := by
    change Φ (Φ.symm ⟨t, ht⟩) = ⟨t, ht⟩
    exact MulEquiv.apply_symm_apply Φ ⟨t, ht⟩
  have htv : (Φ v : SpecialLinearGroup (Fin 6) F2) = t := congrArg Subtype.val hvt
  have hsupp : supp t = 2 * (Finset.univ.filter fun j : Fin 3 => v j ≠ 1).card := by
    rw [← htv]
    exact supp_torusCoord Φ hΦ' v
  rw [hsupp] at h2
  have hcard : (Finset.univ.filter fun j : Fin 3 => v j ≠ 1).card = 1 := by omega
  obtain ⟨j, hj⟩ := Finset.card_eq_one.mp hcard
  have hvj : v j ≠ 1 := by
    have : j ∈ Finset.univ.filter (fun j : Fin 3 => v j ≠ 1) := by
      rw [hj]; exact Finset.mem_singleton_self j
    exact (Finset.mem_filter.mp this).2
  have hv_other : ∀ i : Fin 3, i ≠ j → v i = 1 := by
    intro i hi
    by_contra hne
    have : i ∈ Finset.univ.filter (fun j : Fin 3 => v j ≠ 1) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne⟩
    rw [hj] at this
    exact hi (Finset.mem_singleton.mp this)
  have hv_eq : v = Pi.mulSingle j (v j) := by
    funext i
    by_cases hi : i = j
    · subst hi; rw [Pi.mulSingle_eq_same]
    · rw [Pi.mulSingle_eq_of_ne (fun h => hi h), hv_other i hi]
  have hΦv : t = (omegaBlock 5 (kOf j)) ^ (Multiplicative.toAdd (v j)).val := by
    rw [← htv]
    have h1 : Pi.mulSingle j (v j) = (gen j) ^ (Multiplicative.toAdd (v j)).val := by
      funext i
      rw [gen, Pi.mulSingle_apply, Pi.pow_apply, Pi.mulSingle_apply]
      by_cases hi : i = j
      · rw [if_pos hi, if_pos hi]
        exact (ofAdd_one_pow (v j)).symm
      · rw [if_neg hi, if_neg hi]
        simp
    conv_lhs => rw [hv_eq, h1]
    rw [show Φ (gen j ^ (Multiplicative.toAdd (v j)).val) =
        (Φ (gen j)) ^ (Multiplicative.toAdd (v j)).val from
      map_pow Φ (gen j) (Multiplicative.toAdd (v j)).val,
      Subgroup.coe_pow (halfTorus 5), hΦ' j]
  refine ⟨kOf j, ?_, ?_⟩
  · fin_cases j <;> simp [kOf]
  · have hne0 : (Multiplicative.toAdd (v j)).val ≠ 0 := by
      intro h0
      apply hvj
      have hz : Multiplicative.toAdd (v j) = 0 := by
        rw [← ZMod.natCast_zmod_val (Multiplicative.toAdd (v j)), h0, Nat.cast_zero]
      have := congrArg Multiplicative.ofAdd hz
      rwa [show Multiplicative.ofAdd (Multiplicative.toAdd (v j)) = v j from rfl,
        show Multiplicative.ofAdd (0 : ZMod 3) = 1 from rfl] at this
    have hval : (Multiplicative.toAdd (v j)).val = 1 ∨
        (Multiplicative.toAdd (v j)).val = 2 := by
      have hlt : (Multiplicative.toAdd (v j)).val < 3 := ZMod.val_lt _
      omega
    rcases hval with h1 | h2
    · left
      rw [hΦv, h1, pow_one]
    · right
      rw [hΦv, h2]
      exact eq_inv_of_mul_eq_one_left (by
        rw [← pow_succ, show 2 + 1 = 3 by norm_num, omegaBlock_pow_three])

theorem conj_omegaBlock_mem_blocks {s : SpecialLinearGroup (Fin 6) F2}
    (hs : ∀ t ∈ halfTorus 5, s * t * s⁻¹ ∈ halfTorus 5) {k : Fin 5}
    (hk : k = 0 ∨ k = 2 ∨ k = 4) :
    ∃ k' : Fin 5, (k' = 0 ∨ k' = 2 ∨ k' = 4) ∧
      (s * omegaBlock 5 k * s⁻¹ = omegaBlock 5 k' ∨
        s * omegaBlock 5 k * s⁻¹ = (omegaBlock 5 k')⁻¹) := by
  have hk2 : k.val % 2 = 0 := by rcases hk with h | h | h <;> subst h <;> decide
  have hmem : omegaBlock 5 k ∈ halfTorus 5 :=
    Subgroup.subset_closure ⟨k, hk2, rfl⟩
  have ht : s * omegaBlock 5 k * s⁻¹ ∈ halfTorus 5 := hs _ hmem
  have hsupp : supp (s * omegaBlock 5 k * s⁻¹) = 2 := by
    rw [supp_conj]
    rcases hk with h | h | h
    · subst h
      simpa [kOf] using supp_omegaBlock_kOf (0 : Fin 3)
    · subst h
      simpa [kOf] using supp_omegaBlock_kOf (1 : Fin 3)
    · subst h
      simpa [kOf] using supp_omegaBlock_kOf (2 : Fin 3)
  exact exists_zpowers_omegaBlock_of_mem_halfTorus_supp_two ht hsupp

end CFSG.StandardType.GGHalf

end
