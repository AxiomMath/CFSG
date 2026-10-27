module

public import CFSG.Quasithin.Background.HSU3Unitary

public section

namespace CFSG.Quasithin

namespace H

namespace SU3

open CFSG.Open CFSG.Assembly.LowTwoRank Matrix
open scoped Matrix

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}

omit [Field K] [Finite K] [CharP K 2] in
theorem card_eq_two_pow (hK : Nat.card K = (2 ^ n) ^ 2) : Nat.card K = 2 ^ (2 * n) := by
  rw [hK, ← pow_mul, mul_comm]

theorem two_le_two_pow (hn : 1 ≤ n) : 2 ≤ 2 ^ n := by
  calc 2 = 2 ^ 1 := by norm_num
    _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn

theorem hasScalarCommutant' (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2) :
    HasScalarCommutant (StatedSU 3 (2 ^ n) K) :=
  hasScalarCommutant hK (two_le_two_pow hn)

omit [Finite K] [CharP K 2] in
theorem swapMat_mul_self : (swapMat : Matrix (Fin 3) (Fin 3) K) * swapMat = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [swapMat, Matrix.mul_apply, Fin.sum_univ_three]

omit [Finite K] in
theorem swapSU_mul_self : (swapSU : GL (Fin 3) K) * swapSU = 1 := by
  apply Units.ext
  rw [Units.val_mul, swapSU, coe_glOfDetOne, swapMat_mul_self, Units.val_one]

omit [Finite K] in
theorem swapSU_ne_one : (swapSU : GL (Fin 3) K) ≠ 1 := by
  intro h
  have := congrArg (fun A : GL (Fin 3) K => (A : Matrix (Fin 3) (Fin 3) K) 0 0) h
  simp [swapSU, coe_glOfDetOne, swapMat] at this

@[expose] noncomputable def tSwap (n : ℕ) : MulAut (StdMod (Fin 3) K) :=
  natAut (StatedSU 3 (2 ^ n) K) ⟨swapSU, swapSU_mem (by positivity)⟩

omit [Finite K] in
theorem tSwap_mem : tSwap (K := K) n ∈ natImage (StatedSU 3 (2 ^ n) K) := ⟨_, rfl⟩

omit [Finite K] in
theorem toAddMap_tSwap (v : Fin 3 → K) : toAddMap (tSwap (K := K) n) v = ![v 1, v 0, v 2] := by
  rw [tSwap, toAddMap_natAut]
  change (swapSU : GL (Fin 3) K).val *ᵥ v = _
  rw [swapSU, coe_glOfDetOne, swapMat_mulVec]

omit [Finite K] in
theorem orderOf_tSwap : orderOf (tSwap (K := K) n) = 2 := by
  apply orderOf_eq_prime
  · rw [sq, tSwap, ← map_mul]
    have : (⟨swapSU, swapSU_mem (by positivity)⟩ : ↥(StatedSU 3 (2 ^ n) K)) *
        ⟨swapSU, swapSU_mem (by positivity)⟩ = 1 := Subtype.ext swapSU_mul_self
    rw [this, map_one]
  · intro h
    have := congrArg (fun g => toAddMap g (Pi.single 0 1)) h
    simp only [toAddMap_tSwap, toAddMap_one] at this
    have h0 := congrFun this 0
    simp at h0

theorem rkIdx_fixV_tSwap (hK : Nat.card K = (2 ^ n) ^ 2) :
    rkIdx (fixV (Subgroup.zpowers (tSwap (K := K) n))) = 2 * n := by
  have hK' := card_eq_two_pow hK
  have hcard : Nat.card ↥(fixV (Subgroup.zpowers (tSwap (K := K) n))) = 2 ^ (4 * n) := by
    rw [card_fixV_zpowers]
    have : Nat.card {v : Fin 3 → K // toAddMap (tSwap (K := K) n) v = v} = Nat.card (K × K) := by
      refine Nat.card_congr
        { toFun := fun v => (v.1 0, v.1 2)
          invFun := fun p => ⟨![p.1, p.1, p.2], by
            rw [toAddMap_tSwap]
            ext i
            fin_cases i <;> rfl⟩
          left_inv := fun v => by
            apply Subtype.ext
            have h1 := congrFun v.2 1
            rw [toAddMap_tSwap] at h1
            ext i
            fin_cases i
            · rfl
            · show v.1 0 = v.1 1
              simpa using h1
            · rfl
          right_inv := fun p => rfl }
    rw [this, Nat.card_prod, hK', ← pow_add]
    ring_nf
  rw [rkIdx_fixV_of_card hK' _ (by simp; omega) hcard]
  simp
  omega

section Involutions

variable {X : Subgroup (MulAut (StdMod (Fin 3) K))}

theorem le_rkIdx_fixV_of_involution (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2)
    (hXN : X ≤ natNorm (StatedSU 3 (2 ^ n) K)) {t : MulAut (StdMod (Fin 3) K)} (htX : t ∈ X)
    (ht : orderOf t = 2) : 2 * n ≤ rkIdx (fixV (Subgroup.zpowers t)) := by
  have hK' := card_eq_two_pow hK
  have hΓ := hasScalarCommutant' hn hK
  have hsl := isSemilinear_fieldAut hΓ ⟨t, hXN htX⟩
  have ht1 : t ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at ht
    omega
  by_cases hσ : fieldAut hΓ ⟨t, hXN htX⟩ = RingEquiv.refl K
  · rw [hσ] at hsl
    exact le_rkIdx_fixV_of_linear hK' hsl ht1
  · have ht2 : t ^ 2 = 1 := by rw [← ht]; exact pow_orderOf_eq_one t
    obtain ⟨-, h⟩ := rkIdx_fixV_of_semilinear_two (by omega) hK' hsl hσ ht2
    simp only [Fintype.card_fin] at h
    omega

omit [CharP K 2] in
theorem rkIdx_fixV_of_semilinear_involution (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2)
    {t : MulAut (StdMod (Fin 3) K)} {σ : K ≃+* K} (hsl : IsSemilinear t σ)
    (hσ : σ ≠ RingEquiv.refl K) (ht2 : t ^ 2 = 1) :
    rkIdx (fixV (Subgroup.zpowers t)) = 3 * n := by
  obtain ⟨-, h⟩ := rkIdx_fixV_of_semilinear_two (by omega) (card_eq_two_pow hK) hsl hσ ht2
  simp only [Fintype.card_fin] at h
  omega

end Involutions

theorem mParam_eq (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2)
    {X : Subgroup (MulAut (StdMod (Fin 3) K))} (hLX : natImage (StatedSU 3 (2 ^ n) K) ≤ X)
    (hXN : X ≤ natNorm (StatedSU 3 (2 ^ n) K)) : E3.mParam X = 2 * n := by
  have : Finite (MulAut (StdMod (Fin 3) K)) := MulEquiv.finite_left
  have ht0 : tSwap (K := K) n ∈ X := hLX tSwap_mem
  have hev : Even (Nat.card X) := by
    have h := orderOf_dvd_natCard (⟨tSwap (K := K) n, ht0⟩ : X)
    rw [Subgroup.orderOf_mk, orderOf_tSwap] at h
    exact even_iff_two_dvd.mpr h
  unfold E3.mParam
  rw [ite_eq_left hev]
  apply le_antisymm
  · exact Nat.sInf_le ⟨_, ht0, orderOf_tSwap, (rkIdx_fixV_tSwap hK).symm⟩
  · refine le_csInf ⟨_, _, ht0, orderOf_tSwap, rfl⟩ ?_
    rintro k ⟨t, htX, ht, rfl⟩
    exact le_rkIdx_fixV_of_involution hn hK hXN htX ht

theorem card_inf_linSub_le (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2)
    {E : Subgroup (MulAut (StdMod (Fin 3) K))} (hEN : E ≤ natNorm (StatedSU 3 (2 ^ n) K))
    (hE : IsElemAbelian2 E) : Nat.card ↥(E ⊓ linSub) ≤ 2 ^ n := by
  set E₁ := E ⊓ linSub with hE₁
  have hE₁r : E₁ ≤ matHom.range := by
    intro g hg
    obtain ⟨A, rfl⟩ := exists_matAut_of_mem_linSub hg.2
    exact ⟨A, rfl⟩
  let E₀ : Subgroup (GL (Fin 3) K) := E₁.comap matHom
  have hmap : E₀.map matHom = E₁ := Subgroup.map_comap_eq_self hE₁r
  have hcard : Nat.card E₀ = Nat.card E₁ := by
    rw [← hmap]
    exact (Subgroup.card_map_of_injective matHom_injective).symm
  rw [← hcard]
  have hmem : ∀ A ∈ E₀, matAut A ∈ E := fun A hA => hA.1
  refine card_le_of_unitary_involutions hn hK E₀ ?_ ?_ ?_
  · intro A hA
    apply matHom_injective
    rw [map_mul, map_one, matHom_apply, ← sq]
    exact hE.2 _ (hmem A hA)
  · intro A hA B hB
    apply matHom_injective
    rw [map_mul, map_mul, matHom_apply, matHom_apply]
    exact hE.1 _ (hmem A hA) _ (hmem B hB)
  · intro A hA
    refine isUnitaryM_of_normalizes hn hK ?_ fun l hl => ?_
    · apply matHom_injective
      rw [map_mul, map_one, matHom_apply, ← sq]
      exact hE.2 _ (hmem A hA)
    · have hN := hEN (hmem A hA)
      have hl' : natAut (StatedSU 3 (2 ^ n) K) ⟨l, hl⟩ ∈ natImage (StatedSU 3 (2 ^ n) K) :=
        ⟨_, rfl⟩
      have h1 := (Subgroup.mem_normalizer_iff.mp hN _).mp hl'
      obtain ⟨l', hl'eq⟩ := h1
      have h2 : matHom (A * l * A⁻¹) = matHom (l' : GL (Fin 3) K) := by
        rw [map_mul, map_mul, map_inv, matHom_apply, matHom_apply]
        exact hl'eq.symm
      rw [matHom_injective h2]
      exact l'.2

theorem pRank_le (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2)
    {X : Subgroup (MulAut (StdMod (Fin 3) K))} (hXN : X ≤ natNorm (StatedSU 3 (2 ^ n) K)) :
    CFSG.Open.pRank 2 X ≤ n + 1 := by
  have : Finite (MulAut (StdMod (Fin 3) K)) := MulEquiv.finite_left
  have hΓ := hasScalarCommutant' hn hK
  have h1 := pRank_two_le_linSub hΓ (by omega : 1 ≤ 2 * n) (card_eq_two_pow hK) hXN
  suffices h : CFSG.Open.pRank 2 (X ⊓ linSub) ≤ n by omega
  obtain ⟨E, hEX, hE, hEc⟩ := exists_isElemAbelian_card_pRank (X ⊓ linSub)
  have h2 : Nat.card ↥(E ⊓ linSub) = Nat.card E := by
    rw [inf_eq_left.mpr (hEX.trans inf_le_right)]
  have h3 := card_inf_linSub_le hn hK ((hEX.trans inf_le_left).trans hXN)
    (isElemAbelian2_iff.mpr hE)
  rw [h2, hEc] at h3
  exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp h3

theorem aSet_succ_eq_empty (hn : 2 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2)
    {X : Subgroup (MulAut (StdMod (Fin 3) K))} (hXN : X ≤ natNorm (StatedSU 3 (2 ^ n) K))
    (A : Subgroup (MulAut (StdMod (Fin 3) K))) : A ∉ E3.aSet (n + 1) X := by
  intro hA
  have : Finite (MulAut (StdMod (Fin 3) K)) := MulEquiv.finite_left
  obtain ⟨hAX, -, hAel, hAc⟩ := id hA
  have hK' := card_eq_two_pow hK
  have hΓ := hasScalarCommutant' (by omega) hK
  have hAN := hAX.trans hXN
  have hrk1 : n + 1 ≤ rk ↥A := by
    have := E3.le_mQuot_bot_of_mem_aSet hA
    rwa [mQuot_bot_eq_rk] at this
  have hrk2 : rk ↥A ≤ n + 1 := (rk_le_pRank hAX hAel).trans (pRank_le (by omega) hK hXN)
  have hcardA : Nat.card A = 2 ^ rk ↥A :=
    card_eq_two_pow_of_isPGroup (E3.isPGroup_of_isElemAbelian2 hAel)
  obtain ⟨a, haA, ha⟩ : ∃ a ∈ A, a ∉ linSub := by
    by_contra h
    push Not at h
    have h1 := card_inf_linSub_le (by omega) hK hAN hAel
    rw [inf_eq_left.mpr h, hcardA] at h1
    have := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp h1
    omega
  obtain ⟨c, hcA, hc1⟩ : ∃ c ∈ A ⊓ linSub, c ≠ 1 := by
    have h1 := card_le_two_mul_card_inf_linSub hΓ (by omega) hK' hAN hAel.2
    by_contra h
    push Not at h
    have hbot : A ⊓ linSub = ⊥ := (Subgroup.eq_bot_iff_forall _).mpr h
    rw [hbot, Subgroup.card_bot, hcardA] at h1
    have : 2 ^ 2 ≤ 2 ^ rk ↥A := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have ha2 : a ^ 2 = 1 := hAel.2 a haA
  have ha1 : a ≠ 1 := fun h => ha (h ▸ (linSub).one_mem)
  have hoa : orderOf a = 2 := orderOf_eq_prime ha2 ha1
  have hBA : Subgroup.zpowers a ≤ A := (Subgroup.zpowers_le).mpr haA
  have hfix : fixV (Subgroup.zpowers a) = fixV A := by
    refine hAc _ hBA ?_
    have h1 := E3.mQuot_add (bot_le : (⊥ : Subgroup (MulAut (StdMod (Fin 3) K))) ≤ _) hBA
    rw [mQuot_bot_eq_rk, mQuot_bot_eq_rk] at h1
    have h2 : rk ↥(Subgroup.zpowers a) = 1 := by
      unfold rk
      rw [Nat.card_zpowers, hoa, padicValNat_self]
    omega
  have hsl := isSemilinear_fieldAut hΓ ⟨a, hAN haA⟩
  set σ := fieldAut hΓ ⟨a, hAN haA⟩
  have hσ : σ ≠ RingEquiv.refl K := by
    intro h
    apply ha
    have := hsl
    rw [h] at this
    exact this
  have hσ2 : σ ^ 2 = 1 := by
    have h1 : IsSemilinear (a ^ 2) (σ.trans σ) := by
      rw [pow_two]
      exact hsl.mul hsl
    rw [ha2] at h1
    have := h1.unique isSemilinear_one
    ext x
    exact congrArg (fun τ : K ≃+* K => τ x) this
  have hσo : orderOf σ = 2 := orderOf_eq_prime hσ2 hσ
  obtain ⟨b, hb⟩ := exists_basis_fixed_of_semilinear (by omega) hK' hsl hσo ha2
  apply hc1
  refine eq_one_of_linear_of_fix_basis hcA.2 b fun i => ?_
  have hbi : Multiplicative.ofAdd (b i) ∈ fixV A := by
    rw [← hfix]
    exact mem_fixV_zpowers_iff.mpr (congrArg Multiplicative.ofAdd (hb i))
  exact congrArg Multiplicative.toAdd (hbi c hcA.1)

theorem aParam_le (hn : 2 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2)
    {X : Subgroup (MulAut (StdMod (Fin 3) K))} (hXN : X ≤ natNorm (StatedSU 3 (2 ^ n) K)) :
    E3.aParam X ≤ n := by
  unfold E3.aParam
  split_ifs
  · by_cases hne : {k : ℕ | 0 < k ∧ (E3.aSet k X).Nonempty}.Nonempty
    · refine csSup_le hne ?_
      rintro k ⟨-, A, hA⟩
      by_contra hk
      push Not at hk
      exact aSet_succ_eq_empty hn hK hXN A (E3.aSet_anti hk X hA)
    · rw [Set.not_nonempty_iff_eq_empty.mp hne, csSup_empty]
      exact Nat.zero_le n
  · exact Nat.zero_le n

theorem not_isFOneModule (hn : 2 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2)
    {X : Subgroup (MulAut (StdMod (Fin 3) K))} (hXN : X ≤ natNorm (StatedSU 3 (2 ^ n) K)) :
    ¬ IsFOneModule X := by
  rintro ⟨A, ⟨hAX, hA1, hAel⟩, hoff⟩
  have : Finite (MulAut (StdMod (Fin 3) K)) := MulEquiv.finite_left
  have hΓ := hasScalarCommutant' (by omega) hK
  have hAN := hAX.trans hXN
  have hrk2 : rk ↥A ≤ n + 1 := (rk_le_pRank hAX hAel).trans (pRank_le (by omega) hK hXN)
  have hcardA : Nat.card A = 2 ^ rk ↥A :=
    card_eq_two_pow_of_isPGroup (E3.isPGroup_of_isElemAbelian2 hAel)
  have hmono : ∀ a ∈ A, rkIdx (fixV (Subgroup.zpowers a)) ≤ rkIdx (fixV A) := fun a ha =>
    rkIdx_anti (fun v hv y hy => hv y ((Subgroup.zpowers_le).mpr ha hy))
  by_cases hlin : A ≤ linSub
  · have h1 := card_inf_linSub_le (by omega) hK hAN hAel
    rw [inf_eq_left.mpr hlin, hcardA] at h1
    have hrk : rk ↥A ≤ n := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp h1
    obtain ⟨a, ha1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hA1
    have hoa : orderOf (a : MulAut (StdMod (Fin 3) K)) = 2 :=
      orderOf_eq_prime (hAel.2 a a.2) (fun h => ha1 (Subtype.ext h))
    have h2 := le_rkIdx_fixV_of_involution (by omega) hK hXN (hAX a.2) hoa
    have h3 := hmono a a.2
    omega
  · obtain ⟨a, haA, ha⟩ : ∃ a ∈ A, a ∉ linSub := by
      by_contra h
      push Not at h
      exact hlin h
    have hsl := isSemilinear_fieldAut hΓ ⟨a, hAN haA⟩
    have hσ : fieldAut hΓ ⟨a, hAN haA⟩ ≠ RingEquiv.refl K := by
      intro h
      apply ha
      have := hsl
      rw [h] at this
      exact this
    have h2 : rkIdx (fixV (Subgroup.zpowers a)) = 3 * n :=
      rkIdx_fixV_of_semilinear_involution (by omega) hK hsl hσ (hAel.2 a haA)
    have h3 := hmono a haA
    omega

theorem alphaH_eq_one (hn : 2 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2)
    {X : Subgroup (MulAut (StdMod (Fin 3) K))} (hXN : X ≤ natNorm (StatedSU 3 (2 ^ n) K)) :
    alphaH X = 1 :=
  alphaH_eq_one_of_not_isFOneModule (not_isFOneModule hn hK hXN)

end SU3

open SU3 in
theorem H2_SU3 {V : Type*} [CommGroup V] [Finite V] {L M : Subgroup (MulAut V)} {n : ℕ}
    (hn : 2 ≤ n) (hL : BinaryNaturalSU3 L ⊤ ⊥ n) (hLM : L ≤ M)
    (hMN : M ≤ Subgroup.normalizer (L : Set (MulAut V))) :
    E3.mParam M = 2 * n ∧ CFSG.Open.pRank 2 M ≤ n + 1 ∧ E3.aParam M ≤ n ∧
      ¬ IsFOneModule M ∧ alphaH M = 1 := by
  obtain ⟨K, _, _, hK, hreal⟩ := hL
  have : CharP K 2 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    Nat.prime_two (by omega : 1 ≤ 2 * n) (SU3.card_eq_two_pow hK)
  obtain ⟨e, h1, h2⟩ := exists_transport_natural hreal hLM hMN
  have : Finite (StdMod (Fin 3) K) := Finite.of_equiv V e.toEquiv
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [← mParam_map_congrHom e]
    exact mParam_eq (by omega) hK h1 h2
  · rw [← pRank_two_map_congrHom e]
    exact pRank_le (by omega) hK h2
  · rw [← aParam_map_congrHom e]
    exact aParam_le hn hK h2
  · rw [← isFOneModule_map_congrHom e]
    exact not_isFOneModule hn hK h2
  · rw [← alphaH_map_congrHom e]
    exact SU3.alphaH_eq_one hn hK h2

end H

end CFSG.Quasithin
