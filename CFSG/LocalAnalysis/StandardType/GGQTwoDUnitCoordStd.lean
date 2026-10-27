module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDCoxEven
import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitCoordStdA
import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyRestPerm
import CFSG.LocalAnalysis.EvenSmallLie.OddTranspAlt.PermAut
import CFSG.LocalAnalysis.StandardType.ZS.MonomialBasic

public section

namespace CFSG.StandardType.QTwo

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

open Equiv

theorem ggQTwoDUnit_perm_fixed {m : ℕ} (v : DVec m)
    (hv : ∀ σ : Equiv.Perm (Fin m), dPerm m σ v = v) : ∃ k : ZMod 3, v = fun _ => k := by
  by_cases hm : m = 0
  · subst hm
    exact ⟨0, funext fun i => i.elim0⟩
  have hm1 : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hm
  refine ⟨v ⟨0, hm1⟩, funext fun i => ?_⟩
  by_cases hi : i = (⟨0, hm1⟩ : Fin m)
  · rw [hi]
  · have h := qtwoDB32_dPerm_apply_self m (Equiv.swap i ⟨0, hm1⟩) v i
    rw [Equiv.swap_apply_left, hv] at h
    exact h.symm

theorem ggQTwoDUnit_endo_scalar {m : ℕ} (hm : 4 ≤ m) (T : DVec m →+ DVec m)
    (hT : ∀ (σ : Equiv.Perm (Fin m)) (v : DVec m), ∃ k : ZMod 3,
      T (dPerm m σ v) = dPerm m σ (T v) + fun _ => k) :
    ∃ μ : ZMod 3, ∀ v : DVec m, ∃ k : ZMod 3, T v = μ • v + fun _ => k := by
  classical
  set i0 : Fin m := ⟨0, by omega⟩ with hi0
  set i1 : Fin m := ⟨1, by omega⟩ with hi1
  have h01 : i1 ≠ i0 := by simp [hi0, hi1, Fin.ext_iff]
  set w : DVec m := T (dBasis m i0) with hw
  have hconst : ∀ i j : Fin m, i ≠ i0 → j ≠ i0 → w i = w j := by
    intro i j hi hj
    by_cases hij : i = j
    · rw [hij]
    · obtain ⟨k, hk⟩ := hT (Equiv.swap i j) (dBasis m i0)
      have hσi : Equiv.swap i j i0 = i0 :=
        Equiv.swap_apply_of_ne_of_ne (Ne.symm hi) (Ne.symm hj)
      have hk' : w = dPerm m (Equiv.swap i j) w + fun _ => k := by
        rw [dPerm_apply, hσi, ← hw] at hk
        exact hk
      obtain ⟨l, -, hl⟩ := Finset.exists_mem_notMem_of_card_lt_card
        (s := ({i0, i, j} : Finset (Fin m))) (t := Finset.univ)
        (by rw [Finset.card_univ, Fintype.card_fin]
            exact lt_of_le_of_lt Finset.card_le_three (by omega))
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hl
      obtain ⟨hli0, hli, hlj⟩ := hl
      have hfix : Equiv.swap i j l = l := Equiv.swap_apply_of_ne_of_ne hli hlj
      have hkl : k = 0 := by
        have h := congrFun hk' l
        rw [Pi.add_apply, qtwoDB32_dPerm_eval] at h
        rw [show (Equiv.swap i j).symm l = l by rw [Equiv.symm_swap, hfix]] at h
        exact add_left_cancel (by rw [h.symm, add_zero])
      have h := congrFun hk' i
      rw [Pi.add_apply, qtwoDB32_dPerm_eval] at h
      rw [show (Equiv.swap i j).symm i = j by rw [Equiv.symm_swap, Equiv.swap_apply_left]] at h
      simp only [hkl] at h
      simpa using h
  have hw_c : ∀ i : Fin m, i ≠ i0 → w i = w i1 := fun i hi => hconst i i1 hi h01
  set c : ZMod 3 := w i1 with hc
  set μ : ZMod 3 := w i0 - c with hμ
  have hw_eq : w = μ • dBasis m i0 + fun _ => c := by
    funext j
    by_cases hj : j = i0
    · subst hj
      rw [Pi.add_apply, Pi.smul_apply, dBasis, Pi.basisFun_apply, Pi.single_eq_same, hμ]
      ring
    · have hb : (dBasis m i0) j = 0 := by
        rw [dBasis, Pi.basisFun_apply, Pi.single_eq_of_ne hj]
      rw [Pi.add_apply, Pi.smul_apply, hb, smul_zero, zero_add]
      exact hw_c j hj
  have hTe : ∀ i : Fin m, ∃ k : ZMod 3, T (dBasis m i) = μ • dBasis m i + fun _ => k := by
    intro i
    by_cases hi : i = i0
    · subst hi
      exact ⟨c, by rw [← hw, hw_eq]⟩
    · obtain ⟨k, hk⟩ := hT (Equiv.swap i0 i) (dBasis m i0)
      refine ⟨c + k, ?_⟩
      have hσi : Equiv.swap i0 i i0 = i := Equiv.swap_apply_left i0 i
      have hk' : T (dBasis m i) = dPerm m (Equiv.swap i0 i) w + fun _ => k := by
        rw [dPerm_apply, hσi, ← hw] at hk
        exact hk
      rw [hk']
      simp only [hw_eq, map_add, map_smul, dPerm_apply, hσi, qtwoDB32_dPerm_const]
      funext j
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
  choose kf hkf using hTe
  refine ⟨μ, fun v => ?_⟩
  refine ⟨∑ i, v i * kf i, ?_⟩
  calc T v = T (∑ i : Fin m, v i • dBasis m i) := by rw [qtwoDB32_sum_basis]
    _ = ∑ i : Fin m, T (v i • dBasis m i) := by rw [map_sum]
    _ = ∑ i : Fin m, v i • T (dBasis m i) := by
          apply Finset.sum_congr rfl; intro i _; rw [qtwoDB32_addHom_smul]
    _ = ∑ i : Fin m, v i • (μ • dBasis m i + fun _ => kf i) := by
          apply Finset.sum_congr rfl; intro i _; rw [hkf i]
    _ = μ • v + fun _ => ∑ i, v i * kf i := by
          funext j
          have hvj : v j = ∑ i, v i * (dBasis m i) j := by
            rw [← congrFun (qtwoDB32_sum_basis m v) j, Finset.sum_apply]
            apply Finset.sum_congr rfl
            intro i _
            rw [Pi.smul_apply, smul_eq_mul]
          simp only [Finset.sum_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, hvj]
          rw [Finset.mul_sum, ← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro i _
          ring

theorem ggQTwoDUnit_perm_standard {m : ℕ} (hm : 5 ≤ m)
    (φ : Equiv.Perm (Fin m) →* (DVec m ≃ₗ[ZMod 3] DVec m)) (hinj : Function.Injective φ)
    (hφ : ∀ a b : Fin m, a ≠ b → ∃ (sgn : Bool) (a' b' : Fin m), a' ≠ b' ∧
      φ (Equiv.swap a b) = dTau m sgn a' b') :
    ∃ (P : DVec m ≃ₗ[ZMod 3] DVec m) (π : Equiv.Perm (Fin m)) (t : Fin m → ZMod 3),
      (∀ i, t i = 1 ∨ t i = -1) ∧ (∀ i, P (dBasis m i) = t i • dBasis m (π i)) ∧
        ∀ σ : Equiv.Perm (Fin m), P * φ σ * P⁻¹ = dPerm m σ := by
  classical
  have hm3 : 3 ≤ m := by omega
  obtain ⟨π₀, hπ₀⟩ := CFSG.StandardType.exists_eq_conj_of_isSwap hm3 (qtwoDB32_psi φ hφ)
    (qtwoDB32_psi_injective hm φ hinj hφ)
    (fun σ hσ => by rcases hσ with ⟨a, b, hab, rfl⟩; exact qtwoDB32_psi_swap φ hφ hab)
  let φ' : Equiv.Perm (Fin m) →* (DVec m ≃ₗ[ZMod 3] DVec m) :=
  { toFun := fun σ => (dPerm m π₀)⁻¹ * φ σ * dPerm m π₀
    map_one' := by simp
    map_mul' := by intro σ τ; rw [map_mul]; group }
  have hφ' : ∀ σ, φ' σ = (dPerm m π₀)⁻¹ * φ σ * dPerm m π₀ := fun _ => rfl
  set eps : Fin m → Fin m → ZMod 3 :=
    fun a b => (φ' (Equiv.swap a b) (dBasis m a)) b with heps_def
  have heps : ∀ a b : Fin m, a ≠ b →
      φ' (Equiv.swap a b) = qtwoDB32_dTauZ m (eps a b) a b ∧
        (eps a b = 1 ∨ eps a b = -1) := by
    intro a b hab
    obtain ⟨sgn, a', b', hab', heq⟩ := hφ a b hab
    have hswap : Equiv.swap a' b' = Equiv.swap (π₀ a) (π₀ b) := by
      have h1 : qtwoDB32_psi φ hφ (Equiv.swap a b) = Equiv.swap a' b' := by
        change qtwoDB32_proj m ⟨φ (Equiv.swap a b), qtwoDB32_phi_mem φ hφ _⟩ = Equiv.swap a' b'
        have helem : (⟨φ (Equiv.swap a b), qtwoDB32_phi_mem φ hφ _⟩ : dEven m) =
            ⟨dTau m sgn a' b', dTau_mem_dEven m sgn hab'⟩ := Subtype.ext heq
        rw [helem, qtwoDB32_proj_dTau m sgn hab']
      rw [hπ₀ (Equiv.swap a b), ← Equiv.swap_apply_apply π₀ a b] at h1
      exact h1.symm
    have hπab : π₀ a ≠ π₀ b := fun h => hab (π₀.injective h)
    have hpair := qtwoDB32_pair_eq_of_swap_eq hab' hπab hswap
    have hconj : φ' (Equiv.swap a b) = qtwoDB32_dTauZ m (qtwoDB32_dSgn sgn) a b := by
      rw [hφ', heq, qtwoDB32_dPerm_inv]
      have h2 : dPerm m π₀⁻¹ * dTau m sgn a' b' * dPerm m π₀ =
          dTau m sgn (π₀⁻¹ a') (π₀⁻¹ b') := by
        have h3 := dPerm_conj_dTau m π₀⁻¹ sgn a' b'
        simpa only [qtwoDB32_dPerm_inv, inv_inv] using h3
      rw [h2, qtwoDB32_dTauZ_dSgn]
      rcases hpair with ⟨hpa, hpb⟩ | ⟨hpa, hpb⟩
      · rw [hpa, hpb, show π₀⁻¹ (π₀ a) = a from Equiv.symm_apply_apply π₀ a,
          show π₀⁻¹ (π₀ b) = b from Equiv.symm_apply_apply π₀ b]
      · rw [hpa, hpb, show π₀⁻¹ (π₀ b) = b from Equiv.symm_apply_apply π₀ b,
          show π₀⁻¹ (π₀ a) = a from Equiv.symm_apply_apply π₀ a, dTau_symm]
    have heps_eq : eps a b = qtwoDB32_dSgn sgn := by
      have h := congrArg (fun T : DVec m ≃ₗ[ZMod 3] DVec m => (T (dBasis m a)) b) hconj
      rw [qtwoDB32_dTauZ_apply_left (qtwoDB32_dSgn_cases sgn) hab] at h
      have h' : (φ' (Equiv.swap a b) (dBasis m a)) b = qtwoDB32_dSgn sgn := by
        simpa [Pi.smul_apply, dBasis, Pi.basisFun_apply] using h
      rw [heps_def]
      exact h'
    exact ⟨by rw [heps_eq]; exact hconj, by rw [heps_eq]; exact qtwoDB32_dSgn_cases sgn⟩
  have heps_symm : ∀ a b : Fin m, a ≠ b → eps a b = eps b a := by
    intro a b hab
    have h1 := (heps a b hab).1
    have h1' := (heps a b hab).2
    have h2 := (heps b a hab.symm).1
    have h2' := (heps b a hab.symm).2
    have heq : qtwoDB32_dTauZ m (eps a b) a b = qtwoDB32_dTauZ m (eps b a) b a := by
      rw [← h1, ← h2, Equiv.swap_comm]
    have h := congrArg (fun T : DVec m ≃ₗ[ZMod 3] DVec m => T (dBasis m a)) heq
    rw [qtwoDB32_dTauZ_apply_left h1' hab, qtwoDB32_dTauZ_apply_right h2' hab.symm] at h
    have hb := congrFun h b
    simpa [Pi.smul_apply, dBasis, Pi.basisFun_apply] using hb
  have heps_cocycle : ∀ a b c : Fin m, a ≠ b → b ≠ c → a ≠ c →
      eps a c = eps a b * eps b c := by
    intro i j k hij hjk hik
    have hperm : Equiv.swap i k = Equiv.swap i j * Equiv.swap j k * Equiv.swap i j := by
      have h1 := Equiv.swap_apply_apply (Equiv.swap i j) j k
      rw [Equiv.swap_apply_right,
        Equiv.swap_apply_of_ne_of_ne (Ne.symm hik) (Ne.symm hjk), Equiv.swap_inv] at h1
      exact h1
    have hrel : qtwoDB32_dTauZ m (eps i k) i k =
        qtwoDB32_dTauZ m (eps i j) i j * qtwoDB32_dTauZ m (eps j k) j k *
          qtwoDB32_dTauZ m (eps i j) i j := by
      calc qtwoDB32_dTauZ m (eps i k) i k
          = φ' (Equiv.swap i k) := ((heps i k hik).1).symm
        _ = φ' (Equiv.swap i j * Equiv.swap j k * Equiv.swap i j) := by rw [hperm]
        _ = φ' (Equiv.swap i j) * φ' (Equiv.swap j k) * φ' (Equiv.swap i j) := by
              rw [map_mul, map_mul]
        _ = qtwoDB32_dTauZ m (eps i j) i j * qtwoDB32_dTauZ m (eps j k) j k *
              qtwoDB32_dTauZ m (eps i j) i j := by
              rw [(heps i j hij).1, (heps j k hjk).1]
    have h1 := (heps i j hij).2
    have h2 := (heps j k hjk).2
    have h3 := (heps i k hik).2
    have h := congrArg (fun T : DVec m ≃ₗ[ZMod 3] DVec m => T (dBasis m i)) hrel
    rw [qtwoDB32_dTauZ_apply_left h3 hik, LinearEquiv.mul_apply, LinearEquiv.mul_apply,
      qtwoDB32_dTauZ_apply_left h1 hij, map_smul, qtwoDB32_dTauZ_apply_left h2 hjk,
      map_smul, map_smul, qtwoDB32_dTauZ_apply_of_ne h1 (Ne.symm hik) (Ne.symm hjk),
      smul_smul] at h
    have hk := congrFun h k
    simpa [Pi.smul_apply, dBasis, Pi.basisFun_apply] using hk
  set i0 : Fin m := ⟨0, by omega⟩ with hi0
  have hi01 : i0 ≠ (⟨1, by omega⟩ : Fin m) := by simp [hi0, Fin.ext_iff]
  set t : Fin m → ZMod 3 := fun i => if i = i0 then 1 else eps i0 i with ht_def
  have ht : ∀ i, t i = 1 ∨ t i = -1 := by
    intro i
    rw [ht_def]
    by_cases hi : i = i0
    · simp [hi]
    · simp only [if_neg hi]
      exact (heps i0 i (fun h => hi h.symm)).2
  have ht_i0 : t i0 = 1 := by rw [ht_def]; simp
  have ht_ne : ∀ i : Fin m, i ≠ i0 → t i = eps i0 i := by
    intro i hi
    rw [ht_def]
    simp [hi]
  have ht_eps : ∀ a b : Fin m, a ≠ b → t a * t b = eps a b := by
    intro a b hab
    by_cases ha : a = i0
    · subst ha
      rw [ht_i0, ht_ne b (fun h => hab h.symm), one_mul]
    · by_cases hb : b = i0
      · subst hb
        rw [ht_ne a ha, ht_i0, mul_one]
        exact heps_symm i0 a (fun h => ha h.symm)
      · rw [ht_ne a ha, ht_ne b hb]
        rw [← heps_symm a i0 ha, heps_cocycle a i0 b ha (fun h => hb h.symm) hab]
  set du : Fin m → (ZMod 3)ˣ := fun i => qtwoDB32_unitOfSign (t i) with hdu_def
  set D : DVec m ≃ₗ[ZMod 3] DVec m := ZS.diagMap 3 (dBasis m) du with hD_def
  have hD_apply : ∀ i, D (dBasis m i) = t i • dBasis m i := by
    intro i
    rw [hD_def, ZS.diagMap_apply_basis]
    rw [show du i = qtwoDB32_unitOfSign (t i) from rfl, qtwoDB32_unitOfSign_val (ht i)]
  have hD_inv_apply : ∀ i, D⁻¹ (dBasis m i) = t i • dBasis m i := by
    intro i
    have h : D (t i • dBasis m i) = dBasis m i := by
      rw [map_smul, hD_apply i, smul_smul]
      have htt : t i * t i = 1 := by rcases ht i with h | h <;> rw [h] <;> decide
      rw [htt, one_smul]
    refine D.injective ?_
    change D (D.symm (dBasis m i)) = D (t i • dBasis m i)
    rw [LinearEquiv.apply_symm_apply, h]
  have hD_conj : ∀ a b : Fin m, a ≠ b →
      D * φ' (Equiv.swap a b) * D⁻¹ = dPerm m (Equiv.swap a b) := by
    intro a b hab
    have h1 := (heps a b hab).1
    have h2 := (heps a b hab).2
    refine (dBasis m).ext' fun i => ?_
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hD_inv_apply i, map_smul, map_smul, h1]
    by_cases hia : i = a
    · rw [hia, qtwoDB32_dTauZ_apply_left h2 hab, map_smul, hD_apply b, dPerm_apply,
        Equiv.swap_apply_left]
      rw [smul_smul, smul_smul]
      have hta : t a * t a = 1 := by rcases ht a with h | h <;> rw [h] <;> decide
      have htb : t b * t b = 1 := by rcases ht b with h | h <;> rw [h] <;> decide
      have hte : (t a * eps a b) * t b = 1 := by
        rw [← ht_eps a b hab]
        calc (t a * (t a * t b)) * t b = (t a * t a) * (t b * t b) := by ring
          _ = 1 := by rw [hta, htb, one_mul]
      rw [hte, one_smul]
    · by_cases hib : i = b
      · rw [hib, qtwoDB32_dTauZ_apply_right h2 hab, map_smul, hD_apply a, dPerm_apply,
          Equiv.swap_apply_right]
        rw [smul_smul, smul_smul]
        have hta : t a * t a = 1 := by rcases ht a with h | h <;> rw [h] <;> decide
        have htb : t b * t b = 1 := by rcases ht b with h | h <;> rw [h] <;> decide
        have hte : (t b * eps a b) * t a = 1 := by
          rw [← ht_eps a b hab]
          calc (t b * (t a * t b)) * t a = (t a * t a) * (t b * t b) := by ring
            _ = 1 := by rw [hta, htb, one_mul]
        rw [hte, one_smul]
      · rw [qtwoDB32_dTauZ_apply_of_ne h2 hia hib, dPerm_apply,
          Equiv.swap_apply_of_ne_of_ne hia hib, hD_apply i, smul_smul]
        have htt : t i * t i = 1 := by rcases ht i with h | h <;> rw [h] <;> decide
        rw [htt, one_smul]
  have hF : (MulAut.conj D).toMonoidHom.comp φ' = qtwoDB32_dPermHom m := by
    refine MonoidHom.eq_of_eqOn_dense (Equiv.Perm.closure_isSwap) fun σ hσ => ?_
    rcases hσ with ⟨a, b, hab, rfl⟩
    show D * φ' (Equiv.swap a b) * D⁻¹ = dPerm m (Equiv.swap a b)
    exact hD_conj a b hab
  refine ⟨D * (dPerm m π₀)⁻¹, π₀⁻¹, fun i => t (π₀⁻¹ i), fun i => ht (π₀⁻¹ i), ?_, ?_⟩
  · intro i
    rw [LinearEquiv.mul_apply, qtwoDB32_dPerm_inv, dPerm_apply, hD_apply]
  · intro σ
    have h := congrArg (fun F : Equiv.Perm (Fin m) →* (DVec m ≃ₗ[ZMod 3] DVec m) =>
      F σ) hF
    rw [show (D * (dPerm m π₀)⁻¹) * φ σ * (D * (dPerm m π₀)⁻¹)⁻¹ =
        D * φ' σ * D⁻¹ by rw [hφ']; group]
    exact h

end CFSG.StandardType.QTwo

end
