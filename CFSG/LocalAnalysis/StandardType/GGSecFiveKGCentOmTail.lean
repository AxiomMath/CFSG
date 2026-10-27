module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveKGCentOmCorank
public import CFSG.LocalAnalysis.StandardType.GGRootCentKGOTwoOmPlusStep

import CFSG.LocalAnalysis.StandardType.GGSecFiveKGCentOmTorus
import CFSG.LocalAnalysis.StandardType.GGRootCentralizerOmegaSpin
import CFSG.RankThree.OrthogonalInvolutions.Dickson

public section

namespace CFSG.StandardType.KGCentOm

open CFSG.LieType.Universal CFSG.LieType.Universal.Spin CFSG.StandardType.KGOm QuadraticMap

private theorem linearEquiv_eq_of_vec_eq {n : ℕ} {K : Type} [Field K] (hn : 3 ≤ n)
    {f g : (Fin n ⊕ Fin n → K) ≃ₗ[K] (Fin n ⊕ Fin n → K)}
    (h : ∀ (i : Fin n) (r : Bool),
      f ((plusFrame n K hn).vec i r) = g ((plusFrame n K hn).vec i r)) : f = g :=
  LinearEquiv.toLinearMap_injective (LinearMap.ext_on_range
    (CFSG.LieType.Steinberg.CentralExt.SpinPlusClosed.span_plusFrame hn) fun p => h p.1 p.2)

private theorem exists_mem_ggTorus_spinAction_eq {n : ℕ} {K : Type} [Field K] [Finite K]
    [CharP K 2] (hn : 3 ≤ n) {g : (Fin n ⊕ Fin n → K) ≃ₗ[K] (Fin n ⊕ Fin n → K)}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup (quadPlus n K))
    (hd : ∀ (i : Fin n) (r : Bool),
      ∃ a : K, g ((plusFrame n K hn).vec i r) = a • (plusFrame n K hn).vec i r) :
    ∃ h ∈ ggTorus (plusDatum n K hn), spinAction (quadPlus n K) h = g := by
  choose a ha using hd
  have hab : ∀ i, a i true * a i false = 1 := fun i => by
    have h1 := TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup hg
      ((plusFrame n K hn).vec i true) ((plusFrame n K hn).vec i false)
    have hp : polar (quadPlus n K) ((plusFrame n K hn).vec i true)
        ((plusFrame n K hn).vec i false) = 1 := (plusFrame n K hn).polar_vec_not i true
    rw [ha, ha, polar_smul_left, polar_smul_right, hp, smul_eq_mul, smul_eq_mul, mul_one] at h1
    exact h1
  have hne : ∀ i, a i true ≠ 0 := fun i h0 => by simpa [h0] using hab i
  obtain ⟨h, hT, hh⟩ := exists_mem_ggTorus_vec_eq_smul hn fun i => Units.mk0 (a i true) (hne i)
  refine ⟨h, hT, linearEquiv_eq_of_vec_eq hn fun i r => ?_⟩
  cases r
  · rw [(hh i).2, ha i false, Units.val_mk0, eq_inv_of_mul_eq_one_right (hab i)]
  · rw [(hh i).1, ha i true, Units.val_mk0]

theorem conj_eq_self_of_plusSemi_one {n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    (hn : 3 ≤ n) {G : Type*} [Group G] {ψ : spinGroup (quadPlus n K) →* G}
    (hψ : Function.Injective ψ) {t : G} (ht2 : ∃ m : ℕ, t ^ (2 ^ m) = 1)
    {γ : spinGroup (quadPlus n K)} {c : spinGroup (quadPlus n K) →* spinGroup (quadPlus n K)}
    {ε : Bool} (hconj : ∀ k, t * ψ k * t⁻¹ = ψ (γ * c k * γ⁻¹))
    (hcA : ∀ (k : spinGroup (quadPlus n K)) (y : Fin n ⊕ Fin n → K),
      spinAction (quadPlus n K) (c k) (plusSemi (by omega) ε 1 y) =
        plusSemi (by omega) ε 1 (spinAction (quadPlus n K) k y))
    {S : Set (spinGroup (quadPlus n K))} (hST : S ⊆ ggTorus (plusDatum n K hn))
    (hS : ∀ s ∈ S, γ * c s * γ⁻¹ = s)
    (hR : ∀ {i j : Fin n} (hij : i ≠ j) (s s' : Bool),
      (∀ σ ∈ S, ∀ b : K, σ * (plusFrame n K hn).longRoot hij s s' (.ofAdd b) * σ⁻¹ =
        (plusFrame n K hn).longRoot hij s s' (.ofAdd b)) →
      ∀ b : K, γ * c ((plusFrame n K hn).longRoot hij s s' (.ofAdd b)) * γ⁻¹ =
        (plusFrame n K hn).longRoot hij s s' (.ofAdd b))
    (hI1 : ¬ ∃! i : Fin n, KGCFixedIdx hn S i) :
    ∀ k, t * ψ k * t⁻¹ = ψ k := by
  have hn1 : 1 ≤ n := by omega
  have hcom : ∀ (r : (Fin n ⊕ Fin n → K) ≃ₗ[K] (Fin n ⊕ Fin n → K)) {k : spinGroup (quadPlus n K)},
      (∀ k, spinAction (quadPlus n K) (c k) = r * spinAction (quadPlus n K) k * r⁻¹) →
      γ * c k * γ⁻¹ = k → spinAction (quadPlus n K) γ * r * spinAction (quadPlus n K) k =
        spinAction (quadPlus n K) k * (spinAction (quadPlus n K) γ * r) := fun r k hcr hk => by
    have e := congrArg (spinAction (quadPlus n K)) hk
    rw [map_mul, map_mul, map_inv, hcr] at e
    calc spinAction (quadPlus n K) γ * r * spinAction (quadPlus n K) k =
        spinAction (quadPlus n K) γ * (r * spinAction (quadPlus n K) k * r⁻¹) *
          (spinAction (quadPlus n K) γ)⁻¹ * (spinAction (quadPlus n K) γ * r) := by group
      _ = spinAction (quadPlus n K) k * (spinAction (quadPlus n K) γ * r) := by rw [e]
  have hdiag : ∀ r : (Fin n ⊕ Fin n → K) ≃ₗ[K] (Fin n ⊕ Fin n → K),
      (∀ k, spinAction (quadPlus n K) (c k) = r * spinAction (quadPlus n K) k * r⁻¹) →
      ∀ (i : Fin n) (rr : Bool), ∃ a : K, (spinAction (quadPlus n K) γ * r)
        ((plusFrame n K hn).vec i rr) = a • (plusFrame n K hn).vec i rr := fun r hcr =>
    exists_map_vec_eq_smul_of_commute hn hST (fun s hs => hcom r hcr (hS s hs))
      (fun hij s s' hc b => hcom r hcr (hR hij s s' hc b)) hI1
  have hcen : ∀ z : spinGroup (quadPlus n K), (∀ k, z * k * z⁻¹ = k) → z = 1 := fun z hz => by
    have h : z ∈ Subgroup.center (spinGroup (quadPlus n K)) :=
      Subgroup.mem_center_iff.mpr fun k => (mul_inv_eq_iff_eq_mul.mp (hz k)).symm
    rwa [RootCentOmega.center_spinGroup_quadPlus_eq_bot_charTwo (K := K) hn,
      Subgroup.mem_bot] at h
  cases ε
  · have hc1 : ∀ k, c k = k := fun k => RootCentOmega.spinAction_quadPlus_injective
      (LinearEquiv.ext fun y => by simpa only [plusSemi_false_one] using hcA k y)
    have hd := hdiag 1 fun k => by rw [hc1 k, inv_one, mul_one, one_mul]
    obtain ⟨m, hm⟩ := ht2
    have hpow : ∀ (j : ℕ) (k : spinGroup (quadPlus n K)),
        t ^ j * ψ k * (t ^ j)⁻¹ = ψ (γ ^ j * k * (γ ^ j)⁻¹) := by
      intro j
      induction j with
      | zero => intro k; simp
      | succ j ih =>
        intro k
        calc t ^ (j + 1) * ψ k * (t ^ (j + 1))⁻¹ = t * (t ^ j * ψ k * (t ^ j)⁻¹) * t⁻¹ := by
              rw [pow_succ']; group
          _ = ψ (γ ^ (j + 1) * k * (γ ^ (j + 1))⁻¹) := by
              rw [ih, hconj, hc1, pow_succ']
              congr 1
              group
    have hγm : γ ^ 2 ^ m = 1 := hcen _ fun k => hψ (by
      have e := hpow (2 ^ m) k
      rw [hm, one_mul, inv_one, mul_one] at e
      exact e.symm)
    have hfix : ∀ (i : Fin n) (rr : Bool), spinAction (quadPlus n K) γ
        ((plusFrame n K hn).vec i rr) = (plusFrame n K hn).vec i rr := fun i rr => by
      obtain ⟨a, ha⟩ := hd i rr
      rw [mul_one] at ha
      have hpa : ∀ j : ℕ, (spinAction (quadPlus n K) γ ^ j) ((plusFrame n K hn).vec i rr) =
          a ^ j • (plusFrame n K hn).vec i rr := by
        intro j
        induction j with
        | zero => rw [pow_zero, pow_zero, one_smul, LinearEquiv.coe_one, id_eq]
        | succ j ih =>
          rw [pow_succ (spinAction (quadPlus n K) γ) j, LinearEquiv.mul_apply, ha, map_smul, ih,
            smul_smul, pow_succ' a j]
      have h1 := congrFun (hpa (2 ^ m)) (kgcIdx i rr)
      rw [← map_pow, hγm, map_one, LinearEquiv.coe_one, id_eq, plusFrame_vec_eq_single_kgcIdx hn,
        Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one] at h1
      have h2 := sub_pow_char_pow (p := 2) a 1 m
      rw [← h1, one_pow, sub_self, pow_eq_zero_iff (pow_ne_zero m two_ne_zero),
        sub_eq_zero] at h2
      rw [ha, h2, one_smul]
    have hγ1 : γ = 1 := RootCentOmega.spinAction_quadPlus_injective (by
      rw [map_one]
      exact linearEquiv_eq_of_vec_eq hn fun i rr => by rw [hfix, LinearEquiv.coe_one, id_eq])
    intro k
    rw [hconj, hc1, hγ1, one_mul, inv_one, mul_one]
  · exfalso
    have hr : ∀ y : Fin n ⊕ Fin n → K, plusSemi hn1 true 1 y = plusSemiReflection hn1 y :=
      plusSemi_true_one_apply hn1
    have hcr : ∀ k, spinAction (quadPlus n K) (c k) =
        plusSemiReflection hn1 * spinAction (quadPlus n K) k * (plusSemiReflection hn1)⁻¹ :=
      fun k => LinearEquiv.ext fun x => by
        obtain ⟨y, rfl⟩ : ∃ y, plusSemiReflection hn1 y = x :=
          ⟨(plusSemiReflection hn1)⁻¹ x, LinearEquiv.apply_symm_apply _ _⟩
        have h := hcA k y
        rw [hr, hr] at h
        rw [h, LinearEquiv.mul_apply, LinearEquiv.mul_apply,
          show (plusSemiReflection hn1)⁻¹ (plusSemiReflection hn1 y) = y from
            LinearEquiv.symm_apply_apply _ _]
    have hgO : spinAction (quadPlus n K) γ * plusSemiReflection hn1 ∈
        TauCeti.QuadraticMap.orthogonalGroup (quadPlus n K) :=
      mul_mem (TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr
        (map_spinAction (quadPlus n K) γ)) (plusSemiReflection_mem hn1)
    obtain ⟨h, -, hh⟩ := exists_mem_ggTorus_spinAction_eq hn hgO (hdiag _ hcr)
    have hrE : plusSemiReflection hn1 ∈
        CFSG.ClassicalGroups.Orthogonal.elementaryGroup (quadPlus n K) := by
      rw [← range_spinAction_quadPlus hn]
      exact ⟨γ⁻¹ * h, by rw [map_mul, hh, map_inv, inv_mul_cancel_left]⟩
    have heven := (CFSG.RankThree.OrthogonalInvolutions.mem_omegaGroup.mp
      (RootCentOmega.elementaryGroup_quadPlus_le_omegaGroup hn hrE)).2
    rw [finrank_commSpace_plusSemiReflection hn1] at heven
    exact Nat.not_even_one heven

end CFSG.StandardType.KGCentOm

end
