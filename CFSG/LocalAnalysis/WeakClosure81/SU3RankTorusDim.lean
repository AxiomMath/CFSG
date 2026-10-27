module

public import CFSG.SignalizerFunctorTheorem.Quadratic.Defs
import CFSG.LocalAnalysis.WeakClosure81.SU3RankPrimePower
import CFSG.LocalAnalysis.WeakClosure81.TenFive

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.SignalizerFunctorTheorem.Quadratic

theorem orderOf_two_dvd_finrank_fixSub_inf_commSub {F : Type} [AddCommGroup F]
    [Module (ZMod 2) F] [Finite F] {ℓ k : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hk : 1 ≤ k)
    {E : Subgroup (LGL 2 F)} (hcard : Nat.card E = ℓ ^ 2) {B : Subgroup (LGL 2 F)} (hBE : B ≤ E)
    (hB : Nat.card B = ℓ) {τ : LGL 2 F} (hτE : ∀ e ∈ E, τ * e = e * τ) (hτ : τ ^ (ℓ ^ k) = 1)
    (hτE' : τ ^ (ℓ ^ (k - 1)) ∈ E) (hτB : τ ^ (ℓ ^ (k - 1)) ∉ B) :
    orderOf (2 : ZMod (ℓ ^ k)) ∣ Module.finrank (ZMod 2) ↥(fixSub B ⊓ commSub E) := by
  classical
  have hoddE : Odd (Nat.card E) := by
    rw [hcard]
    exact (hℓ.odd_of_ne_two hℓ2).pow
  have hcompl : IsCompl (fixSub E) (commSub E) := isCompl_fixSub_commSub_of_odd E hoddE
  have hτnormB : τ ∈ Subgroup.normalizer (B : Set (LGL 2 F)) :=
    Subgroup.centralizer_le_normalizer (B : Set (LGL 2 F))
      (Subgroup.mem_centralizer_iff.mpr fun b hb => (hτE b (hBE hb)).symm)
  have hτnormE : τ ∈ Subgroup.normalizer (E : Set (LGL 2 F)) :=
    Subgroup.centralizer_le_normalizer (E : Set (LGL 2 F))
      (Subgroup.mem_centralizer_iff.mpr fun b hb => (hτE b hb).symm)
  have hM : ∀ x ∈ fixSub B ⊓ commSub E, τ x ∈ fixSub B ⊓ commSub E := by
    intro x hx
    exact ⟨map_mem_fixSub_of_mem_normalizer B hτnormB hx.1,
      map_mem_commSub_of_mem_normalizer E hτnormE hx.2⟩
  have hle_sup : B ⊔ Subgroup.zpowers (τ ^ (ℓ ^ (k - 1))) ≤ E :=
    sup_le hBE (Subgroup.zpowers_le.mpr hτE')
  have hcard_sup : Nat.card ↥(B ⊔ Subgroup.zpowers (τ ^ (ℓ ^ (k - 1)))) = ℓ ^ 2 := by
    have hdvd : Nat.card ↥(B ⊔ Subgroup.zpowers (τ ^ (ℓ ^ (k - 1)))) ∣ ℓ ^ 2 := by
      rw [← hcard]
      exact Subgroup.card_dvd_of_le hle_sup
    have hBdvd : ℓ ∣ Nat.card ↥(B ⊔ Subgroup.zpowers (τ ^ (ℓ ^ (k - 1)))) := by
      rw [← hB]
      exact Subgroup.card_dvd_of_le le_sup_left
    obtain ⟨m, hmle, hmeq⟩ := (Nat.dvd_prime_pow hℓ).mp hdvd
    have hmne0 : m ≠ 0 := by
      rintro rfl
      rw [pow_zero] at hmeq
      exact hℓ.not_dvd_one (hmeq ▸ hBdvd)
    have hmne1 : m ≠ 1 := by
      rintro rfl
      rw [pow_one] at hmeq
      have hEq : B = B ⊔ Subgroup.zpowers (τ ^ (ℓ ^ (k - 1))) :=
        Subgroup.eq_of_le_of_card_ge le_sup_left (by rw [hmeq, hB])
      exact hτB (hEq.symm ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers _))
    have hm2 : m = 2 := by omega
    rw [hmeq, hm2]
  have hsup : B ⊔ Subgroup.zpowers (τ ^ (ℓ ^ (k - 1))) = E :=
    Subgroup.eq_of_le_of_card_ge hle_sup (by rw [hcard, hcard_sup])
  have hfix : ∀ x ∈ fixSub B ⊓ commSub E,
      (τ ^ (ℓ ^ (k - 1))) x = x → x = 0 := by
    intro x hx hxe
    have hxfixB : ∀ b ∈ B, b x = x := (mem_fixSub B).mp hx.1
    let K : Subgroup (LGL 2 F) :=
      { carrier := {a | a x = x}
        mul_mem' := fun {a b} ha hb => by
          change a x = x at ha
          change b x = x at hb
          change (a * b) x = x
          rw [LinearEquiv.mul_apply, hb, ha]
        one_mem' := by
          change (1 : LGL 2 F) x = x
          simp
        inv_mem' := fun {a} ha => by
          change a x = x at ha
          change a⁻¹ x = x
          have h := congrArg (fun y : F => a⁻¹ y) ha
          simpa using h.symm }
    have hBK : B ≤ K := fun b hb => show b x = x from hxfixB b hb
    have heK : τ ^ (ℓ ^ (k - 1)) ∈ K := by
      show (τ ^ (ℓ ^ (k - 1))) x = x
      exact hxe
    have hsupK : B ⊔ Subgroup.zpowers (τ ^ (ℓ ^ (k - 1))) ≤ K :=
      sup_le hBK (Subgroup.zpowers_le.mpr heK)
    have hxfixE : x ∈ fixSub E := by
      rw [mem_fixSub E]
      intro a ha
      exact (hsup ▸ hsupK) ha
    have hxinf : x ∈ fixSub E ⊓ commSub E := ⟨hxfixE, hx.2⟩
    rw [hcompl.inf_eq_bot] at hxinf
    exact (Submodule.mem_bot (ZMod 2)).mp hxinf
  exact orderOf_two_dvd_finrank_of_pow_prime_pow hℓ hℓ2 hk hτ (fixSub B ⊓ commSub E) hM hfix

end CFSG.LocalAnalysis.WeakClosure81

end
