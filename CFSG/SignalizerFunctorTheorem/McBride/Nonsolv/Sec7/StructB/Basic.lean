module

public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.RegFam.Fixed
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec6.L62b
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec6.Lines

public section

open CFSG.Open

universe u

namespace CFSG.SignalizerFunctorTheorem.McBride.Nonsolv

section Generic

variable {G : Type*} [Group G]

theorem exists_pow_mul_eq_mul_pow {X A : Subgroup G} (hAX : A ≤ Subgroup.normalizer (X : Set G))
    {h a : G} (hh : h ∈ X) (ha : a ∈ A) (k : ℕ) : ∃ h' ∈ X, (h * a) ^ k = h' * a ^ k := by
  induction k with
  | zero => exact ⟨1, one_mem X, by simp⟩
  | succ k ih =>
    obtain ⟨h', hh', hk⟩ := ih
    have hconj : a ^ k * h * (a ^ k)⁻¹ ∈ X :=
      (Subgroup.mem_normalizer_iff.mp (hAX (pow_mem ha k)) h).mp hh
    refine ⟨h' * (a ^ k * h * (a ^ k)⁻¹), mul_mem hh' hconj, ?_⟩
    rw [pow_succ, hk, pow_succ]
    group

theorem le_of_le_sup_of_coprime {p : ℕ} {X A L : Subgroup G} (hA : IsElemAbelian p A)
    (hAX : A ≤ Subgroup.normalizer (X : Set G)) (hL : L ≤ X ⊔ A)
    (hcop : Nat.Coprime p (Nat.card L)) : L ≤ X := by
  intro x hx
  have hx' : x ∈ ((X ⊔ A : Subgroup G) : Set G) := hL hx
  rw [Subgroup.coe_mul_of_right_le_normalizer_left X A hAX] at hx'
  obtain ⟨h, hh, a, ha, rfl⟩ := hx'
  have hn : Nat.Coprime p (orderOf (h * a)) :=
    hcop.coprime_dvd_right (Subgroup.orderOf_dvd_natCard L hx)
  obtain ⟨h', hh', hk⟩ := exists_pow_mul_eq_mul_pow hAX hh ha (orderOf (h * a))
  rw [pow_orderOf_eq_one] at hk
  have han : a ^ orderOf (h * a) ∈ X := by
    rw [eq_inv_of_mul_eq_one_right hk.symm]
    exact inv_mem hh'
  have hap : a ^ p = 1 := hA.2 a ha
  have hbez : (1 : ℤ) = p * Nat.gcdA p (orderOf (h * a)) + orderOf (h * a) *
      Nat.gcdB p (orderOf (h * a)) := by
    have := Nat.gcd_eq_gcd_ab p (orderOf (h * a))
    rwa [hn.gcd_eq_one, Nat.cast_one] at this
  have haX : a ∈ X := by
    have : a = (a ^ orderOf (h * a)) ^ (Nat.gcdB p (orderOf (h * a))) := by
      calc a = a ^ (1 : ℤ) := (zpow_one a).symm
        _ = a ^ ((p : ℤ) * Nat.gcdA p (orderOf (h * a)) +
              orderOf (h * a) * Nat.gcdB p (orderOf (h * a))) := by rw [← hbez]
        _ = (a ^ p) ^ (Nat.gcdA p (orderOf (h * a))) *
              (a ^ orderOf (h * a)) ^ (Nat.gcdB p (orderOf (h * a))) := by
            rw [zpow_add, zpow_mul, zpow_mul, zpow_natCast, zpow_natCast]
        _ = (a ^ orderOf (h * a)) ^ (Nat.gcdB p (orderOf (h * a))) := by
            rw [hap, one_zpow, one_mul]
    rw [this]
    exact zpow_mem han _
  exact mul_mem hh haX

end Generic

namespace Counterexample

variable {p : ℕ} {G : Type u} [Group G] [Finite G] {A : Subgroup G} {θ : G → Subgroup G}
  {E K : Subgroup G}

theorem kOf_line_of_typeB (h : Counterexample p A θ) (hB : TypeBCore p A θ E K) {F : Subgroup G}
    (hF : F ∈ signalizerFunctorEk p 1 A) (hFE : F ≠ E) : kOf (thetaOf θ F) = thetaOf θ F := by
  obtain ⟨a, ha, ha1, rfl⟩ := exists_zpowers_eq_of_mem_signalizerFunctorEk_one h.prime hF
  refine hB.kOf_eq a ha fun haE => hFE ?_
  exact (h.line_eq_zpowers hB.mem haE ha1).symm

theorem inf_line_eq_bot_of_typeB (h : Counterexample p A θ) (hB : TypeBCore p A θ E K)
    {F : Subgroup G} (hF : F ∈ signalizerFunctorEk p 1 A) (hFE : F ≠ E) : F ⊓ E = ⊥ := by
  rw [inf_comm]
  exact h.inf_eq_bot_of_ne_E1 hB.mem hF hFE.symm

omit [Finite G] in
theorem isFStarSimple_D_of_typeB (hB : TypeBCore p A θ E K) :
    L514.IsFStarSimple ↥(thetaOf θ A) :=
  (L514.isFStarSimple_iff_inSubgroup _).mpr hB.simple_fitting_D

theorem exists_isRegFam_E_of_typeB
    (h : Counterexample p A θ) (hB : TypeBCore p A θ E K) :
    ∃ Ω : Set (Subgroup G), IsRegFam A (thetaOf θ E) Ω E ∧
      ∀ L ∈ Ω, Nonempty (↥L ≃* ↥(thetaOf θ A)) := by
  obtain ⟨L₀, hW, ⟨e⟩⟩ := hB.wreath_E
  have hE0 := h.ne_bot_of_mem_E1 hB.mem
  have hA0 : A ≠ ⊥ := by
    obtain ⟨a, ha, ha1⟩ := h.exists_ne_one
    exact fun h0 => ha1 (Subgroup.mem_bot.mp (h0 ▸ ha))
  have hAX := h.isFunctor.normalizes_thetaOf hB.mem.1
  have hcop : Nat.Coprime p (Nat.card L₀) := by
    rw [Nat.card_congr e.toEquiv]
    exact h.isFunctor.coprime_thetaOf le_rfl hA0
  have hLX : L₀ ≤ thetaOf θ E := le_of_le_sup_of_coprime h.elemAbelian hAX hW.H_le hcop
  have hL1 : L₀ ≠ ⊥ := by
    rintro rfl
    exact h.not_isSolvable_D (Group.isSolvable_of_isSolvable_injective
      (f := e.symm.toMonoidHom) e.symm.injective)
  have hcopA : Nat.Coprime (Nat.card A) (Nat.card (thetaOf θ E)) := by
    rw [h.card]
    exact Nat.Coprime.pow_left 3 (h.isFunctor.coprime_thetaOf hB.mem.1 hE0)
  refine ⟨_, IsWreath.isRegFam hW hAX hcopA hLX hL1, ?_⟩
  rintro _ ⟨a, -, rfl⟩
  exact ⟨(Subgroup.equivMapOfInjective L₀ _ (MulAut.conj a).injective).symm.trans e⟩

end Counterexample

end CFSG.SignalizerFunctorTheorem.McBride.Nonsolv
