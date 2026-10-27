module

public import CFSG.Quasithin.Background.HFL3PRank

public section

namespace CFSG.Quasithin.RonanH44

open CFSG.Quasithin CFSG.Quasithin.H CFSG.Quasithin.H.L3Nine CFSG.Quasithin.H.SU3 Matrix
open scoped MatrixGroups

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}

theorem le_norm_of_perfectCore (hK : Nat.card K = (2 ^ n) ^ 2)
    {M : Subgroup (MulAut (HMod n K))} (hM : perfectCore M = img hK) : M ≤ norm hK := by
  have h := (Subgroup.le_normalizer (H := M)).trans (normalizer_le_normalizer_perfectCore M)
  rw [hM] at h
  exact h

theorem img_le_of_perfectCore (hK : Nat.card K = (2 ^ n) ^ 2)
    {M : Subgroup (MulAut (HMod n K))} (hM : perfectCore M = img hK) : img hK ≤ M := by
  have h := perfectCore_le M
  rw [hM] at h
  exact h

theorem part3 (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2)
    {M : Subgroup (MulAut (HMod n K))} (hMN : M ≤ norm hK) :
    ∀ A : Subgroup (MulAut (HMod n K)), IsA2 M A →
      (3 * n ≤ rk ↥A ∨ (A ≤ img hK ∧ n < rk ↥A)) → 5 * n ≤ rkIdx (fixV A) := by
  intro A hA hr
  have hAc : Nat.card ↥A = 2 ^ rk ↥A :=
    card_eq_two_pow_of_isPGroup (E3.isPGroup_of_isElemAbelian2 hA.2.2)
  have hcard : 2 ^ (3 * n) ≤ Nat.card ↥A ∨ (A ≤ img hK ∧ 2 ^ n < Nat.card ↥A) := by
    rcases hr with h | ⟨hAL, h⟩
    · exact Or.inl (by rw [hAc]; exact Nat.pow_le_pow_right (by norm_num) h)
    · exact Or.inr ⟨hAL, by rw [hAc]; exact Nat.pow_lt_pow_right (by norm_num) h⟩
  have h := le_rkIdx_of_card_le hn hK (j := 4 * n) (by omega)
    (card_fixV_le_of_three hn hK (hA.1.trans hMN) hA.2.2 hcard)
  omega

theorem part4 (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2)
    {M : Subgroup (MulAut (HMod n K))} (hMN : M ≤ norm hK) :
    ∀ A : Subgroup (MulAut (HMod n K)), IsA2 (img hK) A → rk ↥A = 4 * n →
      ¬ ∃ x ∈ M ⊓ Subgroup.normalizer (A : Set (MulAut (HMod n K))),
        orderOf x = 2 ^ (2 * n) - 1 ∧ rk ↥(fixV (A ⊔ Subgroup.zpowers x)) = 3 * n := by
  intro A hA hrk
  rintro ⟨x, ⟨hxM, hxN⟩, hord, hfix⟩
  have hAc : Nat.card ↥A = 2 ^ rk ↥A :=
    card_eq_two_pow_of_isPGroup (E3.isPGroup_of_isElemAbelian2 hA.2.2)
  have hcard : Nat.card ↥A = Nat.card K ^ 2 := by
    rw [hAc, hrk, hK]
    ring
  have hodd : Odd (orderOf x) := by
    rw [hord]
    have h2 : 2 ∣ 2 ^ (2 * n) := dvd_pow_self 2 (by omega)
    have hpos : 0 < 2 ^ (2 * n) := by positivity
    rw [Nat.odd_iff]
    omega
  have hx : x ∈ norm hK := hMN hxM
  have hfixc : Nat.card ↥(fixV (A ⊔ Subgroup.zpowers x)) = 2 ^ (3 * n) := by
    rw [card_eq_two_pow sq_eq_one_HMod (fixV (A ⊔ Subgroup.zpowers x)), hfix]
  exact card_fixV_sup_ne hn hK hA.1 hA.2.2 hcard hx hxN hodd hfixc

theorem two_pow_mod_three_even_aux {m : ℕ} (h : Even m) : 2 ^ m % 3 = 1 := by
  obtain ⟨k, rfl⟩ := h
  have h4 : 2 ^ (k + k) = 4 ^ k := by rw [← two_mul, pow_mul]; norm_num
  rw [h4, Nat.pow_mod]
  norm_num

theorem two_pow_mod_three_odd_aux {m : ℕ} (h : Odd m) : 2 ^ m % 3 = 2 := by
  obtain ⟨k, rfl⟩ := h
  have h4 : 2 ^ (2 * k) = 4 ^ k := by rw [pow_mul]; norm_num
  have h1 : 4 ^ k % 3 = 1 := by rw [Nat.pow_mod]; norm_num
  rw [pow_succ, h4]
  omega

theorem pow_eq_pow_mod_three_aux {R : Type*} [Monoid R] {c : R} (h3 : c ^ 3 = 1) (e : ℕ) :
    c ^ e = c ^ (e % 3) := by
  conv_lhs => rw [← Nat.div_add_mod e 3, pow_add, pow_mul, h3, one_pow, one_mul]

theorem part7 (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2) :
    (Odd n → Nonempty (↥(img hK) ≃* PSL(3, K))) ∧ (Even n → Nonempty (↥(img hK) ≃* SL(3, K))) := by
  have hscal : ∀ g : SpecialLinearGroup (Fin 3) K,
      g ∈ CFSG.LocalAnalysis.ComponentInitial.LinearFlag.scalars 3 K →
      ∃ c : Kˣ, (c : K) ^ 3 = 1 ∧ (g : Matrix (Fin 3) (Fin 3) K) = (c : K) • 1 := by
    intro g hg
    obtain ⟨c, hc, hgc⟩ := CFSG.LocalAnalysis.ComponentInitial.LinearFlag.mem_scalars.mp hg
    refine ⟨c, ?_, ?_⟩
    · have h := congrArg Units.val hc
      rwa [Units.val_pow_eq_pow_val, Units.val_one] at h
    · rw [hgc, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]
  have hodd_c : Odd n → ∀ c : K, c ^ 3 = 1 → c * bar n c = 1 := by
    intro hodd c hc
    have h3 : (2 ^ n + 1) % 3 = 0 := by
      have := two_pow_mod_three_odd_aux hodd
      omega
    rw [bar_apply, ← pow_succ', pow_eq_pow_mod_three_aux hc, h3, pow_zero]
  have heven_c : Even n → ∀ c : K, c ^ 3 = 1 → c * bar n c = 1 → c = 1 := by
    intro heven c hc hcb
    have h3 : (2 ^ n + 1) % 3 = 2 := by
      have := two_pow_mod_three_even_aux heven
      omega
    rw [bar_apply, ← pow_succ', pow_eq_pow_mod_three_aux hc, h3] at hcb
    calc c = c * 1 := (mul_one c).symm
      _ = c * c ^ 2 := by rw [hcb]
      _ = c ^ 3 := by ring
      _ = 1 := hc
  constructor
  · intro hodd
    have hker : (rho hK).ker = Subgroup.center (SpecialLinearGroup (Fin 3) K) := by
      rw [← CFSG.LocalAnalysis.ComponentInitial.LinearFlag.scalars_eq_center 3 K]
      ext g
      rw [MonoidHom.mem_ker]
      constructor
      · intro h
        exact mem_scalars_of_rho_eq_one hK h
      · intro hg
        obtain ⟨c, hc3, hgc⟩ := hscal g hg
        exact rhoT_eq_one_of_smul hK (B := SpecialLinearGroup.toGL g) hgc
          (hodd_c hodd (c : K) hc3)
    exact ⟨(QuotientGroup.quotientKerEquivRange (rho hK)).symm.trans
      (QuotientGroup.quotientMulEquivOfEq hker)⟩
  · intro heven
    have hinj : Function.Injective (rho hK) := by
      rw [injective_iff_map_eq_one]
      intro g h
      obtain ⟨c, hc3, hgc⟩ := hscal g (mem_scalars_of_rho_eq_one hK h)
      have hcb : (c : K) * bar n (c : K) = 1 :=
        norm_eq_one_of_rhoT_smul hK (B := SpecialLinearGroup.toGL g) hgc h
      have hc1 : (c : K) = 1 := heven_c heven (c : K) hc3 hcb
      have hg1 : (g : Matrix (Fin 3) (Fin 3) K) = 1 := by
        rw [hgc, hc1, one_smul]
      exact Subtype.ext (hg1.trans Matrix.SpecialLinearGroup.coe_one.symm)
    exact ⟨(MonoidHom.ofInjective hinj).symm⟩

end CFSG.Quasithin.RonanH44
