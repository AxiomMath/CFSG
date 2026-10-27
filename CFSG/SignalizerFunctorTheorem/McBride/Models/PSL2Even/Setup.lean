module

public import CFSG.SignalizerFunctorTheorem.McBride.Models.PSL2Even.S3
import CFSG.SignalizerFunctorTheorem.NearModels.PSLTwo
import CFSG.SignalizerFunctorTheorem.NearModels.PSLTwo.Arithmetic
import CFSG.Walter.PSL2Facts.Even
import CFSG.SignalizerFunctorTheorem.McBride.Models.PSL2Even.Arithmetic

public section

open CFSG.Open
open scoped MatrixGroups

namespace CFSG.SignalizerFunctorTheorem.McBride.PSL2Even

open CFSG.SignalizerFunctorTheorem.NearModels CFSG.SignalizerFunctorTheorem.NearModels.PSLTwo

section Setup

variable {p : ℕ}

theorem odd_of_coprime (hp : p.Prime)
    (hcop : Nat.Coprime p (Nat.card PSL(2, GaloisField 2 p))) : Odd p :=
  odd_of_coprime_natCard_psl2 _ hp hcop

theorem ne_three_of_coprime (hp : p.Prime)
    (hcop : Nat.Coprime p (Nat.card PSL(2, GaloisField 2 p))) : p ≠ 3 := by
  rintro rfl
  rw [CFSG.Walter.psl2_even_card hp.ne_zero] at hcop
  norm_num [Nat.Coprime] at hcop

theorem not_nine_dvd_card_of_coprime (hp : p.Prime)
    (hcop : Nat.Coprime p (Nat.card PSL(2, GaloisField 2 p))) :
    ¬ 9 ∣ Nat.card PSL(2, GaloisField 2 p) := by
  rw [CFSG.Walter.psl2_even_card hp.ne_zero]
  exact not_nine_dvd_card hp (odd_of_coprime hp hcop) (ne_three_of_coprime hp hcop)

theorem isSimpleGroup_of_prime (hp : p.Prime) : IsSimpleGroup PSL(2, GaloisField 2 p) := by
  refine Matrix.ProjectiveSpecialLinearGroup.rank_two_simple ?_
  rw [GaloisField.card 2 p hp.ne_zero]
  calc 4 = 2 ^ 2 := by norm_num
    _ ≤ 2 ^ p := Nat.pow_le_pow_right (by norm_num) hp.two_le

theorem card_fixed (hp : p.Prime) (hcop : Nat.Coprime p (Nat.card PSL(2, GaloisField 2 p)))
    (f : MulAut PSL(2, GaloisField 2 p)) (hf : orderOf f = p) :
    Nat.card (signalizerFixedSubgroup f) = 6 := by
  obtain ⟨e⟩ := psl2_fixedSubgroup_mulEquiv 2 hp hcop f hf
  rw [Nat.card_congr e.toEquiv,
    Nat.card_congr (CFSG.Walter.psl2MulEquivSL2OfCharTwo (K := ZMod 2)).toEquiv]
  have : Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)) = 2 ^ 1 * 3 ^ 1 := by
    rw [Nat.card_eq_fintype_card]; decide
  rw [this]
  norm_num

theorem hY2_of_charTwo : ∀ u : PSL(2, GaloisField 2 p), orderOf u = 2 →
    IsPGroup 2 (Subgroup.centralizer ({u} : Set PSL(2, GaloisField 2 p))) :=
  fun _ hu => CFSG.Walter.psl2_centralizer_isPGroup_of_charTwo hu

theorem exists_S3Data_of_coprime (hp : p.Prime)
    (hcop : Nat.Coprime p (Nat.card PSL(2, GaloisField 2 p)))
    (f : MulAut PSL(2, GaloisField 2 p)) (hf : orderOf f = p) :
    ∃ c t : PSL(2, GaloisField 2 p), S3Data f c t :=
  exists_S3Data f hY2_of_charTwo (card_fixed hp hcop f hf)

end Setup

theorem isPGroup_of_coprime_eq_one {G : Type*} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    (h : ∀ g : G, Nat.Coprime p (orderOf g) → g = 1) : IsPGroup p G := by
  have : Fact p.Prime := ⟨hp⟩
  refine IsPGroup.iff_orderOf.mpr fun g => ?_
  obtain ⟨a, m, hm, hg⟩ := Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos g).ne' p hp.ne_one
  refine ⟨a, ?_⟩
  have hdvd : p ^ a ∣ orderOf g := ⟨m, hg⟩
  have hord : orderOf (g ^ (p ^ a)) = m := by
    rw [orderOf_pow_of_dvd (pow_ne_zero a hp.ne_zero) hdvd, hg,
      Nat.mul_div_cancel_left _ (pow_pos hp.pos a)]
  have hcop : Nat.Coprime p m := (Nat.Prime.coprime_iff_not_dvd hp).mpr hm
  have h1 := h (g ^ (p ^ a)) (by rw [hord]; exact hcop)
  rw [h1, orderOf_one] at hord
  rw [hg, ← hord, mul_one]

theorem mem_normalizer_of_forall_conj_mem {Y : Type*} [Group Y] [Finite Y] {M : Subgroup Y}
    {x : Y} (hx : ∀ m ∈ M, x * m * x⁻¹ ∈ M) : x ∈ Subgroup.normalizer (M : Set Y) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  refine ⟨fun hh => hx h hh, fun hh => ?_⟩
  let φ : M → M := fun m => ⟨x * m * x⁻¹, hx m m.2⟩
  have hinj : Function.Injective φ := fun a b hab => by
    apply Subtype.ext
    have : x * (a : Y) * x⁻¹ = x * (b : Y) * x⁻¹ := congrArg Subtype.val hab
    simpa using this
  obtain ⟨m, hm⟩ := (Finite.injective_iff_surjective.mp hinj) ⟨x * h * x⁻¹, hh⟩
  have hmh : (m : Y) = h := by
    have : x * (m : Y) * x⁻¹ = x * h * x⁻¹ := congrArg Subtype.val hm
    simpa using this
  exact hmh ▸ m.2

theorem normalizer_eq_of_isCoatom {Y : Type*} [Group Y] (hs : IsSimpleGroup Y) {M : Subgroup Y}
    (hM : IsCoatom M) (hbot : M ≠ ⊥) : Subgroup.normalizer (M : Set Y) = M := by
  by_contra hne
  have hlt : M < Subgroup.normalizer (M : Set Y) :=
    lt_of_le_of_ne Subgroup.le_normalizer (Ne.symm hne)
  have hnorm : M.Normal := Subgroup.normalizer_eq_top_iff.mp (hM.2 _ hlt)
  rcases hs.eq_bot_or_eq_top_of_normal M with h | h
  · exact hbot h
  · exact hM.1 h

end CFSG.SignalizerFunctorTheorem.McBride.PSL2Even
