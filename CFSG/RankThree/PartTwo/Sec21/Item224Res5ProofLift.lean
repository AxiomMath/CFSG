module

public import CFSG.RankThree.LocalRank.SolvablePrimeComplementCore
import CFSG.LieType.CurtisTits.Recognition

public section

namespace CFSG.RankThree.PartTwo.Sec21.Item224Res5Proof

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank

theorem exists_fixed_of_invariant {P Y : Type*} [Group P] [Finite Y] {p : ℕ} [Fact p.Prime]
    (hP : IsPGroup p P) (f : P →* Equiv.Perm Y) (Ω : Set Y)
    (hΩ : ∀ g : P, ∀ y ∈ Ω, f g y ∈ Ω) (hcard : ¬ p ∣ Nat.card Ω) :
    ∃ y ∈ Ω, ∀ g : P, f g y = y := by
  let : MulAction P Y := MulAction.compHom Y f
  let Ω' : SubMulAction P Y := { carrier := Ω, smul_mem' := fun g y hy => hΩ g y hy }
  obtain ⟨⟨y, hy⟩, hfix⟩ := hP.nonempty_fixed_point_of_prime_not_dvd_card Ω' hcard
  exact ⟨y, hy, fun g => congrArg Subtype.val (hfix g)⟩

theorem exists_odd_lift {L : Type*} [Group L] [Finite L] (Θ : Subgroup L) [Θ.Normal]
    (x : L ⧸ Θ) (hx : Odd (orderOf x)) : ∃ y : L, (y : L ⧸ Θ) = x ∧ Odd (orderOf y) := by
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective x
  obtain ⟨a, b, hb, hab⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos y).ne'
  have hcop : (2 ^ a).Coprime (orderOf (QuotientGroup.mk y : L ⧸ Θ)) :=
    Nat.Coprime.pow_left a (Nat.coprime_two_left.mpr hx)
  obtain ⟨k, hk⟩ := exists_pow_eq_self_of_coprime hcop
  refine ⟨(y ^ 2 ^ a) ^ k, ?_, ?_⟩
  · rw [QuotientGroup.mk_pow, QuotientGroup.mk_pow]
    exact hk
  · have h1 : (y ^ 2 ^ a) ^ b = 1 := by rw [← pow_mul, ← hab, pow_orderOf_eq_one]
    exact Odd.of_dvd_nat hb ((orderOf_pow_dvd k).trans (orderOf_dvd_of_pow_eq_one h1))

@[expose] def torsionIn {L : Type*} [Group L] (Θ : Subgroup L) (hΘ : Θ ≤ Subgroup.center L)
    (m : ℕ) : Subgroup L where
  carrier := {θ | θ ∈ Θ ∧ θ ^ m = 1}
  mul_mem' {a b} ha hb := by
    refine ⟨Θ.mul_mem ha.1 hb.1, ?_⟩
    have hc : Commute a b := ((Subgroup.mem_center_iff.mp (hΘ ha.1)) b).symm
    rw [hc.mul_pow, ha.2, hb.2, one_mul]
  one_mem' := ⟨Θ.one_mem, one_pow m⟩
  inv_mem' {a} ha := ⟨Θ.inv_mem ha.1, by rw [inv_pow, ha.2, inv_one]⟩

theorem odd_card_torsionIn {L : Type*} [Group L] [Finite L] (Θ : Subgroup L)
    (hΘ : Θ ≤ Subgroup.center L) {m : ℕ} (hm : Odd m) : ¬ 2 ∣ Nat.card (torsionIn Θ hΘ m) := by
  intro h2
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' 2 h2
  have hgm : (g : L) ^ m = 1 := g.2.2
  have hdvd : orderOf (g : L) ∣ m := orderOf_dvd_of_pow_eq_one hgm
  rw [Subgroup.orderOf_coe, hg] at hdvd
  exact (Nat.not_even_iff_odd.mpr hm) (even_iff_two_dvd.mpr hdvd)

theorem exists_fixed_lift_of_odd {L T : Type*} [Group L] [Finite L] [Group T]
    (Θ : Subgroup L) [Θ.Normal] (hΘ : Θ ≤ Subgroup.center L) (hT : IsPGroup 2 T)
    (ψ : T →* MulAut L) (x : L ⧸ Θ) (hx : Odd (orderOf x))
    (hfix : ∀ t : T, ∀ y : L, (y : L ⧸ Θ) = x → ((ψ t y : L) : L ⧸ Θ) = x) :
    ∃ l : L, (l : L ⧸ Θ) = x ∧ ∀ t : T, ψ t l = l := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨y, hyx, hyodd⟩ := exists_odd_lift Θ x hx
  set m := orderOf y with hm
  set Ω : Set L := {l | (l : L ⧸ Θ) = x ∧ l ^ m = 1} with hΩdef
  have hΩ : Ω = (fun θ => y * θ) '' (torsionIn Θ hΘ m : Set L) := by
    ext l
    constructor
    · rintro ⟨hl, hlm⟩
      have hθ : y⁻¹ * l ∈ Θ := QuotientGroup.eq.mp (hyx.trans hl.symm)
      have hc : Commute y (y⁻¹ * l) :=
        ((Subgroup.mem_center_iff.mp (hΘ hθ)) y)
      refine ⟨y⁻¹ * l, ⟨hθ, ?_⟩, by simp⟩
      have h := hc.mul_pow m
      rw [mul_inv_cancel_left, hlm, pow_orderOf_eq_one, one_mul] at h
      exact h.symm
    · rintro ⟨θ, ⟨hθ, hθm⟩, rfl⟩
      refine ⟨?_, ?_⟩
      · rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff θ).mpr hθ, mul_one, hyx]
      · have hc : Commute y θ := (Subgroup.mem_center_iff.mp (hΘ hθ)) y
        rw [hc.mul_pow, pow_orderOf_eq_one, hθm, one_mul]
  have hcard : ¬ 2 ∣ Nat.card Ω := by
    rw [hΩ, Nat.card_image_of_injective (mul_right_injective y)]
    exact odd_card_torsionIn Θ hΘ (hm ▸ hyodd)
  have hinv : ∀ t : T, ∀ l ∈ Ω, ((MulAut.toPerm L).comp ψ) t l ∈ Ω := by
    rintro t l ⟨hl, hlm⟩
    refine ⟨hfix t l hl, ?_⟩
    change (ψ t l) ^ m = 1
    rw [← map_pow, hlm, map_one]
  obtain ⟨l, ⟨hl, -⟩, hfixl⟩ := exists_fixed_of_invariant hT ((MulAut.toPerm L).comp ψ) Ω hinv
    hcard
  exact ⟨l, hl, hfixl⟩

theorem exists_fixed_lift_of_three {L T : Type*} [Group L] [Finite L] [Group T]
    (Θ : Subgroup L) [Θ.Normal] (hΘ : Θ ≤ Subgroup.center L) (hΘ3 : ¬ 3 ∣ Nat.card Θ)
    (ψ : T →* MulAut L) (x : L ⧸ Θ) (hx : x ^ 3 = 1)
    (hfix : ∀ t : T, ∀ y : L, (y : L ⧸ Θ) = x → ((ψ t y : L) : L ⧸ Θ) = x) :
    ∃ l : L, (l : L ⧸ Θ) = x ∧ l ^ 3 = 1 ∧ ∀ t : T, ψ t l = l := by
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective x
  have hy3 : y ^ 3 ∈ Θ := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
    exact hx
  have hcop : (Nat.card Θ).Coprime 3 :=
    (Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hΘ3))
  obtain ⟨θ₀, hθ₀⟩ := (powCoprime hcop).surjective (⟨y ^ 3, hy3⟩ : Θ)⁻¹
  have hθ₀' : ((θ₀ : L)) ^ 3 = (y ^ 3)⁻¹ := by
    have := congrArg Subtype.val hθ₀
    simpa [powCoprime] using this
  have huniq : ∀ l l' : L, (l : L ⧸ Θ) = y → (l' : L ⧸ Θ) = y → l ^ 3 = 1 → l' ^ 3 = 1 →
      l' = l := by
    intro l l' hl hl' hl3 hl'3
    have hθ : l⁻¹ * l' ∈ Θ := QuotientGroup.eq.mp (hl.trans hl'.symm)
    have hc : Commute l (l⁻¹ * l') := (Subgroup.mem_center_iff.mp (hΘ hθ)) l
    have h3 : (l⁻¹ * l') ^ 3 = 1 := by
      have h := hc.mul_pow 3
      rw [mul_inv_cancel_left, hl'3, hl3, one_mul] at h
      exact h.symm
    have hdvd1 : orderOf (⟨l⁻¹ * l', hθ⟩ : Θ) ∣ 3 := by
      rw [← Subgroup.orderOf_coe]
      exact orderOf_dvd_of_pow_eq_one h3
    have hdvd2 : orderOf (⟨l⁻¹ * l', hθ⟩ : Θ) ∣ Nat.card Θ := orderOf_dvd_natCard _
    have h1 : orderOf (⟨l⁻¹ * l', hθ⟩ : Θ) = 1 :=
      Nat.eq_one_of_dvd_coprimes hcop.symm hdvd1 hdvd2
    rw [orderOf_eq_one_iff] at h1
    have h1' : l⁻¹ * l' = 1 := congrArg Subtype.val h1
    rw [inv_mul_eq_one] at h1'
    exact h1'.symm
  set l := y * (θ₀ : L) with hl
  have hlx : (l : L ⧸ Θ) = y := by
    rw [hl, QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff _).mpr θ₀.2, mul_one]
  have hl3 : l ^ 3 = 1 := by
    have hc : Commute y (θ₀ : L) := (Subgroup.mem_center_iff.mp (hΘ θ₀.2)) y
    rw [hl, hc.mul_pow, hθ₀', mul_inv_cancel]
  refine ⟨l, hlx, hl3, fun t => huniq l (ψ t l) hlx (hfix t l hlx) hl3 ?_⟩
  rw [← map_pow, hl3, map_one]

theorem aschbacherSolvableCore_le_center {Q : Type*} [Group Q] [Finite Q]
    (hQ : CFSG.IsQuasisimple Q) : aschbacherSolvableCore 3 Q ≤ Subgroup.center Q := by
  obtain ⟨hθs, -, -, -, -⟩ :=
    solvable_prime_complement_core_characterization (H := Q) Nat.prime_three
  rcases CFSG.LieType.CurtisTits.le_center_or_eq_top_of_isQuasisimple hQ
      (aschbacherSolvableCore 3 Q) with h | h
  · exact h
  · exfalso
    have hsol' : Group.IsSolvable Q := by
      have hsol : Group.IsSolvable ↥(aschbacherSolvableCore 3 Q) := hθs
      rw [h] at hsol
      exact Group.isSolvable_of_surjective
        (f := (Subgroup.topEquiv : ↥(⊤ : Subgroup Q) ≃* Q).toMonoidHom) (MulEquiv.surjective _)
    obtain ⟨hperf, -, a, b, hab⟩ := hQ
    have : Nontrivial (Q ⧸ Subgroup.center Q) := ⟨⟨a * b, b * a, hab⟩⟩
    have : Nontrivial Q := (QuotientGroup.mk_surjective (s := Subgroup.center Q)).nontrivial
    exact (Group.IsPerfect.not_isSolvable Q) hsol'

end CFSG.RankThree.PartTwo.Sec21.Item224Res5Proof
