module

public import CFSG.RankThree.PartOne.SEITZ6.G2NormU
public import CFSG.RankThree.PartOne.SEITZ6.G2MaxGold

public section

namespace CFSG.RankThree.PartOne.SEITZ6

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Adjoint CFSG.RankThree.PartOne.SEITZ3
  CFSG.RankThree.PartOne.CTP CFSG.Timmesfeld.ExceptionalOrders
open scoped commutatorElement

variable {K : Type} [Field K]

theorem uSL_eq_u2 (c : K) : uSL c = u2 c := by
  apply Subtype.ext
  rw [u2_coe]
  rfl

theorem Up_sq [CharP K 2] {g : adjointGroup .G2 K} (hg : g ∈ Up K) : g ^ 2 = 1 := by
  obtain ⟨a, b, rfl⟩ := mem_Up_iff.1 hg
  rw [((commute_17 b a).symm).mul_pow, pow_two, pow_two, xp_mul_self, xp_mul_self, mul_one]

theorem Up_le_Lp [CharP K 2] : Up K ≤ Lp K := by
  intro g hg
  obtain ⟨a, b, rfl⟩ := mem_Up_iff.1 hg
  exact mul_mem (xp7_mem_Lp a) (xp1_mem_Lp b)

theorem phiP_u2 [CharP K 2] (a b : K) : phiP K (u2 a, u2 b) = xp 7 a * xp 1 b := by
  rw [phiP_apply, show ((u2 a, u2 b) : Matrix.SpecialLinearGroup (Fin 2) K ×
      Matrix.SpecialLinearGroup (Fin 2) K) = (u2 a, 1) * (1, u2 b) by simp, map_mul,
    ← uSL_eq_u2, ← uSL_eq_u2, a1a1Hom_uSL_inl, a1a1Hom_uSL_inr,
    show Wg K * (xp 0 a * xp 8 b) * (Wg K)⁻¹ =
      (Wg K * xp 0 a * (Wg K)⁻¹) * (Wg K * xp 8 b * (Wg K)⁻¹) by group, Wg_xp0, Wg_xp8]

theorem map_Uup_eq [CharP K 2] : ((Uup K).prod (Uup K)).map (phiP K) = Up K := by
  ext g
  constructor
  · rintro ⟨⟨x, y⟩, hxy, rfl⟩
    obtain ⟨a, rfl⟩ := mem_Uup_iff.1 (Subgroup.mem_prod.1 hxy).1
    obtain ⟨b, rfl⟩ := mem_Uup_iff.1 (Subgroup.mem_prod.1 hxy).2
    rw [phiP_u2]
    exact mem_Up_iff.2 ⟨a, b, rfl⟩
  · intro hg
    obtain ⟨a, b, rfl⟩ := mem_Up_iff.1 hg
    exact ⟨(u2 a, u2 b), Subgroup.mem_prod.2 ⟨u2_mem_Uup a, u2_mem_Uup b⟩, phiP_u2 a b⟩

theorem sylow_of_normalizer {X : Type*} [Group X] [Finite X] (S0 : Subgroup X)
    (hN : ∀ y : X, y ∈ Subgroup.normalizer (S0 : Set X) → (∃ k : ℕ, y ^ (2 ^ k) = 1) → y ∈ S0) :
    ∀ {Q : Subgroup X}, IsPGroup 2 Q → S0 ≤ Q → Q = S0 := by
  intro Q hQ hle
  by_contra hne
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnil : Group.IsNilpotent Q := hQ.isNilpotent
  have hcond : NormalizerCondition Q := Group.normalizerCondition_of_isNilpotent
  have hlt' : S0.subgroupOf Q < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro h
    have : Q ≤ S0 := fun x hx => by
      have : (⟨x, hx⟩ : Q) ∈ S0.subgroupOf Q := by rw [h]; trivial
      exact this
    exact hne (le_antisymm this hle)
  have hlt'' := hcond _ hlt'
  obtain ⟨y, hy, hyn⟩ := IsConcreteLE.exists_of_lt hlt''
  apply hyn
  show (y : X) ∈ S0
  apply hN
  · rw [Subgroup.mem_normalizer_iff]
    intro s
    constructor
    · intro hs
      have := (Subgroup.mem_normalizer_iff.1 hy) ⟨s, hle hs⟩
      exact this.1 hs
    · intro hs
      have hsQ : s ∈ Q := by
        have h1 : (y : X)⁻¹ * ((y : X) * s * (y : X)⁻¹) * (y : X) ∈ Q :=
          Q.mul_mem (Q.mul_mem (Q.inv_mem y.2) (hle hs)) y.2
        rwa [show (y : X)⁻¹ * ((y : X) * s * (y : X)⁻¹) * (y : X) = s by group] at h1
      have := (Subgroup.mem_normalizer_iff.1 hy) ⟨s, hsQ⟩
      exact this.2 hs
  · obtain ⟨k, hk⟩ := hQ y
    exact ⟨k, by simpa using congrArg Subtype.val hk⟩

theorem two_elt_in_TgUp [CharP K 2] [Finite K] {t0 u : adjointGroup .G2 K} (ht0 : t0 ∈ Tg K)
    (hu : u ∈ Up K) {k : ℕ} (hk : (t0 * u) ^ (2 ^ k) = 1) : t0 = 1 := by
  have hpow : ∀ j : ℕ, ∃ v ∈ Up K, (t0 * u) ^ j = t0 ^ j * v := by
    intro j
    induction j with
    | zero => exact ⟨1, Subgroup.one_mem _, by simp⟩
    | succ j ih =>
      obtain ⟨v, hv, hvj⟩ := ih
      refine ⟨(t0⁻¹ * v * t0) * u, Subgroup.mul_mem _ ?_ hu, ?_⟩
      · have := Tg_conj_Up (Subgroup.inv_mem _ ht0) hv
        simpa using this
      · rw [pow_succ, hvj]
        group
  obtain ⟨v, hv, hvk⟩ := hpow (2 ^ k)
  rw [hk] at hvk
  have h1 : t0 ^ (2 ^ k) = v⁻¹ := eq_inv_of_mul_eq_one_left hvk.symm
  have h2 : (t0 ^ (2 ^ k)) ^ 2 = 1 := by
    rw [h1]
    exact Up_sq (Subgroup.inv_mem _ hv)
  rw [← pow_mul] at h2
  have h3 : orderOf t0 ∣ 2 ^ (k + 1) := by
    refine orderOf_dvd_of_pow_eq_one ?_
    rw [pow_succ]
    exact h2
  obtain ⟨i, hi, hio⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h3
  have hodd := Tg_odd_order ht0
  have hi0 : i = 0 := by
    rcases Nat.eq_zero_or_pos i with h | h
    · exact h
    · exfalso
      rw [hio] at hodd
      exact (Nat.not_odd_iff_even.2 ((Nat.even_pow' h.ne').2 even_two)) hodd
  rw [hi0, pow_zero] at hio
  exact orderOf_eq_one_iff.1 hio

theorem core_max (hgold : CFSG.Goldschmidt.TopStatement)
    [CharP K 2] [Finite K] {n : ℕ} (hn : 2 ≤ n) (hK : Nat.card K = 2 ^ n)
    (H : Subgroup (adjointGroup .G2 K)) (hL : Lp K ≤ H)
    (hOdd : ∀ R : Subgroup (adjointGroup .G2 K), R ≤ H →
      (∀ h ∈ H, ∀ r ∈ R, h * r * h⁻¹ ∈ R) → Odd (Nat.card R) → R = ⊥) :
    H = Lp K ∨ H = ⊤ := by
  by_cases htop : H = ⊤
  · exact Or.inr htop
  left
  have h4 : 4 ≤ Nat.card K := by rw [hK]; exact four_le_two_pow hn
  have hb3 : ∀ b : K, xp 3 b ∈ H → b = 0 := fun b hb => by
    by_contra hb0
    exact htop (eq_top_of_xp3 hL hb0 hb)
  have hNorm : ∀ y : adjointGroup .G2 K, y ∈ H → (∀ x ∈ Up K, y * x * y⁻¹ ∈ Up K) →
      ∃ t0 ∈ Tg K, ∃ u ∈ Up K, y = t0 * u := by
    intro y hyH hy
    obtain ⟨t0, ht0, a, b, c, rfl⟩ := normalizer_Up_form h4 hy
    have h3 : xp 3 b ∈ H := by
      have h1 : (xp 1 a)⁻¹ * (t0⁻¹ * (t0 * (xp 1 a * xp 3 b * xp 7 c))) * (xp 7 c)⁻¹ ∈ H :=
        H.mul_mem (H.mul_mem (H.inv_mem (hL (xp1_mem_Lp a)))
          (H.mul_mem (H.inv_mem (hL (Tg_le_Lp ht0))) hyH)) (H.inv_mem (hL (xp7_mem_Lp c)))
      rwa [show (xp 1 a)⁻¹ * (t0⁻¹ * (t0 * (xp 1 a * xp 3 b * xp 7 c))) * (xp 7 c)⁻¹ = xp 3 b by
        group] at h1
    have hb0 := hb3 b h3
    subst hb0
    refine ⟨t0, ht0, xp 7 c * xp 1 a, mem_Up_iff.2 ⟨c, a, rfl⟩, ?_⟩
    rw [xp_zero, mul_one, (commute_17 a c).eq]
  have hphi : ∀ x, phiP K x ∈ H := fun x => hL (by rw [← range_phiP]; exact ⟨x, rfl⟩)
  let φ : Matrix.SpecialLinearGroup (Fin 2) K × Matrix.SpecialLinearGroup (Fin 2) K →* H :=
    (phiP K).codRestrict H hphi
  have hφinj : Function.Injective φ := fun x y h => phiP_injective (congrArg Subtype.val h)
  have hφval : ∀ x, ((φ x : H) : adjointGroup .G2 K) = phiP K x := fun x => rfl
  let S0 : Subgroup H := (Up K).subgroupOf H
  have hS0eq : S0 = ((Uup K).prod (Uup K)).map φ := by
    ext ⟨g, hgH⟩
    constructor
    · intro hg
      have hg' : g ∈ Up K := hg
      rw [← map_Uup_eq] at hg'
      obtain ⟨x, hx, rfl⟩ := hg'
      exact ⟨x, hx, Subtype.ext rfl⟩
    · rintro ⟨x, hx, hxg⟩
      have h1 : g = phiP K x := (congrArg Subtype.val hxg).symm
      have h2 : g ∈ Up K := by
        rw [h1, ← map_Uup_eq]
        exact ⟨x, hx, rfl⟩
      exact h2
  have hS0p : IsPGroup 2 S0 := fun g =>
    ⟨1, Subtype.ext (Subtype.ext (by simpa using Up_sq g.2))⟩
  have hNS0 : ∀ y : H, y ∈ Subgroup.normalizer (S0 : Set H) →
      ∃ t0 ∈ Tg K, ∃ u ∈ Up K, (y : adjointGroup .G2 K) = t0 * u := by
    intro y hy
    refine hNorm y y.2 fun x hx => ?_
    have hxH : x ∈ H := hL (Up_le_Lp hx)
    have := (Subgroup.mem_normalizer_iff.1 hy) ⟨x, hxH⟩
    exact this.1 hx
  have hN2 : ∀ y : H, y ∈ Subgroup.normalizer (S0 : Set H) → (∃ k : ℕ, y ^ (2 ^ k) = 1) →
      y ∈ S0 := by
    intro y hy ⟨k, hk⟩
    obtain ⟨t0, ht0, u, hu, hyu⟩ := hNS0 y hy
    have h1 : (t0 * u) ^ (2 ^ k) = 1 := by
      rw [← hyu]
      exact congrArg Subtype.val hk
    have ht1 := two_elt_in_TgUp ht0 hu h1
    show (y : adjointGroup .G2 K) ∈ Up K
    rw [hyu, ht1, one_mul]
    exact hu
  let S : Sylow 2 H :=
    { toSubgroup := S0
      isPGroup' := hS0p
      is_maximal' := fun {Q} hQ hle => sylow_of_normalizer S0 hN2 hQ hle }
  have hNle : Subgroup.normalizer ((S : Subgroup H) : Set H) ≤ φ.range := by
    intro y hy
    obtain ⟨t0, ht0, u, hu, hyu⟩ := hNS0 y hy
    have hmem : (y : adjointGroup .G2 K) ∈ Lp K := by
      rw [hyu]
      exact mul_mem (Tg_le_Lp ht0) (Up_le_Lp hu)
    rw [← range_phiP] at hmem
    obtain ⟨x, hx⟩ := hmem
    exact ⟨x, Subtype.ext hx⟩
  have hX : Nat.card H ∣ g2Order n := by
    have h1 := Subgroup.card_subgroup_dvd_card H
    rw [card_adjointGroup_G2, hK] at h1
    exact h1
  have hOH : ∀ N : Subgroup H, N.Normal → Odd (Nat.card N) → N = ⊥ := by
    intro N hN hodd
    have hRle : N.map H.subtype ≤ H := fun x ⟨y, _, hy⟩ => hy ▸ y.2
    have hRn : ∀ h ∈ H, ∀ r ∈ N.map H.subtype, h * r * h⁻¹ ∈ N.map H.subtype := by
      rintro h hh r ⟨y, hy, rfl⟩
      exact ⟨⟨h, hh⟩ * y * ⟨h, hh⟩⁻¹, hN.conj_mem y hy _, rfl⟩
    have hcard : Nat.card (N.map H.subtype) = Nat.card N :=
      Nat.card_congr (N.equivMapOfInjective H.subtype H.subtype_injective).toEquiv.symm
    have := hOdd _ hRle hRn (hcard ▸ hodd)
    exact (Subgroup.map_eq_bot_iff_of_injective _ H.subtype_injective).1 this
  have hsurj := goldschmidt_finish hgold hn hK φ hφinj S hS0eq hNle hOH hX
  apply le_antisymm
  · intro h hh
    obtain ⟨x, hx⟩ := hsurj ⟨h, hh⟩
    rw [← range_phiP]
    exact ⟨x, congrArg Subtype.val hx⟩
  · exact hL

end CFSG.RankThree.PartOne.SEITZ6
