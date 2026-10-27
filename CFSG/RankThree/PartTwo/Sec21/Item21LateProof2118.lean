module

public import CFSG.RankThree.PartTwo.Sec21.Item21LateProofIdent
public import CFSG.RankThree.PartTwo.Sec21.Item21LateProofGL33
import CFSG.RankThree.PartTwo.Sec6.Item612Local

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly (IsElemAbelian)

@[expose] def Item2118Frame : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A E U : Subgroup G) (c : G) (L : Subgroup G),
    Sec21Pair G A E U c L → (∃ n : ℕ, 0 < n ∧ Even n ∧ Nonempty (lBar L ≃* SL3 n)) →
    IsTypeCOnBarSL A L → Nat.card A = 3 ^ 3 → Nonempty (starOf A L ≃* Equiv.Perm (Fin 3)) →
      c ∈ L ∧ Nat.card (A ⊓ L : Subgroup G) = 9 ∧
        ∃ w ∈ L ⊓ Subgroup.normalizer (A : Set G), (∀ a ∈ A, w ^ 3 * a * (w ^ 3)⁻¹ = a) ∧
          (∃ b ∈ A ⊓ L, w * b * w⁻¹ ≠ b) ∧ ∃ a ∈ A, a⁻¹ * (w * a * w⁻¹) ∉ Subgroup.zpowers c

@[expose] def Item2118TypeTwo : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A E U : Subgroup G) (c : G) (L : Subgroup G),
    Sec21Pair G A E U c L → (∃ n : ℕ, 0 < n ∧ Even n ∧ Nonempty (lBar L ≃* SL3 n)) →
    IsTypeCOnBarSL A L → Nat.card A = 3 ^ 3 → Nonempty (starOf A L ≃* Equiv.Perm (Fin 3)) →
      c ∈ L → Nat.card (A ⊓ L : Subgroup G) = 9 → ∀ e ∈ A, e ∉ L →
        ∀ x ∈ Subgroup.normalizer (A : Set G),
          IsPGroup 3 (Subgroup.zpowers x) → x * c * x⁻¹ = c → x * e * x⁻¹ = e →
            ∀ b ∈ A ⊓ L, x * b * x⁻¹ = b

namespace Item21LateProof

variable {G : Type} [Group G]

theorem eq_of_conj_invariant [Finite G] {A B : Subgroup G}
    (hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) (h3 : ∀ x ∈ A, x ^ 3 = 1)
    (hA : Nat.card A = 27) (hBA : B ≤ A) (hB : Nat.card B = 9) {c : G} (hcB : c ∈ B)
    (hc1 : c ≠ 1) {w : G} (hwA : ∀ a ∈ A, w * a * w⁻¹ ∈ A) (hwB : ∀ y ∈ B, w * y * w⁻¹ ∈ B)
    (hw3 : ∀ a ∈ A, w ^ 3 * a * (w ^ 3)⁻¹ = a) (hwc : w * c * w⁻¹ = c)
    (hwb : ∃ b ∈ B, w * b * w⁻¹ ≠ b) (hwa : ∃ a ∈ A, a⁻¹ * (w * a * w⁻¹) ∉ Subgroup.zpowers c) :
    (∀ a ∈ A, w * a * w⁻¹ = a → a ∈ Subgroup.zpowers c) ∧
      ∀ X : Subgroup G, X ≤ A → (∀ x ∈ X, w * x * w⁻¹ ∈ X) →
        X = ⊥ ∨ X = Subgroup.zpowers c ∨ X = B ∨ X = A := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hBc : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x := fun x hx y hy => hcomm x (hBA hx) y (hBA hy)
  have hB3 : ∀ x ∈ B, x ^ 3 = 1 := fun x hx => h3 x (hBA hx)
  have hc3 : c ^ 3 = 1 := hB3 c hcB
  have hZc : Nat.card (Subgroup.zpowers c) = 3 := by
    rw [Nat.card_zpowers, orderOf_eq_prime hc3 hc1]
  have hZcB : Subgroup.zpowers c ≤ B := Subgroup.zpowers_le.mpr hcB
  have hAB : Nat.card A = 3 * Nat.card B := by rw [hA, hB]
  have hwBc : ∀ y ∈ B, y⁻¹ * (w * y * w⁻¹) ∈ Subgroup.zpowers c :=
    inv_mul_conj_mem_of_pow_three hBc hB3 hZcB (by rw [hB, hZc]) hwB
      (fun y hy => by rw [conj_eq_of_mem_zpowers hwc hy]; exact hy)
      (fun y hy => hw3 y (hBA hy))
  have hwAB : ∀ a ∈ A, a⁻¹ * (w * a * w⁻¹) ∈ B :=
    inv_mul_conj_mem_of_pow_three hcomm h3 hBA hAB hwA hwB hw3
  have hconj : ∀ g x y : G, g * (x * y) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) := fun g x y => by
    group
  have hconjpow : ∀ (g x : G) (k : ℕ), g * x ^ k * g⁻¹ = (g * x * g⁻¹) ^ k := fun g x k => by
    rw [← MulAut.conj_apply, map_pow, MulAut.conj_apply]
  have htriv : ∀ h₀ ∈ A, h₀ ∉ B → h₀⁻¹ * (w * h₀ * w⁻¹) ∈ Subgroup.zpowers c → False := by
    intro h₀ h₀A h₀B hh₀
    obtain ⟨a, haA, ha⟩ := hwa
    apply ha
    obtain ⟨k, -, y, hyB, rfl⟩ := exists_pow_mul_of_card hcomm h3 hBA hAB h₀A h₀B a haA
    have hyA : y ∈ A := hBA hyB
    set d := h₀⁻¹ * (w * h₀ * w⁻¹) with hd
    have hdA : d ∈ A := A.mul_mem (A.inv_mem h₀A) (hwA h₀ h₀A)
    have hwh : w * h₀ * w⁻¹ = h₀ * d := by rw [hd, mul_inv_cancel_left]
    rw [hconj, hconjpow, hwh, Commute.mul_pow (hcomm h₀ h₀A d hdA)]
    have hyd : y⁻¹ * d ^ k = d ^ k * y⁻¹ := hcomm _ (A.inv_mem hyA) _ (A.pow_mem hdA k)
    have e1 : (h₀ ^ k * y)⁻¹ * (h₀ ^ k * d ^ k * (w * y * w⁻¹)) =
        d ^ k * (y⁻¹ * (w * y * w⁻¹)) := by
      have e2 : (h₀ ^ k * y)⁻¹ * (h₀ ^ k * d ^ k * (w * y * w⁻¹)) =
          y⁻¹ * d ^ k * (w * y * w⁻¹) := by group
      rw [e2, hyd, mul_assoc]
    rw [e1]
    exact (Subgroup.zpowers c).mul_mem ((Subgroup.zpowers c).pow_mem hh₀ k) (hwBc y hyB)
  have hfix : ∀ a ∈ A, w * a * w⁻¹ = a → a ∈ Subgroup.zpowers c := by
    intro a haA hwa'
    by_contra hac
    by_cases haB : a ∈ B
    · obtain ⟨b, hbB, hwb'⟩ := hwb
      apply hwb'
      obtain ⟨k, -, z, hz, rfl⟩ :=
        exists_pow_mul_of_card hBc hB3 hZcB (by rw [hB, hZc]) haB hac b hbB
      rw [hconj, hconjpow, hwa', conj_eq_of_mem_zpowers hwc hz]
    · exact htriv a haA haB (by rw [hwa', inv_mul_cancel]; exact Subgroup.one_mem _)
  refine ⟨hfix, fun X hXA hX => ?_⟩
  have hthree : ∀ Y : Subgroup G, Y ≤ A → (∀ y ∈ Y, w * y * w⁻¹ ∈ Y) → Nat.card Y = 3 →
      Y = Subgroup.zpowers c := by
    intro Y hYA hY hY3
    have hYc : ∀ x ∈ Y, ∀ y ∈ Y, x * y = y * x := fun x hx y hy => hcomm x (hYA hx) y (hYA hy)
    have hY3' : ∀ x ∈ Y, x ^ 3 = 1 := fun x hx => h3 x (hYA hx)
    have hfixY : ∀ y ∈ Y, y⁻¹ * (w * y * w⁻¹) ∈ (⊥ : Subgroup G) :=
      inv_mul_conj_mem_of_pow_three hYc hY3' bot_le (by rw [hY3, Subgroup.card_bot])
        hY (fun y hy => by rw [Subgroup.mem_bot] at hy ⊢; rw [hy]; group)
        (fun y hy => hw3 y (hYA hy))
    have hle : Y ≤ Subgroup.zpowers c := by
      intro y hy
      have h1 := hfixY y hy
      rw [Subgroup.mem_bot, inv_mul_eq_one] at h1
      exact hfix y (hYA hy) h1.symm
    exact Subgroup.eq_of_le_of_card_ge hle (by rw [hZc, hY3])
  have hdvd : Nat.card X ∣ 3 ^ 3 := by
    rw [show (3 : ℕ) ^ 3 = 27 by norm_num, ← hA]
    exact Subgroup.card_dvd_of_le hXA
  obtain ⟨k, hk3, hkX⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
  interval_cases k
  · left
    exact Subgroup.eq_bot_of_card_eq X (by rw [hkX, pow_zero])
  · right; left
    exact hthree X hXA hX (by rw [hkX, pow_one])
  ·
    right; right; left
    by_contra hXB
    have hXc : ∀ x ∈ X, ∀ y ∈ B, x * y = y * x := fun x hx y hy => hcomm x (hXA hx) y (hBA hy)
    obtain ⟨hcd, -⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute X B hXc
    have hsup : Nat.card (X ⊔ B : Subgroup G) ≤ 27 := hA ▸ Subgroup.card_le_of_le (sup_le hXA hBA)
    have hinf : Nat.card (X ⊓ B : Subgroup G) ∣ 9 := hB ▸ Subgroup.card_dvd_of_le inf_le_right
    have hinf9 : Nat.card (X ⊓ B : Subgroup G) ≠ 9 := by
      intro h
      apply hXB
      have h1 : X ⊓ B = X := Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h, hkX]; norm_num)
      have h2 : X ⊓ B = B := Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [h, hB])
      rw [← h1, h2]
    rw [hkX, hB] at hcd
    have hpos : 0 < Nat.card (X ⊔ B : Subgroup G) := Nat.card_pos
    have hinf3 : Nat.card (X ⊓ B : Subgroup G) = 3 := by
      rcases (Nat.dvd_prime_pow Nat.prime_three).mp
        (show Nat.card (X ⊓ B : Subgroup G) ∣ 3 ^ 2 by simpa using hinf) with ⟨j, hj, hj'⟩
      interval_cases j
      · rw [pow_zero] at hj'
        rw [hj'] at hcd
        omega
      · rw [pow_one] at hj'
        exact hj'
      · exact absurd (by rw [hj']; norm_num) hinf9
    have hXBc : X ⊓ B = Subgroup.zpowers c :=
      hthree (X ⊓ B) (inf_le_left.trans hXA) (fun y hy => ⟨hX y hy.1, hwB y hy.2⟩) hinf3
    obtain ⟨h₀, h₀X, h₀B⟩ : ∃ h₀ ∈ X, h₀ ∉ B := by
      by_contra hno
      push Not at hno
      apply hXB
      exact Subgroup.eq_of_le_of_card_ge (fun x hx => hno x hx) (by rw [hB, hkX]; norm_num)
    apply htriv h₀ (hXA h₀X) h₀B
    rw [← hXBc]
    exact ⟨X.mul_mem (X.inv_mem h₀X) (hX h₀ h₀X), hwAB h₀ (hXA h₀X)⟩
  · right; right; right
    exact Subgroup.eq_of_le_of_card_ge hXA (by rw [hkX, hA]; norm_num)

end Item21LateProof

open Item21LateProof

theorem item2118_of
    (h211 : Item211) (h2115 : Item2115) (hF : Item2118Frame)
    (hT : Item2118TypeTwo) : Item2118 := by
  intro G _ _ A E U c L hpair ⟨n, ⟨eL⟩⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hn, he, hC, h27, hS3⟩ := case7_of_lBar_SL3 h211 hpair eL
  have hn' : ∃ n : ℕ, 0 < n ∧ Even n ∧ Nonempty (lBar L ≃* SL3 n) := ⟨n, hn, he, ⟨eL⟩⟩
  obtain ⟨hcL, hB9, w, ⟨hwL, hwN⟩, hw3, hwb, hwa⟩ := hF G A E U c L hpair hn' hC h27 hS3
  have hTT := hT G A E U c L hpair hn' hC h27 hS3 hcL hB9
  have hpairs := mem_lThreeStarPairs_iff.mp hpair.mem_pair
  have hAe : IsElemAbelian 3 A := hpair.mem_S.1.1
  have hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hAe.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have h3 : ∀ x ∈ A, x ^ 3 = 1 := hAe.2
  have hA27 : Nat.card A = 27 := by rw [h27]; norm_num
  have hcA : c ∈ A := hpair.mem_E.2 hpairs.1.1
  have hc1 : c ≠ 1 := hpairs.2.1
  have hLc : L ∈ thetaComponentsAt 3 c := lZeroStarAt_subset A c hpairs.2.2.1
  have hLC : L ≤ Subgroup.centralizer ({c} : Set G) :=
    Sec6.le_centralizer_of_mem_thetaComponentsAt hLc
  have hwc : w * c * w⁻¹ = c := by
    rw [(Subgroup.mem_centralizer_singleton_iff.mp (hLC hwL)), mul_inv_cancel_right]
  set B := A ⊓ L with hBdef
  have hcB : c ∈ B := ⟨hcA, hcL⟩
  have nA : ∀ {g : G}, g ∈ Subgroup.normalizer (A : Set G) → ∀ a ∈ A, g * a * g⁻¹ ∈ A :=
    fun hg a ha => (Subgroup.mem_normalizer_iff.mp hg a).mp ha
  have hwB : ∀ y ∈ B, w * y * w⁻¹ ∈ B := fun y hy =>
    ⟨nA hwN y hy.1, L.mul_mem (L.mul_mem hwL hy.2) (L.inv_mem hwL)⟩
  obtain ⟨hfix, hinv⟩ := eq_of_conj_invariant hcomm h3 hA27 inf_le_left hB9 hcB hc1 (nA hwN)
    hwB hw3 hwc hwb hwa
  obtain ⟨s, hsN, hsc⟩ :
      ∃ s ∈ Subgroup.normalizer (A : Set G), s * c * s⁻¹ ∉ Subgroup.zpowers c := by
    by_contra hno
    push Not at hno
    apply h2115 G A E U c L hpair
    intro g hg
    refine Subgroup.mem_normalizer_fintype fun z hz => ?_
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    rw [← MulAut.conj_apply, map_zpow, MulAut.conj_apply]
    exact (Subgroup.zpowers c).zpow_mem (hno g hg) k
  intro X hX
  set X' := X.map A.subtype with hX'
  have hX'A : X' ≤ A := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  have hX'N : ∀ g ∈ Subgroup.normalizer (A : Set G), ∀ x ∈ X', g * x * g⁻¹ ∈ X' := by
    rintro g hg _ ⟨x, hx, rfl⟩
    have h1 := hX (A.normalizerMonoidHom ⟨g, hg⟩) ⟨⟨g, hg⟩, rfl⟩
    have h2 : A.normalizerMonoidHom ⟨g, hg⟩ x ∈ X := by
      rw [← h1]
      exact ⟨x, hx, rfl⟩
    exact ⟨_, h2, rfl⟩
  have hX'eq : X = X'.subgroupOf A := by
    ext x
    constructor
    · intro hx
      exact ⟨x, hx, rfl⟩
    · rintro ⟨y, hy, hyx⟩
      rwa [show y = x from Subtype.ext hyx] at hy
  rcases hinv X' hX'A (hX'N w hwN) with h | h | h | h
  ·
    left
    rw [hX'eq, h, Subgroup.bot_subgroupOf]
  ·
    exfalso
    apply hsc
    rw [← h]
    exact hX'N s hsN c (h ▸ Subgroup.mem_zpowers c)
  ·
    exfalso
    have hBN : ∀ {g : G}, g ∈ Subgroup.normalizer (A : Set G) →
        g ∈ Subgroup.normalizer (B : Set G) := fun hg =>
      Subgroup.mem_normalizer_fintype fun y hy => by
        have h1 := hX'N _ hg y (by rw [h]; exact hy)
        rwa [h] at h1
    obtain ⟨x, hxS, hxc, hxt, y, hyB, hxy⟩ :=
      exists_transvection_of_conj hcomm h3 hA27 inf_le_left hB9 hcB hc1 hwN hsN (hBN hwN)
        (hBN hsN) hw3 hwc hfix hsc
    have hxN : x ∈ Subgroup.normalizer (A : Set G) := by
      refine (Subgroup.closure_le _).mpr ?_ hxS
      rintro g (rfl | rfl)
      · exact hwN
      · exact hsN
    obtain ⟨m, -, hP, hmc, hmy, e, heA, heB, hme⟩ :=
      exists_pPow_transvection hcomm h3 inf_le_left (by rw [hA27, hB9]) hcB hxN hxc hxt hyB hxy
    have heL : e ∉ L := fun heL => heB ⟨heA, heL⟩
    exact hmy (hTT e heA heL (x ^ m) (Subgroup.pow_mem _ hxN m) hP hmc hme y hyB)
  ·
    right
    rw [hX'eq, h, Subgroup.subgroupOf_self]

end CFSG.RankThree.PartTwo.Sec21
