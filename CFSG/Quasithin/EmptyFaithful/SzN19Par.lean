module

public import CFSG.Quasithin.EmptyFaithful.SzN19Swap
public import CFSG.Quasithin.Background.B6Defs

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique
open scoped commutatorElement

namespace SzN19

section Par

variable {Ω : Type*} [Group Ω] [Finite Ω]

omit [Finite Ω] in
theorem isSylowTwoOf_inf_of_normalizes {H N S : Subgroup Ω} (hS : IsSylowTwoOf S H) (hNH : N ≤ H)
    (hSN : S ≤ Subgroup.normalizer (N : Set Ω)) (hHNS : H ≤ N ⊔ S) : IsSylowTwoOf (S ⊓ N) N := by
  have hprod : ∀ h ∈ H, ∃ n ∈ N, ∃ s ∈ S, h = n * s := fun h hh =>
    exists_mul_of_normalizes hSN (hHNS hh)
  refine ⟨inf_le_right, hS.2.1.to_le inf_le_left, ?_⟩
  have key : ((S ⊓ N).subgroupOf N).index = (S.subgroupOf H).index := by
    unfold Subgroup.index
    let f : N ⧸ (S ⊓ N).subgroupOf N → H ⧸ S.subgroupOf H :=
      Quotient.map' (fun n : N => (⟨n, hNH n.2⟩ : H)) (by
        intro a b hab
        have h1 : a⁻¹ * b ∈ (S ⊓ N).subgroupOf N := QuotientGroup.leftRel_apply.mp hab
        rw [QuotientGroup.leftRel_apply]
        exact (Subgroup.mem_subgroupOf.mpr (Subgroup.mem_subgroupOf.mp h1).1))
    have hf : Function.Bijective f := by
      constructor
      · intro a b
        induction a using Quotient.inductionOn' with | _ a => ?_
        induction b using Quotient.inductionOn' with | _ b => ?_
        intro hab
        have h1 : (⟨(a : Ω), hNH a.2⟩ : H)⁻¹ * ⟨(b : Ω), hNH b.2⟩ ∈ S.subgroupOf H :=
          QuotientGroup.leftRel_apply.mp (Quotient.exact' hab)
        apply Quotient.sound'
        rw [QuotientGroup.leftRel_apply]
        refine Subgroup.mem_subgroupOf.mpr ⟨Subgroup.mem_subgroupOf.mp h1, ?_⟩
        exact N.mul_mem (N.inv_mem a.2) b.2
      · intro q
        induction q using Quotient.inductionOn' with | _ h => ?_
        obtain ⟨n, hn, s, hs, hh⟩ := hprod h h.2
        refine ⟨Quotient.mk'' ⟨n, hn⟩, ?_⟩
        show Quotient.mk'' (⟨n, hNH hn⟩ : H) = Quotient.mk'' h
        apply Quotient.sound'
        rw [QuotientGroup.leftRel_apply]
        refine Subgroup.mem_subgroupOf.mpr ?_
        have : ((⟨n, hNH hn⟩ : H)⁻¹ * h : H) = ⟨s, hS.1 hs⟩ := by
          apply Subtype.ext
          show n⁻¹ * (h : Ω) = s
          rw [hh]; group
        show ((⟨n, hNH hn⟩ : H)⁻¹ * h : H).1 ∈ S
        rw [this]; exact hs
    exact (Nat.card_congr (Equiv.ofBijective f hf))
  rw [key]; exact hS.2.2

theorem between_prime_index {B M P : Subgroup Ω} (hBM : B ≤ M) (hMP : M ≤ P)
    (hcard : Nat.card ↥P = 3 * Nat.card ↥B) : M = B ∨ M = P := by
  have hBP : B ≤ P := hBM.trans hMP
  have hrel : B.relIndex P = 3 := by
    have h1 := Subgroup.relIndex_mul_card B P
    rw [inf_eq_left.mpr hBP] at h1
    have hpos : 0 < Nat.card ↥B := Nat.card_pos
    have h2 : B.relIndex P * Nat.card ↥B = 3 * Nat.card ↥B := by rw [h1, hcard]
    exact Nat.eq_of_mul_eq_mul_right hpos h2
  have h1 := Subgroup.relIndex_mul_relIndex B M P hBM hMP
  rw [hrel] at h1
  have hd : B.relIndex M ∣ 3 := ⟨M.relIndex P, h1.symm⟩
  rcases (Nat.dvd_prime Nat.prime_three).mp hd with h2 | h2
  · left
    exact le_antisymm (Subgroup.relIndex_eq_one.mp h2) hBM
  · right
    rw [h2] at h1
    have h3 : M.relIndex P = 1 := by omega
    exact le_antisymm hMP (Subgroup.relIndex_eq_one.mp h3)

theorem odd_mul_two_pow_eq {r e m : ℕ} (hr : Odd r) (h : r * 2 ^ e = 3 * 2 ^ m) :
    r = 3 ∧ e = m := by
  have h3 : Nat.Coprime (2 ^ e) 3 := Nat.Coprime.pow_left e (by norm_num)
  have hr' : Nat.Coprime (2 ^ m) r := Nat.Coprime.pow_left m hr.coprime_two_right.symm
  have h1 : 2 ^ e ∣ 2 ^ m := h3.dvd_of_dvd_mul_left ⟨r, by rw [← h]; ring⟩
  have h2 : 2 ^ m ∣ 2 ^ e := hr'.dvd_of_dvd_mul_left ⟨3, by rw [h]; ring⟩
  have hem : e = m :=
    le_antisymm ((Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp h1)
      ((Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp h2)
  subst hem
  exact ⟨Nat.eq_of_mul_eq_mul_right (pow_pos (by norm_num) _) h, rfl⟩

theorem card_eq_two_pow_mul_three {Y : Subgroup Ω}
    (hord : ∀ y ∈ Y, ∃ k : ℕ, y ^ (2 ^ k * 3) = 1) (hex : ∃ y ∈ Y, orderOf y = 3)
    (hY3 : ∀ E : Subgroup Ω, E ≤ Y → IsPGroup 3 E → Nat.card E ≤ 3) :
    ∃ a : ℕ, Nat.card ↥Y = 2 ^ a * 3 := by
  classical
  have hF3 : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hn0 : Nat.card ↥Y ≠ 0 := Nat.card_pos.ne'
  obtain ⟨a, m, hmodd, hnm⟩ := Nat.exists_eq_two_pow_mul_odd hn0
  have hprime : ∀ {p : ℕ}, p.Prime → p ∣ Nat.card ↥Y → p = 2 ∨ p = 3 := by
    intro p hp hpd
    have : Fact p.Prime := ⟨hp⟩
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p hpd
    obtain ⟨k, hk⟩ := hord (x : Ω) x.2
    have hxk : x ^ (2 ^ k * 3) = 1 := Subtype.ext (by simpa using hk)
    have hdvd : p ∣ 2 ^ k * 3 := hx ▸ orderOf_dvd_of_pow_eq_one hxk
    rcases (Nat.Prime.dvd_mul hp).mp hdvd with h2 | h3
    · left
      exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h2)
    · right
      exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h3
  have hm0 : m ≠ 0 := by
    rintro rfl
    simp at hnm
    exact hn0 hnm
  have hm3 : m = 3 ^ m.primeFactorsList.length := by
    refine Nat.eq_prime_pow_of_unique_prime_dvd hm0 fun {d} hd hdm => ?_
    have hdn : d ∣ Nat.card ↥Y := hnm ▸ Dvd.dvd.mul_left hdm _
    rcases hprime hd hdn with h2 | h3
    · exfalso
      subst h2
      exact (Nat.not_even_iff_odd.mpr hmodd) (even_iff_two_dvd.mpr hdm)
    · exact h3
  set b := m.primeFactorsList.length with hb
  obtain ⟨y, hyY, hy3⟩ := hex
  have h3dvd : 3 ∣ Nat.card ↥Y := by
    have := orderOf_dvd_natCard (⟨y, hyY⟩ : ↥Y)
    rwa [Subgroup.orderOf_mk, hy3] at this
  have hb1 : 1 ≤ b := by
    by_contra hb0
    have hb0' : b = 0 := by omega
    rw [hb0', pow_zero] at hm3
    rw [hm3, mul_one] at hnm
    have h32 : 3 ∣ 2 ^ a := hnm ▸ h3dvd
    exact absurd ((Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
      (Nat.prime_three.dvd_of_dvd_pow h32)) (by norm_num)
  have hb2 : b ≤ 1 := by
    by_contra hb2
    have hb2' : 2 ≤ b := by omega
    have h9 : 9 ∣ Nat.card ↥Y := by
      rw [hnm, hm3]
      exact Dvd.dvd.mul_left (pow_dvd_pow 3 hb2' : 3 ^ 2 ∣ 3 ^ b) _
    obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime (G := ↥Y) 3 (n := 2) (by simpa using h9)
    have hKp : IsPGroup 3 ↥K := IsPGroup.of_card (n := 2) (by simpa using hK)
    have hmap : IsPGroup 3 ↥(K.map Y.subtype) :=
      hKp.of_equiv (Subgroup.equivMapOfInjective K _ Y.subtype_injective)
    have hle : K.map Y.subtype ≤ Y := fun x ⟨y, _, hy⟩ => hy ▸ y.2
    have h3 := hY3 _ hle hmap
    rw [Subgroup.card_map_of_injective Y.subtype_injective, hK] at h3
    norm_num at h3
  have hb' : b = 1 := le_antisymm hb2 hb1
  exact ⟨a, by rw [hnm, hm3, hb', pow_one]⟩

theorem card_sup_eq_three_mul {X Y S : Subgroup Ω} (hS : IsSylowTwoOf S X) (hYX : Y ≤ X)
    (hSY : S ≤ Subgroup.normalizer (Y : Set Ω))
    (hord : ∀ y ∈ Y, ∃ k : ℕ, y ^ (2 ^ k * 3) = 1) (hex : ∃ y ∈ Y, orderOf y = 3)
    (hY3 : ∀ E : Subgroup Ω, E ≤ Y → IsPGroup 3 E → Nat.card E ≤ 3) :
    Nat.card ↥(Y ⊔ S) = 3 * Nat.card ↥S := by
  classical
  obtain ⟨a, ha⟩ := card_eq_two_pow_mul_three hord hex hY3
  set P : Subgroup Ω := Y ⊔ S with hP
  have hSP : S ≤ P := le_sup_right
  have hYP : Y ≤ P := le_sup_left
  have hPX : P ≤ X := sup_le hYX hS.1
  have hnorm : (Y.subgroupOf P).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hYP).mpr
      (sup_le Subgroup.le_normalizer hSY)
  have hsurj : Function.Surjective
      ((QuotientGroup.mk' (Y.subgroupOf P)).comp (Subgroup.inclusion hSP)) := by
    intro z
    induction z using QuotientGroup.induction_on with
    | H x =>
      obtain ⟨y, hy, s, hs, hx⟩ := exists_mul_of_normalizes hSY x.2
      refine ⟨⟨s, hs⟩, ?_⟩
      show (QuotientGroup.mk (⟨s, hSP hs⟩ : ↥P) : ↥P ⧸ Y.subgroupOf P) = QuotientGroup.mk x
      rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
      have e : (((⟨s, hSP hs⟩ : ↥P)⁻¹ * x : ↥P) : Ω) = s⁻¹ * y * s := by
        simp [hx, mul_assoc]
      rw [e]
      have := (Subgroup.mem_normalizer_iff.mp (hSY (S.inv_mem hs)) y).mp hy
      simpa using this
  have hquot : IsPGroup 2 (↥P ⧸ Y.subgroupOf P) := hS.2.1.of_surjective _ hsurj
  obtain ⟨c, hc⟩ := hquot.exists_card_eq
  have hP1 : Nat.card ↥P = Nat.card (↥P ⧸ Y.subgroupOf P) * Nat.card ↥(Y.subgroupOf P) :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup _
  have hYP' : Nat.card ↥(Y.subgroupOf P) = Nat.card ↥Y :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hYP).toEquiv
  have hcardP : Nat.card ↥P = 2 ^ c * (2 ^ a * 3) := by rw [hP1, hc, hYP', ha]
  have hrel : ¬ 2 ∣ S.relIndex P := by
    have h1 := Subgroup.relIndex_mul_relIndex S P X hSP hPX
    have h2 : S.relIndex P ∣ S.relIndex X := ⟨P.relIndex X, h1.symm⟩
    exact fun h => hS.2.2 (h.trans h2)
  have hodd : Odd (S.relIndex P) := Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp hrel)
  have hmul := Subgroup.relIndex_mul_card S P
  rw [inf_eq_left.mpr hSP] at hmul
  obtain ⟨e, he⟩ := hS.2.1.exists_card_eq
  have hmain : S.relIndex P * 2 ^ e = 3 * 2 ^ (a + c) := by
    rw [← he, hmul, hcardP]
    ring
  obtain ⟨hr3, -⟩ := odd_mul_two_pow_eq hodd hmain
  rw [← hmul, hr3]

theorem isMinParabolicOf_of_selfNormalizing {X Y S : Subgroup Ω} (hS : IsSylowTwoOf S X)
    (hYX : Y ≤ X) (hSY : S ≤ Subgroup.normalizer (Y : Set Ω))
    (hord : ∀ y ∈ Y, ∃ k : ℕ, y ^ (2 ^ k * 3) = 1) (hex : ∃ y ∈ Y, orderOf y = 3)
    (hY3 : ∀ E : Subgroup Ω, E ≤ Y → IsPGroup 3 E → Nat.card E ≤ 3)
    (hselfN : Subgroup.normalizer (S : Set Ω) ⊓ X ≤ S) : IsMinParabolicOf X (Y ⊔ S) := by
  obtain ⟨y, hyY, hy3⟩ := hex
  have hcard := card_sup_eq_three_mul hS hYX hSY hord ⟨y, hyY, hy3⟩ hY3
  have hyS : y ∉ S := by
    intro hyS
    obtain ⟨k, hk⟩ := hS.2.1 ⟨y, hyS⟩
    have hpow : y ^ 2 ^ k = 1 := congrArg Subtype.val hk
    have hdvd : 3 ∣ 2 ^ k := hy3 ▸ orderOf_dvd_of_pow_eq_one hpow
    have : 3 ∣ 2 := Nat.Prime.dvd_of_dvd_pow Nat.prime_three hdvd
    omega
  have hlt : S < Y ⊔ S :=
    lt_of_le_of_ne le_sup_right fun h => hyS (h ▸ Subgroup.mem_sup_left hyY)
  refine ⟨S, hS, ⟨⟨sup_le hYX hS.1, hlt, ?_⟩, ?_⟩⟩
  · rw [Set.ncard_eq_one]
    refine ⟨S, ?_⟩
    ext N
    simp only [maxOver, Set.mem_ofPred_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨⟨hNlt, hNmax⟩, hSN⟩
      rcases between_prime_index hSN hNlt.le hcard with h | h
      · exact h
      · exact absurd h hNlt.ne
    · rintro rfl
      refine ⟨⟨hlt, fun K hSK hKP => ?_⟩, le_rfl⟩
      rcases between_prime_index hSK.le hKP hcard with h | h
      · exact absurd h hSK.ne'
      · exact h
  · intro hPn
    have hyN : y ∈ Subgroup.normalizer (S : Set Ω) := hPn (Subgroup.mem_sup_left hyY)
    exact hyS (hselfN ⟨hyN, hYX hyY⟩)

end Par

end SzN19

end CFSG.Quasithin
