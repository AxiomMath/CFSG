module

public import CFSG.RankThree.PartTwo.Sec21.FF79Vocab

import CFSG.Goldschmidt.Steps.G310Basic
import CFSG.GroupTheory.ElementaryAbelianTransport
import CFSG.RankThree.PartTwo.Sec21.FF79Lemma13bSyl

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF79

open CFSG CFSG.RankThree.PartTwo.Sec21
open CFSG.Assembly.RankThreeEven (localRank)

theorem exists_normal_complement_of_central {H : Type} [Group H] [Finite H] (P : Sylow 3 H)
    (hP : Subgroup.normalizer (P : Set H) ≤ Subgroup.centralizer (P : Set H)) :
    ∃ X : Subgroup H, X.Normal ∧ Nat.card H = Nat.card X * Nat.card P ∧ ¬ 3 ∣ Nat.card X ∧
      ∀ h : H, Nat.Coprime (orderOf h) 3 → h ∈ X := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hc := MonoidHom.ker_transferSylow_isComplement' P hP
  refine ⟨(MonoidHom.transferSylow P hP).ker, inferInstance, ?_,
    MonoidHom.not_dvd_card_ker_transferSylow P hP, ?_⟩
  · rw [← hc.card_mul]
  · intro h hh
    set f := MonoidHom.transferSylow P hP
    have h1 : orderOf (f h) ∣ orderOf h := orderOf_map_dvd f h
    have h2 : orderOf (f h) ∣ Nat.card P := orderOf_dvd_natCard (f h)
    obtain ⟨n, hn⟩ := P.isPGroup'.exists_card_eq
    have h3 : Nat.Coprime (orderOf (f h)) (3 ^ n) :=
      Nat.Coprime.pow_right n (Nat.Coprime.coprime_dvd_left h1 hh)
    rw [hn] at h2
    have h4 : orderOf (f h) = 1 := Nat.Coprime.eq_one_of_dvd h3 h2
    exact MonoidHom.mem_ker.mpr (orderOf_eq_one_iff.mp h4)


theorem pRank_three_le_card {G : Type} [Group G] [Finite G] (H : Subgroup G) :
    CFSG.Open.pRank 3 H ≤ Nat.card G := by
  unfold CFSG.Open.pRank
  refine csSup_le ⟨0, ⊥, bot_le, CFSG.Open.isElemAbelian_bot 3, by simp⟩ ?_
  rintro k ⟨E, -, -, hk⟩
  have h1 : k < 3 ^ k := Nat.lt_pow_self (by norm_num)
  have h2 : Nat.card E ≤ Nat.card G := Subgroup.card_le_card_group E
  omega

theorem four_le_localRank {G : Type} [Group G] [Finite G] {S A : Subgroup G} (hS : S ≠ ⊥)
    (hS2 : IsPGroup 2 S) (hA : IsElemAb 3 4 A) (hAS : A ≤ Subgroup.normalizer (S : Set G)) :
    4 ≤ localRank 3 G := by
  have h1 : 4 ≤ CFSG.Open.pRank 3 (Subgroup.normalizer (S : Set G)) := by
    unfold CFSG.Open.pRank
    refine le_csSup ⟨Nat.card G, ?_⟩ ⟨A, hAS, ?_, hA.2⟩
    · rintro k ⟨E, -, -, hk⟩
      have h1 : k < 3 ^ k := Nat.lt_pow_self (by norm_num)
      have h2 : Nat.card E ≤ Nat.card G := Subgroup.card_le_card_group E
      omega
    · exact CFSG.Open.isElemAbelian_iff_isElementaryAbelian.mpr hA.1
  unfold localRank CFSG.Open.twoLocalPrimeRank
  refine h1.trans (le_csSup ⟨Nat.card G, ?_⟩ ⟨_, ⟨S, hS, hS2, rfl⟩, rfl⟩)
  rintro k ⟨H, -, rfl⟩
  exact pRank_three_le_card H


open L13b in
theorem odd_card_cenS_of_rank {G : Type} [Group G] [Finite G] {b : G} {B A : Subgroup G}
    (hB : IsSylowOf 3 B (Cen b)) (hbB : b ∈ B) (hab : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x)
    (hA : IsElemAb 3 4 A) (hAB : A ≤ Nor B) (hr : localRank 3 G ≤ 3) :
    Odd (Nat.card (CenS B)) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set H : Subgroup G := CenS B with hH
  have hBH : B ≤ H := fun x hx => Subgroup.mem_centralizer_iff.mpr fun y hy => (hab y hy x hx)
  have hHb : H ≤ Cen b := fun x hx =>
    Subgroup.mem_centralizer_iff.mpr fun y hy => by
      rw [Set.mem_singleton_iff] at hy; subst hy
      exact Subgroup.mem_centralizer_iff.mp hx _ hbB
  have hBsyl : IsSylowOf 3 B H := by
    refine isSylowOf_of_card hBH ?_
    have h1 := isSylowOf_card hB
    have h2 : (Nat.card H).factorization 3 ≤ (Nat.card (Cen b)).factorization 3 :=
      (Nat.factorization_le_iff_dvd Nat.card_pos.ne' Nat.card_pos.ne').mpr
        (Subgroup.card_dvd_of_le hHb) 3
    have h4 : Nat.card B ∣ Nat.card H := Subgroup.card_dvd_of_le hBH
    have h5 : 3 ^ (Nat.card (Cen b)).factorization 3 ∣ Nat.card H := h1 ▸ h4
    have h6 := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three Nat.card_pos.ne').mp h5
    exact h1.trans (congrArg (3 ^ ·) (le_antisymm h6 h2))
  have hP3 : IsPGroup 3 (B.subgroupOf H) := hBsyl.2.1.comap_subtype
  have hidx : ¬ 3 ∣ (B.subgroupOf H).index :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp hBsyl.2.2
  let P : Sylow 3 H := hP3.toSylow hidx
  have hPc : Subgroup.normalizer (P : Set H) ≤ Subgroup.centralizer (P : Set H) := by
    intro h _
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have hx' : (x : G) ∈ B := by simpa [P, Subgroup.mem_subgroupOf] using hx
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp h.2 (x : G) hx')
  obtain ⟨X, hXn, hcard, h3X, hX⟩ := exists_normal_complement_of_central P hPc
  set Xg : Subgroup G := X.map H.subtype with hXg
  have hcardXg : Nat.card Xg = Nat.card X := Subgroup.card_map_of_injective H.subtype_injective
  have hconj : ∀ a ∈ A, ∀ x ∈ Xg, a * x * a⁻¹ ∈ Xg := by
    intro a ha y hy
    obtain ⟨x, hxX, rfl⟩ := hy
    have haN : a ∈ Nor B := hAB ha
    have haN' : a⁻¹ ∈ Nor B := (Subgroup.normalizer (B : Set G)).inv_mem haN
    have hmem : a * (x : G) * a⁻¹ ∈ H := by
      show a * (x : G) * a⁻¹ ∈ CenS B
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      have hz' : a⁻¹ * z * a⁻¹⁻¹ ∈ B := (Subgroup.mem_normalizer_iff.mp haN' z).mp hz
      have := Subgroup.mem_centralizer_iff.mp x.2 _ hz'
      calc z * (a * x * a⁻¹) = a * ((a⁻¹ * z * a) * x) * a⁻¹ := by group
        _ = a * (x * (a⁻¹ * z * a)) * a⁻¹ := by simpa using congrArg (fun w => a * w * a⁻¹) this
        _ = a * x * a⁻¹ * z := by group
    have hord : Nat.Coprime (orderOf (⟨a * (x : G) * a⁻¹, hmem⟩ : H)) 3 := by
      have h1 : orderOf (⟨a * (x : G) * a⁻¹, hmem⟩ : H) = orderOf (x : G) := by
        rw [← Subgroup.orderOf_coe]
        exact orderOf_injective (MulAut.conj a).toMonoidHom (MulAut.conj a).injective (x : G)
      rw [h1, Subgroup.orderOf_coe]
      have h2 : orderOf x ∣ Nat.card X := by
        have := orderOf_dvd_natCard (⟨x, hxX⟩ : X)
        simpa using this
      exact Nat.Coprime.coprime_dvd_left h2
        ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3X).symm
    exact ⟨_, hX _ hord, rfl⟩
  have hAXg : A ≤ Subgroup.normalizer (Xg : Set G) := fun a ha => mem_nor_of_forall (hconj a ha)
  have h2X : ¬ 2 ∣ Nat.card X := by
    intro h2
    have h2' : 2 ∣ Nat.card Xg := by rw [hcardXg]; exact h2
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hA3 : IsPGroup 3 A := IsPGroup.of_card (n := 4) hA.2
    have h3Xg : ¬ 3 ∣ Nat.card Xg := by rw [hcardXg]; exact h3X
    obtain ⟨S, hS, -, hAS⟩ := CFSG.Goldschmidt.G310.exists_invariant_sylow_containing
      Nat.prime_three Nat.prime_two (A := A) (M := Xg) (Q := ⊥) hA3 h3Xg hAXg bot_le
      (IsPGroup.of_card (n := 0) (by simp))
      (show A ≤ Subgroup.normalizer ((⊥ : Subgroup G) : Set G) from
        fun a _ => mem_nor_of_forall (fun y hy => by
          rw [(Subgroup.mem_bot).mp hy]; simp))
    have hSne : S ≠ ⊥ := by
      intro hSb
      haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := Xg) 2 h2'
      have hxo : orderOf (x : G) = 2 := by rw [Subgroup.orderOf_coe]; exact hx
      have hZ : Subgroup.zpowers (x : G) ≤ Xg := Subgroup.zpowers_le.mpr x.2
      have hZp : IsPGroup 2 (Subgroup.zpowers (x : G)) :=
        IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hxo]; simp)
      have := hS.2.2 _ hZ hZp (by rw [hSb]; exact bot_le)
      rw [hSb] at this
      have h1 : (x : G) ∈ (⊥ : Subgroup G) := by
        rw [← this]; exact Subgroup.mem_zpowers _
      have : (x : G) = 1 := by simpa using h1
      rw [this, orderOf_one] at hxo
      omega
    have := four_le_localRank hSne hS.2.1 hA hAS
    omega
  have hoddX : Odd (Nat.card X) := Nat.odd_iff.mpr (by omega)
  obtain ⟨n, hn⟩ := P.isPGroup'.exists_card_eq
  have : Nat.card H = Nat.card X * 3 ^ n := by rw [hcard]; congr 1
  rw [this]
  exact hoddX.mul (Odd.pow (by decide))

end CFSG.RankThree.PartTwo.Sec21.FF79
