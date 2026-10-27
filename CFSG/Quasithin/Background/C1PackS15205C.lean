module

public import CFSG.Quasithin.Background.C1PackS15205B
public import CFSG.Quasithin.EmptyFaithful.S152Y18

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement Pointwise

namespace C1Pack5

section Abstract

variable {A : Type*} [Group A] [Finite A]

theorem card_eq_four_of_isSylowTwoOf {X S : Subgroup A} (hX : Nat.card X = 36)
    (hS : IsSylowTwoOf S X) : Nat.card S = 4 := by
  obtain ⟨b, hb⟩ := hS.2.1.exists_card_eq
  have h1 : Nat.card (S.subgroupOf X) * (S.subgroupOf X).index = Nat.card X :=
    Subgroup.card_mul_index _
  have h2 : Nat.card (S.subgroupOf X) = Nat.card S :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hS.1).toEquiv
  have hodd : ¬ 2 ∣ (S.subgroupOf X).index := hS.2.2
  rw [h2, hb, hX] at h1
  have hb5 : b ≤ 5 := by
    by_contra h
    have : 2 ^ 6 ≤ 2 ^ b := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hi : 0 < (S.subgroupOf X).index := Nat.pos_of_ne_zero (by rintro h0; rw [h0] at h1; omega)
    nlinarith
  rw [hb]
  interval_cases b <;> first | rfl | (exfalso; apply hodd; omega)

theorem abstract_three {Mb Tb Hb : Subgroup A} (sh : OmShape Mb) (hSyl : IsSylowTwoOf Tb Mb)
    (hTH : Tb ≤ Hb) (hHM : Hb ≤ Mb) (hne : Hb ≠ Tb) (hneM : Hb ≠ Mb) :
    ∃ Q : Subgroup A, Q ≤ oTwoUpper Mb ∧ Nat.card Q = 3 ∧
      (∀ g ∈ Mb, ∀ q ∈ Q, g * q * g⁻¹ ∈ Q) ∧ Hb = Q ⊔ Tb := by
  classical
  obtain ⟨hcardX, hcardP, hcomm, hexp, hcent, htwo, hie, hpair⟩ := sh
  set P : Subgroup A := oTwoUpper Mb with hPdef
  have hPM : P ≤ Mb := oTwoUpper_le Mb
  have hTcard : Nat.card Tb = 4 := card_eq_four_of_isSylowTwoOf hcardX hSyl
  have hMn : ∀ g ∈ Mb, ∀ p ∈ P, g * p * g⁻¹ ∈ P := fun g hg p hp =>
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_oTwoUpper Mb hg) p).mp hp
  have hTMn : Tb ≤ Subgroup.normalizer (P : Set A) := by
    intro t ht
    rw [Subgroup.mem_normalizer_iff]
    intro x
    exact ⟨fun hx => hMn t (hSyl.1 ht) x hx, fun hx => by
      have := hMn t⁻¹ (Mb.inv_mem (hSyl.1 ht)) _ hx
      simpa [mul_assoc] using this⟩
  have hsup : P ⊔ Tb = Mb := by
    have hle : P ⊔ Tb ≤ Mb := sup_le hPM hSyl.1
    have hd1 : 9 ∣ Nat.card (P ⊔ Tb : Subgroup A) := hcardP ▸ Subgroup.card_dvd_of_le le_sup_left
    have hd2 : 4 ∣ Nat.card (P ⊔ Tb : Subgroup A) := hTcard ▸ Subgroup.card_dvd_of_le le_sup_right
    have hd : 36 ∣ Nat.card (P ⊔ Tb : Subgroup A) :=
      (Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num : Nat.Coprime 9 4) hd1 hd2)
    exact Subgroup.eq_of_le_of_card_ge hle (by rw [hcardX]; exact Nat.le_of_dvd Nat.card_pos hd)
  have hfac : ∀ x ∈ Mb, ∃ p ∈ P, ∃ t ∈ Tb, x = p * t := by
    intro x hx
    rw [← hsup] at hx
    have hx' : x ∈ ((P ⊔ Tb : Subgroup A) : Set A) := hx
    rw [Subgroup.coe_mul_of_right_le_normalizer_left P Tb hTMn] at hx'
    obtain ⟨p, hp, t, ht, rfl⟩ := Set.mem_mul.mp hx'
    exact ⟨p, hp, t, ht, rfl⟩
  set Q : Subgroup A := Hb ⊓ P with hQdef
  have hQP : Q ≤ P := inf_le_right
  have hHQ : Hb = Q ⊔ Tb := by
    refine le_antisymm (fun h hh => ?_) (sup_le inf_le_left hTH)
    obtain ⟨p, hp, t, ht, rfl⟩ := hfac h (hHM hh)
    have hpH : p ∈ Hb := by
      have : p = p * t * t⁻¹ := by group
      rw [this]
      exact Hb.mul_mem hh (Hb.inv_mem (hTH ht))
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ⟨hpH, hp⟩) (Subgroup.mem_sup_right ht)
  have hQcard : Nat.card Q = 3 := by
    have hd : Nat.card Q ∣ 3 ^ 2 := (by norm_num : (9 : ℕ) = 3 ^ 2) ▸ hcardP ▸
      Subgroup.card_dvd_of_le hQP
    obtain ⟨i, hi, hQi⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hd
    interval_cases i
    · exfalso
      have : Q = ⊥ := Subgroup.card_eq_one.mp (by simpa using hQi)
      apply hne
      rw [hHQ, this, bot_sup_eq]
    · simpa using hQi
    · exfalso
      have hQP' : Q = P := Subgroup.eq_of_le_of_card_ge hQP (by rw [hcardP, hQi]; norm_num)
      apply hneM
      apply le_antisymm hHM
      rw [← hsup]
      exact sup_le (hQP' ▸ inf_le_left) hTH
  refine ⟨Q, hQP, hQcard, fun g hg q hq => ?_, hHQ⟩
  obtain ⟨p, hp, t, ht, rfl⟩ := hfac g hg
  have h1 : t * q * t⁻¹ ∈ Q :=
    ⟨Hb.mul_mem (Hb.mul_mem (hTH ht) hq.1) (Hb.inv_mem (hTH ht)),
      hMn t (hSyl.1 ht) q hq.2⟩
  have hpc : p * (t * q * t⁻¹) = (t * q * t⁻¹) * p := hcomm p hp _ (hQP h1)
  have e : p * t * q * (p * t)⁻¹ = t * q * t⁻¹ := by
    calc p * t * q * (p * t)⁻¹ = p * (t * q * t⁻¹) * p⁻¹ := by group
      _ = (t * q * t⁻¹) := by rw [hpc]; group
  rw [e]
  exact h1

end Abstract

section Concrete

variable {G : Type} [Group G] [Finite G] {T Mc M M₁ : Subgroup G}

theorem Ctr5.not_Hb_le_Mcb (c : Ctr5 T Mc M M₁) :
    ¬ autOn (M₁ ⊓ M) (V154 T Mc M) ≤ autOn (M ⊓ Mc) (V154 T Mc M) := fun h =>
  c.not_forall_mul_Mc (exists_mul_of_autOn_le c.std.data.hMV inf_le_right inf_le_left h)

theorem Ctr5.exists_Qbar (hOm : Om4IsoStatement) (c : Ctr5 T Mc M M₁) :
    ∃ Q : Subgroup (MulAut (V154 T Mc M)), Q ≤ oTwoUpper (mBar0 T Mc M) ∧ Nat.card Q = 3 ∧
      (∀ g ∈ autOn M (V154 T Mc M), ∀ q ∈ Q, g * q * g⁻¹ ∈ Q) ∧
      autOn (M₁ ⊓ M) (V154 T Mc M) = Q ⊔ autOn T (V154 T Mc M) := by
  have hd := c.std.data
  have h3 := c.case_three
  obtain ⟨-, hA, -⟩ := id h3
  have sh : OmShape (mBar0 T Mc M) := S152Y.omShape_mBar0 hOm h3
  have hSyl : IsSylowTwoOf (autOn T (V154 T Mc M)) (mBar0 T Mc M) := by
    rw [← hA]
    exact S152Y.isSylowTwoOf_Tb hd
  have hTH : autOn T (V154 T Mc M) ≤ autOn (M₁ ⊓ M) (V154 T Mc M) := A4.autOn_mono c.T_le_H
  have hHM : autOn (M₁ ⊓ M) (V154 T Mc M) ≤ mBar0 T Mc M := by
    rw [← hA]
    exact A4.autOn_mono inf_le_right
  have hne : autOn (M₁ ⊓ M) (V154 T Mc M) ≠ autOn T (V154 T Mc M) := fun h =>
    c.not_Hb_le_Mcb (by
      rw [h]
      exact A4.autOn_mono (le_inf c.T_le_M c.qtfe.t_le_mc))
  have hneM : autOn (M₁ ⊓ M) (V154 T Mc M) ≠ mBar0 T Mc M := fun h =>
    c.not_mBar0_le (le_of_eq h.symm)
  obtain ⟨Q, hQP, hQ3, hQn, hHQ⟩ := abstract_three sh hSyl hTH hHM hne hneM
  exact ⟨Q, hQP, hQ3, fun g hg q hq => hQn g (by rw [← hA]; exact hg) q hq, hHQ⟩

end Concrete

end C1Pack5

end CFSG.Quasithin
