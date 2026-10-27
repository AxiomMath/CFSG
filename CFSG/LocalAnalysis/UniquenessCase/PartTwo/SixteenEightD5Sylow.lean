module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightD5Aut
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightD5CoordCor

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup

variable {W : Type} [CommGroup W] [Finite W] {L : Subgroup (MulAut W)}
  {K : Fin 4 → Subgroup (MulAut W)} {Z : Fin 4 → Subgroup W}

private lemma s16e_d5_nine_le_of_mul {a b : ℕ} (h : a * b = 27) (h1 : 0 < a) (h2 : a ≤ 3) :
    9 ≤ b := by
  interval_cases a <;> omega

theorem s16e_d5_sylow (hfr : s16e_d5_Frame L K Z) {A : Subgroup (MulAut W)} (hLA : L ≤ A)
    (hLn : ∀ g ∈ A, g ∈ Subgroup.normalizer (L : Set (MulAut W))) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (h3 : 3 ≤ CFSG.Open.pRank p A) :
    p = 3 ∧ 27 ≤ Nat.card ↥(A ⊓ Subgroup.centralizer (L : Set (MulAut W))) := by
  haveI : Fact p.Prime := ⟨hp⟩
  set C : Subgroup (MulAut W) := Subgroup.centralizer (L : Set (MulAut W)) with hC
  obtain ⟨E0, hE0A, hE0el, hE0card⟩ := CFSG.SectionRank.exists_pRank hp.one_lt A
  have hdvd0 : p ^ 3 ∣ Nat.card ↥E0 := by
    rw [hE0card]
    exact pow_dvd_pow p h3
  obtain ⟨Esub, hEsubcard⟩ :=
    Sylow.exists_subgroup_card_pow_prime (G := ↥E0) p (n := 3) hdvd0
  let E : Subgroup (MulAut W) := Esub.map E0.subtype
  have hEcard : Nat.card ↥E = p ^ 3 := by
    dsimp only [E]
    rw [Subgroup.card_map_of_injective E0.subtype_injective, hEsubcard]
  have hE0le : E ≤ E0 := Subgroup.map_subtype_le Esub
  have hEA : E ≤ A := hE0le.trans hE0A
  have hEcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := by
    intro x hx y hy
    haveI : IsMulCommutative ↥E0 := hE0el.1
    exact congrArg Subtype.val (mul_comm' ⟨x, hE0le hx⟩ ⟨y, hE0le hy⟩)
  have hIdxA : ((A ⊓ C).subgroupOf A).index ∣ 48 := by
    have h := s16e_d5_index_dvd_48 (G := MulAut W) (L := L) (A := A)
      (by rw [hfr.card_L]) hLn
    simpa only [hC] using h
  have hCent : Nat.card ↥C ∣ 81 := by
    simpa only [hC] using s16e_d5_card_cent_dvd hfr
  have hCardBdvdC : Nat.card ↥(A ⊓ C) ∣ Nat.card ↥C :=
    Subgroup.card_dvd_of_le (inf_le_right : A ⊓ C ≤ C)
  have hCardBdvd81 : Nat.card ↥(A ⊓ C) ∣ 81 := hCardBdvdC.trans hCent
  have hCardA : Nat.card ↥A = Nat.card ↥(A ⊓ C) * ((A ⊓ C).subgroupOf A).index := by
    have h := Subgroup.relIndex_mul_card (H := A ⊓ C) (K := A)
    rw [inf_of_le_left (inf_le_left : A ⊓ C ≤ A)] at h
    rw [mul_comm]
    exact h.symm
  have hCardAdvd : Nat.card ↥A ∣ 81 * 48 := by
    rw [hCardA]
    exact Nat.mul_dvd_mul hCardBdvd81 hIdxA
  have hp3dvd : p ^ 3 ∣ Nat.card ↥A := by
    have h := Subgroup.card_dvd_of_le hEA
    rwa [hEcard] at h
  have hpdvd : p ∣ Nat.card ↥A := (dvd_pow_self p (by norm_num : 3 ≠ 0)).trans hp3dvd
  have hpdvd3888 : p ∣ 2 ^ 4 * 3 ^ 5 := by
    have h : (2 : ℕ) ^ 4 * 3 ^ 5 = 81 * 48 := by norm_num
    rw [h]
    exact hpdvd.trans hCardAdvd
  have hp23 : p ∣ 2 ∨ p ∣ 3 := by
    rcases hp.dvd_mul.mp hpdvd3888 with h | h
    · exact Or.inl (hp.dvd_of_dvd_pow h)
    · exact Or.inr (hp.dvd_of_dvd_pow h)
  have hp3 : p = 3 := by
    rcases hp23 with h2 | h3dvd
    · exact absurd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2) hp2
    · exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h3dvd
  have hEcard27 : Nat.card ↥E = 27 := by
    rw [hp3] at hEcard
    norm_num at hEcard
    exact hEcard
  have hIdxE48 : ((E ⊓ C).subgroupOf E).index ∣ 48 := by
    have h := s16e_d5_index_dvd_48 (G := MulAut W) (L := L) (A := E)
      (by rw [hfr.card_L]) (fun g hg => hLn g (hEA hg))
    simpa only [hC] using h
  have hmulE : ((E ⊓ C).subgroupOf E).index * Nat.card ↥(E ⊓ C) = Nat.card ↥E := by
    have h := Subgroup.relIndex_mul_card (H := E ⊓ C) (K := E)
    rw [inf_of_le_left (inf_le_left : E ⊓ C ≤ E)] at h
    exact h
  have hmulE27 : ((E ⊓ C).subgroupOf E).index * Nat.card ↥(E ⊓ C) = 27 := by
    rw [hmulE, hEcard27]
  have hIdxE27 : ((E ⊓ C).subgroupOf E).index ∣ 27 :=
    ⟨Nat.card ↥(E ⊓ C), hmulE27.symm⟩
  have hIdx3 : ((E ⊓ C).subgroupOf E).index ∣ 3 := by
    have h := Nat.dvd_gcd hIdxE27 hIdxE48
    rwa [show Nat.gcd 27 48 = 3 by norm_num] at h
  have hidx_le : ((E ⊓ C).subgroupOf E).index ≤ 3 :=
    Nat.le_of_dvd (by norm_num) hIdx3
  have hidx_pos : 0 < ((E ⊓ C).subgroupOf E).index := by
    by_contra h
    rw [not_lt, Nat.le_zero] at h
    rw [h, zero_mul] at hmulE27
    norm_num at hmulE27
  have hcardE9 : 9 ≤ Nat.card ↥(E ⊓ C) :=
    s16e_d5_nine_le_of_mul hmulE27 hidx_pos hidx_le
  have hnotle : ¬ (E ⊓ C ≤ L) := by
    intro hle
    have hcard_le : Nat.card ↥(E ⊓ C) ≤ Nat.card ↥L := Subgroup.card_le_of_le hle
    rw [hfr.card_L] at hcard_le
    have hcard_eq : Nat.card ↥(E ⊓ C) = 9 := le_antisymm hcard_le hcardE9
    have hEq : E ⊓ C = L :=
      Subgroup.eq_of_le_of_card_ge hle (by rw [hfr.card_L]; exact hcardE9)
    have hLE : L ≤ E := by rw [← hEq]; exact inf_le_left
    have hEsubC : E ≤ C := by
      intro x hx
      rw [hC, Subgroup.mem_centralizer_iff]
      intro y hy
      exact (hEcomm x hx y (hLE hy)).symm
    have hEinfC : E ⊓ C = E := inf_eq_left.2 hEsubC
    have hcontra : Nat.card ↥(E ⊓ C) = 27 := by rw [hEinfC, hEcard27]
    omega
  have hb_exists : ∃ b : MulAut W, b ∈ E ⊓ C ∧ b ∉ L := by
    by_contra hcon
    apply hnotle
    intro x hx
    by_contra hxL
    exact hcon ⟨x, hx, hxL⟩
  obtain ⟨b, hbB, hbL⟩ := hb_exists
  have hLB : L ≤ A ⊓ C := by
    refine le_inf hLA ?_
    rw [hC]
    exact s16e_d5_L_le_cent hfr
  have hne : L ≠ A ⊓ C := by
    intro hEq
    rw [hEq] at hbL
    exact hbL ⟨hEA hbB.1, hbB.2⟩
  have hlt : L < A ⊓ C := lt_of_le_of_ne hLB hne
  have hcardLt : Nat.card ↥L < Nat.card ↥(A ⊓ C) := Subgroup.card_lt_of_lt hlt
  rw [hfr.card_L] at hcardLt
  have h81' : Nat.card ↥(A ⊓ C) ∣ 3 ^ 4 := by
    rwa [show (3 : ℕ) ^ 4 = 81 by norm_num]
  obtain ⟨k, hk_le, hk⟩ := (Nat.dvd_prime_pow (p := 3) Nat.prime_three).mp h81'
  have hk3 : 3 ≤ k := by
    by_contra h
    have hk2 : k ≤ 2 := by omega
    have hle : 3 ^ k ≤ 3 ^ 2 := Nat.pow_le_pow_right (by norm_num) hk2
    rw [show (3 : ℕ) ^ 2 = 9 by norm_num] at hle
    rw [hk] at hcardLt
    omega
  have h27 : 27 ≤ Nat.card ↥(A ⊓ C) := by
    calc (27 : ℕ) = 3 ^ 3 := by norm_num
      _ ≤ 3 ^ k := Nat.pow_le_pow_right (by norm_num) hk3
      _ = Nat.card ↥(A ⊓ C) := hk.symm
  refine ⟨hp3, ?_⟩
  simpa only [hC] using h27

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
