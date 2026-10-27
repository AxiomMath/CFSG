module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1677ThreeTools
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenThreeNaturalProduct
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3Kbar
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1Red
public import CFSG.LocalAnalysis.ComponentClassification.Asc75T4Bridge

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

private theorem s168e3_eq_seven_of_sq_dvd_168_mul_seven {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    (h : q ^ 2 ∣ 168 * 7) : q = 7 := by
  have hle : q ^ 2 ≤ 168 * 7 := Nat.le_of_dvd (by norm_num) h
  have hqlo : 2 ≤ q := hq.two_le
  have hqle : q ≤ 34 := by nlinarith
  interval_cases q <;> first
    | (norm_num at hq; done)
    | (norm_num at hq2; done)
    | (norm_num at h; done)
    | rfl

private theorem s168e3_eq_three_or_seven_of_sq_dvd_168_mul_21 {q : ℕ} (hq : q.Prime)
    (hq2 : q ≠ 2) (h : q ^ 2 ∣ 168 * 21) : q = 3 ∨ q = 7 := by
  have hle : q ^ 2 ≤ 168 * 21 := Nat.le_of_dvd (by norm_num) h
  have hqlo : 2 ≤ q := hq.two_le
  have hqle : q ≤ 59 := by nlinarith
  interval_cases q <;> first
    | (norm_num at hq; done)
    | (norm_num at hq2; done)
    | (norm_num at h; done)
    | exact Or.inl rfl
    | exact Or.inr rfl

theorem s168e3_threeNatSeven_l3_sig_eq_seven_of_small_kBar
    {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV)
    (hT : ThreeNat (Mbar D.M V₀ V hV) (lBar V₀ V hV L)
      (barSub V₀ V hV D.T))
    (h7 : Nat.card ↥(irrSet (lBar V₀ V hV L)) = 7)
    (hL3 : IsL3 ↥(lBar V₀ V hV L) 1)
    (hK : Nat.card ↥(s1t3KBar (Mbar D.M V₀ V hV) (lBar V₀ V hV L)) = 7 ∨
      Nat.card ↥(s1t3KBar (Mbar D.M V₀ V hV) (lBar V₀ V hV L)) = 21) :
    D.sig = {7} := by
  have : Finite (MulAut (Vtil V₀ V hV)) := MulEquiv.finite_left
  let A := Mbar D.M V₀ V hV
  let B := lBar V₀ V hV L
  let K := s1t3KBar A B
  have hprod : B ⊔ K = A := hT.sup_kBar_eq_of_isL3 h7 hL3
  obtain ⟨N, -, hLN, -, -, hNK, -, -⟩ := hT.structure_of_seven h7
  have hBK : B ⊓ K = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hxN : (x : MulAut (Vtil V₀ V hV)) ∈ N := hLN hx.1
    have hxNK : (x : MulAut (Vtil V₀ V hV)) ∈ N ⊓ K := ⟨hxN, hx.2⟩
    rw [hNK, Subgroup.mem_bot] at hxNK
    exact hxNK
  have hcommBK : ∀ b ∈ B, ∀ k ∈ K, b * k = k * b := by
    intro b hb k hk
    have hkcent :
        k ∈ Subgroup.centralizer (B : Set (MulAut (Vtil V₀ V hV))) :=
      (Subgroup.mem_inf.mp hk).2
    exact (Subgroup.mem_centralizer_iff.mp hkcent) b hb
  let e : B × K ≃* A :=
    CFSG.ComponentClassification.Asc75T4.mulEquivOfCommute hT.le inf_le_left hcommBK hBK hprod
  have hcardA : Nat.card ↥A = 168 * Nat.card ↥K := by
    rw [← Nat.card_congr e.toEquiv, Nat.card_prod, card_eq_of_isL3 hL3]
  have hforall : ∀ q ∈ D.sig, q = 7 := by
    intro q hq
    obtain ⟨hqprime, hq2⟩ := D.sig_prime q hq
    have hqrank : 2 ≤ CFSG.Open.pRank q A := c.two_le_pRank_mbar hq
    obtain ⟨E, hEA, -, hEcard⟩ := CFSG.SectionRank.exists_pRank hqprime.one_lt A
    have hq2dvd : q ^ 2 ∣ Nat.card ↥A := by
      have h1 : q ^ 2 ∣ Nat.card ↥E := by
        rw [hEcard]
        exact pow_dvd_pow q hqrank
      exact h1.trans (Subgroup.card_dvd_of_le hEA)
    rcases hK with hK7 | hK21
    · have hcard7 : Nat.card ↥A = 168 * 7 := by rw [hcardA, hK7]
      exact s168e3_eq_seven_of_sq_dvd_168_mul_seven hqprime hq2 (hcard7 ▸ hq2dvd)
    ·
      have hnot3 : 3 ∉ D.sig := by
        intro h3
        let pi : ↥A →* ↥K := (MonoidHom.snd B K).comp e.symm.toMonoidHom
        have hpi : Function.Surjective pi := by
          intro k
          refine ⟨e (1, k), ?_⟩
          simp [pi]
        obtain ⟨P, hPnorm, hPcard⟩ :=
          CFSG.Walter.W67.exists_normal_card_seven hK21
        have : P.Normal := hPnorm
        have hPindex : P.index = 3 := by
          have hcardmul := P.card_mul_index
          rw [hPcard, hK21] at hcardmul
          omega
        let N : Subgroup ↥A := P.comap pi
        have : N.Normal := Subgroup.normal_comap pi
        have hNindex : N.index = 3 := by
          rw [Subgroup.index_comap_of_surjective P hpi, hPindex]
        exact s16e_mbar_index_ne_three D c.std.h638 h3 c.setting.hyp16 hV N hNindex
      have hcard21 : Nat.card ↥A = 168 * 21 := by rw [hcardA, hK21]
      rcases s168e3_eq_three_or_seven_of_sq_dvd_168_mul_21 hqprime hq2
        (hcard21 ▸ hq2dvd) with hq3 | hq7
      · exact absurd (hq3 ▸ hq) hnot3
      · exact hq7
  rw [Set.eq_singleton_iff_unique_mem]
  constructor
  · obtain ⟨q, hq⟩ := c.std.hx.sig_nonempty
    rwa [hforall q hq] at hq
  · exact hforall

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
