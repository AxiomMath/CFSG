module

public import CFSG.RankThree.PartTwo.Sec14.Ronan148KT1Rows
public import CFSG.RankThree.PartTwo.Sec14.Ronan148KT1Gen
public import CFSG.RankThree.PartTwo.KFacts.AutSzOrderThree

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148K

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo

theorem suzuki_quot_order_dvd {M : Type} [Group M] [Finite M]
    (X : Subgroup M) (N : Subgroup X) [N.Normal] {p f : ℕ}
    (hSz : CFSG.Blueprint.SuzukiModel (X ⧸ N) p f) :
    ∃ a : ℕ, 1 ≤ a ∧
      Nat.card (X ⧸ N) =
        (2 ^ (2 * a + 1)) ^ 2 * (2 ^ (2 * a + 1) - 1) * ((2 ^ (2 * a + 1)) ^ 2 + 1) ∧
      Nat.card (X ⧸ N) ∣ Nat.card M := by
  obtain ⟨-, a, ha, K, _, _, hf, hK, ⟨θ⟩⟩ := hSz
  have hK' : Nat.card K = 2 ^ (2 * a + 1) := by rw [hK, hf]
  refine ⟨a, ha, ?_, ?_⟩
  · rw [Nat.card_congr θ.toEquiv, CFSG.LieType.Ree.suzuki_order hK']
  · exact (Subgroup.card_dvd_of_surjective (f := QuotientGroup.mk' N)
      (QuotientGroup.mk'_surjective N)).trans (Subgroup.card_subgroup_dvd_card X)

theorem noSzSection_of_not_dvd_alt {M : Type} [Group M] [Finite M]
    (h13 : ¬ 13 ∣ Nat.card M) (h31 : ¬ 31 ∣ Nat.card M) (h2 : ¬ 2 ^ 14 ∣ Nat.card M) :
    CFSG.RankThree.PartTwo.Sec16.Steps166.NoSzSection M := by
  intro X N _ p f hSz
  obtain ⟨a, ha, hord, hdvd⟩ := suzuki_quot_order_dvd X N hSz
  rw [hord] at hdvd
  obtain rfl | rfl | h3 : a = 1 ∨ a = 2 ∨ 3 ≤ a := by omega
  · exact h13 (dvd_trans (by norm_num) hdvd)
  · exact h31 (dvd_trans (by norm_num) hdvd)
  · refine h2 (dvd_trans ?_ hdvd)
    refine Dvd.dvd.mul_right (Dvd.dvd.mul_right ?_ _) _
    rw [← pow_mul]
    exact Nat.pow_dvd_pow 2 (by omega)

theorem noSzSection_of_card_lt_alt {M : Type} [Group M] [Finite M]
    (h : Nat.card M < 29120) : CFSG.RankThree.PartTwo.Sec16.Steps166.NoSzSection M := by
  intro X N _ p f hSz
  obtain ⟨a, ha, hord, hdvd⟩ := suzuki_quot_order_dvd X N hSz
  have hle : Nat.card (X ⧸ N) ≤ Nat.card M := Nat.le_of_dvd Nat.card_pos hdvd
  rw [hord] at hle
  have h8 : 8 ≤ 2 ^ (2 * a + 1) :=
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ (2 * a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  set q := 2 ^ (2 * a + 1) with hq
  have h64 : 64 ≤ q ^ 2 := by
    have h' := Nat.pow_le_pow_left h8 2
    norm_num at h'
    exact h'
  have h7 : 7 ≤ q - 1 := by omega
  have h65 : 65 ≤ q ^ 2 + 1 := by omega
  have hprod := Nat.mul_le_mul (Nat.mul_le_mul h64 h7) h65
  have h29 : 29120 ≤ Nat.card M := le_trans hprod hle
  omega

theorem finite_mulAut_alt (n : ℕ) : Finite (MulAut (alternatingGroup (Fin n))) :=
  Finite.of_injective
    (fun φ : MulAut (alternatingGroup (Fin n)) =>
      (φ : alternatingGroup (Fin n) → alternatingGroup (Fin n)))
    DFunLike.coe_injective

theorem not_dvd_factorial_alt {n : ℕ} (hn5 : 5 ≤ n) (hn12 : n ≤ 12) (h6 : n ≠ 6) :
    ¬ 13 ∣ n.factorial ∧ ¬ 31 ∣ n.factorial ∧ ¬ 2 ^ 14 ∣ n.factorial := by
  interval_cases n <;> first | exact absurd rfl h6 | norm_num [Nat.factorial]

theorem rowOf143_alt
    (n : ℕ) (hn5 : 5 ≤ n) (hn12 : n ≤ 12) : RowOf143 (alternatingGroup (Fin n)) := by
  intro S _ _ _ _ ⟨e⟩ _
  have hA : CFSG.RankThree.PartTwo.Sec16.Steps166.NoSzSection
      (MulAut (alternatingGroup (Fin n))) := by
    haveI := finite_mulAut_alt n
    by_cases h6 : n = 6
    · subst h6
      exact noSzSection_of_card_lt_alt
        (lt_of_le_of_lt
          CFSG.ComponentClassification.CatalogueSchreierAlternating.DegreeSix.automorphism_card_le
          (by norm_num))
    · obtain ⟨h13, h31, h2⟩ := not_dvd_factorial_alt hn5 hn12 h6
      have hcard := CFSG.RankThree.PartTwo.Sec16.Steps166.card_mulAut_alternatingGroup hn5 h6
      exact noSzSection_of_not_dvd_alt (by rw [hcard]; exact h13) (by rw [hcard]; exact h31)
        (by rw [hcard]; exact h2)
  exact row143_of_noSzSection
    (CFSG.RankThree.PartTwo.Sec16.Steps166.noSzSection_mulAut_of_mulEquiv e hA)

theorem rowOf143_suzuki (m : ℕ)
    (hm : (TauCeti.LieTypeIndex.suzuki m).Valid) :
    RowOf143 (TauCeti.CFSGIndex.lie ⟨.suzuki m, hm⟩).Group := by
  intro S _ _ _ _ ⟨e⟩ h3
  obtain ⟨-, a, -, K, _, _, hf, hK', ⟨θ⟩⟩ :=
    CFSG.RankThree.PartTwo.Sec4.Census.suzukiModel_of_index m hm
  have hK : Nat.card K = 2 ^ (2 * a + 1) := by rw [hK', hf]
  have h3' : ¬ 3 ∣ Nat.card S := by
    rw [Nat.card_congr (e.trans θ).toEquiv]
    exact CFSG.RankThree.PartTwo.KFacts.not_three_dvd_card_suzukiGroup hK
  exact absurd h3 h3'

end CFSG.RankThree.PartTwo.Sec14.Ronan148K
