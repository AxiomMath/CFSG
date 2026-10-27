module

public import CFSG.RankThree.PartTwo.Sec4.RonanK432Defs
public import CFSG.RankThree.PartTwo.Sec4.Item424Res7ProofG2

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK432

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley
open CFSG.AGLEmbeddingD2.Wilson.MaximalityAmbient.RealThree (Real3)

theorem g2Row_exists_inv_of_conj_inv {G : Type*} [Group G] {x g n : G}
    (h : n * (g * x * g⁻¹) * n⁻¹ = (g * x * g⁻¹)⁻¹) : ∃ t : G, t * x * t⁻¹ = x⁻¹ :=
  ⟨g⁻¹ * n * g, by
    calc g⁻¹ * n * g * x * (g⁻¹ * n * g)⁻¹ = g⁻¹ * (n * (g * x * g⁻¹) * n⁻¹) * g := by group
      _ = g⁻¹ * (g * x * g⁻¹)⁻¹ * g := by rw [h]
      _ = x⁻¹ := by group⟩

theorem g2Row_ringChar_ne_three_of_card {K : Type} [Field K] [Finite K] {p f : ℕ} (hp : p.Prime)
    (hp3 : p ≠ 3) (hK : Nat.card K = p ^ f) : ringChar K ≠ 3 := by
  intro h
  have : Fintype K := Fintype.ofFinite K
  have : CharP K 3 := by rw [← h]; exact ringChar.charP K
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨n, -, hn⟩ := FiniteField.card K 3
  have h1 : Nat.card K = 3 ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card, hn]
  have h2 : 3 ∣ p ^ f := by
    rw [← hK, h1]
    exact dvd_pow_self 3 n.ne_zero
  exact hp3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp
    (Nat.prime_three.dvd_of_dvd_pow h2)).symm

theorem g2Row_four_le_pow_of_three_le {p f : ℕ} (hp : p.Prime) (hp3 : p ≠ 3) (hf : 1 ≤ f)
    (h3 : 3 ≤ p ^ f) : 4 ≤ p ^ f := by
  by_contra h
  have h33 : p ^ f = 3 := by omega
  have hdvd : p ∣ 3 := by
    rw [← h33]
    exact dvd_pow_self p (by omega)
  rcases Nat.prime_three.eq_one_or_self_of_dvd p hdvd with h1 | h1
  · exact hp.one_lt.ne' h1
  · exact hp3 h1

theorem g2Row_five_le_of_prime_ne_two_three {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) :
    5 ≤ p := by
  have h2 := hp.two_le
  by_contra h
  have h4 : p = 4 := by omega
  subst h4
  exact absurd hp (by decide)

section Real


theorem real3_adjointGroup_G2 {K : Type} [Field K] [Finite K] (hchar : ringChar K ≠ 3)
    (h4 : 4 ≤ Nat.card K) : Real3 (adjointGroup .G2 K) := by
  intro x hx
  by_cases hx1 : x = 1
  · exact ⟨1, by simp [hx1]⟩
  obtain ⟨g, hg⟩ := Sec11.KS11Lie7Proof.g2ThreeConjSL2_holds K hchar h4 x hx hx1
  have h3 : (3 : K) ≠ 0 := Res424Seven.three_ne_zero_of_ringChar hchar
  have hc3 : (g * x * g⁻¹) ^ 3 = 1 := by rw [conj_pow, hx, mul_one, mul_inv_cancel]
  have hc1 : g * x * g⁻¹ ≠ 1 := fun h => hx1 (by simpa using h)
  rcases hg with hS | hM
  · obtain ⟨n, -, hn⟩ := Res424Seven.exists_inv_short h3 (Subgroup.one_mem _) hS hc3 hc1
    exact g2Row_exists_inv_of_conj_inv hn
  · obtain ⟨n, hn, -⟩ := Res424Seven.exists_inv_long h3 hM (Subgroup.one_mem _) hc3 hc1
    exact g2Row_exists_inv_of_conj_inv hn

theorem real3_of_chevalleyExceptionalModel_G2 {S : Type} [Group S] {p f : ℕ} (hp3 : p ≠ 3)
    (h : ChevalleyExceptionalModel S .G2 p f) : Real3 S := by
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := exists_mulEquiv_adjointGroup_G2 h
  have hp : p.Prime := h.1.1
  have h3 : 3 ≤ p ^ f := h.1.2.2.2
  exact Real3.of_mulEquiv e
    (real3_adjointGroup_G2 (g2Row_ringChar_ne_three_of_card hp hp3 hK)
      (hK ▸ g2Row_four_le_pow_of_three_le hp hp3 h.1.2.1 h3))

end Real

section NoCover


theorem noCover3_of_chevalleyExceptionalModel_G2 {S : Type} [Group S] {p f : ℕ} (hp3 : p ≠ 3)
    (h : ChevalleyExceptionalModel S .G2 p f) : NoCover3 S := by
  intro L _ _ hq hZ ⟨e⟩
  have hM : ChevalleyExceptionalModel (L ⧸ Subgroup.center L) .G2 p f :=
    CFSG.SectionRank.chevalleyExceptionalModel_of_mulEquiv e h
  by_cases hp2 : p = 2
  · subst hp2
    have : Group.IsPerfect L := hq.1
    have hodd : Odd (Nat.card (QuotientGroup.mk' (Subgroup.center L)).ker) := by
      rw [QuotientGroup.ker_mk']
      obtain ⟨k, hk⟩ := hZ.exists_card_eq
      rw [hk]
      exact Odd.pow (by decide)
    have hker := CFSG.SectionRank.g2_even_perfect_odd_cover_trivial hM
      (QuotientGroup.mk' (Subgroup.center L)) (QuotientGroup.mk'_surjective _)
      (by rw [QuotientGroup.ker_mk']) hodd
    rwa [QuotientGroup.ker_mk'] at hker
  · have hp : p.Prime := h.1.1
    have hf : f ≠ 0 := by have := h.1.2.1; omega
    have h5 : 5 ≤ p ^ f :=
      (g2Row_five_le_of_prime_ne_two_three hp hp2 hp3).trans (Nat.le_self_pow hf p)
    exact GH74.GLS.Stage2.Signalizer.Odd87.g2_center_eq_bot hq
      (Or.inr (Or.inl ⟨rfl, by decide, hM⟩)) h5

end NoCover

section ListRow


theorem listRow_of_chevalleyExceptionalModel_G2 {S : Type} [Group S] [Finite S] {p f : ℕ}
    (hp3 : p ≠ 3) (h : ChevalleyExceptionalModel S .G2 p f) : ListRow S :=
  fun _ _ _ => Or.inr (Or.inl ⟨Or.inl ⟨p, f, h⟩, real3_of_chevalleyExceptionalModel_G2 hp3 h,
    noCover3_of_chevalleyExceptionalModel_G2 hp3 h⟩)

end ListRow

end CFSG.RankThree.PartTwo.Sec4.RonanK432
