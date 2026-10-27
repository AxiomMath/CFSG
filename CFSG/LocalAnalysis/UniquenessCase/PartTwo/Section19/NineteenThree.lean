module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.Statements
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.Ctx19One

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19

open CFSG.Open Subgroup CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo

variable {G : Type} [Group G] [Finite G]

theorem prime_dvd_bar2 {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {L : Subgroup G}
    (h : p ∈ piSet L) : p ∣ Nat.card (Bar2 L) := by
  obtain ⟨-, hdvd⟩ := h
  have hcard := Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 ↥L)
  have hpc2 : IsPGroup 2 (CFSG.pCore 2 ↥L) := CFSG.pCore_isPGroup
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := 2) (G := ↥(CFSG.pCore 2 ↥L))).mp hpc2
  have hpdvd : p ∣ Nat.card (Bar2 L) * Nat.card ↥(CFSG.pCore 2 ↥L) := hcard ▸ hdvd
  rcases hp.dvd_mul.mp hpdvd with h1 | h1
  · exact h1
  · rw [hk] at h1
    have hp2' : p = 2 := by
      have h2 : p ∣ 2 := hp.dvd_of_dvd_pow h1
      rcases (Nat.dvd_prime (Nat.prime_two)).mp h2 with h | h
      · exact absurd h hp.ne_one
      · exact h
    exact absurd hp2' hp2

theorem nineteen_three_of_rank_le_three (D : Data G) {V₀ V : Subgroup G} {p : ℕ}
    {L K : Subgroup G} (h : Ctx19_1 D V₀ V p L K) (h3 : mSub V₀ ≤ 3) :
    R19_3At D V₀ V p L K h := by
  have hP := h.hyp.hyp125.pairFacts
  have hV2 : IsPGroup 2 V₀ := hP.elemAbelian₀.isPGroup
  have hcard : Nat.card V₀ = 2 ^ mSub V₀ := card_eq_two_pow_mSub hV2
  have h8 : Nat.card V₀ ≤ 8 := by
    rw [hcard]
    have : 2 ^ mSub V₀ ≤ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) h3
    omega
  have hLN : L ≤ normalizer (V₀ : Set G) :=
    (CFSG.Quasithin.A3.subnormal_le h.hyp.hL.1.1).trans hP.le_normalizer₀
  have hKN : K ≤ normalizer (V₀ : Set G) :=
    (CFSG.Quasithin.A3.subnormal_le h.hK.1).trans hP.le_normalizer₀
  have hLsimple : IsSimpleGroup (Bar2 L) := isSimpleGroup_bar2_of_shape h.shape
  have h5L : 5 ∣ Nat.card (Bar2 L) := by
    have hp : (5 : ℕ).Prime := Nat.prime_five
    exact prime_dvd_bar2 hp (by norm_num) (by simpa [h.p_eq] using h.hyp.hL.2)
  have hKsimple : IsSimpleGroup (Bar2 K) := isSimpleGroup_bar2_of_isAlt_five h.hKshape
  have h5K : 5 ∣ Nat.card (Bar2 K) := by
    rw [card_bar2_of_isAlt_five h.hKshape]
    norm_num
  have hLc : L ≤ centralizer (V₀ : Set G) :=
    le_centralizer_of_bar2_simple h.hyp.hL.1.2.1 hLsimple h5L hLN hV2 h8
  have hKc : K ≤ centralizer (V₀ : Set G) :=
    le_centralizer_of_bar2_simple h.hK.2.1 hKsimple h5K hKN hV2 h8
  exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr (sup_le hLc hKc)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19
