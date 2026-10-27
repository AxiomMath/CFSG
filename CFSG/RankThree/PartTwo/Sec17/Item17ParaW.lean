module

public import CFSG.RankThree.PartTwo.Sec17.Item17ParaTools
public import CFSG.RankThree.PartTwo.Sec14.Item1411Chain

public section

namespace CFSG.RankThree.PartTwo.Sec17

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.RankThree.PartTwo.Late CFSG.GH74.GLS

section Para

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {p : ℕ}

omit [Finite G] in
theorem xA_le_normalizer (A : Subgroup G) : xA A ≤ Subgroup.normalizer (A : Set G) :=
  (pPrimeCoreOf_le 3 _).trans (Subgroup.centralizer_le_normalizer _)

omit [Finite G] in
theorem xA_le_centralizer_of_mem {a : G} (ha : a ∈ A) :
    xA A ≤ Subgroup.centralizer ({a} : Set G) :=
  (pPrimeCoreOf_le 3 _).trans (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr ha))

theorem qStar_eq_conj
    (htr : ∀ Q₁ ∈ scriptQPiStar A (lB A) ⊤ (piOf p), ∀ Q₂ ∈ scriptQPiStar A (lB A) ⊤ (piOf p),
      IsConjIn (xA A) Q₁ Q₂)
    {Q : Subgroup G} (hQ : Q ∈ scriptQPiStar A (lB A) ⊤ (piOf p)) :
    scriptQPiStar A (lB A) ⊤ (piOf p) =
      {R | ∃ x ∈ xA A, R = Q.map (MulAut.conj x).toMonoidHom} := by
  ext R
  constructor
  · exact fun hR => htr Q hQ R hR
  · rintro ⟨x, hx, rfl⟩
    exact map_conj_mem_qStarTop (xA_le_normalizer A hx) hQ

theorem not_three_dvd_card_qStar
    (htr : ∀ Q₁ ∈ scriptQPiStar A (lB A) ⊤ (piOf p), ∀ Q₂ ∈ scriptQPiStar A (lB A) ⊤ (piOf p),
      IsConjIn (xA A) Q₁ Q₂)
    {Q : Subgroup G} (hQ : Q ∈ scriptQPiStar A (lB A) ⊤ (piOf p)) :
    ¬ 3 ∣ Nat.card (scriptQPiStar A (lB A) ⊤ (piOf p)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [Nat.card_coe_set_eq, qStar_eq_conj htr hQ]
  intro h3
  exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp
    (coprime_card_pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)))
    (h3.trans (ncard_conj_dvd (xA A) Q))

omit [Finite G] in
theorem three_dvd_card_of_mem {L : Subgroup G} {w : G} (hwL : w ∈ L) (hw : orderOf w = 3) :
    3 ∣ Nat.card L := by
  have := orderOf_dvd_natCard (⟨w, hwL⟩ : L)
  rwa [Subgroup.orderOf_mk, hw] at this

omit [Finite G] in
theorem normalizerMonoidHom_inv_mul_eq {g x : G} (hg : g ∈ Subgroup.normalizer (A : Set G))
    (hx : x ∈ Subgroup.centralizer (A : Set G))
    (hxg : x⁻¹ * g ∈ Subgroup.normalizer (A : Set G)) :
    A.normalizerMonoidHom ⟨x⁻¹ * g, hxg⟩ = A.normalizerMonoidHom ⟨g, hg⟩ := by
  ext a
  rw [Sec4.normalizerMonoidHom_apply_coe, Sec4.normalizerMonoidHom_apply_coe]
  have hga : g * (a : G) * g⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.mp hg a).mp a.2
  have hcomm : x⁻¹ * (g * a * g⁻¹) = g * a * g⁻¹ * x⁻¹ :=
    (Subgroup.mem_centralizer_iff.mp (inv_mem hx) _ hga).symm
  calc x⁻¹ * g * (a : G) * (x⁻¹ * g)⁻¹ = x⁻¹ * (g * a * g⁻¹) * x := by group
    _ = g * a * g⁻¹ := by rw [hcomm, inv_mul_cancel_right]

end Para

end CFSG.RankThree.PartTwo.Sec17
