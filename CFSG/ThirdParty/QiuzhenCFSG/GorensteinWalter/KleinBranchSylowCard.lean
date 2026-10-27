module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CardSupOfDisjointNormalizer
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Theorem26
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# Sylow order in the Klein-four / D6 centralizer branch
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

/-- A Klein internal two-core and the `D6` quotient from Theorem 2.6 force
the distinguished Sylow `2`-subgroup to have order eight. -/
public theorem sylow_card_eight_of_klein_twoCore_and_d6_quotient
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G)
    (hklein : IsKleinFour (pCore 2 c.Hhat))
    (hq : Nonempty
      ((c.Hhat ⧸ (pCore 2 c.Hhat ⊔ pPrimeCore 2 c.Hhat)) ≃*
        DihedralGroup 3)) :
    Nat.card (↑(c.S : Subgroup G)) = 8 := by
  classical
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let H : Subgroup G := c.Hhat
  let N : Subgroup H := pCore 2 H
  let O : Subgroup H := pPrimeCore 2 H
  let K : Subgroup H := N ⊔ O
  have : N.Normal := by
    dsimp [N, H]
    infer_instance
  have : O.Normal := by
    dsimp [O, H]
    infer_instance
  have : K.Normal := by
    dsimp [K, N, O, H]
    infer_instance
  have hNcard : Nat.card N = 4 := hklein.card_four
  have hOcop : Nat.Coprime 2 (Nat.card O) := by
    simpa [O] using pPrimeCore_coprime_card (p := 2) (G := H)
  have hOodd : Odd (Nat.card O) := Nat.coprime_two_left.mp hOcop
  have hNp : IsPGroup 2 N := by
    simpa [N] using (pCore_isPGroup (G := H) (p := 2))
  have hNdisjO : Disjoint N O := by
    rcases (IsPGroup.iff_card (p := 2) (G := N)).mp hNp with ⟨n, hn⟩
    have hcop : Nat.Coprime (Nat.card N) (Nat.card O) := by
      rw [hn]
      exact hOcop.pow_left n
    exact Subgroup.disjoint_of_coprime_natCard hcop
  have hOleN : O ≤ Subgroup.normalizer (N : Set H) := by
    have : N.Normal := by infer_instance
    simp [Subgroup.normalizer_eq_top]
  have hKcard : Nat.card K = Nat.card N * Nat.card O :=
    card_sup_eq_mul_of_disjoint_of_le_normalizer N O hOleN hNdisjO
  have hq' : Nonempty ((H ⧸ K) ≃* DihedralGroup 3) := by
    simpa [H, N, O, K] using hq
  obtain ⟨eq⟩ := hq'
  have hQcard : Nat.card (H ⧸ K) = 6 := by
    calc
      Nat.card (H ⧸ K) = Nat.card (DihedralGroup 3) :=
        Nat.card_congr eq.toEquiv
      _ = 2 * 3 := DihedralGroup.nat_card
      _ = 6 := by norm_num
  have hHcard : Nat.card H = 24 * Nat.card O := by
    have hKindex : K.index = Nat.card (H ⧸ K) := by
      rw [Subgroup.index_eq_card]
    have hmul := K.card_mul_index
    change Nat.card K * K.index = Nat.card H at hmul
    rw [hKcard, hKindex, hQcard, hNcard] at hmul
    calc
      Nat.card H = (4 * Nat.card O) * 6 := hmul.symm
      _ = 24 * Nat.card O := by ring
  have hfact : (Nat.card H).factorization 2 = 3 := by
    rw [hHcard]
    have hOnot : ¬ 2 ∣ Nat.card O := hOodd.not_two_dvd_nat
    have h24 : (24 : ℕ).factorization 2 = 3 := by
      rw [show (24 : ℕ) = 2 ^ 3 * 3 by norm_num]
      rw [Nat.factorization_mul (by norm_num) (by norm_num)]
      rw [Nat.factorization_pow]
      simp [Nat.prime_two.factorization_self,
        Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 2 ∣ 3)]
    have hOcard_ne : Nat.card O ≠ 0 := Nat.card_pos.ne'
    rw [Nat.factorization_mul (by norm_num : (24 : ℕ) ≠ 0) hOcard_ne]
    simp [h24, Nat.factorization_eq_zero_of_not_dvd hOnot]
  have hSleHhat : (c.S : Subgroup G) ≤ c.Hhat :=
    (centralizerSetup_S_le_H c).trans c.H_le_Hhat
  let P : Sylow 2 (↑c.Hhat) := c.S.subtype hSleHhat
  have hPcard : Nat.card (P : Subgroup (↑c.Hhat)) =
      2 ^ (Nat.card (↑c.Hhat)).factorization 2 := by
    simpa using (Sylow.card_eq_multiplicity (G := ↑c.Hhat) (p := 2) P)
  have hPcard' : Nat.card (P : Subgroup (↑c.Hhat)) =
      Nat.card (c.S : Subgroup G) := by
    calc
      Nat.card (P : Subgroup (↑c.Hhat)) =
          Nat.card ((c.S : Subgroup G).subgroupOf c.Hhat) := by
            simp [P]
      _ = Nat.card (c.S : Subgroup G) := by
        exact Nat.card_congr
          (Subgroup.subgroupOfEquivOfLe hSleHhat).toEquiv
  rw [hPcard, hfact] at hPcard'
  norm_num at hPcard'
  exact hPcard'.symm

end CFSG.GorensteinWalter
