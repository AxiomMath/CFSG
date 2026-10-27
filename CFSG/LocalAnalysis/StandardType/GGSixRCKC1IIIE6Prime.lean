module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeConfigID
import CFSG.LocalAnalysis.StandardType.GGSixFieldFiveTagsRank
import CFSG.LocalAnalysis.AGLEmbedding.SurvivorBlockInner
import Mathlib.Tactic.NormNum

public section

namespace CFSG.Open

theorem eq_two_or_three_of_pow_four_dvd_ordE6_two {p : ℕ} (hp : p.Prime)
    (hd : p ^ 4 ∣ ordE6 2) : p = 2 ∨ p = 3 := by
  have hf : ordE6 2 = 2 ^ 36 * 3 ^ 6 * 5 ^ 2 * 7 ^ 3 * 13 * 17 * 31 * 73 := by
    norm_num [ordE6]
  have hpd : p ∣ 2 ^ 36 * 3 ^ 6 * 5 ^ 2 * 7 ^ 3 * 13 * 17 * 31 * 73 := by
    rw [← hf]
    exact (dvd_pow_self p (by decide : 4 ≠ 0)).trans hd
  simp only [hp.dvd_mul, or_assoc] at hpd
  have heq {q k : ℕ} (hq : q.Prime) (h : p ∣ q ^ k) : p = q :=
    (Nat.prime_dvd_prime_iff_eq hp hq).mp (hp.dvd_of_dvd_pow h)
  rcases hpd with h2 | h3 | h5 | h7 | h13 | h17 | h31 | h73
  · exact Or.inl (heq Nat.prime_two h2)
  · exact Or.inr (heq (by decide) h3)
  · have : p = 5 := heq (by decide) h5
    subst p
    norm_num [ordE6] at hd
  · have : p = 7 := heq (by decide) h7
    subst p
    norm_num [ordE6] at hd
  · have : p = 13 := (Nat.prime_dvd_prime_iff_eq hp (by decide)).mp h13
    subst p
    norm_num [ordE6] at hd
  · have : p = 17 := (Nat.prime_dvd_prime_iff_eq hp (by decide)).mp h17
    subst p
    norm_num [ordE6] at hd
  · have : p = 31 := (Nat.prime_dvd_prime_iff_eq hp (by decide)).mp h31
    subst p
    norm_num [ordE6] at hd
  · have : p = 73 := (Nat.prime_dvd_prime_iff_eq hp (by decide)).mp h73
    subst p
    norm_num [ordE6] at hd

end CFSG.Open

namespace CFSG.StandardType.RCKC1

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.StandardType

theorem pow_dvd_card_of_faithful_inner_of_isElemAbelian {X : Type} [Group X] [Finite X]
    {p k : ℕ} (hp : p.Prime) {G₀ A : Subgroup X} (hA : IsElemAbelian p A)
    (hAN : A ≤ Subgroup.normalizer (G₀ : Set X))
    (hfaith : A ⊓ Subgroup.centralizer (G₀ : Set X) = ⊥)
    (hinner : ∀ a ∈ A, ∃ g ∈ G₀, a * g ∈ Subgroup.centralizer (G₀ : Set X))
    (hk : p ^ k ≤ Nat.card A) : p ^ k ∣ Nat.card G₀ := by
  have hAG : Nat.card A ∣ Nat.card G₀ :=
    CFSG.AGLEmbedding.card_dvd_of_faithful_inner hAN Subgroup.le_normalizer hfaith
      fun a ha => by
        obtain ⟨g, hg, hag⟩ := hinner a ha
        exact ⟨g⁻¹, G₀.inv_mem hg, by simpa only [inv_inv] using hag⟩
  have hpow : p ^ k ∣ Nat.card A :=
    CFSG.RankThree.PartOne.Planes.pow_dvd_card_of_le_card hp
      (CFSG.Open.isElemAbelian_iff_isElementaryAbelian.mp hA) hk
  exact hpow.trans hAG


theorem prime_eq_three_of_e6_two_innerDiag
    {X : Type} [Group X] [Finite X] {n p : ℕ}
    {ψ : (ggU .E6 n 1).K →* X} {G₀ A : Subgroup X}
    (hpres : GGPresentsG0 G₀ (ggU .E6 n 1).D .E6 n 1 ψ)
    (hp : p.Prime) (hp2 : p ≠ 2) (hA : IsElemAbelian p A)
    (hAN : A ≤ Subgroup.normalizer (G₀ : Set X))
    (hdiag : ∀ a ∈ A, GGPsiInnerDiag (ggU .E6 n 1).D ψ a)
    (hfaith : A ⊓ Subgroup.centralizer (G₀ : Set X) = ⊥)
    (h4 : p ^ 4 ≤ Nat.card A) : p = 3 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hrange : ψ.range = G₀ := hpres.2.1.1
  have hfield : Nat.card (GaloisField 2 1) = 2 := by
    rw [GaloisField.card 2 1 one_ne_zero, pow_one]
  let ψE : ↥(CFSG.LieType.Steinberg.Minuscule.e6Data_valid.minGroup
      (GaloisField 2 1)) →* X := ψ
  have hrangeE : ψE.range = G₀ := hrange
  have hkerE : ψE.ker ≤ Subgroup.center ↥(CFSG.LieType.Steinberg.Minuscule.e6Data_valid.minGroup
      (GaloisField 2 1)) := hpres.2.1.2
  have hinner : ∀ a ∈ A, ∃ g ∈ G₀, a * g ∈ Subgroup.centralizer (G₀ : Set X) := by
    intro a ha
    obtain ⟨g, hg, hag⟩ := exists_mem_centralizer_E6_two hfield ψE hkerE (hdiag a ha)
    exact ⟨g, hrangeE ▸ hg, hrangeE ▸ hag⟩
  have hZ : Subgroup.center ↥(CFSG.LieType.Steinberg.Minuscule.e6Data_valid.minGroup
      (GaloisField 2 1)) = ⊥ := by
    rw [← Subgroup.card_eq_one,
      (CFSG.LieType.Steinberg.CentralExt.MinusculeClosed.card_center_e6 (GaloisField 2 1)).1,
      hfield]
    rfl
  have hinj : Function.Injective (CFSG.LieType.Steinberg.Isogeny.e6Isogeny (GaloisField 2 1)) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff, ← hZ]
    exact CFSG.ClassicalInvolution.ModelFacts.ChevAut.e6Isogeny_ker_le_center (GaloisField 2 1)
  have horder : Nat.card ↥(CFSG.Blueprint.Chevalley.adjointGroup .E6 (GaloisField 2 1)) =
      CFSG.Open.ordE6 2 := by
    rw [CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_E6, hfield]
  have hU : Nat.card (ggU .E6 n 1).K ∣ CFSG.Open.ordE6 2 := by
    show Nat.card ↥(CFSG.LieType.Steinberg.Minuscule.e6Data_valid.minGroup
      (GaloisField 2 1)) ∣ _
    rw [← horder, Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv]
    exact Subgroup.card_subgroup_dvd_card _
  have hd : p ^ 4 ∣ CFSG.Open.ordE6 2 :=
    (pow_dvd_card_of_faithful_inner_of_isElemAbelian hp hA hAN hfaith hinner h4).trans
      ((hrange ▸ Subgroup.card_range_dvd ψ).trans hU)
  exact (CFSG.Open.eq_two_or_three_of_pow_four_dvd_ordE6_two hp hd).resolve_left hp2

theorem prime_eq_three_of_e6_two_compConfig
    {X : Type} [Group X] [Finite X] {n p : ℕ}
    {ψ : (ggU .E6 n 1).K →* X} {G₀ A B₁ D J L K : Subgroup X} {e : X}
    (h : RCKRP.RCKCompConfig .E6 n 1 ψ p G₀ A B₁ D J L K e) : p = 3 := by
  have hdiag := RCKRP.rckRPConfigInnerDiag_holds X .E6 n 1 ψ p G₀ A B₁ D J L K e h
  obtain ⟨hpres, -, hp, hp2, hA, hBA, -, -, hAN, -, -, -, hB4, -, -, hfaith, -⟩ := h
  exact prime_eq_three_of_e6_two_innerDiag hpres hp hp2 hA hAN hdiag hfaith
    (hB4.trans (Nat.le_of_dvd (Nat.card_pos : 0 < Nat.card A) (Subgroup.card_dvd_of_le hBA)))

end CFSG.StandardType.RCKC1
