module

public import CFSG.Quasithin.Vol2.GoldschmidtF134OddLieF4Embed
public import CFSG.Quasithin.Vol2.GoldschmidtF134OddLieF4Elem
public import CFSG.Quasithin.Vol2.GoldschmidtF134OddLieF4Arith
public import CFSG.Quasithin.Vol2.GoldschmidtF134OddLieS5
import CFSG.Quasithin.Vol2.F134LieF4Borel
import CFSG.LieType.BorelTits.Ree

set_option linter.unusedSectionVars false

public section

open CFSG.LieType.Chevalley CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag CFSG.Blueprint
  CFSG.Blueprint.Chevalley CFSG.ABGLocalTools CFSG.QuasithinUnique.Setup.X6
  CFSG.Assembly.LowTwoRank CFSG.Quasithin.F134.LieF4

namespace CFSG.Quasithin.H13.NQCore.F4


theorem le_normalizer_of_card_eq {X : Type} [Group X] [Finite X] {n : ℕ}
    (hX : ReeTitsModel X .twistedF4 2 n) {p a : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (ha : a = 2 ∨ a = 3) {S H : Subgroup X} (hS : CFSG.QuasithinUnique.IsSylowTwoOf S ⊤)
    (hSH : S ≤ H) (hH : Nat.card H = p ^ a * Nat.card S) :
    H ≤ Subgroup.normalizer (S : Set X) := by
  obtain ⟨b, K, _, _, _, φ, hb, hn, hK, hφi, hφr, hφS⟩ := exists_embedding hX hS
  have hK' : Nat.card K = 2 ^ (2 * b + 1) := hn ▸ hK
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (ModGL F4.tag K) := finite_modGL
  have hp2 : p ≠ 2 := by omega
  have hU' : IsSylowOf 2 S ⊤ := isSylowTwoOf_iff_isSylowOf.1 hS
  obtain ⟨E₀, hE₀U, hE₀2, hE₀c⟩ := exists_elementaryAbelian_reeFixedPosUnipotent (a := b) hK'
  have hq8 : 8 ≤ Nat.card K := by
    rw [hK']
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ (2 * b + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hE₀Γ : E₀ ≤ φ.range := hφr ▸ hE₀U.trans reeFixedPosUnipotent_le_reeGamma
  have hES : E₀.comap φ ≤ S := by
    intro x hx
    obtain ⟨s, hs, hsx⟩ : φ x ∈ S.map φ := hφS ▸ hE₀U hx
    rwa [← hφi hsx]
  have hEcard : Nat.card (E₀.comap φ) = Nat.card E₀ := by
    rw [← Subgroup.card_map_of_injective hφi, Subgroup.map_comap_eq_self hE₀Γ]
  have hE2 : ∀ x ∈ E₀.comap φ, x ^ 2 = 1 := fun x hx => hφi (by
    rw [map_pow, map_one]
    exact hE₀2 _ hx)
  have hE16 : 16 ≤ Nat.card (E₀.comap φ) := by
    rw [hEcard]
    calc 16 ≤ 8 ^ 2 := by norm_num
      _ ≤ Nat.card K ^ 2 := Nat.pow_le_pow_left hq8 2
      _ ≤ Nat.card E₀ := hE₀c
  have hBT : CFSG.LieType.BorelTits.Holds X 2 :=
    CFSG.LieType.BorelTits.holds_of_reeTitsModel hX (by decide)
  obtain ⟨m, hm⟩ : ∃ m, Nat.card S = 2 ^ m := (IsPGroup.iff_card).1 hS.2.1
  obtain ⟨Q, hQ, hHQ, hNQ⟩ := CFSG.Quasithin.H13.NQCore.S5.exists_proper_overgroup hBT hU' hSH
    (hES.trans hSH) hE2 hE16 hp hp2 (m := m) (a := a) (by rw [hH, hm, mul_comm]) (by omega)
  have hBQ : F4.reeFixedBorel K b ≤ Q.map φ := by
    intro y hy
    obtain ⟨x, rfl⟩ : y ∈ φ.range := hφr ▸ reeFixedBorel_le_reeGamma hy
    exact ⟨x, hNQ ((mem_normalizer_iff_mem_reeFixedBorel hφi hφr hφS x).2 hy), rfl⟩
  have hQΓ : Q.map φ ≤ F4.reeGamma K b := hφr ▸ Subgroup.map_le_range φ Q
  have hQne : Q.map φ ≠ F4.reeGamma K b := by
    intro h
    apply hQ
    apply Subgroup.map_injective hφi
    rw [h, ← MonoidHom.range_eq_map, hφr]
  obtain ⟨i, hi⟩ := exists_le_reeLocalParabolic hBQ hQΓ hQne
  have hUH : F4.reeFixedPosUnipotent K b ≤ H.map φ := hφS ▸ Subgroup.map_mono hSH
  rcases le_reeFixedBorel_or_dvd ((Subgroup.map_mono hHQ).trans hi) hUH with hB | hdvd
  · exact fun h hh => (mem_normalizer_iff_mem_reeFixedBorel hφi hφr hφS h).2 (hB ⟨h, hh, rfl⟩)
  exfalso
  have hrel : (F4.reeFixedPosUnipotent K b).relIndex (H.map φ) = p ^ a := by
    have hcardH : Nat.card (H.map φ) = p ^ a * Nat.card (F4.reeFixedPosUnipotent K b) := by
      rw [Subgroup.card_map_of_injective hφi, hH, ← hφS, Subgroup.card_map_of_injective hφi]
    have h := Subgroup.relIndex_mul_card (F4.reeFixedPosUnipotent K b) (H.map φ)
    rw [inf_eq_left.2 hUH, hcardH] at h
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h
  rw [hrel] at hdvd
  obtain ⟨i, hi2⟩ := i
  have hi2' : i < 2 := hi2
  interval_cases i
  · rw [card_reeFixedOrbitUnipotent_zero hK', hK'] at hdvd
    exact two_pow_add_one_not_dvd_prime_pow hp hp5 hdvd
  · rw [card_reeFixedOrbitUnipotent_one hK', hK'] at hdvd
    exact two_pow_sq_add_one_not_dvd_prime_pow hp hb hdvd

end CFSG.Quasithin.H13.NQCore.F4
