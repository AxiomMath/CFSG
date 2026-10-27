module

public import CFSG.Quasithin.Vol2.GoldschmidtF134OddDickson
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeBasicBase
public import CFSG.Quasithin.Background.F420Orders

public section

namespace CFSG.Quasithin.H13.NQCore

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open CFSG.QuasithinUnique.Vol2Native
open scoped MatrixGroups

theorem psl2_borel_data {A : Type} [Group A] [Finite A]
    {L B U : Subgroup A} {m p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hL : IsPSL 2 2 m ↥L)
    (hUB : U ≤ B) (hBL : B ≤ L) (hU : IsSylowTwoOf U L)
    (hB : ∀ q : ℕ, q.Prime → q ∣ Nat.card B → q = 2 ∨ q = p) {y : A} (hy : y ∈ B)
    (hyo : orderOf y = p) : p ∣ 2 ^ m - 1 ∧ B ≤ Subgroup.normalizer (U : Set A) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨⟨-, hm1, -, h22, -⟩, -⟩ := id hL
  have hm : 2 ≤ m := by
    by_contra h
    have : m = 1 := by omega
    subst this
    exact h22 (by norm_num)
  have hcardL := CFSG.Quasithin.F420.card_of_statedPSL_two_two hL
  obtain ⟨e⟩ := nonempty_mulEquiv_psl2_odd hL
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hU.2.1
  have hodd4 : Odd (4 ^ m - 1) := Nat.odd_iff.mpr (by
    have h1 : 1 ≤ 4 ^ m := Nat.one_le_pow _ _ (by norm_num)
    have h2 : 2 ∣ 4 ^ m := dvd_pow (by norm_num) (by omega)
    omega)
  have hidx := (U.subgroupOf L).card_mul_index
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hU.1).toEquiv, hk, hcardL] at hidx
  have hcop : Nat.Coprime (2 ^ m) (U.subgroupOf L).index :=
    Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr (Nat.odd_iff.mpr (by
      have := hU.2.2
      omega)))
  have h2U : 2 ^ m ∣ Nat.card U := by
    rw [hk]
    exact hcop.dvd_of_dvd_mul_right (hidx ▸ Dvd.intro _ rfl)
  have hUm : Nat.card U = 2 ^ m := by
    have hdvd : Nat.card U ∣ 2 ^ m * (4 ^ m - 1) := hcardL ▸ Subgroup.card_dvd_of_le hU.1
    rw [hk] at hdvd h2U ⊢
    have hcop2 : Nat.Coprime (2 ^ k) (4 ^ m - 1) :=
      Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hodd4)
    have h1 : 2 ^ k ∣ 2 ^ m := hcop2.dvd_of_dvd_mul_right hdvd
    have hkm : k ≤ m := (Nat.pow_dvd_pow_iff_le_right (by norm_num)).1 h1
    have hmk : m ≤ k := (Nat.pow_dvd_pow_iff_le_right (by norm_num)).1 h2U
    rw [le_antisymm hkm hmk]
  let φ : B →* PSL(2, GaloisField 2 m) := e.toMonoidHom.comp (Subgroup.inclusion hBL)
  have hφ : Function.Injective φ := e.injective.comp (Subgroup.inclusion_injective hBL)
  have hrφ : Function.Injective φ.rangeRestrict := fun a b h => hφ (congrArg Subtype.val h)
  have hH : Nat.card φ.range = Nat.card B :=
    (Nat.card_congr (MonoidHom.ofInjective hφ).toEquiv).symm
  have h2H : 2 ^ m ∣ Nat.card φ.range := by
    rw [hH, ← hUm]
    exact Subgroup.card_dvd_of_le hUB
  have hpH : p ∣ Nat.card φ.range := by
    rw [hH, ← hyo]
    exact Subgroup.orderOf_dvd_natCard B hy
  obtain ⟨hpd, hnorm⟩ := psl2_borel_core hm hp hp5 φ.range h2H hpH (hH ▸ hB)
  have hS : Nat.card ((U.subgroupOf B).map φ.rangeRestrict) = 2 ^ m := by
    rw [Subgroup.card_map_of_injective hrφ,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUB).toEquiv, hUm]
  have hSn := hnorm _ hS
  have key : ∀ b ∈ B, ∀ u ∈ U, b * u * b⁻¹ ∈ U := by
    intro b hb u hu
    have hu' : (⟨u, hUB hu⟩ : B) ∈ U.subgroupOf B := hu
    have hmem := hSn.conj_mem _ (Subgroup.mem_map_of_mem φ.rangeRestrict hu')
      (φ.rangeRestrict ⟨b, hb⟩)
    obtain ⟨w, hw, hweq⟩ := hmem
    have hwe : w = ⟨b, hb⟩ * ⟨u, hUB hu⟩ * ⟨b, hb⟩⁻¹ := by
      apply hrφ
      rw [hweq, map_mul, map_mul, map_inv]
    have hw' : (w : A) ∈ U := hw
    rw [hwe] at hw'
    exact hw'
  refine ⟨hpd, fun b hb => ?_⟩
  rw [Subgroup.mem_normalizer_iff]
  intro u
  refine ⟨fun hu => key b hb u hu, fun hbu => ?_⟩
  have := key b⁻¹ (B.inv_mem hb) _ hbu
  simpa [mul_assoc] using this

theorem facts134Odd_psl2Borel :
    ∀ (A : Type) [Group A] [Finite A] (L B U : Subgroup A) (m p : ℕ) (y : A),
      SQTKHypCat A → p.Prime → 5 ≤ p → IsPSL 2 2 m ↥L → U ≤ B → B ≤ L → IsSylowTwoOf U L →
      (∀ q : ℕ, q.Prime → q ∣ Nat.card B → q = 2 ∨ q = p) → y ∈ B → orderOf y = p →
      p ∣ 2 ^ m - 1 :=
  fun _ _ _ _ _ _ _ _ _ _ hp hp5 hL hUB hBL hU hB hy hyo =>
    (psl2_borel_data hp hp5 hL hUB hBL hU hB hy hyo).1

end CFSG.Quasithin.H13.NQCore
