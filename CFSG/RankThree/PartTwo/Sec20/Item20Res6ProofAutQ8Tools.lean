module

import CFSG.RankThree.PartTwo.Sec20.Item20Res6ProofTools
import CFSG.RankThree.PartTwo.Sec20.Item20Res5ProofCyclic
import CFSG.RankThree.PartTwo.Sec18.Tools
public import CFSG.RankThree.PartTwo.Sec20.OneTools

public section

namespace CFSG.RankThree.PartTwo.Sec20

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late
open CFSG.ABGLocalTools (IsSylowOf)

namespace Res6

variable {G : Type} [Group G]

@[expose] def cenK (K : Subgroup G) : Subgroup G where
  carrier := {m | m ∈ Subgroup.normalizer (K : Set G) ∧
    ∀ k ∈ K, m * k * m⁻¹ * k⁻¹ ∈ CFSG.Open.pCoreOf 2 K}
  mul_mem' := by
    rintro x y ⟨hxN, hx⟩ ⟨hyN, hy⟩
    refine ⟨mul_mem hxN hyN, fun k hk => ?_⟩
    have hxO := CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K hxN
    have h1 := (Subgroup.mem_normalizer_iff.mp hxO _).mp (hy k hk)
    have e : x * y * k * (x * y)⁻¹ * k⁻¹ =
        (x * (y * k * y⁻¹ * k⁻¹) * x⁻¹) * (x * k * x⁻¹ * k⁻¹) := by group
    rw [e]
    exact Subgroup.mul_mem _ h1 (hx k hk)
  one_mem' := ⟨Subgroup.one_mem _, fun k _ => by
    rw [show (1 : G) * k * 1⁻¹ * k⁻¹ = 1 by group]
    exact Subgroup.one_mem _⟩
  inv_mem' := by
    rintro z ⟨hzN, hz⟩
    refine ⟨inv_mem hzN, fun y hy => ?_⟩
    have hy' : z⁻¹ * y * z⁻¹⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp (inv_mem hzN) y).mp hy
    have h1 := Subgroup.inv_mem _ (hz _ hy')
    have e : (z * (z⁻¹ * y * z⁻¹⁻¹) * z⁻¹ * (z⁻¹ * y * z⁻¹⁻¹)⁻¹)⁻¹ = z⁻¹ * y * z⁻¹⁻¹ * y⁻¹ := by
      group
    rwa [e] at h1

theorem conj_mem_cenK {K : Subgroup G} {g x : G} (hg : g ∈ Subgroup.normalizer (K : Set G))
    (hx : x ∈ cenK K) : g * x * g⁻¹ ∈ cenK K := by
  obtain ⟨hxN, hx⟩ := hx
  refine ⟨mul_mem (mul_mem hg hxN) (inv_mem hg), fun k hk => ?_⟩
  have hgO := CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K hg
  have hk' : g⁻¹ * k * g⁻¹⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp (inv_mem hg) k).mp hk
  have h1 := (Subgroup.mem_normalizer_iff.mp hgO _).mp (hx _ hk')
  have e : g * (x * (g⁻¹ * k * g⁻¹⁻¹) * x⁻¹ * (g⁻¹ * k * g⁻¹⁻¹)⁻¹) * g⁻¹ =
      g * x * g⁻¹ * k * (g * x * g⁻¹)⁻¹ * k⁻¹ := by group
  rwa [e] at h1

theorem normalizer_le_normalizer_cenK (K : Subgroup G) :
    Subgroup.normalizer (K : Set G) ≤ Subgroup.normalizer (cenK K : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · exact conj_mem_cenK hg
  · intro hx
    have := conj_mem_cenK (inv_mem hg) hx
    simpa [mul_assoc] using this

theorem exists_conj_eq_of_sup [Finite G] {M B : Subgroup G} (hB3 : IsPGroup 3 B) (hBM : B ≤ M)
    (hBn : M ≤ Subgroup.normalizer ((B ⊔ CFSG.Open.pCoreOf 2 M : Subgroup G) : Set G))
    {g : G} (hg : g ∈ M) :
    ∃ o ∈ CFSG.Open.pCoreOf 2 M,
      B.map (MulAut.conj g).toMonoidHom = B.map (MulAut.conj o).toMonoidHom := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set O := CFSG.Open.pCoreOf 2 M with hO
  have hO2 : IsPGroup 2 O := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M
  have hBO : B ≤ Subgroup.normalizer (O : Set G) :=
    hBM.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M)
  have hO3 : ¬ 3 ∣ Nat.card O :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp
      (coprime_card_of_isPGroup Nat.prime_three (by norm_num) hO2)
  have hsyl : IsSylowOf 3 B (B ⊔ O) := Sec20.isSylowOf_sup_of_coprime hB3 hO3 hBO
  have hgP : (B.map (MulAut.conj g).toMonoidHom) ≤ B ⊔ O := by
    have := Late.map_conj_eq_of_mem_normalizer (hBn hg)
    rw [← this]
    exact Subgroup.map_mono le_sup_left
  have hsyl' : IsSylowOf 3 (B.map (MulAut.conj g).toMonoidHom) (B ⊔ O) := by
    apply CFSG.ABGLocalTools.isSylowOf_of_card hgP
    rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]
    exact hsyl.card_eq
  obtain ⟨y, hy, hyeq⟩ := Sec18.exists_map_conj_eq_of_isSylowOf hsyl hsyl'
  have hy' : y ∈ ((O ⊔ B : Subgroup G) : Set G) := by rw [sup_comm]; exact hy
  rw [Subgroup.coe_mul_of_right_le_normalizer_left O B hBO] at hy'
  obtain ⟨o, ho, b, hb, hyob⟩ := hy'
  refine ⟨o, ho, ?_⟩
  have hyob' : y = o * b := hyob.symm
  rw [hyeq, hyob', ← Res5.map_conj_map_conj, Late.map_conj_eq_of_mem_normalizer
    (Subgroup.le_normalizer hb)]

end Res6

end CFSG.RankThree.PartTwo.Sec20
