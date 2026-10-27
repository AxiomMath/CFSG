module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.ThreeD4TwoSevenLines
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.ThreeD4TwoOrderFacts
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434D42Link
public import CFSG.Sporadic.SuzOddCore.OddCoreLines
public import CFSG.GroupTheory.PGroup.ElemAbelianSq
public import CFSG.GroupTheory.GL52.SylowTools

public section


namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.AGLEmbedding.D4Two CFSG.Quasithin CFSG.Quasithin.H13.D42
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.D4SevenLines

theorem k_3D4TwoSevenNormalizer_holds :
    Inputs1719.K_3D4TwoSevenNormalizer := by
  classical
  intro K _ _ hK x hx
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  obtain ⟨e⟩ := CFSG.LargeExtraspecial.S63.nonempty_equiv_trialityGroup8 K hK
  have hcard : Nat.card K = 211341312 := Inputs1719.card_eq_of_is3D4_one hK
  have hx1 : x ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hx
    exact absurd hx (by norm_num)
  apply le_antisymm
  ·
    by_contra hlt
    push Not at hlt
    obtain ⟨E, -, hE, hE9⟩ := CFSG.SectionRank.exists_isElemAbelian_card_of_le_pRank
      (p := 3) (k := 2) (H := (⊤ : Subgroup ↥(Subgroup.normalizer (Subgroup.zpowers x : Set K))))
      hlt
    have hW := CFSG.RankThree.PartTwo.Sec4.Item434D42.d4_k3_of_equiv e hcard
      (E := E.map (Subgroup.normalizer (Subgroup.zpowers x : Set K)).subtype)
      (W := Subgroup.zpowers x) (CFSG.SectionRank.isElemAbelian_map hE _)
      (by rw [Subgroup.card_map_of_injective Subtype.val_injective, hE9]; norm_num)
      (by rw [Nat.card_zpowers, hx]; norm_num) (Subgroup.map_subtype_le E)
    exact hx1 (Subgroup.zpowers_eq_bot.mp hW)
  ·
    set P : Subgroup ↥trialityGroup8 := Subgroup.zpowers hD ⊔ Subgroup.zpowers zD with hPdef
    set PK : Subgroup K := P.map e.symm.toMonoidHom with hPKdef
    have hPK : Nat.card PK = 7 ^ 2 := by
      rw [hPKdef, Subgroup.card_map_of_injective e.symm.injective, hPdef, card_P]
      norm_num
    have hidx : ¬ 7 ∣ PK.index := by
      have h1 := Subgroup.card_mul_index PK
      rw [hPK, hcard] at h1
      have h2 : PK.index = 4313088 := by omega
      rw [h2]
      norm_num
    let S : Sylow 7 K := (IsPGroup.of_card hPK).toSylow hidx
    obtain ⟨c, hc⟩ := CFSG.Sporadic.SuzOddCore.exists_conj_mem_sylow_of_orderOf S hx
    have hc' : c * x * c⁻¹ ∈ PK := hc
    obtain ⟨y, hyP, hy⟩ := Subgroup.mem_map.mp hc'
    obtain ⟨w, m, hw, hw3, hw1⟩ := exists_conj_pow_of_mem hyP
    have hxy : x = c⁻¹ * e.symm y * c := by
      have hy' : e.symm y = c * x * c⁻¹ := hy
      rw [hy']
      group
    have hconj : ∀ (b : K) (n : ℕ), (c⁻¹ * b * c) ^ n = c⁻¹ * b ^ n * c := fun b n => by
      simpa only [inv_inv] using (conj_pow (a := c⁻¹) (b := b) (i := n))
    set t : K := c⁻¹ * e.symm w * c with htdef
    have htx : t * x * t⁻¹ = x ^ m := by
      have h1 : t * x * t⁻¹ = c⁻¹ * e.symm (w * y * w⁻¹) * c := by
        rw [htdef, hxy, map_mul, map_mul, map_inv]
        group
      rw [h1, hw, map_pow, hxy, hconj]
    have htN : t ∈ Subgroup.normalizer (Subgroup.zpowers x : Set K) :=
      CFSG.GroupTheory.GL52.mem_normalizer_zpowers_of_conj_mem (by
        rw [htx]
        exact Subgroup.pow_mem _ (Subgroup.mem_zpowers x) m)
    have ht3 : t ^ 3 = 1 := by
      rw [htdef, hconj, ← map_pow, hw3, map_one, mul_one, inv_mul_cancel]
    have ht1 : t ≠ 1 := by
      intro h
      apply hw1
      have h2 : e.symm w = 1 := by
        rw [htdef] at h
        calc e.symm w = c * (c⁻¹ * e.symm w * c) * c⁻¹ := by group
          _ = 1 := by rw [h]; group
      simpa using congrArg e h2
    have hord : orderOf (⟨t, htN⟩ : ↥(Subgroup.normalizer (Subgroup.zpowers x : Set K))) = 3 :=
      orderOf_eq_prime (Subtype.ext ht3) (fun h => ht1 (congrArg Subtype.val h))
    have hcard3 : Nat.card ↥(Subgroup.zpowers
        (⟨t, htN⟩ : ↥(Subgroup.normalizer (Subgroup.zpowers x : Set K)))) = 3 := by
      rw [Nat.card_zpowers, hord]
    exact CFSG.SectionRank.le_pRank (by norm_num) le_top
      (CFSG.GroupTheory.isElemAbelian_of_card_prime hcard3) (by rw [hcard3, pow_one])
