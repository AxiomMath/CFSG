module

public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSAPairAux
import CFSG.LieType.Universal.Unitary.Comparison
import CFSG.LieType.Steinberg.CentralExt.SUTwo
import CFSG.ClassicalInvolution.Phan.Center
import CFSG.ClassicalInvolution.Phan.StandardPair

public section

namespace CFSG.StandardType

open CFSG.ClassicalInvolution.Phan CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits Matrix
open scoped MatrixGroups

theorem ggPhanNSAPairAux_card_su_two (K : Type) [Field K] [Finite K] (p f : ℕ)
    [Fact p.Prime] [CharP K p] (hK : Nat.card K = (p ^ f) ^ 2) :
    Nat.card (Su K p f 2) = p ^ f * ((p ^ f) ^ 2 - 1) := by
  obtain ⟨P, hP⟩ := exists_wittMatrix (F := K) (p := p) (f := f) hK 2
  rw [← Nat.card_congr (conjEquiv P hP).toEquiv]
  exact CFSG.LieType.Steinberg.card_SU_two hK

theorem ggPhanNSAPairAux_card_map_pair {K : Type} [Field K] [Finite K] {f n : ℕ} [CharP K 2]
    {G : Type} [Group G] (ψ : Su K 2 f n →* G) (hK : Nat.card K = (2 ^ f) ^ 2)
    (hker : ψ.ker ≤ Subgroup.center (Su K 2 f n)) (hn : 3 ≤ n) {a b : Fin n} (hab : a ≠ b) :
    Nat.card ((ggSuPairBlock K 2 f n a b).map ψ) = 2 ^ f * ((2 ^ f) ^ 2 - 1) := by
  classical
  obtain ⟨σ, hσ0, hσ1⟩ :=
    ggPhanNSAPairAux_exists_perm_two (a := (⟨0, by omega⟩ : Fin n)) (b := (⟨1, by omega⟩ : Fin n))
      (i := a) (j := b) (by simp [Fin.ext_iff]) hab
  let P : Su K 2 f n := ggPhanNSAPairAux_permElt (f := f) σ
  let θ : Su K 2 f 2 →* Su K 2 f n :=
    (MulAut.conj P).toMonoidHom.comp (blockEmb K 2 f n 2 0 (by omega))
  have hθrange : θ.range = ggSuPairBlock K 2 f n a b := by
    rw [MonoidHom.range_comp,
      ggPhanNSAPairAux_range_blockEmb2 (p := 2) (f := f) (i := 0) (by omega),
      ggPhanNSAPairAux_suPairBlock_conj, hσ0, hσ1]
  have hχker : (ψ.comp (MulAut.conj P).toMonoidHom).ker ≤ Subgroup.center (Su K 2 f n) := by
    rw [← MonoidHom.comap_ker]
    exact le_trans (Subgroup.comap_mono hker)
      (Subgroup.comap_center_le_center (MulAut.conj P).injective)
  have hinj : Function.Injective (ψ.comp θ) := by
    change Function.Injective ((ψ.comp (MulAut.conj P).toMonoidHom).comp
      (blockEmb K 2 f n 2 0 (by omega)))
    exact comp_blockEmb_injective (θ := ψ.comp (MulAut.conj P).toMonoidHom) hK hχker
      (by omega : 0 + 2 ≤ n) (by omega : 2 < n) hn
  have hmap : (ggSuPairBlock K 2 f n a b).map ψ = (ψ.comp θ).range := by
    rw [← hθrange, MonoidHom.map_range]
  rw [hmap, MonoidHom.range_eq_map, Subgroup.card_map_of_injective (K := ⊤) hinj]
  simp only [Subgroup.card_top]
  exact ggPhanNSAPairAux_card_su_two K 2 f hK

theorem ggPhanNSAPairAux_card_fun_eq {q q' : ℕ} (hq : 2 ≤ q) (hq' : 2 ≤ q')
    (h : q * (q ^ 2 - 1) = q' * (q' ^ 2 - 1)) : q = q' := by
  have key : ∀ a b : ℕ, 2 ≤ a → a < b → a * (a ^ 2 - 1) < b * (b ^ 2 - 1) := by
    intro a b ha hab
    have ha1 : 1 ≤ a ^ 2 - 1 := by
      have h4 : 4 ≤ a ^ 2 := by simpa using Nat.pow_le_pow_left ha 2
      omega
    have hb : a ^ 2 - 1 < b ^ 2 - 1 := by
      have hsq : a ^ 2 < b ^ 2 := Nat.pow_lt_pow_left hab (by norm_num)
      omega
    calc a * (a ^ 2 - 1) < b * (a ^ 2 - 1) := Nat.mul_lt_mul_of_pos_right hab ha1
      _ ≤ b * (b ^ 2 - 1) := Nat.mul_le_mul_left b (le_of_lt hb)
  rcases lt_trichotomy q q' with hlt | heq | hgt
  · exact absurd h (ne_of_lt (key q q' hq hlt))
  · exact heq
  · exact absurd h.symm (ne_of_lt (key q' q hq' hgt))

theorem ggPhanNSAPairAux_stdPair_congr_field {K K' : Type} [Field K] [Field K']
    [Finite K] [Finite K'] [CharP K 2] [CharP K' 2] {f : ℕ}
    {G : Type} [Group G] {W U V : Subgroup G}
    (e : K' ≃+* K) (h : UnitaryBlockStandardPair K 2 f W U V) :
    UnitaryBlockStandardPair K' 2 f W U V := by
  have he : ∀ c, e (unitaryInvolution K' 2 f c) = unitaryInvolution K 2 f (e c) := by
    intro c
    simp only [unitaryInvolution_apply, map_pow]
  let E : Su K' 2 f 3 ≃* Su K 2 f 3 := suidCongr e he 3
  have hB12 : (B12 K' 2 f).map E.toMonoidHom = B12 K 2 f := by
    have hmap : (ggSuPairBlock K' 2 f 3 0 1).map E.toMonoidHom =
        ggSuPairBlock K 2 f 3 0 1 := SetLike.coe_injective (by
      simpa only [Subgroup.coe_map, MulEquiv.coe_toMonoidHom, E] using
        ggPhanNSAPairAux_suidCongr_pairBlock e he (0 : Fin 3) 1)
    simp only [B12, embSUid_two_eq_blockEmb, ggPhanNSAPairAux_range_blockEmb2]
    convert hmap using 1 <;> norm_num
  have hB23 : (B23 K' 2 f).map E.toMonoidHom = B23 K 2 f := by
    have hmap : (ggSuPairBlock K' 2 f 3 1 2).map E.toMonoidHom =
        ggSuPairBlock K 2 f 3 1 2 := SetLike.coe_injective (by
      simpa only [Subgroup.coe_map, MulEquiv.coe_toMonoidHom, E] using
        ggPhanNSAPairAux_suidCongr_pairBlock e he (1 : Fin 3) 2)
    simp only [B23, embSUid_zero_eq_blockEmb, ggPhanNSAPairAux_range_blockEmb2]
    convert hmap using 1 <;> norm_num
  obtain ⟨θ, hrange, hker, hU, hV⟩ := pair_normalize h
  have hker' : (θ.comp E.toMonoidHom).ker ≤ Subgroup.center (Su K' 2 f 3) := by
    rw [← MonoidHom.comap_ker]
    exact le_trans (Subgroup.comap_mono hker)
      (Subgroup.comap_center_le_center E.injective)
  have hrange' : (θ.comp E.toMonoidHom).range = W := by
    have hE : E.toMonoidHom.range = ⊤ := MonoidHom.range_eq_top.mpr E.surjective
    rw [MonoidHom.range_comp, hE, ← MonoidHom.range_eq_map, hrange]
  rw [← hrange']
  apply CFSG.GH74.L5U5.unitaryBlockStandardPair_of_blocks hker'
  · rw [← Subgroup.map_map, hB12, hU]
  · rw [← Subgroup.map_map, hB23, hV]

theorem ggPhanNSAPairAux_stdPair_of_card {K K' : Type} [Field K] [Field K']
    [Finite K] [Finite K'] [CharP K 2] [CharP K' 2] {f f' : ℕ}
    {G : Type} [Group G] {W U V : Subgroup G}
    (hK : Nat.card K = (2 ^ f) ^ 2) (hK' : Nat.card K' = (2 ^ f') ^ 2)
    (h : UnitaryBlockStandardPair K 2 f W U V)
    (hU : Nat.card U = 2 ^ f' * ((2 ^ f') ^ 2 - 1)) :
    UnitaryBlockStandardPair K' 2 f' W U V := by
  obtain ⟨eU⟩ := (nonempty_mulEquiv_of_standardPair hK h).1
  have hcard : 2 ^ f * ((2 ^ f) ^ 2 - 1) = 2 ^ f' * ((2 ^ f') ^ 2 - 1) := by
    rw [← ggPhanNSAPairAux_card_su_two K 2 f hK, Nat.card_congr eU.toEquiv, hU]
  have hq : 2 ≤ 2 ^ f := by
    have hlt := Finite.one_lt_card (α := K)
    rw [hK] at hlt
    have hpos := pow_pos (by norm_num : 0 < (2 : ℕ)) f
    nlinarith
  have hq' : 2 ≤ 2 ^ f' := by
    have hlt := Finite.one_lt_card (α := K')
    rw [hK'] at hlt
    have hpos := pow_pos (by norm_num : 0 < (2 : ℕ)) f'
    nlinarith
  have hf : f = f' := Nat.pow_right_injective (by norm_num : 2 ≤ 2)
    (ggPhanNSAPairAux_card_fun_eq hq hq' hcard)
  subst f'
  classical
  letI : Fintype K := Fintype.ofFinite K
  letI : Fintype K' := Fintype.ofFinite K'
  let e : K' ≃+* K := FiniteField.ringEquivOfCardEq (by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hK', hK])
  exact ggPhanNSAPairAux_stdPair_congr_field e h

end CFSG.StandardType

end
