module

public import CFSG.LocalAnalysis.UniquenessCase.Lie.RankOne
import CFSG.RankThree.S4Free.SuzukiEight
import CFSG.RankThree.PartTwo.KFacts.AutSz
public import CFSG.LieType.SteinbergBRSuzukiNormalizer
import CFSG.Blueprint.LieModelAPI

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.Blueprint CFSG.LieType.Ree Subgroup
open scoped commutatorElement

section Datum

variable {a : ℕ} {K : Type} [Field K]

@[expose] noncomputable def uc22pwr1_szD (a : ℕ) (K : Type) [Field K] :
    Kˣ →* suzukiGroup a K where
  toFun := suzukiDElt a K
  map_one' := suzukiDElt_one
  map_mul' l m := (suzukiDElt_mul l m).symm

theorem uc22pwr1_sz_T_eq : suzukiT a K = (uc22pwr1_szD a K).range := by
  apply SetLike.coe_injective
  rw [coe_suzukiT]
  rfl

theorem uc22pwr1_sz_isCyclic_T [Finite K] : IsCyclic (suzukiT a K) := by
  rw [uc22pwr1_sz_T_eq]
  exact isCyclic_of_surjective (uc22pwr1_szD a K).rangeRestrict
    (uc22pwr1_szD a K).rangeRestrict_surjective

@[expose] noncomputable def uc22pwr1_sz_sylow [Finite K] (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    Sylow 2 (suzukiGroup a K) :=
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  (CFSG.LieType.SteinbergBR.isPGroup_suzukiU hK).toSylow
    (CFSG.LieType.SteinbergBR.not_two_dvd_index_suzukiU hK)

theorem uc22pwr1_sz_sylow_coe [Finite K] (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    ((uc22pwr1_sz_sylow hK : Sylow 2 (suzukiGroup a K)) : Subgroup (suzukiGroup a K)) = suzukiU a K :=
  rfl

theorem uc22pwr1_sz_normalizer [Finite K] (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    normalizer (suzukiU a K : Set (suzukiGroup a K)) = suzukiB a K := by
  refine le_antisymm (fun g hg => ?_) (CFSG.RankThree.S4Free.Suzuki.suzukiB_le_normalizer_suzukiU hK)
  have h := CFSG.RankThree.S4Free.Suzuki.normalizer_eq_map_suzukiB hK
    (MulEquiv.refl (suzukiGroup a K)) (S := suzukiU a K) (g := 1) (fun x => by simp)
  rw [h] at hg
  obtain ⟨b, hb, hbg⟩ := hg
  have : b = g := by simpa using hbg
  rw [← this]
  exact hb

theorem uc22pwr1_datum_suzuki [Finite K] (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    UC22pwR1Datum (suzukiGroup a K) (suzukiU a K) (2 * a + 1) := by
  have hstr := suzuki_borel_structure hK
  have hTcard : Nat.card (suzukiT a K) = 2 ^ (2 * a + 1) - 1 := hstr.2.2.1
  have hBN := CFSG.RankThree.S4Free.Suzuki.suzukiB_le_normalizer_suzukiU hK
  have hTB : suzukiT a K ≤ suzukiB a K := suzukiT_le_suzukiB a K
  have hodd : Odd (2 ^ (2 * a + 1) - 1) := by
    have he : Even (2 ^ (2 * a + 1)) := Nat.even_pow.2 ⟨even_two, by omega⟩
    exact Nat.Even.sub_odd Nat.one_le_two_pow he odd_one
  refine ⟨suzukiT a K, suzukiWElt a K, uc22pwr1_sz_isCyclic_T, hTcard ▸ hodd, hstr.2.2.2.1,
    fun p _ hp => hTcard ▸ hp, by rw [pow_two]; exact suzukiWElt_mul_self, ?_, ?_, ?_⟩
  · intro t ht _
    have ht' : t ∈ Set.range (suzukiDElt a K) := by rw [← coe_suzukiT]; exact ht
    obtain ⟨l, rfl⟩ := ht'
    rw [suzukiWElt_inv, suzukiWElt_D_W hK, suzukiDElt_inv]
  · refine eq_top_iff.2 fun g _ => ?_
    have hW : suzukiWElt a K ∈ normalizer (suzukiU a K : Set (suzukiGroup a K)) ⊔
        zpowers (suzukiWElt a K) := Subgroup.mem_sup_right (mem_zpowers _)
    rcases suzukiGroup_mem_cells hK g with hg | ⟨b, hb, x, hx, rfl⟩
    · exact Subgroup.mem_sup_left (hBN hg)
    · exact mul_mem (mul_mem (Subgroup.mem_sup_left (hBN hb)) hW)
        (Subgroup.mem_sup_left (hBN (suzukiU_le_suzukiB a K hx)))
  · intro ψ hψ
    haveI : CharP K 2 := uc22pwlie_charP_two hK
    obtain ⟨g, σ, hψσ⟩ := CFSG.RankThree.PartTwo.KFacts.exists_conj_mul_szFieldAut ha hK ψ
    obtain ⟨i, hi⟩ := uc22pwlie_ringEquiv_pow σ
    have hσU1 : ∀ τ : RingAut K, ∀ x ∈ suzukiU a K,
        CFSG.SignalizerFunctorTheorem.NearModels.Suzuki.szFieldAut a K τ x ∈ suzukiU a K := by
      intro τ x hx
      obtain ⟨u, v, rfl⟩ := (mem_suzukiU_iff hK).1 hx
      rw [CFSG.SignalizerFunctorTheorem.NearModels.Suzuki.szFieldAut_S]
      exact suzukiSElt_mem_suzukiU a K _ _
    have hσU : ∀ τ : RingAut K, ∀ x, x ∈ suzukiU a K ↔
        CFSG.SignalizerFunctorTheorem.NearModels.Suzuki.szFieldAut a K τ x ∈ suzukiU a K := by
      intro τ x
      refine ⟨hσU1 τ x, fun hx => ?_⟩
      have h1 := hσU1 τ⁻¹ _ hx
      rwa [map_inv, MulAut.inv_apply_self] at h1
    have hgN : g ∈ normalizer (suzukiU a K : Set (suzukiGroup a K)) := by
      rw [Subgroup.mem_normalizer_iff]
      intro n
      have h1 : ψ ((CFSG.SignalizerFunctorTheorem.NearModels.Suzuki.szFieldAut a K σ)⁻¹ n) =
          g * n * g⁻¹ := by
        rw [hψσ, MulAut.mul_apply, MulAut.apply_inv_self, MulAut.conj_apply]
      rw [← h1, ← hψ]
      have h2 := hσU σ⁻¹ n
      rwa [map_inv] at h2
    have hgB : g ∈ suzukiB a K := by rw [← uc22pwr1_sz_normalizer hK]; exact hgN
    refine ⟨i, fun t ht _ => ?_⟩
    have ht' : t ∈ Set.range (suzukiDElt a K) := by rw [← coe_suzukiT]; exact ht
    obtain ⟨l, rfl⟩ := ht'
    have hpow : (uc22pwr1_szD a K) (l ^ 2 ^ i) = suzukiDElt a K l ^ 2 ^ i :=
      map_pow (uc22pwr1_szD a K) l (2 ^ i)
    have hD : suzukiDElt a K (Units.map (σ : K →* K) l) = suzukiDElt a K l ^ 2 ^ i := by
      have hl : Units.map (σ : K →* K) l = l ^ 2 ^ i := Units.ext (by simp [hi])
      rw [hl]
      exact hpow
    have hψt : ψ (suzukiDElt a K l) = g * suzukiDElt a K l ^ 2 ^ i * g⁻¹ := by
      rw [hψσ, MulAut.mul_apply, CFSG.SignalizerFunctorTheorem.NearModels.Suzuki.szFieldAut_D, hD,
        MulAut.conj_apply]
    have hT' : suzukiDElt a K l ^ 2 ^ i ∈ suzukiB a K :=
      hTB (Subgroup.pow_mem _ (suzukiDElt_mem_suzukiT a K l) _)
    refine ⟨⁅g, suzukiDElt a K l ^ 2 ^ i⁆, commutatorElement_mem_suzukiU hK hgB hT', ?_⟩
    rw [hψt, commutatorElement_def]
    group

end Datum

theorem uc22pwr1_concl_of_isSzG {X : Type} [Group X] [Finite X] {n : ℕ}
    (h : IsSz X n) (U : Sylow 2 X) {P : Type} [Group P] (hP : IsPGroup 2 P) (ψ : P →* MulAut X)
    (hψ : ∀ (g : P) (x : X), x ∈ (U : Subgroup X) ↔ ψ g x ∈ (U : Subgroup X)) {m' : ℕ} (hm' : Odd m')
    {e : ℕ} (hnem : n = 2 ^ e * m') :
    ∃ E : Subgroup X, uc22pwlie_ConclAt uc22pwr1_shape X (U : Subgroup X) P ψ n m' E ∧
      uc22pwlie_Gal (U : Subgroup X) E ψ := by
  obtain ⟨-, -, a, ha, K, _, _, hn, hcard, ⟨e₀⟩⟩ := LieModel.suzukiModel h
  have hK : Nat.card K = 2 ^ (2 * a + 1) := hn ▸ hcard
  have hD := uc22pwr1_datum_suzuki ha hK
  rw [← hn] at hD
  exact uc22pwr1_concl_of_datum_sylowG e₀ U (uc22pwr1_sz_sylow hK) hD hP ψ hψ hm' hnem

theorem uc22pwr1_concl_of_isSz {X : Type} [Group X] [Finite X] {n : ℕ}
    (h : IsSz X n) (U : Sylow 2 X) {P : Type} [Group P] (hP : IsPGroup 2 P) (ψ : P →* MulAut X)
    (hψ : ∀ (g : P) (x : X), x ∈ (U : Subgroup X) ↔ ψ g x ∈ (U : Subgroup X)) {m' : ℕ} (hm' : Odd m')
    {e : ℕ} (hnem : n = 2 ^ e * m') :
    uc22pwlie_Concl uc22pwr1_shape X (U : Subgroup X) P ψ n m' := by
  obtain ⟨E, hE, -⟩ := uc22pwr1_concl_of_isSzG h U hP ψ hψ hm' hnem
  exact ⟨E, hE⟩

end CFSG.LocalAnalysis.UniquenessCase.UC22
