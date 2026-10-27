module

public import CFSG.Blueprint.Catalog
import CFSG.Quasithin.Vol2.KGFactInspPerf
import CFSG.Quasithin.Vol2.KGFactInspModelU
import CFSG.Quasithin.Vol2.KGFactInspSL2Odd
import CFSG.Quasithin.Vol2.KGFactInspE16Base

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82

open Subgroup
open scoped MatrixGroups commutatorElement

private theorem pCoreOf_two_commute_of_invCentModel
    {P : Type} [Group P] [Finite P] {F₀ : Type} [Field F₀] [Finite F₀]
    (hM : CFSG.Quasithin.H13.KGInspOdd.InvCentModel P F₀)
    (hrank : CFSG.Open.pRank 2 (⊤ : Subgroup P) ≤ 2) {K : Subgroup P}
    (hK : ⁅K, K⁆ = K) : ∀ a ∈ CFSG.Open.pCoreOf 2 K, ∀ k ∈ K, a * k = k * a := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro a ha k hk
  by_cases hR : CFSG.Open.pCoreOf 2 K = ⊥
  · rw [hR, Subgroup.mem_bot] at ha
    rw [ha, one_mul, mul_one]
  have hR2 : IsPGroup 2 (CFSG.Open.pCoreOf 2 K) :=
    CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K
  have hbound : ∀ E : Subgroup P, E ≤ CFSG.Open.pCoreOf 2 K →
      CFSG.Open.IsElemAbelian 2 E → Nat.card E ≤ 4 := by
    intro E hER hE
    obtain ⟨m, hm⟩ := (hR2.to_le hER).exists_card_eq
    have hm2 : m ≤ 2 := (CFSG.SectionRank.le_pRank (by norm_num) le_top hE hm).trans hrank
    rw [hm]
    calc 2 ^ m ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) hm2
      _ = 4 := by norm_num
  obtain ⟨z, -, hz2, -, hzK⟩ := CFSG.Quasithin.H13.KGInspOdd.exists_involution_centralized hK
    (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K) hR hR2 hbound
  obtain ⟨ι, hιinj, hιC, hCC, -⟩ := hM z hz2
  have hKC : K ≤ Subgroup.centralizer ({z} : Set P) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hzK x hx)
  have hKι : K ≤ ι.range :=
    calc K = ⁅K, K⁆ := hK.symm
      _ ≤ ⁅Subgroup.centralizer ({z} : Set P), Subgroup.centralizer ({z} : Set P)⁆ :=
        Subgroup.commutator_mono hKC hKC
      _ ≤ ι.range := hCC
  set K₂ : Subgroup SL(2, F₀) := K.comap ι with hK₂def
  have hmapK : K₂.map ι = K := Subgroup.map_comap_eq_self hKι
  have hK₂perf : ⁅K₂, K₂⁆ = K₂ := by
    apply Subgroup.map_injective hιinj
    rw [Subgroup.map_commutator, hmapK, hK]
  have hK1 : K ≠ ⊥ := by
    rintro rfl
    exact hR (le_bot_iff.mp (CFSG.LieType.BorelTits.pCoreOf_le 2 ⊥))
  have hK₂1 : K₂ ≠ ⊥ := by
    rintro h
    exact hK1 (by rw [← hmapK, h, Subgroup.map_bot])
  set A : Subgroup SL(2, F₀) := (CFSG.Open.pCoreOf 2 K).comap ι with hAdef
  have hA2 : IsPGroup 2 A := hR2.comap_of_injective ι hιinj
  have hAnormal : (A.subgroupOf K₂).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    rw [hAdef, Subgroup.mem_comap] at hn ⊢
    have hconj := (Subgroup.mem_normalizer_iff.mp
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K (Subgroup.mem_comap.mp g.2))
      (ι (n : SL(2, F₀)))).mp hn
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv] using hconj
  have hA_le : A ≤ K₂ := fun y hy => CFSG.LieType.BorelTits.pCoreOf_le 2 K hy
  have hAcore : A ≤ CFSG.Open.pCoreOf 2 K₂ :=
    CFSG.LieType.BorelTits.le_pCoreOf 2 hA_le hAnormal hA2
  have hAz : A ≤ Subgroup.zpowers (-1 : SL(2, F₀)) :=
    hAcore.trans (CFSG.Quasithin.H13.KGInspOdd.pCoreOf_le_zpowers hK₂perf hK₂1)
  obtain ⟨y, -, rfl⟩ := Subgroup.mem_map.mp (hmapK ▸ CFSG.LieType.BorelTits.pCoreOf_le 2 K ha)
  have hyz : y ∈ Subgroup.zpowers (-1 : SL(2, F₀)) :=
    hAz (by rw [hAdef, Subgroup.mem_comap]; exact ha)
  obtain ⟨t, rfl⟩ := (show k ∈ ι.range from hKι hk)
  rw [← map_mul, ← map_mul,
    Subgroup.mem_center_iff.mp (CFSG.Quasithin.H13.KGInspOdd.zpowers_le_center hyz) t]

private theorem pCoreOf_two_commute_of_mulEquiv
    {X P : Type} [Group X] [Finite X] [Group P] [Finite P] {F₀ : Type} [Field F₀] [Finite F₀]
    (e : X ≃* P) {K : Subgroup X} (hK : ⁅K, K⁆ = K)
    (hM : CFSG.Quasithin.H13.KGInspOdd.InvCentModel P F₀)
    (hrank : CFSG.Open.pRank 2 (⊤ : Subgroup P) ≤ 2) :
    ∀ a ∈ CFSG.Open.pCoreOf 2 K, ∀ k ∈ K, a * k = k * a := by
  have hmain := pCoreOf_two_commute_of_invCentModel hM hrank
    (K := K.map e.toMonoidHom) (by rw [← Subgroup.map_commutator, hK])
  intro a ha k hk
  have ha' : e a ∈ CFSG.Open.pCoreOf 2 (K.map e.toMonoidHom) := by
    rw [CFSG.LieType.BorelTits.pCoreOf_map_mulEquiv (e := e)]
    exact Subgroup.mem_map_of_mem e.toMonoidHom ha
  exact e.injective (by
    simpa only [map_mul] using hmain (e a) ha' (e k) (Subgroup.mem_map_of_mem e.toMonoidHom hk))

theorem pCoreOf_two_commute_of_lieModel_odd {X : Type} [Group X]
    [Finite X] {ℓ f : ℕ} (hℓ : ℓ ≠ 2)
    (hX : CFSG.Blueprint.LieModel X .PSL 3 ℓ f ∨ CFSG.Blueprint.LieModel X .PSU 3 ℓ f)
    {K : Subgroup X} (hK : ⁅K, K⁆ = K) :
    ∀ a ∈ CFSG.Open.pCoreOf 2 K, ∀ k ∈ K, a * k = k * a := by
  have hp : ℓ.Prime := by
    rcases hX with h | h
    · exact (CFSG.Blueprint.LieModel.admissible h).1
    · exact (CFSG.Blueprint.LieModel.admissible h).1
  rcases hX with hX | hX
  ·
    obtain ⟨-, F, hF, hFfin, hFcard, ⟨e⟩⟩ :=
      CFSG.Blueprint.LieModel.statedClassicalModel hX (by decide)
    haveI : Finite F := hFfin
    have hodd : Odd (Nat.card F) := by
      rw [hFcard]
      exact (hp.odd_of_ne_two hℓ).pow
    have h2 : (2 : F) ≠ 0 := CFSG.Wreathed.OddLinearThreeCentralizerCore.two_ne_zero F hodd
    have hrank : CFSG.Open.pRank 2 (⊤ : Subgroup X) ≤ 2 :=
      CFSG.Quasithin.H13.KGInsp4316.pRank_two_le_two_of_psl3_odd hp hℓ
        (CFSG.Blueprint.LieModel.statedClassicalModel hX (by decide))
    exact pCoreOf_two_commute_of_mulEquiv e hK
      (CFSG.Quasithin.H13.KGInspOdd.invCentModel_psl h2)
      ((CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num : 1 < 2) e).symm.trans_le hrank)
  ·
    obtain ⟨hadmin, K₀, hK₀, hK₀fin, hK₀card, ⟨e⟩⟩ :=
      CFSG.Blueprint.LieModel.statedClassicalModel hX (by decide)
    haveI : Finite K₀ := hK₀fin
    have hU : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData ℓ f K₀ :=
      ⟨hp, hadmin.2.1, by rw [hK₀card, ← pow_mul, mul_comm]⟩
    have : Fact ℓ.Prime := ⟨hp⟩
    have : CharP K₀ ℓ := hU.charP
    have hrank : CFSG.Open.pRank 2 (⊤ : Subgroup X) ≤ 2 :=
      CFSG.Quasithin.H13.KGInsp4316.pRank_two_le_two_of_psu3_odd hp hℓ
        (CFSG.Blueprint.LieModel.statedClassicalModel hX (by decide))
    exact pCoreOf_two_commute_of_mulEquiv e hK
      (CFSG.Quasithin.H13.KGInspOdd.invCentModel_psu hU hℓ hK₀card)
      ((CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num : 1 < 2) e).symm.trans_le hrank)

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82
