module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.Defs
import CFSG.Quasithin.Background.SmithC27RLieA6

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo

private lemma factorization_24_two : (24 : ℕ).factorization 2 = 3 := by
  rw [show (24 : ℕ) = 2 ^ 3 * 3 by norm_num, Nat.factorization_mul (by norm_num) (by norm_num),
    Finsupp.add_apply, Nat.Prime.factorization_pow Nat.prime_two]
  simp [Nat.factorization_eq_zero_of_not_dvd]

private lemma factorization_360_two : (360 : ℕ).factorization 2 = 3 := by
  rw [show (360 : ℕ) = 2 ^ 3 * 45 by norm_num, Nat.factorization_mul (by norm_num) (by norm_num),
    Finsupp.add_apply, Nat.Prime.factorization_pow Nat.prime_two]
  simp [Nat.factorization_eq_zero_of_not_dvd]

theorem card_pCore_of_card_eq_24 {H : Type} [Group H] [Finite H] (hH : Nat.card H = 24)
    (hP : ∀ P : Sylow 2 H, normalizer ((P : Subgroup H) : Set H) = P) :
    Nat.card (CFSG.pCore 2 H) = 4 ∧ ∃ a b : H, a * b * a⁻¹ * b⁻¹ ∉ CFSG.pCore 2 H := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let P : Sylow 2 H := default
  have hQ8 : Nat.card (P : Subgroup H) = 8 := by
    rw [Sylow.card_eq_multiplicity P, hH, factorization_24_two]
    norm_num
  have hQidx : (P : Subgroup H).index = 3 := by
    rw [Subgroup.index_eq_card_div, hQ8, hH]
  have hSylow3 : Nat.card (Sylow 2 H) = 3 := by
    rw [Sylow.card_eq_index_normalizer P]
    have hnorm : Subgroup.normalizer (P : Set H) = (P : Subgroup H) := hP P
    rw [hnorm, hQidx]
  have hQnotNormal : ¬ (P : Subgroup H).Normal := by
    intro hQn
    haveI : Unique (Sylow 2 H) := Sylow.unique_of_normal P hQn
    have h1 : Nat.card (Sylow 2 H) = 1 := Nat.card_unique
    omega
  have hcoreEq : CFSG.pCore 2 H = (P : Subgroup H).normalCore := by
    refine le_antisymm ?_ ?_
    · exact Subgroup.normal_le_normalCore.mpr (CFSG.fitting_pCore_le_sylow P)
    · exact le_sSup ⟨inferInstance, P.isPGroup'.to_le (Subgroup.normalCore_le _)⟩
  have hcoreIdx : (P : Subgroup H).normalCore.index = 6 := by
    have hdvd1 : (P : Subgroup H).index ∣ (P : Subgroup H).normalCore.index :=
      Subgroup.index_dvd_of_le (Subgroup.normalCore_le _)
    have hdvd2 := Subgroup.index_normalCore_dvd_factorial_index (P : Subgroup H)
    rw [hQidx] at hdvd1 hdvd2
    norm_num at hdvd2
    have hidxpos : 0 < (P : Subgroup H).normalCore.index :=
      Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite)
    have hle : (P : Subgroup H).normalCore.index ≤ 6 := Nat.le_of_dvd (by norm_num) hdvd2
    have hge : 3 ≤ (P : Subgroup H).normalCore.index := Nat.le_of_dvd hidxpos hdvd1
    have hmem : (P : Subgroup H).normalCore.index = 3 ∨
        (P : Subgroup H).normalCore.index = 6 := by
      interval_cases h : (P : Subgroup H).normalCore.index
      · exact Or.inl rfl
      · exact absurd hdvd2 (by decide)
      · exact absurd hdvd2 (by decide)
      · exact Or.inr rfl
    rcases hmem with h3 | h6
    · exfalso
      have hcardcore : Nat.card (P : Subgroup H).normalCore = 8 := by
        have hci := Subgroup.card_mul_index ((P : Subgroup H).normalCore)
        rw [h3, hH] at hci
        omega
      have hcoreeq : (P : Subgroup H).normalCore = (P : Subgroup H) :=
        Subgroup.eq_of_le_of_card_ge (Subgroup.normalCore_le _) (by rw [hcardcore, hQ8])
      exact hQnotNormal (hcoreeq ▸ Subgroup.normalCore_normal _)
    · exact h6
  have hpCorecard : Nat.card (CFSG.pCore 2 H) = 4 := by
    rw [hcoreEq]
    have hci := Subgroup.card_mul_index ((P : Subgroup H).normalCore)
    rw [hcoreIdx, hH] at hci
    omega
  refine ⟨hpCorecard, ?_⟩
  let φ : H →* Equiv.Perm (H ⧸ (P : Subgroup H)) :=
    MulAction.toPermHom H (H ⧸ (P : Subgroup H))
  have hker : φ.ker = CFSG.pCore 2 H := by
    dsimp only [φ]
    rw [hcoreEq, Subgroup.normalCore_eq_ker]
  have hpCoreIdx : (CFSG.pCore 2 H).index = 6 := by
    rw [hcoreEq, hcoreIdx]
  have hcardQuot : Nat.card (H ⧸ (P : Subgroup H)) = 3 := by
    rw [← Subgroup.index_eq_card, hQidx]
  have hrangeCard : Nat.card φ.range = 6 := by
    rw [← Subgroup.index_ker φ, hker, hpCoreIdx]
  have hpermCard : Nat.card (Equiv.Perm (H ⧸ (P : Subgroup H))) = 6 := by
    rw [Nat.card_perm, hcardQuot]
    norm_num
  have hrangeTop : φ.range = ⊤ :=
    Subgroup.eq_top_of_card_eq (H := φ.range) (by rw [hrangeCard, hpermCard])
  have hsurj : Function.Surjective φ := MonoidHom.range_eq_top.mp hrangeTop
  have hnotcomm : ¬ IsMulCommutative (Equiv.Perm (H ⧸ (P : Subgroup H))) := by
    rw [Equiv.Perm.isMulCommutative_iff_card_le_two, hcardQuot]
    norm_num
  have hnotcomm' : ¬ (∀ σ τ : Equiv.Perm (H ⧸ (P : Subgroup H)), σ * τ = τ * σ) :=
    fun h => hnotcomm (IsMulCommutative.of_comm h)
  push Not at hnotcomm'
  obtain ⟨σ, τ, hστ⟩ := hnotcomm'
  obtain ⟨a, ha⟩ := hsurj σ
  obtain ⟨b, hb⟩ := hsurj τ
  refine ⟨a, b, ?_⟩
  intro hmem
  apply hστ
  have hmemker : a * b * a⁻¹ * b⁻¹ ∈ φ.ker := by
    rw [hker]
    exact hmem
  rw [MonoidHom.mem_ker] at hmemker
  simp only [map_mul, map_inv, ha, hb] at hmemker
  calc σ * τ = (σ * τ * σ⁻¹ * τ⁻¹) * (τ * σ) := by group
    _ = 1 * (τ * σ) := by rw [hmemker]
    _ = τ * σ := one_mul _

theorem normalizer_sylow_eq_of_le_alt6 {H : Subgroup (alternatingGroup (Fin 6))}
    (hH : 8 ∣ Nat.card H) (P : Sylow 2 ↥H) :
    normalizer ((P : Subgroup ↥H) : Set ↥H) = P := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI hHne : Nonempty ↥H := ⟨1⟩
  haveI haltne : Nonempty (alternatingGroup (Fin 6)) := ⟨1⟩
  have hPcard : Nat.card (P : Subgroup ↥H) = 8 := by
    rw [Sylow.card_eq_multiplicity P]
    have hge : 3 ≤ (Nat.card ↥H).factorization 2 := by
      have hH' : 2 ^ 3 ∣ Nat.card ↥H := by
        rw [show (2 : ℕ) ^ 3 = 8 by norm_num]
        exact hH
      exact (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two Nat.card_pos.ne').mp hH'
    have hle : (Nat.card ↥H).factorization 2 ≤ 3 := by
      have hdvd : Nat.card ↥H ∣ Nat.card (alternatingGroup (Fin 6)) :=
        Subgroup.card_subgroup_dvd_card H
      have h := (Nat.factorization_le_iff_dvd Nat.card_pos.ne'
        (Nat.card_pos (α := alternatingGroup (Fin 6))).ne').mpr hdvd
      have h2 := (Finsupp.le_def.mp h) 2
      rw [CFSG.QuasithinUnique.Setup.X3.card_alt6, factorization_360_two] at h2
      exact h2
    have hfac : (Nat.card ↥H).factorization 2 = 3 := le_antisymm hle hge
    rw [hfac]
    norm_num
  let S : Subgroup (alternatingGroup (Fin 6)) := (P : Subgroup ↥H).map H.subtype
  have hSle : S ≤ H := Subgroup.map_subtype_le (P : Subgroup ↥H)
  have hSindex : ¬ 2 ∣ S.index := by
    have hcardS : Nat.card S = 8 := by
      rw [← hPcard]
      exact Nat.card_congr
        (P.equivMapOfInjective H.subtype H.subtype_injective).symm.toEquiv
    rw [Subgroup.index_eq_card_div, hcardS, CFSG.QuasithinUnique.Setup.X3.card_alt6]
    norm_num
  have hSylTop : CFSG.QuasithinUnique.IsSylowTwoOf S ⊤ := by
    refine ⟨le_top, P.isPGroup'.map H.subtype, ?_⟩
    have h3 : (S.subgroupOf ⊤).index = S.index := Subgroup.relIndex_top_right S
    rw [h3]
    exact hSindex
  have hnormS : Subgroup.normalizer (S : Set _) = S :=
    CFSG.Quasithin.SmithC27.normalizer_eq_of_isSylowTwoOf_alt6 hSylTop
  have hsub : S.subgroupOf H = (P : Subgroup ↥H) := by
    dsimp only [S, Subgroup.subgroupOf]
    rw [Subgroup.comap_map_eq_self_of_injective H.subtype_injective]
  have hkey := Subgroup.subgroupOf_normalizer_eq (H := S) (N := H) hSle
  rw [hnormS, hsub] at hkey
  exact hkey.symm

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
