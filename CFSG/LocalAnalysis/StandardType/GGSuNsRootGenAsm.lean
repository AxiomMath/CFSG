module

public import CFSG.LocalAnalysis.StandardType.GGSuNsRootGenModel
public import CFSG.LocalAnalysis.StandardType.GGSuNsRootGenWeyl
public import CFSG.LocalAnalysis.StandardType.GGSuNsRootGenHyp
public import CFSG.LocalAnalysis.StandardType.GGSuNsRootGenComp
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyRootGenAvoidKG
import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyU

public section

namespace CFSG.StandardType

open CFSG.Assembly SuNsRootGen

theorem ggTorusRootGenAvoidKG_unitaryCoprime
    {K : Type} [Field K]
    {n d p : ℕ} (hK : Nat.card K = (2 ^ n) ^ 2) (hn : 2 ≤ n) (hd : 3 ≤ d) (hp : p.Prime)
    (hpq : p ∣ 2 ^ n + 1) (hpd : ¬ p ∣ d) (r : ℕ) :
    GGTorusRootGenAvoidKG p r (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n)))
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin d) K (2 ^ n)))
        (LargeEvenGUSet (Fin d) K (2 ^ n))) := by
  classical
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  have h := TableBU.unitaryFieldData_of_card hK (by omega)
  have hp2 : p ≠ 2 := TableBU.ne_two_of_dvd_two_pow_add_one (by omega) hpq
  have hq : 4 ≤ 2 ^ n := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  intro L' _ _ ψ hψ hker hperf A hA hAI _ h3 hsc ρ
  rcases (show d = 3 ∨ 4 ≤ d by omega) with rfl | hd4
  · exfalso
    have hdq : ((3 : ℕ), 2 ^ n) ≠ (3, 2) := fun h' => by
      have := congrArg Prod.snd h'
      simp only at this
      omega
    obtain ⟨Θ, -⟩ := exists_permModel hp (TableBUE.center_proj_eq_bot hK le_rfl hdq)
      (fun φ hφ hφp => InndiagSU.ggOutdiagPrime_unitary hK (by omega) le_rfl hdq hp hpq hpd φ hφ
        hφp)
      (StdSubRestU.ggCenterPrime_unitary hK (by omega) le_rfl hdq hp hp2 hpd)
      (UModel.ggTorusPermEltSC_unitary hK (by omega) (by omega) hp hp2 hpq hpd)
      hψ hker hperf hA hAI h3 hsc
    have : NeZero p := ⟨hp.ne_zero⟩
    have hle : Nat.card ↥(UCoord.sumZero 3 p) ≤ p ^ 2 := UCoord.card_sumZero_le 2 p
    rw [Nat.card_congr Θ.toEquiv] at hle
    have := (Nat.pow_le_pow_iff_right hp.one_lt).mp (h3.trans hle)
    omega
  · obtain ⟨φ, hφs, hφker, hM⟩ :=
      exists_isDiagTorusModelU hK hn hd4 hp hpq hpd hψ hker hperf hA hAI hsc
    obtain ⟨i₀, j₀, hρ⟩ : ∃ i₀ j₀ : Fin d, ∀ i j, i ≠ j →
        ggConjAut A (conj_swapU_mem_normalizer h hM i j) = ρ →
          ({i, j} : Finset (Fin d)) = {i₀, j₀} := by
      by_cases hc : ∃ i j, i ≠ j ∧ ggConjAut A (conj_swapU_mem_normalizer h hM i j) = ρ
      · obtain ⟨i₀, j₀, hij₀, h₀⟩ := hc
        exact ⟨i₀, j₀, fun i j hij hρ' => pair_eq_of_ggConjAut_eq_swapU h hp hpq hpd (by omega)
          hφker hM hij hij₀ (hρ'.trans h₀.symm)⟩
      · push Not at hc
        exact ⟨⟨0, by omega⟩, ⟨0, by omega⟩, fun i j hij hρ' => absurd hρ' (hc i j hij)⟩
    apply le_antisymm le_top
    rw [← Subgroup.map_top_of_surjective φ hφs,
      ← iSup_blockSU_pairs (K := K) (n := n) h hq (by omega) i₀ j₀]
    simp only [Subgroup.map_iSup]
    refine iSup_le fun i => iSup_le fun j => iSup_le fun hij => ?_
    have hcomp := isComponentOf_blockSU_pair (φ := φ) h hn hp hpq hd4 hφker hij.1
    rw [← ggHypCent_swapU_eq h hp hpd hφs hφker hM i j] at hcomp
    exact le_iSup_of_le (φ (SURep.swapU h i j)) (le_iSup_of_le (conj_swapU_mem_normalizer h hM i j)
      (le_iSup_of_le ((TableBUE.blockSU (K := K) (n := n) ({i, j} : Finset (Fin d))).map φ)
        (le_iSup_of_le ⟨ggTorusWeylElt_swapU h hM i j,
          isReflection_conj_swapU h hp hpq hpd (by omega) hφker hM hij.1,
          fun h' => hij.2 (hρ i j hij.1 h'),
          Subgroup.mem_map_of_mem φ (swapU_mem_blockSU h i j), hcomp,
          dvd_card_blockSU_pair h hp hpq (by omega) hφker hij.1⟩ le_rfl)))

end CFSG.StandardType

end
