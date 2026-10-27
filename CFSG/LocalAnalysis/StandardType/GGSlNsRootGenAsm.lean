module

public import CFSG.LocalAnalysis.StandardType.GGSlNsRootGenModel
public import CFSG.LocalAnalysis.StandardType.GGSlNsRootGenTorus
public import CFSG.LocalAnalysis.StandardType.GGSlNsRootGenWeyl
public import CFSG.LocalAnalysis.StandardType.GGSlNsRootGenComp
public import CFSG.LocalAnalysis.StandardType.GGSlNsRootGenGen
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyRootGenAvoidKG
public import CFSG.LocalAnalysis.StandardType.GGTableBTypeATransport
public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerLinearNsFrame

public section

namespace CFSG.StandardType.SlNsRootGen

open Matrix Polynomial CoordSL CFSG.RankThree.CALinearPlane CFSG.Assembly TableB
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open Multiplicative

theorem ggTorusRootGenAvoidKG_projectiveSL {K : Type} [Field K] [Finite K] [CharP K 2]
    {d p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpK : p ∣ Nat.card K + 1) (h4 : 4 ≤ Nat.card K)
    (r : ℕ) : GGTorusRootGenAvoidKG p r (projectiveSL d K) (Set.range (conjAut d K)) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  haveI : Nonempty K := ⟨0⟩
  intro L' _ _ ψ hψ hker hperf A hA hAI _ h3 hsc ρ
  have hpK' : ¬ p ∣ Nat.card K - 1 := by
    intro hK1
    have hdvd : p ∣ 2 := by
      have hsub : Nat.card K + 1 - (Nat.card K - 1) = 2 := by
        have := Nat.card_pos (α := K)
        omega
      rw [← hsub]
      exact Nat.dvd_sub hpK hK1
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hdvd)
  have hpK0 : (p : K) ≠ 0 := OrdPNS.natCast_ne_zero_of_charTwo hp hp2
  obtain ⟨g, hg, hgd⟩ := exists_irreducible_dvd_cyclotomic (K := K) hp
  haveI : Fact (Irreducible g) := ⟨hg⟩
  have hζ : AdjoinRoot.root g ^ p = 1 := (CoordSL.root_isPrimitiveRoot hp hpK0 hgd).pow_eq_one
  have hC : (rootMat g).det = 1 := CoordSL.det_rootMat hp hpK' hpK0 hgd
  have hCp : rootMat g ^ p = 1 := CoordSL.rootMat_pow_eq_one hp hpK0 hgd
  have hunit : ∀ j : ℕ, ¬ p ∣ j → ∀ c : K, IsUnit (rootMat g ^ j - c • 1) :=
    CoordSL.isUnit_rootMat_pow_sub hp hpK' hpK0 hgd
  have hdim : 2 ≤ (rootPB g).dim :=
    LinTwoTv.two_le_rootPB_dim fun c => hunit 1 hp.not_dvd_one c
  obtain ⟨s, r', ε, φ, hφs, hφc, hs3, hM⟩ :=
    exists_isBlockTorusModel (g := g) hp hp2 hpK hgd hC hψ hker hperf hA hAI h3 hsc
  let P : ((Fin s → ZMod p) → (Fin s → ZMod p)) → Prop := fun f =>
    ∃ (w : SpecialLinearGroup (Fin d) K)
      (hn : MulAut.conj (φ w) ∈ Subgroup.normalizer (A : Set (MulAut L'))),
      (∀ t : Fin s → ZMod p,
        w * torusSL ε hC hCp (ofAdd t) * w⁻¹ = torusSL ε hC hCp (ofAdd (f t))) ∧
      ggConjAut A hn = ρ
  have hPuniq : ∀ f₁ f₂, P f₁ → P f₂ → f₁ = f₂ := by
    rintro f₁ f₂ ⟨w₁, hn₁, hw₁, hρ₁⟩ ⟨w₂, hn₂, hw₂, hρ₂⟩
    exact eq_of_ggConjAut_eq hM hφc hunit hw₁ hw₂ hn₁ hn₂ (hρ₁.trans hρ₂.symm)
  set S : Subgroup L' :=
    ⨆ (n : L') (hn : MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut L')))
      (J : Subgroup L') (_ : GGTorusWeylElt p A n ∧ GGIsReflection p (ggConjAut A hn) ∧
        ggConjAut A hn ≠ ρ ∧ n ∈ J ∧ IsComponentOf J (ggHypCent A n) ∧ p ∣ Nat.card J), J
    with hS
  have hpair : ∀ (i j : Fin s), i ≠ j → ¬ P (swapMap i j) →
      (pairBlock g ε i j).map φ ≤ S := by
    intro i j hij hPij
    obtain ⟨w, hwB, hwconj⟩ := exists_swap_mem_pairBlock (ε := ε) hC hCp i j
    let hn := conj_mem_normalizer_of_conj hM hwconj (swapMap_surjective i j)
    have hW : GGTorusWeylElt p A (φ w) := ggTorusWeylElt_of_conj hM hwconj
    have hR : GGIsReflection p (ggConjAut A hn) :=
      isReflection_of_conj hM hφc hunit hwconj hn (swapMap_swapMap i j)
        (card_fixed_swapMap hij)
    have hne : ggConjAut A hn ≠ ρ := fun h => hPij ⟨w, hn, hwconj, h⟩
    have hmem : φ w ∈ (pairBlock g ε i j).map φ := Subgroup.mem_map_of_mem φ hwB
    have hcomp : IsComponentOf ((pairBlock g ε i j).map φ) (ggHypCent A (φ w)) :=
      isComponentOf_pairBlock (ε := ε) (hC := hC) (hCp := hCp) hp2 hpK hgd hM hφs hφc
        hs3 hij hmem
        (fun t => (commute_conj_iff_of_conj hφc hunit hwconj t).trans swapMap_eq_self_iff)
    have hdvd : p ∣ Nat.card ((pairBlock g ε i j).map φ) :=
      dvd_card_map_pairBlock (ε := ε) hp2 hpK hgd hφc hij
    exact le_iSup_of_le (φ w) (le_iSup_of_le hn (le_iSup_of_le ((pairBlock g ε i j).map φ)
      (le_iSup_of_le ⟨hW, hR, hne, hmem, hcomp, hdvd⟩ le_rfl)))
  have hzero : ∀ m : Fin s, ¬ P (negMap m) → (zeroBlock g ε m).map φ ≤ S := by
    intro m hPm
    obtain ⟨w, hwB, hwconj⟩ := exists_neg_mem_zeroBlock (ε := ε) hC hCp hζ hpK m
    let hn := conj_mem_normalizer_of_conj hM hwconj (negMap_surjective m)
    have hW : GGTorusWeylElt p A (φ w) := ggTorusWeylElt_of_conj hM hwconj
    have hR : GGIsReflection p (ggConjAut A hn) :=
      isReflection_of_conj hM hφc hunit hwconj hn (negMap_negMap m) (card_fixed_negMap hp2 m)
    have hne : ggConjAut A hn ≠ ρ := fun h => hPm ⟨w, hn, hwconj, h⟩
    have hmem : φ w ∈ (zeroBlock g ε m).map φ := Subgroup.mem_map_of_mem φ hwB
    have hcomp : IsComponentOf ((zeroBlock g ε m).map φ) (ggHypCent A (φ w)) :=
      isComponentOf_zeroBlock (ε := ε) (hC := hC) (hCp := hCp) hp2 hpK hgd hM hφs hφc
        h4 (by omega) hmem
        (fun t => (commute_conj_iff_of_conj hφc hunit hwconj t).trans (negMap_eq_self_iff hp2))
    have hdvd : p ∣ Nat.card ((zeroBlock g ε m).map φ) :=
      dvd_card_map_zeroBlock (ε := ε) hp2 hpK hgd hφc (by omega) m
    exact le_iSup_of_le (φ w) (le_iSup_of_le hn (le_iSup_of_le ((zeroBlock g ε m).map φ)
      (le_iSup_of_le ⟨hW, hR, hne, hmem, hcomp, hdvd⟩ le_rfl)))
  apply le_antisymm le_top
  by_cases hpa : ∃ i₀ j₀ : Fin s, i₀ ≠ j₀ ∧ P (swapMap i₀ j₀)
  · obtain ⟨i₀, j₀, hij₀, hP₀⟩ := hpa
    rw [← Subgroup.map_top_of_surjective φ hφs,
      ← iSup_blocks_avoid_pair_eq_top (ε := ε) hdim hs3 i₀ j₀]
    simp only [Subgroup.map_sup, Subgroup.map_iSup]
    refine sup_le ?_ ?_
    · refine iSup_le fun i => iSup_le fun j => iSup_le fun h => ?_
      exact hpair i j h.1 fun hP =>
        h.2 (pair_eq_of_swapMap_eq h.1 hij₀ (hPuniq _ _ hP hP₀))
    · refine iSup_le fun m => ?_
      exact hzero m fun hP => swapMap_ne_negMap hij₀ m (hPuniq _ _ hP₀ hP)
  · push Not at hpa
    by_cases hpb : ∃ m₀ : Fin s, P (negMap m₀)
    · obtain ⟨m₀, hP₀⟩ := hpb
      rw [← Subgroup.map_top_of_surjective φ hφs,
        ← iSup_blocks_avoid_zero_eq_top (ε := ε) hdim (by omega) m₀]
      simp only [Subgroup.map_sup, Subgroup.map_iSup]
      refine sup_le ?_ ?_
      · refine iSup_le fun i => iSup_le fun j => iSup_le fun hij => ?_
        exact hpair i j hij fun hP => hpa i j hij hP
      · refine iSup_le fun m => iSup_le fun hm => ?_
        exact hzero m fun hP => hm (eq_of_negMap_eq hp2 (hPuniq _ _ hP hP₀))
    · push Not at hpb
      rw [← Subgroup.map_top_of_surjective φ hφs,
        ← iSup_blocks_eq_top (ε := ε) hdim (by omega)]
      simp only [Subgroup.map_sup, Subgroup.map_iSup]
      refine sup_le ?_ ?_
      · refine iSup_le fun i => iSup_le fun j => iSup_le fun hij => ?_
        exact hpair i j hij fun hP => hpa i j hij hP
      · refine iSup_le fun m => ?_
        exact hzero m fun hP => hpb m hP

end CFSG.StandardType.SlNsRootGen

namespace CFSG.StandardType

open CFSG.Assembly

theorem ggTorusRootGenAvoidKG_linearNs {K : Type} [Field K] {n d p : ℕ}
    (hK : Nat.card K = 2 ^ n) (hn : 2 ≤ n) (hp : p.Prime) (hpq : p ∣ 2 ^ n + 1) (r : ℕ) :
    GGTorusRootGenAvoidKG p r (LargeEvenProj (LargeEvenSLGroup (Fin d) K))
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSLGroup (Fin d) K)) Set.univ) := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  haveI : CharP K 2 := charP_two_of_card hK
  have hp2 : p ≠ 2 := TableBU.ne_two_of_dvd_two_pow_add_one (by omega) hpq
  have h4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hpK : p ∣ Nat.card K + 1 := by rw [hK]; exact hpq
  exact ggTorusRootGenAvoidKG_of_mulEquiv (TypeA.recipeEquiv d K)
    (fun _ hφ => TypeA.congr_recipeEquiv_mem hφ)
    (SlNsRootGen.ggTorusRootGenAvoidKG_projectiveSL hp hp2 hpK h4 r)

end CFSG.StandardType

end
