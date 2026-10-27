module

public import CFSG.RankThree.PartOne.S15K.SpCenter
import CFSG.RankThree.PartOne.S15K.BlockFacts
public import CFSG.RankThree.PartOne.KC.SymplecticInnerPlane
import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeRing
public import CFSG.RankThree.PartOne.KC.SymplecticTorusSetting

public section

namespace CFSG.RankThree.PartOne.S15K

open Polynomial CFSG CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher CFSG.RankThree.PartOne
  CFSG.RankThree.PartOne.KCSpComm CFSG.RankThree.PartOne.KCPrimary
  CFSG.RankThree.PartOne.KCSpIsotypic CFSG.RankThree.Classical CFSG.RankThree.PartOne.KCUnitary
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)

variable {r : ℕ} {K : Type} [Field K]

theorem sp_not_dvd_mult {ℓ f p : ℕ} {x : StatedSp 3 K} (hp : p.Prime) (hp5 : 5 ≤ p)
    (blocks : SpPrimaryBlocks ℓ f p x (proj 3 K x))
    (hsq : Squarefree (minpoly K (spEnd x))) (a : primaryFactors (spEnd x)) :
    ¬ p ∣ primaryMultiplicity (spEnd x) (a : K[X]) := by
  intro hdvd
  have hp2 : p ≠ 2 := by omega
  by_cases hX : (a : K[X]) = X - 1
  · obtain ⟨s, hs, -⟩ := blocks.rank
    have hm : primaryMultiplicity (spEnd x) (a : K[X]) =
        Module.finrank K (primaryComponent (spEnd x) (X - 1)) := by
      rw [hX, show (X - 1 : K[X]) = X - C 1 by rw [C_1]]
      exact primaryMultiplicity_X_sub_C_eq _ _
    have hle := primaryMultiplicity_le_finrank hsq a
    have hpos := KCUnitaryModel.primaryMultiplicity_pos hsq a
    simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin] at hle
    have hpm6 : p ≤ primaryMultiplicity (spEnd x) (a : K[X]) := Nat.le_of_dvd hpos hdvd
    have h6 : primaryMultiplicity (spEnd x) (a : K[X]) = 6 := by omega
    rw [h6] at hdvd
    have hp6 : p ≤ 6 := Nat.le_of_dvd (by norm_num) hdvd
    interval_cases p
    · omega
    · norm_num at hp
  · have hle := primaryMultiplicity_le hp hp2 blocks a hX
    have hpos := KCUnitaryModel.primaryMultiplicity_pos hsq a
    have : p ≤ primaryMultiplicity (spEnd x) (a : K[X]) := Nat.le_of_dvd hpos hdvd
    omega

theorem spBlockGSp_mem_range [NeZero r] {x : StatedSp r K} {a : K[X]} {f : gsp r K}
    (hf : f ∈ spBlockGSp x a) :
    ∃ f₀ ∈ Subgroup.centralizer ({x} : Set (StatedSp r K)), f = spXg f₀ := by
  have hfker := spBlockGSp_le_ker_multiplier (x := x) a hf
  have hfS : (f : GL (Fin r ⊕ Fin r) K) ∈ StatedSp r K := by
    rw [SymplecticHigher.ker_multiplier] at hfker
    exact hfker
  have hfc := spBlockGSp_le_centralizer (x := x) a hf
  refine ⟨⟨f, hfS⟩, ?_, rfl⟩
  rw [Subgroup.mem_centralizer_singleton_iff]
  apply Subtype.ext
  have := Subgroup.mem_centralizer_singleton_iff.mp hfc
  exact congrArg (fun g : gsp r K => (g : GL (Fin r ⊕ Fin r) K)) this

theorem spXg_commute_of_mem_block [NeZero r] {x z : StatedSp r K} {a : K[X]}
    (hz : ∀ g ∈ Subgroup.centralizer ({x} : Set (StatedSp r K)), z * g = g * z) {f : gsp r K}
    (hf : f ∈ spBlockGSp x a) : spXg z * f = f * spXg z := by
  obtain ⟨f₀, hf₀, rfl⟩ := spBlockGSp_mem_range hf
  apply Subtype.ext
  exact congrArg (fun s : StatedSp r K => (s : GL (Fin r ⊕ Fin r) K)) (hz f₀ hf₀)

theorem spXg_mul_mem_derived {ℓ f p : ℕ} [Finite K] {x : StatedSp 3 K} (hℓ : ℓ.Prime)
    (hf : 1 ≤ f) (hK : Nat.card K = ℓ ^ f) (hp : p.Prime) (hp5 : 5 ≤ p) (hq2 : 2 ≤ ℓ ^ f)
    (h42 : ¬ (spFixedDim x = 4 ∧ Nat.card K = 2))
    (blocks : SpPrimaryBlocks ℓ f p x (proj 3 K x)) {k w : StatedSp 3 K} (hk : k ∈ spPullAll x)
    (hw : w ∈ spFixedFactor x) (hwp : w ^ p = 1) :
    spXg k * spXg w ∈ ⁅Subgroup.centralizer ({spXg x} : Set (gsp 3 K)),
      Subgroup.centralizer ({spXg x} : Set (gsp 3 K))⁆ := by
  set CS := Subgroup.centralizer ({x} : Set (StatedSp 3 K)) with hCS
  set M := Subgroup.centralizer ({spXg x} : Set (gsp 3 K)) with hM
  let incl : StatedSp 3 K →* gsp 3 K := Subgroup.inclusion statedSp_le_gsp
  have hmapC : CS.map incl ≤ M := by
    rintro _ ⟨s, hs, rfl⟩
    have hs' : s * x = x * s := Subgroup.mem_centralizer_singleton_iff.mp hs
    show incl s ∈ Subgroup.centralizer ({spXg x} : Set (gsp 3 K))
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply Subtype.ext
    exact congrArg (fun s : StatedSp 3 K => (s : GL (Fin 3 ⊕ Fin 3) K)) hs'
  have hcomm : (⁅CS, CS⁆).map incl ≤ ⁅M, M⁆ := by
    rw [Subgroup.map_commutator]
    exact Subgroup.commutator_mono hmapC hmapC
  have hk' : k ∈ ⁅CS, CS⁆ := by
    have : spPullAll x ≤ ⁅CS, CS⁆ := by
      refine iSup_le fun h => iSup_le fun hh => ?_
      have hquasi := spPull_isQuasisimple (spBlockFacts_nontrivial hp5 hq2 blocks h hh.1) hh.2
      calc spPull x (h : K[X]) = ⁅spPull x (h : K[X]), spPull x (h : K[X])⁆ :=
            ((Subgroup.isPerfect_iff).1 hquasi.1).symm
        _ ≤ ⁅CS, CS⁆ := Subgroup.commutator_mono (spPull_le_centralizer _ _)
            (spPull_le_centralizer _ _)
    exact this hk
  have hw' : w ∈ ⁅CS, CS⁆ := by
    by_cases hl : SpFixedListed x
    · have hquasi := spFixedFactor_isQuasisimple hK hℓ hf blocks hl h42
      have : spFixedFactor x ≤ ⁅CS, CS⁆ := by
        calc spFixedFactor x = ⁅spFixedFactor x, spFixedFactor x⁆ :=
              ((Subgroup.isPerfect_iff).1 hquasi.1).symm
          _ ≤ ⁅CS, CS⁆ := Subgroup.commutator_mono (spFixedFactor_le_centralizer _)
              (spFixedFactor_le_centralizer _)
      exact this hw
    · rw [eq_one_of_not_listed hp hp5 blocks hl hw hwp]
      exact one_mem _
  exact mul_mem (hcomm ⟨k, hk', rfl⟩) (hcomm ⟨w, hw', rfl⟩)

theorem spBlockGSp_conjAut_inj [NeZero r] [Finite K] [CharP K 2]
    (hinj : Function.Injective (MulAut.conj : StatedProj (StatedSp r K) →*
      MulAut (StatedProj (StatedSp r K)))) {x : StatedSp r K} {a : K[X]} {u : gsp r K}
    (hu : u ∈ spBlockGSp x a) (h1 : SymplecticHigher.conjAut r K u = 1) : u = 1 := by
  have hker := spBlockGSp_le_ker_multiplier (x := x) a hu
  have hS : (u : GL (Fin r ⊕ Fin r) K) ∈ StatedSp r K := by
    rw [SymplecticHigher.ker_multiplier] at hker
    exact hker
  have h1' : MulAut.conj (proj r K ⟨u, hS⟩) = SymplecticHigher.conjAut r K u := by
    have := conjAut_statedSp (r := r) (K := K) ⟨u, hS⟩
    have e : (⟨((⟨u, hS⟩ : StatedSp r K) : GL (Fin r ⊕ Fin r) K),
        statedSp_le_gsp (⟨u, hS⟩ : StatedSp r K).2⟩ : gsp r K) = u := Subtype.ext rfl
    rw [e] at this
    exact this.symm
  have h2 : proj r K ⟨u, hS⟩ = 1 := hinj (h1'.trans (h1.trans (map_one _).symm))
  have h4 : (proj r K).ker = ⊥ :=
    (SymplecticHigher.ker_proj).trans
      (CFSG.Timmesfeld.ClassicalOrders.statedScalars_subgroupOf_statedSp_eq_bot r)
  have h3 : (⟨u, hS⟩ : StatedSp r K) ∈ (proj r K).ker := h2
  rw [h4, Subgroup.mem_bot] at h3
  apply Subtype.ext
  exact congrArg (fun s : StatedSp r K => (s : GL (Fin r ⊕ Fin r) K)) h3

theorem spBlockGSp_center_pow {ℓ f p : ℕ} [NeZero r] [Finite K] {x : StatedSp r K} (hp : p.Prime)
    (hp5 : 5 ≤ p) (hq : 3 < ℓ ^ f) (hK : Nat.card K = ℓ ^ f)
    (H : AltPrimaryData (spForm r K) (spLin r K x)) (blocks : SpPrimaryBlocks ℓ f p x (proj r K x))
    (a : primaryFactors (spEnd x)) (hpm : ¬ p ∣ primaryMultiplicity (spEnd x) (a : K[X])) :
    ∀ u ∈ spBlockGSp x (a : K[X]), (∀ g ∈ spBlockGSp x (a : K[X]), u * g = g * u) → u ^ p = 1 →
      u = 1 := by
  intro u hu hcen hup
  have hfacts := spBlockFacts hp5 hq hK H.squarefree blocks a
  have hu' : gspLin r K u ∈ specialBlock (spForm r K) (spLin r K x) (a : K[X]) :=
    mem_spBlockGSp.1 hu
  have hcomm' : ∀ g ∈ specialBlock (spForm r K) (spLin r K x) (a : K[X]),
      Commute (gspLin r K u) g := by
    intro g hg
    rw [← map_spBlockGSp] at hg
    obtain ⟨g₀, hg₀, rfl⟩ := hg
    show gspLin r K u * gspLin r K g₀ = gspLin r K g₀ * gspLin r K u
    rw [← map_mul, ← map_mul, hcen g₀ hg₀]
  have hup' : (gspLin r K u) ^ p = 1 := by rw [← map_pow, hup, map_one]
  have := sp_specialBlock_center_pow hp H a hpm hfacts hu' hcomm' hup'
  exact gspLin_injective (by rw [this, map_one])

end CFSG.RankThree.PartOne.S15K
