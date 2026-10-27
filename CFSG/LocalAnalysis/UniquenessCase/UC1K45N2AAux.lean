module

public import CFSG.LocalAnalysis.UniquenessCase.UC1K45N2AStab
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK.UC46

open Subgroup
open scoped BigOperators

section FixedPoint

variable {W : Type} [AddCommGroup W] [Module (ZMod 2) W]

lemma orbit_ncard_eq_index (ρ : Alt5 →* (W ≃ₗ[ZMod 2] W)) (s : W) :
    (Set.range fun g : Alt5 => ρ g s).ncard = (stab ρ s).index := by
  letI : MulAction Alt5 W := MulAction.compHom W ρ
  have hstab : stab ρ s = MulAction.stabilizer Alt5 s := by
    ext g
    rw [mem_stab]
    show (ρ g s = s) ↔ g • s = s
    rw [MulAction.compHom_smul_def, LinearEquiv.smul_def]
  have horbit : (Set.range fun g : Alt5 => ρ g s) = MulAction.orbit Alt5 s := by
    ext x
    constructor
    · rintro ⟨g, rfl⟩
      exact MulAction.mem_orbit_iff.mpr
        ⟨g, by rw [MulAction.compHom_smul_def, LinearEquiv.smul_def]⟩
    · intro hx
      obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.mp hx
      exact ⟨g, by rw [MulAction.compHom_smul_def, LinearEquiv.smul_def] at hg; exact hg⟩
  rw [horbit, hstab, MulAction.index_stabilizer Alt5 s]

lemma orbit_subset_of_invariant (ρ : Alt5 →* (W ≃ₗ[ZMod 2] W)) (S : Finset W)
    (hInv : ∀ g, ∀ s ∈ S, ρ g s ∈ S) {s : W} (hs : s ∈ S) :
    Set.range (fun g : Alt5 => ρ g s) ⊆ (↑S : Set W) := by
  rintro x ⟨g, rfl⟩
  exact hInv g s hs

lemma orbit_ncard_le_card_of_invariant (ρ : Alt5 →* (W ≃ₗ[ZMod 2] W)) (S : Finset W)
    (hInv : ∀ g, ∀ s ∈ S, ρ g s ∈ S) {s : W} (hs : s ∈ S) :
    (Set.range (fun g : Alt5 => ρ g s)).ncard ≤ S.card := by
  have h := Set.ncard_le_ncard (orbit_subset_of_invariant ρ S hInv hs) (Finset.finite_toSet S)
  rwa [Set.ncard_coe_finset] at h

lemma five_le_index_of_not_fixed (ρ : Alt5 →* (W ≃ₗ[ZMod 2] W)) {s : W}
    (hfix : ¬ ∀ g, ρ g s = s) : 5 ≤ (stab ρ s).index := by
  have hstab : stab ρ s ≠ ⊤ := by
    intro htop
    apply hfix
    intro g
    have hg : g ∈ stab ρ s := by rw [htop]; exact Subgroup.mem_top g
    exact (mem_stab ρ s g).mp hg
  exact CFSG.Quasithin.Kleidman.F204.alt5_index_ge_five_of_ne_top (stab ρ s) hstab

lemma index_le_six_of_not_fixed_of_card_seven (ρ : Alt5 →* (W ≃ₗ[ZMod 2] W)) (S : Finset W)
    (hInv : ∀ g, ∀ s ∈ S, ρ g s ∈ S) (hcard : S.card = 7) {s : W} (hs : s ∈ S)
    (hfix : ¬ ∀ g, ρ g s = s) : (stab ρ s).index ≤ 6 := by
  have hidx7 : (stab ρ s).index ≤ 7 := by
    rw [← orbit_ncard_eq_index ρ s]
    have hle := orbit_ncard_le_card_of_invariant ρ S hInv hs
    rwa [hcard] at hle
  have hidvd : (stab ρ s).index ∣ 60 := by
    have h := Subgroup.index_dvd_card (stab ρ s)
    rwa [card_alt5] at h
  by_contra h
  push Not at h
  have h7 : (stab ρ s).index = 7 := le_antisymm hidx7 h
  rw [h7] at hidvd
  norm_num at hidvd

lemma exists_mem_notMem_orbit_of_card_seven (ρ : Alt5 →* (W ≃ₗ[ZMod 2] W)) (S : Finset W)
    (hInv : ∀ g, ∀ s ∈ S, ρ g s ∈ S) (hcard : S.card = 7) {s : W} (hs : s ∈ S)
    (hfix : ¬ ∀ g, ρ g s = s) :
    ∃ t ∈ S, t ∉ Set.range (fun g : Alt5 => ρ g s) := by
  have hidx6 := index_le_six_of_not_fixed_of_card_seven ρ S hInv hcard hs hfix
  have hsub := orbit_subset_of_invariant ρ S hInv hs
  have hlt : (Set.range (fun g : Alt5 => ρ g s)).ncard < (↑S : Set W).ncard := by
    rw [orbit_ncard_eq_index, Set.ncard_coe_finset, hcard]
    omega
  have hne : (Set.range fun g : Alt5 => ρ g s) ≠ (↑S : Set W) := by
    intro h
    rw [h] at hlt
    exact lt_irrefl _ hlt
  have hproper : (Set.range fun g : Alt5 => ρ g s) ⊂ (↑S : Set W) :=
    Set.ssubset_iff_subset_ne.mpr ⟨hsub, hne⟩
  obtain ⟨t, htS, htO⟩ := Set.exists_of_ssubset hproper
  rw [Finset.mem_coe] at htS
  exact ⟨t, htS, htO⟩

lemma eq_of_orbit_subset_card_le_two (ρ : Alt5 →* (W ≃ₗ[ZMod 2] W)) {t : W} {T : Set W}
    (hTfin : T.Finite) (hsub : Set.range (fun g : Alt5 => ρ g t) ⊆ T) (hT : T.ncard ≤ 2) :
    ∀ g, ρ g t = t := by
  by_contra hfix
  have hidx5 := five_le_index_of_not_fixed ρ hfix
  have hle : (Set.range fun g : Alt5 => ρ g t).ncard ≤ 2 :=
    le_trans (Set.ncard_le_ncard hsub hTfin) hT
  rw [orbit_ncard_eq_index] at hle
  omega

theorem exists_fixed_of_invariant_card_le_four
    (ρ : Alt5 →* (W ≃ₗ[ZMod 2] W)) (S : Finset W)
    (hInv : ∀ g, ∀ s ∈ S, ρ g s ∈ S) (hne : S.Nonempty) (hcard : S.card ≤ 4) :
    ∃ s ∈ S, ∀ g, ρ g s = s := by
  obtain ⟨s, hs⟩ := hne
  by_cases hfix : ∀ g, ρ g s = s
  · exact ⟨s, hs, hfix⟩
  · exfalso
    have hidx5 := five_le_index_of_not_fixed ρ hfix
    have hle := orbit_ncard_le_card_of_invariant ρ S hInv hs
    rw [← orbit_ncard_eq_index] at hidx5
    omega

theorem exists_fixed_of_invariant_card_seven
    (ρ : Alt5 →* (W ≃ₗ[ZMod 2] W)) (S : Finset W)
    (hInv : ∀ g, ∀ s ∈ S, ρ g s ∈ S) (hcard : S.card = 7) :
    ∃ s ∈ S, ∀ g, ρ g s = s := by
  obtain ⟨s, hs⟩ := Finset.card_pos.mp (by omega : 0 < S.card)
  by_cases hfix : ∀ g, ρ g s = s
  · exact ⟨s, hs, hfix⟩
  · obtain ⟨t, htS, htO⟩ := exists_mem_notMem_orbit_of_card_seven ρ S hInv hcard hs hfix
    refine ⟨t, htS, ?_⟩
    by_cases hfixt : ∀ g, ρ g t = t
    · exact hfixt
    · exfalso
      have hsub : Set.range (fun g : Alt5 => ρ g t) ⊆
          (↑S : Set W) \ Set.range (fun g : Alt5 => ρ g s) := by
        rintro x ⟨g, rfl⟩
        refine ⟨hInv g t htS, ?_⟩
        rintro ⟨h, hh⟩
        simp only at hh
        exact htO ⟨g⁻¹ * h, by
          show ρ (g⁻¹ * h) s = t
          rw [map_mul, LinearEquiv.mul_apply, hh]
          simp⟩
      have hle : ((↑S : Set W) \ Set.range (fun g : Alt5 => ρ g s)).ncard ≤ 2 := by
        rw [Set.ncard_sdiff' (orbit_subset_of_invariant ρ S hInv hs) (Finset.finite_toSet S)]
        rw [Set.ncard_coe_finset, hcard, orbit_ncard_eq_index]
        have hidx5 := five_le_index_of_not_fixed ρ hfix
        have hidx6 := index_le_six_of_not_fixed_of_card_seven ρ S hInv hcard hs hfix
        omega
      exact hfixt (eq_of_orbit_subset_card_le_two ρ
        ((Finset.finite_toSet S).subset Set.sdiff_subset) hsub hle)

end FixedPoint

section Irreducible

variable {W : Type} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]

lemma exists_mem_ne_zero_of_ne_bot (U : Submodule (ZMod 2) W) (hbot : U ≠ ⊥) :
    ∃ u ∈ U, u ≠ 0 := by
  by_contra h
  apply hbot
  rw [Submodule.eq_bot_iff]
  intro x hx
  by_contra hx0
  exact h ⟨x, hx, hx0⟩

lemma two_le_card_of_ne_bot (U : Submodule (ZMod 2) W) (hbot : U ≠ ⊥) :
    2 ≤ Nat.card U := by
  classical
  letI : Fintype W := Fintype.ofFinite W
  obtain ⟨u, huU, hu0⟩ := exists_mem_ne_zero_of_ne_bot U hbot
  have hT : (Finset.univ.filter (fun w : W => w ∈ U)).card = Nat.card U := by
    rw [← Fintype.card_subtype (fun w : W => w ∈ U), ← Nat.card_eq_fintype_card]
  rw [← hT]
  have hsub : ({0, u} : Finset W) ⊆ Finset.univ.filter (fun w : W => w ∈ U) := by
    intro x hx
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ x, ?_⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact U.zero_mem
    · exact huU
  calc 2 = ({0, u} : Finset W).card := (Finset.card_pair (Ne.symm hu0)).symm
    _ ≤ _ := Finset.card_le_card hsub

lemma card_lt_sixteen_of_ne_top (hW : Nat.card W = 16) (U : Submodule (ZMod 2) W)
    (htop : U ≠ ⊤) : Nat.card U < 16 := by
  have hne : (↑U : Set W) ≠ Set.univ := by
    intro h
    apply htop
    rw [Submodule.eq_top_iff']
    intro x
    have : x ∈ (↑U : Set W) := by rw [h]; exact Set.mem_univ x
    exact this
  have h := Set.ncard_lt_card hne
  rw [hW] at h
  change (↑U : Set W).ncard < 16
  exact h

lemma card_dvd_sixteen (hW : Nat.card W = 16) (U : Submodule (ZMod 2) W) :
    Nat.card U ∣ 16 := by
  have hcardU : Nat.card U = Nat.card U.toAddSubgroup :=
    Nat.card_congr (Equiv.subtypeEquivRight (fun x => (Submodule.mem_toAddSubgroup U).symm))
  have h := AddSubgroup.card_mul_index U.toAddSubgroup
  refine ⟨U.toAddSubgroup.index, ?_⟩
  rw [hcardU]
  exact hW.symm.trans h.symm

lemma invariant_submodule_card_eq_two_or_four_or_eight (hW : Nat.card W = 16)
    (U : Submodule (ZMod 2) W) (hbot : U ≠ ⊥) (htop : U ≠ ⊤) :
    Nat.card U = 2 ∨ Nat.card U = 4 ∨ Nat.card U = 8 := by
  have h2 := two_le_card_of_ne_bot U hbot
  have hlt := card_lt_sixteen_of_ne_top hW U htop
  have hdvd := card_dvd_sixteen hW U
  interval_cases Nat.card U <;> norm_num at hdvd
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr rfl)

lemma card_nonzero_of_submodule (U : Submodule (ZMod 2) W) [Fintype W] [DecidableEq W]
    [DecidablePred (· ∈ U)] :
    (Finset.univ.filter (fun w : W => w ∈ U ∧ w ≠ 0)).card = Nat.card U - 1 := by
  classical
  have h0T : (0 : W) ∈ Finset.univ.filter (fun w : W => w ∈ U) := by
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ 0, U.zero_mem⟩
  have hT : (Finset.univ.filter (fun w : W => w ∈ U)).card = Nat.card U := by
    rw [← Fintype.card_subtype (fun w : W => w ∈ U), ← Nat.card_eq_fintype_card]
  have hEq : Finset.univ.filter (fun w : W => w ∈ U ∧ w ≠ 0) =
      (Finset.univ.filter (fun w : W => w ∈ U)).filter (fun w => w ≠ 0) := by
    change Finset.univ.filter (fun w : W => w ∈ U ∧ w ≠ 0) = _
    rw [Finset.filter_filter]
  rw [hEq, Finset.filter_ne', Finset.card_erase_of_mem h0T, hT]

lemma invariant_submodule_contradiction (ρ : Alt5 →* (W ≃ₗ[ZMod 2] W))
    (h0 : ∀ w : W, (∀ g, ρ g w = w) → w = 0) (U : Submodule (ZMod 2) W)
    (hInv : ∀ g, U.map (ρ g : W →ₗ[ZMod 2] W) ≤ U) (hbot : U ≠ ⊥)
    (hcases : Nat.card U = 2 ∨ Nat.card U = 4 ∨ Nat.card U = 8) : False := by
  classical
  letI : Fintype W := Fintype.ofFinite W
  obtain ⟨u, huU, hu0⟩ := exists_mem_ne_zero_of_ne_bot U hbot
  let S : Finset W := Finset.univ.filter (fun w => w ∈ U ∧ w ≠ 0)
  have hS_card : S.card = Nat.card U - 1 := card_nonzero_of_submodule U
  have hS_inv : ∀ g, ∀ s ∈ S, ρ g s ∈ S := by
    intro g s hs
    rw [Finset.mem_filter] at hs ⊢
    obtain ⟨-, hsU, hs0⟩ := hs
    refine ⟨Finset.mem_univ _, hInv g (Submodule.mem_map.mpr ⟨s, hsU, rfl⟩), ?_⟩
    intro h
    exact hs0 ((ρ g).injective (by rw [h, map_zero]))
  have hS_ne : S.Nonempty := by
    refine ⟨u, ?_⟩
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ u, huU, hu0⟩
  have hcontra : ∀ s ∈ S, (∀ g, ρ g s = s) → False := by
    intro s hs hfix
    exact (Finset.mem_filter.mp hs).2.2 (h0 s hfix)
  rcases hcases with h2 | h4 | h8
  · have hSc : S.card ≤ 4 := by omega
    obtain ⟨s, hs, hfix⟩ := exists_fixed_of_invariant_card_le_four ρ S hS_inv hS_ne hSc
    exact hcontra s hs hfix
  · have hSc : S.card ≤ 4 := by omega
    obtain ⟨s, hs, hfix⟩ := exists_fixed_of_invariant_card_le_four ρ S hS_inv hS_ne hSc
    exact hcontra s hs hfix
  · have hSc : S.card = 7 := by omega
    obtain ⟨s, hs, hfix⟩ := exists_fixed_of_invariant_card_seven ρ S hS_inv hSc
    exact hcontra s hs hfix

theorem invariant_eq_bot_or_top
    (ρ : Alt5 →* (W ≃ₗ[ZMod 2] W)) (hW : Nat.card W = 16)
    (h0 : ∀ w : W, (∀ g, ρ g w = w) → w = 0)
    (U : Submodule (ZMod 2) W) (hInv : ∀ g, U.map (ρ g : W →ₗ[ZMod 2] W) ≤ U) :
    U = ⊥ ∨ U = ⊤ := by
  by_cases hbot : U = ⊥
  · exact Or.inl hbot
  · right
    by_contra htop
    exact invariant_submodule_contradiction ρ h0 U hInv hbot
      (invariant_submodule_card_eq_two_or_four_or_eight hW U hbot htop)

end Irreducible

section Main

variable {W : Type} [AddCommGroup W] [Module (ZMod 2) W]

def linComb (b : Fin 5 → W) : (Fin 5 → ZMod 2) →ₗ[ZMod 2] W where
  toFun v := ∑ i, v i • b i
  map_add' v w := by
    simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' c v := by
    simp only [Pi.smul_apply, RingHom.id_apply, smul_assoc, Finset.smul_sum]

lemma linComb_single (b : Fin 5 → W) (i : Fin 5) :
    linComb b (Pi.single i (1 : ZMod 2) : Fin 5 → ZMod 2) = b i := by
  change (∑ j, (Pi.single i (1 : ZMod 2) : Fin 5 → ZMod 2) j • b j) = b i
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    rw [Pi.single_eq_of_ne hj, zero_smul]
  · intro h
    exact absurd (Finset.mem_univ i) h

lemma linComb_equivariant (b : Fin 5 → W) (ρ : Alt5 →* (W ≃ₗ[ZMod 2] W))
    (η : Alt5 →* Equiv.Perm (Fin 5)) (g : Alt5)
    (hb : ∀ i, ρ g (b i) = b (η g i)) (v : Fin 5 → ZMod 2) :
    ρ g (linComb b v) = linComb b (fun i => v ((η g)⁻¹ i)) := by
  change ρ g (∑ i, v i • b i) = ∑ i, v ((η g)⁻¹ i) • b i
  rw [map_sum]
  simp only [map_smul]
  simp_rw [hb]
  exact Fintype.sum_equiv (η g) (fun i => v i • b (η g i))
    (fun j => v ((η g)⁻¹ j) • b j) (fun i => by simp)

end Main

end CFSG.LocalAnalysis.UniquenessCase.UCK.UC46

end
