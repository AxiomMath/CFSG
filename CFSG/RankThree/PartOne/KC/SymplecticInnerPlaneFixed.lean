module

public import CFSG.RankThree.PartOne.KC.SymplecticInnerPlaneDefs
public import CFSG.RankThree.PartOne.KC.SymplecticIsotypicOrbits

public section

namespace CFSG.RankThree.PartOne

open Polynomial Module CFSG.RankThree.Classical CFSG.LocalAnalysis.ComponentInitial
  CFSG.Assembly.LowTwoRank CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCUnitary
  CFSG.RankThree.PartOne.KCSpIsotypic
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)
open scoped commutatorElement

section Fixed

variable {r : ℕ} {K : Type} [Field K]

theorem spFixedFactor_le_centralizer (x : StatedSp r K) :
    spFixedFactor x ≤ Subgroup.centralizer ({x} : Set (StatedSp r K)) := fun _ hg =>
  Subgroup.mem_centralizer_singleton_iff.mpr (mem_spSupported.mp hg).1

theorem spFixedFactor_normalized (x : StatedSp r K) :
    ∀ m ∈ Subgroup.centralizer ({x} : Set (StatedSp r K)), ∀ g ∈ spFixedFactor x,
      m * g * m⁻¹ ∈ spFixedFactor x := by
  intro m hm g hg
  have hm' : spLin r K m ∈ unitaryCentralizer (spForm r K) (spLin r K x) := by
    rw [unitaryCentralizer_spForm_eq_map]
    exact Subgroup.mem_map_of_mem _ hm
  have := conj_mem_supportedUnitary hm' (show spLin r K g ∈
    supportedUnitary (spForm r K) (spLin r K x) {X - 1} from hg)
  change spLin r K (m * g * m⁻¹) ∈ supportedUnitary (spForm r K) (spLin r K x) {X - 1}
  rwa [map_mul, map_mul, map_inv]

theorem X_sub_one_mem_primaryFactors (x : StatedSp r K) (h : 0 < spFixedDim x) :
    (X - 1 : K[X]) ∈ primaryFactors (spEnd x) := by
  by_contra hnm
  have hbot := primaryComponent_eq_bot_of_not_mem irreducible_X_sub_one monic_X_sub_one hnm
  have : spFixedDim x = 0 := by
    unfold spFixedDim
    rw [hbot]
    simp
  omega

theorem spFixed_hq {ℓ f p : ℕ} {x : StatedSp r K}
    (blocks : SpPrimaryBlocks ℓ f p x (proj r K x)) (hlist : SpFixedListed x)
    (h42 : ¬ (spFixedDim x = 4 ∧ Nat.card K = 2)) (hq2 : 2 ≤ Nat.card K) :
    4 ≤ Nat.card K ∨ (Nat.card K = 3 ∧ 4 ≤ spFixedDim x) ∨
      (Nat.card K = 2 ∧ 6 ≤ spFixedDim x) := by
  obtain ⟨s, hs, -⟩ := blocks.rank
  have hd : spFixedDim x = 2 * s := hs
  obtain ⟨h2, h22⟩ := hlist
  omega

variable [Finite K]

omit [Finite K] in
theorem spFixedFactor_isQuasisimple {ℓ f p : ℕ} (hK : Nat.card K = ℓ ^ f) (hℓ : ℓ.Prime)
    (hf : 1 ≤ f) {x : StatedSp r K} (blocks : SpPrimaryBlocks ℓ f p x (proj r K x))
    (hlist : SpFixedListed x) (h42 : ¬ (spFixedDim x = 4 ∧ Nat.card K = 2)) :
    CFSG.IsQuasisimple ↥(spFixedFactor x) := by
  have hq2 : 2 ≤ Nat.card K := by
    rw [hK]
    exact hℓ.two_le.trans (Nat.le_self_pow (by omega) ℓ)
  have hmem := X_sub_one_mem_primaryFactors x (by have := hlist.1; omega)
  obtain ⟨φ, -⟩ := blocks.fixedFactor hmem
  have hB : ((spForm r K).restrict (primaryComponent (spEnd x) (X - 1))).IsAlt :=
    fun v => spForm_isAlt (v : Fin r ⊕ Fin r → K)
  have hq := isQuasisimple_sesqUnitaryGroup_of_alt hB blocks.fixed_nondegenerate hlist.1
    (spFixed_hq blocks hlist h42 hq2)
  exact CFSG.LocalCores.isQuasisimple_of_mulEquiv φ.symm hq

theorem card_spFixedFactor_of_dim_two {ℓ f p : ℕ} {x : StatedSp r K}
    (blocks : SpPrimaryBlocks ℓ f p x (proj r K x)) (hd : spFixedDim x = 2) :
    Nat.card ↥(spFixedFactor x) = Nat.card K * (Nat.card K ^ 2 - 1) := by
  have hmem := X_sub_one_mem_primaryFactors x (by omega)
  obtain ⟨φ, -⟩ := blocks.fixedFactor hmem
  have hB : ((spForm r K).restrict (primaryComponent (spEnd x) (X - 1))).IsAlt :=
    fun v => spForm_isAlt (v : Fin r ⊕ Fin r → K)
  obtain ⟨s', hs', ⟨e⟩⟩ := exists_mulEquiv_sesqUnitaryGroup_statedSp hB blocks.fixed_nondegenerate
  have hs1 : s' = 1 := by
    have : finrank K (primaryComponent (spEnd x) (X - 1)) = 2 := hd
    omega
  subst hs1
  change Nat.card ↥(spSupported x {X - 1}) = _
  rw [Nat.card_congr (φ.trans e).toEquiv, SymplecticFlag.card_statedSp]
  simp [Finset.Icc_self]

theorem eq_one_of_not_listed {ℓ f p : ℕ} {x : StatedSp r K}
    (hp : p.Prime) (hp5 : 5 ≤ p) (blocks : SpPrimaryBlocks ℓ f p x (proj r K x))
    (hnl : ¬ SpFixedListed x) {w : StatedSp r K} (hw : w ∈ spFixedFactor x)
    (hwp : w ^ p = 1) : w = 1 := by
  classical
  obtain ⟨s, hs, -⟩ := blocks.rank
  have hd : spFixedDim x = 2 * s := hs
  have hnl' : 2 ≤ spFixedDim x → spFixedDim x = 2 ∧ (Nat.card K = 2 ∨ Nat.card K = 3) := by
    intro h2
    by_contra hc
    exact hnl ⟨h2, hc⟩
  by_cases h0 : 2 ≤ spFixedDim x
  ·
    obtain ⟨hd2, hq23⟩ := hnl' h0
    have hw' : w ∈ spSupported x {X - 1} := hw
    have hcard0 := card_spFixedFactor_of_dim_two blocks hd2
    have hcard : Nat.card ↥(spSupported x {X - 1}) = 6 ∨
        Nat.card ↥(spSupported x {X - 1}) = 24 := by
      rcases hq23 with h | h
      · left
        change Nat.card ↥(spFixedFactor x) = 6
        rw [hcard0, h]
        norm_num
      · right
        change Nat.card ↥(spFixedFactor x) = 24
        rw [hcard0, h]
        norm_num
    have h1 : orderOf (⟨w, hw'⟩ : ↥(spSupported x {X - 1})) ∣ p :=
      orderOf_dvd_of_pow_eq_one (Subtype.ext (by simpa using hwp))
    have h2 : orderOf (⟨w, hw'⟩ : ↥(spSupported x {X - 1})) ∣
        Nat.card ↥(spSupported x {X - 1}) := orderOf_dvd_natCard _
    rcases (Nat.dvd_prime hp).mp h1 with h3 | h3
    · exact congrArg Subtype.val (orderOf_eq_one_iff.mp h3)
    · exfalso
      rw [h3] at h2
      rcases hcard with h | h
      · rw [h] at h2
        have := Nat.le_of_dvd (by norm_num) h2
        interval_cases p <;> first | omega | exact absurd hp (by norm_num)
      · rw [h] at h2
        have := Nat.le_of_dvd (by norm_num) h2
        interval_cases p <;> first | omega | exact absurd hp (by norm_num)
  ·
    have hd0 : spFixedDim x = 0 := by omega
    have hbot : primaryComponent (spEnd x) (X - 1) = ⊥ := by
      have : finrank K (primaryComponent (spEnd x) (X - 1)) = 0 := hd0
      exact Submodule.finrank_eq_zero.mp this
    have hsq := blocks.isInternal.submodule_iSup_eq_top
    have hall : ∀ v : Fin r ⊕ Fin r → K, spEnd w v = v := by
      intro v
      have hv : v ∈ ⨆ k : primaryFactors (spEnd x), primaryComponent (spEnd x) (k : K[X]) := by
        rw [hsq]; trivial
      refine Submodule.iSup_induction (fun k : primaryFactors (spEnd x) =>
        primaryComponent (spEnd x) (k : K[X])) (motive := fun v => spEnd w v = v) hv ?_ ?_ ?_
      · intro k v hv
        by_cases hk : (k : K[X]) = X - 1
        · rw [hk, hbot] at hv
          rw [(Submodule.mem_bot K).mp hv, map_zero]
        · exact (mem_spSupported.mp hw).2 k k.2 (by simpa using hk) v hv
      · exact map_zero _
      · intro a b ha hb
        rw [map_add, ha, hb]
    apply spLin_injective
    refine Units.ext (LinearMap.ext fun v => ?_)
    rw [map_one]
    exact hall v

end Fixed

end CFSG.RankThree.PartOne
