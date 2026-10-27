module

public import Mathlib.GroupTheory.IsPerfect
import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.GN516.GOrbPerfect

public section

namespace CFSG.RankThree.PartTwo.Sec15.Sylow155R1

open scoped commutatorElement

theorem res1340_le_normalizer_of_commutator_le {G : Type*} [Group G] [Finite G]
    {X W W' : Subgroup G} (hX : Group.IsPerfect ↥X) (hW'2 : IsPGroup 2 W')
    (hW'X : W' ≤ Subgroup.normalizer (X : Set G)) (hWX : ⁅W, X⁆ ≤ W') :
    W ≤ Subgroup.normalizer (X : Set G) := by
  intro w hw
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  have hperf : ∀ f : G →* G, ⁅X.map f, X.map f⁆ = X.map f := fun f => by
    rw [← Subgroup.map_commutator, Subgroup.isPerfect_iff.1 hX]
  have hle : X.map (MulAut.conj w : G →* G) ≤ X ⊔ W' := by
    rintro _ ⟨x, hx, rfl⟩
    have h1 : ⁅w, x⁆ * x ∈ W' ⊔ X :=
      Subgroup.mul_mem_sup (hWX (Subgroup.commutator_mem_commutator hw hx)) hx
    rw [sup_comm]
    simpa [commutatorElement_def] using h1
  have hYX : X.map (MulAut.conj w : G →* G) ≤ X :=
    CFSG.AGLEmbeddingD2.Tits.GN516.Perf.le_of_perfect_of_le_sup (p := 2) (hperf _) hle hW'X hW'2
  exact Subgroup.eq_of_le_of_card_ge hYX
    (Subgroup.card_map_of_injective (MulAut.conj w).injective).ge

theorem res1340_le_normalizer_of_stable {G : Type*} [Group G] [Finite G]
    {X B P : Subgroup G} (hX : Group.IsPerfect ↥X) (hP2 : IsPGroup 2 P) (hXB : X ≤ B)
    (hBP : B ≤ Subgroup.normalizer (P : Set G)) (hBX : B ≤ Subgroup.normalizer (X : Set G))
    (hst : ∀ Z : Subgroup G, Z ≤ P → B ≤ Subgroup.normalizer (Z : Set G) → ⁅Z, X⁆ = Z →
      Z ≤ Subgroup.normalizer (X : Set G)) :
    P ≤ Subgroup.normalizer (X : Set G) := by
  obtain ⟨W, hW0, hWs⟩ : ∃ W : ℕ → Subgroup G, W 0 = P ∧ ∀ n, W (n + 1) = ⁅W n, X⁆ :=
    ⟨fun n => (fun H : Subgroup G => ⁅H, X⁆)^[n] P, rfl,
      fun n => Function.iterate_succ_apply' _ _ _⟩
  have hWB : ∀ n, B ≤ Subgroup.normalizer (W n : Set G) := by
    intro n
    induction n with
    | zero => rwa [hW0]
    | succ n ih =>
      intro b hb
      rw [Subgroup.mem_normalizer_iff_map_conj_eq, hWs, Subgroup.map_commutator,
        Subgroup.mem_normalizer_iff_map_conj_eq.1 (ih hb),
        Subgroup.mem_normalizer_iff_map_conj_eq.1 (hBX hb)]
  have hle : ∀ n, W (n + 1) ≤ W n := fun n =>
    (hWs n).le.trans (Subgroup.le_normalizer_iff_commutator_le_left.1 (hXB.trans (hWB n)))
  have hanti : Antitone W := antitone_nat_of_succ_le hle
  have hWP : ∀ n, W n ≤ P := fun n => (hanti n.zero_le).trans hW0.le
  obtain ⟨k, hk⟩ : ∃ k, W (k + 1) = W k := by
    have : Finite (Subgroup G) := Finite.of_injective _ SetLike.coe_injective
    obtain ⟨m, n, hne, hmn⟩ := Finite.exists_ne_map_eq_of_infinite W
    rcases lt_or_gt_of_ne hne with h | h
    · exact ⟨m, le_antisymm (hle m) (hmn.le.trans (hanti (by omega)))⟩
    · exact ⟨n, le_antisymm (hle n) (hmn.symm.le.trans (hanti (by omega)))⟩
  have hWk : W k ≤ Subgroup.normalizer (X : Set G) :=
    hst (W k) (hWP k) (hWB k) ((hWs k).symm.trans hk)
  have hdown : ∀ n i, k ≤ i + n → W i ≤ Subgroup.normalizer (X : Set G) := by
    intro n
    induction n with
    | zero => exact fun i hi => (hanti (by omega)).trans hWk
    | succ n ih =>
      exact fun i hi => res1340_le_normalizer_of_commutator_le hX (hP2.to_le (hWP (i + 1)))
        (ih (i + 1) (by omega)) (hWs i).ge
  have h0 := hdown k 0 (by omega)
  rwa [hW0] at h0

end CFSG.RankThree.PartTwo.Sec15.Sylow155R1
