module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.ConjSetCard
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22d
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma53
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.GF3Lie
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.StatementsA
public import CFSG.Quasithin.Vol2.Ch10SecKGA318
public import CFSG.RankThree.PartTwo.Sec3.TwoThreeStructure

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.CGT.Timmesfeld75 (IsTI)
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem not_dvd_card_inf_of_mem_conjSetOf {D : Data G} {V₀ V L : Subgroup G} {r q : ℕ}
    (hC : Ctx17_6 D V₀ V L r q) (h17_7 : R17_7At D V₀ V L r q hC)
    (h7 : IsL2Over17 (Bar2 L) 7) {K : Subgroup G} (hK : K ∈ conjSetOf D.M L) :
    ∀ g : G, g ∉ D.M →
      ¬ 3 ∣ Nat.card ↥(K ⊓ (D.M.map (MulAut.conj g).toMonoidHom : Subgroup G)) := by
  obtain ⟨u, huM, rfl⟩ := hK
  intro g hg
  have hgu : u⁻¹ * g ∉ D.M := by
    intro h
    exact hg (by simpa [mul_assoc] using D.M.mul_mem huM h)
  have h := h17_7.2 h7 (u⁻¹ * g) hgu
  have h3 : ¬ 3 ∣ Nat.card
      ↥(L ⊓ (D.M.map (MulAut.conj (u⁻¹ * g)).toMonoidHom : Subgroup G)) := by
    intro hd
    exact h ⟨Nat.prime_three, hd⟩
  have hinf : L.map (MulAut.conj u).toMonoidHom ⊓ D.M.map (MulAut.conj g).toMonoidHom =
      (L ⊓ D.M.map (MulAut.conj (u⁻¹ * g)).toMonoidHom).map (MulAut.conj u).toMonoidHom := by
    rw [Subgroup.map_inf L (D.M.map (MulAut.conj (u⁻¹ * g)).toMonoidHom)
      (MulAut.conj u).toMonoidHom (MulAut.conj u).injective,
      CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p22d_map_conj_map_conj]
    rw [show u * (u⁻¹ * g) = g by group]
  rw [hinf, Subgroup.card_map_of_injective (MulAut.conj u).injective]
  exact h3

theorem exists_three_conj_of_two_lt_ncard {M L : Subgroup G}
    (h : 2 < (conjSetOf M L).ncard) :
    ∃ x ∈ M, ∃ y ∈ M, L.map (MulAut.conj x).toMonoidHom ≠ L ∧
      L.map (MulAut.conj y).toMonoidHom ≠ L ∧
      L.map (MulAut.conj y).toMonoidHom ≠ L.map (MulAut.conj x).toMonoidHom := by
  have h3 : 3 ≤ (conjSetOf M L).ncard := h
  obtain ⟨t, ht_sub, ht_card⟩ :=
    Set.exists_subset_card_eq (s := conjSetOf M L) (n := 3) h3
  obtain ⟨A, B, C, hAB, hAC, hBC, rfl⟩ := Set.ncard_eq_three.mp ht_card
  have hA : A ∈ conjSetOf M L := ht_sub (by simp)
  have hB : B ∈ conjSetOf M L := ht_sub (by simp)
  have hC : C ∈ conjSetOf M L := ht_sub (by simp)
  obtain ⟨a, haM, rfl⟩ := hA
  obtain ⟨b, hbM, rfl⟩ := hB
  obtain ⟨c, hcM, rfl⟩ := hC
  by_cases hA' : L.map (MulAut.conj a).toMonoidHom = L
  · have hB' : L.map (MulAut.conj b).toMonoidHom ≠ L := by
      intro hb
      exact hAB (by rw [hA', hb])
    have hC' : L.map (MulAut.conj c).toMonoidHom ≠ L := by
      intro hc
      exact hAC (by rw [hA', hc])
    exact ⟨b, hbM, c, hcM, hB', hC', fun h' => hBC h'.symm⟩
  · by_cases hB' : L.map (MulAut.conj b).toMonoidHom = L
    · have hC' : L.map (MulAut.conj c).toMonoidHom ≠ L := by
        intro hc
        exact hBC (by rw [hB', hc])
      exact ⟨a, haM, c, hcM, hA', hC', fun h' => hAC h'.symm⟩
    · exact ⟨a, haM, b, hbM, hA', hB', fun h' => hAB h'.symm⟩


theorem exists_conj_pair_of_not_normal {D : Data G} {L : Subgroup G}
    (h3 : ¬ 2 < (conjSetOf D.M L).ncard)
    (hN : ¬ (L.subgroupOf (L ⊔ D.T)).Normal) :
    ∃ L₂ : Subgroup G,
      (∃ t ∈ D.T, L₂ = CFSG.Quasithin.conjSubgroup L t) ∧ L ≠ L₂ ∧
        (∀ t ∈ D.T, CFSG.Quasithin.conjSubgroup L t = L ∨
          CFSG.Quasithin.conjSubgroup L t = L₂) := by
  have hTnot : ¬ D.T ≤ normalizer (L : Set G) := by
    intro hT
    apply hN
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
      (sup_le Subgroup.le_normalizer hT)
  change ¬ (D.T : Set G) ⊆ (normalizer (L : Set G) : Set G) at hTnot
  rw [Set.not_subset] at hTnot
  obtain ⟨t, ht, htN⟩ := hTnot
  have hLt : L.map (MulAut.conj t).toMonoidHom ≠ L := by
    intro h
    exact htN (Subgroup.mem_normalizer_iff_map_conj_eq.mpr h)
  have h2le : 2 ≤ (conjSetOf D.M L).ncard := by
    have hsub : ({L, L.map (MulAut.conj t).toMonoidHom} : Set (Subgroup G)) ⊆
        conjSetOf D.M L := by
      intro K hK
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hK
      rcases hK with rfl | rfl
      · refine ⟨1, D.M.one_mem, ?_⟩
        ext x
        simp [MulAut.conj_apply]
      · exact ⟨t, D.sylowM.le ht, rfl⟩
    have hc : ({L, L.map (MulAut.conj t).toMonoidHom} : Set (Subgroup G)).ncard = 2 :=
      Set.ncard_pair hLt.symm
    have hle := Set.ncard_le_ncard hsub (Set.toFinite (conjSetOf D.M L))
    omega
  have hc2 : (conjSetOf D.M L).ncard = 2 := le_antisymm (by omega) h2le
  have hself : L ∈ conjSetOf D.M L := by
    refine ⟨1, D.M.one_mem, ?_⟩
    ext x
    simp [MulAut.conj_apply]
  obtain ⟨L₂, hL₂ne, hclass⟩ :=
    exists_pair_eq_conjSetOf_of_ncard_eq_two hself hc2
  have hKmem : L.map (MulAut.conj t).toMonoidHom = L₂ := by
    have hmem : L.map (MulAut.conj t).toMonoidHom ∈ ({L, L₂} : Set (Subgroup G)) := by
      rw [← hclass]
      exact ⟨t, D.sylowM.le ht, rfl⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
    exact hmem.resolve_left hLt
  have hex : ∃ s ∈ D.T, L₂ = CFSG.Quasithin.conjSubgroup L s := by
    refine ⟨t⁻¹, D.T.inv_mem ht, ?_⟩
    rw [← hKmem, CFSG.Quasithin.conjSubgroup, inv_inv]
  have hall : ∀ s ∈ D.T, CFSG.Quasithin.conjSubgroup L s = L ∨
      CFSG.Quasithin.conjSubgroup L s = L₂ := by
    intro s hs
    have hmem : CFSG.Quasithin.conjSubgroup L s ∈ ({L, L₂} : Set (Subgroup G)) := by
      rw [← hclass]
      exact ⟨s⁻¹, D.sylowM.le (D.T.inv_mem hs), by rw [CFSG.Quasithin.conjSubgroup]⟩
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hmem
  exact ⟨L₂, hex, hL₂ne.symm, hall⟩

@[expose] def Gap17_15_threeConjInFSq (D : Data G) (V₀ V L : Subgroup G) (r q : ℕ)
    (hC : Ctx17_6 D V₀ V L r q) : Prop :=
  IsL2Over17 (Bar2 L) 7 →
    CFSG.Quasithin.F6.IsPGL2 7 (Bar2 (L ⊔ NTL17 D L)) →
      CFSG.LocalAnalysis.WeakClosure81.InFSq 1 (L ⊔ D.T)

@[expose] def Gap17_15_swapPairInner (D : Data G) (V₀ V L : Subgroup G) (r q : ℕ)
    (hC : Ctx17_6 D V₀ V L r q) : Prop :=
  IsL2Over17 (Bar2 L) 7 → ¬ IsL2Over17 (Bar2 (L ⊔ D.T)) 7 →
    IsL2Over17 (Bar2 (L ⊔ NTL17 D L)) 7 →
    ¬ (L.subgroupOf (L ⊔ D.T)).Normal →
      ∃ X₁ X₂ : Subgroup G, X₁ ≤ L ∧ X₂ ≤ L ∧ Nat.card X₁ = 3 ∧ Nat.card X₂ = 3 ∧
        Permutes X₁ (NTL17 D L) ∧ Permutes X₂ (NTL17 D L) ∧ L ≤ X₁ ⊔ X₂ ⊔ D.T

@[expose] def Gap17_15_swapInFSq (D : Data G) (V₀ V L : Subgroup G) (r q : ℕ)
    (hC : Ctx17_6 D V₀ V L r q) : Prop :=
  IsL2Over17 (Bar2 L) 7 → ¬ IsL2Over17 (Bar2 (L ⊔ D.T)) 7 →
    IsL2Over17 (Bar2 (L ⊔ NTL17 D L)) 7 →
    ¬ (L.subgroupOf (L ⊔ D.T)).Normal →
      ∀ X : Subgroup G, X ≤ L → Nat.card X = 3 → Permutes X (NTL17 D L) →
        CFSG.LocalAnalysis.WeakClosure81.InFSq 1 (X ⊔ D.T)

@[expose] def Gap17_15_swapSplit (D : Data G) (V₀ V L : Subgroup G) (r q : ℕ)
    (hC : Ctx17_6 D V₀ V L r q) : Prop :=
  IsL2Over17 (Bar2 L) 7 → ¬ (L.subgroupOf (L ⊔ D.T)).Normal →
    IsL2Over17 (Bar2 (L ⊔ NTL17 D L)) 7 ∨
      CFSG.Quasithin.F6.IsPGL2 7 (Bar2 (L ⊔ NTL17 D L))

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

end
