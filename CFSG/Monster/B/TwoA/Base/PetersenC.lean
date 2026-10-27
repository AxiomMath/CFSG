
module

public import CFSG.Monster.B.TwoA.Base.PetersenCBase

public import CFSG.Monster.B.TwoA.Base.PetersenA

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice
  CFSG.Monster.Griess CFSG.Monster.Visible CFSG.Monster.Generated CFSG.Monster.B.Short
  CFSG.Monster.B CFSG.Monster.VisQuot CFSG.Monster.ScalarKernel CFSG.Monster.B.Co2
  CFSG.Monster.Lifts CFSG.Monster.VisCert CFSG.Sporadic.Mathieu

open scoped Pointwise

theorem pairSpace_UR4
    (c : Fin 15) : PairSpace (UR4 c) (R4 c) := by
  have h := pairSpace_U3.map_monomial (kmon (aut4 c) (aut4_mem_Ppair c)).2
  rwa [show aut4 c • A2 = R4 c from perm4_smul_A2 c] at h

theorem pairSpace_UR5
    (d : Fin 10) : PairSpace (UR5 d) (R5 d) := by
  have h := pairSpace_U4.map_monomial (kmon (aut5 d) (aut5_mem_Ppair d)).2
  rwa [show aut5 d • A3 = R5 d from perm5_smul_A3 d] at h

theorem Y4_eq_conjSub
    (c : Fin 15) : ∃ g ∈ K3, conjSub g E4 = Y4 c := by
  obtain ⟨g, hg, hgU⟩ := exists_K3_conjSub_EU (aut4_mem_Ppair c) (perm4_fix c 2 (by decide))
    (perm4_fix c 3 (by decide))
  exact ⟨g, hg, by rw [E4_eq_EU, hgU]; rfl⟩

theorem Y5_eq_conjSub
    (d : Fin 10) : ∃ g ∈ K3, conjSub g E5 = Y5 d := by
  obtain ⟨g, hg, hgU⟩ := exists_K3_conjSub_EU (aut5_mem_Ppair d) (perm5_fix d 2 (by decide))
    (perm5_fix d 3 (by decide))
  exact ⟨g, hg, by rw [E5_eq_EU, hgU]; rfl⟩

theorem Y4_mem_X4
    (c : Fin 15) : Y4 c ∈ X4 := by
  rw [X4_eq]
  obtain ⟨g, hg, h⟩ := Y4_eq_conjSub c
  exact ⟨g, hg, h.symm⟩

theorem Y5_mem_X5
    (d : Fin 10) : Y5 d ∈ X5 := by
  rw [X5_eq]
  obtain ⟨g, hg, h⟩ := Y5_eq_conjSub d
  exact ⟨g, hg, h.symm⟩

theorem Y4_le_Y5_iff
    (c : Fin 15) (d : Fin 10) : Y4 c ≤ Y5 d ↔ R4 c ⊆ R5 d := by
  rw [Y4, Y5, EU_le_EU_iff, (pairSpace_UR4 c).le_iff (pairSpace_UR5 d)]

theorem Y4_injective :
    Function.Injective Y4 := by
  intro c c' h
  have h1 : UR4 c = UR4 c' := le_antisymm (EU_le_EU_iff.1 h.le) (EU_le_EU_iff.1 h.ge)
  exact R4_injective (Finset.Subset.antisymm
    (((pairSpace_UR4 c).le_iff (pairSpace_UR4 c')).1 h1.le)
    (((pairSpace_UR4 c').le_iff (pairSpace_UR4 c)).1 h1.ge))

theorem Y5_injective :
    Function.Injective Y5 := by
  intro d d' h
  have h1 : UR5 d = UR5 d' := le_antisymm (EU_le_EU_iff.1 h.le) (EU_le_EU_iff.1 h.ge)
  exact R5_injective (Finset.Subset.antisymm
    (((pairSpace_UR5 d).le_iff (pairSpace_UR5 d')).1 h1.le)
    (((pairSpace_UR5 d').le_iff (pairSpace_UR5 d)).1 h1.ge))

instance finite_X4 :
    Finite X4 := Nat.finite_of_card_ne_zero (by rw [natCard_X4]; decide)

instance finite_X5 :
    Finite X5 := Nat.finite_of_card_ne_zero (by rw [natCard_X5]; decide)

@[expose] def enum4 :
    Fin 15 ≃ X4 :=
  Equiv.ofBijective (fun c => ⟨Y4 c, Y4_mem_X4 c⟩)
    (Function.Injective.bijective_of_nat_card_le
      (fun c c' h => Y4_injective (congrArg Subtype.val h)) (by rw [natCard_X4, Nat.card_fin]))

@[expose] def enum5 :
    Fin 10 ≃ X5 :=
  Equiv.ofBijective (fun d => ⟨Y5 d, Y5_mem_X5 d⟩)
    (Function.Injective.bijective_of_nat_card_le
      (fun d d' h => Y5_injective (congrArg Subtype.val h)) (by rw [natCard_X5, Nat.card_fin]))

theorem coe_enum4
    (c : Fin 15) : ((enum4 c : X4) : Subgroup Dfull) = Y4 c := rfl

theorem coe_enum5
    (d : Fin 10) : ((enum5 d : X5) : Subgroup Dfull) = Y5 d := rfl

@[expose] def vertEquiv :
    X5 ≃ PetVert :=
  enum5.symm.trans (Equiv.ofBijective vlab vlab_bijective)

@[expose] def edgeEquiv :
    X4 ≃ PetEdge :=
  enum4.symm.trans (Equiv.ofBijective edgeLab ⟨edgeLab_injective, edgeLab_surjective⟩)

theorem vertEquiv_enum5
    (d : Fin 10) : vertEquiv (enum5 d) = vlab d := by
  rw [vertEquiv, Equiv.trans_apply, Equiv.symm_apply_apply]
  rfl

theorem edgeEquiv_enum4
    (c : Fin 15) : edgeEquiv (enum4 c) = edgeLab c := by
  rw [edgeEquiv, Equiv.trans_apply, Equiv.symm_apply_apply]
  rfl

theorem le_iff_mem_edge
    (F : X4) (G : X5) :
    (F : Subgroup Dfull) ≤ G ↔ vertEquiv G ∈ (edgeEquiv F).1 := by
  obtain ⟨c, rfl⟩ := enum4.surjective F
  obtain ⟨d, rfl⟩ := enum5.surjective G
  rw [coe_enum4, coe_enum5, vertEquiv_enum5, edgeEquiv_enum4, Y4_le_Y5_iff, R4_subset_R5_iff]
  change _ ↔ vlab d ∈ ({vlab (ev4 c 0), vlab (ev4 c 1)} : Finset PetVert)
  rw [Finset.mem_insert, Finset.mem_singleton, vlab_injective.eq_iff, vlab_injective.eq_iff]

theorem rank_three_upper_residue_Petersen :
    Nat.card X4 = 15 ∧ Nat.card X5 = 10 ∧
    (∀ k ∈ K3, ∀ F ∈ X4, conjSub k F ∈ X4) ∧ (∀ k ∈ K3, ∀ G ∈ X5, conjSub k G ∈ X5) ∧
    (∀ F ∈ X4, ∀ G ∈ X5, F ≤ G → ∀ F' ∈ X4, ∀ G' ∈ X5, F' ≤ G' →
      ∃ k ∈ K3, conjSub k F = F' ∧ conjSub k G = G') ∧
    (∃ (φ : X5 ≃ PetVert) (χ : X4 ≃ PetEdge),
      ∀ (F : X4) (G : X5), (F : Subgroup Dfull) ≤ G ↔ φ G ∈ (χ F).1) ∧
    (∀ (F : X4) (G : X5), (F : Subgroup Dfull) ≤ G ↔ vertEquiv G ∈ (edgeEquiv F).1) ∧
    (∀ d : Fin 10, ((enum5 d : X5) : Subgroup Dfull) = EU (UR5 d) ∧
      PairSpace (UR5 d) (R5 d) ∧ (vertEquiv (enum5 d) : Finset ℕ) = tetLab d) ∧
    (∀ (d : Fin 10) (k : Fin 5),
      (k : ℕ) + 1 ∈ tetLab d ↔ ∀ D ∈ R5 d, ¬ ((D : Finset (Fin 24)) ⊆ tetrad k)) ∧
    (∀ c : Fin 15, ((enum4 c : X4) : Subgroup Dfull) = EU (UR4 c) ∧ PairSpace (UR4 c) (R4 c)) :=
  ⟨natCard_X4, natCard_X5, fun _ hk _ hF => conjSub_mem_X4 hk hF,
    fun _ hk _ hG => conjSub_mem_X5 hk hG,
    fun _ hF _ hG hFG _ hF' _ hG' hFG' => incident_transitive hF hG hFG hF' hG' hFG',
    ⟨vertEquiv, edgeEquiv, le_iff_mem_edge⟩, le_iff_mem_edge,
    fun d => ⟨rfl, pairSpace_UR5 d, by rw [vertEquiv_enum5]; rfl⟩, mem_tetLab_iff,
    fun c => ⟨rfl, pairSpace_UR4 c⟩⟩

end CFSG.Monster.B.TwoA
