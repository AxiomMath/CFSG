module

public import CFSG.Quasithin.Background.E2TwoProofFam
public import CFSG.Quasithin.Background.E2TwoProofPerm
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246C127Even6

public section

namespace CFSG.Quasithin

open CFSG.QuasithinUnique CFSG.QuasithinUnique.L246C127 Equiv

namespace E2P

namespace A6

abbrev L1 : Subgroup (Perm (Fin 6)) := Subgroup.closure {g | g ∈ Even6.L1}

abbrev L2 : Subgroup (Perm (Fin 6)) := Subgroup.closure {g | g ∈ Even6.L2}

abbrev A : Subgroup (Perm (Fin 6)) := alternatingGroup (Fin 6)

abbrev U : Subgroup ↥A := Even6.D.subgroupOf A

abbrev P1 : Subgroup ↥A := L1.subgroupOf A

abbrev P2 : Subgroup ↥A := L2.subgroupOf A

theorem card_D : Nat.card Even6.D = 8 :=
  lat_card Even6.cert Even6.cert_check 0 (by decide)

theorem card_L1 : Nat.card L1 = 24 :=
  lat_card Even6.cert Even6.cert_check 1 (by decide)

theorem card_L2 : Nat.card L2 = 24 :=
  lat_card Even6.cert Even6.cert_check 2 (by decide)

theorem L1_le : L1 ≤ alternatingGroup (Fin 6) := by
  rw [Subgroup.closure_le]
  intro g hg
  have h : ∀ g ∈ Even6.L1, Perm.sign g = 1 := by decide +kernel
  exact Equiv.Perm.mem_alternatingGroup.mpr (h g hg)

theorem L2_le : L2 ≤ alternatingGroup (Fin 6) := by
  rw [Subgroup.closure_le]
  intro g hg
  have h : ∀ g ∈ Even6.L2, Perm.sign g = 1 := by decide +kernel
  exact Equiv.Perm.mem_alternatingGroup.mpr (h g hg)

@[expose] def b45 (x : Fin 6) : Bool := decide (x = 4 ∨ x = 5)

theorem L2_le_boolStab : L2 ≤ boolStab b45 := by
  rw [Subgroup.closure_le]
  intro g hg
  have h : ∀ g ∈ Even6.L2, ∀ x : Fin 6, b45 (g x) = b45 x := by decide +kernel
  exact h g hg

theorem L1_not_le : ¬ L1 ≤ boolStab b45 := by
  intro h
  have hg : Even6.L1.getD 2 1 ∈ L1 := Subgroup.subset_closure (by decide)
  have h1 := h hg 4
  revert h1
  decide +kernel

theorem L1_ne_L2 : L1 ≠ L2 := fun h => L1_not_le (h ▸ L2_le_boolStab)

theorem overgroups (Y : Subgroup ↥A)
    (hY : U ≤ Y) :
    Y = U ∨ Y = P1 ∨ Y = P2 ∨ Y = ⊤ := by
  obtain ⟨j, hj, hjA, hYj, hcard⟩ :=
    lat_cases Even6.cert Even6.closure_mGens Even6.cert_check Y hY
  have hcY : Nat.card Y = Even6.cert.sizes.getD j 0 := by
    rw [hYj, card_subgroupOf_of_le hjA, hcard]
  have hj4 : j < 4 := hj
  interval_cases j
  · exact Or.inl hYj
  · exact Or.inr (Or.inl hYj)
  · exact Or.inr (Or.inr (Or.inl hYj))
  · refine Or.inr (Or.inr (Or.inr (Subgroup.eq_top_of_card_eq _ ?_)))
    rw [hcY, Even6.card_alt]
    rfl

theorem ne_top_of_card {H : Subgroup (Perm (Fin 6))} (hH : H ≤ A) (hc : Nat.card H = 24) :
    H.subgroupOf A ≠ ⊤ := by
  intro h
  have h1 := card_subgroupOf_of_le hH
  rw [h, Subgroup.card_top, Even6.card_alt, hc] at h1
  exact absurd h1 (by decide)

theorem D_le_L1 : Even6.D ≤ L1 :=
  Subgroup.closure_mono fun g hg => by
    have h : Even6.L1 = Even6.tGens ++ [Even6.L1.getD 2 1] := rfl
    rw [Set.mem_ofPred_eq, h]
    exact List.mem_append_left _ hg

theorem D_le_L2 : Even6.D ≤ L2 :=
  Subgroup.closure_mono fun g hg => by
    have h : Even6.L2 = Even6.tGens ++ [Even6.L2.getD 2 1] := rfl
    rw [Set.mem_ofPred_eq, h]
    exact List.mem_append_left _ hg

theorem subgroupOf_ne_of_ne {H₁ H₂ : Subgroup (Perm (Fin 6))} (h₁ : H₁ ≤ A) (h₂ : H₂ ≤ A)
    (hne : H₁ ≠ H₂) : H₁.subgroupOf A ≠ H₂.subgroupOf A := by
  intro h
  apply hne
  rw [← Subgroup.map_subgroupOf_eq_of_le h₁, ← Subgroup.map_subgroupOf_eq_of_le h₂, h]

theorem P_ne : P1 ≠ P2 :=
  subgroupOf_ne_of_ne L1_le L2_le L1_ne_L2

theorem eq_of_le_card {P P' : Subgroup ↥A} (h : P ≤ P')
    (hc : Nat.card P = 24) (hc' : Nat.card P' = 24) : P = P' :=
  Subgroup.eq_of_le_of_card_ge h (by rw [hc, hc'])

theorem card_P1 : Nat.card P1 = 24 := by
  rw [card_subgroupOf_of_le L1_le, card_L1]

theorem card_P2 : Nat.card P2 = 24 := by
  rw [card_subgroupOf_of_le L2_le, card_L2]

theorem card_U : Nat.card U = 8 := by
  rw [card_subgroupOf_of_le Even6.D_le, card_D]

theorem isCoatom_iff (Y : Subgroup ↥A) (hY : U ≤ Y) :
    IsCoatom Y ↔ Y = P1 ∨ Y = P2 := by
  have hU1 : U ≤ P1 := Subgroup.subgroupOf_mono _ D_le_L1
  have hU2 : U ≤ P2 := Subgroup.subgroupOf_mono _ D_le_L2
  have hP1 := ne_top_of_card L1_le card_L1
  have hP2 := ne_top_of_card L2_le card_L2
  have hUP1 : U ≠ P1 := fun h => absurd (card_U.symm.trans (h ▸ card_P1)) (by decide)
  constructor
  · intro hc
    rcases overgroups Y hY with rfl | rfl | rfl | rfl
    · exact absurd (hc.2 _ (lt_of_le_of_ne hU1 hUP1)) hP1
    · exact Or.inl rfl
    · exact Or.inr rfl
    · exact absurd rfl hc.1
  · rintro (rfl | rfl)
    · refine ⟨hP1, fun Z hZ => ?_⟩
      rcases overgroups Z (hU1.trans hZ.le) with rfl | rfl | rfl | rfl
      · exact absurd (hU1.trans_lt hZ) (lt_irrefl _)
      · exact absurd hZ (lt_irrefl _)
      · exact absurd (eq_of_le_card hZ.le card_P1 card_P2) P_ne
      · rfl
    · refine ⟨hP2, fun Z hZ => ?_⟩
      rcases overgroups Z (hU2.trans hZ.le) with rfl | rfl | rfl | rfl
      · exact absurd (hU2.trans_lt hZ) (lt_irrefl _)
      · exact absurd (eq_of_le_card hZ.le card_P2 card_P1).symm P_ne
      · exact absurd hZ (lt_irrefl _)
      · rfl

theorem inf_le : P1 ⊓ P2 ≤
    Subgroup.normalizer ((U : Subgroup ↥A) : Set ↥A) := by
  have hU : U ≤ P1 ⊓ P2 :=
    le_inf (Subgroup.subgroupOf_mono _ D_le_L1) (Subgroup.subgroupOf_mono _ D_le_L2)
  rcases overgroups _ hU with h | h | h | h
  · rw [h]
    exact Subgroup.le_normalizer
  · exact absurd (eq_of_le_card (h ▸ inf_le_right) card_P1 card_P2) P_ne
  · exact absurd (eq_of_le_card (h ▸ inf_le_left) card_P2 card_P1).symm P_ne
  · exact absurd (top_le_iff.mp (h ▸ inf_le_left)) (ne_top_of_card L1_le card_L1)

end A6

variable {X : Type} [Group X] [Finite X] {K T M : Subgroup X}

theorem ASHyp.a6 (hX : ASHyp K T M)
    (e : ↥K ≃* alternatingGroup (Fin 6)) :
    E2.IsDiagramNontrivial T K (T ⊓ K) ∧ E2.IsBorelIn K (M ⊓ K) :=
  hX.rankTwo e Even6.isSylow_D (Subgroup.subgroupOf_mono _ A6.D_le_L1)
    (Subgroup.subgroupOf_mono _ A6.D_le_L2) A6.P_ne A6.isCoatom_iff A6.inf_le

end E2P

end CFSG.Quasithin
