module

public import CFSG.Quasithin.H13.U3S1349L

public section

namespace CFSG.Quasithin.H13.NQS134

open Subgroup Equiv CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.Quasithin.H13.A6

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G}

omit [Finite G] in
theorem eq_or_eq_of_overgroups {T X A₁ A₂ B C Y : Subgroup G}
    (hcls : ∀ Y : Subgroup G, T ≤ Y → Y ≤ X → Y = T ∨ Y = A₁ ∨ Y = A₂ ∨ Y = X)
    (hTB : T ≤ B) (hBX : B ≤ X) (hBT : B ≠ T) (hBX' : B ≠ X)
    (hTC : T ≤ C) (hCX : C ≤ X) (hCT : C ≠ T) (hCX' : C ≠ X) (hBC : B ≠ C)
    (hTY : T ≤ Y) (hYX : Y ≤ X) (hYT : Y ≠ T) (hYX' : Y ≠ X) : Y = B ∨ Y = C := by
  have key : ∀ {E : Subgroup G}, T ≤ E → E ≤ X → E ≠ T → E ≠ X → E = A₁ ∨ E = A₂ := by
    intro E hTE hEX hET hEX'
    rcases hcls E hTE hEX with h | h | h | h
    · exact absurd h hET
    · exact Or.inl h
    · exact Or.inr h
    · exact absurd h hEX'
  rcases key hTB hBX hBT hBX' with hB | hB <;> rcases key hTC hCX hCT hCX' with hC | hC <;>
    rcases key hTY hYX hYT hYX' with hY | hY
  · exact absurd (hB.trans hC.symm) hBC
  · exact absurd (hB.trans hC.symm) hBC
  · exact Or.inl (hY.trans hB.symm)
  · exact Or.inr (hY.trans hC.symm)
  · exact Or.inr (hY.trans hC.symm)
  · exact Or.inl (hY.trans hB.symm)
  · exact absurd (hB.trans hC.symm) hBC
  · exact absurd (hB.trans hC.symm) hBC

theorem eight_ii (S : A6.Setting134 G T L V) (h1345 : Stmt13_4_5) {H₂ : Subgroup G}
    (hstar : IsHStar T (normalizer (L : Set G)) H₂)
    (hL2TM : U3.l2Of S ⊔ T ≤ normalizer (L : Set G)) (h2T : U3.l2Of S ⊔ T ≠ T)
    (hL2H₂ : ¬ U3.l2Of S ⊔ T ≤ H₂)
    (hInH0 : InH T (H₂ ⊔ (U3.l2Of S ⊔ T)))
    (hH0M : ¬ H₂ ⊔ (U3.l2Of S ⊔ T) ≤ normalizer (L : Set G))
    (hii : U3.Concl1347ii T H₂ (U3.l2Of S ⊔ T))
    (hmax : ∀ X : Subgroup G, InH (H₂ ⊔ (U3.l2Of S ⊔ T)) X → X = H₂ ⊔ (U3.l2Of S ⊔ T)) :
    H₂ ⊔ (U3.l2Of S ⊔ T) = normalizer (thompsonJ T : Set G) ∧
      InM T (H₂ ⊔ (U3.l2Of S ⊔ T)) ∧
      ∀ X : Subgroup G, IsHStar T (normalizer (L : Set G)) X →
        X ≤ H₂ ⊔ (U3.l2Of S ⊔ T) → X = H₂ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hT2 : IsPGroup 2 T := S.h13.sylow.1
  have hT1 : T ≠ ⊥ := fun h => S.irr.2.1 (le_bot_iff.1 (h ▸ S.V_le_T))
  have hJ1 : thompsonJ T ≠ ⊥ := S1414.thompsonJ_ne_bot hT2 hT1
  have hJT : thompsonJ T ≤ T := iSup₂_le fun _ hA => hA.1
  have hJ2 : IsPGroup 2 ↥(thompsonJ T) := hT2.to_le hJT
  have hTH0 : T ≤ H₂ ⊔ (U3.l2Of S ⊔ T) := le_sup_right.trans le_sup_right
  obtain ⟨K₀, hH0K, hKc, -, -, hKq, hH0J, -⟩ := hii
  have hNJ : normalizer (thompsonJ T : Set G) = H₂ ⊔ (U3.l2Of S ⊔ T) := by
    refine hmax _ ⟨hH0J, fun h => hJ1 (le_bot_iff.1 ?_)⟩
    rw [← h]
    exact LieType.BorelTits.le_pCoreOf_normalizer 2 _ hJ2
  have hloc : IsTwoLocal (H₂ ⊔ (U3.l2Of S ⊔ T)) := ⟨thompsonJ T, hJ1, hJ2, hNJ.symm⟩
  have hInM : InM T (H₂ ⊔ (U3.l2Of S ⊔ T)) := by
    refine ⟨⟨hloc, fun Y hY hH0Y => ?_⟩, hTH0⟩
    obtain ⟨P, hP1, hP2, rfl⟩ := hY
    refine hmax _ ⟨hH0Y, fun h => hP1 (le_bot_iff.1 ?_)⟩
    rw [← h]
    exact LieType.BorelTits.le_pCoreOf_normalizer 2 _ hP2
  refine ⟨hNJ.symm, hInM, fun X hX hXH0 => ?_⟩
  have hK0H0 : K₀ ≤ H₂ ⊔ (U3.l2Of S ⊔ T) := le_sup_left.trans hH0K.symm.le
  have hH0sol : ¬ Group.IsSolvable ↥(H₂ ⊔ (U3.l2Of S ⊔ T)) := fun hs =>
    hKc.1 (U3.eq_bot_of_perfect_of_le_solvable hs hKc.2.1 hK0H0)
  have hH0N : H₂ ⊔ (U3.l2Of S ⊔ T) ≤ normalizer (K₀ : Set G) :=
    ((h1345 G T L V S _ hInH0 hH0M hH0sol).2 K₀ hKc).2.1
  have hTsylH0 : IsSylowTwoOf T (H₂ ⊔ (U3.l2Of S ⊔ T)) :=
    A5.isSylowTwoOf_of_le S.h13.sylow hTH0
  have hK0L2 : ¬ K₀ ≤ U3.l2Of S ⊔ T := fun h =>
    hH0M (hH0K.le.trans (sup_le (h.trans hL2TM) S.T_le_NL))
  have hH0q : quasithinO2QuotientIso (H₂ ⊔ (U3.l2Of S ⊔ T)) SL3.S :=
    U3.quot_SL3_of_sup hTsylH0 hH0N hH0K hKq le_sup_right le_sup_right h2T hK0L2
  obtain ⟨P₀, X₁, X₂, hP, hP', hc, hX₁, hX₂, hX₁₂, hX₂₁⟩ := A6.modelData_SL3.exists_data
  obtain ⟨A₁, A₂, -, -, -, -, -, -, -, -, hcls⟩ :=
    A6.overgroups_transport hH0q hTsylH0 hP hP' hc hX₁ hX₂ hX₁₂ hX₂₁
  have hH₂M : ¬ H₂ ≤ normalizer (L : Set G) := hstar.2.1
  by_cases hXH : X = H₂ ⊔ (U3.l2Of S ⊔ T)
  · exact (hX.2.2 H₂ hstar.1 (hXH ▸ le_sup_left) hH₂M).symm
  have hXT : X ≠ T := fun h => hX.2.1 (h ▸ S.T_le_NL)
  have hH₂T : H₂ ≠ T := fun h => hH₂M (h ▸ S.T_le_NL)
  have hH₂H0 : H₂ ≠ H₂ ⊔ (U3.l2Of S ⊔ T) := fun h => hL2H₂ (h ▸ le_sup_right)
  have hL2H0 : U3.l2Of S ⊔ T ≠ H₂ ⊔ (U3.l2Of S ⊔ T) := fun h => hH0M (h ▸ hL2TM)
  have hH₂L2 : H₂ ≠ U3.l2Of S ⊔ T := fun h => hH₂M (h ▸ hL2TM)
  rcases eq_or_eq_of_overgroups hcls hstar.1.1 le_sup_left hH₂T hH₂H0 le_sup_right le_sup_right
    h2T hL2H0 hH₂L2 hX.1.1 hXH0 hXT hXH with h | h
  · exact h
  · exact absurd (h ▸ hL2TM) hX.2.1

end CFSG.Quasithin.H13.NQS134
