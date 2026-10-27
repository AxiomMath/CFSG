module

public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4E6Chain
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4E6Dich
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4E6FrameDef
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4TwistOuter
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4Inputs2

public section

namespace CFSG.StandardType.TableCRes

open CFSG.StandardType.KGCentE6 (iform_comm_E6 iform_add_left_E6 iform_smul_left_E6
  iform_sub_left_E6 iform_right_neg_E6)

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Blueprint
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus
open CFSG.Assembly (LargeEvenLabel LargeEvenInLambda2 LargeEvenLieTag LargeEvenMarking
  LargeEvenSplit)

@[expose] def stdFpos : List (List ℤ) :=
  [intv 0 3, intv 0 4, intv 0 5, intv 1 3, intv 1 4, intv 1 5, intv 2 3, intv 2 4, intv 2 5]

structure A5SwapPos (ρ : (Fin Tag.E6.rank → ℤ) → (Fin Tag.E6.rank → ℤ))
    (δ : Fin 5 → (Fin Tag.E6.rank → ℤ)) : Prop where
  s0 : ∃ c ∈ stdX2, ρ (δ 0) = tcChainVec c δ
  s1 : ∃ c ∈ stdX2, ρ (δ 1) = tcChainVec c δ
  s2 : ∃ c ∈ stdFpos, ρ (δ 2) = tcChainVec c δ
  s3 : ∃ c ∈ stdX1, ρ (δ 3) = tcChainVec c δ
  s4 : ∃ c ∈ stdX1, ρ (δ 4) = tcChainVec c δ

theorem e6d_std30_fpos : ∀ c ∈ std30, c.getD 2 0 = 1 → c ∈ stdFpos := by
  decide

theorem a5SwapPos_of_frame
    {α₁ β₁ α₂ β₂ α₃ β₃ : Fin Tag.E6.rank → ℤ} (fr : E6Frame α₁ β₁ α₂ β₂ α₃ β₃)
    (r1 : IsRoot .E6 α₁) (r2 : IsRoot .E6 β₁) (a1 : iform α₁ β₁ = -1)
    (r3 : IsRoot .E6 α₂) (r4 : IsRoot .E6 β₂) (a2 : iform α₂ β₂ = -1)
    {δ : Fin 5 → (Fin Tag.E6.rank → ℤ)} (hδ : A5Chain δ)
    (h0 : δ 0 ∈ tcA2Set α₁ β₁) (h1 : δ 1 ∈ tcA2Set α₁ β₁) (h3 : δ 3 ∈ tcA2Set α₂ β₂)
    (h4 : δ 4 ∈ tcA2Set α₂ β₂) (h2 : δ 2 ∉ tcA2Set α₁ β₁ ∪ tcA2Set α₂ β₂)
    {ρ : Equiv.Perm (Fin Tag.E6.rank → ℤ)}
    (hρ1 : (ρ : (Fin Tag.E6.rank → ℤ) → (Fin Tag.E6.rank → ℤ)) '' tcA2Set α₁ β₁ = tcA2Set α₂ β₂)
    (hρ2 : (ρ : (Fin Tag.E6.rank → ℤ) → (Fin Tag.E6.rank → ℤ)) '' tcA2Set α₂ β₂ = tcA2Set α₁ β₁)
    (hu : ∀ γ, IsRoot .E6 γ → iform (ρ γ) α₃ = iform γ α₃ ∧ iform (ρ γ) β₃ = iform γ β₃)
    (hst : ∀ γ ∈ tcChainSet δ, ρ γ ∈ tcChainSet δ) :
    A5SwapPos (ρ : (Fin Tag.E6.rank → ℤ) → (Fin Tag.E6.rank → ℤ)) δ := by
  have g01 : iform (δ 0) (δ 1) = -1 := by
    rw [hδ.gram 0 1]
    decide
  have g34 : iform (δ 3) (δ 4) = -1 := by
    rw [hδ.gram 3 4]
    decide
  have hX1 : tcA2Set (δ 0) (δ 1) = tcA2Set α₁ β₁ := a2Set_eq_of_mem r1 r2 a1 h0 h1 g01
  have hX2 : tcA2Set (δ 3) (δ 4) = tcA2Set α₂ β₂ := a2Set_eq_of_mem r3 r4 a2 h3 h4 g34
  have z0 : iform (δ 0) α₃ = 0 ∧ iform (δ 0) β₃ = 0 :=
    (fr.mem (δ 0) (hδ.root 0)).1 (Set.mem_union_left _ h0)
  have z1 : iform (δ 1) α₃ = 0 ∧ iform (δ 1) β₃ = 0 :=
    (fr.mem (δ 1) (hδ.root 1)).1 (Set.mem_union_left _ h1)
  have z3 : iform (δ 3) α₃ = 0 ∧ iform (δ 3) β₃ = 0 :=
    (fr.mem (δ 3) (hδ.root 3)).1 (Set.mem_union_right _ h3)
  have z4 : iform (δ 4) α₃ = 0 ∧ iform (δ 4) β₃ = 0 :=
    (fr.mem (δ 4) (hδ.root 4)).1 (Set.mem_union_right _ h4)
  have nz2 : ¬ (iform (δ 2) α₃ = 0 ∧ iform (δ 2) β₃ = 0) :=
    fun h => h2 ((fr.mem (δ 2) (hδ.root 2)).2 h)
  have hX1mem : ∀ x ∈ tcA2Set α₁ β₁, ∃ c ∈ stdX1, x = tcChainVec c δ := by
    intro x hx
    rw [← hX1] at hx
    exact e6d_mem_X1 δ x hx
  have hX2mem : ∀ x ∈ tcA2Set α₂ β₂, ∃ c ∈ stdX2, x = tcChainVec c δ := by
    intro x hx
    rw [← hX2] at hx
    exact e6d_mem_X2 δ x hx
  have hs0 : ρ (δ 0) ∈ tcA2Set α₂ β₂ := by
    rw [← hρ1]
    exact ⟨δ 0, h0, rfl⟩
  have hs1 : ρ (δ 1) ∈ tcA2Set α₂ β₂ := by
    rw [← hρ1]
    exact ⟨δ 1, h1, rfl⟩
  have hs3 : ρ (δ 3) ∈ tcA2Set α₁ β₁ := by
    rw [← hρ2]
    exact ⟨δ 3, h3, rfl⟩
  have hs4 : ρ (δ 4) ∈ tcA2Set α₁ β₁ := by
    rw [← hρ2]
    exact ⟨δ 4, h4, rfl⟩
  obtain ⟨c, hc30, hcρ⟩ : ∃ c ∈ std30, ρ (δ 2) = tcChainVec c δ :=
    hst (δ 2) (e6d_two_mem δ)
  have hk : c.getD 2 0 = 1 := by
    have ha : c.getD 2 0 * iform (δ 2) α₃ = iform (δ 2) α₃ := by
      have h := (hu (δ 2) (hδ.root 2)).1
      rw [hcρ, e6d_iform_chainVec, z0.1, z1.1, z3.1, z4.1] at h
      linear_combination h
    have hb : c.getD 2 0 * iform (δ 2) β₃ = iform (δ 2) β₃ := by
      have h := (hu (δ 2) (hδ.root 2)).2
      rw [hcρ, e6d_iform_chainVec, z0.2, z1.2, z3.2, z4.2] at h
      linear_combination h
    by_contra hne
    have hne' : c.getD 2 0 - 1 ≠ 0 := fun h => hne (by linarith)
    have hk1 : (c.getD 2 0 - 1) * iform (δ 2) α₃ = 0 := by linear_combination ha
    have hk2 : (c.getD 2 0 - 1) * iform (δ 2) β₃ = 0 := by linear_combination hb
    exact nz2 ⟨(mul_eq_zero.1 hk1).resolve_left hne', (mul_eq_zero.1 hk2).resolve_left hne'⟩
  have hcF : c ∈ stdFpos := e6d_std30_fpos c hc30 hk
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨c0, hc0, hce0⟩ := hX2mem _ hs0
    exact ⟨c0, hc0, hce0⟩
  · obtain ⟨c1, hc1, hce1⟩ := hX2mem _ hs1
    exact ⟨c1, hc1, hce1⟩
  · exact ⟨c, hcF, hcρ⟩
  · obtain ⟨c3, hc3, hce3⟩ := hX1mem _ hs3
    exact ⟨c3, hc3, hce3⟩
  · obtain ⟨c4, hc4, hce4⟩ := hX1mem _ hs4
    exact ⟨c4, hc4, hce4⟩

theorem std_outer_disc :
    ∀ e₀ ∈ stdX2, ∀ e₁ ∈ stdX2, ip5 e₀ e₁ = -1 →
    ∀ e₂ ∈ stdFpos, ip5 e₁ e₂ = -1 → ip5 e₀ e₂ = 0 →
    ∀ e₃ ∈ stdX1, ip5 e₂ e₃ = -1 → ip5 e₁ e₃ = 0 → ip5 e₀ e₃ = 0 →
    ∀ e₄ ∈ stdX1, ip5 e₃ e₄ = -1 → ip5 e₂ e₄ = 0 → ip5 e₁ e₄ = 0 → ip5 e₀ e₄ = 0 →
      ¬ (36 : ℤ) ∣ 5 * ip5 [5, 4, 3, 2, 1] e₀ + 4 * ip5 [5, 4, 3, 2, 1] e₁ +
        3 * ip5 [5, 4, 3, 2, 1] e₂ + 2 * ip5 [5, 4, 3, 2, 1] e₃ + ip5 [5, 4, 3, 2, 1] e₄ -
        ip5 [5, 4, 3, 2, 1] [5, 4, 3, 2, 1] := by
  decide +kernel

theorem not_twistInner_chainSet_pos
    {δ : Fin 5 → (Fin Tag.E6.rank → ℤ)} (hδ : A5Chain δ)
    {ρ : Equiv.Perm (Fin Tag.E6.rank → ℤ)}
    (hρform : ∀ γ γ', iform (ρ γ) (ρ γ') = iform γ γ')
    (hρlin : ∃ σ : (Fin Tag.E6.rank → ℤ) →+ (Fin Tag.E6.rank → ℤ),
      ∀ γ, IsRoot .E6 γ → ρ γ = σ γ)
    (hs : A5SwapPos (ρ : (Fin Tag.E6.rank → ℤ) → (Fin Tag.E6.rank → ℤ)) δ) :
    ¬ twistInner (tcChainSet δ) (ρ : (Fin Tag.E6.rank → ℤ) → (Fin Tag.E6.rank → ℤ)) := by
  obtain ⟨σ, hσ⟩ := hρlin
  obtain ⟨e0, he0, hρ0⟩ := hs.s0
  obtain ⟨e1, he1, hρ1⟩ := hs.s1
  obtain ⟨e2, he2, hρ2⟩ := hs.s2
  obtain ⟨e3, he3, hρ3⟩ := hs.s3
  obtain ⟨e4, he4, hρ4⟩ := hs.s4
  have L2 : ∀ c ∈ stdX2, c.length = 5 := by decide +kernel
  have LF : ∀ c ∈ stdFpos, c.length = 5 := by decide +kernel
  have L1 : ∀ c ∈ stdX1, c.length = 5 := by decide +kernel
  have g01 : ip5 e0 e1 = -1 :=
    (ip5_eq_of_image hδ hρform (L2 e0 he0) (L2 e1 he1) hρ0 hρ1).trans (by decide)
  have g12 : ip5 e1 e2 = -1 :=
    (ip5_eq_of_image hδ hρform (L2 e1 he1) (LF e2 he2) hρ1 hρ2).trans (by decide)
  have g02 : ip5 e0 e2 = 0 :=
    (ip5_eq_of_image hδ hρform (L2 e0 he0) (LF e2 he2) hρ0 hρ2).trans (by decide)
  have g23 : ip5 e2 e3 = -1 :=
    (ip5_eq_of_image hδ hρform (LF e2 he2) (L1 e3 he3) hρ2 hρ3).trans (by decide)
  have g13 : ip5 e1 e3 = 0 :=
    (ip5_eq_of_image hδ hρform (L2 e1 he1) (L1 e3 he3) hρ1 hρ3).trans (by decide)
  have g03 : ip5 e0 e3 = 0 :=
    (ip5_eq_of_image hδ hρform (L2 e0 he0) (L1 e3 he3) hρ0 hρ3).trans (by decide)
  have g34 : ip5 e3 e4 = -1 :=
    (ip5_eq_of_image hδ hρform (L1 e3 he3) (L1 e4 he4) hρ3 hρ4).trans (by decide)
  have g24 : ip5 e2 e4 = 0 :=
    (ip5_eq_of_image hδ hρform (LF e2 he2) (L1 e4 he4) hρ2 hρ4).trans (by decide)
  have g14 : ip5 e1 e4 = 0 :=
    (ip5_eq_of_image hδ hρform (L2 e1 he1) (L1 e4 he4) hρ1 hρ4).trans (by decide)
  have g04 : ip5 e0 e4 = 0 :=
    (ip5_eq_of_image hδ hρform (L2 e0 he0) (L1 e4 he4) hρ0 hρ4).trans (by decide)
  have hc : ([5, 4, 3, 2, 1] : List ℤ).length = 5 := by decide
  have hroot : ∀ γ ∈ tcChainSet δ, IsRoot .E6 γ := fun γ hγ => isRoot_of_mem_chainSet hδ hγ
  have h6 : ∀ c ∈ std30, (6 : ℤ) ∣ ip5 [5, 4, 3, 2, 1] c := by decide +kernel
  have hself : ∀ c ∈ std30, ip5 c c = 2 := by decide +kernel
  have hsl : ∀ γ ∈ tcChainSet δ, iform γ γ = 2 := by
    intro γ hγ
    obtain ⟨c, hc30, rfl⟩ := hγ
    rw [iform_chainVec hδ.gram (std30_length c hc30) (std30_length c hc30)]
    exact hself c hc30
  have hμd : ∀ γ ∈ tcChainSet δ, (6 : ℤ) ∣ iform (tcChainVec [5, 4, 3, 2, 1] δ) γ := by
    intro γ hγ
    obtain ⟨c, hc30, rfl⟩ := hγ
    rw [iform_chainVec hδ.gram hc (std30_length c hc30)]
    exact h6 c hc30
  have hμ : tcChainVec [5, 4, 3, 2, 1] δ ∈ Submodule.span ℤ (tcChainSet δ) := by
    have h0 : δ 0 ∈ Submodule.span ℤ (tcChainSet δ) :=
      Submodule.subset_span (delta_mem_chainSet δ 0)
    have h1 : δ 1 ∈ Submodule.span ℤ (tcChainSet δ) :=
      Submodule.subset_span (delta_mem_chainSet δ 1)
    have h2 : δ 2 ∈ Submodule.span ℤ (tcChainSet δ) :=
      Submodule.subset_span (delta_mem_chainSet δ 2)
    have h3 : δ 3 ∈ Submodule.span ℤ (tcChainSet δ) :=
      Submodule.subset_span (delta_mem_chainSet δ 3)
    have h4 : δ 4 ∈ Submodule.span ℤ (tcChainSet δ) :=
      Submodule.subset_span (delta_mem_chainSet δ 4)
    rw [chainVec_five']
    exact Submodule.add_mem _ (Submodule.add_mem _ (Submodule.add_mem _ (Submodule.add_mem _
      (Submodule.smul_mem _ 5 h0) (Submodule.smul_mem _ 4 h1))
      (Submodule.smul_mem _ 3 h2)) (Submodule.smul_mem _ 2 h3)) (Submodule.smul_mem _ 1 h4)
  have hσ0 : σ (δ 0) = tcChainVec e0 δ := (hσ (δ 0) (hδ.root 0)).symm.trans hρ0
  have hσ1 : σ (δ 1) = tcChainVec e1 δ := (hσ (δ 1) (hδ.root 1)).symm.trans hρ1
  have hσ2 : σ (δ 2) = tcChainVec e2 δ := (hσ (δ 2) (hδ.root 2)).symm.trans hρ2
  have hσ3 : σ (δ 3) = tcChainVec e3 δ := (hσ (δ 3) (hδ.root 3)).symm.trans hρ3
  have hσ4 : σ (δ 4) = tcChainVec e4 δ := (hσ (δ 4) (hδ.root 4)).symm.trans hρ4
  have hσμ : σ (tcChainVec [5, 4, 3, 2, 1] δ) =
      (5 : ℤ) • tcChainVec e0 δ + (4 : ℤ) • tcChainVec e1 δ + (3 : ℤ) • tcChainVec e2 δ +
        (2 : ℤ) • tcChainVec e3 δ + tcChainVec e4 δ := by
    rw [chainVec_five']
    simp only [map_add, map_zsmul, one_smul]
    rw [hσ0, hσ1, hσ2, hσ3, hσ4]
  have hif0 : iform (tcChainVec [5, 4, 3, 2, 1] δ) (tcChainVec e0 δ) =
      ip5 [5, 4, 3, 2, 1] e0 := iform_chainVec hδ.gram hc (L2 e0 he0)
  have hif1 : iform (tcChainVec [5, 4, 3, 2, 1] δ) (tcChainVec e1 δ) =
      ip5 [5, 4, 3, 2, 1] e1 := iform_chainVec hδ.gram hc (L2 e1 he1)
  have hif2 : iform (tcChainVec [5, 4, 3, 2, 1] δ) (tcChainVec e2 δ) =
      ip5 [5, 4, 3, 2, 1] e2 := iform_chainVec hδ.gram hc (LF e2 he2)
  have hif3 : iform (tcChainVec [5, 4, 3, 2, 1] δ) (tcChainVec e3 δ) =
      ip5 [5, 4, 3, 2, 1] e3 := iform_chainVec hδ.gram hc (L1 e3 he3)
  have hif4 : iform (tcChainVec [5, 4, 3, 2, 1] δ) (tcChainVec e4 δ) =
      ip5 [5, 4, 3, 2, 1] e4 := iform_chainVec hδ.gram hc (L1 e4 he4)
  have hifc : iform (tcChainVec [5, 4, 3, 2, 1] δ) (tcChainVec [5, 4, 3, 2, 1] δ) =
      ip5 [5, 4, 3, 2, 1] [5, 4, 3, 2, 1] := iform_chainVec hδ.gram hc hc
  have hE : iform (tcChainVec [5, 4, 3, 2, 1] δ)
      (σ (tcChainVec [5, 4, 3, 2, 1] δ) - tcChainVec [5, 4, 3, 2, 1] δ) =
      5 * ip5 [5, 4, 3, 2, 1] e0 + 4 * ip5 [5, 4, 3, 2, 1] e1 + 3 * ip5 [5, 4, 3, 2, 1] e2 +
        2 * ip5 [5, 4, 3, 2, 1] e3 + ip5 [5, 4, 3, 2, 1] e4 -
        ip5 [5, 4, 3, 2, 1] [5, 4, 3, 2, 1] := by
    rw [hσμ, iform_sub_right_E6]
    simp only [iform_add_right_E6, iform_smul_right_E6]
    rw [hif0, hif1, hif2, hif3, hif4, hifc]
  have hnd : ¬ (6 : ℤ) * 6 ∣ iform (tcChainVec [5, 4, 3, 2, 1] δ)
      (σ (tcChainVec [5, 4, 3, 2, 1] δ) - tcChainVec [5, 4, 3, 2, 1] δ) := by
    rw [hE, show (6 : ℤ) * 6 = 36 by norm_num]
    exact std_outer_disc e0 he0 e1 he1 g01 e2 he2 g12 g02 e3 he3 g23 g13 g03
      e4 he4 g34 g24 g14 g04
  have hmain : ¬ twistInner (tcChainSet δ)
      (σ : (Fin Tag.E6.rank → ℤ) → (Fin Tag.E6.rank → ℤ)) :=
    not_twistInner_of_disc hroot hsl σ hμ hμd hμd hnd
  intro hρin
  obtain ⟨w, hw, hwγ⟩ := hρin
  exact hmain ⟨w, hw, fun γ hγ => by rw [← hσ γ (hroot γ hγ)]; exact hwγ γ hγ⟩

theorem componentLabel_chainSet_outer
    {δ : Fin 5 → (Fin Tag.E6.rank → ℤ)} (hδ : A5Chain δ) {ρ : Equiv.Perm (Fin Tag.E6.rank → ℤ)}
    (hst : (ρ : (Fin Tag.E6.rank → ℤ) → (Fin Tag.E6.rank → ℤ)) '' tcChainSet δ = tcChainSet δ)
    (hout : ¬ twistInner (tcChainSet δ) (ρ : (Fin Tag.E6.rank → ℤ) → (Fin Tag.E6.rank → ℤ)))
    (n : ℕ) :
    componentLabel (compRank (tcChainSet δ)) (tcChainSet δ).ncard (twistKindOf ρ (tcChainSet δ)) n =
      ⟨LargeEvenLieTag.twA, 5, n⟩ := by
  have h1 := tcE6_componentOrbitLength_eq_one hst
  have hk : twistKindOf ρ (tcChainSet δ) = .suN := by
    unfold twistKindOf
    rw [h1]
    rw [if_neg (by simpa using hout)]
    rw [if_neg (by
      rintro (⟨h6, -⟩ | ⟨h4, -⟩)
      · rw [compRank_chainSet hδ.gram] at h6
        exact absurd h6 (by norm_num)
      · rw [compRank_chainSet hδ.gram] at h4
        exact absurd h4 (by norm_num))]
    rw [if_neg (by rw [compRank_chainSet hδ.gram, ncard_chainSet hδ.gram]; norm_num)]
    rw [if_pos (by rw [compRank_chainSet hδ.gram, ncard_chainSet hδ.gram]; norm_num)]
  rw [hk, compRank_chainSet hδ.gram, ncard_chainSet hδ.gram]
  simp [componentLabel]

end CFSG.StandardType.TableCRes

end
