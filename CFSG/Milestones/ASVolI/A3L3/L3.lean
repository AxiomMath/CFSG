module

public import CFSG.Milestones.ASVolI.A3L3.L3Facts

public section

namespace CFSG.ASVolI

open Matrix CFSG.RankThree.SubgroupLists CFSG.GH74.GLS.IVK.Proofs2.Lemma41aL3 CFSG.ASVolI.ChA
open scoped MatrixGroups

@[expose] def burnsideA315y_L3EStatement : Prop :=
  ∀ (F : Type) [Field F] [Finite F] (p : ℕ) [Fact p.Prime], Nat.card F = p →
    ∀ (x y : F) (hxy : x ^ 2 + y ^ 2 = -1) (two_ne : (2 : F) ≠ 0)
      (B' : Subgroup (MulAut PSL(3, F))),
      (burnsideA315y_l3Model x y hxy two_ne).DichE B' →
      B' ≤ (MulAut.conj : PSL(3, F) →* MulAut PSL(3, F)).range ∧
      CFSG.Quasithin.IsElemAbelianOfRank p 2 ↥B' ∧
      (burnsideA315y_l3Model x y hxy two_ne).S ≤ Subgroup.normalizer (B' : Set (MulAut PSL(3, F))) ∧
      B' ≠ ⊥ ∧
      ∀ C : Subgroup (MulAut PSL(3, F)), C ≤ B' →
        (burnsideA315y_l3Model x y hxy two_ne).S ≤ Subgroup.normalizer (C : Set (MulAut PSL(3, F))) →
          C = ⊥ ∨ C = B'

@[expose] def burnsideA315y_L3UStatement : Prop :=
  ∀ (F : Type) [Field F] [Finite F] (p : ℕ) [Fact p.Prime], Nat.card F = p →
    ∀ (x y : F) (hxy : x ^ 2 + y ^ 2 = -1) (two_ne : (2 : F) ≠ 0),
      ∃ U : Subgroup (MulAut PSL(3, F)),
        CFSG.Quasithin.A315.IsSylowOf p U (MulAut.conj : PSL(3, F) →* MulAut PSL(3, F)).range ∧
        (burnsideA315y_l3Model x y hxy two_ne).D₀.map (burnsideA315y_l3Model x y hxy two_ne).c ≤
          Subgroup.normalizer (U : Set (MulAut PSL(3, F)))

theorem burnsideA315y_l3Case_of (hfit : burnsideA315y_FittingStatement)
    (hsteps : burnsideA315y_StepsStatement) (hcartan : burnsideA315y_CartanStatement)
    (hEfact : burnsideA315y_L3EStatement) (hUfact : burnsideA315y_L3UStatement)
    {G : Type} [Group G] {L T B : Subgroup G} (h : CFSG.Quasithin.A315Hyp L T B)
    (hab : IsMulCommutative ↥B) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hL : CFSG.Quasithin.IsPSLEps3 true p 1 ↥L) :
    CFSG.Quasithin.A315Case2 L T B ∨ CFSG.Quasithin.A315Case3 L T B := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI := burnsideA315x_normal h
  have hL2 : CFSG.Open.StatedClassicalModel ↥L .PSL 3 p 1 := hL
  obtain ⟨-, F, hFf, hFfin, hcard, ⟨e₀⟩⟩ := hL2
  have hF : Nat.card F = p := by rw [hcard, pow_one]
  let e : ↥L ≃* PSL(3, F) :=
    e₀.trans (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 3 F).symm
  obtain ⟨x, y, hxy⟩ := burnsideA315y_l3_exists_xy hF
  have two_ne := burnsideA315y_l3_two_ne hF hp2
  set M := burnsideA315y_l3Model x y hxy two_ne with hM
  obtain ⟨hD₀cyc, hD₀card⟩ := burnsideA315y_l3_D₀ (hxy := hxy) (two_ne := two_ne) hF
  refine burnsideA315y_finish' h e hp2 hL M hfit hsteps hcartan
    (burnsideA315y_Model.ofData_relIndex _ _ _ _ _ _ _ _ _ _ _ _ _ _)
    (burnsideA315y_l3_C₁ hF hp2) burnsideA315y_l3Model_L (burnsideA315y_l3_odd hF)
    (burnsideA315y_l3_K hF) (fun _ _ _ _ => trivial) (fun _ _ _ _ _ _ => trivial)
    burnsideA315y_l3_e22 (burnsideA315y_l3_Γ₁ hF) hD₀cyc (by simpa using hD₀card)
    (hUfact F p hF x y hxy two_ne) ?_ hab
  intro B' _ _ _ _ _ hDE
  exact ⟨rfl, hEfact F p hF x y hxy two_ne B' hDE⟩

end CFSG.ASVolI
