module

public import CFSG.LocalAnalysis.StandardType.GGTPNA3PlusFinal
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyReflDom
public import CFSG.LocalAnalysis.StandardType.GGExclNoIso
public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL45ConfigIso
public import CFSG.LocalAnalysis.StandardType.GGAssemblyFiveDefs
public import CFSG.LocalAnalysis.StandardType.GGTwistedF4DiagRaw
public import CFSG.LocalAnalysis.StandardType.GGF4H4ListLinHolds
import CFSG.LocalAnalysis.StandardType.GGTypeANbrRowFilter

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem ggLabelIso_a5_right {m : ℕ} {lab : LargeEvenLabel} (h : GGLabelIso lab ⟨.A, 5, m⟩) :
    lab = ⟨.A, 5, m⟩ := by
  obtain ⟨t, r, n⟩ := lab
  unfold GGLabelIso at h
  rcases h with h | ⟨-, h, -⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨h, -⟩
  · exact h
  · rcases h with h | h <;> cases h
  all_goals simp at h

theorem ggOppPlus_psl6Four_of_config
    (hB3 : GGK0ExcB3) (hLB : GGLBalanceInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {d : G} {A : Subgroup G} (hc : GGConfig p B Bs x L D J) (hL : GGInnerDiagOn Bs L)
    (hA : GGInnerDiagOn Bs A) (hn : GGNbr p B x D J d A) (hJA : J ≤ A)
    (hpJ : p ∣ Nat.card J) (hI1 : Bs ⊓ Subgroup.centralizer (J : Set G) ≤ D) {m : ℕ}
    (hm : 2 ≤ m) (hpm : p ∣ 2 ^ m + 1) (hΛJ : LargeEvenInLambda2 ⟨.A, 3, m⟩)
    (hhJ : GGHasLabel ⟨.A, 3, m⟩ (J ⧸ Subgroup.center J))
    (hOm : ¬ GGHasLabel ⟨.twD, 4, m⟩ (A ⧸ Subgroup.center A)) :
    p = 5 ∧ m = 2 ∧ Subgroup.center A = ⊥ ∧ GGHasLabel ⟨.A, 5, 2⟩ (A ⧸ Subgroup.center A) := by
  have hβ := hc.1.2.2.2.2.2.1
  have hp : p.Prime := hβ.1
  have hp2 : p ≠ 2 := hβ.2.1
  obtain ⟨labA, hlabA, hΛA, hhA⟩ :=
    ggNbrLabel_a3Plus_of_config hB3 hLB hc hL hA hn hJA hpJ hI1 hm hpm hΛJ hhJ
  rcases hlabA with rfl | rfl
  swap
  · exact (hOm hhA).elim
  have hraw : GGRawInnFieldInput := ggRawInnFieldInput_holds
  have hiso : GGRawInndiagIsoInput :=
    ggRawInndiagIsoInput_of_rest (ggRawInndiagIsoRestInput_of_round5 ggRawInndiagIsoRound5_holds)
  obtain ⟨lab₁, hΛ₁, hhas₁, -, -, -, -, -, hHS⟩ :=
    largeEvenMarking_exists_hasLabel (ggNbr_halfSplit_of_hyp hraw hiso hc hn hA)
  have hlab₁ : lab₁ = ⟨.A, 5, m⟩ :=
    ggLabelIso_a5_right (ggLabelRigidInput_holds lab₁ _ _ hΛ₁ hΛA hhas₁ hhA)
  subst hlab₁
  rcases F4H4Lin.halfSplit_A rfl hHS with hq | ⟨hn1, -⟩ | ⟨-, hn2, hZ, hp5⟩ | ⟨hr8, -, -⟩
  · exact (not_dvd_two_pow_sub_add hp2 hp hq hpm).elim
  · simp only at hn1
    omega
  · simp only at hn2
    subst hn2
    exact ⟨hp5, rfl, hZ, hhA⟩
  · simp at hr8

end CFSG.StandardType

end
