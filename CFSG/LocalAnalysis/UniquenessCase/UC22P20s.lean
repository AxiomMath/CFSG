module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P20m

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.Assembly.LowTwoRank (StatedLieTag)
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem uc22p20s_calLOf_nonempty (D : Data G) (h20_4 : S20_4 D) (h1930 : H1930 D)
    {H : Subgroup G} (hH : H ∈ hSet D.T D.M) : (calLOf D.T D.M H).Nonempty := by
  by_contra hne
  rw [Set.not_nonempty_iff_eq_empty] at hne
  have h := h20_4 h1930 H hH
  rw [hne, iSup_emptyset, Subgroup.coe_bot] at h
  apply hH.2.1
  intro a ha
  have ha' : a ∈ ({1} : Set G) * ((H ⊓ D.M : Subgroup G) : Set G) := by
    rw [h]; exact ha
  obtain ⟨u, hu, b, hb, rfl⟩ := Set.mem_mul.1 ha'
  rw [Set.mem_singleton_iff] at hu
  subst hu
  rw [one_mul]
  exact hb.2

theorem uc22p20s_centralizer_le {D : Data G} {L R : Subgroup G} (hL : L ∈ calL D.T D.M)
    (hTR : D.T ≤ R) (hRL : R ≤ L ⊔ D.T) :
    R ⊓ centralizer (pCoreOf 2 R : Set G) ≤ pCoreOf 2 R := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hLT : L ⊔ D.T ∈ hSet D.T D.M := hL.2.2.1
  have hOT : pCoreOf 2 (L ⊔ D.T) ≤ D.T := uc22p20b_pCoreOf_le_T D le_sup_right
  have hOR : pCoreOf 2 (L ⊔ D.T) ≤ pCoreOf 2 R := by
    refine uc22p20b_le_pCoreOf (hOT.trans hTR) (uc22p20b_isPGroup_pCoreOf _) ?_
    intro k hk x hx
    exact uc22p20b_conj_mem_pCoreOf_self (hRL hk) hx
  intro x hx
  have hxLT : x ∈ L ⊔ D.T := hRL hx.1
  have hxC : x ∈ centralizer (pCoreOf 2 (L ⊔ D.T) : Set G) :=
    Subgroup.centralizer_le (SetLike.coe_subset_coe.2 hOR) hx.2
  exact hOR (hLT.2.2 ⟨hxLT, hxC⟩)

theorem uc22p20s_parabolic_le_M (D : Data G) (h20_4 : S20_4 D) (h1930 : H1930 D) {L Q : Subgroup G}
    (hL : L ∈ calLLow D.T D.M) (hQ : ParabolicOf L Q) (hTQ : D.T ≤ normalizer (Q : Set G))
    (hQL : Q ≠ L) : Q ≤ D.M := by
  by_contra hQM
  have hLcal : L ∈ calL D.T D.M := hL.prop
  have hQL' : Q ≤ L := hQ.2.1
  have hRL : Q ⊔ D.T ≤ L ⊔ D.T := sup_le (hQL'.trans le_sup_left) le_sup_right
  have hR : Q ⊔ D.T ∈ hSet D.T D.M :=
    ⟨le_sup_right, fun h => hQM (le_sup_left.trans h), uc22p20s_centralizer_le hLcal le_sup_right hRL⟩
  obtain ⟨L', hL'⟩ := uc22p20s_calLOf_nonempty D h20_4 h1930 hR
  have hL'cal : L' ∈ calL D.T D.M := hL'.1
  have hL'R : L' ≤ Q ⊔ D.T := hL'.2.le
  have hL'Q : L' ≤ Q :=
    uc22p20m_le_of_perfect_sup hL'cal.2.1 hL'R hTQ D.sylowM.isPGroup
  have hLL' : L ≤ L' := hL.2 hL'cal (hL'Q.trans hQL')
  exact hQL (le_antisymm hQL' (hLL'.trans hL'Q))

@[expose] def uc22p20sRankTwo (t : StatedLieTag) (m n : ℕ) : Prop :=
  (2 < n ∧ ((t = .PSL ∧ m = 4) ∨ (t = .PSU ∧ m = 4) ∨ t = .G2 ∨ t = .trialityD4 ∨ t = .twistedF4 ∨
    (t = .PSp ∧ m = 3) ∨ (t = .POmegaMinus ∧ m = 4))) ∨
  (n = 2 ∧ ((t = .PSU ∧ (m = 4 ∨ m = 5)) ∨ t = .trialityD4 ∨ (t = .POmegaMinus ∧ m = 4))) ∨
  (n = 1 ∧ t = .trialityD4)

@[expose] def uc22p20sGraphShape (t : StatedLieTag) (m n : ℕ) : Prop :=
  2 < n ∧ ((t = .PSL ∧ m = 3) ∨ (t = .PSp ∧ m = 2))

end CFSG.LocalAnalysis.UniquenessCase.UC22
