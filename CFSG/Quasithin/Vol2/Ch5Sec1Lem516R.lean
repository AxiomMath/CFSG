module

public import CFSG.Quasithin.Vol2.Ch5Sec1Lem513
public import CFSG.Quasithin.Vol2.Ch5Sec1Thm5114
public import CFSG.Quasithin.Vol2.Ch3Sec2Lem322Eight
public import CFSG.Quasithin.H13.U3L14J
public import CFSG.Quasithin.H13.A7Nat1238NQBase

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits

variable {G : Type} [Group G] [Finite G] {T M L V W H : Subgroup G} {n : ℕ}

omit [Finite G] in
theorem IsCh5Module.le_reducedAggregate (hV : IsCh5Module T L V) :
    V ≤ reducedAggregate (L ⊔ T) :=
  A7.le_reducedAggregate_of_isTwoReducedIn hV.isTwoReducedIn

theorem IsCh5Module.isCh5Module_reducedAggregate (hV : IsCh5Module T L V) :
    IsCh5Module T L (reducedAggregate (L ⊔ T)) := by
  obtain ⟨h1, h2⟩ :=
    isTwoReducedIn_iff_isPrimeReduced_subgroupOf.mp (U3.isTwoReducedIn_reducedAggregate (L ⊔ T))
  refine ⟨h1, h2, fun hb => hV.2.2 ?_⟩
  rw [eq_bot_iff, ← hb]
  exact Subgroup.commutator_mono hV.le_reducedAggregate le_rfl

namespace Hyp5_0_1

variable (h : Hyp5_0_1 G T M L n)
include h

theorem charTwo_sup : CharTwo (L ⊔ T) :=
  charTwo_of_inH' h.qtke h.sylow ⟨le_sup_right, h.maximal.1.2.2.2⟩

theorem omega_le_reducedAggregate :
    quasithinOmegaOneCenter T ≤ reducedAggregate (L ⊔ T) := by
  obtain ⟨S, hS⟩ := exists_sylow_coe_eq h.sylow
  have hred : IsTwoReducedIn (L ⊔ T) (conjClosure (quasithinOmegaOneCenter T) (L ⊔ T)) := by
    have := isTwoReducedIn_conjClosure (L ⊔ T) S (hS ▸ le_sup_right) h.charTwo_sup
      (Z := quasithinOmegaOneCenter T) (by rw [hS])
    exact this
  exact (le_conjClosure _ _).trans (A7.le_reducedAggregate_of_isTwoReducedIn hred)

theorem reducedAggregate_le_T : reducedAggregate (L ⊔ T) ≤ T :=
  (Lem3228.reducedAggregate_le_pCoreOf' _).trans
    (F7.isSylowTwoOf_pCoreOf_le (h.isSylowTwoOf le_sup_right))

theorem inf_centralizer_T :
    reducedAggregate (L ⊔ T) ⊓ Subgroup.centralizer (T : Set G) = quasithinOmegaOneCenter T := by
  apply le_antisymm
  · intro x hx
    refine Subgroup.subset_closure ⟨⟨h.reducedAggregate_le_T hx.1, hx.2⟩, ?_⟩
    exact (reducedAggregate_props _).1 x hx.1
  · exact le_inf h.omega_le_reducedAggregate
      ((quasithinOmegaOneCenter_le_inf T).trans inf_le_right)

theorem dichotomy (h331 : Stmt3_3_1) (hC58 : TheoremC58) (h317 : AS317Sylow)
    (h512 : Stmt5_1_2) (hW : IsCh5Module T L W) (hH : IsHStar T M H) :
    (⁅quasithinOmegaOneCenter T, H⁆ = ⊥ ∧ W ⊓ Subgroup.centralizer (L : Set G) = ⊥) ∨
      (⁅W, thompsonJ T⁆ ≠ ⊥ ∧ (IsNatQuotCh5 L W n ∨
        (n = 2 ∧ IsCommCentralSplit L T W ∧ IsBarS5 L T W ∧ IsS5ModCh5 L T ⁅W, L⁆))) := by
  rcases theorem318_three hC58 h317 h.simple h.nonabelian h.qtke h.sylow
      (h.hyp318 h331 hW hH) with ⟨hJ, -⟩ | ⟨-, hZ, hZ0⟩
  · right
    rcases h512 G T M L W n h hW with ⟨h1, -⟩ | ⟨h2, h3⟩ | ⟨h2, h3⟩
    · exact absurd (le_inf (thompsonJ_le_self T) (h1.trans inf_le_right)) hJ
    · exact ⟨h2, Or.inl h3⟩
    · exact ⟨h2, Or.inr h3⟩
  · left
    refine ⟨?_, h.module_inf_centralizer_eq_bot hW hZ0⟩
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr ((hZ H hH).trans inf_le_right)

end Hyp5_0_1

end CFSG.Quasithin.H13
