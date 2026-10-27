module

public import CFSG.Quasithin.EmptyFaithful.R3c10Cl
public import CFSG.Quasithin.Vol2.F134L2

public section

namespace CFSG.Quasithin.R3c10

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1 CFSG.Blueprint
  CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.OuterAutomorphisms
open scoped commutatorElement

section Rank

variable {G : Type} [Group G] [Finite G]

theorem false_of_pRank_two_of_noElemNine {Y L : Subgroup G} (hYL : Y ≤ L)
    (hr : CFSG.Open.pRank 3 Y = 2) (hN : CFSG.Quasithin.F134.NoElemNine ↥L) : False := by
  obtain ⟨E, hEY, hE, hE9⟩ := exists_nine_of_pRank_two hr
  have hEL : E ≤ L := hEY.trans hYL
  refine hN (E.subgroupOf L) ?_ ?_
  · rw [← hE9]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEL).toEquiv
  · intro x hx
    have h1 : ((x : ↥L) : G) ∈ E := Subgroup.mem_subgroupOf.mp hx
    exact Subtype.ext (by simpa using hE.2 _ h1)

end Rank

section Main

@[expose] def Input15342Residue : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M V₁ V₂ Yp I L : Subgroup G) (t : G),
    CtxComp2 T Mc M V₁ V₂ Yp I L t →
      (∀ K : Subgroup G, IsHPlus Yp (Sgp153 T V₁) M K → K ≤ I → K = I) →
        I ≤ Subgroup.normalizer (L : Set G) → I = L ⊔ Sgp153 T V₁ → Yp ≤ L →
          (Nonempty ((↥L ⧸ Subgroup.center ↥L) ≃* alternatingGroup (Fin 7)) ∨
            CFSG.Assembly.LowTwoRank.StatedClassicalModel ↥L .PSL 3 3 1 ∨
            (∃ s : TauCeti.SporadicName, IsLemma115SporadicName s ∧
              Nonempty ((↥L ⧸ CFSG.pCore 2 ↥L) ≃* CFSG.Blueprint.NativeSporadic.Carrier s))) → False

theorem input15342_of_residue
    (hlist : Lemma115_3_List) (hA : R3c2.Input15333Two) (kR : Input15342Residue) : Input15342 := by
  classical
  intro G _ _ T Mc M V₁ V₂ Yp I L t c hmin hN hIeq hYL
  have hh : Hyp15310 G T Mc M V₁ V₂ Yp t := c.hyp
  have hq := hh.hyp.qtfe
  have hQ : CFSG.IsQuasisimple ↥L := c.c33.quasisimple
  have hperf : Group.IsPerfect ↥L := hQ.1
  obtain ⟨z, hz⟩ := hA G T Mc M V₁ V₂ Yp I t c.toCtxComp
  have hcomp : IsComponentIn L I := Id2519.isComponentIn_of_mem_cComp c.c33.mem c.c33.quasisimple
  have hsimple : IsSimpleGroup G := hq.simple
  have hcore : QTKECore G := qtkeCore_of_cat hq.nonabelian hq.qtke
  have hcases : Lemma115Cases L z :=
    (Lemma115_3_List.component_cases hlist hsimple hq.nonabelian hcore hz hcomp).2.2.2
  rcases hcases with ⟨hs, hlie, -⟩ | ⟨-, hZO, hmod, -⟩ | ⟨φ, σ, -⟩ | ⟨φ, σ, hZ13, -⟩ | ⟨hE, -⟩ |
    ⟨hF, -⟩
  ·
    exact Lemma115LieCharTwo.of_mulEquiv (R3c3.quotCenterEquivOfSimple hs hperf) hlie
  ·
    have hLie : Lemma115LieCharTwo (↥L ⧸ CFSG.pCore 2 ↥L) := by
      rcases hmod with h | h
      · exact Or.inl (Or.inl (Or.inl ⟨2, Or.inr (Or.inl ⟨by norm_num, h⟩)⟩))
      · exact Or.inl (Or.inl (Or.inl ⟨2, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨le_rfl, h⟩))))⟩))
    exact Lemma115LieCharTwo.of_mulEquiv (QuotientGroup.quotientMulEquivOfEq hZO) hLie
  ·
    exact Or.inr (Or.inl ⟨φ⟩)
  ·
    exact (kR G T Mc M V₁ V₂ Yp I L t c hmin hN hIeq hYL (Or.inl ⟨φ⟩)).elim
  ·
    rcases hE with hL33 | ⟨p, hFM, hm⟩
    · exact (kR G T Mc M V₁ V₂ Yp I L t c hmin hN hIeq hYL (Or.inr (Or.inl hL33))).elim
    · have hp3 : p ≠ 3 := by
        rintro rfl
        obtain ⟨⟨-, -, -, -, h23⟩, -⟩ := hm
        exact h23 (by simp)
      exact (false_of_pRank_two_of_noElemNine hYL c.rank
        (CFSG.Quasithin.F134.noElemNine_of_statedPSL_two hp3 hm)).elim
  ·
    exact (kR G T Mc M V₁ V₂ Yp I L t c hmin hN hIeq hYL (Or.inr (Or.inr hF))).elim

end Main

end CFSG.Quasithin.R3c10
