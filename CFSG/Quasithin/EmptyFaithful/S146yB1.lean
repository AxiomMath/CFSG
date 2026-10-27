module

public import CFSG.Quasithin.EmptyFaithful.S146yB1Star
public import CFSG.Quasithin.EmptyFaithful.S146yB1Res
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239ListedMain
public import CFSG.LocalAnalysis.QuasithinUnique.BenderBranchBasic
public import CFSG.Quasithin.EmptyFaithful.S1469Inputs

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1
open scoped commutatorElement

section Main

variable {G : Type} [Group G] [Finite G]

structure B1Ctx (I Iz K : Subgroup G) (z : G) : Prop where
  hKI : K ≤ I
  hKne : K ≠ ⊥
  hzI : z ∈ I
  hz2 : z ^ 2 = 1
  hKz : ⁅K, Subgroup.zpowers z⁆ = K
  hIz : Iz = I ⊓ Subgroup.centralizer ({z} : Set G)

omit [Finite G] in
theorem B1Ctx.mem_normalizer {I Iz K : Subgroup G} {z : G} (c : B1Ctx I Iz K z) :
    z ∈ Subgroup.normalizer (K : Set G) := by
  have h := Subgroup.normalizer_commutator_ge_left K (Subgroup.zpowers z)
  rw [c.hKz] at h
  have h2 := Subgroup.normalizer_commutator_ge_right K (Subgroup.zpowers z)
  rw [c.hKz] at h2
  exact h2 (Subgroup.mem_zpowers z)

theorem B1Ctx.false_of_borel {I Iz K : Subgroup G} {z : G} (c : B1Ctx I Iz K z) (rA : BorelAutFree)
    {n : ℕ}
    (hX : E2.IsBenderOf n ↥(E2.star Iz I K) ∨
      (2 ≤ n ∧ (IsPSL 3 2 n ↥(E2.star Iz I K) ∨ E2.IsSp4Prime n ↥(E2.star Iz I K))))
    (hB : E2.IsBorelIn (E2.star Iz I K) (E2.star Iz I (Iz ⊓ K))) : False := by
  have hcomm := rA (E2.StarQuot Iz I) (E2.star Iz I K) (E2.star Iz I (Iz ⊓ K)) n
    (starMk Iz I ⟨z, c.hzI⟩) hX hB (starMk_mem_normalizer c.hzI c.mem_normalizer)
    (starMk_sq c.hzI c.hz2) (fun b hb => starMk_comm_of_mem c.hzI (fun m hm => ?_) hb)
  · exact false_of_star_comm c.hzI c.hIz c.hKz c.hKne c.hKI hcomm
  · have hm' : m ∈ I ⊓ Subgroup.centralizer ({z} : Set G) := c.hIz ▸ hm
    exact (Subgroup.mem_centralizer_iff.mp hm'.2 z rfl).symm

omit [Finite G] in
theorem star_isPGroup_two {Iz I S : Subgroup G} (hSI : S ≤ I) (hS : IsPGroup 2 S) :
    IsPGroup 2 ↥(E2.star Iz I S) := by
  have h1 : IsPGroup 2 ↥(S.subgroupOf I) :=
    IsPGroup.of_injective hS (Subgroup.subgroupOfEquivOfLe hSI).toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hSI).injective
  exact h1.map _

theorem shape_of_psl_prime {I S Iz K : Subgroup G} (rB : L2PrimeOnList115) (rC : L3TwoParabolicAut)
    (hSI : S ≤ I) (hS2 : IsPGroup 2 S) (hKI : K ≤ I) (hKcomp : IsComponentIn K I)
    (hK115 : Lemma115Type ↥K) {p : ℕ} (hp : p.Prime) (hp8 : p % 8 = 1 ∨ p % 8 = 7)
    (hX : IsPSL 2 p 1 ↥(E2.star Iz I K))
    (h8 : 8 < E2.autCard (E2.star Iz I S) (E2.star Iz I K)) : Shape1469B S Iz K I := by
  by_cases hp7 : p = 7
  · subst hp7
    refine Or.inr (Or.inl ⟨Or.inl
      (Vol2Native.L239.statedClassicalModel_psl_three_two_of_psl_two_seven hX), ?_⟩)
    intro P hP _ hTsP
    have hle := rC (E2.StarQuot Iz I) (E2.star Iz I S) (E2.star Iz I K) P (star_isPGroup_two hSI hS2)
      (Vol2Native.L239.statedClassicalModel_psl_three_two_of_psl_two_seven hX) hP
      (inf_le_left.trans hTsP)
    omega
  · left
    have hs : IsSimpleGroup ↥(E2.star Iz I K) := (LieType.Simplicity.fam_PSL_simplicity _ 2 p 1 hX).2
    obtain ⟨e⟩ := nonempty_star_mulEquiv_center hKI
      (BenderBranch.isQuasisimple_of_isComponentIn hKcomp) hs
    have hX' : IsPSL 2 p 1 (↥K ⧸ Subgroup.center ↥K) :=
      SectionRank.statedClassicalModel_of_mulEquiv e.symm hX
    rcases rB ↥K (BenderBranch.isQuasisimple_of_isComponentIn hKcomp) hK115 p hp hp8 hX' with h7 | hfm
    · exact absurd h7 hp7
    · refine ⟨p, hfm, ?_, hX⟩
      have := hp.two_le
      omega

theorem B1_false_of_psl_square {I Iz K : Subgroup G} (rB : L2SquareNotOnList115)
    (hKcomp : IsComponentIn K I) (hK115 : Lemma115Type ↥K) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hX : IsPSL 2 p 2 ↥(E2.star Iz I K)) : False := by
  have hs : IsSimpleGroup ↥(E2.star Iz I K) := (LieType.Simplicity.fam_PSL_simplicity _ 2 p 2 hX).2
  obtain ⟨e⟩ := nonempty_star_mulEquiv_center hKcomp.1
    (BenderBranch.isQuasisimple_of_isComponentIn hKcomp) hs
  exact rB ↥K (BenderBranch.isQuasisimple_of_isComponentIn hKcomp) hK115 p hp hp3
    (SectionRank.statedClassicalModel_of_mulEquiv e.symm hX)

theorem B1_false_of_psu_three {I Iz K : Subgroup G} (rB : U3OddNotOnList115)
    (hKcomp : IsComponentIn K I) (hK115 : Lemma115Type ↥K) {p : ℕ} (hp : p.Prime) (hp4 : p % 4 = 1)
    (hX : IsPSU 3 p 1 ↥(E2.star Iz I K)) : False := by
  have hs : IsSimpleGroup ↥(E2.star Iz I K) :=
    (ClassicalGroups.Unitary.fam_PSU_simplicity _ 3 p 1 hX).2
  obtain ⟨e⟩ := nonempty_star_mulEquiv_center hKcomp.1
    (BenderBranch.isQuasisimple_of_isComponentIn hKcomp) hs
  exact rB ↥K (BenderBranch.isQuasisimple_of_isComponentIn hKcomp) hK115 p hp hp4
    (SectionRank.statedClassicalModel_of_mulEquiv e.symm hX)

theorem B1_false_of_psl_three {I Iz K : Subgroup G} (rB : L3OddNotOnList115)
    (hKcomp : IsComponentIn K I) (hK115 : Lemma115Type ↥K) {p : ℕ} (hp : p.Prime) (hp4 : p % 4 = 3)
    (hp3 : 3 < p) (hX : IsPSL 3 p 1 ↥(E2.star Iz I K)) : False := by
  have hs : IsSimpleGroup ↥(E2.star Iz I K) := (LieType.Simplicity.fam_PSL_simplicity _ 3 p 1 hX).2
  obtain ⟨e⟩ := nonempty_star_mulEquiv_center hKcomp.1
    (BenderBranch.isQuasisimple_of_isComponentIn hKcomp) hs
  exact rB ↥K (BenderBranch.isQuasisimple_of_isComponentIn hKcomp) hK115 p hp hp4 hp3
    (SectionRank.statedClassicalModel_of_mulEquiv e.symm hX)

end Main

end CFSG.Quasithin
