module

import CFSG.RankThree.PartTwo.Sec15.Gagen155W315PGroup
import CFSG.RankThree.PartTwo.Sec15.Item15Res6ProofComp
import CFSG.RankThree.PartTwo.Sec19.Step1914Tri
public import CFSG.GroupTheory.LocalCores.Components
public import CFSG.RankThree.PartTwo.Sec14.Item14ListStatements
public import CFSG.RankThree.PartTwo.Sec14.Std
public import CFSG.RankThree.PartTwo.Sec6.Item612Local
import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
import CFSG.RankThree.PartTwo.Sec15.Item153Twin2ProofTypesTools

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS

variable {G : Type} [Group G] [Finite G]

namespace Proof155P

private theorem eq_bot_of_cover_simple {T X : Type*} [Group T] [Group X] [IsSimpleGroup X]
    (e : T ≃* X) {V E : Subgroup T} (hV : V.IsSubnormal) (hVq : CFSG.IsQuasisimple ↥V)
    (hEp : Group.IsPerfect ↥E) (hVE : ⁅V, E⁆ = ⊥) : E = ⊥ :=
  eq_bot_of_cover (ψ := MonoidHom.id X) Function.surjective_id
    (by rw [MonoidHom.ker_id]; exact bot_le) (φ := e.symm.toMonoidHom) e.symm.surjective
    hV hVq hEp hVE

private theorem eq_bot_of_cover_quasisimple {T X : Type*} [Group T] [Group X]
    (hX : CFSG.IsQuasisimple X) (e : T ≃* X) {V E : Subgroup T} (hV : V.IsSubnormal)
    (hVq : CFSG.IsQuasisimple ↥V) (hEp : Group.IsPerfect ↥E) (hVE : ⁅V, E⁆ = ⊥) : E = ⊥ := by
  obtain ⟨-, hsimple, -⟩ := hX
  letI : IsSimpleGroup (X ⧸ Subgroup.center X) := hsimple
  exact eq_bot_of_cover (ψ := QuotientGroup.mk' (Subgroup.center X))
    (QuotientGroup.mk'_surjective _) (by rw [QuotientGroup.ker_mk'])
    (φ := e.symm.toMonoidHom) e.symm.surjective hV hVq hEp hVE

private theorem eq_bot_of_cover_triple {T S : Type*} [Group T] [Group S] [IsSimpleGroup S]
    (h : Sec4.IsTripleCover T S) {V E : Subgroup T} (hV : V.IsSubnormal)
    (hVq : CFSG.IsQuasisimple ↥V) (hEp : Group.IsPerfect ↥E) (hVE : ⁅V, E⁆ = ⊥) : E = ⊥ := by
  obtain ⟨-, ⟨ε⟩⟩ := h
  obtain ⟨hψ, hk⟩ := Proof153Twin2.tripleCover_cover ε
  exact eq_bot_of_cover hψ hk (φ := MonoidHom.id T) Function.surjective_id hV hVq hEp hVE

theorem shape148_of_ne_bot
    {A L : Subgroup G} {c : G} (h : Sec14Std G A c L)
    (h148 : Item148 A (lB A)) {M : Subgroup G} (hM : M ∈ scriptY2 A) :
    letI := ker148_normal hM.1.2
    ∀ V E : Subgroup ↥(img148 A M (deltaZero A (lB A) M)), V.IsSubnormal →
      CFSG.IsQuasisimple ↥V → Group.IsPerfect ↥E → ⁅V, E⁆ = ⊥ → E ≠ ⊥ →
      (∃ d : G, d ∈ A ∧ d ≠ 1 ∧
        deltaZero A (lB A) M = pPrimeCoreOf 3 (deltaZero A (lB A) M) ⊔
          deltaZero A (lB A) (M ⊓ Subgroup.centralizer ({d} : Set G)) ∧
        (IsCentralProductA6Covers ↥(img148 A M (deltaZero A (lB A) M)) ∨
          IsA6CoverTimesA5 ↥(img148 A M (deltaZero A (lB A) M)) ∨
          Nonempty (↥(img148 A M (deltaZero A (lB A) M)) ≃*
            alternatingGroup (Fin 5) × alternatingGroup (Fin 5)))) ∨
      Nonempty (↥(img148 A M (deltaZero A (lB A) M)) ≃*
        alternatingGroup (Fin 5) × CFSG.Blueprint.NativeSporadic.J2) := by
  intro V E hV hVq hEp hVE hE1
  let := ker148_normal hM.1.2
  haveI hA5s : IsSimpleGroup (alternatingGroup (Fin 5)) :=
    alternatingGroup.isSimpleGroup (by simp)
  haveI hA6s : IsSimpleGroup (alternatingGroup (Fin 6)) :=
    alternatingGroup.isSimpleGroup (by simp)
  haveI hA7s : IsSimpleGroup (alternatingGroup (Fin 7)) :=
    alternatingGroup.isSimpleGroup (by simp)
  haveI hA10s : IsSimpleGroup (alternatingGroup (Fin 10)) :=
    alternatingGroup.isSimpleGroup (by simp)
  haveI hONs : IsSimpleGroup CFSG.Blueprint.NativeSporadic.ON :=
    CFSG.Sporadic.ON.isSimpleGroup_ON
  rcases (h148 M hM.1).2 with h1 | h2 | h3 | h4 | h5 | h6 | h7'
  ·
    have hD : img148 A M (deltaZero A (lB A) M) = ⊥ := img148_eq_bot_of_le h1
    haveI hsub : Subsingleton ↥(img148 A M (deltaZero A (lB A) M)) := by
      rw [hD]
      exact inferInstance
    have hVbot : V = ⊥ := by
      rw [eq_bot_iff]
      intro x _
      rw [show x = 1 from Subsingleton.elim x 1]
      exact Subgroup.one_mem ⊥
    exact absurd hVbot ((Subgroup.nontrivial_iff_ne_bot V).mp
      (CFSG.LocalCores.isQuasisimple_nontrivial hVq))
  ·
    obtain ⟨c', hc', hdec, hL'⟩ := h2
    obtain ⟨L', hL', hcases⟩ := hL'
    rcases hcases with ⟨⟨φ⟩⟩ | ⟨-, ⟨φ⟩⟩ | ⟨p, f, e', hp, hf, -, -, hε⟩ | ⟨-, h6 | ⟨⟨φ⟩⟩⟩
    · exact (hE1 (eq_bot_of_cover_quasisimple
        (Sec6.isQuasisimple_of_mem_thetaComponentsAt hL'.1) φ hV hVq hEp hVE)).elim
    · exact (hE1 (eq_bot_of_cover_simple φ hV hVq hEp hVE)).elim
    · haveI : Fact p.Prime := hp
      rcases hε with ⟨⟨φ⟩⟩ | ⟨h2q, ⟨φ⟩⟩
      · haveI : IsSimpleGroup
            (CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField p f)) :=
          Sec19.Step1914TriProof.isSimpleGroup_projSL_three_of_field _
        exact (hE1 (eq_bot_of_cover_simple φ hV hVq hEp hVE)).elim
      · haveI : IsSimpleGroup (CFSG.Assembly.RankThreeEven.projSU 3 p f) :=
          Sec19.Step1914TriProof.isSimpleGroup_projSU_three_of_ne_two p f hf (by omega)
        exact (hE1 (eq_bot_of_cover_simple φ hV hVq hEp hVE)).elim
    · exact (hE1 (eq_bot_of_cover_triple h6 hV hVq hEp hVE)).elim
    · exact (hE1 (eq_bot_of_cover_simple φ hV hVq hEp hVE)).elim
  ·
    obtain ⟨-, d, -, -, -, -, hdA, hd1, -, hdecomp, htypes⟩ := h3
    rcases htypes with hON | hCP | hCTA | ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩ | ⟨hp7, ⟨φ⟩⟩
    · exact (hE1 (eq_bot_of_cover_triple hON hV hVq hEp hVE)).elim
    · exact Or.inl ⟨d, hdA, hd1, hdecomp, Or.inl hCP⟩
    · exact Or.inl ⟨d, hdA, hd1, hdecomp, Or.inr (Or.inl hCTA)⟩
    · exact Or.inl ⟨d, hdA, hd1, hdecomp, Or.inr (Or.inr ⟨φ⟩)⟩
    · exact (hE1 (eq_bot_of_cover_simple φ hV hVq hEp hVE)).elim
    · haveI : Fact (Nat.Prime 7) := hp7
      haveI : IsSimpleGroup
          (CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 7 1)) :=
        Sec19.Step1914TriProof.isSimpleGroup_projSL_three_of_field _
      exact (hE1 (eq_bot_of_cover_simple φ hV hVq hEp hVE)).elim
  ·
    obtain ⟨⟨φ⟩, -, -⟩ := h4
    exact (hE1 (eq_bot_of_cover_simple φ hV hVq hEp hVE)).elim
  ·
    obtain ⟨-, -, -, n, -, -, -, hn, -, hiso, -⟩ := h5
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    rcases hiso with ⟨-, ⟨φ⟩⟩ | ⟨-, ⟨φ⟩⟩
    · haveI : IsSimpleGroup
          (CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 2 (3 * n))) :=
        Sec19.Step1914TriProof.isSimpleGroup_projSL_three_of_field _
      exact (hE1 (eq_bot_of_cover_simple φ hV hVq hEp hVE)).elim
    · have h2 : 2 ^ (3 * n) ≠ 2 := by
        intro h22
        have := Nat.pow_right_injective (le_refl 2) (h22.trans (pow_one 2).symm)
        omega
      haveI : IsSimpleGroup (CFSG.Assembly.RankThreeEven.projSU 3 2 (3 * n)) :=
        Sec19.Step1914TriProof.isSimpleGroup_projSU_three_of_ne_two 2 (3 * n) (by omega) h2
      exact (hE1 (eq_bot_of_cover_simple φ hV hVq hEp hVE)).elim
  ·
    obtain ⟨⟨φ⟩, -, -⟩ := h6
    exact Or.inr ⟨φ⟩
  ·
    exact (Proof15Res6.false_of_case148Seven_two h h148 hM h7').elim

end Proof155P

end CFSG.RankThree.PartTwo.Sec15
