module

public import CFSG.LocalAnalysis.StandardType.GGHdRo7SUDefs

import CFSG.LocalAnalysis.StandardType.GGTableBSymplectic
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyEvenSymplectic
import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowY1OutUniRank
import CFSG.LocalAnalysis.GLTheoremA.CatB.U42CatAct
import CFSG.CharacterTheory.Wreathed.BrauerWongTypes
import CFSG.CharacterTheory.Wreathed.WreathCentralSquare
import CFSG.LocalAnalysis.ComponentClassification.BurgoynePSLInner
import CFSG.LocalAnalysis.ComponentClassification.BurgoyneProjSlice
import CFSG.LocalAnalysis.ComponentClassification.InnAutDerivedUnitary
import CFSG.LocalAnalysis.GLTheoremA.S10.InputsSetup
import CFSG.LocalAnalysis.GLTheoremA.S12.Inputs122
import CFSG.LocalAnalysis.GLTheoremA.Sec5Setup
import CFSG.LocalAnalysis.GLTheoremB.Lemma911Proof

public section

namespace CFSG.StandardType.HdRo7LNC

open CFSG.StandardType.HdRo7C

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

lemma hdRo7LNCAux_sp_noncyclic {G : Type} [Group G] [Finite G]
    {L : Subgroup G} {lab : CFSG.Assembly.LargeEvenLabel}
    (htag : lab.tag = .B ∨ lab.tag = .C) (hn : lab.n = 1) (hl2 : 2 ≤ lab.rank)
    (hR : GGHasLabel lab (↥L ⧸ Subgroup.center ↥L)) :
    ∃ S : Subgroup G, S ≤ L ∧ IsPGroup 3 S ∧ ¬ IsCyclic S := by
  rw [GGHasLabel] at hR
  rcases lab with ⟨t, l, n⟩
  simp only at htag hn hl2 hR
  subst hn
  have hraw : CFSG.Assembly.LargeEvenRecipeSymplectic l (2 ^ 1) false
      (fun R' _ _ _ => Nonempty (↥L ⧸ Subgroup.center ↥L ≃* R')) := by
    rcases htag with rfl | rfl
    · dsimp only [LargeEvenRawDatum] at hR; exact hR
    · dsimp only [LargeEvenRawDatum] at hR; exact hR
  obtain ⟨K, hField, hFinite, hKcard, ⟨e⟩⟩ := hraw
  haveI : CharP K 2 :=
    CFSG.StandardType.charP_two_of_card (m := 1) (by simpa using hKcard)
  obtain ⟨E, hE, hEcard⟩ :=
    CFSG.QuasithinUnique.Setup.Family.even_symplectic_three_rank (K := K) l
  set ψ : ↥L →* CFSG.Assembly.LargeEvenProj (CFSG.Assembly.LargeEvenSpGroup K l) :=
    e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥L)) with hψdef
  have hψ : Function.Surjective ψ := e.surjective.comp (QuotientGroup.mk'_surjective _)
  refine CFSG.StandardType.exists_noncyclic_of_noncyclic_quot (F := E) ψ hψ ?_ ?_
  · haveI : CFSG.IsElementaryAbelian 3 ↥E := hE
    exact CFSG.IsElementaryAbelian.isPGroup 3 ↥E
  · have hexp : ∀ x ∈ E, x ^ 3 = 1 := by
      intro x hx
      haveI : CFSG.IsElementaryAbelian 3 E := hE
      exact CFSG.elemPow_eq_one_of_isElementaryAbelian x hx
    have hcard : 3 < Nat.card ↥E := by
      rw [hEcard]
      calc 3 < 3 ^ 2 := by norm_num
        _ ≤ 3 ^ l := Nat.pow_le_pow_right (by norm_num) hl2
    exact CFSG.LocalAnalysis.GLTheoremA.CatB.U42Cat.not_isCyclic_of_exponent
      Nat.prime_three hexp hcard

theorem lnc_of_innerDiag_sp {G : Type} [Group G] [Finite G]
    {p : ℕ} {Bs L : Subgroup G}
    (hM : GGInnerDiagOnLabel
      (fun p lab => p = 3 ∧ (lab.tag = .B ∨ lab.tag = .C) ∧ lab.n = 1 ∧ 5 ≤ lab.rank) p Bs L) :
    ∃ S : Subgroup G, S ≤ L ∧ IsPGroup p S ∧ ¬ IsCyclic S := by
  obtain ⟨lab, _, hhas, _, _, _, _, _, hS, _, _⟩ :=
    largeEvenMarking_exists_hasLabel hM
  obtain ⟨hp3, htag, hn, h5⟩ := hS
  rw [hp3]
  exact hdRo7LNCAux_sp_noncyclic htag hn (by omega) hhas

lemma hdRo7LNCAux_su_noncyclic {G : Type} [Group G] [Finite G]
    {L : Subgroup G} {lab : CFSG.Assembly.LargeEvenLabel}
    (htag : lab.tag = .twA) (hn : lab.n = 1) (hl6 : 6 ≤ lab.rank)
    (hR : GGHasLabel lab (↥L ⧸ Subgroup.center ↥L)) :
    ∃ S : Subgroup G, S ≤ L ∧ IsPGroup 3 S ∧ ¬ IsCyclic S := by
  rw [GGHasLabel] at hR
  rcases lab with ⟨t, l, n⟩
  simp only at htag hn hl6 hR
  subst hn
  have hraw : CFSG.Assembly.LargeEvenRecipeUnitary (l + 1) (2 ^ 1)
      (fun R' _ _ _ => Nonempty (↥L ⧸ Subgroup.center ↥L ≃* R')) := by
    subst htag
    dsimp only [LargeEvenRawDatum] at hR
    exact hR
  obtain ⟨K, hField, hFinite, hKcard, ⟨e⟩⟩ := hraw
  have hUF : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 1 K :=
    CFSG.StandardType.TableBU.unitaryFieldData_of_card (n := 1) (by simpa using hKcard)
      (by norm_num)
  obtain ⟨E, hE, hEcard⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.KD264Lie.exists_elemAbelian_card_81_unitary
      (K := K) hUF (by norm_num) (m := l + 1) (by omega)
  let e' : ↥L ⧸ Subgroup.center ↥L ≃*
      CFSG.Open.StatedProj (CFSG.Open.StatedSU (l + 1) (2 ^ 1) K) := e
  set ψ : ↥L →* CFSG.Open.StatedProj (CFSG.Open.StatedSU (l + 1) (2 ^ 1) K) :=
    e'.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥L)) with hψdef
  have hψ : Function.Surjective ψ := e'.surjective.comp (QuotientGroup.mk'_surjective _)
  refine CFSG.StandardType.exists_noncyclic_of_noncyclic_quot (F := E) ψ hψ ?_ ?_
  · intro x
    refine ⟨1, ?_⟩
    apply Subtype.ext
    simpa using hE.2 (Subtype.val x) x.2
  · have hexp : ∀ x ∈ E, x ^ 3 = 1 := hE.2
    have hcard : 3 < Nat.card ↥E := by
      rw [hEcard]
      norm_num
    exact CFSG.LocalAnalysis.GLTheoremA.CatB.U42Cat.not_isCyclic_of_exponent
      Nat.prime_three hexp hcard

theorem lnc_of_innerDiag_su {G : Type} [Group G] [Finite G]
    {p : ℕ} {Bs L : Subgroup G}
    (hM : GGInnerDiagOnLabel
      (fun p lab => p = 3 ∧ lab.tag = .twA ∧ lab.n = 1 ∧ 6 ≤ lab.rank ∧
        ¬ 3 ∣ lab.rank + 1) p Bs L) :
    ∃ S : Subgroup G, S ≤ L ∧ IsPGroup p S ∧ ¬ IsCyclic S := by
  obtain ⟨lab, _, hhas, _, _, _, _, _, hS, _, _⟩ :=
    largeEvenMarking_exists_hasLabel hM
  obtain ⟨hp3, htag, hn, h6, -⟩ := hS
  rw [hp3]
  exact hdRo7LNCAux_su_noncyclic htag hn h6 hhas

theorem lnc_holds :
    ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
      (y : G) (K : Subgroup G), GGResHyp p B Bs x L D J y K → ∀ [Fact p.Prime],
      (GGResRowAt ggRowCorank2C p J L ∨ GGResRowAt ggRowSUCorank2 p J L) →
      ∃ S : Subgroup G, S ≤ L ∧ IsPGroup p S ∧ ¬ IsCyclic S := by
  intro G _ _ p B Bs x L D J y K hH hp hrow
  rcases hrow with hrowC | hrowU
  · obtain ⟨labJ, labL, hJlam, hLlam, hJlab, hLlab, hr⟩ := hrowC
    obtain ⟨rfl, hJtag, hJn, hLtag, hLn, hrk⟩ := hr
    have hJrank : 2 ≤ labJ.rank := by
      obtain ⟨t, l, n⟩ := labJ
      simp only at hJtag
      rcases hJtag with rfl | rfl
      · dsimp only [CFSG.Assembly.LargeEvenInLambda2] at hJlam
        exact hJlam.2.1
      · dsimp only [CFSG.Assembly.LargeEvenInLambda2] at hJlam
        exact hJlam.2.1
    have hl2 : 2 ≤ labL.rank := by omega
    exact hdRo7LNCAux_sp_noncyclic hLtag hLn hl2 hLlab
  · obtain ⟨labJ, labL, hJlam, hLlam, hJlab, hLlab, hr⟩ := hrowU
    obtain ⟨rfl, hJtag, hJn, hLtag, hLn, hrk, hl6, hndvd⟩ := hr
    exact hdRo7LNCAux_su_noncyclic hLtag hLn hl6 hLlab

end CFSG.StandardType.HdRo7LNC
