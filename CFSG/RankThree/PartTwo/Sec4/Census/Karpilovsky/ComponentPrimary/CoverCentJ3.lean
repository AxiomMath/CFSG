module

public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.ComponentPrimary.CoverCentCore
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.NormalizerAction.J3CentralizerA6

public section

namespace CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.ComponentPrimary

open CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.KFacts.K426 CFSG.Blueprint Subgroup
open CFSG.Sporadic.Schreier (j3P)
open CFSG.AGLEmbeddingD2.Wilson.NormalizerAction


set_option linter.unusedSectionVars false

theorem noType424_centralizer_j3P (y : ↥j3P) (hy3 : orderOf (y : Equiv.Perm (Fin 6156)) = 3) :
    ¬ Sec11.KS11Lie2Proof.HasType424 ↥(centralizer ({y} : Set ↥j3P)) := by
  obtain ⟨k0, hk0, c, hc, e', he', hyeq⟩ := j3t_fusion y.2 hy3
  rcases hc with rfl | rfl
  · have hA3 : j3tXA ^ 3 = 1 := (j3tReps_spec (c := 0) (by norm_num)).2
    set D : Subgroup (Equiv.Perm (Fin 6156)) := closure (Set.range j3tD) with hD
    obtain ⟨eD⟩ : Nonempty (↥D ≃* alternatingGroup (Fin 6)) :=
      CFSG.AGLEmbeddingD2.Wilson.Census228Spor.nonempty_mulEquiv_D_alt6
    have hDj : D ≤ j3P := (closure_le _).2 (by rintro _ ⟨i, rfl⟩; exact j3tD_mem i)
    have hDC : D ≤ centralizer ({j3tXA} : Set (Equiv.Perm (Fin 6156))) ⊓ j3P :=
      le_inf CFSG.AGLEmbeddingD2.Wilson.Census228Spor.closure_j3tD_le_centralizer hDj
    set σ : Equiv.Perm (Fin 6156) →* Equiv.Perm (Fin 6156) := (MulAut.conj k0).toMonoidHom
      with hσ
    have hσinj : Function.Injective σ := (MulAut.conj k0).injective
    have hCy : centralizer ({(y : Equiv.Perm (Fin 6156))} : Set (Equiv.Perm (Fin 6156))) ⊓ j3P =
        (centralizer ({j3tXA} : Set (Equiv.Perm (Fin 6156))) ⊓ j3P).map σ := by
      rw [Subgroup.map_inf_eq _ _ σ hσinj, hσ, map_conj_eq_of_mem hk0, hyeq,
        centralizer_conj_map', CFSG.Quasithin.Kleidman.centralizer_pow_eq hA3 he']
    have h1 : D.map σ ≤ centralizer ({(y : Equiv.Perm (Fin 6156))} : Set _) ⊓ j3P := by
      rw [hCy]; exact Subgroup.map_mono hDC
    have h2 : ⁅centralizer ({(y : Equiv.Perm (Fin 6156))} : Set _) ⊓ j3P,
        centralizer ({(y : Equiv.Perm (Fin 6156))} : Set _) ⊓ j3P⁆ ≤ D.map σ := by
      rw [hCy, ← Subgroup.map_commutator]
      exact Subgroup.map_mono j3t_derived.1
    have hDy : D.map σ ≤ j3P := h1.trans inf_le_right
    obtain ⟨t1, t2⟩ := transfer_subgroupOf j3P y (D.map σ) h1 h2
    exact not_hasType424_of_alt6_core _ _ t1 t2
      ((Subgroup.subgroupOfEquivOfLe hDy).trans
        ((MulEquiv.subgroupMap (MulAut.conj k0) D).symm.trans eD))
  · have hB3 : j3tXB ^ 3 = 1 := (j3tReps_spec (c := 1) (by norm_num)).2
    have hcard : Nat.card (centralizer ({(y : Equiv.Perm (Fin 6156))} : Set _) ⊓ j3P :
        Subgroup (Equiv.Perm (Fin 6156))) = 3 ^ 5 := by
      rw [hyeq, CFSG.RankThree.PartTwo.KFacts.K426Rest.card_centralizer_conj hk0 hB3 he',
        ← j3t_caseB.1, j3t_caseB.2]
      norm_num
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hP : IsPGroup 3 ↥(centralizer ({(y : Equiv.Perm (Fin 6156))} : Set _) ⊓ j3P :
        Subgroup (Equiv.Perm (Fin 6156))) := IsPGroup.of_card hcard
    have hsol : Group.IsSolvable ↥(centralizer ({(y : Equiv.Perm (Fin 6156))} : Set _) ⊓ j3P :
        Subgroup (Equiv.Perm (Fin 6156))) :=
      let _ : Group.IsNilpotent _ := hP.isNilpotent
      inferInstance
    let f : ↥(centralizer ({y} : Set ↥j3P)) →*
        ↥(centralizer ({(y : Equiv.Perm (Fin 6156))} : Set _) ⊓ j3P :
          Subgroup (Equiv.Perm (Fin 6156))) :=
      ((j3P.subtype.comp (centralizer ({y} : Set ↥j3P)).subtype).codRestrict _ (fun c => by
        refine ⟨?_, (c.1).2⟩
        have := mem_centralizer_singleton_iff.1 c.2
        show ((c.1 : ↥j3P) : Equiv.Perm (Fin 6156)) ∈ centralizer _
        rw [mem_centralizer_singleton_iff]
        exact congrArg Subtype.val this))
    have hf : Function.Injective f := by
      intro a b hab
      apply Subtype.ext; apply Subtype.ext
      have h := congrArg Subtype.val hab
      exact h
    exact Proving.not_hasType424_of_isSolvable
      (Group.isSolvable_of_isSolvable_injective hf)

theorem noType424At3_of_mulEquiv_j3P {G : Type} [Group G] (ψ : G ≃* ↥j3P) :
    Coordinator.CoverCent.NoType424At3 G :=
  haveI : Finite G := Finite.of_equiv _ ψ.symm.toEquiv
  noType424At3_of_mulEquiv ψ fun y hy3 =>
    noType424_centralizer_j3P y (by rw [Subgroup.orderOf_coe]; exact hy3)

theorem noType424At3_J3 :
    Coordinator.CoverCent.NoType424At3 (NativeSporadic.Carrier .J3) :=
  noType424At3_of_mulEquiv_j3P Sec21.Item228CensusProof.j3CarrierEquiv

end CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.ComponentPrimary
