module

public import CFSG.RankThree.PartTwo.Sec21.FF79KLemmaOUniInner
import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55UDesc
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.HardMathSupport.Solomon.Coordinator.InndiagProxy
public import CFSG.LieType.SeitzGeneration.SubfieldPairSUPhan
public import CFSG.RankThree.PartTwo.KFacts.KS21Mult

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF79

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.MovingAround
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup PerfectInLayer)
open CFSG.LocalAnalysis.GLTheoremB.MovingAround.Claims1110h

section Unitary

open CFSG.HardMathSupport.Solomon.Coordinator.LieComp
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.RankThree.PartOne.KCUnitaryModel CFSG.ClassicalGroups.UnitaryFlag

theorem unitary_a5_false {S : Type} [Group S] [Finite S] (r : ℕ) (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.twistedA r q).Valid) (hq3 : q.p ≠ 3) (hq2 : q.p ≠ 2)
    (hn : r + 1 ∣ 3)
    (he : Nonempty (S ≃* (TauCeti.CFSGIndex.lie ⟨.twistedA r q, hv⟩).Group))
    {α : MulAut S} (hα : α ^ 3 = 1) {K : Subgroup S} (hK : IsComponentOf K (fixSubgroup α))
    (hZ : Subgroup.center ↥K = ⊥)
    (hL : Nonempty ((↥K ⧸ Subgroup.center ↥K) ≃* alternatingGroup (Fin 5))) : False := by
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  have hp3 : (3 : ℕ).Prime := Nat.prime_three
  obtain ⟨e⟩ := he
  obtain ⟨⟨hℓ, hf, hn3, hq⟩, F, _, _, hF, ⟨eT⟩⟩ :=
    CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA r q hv e
  have h : UnitaryFieldData q.p q.exponent F := ⟨hℓ, hf, by rw [hF, ← pow_mul, mul_comm]⟩
  obtain ⟨eP⟩ := nonempty_primeFormP_mulEquiv h (isPrimeFormGram_idGram (n := r + 1) (K := F))
  let e' : S ≃* primeFormP h (idGram F (r + 1)) :=
    (eT.trans (unitaryPSUEquiv h (by omega)).symm).trans eP.symm
  have hq' : ¬(r + 1 = 3 ∧ q.p ^ q.exponent = 2) := fun h3 => hq (Prod.ext h3.1 h3.2)
  have hC : IsPrimeFormGram (1 : GL (Fin (r + 1)) F) := isPrimeFormGram_idGram
  have hβ' : MulAut.congr e' α ^ 3 = 1 := by rw [← map_pow, hα, map_one]
  have hK1 := InputsL33.isComponentOf_map_congr e' hK
  have hL1 := a5Center_map e' hL
  have hZ1 : Subgroup.center ↥(K.map (e' : S →* primeFormP h (idGram F (r + 1)))) = ⊥ := by
    rw [← Subgroup.map_center_eq (K.equivMapOfInjective
      (e' : S →* primeFormP h (idGram F (r + 1))) e'.injective), hZ,
      Subgroup.map_bot]
  obtain ⟨-, -, hker1, -, -, -, -, hkerD, -, -, -⟩ :=
    unitary_prime_form_full_semilinear_realization h hC hn3 hq'
  by_cases hσ : primeFormFieldFactor h hC hn3 hq' (MulAut.congr e' α) = 1
  ·
    have hβD : MulAut.congr e' α ∈ (primeFormFieldFactor h hC hn3 hq').ker := hσ
    rw [hkerD, primeFormD, MonoidHom.mem_range] at hβD
    obtain ⟨A, hA⟩ := hβD
    have h1 : primeFormPsi h hC ⟨A ^ 3, 1⟩ = 1 := by
      rw [primeFormPsi_apply, map_pow, hA, hβ', map_one, one_mul]
    obtain ⟨-, c, -, hc⟩ := (hker1 _).1 h1
    have hAp : (A : GL (Fin (r + 1)) F) ^ 3 =
        Matrix.GeneralLinearGroup.scalar (Fin (r + 1)) c := by
      rwa [SubgroupClass.coe_pow] at hc
    rw [← hA] at hK1
    exact unitary_inner_a5_false hp3 (Ne.symm hq3) hq2 hn A hAp _ hK1 hZ1 hL1
  ·
    have hne : MulAut.congr e' α ≠ 1 := fun h1 => hσ (by rw [h1, map_one])
    have : Fact (3 : ℕ).Prime := ⟨hp3⟩
    have hord : orderOf (MulAut.congr e' α) = 3 := orderOf_eq_prime hβ' hne
    have hσp : orderOf (primeFormFieldFactor h hC hn3 hq' (MulAut.congr e' α)) = 3 :=
      orderOf_eq_prime (by rw [← map_pow, hβ', map_one]) hσ
    obtain ⟨-, -, -, -, -, M, hM⟩ :=
      CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.unitary_prime_descent_char h hn3 hq' hp3
        (by norm_num) (MulAut.congr e' α) hord _ rfl hσp
    have hK2 := InputsL33.isComponentOf_map_congr
      ((primeFormConjHom h (idGram F (r + 1)) M)⁻¹ : MulAut _) hK1
    rw [InputsL33.congr_self_eq, inv_inv, hM] at hK2
    have hL2 := Claims1110h.a5Center_map
      ((primeFormConjHom h (idGram F (r + 1)) M)⁻¹ : MulAut _) hL1
    obtain ⟨-, g, hg, hgk⟩ :=
      unitary_fieldAut_components h hn3 hC hp3 (by norm_num) hσp _ hK2
    exact Claims1110h.su_a5_false
      (CFSG.RankThree.Classical.fixSubfield_unitaryFieldData h hp3 (by norm_num) hσp) hn3 g hg hgk
      hL2

end Unitary

end CFSG.RankThree.PartTwo.Sec21.FF79
