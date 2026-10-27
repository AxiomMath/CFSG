module

public import CFSG.LocalAnalysis.StandardType.GGKD2Connected1619Contracts
public import CFSG.LocalAnalysis.StandardType.GGTwF4FixOrderThree
public import CFSG.LocalAnalysis.StandardType.GGTableBOutdiag
import CFSG.LocalAnalysis.StandardType.GGKD2Connected1619SU3Holds
import CFSG.LocalAnalysis.StandardType.GGKD2Connected1619CoverDescentHolds
import CFSG.LocalAnalysis.ComponentInitial.LocalComponents
import CFSG.GroupTheory.LocalCores.Components
import CFSG.LocalAnalysis.StandardType.GGSecFiveNonWeylOfKnown

public section

namespace S2MathAs3_1619Final

open CFSG CFSG.Assembly CFSG.StandardType CFSG.ClassicalGroups.UnitaryFlag


theorem reeProducer_holds {f} (hf : Odd f) (h3 : 3 ≤ f) :
    Odd f ∧ 3 ≤ f ∧
      ∀ lab : LargeEvenLabel, LargeEvenInLambda2 lab → lab.tag = .twF4 → lab.n = f →
        LargeEvenLabelAll lab (fun R _ I _ => ReeWitness f R I) := by
  refine ⟨hf, h3, ?_⟩
  intro lab _ ht hn
  obtain ⟨t, l, n⟩ := lab
  dsimp only at ht hn
  subst ht hn
  intro Q hQ
  have h2a1 : 2 * ((n - 1) / 2) + 1 = n := by
    obtain ⟨k, hk⟩ := hf
    omega
  have ha : 1 ≤ (n - 1) / 2 := by omega
  have hA : ∀ (K : Type) [Field K] [Finite K], Nat.card K = 2 ^ (2 * ((n - 1) / 2) + 1) →
      ReeWitness n (LargeEvenCenterQuot (LargeEvenTwF4H ((n - 1) / 2) K))
        (LargeEvenChevIDImage LargeEvenCartanF4 K (LargeEvenTwF4H ((n - 1) / 2) K)) := by
    intro K _ _ hK
    unfold ReeWitness
    refine ⟨hf, h3, fun φ hφI hφ1 hφ3 => ?_⟩
    obtain ⟨e⟩ :=
      twF4_ggAutFixedSubgroup_mulEquiv_unitarySU ((n - 1) / 2) ha K hK φ hφI hφ3 hφ1
    have hfix : ggFixSub φ = ggAutFixedSubgroup φ := by
      ext x
      rw [mem_ggFixSub, mem_ggAutFixedSubgroup]
    have hE : Nonempty (↥(ggFixSub φ) ≃* ↥(unitarySU 2 (2 * ((n - 1) / 2) + 1)
        (GaloisField 2 (2 * (2 * ((n - 1) / 2) + 1))) 3)) :=
      ⟨(MulEquiv.subgroupCongr hfix).trans e⟩
    rw [h2a1] at hE
    have hcard : Nat.card (GaloisField 2 (2 * n)) = 2 ^ (2 * n) :=
      GaloisField.card 2 (2 * n) (by omega)
    exact ⟨GaloisField 2 (2 * n), inferInstance, inferInstance, inferInstance, hcard,
      ⟨Nat.prime_two, by omega, hcard⟩, hE⟩
  have hQ' : LargeEvenRecipeTwF4 ((n - 1) / 2) Q := by
    simpa only [CFSG.StandardType.LargeEvenRawDatum] using hQ
  have h := recipeTwF4_and (P := fun R _ I _ => ReeWitness n R I) (fun K _ _ hK => hA K hK) hQ'
  simpa only [CFSG.StandardType.LargeEvenRawDatum] using h

theorem ree_rawActionAt_of_witness {R : Type} [Group R] {I : Set (MulAut R)}
    {f : ℕ} (h : ReeWitness f R I) : RawActionAt R I := by
  intro phi hphiI hphi1 hphi3 C hC hlabel beta hbetaI hcomm hpres
  obtain ⟨K, hField, hFinite, hChar, hcard, hU, ⟨e⟩⟩ := h.2.2 phi hphiI hphi1 hphi3
  let : Field K := hField
  let : Finite K := hFinite
  let : CharP K 2 := hChar
  let D : Subgroup (ggFixSub phi) := C.subgroupOf (ggFixSub phi)
  have hD : CFSG.IsComponent D :=
    (CFSG.LocalAnalysis.ComponentInitial.isComponentOf_iff_isComponent_subgroupOf hC.1).mp hC
  let E : Subgroup (unitarySU 2 f K 3) := D.map e.toMonoidHom
  have hE : CFSG.Assembly.IsComponentOf E ⊤ :=
    (CFSG.ComponentClassification.AssemblyBPredicates.isComponentOf_top_iff_native E).mpr
      (CFSG.LocalCores.isComponent_map_mulEquiv e hD)
  let ec : C ≃* E :=
    (Subgroup.subgroupOfEquivOfLe hC.1).symm.trans
      (D.equivMapOfInjective e.toMonoidHom e.injective)
  let eqc : (C ⧸ Subgroup.center C) ≃* (E ⧸ Subgroup.center E) :=
    QuotientGroup.congr _ _ ec (Subgroup.map_center_eq ec)
  exact (su3NoA1Eight_holds f h.2.1 K hU E hE (ggHasLabel_of_mulEquiv eqc hlabel)).elim

theorem noSetupAt_twF4_labelAll {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) (htag : lab.tag = .twF4) :
    LargeEvenLabelAll lab (fun R _ I _ => NoSetupAt R I) := by
  have hpar : Odd lab.n ∧ 3 ≤ lab.n := by
    have hpar' : lab.rank = 0 ∧ Odd lab.n ∧ 3 ≤ lab.n := by
      simpa [LargeEvenInLambda2, htag] using hlab.2
    exact hpar'.2
  exact LargeEvenLabelAll.mono
    (fun R _ I _ h => coverDescent_holds R I (ree_rawActionAt_of_witness h))
    ((reeProducer_holds hpar.1 hpar.2).2.2 lab hlab htag rfl)

end S2MathAs3_1619Final

end
