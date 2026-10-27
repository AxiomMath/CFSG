module

public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54SporGen
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54SporOrder
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofLieOrder
public import CFSG.Sporadic.SmallOddCore.Co3Aut
public import Certificates.Certificate75337

public section

namespace CFSG.LocalAnalysis.WeakClosure81

namespace SporCo3

open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.Sporadic.Schreier.Co3 CFSG.Sporadic.Schreier.Co3.Native
open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22.F12 (HasCompFactor)

section Pair

noncomputable abbrev T0 : Subgroup co3P := co3T.subgroupOf co3P

noncomputable abbrev A0 : Subgroup co3P := pairA.subgroupOf co3P

noncomputable abbrev B0 : Subgroup co3P := pairB.subgroupOf co3P

theorem card_A0 : Nat.card A0 = 3072 := by
  rw [Nat.card_congr (subgroupOfEquivOfLe Certificates.certificate75337.1).toEquiv,
    Certificates.certificate75337.2.2.2.2.1]

theorem card_B0 : Nat.card B0 = 27648 := by
  rw [Nat.card_congr (subgroupOfEquivOfLe Certificates.certificate75337.2.1).toEquiv,
    Certificates.certificate75337.2.2.2.2.2.1]

theorem ne_top_of_card {Q : Subgroup co3P} {m : ℕ} (hQ : Nat.card Q = m)
    (hm : m ≠ 495766656000) : Q ≠ ⊤ := by
  rintro rfl
  rw [card_top, card_co3P] at hQ
  exact hm hQ.symm

theorem isSylowIn_T0 : IsSylowIn 2 T0 ⊤ := by
  refine ⟨le_top, co3T_isPGroup, ?_⟩
  rw [relIndex_top_right]
  exact co3T_not_dvd_index

theorem T0_le_A0 : T0 ≤ A0 := fun _ hx =>
  mem_subgroupOf.2 (Certificates.certificate75337.2.2.1 (mem_subgroupOf.1 hx))

theorem T0_le_B0 : T0 ≤ B0 := fun _ hx =>
  mem_subgroupOf.2 (Certificates.certificate75337.2.2.2.1 (mem_subgroupOf.1 hx))

theorem sup_pairA_pairB : pairA ⊔ pairB = co3P :=
  le_antisymm (sup_le Certificates.certificate75337.1 Certificates.certificate75337.2.1)
    Certificates.certificate75337.2.2.2.2.2.2

theorem A0_sup_B0 : A0 ⊔ B0 = ⊤ := by
  rw [A0, B0, ← subgroupOf_sup Certificates.certificate75337.1
    Certificates.certificate75337.2.1, sup_pairA_pairB, subgroupOf_self]

theorem card_outer_co3P :
    Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer co3P) = 1 := by
  have hinner : CFSG.ComponentClassification.OuterAutomorphisms.inner co3P = ⊤ := by
    rw [CFSG.ComponentClassification.OuterAutomorphisms.inner, MonoidHom.range_eq_top]
    intro α
    obtain ⟨g, hg⟩ := CFSG.Sporadic.SmallOddCore.co3P_allInner α
    exact ⟨g, hg.symm⟩
  show (CFSG.ComponentClassification.OuterAutomorphisms.inner co3P).index = 1
  rw [hinner, index_top]

end Pair

end SporCo3

open SporCo3 in
theorem asch54SporGenAt_co3 :
    Asch54SporGenAt .Co3 := by
  obtain ⟨e⟩ := CFSG.Sporadic.Bridge.Co3.nonempty_mulEquiv
  have hsC : Nonempty (TauCeti.SporadicName.Co3.Group ≃* ↥CFSG.Sporadic.Schreier.Co3.co3P) :=
    ⟨e.symm.trans CFSG.Sporadic.Schreier.Co3.co3PermEquiv⟩
  have hO := CFSG.ComponentClassification.CatLeafProof.lieOrderFormulasInput
  have hpair : IsLPair IsCalL0 T0 A0 B0 :=
    ⟨T0_le_A0, T0_le_B0, ne_top_of_card card_A0 (by norm_num), ne_top_of_card card_B0 (by norm_num),
      not_hasCompFactor_isCalL0_of_dvd hO (k := 10) (N := 3072) (by decide +kernel)
        (by rw [card_A0]),
      not_hasCompFactor_isCalL0_of_dvd hO (k := 10) (N := 27648) (by decide +kernel)
        (by rw [card_B0]),
      A0_sup_B0⟩
  exact asch54SporGenAt_of_isLPair_of_card_outer_eq_one hsC card_outer_co3P isSylowIn_T0 hpair

end CFSG.LocalAnalysis.WeakClosure81

end
