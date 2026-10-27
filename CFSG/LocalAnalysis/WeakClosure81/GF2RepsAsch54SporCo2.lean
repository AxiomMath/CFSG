module

public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54SporGen
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54SporOrder
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofLieOrder
public import CFSG.Sporadic.Co2Schreier.FullAut
public import Certificates.Certificate75342

public section

namespace CFSG.LocalAnalysis.WeakClosure81

namespace SporCo2

open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.Sporadic.Co2Cert CFSG.Sporadic.Co2Schreier
open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22.F12 (HasCompFactor)

section Pair

noncomputable abbrev T0 : Subgroup co2P := locS.subgroupOf co2P

theorem ne_top_of_card {Q : Subgroup co2P} {m : ℕ} (hQ : Nat.card Q = m)
    (hm : m ≠ 42305421312000) : Q ≠ ⊤ := by
  rintro rfl
  rw [card_top, card_co2P] at hQ
  exact hm hQ.symm

theorem isSylowIn_T0 : IsSylowIn 2 T0 ⊤ := by
  refine ⟨le_top, isPGroup_locS_subgroupOf, ?_⟩
  rw [relIndex_top_right, index_locS_subgroupOf]
  decide

theorem card_subgroupOf {A : Subgroup (Equiv.Perm (Fin 2300))} (hA : A ≤ co2P) {m : ℕ}
    (h : Nat.card A = m) : Nat.card (A.subgroupOf co2P) = m := by
  rw [Nat.card_congr (subgroupOfEquivOfLe hA).toEquiv, h]

theorem T0_le_of {A : Subgroup (Equiv.Perm (Fin 2300))} (h : locS ≤ A) :
    T0 ≤ A.subgroupOf co2P := fun _ hx => mem_subgroupOf.2 (h (mem_subgroupOf.1 hx))

theorem sup_eq_top_of {A B : Subgroup (Equiv.Perm (Fin 2300))} (hA : A ≤ co2P) (hB : B ≤ co2P)
    (h : co2P ≤ A ⊔ B) : A.subgroupOf co2P ⊔ B.subgroupOf co2P = ⊤ := by
  rw [← subgroupOf_sup hA hB, le_antisymm (sup_le hA hB) h, subgroupOf_self]

theorem card_outer_co2P :
    Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer co2P) = 1 := by
  have hinner : CFSG.ComponentClassification.OuterAutomorphisms.inner co2P = ⊤ := by
    rw [CFSG.ComponentClassification.OuterAutomorphisms.inner, MonoidHom.range_eq_top]
    intro α
    obtain ⟨g, hg⟩ := CTUC_Co2_full_automorphisms_inner α
    exact ⟨g, hg.symm⟩
  show (CFSG.ComponentClassification.OuterAutomorphisms.inner co2P).index = 1
  rw [hinner, index_top]

end Pair

end SporCo2

open SporCo2 in
theorem asch54SporGenAt_co2 :
    Asch54SporGenAt .Co2 := by
  obtain ⟨e⟩ := CFSG.Sporadic.Bridge.Co2.nonempty_mulEquiv
  have hsC : Nonempty (TauCeti.SporadicName.Co2.Group ≃* ↥CFSG.Sporadic.Co2Cert.co2P) :=
    ⟨e.symm.trans CFSG.Sporadic.Co2Cert.co2PermEquiv⟩
  have hO := CFSG.ComponentClassification.CatLeafProof.lieOrderFormulasInput
  obtain ⟨A, B, hAP, hBP, hSA, hSB, hcA, hcB, hle⟩ := Certificates.certificate75342
  have cA := card_subgroupOf hAP hcA
  have cB := card_subgroupOf hBP hcB
  have hpair : IsLPair IsCalL0 T0 (A.subgroupOf CFSG.Sporadic.Co2Cert.co2P)
      (B.subgroupOf CFSG.Sporadic.Co2Cert.co2P) :=
    ⟨T0_le_of hSA, T0_le_of hSB, ne_top_of_card cA (by norm_num), ne_top_of_card cB (by norm_num),
      not_hasCompFactor_isCalL0_of_dvd hO (k := 18) (N := 5505024) (by decide +kernel)
        (by rw [cA]),
      not_hasCompFactor_isCalL0_of_dvd hO (k := 18) (N := 11796480) (by decide +kernel)
        (by rw [cB]),
      sup_eq_top_of hAP hBP hle⟩
  exact asch54SporGenAt_of_isLPair_of_card_outer_eq_one hsC card_outer_co2P isSylowIn_T0 hpair

end CFSG.LocalAnalysis.WeakClosure81

end
