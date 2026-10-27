module

public import CFSG.Quasithin.H13.LocDblOddRu
public import Certificates.Certificate589230
public import Certificates.Certificate589231
public import Certificates.Certificate589232
public import Certificates.Certificate589233
public import Certificates.Certificate589234
public import Certificates.Certificate589235
public import Certificates.Certificate589236
import all CFSG.Blueprint.NativeSporadic

public section

namespace CFSG.Quasithin.H13.K1262Two.RuP

set_option maxRecDepth 20000

open CFSG.QuasithinUnique.K1.SporadicPerm CFSG.Sporadic.SmallF2
open CFSG.Quasithin.H13.LocDbl
open CFSG.Sporadic.Ru.Native (ruData)

theorem ru_card : Nat.card ↥(J ruData) = 145926144000 := by
  have hF : Facts ruData 3 := CFSG.Sporadic.Ru.ruFacts
  exact (Nat.card_congr (seedEquiv hF.toBaseFacts).toEquiv).symm.trans CFSG.Sporadic.Ru.card_Ru

theorem noBig_100 :
    NoBig (Subgroup.closure {x | x ∈ [ruT2 (a ruData) (b ruData),
      ruT1 (a ruData) (b ruData) * ruT2 (a ruData) (b ruData) * ruT1 (a ruData) (b ruData),
      ruT3 (a ruData) (b ruData),
      ruT1 (a ruData) (b ruData) * ruT3 (a ruData) (b ruData) * ruT1 (a ruData) (b ruData)]}) :=
  Certificates.certificate589230

theorem noBig_010 :
    NoBig (Subgroup.closure {x | x ∈ [ruT1 (a ruData) (b ruData),
      ruT2 (a ruData) (b ruData) * ruT1 (a ruData) (b ruData) * ruT2 (a ruData) (b ruData),
      ruT3 (a ruData) (b ruData),
      ruT2 (a ruData) (b ruData) * ruT3 (a ruData) (b ruData) * ruT2 (a ruData) (b ruData)]}) :=
  Certificates.certificate589231

theorem noBig_001 :
    NoBig (Subgroup.closure {x | x ∈ [ruT1 (a ruData) (b ruData),
      ruT3 (a ruData) (b ruData) * ruT1 (a ruData) (b ruData) * ruT3 (a ruData) (b ruData),
      ruT2 (a ruData) (b ruData),
      ruT3 (a ruData) (b ruData) * ruT2 (a ruData) (b ruData) * ruT3 (a ruData) (b ruData)]}) :=
  Certificates.certificate589232

theorem noBig_110 :
    NoBig (Subgroup.closure {x | x ∈ [
      ruT2 (a ruData) (b ruData) * ruT1 (a ruData) (b ruData), ruT3 (a ruData) (b ruData),
      ruT1 (a ruData) (b ruData) * ruT3 (a ruData) (b ruData) * ruT1 (a ruData) (b ruData)]}) :=
  Certificates.certificate589233

theorem noBig_101 :
    NoBig (Subgroup.closure {x | x ∈ [ruT2 (a ruData) (b ruData),
      ruT1 (a ruData) (b ruData) * ruT2 (a ruData) (b ruData) * ruT1 (a ruData) (b ruData),
      ruT3 (a ruData) (b ruData) * ruT1 (a ruData) (b ruData)]}) :=
  Certificates.certificate589234

theorem noBig_011 :
    NoBig (Subgroup.closure {x | x ∈ [ruT1 (a ruData) (b ruData),
      ruT2 (a ruData) (b ruData) * ruT1 (a ruData) (b ruData) * ruT2 (a ruData) (b ruData),
      ruT3 (a ruData) (b ruData) * ruT2 (a ruData) (b ruData)]}) :=
  Certificates.certificate589235

theorem noBig_111 :
    NoBig (Subgroup.closure {x | x ∈ [
      ruT2 (a ruData) (b ruData) * ruT1 (a ruData) (b ruData),
      ruT3 (a ruData) (b ruData) * ruT1 (a ruData) (b ruData)]}) :=
  Certificates.certificate589236

theorem ru_covers :
    Covers (ruT1 (a ruData) (b ruData)) (ruT2 (a ruData) (b ruData))
      (ruT3 (a ruData) (b ruData)) :=
  ⟨noBig_100, noBig_010, noBig_001, noBig_110, noBig_101, noBig_011, noBig_111⟩

theorem ru_T_card :
    Nat.card (Subgroup.closure {x | x ∈ [ruT1 (a ruData) (b ruData), ruT2 (a ruData) (b ruData),
      ruT3 (a ruData) (b ruData)]}) = 2 ^ 14 := by
  have h : CFSG.QuasithinUnique.Ch1.SporLat.RuCert.ruSgK =
      [ruT1 (a ruData) (b ruData), ruT2 (a ruData) (b ruData), ruT3 (a ruData) (b ruData)] := by
    simp only [CFSG.QuasithinUnique.Ch1.SporLat.RuCert.ruSgK, ruQp, List.map_cons, List.map_nil,
      ruT1, ruT2, ruT3]
  rw [← h]
  exact RuCert.ru_S_card

theorem noBigGroup_Ru
    (H : Subgroup ↥(J ruData)) (hH : H ≠ ⊤) (h13 : 2 ^ 13 ∣ Nat.card H) (h9 : 9 ∣ Nat.card H)
    (h5 : 5 ∣ Nat.card H) : False := by
  have hcard := ru_card
  by_cases h14 : 2 ^ 14 ∣ Nat.card H
  ·
    obtain ⟨d, hd⟩ := h14
    have h1 := H.card_mul_index
    rw [hcard, hd] at h1
    have hdi : d * H.index = 8906625 :=
      Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 2 ^ 14)
        ((by rw [← mul_assoc]; exact h1 : 2 ^ 14 * (d * H.index) = 145926144000).trans
          (by norm_num))
    have hodd : ¬ 2 ∣ H.index := fun h2 => by
      have := (Dvd.dvd.mul_left h2 d : 2 ∣ d * H.index)
      rw [hdi] at this
      exact absurd this (by decide)
    obtain ⟨N, hN, hdvd⟩ := oddIndexBound_Ru_group H hodd hH
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hN
    rcases hN with rfl | rfl
    · exact absurd (h9.trans hdvd) (by decide)
    · exact absurd (h9.trans hdvd) (by decide)
  · set T : Subgroup ↥(J ruData) := Subgroup.closure {x | x ∈ [ruT1 (a ruData) (b ruData),
      ruT2 (a ruData) (b ruData), ruT3 (a ruData) (b ruData)]} with hT
    have hTc : Nat.card T = 2 ^ 14 := ru_T_card
    have hTi : ¬ 2 ∣ T.index := by
      have h1 := T.card_mul_index
      rw [hcard, hTc] at h1
      have h2 : T.index = 8906625 :=
        Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 2 ^ 14) (h1.trans (by norm_num))
      rw [h2]
      decide
    exact noBig_of_covers ru_covers hT hTc hTi H hH h13 h14 h9 h5

end CFSG.Quasithin.H13.K1262Two.RuP
