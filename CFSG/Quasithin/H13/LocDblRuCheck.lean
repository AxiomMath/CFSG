module

public import Certificates.Certificate7032
import all CFSG.Blueprint.NativeSporadic

set_option maxRecDepth 100000

public section

namespace CFSG.Quasithin.H13.LocDbl.RuCert

open CFSG.QuasithinUnique CFSG.QuasithinUnique.K1.SporadicPerm CFSG.Sporadic.SmallF2
open CFSG.Quasithin.H13.LocDbl.RuCov
open CFSG.Sporadic.Ru.Native (ruData)

section Cert

theorem ru_S_card : Nat.card ruS = 2 ^ 14 := Certificates.certificate7032.1

theorem ru_VA_card : Nat.card ruVA = 245760 := Certificates.certificate7032.2.2.2.1

theorem ru_VB_card : Nat.card ruVB = 344064 := Certificates.certificate7032.2.2.2.2.1

theorem ru_over : ∀ Y : Subgroup (J ruData), ruS ≤ Y → Y ≠ ⊤ → Y ≤ ruVA ∨ Y ≤ ruVB :=
  Certificates.certificate7032.2.2.2.2.2.1

theorem ru_over_dvd : ∀ Y : Subgroup (J ruData), ruS ≤ Y → Y ≠ ⊤ →
    ∃ N ∈ [245760, 344064], Nat.card Y ∣ N := by
  intro Y hY hne
  rcases ru_over Y hY hne with h | h
  · exact ⟨245760, by simp, ru_VA_card ▸ Subgroup.card_dvd_of_le h⟩
  · exact ⟨344064, by simp, ru_VB_card ▸ Subgroup.card_dvd_of_le h⟩

end Cert

theorem ru_sq : ∀ N ∈ [245760, 344064],
    N ≠ 0 ∧ (N.primeFactors.filter fun r => r ^ 2 ∣ N).card ≤ 2 := by
  intro N hN
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hN
  rcases hN with h | h <;> rw [h] <;> refine ⟨by norm_num, ?_⟩ <;> simp [Nat.primeFactors] <;>
    decide

theorem ru_card : Nat.card (J ruData) = 145926144000 :=
  (Nat.card_congr (seedEquiv CFSG.Sporadic.Ru.ruFacts.toBaseFacts).toEquiv).symm.trans
    CFSG.Sporadic.Ru.card_Ru

theorem ru_S_index :
    ruS.index = 8906625 := by
  have h1 := ruS.card_mul_index
  rw [ru_S_card, ru_card] at h1
  omega

theorem ru_S_sylow :
    IsSylowTwoOf ruS ⊤ := by
  refine ⟨le_top, IsPGroup.of_card ru_S_card, ?_⟩
  have h : (ruS.subgroupOf ⊤).index = ruS.index := Subgroup.relIndex_top_right ruS
  rw [h, ru_S_index]
  decide

end CFSG.Quasithin.H13.LocDbl.RuCert

end
