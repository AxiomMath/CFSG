module

public import CFSG.Quasithin.Recognition.CertTitsOuter
public import CFSG.Sporadic.Schreier.PairOuter
public import CFSG.Sporadic.Schreier.Outer
public import Certificates.Certificate8074

public noncomputable section

namespace CFSG.Quasithin

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates CFSG.Certificates.Native
  CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.PairNative
  CFSG.ComponentClassification.OuterAutomorphisms

attribute [local irreducible] titsPairO titsPairStrong titsGens titsStrong titsA titsB

private theorem titsPairO_size' : titsPairO.size = 2 := by simp [titsPairO]

private theorem titsPairO_zero' : titsPairO[0]! = titsA := by simp [titsPairO]

private theorem titsPairO_one' : titsPairO[1]! = titsB := by simp [titsPairO]

theorem titsPairQ_eq_titsModelJ
    : titsPairQ.originalSubgroup = titsModelJ := by
  obtain ⟨hA, hB, -, -, -, -, -, -, -⟩ := titsPair_check
  have hJ := titsOuter_check
  have hle : Subgroup.closure {g | ∃ k < titsPairO.size, permOfArr 1755 titsPairO[k]! = g} ≤
      titsModelJ := by
    refine (Subgroup.closure_le _).2 ?_
    rintro g ⟨k, hk, rfl⟩
    rw [titsPairO_size'] at hk
    interval_cases k
    · rw [titsPairO_zero']
      exact (titsSift_iff (rep_permOfArr hA).1).1 hJ.2.1
    · rw [titsPairO_one']
      exact (titsSift_iff (rep_permOfArr hB).1).1 hJ.2.2.1
  have hcardJ : Nat.card titsModelJ = 17971200 := by
    rw [titsModelJ_eq]
    exact card_closure_tits_perm
  rw [← titsPairQ_original] at hle
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [hcardJ, card_titsPair_chain])

theorem card_titsPairQ
    : Nat.card titsPairQ.originalSubgroup = 17971200 := by
  rw [titsPairQ_eq_titsModelJ, titsModelJ_eq]
  exact card_closure_tits_perm

noncomputable def titsPairEquiv
    : CFSG.Open.quasithinTits ≃* titsPairQ.originalSubgroup :=
  ((unitsClosurePairEquiv _ _ _ _
    (coe_permOfArr_titsArray CFSG.Open.quasithinTitsData1 titsChain_check.1)
    (coe_permOfArr_titsArray CFSG.Open.quasithinTitsData2 titsChain_check.2.1)).trans
    (MulEquiv.subgroupCongr titsModelJ_eq.symm)).trans
    (MulEquiv.subgroupCongr titsPairQ_eq_titsModelJ.symm)

theorem titsOuter_card_le_two
    : Nat.card (Outer CFSG.Open.quasithinTits) ≤ 2 := by
  have hs : IsSimpleGroup titsPairQ.originalSubgroup :=
    (MulEquiv.isSimpleGroup_congr titsPairEquiv).1 isSimpleGroup_quasithinTits
  have hk : Nat.card (MulAut titsPairQ.originalSubgroup) ≤
      2 * Nat.card titsPairQ.originalSubgroup := by
    have h := Certificates.certificate8074
    rw [← titsPairQ_original'] at h
    rw [card_titsPairQ]
    exact h
  have hab : (⟨titsPermA, titsPermA_mem⟩ : titsPairQ.originalSubgroup) * ⟨titsPermB, titsPermB_mem⟩ ≠
      ⟨titsPermB, titsPermB_mem⟩ * ⟨titsPermA, titsPermA_mem⟩ :=
    fun h => titsPerm_noncomm (congrArg Subtype.val h)
  have hP := outer_card_le_of_mulAut_card hs hab hk (by rw [card_titsPairQ]; norm_num)
  exact outer_card_le_of_equiv hP titsPairEquiv

end CFSG.Quasithin
