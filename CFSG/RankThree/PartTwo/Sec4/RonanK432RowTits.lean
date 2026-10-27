module

public import CFSG.RankThree.PartTwo.Sec4.RonanK432Refine
public import Certificates.Certificate428001

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK432

open CFSG CFSG.Blueprint CFSG.Sporadic.Schreier.Tits
open CFSG.Monster.B.Co2 (permOfArr)

set_option linter.unusedSectionVars false

theorem titsWitData_gens_mem :
    ∀ k < titsWitData.gens.size, permOfArr titsWitData.n titsWitData.gens[k]! ∈ titsD := by
  intro k hk
  have hk2 : k < 2 := by simpa [titsWitData] using hk
  interval_cases k
  · show permOfArr 1755 titsDerivedArrs[0]! ∈ titsD
    rw [titsDerived_perm (by norm_num)]
    exact titsDGen_mem_titsD (by norm_num)
  · show permOfArr 1755 titsDerivedArrs[1]! ∈ titsD
    rw [titsDerived_perm (by norm_num)]
    exact titsDGen_mem_titsD (by norm_num)

theorem listRow_titsD :
    ListRow ↥titsD := by
  haveI : Finite ↥titsD := Nat.finite_of_card_ne_zero (by rw [card_titsD]; norm_num)
  obtain ⟨P, hPD, hPcard, hP⟩ := Certificates.certificate428001.apply
    titsD titsD (titsWitData_gens_mem) (titsWitData_gens_mem)
  have hP27 : Nat.card (P.subgroupOf titsD) = 3 ^ 3 := by
    rw [card_subgroupOf_of_le hPD, hPcard]
    rfl
  refine listRow_of_wit3 ?_
  refine wit3_all_of_sylow (⊤ : Subgroup ↥titsD) (fun _ _ _ => Subgroup.mem_top _)
    (P.subgroupOf titsD) 3 hP27 (by rw [card_titsD]; decide) ?_
  intro σ hσ hσ1 hσ3
  have hσ' : (σ : Equiv.Perm (Fin 1755)) ∈ P := Subgroup.mem_subgroupOf.mp hσ
  have h1 : (σ : Equiv.Perm (Fin 1755)) ≠ 1 := fun h => hσ1 (Subtype.ext h)
  have h3 : (σ : Equiv.Perm (Fin 1755)) ^ 3 = 1 := by
    simpa using congrArg Subtype.val hσ3
  have hw := wit3_subgroupOf (le_refl titsD) σ.2 (hP _ hσ' h1 h3)
  rwa [Subgroup.subgroupOf_self] at hw

theorem listRowOf_tits_of_cert
    (ht : TauCeti.LieTypeIndex.tits.Valid) :
    ListRowOf (TauCeti.CFSGIndex.lie ⟨.tits, ht⟩).Group := by
  intro S _ _ _ _ ⟨e⟩
  have hm : CFSG.Blueprint.ReeTitsModel S .Tits 2 1 :=
    CFSG.SectionRank.reeTitsModel_of_mulEquiv e (Census.bridgeExceptional46.tits ht)
  obtain ⟨e'⟩ := titsModelEquiv S 2 1 hm
  exact ListRow.of_mulEquiv e'.symm listRow_titsD

end CFSG.RankThree.PartTwo.Sec4.RonanK432
