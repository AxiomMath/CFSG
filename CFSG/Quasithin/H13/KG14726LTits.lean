module

public import CFSG.Quasithin.H13.KG14726LSylow
public import CFSG.Quasithin.H13.KG14726Tits
public import CFSG.Sporadic.Schreier.TitsOuter

public section

namespace CFSG.Quasithin.H13.KG14726

open Subgroup CFSG.Sporadic.Schreier.Tits

theorem kg115Excluded_titsD :
    KG115Excluded ↥titsD := by
  have : IsSimpleGroup ↥titsD := titsD_simple
  obtain ⟨⟨P₀, hP₀⟩, -⟩ := AT_Tits_intrinsic_local_pair
  obtain ⟨-, hcen, hHz, -⟩ := AT_Tits_local_center_and_centralizer_checks
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS₀ : IsPGroup 2 (titsS.subgroupOf titsD) := by
    rw [← hP₀]
    exact P₀.isPGroup'
  have hS₀i : ¬ 2 ∣ (titsS.subgroupOf titsD).index := by
    rw [← hP₀]
    exact P₀.not_dvd_index
  refine kg115Excluded_of_prime_conj hS₀ hS₀i
    (sylowTwoNoThree_of_twoCentral twoCentralConstrained_titsD
      (by rw [card_titsD]; norm_num) _ hS₀ hS₀i) ?_
  intro u hu huc hu1
  have huS : (u : Equiv.Perm (Fin 1755)) ∈ titsS := mem_subgroupOf.mp hu
  have huZ : (u : Equiv.Perm (Fin 1755)) ∈
      ((center titsS).map titsS.subtype : Set (Equiv.Perm (Fin 1755))) := by
    refine ⟨⟨u, huS⟩, mem_center_iff.mpr fun s => Subtype.ext ?_, rfl⟩
    have := huc ⟨s, titsS_le_titsD s.2⟩ (mem_subgroupOf.mpr s.2)
    show (s : Equiv.Perm (Fin 1755)) * u = u * s
    exact congrArg Subtype.val this
  rw [hcen] at huZ
  have huz : (u : Equiv.Perm (Fin 1755)) = titsZ := by
    rcases huZ with h | h
    · exact absurd (Subtype.ext h) hu1
    · exact h
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨h5, hh5⟩ := exists_prime_orderOf_dvd_card' (G := ↥titsH) 5
    (by rw [titsQH_facts.2.2.2]; norm_num)
  refine ⟨⟨h5, titsH_le_titsD h5.2⟩, Subtype.ext ?_, 5, by norm_num, le_rfl, ?_⟩
  · have := mem_centralizer_singleton_iff.mp (hHz h5.2)
    simp only [coe_mul]
    rw [huz]
    exact this
  · rw [Subgroup.orderOf_mk, Subgroup.orderOf_coe, hh5]

theorem kg115TitsInput_holds :
    KG115TitsInput := by
  intro X _ h
  obtain ⟨e⟩ := titsModelEquiv X 2 1 h
  exact kg115Excluded_of_mulEquiv e kg115Excluded_titsD

end CFSG.Quasithin.H13.KG14726

end
