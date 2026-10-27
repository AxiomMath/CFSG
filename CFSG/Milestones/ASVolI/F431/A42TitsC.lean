module

public import CFSG.Milestones.ASVolI.F431.A42Tits
public import Certificates.Certificate7450

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.ASVolI.ChF CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H13.F431
  CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion
  CFSG.Sporadic.Schreier.Tits

section Tits

set_option linter.unusedSectionVars false

theorem burnsideF4m_tEl_mem_titsK : CFSG.Quasithin.H13.F431.TwoF4.tEl.1 ∈ titsK :=
  (mem_titsK_iff_sift CFSG.Quasithin.H13.F431.TwoF4.rep_tEl).1 Certificates.certificate7450

theorem burnsideF4m_tD_mem_O2N : CFSG.Quasithin.H13.F431.TitsD.tD ∈ pCoreOf 2 titsND := by
  have hp : IsPGroup 2 titsK := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact IsPGroup.of_card (n := 10) (by rw [titsQK_facts.2.2.2]; norm_num)
  have hK : titsK ≤ pCoreOf 2 titsN :=
    CFSG.LieType.BorelTits.le_pCoreOf 2 titsK_le_titsN titsK_normal_N hp
  have hmap : titsND.map titsD.subtype = titsN := by
    rw [Subgroup.subgroupOf_map_subtype]
    exact inf_eq_left.mpr titsN_le_titsD
  have h := CFSG.Quasithin.H13.F431.pCoreOf_map_of_injective titsD.subtype
    titsD.subtype_injective titsND
  rw [hmap] at h
  have ht : (CFSG.Quasithin.H13.F431.TitsD.tD : Equiv.Perm (Fin 1755)) ∈ pCoreOf 2 titsN :=
    hK burnsideF4m_tEl_mem_titsK
  rw [h] at ht
  obtain ⟨y, hy, hye⟩ := ht
  have hyt : y = CFSG.Quasithin.H13.F431.TitsD.tD := Subtype.ext hye
  rw [← hyt]
  exact hy

variable {f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E} {Y : Type} [Group Y]
  {β : Cpl M₁ M₂ Y} {M : Type} [Group M] {ε : Y →* M} {z : M}

theorem burnsideF4m_A42Rest'_of'' (hrest : burnsideF4m_A42Rest'') : burnsideF4m_A42Rest' :=
  burnsideF4m_A42Rest'_of''_of_tD burnsideF4m_tD_mem_O2N hrest

end Tits

end CFSG.ASVolI
