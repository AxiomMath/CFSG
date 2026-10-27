module

public import CFSG.Quasithin.Vol2.Ch1Sec3L42J4
public import CFSG.Quasithin.Vol2.Ch1Sec3L42Gen
public import CFSG.Quasithin.Vol2.KGFactHeInspJ4

public section

namespace CFSG.Quasithin.L139L42

open CFSG.Open (pCoreOf)
open CFSG.Blueprint

theorem exists_inner_j4_sub
    (hJ4 : FactJ4L42Inner) {Q : Type} [Group Q] [Finite Q]
    {K B : Subgroup Q} (hK : IsSporadic .J4 ↥K) (hBK : B ≤ K) (h4 : IsPSL 4 2 1 (ModO2 B))
    {g : Q} (hgK : g ∈ Subgroup.normalizer (K : Set Q))
    (hgB : g ∈ Subgroup.normalizer (B : Set Q)) :
    ∃ b ∈ B, ∀ x ∈ B, (g * x * g⁻¹)⁻¹ * (b * x * b⁻¹) ∈ pCoreOf 2 B := by
  obtain ⟨eK⟩ := hK
  let eJ : ↥K ≃* CFSG.Sporadic.J4.J :=
    eK.trans (CFSG.Sporadic.J4.seedEquiv CFSG.Sporadic.J4.j4Facts.mat)
  obtain ⟨k, hk⟩ := CFSG.Quasithin.H13.KGInsp.j4_all_inner eJ (L139A5.conjSub hgK)
  have h4' : IsPSL 4 2 1 (ModO2 (B.subgroupOf K)) :=
    IsPSL.of_mulEquiv (modO2SubgroupOfEquiv hBK).symm h4
  exact exists_inner_of_conj hBK hgK hk
    (hJ4 ↥K ⟨eK⟩ (B.subgroupOf K) h4' k (mem_normalizer_of_conj hgK hgB hk))

end CFSG.Quasithin.L139L42
