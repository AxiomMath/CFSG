module

public import CFSG.Quasithin.Vol2.Ch12Sec7GzSFacts
public import CFSG.Quasithin.Vol2.Ch12Sec7GzSPCore

public section

namespace CFSG.Quasithin.H13.I1277

open CFSG.Open CFSG.Quasithin.H13.S127.Mod Certificates.Data.S1277Facts
open scoped IsMulCommutative

section Fin1

variable {G : Type} [Group G] [Finite G]

theorem structAt_T_fixed {V M M₀ P : Subgroup G} [IsMulCommutative ↥V] {Γ : List B6} {z : G}
    (SP : SplitHyp V M M₀) (C : Coding ↥V) (hΓ1 : ∀ a ∈ autOn M V, C.cB a ∈ Γ)
    (hΓ2 : ∀ B ∈ Γ, ∃ a ∈ autOn M V, C.cB a = B) (hz : z ∈ V) (hzc : C.cd ⟨z, hz⟩ = 5)
    (hF : ModelFacts1277 Γ) (hVel : IsElemAbelian 2 V) (hV64 : Nat.card V = 64)
    (hPM : P ≤ M) (hPz : P ≤ Gz z) (hP2 : IsPGroup 2 ↥P) (hPodd : ¬ 2 ∣ P.index)
    (hne : ¬ Gz z ≤ M) (hNM : Subgroup.normalizer (V : Set G) ≤ M) (hz2 : z * z = 1)
    (hchar : Gz z ⊓ Subgroup.centralizer ((pCoreOf 2 (Gz z) : Subgroup G) : Set G) ≤
      pCoreOf 2 (Gz z)) : StructAt G z := by
  have hzH : z ∈ Gz z := Subgroup.mem_centralizer_singleton_iff.2 rfl
  have hzQ : z ∈ pCoreOf 2 (Gz z) :=
    mem_pcore_of_central hzH (fun h hh => Subgroup.mem_centralizer_singleton_iff.1 hh) hz2
  have hPodd' : ¬ 2 ∣ P.relIndex (Gz z) := fun hd =>
    hPodd (hd.trans (Subgroup.relIndex_dvd_index_of_le hPz))
  have hQP : pCoreOf 2 (Gz z) ≤ P := pcore_le_of_odd hPz hP2 hPodd'
  have hPK : P ≤ M ⊓ Gz z := le_inf hPM hPz
  have hodd : ¬ 2 ∣ (M ⊓ Gz z).relIndex (Gz z) := fun hd =>
    hPodd' (hd.trans (Subgroup.relIndex_dvd_of_le_left (Gz z) hPK))
  refine model_main_facts SP C hΓ1 hΓ2 hz hzc hF hVel hV64 rfl hzQ (hQP.trans hPK) (pcore_normal _)
    (pcore_isPGroup _) (fun X hXH hXn hX2 => pcore_max _ hXH hXn hX2) ?_ hodd hne ?_
  · intro h hh hcen
    exact hchar (Subgroup.mem_inf.2 ⟨hh, Subgroup.mem_centralizer_iff.2 fun y hy =>
      (hcen y hy).symm⟩)
  · intro h hh hhV
    exact Subgroup.mem_inf.2 ⟨hNM hhV, hh⟩

end Fin1

end CFSG.Quasithin.H13.I1277

end
