module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35B5E1

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open CFSG.Quasithin.F53Mod
open scoped commutatorElement

namespace F53.Stellmacher

open CosetGeom F53 Equiv

namespace S35.B5

open S35.Std

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

omit [Finite G] in
theorem comm_Qv_Lr_le (β : Geo H M) : ⁅Qv β, Lr β⁆ ≤ Qv β := by
  rw [Subgroup.commutator_le]
  intro q hq x hx
  have hxs : x ∈ stab β := oTwoRes_le _ hx
  have h1 : x * q⁻¹ * x⁻¹ ∈ Qv β :=
    conj_mem_of_le_normalizer (le_normalizer_pCoreOf 2 (stab β)) hxs ((Qv β).inv_mem hq)
  have e : ⁅q, x⁆ = q * (x * q⁻¹ * x⁻¹) := by simp only [commutatorElement_def]; group
  rw [e]
  exact (Qv β).mul_mem hq h1

theorem condD_of_comm (hC : Ch.Ctx H M S) (h6a : Claim6a H M)
    {β l δ l0 γ : Geo H M} (hcfg : Cfg H M β l δ l0 γ)
    (hK : ⁅Yg β δ γ, ⁅Qv β, Lr β⁆⁆ ≤ Vn β) :
    ∃ δ'' : Geo H M, δ'' ∈ nbrs l ∧ δ'' ≠ β ∧ δ'' ≠ δ ∧ Vn δ'' ≤ Vn β ⊔ Vn δ := by
  have hS := hC.sit
  obtain ⟨t, htc, htl⟩ := IsConcreteLE.not_le_iff_exists.mp (h6a β l hcfg.vβ hcfg.l_nbr)
  have htQ : t ∈ Qv β := comm_Qv_Lr_le β htc
  have hlt := hcfg.vl
  have hβl : β ∈ nbrs l := mem_nbrs_symm.mp hcfg.l_nbr
  have htsl : t ∈ stab l := Qv_le_stab hS hcfg.l_nbr htQ
  have htsβ : t ∈ stab β := Ch.Qv_le_stab' β htQ
  have htδ : t ∉ stab δ := fun h =>
    htl (mem_Qv_of_fix_two hS hlt hβl hcfg.δ_nbr hcfg.δ_ne.symm htsl htsβ h)
  let g : ↥(H ⊔ M) := ⟨t, stab_le l htsl⟩
  have hgβ : g • β = β := smul_eq_of_mem_stab htsβ
  refine ⟨g • δ, smul_mem_nbrs_of_stab htsl hcfg.δ_nbr, fun h => hcfg.δ_ne ?_, fun h => htδ ?_, ?_⟩
  · exact MulAction.injective g (h.trans hgβ.symm)
  · exact mem_stab_of_smul_eq h
  · intro u hu
    rw [Vn_smul, mem_conjSub] at hu
    have hv : t⁻¹ * u * t ∈ Yg β δ γ := Subgroup.mem_sup_left (Subgroup.mem_sup_left hu)
    have hcm : ⁅t⁻¹ * u * t, t⁆ ∈ Vn β :=
      hK (Subgroup.commutator_mem_commutator hv htc)
    have e : u = (⁅t⁻¹ * u * t, t⁆)⁻¹ * (t⁻¹ * u * t) := by
      simp only [commutatorElement_def]; group
    rw [e]
    exact (Vn β ⊔ Vn δ).mul_mem ((Vn β ⊔ Vn δ).inv_mem (Subgroup.mem_sup_left hcm))
      (Subgroup.mem_sup_right hu)

end S35.B5

end F53.Stellmacher

end CFSG.Quasithin
