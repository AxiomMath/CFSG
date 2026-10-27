module

public import CFSG.Quasithin.Recognition.Kleidman.F204.CaseIBase
public import CFSG.Quasithin.Recognition.Kleidman.F204.CaseIOffNatA

public section

namespace CFSG.Quasithin.Kleidman.F204

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.F7
  CFSG.Quasithin.FA5 CFSG.Quasithin.F53 CFSG.Quasithin.CosetGeom
  CFSG.QuasithinUnique.A5.Delta5

open scoped commutatorElement

set_option linter.unusedSectionVars false

variable {G : Type} [Group G] [Finite G] {L1 L2 S D X : Subgroup G}

section Interface

variable (F : Frame L1 L2 S D X)
include F

theorem vertex_hsq {α β : Geo (P1 L1 L2 S) (P2 L1 L2 S)} (hα : vtype α = true)
    (hβ : β ∈ nbrs α) :
    ∀ t : ↥(P1 L1 L2 S ⊔ P2 L1 L2 S), (t : G) ∈ Qv β → ∀ μ ∈ nbrs α, t • (t • μ) = μ := by
  have hA := Amal.of_frame F
  intro t ht μ hμ
  have hsq : (t : G) * (t : G) ∈ Qv α := sq_mem_Qv_of_mem_nbrs F hα hβ ht
  have hμs : (t * t : ↥(P1 L1 L2 S ⊔ P2 L1 L2 S)) • μ = μ :=
    smul_eq_of_mem_stab (hA.Qv_le_stab_of_mem_nbrs hμ hsq)
  rw [← mul_smul]
  exact hμs

theorem vertex_hfree {α β : Geo (P1 L1 L2 S) (P2 L1 L2 S)} (hα : vtype α = true)
    (hβ : β ∈ nbrs α) :
    ∀ t : ↥(P1 L1 L2 S ⊔ P2 L1 L2 S), (t : G) ∈ Qv β → ∀ μ ∈ nbrs α, μ ≠ β → t • μ = μ →
      ∀ μ' ∈ nbrs α, t • μ' = μ' := by
  have hA := Amal.of_frame F
  obtain ⟨φ, hφs, hφk⟩ := exists_phi_stab F hα
  have hT := card_map_Qv_nbr F hα hβ hφs hφk
  set T := ((Qv β).subgroupOf (stab α)).map φ with hTdef
  have hQβα : Qv β ≤ stab α := hA.Qv_le_stab_of_mem_nbrs (mem_nbrs_symm hβ)
  have hcomm : ∀ q t : G, q ∈ Qv β → t ∈ Qv β → q * t * q⁻¹ * t⁻¹ ∈ Qv α := by
    intro q t hq ht
    have hq' : φ ⟨q, hQβα hq⟩ ∈ T := ⟨⟨q, hQβα hq⟩, Subgroup.mem_subgroupOf.mpr hq, rfl⟩
    have ht' : φ ⟨t, hQβα ht⟩ ∈ T := ⟨⟨t, hQβα ht⟩, Subgroup.mem_subgroupOf.mpr ht, rfl⟩
    have hsq := fun {k : Alt5} (hk : k ∈ T) => alt5_klein_sq hT hk
    have h1 := hsq hq'
    have h2 := hsq ht'
    have h3 := hsq (T.mul_mem hq' ht')
    set a := φ ⟨q, hQβα hq⟩
    set b := φ ⟨t, hQβα ht⟩
    have hab : a * b * a⁻¹ * b⁻¹ = 1 := by
      have ha : a⁻¹ = a := by
        calc a⁻¹ = a⁻¹ * (a * a) := by rw [h1]; group
          _ = a := by group
      have hb : b⁻¹ = b := by
        calc b⁻¹ = b⁻¹ * (b * b) := by rw [h2]; group
          _ = b := by group
      rw [ha, hb]
      calc a * b * a * b = (a * b) * (a * b) := by group
        _ = 1 := h3
    have : φ (⟨q, hQβα hq⟩ * ⟨t, hQβα ht⟩ * ⟨q, hQβα hq⟩⁻¹ * ⟨t, hQβα ht⟩⁻¹) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv]; exact hab
    have hk := MonoidHom.mem_ker.mpr this
    rw [hφk, Subgroup.mem_subgroupOf] at hk
    simpa using hk
  intro t ht μ hμ hμβ hfix ν hν
  by_cases hνβ : ν = β
  · subst hνβ
    exact smul_eq_of_mem_stab (pCoreOf_le 2 (stab ν) ht)
  obtain ⟨q, hq, hqμ⟩ := exists_Qv_smul_nbr F hα hβ hμ hν hμβ hνβ
  have hc : ((q * t * q⁻¹ * t⁻¹ : ↥(P1 L1 L2 S ⊔ P2 L1 L2 S)) : G) ∈ Qv α := by
    have := hcomm (q : G) (t : G) hq ht
    simpa using this
  have hcs : (q * t * q⁻¹ * t⁻¹ : ↥(P1 L1 L2 S ⊔ P2 L1 L2 S)) • ν = ν :=
    smul_eq_of_mem_stab (hA.Qv_le_stab_of_mem_nbrs hν hc)
  have h1 : (q * t * q⁻¹) • ν = ν := by
    rw [mul_smul, mul_smul, ← hqμ, inv_smul_smul, hfix]
  have h2 : (q * t * q⁻¹ * t⁻¹) • (t • ν) = ν := by
    rw [show (q * t * q⁻¹ * t⁻¹) • (t • ν) = (q * t * q⁻¹) • ((t⁻¹ * t) • ν) from by
      rw [mul_smul (q * t * q⁻¹) t⁻¹, mul_smul t⁻¹ t]]
    rw [inv_mul_cancel, one_smul, h1]
  exact MulAction.injective (q * t * q⁻¹ * t⁻¹) (h2.trans hcs.symm)

theorem vertex_hgen (hT1 : ConfigT1 L1 L2 S) {α : Geo (P1 L1 L2 S) (P2 L1 L2 S)}
    (hα : vtype α = true) :
    Zv α ≤ ⨆ (ν : Geo (P1 L1 L2 S) (P2 L1 L2 S)) (_ : ν ∈ nbrs α),
      Zv α ⊓ Subgroup.centralizer (Qv ν : Set G) := by
  have hA := Amal.of_frame F
  obtain ⟨ν₀, hν₀⟩ := exists_adj α
  have hν₀' : ν₀ ∈ nbrs α := hν₀
  obtain ⟨T, hTα, hTν, -⟩ := hA.exists_common_sylow hν₀'
  refine (Zv_eq_conjClosure hTα).le.trans (conjClosure_le fun h hh z hz => ?_)
  have hz' : z ∈ Zv ν₀ := (hA.omegaOneCenter_le_Zv hTα hTν).2.2 hz
  set g' : ↥(P1 L1 L2 S ⊔ P2 L1 L2 S) := ⟨h, (mem_stab.mp hh).1⟩ with hg'
  have hgα : g' • α = α := smul_eq_of_mem_stab hh
  have hmem : g' • ν₀ ∈ nbrs α := by
    have := (smul_adj g').mpr (show (graph _ _ _).Adj α ν₀ from hν₀')
    rwa [hgα] at this
  have hsub : Zv (g' • ν₀) ≤ ⨆ (ν : Geo (P1 L1 L2 S) (P2 L1 L2 S)) (_ : ν ∈ nbrs α),
      Zv α ⊓ Subgroup.centralizer (Qv ν : Set G) :=
    le_iSup₂_of_le (g' • ν₀) hmem (Zv_eq_inf_centralizer F hT1 hα hmem).le
  refine hsub ?_
  rw [Zv_smul, mem_conjSub]
  have e : (g' : G)⁻¹ * (h * z * h⁻¹) * (g' : G) = z := by
    show h⁻¹ * (h * z * h⁻¹) * h = z
    group
  rw [e]; exact hz'

end Interface

end CFSG.Quasithin.Kleidman.F204
