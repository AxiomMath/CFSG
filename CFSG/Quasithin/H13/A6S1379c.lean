module

public import CFSG.Quasithin.H13.A6S1379b
public import CFSG.Quasithin.H13.A6S1379a

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open scoped commutatorElement Pointwise

theorem R8_cases : ∀ σ ∈ R8, σ ∈ K4L ∨ σ * swap 4 5 ∈ K4L := by decide +kernel

namespace Setting4

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting4 G T L V)
include S

section Abelian

variable (hNS : ¬ LieModel G .PSp 3 2 1) (h13315 : Stmt13_3_15) (h1356two : Input1356Two)
  {H : Subgroup G} (hH : H ∈ S.Hz) (hab : IsElemAbelian 2 (conjClosure S.V3 H))
include hNS h13315 h1356two hH hab

omit hab in
theorem not_comm_VH_H_le_UH (h13314 : Stmt13_3_14) :
    ¬ ∀ h ∈ H, ∀ x ∈ conjClosure V H, h * x * h⁻¹ * x⁻¹ ∈ conjClosure S.V3 H := by
  intro hcon
  have hF := S.hypF91 hNS h13315 h1356two hH
  have hVU : V ≤ Subgroup.normalizer (conjClosure S.V3 H : Set G) :=
    hF.V_le_H.trans (le_normalizer_conjClosure S.V3 H)
  have hVH : conjClosure V H ≤ V ⊔ conjClosure S.V3 H := by
    refine conjClosure_le fun h hh v hv => ?_
    have hc := hcon h hh v (le_conjClosure _ _ hv)
    have e : h * v * h⁻¹ = (h * v * h⁻¹ * v⁻¹) * v := by group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hc) (Subgroup.mem_sup_left hv)
  have hle : conjClosure S.V3 H ≤ S.V3 := by
    rw [← S.comm_VH_QH_eq hNS h13315 h1356two hH h13314, Subgroup.commutator_le]
    intro a ha b hb
    have ha' : a ∈ (V : Set G) * (conjClosure S.V3 H : Set G) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right V _ hVU]
      exact hVH ha
    obtain ⟨v, hv, u, hu, rfl⟩ := Set.mem_mul.mp ha'
    have h1 : u * b * u⁻¹ * b⁻¹ ∈ fsuV1 T V := hF.commutator_conjClosure_le u hu b hb
    have h2 : v * b * v⁻¹ * b⁻¹ ∈ S.V3 := by
      have hc := S.comm_V_QH_mem_V3 hNS h13315 h1356two hH hv hb
      have e : v * b * v⁻¹ * b⁻¹ = (b * v * b⁻¹ * v⁻¹)⁻¹ := by group
      rw [e]
      exact S.V3.inv_mem hc
    have e : ⁅v * u, b⁆ = v * (u * b * u⁻¹ * b⁻¹) * v⁻¹ * (v * b * v⁻¹ * b⁻¹) := by
      rw [commutatorElement_def]; group
    rw [e, S.conj_V1_of_mem hH (hF.V_le_H hv) h1]
    exact S.V3.mul_mem ((S.V1_le_V2.trans S.V2_le_V3) h1) h2
  exact (S.V3_lt_UH h13315 hH).ne' (le_antisymm hle (le_conjClosure _ _))

theorem rho_VH {x : G} (hx : x ∈ conjClosure V H) :
    ∃ hxN : x ∈ Subgroup.normalizer (V : Set G),
      S.frame.ρ ⟨x, hxN⟩ = 1 ∨ S.frame.ρ ⟨x, hxN⟩ = swap 4 5 := by
  let X : Subgroup G := ((Subgroup.zpowers (swap (4 : Fin 6) 5)).comap S.frame.ρ).map
    (Subgroup.normalizer (V : Set G)).subtype
  have hmemX : ∀ y : ↥(Subgroup.normalizer (V : Set G)),
      S.frame.ρ y = 1 ∨ S.frame.ρ y = swap 4 5 → (y : G) ∈ X := by
    intro y hy
    refine Subgroup.mem_map_of_mem _ ?_
    rw [Subgroup.mem_comap]
    rcases hy with h | h
    · rw [h]; exact Subgroup.one_mem _
    · rw [h]; exact Subgroup.mem_zpowers _
  have hX : conjClosure V H ≤ X := by
    refine conjClosure_le fun h hh v hv => ?_
    obtain ⟨hwN, hρ⟩ := S.rho_conjSub_V hNS h13315 h1356two hH hab hh (mul_mem_conjSub hv)
    exact hmemX ⟨_, hwN⟩ hρ
  obtain ⟨y, hy, rfl⟩ := hX hx
  refine ⟨y.2, ?_⟩
  have hy' : S.frame.ρ y ∈ Subgroup.zpowers (swap (4 : Fin 6) 5) := hy
  show S.frame.ρ y = 1 ∨ S.frame.ρ y = swap 4 5
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hy'
  rcases Int.even_or_odd k with ⟨m, rfl⟩ | ⟨m, rfl⟩
  · left
    rw [← hk, ← two_mul, zpow_mul, show swap (4 : Fin 6) 5 ^ (2 : ℤ) = 1 by decide, one_zpow]
  · right
    rw [← hk, zpow_add, zpow_mul, show swap (4 : Fin 6) 5 ^ (2 : ℤ) = 1 by decide, one_zpow,
      one_mul, zpow_one]

theorem R8_le_rho_QH (h13314 : Stmt13_3_14)
    (hna : ¬ IsElemAbelian 2 (conjClosure V H)) :
    ∀ σ ∈ R8, ∃ q ∈ pCoreOf 2 H, ∃ hqN : q ∈ Subgroup.normalizer (V : Set G),
      S.frame.ρ ⟨q, hqN⟩ = σ := by
  have hF := S.hypF91 hNS h13315 h1356two hH
  obtain ⟨h, hh, w, hw, hwN, hρw⟩ := S.exists_conjSub_rho_45 hNS h13315 h1356two hH hab hna
  have hwQ : w ∈ pCoreOf 2 H :=
    hF.conjSub_le_pCoreOf (S.V_le_QH hNS h13315 h1356two hH hab) hh hw
  intro σ hσ
  rcases R8_cases σ hσ with hK | hK
  · exact S.K4_le_rho_QH hNS h13315 h1356two hH h13314 σ hK
  · obtain ⟨q, hq, hqN, hρq⟩ := S.K4_le_rho_QH hNS h13315 h1356two hH h13314 _ hK
    refine ⟨q * w, (pCoreOf 2 H).mul_mem hq hwQ, Subgroup.mul_mem _ hqN hwN, ?_⟩
    have e : (⟨q * w, Subgroup.mul_mem _ hqN hwN⟩ : ↥(Subgroup.normalizer (V : Set G))) =
        ⟨q, hqN⟩ * ⟨w, hwN⟩ := rfl
    rw [e, map_mul, hρq, hρw, mul_assoc, show swap (4 : Fin 6) 5 * swap 4 5 = 1 by decide,
      mul_one]

end Abelian

end Setting4

end CFSG.Quasithin.H13.A6
