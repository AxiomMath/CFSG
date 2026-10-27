module

public import CFSG.Quasithin.Recognition.Kleidman.F204.CaseIIPropBA
public import CFSG.Quasithin.Recognition.Kleidman.F204.CaseIIQuad
public import CFSG.Quasithin.Recognition.Kleidman.F204.CaseIIPropB2
public import CFSG.Quasithin.Recognition.Kleidman.F204.CaseIIPropB3

public section

namespace CFSG.Quasithin.Kleidman.F204

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.S152X
open CFSG.Quasithin.F7 CFSG.Quasithin.FA5
open CFSG.Quasithin.F53
open CFSG.Quasithin.CosetGeom

open scoped commutatorElement

set_option linter.unusedSectionVars false

variable {G : Type} [Group G] [Finite G] {L1 L2 S D X : Subgroup G}

omit [Finite G] in
theorem mem_normalizer_of_conj_mem' {K : Subgroup G} {g : G}
    (h1 : ∀ y ∈ K, g * y * g⁻¹ ∈ K) (h2 : ∀ y ∈ K, g⁻¹ * y * g⁻¹⁻¹ ∈ K) :
    g ∈ Subgroup.normalizer (K : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  exact ⟨fun hy => h1 y hy, fun hy => by
    have := h2 _ hy
    have e : g⁻¹ * (g * y * g⁻¹) * g⁻¹⁻¹ = y := by group
    rwa [e] at this⟩

section PropB

variable (F : Frame L1 L2 S D X) (hT1 : ConfigT1 L1 L2 S)
  {α β α' : Geo (P1 L1 L2 S) (P2 L1 L2 S)} (hc : IsCritData α β α') (hII : Zv α' ≤ Qv α)
include F hT1 hc hII

theorem propB_false {ρ : G} (hρα' : ρ ∈ stab α') (hρβ : ρ ∈ stab β) (hρ3 : ρ ^ 3 = 1)
    (hρ1 : ρ ≠ 1) : False := by
  classical
  have hA := Amal.of_frame F
  obtain ⟨hα, hβf, hα'f, -, hb3⟩ := t1II_setup F hT1 hc hII
  have hβ : β ∈ nbrs α := hc.adj
  have hαβ : α ∈ nbrs β := mem_nbrs_symm hβ
  have hρα : ρ ∈ stab α := three_mem_stab_nbr F hβf hαβ hρβ hρ3
  obtain ⟨u, hu, huvt, hquadu⟩ := propB_quad F hT1 hc hII hρα' hρβ hρ3 hρ1
  have hquad : QuadAt α β :=
    QuadAt.transport huvt (mem_nbrs_symm hu) hα hβ (fun z hz t ht => hquadu z hz t ht)
  have hbβ : bMin (P1 L1 L2 S) (P2 L1 L2 S) < bAt β := by
    refine lt_of_le_of_ne (bMin_le_bAt β) fun h => ?_
    exact hA.not_ZCentral_of_bAt h.symm ((hT1 β).mpr hβf)
  have hZβ : Zv β ≤ Qv α' := Zv_le_Qv_of_dist_lt (by have := hc.dist_eq'; omega)
  have hZαβ : Zv α ⊓ Subgroup.centralizer (Qv β : Set G) = Zv β :=
    (Zv_eq_inf_centralizer F hT1 hα hβ).symm
  have hZα' : Zv α ≤ stab α' := hA.Zv_le_stab_of_dist_le (by rw [hc.dist_eq, hc.bAt_eq])
  have hW2 : (Zv α ⊓ Qv α').relIndex (Zv α) = 2 := by
    have h1 := relIndex_inf_Qv_le_two F hα'f hZα' (hA.isElemAbelian_Zv α)
    have h2 : (Zv α ⊓ Qv α').relIndex (Zv α) ≠ 1 := by
      intro h
      rw [Subgroup.relIndex_eq_one] at h
      exact hc.not_le fun z hz => (h hz).2
    have h3 : (Zv α ⊓ Qv α').relIndex (Zv α) ≠ 0 := Subgroup.index_ne_zero_of_finite
    omega
  have hCW : Zv α ⊓ Subgroup.centralizer (Qv β : Set G) ≤ Zv α ⊓ Qv α' := by
    rw [hZαβ]
    exact le_inf ((Zv_eq_inf_centralizer F hT1 hα hβ).le.trans inf_le_left) hZβ
  have hZn : ∀ g ∈ stab α, ∀ y ∈ Zv α, g * y * g⁻¹ ∈ Zv α := fun g hg y hy =>
    (Subgroup.mem_normalizer_iff.mp (hA.stab_le_normalizer_Zv α hg) y).mp hy
  have hQn : ∀ g ∈ stab α', ∀ y ∈ Qv α', g * y * g⁻¹ ∈ Qv α' := fun g hg y hy =>
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 (stab α') hg) y).mp hy
  have hWρ : ρ ∈ Subgroup.normalizer ((Zv α ⊓ Qv α' : Subgroup G) : Set G) := by
    refine mem_normalizer_of_conj_mem' (fun y hy => ⟨hZn ρ hρα y hy.1, hQn ρ hρα' y hy.2⟩)
      (fun y hy => ⟨?_, ?_⟩)
    · exact hZn ρ⁻¹ ((stab α).inv_mem hρα) y hy.1
    · exact hQn ρ⁻¹ ((stab α').inv_mem hρα') y hy.2
  have hWQα : Qv α ≤ Subgroup.normalizer ((Zv α ⊓ Qv α' : Subgroup G) : Set G) := by
    intro q hq
    have hqc : ∀ y ∈ Zv α, q * y * q⁻¹ = y := by
      intro y hy
      have := Subgroup.mem_centralizer_iff.mp (hA.Zv_le_centerOf_Qv α hy).2 q hq
      calc q * y * q⁻¹ = (q * y) * q⁻¹ := rfl
        _ = (y * q) * q⁻¹ := by rw [this]
        _ = y := by group
    refine mem_normalizer_of_conj_mem' (fun y hy => ?_) (fun y hy => ?_)
    · rw [hqc y hy.1]; exact hy
    · have := hqc y hy.1
      have e : q⁻¹ * y * q⁻¹⁻¹ = y := by
        have h2 := Subgroup.mem_centralizer_iff.mp (hA.Zv_le_centerOf_Qv α hy.1).2 q⁻¹ ((Qv α).inv_mem hq)
        calc q⁻¹ * y * q⁻¹⁻¹ = (q⁻¹ * y) * q := by group
          _ = (y * q⁻¹) * q := by rw [h2]
          _ = y := by group
      rw [e]; exact hy
  have hWQβ' : ∀ t ∈ Qv β, ∀ y ∈ Zv α ⊓ Qv α', t * y * t⁻¹ ∈ Zv α ⊓ Qv α' := by
    intro t ht y hy
    have htα : t ∈ stab α := hA.Qv_le_stab_of_mem_nbrs hαβ ht
    have hc1 := hquad y hy.1 t ht
    have hcZ : y * t * y⁻¹ * t⁻¹ ∈ Zv α := by
      have e : y * t * y⁻¹ * t⁻¹ = y * (t * y⁻¹ * t⁻¹) := by group
      rw [e]
      exact (Zv α).mul_mem hy.1 (hZn t htα y⁻¹ ((Zv α).inv_mem hy.1))
    have hcβ : y * t * y⁻¹ * t⁻¹ ∈ Zv α ⊓ Qv α' := hCW ⟨hcZ, hc1⟩
    have e : t * y * t⁻¹ = (y * t * y⁻¹ * t⁻¹)⁻¹ * y := by group
    rw [e]
    exact (Zv α ⊓ Qv α').mul_mem ((Zv α ⊓ Qv α').inv_mem hcβ) hy
  have hWQβ : Qv β ≤ Subgroup.normalizer ((Zv α ⊓ Qv α' : Subgroup G) : Set G) := by
    intro t ht
    exact mem_normalizer_of_conj_mem' (fun y hy => hWQβ' t ht y hy)
      (fun y hy => hWQβ' t⁻¹ ((Qv β).inv_mem ht) y hy)
  have hWn : stab α ⊓ stab β ≤ Subgroup.normalizer ((Zv α ⊓ Qv α' : Subgroup G) : Set G) :=
    edge_gen F hα hβ hρα hρβ hρ3 hρ1 hWQα hWQβ hWρ
  exact hA.false_of_quadratic_hyperplane hβ (V := Zv α) (W := Zv α ⊓ Qv α')
    (hA.stab_le_normalizer_Zv α) hW2 hWn hCW
    (fun ν hν => hA.Qv_le_stab_of_mem_nbrs (mem_nbrs_symm hν))
    (fun ν hν μ hμ μ' hμ' hμν hμ'ν => exists_Qv_smul_nbr F hα hν hμ hμ' hμν hμ'ν)
    (vertex_hfree F hα hβ) (vertex_hsq F hα hβ) (vertex_hgen F hT1 hα)
    (fun v hv t ht => hquad v hv t ht)

end PropB

end CFSG.Quasithin.Kleidman.F204
