module

public import CFSG.Quasithin.Recognition.Kleidman.F204.CaseIIT1Ge7F
import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.Quasithin.Recognition.Kleidman.F204.CaseIIT1Ge7E

public section

namespace CFSG.Quasithin.Kleidman.F204

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.S152X
open CFSG.Quasithin.F7 CFSG.Quasithin.FA5
open CFSG.Quasithin.F53
open CFSG.Quasithin.CosetGeom

set_option linter.unusedSectionVars false

variable {G : Type} [Group G] [Finite G] {L1 L2 S D X : Subgroup G}

omit [Finite G] in
private theorem isElemAbelian_of_le' {E F : Subgroup G} (hEF : E ≤ F) (hF : IsElemAbelian 2 F) :
    IsElemAbelian 2 E := CFSG.Open.IsElemAbelian.mono hF hEF

private theorem vtype_of_mem_nbrs'' {H M : Subgroup G} {u v : Geo H M} (h : v ∈ nbrs u) :
    vtype v = !vtype u := by
  have := vtype_ne_of_adj (show (graph _ _ _).Adj u v from h)
  cases h1 : vtype u <;> cases h2 : vtype v <;> simp_all

section CaseII

variable (F : Frame L1 L2 S D X) (hT1 : ConfigT1 L1 L2 S)
  {α β α' : Geo (P1 L1 L2 S) (P2 L1 L2 S)} (hc : IsCritData α β α') (hII : Zv α' ≤ Qv α)
  (hb7 : 7 ≤ bMin (P1 L1 L2 S) (P2 L1 L2 S))
  (hF1 : ∀ x : Geo (P1 L1 L2 S) (P2 L1 L2 S), vtype x = true → ∀ d ∈ nbrs x, ∀ d' ∈ nbrs x,
    d ≠ d' → Zv d ⊓ Zv d' = ⊥)
include F hT1 hc hII hb7 hF1

theorem exists_small_comm {μ : Geo (P1 L1 L2 S) (P2 L1 L2 S)} (hμ : μ ∈ nbrs α')
    (hμβ : ¬ Zv μ ≤ Qv β) :
    ∃ t ∈ stab β, t ∉ Qv β ∧ t ^ 2 = 1 ∧ ∃ Y : Subgroup G, Y ≤ Vball 3 β ∧
      Y.relIndex (Vball 3 β) ≤ 2 ∧ ∀ y ∈ Y, t * y * t⁻¹ * y⁻¹ ∈ Vn β := by
  have hA := Amal.of_frame F
  have hgen := hA.amalgam.gen
  obtain ⟨hα, hβ, hα', -, hb3⟩ := t1II_setup F hT1 hc hII
  obtain ⟨hVβ, hWβ⟩ := t1II_Vn_le_stab F hT1 hc hII
  have hdβα' := hc.dist_eq'
  obtain ⟨γ, hγ, hdγ⟩ := exists_adj_dist_eq hgen (α := β) (δ := α')
    (d := bMin (P1 L1 L2 S) (P2 L1 L2 S) - 2) (by omega)
  obtain ⟨ε, hε, hdε⟩ := exists_adj_dist_eq hgen (α := β) (δ := γ)
    (d := bMin (P1 L1 L2 S) (P2 L1 L2 S) - 3) (by omega)
  obtain ⟨ε3, hε3, hdε3⟩ := exists_adj_dist_eq hgen (α := β) (δ := ε)
    (d := bMin (P1 L1 L2 S) (P2 L1 L2 S) - 4) (by omega)
  have hγn : γ ∈ nbrs α' := hγ
  have hεn : ε ∈ nbrs γ := hε
  have hε3n : ε3 ∈ nbrs ε := hε3
  have hγt : vtype γ = true := by rw [vtype_of_mem_nbrs'' hγn, hα']; rfl
  have hεf : vtype ε = false := by rw [vtype_of_mem_nbrs'' hεn, hγt]; rfl
  have hU2 := hA.isElemAbelian_Vball (n := 3) (by omega) β
  have hUε3 : Vball 3 β ≤ Qv ε3 := hA.Vball_le_Qv (by omega)
  have hUε : Vball 3 β ≤ stab ε := hUε3.trans (hA.Qv_le_stab_of_mem_nbrs (mem_nbrs_symm hε3n))
  set Y : Subgroup G := Vball 3 β ⊓ Qv ε with hYdef
  have hYidx : Y.relIndex (Vball 3 β) ≤ 2 := relIndex_inf_Qv_le_two F hεf hUε hU2
  have hYγ : Y ≤ Qv γ := Vball_inf_Qv_le F hT1 hc hII hb7 hF1 hγn hεn (by omega)
  have hYα' : Y ≤ stab α' := hYγ.trans (hA.Qv_le_stab_of_mem_nbrs (mem_nbrs_symm hγn))
  have hVU : Vn β ≤ Vball 3 β := (Vn_le_Vball_one β).trans (Vball_mono (by norm_num) β)
  have hVY : Vn β ≤ Y := le_inf hVU ((Vn_le_Vball_one β).trans (hA.Vball_le_Qv (by omega)))
  have hY2 : IsElemAbelian 2 Y := isElemAbelian_of_le' inf_le_left hU2
  have hYQ := relIndex_inf_Qv_le_two F hα' hYα' hY2
  obtain ⟨z0, hz0, hz0Q⟩ := t1II_exists_z F hT1 hc hII
  have hz0V : z0 ∈ Vn β := hA.Zv_le_Vn (mem_nbrs_symm (show β ∈ nbrs α from hc.adj)) hz0
  obtain ⟨t, ht, htQ⟩ : ∃ t ∈ Zv μ, t ∉ Qv β := by
    by_contra h; push Not at h; exact hμβ fun t ht => h t ht
  have htβ : t ∈ stab β := hWβ (hA.Zv_le_Vn hμ ht)
  have ht2 : t ^ 2 = 1 := (hA.isElemAbelian_Zv μ).2 t ht
  have htNV : t ∈ Subgroup.normalizer (Vn β : Set G) := stab_le_normalizer_Vn β htβ
  have htc : ∀ m ∈ Qv μ, t * m = m * t := fun m hm =>
    (Subgroup.mem_centralizer_iff.mp (hA.Zv_le_centerOf_Qv μ ht).2 m hm).symm
  obtain ⟨k₀, hk₀, hk₀Q⟩ := exists_k0 F hT1 hc hII hμ hμβ
  obtain ⟨hk₀V, hk₀α'⟩ := Subgroup.mem_inf.mp hk₀
  have htk : ∀ v ∈ Vn β, t * v * t⁻¹ * v⁻¹ ∈ Vn β := fun v hv =>
    (Vn β).mul_mem ((Subgroup.mem_normalizer_iff.mp htNV v).mp hv) ((Vn β).inv_mem hv)
  have hQpart : ∀ y ∈ Y ⊓ Qv α', t * y * t⁻¹ * y⁻¹ ∈ Vn β := by
    by_cases h3 : ∃ y₁ ∈ Y ⊓ Qv α', y₁ ∉ Qv μ ∧ k₀⁻¹ * y₁ ∉ Qv μ
    · obtain ⟨y₁, hy₁, hy₁Q, hy₁k⟩ := h3
      have hy₁' : y₁ ∈ Vball 3 β ⊓ Qv α' := ⟨(Subgroup.mem_inf.mp hy₁).1.1, (Subgroup.mem_inf.mp hy₁).2⟩
      have hk₀' : k₀ ∈ Vball 3 β ⊓ Qv α' := ⟨hVU hk₀V, hk₀α'⟩
      have hab : y₁⁻¹ * k₀ ∉ Qv μ := by
        intro h; apply hy₁k
        have := (Qv μ).inv_mem h
        rwa [mul_inv_rev, inv_inv] at this
      have hfull : ∀ y ∈ Vball 3 β ⊓ Qv α', ∀ z ∈ Zv μ, y * z * y⁻¹ * z⁻¹ ∈ Zv α' :=
        fun y hy z hz => comm_mem_Zv_of_full F hT1 hc hII hb7 hμ hy₁' hk₀' hy₁Q hk₀Q hab hy hz
      have hZV := Zv_le_Vn_of_full F hT1 hc hII hb7 hF1 hμ hk₀ hk₀Q hfull
      intro y hy
      have hy' : y ∈ Vball 3 β ⊓ Qv α' := ⟨(Subgroup.mem_inf.mp hy).1.1, (Subgroup.mem_inf.mp hy).2⟩
      have := hZV ((Zv α').inv_mem (hfull y hy' t ht))
      rwa [show (y * t * y⁻¹ * t⁻¹)⁻¹ = t * y * t⁻¹ * y⁻¹ by group] at this
    · push Not at h3
      intro y hy
      by_cases hyμ : y ∈ Qv μ
      · rw [show t * y * t⁻¹ * y⁻¹ = (t * y) * t⁻¹ * y⁻¹ by group, htc y hyμ]
        rw [show y * t * t⁻¹ * y⁻¹ = 1 by group]
        exact (Vn β).one_mem
      · have hm := h3 y hy hyμ
        have e : t * y * t⁻¹ * y⁻¹ = t * k₀ * t⁻¹ * k₀⁻¹ := by
          have hc' := htc _ hm
          have hm' : (k₀⁻¹ * y) * t⁻¹ * (k₀⁻¹ * y)⁻¹ = t⁻¹ := by
            calc (k₀⁻¹ * y) * t⁻¹ * (k₀⁻¹ * y)⁻¹
                = t⁻¹ * (t * (k₀⁻¹ * y)) * t⁻¹ * (k₀⁻¹ * y)⁻¹ := by group
              _ = t⁻¹ * ((k₀⁻¹ * y) * t) * t⁻¹ * (k₀⁻¹ * y)⁻¹ := by rw [hc']
              _ = t⁻¹ := by group
          calc t * y * t⁻¹ * y⁻¹ = t * k₀ * ((k₀⁻¹ * y) * t⁻¹ * (k₀⁻¹ * y)⁻¹) * k₀⁻¹ := by group
            _ = t * k₀ * t⁻¹ * k₀⁻¹ := by rw [hm']
        rw [e]; exact htk k₀ hk₀V
  refine ⟨t, htβ, htQ, ht2, Y, inf_le_left, hYidx, fun y hy => ?_⟩
  by_cases hyα' : y ∈ Qv α'
  · exact hQpart y (Subgroup.mem_inf.mpr ⟨hy, hyα'⟩)
  · have hz0Y : z0 ∈ Y := hVY hz0V
    have hm := inv_mul_mem_of_relIndex_le_two hYQ hz0Y hy hz0Q hyα'
    have hy' : z0⁻¹ * y ∈ Y ⊓ Qv α' :=
      Subgroup.mem_inf.mpr ⟨Y.mul_mem (Y.inv_mem hz0Y) hy, hm⟩
    have h1 := hQpart _ hy'
    have h2 : t * z0 * t⁻¹ ∈ Vn β := (Subgroup.mem_normalizer_iff.mp htNV z0).mp hz0V
    have e : t * y * t⁻¹ * y⁻¹ =
        (t * z0 * t⁻¹) * (t * (z0⁻¹ * y) * t⁻¹ * (z0⁻¹ * y)⁻¹) * z0⁻¹ := by group
    rw [e]
    exact (Vn β).mul_mem ((Vn β).mul_mem h2 h1) ((Vn β).inv_mem hz0V)

end CaseII

end CFSG.Quasithin.Kleidman.F204
