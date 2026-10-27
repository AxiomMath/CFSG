module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35B5Gen2
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35B5Gen1

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open CFSG.Quasithin.F53Mod
open scoped commutatorElement

namespace F53.Stellmacher

open CosetGeom F53 Equiv

namespace S35.B5

open S35.Std S35.Fin

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

theorem exists_gen (hC : Ch.Ctx H M S) {β l0 γ : Geo H M} (hβ : vtype β = false)
    (h0 : l0 ∈ nbrs β) (hγ : γ ∈ nbrs l0) (hγβ : γ ≠ β)
    (hW : ¬ Wb γ ≤ Lr β ⊔ Qv β) :
    ∃ l ∈ nbrs β, ∃ δ ∈ nbrs l, δ ≠ β ∧ stab β ≤ Wb δ ⊔ Wb γ ⊔ Qv β := by
  have hS : Sit H M S := hC.sit
  obtain ⟨c⟩ := hC.nonempty_chart hβ
  obtain ⟨g, hg⟩ := exists_gen_perm (c.card_Dl hS h0) (bar_Wb_le_Dl hS c h0 hγ)
    (bar_Wb_normal hS hβ c h0 hγ) (not_bar_Wb_le_alt hS hβ c h0 hγ hW)
  obtain ⟨g0, rfl⟩ := c.surj g
  have hg0 : (g0 : G) ∈ H ⊔ M := stab_le β g0.2
  let g1 : ↥(H ⊔ M) := ⟨g0, hg0⟩
  have hg1 : (g1 : G) ∈ stab β := g0.2
  have hfix : g1 • β = β := smul_eq_of_mem_stab hg1
  have hl : g1 • l0 ∈ nbrs β := smul_mem_nbrs_of_stab hg1 h0
  have hδl : g1 • γ ∈ nbrs (g1 • l0) := (smul_mem_nbrs_iff' g1).mpr hγ
  refine ⟨g1 • l0, hl, g1 • γ, hδl, ?_, ?_⟩
  · intro h
    rw [← hfix] at h
    exact hγβ (MulAction.injective g1 h)
  · have hWs : Wb (g1 • γ) = conjSub (g1 : G) (Wb γ) := Wb_smul g1 γ
    have hWδ : Wb (g1 • γ) ≤ stab β :=
      (Wb_le_Ql hS (mem_nbrs_symm.mp hδl)).trans (Qv_le_stab hS (mem_nbrs_symm.mp hl))
    have hbar : c.bar (Wb (g1 • γ)) = cj (c.θ g0) (c.bar (Wb γ)) := by
      rw [hWs]
      exact c.bar_conjSub hg1 (Wb_le_stab hS h0 hγ)
    set A : Subgroup G := Wb (g1 • γ) ⊔ Wb γ ⊔ Qv β with hA
    have hAs : A ≤ stab β :=
      sup_le (sup_le hWδ (Wb_le_stab hS h0 hγ)) (Ch.Qv_le_stab' β)
    have hQA : Qv β ≤ A := le_sup_right
    have htop : c.bar A = ⊤ := by
      rw [eq_top_iff, ← hg, sup_comm, ← hbar]
      exact sup_le (c.bar_mono (le_sup_left.trans le_sup_left))
        (c.bar_mono (le_sup_right.trans le_sup_left))
    intro y hy
    have h1 : y ∈ c.preθ (c.bar A) :=
      (c.mem_preθ_iff ⟨y, hy⟩).mpr (by rw [htop]; exact Subgroup.mem_top _)
    rwa [c.preθ_bar hS hβ hAs hQA] at h1

end S35.B5

end F53.Stellmacher

end CFSG.Quasithin
