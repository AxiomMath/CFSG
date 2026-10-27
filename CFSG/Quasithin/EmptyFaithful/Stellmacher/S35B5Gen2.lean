module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35ChSyl
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S43BaseModD
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35Std3

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

omit [Finite G] in
theorem Wb_smul (g : ↥(H ⊔ M)) (β : Geo H M) : Wb (g • β) = conjSub (g : G) (Wb β) := by
  unfold Wb
  apply le_antisymm
  · refine iSup₂_le fun ρ hρ => ?_
    obtain ⟨ρ', rfl⟩ : ∃ ρ', ρ = g • ρ' := ⟨g⁻¹ • ρ, by simp⟩
    have hρ' : dist ρ' β = 2 := by rwa [CosetGeom.dist_smul] at hρ
    rw [Vn_smul]
    exact conjSub_mono _ (le_iSup₂_of_le (f := fun (ρ : Geo H M) (_ : dist ρ β = 2) => Vn ρ)
      ρ' hρ' le_rfl)
  · rw [conjSub_le_iff]
    refine iSup₂_le fun ρ hρ => ?_
    rw [← conjSub_le_iff, ← Vn_smul]
    exact le_iSup₂_of_le (f := fun (ρ : Geo H M) (_ : dist ρ (g • β) = 2) => Vn ρ) (g • ρ)
      (by rwa [CosetGeom.dist_smul]) le_rfl

variable {β l0 γ : Geo H M}

theorem Wb_le_stab (hS : Sit H M S) (h0 : l0 ∈ nbrs β) (hγ : γ ∈ nbrs l0) : Wb γ ≤ stab β :=
  (Wb_le_Ql hS (mem_nbrs_symm.mp hγ)).trans (Qv_le_stab hS (mem_nbrs_symm.mp h0))

theorem bar_Wb_le_Dl (hS : Sit H M S) (c : Ch.Chart β) (h0 : l0 ∈ nbrs β) (hγ : γ ∈ nbrs l0) :
    c.bar (Wb γ) ≤ c.Dl l0 :=
  c.bar_mono (le_inf (Wb_le_stab hS h0 hγ)
    ((Wb_le_Ql hS (mem_nbrs_symm.mp hγ)).trans (Ch.Qv_le_stab' l0)))

theorem bar_Wb_normal (hS : Sit H M S) (hβ : vtype β = false) (c : Ch.Chart β)
    (h0 : l0 ∈ nbrs β) (hγ : γ ∈ nbrs l0) :
    ∀ d ∈ c.Dl l0, ∀ x ∈ c.bar (Wb γ), d * x * d⁻¹ ∈ c.bar (Wb γ) := by
  intro d hd x hx
  obtain ⟨a, ha, rfl⟩ := (c.mem_bar_iff).mp hd
  obtain ⟨w, hw, rfl⟩ := (c.mem_bar_iff).mp hx
  rw [stab_inf_eq hS hβ h0] at ha
  have hle : Qv β ⊔ Qv l0 ≤ c.preθ (c.bar (Qv l0)) := by
    refine sup_le (c.Qv_le_preθ hS hβ _) fun y hy => ?_
    have hys : y ∈ stab β := Qv_le_stab hS (mem_nbrs_symm.mp h0) hy
    exact (c.mem_preθ_iff ⟨y, hys⟩).mpr (c.mem_bar_of_mem hy hys)
  obtain ⟨q2s, hq2, hθa⟩ := (c.mem_bar_iff).mp ((c.mem_preθ_iff a).mp (hle ha))
  have hq2s : (q2s : G) ∈ stab β := q2s.2
  have hq2γ : (q2s : G) ∈ stab γ := Qv_le_stab hS hγ hq2
  set q2 : G := (q2s : G)
  have hθa' : c.θ a = c.θ ⟨q2, hq2s⟩ := hθa.symm
  rw [hθa']
  have hmem : q2 * (w : G) * q2⁻¹ ∈ Wb γ :=
    S43.conj_mem_of_normalizes (Wb_normal γ) hq2γ hw
  have hmems : q2 * (w : G) * q2⁻¹ ∈ stab β :=
    (stab β).mul_mem ((stab β).mul_mem hq2s w.2) ((stab β).inv_mem hq2s)
  have := c.mem_bar_of_mem hmem hmems
  convert this using 1
  rw [← map_inv, ← map_mul, ← map_mul]
  rfl

theorem not_bar_Wb_le_alt (hS : Sit H M S) (hβ : vtype β = false) (c : Ch.Chart β)
    (h0 : l0 ∈ nbrs β) (hγ : γ ∈ nbrs l0) (hW : ¬ Wb γ ≤ Lr β ⊔ Qv β) :
    ¬ c.bar (Wb γ) ≤ alternatingGroup (Fin 5) := by
  intro hX
  apply hW
  intro w hw
  have hws : w ∈ stab β := Wb_le_stab hS h0 hγ hw
  have h1 : c.θ ⟨w, hws⟩ ∈ alternatingGroup (Fin 5) := hX (c.mem_bar_of_mem hw hws)
  rw [← S43.map_oTwoRes_eq_alt c.surj] at h1
  obtain ⟨x, hx, hxw⟩ := h1
  have hxs : (x : G) ∈ Lr β := hx
  have hk : c.θ (⟨w, hws⟩ * x⁻¹) = 1 := by rw [map_mul, map_inv, ← hxw, mul_inv_cancel]
  have hq : w * (x : G)⁻¹ ∈ Qv β := (c.ker_iff hS hβ _).mp hk
  have : w = (w * (x : G)⁻¹) * (x : G) := by group
  rw [this]
  exact (Lr β ⊔ Qv β).mul_mem (Subgroup.mem_sup_right hq) (Subgroup.mem_sup_left hxs)

end S35.B5

end F53.Stellmacher

end CFSG.Quasithin
