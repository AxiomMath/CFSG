module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35FnCfg

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open CFSG.Quasithin.F53Mod
open scoped commutatorElement

namespace F53.Stellmacher

open CosetGeom F53

namespace S35.Fn

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

@[expose] def commSub (W R : Subgroup G) (hW : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x) (hR : R ≤ W)
    (z : G) : Subgroup G where
  carrier := {w | w ∈ W ∧ ⁅z, w⁆ ∈ R}
  one_mem' := ⟨W.one_mem, by simp⟩
  mul_mem' := by
    rintro a b ⟨ha, haR⟩ ⟨hb, hbR⟩
    refine ⟨W.mul_mem ha hb, ?_⟩
    have h1 : ⁅z, a * b⁆ = ⁅z, a⁆ * (a * ⁅z, b⁆ * a⁻¹) := by
      simp only [commutatorElement_def]; group
    have h2 : a * ⁅z, b⁆ * a⁻¹ = ⁅z, b⁆ := by
      rw [hW a ha _ (hR hbR)]; group
    rw [h1, h2]
    exact R.mul_mem haR hbR
  inv_mem' := by
    rintro a ⟨ha, haR⟩
    refine ⟨W.inv_mem ha, ?_⟩
    have h1 : ⁅z, a⁻¹⁆ = a⁻¹ * ⁅z, a⁆⁻¹ * a := by
      simp only [commutatorElement_def]; group
    have h2 : a⁻¹ * ⁅z, a⁆⁻¹ * a = ⁅z, a⁆⁻¹ := by
      have := hW a ha _ (hR (R.inv_mem haR))
      rw [mul_assoc, ← this]; group
    rw [h1, h2]
    exact R.inv_mem haR

variable {β α' m γ' : Geo H M}

theorem comm_Zα'_Wl (hS : Sit H M S) (h15c : Claim15c H M)
    (hI2 : ∀ β l δ δ' : Geo H M, vtype β = false → l ∈ nbrs β → l ∈ nbrs δ → l ∈ nbrs δ' →
      δ ≠ β → δ' ≠ β → Vn β ⊓ Vn δ = Vn β ⊓ Vn δ')
    (hL : Lam β α') (hB : Back H M β α' m γ') {l : Geo H M} (hl : l ∈ nbrs β) {δ : Geo H M}
    (hδ : δ ∈ nbrs l) (hδβ : δ ≠ β) {z : G} (hz : z ∈ Zv α') {w : G} (hw : w ∈ Wl l) :
    ⁅z, w⁆ ∈ Vn β ⊓ Vn δ := by
  have hβ := hL.1.vδ
  have hβl : β ∈ nbrs l := Std.mem_nbrs_symm.mp hl
  have hR : Vn β ⊓ Vn δ ≤ Wl l := inf_le_left.trans (Std.Vn_le_Wl hβl)
  have hzK : z ∈ Kb β := Zm_le_Kb hS hL hB (Zα'_le_Zm hS hL hB hz)
  have hle : Wl l ≤ commSub (Wl l) (Vn β ⊓ Vn δ) (Std.Wl_comm hS l) hR z := by
    refine Std.Wl_le fun ρ hρ => ?_
    intro v hv
    refine ⟨Std.Vn_le_Wl hρ hv, ?_⟩
    by_cases hρβ : ρ = β
    · rw [hρβ] at hv
      have h1 : ⁅z, v⁆ = 1 :=
        commutatorElement_eq_one_iff_mul_comm.mpr (Subgroup.mem_centralizer_iff.mp hzK.2 v hv).symm
      rw [h1]
      exact (Vn β ⊓ Vn δ).one_mem
    · have hd2 : dist ρ β = 2 := Std.dist_eq_two_iff.mpr ⟨l, hl, hρ, hρβ⟩
      have hzρ : z ∈ stab ρ := by
        refine Zα'_le_stab_of_dist hS hL ?_ hz
        rw [CosetGeom.dist_comm]; omega
      have h1 : ⁅z, v⁆ ∈ Vn ρ := by
        have h3 := Subgroup.mem_normalizer_iff.mp ((Std.Vn_normal ρ) hzρ) v
        rw [commutatorElement_def]
        exact (Vn ρ).mul_mem (h3.mp hv) ((Vn ρ).inv_mem hv)
      have h2 : ⁅z, v⁆ ∈ Vn β := by
        have hvW : v ∈ Wb β := Std.Vn_le_Wb hd2 hv
        have := h15c β hβ (Subgroup.commutator_mem_commutator hvW hzK)
        rw [← commutatorElement_inv]
        exact inv_mem this
      have h3 : ⁅z, v⁆ ∈ Vn β ⊓ Vn ρ := ⟨h2, h1⟩
      rw [hI2 β l δ ρ hβ hl (Std.mem_nbrs_symm.mp hδ)
        (Std.mem_nbrs_symm.mp hρ) hδβ hρβ]
      exact h3
  exact (hle hw).2

end S35.Fn

end F53.Stellmacher

end CFSG.Quasithin
