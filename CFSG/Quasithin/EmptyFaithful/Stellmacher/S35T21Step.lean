module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35T21Red2
public import CFSG.Quasithin.EmptyFaithful.SzF53B3NSec

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open CFSG.Quasithin.F53Mod
open scoped commutatorElement

namespace F53.Stellmacher

open CosetGeom F53

open S35.II

namespace S35.T21

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

theorem step21_of_fixZ (hS : Sit H M S) (hII : CaseII H M) (hfix : FixZ H M) :
    Step21 H M := by
  intro hN β l δ σ hβ hl hδ hσ hδβ hσβ hδσ
  have hl3 : vtype l = true := Std.vtype_nbr_S5 hβ hl
  have hδ5 : vtype δ = false := Std.vtype_nbr_S3 hl3 hδ
  have hβl : β ∈ nbrs l := Std.mem_nbrs_symm.mp hl
  have hlδ : l ∈ nbrs δ := Std.mem_nbrs_symm.mp hδ
  have hlσ : l ∈ nbrs σ := Std.mem_nbrs_symm.mp hσ
  have hW : ∀ ρ ∈ nbrs l, ∀ ρ' ∈ nbrs l, ∀ a ∈ Vn ρ, ∀ b ∈ Vn ρ', a * b = b * a :=
    fun ρ hρ ρ' hρ' a ha b hb => Std.Wl_comm hS l a (Std.Vn_le_Wl hρ ha) b (Std.Vn_le_Wl hρ' hb)
  set Y' : Subgroup G := Vn δ ⊓ (Vn σ ⊔ Vn β) with hY'
  have hX : (Vn δ ⊔ Vn β) ⊓ (Vn σ ⊔ Vn β) = Y' ⊔ Vn β := by
    apply le_antisymm
    · intro x hx
      obtain ⟨d, hd, b, hb, rfl⟩ := exists_mul_of_mem_sup_of_comm (hW δ hδ β hβl) hx.1
      have hdY : d ∈ Y' := ⟨hd, by
        have : d = d * b * b⁻¹ := by group
        rw [this]
        exact Subgroup.mul_mem _ hx.2 (Subgroup.inv_mem _ (Subgroup.mem_sup_right hb))⟩
      exact Subgroup.mul_mem_sup hdY hb
    · exact sup_le (le_inf (inf_le_left.trans le_sup_left) inf_le_right)
        (le_inf le_sup_right le_sup_right)
  have hYn : Y' ≤ Subgroup.normalizer (Vn β : Set G) := fun y hy =>
    mem_normalizer_of_comm fun b hb => hW δ hδ β hβl y hy.1 b hb
  have hYV : Y' ⊓ Vn β = Zv l := by
    apply le_antisymm
    · intro x hx
      rw [← hII β l δ hβ hl hlδ hδβ]
      exact ⟨hx.2, hx.1.1⟩
    · exact le_inf (le_inf (Std.Zv_le_Vn hlδ) ((Std.Zv_le_Vn hlσ).trans le_sup_left))
        (Std.Zv_le_Vn hl)
  have hnorm : stab δ ⊓ stab l ≤ Subgroup.normalizer (Zv l : Set G) :=
    inf_le_right.trans (stab_le_normalizer_Zv hS.glob.amalg l)
  have hmem : ∀ x, x ∈ cSecIn (stab δ ⊓ stab l) (Zv l) Y' ↔
      x ∈ stab δ ⊓ stab l ∧ ∀ y ∈ Y', x * y * x⁻¹ * y⁻¹ ∈ Zv l := fun x =>
    F53B3.N37.mem_cSecIn_iff hnorm
  have h1 : Qv β ⊓ Qv l ≤ cSecIn (stab δ ⊓ stab l) (Zv l) Y' := by
    intro q hq
    rw [hmem]
    exact ⟨⟨Std.Qv_le_stab hS hδ hq.2, pCoreOf_le 2 _ hq.2⟩, fun y hy =>
      comm_mem_Zv_of_mem_Qv_inf hS hII hβ hl hδ hσ hδσ.symm hq hy⟩
  have h2 : Qv δ ≤ cSecIn (stab δ ⊓ stab l) (Zv l) Y' := by
    intro q hq
    rw [hmem]
    refine ⟨⟨pCoreOf_le 2 _ hq, Std.Qv_le_stab hS hlδ hq⟩, fun y hy => ?_⟩
    have hc : q * y * q⁻¹ * y⁻¹ ∈ ⁅Vn δ, Qv δ⁆ := by
      rw [← Subgroup.commutator_comm]
      have := Subgroup.commutator_mem_commutator hq (hy.1 : y ∈ Vn δ)
      rwa [commutatorElement_def] at this
    rw [Std.comm_Vn_Qv hS hδ5] at hc
    exact Std.Zv_le_Zv_of_nbr hS hδ5 hlδ hc
  have hDS : stab δ ⊓ stab l ≤ cSecIn (stab δ ⊓ stab l) (Zv l) Y' :=
    (hN β l δ hβ hl hlδ hδβ).trans (sup_le h1 h2)
  have hVn : Vn δ ≤ Subgroup.normalizer (Zv l : Set G) := fun v hv =>
    mem_normalizer_of_comm fun b hb => hW δ hδ δ hδ v hv b (Std.Zv_le_Vn hlδ hb)
  have hYfix : Y' ≤ fixSecIn (stab δ ⊓ stab l) (Zv l) (Vn δ) := by
    intro y hy
    rw [F53B3.N37.mem_fixSecIn_iff (Std.Zv_le_Vn hlδ) hVn]
    exact ⟨hy.1, fun g hg => ((hmem g).mp (hDS hg)).2 y hy⟩
  rw [hX, ← relIndex_inf_eq_relIndex_sup hYn, hYV]
  calc (Zv l).relIndex Y' ≤ (Zv l).relIndex (fixSecIn (stab δ ⊓ stab l) (Zv l) (Vn δ)) :=
        Subgroup.relIndex_le_of_le_right hYfix Subgroup.FiniteIndex.index_ne_zero
    _ ≤ 2 := hfix δ l hδ5 hlδ

end S35.T21

end F53.Stellmacher

end CFSG.Quasithin
