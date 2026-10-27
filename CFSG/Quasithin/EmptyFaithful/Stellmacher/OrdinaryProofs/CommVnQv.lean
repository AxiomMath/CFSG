module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.CriticalDistanceGeometry.Index
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.OrdinaryProofs.ZvEdgeCentralizer
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.ModToolBase

public section

namespace CFSG.Quasithin.EmptyFaithful.Stellmacher.OrdinaryProofs

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.F53 CFSG.Quasithin.CosetGeom CFSG.LieType.BorelTits
  CFSG.Quasithin.F53Mod Equiv
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem quot_mem_of_relIndex_two {N T : Subgroup G} (h : N.relIndex T = 2) {u v : G}
    (hu : u ∈ T) (hv : v ∈ T) (hun : u ∉ N) (hvn : v ∉ N) : u⁻¹ * v ∈ N := by
  have h2 : (N.subgroupOf T).index = 2 := h
  obtain ⟨a, ha⟩ := Subgroup.index_eq_two_iff'.mp h2
  have hu' := ha ⟨u, hu⟩
  have hv' := ha ⟨v, hv⟩
  simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul] at hu' hv'
  have hau : (a : G) * u ∈ N := by
    unfold Xor at hu'
    tauto
  have hav : (a : G) * v ∈ N := by
    unfold Xor at hv'
    tauto
  have e : u⁻¹ * v = ((a : G) * u)⁻¹ * ((a : G) * v) := by group
  rw [e]
  exact N.mul_mem (N.inv_mem hau) hav

omit [Finite G] in
theorem conj_eq_of_le_centerOf {P L : Subgroup G} (h : L ≤ centerOf P) {x l : G}
    (hx : x ∈ P) (hl : l ∈ L) : x * l * x⁻¹ = l := by
  have hc : l ∈ Subgroup.centralizer (P : Set G) := (h hl).2
  have hxl : x * l = l * x := Subgroup.mem_centralizer_iff.mp hc x hx
  rw [hxl]
  group

omit [Finite G] in
theorem iSup_good {ι : Sort*} (S : ι → Subgroup G) (P : G → Prop) (hone : P 1)
    (hmul : ∀ x y, P x → P y → P (x * y)) (hgen : ∀ i, ∀ x ∈ S i, P x) :
    ∀ x ∈ ⨆ i, S i, P x :=
  fun _ hx => Subgroup.iSup_induction (C := P) S hx hgen hone hmul

theorem mem_Zv_of_sign_centralizes {H M S : Subgroup G} (hA : F53Amalgam H M S)
    {β ℓ : Geo H M} (hadj : (graph (H ⊔ M) H M).Adj ℓ β)
    (hz : Zv β ≤ centerOf (stab β)) {q : G} (hqT : q ∈ stab ℓ ⊓ stab β)
    (hqN : q ∉ Qv ℓ) (hidx : (Qv ℓ).relIndex (stab ℓ ⊓ stab β) = 2) {c : G}
    (hc : c ∈ Zv ℓ) (hcq : q * c * q⁻¹ = c) : c ∈ Zv β := by
  have hcent : ∀ k ∈ Qv ℓ, k * c = c * k := fun k hk =>
    Subgroup.mem_centralizer_iff.mp (Zv_le_centerOf_Qv hA ℓ hc).2 k hk
  have hcT : ∀ t ∈ (stab ℓ ⊓ stab β : Subgroup G), t * c = c * t := by
    intro t ht
    by_cases htN : t ∈ Qv ℓ
    · exact hcent t htN
    · have hn : q⁻¹ * t ∈ Qv ℓ := quot_mem_of_relIndex_two hidx hqT ht hqN htN
      have hcn := hcent (q⁻¹ * t) hn
      have hqc2 : q * c = c * q := by
        calc q * c = (q * c * q⁻¹) * q := by group
          _ = c * q := by rw [hcq]
      calc t * c = q * ((q⁻¹ * t) * c) := by group
        _ = q * (c * (q⁻¹ * t)) := by rw [hcn]
        _ = (q * c) * (q⁻¹ * t) := by group
        _ = (c * q) * (q⁻¹ * t) := by rw [hqc2]
        _ = c * (q * (q⁻¹ * t)) := by group
        _ = c * t := by group
  have hmem : c ∈ Zv ℓ ⊓ Subgroup.centralizer ((stab ℓ ⊓ stab β : Subgroup G) : Set G) :=
    ⟨hc, Subgroup.mem_centralizer_iff.mpr (fun t ht => hcT t ht)⟩
  rw [Zv_inf_centralizer_edge_eq hA hadj hz] at hmem
  exact hmem

theorem comm_Zv_Qv_mem_Zv {H M S : Subgroup G} (hA : F53Amalgam H M S) {β ℓ : Geo H M}
    (hβ : vtype β = false) (hz : Zv β ≤ centerOf (stab β)) (hl : ℓ ∈ nbrs β) {x q : G}
    (hx : x ∈ Zv ℓ) (hq : q ∈ Qv β) : ⁅x, q⁆ ∈ Zv β := by
  have hadj : (graph (H ⊔ M) H M).Adj β ℓ := hl
  have hadj' : (graph (H ⊔ M) H M).Adj ℓ β := hadj.symm
  have hβℓ : β ∈ nbrs ℓ := hadj'
  have hvℓ : vtype ℓ = true := by
    have h := vtype_ne_of_adj hadj
    rw [hβ] at h
    revert h
    cases vtype ℓ <;> simp
  have hidx : (Qv ℓ).relIndex (stab ℓ ⊓ stab β) = 2 := relIndex_Qv_inf_true hA hβℓ hvℓ
  have hqβ : q ∈ stab β ⊓ stab ℓ := Qv_le_inf hA hl hq
  have hqT : q ∈ stab ℓ ⊓ stab β := ⟨hqβ.2, hqβ.1⟩
  have hqℓ : q ∈ stab ℓ := hqβ.2
  rw [commutatorElement_def]
  by_cases hqN : q ∈ Qv ℓ
  · have hc : q * x = x * q :=
      Subgroup.mem_centralizer_iff.mp (Zv_le_centerOf_Qv hA ℓ hx).2 q hqN
    have e : x * q * x⁻¹ * q⁻¹ = 1 := by
      rw [← hc]
      group
    rw [e]
    exact (Zv β).one_mem
  · have hnorm : q * x * q⁻¹ ∈ Zv ℓ :=
      (Subgroup.mem_set_normalizer_iff.mp (stab_le_normalizer_Zv hA ℓ hqℓ) x).mp hx
    have hcℓ : x * (q * x * q⁻¹)⁻¹ ∈ Zv ℓ := (Zv ℓ).mul_mem hx ((Zv ℓ).inv_mem hnorm)
    have hq2 : q * q ∈ Qv ℓ := by
      have h1 : q⁻¹ ∈ stab ℓ ⊓ stab β := inv_mem hqT
      have h2 : q⁻¹ ∉ Qv ℓ := fun h => hqN (by simpa using (Qv ℓ).inv_mem h)
      have h3 := quot_mem_of_relIndex_two hidx hqT h1 hqN h2
      have e : q * q = (q⁻¹ * q⁻¹)⁻¹ := by simp
      rw [e]
      exact (Qv ℓ).inv_mem h3
    have hqq : (q * q) * x = x * (q * q) :=
      Subgroup.mem_centralizer_iff.mp (Zv_le_centerOf_Qv hA ℓ hx).2 (q * q) hq2
    have hqy : q * (q * x * q⁻¹) * q⁻¹ = x := by
      calc q * (q * x * q⁻¹) * q⁻¹ = (q * q) * x * (q * q)⁻¹ := by group
        _ = x * (q * q) * (q * q)⁻¹ := by rw [hqq]
        _ = x := by group
    have hc2 : (x * (q * x * q⁻¹)⁻¹) ^ 2 = 1 := (isElemAbelian_Zv hA ℓ).2 _ hcℓ
    have hcinv : (x * (q * x * q⁻¹)⁻¹)⁻¹ = x * (q * x * q⁻¹)⁻¹ := by
      rw [inv_eq_iff_mul_eq_one, ← pow_two]
      exact hc2
    have hqc : q * (x * (q * x * q⁻¹)⁻¹) * q⁻¹ = x * (q * x * q⁻¹)⁻¹ := by
      calc q * (x * (q * x * q⁻¹)⁻¹) * q⁻¹
          = (q * x * q⁻¹) * ((q * (q * x * q⁻¹) * q⁻¹))⁻¹ := by group
        _ = (q * x * q⁻¹) * x⁻¹ := by rw [hqy]
        _ = (x * (q * x * q⁻¹)⁻¹)⁻¹ := by group
        _ = x * (q * x * q⁻¹)⁻¹ := hcinv
    have e : x * q * x⁻¹ * q⁻¹ = x * (q * x * q⁻¹)⁻¹ := by group
    rw [e]
    exact mem_Zv_of_sign_centralizes hA hadj' hz hqT hqN hidx hcℓ hqc

theorem commutator_Vn_Qv_le {H M S : Subgroup G} (hA : F53Amalgam H M S) {β : Geo H M}
    (hβ : vtype β = false) (hz : Zv β ≤ centerOf (stab β)) :
    ⁅Vn β, Qv β⁆ ≤ Zv β := by
  let P : G → Prop := fun x => x ∈ stab β ∧ ∀ b ∈ Qv β, ⁅x, b⁆ ∈ Zv β
  have hone : P 1 := by
    refine ⟨(stab β).one_mem, fun b _ => ?_⟩
    rw [commutatorElement_def]
    simp
  have hmul : ∀ x y, P x → P y → P (x * y) := by
    intro x y hx hy
    refine ⟨(stab β).mul_mem hx.1 hy.1, fun b hb => ?_⟩
    have hl : ⁅y, b⁆ ∈ Zv β := hy.2 b hb
    have hm : ⁅x, b⁆ ∈ Zv β := hx.2 b hb
    rw [commutatorElement_def] at hl hm
    have hconj : x * (y * b * y⁻¹ * b⁻¹) * x⁻¹ = y * b * y⁻¹ * b⁻¹ :=
      conj_eq_of_le_centerOf hz hx.1 hl
    have e : x * y * b * (x * y)⁻¹ * b⁻¹
        = (x * (y * b * y⁻¹ * b⁻¹) * x⁻¹) * (x * b * x⁻¹ * b⁻¹) := by group
    rw [commutatorElement_def, e, hconj]
    exact (Zv β).mul_mem hl hm
  have gen : ∀ μ : Geo H M, ∀ _ : μ ∈ nbrs β, ∀ x ∈ Zv μ, P x := by
    intro μ h x hx
    have hβμ : β ∈ nbrs μ := (show (graph (H ⊔ M) H M).Adj β μ from h).symm
    exact ⟨((Qv_le_inf hA hβμ) (Zv_le_Qv hA μ hx)).2,
      fun b hb => comm_Zv_Qv_mem_Zv hA hβ hz h hx hb⟩
  have hVn : ∀ x ∈ Vn β, P x :=
    iSup_good (fun μ : Geo H M => ⨆ (_ : μ ∈ nbrs β), Zv μ) P hone hmul
      (fun μ => iSup_good (fun _ : μ ∈ nbrs β => Zv μ) P hone hmul
        (fun h x hx => gen μ h x hx))
  refine Subgroup.commutator_le.mpr ?_
  intro g₁ hg₁ g₂ hg₂
  exact (hVn g₁ hg₁).2 g₂ hg₂

end CFSG.Quasithin.EmptyFaithful.Stellmacher.OrdinaryProofs

end
