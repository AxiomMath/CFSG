module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35Notation
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35Sit

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open CFSG.Quasithin.F53Mod

namespace F53.Stellmacher

open CosetGeom F53
open scoped commutatorElement

namespace S35.C56.Six

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

omit [Finite G] in
theorem stab_le_normalizer_Qv (δ : Geo H M) : stab δ ≤ Subgroup.normalizer (Qv δ : Set G) :=
  le_normalizer_pCoreOf 2 (stab δ)

omit [Finite G] in
theorem mem_normalizer_of_conj {Y : Subgroup G} {x : G} (h : ∀ y ∈ Y, x * y * x⁻¹ ∈ Y)
    (h' : ∀ y ∈ Y, x⁻¹ * y * x ∈ Y) : x ∈ Subgroup.normalizer (Y : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨h y, fun hy => ?_⟩
  simpa [mul_assoc] using h' _ hy

omit [Finite G] in
theorem mem_normalizer_inf {A B : Subgroup G} {x : G} (hA : x ∈ Subgroup.normalizer (A : Set G))
    (hB : x ∈ Subgroup.normalizer (B : Set G)) :
    x ∈ Subgroup.normalizer ((A ⊓ B : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff] at hA hB ⊢
  intro n
  simp only [Subgroup.mem_inf] at hA hB ⊢
  exact and_congr (hA n) (hB n)

omit [Finite G] in
theorem Lr_le_normalizer_inter {β l : Geo H M} (h : ⁅Qv β, Lr β⁆ ≤ Qv l) :
    Lr β ≤ Subgroup.normalizer ((Qv β ⊓ Qv l : Subgroup G) : Set G) := by
  have key : ∀ x ∈ Lr β, ∀ y ∈ Qv β ⊓ Qv l, x * y * x⁻¹ ∈ Qv β ⊓ Qv l := by
    intro x hx y hy
    have hxs : x ∈ stab β := oTwoRes_le _ hx
    refine ⟨((Subgroup.mem_normalizer_iff.mp (stab_le_normalizer_Qv β hxs) y).mp hy.1),
      ?_⟩
    have hc : ⁅x, y⁆ ∈ ⁅Qv β, Lr β⁆ := by
      rw [Subgroup.commutator_comm]
      exact Subgroup.commutator_mem_commutator hx hy.1
    have e : x * y * x⁻¹ = ⁅x, y⁆ * y := by rw [commutatorElement_def]; group
    rw [e]
    exact (Qv l).mul_mem (h hc) hy.2
  intro x hx
  exact mem_normalizer_of_conj (key x hx) (by simpa using key x⁻¹ ((Lr β).inv_mem hx))

theorem stab_le_normalizer_inter (hS : Sit H M S) {β l : Geo H M} (hl : l ∈ nbrs β)
    (h : ⁅Qv β, Lr β⁆ ≤ Qv l) :
    stab β ≤ Subgroup.normalizer ((Qv β ⊓ Qv l : Subgroup G) : Set G) := by
  refine (le_oTwoRes_sup_of_isSylowTwoOf (sylow_stab_inf_left hS.glob.amalg hl)).trans
    (sup_le (Lr_le_normalizer_inter h) ?_)
  intro x hx
  exact mem_normalizer_inf (stab_le_normalizer_Qv β hx.1) (stab_le_normalizer_Qv l hx.2)

theorem inter_le_Qv_nbr (hS : Sit H M S) {β l μ : Geo H M} (hl : l ∈ nbrs β) (hμ : μ ∈ nbrs β)
    (h : ⁅Qv β, Lr β⁆ ≤ Qv l) : Qv β ⊓ Qv l ≤ Qv μ := by
  obtain ⟨g, hg, hgl⟩ := stab_transitive_on_nbrs hl hμ
  intro y hy
  have e : Qv μ = conjSub (g : G) (Qv l) := by rw [← hgl, Qv_smul]
  rw [e, mem_conjSub]
  have hn := stab_le_normalizer_inter hS hl h ((stab β).inv_mem hg)
  have := (Subgroup.mem_normalizer_iff.mp hn y).mp hy
  simpa using this.2

theorem inter_le_Kb (hS : Sit H M S) {β l : Geo H M} (hl : l ∈ nbrs β)
    (h : ⁅Qv β, Lr β⁆ ≤ Qv l) : Qv β ⊓ Qv l ≤ Kb β := by
  have hV : Vn β ≤ Subgroup.centralizer ((Qv β ⊓ Qv l : Subgroup G) : Set G) := by
    refine iSup₂_le fun μ hμ z hz => Subgroup.mem_centralizer_iff.mpr fun y hy => ?_
    exact (Subgroup.mem_centralizer_iff.mp (Zv_le_centerOf_Qv hS.glob.amalg μ hz).2) y
      (inter_le_Qv_nbr hS hl hμ h hy)
  intro y hy
  refine ⟨hy.1, Subgroup.mem_centralizer_iff.mpr fun v hv => ?_⟩
  exact (Subgroup.mem_centralizer_iff.mp (hV hv) y hy).symm

end S35.C56.Six

end F53.Stellmacher

end CFSG.Quasithin
