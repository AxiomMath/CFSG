module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35C56a1
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35Std2

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open CFSG.Quasithin.F53Mod

namespace F53.Stellmacher

open CosetGeom F53
open scoped commutatorElement

namespace S35.C56

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

@[expose] def CVQ (β : Geo H M) : Subgroup G := Vn β ⊓ Subgroup.centralizer (Qv β : Set G)

namespace Six

theorem Zv_le_CVQ (hS : Sit H M S) {β : Geo H M} (hβ : vtype β = false) :
    Zv β ≤ CVQ β := by
  intro z hz
  refine ⟨Std.Zv_le_Vn_S5 hS hβ hz, Subgroup.mem_centralizer_iff.mpr fun q hq => ?_⟩
  exact (Subgroup.mem_centralizer_iff.mp (Std.Zv_central hS hβ hz).2) q (pCoreOf_le 2 _ hq)

omit [Finite G] in
theorem stab_le_normalizer_CVQ (β : Geo H M) :
    stab β ≤ Subgroup.normalizer ((CVQ β : Subgroup G) : Set G) := by
  have key : ∀ g ∈ stab β, ∀ c ∈ CVQ β, g * c * g⁻¹ ∈ CVQ β := by
    intro g hg c hc
    refine ⟨((Subgroup.mem_normalizer_iff.mp (Std.Vn_normal β hg) c).mp hc.1), ?_⟩
    refine Subgroup.mem_centralizer_iff.mpr fun q hq => ?_
    have hq' : g⁻¹ * q * g ∈ Qv β := by
      have := (Subgroup.mem_normalizer_iff.mp (stab_le_normalizer_Qv β ((stab β).inv_mem hg)) q).mp
        hq
      simpa using this
    have hcq := Subgroup.mem_centralizer_iff.mp hc.2 _ hq'
    calc q * (g * c * g⁻¹) = g * ((g⁻¹ * q * g) * c) * g⁻¹ := by group
      _ = g * (c * (g⁻¹ * q * g)) * g⁻¹ := by rw [hcq]
      _ = (g * c * g⁻¹) * q := by group
  intro g hg
  exact mem_normalizer_of_conj (key g hg) (by simpa using key g⁻¹ ((stab β).inv_mem hg))

theorem mem_CVQ_iff (hS : Sit H M S) {β l : Geo H M} (hβ : vtype β = false) (hl : l ∈ nbrs β)
    (hK : Qv β ⊓ Qv l ≤ Kb β) {q0 : G} (hq0 : q0 ∈ Qv β) (hq0l : q0 ∉ Qv l) {v : G}
    (hv : v ∈ Vn β) (hc : v * q0 = q0 * v) : v ∈ CVQ β := by
  refine ⟨hv, Subgroup.mem_centralizer_iff.mpr fun q hq => ?_⟩
  by_cases hqY : q ∈ Qv β ⊓ Qv l
  · exact Subgroup.mem_centralizer_iff.mp (hK hqY).2 v hv |>.symm
  · have hq0Y : q0 ∉ Qv β ⊓ Qv l := fun h => hq0l h.2
    have hy : q0⁻¹ * q ∈ Qv β ⊓ Qv l :=
      EmptyFaithful.Stellmacher.OrdinaryProofs.quot_mem_of_relIndex_two
        (Std.relIndex_Qv hS hβ hl) hq0 hq hq0Y hqY
    have hyc := Subgroup.mem_centralizer_iff.mp (hK hy).2 v hv
    have hqe : q = q0 * (q0⁻¹ * q) := by group
    rw [hqe]
    calc q0 * (q0⁻¹ * q) * v = q0 * ((q0⁻¹ * q) * v) := by rw [mul_assoc]
      _ = q0 * (v * (q0⁻¹ * q)) := by rw [← hyc]
      _ = (q0 * v) * (q0⁻¹ * q) := by rw [← mul_assoc]
      _ = v * q0 * (q0⁻¹ * q) := by rw [hc]
      _ = v * (q0 * (q0⁻¹ * q)) := by rw [mul_assoc]

end Six

end S35.C56

end F53.Stellmacher

end CFSG.Quasithin
