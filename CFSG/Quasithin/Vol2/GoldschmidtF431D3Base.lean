module

public import CFSG.Quasithin.Vol2.GoldschmidtF431D4AutPt
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.EmptyFaithful.S1421Inputs

public section

namespace CFSG.Quasithin.D4Hex

open CFSG.LargeExtraspecial.S63 CFSG.Quasithin

@[expose] noncomputable def d3T : Subgroup (MulAut D) := d4U.map (MulAut.conj : D →* MulAut D)

@[expose] noncomputable def d3z : MulAut D := MulAut.conj d4z

@[expose] noncomputable def d3t : MulAut D := MulAut.conj d4t

theorem aut_mul_conj_inv {G : Type*} [Group G] (α : MulAut G) (g : G) :
    α * MulAut.conj g * α⁻¹ = MulAut.conj (α g) := by
  ext x
  simp [MulAut.conj_apply, map_mul, map_inv]

theorem mem_centralizer_conj_iff {G : Type*} [Group G]
    (hinj : Function.Injective (MulAut.conj : G →* MulAut G)) (α : MulAut G) (g : G) :
    α ∈ Subgroup.centralizer ({MulAut.conj g} : Set (MulAut G)) ↔ α g = g := by
  rw [Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    have h1 : α * MulAut.conj g * α⁻¹ = MulAut.conj g := by rw [h]; group
    rw [aut_mul_conj_inv] at h1
    exact hinj h1
  · intro h
    have h1 := aut_mul_conj_inv α g
    rw [h] at h1
    calc α * MulAut.conj g = (α * MulAut.conj g * α⁻¹) * α := by group
      _ = MulAut.conj g * α := by rw [h1]

theorem conj_mem_autStab {G : Type} [Group G] {P : Subgroup G} {g : G} (hg : g ∈ P) :
    MulAut.conj g ∈ autStab P := by
  show ∀ x, x ∈ P ↔ MulAut.conj g x ∈ P
  intro x
  rw [MulAut.conj_apply]
  constructor
  · intro hx
    exact P.mul_mem (P.mul_mem hg hx) (P.inv_mem hg)
  · intro hx
    have h := P.mul_mem (P.mul_mem (P.inv_mem hg) hx) hg
    simpa [mul_assoc] using h

theorem orderOf_conj {G : Type*} [Group G]
    (hinj : Function.Injective (MulAut.conj : G →* MulAut G)) (g : G) :
    orderOf (MulAut.conj g) = orderOf g :=
  orderOf_injective _ hinj g

section Model

theorem conj_injective (hs : IsSimpleGroup D) :
    Function.Injective (MulAut.conj : D →* MulAut D) := by
  intro g g' h
  apply act_injective hs
  rw [← autPt_conj, ← autPt_conj, h]

end Model

theorem mem_d3T_iff {α : MulAut D} : α ∈ d3T ↔ ∃ u ∈ d4U, MulAut.conj u = α := Subgroup.mem_map

theorem conj_mem_d3T {u : D} (hu : u ∈ d4U) : MulAut.conj u ∈ d3T :=
  Subgroup.mem_map_of_mem _ hu

theorem d3z_mem_d3T : d3z ∈ d3T := conj_mem_d3T d4z_mem_d4U

theorem d3t_mem_d3T : d3t ∈ d3T := conj_mem_d3T d4t_mem_d4U

end CFSG.Quasithin.D4Hex
