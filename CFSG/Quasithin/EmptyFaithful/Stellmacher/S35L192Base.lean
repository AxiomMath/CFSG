module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35Stmt2
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35Std4

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7 CFSG.Quasithin.F53Mod
open scoped commutatorElement

namespace F53.Stellmacher

open CosetGeom F53

namespace S35.L192

open S35.Std S35.II

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

theorem back_of_PD (hS : Sit H M S) {β α' : Geo H M} (hp : S34.PD β α') :
    ∃ m γ' : Geo H M, Back H M β α' m γ' := by
  obtain ⟨m, γ', hm, hγ, h1, h2, -⟩ := Std.PD_geodesic hS hp
  exact ⟨m, γ', hm, hγ, h1, h2⟩

theorem mem_stab_of_cent (hS : Sit H M S) {m α' : Geo H M} (hm : vtype m = true)
    (hα : α' ∈ nbrs m) {x : G} (hx : x ∈ stab m) (hc : ∀ z ∈ Zv α', x * z = z * x) :
    x ∈ stab α' := by
  set g : ↥(H ⊔ M) := ⟨x, stab_le m hx⟩ with hg
  have hn : g • α' ∈ nbrs m := Std.smul_mem_nbrs_of_stab (g := g) hx hα
  have hZ : Zv (g • α') = Zv α' := by
    rw [Zv_smul]
    ext y
    rw [mem_conjSub]
    constructor
    · intro h
      have h1 := hc _ h
      have h2 : y * x = ((x⁻¹ * y * x) * x) := by
        calc y * x = x * (x⁻¹ * y * x) := by group
          _ = _ := h1
      have h3 : y = x⁻¹ * y * x := mul_right_cancel h2
      rw [h3]
      exact h
    · intro h
      have h1 : x⁻¹ * y * x = y := by
        have : x * y = y * x := hc y h
        calc x⁻¹ * y * x = x⁻¹ * (y * x) := by group
          _ = x⁻¹ * (x * y) := by rw [this]
          _ = y := by group
      show x⁻¹ * y * x ∈ Zv α'
      rw [h1]
      exact h
  by_contra hne
  have hne' : g • α' ≠ α' := fun h => hne (mem_stab_of_smul_eq h)
  exact (Std.Zv_ne hS hm hn hα hne').1 hZ

omit [Finite G] in
theorem mem_normalizer_of_comm {K : Subgroup G} {x : G} (h : ∀ z ∈ K, x * z = z * x) :
    x ∈ Subgroup.normalizer (K : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro z
  have e : ∀ z ∈ K, x * z * x⁻¹ = z := fun z hz => by rw [h z hz]; group
  constructor
  · intro hz
    rw [e z hz]
    exact hz
  · intro hz
    have h2 := h _ hz
    have h3 : x * (x * z * x⁻¹) = x * z := by rw [h2]; group
    have h4 := mul_left_cancel h3
    rw [h4] at hz
    exact hz

theorem comm_of_mem_Zv (hS : Sit H M S) {β : Geo H M} (hβ : vtype β = false) {z x : G}
    (hz : z ∈ Zv β) (hx : x ∈ stab β) : x * z = z * x :=
  Subgroup.mem_centralizer_iff.mp (hS.glob.central β hβ hz).2 x hx

end S35.L192

end F53.Stellmacher

end CFSG.Quasithin
