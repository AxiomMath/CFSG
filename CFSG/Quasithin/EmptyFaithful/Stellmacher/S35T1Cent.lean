module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35T1Base

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open CFSG.Quasithin.F53Mod
open scoped commutatorElement

namespace F53.Stellmacher

open CosetGeom F53

namespace S35.T1

open S35.Std S35.II

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G} {β α' m γ' : Geo H M}

@[expose] def Xg (γ' m : Geo H M) : Subgroup G :=
  stab γ' ⊓ Subgroup.centralizer (Zv m : Set G)

omit [Finite G] in
theorem mem_Xg {x : G} : x ∈ Xg γ' m ↔ x ∈ stab γ' ∧ ∀ z ∈ Zv m, z * x = x * z := by
  unfold Xg
  rw [Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
  rfl

theorem Wb_le_Xg (hS : Sit H M S) (hp : S34.PD β α') (hb : Back H M β α' m γ')
    (hW : ∀ w ∈ Wb β, ∀ z ∈ Zv α', ⁅w, z⁆ = 1) : Wb β ≤ Xg γ' m := by
  obtain ⟨hm3, hγ5, hne, -, -⟩ := back_facts hp hb
  have hWγ := Wb_le_stab hS hp hb
  have hsup : Zv γ' ⊔ Zv α' = Zv m :=
    (Zv_ne hS hm3 hb.2.1 (mem_nbrs_symm.mp hb.1) hne).2.1
  intro w hw
  refine mem_Xg.mpr ⟨hWγ hw, ?_⟩
  have h1 : Zv γ' ≤ Subgroup.centralizer ({w} : Set G) := by
    intro z hz
    have hzc : z ∈ Subgroup.centralizer (stab γ' : Set G) := (Zv_central hS hγ5 hz).2
    rw [Subgroup.mem_centralizer_iff] at hzc ⊢
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    rw [hh]
    exact hzc w (hWγ hw)
  have h2 : Zv α' ≤ Subgroup.centralizer ({w} : Set G) := by
    intro z hz
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    rw [hh]
    exact (commutatorElement_eq_one_iff_mul_comm.mp (hW w hw z hz))
  intro z hz
  have hz' : z ∈ Subgroup.centralizer ({w} : Set G) := by
    rw [← hsup] at hz
    exact (sup_le h1 h2) hz
  rw [Subgroup.mem_centralizer_iff] at hz'
  exact (hz' w rfl).symm

theorem Qv_le_Xg (hS : Sit H M S) (hb : γ' ∈ nbrs m) : Qv m ≤ Xg γ' m := by
  intro q hq
  refine mem_Xg.mpr ⟨Qv_le_stab hS hb hq, fun z hz => ?_⟩
  have hzc : z ∈ Subgroup.centralizer (Qv m : Set G) :=
    (Zv_le_centerOf_Qv hS.glob.amalg m hz).2
  rw [Subgroup.mem_centralizer_iff] at hzc
  exact (hzc q hq).symm

theorem Xg_inf_Qv_le (hS : Sit H M S) (hm3 : vtype m = true) (hb : γ' ∈ nbrs m) :
    Xg γ' m ⊓ Qv γ' ≤ Qv m := by
  intro x hx
  have h1 : x ∈ stab m := Qv_le_stab hS (mem_nbrs_symm.mp hb) hx.2
  have h2 : x ∈ Subgroup.centralizer (Zv m : Set G) := hx.1.2
  have := centralizer_Zv_eq_Qv_of_bAt hS.glob.amalg (hS.glob.crit m hm3)
  rw [← this]
  exact ⟨h1, h2⟩

end S35.T1

end F53.Stellmacher

end CFSG.Quasithin
