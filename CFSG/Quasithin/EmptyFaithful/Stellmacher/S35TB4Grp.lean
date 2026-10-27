module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35Std1

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7 CFSG.Quasithin.F53Mod
open scoped commutatorElement

namespace F53.Stellmacher

open CosetGeom F53

namespace S35.TB4

open S35.Std

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

theorem Qv_comm_Zv (hS : Sit H M S) {l : Geo H M} {q z : G} (hq : q ∈ Qv l) (hz : z ∈ Zv l) :
    q * z = z * q :=
  Subgroup.mem_centralizer_iff.mp (Zv_le_centerOf_Qv hS.glob.amalg l hz).2 q hq

omit [Finite G] in
theorem conjSub_eq_of_comm {q : G} {A : Subgroup G} (hc : ∀ z ∈ A, q * z = z * q) :
    conjSub q A = A := by
  ext x
  rw [mem_conjSub]
  constructor
  · intro h
    have h1 := hc _ h
    have h3 : x * q = (q⁻¹ * x * q) * q := by rw [← h1]; group
    have : q⁻¹ * x * q = x := (mul_right_cancel h3).symm
    rwa [this] at h
  · intro h
    have h1 := hc x h
    have : q⁻¹ * x * q = x := by
      calc q⁻¹ * x * q = q⁻¹ * (x * q) := by group
        _ = q⁻¹ * (q * x) := by rw [← h1]
        _ = x := by group
    rwa [this]

theorem mem_stab_of_comm_Zv (hS : Sit H M S) {l ρ : Geo H M} (hl : vtype l = true)
    (hρ : ρ ∈ nbrs l) {q : G} (hq : q ∈ stab l) (hc : ∀ z ∈ Zv ρ, q * z = z * q) :
    q ∈ stab ρ := by
  by_contra hn
  let g : ↥(H ⊔ M) := ⟨q, stab_le l hq⟩
  have h1 : g • ρ ∈ nbrs l := smul_mem_nbrs_of_stab (g := g) hq hρ
  have h2 : g • ρ ≠ ρ := fun h => hn (mem_stab_of_smul_eq h)
  apply (Zv_ne hS hl h1 hρ h2).1
  rw [Zv_smul]
  exact conjSub_eq_of_comm hc

theorem Qv_inf_Qv_eq (hS : Sit H M S) {γ l : Geo H M} (hγ : vtype γ = false) (hl : l ∈ nbrs γ) :
    Qv γ ⊓ Qv l = Qv γ ⊓ Subgroup.centralizer (Zv l : Set G) := by
  have hl' : vtype l = true := vtype_nbr_S5 hγ hl
  ext q
  simp only [Subgroup.mem_inf, Subgroup.mem_centralizer_iff, SetLike.mem_coe]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun z hz => (Qv_comm_Zv hS h2 hz).symm⟩
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    have hq : q ∈ stab l := Qv_le_stab hS hl h1
    obtain ⟨a, b, c, hnb, hab, -, -⟩ := nbrs_S3 hS hl'
    have ha : a ∈ nbrs l := by rw [hnb]; simp
    have hb : b ∈ nbrs l := by rw [hnb]; simp
    have hZ : ∀ ρ ∈ nbrs l, ∀ z ∈ Zv ρ, q * z = z * q := fun ρ hρ z hz => by
      have := Zv_le_Zv_of_nbr hS (vtype_nbr_S3 hl' hρ) (mem_nbrs_symm.mp hρ) hz
      exact (h2 z this).symm
    exact mem_Qv_of_fix_two hS hl' ha hb hab hq (mem_stab_of_comm_Zv hS hl' ha hq (hZ a ha))
      (mem_stab_of_comm_Zv hS hl' hb hq (hZ b hb))

theorem Qv_inf_Qv_eq_of_Zv_eq (hS : Sit H M S) {γ l l' : Geo H M} (hγ : vtype γ = false)
    (hl : l ∈ nbrs γ) (hl' : l' ∈ nbrs γ) (h : Zv l = Zv l') : Qv γ ⊓ Qv l = Qv γ ⊓ Qv l' := by
  rw [Qv_inf_Qv_eq hS hγ hl, Qv_inf_Qv_eq hS hγ hl', h]

omit [Finite G] in
theorem conjSub_Qv_inf {γ l : Geo H M} {g : ↥(H ⊔ M)} (hg : (g : G) ∈ stab γ) :
    conjSub (g : G) (Qv γ ⊓ Qv l) = Qv γ ⊓ Qv (g • l) := by
  have h1 : Qv (g • γ) = conjSub (g : G) (Qv γ) := Qv_smul g γ
  rw [smul_eq_of_mem_stab hg] at h1
  rw [Qv_smul g l, conjSub_inf, ← h1]

end S35.TB4

end F53.Stellmacher

end CFSG.Quasithin
