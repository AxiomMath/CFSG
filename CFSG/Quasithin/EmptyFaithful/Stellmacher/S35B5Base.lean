module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35Std3

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open CFSG.Quasithin.F53Mod
open scoped commutatorElement

namespace F53.Stellmacher

open CosetGeom F53 Equiv

namespace S35.B5

open S35.Std

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

@[expose] def CondD (H M : Subgroup G) : Prop :=
  ∀ β l δ δ' : Geo H M, vtype β = false → l ∈ nbrs β → l ∈ nbrs δ → l ∈ nbrs δ' →
    δ ≠ β → δ' ≠ β → δ' ≠ δ → Vn δ' ≤ Vn β ⊔ Vn δ

structure Cfg (H M : Subgroup G) (β l δ l0 γ : Geo H M) : Prop where
  vβ : vtype β = false
  l_nbr : l ∈ nbrs β
  δ_nbr : δ ∈ nbrs l
  δ_ne : δ ≠ β
  l0_nbr : l0 ∈ nbrs β
  γ_nbr : γ ∈ nbrs l0
  γ_ne : γ ≠ β

@[expose] def Yg (β δ γ : Geo H M) : Subgroup G := Vn δ ⊔ Vn γ ⊔ Vn β

namespace Cfg

variable {β l δ l0 γ : Geo H M} (h : Cfg H M β l δ l0 γ)
include h

omit [Finite G] in
theorem vl : vtype l = true := vtype_nbr_S5 h.vβ h.l_nbr

omit [Finite G] in
theorem vl0 : vtype l0 = true := vtype_nbr_S5 h.vβ h.l0_nbr

omit [Finite G] in
theorem vδ : vtype δ = false := vtype_nbr_S3 h.vl h.δ_nbr

omit [Finite G] in
theorem vγ : vtype γ = false := vtype_nbr_S3 h.vl0 h.γ_nbr

theorem dist_δβ : dist δ β = 2 := dist_eq_two_iff.mpr ⟨l, h.l_nbr, h.δ_nbr, h.δ_ne⟩

theorem dist_γβ : dist γ β = 2 := dist_eq_two_iff.mpr ⟨l0, h.l0_nbr, h.γ_nbr, h.γ_ne⟩

theorem dist_δγ_le : dist δ γ ≤ 4 := by
  have h1 := dist_triangle rfl δ β γ
  have h2 : dist β γ = 2 := by rw [CosetGeom.dist_comm]; exact h.dist_γβ
  have h3 := h.dist_δβ
  omega

theorem Vδ_le_Wb : Vn δ ≤ Wb β := Vn_le_Wb h.dist_δβ

theorem Vγ_le_Wb : Vn γ ≤ Wb β := Vn_le_Wb h.dist_γβ

theorem Vβ_le_Wδ : Vn β ≤ Wb δ := Vn_le_Wb (by rw [CosetGeom.dist_comm]; exact h.dist_δβ)

theorem Vδ_le_stab_γ (hS : Sit H M S) : Vn δ ≤ stab γ :=
  Vn_le_stab_dist hS (by have := h.dist_δγ_le; have := hS.b5; omega)

theorem Vγ_le_stab_δ (hS : Sit H M S) : Vn γ ≤ stab δ :=
  Vn_le_stab_dist hS (by
    have := h.dist_δγ_le; have := hS.b5
    rw [CosetGeom.dist_comm]; omega)

end Cfg

end S35.B5

end F53.Stellmacher

end CFSG.Quasithin
