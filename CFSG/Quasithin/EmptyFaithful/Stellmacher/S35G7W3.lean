module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35G7W2
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35C56Irr
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35Fin1
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35Std3
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35Stmt

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7 CFSG.Quasithin.F53Mod
open CFSG.LieType.BorelTits Equiv
open CFSG.Quasithin.F53.Stellmacher.S35.Fin
open scoped commutatorElement

namespace F53.Stellmacher.S35.G7

open CosetGeom F53

variable {G : Type} [Group G] [Finite G]

namespace WM

variable {H M S : Subgroup G} {β : Geo H M} {c : Ch.Chart β} {E K : Subgroup G}
  (b : WBase (stab β) E K (Wb β) c.θ) (hS : Sit H M S)
include hS

theorem Wl_le_Wb (hβ : vtype β = false) {l₀ : Geo H M} (hl₀ : l₀ ∈ nbrs β) :
    Wl l₀ ≤ Wb β := by
  rw [Std.Wb_eq_iSup_Wl hS hβ]
  exact le_iSup₂ (f := fun (l : Geo H M) (_ : l ∈ nbrs β) => Wl l) l₀ hl₀

theorem Vn_le_Wb_of_nbr (hβ : vtype β = false) {l₀ δ : Geo H M} (hl₀ : l₀ ∈ nbrs β)
    (hδ : δ ∈ nbrs l₀) : Vn δ ≤ Wb β :=
  (Std.Vn_le_Wl hδ).trans (Wl_le_Wb hS hβ hl₀)

theorem isInvSub_image_Vn (hβ : vtype β = false) {l₀ δ : Geo H M} (hl₀ : l₀ ∈ nbrs β)
    (hS5 : ((stab β ⊓ stab l₀).subgroupOf (stab β)).map c.θ = S5Syl) (hδ : δ ∈ nbrs l₀) :
    IsInvSub orth S5Syl (((Vn δ).subgroupOf (Wb β)).map (fm b)) := by
  intro s hs y hy
  obtain ⟨q, hq, rfl⟩ := exists_mem_Qv_of_mem_S5Syl hS hβ hl₀ hS5 hs
  obtain ⟨x, hx, rfl⟩ := hy
  have hqδ : (q : G) ∈ stab δ := Std.Qv_le_stab hS hδ hq
  have hmem : (q : G) * (x : G) * (q : G)⁻¹ ∈ Vn δ :=
    Ch.conj_mem_Vn hqδ (Subgroup.mem_subgroupOf.mp hx)
  rw [fm_conj b q x (Vn_le_Wb_of_nbr hS hβ hl₀ hδ hmem)]
  exact ⟨_, Subgroup.mem_subgroupOf.mpr hmem, rfl⟩

theorem card_image_Vn (hI : CaseI H M) (h6b : Claim6b H M) (hβ : vtype β = false)
    {l₀ δ : Geo H M} (hl₀ : l₀ ∈ nbrs β) (hδ : δ ∈ nbrs l₀) (hne : δ ≠ β)
    (hnE : stab β ≤ Subgroup.normalizer (E : Set G)) (hVE : Vn β ≤ E) (hEW : E ≤ Wb β)
    (hEL : ⁅E, Lr β⁆ ≤ Vn β) :
    Nat.card (((Vn δ).subgroupOf (Wb β)).map (fm b)) = 4 := by
  have hl₀t : vtype l₀ = true := Std.vtype_nbr_S5 hβ hl₀
  have hδf : vtype δ = false := Std.vtype_nbr_S3 hl₀t hδ
  have hδ' : l₀ ∈ nbrs δ := Std.mem_nbrs_symm.mp hδ
  rw [card_map_fm b (Vn_le_Wb_of_nbr hS hβ hl₀ hδ)]
  have h1 := relIndex_mul_card_inf E (Vn δ)
  have h2 : Vn δ ⊓ E = Vn δ ⊓ Vn β := h6b β l₀ δ E hβ hl₀ hδ' hne hnE hVE hEW hEL
  have h3 : E ⊓ Vn δ = Vn β ⊓ Vn δ := by rw [inf_comm, h2, inf_comm]
  have h4 := (hI β l₀ δ hβ hl₀ hδ' hne).1
  have h5 := S35.C56.card_Vn hS hI hδf
  rw [h3, h4, h5] at h1
  omega

end WM

end F53.Stellmacher.S35.G7

end CFSG.Quasithin
