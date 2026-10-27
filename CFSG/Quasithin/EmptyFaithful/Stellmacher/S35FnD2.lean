module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35FnD1
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35FnA

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open CFSG.Quasithin.F53Mod
open scoped commutatorElement

namespace F53.Stellmacher

open CosetGeom F53

namespace S35.Fn

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

variable {β α' m γ' : Geo H M}

theorem Zγ'_le_inter (hS : Sit H M S) (h15c : Claim15c H M)
    (hI2 : ∀ β l δ δ' : Geo H M, vtype β = false → l ∈ nbrs β → l ∈ nbrs δ → l ∈ nbrs δ' →
      δ ≠ β → δ' ≠ β → Vn β ⊓ Vn δ = Vn β ⊓ Vn δ')
    (hL : Lam β α') (hB : Back H M β α' m γ') {l : Geo H M} (hl : l ∈ nbrs β)
    (hQ : Wl l ≤ Qv γ') (hW : ¬ Wl l ≤ stab α') {δ : Geo H M} (hδ : δ ∈ nbrs l)
    (hδβ : δ ≠ β) : Zv γ' ≤ Vn β ⊓ Vn δ := by
  obtain ⟨w, hwl, hwα⟩ := IsConcreteLE.not_le_iff_exists.mp hW
  have hwQ : w ∈ Qv γ' := hQ hwl
  have hwγ : w ∈ stab γ' := ((Std.mem_Qv_iff hS γ').mp hwQ).1
  have hwm : w ∈ stab m := Std.Qv_le_stab hS (Std.mem_nbrs_symm.mp hB.2.1) hwQ
  have hZ0 : Zv α' ≠ ⊥ := by
    intro h
    have := hS.cardZ5 α' hL.1.vδ'
    rw [h] at this
    simp at this
  obtain ⟨z, hz1⟩ := (Subgroup.ne_bot_iff_exists_ne_one (H := Zv α')).mp hZ0
  have hzA : (z : G) ∈ Zv α' := z.2
  have hz1' : (z : G) ≠ 1 := fun h => hz1 (Subtype.ext h)
  have hαγ : α' ≠ γ' := by
    intro h
    subst h
    have := dist_γ' hL hB
    have := dist_m hL hB
    have := hL.1.dist_eq
    omega
  obtain ⟨hc, hc1⟩ := comm_swap hS (vtype_m hL hB) (Std.mem_nbrs_symm.mp hB.1) hB.2.1 hαγ hwm
    hwγ hwα hzA hz1'
  exact le_of_mem_of_card_two (hS.cardZ5 γ' (vtype_γ' hL hB)) hc hc1
    (comm_Zα'_Wl hS h15c hI2 hL hB hl hδ hδβ hzA hwl)

end S35.Fn

end F53.Stellmacher

end CFSG.Quasithin
