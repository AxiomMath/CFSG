module

public import CFSG.Quasithin.Recognition.F112WSetup

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7 CFSG.Quasithin.CosetGeom

namespace F112W

section Aut

theorem card_subgroup_mulAut_le_six {V : Type*} [Group V] [Finite V] (hcard : Nat.card V = 4)
    (X : Subgroup (MulAut V)) : Nat.card X ≤ 6 := by
  classical
  have : Fintype V := Fintype.ofFinite V
  let W := {v : V // v ≠ 1}
  have hW : Nat.card W = 3 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl, Fintype.card_subtype_eq]
    rw [Nat.card_eq_fintype_card] at hcard
    omega
  let f : MulAut V → Equiv.Perm W := fun φ =>
    { toFun := fun w => ⟨φ w.1, fun h => w.2 (φ.injective (by rw [h, map_one]))⟩
      invFun := fun w => ⟨φ.symm w.1, fun h => w.2 (φ.symm.injective (by rw [h, map_one]))⟩
      left_inv := fun w => by ext; simp
      right_inv := fun w => by ext; simp }
  have hf : Function.Injective f := by
    intro φ ψ h
    ext v
    by_cases hv : v = 1
    · rw [hv, map_one, map_one]
    · have := congrArg (fun σ : Equiv.Perm W => (σ ⟨v, hv⟩).1) h
      simpa [f] using this
  have h1 := Nat.card_le_card_of_injective (fun x : X => f x.1) (hf.comp Subtype.val_injective)
  have h2 : Nat.card (Equiv.Perm W) = 6 := by
    have h3 : Nat.card (Equiv.Perm W) = (Nat.card W).factorial := by
      rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card (α := W), Fintype.card_perm]
    rw [h3, hW]
    rfl
  omega

variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
theorem relIndex_pCoreOf_eq_six {L : Subgroup G} (hperm : Nonempty (oTwoQuot ↥L ≃* Equiv.Perm (Fin 3))) :
    (pCoreOf 2 L).relIndex L = 6 := by
  obtain ⟨e⟩ := hperm
  have h3 : (pCoreOf 2 L).subgroupOf L = CFSG.Open.pCore 2 ↥L := by
    unfold pCoreOf Subgroup.subgroupOf
    exact Subgroup.comap_map_eq_self_of_injective L.subtype_injective _
  show ((pCoreOf 2 L).subgroupOf L).index = 6
  rw [h3, Subgroup.index, ← perm3_card]
  exact Nat.card_congr e.toEquiv

end Aut

end F112W

end CFSG.Quasithin
