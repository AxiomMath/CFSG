module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.WeakClosureNine3CData
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.WeakClosureNine3CCodes
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.Basic
public import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.LocalAnalysis.WeakClosure81.NF3C

open CFSG.QuasithinUnique CFSG.QuasithinUnique.A6Facts Subgroup
open scoped commutatorElement

abbrev Y : Type := Equiv.Perm (Fin 36) × Equiv.Perm (Fin 10)

@[expose] def ι46 : Y →* Equiv.Perm (Fin 46) :=
  (finSumFinEquiv.permCongrHom).toMonoidHom.comp (Equiv.Perm.sumCongrHom (Fin 36) (Fin 10))

theorem ι46_injective : Function.Injective ι46 :=
  (finSumFinEquiv.permCongrHom).injective.comp Equiv.Perm.sumCongrHom_injective

abbrev π10 : Y →* Equiv.Perm (Fin 10) := MonoidHom.snd _ _

@[expose] def sAdd : Equiv.Perm (Fin 36) := permOfCodes 36 cAdd iAdd (by decide +kernel)
@[expose] def sSq : Equiv.Perm (Fin 36) := permOfCodes 36 cSq iSq (by decide +kernel)
@[expose] def sInv : Equiv.Perm (Fin 36) := permOfCodes 36 cInv iInv (by decide +kernel)
@[expose] def sMul : Equiv.Perm (Fin 36) := permOfCodes 36 cMul iMul (by decide +kernel)
@[expose] def sFrob : Equiv.Perm (Fin 36) := permOfCodes 36 cFrob iFrob (by decide +kernel)
@[expose] def sMF : Equiv.Perm (Fin 36) := permOfCodes 36 cMulFrob iMulFrob (by decide +kernel)
@[expose] def sZeta : Equiv.Perm (Fin 36) := permOfCodes 36 cZeta iZeta (by decide +kernel)

@[expose] def gAdd : Y := (sAdd, A6Models.tAdd)
@[expose] def gSq : Y := (sSq, A6Models.tSq)
@[expose] def gInv : Y := (sInv, A6Models.tInv)
@[expose] def gMul : Y := (sMul, A6Models.tMul)
@[expose] def gFrob : Y := (sFrob, A6Models.tFrob)
@[expose] def gMF : Y := (sMF, A6Models.tMulFrob)
@[expose] def gZeta : Y := (sZeta, 1)

@[expose] def ML : Subgroup Y := closure {gAdd, gSq, gInv}
@[expose] def GP : Subgroup Y := closure {gAdd, gSq, gInv, gMul}
@[expose] def GM : Subgroup Y := closure {gAdd, gSq, gInv, gMF}
@[expose] def GA : Subgroup Y := closure {gAdd, gSq, gInv, gMul, gFrob}

@[expose] def genML : Fin 3 → Y := ![gAdd, gSq, gInv]

theorem genML_mem (i : Fin 3) : genML i ∈ ML := by
  apply Subgroup.subset_closure
  fin_cases i <;> simp [genML]

theorem prod_mem_ML (w : List (Fin 3)) : (w.map genML).prod ∈ ML :=
  list_prod_mem fun y hy => by
    obtain ⟨i, -, rfl⟩ := List.mem_map.mp hy
    exact genML_mem i

theorem mem_ML_of_eq {y : Y} (w : List (Fin 3)) (h : y = (w.map genML).prod) : y ∈ ML :=
  h ▸ prod_mem_ML w

theorem gZeta_mem_ML : gZeta ∈ ML := mem_ML_of_eq [0, 1, 1, 0, 1, 1] (by decide +kernel)

theorem gZeta_pow_three : gZeta ^ 3 = 1 := by decide +kernel

theorem gZeta_ne_one : gZeta ≠ 1 := by decide +kernel

theorem orderOf_gZeta : orderOf gZeta = 3 :=
  orderOf_eq_prime gZeta_pow_three gZeta_ne_one

theorem card_zpowers_gZeta : Nat.card (zpowers gZeta) = 3 := by
  rw [Nat.card_zpowers, orderOf_gZeta]

theorem π10_gZeta : π10 gZeta = 1 := rfl

theorem gZeta_comm : gAdd * gZeta = gZeta * gAdd ∧ gSq * gZeta = gZeta * gSq ∧
    gInv * gZeta = gZeta * gInv := by
  decide +kernel

theorem ML_le_centralizer : ML ≤ centralizer {gZeta} := by
  rw [ML, closure_le]
  intro g hg
  rw [SetLike.mem_coe, mem_centralizer_singleton_iff]
  obtain ⟨h1, h2, h3⟩ := gZeta_comm
  rcases hg with rfl | rfl | rfl
  · exact h1
  · exact h2
  · exact h3

theorem zpowers_gZeta_comm {z m : Y} (hz : z ∈ zpowers gZeta) (hm : m ∈ ML) : z * m = m * z := by
  have h1 : zpowers gZeta ≤ centralizer (ML : Set Y) := by
    rw [zpowers_le, mem_centralizer_iff]
    intro x hx
    exact (mem_centralizer_singleton_iff.mp (ML_le_centralizer hx))
  exact (mem_centralizer_iff.mp (h1 hz) m hm).symm

theorem gZeta_eq_commutator : gZeta = ⁅gAdd, gSq * gAdd * gSq * gSq * gSq⁆ := by
  decide +kernel

theorem map_ML_π10 : ML.map π10 = A6Models.psl29 := by
  rw [ML, MonoidHom.map_closure, A6Models.psl29]
  congr 1
  simp only [Set.image_insert_eq, Set.image_singleton]
  rfl

theorem map_GP_π10 : GP.map π10 = A6Models.pgl29 := by
  rw [GP, MonoidHom.map_closure, A6Models.pgl29]
  congr 1
  simp only [Set.image_insert_eq, Set.image_singleton]
  rfl

theorem map_GM_π10 : GM.map π10 = A6Models.m10 := by
  rw [GM, MonoidHom.map_closure, A6Models.m10]
  congr 1
  simp only [Set.image_insert_eq, Set.image_singleton]
  rfl

theorem map_GA_π10 : GA.map π10 = A6Models.autA6 := by
  rw [GA, MonoidHom.map_closure, A6Models.autA6]
  congr 1
  simp only [Set.image_insert_eq, Set.image_singleton]
  rfl

theorem ML_le_GP : ML ≤ GP := by
  refine closure_mono ?_
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
  tauto

theorem ML_le_GM : ML ≤ GM := by
  refine closure_mono ?_
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
  tauto

theorem ML_le_GA : ML ≤ GA := by
  refine closure_mono ?_
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
  tauto

end CFSG.LocalAnalysis.WeakClosure81.NF3C
