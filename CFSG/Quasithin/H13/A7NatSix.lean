module

public import CFSG.Quasithin.H13.A7NatLocal

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13.A7

open Equiv Equiv.Perm Subgroup CFSG.Open CFSG.Quasithin CFSG.Quasithin.SteinbergCB

@[expose] def vecSix : Fin 7 → ZMod 2 := fun i => if i = 6 then 0 else 1

theorem vecSix_mem : vecSix ∈ evenWeight 7 := by
  rw [mem_evenWeight]
  decide

theorem hammingNorm_vecSix : hammingNorm vecSix = 6 := by
  decide

theorem vecSix_six : vecSix 6 = 0 := rfl

theorem permAct7_vecSix_iff (σ : Perm (Fin 7)) : permAct7 σ vecSix = vecSix ↔ σ 6 = 6 :=
  permAct7_fix_iff_of_weight_six hammingNorm_vecSix vecSix_six σ

@[expose] noncomputable def altLift6 :
    ↥(alternatingGroup (Fin 6)) →* ↥(alternatingGroup (Fin 7)) :=
  ((Equiv.Perm.viaEmbeddingHom (Fin.castSuccEmb : Fin 6 ↪ Fin 7)).comp
      (alternatingGroup (Fin 6)).subtype).codRestrict (alternatingGroup (Fin 7)) fun σ => by
    have h := σ.2
    rw [Equiv.Perm.mem_alternatingGroup] at h ⊢
    have key : Equiv.Perm.sign (Equiv.Perm.viaEmbeddingHom (Fin.castSuccEmb : Fin 6 ↪ Fin 7)
        (σ : Equiv.Perm (Fin 6))) = Equiv.Perm.sign (σ : Equiv.Perm (Fin 6)) := by
      classical
      rw [Equiv.Perm.viaEmbeddingHom_apply, Equiv.Perm.viaEmbedding]
      convert Equiv.Perm.sign_extendDomain (σ : Equiv.Perm (Fin 6))
        (Equiv.ofInjective (Fin.castSuccEmb : Fin 6 ↪ Fin 7).1 (Fin.castSuccEmb : Fin 6 ↪ Fin 7).2)
    exact key.trans h

theorem altLift6_injective : Function.Injective altLift6 := by
  intro a b h
  apply Subtype.ext
  apply Equiv.Perm.viaEmbeddingHom_injective (Fin.castSuccEmb : Fin 6 ↪ Fin 7)
  exact congrArg Subtype.val h

theorem altLift6_apply_last (σ : alternatingGroup (Fin 6)) :
    (altLift6 σ : Perm (Fin 7)) 6 = 6 := by
  classical
  show Equiv.Perm.viaEmbedding (σ : Perm (Fin 6)) (Fin.castSuccEmb : Fin 6 ↪ Fin 7) 6 = 6
  apply Equiv.Perm.viaEmbedding_apply_of_notMem
  rintro ⟨i, hi⟩
  have := i.2
  have h6 : ((Fin.castSuccEmb : Fin 6 ↪ Fin 7) i : ℕ) = i := rfl
  rw [hi] at h6
  simp at h6
  omega

theorem card_filter_stab_six : (Finset.univ.filter fun σ : Perm (Fin 7) =>
    sign σ = 1 ∧ σ 6 = 6).card = 360 := by
  decide +kernel

theorem nat_card_stabA7_vecSix : Nat.card (stabA7 vecSix) = 360 := by
  rw [← card_filter_stab_six, ← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
  refine Nat.card_congr ⟨fun x => ⟨(x : alternatingGroup (Fin 7)), ?_⟩,
    fun x => ⟨⟨(x : Perm (Fin 7)), mem_alternatingGroup.2 (x.2).1⟩,
      (permAct7_vecSix_iff _).2 (x.2).2⟩, fun x => rfl, fun x => rfl⟩
  exact ⟨mem_alternatingGroup.1 (x : alternatingGroup (Fin 7)).2,
    (permAct7_vecSix_iff _).1 x.2⟩

@[expose] noncomputable def altSixEquiv : alternatingGroup (Fin 6) ≃* stabA7 vecSix :=
  MulEquiv.ofBijective (altLift6.codRestrict (stabA7 vecSix) fun σ =>
      (permAct7_vecSix_iff _).2 (altLift6_apply_last σ)) (by
    have hinj : Function.Injective (altLift6.codRestrict (stabA7 vecSix) fun σ =>
        (permAct7_vecSix_iff _).2 (altLift6_apply_last σ)) := fun a b h =>
      altLift6_injective (congrArg Subtype.val h)
    refine ⟨hinj, ?_⟩
    have hcard : Nat.card (alternatingGroup (Fin 6)) = Nat.card (stabA7 vecSix) := by
      rw [nat_card_stabA7_vecSix, nat_card_alternatingGroup, Nat.card_fin]
      rfl
    exact (Function.Injective.bijective_of_nat_card_le hinj hcard.ge).2)

end CFSG.Quasithin.H13.A7
