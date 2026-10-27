module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection1.Defs

public section

universe u v

namespace CFSG.RankThree.S4Free

open Subgroup

@[expose] def IsSym4Free (X : Type*) [Group X] : Prop :=
  ∀ (H : Subgroup X) (K : Subgroup H) [K.Normal], IsEmpty (H ⧸ K ≃* Equiv.Perm (Fin 4))

theorem isSym4Free_iff (X : Type*) [Group X] :
    IsSym4Free X ↔ ∀ (H : Subgroup X) (φ : H →* Equiv.Perm (Fin 4)), ¬ Function.Surjective φ := by
  constructor
  · intro h H φ hφ
    exact (h H φ.ker).false (QuotientGroup.quotientKerEquivOfSurjective φ hφ)
  · intro h H K _
    exact ⟨fun e => h H (e.toMonoidHom.comp (QuotientGroup.mk' K))
      (e.surjective.comp (QuotientGroup.mk'_surjective K))⟩

theorem IsSym4Free.subgroup {X : Type*} [Group X] (hX : IsSym4Free X) (Y : Subgroup X) :
    IsSym4Free Y := by
  rw [isSym4Free_iff] at hX ⊢
  intro H φ hφ
  let e : H ≃* H.map Y.subtype := H.equivMapOfInjective Y.subtype Y.subtype_injective
  exact hX _ (φ.comp e.symm.toMonoidHom) (hφ.comp e.symm.surjective)

theorem IsSym4Free.quotient {X : Type*} [Group X] (hX : IsSym4Free X) (N : Subgroup X)
    [N.Normal] : IsSym4Free (X ⧸ N) := by
  rw [isSym4Free_iff] at hX ⊢
  intro H φ hφ
  let r : H.comap (QuotientGroup.mk' N) →* H :=
    { toFun := fun x => ⟨QuotientGroup.mk' N x, x.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hr : Function.Surjective r := by
    rintro ⟨y, hy⟩
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective N y
    exact ⟨⟨x, hy⟩, rfl⟩
  exact hX _ (φ.comp r) (hφ.comp hr)

theorem IsSym4Free.of_mulEquiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y)
    (hX : IsSym4Free X) : IsSym4Free Y := by
  rw [isSym4Free_iff] at hX ⊢
  intro H φ hφ
  let e' : H.comap e.toMonoidHom ≃* H :=
    { toFun := fun x => ⟨e x.1, x.2⟩
      invFun := fun y => ⟨e.symm y.1, by simp [mem_comap]⟩
      left_inv := fun x => Subtype.ext (e.symm_apply_apply x.1)
      right_inv := fun y => Subtype.ext (e.apply_symm_apply y.1)
      map_mul' := fun x y => Subtype.ext (map_mul e x.1 y.1) }
  exact hX _ (φ.comp e'.toMonoidHom) (hφ.comp e'.surjective)

theorem isSym4Free_of_not_three_dvd {X : Type*} [Group X] [Finite X]
    (h3 : ¬ 3 ∣ Nat.card X) : IsSym4Free X := by
  intro H K _
  refine ⟨fun e => h3 ?_⟩
  have h24 : Nat.card (H ⧸ K) = 24 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_perm, Nat.card_fin]
    rfl
  have hdvd : Nat.card (H ⧸ K) ∣ Nat.card X :=
    (Subgroup.card_quotient_dvd_card K).trans (Subgroup.card_subgroup_dvd_card H)
  rw [h24] at hdvd
  exact (show (3 : ℕ) ∣ 24 by norm_num).trans hdvd

abbrev oTwo (X : Type*) [Group X] : Subgroup X :=
  CFSG.piCore ({⟨2, Nat.prime_two⟩} : Set Nat.Primes) X

structure IsAdmissibleHost {S : Type*} [Group S] {X : Type*} [Group X] (ι : S →* X) :
    Prop where
  finite : Finite X
  sym4Free : IsSym4Free X
  injective : Function.Injective ι
  sylow : ∃ P : Sylow 2 X, (P : Subgroup X) = ι.range
  centralizer_le : centralizer (oTwo X : Set X) ≤ oTwo X

theorem IsAdmissibleHost.comp_mulEquiv {S : Type*} [Group S] {X : Type*} [Group X]
    {ι : S →* X} (h : IsAdmissibleHost ι) (α : S ≃* S) :
    IsAdmissibleHost (ι.comp α.toMonoidHom) where
  finite := h.finite
  sym4Free := h.sym4Free
  injective := h.injective.comp α.injective
  sylow := by
    obtain ⟨P, hP⟩ := h.sylow
    refine ⟨P, hP.trans ?_⟩
    rw [MonoidHom.range_comp, MonoidHom.range_eq_map, MonoidHom.range_eq_map]
    congr 1
    exact (map_top_of_surjective _ α.surjective).symm
  centralizer_le := h.centralizer_le

variable (S : Type u) [Group S]

variable {S}

end CFSG.RankThree.S4Free
