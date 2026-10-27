module

public import Mathlib.GroupTheory.IsSubnormal
public import Mathlib.GroupTheory.Solvable
public import Mathlib.GroupTheory.QuotientGroup.Basic

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecB

abbrev GrpPred : Type 1 := ∀ (X : Type) [Group X], Prop

@[expose] def SecAll (X : Type) [Group X] (P : GrpPred) : Prop :=
  ∀ (H₁ : Subgroup X) (N : Subgroup ↥H₁) [N.Normal], H₁.IsSubnormal →
    IsSimpleGroup (↥H₁ ⧸ N) → (∃ a b : ↥H₁ ⧸ N, a * b ≠ b * a) → P (↥H₁ ⧸ N)

@[expose] def IsoInv (P : GrpPred) : Prop :=
  ∀ (A B : Type) [Group A] [Group B], A ≃* B → P B → P A

theorem not_nonabelian_of_isSolvable {Q : Type} [Group Q] [IsSimpleGroup Q]
    (hs : Group.IsSolvable Q) : ¬ ∃ a b : Q, a * b ≠ b * a := by
  rintro ⟨a, b, hab⟩
  exact hab (IsSimpleGroup.comm_iff_isSolvable.mpr hs a b)

theorem secAll_of_isSolvable {X : Type} [Group X] (hX : Group.IsSolvable X) (P : GrpPred) :
    SecAll X P := by
  intro H₁ N _ _ hs hnab
  have hQ : Group.IsSolvable (↥H₁ ⧸ N) := inferInstance
  exact absurd hnab (not_nonabelian_of_isSolvable hQ)

theorem secAll_of_surjective {X X' : Type} [Group X] [Group X'] {P : GrpPred}
    (hP : IsoInv P) (f : X →* X') (hf : Function.Surjective f) (hker : Group.IsSolvable ↥f.ker)
    (h : SecAll X' P) : SecAll X P := by
  intro H₁ N _ hsn hs hnab
  set π := QuotientGroup.mk' N with hπ
  set D : Subgroup ↥H₁ := f.ker.subgroupOf H₁ with hD
  have hDn : D.Normal := by rw [hD]; infer_instance
  have hDm : (D.map π).Normal := hDn.map π (QuotientGroup.mk'_surjective N)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (D.map π) with hbot | htop
  ·
    have hDN : D ≤ N := by
      intro x hx
      have : π x ∈ D.map π := ⟨x, hx, rfl⟩
      rw [hbot, Subgroup.mem_bot] at this
      exact (QuotientGroup.eq_one_iff x).mp this
    set g := f.subgroupMap H₁ with hg
    have hgs : Function.Surjective g := f.subgroupMap_surjective H₁
    set N' : Subgroup ↥(H₁.map f) := N.map g with hN'
    have hN'n : N'.Normal := Subgroup.Normal.map inferInstance g hgs
    have hker' : g.ker = D := by
      ext x
      rw [MonoidHom.mem_ker, hD, Subgroup.mem_subgroupOf, MonoidHom.mem_ker, hg, Subtype.ext_iff]
      exact Iff.rfl
    set ψ : ↥H₁ →* ↥(H₁.map f) ⧸ N' := (QuotientGroup.mk' N').comp g with hψ
    have hψs : Function.Surjective ψ := (QuotientGroup.mk'_surjective N').comp hgs
    have hψk : ψ.ker = N := by
      rw [hψ, ← MonoidHom.comap_ker, QuotientGroup.ker_mk', hN', Subgroup.comap_map_eq, hker',
        sup_eq_left.mpr hDN]
    let e : (↥H₁ ⧸ N) ≃* (↥(H₁.map f) ⧸ N') :=
      (QuotientGroup.quotientMulEquivOfEq hψk.symm).trans
        (QuotientGroup.quotientKerEquivOfSurjective ψ hψs)
    have hs' : IsSimpleGroup (↥(H₁.map f) ⧸ N') := e.isSimpleGroup_congr.mp hs
    have hnab' : ∃ a b : ↥(H₁.map f) ⧸ N', a * b ≠ b * a := by
      obtain ⟨a, b, hab⟩ := hnab
      refine ⟨e a, e b, fun h' => hab ?_⟩
      apply e.injective
      rw [map_mul, map_mul, h']
    exact hP _ _ e (h (H₁.map f) N' (hsn.map hf) hs' hnab')
  ·
    have hDs : Group.IsSolvable ↥D := by
      let j : ↥D →* ↥f.ker :=
        { toFun := fun x => ⟨((x : ↥H₁) : X), Subgroup.mem_subgroupOf.mp x.2⟩
          map_one' := rfl
          map_mul' := fun _ _ => rfl }
      refine Group.isSolvable_of_isSolvable_injective (f := j) fun a b hab => ?_
      apply Subtype.ext
      apply Subtype.ext
      simpa [j] using congrArg Subtype.val hab
    have hsurj : Function.Surjective (π.comp D.subtype) := by
      intro q
      have hq : q ∈ D.map π := by rw [htop]; trivial
      obtain ⟨x, hx, rfl⟩ := hq
      exact ⟨⟨x, hx⟩, rfl⟩
    have : Group.IsSolvable (↥H₁ ⧸ N) := Group.isSolvable_of_surjective hsurj
    exact absurd hnab (not_nonabelian_of_isSolvable this)

theorem secAll_of_mulEquiv {X X' : Type} [Group X] [Group X'] {P : GrpPred}
    (hP : IsoInv P) (e : X ≃* X') (h : SecAll X' P) : SecAll X P := by
  refine secAll_of_surjective hP e.toMonoidHom e.surjective ?_ h
  have hk : (e.toMonoidHom).ker = ⊥ := by
    ext x
    simp
  rw [hk]
  infer_instance

end CFSG.Quasithin.Vol2.Ch11.SecB
