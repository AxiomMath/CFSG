module

public import CFSG.Quasithin.Vol2.Ch10SecG31I

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin.G31

open Module CFSG.Open CFSG.Quasithin.ASInputs
open CFSG.Quasithin.Vol2.Ch10.SecD (map_conj_transvGroup_le)

variable {V : Type} [CommGroup V]

theorem map_map_inv (g : MulAut V) (X : Subgroup V) :
    (X.map g.toMonoidHom).map g⁻¹.toMonoidHom = X := by
  rw [Subgroup.map_map]
  convert Subgroup.map_id X
  ext v
  simp

theorem map_conj_transvGroup {Gm : Subgroup (MulAut V)} {g : MulAut V} (hg : g ∈ Gm)
    (X : Subgroup V) :
    (transvGroup Gm X).map (MulAut.conj g).toMonoidHom = transvGroup Gm (X.map g.toMonoidHom) := by
  refine le_antisymm (map_conj_transvGroup_le hg X) ?_
  have h1 := map_conj_transvGroup_le (Gm.inv_mem hg) (X.map g.toMonoidHom)
  rw [map_map_inv] at h1
  have h2 := Subgroup.map_mono (f := (MulAut.conj g).toMonoidHom) h1
  rwa [Subgroup.map_map, show (MulAut.conj g).toMonoidHom.comp (MulAut.conj g⁻¹).toMonoidHom =
    MonoidHom.id _ from MonoidHom.ext fun k => by simp [mul_assoc], Subgroup.map_id] at h2

theorem conj_mem_g31G {Gm : Subgroup (MulAut V)} {Δ₀ : Set (Subgroup V)}
    (hinv : ∀ X ∈ Δ₀, ∀ g ∈ Gm, X.map (g : MulAut V).toMonoidHom ∈ Δ₀) {g : MulAut V}
    (hg : g ∈ Gm) {k : MulAut V} (hk : k ∈ g31G Gm Δ₀) : g * k * g⁻¹ ∈ g31G Gm Δ₀ := by
  have hle : (g31G Gm Δ₀).map (MulAut.conj g).toMonoidHom ≤ g31G Gm Δ₀ := by
    rw [g31G, Subgroup.map_iSup]
    refine iSup_le fun X => ?_
    rw [Subgroup.map_iSup]
    refine iSup_le fun hX => ?_
    rw [map_conj_transvGroup hg]
    exact le_iSup₂ (f := fun Y (_ : Y ∈ Δ₀) => transvGroup Gm Y) _ (hinv X hX g hg)
  exact hle ⟨k, hk, rfl⟩

theorem two_nsmul_eq_zero (hV : ∀ v : V, v ^ 2 = 1) (w : Additive V) : 2 • w = 0 := by
  apply Additive.toMul.injective
  rw [toMul_nsmul, hV]
  rfl

variable [Module (ZMod 2) (Additive V)]

@[expose] def subEquiv (X : Subgroup V) : subE X ≃+ Additive X where
  toFun w := Additive.ofMul ⟨Additive.toMul (w : Additive V), mem_subE.1 w.2⟩
  invFun u := ⟨Additive.ofMul ((Additive.toMul u : X) : V), mem_subE.2 (Additive.toMul u).2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

@[expose] def linEquivOf {X : Subgroup V} (φ : X ≃* X) : subE X ≃ₗ[ZMod 2] subE X :=
  ((subEquiv X).trans ((MulEquiv.toAdditive φ).trans (subEquiv X).symm)).toLinearEquiv
    (ZMod.map_smul _)

theorem linEquivOf_apply {X : Subgroup V} (φ : X ≃* X) (v : X) :
    ((linEquivOf φ ⟨Additive.ofMul (v : V), mem_subE.2 v.2⟩ : subE X) : Additive V) =
      Additive.ofMul ((φ v : X) : V) :=
  rfl

theorem natCard_subE (X : Subgroup V) : Nat.card (subE X) = Nat.card X :=
  Nat.card_congr ((subEquiv X).toEquiv.trans Additive.toMul)

end CFSG.Quasithin.G31
