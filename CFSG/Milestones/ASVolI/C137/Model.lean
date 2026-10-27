module

public import CFSG.Milestones.ASVolI.C1

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChC

variable {G : Type} [Group G]

@[expose] def burnsideC137_toIntMod {U : Subgroup G} (hU : IsElemAbelian 2 U) :
    ↥U →* IntMod U hU where
  toFun u := IntMod.mk hU u
  map_one' := rfl
  map_mul' _ _ := rfl

theorem burnsideC137_toIntMod_val {U : Subgroup G} (hU : IsElemAbelian 2 U) (u : ↥U) :
    (burnsideC137_toIntMod hU u).val = (u : G) := rfl

theorem burnsideC137_ims_of_marking {D : FFModel} (hD : D.IsActionModel)
    (hinj : Function.Injective hD.modAct)
    {X V U Z : Subgroup G} (hU : IsElemAbelian 2 U) (hZU : Z ≤ U) (hUV : U ≤ V)
    (hXU : X ≤ Subgroup.normalizer (U : Set G)) (hXZ : X ≤ Subgroup.normalizer (Z : Set G))
    (hC : X ⊓ Subgroup.centralizer (U : Set G) = X ⊓ Subgroup.centralizer (V : Set G))
    (f : IntMod U hU →* D.Mod) (hfs : Function.Surjective f)
    (hfk : ∀ w : IntMod U hU, f w = 1 ↔ w.val ∈ Z)
    (hfaith : ∀ x : ↥X, (∀ w, f (convHom hU X hXU x w) = f w) → convHom hU X hXU x = 1)
    (hX : ∀ x : ↥X, ∃ δ : D.Gam, ∀ w, f (convHom hU X hXU x w) = hD.modAct δ (f w))
    (hX' : ∀ δ : D.Gam, ∃ x : ↥X, ∀ w, f (convHom hU X hXU x w) = hD.modAct δ (f w)) :
    InternalModelSection D X V U Z := by
  classical
  choose δ hδ using hX
  have hext : ∀ γ γ' : D.Gam, (∀ w, hD.modAct γ (f w) = hD.modAct γ' (f w)) → γ = γ' := by
    intro γ γ' hγ
    apply hinj
    ext q
    obtain ⟨w, rfl⟩ := hfs q
    exact hγ w
  have hmul : ∀ x y : ↥X, δ (x * y) = δ x * δ y := by
    intro x y
    refine hext _ _ fun w => ?_
    rw [← hδ, map_mul, MulAut.mul_apply, hδ, map_mul, MulAut.mul_apply, hδ]
  let α : ↥X →* D.Gam := MonoidHom.mk' δ hmul
  have hα : ∀ x, α x = δ x := fun _ => rfl
  refine ⟨hZU, hUV, hXU, hXZ, hD.ker_le, hD.sec_inv, hD.ker_inv, α,
    f.comp (burnsideC137_toIntMod hU), ?_, ?_, ?_, ?_, ?_⟩
  · intro γ
    obtain ⟨x, hx⟩ := hX' γ
    refine ⟨x, hext _ _ fun w => ?_⟩
    rw [hα, ← hδ, hx]
  · ext x
    rw [MonoidHom.mem_ker, hα, Subgroup.mem_subgroupOf]
    have hxC : (x : G) ∈ X ⊓ Subgroup.centralizer (V : Set G) ↔
        (x : G) ∈ Subgroup.centralizer (U : Set G) := by
      rw [← hC]
      exact ⟨fun h => h.2, fun h => ⟨x.2, h⟩⟩
    rw [hxC, ← convI_eq_one_iff hU ⟨x, hXU x.2⟩]
    change δ x = 1 ↔ convHom hU X hXU x = 1
    constructor
    · intro h1
      refine hfaith x fun w => ?_
      rw [hδ, h1, map_one, MulAut.one_apply]
    · intro h1
      refine hext _ _ fun w => ?_
      rw [← hδ, h1, map_one, MulAut.one_apply, MulAut.one_apply]
  · intro q
    obtain ⟨w, rfl⟩ := hfs q
    exact ⟨w, rfl⟩
  · ext u
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, MonoidHom.comp_apply]
    exact hfk _
  · intro x u v m hm huv hum
    have hw : burnsideC137_toIntMod hU v = convHom hU X hXU x (burnsideC137_toIntMod hU u) := by
      apply IntMod.val_injective
      rw [convHom_apply, convI_apply_val, burnsideC137_toIntMod_val, burnsideC137_toIntMod_val,
        huv]
      rfl
    simp only [MonoidHom.comp_apply] at hum ⊢
    rw [hw, hδ, hum, FFModel.IsActionModel.modAct_apply, FFModel.IsActionModel.modEnd_mk]
    rfl

end CFSG.ASVolI
