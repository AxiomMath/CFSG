
module

public import CFSG.Quasithin.Background.C2Blocks

public section

namespace CFSG.Quasithin

namespace SBc9

open CFSG.QuasithinUnique

@[expose] def permWeightHom (σ : Equiv.Perm (Fin 6)) : ↥(evenWeight 6) →+ ↥(evenWeight 6) where
  toFun := permWeight 6 σ
  map_zero' := by
    apply Subtype.ext
    funext i
    rfl
  map_add' := fun x y => by
    apply Subtype.ext
    funext i
    rfl

theorem permWeightHom_apply (σ : Equiv.Perm (Fin 6)) (x : ↥(evenWeight 6)) :
    permWeightHom σ x = permWeight 6 σ x := rfl

theorem permWeightHom_mul (σ τ : Equiv.Perm (Fin 6)) (x : ↥(evenWeight 6)) :
    permWeightHom (σ * τ) x = permWeightHom σ (permWeightHom τ x) := by
  apply Subtype.ext
  funext i
  simp [permWeightHom, permWeight, mul_inv_rev, Equiv.Perm.mul_apply]

theorem permWeightHom_one (x : ↥(evenWeight 6)) : permWeightHom 1 x = x := by
  apply Subtype.ext
  funext i
  simp [permWeightHom, permWeight]

theorem permWeightHom_mem_constWeight (σ : Equiv.Perm (Fin 6)) {x : ↥(evenWeight 6)}
    (hx : x ∈ constWeight 6) : permWeightHom σ x ∈ constWeight 6 := by
  intro i j
  exact hx (σ⁻¹ i) (σ⁻¹ j)

@[expose] def heartAct (σ : Equiv.Perm (Fin 6)) : AltHeart 6 →+ AltHeart 6 :=
  QuotientAddGroup.map (constWeight 6) (constWeight 6) (permWeightHom σ)
    (fun _ hx => permWeightHom_mem_constWeight σ hx)

theorem heartAct_mk (σ : Equiv.Perm (Fin 6)) (x : ↥(evenWeight 6)) :
    heartAct σ (QuotientAddGroup.mk x : AltHeart 6) =
      (QuotientAddGroup.mk (permWeight 6 σ x) : AltHeart 6) := rfl

theorem heartAct_mul (σ τ : Equiv.Perm (Fin 6)) (u : AltHeart 6) :
    heartAct (σ * τ) u = heartAct σ (heartAct τ u) := by
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective u
  show (QuotientAddGroup.mk (permWeightHom (σ * τ) x) : AltHeart 6) =
    (QuotientAddGroup.mk (permWeightHom σ (permWeightHom τ x)) : AltHeart 6)
  rw [permWeightHom_mul]

theorem heartAct_one (u : AltHeart 6) : heartAct 1 u = u := by
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective u
  show (QuotientAddGroup.mk (permWeightHom 1 x) : AltHeart 6) = QuotientAddGroup.mk x
  rw [permWeightHom_one]

theorem heartAct_inv_apply (σ : Equiv.Perm (Fin 6)) (u : AltHeart 6) :
    heartAct σ⁻¹ (heartAct σ u) = u := by
  rw [← heartAct_mul, inv_mul_cancel, heartAct_one]

theorem heartAct_apply_inv (σ : Equiv.Perm (Fin 6)) (u : AltHeart 6) :
    heartAct σ (heartAct σ⁻¹ u) = u := by
  rw [← heartAct_mul, mul_inv_cancel, heartAct_one]

end SBc9

end CFSG.Quasithin
