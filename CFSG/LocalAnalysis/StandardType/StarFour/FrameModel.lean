module

public import CFSG.LocalAnalysis.StandardType.StarFour.BlockDatum
public import CFSG.LinearAlgebra.RootGroupSL.ModelBasic

public section

namespace CFSG.StandardType.StarFour

open CFSG.LinearAlgebra.RootGroupSL

variable {F : Type} [Field F] {P : Type} [CommGroup P] {V : Type} [AddCommGroup V] [Module F V]
  {ρ : P →* (V ≃ₗ[F] V)}

instance SemiFrame.instModuleFinite [Finite F] (fr : SemiFrame F ρ) (i : Fin fr.r) :
    Module.Finite F (fr.E i) :=
  Module.Finite.of_finite

@[expose] noncomputable def SemiFrame.modelEquiv (fr : SemiFrame F ρ) (i : Fin fr.r) :
    V ≃ₗ[F] (Fin (fr.m i) → fr.E i) × fr.blockCompl i :=
  fr.Φ.trans (fr.splitEquiv i)

variable [Finite F] [Module.Finite F V]

private lemma phi_blockIota (fr : SemiFrame F ρ) (i : Fin fr.r) (a : Fin (fr.m i))
    (t : fr.E i) : fr.Φ (fr.blockIota i a t) = Pi.single i (Pi.single a t) := by
  rw [SemiFrame.blockIota, LinearMap.comp_apply, LinearMap.comp_apply,
    LinearMap.single_apply, LinearMap.single_apply]
  exact fr.Φ.apply_symm_apply _

private lemma blockPi_apply (fr : SemiFrame F ρ) (i : Fin fr.r) (b : Fin (fr.m i)) (v : V) :
    fr.blockPi i b v = fr.Φ v i b := by
  rw [SemiFrame.blockPi, LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.proj_apply,
    LinearMap.proj_apply]
  rfl

private lemma single_eq_smul_single_one {E : Type} [Semiring E] {n : ℕ} (a : Fin n) (t : E) :
    (Pi.single a t : Fin n → E) = t • (Pi.single a 1 : Fin n → E) := by
  funext j
  by_cases h : j = a
  · subst h
    simp
  · rw [Pi.single_eq_of_ne h, Pi.smul_apply, Pi.single_eq_of_ne h, smul_zero]

private theorem modelEquiv_apply (fr : SemiFrame F ρ) (i : Fin fr.r) (v : V) :
    fr.modelEquiv i v =
      (fr.Φ v i, fun a : {j : Fin fr.r // j ≠ i} => fr.Φ v a.1) :=
  rfl

private theorem modelEquiv_apply_eq_split (fr : SemiFrame F ρ) (i : Fin fr.r) (v : V) :
    fr.modelEquiv i v = fr.splitEquiv i (fr.Φ v) :=
  rfl

private theorem phi_modelEquiv_symm (fr : SemiFrame F ρ) (i : Fin fr.r)
    (p : (Fin (fr.m i) → fr.E i) × fr.blockCompl i) :
    fr.Φ ((fr.modelEquiv i).symm p) = (fr.splitEquiv i).symm p := by
  rw [show (fr.modelEquiv i).symm p =
      fr.Φ.symm ((fr.splitEquiv i).symm p) from rfl, LinearEquiv.apply_symm_apply]

private theorem splitEquiv_symm_apply_self (fr : SemiFrame F ρ) (i : Fin fr.r)
    (p : (Fin (fr.m i) → fr.E i) × fr.blockCompl i) :
    (fr.splitEquiv i).symm p i = p.1 := by
  show (if h : i = i then h.symm ▸ p.1 else p.2 ⟨i, h⟩) = p.1
  simp

private noncomputable def frBlockSpecialLinearHom (fr : SemiFrame F ρ) (i : Fin fr.r) :
    SpecialLinearGroup (fr.E i) (Fin (fr.m i) → fr.E i) →* SpecialLinearGroup F V where
  toFun := fr.blockSpecialLinear i
  map_one' := by
    apply SpecialLinearGroup.ext
    intro v
    apply fr.Φ.injective
    change fr.Φ (fr.blockSpecialLinear i 1 v) = fr.Φ v
    rw [fr.blockSpecialLinear_apply i 1 v]
    funext j
    by_cases hj : j = i
    · subst hj
      simp
    · simp [Function.update_of_ne hj]
  map_mul' := fr.blockSpecialLinear_mul i

private theorem frSlOnBlock_eq_range (fr : SemiFrame F ρ) (i : Fin fr.r) :
    fr.slOnBlock i = (frBlockSpecialLinearHom fr i).range := by
  apply le_antisymm
  · intro g hg
    obtain ⟨B, hB⟩ := hg
    refine ⟨B, ?_⟩
    apply SpecialLinearGroup.ext
    intro v
    apply fr.Φ.injective
    change fr.Φ (fr.blockSpecialLinear i B v) = fr.Φ (g v)
    rw [fr.blockSpecialLinear_apply i B v, hB]
  · rintro g ⟨B, rfl⟩
    exact ⟨B, fr.blockSpecialLinear_apply i B⟩

private theorem frBlockSpecialLinearHom_comp_congr (fr : SemiFrame F ρ) (i : Fin fr.r) :
    (SpecialLinearGroup.congr_linearEquiv (fr.modelEquiv i)).toMonoidHom.comp
        (frBlockSpecialLinearHom fr i) =
      blockSLE (E := fr.E i) (VJ := Fin (fr.m i) → fr.E i) F (fr.blockCompl i) := by
  apply MonoidHom.ext
  intro B
  change (SpecialLinearGroup.congr_linearEquiv (fr.modelEquiv i)) (fr.blockSpecialLinear i B) =
      blockSLE (E := fr.E i) (VJ := Fin (fr.m i) → fr.E i) F (fr.blockCompl i) B
  apply SpecialLinearGroup.ext
  intro p
  rw [SpecialLinearGroup.congr_linearEquiv_apply_apply]
  change fr.modelEquiv i (fr.blockSpecialLinear i B ((fr.modelEquiv i).symm p)) =
    (((B : (Fin (fr.m i) → fr.E i) ≃ₗ[fr.E i]
        (Fin (fr.m i) → fr.E i)).restrictScalars F) p.1, p.2)
  have hw : fr.splitEquiv i (fr.Φ ((fr.modelEquiv i).symm p)) = p := by
    rw [phi_modelEquiv_symm, LinearEquiv.apply_symm_apply]
  rw [modelEquiv_apply_eq_split, fr.blockSpecialLinear_apply i B,
    ← fr.blockUpdate_apply i B (fr.Φ ((fr.modelEquiv i).symm p)),
    fr.splitEquiv_blockUpdate i B (fr.Φ ((fr.modelEquiv i).symm p)),
    hw, LinearEquiv.prodCongr_apply]
  rfl

theorem SemiFrame.map_slOnBlock_modelEquiv (fr : SemiFrame F ρ) (i : Fin fr.r) :
    (fr.slOnBlock i).map
        (SpecialLinearGroup.congr_linearEquiv (fr.modelEquiv i)).toMonoidHom =
      modelJ F (fr.E i) (Fin (fr.m i) → fr.E i) (fr.blockCompl i) := by
  rw [frSlOnBlock_eq_range fr i,
    MonoidHom.map_range (SpecialLinearGroup.congr_linearEquiv (fr.modelEquiv i)).toMonoidHom
      (frBlockSpecialLinearHom fr i),
    frBlockSpecialLinearHom_comp_congr fr i]
  rfl

theorem SemiFrame.modelEquiv_comp_blockIota (fr : SemiFrame F ρ) (i : Fin fr.r)
    (a : Fin (fr.m i)) :
    (fr.modelEquiv i).toLinearMap ∘ₗ fr.blockIota i a =
      modelIota (E := fr.E i) F (fr.blockCompl i) (Pi.single a 1) := by
  apply LinearMap.ext
  intro t
  change fr.modelEquiv i (fr.blockIota i a t) =
    modelIota (E := fr.E i) F (fr.blockCompl i) (Pi.single a 1) t
  rw [modelEquiv_apply, phi_blockIota, Pi.single_eq_same, modelIota_apply,
    single_eq_smul_single_one]
  refine Prod.ext rfl ?_
  funext b
  change (Pi.single i (t • Pi.single a 1) : (∀ j, Fin (fr.m j) → fr.E j)) b.1 = 0
  rw [Pi.single_eq_of_ne b.2]

theorem SemiFrame.blockPi_comp_modelEquiv_symm (fr : SemiFrame F ρ) (i : Fin fr.r)
    (b : Fin (fr.m i)) :
    fr.blockPi i b ∘ₗ (fr.modelEquiv i).symm.toLinearMap =
      modelPi F (fr.blockCompl i)
        (LinearMap.proj b : (Fin (fr.m i) → fr.E i) →ₗ[fr.E i] fr.E i) := by
  apply LinearMap.ext
  intro p
  change fr.blockPi i b ((fr.modelEquiv i).symm p) =
    modelPi F (fr.blockCompl i)
      (LinearMap.proj b : (Fin (fr.m i) → fr.E i) →ₗ[fr.E i] fr.E i) p
  rw [blockPi_apply, phi_modelEquiv_symm, splitEquiv_symm_apply_self,
    modelPi_apply, LinearMap.proj_apply]

end CFSG.StandardType.StarFour
