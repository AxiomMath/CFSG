module

public import CFSG.Sporadic.Th.Recog.A9Mod.NormalForm
public import Certificates.Certificate687010
public import TauCeti.LinearAlgebra.GeneralLinearGroup.Congr

public section

local instance (priority := high) CFSG.Sporadic.Th.Recog.A9Mod.instAddCommGroupZMod2Classify :
    AddCommGroup (ZMod 2) :=
  Ring.toAddCommGroup

namespace CFSG.Sporadic.Th.Recog


namespace A9Mod

open CFSG.Sporadic.Th.Max3

theorem endHom_rho8a_a : endHom rho8a ⟨aPerm, aPerm_mem⟩ = toLin B1M :=
  LinearMap.ext fun v => by rw [endHom_apply, rho8a_aPerm, B1M_spec, Matrix.toLin'_apply]

theorem endHom_rho8a_b : endHom rho8a ⟨bPerm, bPerm_mem⟩ = toLin B2M :=
  LinearMap.ext fun v => by rw [endHom_apply, rho8a_bPerm, B2M_spec, Matrix.toLin'_apply]

theorem closure_wordA_wordB' :
    Subgroup.closure ({evalA wordA, evalA wordB'} : Set (alternatingGroup (Fin 9))) = ⊤ := by
  have e1 : (conjA (Equiv.swap 0 1)).toMonoidHom ⟨aPerm, aPerm_mem⟩ = evalA wordA :=
    Subtype.ext (by rw [MulEquiv.coe_toMonoidHom, conjA_apply]; decide +kernel)
  have e2 : (conjA (Equiv.swap 0 1)).toMonoidHom ⟨bPerm, bPerm_mem⟩ = evalA wordB' :=
    Subtype.ext (by rw [MulEquiv.coe_toMonoidHom, conjA_apply]; decide +kernel)
  have hs : Function.Surjective (conjA (Equiv.swap 0 1)).toMonoidHom := by
    rw [MulEquiv.coe_toMonoidHom]
    exact (conjA (Equiv.swap 0 1)).surjective
  have := congrArg (Subgroup.map (conjA (Equiv.swap 0 1)).toMonoidHom) closure_aPerm_bPerm
  rw [MonoidHom.map_closure, Set.image_pair, Subgroup.map_top_of_surjective _ hs, e1, e2] at this
  exact this

theorem classify_of_nf (ρ : alternatingGroup (Fin 9) →* (V8 ≃ₗ[ZMod 2] V8))
    (hg : endHom ρ eltG = toLin N1 ∨ endHom ρ eltG = toLin N2) :
    ∃ P : V8 ≃ₗ[ZMod 2] V8, (∀ x v, P (ρ x v) = rho8a x (P v)) ∨
      (∀ x v, P (ρ x v) = rho8a (conjA (Equiv.swap 0 1) x) (P v)) ∨
        (∀ x v, P (ρ x v) = rho8p x (P v)) := by
  have hc : ConjToTarget (endHom ρ) := Certificates.certificate687010 (endHom ρ) hg
  obtain ⟨p, hinj, hcases⟩ := hc
  refine ⟨LinearEquiv.ofInjectiveEndo (toLin p) hinj, ?_⟩
  rw [LinearEquiv.coe_ofInjectiveEndo]
  rcases hcases with ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩
  · left
    intro x v
    have := LinearMap.congr_fun (intertwine (endHom ρ) (endHom rho8a) (toLin p)
      ⟨aPerm, aPerm_mem⟩ ⟨bPerm, bPerm_mem⟩ closure_aPerm_bPerm
      (by rw [endHom_rho8a_a, ← ha, wordA_spec]) (by rw [endHom_rho8a_b, ← hb, wordB_spec]) x) v
    rwa [Module.End.mul_apply, Module.End.mul_apply, endHom_apply, endHom_apply] at this
  · right
    left
    intro x v
    let τ : alternatingGroup (Fin 9) →* Module.End (ZMod 2) V8 :=
      (endHom rho8a).comp (conjA (Equiv.swap 0 1)).toMonoidHom
    have hτ : ∀ y, τ y = endHom rho8a (conjA (Equiv.swap 0 1) y) := fun y => by
      rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
    have hτa : τ (evalA wordA) = toLin B1M := by rw [hτ, wordA_conj, endHom_rho8a_a]
    have hτb : τ (evalA wordB') = toLin B2M := by rw [hτ, wordB'_conj, endHom_rho8a_b]
    have := LinearMap.congr_fun (intertwine (endHom ρ) τ (toLin p) _ _ closure_wordA_wordB'
      (by rw [hτa, ha]) (by rw [hτb, hb]) x) v
    rwa [Module.End.mul_apply, Module.End.mul_apply, endHom_apply, hτ, endHom_apply] at this
  · right
    right
    intro x v
    have := LinearMap.congr_fun (intertwine (endHom ρ) (endHom rho8p) (toLin p)
      ⟨aPerm, aPerm_mem⟩ ⟨bPerm, bPerm_mem⟩ closure_aPerm_bPerm
      (by rw [endHom_rho8p_a, ← ha, wordA_spec]) (by rw [endHom_rho8p_b, ← hb, wordB_spec]) x) v
    rwa [Module.End.mul_apply, Module.End.mul_apply, endHom_apply, endHom_apply] at this

end A9Mod

theorem a9FaithfulDimEight_holds : A9FaithfulDimEight := by
  intro V _ _ hV ρ hρ
  have hinj : Function.Injective (A9Mod.endHom ρ) := fun x y hxy =>
    hρ (LinearEquiv.toLinearMap_injective (show (ρ x : V →ₗ[ZMod 2] V) = ρ y from hxy))
  have h9 : A9Mod.endHom ρ A9Mod.eltG ^ 9 = 1 := by
    rw [← map_pow, show A9Mod.eltG ^ 9 = 1 by decide +kernel, map_one]
  have h3 : A9Mod.endHom ρ A9Mod.eltG ^ 3 ≠ 1 := by
    rw [← map_pow]
    intro h
    exact absurd (hinj (h.trans (map_one _).symm)) (by decide +kernel)
  obtain ⟨e, he⟩ := A9Mod.exists_nf hV (A9Mod.endHom ρ A9Mod.eltG) h9 h3
  let ρ' : alternatingGroup (Fin 9) →* (V8 ≃ₗ[ZMod 2] V8) :=
    (LinearEquiv.autCongr e).toMonoidHom.comp ρ
  have key : ∀ x v, ρ' x (e v) = e (ρ x v) := fun x v => by
    show LinearEquiv.autCongr e (ρ x) (e v) = e (ρ x v)
    rw [LinearEquiv.autCongr_apply_apply, LinearEquiv.symm_apply_apply]
  have hg : A9Mod.endHom ρ' A9Mod.eltG = A9Mod.toLin A9Mod.N1 ∨
      A9Mod.endHom ρ' A9Mod.eltG = A9Mod.toLin A9Mod.N2 := by
    rcases he with he | he
    · refine Or.inl (LinearMap.ext fun w => ?_)
      rw [A9Mod.endHom_apply, ← e.apply_symm_apply w, key, ← A9Mod.endHom_apply ρ, he]
    · refine Or.inr (LinearMap.ext fun w => ?_)
      rw [A9Mod.endHom_apply, ← e.apply_symm_apply w, key, ← A9Mod.endHom_apply ρ, he]
  obtain ⟨P, hP⟩ := A9Mod.classify_of_nf ρ' hg
  rcases hP with hP | hP | hP
  · exact ⟨1, e.trans P, Or.inl fun g v => by
      rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply, ← key, hP, A9Mod.conjA_one_apply]⟩
  · exact ⟨Equiv.swap 0 1, e.trans P, Or.inl fun g v => by
      rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply, ← key, hP]⟩
  · exact ⟨1, e.trans P, Or.inr fun g v => by
      rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply, ← key, hP]⟩

end CFSG.Sporadic.Th.Recog
