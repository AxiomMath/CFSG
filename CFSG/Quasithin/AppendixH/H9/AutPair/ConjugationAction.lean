module

public import CFSG.Quasithin.AppendixH.H9.GLBasics
public import CFSG.Quasithin.AppendixH.H9.GLAutomorphisms
public import CFSG.Quasithin.AppendixH.H9.AutPair.StabilizerElements

public section

open scoped Matrix

namespace CFSG.ASVolI.ChH.AutPair

open CFSG.Quasithin CFSG.Open

variable (m : ℕ)

@[expose] noncomputable def Mv : Subgroup (MulAut (PairN (m + 1))) :=
  Mg (m + 1) ⊓ centSub (Subgroup.zpowers (pairVec (ez m) 0 * pairVec 0 (ez m)))

variable {m}

theorem mem_Mv {g : MulAut (PairN (m + 1))} :
    g ∈ Mv m ↔ (∃ B : GL (Fin m) (ZMod 2), g = pairActN (m + 1) (levi m B)) ∨
      ∃ B : GL (Fin m) (ZMod 2), g = pairActN (m + 1) (levi m B) * swapN (m + 1) :=
  mem_Mv_iff

variable (m)

@[expose] noncomputable def kappa : GL (Fin m) (ZMod 2) →* Mv m :=
  ((pairActN (m + 1)).comp (levi m)).codRestrict (Mv m) fun B => mem_Mv.2 (Or.inl ⟨B, rfl⟩)

@[expose] noncomputable def swapElt : Mv m :=
  ⟨swapN (m + 1), mem_Mv.2 (Or.inr ⟨1, by simp⟩)⟩

variable {m}

theorem kappa_injective : Function.Injective (kappa m) := by
  intro B B' h
  exact levi_injective (pairActN_injective (congrArg Subtype.val h))

theorem exists_eq_kappa_or (g : Mv m) :
    (∃ B : GL (Fin m) (ZMod 2), g = kappa m B) ∨
      ∃ B : GL (Fin m) (ZMod 2), g = kappa m B * swapElt m := by
  obtain ⟨g, hg⟩ := g
  rcases mem_Mv.1 hg with ⟨B, rfl⟩ | ⟨B, rfl⟩
  · exact Or.inl ⟨B, rfl⟩
  · exact Or.inr ⟨B, rfl⟩

theorem swapElt_mul_kappa_mul_inv (X : GL (Fin m) (ZMod 2)) :
    swapElt m * kappa m X * (swapElt m)⁻¹ = kappa m (dualGLn m X) := by
  apply Subtype.ext
  show swapN (m + 1) * pairActN (m + 1) (levi m X) * (swapN (m + 1))⁻¹ =
    pairActN (m + 1) (levi m (dualGLn m X))
  rw [swapN_mul_pairActN_levi, mul_assoc, mul_inv_cancel, mul_one]

instance kappa_range_normal : (kappa m).range.Normal where
  conj_mem := by
    rintro _ ⟨X, rfl⟩ g
    rcases exists_eq_kappa_or g with ⟨B, rfl⟩ | ⟨B, rfl⟩
    · exact ⟨B * X * B⁻¹, by simp only [map_mul, map_inv]⟩
    · refine ⟨B * dualGLn m X * B⁻¹, ?_⟩
      rw [map_mul, map_mul, map_inv, ← swapElt_mul_kappa_mul_inv]
      group

variable (m)

noncomputable def conjAction : Mv m →* MulAut (GL (Fin m) (ZMod 2)) :=
  (MulAut.congr (MonoidHom.ofInjective (kappa_injective (m := m))).symm).toMonoidHom.comp
    MulAut.conjNormal

variable {m}

theorem kappa_conjAction (g : Mv m) (X : GL (Fin m) (ZMod 2)) :
    kappa m (conjAction m g X) = g * kappa m X * g⁻¹ := by
  simp [conjAction, MonoidHom.apply_ofInjective_symm, MulAut.conjNormal_apply,
    MonoidHom.ofInjective_apply]

theorem conjAction_kappa (B X : GL (Fin m) (ZMod 2)) :
    conjAction m (kappa m B) X = B * X * B⁻¹ := by
  apply kappa_injective
  rw [kappa_conjAction]
  simp only [map_mul, map_inv]

theorem conjAction_kappa_mul_swapElt (B X : GL (Fin m) (ZMod 2)) :
    conjAction m (kappa m B * swapElt m) X = B * dualGLn m X * B⁻¹ := by
  apply kappa_injective
  rw [kappa_conjAction, map_mul, map_mul, map_inv, ← swapElt_mul_kappa_mul_inv]
  group

theorem conjAction_injective (hm : 3 ≤ m) : Function.Injective (conjAction m) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  have key : ∀ X, conjAction m g X = X := fun X => by rw [hg]; rfl
  rcases exists_eq_kappa_or g with ⟨B, rfl⟩ | ⟨B, rfl⟩
  · have hB : B = 1 := eq_one_of_forall_commute_GL (by omega) fun X => by
      have h := key X
      rw [conjAction_kappa] at h
      calc B * X = B * X * B⁻¹ * B := by group
        _ = X * B := by rw [h]
    rw [hB, map_one]
  · exfalso
    refine dualGLn_not_inner hm ⟨B⁻¹, fun X => ?_⟩
    have h := key X
    rw [conjAction_kappa_mul_swapElt] at h
    calc dualGLn m X = B⁻¹ * (B * dualGLn m X * B⁻¹) * B := by group
      _ = B⁻¹ * X * B⁻¹⁻¹ := by rw [h]; group

theorem conjAction_surjective (hm : 3 ≤ m) : Function.Surjective (conjAction m) := by
  intro α
  obtain ⟨B, hB | hB⟩ := exists_aut_form_GL_two hm α
  · refine ⟨kappa m B, MulEquiv.ext fun X => ?_⟩
    rw [conjAction_kappa, hB]
  · refine ⟨kappa m B * swapElt m, MulEquiv.ext fun X => ?_⟩
    rw [conjAction_kappa_mul_swapElt, hB]

noncomputable def mulEquivAut (hm : 3 ≤ m) : Mv m ≃* MulAut (GL (Fin m) (ZMod 2)) :=
  MulEquiv.ofBijective (conjAction m) ⟨conjAction_injective hm, conjAction_surjective hm⟩

end CFSG.ASVolI.ChH.AutPair
