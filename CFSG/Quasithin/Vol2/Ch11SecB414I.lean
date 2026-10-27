module

public import CFSG.Quasithin.Vol2.Ch11SecB414A
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7Basic
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7aGroup
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin.H13.Ch4.B414

open Subgroup CFSG.QuasithinUnique.Setup.X7a
open scoped MatrixGroups

variable {G : Type} [Group G] {V Z : Subgroup G} [Fact (IsElem V Z)] {Γ : Subgroup G}
  (hΓV : Γ ≤ normalizer (V : Set G)) (hΓZ : Γ ≤ normalizer (Z : Set G))
  {F : Type} [Field F] {α : ↥Γ →* GL (Fin 3) F ⧸ center (GL (Fin 3) F)}
  (hα : Function.Surjective α)
  (hker : ∀ γ : ↥Γ, α γ = 1 → ∀ v ∈ V, (γ : G) * v * (γ : G)⁻¹ * v⁻¹ ∈ Z)

include hΓV hΓZ hker in
theorem ker_le_ker_secRep : α.ker ≤ (secRep V Z Γ hΓV hΓZ).ker := fun γ hγ =>
  (MonoidHom.mem_ker).mpr ((secRep_eq_one_iff V Z Γ hΓV hΓZ γ).mpr
    (hker γ (MonoidHom.mem_ker.mp hγ)))

@[expose] noncomputable def glRep : Representation (ZMod 2) (GL (Fin 3) F) (SecU V Z) :=
  (QuotientGroup.lift α.ker (secRep V Z Γ hΓV hΓZ) (ker_le_ker_secRep hΓV hΓZ hker)).comp
    ((QuotientGroup.quotientKerEquivOfSurjective α hα).symm.toMonoidHom.comp
      (QuotientGroup.mk' (center (GL (Fin 3) F))))

theorem glRep_eq {γ : ↥Γ} {g : GL (Fin 3) F}
    (h : QuotientGroup.mk' (center (GL (Fin 3) F)) g = α γ) :
    glRep hΓV hΓZ hα hker g = secRep V Z Γ hΓV hΓZ γ := by
  have e : (QuotientGroup.quotientKerEquivOfSurjective α hα).symm (α γ) =
      (QuotientGroup.mk γ : ↥Γ ⧸ α.ker) :=
    (MulEquiv.symm_apply_eq _).mpr rfl
  rw [glRep, MonoidHom.comp_apply, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, h, e,
    QuotientGroup.lift_mk]

theorem glRep_eq_one {g : GL (Fin 3) F} (h : g ∈ center (GL (Fin 3) F)) :
    glRep hΓV hΓZ hα hker g = 1 := by
  have h1 : QuotientGroup.mk' (center (GL (Fin 3) F)) g = 1 :=
    (QuotientGroup.eq_one_iff g).mpr h
  rw [glRep, MonoidHom.comp_apply, MonoidHom.comp_apply, h1, map_one, map_one]

omit [Fact (IsElem V Z)] in
theorem exists_glRep_eq (γ : ↥Γ) : ∃ g : GL (Fin 3) F,
    QuotientGroup.mk' (center (GL (Fin 3) F)) g = α γ :=
  QuotientGroup.mk'_surjective _ (α γ)

theorem glRep_isIrreducible (hZV : Z < V)
    (hirr : ∀ J : Subgroup G, Z ≤ J → J ≤ V → Γ ≤ normalizer (J : Set G) → J = Z ∨ J = V) :
    (glRep hΓV hΓZ hα hker).IsIrreducible := by
  rw [CFSG.QuasithinUnique.Setup.X7.isIrreducible_iff]
  refine ⟨?_, fun W hW => ?_⟩
  · obtain ⟨v, hv, hvZ⟩ := IsConcreteLE.exists_of_lt hZV
    exact ⟨⟨secπ V Z ⟨v, hv⟩, 0, fun h => hvZ ((secπ_eq_zero_iff V Z ⟨v, hv⟩).mp h)⟩⟩
  have hΓ : Γ ≤ normalizer (secPre V Z W.toAddSubgroup : Set G) := by
    refine le_normalizer_secPre V Z hΓV hΓZ le_rfl fun γ _ u hu => ?_
    obtain ⟨g, hg⟩ := exists_glRep_eq (α := α) γ
    rw [← glRep_eq hΓV hΓZ hα hker hg]
    exact hW g u hu
  rcases hirr _ (le_secPre V Z _) (secPre_le V Z _) hΓ with h | h
  · left
    exact Submodule.toAddSubgroup_injective (secPre_injective V Z (h.trans (secPre_bot V Z).symm))
  · right
    exact Submodule.toAddSubgroup_injective (secPre_injective V Z (h.trans (secPre_top V Z).symm))

@[expose] noncomputable def slRep : Representation (ZMod 2) SL(3, F) (SecU V Z) :=
  (glRep hΓV hΓZ hα hker).comp Matrix.SpecialLinearGroup.toGL

theorem slRep_apply (s : SL(3, F)) :
    slRep hΓV hΓZ hα hker s = glRep hΓV hΓZ hα hker (Matrix.SpecialLinearGroup.toGL s) := rfl

theorem slRep_dT_omega [CharP F 2] {ω : Fˣ} (hω : ω ^ 3 = 1) :
    slRep hΓV hΓZ hα hker (dT ω ω) = 1 := by
  rw [slRep_apply]
  apply glRep_eq_one
  have hsc : ((Matrix.SpecialLinearGroup.toGL (dT ω ω) : GL (Fin 3) F) :
      Matrix (Fin 3) (Fin 3) F) = Matrix.scalar (Fin 3) (ω : F) := by
    have h1 : ((ω * ω)⁻¹ : Fˣ) = ω :=
      inv_eq_of_mul_eq_one_left (by rw [← sq, ← pow_succ', hω])
    show (dT ω ω : Matrix (Fin 3) (Fin 3) F) = _
    rw [dT_coe]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [dTMat, h1]
  rw [mem_center_iff]
  intro h
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, hsc]
  exact (Matrix.scalar_commute (ω : F) (fun _ => Commute.all _ _) _).symm

end CFSG.Quasithin.H13.Ch4.B414
