module

public import CFSG.Quasithin.Background.G9StmtsModels
import CFSG.LocalAnalysis.GLTheoremB.I2810.AltOverlap

public section

namespace CFSG.Quasithin.G11

open CFSG.LocalAnalysis.GLTheoremB.Prop95Iv.I2810.AltOverlap
open CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.SmallOmegaSix

private theorem mem_permCore_eight_iff (x : Fin 8 → ZMod 2) :
    x ∈ permCore 8 ↔ x ∈ CFSG.LocalAnalysis.GLTheoremB.evenWt 8 := by
  change (∑ i, x i = 0) ↔ x ∈ CFSG.LocalAnalysis.GLTheoremB.evenWt 8
  simp only [CFSG.LocalAnalysis.GLTheoremB.evenWt, AddMonoidHom.mem_ker,
    AddMonoidHom.finsetSum_apply, Pi.evalAddMonoidHom_apply]

private theorem exists_altHeart_eight_equiv {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    (β : ↥(permCore 8) →ₗ[ZMod 2] V) (hβs : Function.Surjective β)
    (hβk : ∀ u : ↥(permCore 8), β u = 0 ↔
      (u = 0 ∨ (Even 8 ∧ ∀ i, (u : Fin 8 → ZMod 2) i = 1))) :
    ∃ δ : CFSG.LocalAnalysis.GLTheoremB.AltHeart 8 ≃+ V,
      ∀ (x : ↥(CFSG.LocalAnalysis.GLTheoremB.evenWt 8)) (u : ↥(permCore 8)),
        (u : Fin 8 → ZMod 2) = (x : Fin 8 → ZMod 2) →
          δ (QuotientAddGroup.mk x) = β u := by
  let toCore : ↥(CFSG.LocalAnalysis.GLTheoremB.evenWt 8) →+ ↥(permCore 8) :=
    { toFun := fun x => ⟨(x : Fin 8 → ZMod 2), (mem_permCore_eight_iff x).2 x.2⟩
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have hker : ∀ x ∈ (CFSG.LocalAnalysis.GLTheoremB.constWt 8 ⊓
      CFSG.LocalAnalysis.GLTheoremB.evenWt 8).addSubgroupOf
        (CFSG.LocalAnalysis.GLTheoremB.evenWt 8),
      (β.toAddMonoidHom.comp toCore) x = 0 := by
    intro x hx
    show β (toCore x) = 0
    rw [hβk (toCore x)]
    obtain ⟨hc, _⟩ := AddSubgroup.mem_inf.mp (AddSubgroup.mem_addSubgroupOf.mp hx)
    obtain ⟨k, hk⟩ := AddSubgroup.mem_zmultiples_iff.mp hc
    have hxfun : (x : Fin 8 → ZMod 2) = fun _ : Fin 8 => (k : ZMod 2) := by
      rw [← hk]
      funext i
      simp
    rcases eq_or_ne (k : ZMod 2) 0 with h0 | h0
    · left
      apply Subtype.ext
      show (x : Fin 8 → ZMod 2) = 0
      rw [hxfun]
      funext i
      simpa using h0
    · right
      refine ⟨⟨4, rfl⟩, fun i => ?_⟩
      have h1 : (k : ZMod 2) = 1 := by
        have hAll : ∀ a : ZMod 2, a ≠ 0 → a = 1 := by decide
        exact hAll _ h0
      change (x : Fin 8 → ZMod 2) i = 1
      rw [hxfun]
      simpa using h1
  let δ₀ : CFSG.LocalAnalysis.GLTheoremB.AltHeart 8 →+ V :=
    QuotientAddGroup.lift _ (β.toAddMonoidHom.comp toCore) hker
  have hδ₀ : ∀ x : ↥(CFSG.LocalAnalysis.GLTheoremB.evenWt 8),
      δ₀ (QuotientAddGroup.mk x) = β (toCore x) := fun _ => rfl
  have hinj : Function.Injective δ₀ := by
    rw [injective_iff_map_eq_zero]
    intro w hw
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective w
    have hx0 : β (toCore x) = 0 := hw
    rcases (hβk (toCore x)).mp hx0 with hzero | ⟨_, hall⟩
    · have hxeq : x = 0 := Subtype.ext (by
        have h' := congrArg (fun t : ↥(permCore 8) => (t : Fin 8 → ZMod 2)) hzero
        exact h')
      rw [hxeq]
      rfl
    · rw [QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf, AddSubgroup.mem_inf]
      refine ⟨AddSubgroup.mem_zmultiples_iff.mpr ⟨1, ?_⟩, x.2⟩
      rw [one_zsmul]
      funext i
      exact (hall i).symm
  have hsurj : Function.Surjective δ₀ := by
    intro v
    obtain ⟨u, hu⟩ := hβs v
    refine ⟨QuotientAddGroup.mk ⟨u, (mem_permCore_eight_iff u).1 u.2⟩, ?_⟩
    show β (toCore ⟨u, (mem_permCore_eight_iff u).1 u.2⟩) = v
    rw [show toCore ⟨u, (mem_permCore_eight_iff u).1 u.2⟩ = u from Subtype.ext rfl, hu]
  refine ⟨AddEquiv.ofBijective δ₀ ⟨hinj, hsurj⟩, ?_⟩
  intro x u huv
  change δ₀ (QuotientAddGroup.mk x) = β u
  exact (hδ₀ x).trans (congrArg β (Subtype.ext huv.symm))

private theorem altHeart_eight_equiv_equivariant {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    {H : Subgroup (GLV V)} (φ : ↥H ≃* ↥(alternatingGroup (Fin 8)))
    (β : ↥(permCore 8) →ₗ[ZMod 2] V)
    (hβe : ∀ (γ : ↥H) (u u' : ↥(permCore 8)),
      (u' : Fin 8 → ZMod 2) =
        permAct ((φ γ : ↥(alternatingGroup (Fin 8))) : Equiv.Perm (Fin 8)) (u : Fin 8 → ZMod 2) →
          β u' = (γ : GLV V) (β u))
    (δ : CFSG.LocalAnalysis.GLTheoremB.AltHeart 8 ≃+ V)
    (hδ : ∀ (x : ↥(CFSG.LocalAnalysis.GLTheoremB.evenWt 8)) (u : ↥(permCore 8)),
      (u : Fin 8 → ZMod 2) = (x : Fin 8 → ZMod 2) → δ (QuotientAddGroup.mk x) = β u)
    (γ : ↥H) (w : CFSG.LocalAnalysis.GLTheoremB.AltHeart 8) :
    δ (CFSG.LocalAnalysis.GLTheoremB.altHeartAct 8
        ((φ γ : ↥(alternatingGroup (Fin 8))) : Equiv.Perm (Fin 8)) w) = (γ : GLV V) (δ w) := by
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective w
  let σ : Equiv.Perm (Fin 8) := ((φ γ : ↥(alternatingGroup (Fin 8))) : Equiv.Perm (Fin 8))
  let u : ↥(permCore 8) := ⟨(x : Fin 8 → ZMod 2), (mem_permCore_eight_iff x).2 x.2⟩
  let x' : ↥(CFSG.LocalAnalysis.GLTheoremB.evenWt 8) :=
    CFSG.LocalAnalysis.GLTheoremB.permEven 8 σ x
  let u' : ↥(permCore 8) :=
    ⟨(x' : Fin 8 → ZMod 2), (mem_permCore_eight_iff x').2 x'.2⟩
  have hx' : (u' : Fin 8 → ZMod 2) = (x' : Fin 8 → ZMod 2) := rfl
  have hx0 : (u : Fin 8 → ZMod 2) = (x : Fin 8 → ZMod 2) := rfl
  have hperm : (u' : Fin 8 → ZMod 2) = permAct σ (u : Fin 8 → ZMod 2) := rfl
  have h1 : δ (QuotientAddGroup.mk x') = β u' := hδ x' u' hx'
  have h2 : δ (QuotientAddGroup.mk x) = β u := hδ x u hx0
  have h3 : β u' = (γ : GLV V) (β u) := hβe γ u u' hperm
  show δ (QuotientAddGroup.mk x') = (γ : GLV V) (δ (QuotientAddGroup.mk x))
  rw [h1, h2, h3]

theorem isNaturalMatrixModule_omega6_of_isPermCoreModule_alt8 {V : Type} [AddCommGroup V]
    [Module (ZMod 2) V] {H : Subgroup (GLV V)}
    (h : IsPermCoreModule H (alternatingGroup (Fin 8))) :
    IsNaturalMatrixModule H
      (CFSG.Open.StatedOmega (CFSG.Open.StatedQuadPlus 3 (ZMod 2))) := by
  obtain ⟨φ, β, hβs, hβk, hβe⟩ := h
  obtain ⟨δ, hδ⟩ := exists_altHeart_eight_equiv β hβs hβk
  have hequi := altHeart_eight_equiv_equivariant φ β hβe δ hδ
  let ψadd : V ≃+ (ι6 → ZMod 2) :=
    δ.symm.trans (AddEquiv.ofBijective gammaSix gammaSix_bijective)
  let ψ : V ≃ₗ[ZMod 2] (ι6 → ZMod 2) :=
    { ψadd.toAddMonoidHom.toZModLinearMap 2 with
      invFun := ψadd.symm
      left_inv := ψadd.left_inv
      right_inv := ψadd.right_inv }
  refine ⟨φ.trans thetaSix.symm, ψ, fun γ v => ?_⟩
  have hperm : omegaPerm6 ((φ.trans thetaSix.symm) γ) =
      ((φ γ : ↥(alternatingGroup (Fin 8))) : Equiv.Perm (Fin 8)) := by
    rw [← thetaSix_apply]
    simp
  have hmat : ((((φ.trans thetaSix.symm) γ : ↥(CFSG.Open.StatedOmega Q6)) :
      GL ι6 (ZMod 2)) : Matrix ι6 ι6 (ZMod 2)) =
      Mm ((φ γ : ↥(alternatingGroup (Fin 8))) : Equiv.Perm (Fin 8)) := by
    rw [← psi_val, ← hperm, psi_omegaPerm6]
  have key : δ.symm ((γ : GLV V) v) = CFSG.LocalAnalysis.GLTheoremB.altHeartAct 8
      ((φ γ : ↥(alternatingGroup (Fin 8))) : Equiv.Perm (Fin 8)) (δ.symm v) := by
    apply δ.injective
    rw [AddEquiv.apply_symm_apply, hequi, AddEquiv.apply_symm_apply]
  show gammaSix (δ.symm ((γ : GLV V) v)) = _
  rw [key, gammaSix_altHeartAct, hmat]
  rfl

end CFSG.Quasithin.G11
