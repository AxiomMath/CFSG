module

public import CFSG.LocalAnalysis.StandardType.GGE6ThreeFullCentre1585Defs
public import CFSG.LocalAnalysis.StandardType.GGE6ThreeFullCentre1585Frob
public import CFSG.LocalAnalysis.StandardType.GGE6ThreeCentralizer1585Expl
public import CFSG.LieType.Chevalley.GraphFixedD4TorusWords

public section

namespace CFSG.StandardType.E6Centralizer1585

open CFSG CFSG.Assembly CFSG.StandardType
open CFSG.StandardType.GGK0MarkedKacIface1587
open CFSG.HardMathSupport.Timmesfeld.LangTorus
open CFSG.Blueprint.Chevalley
open CFSG.LieType.Chevalley
open CFSG.LieType.AlgebraicGroups
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

private theorem ltrv4b_rootChar_zsmul {τ : Tag} {K : Type} [Field K]
    (a : Fin τ.rank → Kˣ) (k : ℤ) (v : Fin τ.rank → ℤ) :
    rootChar a (k • v) = rootChar a v ^ k := by
  simp only [rootChar, Pi.smul_apply, smul_eq_mul, ← Finset.prod_zpow, ← zpow_mul, mul_comm]

private lemma ltrv4b_kernel_vanishes
    {Omega : Type} [Field Omega] [IsAlgClosed Omega] [CharP Omega 2]
    {lab : LargeEvenLabel} {p : ℕ} {R : Type} [Group R] {I : Set (MulAut R)} {phi : MulAut R}
    (ρ : MarkedRationalKacRealization Omega lab p R I phi) (b : Fin ρ.tau.rank → Omegaˣ)
    (hb : ∀ v ∈ kernelRoots (rootCharHom ρ.a), rootChar b v = 1) :
    ∀ v ∈ kernelLattice ρ, rootChar b v = 1 := by
  intro v hv
  let Kb : Submodule ℤ (Fin ρ.tau.rank → ℤ) :=
    { carrier := {w | rootChar b w = 1}
      zero_mem' := by simp [rootChar_zero]
      add_mem' := by
        intro u w hu hw
        simp only [Set.mem_setOf_eq] at hu hw
        show rootChar b (u + w) = 1
        rw [rootChar_add, hu, hw, one_mul]
      smul_mem' := by
        intro k w hw
        simp only [Set.mem_setOf_eq] at hw
        show rootChar b (k • w) = 1
        rw [ltrv4b_rootChar_zsmul, hw, one_zpow] }
  have hle : kernelLattice ρ ≤ Kb := by
    change Submodule.span ℤ (kernelRoots (rootCharHom ρ.a)) ≤ Kb
    rw [Submodule.span_le]
    intro w hw
    exact hb w hw
  exact hle hv

private lemma ltrv4b_frob_vanishes
    {Omega : Type} [Field Omega] [IsAlgClosed Omega] [CharP Omega 2]
    {lab : LargeEvenLabel} {p : ℕ} {R : Type} [Group R] {I : Set (MulAut R)} {phi : MulAut R}
    (ρ : MarkedRationalKacRealization Omega lab p R I phi) (b : Fin ρ.tau.rank → Omegaˣ)
    (hb : rootDiagUnit ρ.tau b ∈ ρ.setup.D.model) :
    ∀ v ∈ frobDefect ρ, rootChar b v = 1 := by
  intro v hv
  obtain ⟨w, rfl⟩ := hv
  change rootChar b (ρ.frobLinear w - ((2 ^ lab.n : ℕ) : ℤ) • w) = 1
  rw [rootChar_sub, rootChar_frobLinear_of_mem_model ρ b hb w, ltrv4b_rootChar_zsmul]
  simp only [zpow_natCast, mul_inv_cancel]

theorem fullCentre_injects_chars
    {Omega : Type} [Field Omega] [IsAlgClosed Omega] [CharP Omega 2]
    {lab : LargeEvenLabel} {p : ℕ} {R : Type} [Group R] {I : Set (MulAut R)} {phi : MulAut R}
    (ρ : MarkedRationalKacRealization Omega lab p R I phi) :
    ∃ f : ↥(fullCentre ρ) →* ↥(charKilled ρ.tau Omega (kernelLattice ρ ⊔ frobDefect ρ)),
      Function.Injective f := by
  let Sx : Subgroup ↥(ρ.setup.D.model) :=
    (connectedCentre ρ ⊓ ρ.setup.D.model).subgroupOf ρ.setup.D.model
  have hmem : ∀ y : Sx,
      ((y : ↥(ρ.setup.D.model)) : ModGL ρ.tau Omega) ∈
        (rootDiagUnitHom ρ.tau Omega).range := by
    intro y
    obtain ⟨-, b, hb, -⟩ :=
      (markedCentreExplicit1585_holds (Omega := Omega) lab p R I phi ρ
        ((y : ↥(ρ.setup.D.model)) : ModGL ρ.tau Omega)).1
        ⟨(Subgroup.mem_inf.1 y.2).1, (Subgroup.mem_inf.1 y.2).2⟩
    exact ⟨b, hb⟩
  let e : (Fin ρ.tau.rank → Omegaˣ) ≃* (rootDiagUnitHom ρ.tau Omega).range :=
    MonoidHom.ofInjective (f := rootDiagUnitHom ρ.tau Omega) rootDiagUnit_injective
  let ψ : Sx →* (rootDiagUnitHom ρ.tau Omega).range :=
    ((ρ.setup.D.model).subtype.comp Sx.subtype).codRestrict _ hmem
  let Φ : Sx →* ↥(charKilled ρ.tau Omega (kernelLattice ρ ⊔ frobDefect ρ)) :=
    (e.symm.toMonoidHom.comp ψ).codRestrict _ (by
      intro y
      change ∀ v ∈ (kernelLattice ρ ⊔ frobDefect ρ), rootChar (e.symm (ψ y)) v = 1
      obtain ⟨-, b, hb, hker⟩ :=
        (markedCentreExplicit1585_holds (Omega := Omega) lab p R I phi ρ
          ((y : ↥(ρ.setup.D.model)) : ModGL ρ.tau Omega)).1
          ⟨(Subgroup.mem_inf.1 y.2).1, (Subgroup.mem_inf.1 y.2).2⟩
      have hbmodel : rootDiagUnit ρ.tau b ∈ ρ.setup.D.model := by
        rw [hb]; exact (Subgroup.mem_inf.1 y.2).2
      have hsymm : e.symm (ψ y) = b := by
        apply rootDiagUnit_injective
        have h1 := congrArg Subtype.val (e.apply_symm_apply (ψ y))
        have h1' : rootDiagUnit ρ.tau (e.symm (ψ y)) =
            ((y : ↥(ρ.setup.D.model)) : ModGL ρ.tau Omega) := h1
        rw [h1', hb]
      rw [hsymm]
      intro v hv
      obtain ⟨v1, hv1, v2, hv2, rfl⟩ := Submodule.mem_sup.1 hv
      rw [rootChar_add, ltrv4b_kernel_vanishes ρ b hker v1 hv1,
        ltrv4b_frob_vanishes ρ b hbmodel v2 hv2, one_mul])
  have hΦinj : Function.Injective Φ := by
    intro y1 y2 h
    have h1 : e.symm (ψ y1) = e.symm (ψ y2) := by
      have := congrArg Subtype.val h
      simpa [Φ] using this
    have h2 : ψ y1 = ψ y2 := e.symm.injective h1
    have hval : ((y1 : ↥(ρ.setup.D.model)) : ModGL ρ.tau Omega) =
        ((y2 : ↥(ρ.setup.D.model)) : ModGL ρ.tau Omega) := by
      exact congrArg (fun z : ↥(rootDiagUnitHom ρ.tau Omega).range =>
        (z : ModGL ρ.tau Omega)) h2
    exact Subtype.ext (Subtype.ext hval)
  refine ⟨Φ.comp (Subgroup.equivMapOfInjective Sx ρ.modelAction ρ.modelAction_inj).symm.toMonoidHom,
    ?_⟩
  intro x y hxy
  exact (Subgroup.equivMapOfInjective Sx ρ.modelAction ρ.modelAction_inj).symm.injective
    (hΦinj hxy)

end CFSG.StandardType.E6Centralizer1585

end
