module

public import CFSG.LocalAnalysis.StandardType.GGLatEigenOrbit
public import CFSG.LocalAnalysis.StandardType.GGLangRatComp
public import CFSG.LocalAnalysis.StandardType.GGLangOrbitTorus

public section

namespace CFSG.StandardType.LangRat

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus

theorem rootDiagUnit_latEigenCoroot_mem_rationalComponent
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ p : ℕ} [Fact p.Prime]
    (S : LangSetup τ L p₀) {Smat : Matrix (Fin τ.rank) (Fin τ.rank) ℤ}
    (π : Equiv.Perm (Fin τ.rank)) (O : Set (Fin τ.rank → ℤ)) {ζ : Lˣ} (hζ : ζ ^ p = 1)
    (hp2 : p ≠ 2) (hS : ∀ i j, Smat (π i) (π j) = Smat i j)
    {a : Fin τ.rank → Lˣ} (i : KernelComponent (rootCharHom a))
    (hgen : ∀ α ∈ O, rootDiagUnit τ (fun j => ζ ^ latOrbitSumZ Smat π α j) ∈
      rationalComponent S.ρ S.Γ (rootCharHom a) i)
    {g : Fin τ.rank → ZMod p} (hg : g ∈ latEigenCoroot p Smat π O) :
    rootDiagUnit τ (fun j => ζ ^ (g j).val) ∈
      rationalComponent S.ρ S.Γ (rootCharHom a) i := by
  classical
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have hval : ∀ n : ℤ, ζ ^ ((n : ZMod p).val) = ζ ^ n := by
    intro n
    rw [← zpow_natCast, zpow_eq_zpow_iff_modEq, ZMod.val_intCast]
    exact (Int.mod_modEq n (p : ℤ)).of_dvd (by exact_mod_cast orderOf_dvd_of_pow_eq_one hζ)
  have hzero : rootDiagUnit τ (fun j => ζ ^ ((0 : Fin τ.rank → ZMod p) j).val) = 1 := by
    have h : (fun j => ζ ^ ((0 : Fin τ.rank → ZMod p) j).val) = 1 := by
      funext j
      simp
    rw [h, rootDiagUnit_one]
  have hadd : ∀ g h : Fin τ.rank → ZMod p,
      rootDiagUnit τ (fun j => ζ ^ ((g + h) j).val) =
        rootDiagUnit τ (fun j => ζ ^ (g j).val) *
          rootDiagUnit τ (fun j => ζ ^ (h j).val) := by
    intro g h
    rw [show (fun j => ζ ^ ((g + h) j).val) =
        (fun j => ζ ^ (g j).val) * (fun j => ζ ^ (h j).val) by
      funext j
      rw [Pi.add_apply, Pi.mul_apply, ZMod.val_add, ← pow_eq_pow_mod _ hζ, pow_add]]
    exact rootDiagUnit_mul _ _
  have hneg : ∀ g : Fin τ.rank → ZMod p,
      rootDiagUnit τ (fun j => ζ ^ ((-g) j).val) =
        (rootDiagUnit τ (fun j => ζ ^ (g j).val))⁻¹ := by
    intro g
    have h : rootDiagUnit τ (fun j => ζ ^ (g j).val) *
        rootDiagUnit τ (fun j => ζ ^ ((-g) j).val) = 1 := by
      rw [← hadd g (-g)]
      have h0 : (fun j => ζ ^ ((g + -g) j).val) =
          (fun j => ζ ^ ((0 : Fin τ.rank → ZMod p) j).val) := by
        funext j
        simp only [Pi.add_apply, Pi.neg_apply, Pi.zero_apply]
        rw [show g j + -g j = (0 : ZMod p) from add_neg_cancel (g j)]
      rw [h0]
      exact hzero
    exact eq_inv_of_mul_eq_one_right h
  have hgen_eq : ∀ α : Fin τ.rank → ℤ,
      rootDiagUnit τ (fun j => ζ ^ ((latOrbitSum p Smat π α) j).val) =
        rootDiagUnit τ (fun j => ζ ^ latOrbitSumZ Smat π α j) := by
    intro α
    refine congrArg (rootDiagUnit τ) ?_
    funext j
    have h : latOrbitSum p Smat π α j = (latOrbitSumZ Smat π α j : ZMod p) :=
      congrFun (latOrbitSum_eq_latOrbitSumZ p Smat π α) j
    rw [h]
    exact hval _
  have hmem : ∀ g ∈ AddSubgroup.closure (latOrbitSum p Smat π '' O),
      rootDiagUnit τ (fun j => ζ ^ (g j).val) ∈
        rationalComponent S.ρ S.Γ (rootCharHom a) i := by
    intro g hg
    induction hg using AddSubgroup.closure_induction with
    | mem x hx =>
      obtain ⟨α, hα, rfl⟩ := hx
      rw [hgen_eq α]
      exact hgen α hα
    | zero =>
      rw [hzero]
      exact one_mem _
    | add x y _ _ ihx ihy =>
      rw [hadd x y]
      exact mul_mem ihx ihy
    | neg x _ ih =>
      change rootDiagUnit τ (fun j => ζ ^ ((-x) j).val) ∈
        rationalComponent S.ρ S.Γ (rootCharHom a) i
      rw [hneg x]
      exact inv_mem ih
  exact hmem g (latEigenCoroot_le_closure_orbitSum p hp2 Smat π hS O hg)

end CFSG.StandardType.LangRat

end
