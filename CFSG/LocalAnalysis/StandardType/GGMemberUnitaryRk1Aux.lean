module

public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSADefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveKGPosBridge
public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSAPairAux
public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSAPairAux2
public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSARk1
public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylEltOfAutomizer
public import CFSG.LocalAnalysis.StandardType.GGPsiDiagInner
public import CFSG.LieType.Steinberg.CentralExt.SUThreeThree

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.LieType.Universal CFSG.ClassicalInvolution.Phan
  CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits Matrix
open CFSG.ClassicalInvolution.Models CFSG.LieType.Steinberg
open scoped MatrixGroups

theorem ggMUR1_refl_eq_swap
    {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {Bs X : Subgroup G} (hBs : IsElemAbelian p Bs) {n : ℕ}
    (ε : Equiv.Perm (Fin n) ≃* ↥(ggAutomizer X Bs))
    (hεrefl : ∀ a b : Fin n, a ≠ b →
      GGIsReflection p ((ε (Equiv.swap a b) : ↥(ggAutomizer X Bs)) : MulAut ↥Bs))
    {r : MulAut ↥Bs} (hrA : r ∈ ggAutomizer X Bs) (hr : GGIsReflection p r) :
    ∃ a b : Fin n, a ≠ b ∧ r = ((ε (Equiv.swap a b) : ↥(ggAutomizer X Bs)) : MulAut ↥Bs) := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨V, hVadd, hVmod, ⟨ι⟩⟩ := exists_ggLinData (p := p) hBs
  letI : AddCommGroup V := hVadd
  letI : Module (ZMod p) V := hVmod
  haveI : Finite V := Finite.of_equiv (Additive ↥Bs) ι.toEquiv
  let T : Equiv.Perm (Fin n) →* (V ≃ₗ[ZMod p] V) :=
    (ggLin (p := p) ι).comp ((Subgroup.subtype (ggAutomizer X Bs)).comp ε.toMonoidHom)
  have hT : ∀ π : Equiv.Perm (Fin n),
      T π = ggLin (p := p) ι (((ε π : ↥(ggAutomizer X Bs)) : MulAut ↥Bs)) := fun _ => rfl
  have hlin : ∀ {φ : MulAut ↥Bs}, GGIsReflection p φ → IsLinRefl (ggLin (p := p) ι φ) := by
    intro φ hφ
    obtain ⟨x, f, hfx, hrepr⟩ := exists_of_ggIsReflection (p := p) ι hφ
    rw [ggLin_eq_reflection ι hfx hrepr]
    exact ⟨x, f, hfx, fun v => Module.reflection_apply v hfx⟩
  have hinj : Function.Injective T := by
    intro x y hxy
    exact ε.injective (Subtype.ext (ggLin_injective ι hxy))
  have hsw : ∀ a b : Fin n, a ≠ b → IsLinRefl (T (Equiv.swap a b)) := by
    intro a b hab
    rw [hT]
    exact hlin (hεrefl a b hab)
  let π : Equiv.Perm (Fin n) := ε.symm ⟨r, hrA⟩
  have hπ : IsLinRefl (T π) := by
    rw [hT]
    have hval : ((ε π : ↥(ggAutomizer X Bs)) : MulAut ↥Bs) = r := by
      change ((ε (ε.symm ⟨r, hrA⟩) : ↥(ggAutomizer X Bs)) : MulAut ↥Bs) = r
      simp
    rw [hval]
    exact hlin hr
  obtain ⟨a, b, hab, hswap⟩ := isSwap_of_isLinRefl hp2 T hinj hsw hπ
  refine ⟨a, b, hab, ?_⟩
  have hval : ((ε (Equiv.swap a b) : ↥(ggAutomizer X Bs)) : MulAut ↥Bs) = r := by
    rw [← hswap]
    change ((ε π : ↥(ggAutomizer X Bs)) : MulAut ↥Bs) = r
    change ((ε (ε.symm ⟨r, hrA⟩) : ↥(ggAutomizer X Bs)) : MulAut ↥Bs) = r
    simp
  exact hval.symm

end CFSG.StandardType

end
