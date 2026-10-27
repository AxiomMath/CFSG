module

public import CFSG.Quasithin.Background.E11Stmt
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.Quasithin

namespace G11

namespace Canon

namespace F2E11

theorem not_trivial_action {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    {H : Subgroup (GLV V)} {I : Submodule (ZMod 2) V} (hHI : Invariant H I)
    (D : E11Data H I) (hF : Nat.card D.F = 2) (hI4 : Module.finrank (ZMod 2) I = 4)
    (htriv : ∀ g : H, restrictHom H I hHI g = 1) : False := by
  have hall : ∀ f : Module.End (ZMod 2) I, f ∈ endOn H I := by
    intro f
    rw [endOn, Subalgebra.mem_centralizer_iff]
    rintro s ⟨g, hg, hgH, rfl⟩
    have h1 : restrictEquiv g I hg = restrictHom H I hHI ⟨g, hgH⟩ := rfl
    rw [h1, htriv ⟨g, hgH⟩]
    exact LinearMap.ext fun x => rfl
  haveI : Module.Finite (ZMod 2) I := Module.finite_of_finrank_pos (by rw [hI4]; norm_num)
  let b : Module.Basis (Fin 4) (ZMod 2) I := Module.finBasisOfFinrankEq (ZMod 2) I hI4
  let f : Module.End (ZMod 2) I := (b.coord 0).smulRight (b 1)
  have hf_b0 : f (b 0) = b 1 := by
    simp [f, LinearMap.smulRight_apply, Module.Basis.coord_apply, Module.Basis.repr_self]
  have hf_b1 : f (b 1) = 0 := by
    simp [f, LinearMap.smulRight_apply, Module.Basis.coord_apply, Module.Basis.repr_self]
  have hf0 : f ≠ 0 := by
    intro h
    have h1 : f (b 0) = 0 := by rw [h]; rfl
    exact b.ne_zero 1 (hf_b0.symm.trans h1)
  have hf1 : f ≠ 1 := by
    intro h
    have h1 : f (b 1) = b 1 := by rw [h]; rfl
    exact b.ne_zero 1 (h1.symm.trans hf_b1)
  have h01 : (0 : Module.End (ZMod 2) I) ≠ 1 := by
    intro h
    have := congrArg (fun T : Module.End (ZMod 2) I => T (b 0)) h
    simp at this
    exact b.ne_zero 0 this.symm
  let e0 : endOn H I := ⟨0, hall 0⟩
  let e1 : endOn H I := ⟨1, hall 1⟩
  let ef : endOn H I := ⟨f, hall f⟩
  have hinj : Function.Injective (![e0, e1, ef] : Fin 3 → endOn H I) := by
    intro i j hij
    have hval : ∀ k : Fin 3, (((![e0, e1, ef] : Fin 3 → endOn H I) k : endOn H I) :
        Module.End (ZMod 2) I) = ![0, 1, f] k := by
      intro k
      fin_cases k <;> rfl
    have h := congrArg (fun x : endOn H I => (x : Module.End (ZMod 2) I)) hij
    rw [hval i, hval j] at h
    fin_cases i <;> fin_cases j <;> simp_all
  haveI : Finite (endOn H I) := Finite.of_equiv D.F D.endEquiv.symm.toEquiv
  have hcard := Nat.card_le_card_of_injective _ hinj
  rw [Nat.card_congr D.endEquiv.toEquiv, hF, Nat.card_fin] at hcard
  omega

theorem faithful_of_E11 {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    {H : Subgroup (GLV V)} {I : Submodule (ZMod 2) V} (hHI : Invariant H I)
    (D : E11Data H I) (hF : Nat.card D.F = 2) (hI4 : Module.finrank (ZMod 2) I = 4)
    (φH : ↥H ≃* ↥(alternatingGroup (Fin 5))) :
    ∀ h : H, (∀ v ∈ I, (h : GLV V) v = v) → h = 1 := by
  haveI : IsSimpleGroup ↥H := φH.isSimpleGroup
  intro h hh
  rcases Subgroup.Normal.eq_bot_or_eq_top (restrictHom H I hHI).ker with hbot | htop
  · have hmem : h ∈ (restrictHom H I hHI).ker :=
      MonoidHom.mem_ker.2 (restrictHom_eq_one_iff.2 hh)
    rw [hbot, Subgroup.mem_bot] at hmem
    exact hmem
  · exact (not_trivial_action hHI D hF hI4 (fun g => by
      have hg : g ∈ (restrictHom H I hHI).ker := by rw [htop]; exact Subgroup.mem_top g
      exact MonoidHom.mem_ker.1 hg)).elim

end F2E11

end Canon

end G11

end CFSG.Quasithin
