module

public import CFSG.LocalAnalysis.StandardType.GGCompatNbrSomeTypeA
public import CFSG.LocalAnalysis.StandardType.GGSecFiveRestLevi
public import CFSG.LocalAnalysis.StandardType.GGCompatPresentedConj

public section

namespace CFSG.StandardType

open Matrix CFSG.Assembly CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.Assembly.LowTwoRank
  SpecialLinear

section Block

variable {n : ℕ} {F : Type} [Field F]

variable (n F) in
@[expose] noncomputable def slBlockHom₃ :
    Matrix.SpecialLinearGroup (Fin (n + 1)) F →*
      Matrix.SpecialLinearGroup (Fin (n + 1 + 1 + 1 + 1)) F :=
  (slBlockHom (n + 1 + 1) F).comp (slBlockHom₂ n F)

theorem slBlockHom₃_apply (g : Matrix.SpecialLinearGroup (Fin (n + 1)) F) :
    slBlockHom₃ n F g = slBlockHom (n + 1 + 1) F (slBlockHom₂ n F g) := rfl

theorem slBlockHom₃_injective : Function.Injective (slBlockHom₃ n F) :=
  slBlockHom_injective.comp slBlockHom₂_injective

theorem slBlockHom₃_rootGroup {i j : Fin (n + 1)} (hij : i ≠ j) :
    ∀ z ∈ (SpecialLinear.rootDatum (n + 1 + 1 + 1) F).rootGroup
        (InnerDiagA.typeARoot (m := n + 1 + 1 + 1) i.castSucc.castSucc.castSucc
          j.castSucc.castSucc.castSucc),
      ∃ z' ∈ (SpecialLinear.rootDatum n F).rootGroup (InnerDiagA.typeARoot (m := n) i j),
        slBlockHom₃ n F z' = z := by
  intro z hz
  have hij₁ : i.castSucc ≠ j.castSucc := (Fin.castSucc_injective _).ne hij
  have hij₂ : i.castSucc.castSucc ≠ j.castSucc.castSucc := (Fin.castSucc_injective _).ne hij₁
  obtain ⟨z₁, hz₁, rfl⟩ := slBlockHom_rootGroup (n := n + 1 + 1) hij₂ z hz
  obtain ⟨z₂, hz₂, rfl⟩ := slBlockHom_rootGroup (n := n + 1) hij₁ z₁ hz₁
  obtain ⟨z₃, hz₃, rfl⟩ := slBlockHom_rootGroup (n := n) hij z₂ hz₂
  exact ⟨z₃, hz₃, slBlockHom₃_apply z₃⟩

theorem slBlockHom₃_mem_ggTorus (hn : 1 ≤ n) {h : Matrix.SpecialLinearGroup (Fin (n + 1)) F}
    (hh : h ∈ ggTorus (SpecialLinear.rootDatum n F)) :
    slBlockHom₃ n F h ∈ ggTorus (SpecialLinear.rootDatum (n + 1 + 1 + 1) F) := by
  rw [slBlockHom₃_apply]
  apply slBlockHom_mem_ggTorus (n := n + 1 + 1) (by omega)
  rw [slBlockHom₂_apply]
  exact slBlockHom_mem_ggTorus (n := n + 1) (by omega)
    (slBlockHom_mem_ggTorus (n := n) hn hh)

end Block

section Compat

theorem ggCompatPresented_slBlock₃_conj {G : Type*} [Group G] {n f : ℕ} (hn : 2 ≤ n) (hf : 1 ≤ f)
    {ψ : Matrix.SpecialLinearGroup (Fin (n + 1 + 1 + 1 + 1)) (GaloisField 2 f) →* G}
    (hker : ψ.ker ≤
      Subgroup.center (Matrix.SpecialLinearGroup (Fin (n + 1 + 1 + 1 + 1)) (GaloisField 2 f)))
    (u : Matrix.SpecialLinearGroup (Fin (n + 1 + 1 + 1 + 1)) (GaloisField 2 f)) :
    GGCompatPresented (SpecialLinear.rootDatum (n + 1 + 1 + 1) (GaloisField 2 f)) ψ
      (ψ.comp ((MulAut.conj u).toMonoidHom.comp (slBlockHom₃ n (GaloisField 2 f)))).range := by
  have hij : (⟨0, by omega⟩ : Fin (n + 1)) ≠ ⟨1, by omega⟩ := by simp [Fin.ext_iff]
  have hij₃ : (⟨0, by omega⟩ : Fin (n + 1)).castSucc.castSucc.castSucc ≠
      (⟨1, by omega⟩ : Fin (n + 1)).castSucc.castSucc.castSucc := by
    simp [Fin.ext_iff]
  exact ggCompatPresented_conj_comp (t' := .PSL) (n' := n + 1) (f' := f) hker
    (statedLieAdmissible_PSL hn hf) (by change 2 ≤ n; omega)
    (ι := slBlockHom₃ n (GaloisField 2 f)) slBlockHom₃_injective u
    (InnerDiagA.typeARoot_mem_roots _ hij)
    (InnerDiagA.typeARoot_mem_roots _ hij₃)
    (slBlockHom₃_rootGroup hij)
    (fun _ hh' => slBlockHom₃_mem_ggTorus (by omega) hh')

end Compat

end CFSG.StandardType

end
