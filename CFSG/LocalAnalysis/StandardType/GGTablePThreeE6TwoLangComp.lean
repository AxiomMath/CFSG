module

public import CFSG.LocalAnalysis.StandardType.GGTablePThreeE6TwoDefs
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeE6RatLabel
public import Certificates.Certificate707002
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeE6FrobAdd
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeE6TwoRatLabelD
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeE6TwoCentre
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeE6RatLabelA
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeE6RatLabelD
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeE6RatLabelOuterD
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeE6RatDistinct
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeE6RatTransfer
public import CFSG.LocalAnalysis.StandardType.GGLangSolvBridge
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeE6CompLabel
public import CFSG.LocalAnalysis.StandardType.GGJ4dRankOne
public import CFSG.LocalAnalysis.StandardType.GGLangSixRoot
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.TypeAOne
import CFSG.Quasithin.H13.NQTermLinearThreeTools
import CFSG.LocalAnalysis.StandardType.GGTablePThreeE6TwoLangCompAdm
import CFSG.LocalAnalysis.StandardType.GGTablePThreeE6TwoLangCompLabel
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.Basic
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.Certs
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcInnerLang

public section

namespace CFSG.StandardType.TablePThreeKG

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.AlgebraicGroups CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

theorem e6Two_lang_rationalComponents
    {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {p₀ : ℕ}
    (S : LangSetup Tag.E6 L p₀) (hq : S.D.q = 2) (hAlg : S.IsAlgebraic)
    {a : Fin Tag.E6.rank → Lˣ} (hT : rootDiagUnit Tag.E6 a ∈ S.D.torus)
    (hap : ∀ j, a j ^ 3 = 1) (h1 : rootDiagUnit Tag.E6 a ≠ 1) (i : KernelComponent (rootCharHom a))
    (hQS : CFSG.IsQuasisimple ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i))
    (huniq : ∀ i' : KernelComponent (rootCharHom a),
      CFSG.IsQuasisimple ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i') →
        rationalComponent S.ρ S.Γ (rootCharHom a) i' = rationalComponent S.ρ S.Γ (rootCharHom a) i) :
    ∃ lab : LargeEvenLabel, RationalLabelIs S i lab ∧
      (E6CosetW S.ρ → E6TwoCompLabelW lab) ∧ (¬ E6CosetW S.ρ → E6TwoCompLabelT lab) ∧
      (lab = ⟨.A, 2, 2⟩ → rootDiagUnit Tag.E6 a ∈ rationalComponent S.ρ S.Γ (rootCharHom a) i) := by
  classical
  have h3ne : ((3 : ℕ) : L) ≠ 0 := by
    have h2 : ((2 : ℕ) : L) = 0 := CharP.cast_eq_zero L 2
    have h3 : ((3 : ℕ) : L) = 1 := by
      have hcast : ((3 : ℕ) : L) = ((2 : ℕ) : L) + 1 := by norm_num
      rw [hcast, h2, zero_add]
    rw [h3]; exact one_ne_zero
  obtain ⟨ω, hω⟩ :=
    CFSG.Quasithin.H13.NQTerm.exists_isPrimitiveRoot_of_isAlgClosed (n := 3) (by norm_num) h3ne
  have ha3 : ∀ j, ((a j : L)) ^ 3 = 1 := fun j => by
    rw [← Units.val_pow_eq_pow_val, hap j, Units.val_one]
  choose k hklt hk using fun j => hω.eq_pow_of_pow_eq_one (ha3 j)
  let v : Fin Tag.E6.rank → ZMod 3 := fun j => (k j : ZMod 3)
  have hv : ∀ j, ((a j : Lˣ) : L) = ω ^ (v j).val := by
    intro j
    rw [ZMod.val_natCast_of_lt (hklt j)]
    exact (hk j).symm
  have hvne : v ≠ 0 := by
    intro hv0
    apply h1
    have ha1 : a = 1 := by
      funext j
      apply Units.ext
      have h : ((a j : Lˣ) : L) = 1 := by
        have hj := hv j
        rw [hv0] at hj
        simpa using hj
      simpa using h
    rw [ha1, rootDiagUnit_one]
  have hadm := e6TwoLangComp_admissible S hq hT ω hω v hv
  have hker' : kernelRoots (e6Chi v) =
      {γ | IsRoot Tag.E6 γ ∧ ∑ k, ((γ k : ℤ) : ZMod 3) * v k = 0} := by
    ext γ
    have hchi : (e6Chi v) (Multiplicative.ofAdd γ) =
        Multiplicative.ofAdd (∑ k, ((γ k : ℤ) : ZMod 3) * v k) := rfl
    simp only [kernelRoots, Set.mem_setOf_eq, hchi, ofAdd_eq_one]
  have hker : kernelRoots (rootCharHom a) = kernelRoots (e6Chi v) := by
    rw [hadm.2, ← hker']
  let Ψ : Set (Fin Tag.E6.rank → ℤ) := componentRoots (rootCharHom a) i
  have hΨ : E6KerComponent v Ψ := e6_kerComponent_of_component hω v hv i
  have hnotSolv : ¬ E6SolvTwo S.ρ Ψ := e6TwoLangComp_not_solv S hq hT hap h1 i hQS
  have hothers : ∀ Ψ' : Set (Fin Tag.E6.rank → ℤ), E6KerComponent v Ψ' →
      (∀ k : ℕ, (S.ρ : (Fin Tag.E6.rank → ℤ) → (Fin Tag.E6.rank → ℤ))^[k] '' Ψ ≠ Ψ') →
      E6SolvTwo S.ρ Ψ' :=
    fun Ψ' hΨ' hno => e6TwoLangComp_others S hq hT hap h1 i hQS huniq hker Ψ' hΨ' hno
  have hTres := Certificates.certificate707002 S.ρ v (frobRootMap_map_add S.D S.frob)
      (fun γ hγ => (S.frob.isRoot_iff γ).2 hγ) hadm.1 hvne Ψ hΨ hnotSolv hothers
  by_cases hW : E6CosetW S.ρ
  · obtain ⟨lab, hRL, hlab, hd⟩ :=
      e6TwoLangComp_labelW S hq hAlg hT hap h1 i hQS (hTres.1 hW)
    exact ⟨lab, hRL, fun _ => hlab, fun h => (h hW).elim, hd⟩
  · obtain ⟨lab, hRL, hlab, hd⟩ :=
      e6TwoLangComp_labelT S hq hT hap h1 i hQS (hTres.2 hW)
    exact ⟨lab, hRL, fun h => (hW h).elim, fun _ => hlab, hd⟩

end CFSG.StandardType.TablePThreeKG

end
