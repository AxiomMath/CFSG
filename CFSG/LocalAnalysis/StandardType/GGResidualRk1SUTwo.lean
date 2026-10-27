module

public import CFSG.LocalAnalysis.StandardType.GGNSJoinQFourExact
public import CFSG.ClassicalInvolution.Phan.Defs
import CFSG.ClassicalInvolution.Models.UnitaryPairs.RootSU2
import CFSG.LieType.Steinberg.CentralExt.UnitaryField
import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylEltOfAutomizer
import CFSG.LocalAnalysis.StandardType.GGNSJoinBaseLabel

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.ClassicalInvolution.Phan CFSG.LieType.Steinberg


theorem ggRk1ConclEx_of_su_two_rankOne {G : Type} [Group G] [Finite G] {p : ℕ}
    {Bs X : Subgroup G} {r : MulAut ↥Bs} (hrA : r ∈ ggAutomizer X Bs) (hrR : GGIsReflection p r)
    {f : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2] (hF : Nat.card F = (2 ^ f) ^ 2)
    (hS : Nonempty (Su F 2 f 2 ≃* ggRankOneIn X Bs r)) (hXns : ¬ GGSplitLie p X)
    (hdvd : p ∣ 2 ^ f + 1)
    (hle : ∀ lab : LargeEvenLabel, LargeEvenInLambda2 lab →
      GGHasLabel lab (↥X ⧸ Subgroup.center ↥X) → lab.n ≤ f)
    (hex : ∃ lab : LargeEvenLabel, LargeEvenInLambda2 lab ∧
      GGHasLabel lab (↥X ⧸ Subgroup.center ↥X) ∧ lab.n = f) :
    GGRk1ConclEx p Bs X r := by
  obtain ⟨σ⟩ := hS
  obtain ⟨Θ⟩ := CFSG.ClassicalInvolution.Models.nonempty_sl2_mulEquiv_su_two (K := F) (p := 2) (f := f) hF
  have hcard : Nat.card (fixedSubfield F 2 f) = 2 ^ f := card_fixedSubfield hF
  let θ : Matrix.SpecialLinearGroup (Fin 2) (fixedSubfield F 2 f) →* G :=
    (ggRankOneIn X Bs r).subtype.comp (σ.toMonoidHom.comp Θ.toMonoidHom)
  have hr2 : r * r = 1 := by simpa [pow_two] using hrR.1
  refine ⟨fixedSubfield F 2 f, inferInstance, inferInstance, θ, inferInstance, ?_, ?_,
    ggExists_weylElt_of_mem_ggAutomizer hrA hr2, fun hs => absurd hs hXns, fun _ => hcard ▸ hdvd, ?_, ?_⟩
  · exact (ggRankOneIn X Bs r).subtype_injective.comp (σ.injective.comp Θ.injective)
  · ext g
    constructor
    · rintro ⟨A, rfl⟩
      exact (σ (Θ A)).2
    · intro hg
      exact ⟨Θ.symm (σ.symm ⟨g, hg⟩), by simp [θ]⟩
  · intro lab hlam hhas
    rw [hcard]
    exact Nat.pow_le_pow_right (by norm_num) (hle lab hlam hhas)
  · obtain ⟨lab, hlam, hhas, hn⟩ := hex
    exact ⟨lab, hlam, hhas, by rw [hcard, hn]⟩

theorem ggRk1ConclEx_of_su_two_rankOne_of_label (hRig : GGLabelRigidInput) {G : Type} [Group G] [Finite G]
    {p : ℕ} {Bs X : Subgroup G} {r : MulAut ↥Bs} (hrA : r ∈ ggAutomizer X Bs) (hrR : GGIsReflection p r)
    {f : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2] (hF : Nat.card F = (2 ^ f) ^ 2)
    (hS : Nonempty (Su F 2 f 2 ≃* ggRankOneIn X Bs r)) (hXns : ¬ GGSplitLie p X)
    (hdvd : p ∣ 2 ^ f + 1) {lab : LargeEvenLabel} (hlam : LargeEvenInLambda2 lab)
    (hhas : GGHasLabel lab (↥X ⧸ Subgroup.center ↥X)) (hA : lab.tag ≠ .A)
    (hD : lab.tag = .twD → lab.rank ≠ 2) (hn : lab.n = f) :
    GGRk1ConclEx p Bs X r := by
  refine ggRk1ConclEx_of_su_two_rankOne hrA hrR hF hS hXns hdvd (fun lab' hlam' hhas' => ?_)
    ⟨lab, hlam, hhas, hn⟩
  have h := NSJoin.ggLabelIso_n_eq (hRig lab lab' _ hlam hlam' hhas hhas') hA hD
  omega

end CFSG.StandardType

end
