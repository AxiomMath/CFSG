module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.KSeven.Defs
import CFSG.RankThree.PartOne.FOC.PSLTwoOuter
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwoCoordinates
public import CFSG.RankThree.PartOne.S11c.Sec66TDefs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Seven

open CFSG.ComponentClassification.CatalogueSchreierLinearTwo
open CFSG.RankThree.PartOne.Sec66T (fixSub mem_fixSub innerAut)
open CFSG.RankThree.PartOne.FOC (psl_two_fixSub_equiv_gen)

private lemma ksl2f_mem_fixedBy_zpowers_iff {J : Type*} [Group J] (α : MulAut J) (x : J) :
    x ∈ fixedBy (Subgroup.zpowers α) ↔ α x = x := by
  rw [mem_fixedBy]
  refine ⟨fun h => h α (Subgroup.mem_zpowers α), fun h w hw => ?_⟩
  have h1 : w • x = x :=
    smul_eq_self_of_mem_zpowers hw (by simpa [MulAut.smul_def] using h)
  simpa [MulAut.smul_def] using h1

private lemma ksl2f_fixSub_eq_fixedBy {J : Type} [Group J] (α : MulAut J) :
    fixSub α = fixedBy (Subgroup.zpowers α) := by
  ext x
  rw [mem_fixSub, ksl2f_mem_fixedBy_zpowers_iff]

theorem exists_equiv_fixedBy_zpowers_coordinateG {T : Type} [Group T] [Finite T] {K : Type}
    [Field K] [Finite K] {ℓ f p : ℕ} (hℓ : ℓ.Prime) (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (hK : Nat.card K = ℓ ^ f) (ψ : T ≃* coordinateG K) (hpT : ¬ p ∣ Nat.card T)
    {α : MulAut T} (hord : orderOf α = p) :
    p ∣ f ∧ ∃ k : Subfield K, Nat.card k = ℓ ^ (f / p) ∧
      Nonempty (↥(fixedBy (Subgroup.zpowers α)) ≃* coordinateG ↥k) := by
  have hαinn : α ∉ innerAut T := by
    rintro ⟨t, rfl⟩
    have hdvd : orderOf (MulAut.conj t) ∣ orderOf t := orderOf_map_dvd MulAut.conj t
    rw [hord] at hdvd
    exact hpT (hdvd.trans (orderOf_dvd_natCard t))
  obtain ⟨hpf, k, hkcard, ⟨e⟩⟩ :=
    psl_two_fixSub_equiv_gen hℓ hp hp2 hf hK ψ hord hαinn
  exact ⟨hpf, k, hkcard,
    ⟨(MulEquiv.subgroupCongr (ksl2f_fixSub_eq_fixedBy α)).symm.trans e⟩⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Seven
