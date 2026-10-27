module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight105KFacts
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight105KRadModels
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight105KRadTransport
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight105KTorusAbelian
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight102KTypesHolds
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight102KTypesCore
public import CFSG.CGT.Timmesfeld75.Statements
public import CFSG.Foundations
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LBalanceComponentLifts
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.ComponentInitial.LayerComponentOrbit
public import CFSG.LocalAnalysis.RankThreeUC.Asc1930
public import CFSG.Quasithin.Background.A1bGroups
public import CFSG.RankThree.PartOne.S10.ThetaContract
public import CFSG.RankThree.PartOne.S12.InputsBase

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped Pointwise

private theorem exists_notationB8103_of_conj {X : Type} [Group X] [Finite X]
    {S Sstar Bstar : Subgroup X} {n : ℕ} {g : X}
    (hBstar : F08.NotationB8103 ⊤ Sstar n Bstar)
    (hSg : Sstar.map (MulAut.conj g).toMonoidHom = S) :
    F08.NotationB8103 ⊤ S n (Bstar.map (MulAut.conj g).toMonoidHom) := by
  have hB'le : Bstar.map (MulAut.conj g).toMonoidHom ≤ S := by
    rw [← hSg]
    exact Subgroup.map_mono hBstar.2.1
  have hBtop : F08.NotationB8103 ⊤ ⊤ n Bstar := ⟨hBstar.1, le_top, hBstar.2.2⟩
  have hB'top : F08.NotationB8103 ⊤ ⊤ n (Bstar.map (MulAut.conj g).toMonoidHom) :=
    (KTypes.notationB8103_map_conj_iff (L := ⊤) (B := Bstar) (g := g)
      (mem_top g) le_top).mpr hBtop
  exact ⟨hB'top.1, hB'le, hB'top.2.2⟩

private theorem exists_radical_overgroups_of_radicalFacts {X : Type} [Group X] [Finite X]
    {S B₀ : Subgroup X} (hB₀S : B₀ ≤ S)
    (hcomm : ∀ a ∈ S, ∀ b ∈ S, a * b = b * a) (h : K105.RadicalFacts X B₀) :
    ∃ Y₁ Y₂ : Subgroup X,
      (∀ Y ∈ ({Y₁, Y₂} : Set (Subgroup X)),
        Y ≠ ⊤ ∧ (∃ T₀ : Sylow 2 X, normalizer ((T₀ : Subgroup X) : Set X) ≤ Y) ∧
          F08.KOf8103 ⊤ B₀ ⊔ S ≤ Y ∧ pCoreOf 2 Y ≠ ⊥ ∧
          F08.KOf8103 ⊤ B₀ ⊓ pCoreOf 2 Y = ⊥ ∧
          ∀ T₀ : Sylow 2 X, pCoreOf 2 Y ≤ (T₀ : Subgroup X) →
            normalizer ((T₀ : Subgroup X) : Set X) ≤ Y) ∧
      pCoreOf 2 Y₁ ⊓ Y₂ = ⊥ ∧ pCoreOf 2 Y₂ ⊓ Y₁ = ⊥ ∧
      ∀ Z : Subgroup X, Z ≠ ⊤ →
        (∃ T₀ : Sylow 2 X, normalizer ((T₀ : Subgroup X) : Set X) ≤ Z) →
          F08.KOf8103 ⊤ B₀ ⊔ S ≤ Z → Z = Y₁ ∨ Z = Y₂ := by
  obtain ⟨Y₁, Y₂, hY, hY₁, hY₂, hZ⟩ := h
  have hKcent : F08.KOf8103 ⊤ B₀ ≤ centralizer (B₀ : Set X) := by
    rw [F08.KOf8103]
    exact (Subgroup.map_subtype_le _).trans inf_le_right
  have hScent : S ≤ centralizer (B₀ : Set X) := by
    intro s hs
    rw [Subgroup.mem_centralizer_iff]
    exact fun b hb => hcomm b (hB₀S hb) s hs
  refine ⟨Y₁, Y₂, ?_, hY₁, hY₂, ?_⟩
  · intro Y hY'
    obtain ⟨hne, hN, hcent, hp, hKi, hNs⟩ := hY Y hY'
    exact ⟨hne, hN, sup_le (hKcent.trans hcent) (hScent.trans hcent), hp, hKi, hNs⟩
  · intro Z hZne hN hKZ
    exact hZ Z hZne hN (sup_le (le_sup_left.trans hKZ) ((hB₀S.trans le_sup_right).trans hKZ))

theorem kU45Radical_holds : KU45Radical := by
  intro X _ _ n hX S hS hSi B₀ hB₀
  obtain ⟨Sstar, Bstar, hSstar, hSstari, hBstar, hRF⟩ :=
    K105.exists_radicalFacts_of_isU45 hX
  have h2 : 2 ^ n + 1 ≠ 1 := by
    have hpos : 0 < 2 ^ n := pow_pos (by norm_num) n
    omega
  obtain ⟨p, hp, hpn⟩ := Nat.exists_prime_and_dvd h2
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq X (hSstar.toSylow hSstari) (hS.toSylow hSi)
  have hSg : Sstar.map (MulAut.conj g).toMonoidHom = S := by
    have hcoe : ((hS.toSylow hSi : Sylow 3 X) : Subgroup X) =
        MulAut.conj g • ((hSstar.toSylow hSstari : Sylow 3 X) : Subgroup X) := by
      conv_lhs => rw [← hg]
      rfl
    rw [Subgroup.pointwise_smul_def] at hcoe
    exact hcoe.symm
  have hB'not : F08.NotationB8103 ⊤ S n (Bstar.map (MulAut.conj g).toMonoidHom) :=
    exists_notationB8103_of_conj hBstar hSg
  obtain ⟨x, hx⟩ :=
    (kU45Types_holds X n hX p hp hpn S hS hSi).2.2.2.2
      (Bstar.map (MulAut.conj g).toMonoidHom) B₀ hB'not hB₀
  have hB₀eq : B₀ = Bstar.map (MulAut.conj (x * g)).toMonoidHom := by
    rw [hx, Subgroup.map_map]
    congr 1
    ext y
    simp [MulAut.conj_apply, mul_assoc]
  have hRF₀ : K105.RadicalFacts X B₀ := by
    rw [hB₀eq]
    exact K105.RadicalFacts.of_mulEquiv (MulAut.conj (x * g)) hBstar.1 hRF
  exact exists_radical_overgroups_of_radicalFacts hB₀.2.1
    (K105.sylow_three_comm hX hS hSi) hRF₀

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
