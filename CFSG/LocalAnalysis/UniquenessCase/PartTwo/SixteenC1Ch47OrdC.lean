module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1Forty7aCommon
import CFSG.LocalAnalysis.UniquenessCase.UC22P22f
import CFSG.LocalAnalysis.UniquenessCase.UC22P22nA
import CFSG.Quasithin.Vol2.Ch12Sec2Lem22C
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem s16c1_V₀_inter_conj_ne_bot (D : Data G) {V₀ V : Subgroup G} (hV : IsElemAbelian 2 V)
    (hle : V₀ ≤ V) (hV₀M : V₀ ≤ D.M) (hM₀ : D.M ≤ normalizer (V₀ : Set G)) (hne : V₀ ≠ ⊥)
    {z : G} (hz : z ∈ V) (hz1 : z ≠ 1)
    (hSyl : IsSylowIn 2 (D.T ⊓ centralizer ({z} : Set G)) (centralizer ({z} : Set G))) {h : G}
    (hh : h ∈ centralizer ({z} : Set G)) :
    V₀ ⊓ conjSubgroup D.M h ≠ ⊥ ∧ conjSubgroup V₀ h ⊓ D.M ≠ ⊥ := by
  let H := centralizer ({z} : Set G)
  let Q := pCoreOf 2 H
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hz2 : z ^ 2 = 1 := by simpa using hV.2 z hz
  have hchar : CFSG.QuasithinUnique.CharTwo H :=
    D.standing.charTwo H (uc22p22f_isTwoLocal_centralizer hz1 hz2)
  have hV₀pg : IsPGroup 2 V₀ := fun y =>
    ⟨1, Subtype.ext (by simpa using hV.2 (y : G) (hle y.2))⟩
  have hV₀T : V₀ ≤ D.T :=
    uc22p22na_le_sylow_of_normal D.sylowM hV₀M hM₀ hV₀pg
  have hT₀ : D.T ≤ normalizer (V₀ : Set G) := D.sylowM.le.trans hM₀
  obtain ⟨c, hcV₀, hc1, hcT⟩ :=
    CFSG.Quasithin.H13.Lem22.exists_ne_one_mem_centralizer D.sylowM.isPGroup hV₀T hT₀ hne
  have hcH : c ∈ H := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff.1 hy]
    exact IsElemAbelian.comm hV hz (hle hcV₀)
  have hQS : Q ≤ D.T ⊓ H := CFSG.Quasithin.pCoreOf_le_of_isSylowIn hSyl
  have hcent : c ∈ Subgroup.centralizer (Q : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro r hr
    exact Subgroup.mem_centralizer_iff.1 hcT r (hQS hr).1
  have hcQ : c ∈ Q := hchar (Subgroup.mem_inf.2 ⟨hcH, hcent⟩)
  have hQM : Q ≤ D.M := s16c1_pCoreOf_le_M D hSyl
  have hQh : conjSubgroup Q h = Q := s16c1_conjSubgroup_pCoreOf_self H hh
  have hchQ : h * c * h⁻¹ ∈ Q := mem_conjSubgroup_iff.mp (hQh.symm ▸ hcQ)
  have hchM : h * c * h⁻¹ ∈ D.M := hQM hchQ
  have hcConj : c ∈ conjSubgroup D.M h := by
    rw [mem_conjSubgroup_iff]
    exact hchM
  have hfirst : V₀ ⊓ conjSubgroup D.M h ≠ ⊥ := by
    intro hbot
    have hmem : c ∈ V₀ ⊓ conjSubgroup D.M h := Subgroup.mem_inf.2 ⟨hcV₀, hcConj⟩
    rw [hbot] at hmem
    exact hc1 (Subgroup.mem_bot.1 hmem)
  have hQh' : conjSubgroup Q h⁻¹ = Q :=
    s16c1_conjSubgroup_pCoreOf_self H (H.inv_mem hh)
  have hc'Q : h⁻¹ * c * h ∈ Q := by
    have h := mem_conjSubgroup_iff.mp (hQh'.symm ▸ hcQ)
    simpa using h
  have hc'M : h⁻¹ * c * h ∈ D.M := hQM hc'Q
  have hc'1 : h⁻¹ * c * h ≠ 1 := by
    intro h1
    apply hc1
    calc c = h * (h⁻¹ * c * h) * h⁻¹ := by group
      _ = 1 := by rw [h1]; group
  have hc'Conj : h⁻¹ * c * h ∈ conjSubgroup V₀ h := by
    rw [mem_conjSubgroup_iff]
    have hc : h * (h⁻¹ * c * h) * h⁻¹ = c := by group
    rw [hc]
    exact hcV₀
  have hsecond : conjSubgroup V₀ h ⊓ D.M ≠ ⊥ := by
    intro hbot
    have hmem : h⁻¹ * c * h ∈ conjSubgroup V₀ h ⊓ D.M :=
      Subgroup.mem_inf.2 ⟨hc'Conj, hc'M⟩
    rw [hbot] at hmem
    exact hc'1 (Subgroup.mem_bot.1 hmem)
  exact ⟨hfirst, hsecond⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
