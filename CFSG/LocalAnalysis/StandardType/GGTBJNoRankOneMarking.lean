module

public import CFSG.LocalAnalysis.StandardType.GGTBJNoRankOneDefs
public import CFSG.LocalAnalysis.StandardType.GGOneFiveDefs
import CFSG.LocalAnalysis.StandardType.GGTBJNoRankOneSetup

public section

namespace CFSG.StandardType

open CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem ggRankOne_marking {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hcfg : GGConfig p B Bs x L D J) {n : ℕ} (hn : 2 ≤ n)
    (hJ : GGHasLabel (⟨.A, 1, n⟩ : LargeEvenLabel) (↥J ⧸ Subgroup.center ↥J))
    {P' : LargeEvenLabel → LargeEvenRawCont}
    (hall : ∀ lab, LargeEvenInLambda2 lab → LargeEvenLabelAll lab (P' lab)) :
    ∃ (lab : LargeEvenLabel) (R : Type) (_ : Group R) (I F : Set (MulAut R))
      (θ : ↥L ⧸ Subgroup.center ↥L ≃* R) (e a : MulAut ↥L) (J' : Subgroup ↥L)
      (A : Subgroup (MulAut ↥L)),
      LargeEvenInLambda2 lab ∧ GGHasLabel lab (↥L ⧸ Subgroup.center ↥L) ∧ P' lab R I F ∧
      commutator ↥L = ⊤ ∧
      GGRankOneSetup I (θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥L))) p e J' n a ∧
      IsElemAbelian p A ∧ Nat.card A * p = Nat.card B ∧ e ∈ A ∧ a ∈ A ∧
      (∀ c ∈ A, ∃ b ∈ B, ∀ l : ↥L, ((c l : ↥L) : G) = b * l * b⁻¹) ∧
      (∀ c ∈ A, ∃ φ ∈ I, ∀ l : ↥L, φ (θ (QuotientGroup.mk l)) = θ (QuotientGroup.mk (c l))) ∧
      (∀ c ∈ A, ∀ j ∈ J', c j ∈ J') := by
  classical
  obtain ⟨e, a, J', A, he1, hep, hcomp, hlabJ, hae, haJ, hanon, hAelem, hAcard, heA, haA,
    hAb, hAJ⟩ := ggRankOne_setup hcfg hn hJ
  have hst : LargeEvenStandardType p B x L := hcfg.1.2.2.2.2.2.2.2
  obtain ⟨hLperf, lab, hlab2, hraw⟩ := hst.1
  have hrawP := (hall lab hlab2) _ hraw
  obtain ⟨R, hRgrp, I, F, hQ, hP'⟩ := largeEvenRawDatum_exists hrawP
  obtain ⟨-, -, θ, -, -, hInd⟩ := hQ
  have hp : p.Prime := hcfg.1.2.2.2.2.2.1.1
  have hp2 : p ≠ 2 := hcfg.1.2.2.2.2.2.1.2.1
  have hGG : GGHasLabel lab (↥L ⧸ Subgroup.center ↥L) :=
    largeEvenRawDatum_mono (fun R _ I F h => by obtain ⟨-, -, θ, -⟩ := h; exact ⟨θ⟩) hraw
  let ψ : ↥L →* R := θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥L))
  have hAI : ∀ c ∈ A, ∃ φ ∈ I, ∀ l : ↥L,
      φ (θ (QuotientGroup.mk l)) = θ (QuotientGroup.mk (c l)) := by
    intro c hc
    obtain ⟨b, hbB, hb⟩ := hAb c hc
    obtain ⟨φ, hφI, hφind⟩ := hInd b⁻¹ (B.inv_mem hbB)
    refine ⟨φ, hφI, fun l => ?_⟩
    have hrel : ((c l : ↥L) : G) = (b⁻¹)⁻¹ * (l : G) * b⁻¹ := by
      rw [hb l]
      simp
    simpa using hφind l (c l) hrel
  have hIndE : ∃ φ ∈ I, ∀ l : ↥L, φ (ψ l) = ψ (e l) := by
    obtain ⟨φ, hφI, hφ⟩ := hAI e heA
    exact ⟨φ, hφI, fun l => by simpa [ψ] using hφ l⟩
  have hIndA : ∃ φ ∈ I, ∀ l : ↥L, φ (ψ l) = ψ (a l) := by
    obtain ⟨φ, hφI, hφ⟩ := hAI a haA
    exact ⟨φ, hφI, fun l => by simpa [ψ] using hφ l⟩
  have hSetup : GGRankOneSetup I ψ p e J' n a :=
    ⟨hp, hp2, he1, hep, hIndE, hcomp, hn, hlabJ, hae, hIndA, haJ, hanon⟩
  exact ⟨lab, R, hRgrp, I, F, θ, e, a, J', A,
    ⟨hlab2, hGG, hP', hLperf, hSetup, hAelem, hAcard, heA, haA, hAb, hAI, hAJ⟩⟩

end CFSG.StandardType

end
