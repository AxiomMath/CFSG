module

public import CFSG.RankThree.PartOne.KE.SigmaUntwisted2
public import CFSG.RankThree.PartOne.KE.CommutatorFactor
public import CFSG.RankThree.PartOne.KE.A2Family
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs

public noncomputable section

namespace CFSG.RankThree.PartOne.KE

open Matrix CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.Chevalley CFSG.RankThree.Lattice
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

theorem e8_perx_core {K : Type} [Field K] [Finite K] {L : Type} [Field L] [Algebra K L]
    (Fr : L →+* L) (hFr : ∀ c, Fr c = c ^ Nat.card K) (n g0 : ModGL .E8 L)
    (hg0C : g0 ∈ adjointGroup .E8 L) (hg0 : Units.map (entrywiseHom Fr) g0 = g0 * n)
    (hperf : ∀ P : Subgroup (ModGL .E8 L), Finite P → P ≤ adjointGroup .E8 L →
      (∀ x ∈ P, Units.map (entrywiseHom Fr) x = x) → ⁅P, P⁆ = P →
        P ≤ (adjEmb .E8 K L).range)
    {p : ℕ} (hp : p.Prime) (hordW : ¬ p ∣ Nat.card (WeylGroup .E8))
    {x : adjointGroup .E8 K} (hx : orderOf x = p) (c : adjointGroup .E8 K)
    {b : Fin Tag.E8.rank → Lˣ}
    (hbh : rootDiagUnit .E8 b = g0⁻¹ * adjEmb .E8 K L (c * x * c⁻¹) * g0)
    (hh : g0⁻¹ * adjEmb .E8 K L (c * x * c⁻¹) * g0 ∈
      twistedTorusOf n (Units.map (entrywiseHom Fr)))
    {S : Set (Fin Tag.E8.rank → ℤ)} (hSeq : rootCharKernel b = S)
    (hS : ∀ α ∈ S, IsRoot .E8 α) (hSn : ∀ α ∈ S, -α ∈ S)
    {ι' : Type} {P : ι' → Subgroup (ModGL .E8 L)} (hfam : IsSigmaFamily n Fr S P) :
    ∃ ψ : Subgroup.centralizer ({x} : Set (adjointGroup .E8 K)) →* ModGL .E8 L,
      Function.Injective ψ ∧
      (∀ y, ψ y = g0⁻¹ * adjEmb .E8 K L (c * (y : adjointGroup .E8 K) * c⁻¹) * g0) ∧
      (∀ y, ψ y ∈ torusGroup .E8 L ⊔ rootSpan .E8 L S) ∧
      (∀ y, n * Units.map (entrywiseHom Fr) (ψ y) * n⁻¹ = ψ y) ∧
      (∀ y, ψ y ∈ adjointGroup .E8 L) ∧ (∀ i, P i ≤ ψ.range) ∧
      ∀ V : Subgroup (Subgroup.centralizer ({x} : Set (adjointGroup .E8 K))), V.Normal →
        Group.IsSolvable V → ∀ v ∈ V, ψ v ∈ subtorusSigma n (Units.map (entrywiseHom Fr)) S := by
  classical
  obtain ⟨hPfin, hPq, hPQ, hPR, hPadj, hPnorm, hPcent⟩ := hfam
  have hsub : S ⊆ rootCharKernel b := fun α hα => by rw [hSeq]; exact hα
  have hle := rootSpan_le_centralizer (K := L) b hsub
  have hcS : c * x * c⁻¹ ∈ subtorusImage (adjEmb .E8 K L) g0
      (subtorusSigma n (Units.map (entrywiseHom Fr)) S) := by
    rw [mem_subtorusImage_iff]
    refine Subgroup.mem_inf.2 ⟨hh, Subgroup.mem_centralizer_iff.2 fun g hg => ?_⟩
    have h1 := Subgroup.mem_centralizer_singleton_iff.1 (hle hg)
    rw [hbh] at h1
    exact h1
  have hkerZ : ∀ a : Fin Tag.E8.rank → Lˣ,
      rootDiagUnit .E8 a = g0⁻¹ * adjEmb .E8 K L (c * x * c⁻¹) * g0 → rootCharKernel a ⊆ S :=
    fun a ha => by
      have : a = b := rootDiagUnit_injective (ha.trans hbh.symm)
      rw [this, hSeq]
  exact sigma_embedding_data (adjEmb .E8 K L) adjEmb_injective adjEmb_mem
    (Units.map (entrywiseHom Fr)) (adjEmb_frobenius Fr hFr) n g0 hg0C hg0 hperf hp hordW hS hSn P
    hPfin hPq hPQ hPR hPadj hPnorm hPcent hx c hcS hkerZ

theorem e8_perx_commutator {D L : Type} [Group D] [Field L]
    (Fr : L →+* L) (n : ModGL .E8 L) {S : Set (Fin Tag.E8.rank → ℤ)}
    (hS : ∀ α ∈ S, IsRoot .E8 α) (ψ : D →* ModGL .E8 L)
    (hψHQ : ∀ y, ψ y ∈ torusGroup .E8 L ⊔ rootSpan .E8 L S)
    (hψR : ∀ y, n * Units.map (entrywiseHom Fr) (ψ y) * n⁻¹ = ψ y)
    {P : Subgroup (ModGL .E8 L)}
    (hP1 : P = rootSpan .E8 L S ⊓ twistedFixedPoints n (Units.map (entrywiseHom Fr)))
    (hPψ : P ≤ ψ.range) (hPq : CFSG.IsQuasisimple P) : ⁅ψ.range, ψ.range⁆ = P := by
  refine commutator_range_eq_of_family ψ (H := torusGroup .E8 L) (Q := rootSpan .E8 L S)
    (R := twistedFixedPoints n (Units.map (entrywiseHom Fr))) ?_ ?_ hψHQ
    (fun y => mem_twistedFixedPoints.2 (hψR y)) hP1 hPψ ?_
  · exact torusGroup_le_normalizer_rootSpan hS
  · intro a ha a' ha'
    obtain ⟨b₁, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup ha
    exact rootDiagUnit_mul_comm_of_mem_torusGroup b₁ ha'
  · exact Subgroup.isPerfect_iff.1 hPq.1

end CFSG.RankThree.PartOne.KE
