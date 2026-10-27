module

public import CFSG.LocalAnalysis.StandardType.GGPhiTwoGenHyper
public import CFSG.LocalAnalysis.StandardType.GGPhiTwoGenInput

public section

namespace CFSG.StandardType.PhiTwoRootGen

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley Multiplicative
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

theorem iSup_le_iSup_phiTwoCompIn_of_hyperplane_family
    {τ : Tag} (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8 ∨ τ = .F4) {K : Type} [Field K] {p : ℕ}
    [Fact p.Prime] (hp2 : p ≠ 2) {g0 : ModGL τ (AlgebraicClosure K)}
    (hg0C : g0 ∈ adjointGroup τ (AlgebraicClosure K)) {ζ : (AlgebraicClosure K)ˣ}
    (hζo : orderOf ζ = p) (hζ : ζ ^ p = 1)
    {R : Subgroup (ModGL τ K)} (hR : R ≤ adjointGroup τ K)
    {T : Multiplicative (Fin τ.rank → ZMod p) →* ↥R}
    (hT : ∀ t : Fin τ.rank → ZMod p,
      baseChangeGL (algebraMap K (AlgebraicClosure K)) ((T (ofAdd t) : ↥R) : ModGL τ K) =
        g0 * rootDiagUnit τ (TableBExc.E6Three.zetaVec ζ hζ t) * g0⁻¹)
    {ι : Type} (S : ι → Subgroup ↥R) (hperf : ∀ i, ⁅S i, S i⁆ = S i)
    (hhyp : ∀ i, ∃ V : Set (Fin τ.rank → ZMod p), V.ncard = p ^ (τ.rank - 1) ∧
      ∀ x ∈ S i, ∀ t ∈ V, x * T (ofAdd t) = T (ofAdd t) * x) :
    (⨆ i, S i) ≤ ⨆ γ : {γ : Fin τ.rank → ℤ // IsRoot τ γ}, phiTwoCompIn R g0 γ.1 := by
  refine iSup_le fun i => ?_
  obtain ⟨V, hVcard, hVcent⟩ := hhyp i
  let incl : ↥R →* ↥(adjointGroup τ K) := Subgroup.inclusion hR
  have hT' : ∀ t : Fin τ.rank → ZMod p,
      baseChangeGL (algebraMap K (AlgebraicClosure K))
          (((incl.comp T) (ofAdd t) : ↥(adjointGroup τ K)) : ModGL τ K) =
        g0 * rootDiagUnit τ (TableBExc.E6Three.zetaVec ζ hζ t) * g0⁻¹ := fun t => hT t
  have hperf' : ⁅(S i).map incl, (S i).map incl⁆ = (S i).map incl := by
    rw [← Subgroup.map_commutator, hperf i]
  have hP' : ∀ x ∈ (S i).map incl, ∀ t ∈ V,
      x * (incl.comp T) (ofAdd t) = (incl.comp T) (ofAdd t) * x := by
    rintro _ ⟨y, hy, rfl⟩ t ht
    have h := hVcent y hy t ht
    simp only [MonoidHom.comp_apply]
    rw [← map_mul, ← map_mul, h]
  obtain ⟨α, hαroot, hle⟩ := exists_isRoot_perfect_le_phiTwoComp hτ hp2 hg0C hζo hζ hT' hVcard
    hperf' hP'
  refine le_trans ?_ (le_iSup
    (fun γ : {γ : Fin τ.rank → ℤ // IsRoot τ γ} => phiTwoCompIn R g0 γ.1) ⟨α, hαroot⟩)
  intro x hx
  rw [mem_phiTwoCompIn_iff]
  have hxP : incl x ∈ (S i).map incl := ⟨x, hx, rfl⟩
  have h := hle hxP
  rw [mem_phiTwoComp_iff] at h
  exact h

end CFSG.StandardType.PhiTwoRootGen

end
