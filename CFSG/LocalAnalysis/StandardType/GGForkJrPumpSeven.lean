module

public import CFSG.LocalAnalysis.StandardType.GGForkJrPumpDefs
public import CFSG.LocalAnalysis.StandardType.GGNbrMarkingLabel
public import CFSG.LocalAnalysis.StandardType.GGNbrHalfSplitArith
public import CFSG.LocalAnalysis.StandardType.GGNbrReflGenTables
public import CFSG.LocalAnalysis.StandardType.GGSixLayerCXNonsplitMarking
public import CFSG.LocalAnalysis.StandardType.GGNbrPrimeFieldExcl

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

section Transfer

variable {G : Type} [Group G] [Finite G]

theorem ggNbr_latticeLabel_or_seven (hRig : GGLabelRigidInput) (hraw : GGRawInnFieldInput)
    (hiso : GGRawInndiagIsoInput) {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hcfg : GGConfig p B Bs x L D J) (hInn : GGInnerDiagAll p B Bs x L D J) (hp5 : 5 ≤ p)
    {y : G} {K : Subgroup G} (hnb : GGNbr p B x D J y K) :
    GGInnerDiagOnLabel GGForkLatticeLabel p Bs K ∨ GGInnerDiagOnLabel GGForkE6TwoLabel p Bs K ∨
      (p = 7 ∧ GGHasLabel ⟨.A, 8, 1⟩ (↥K ⧸ Subgroup.center ↥K)) := by
  have hInnK : GGInnerDiagOn Bs K := hInn.2 y K hnb
  have hp : p.Prime := hcfg.1.2.2.2.2.2.1.1
  have hp2 : p ≠ 2 := hcfg.1.2.2.2.2.2.1.2.1
  have hxBs : x ∈ Bs := hcfg.2.1.1 hcfg.1.2.2.2.2.2.2.1.2.1
  have h5 : GGNbrClauseFiveMarking p x K :=
    (hcfg.1.2.2.2.2.2.2.2.2.2.1 y K ⟨hnb.1, D, J, hcfg.2.2, hnb.2⟩).2
  have hhalf : LargeEvenMarking ↥K fun lab _ _ _ _ _ =>
      LargeEvenHalfSplit p lab (Subgroup.center ↥K = ⊥) := by
    rcases largeEvenMarking_or h5 with hh | hh
    · exact hh
    · exact absurd hh (ggNbr_not_primeField hraw hiso hp hp2 hxBs hInnK)
  obtain ⟨lab, hlab, hhas, R, _, I, F, θ, hH⟩ := largeEvenMarking_exists_hasLabel hhalf
  have hmark := ggInnerDiagOn_relabel hRig hInnK hlab hhas
  have key : ∀ S : ℕ → LargeEvenLabel → Prop, S p lab → GGInnerDiagOnLabel S p Bs K := by
    intro S hS
    refine largeEvenMarking_mono ?_ hmark
    rintro lab' R' _ I' F' θ' ⟨h1, h2, h3⟩
    subst h1
    exact ⟨hS, h2, h3⟩
  rcases largeEvenHalfSplit_dvd hlab hH with hdvd | ⟨hp7, hlab7⟩
  · have h4 : (2 ^ lab.n) ^ 2 = 4 ^ lab.n := by
      rw [← pow_mul, mul_comm, pow_mul]
      norm_num
    have hdvd' : p ∣ 4 ^ lab.n - 1 := h4 ▸ hdvd
    have hn1 : lab.n ≠ 1 := by
      intro hn
      have hle : p ≤ 3 := by
        have hdvd1 : p ∣ (2 ^ 1) ^ 2 - 1 := by rwa [hn] at hdvd
        have h := Nat.le_of_dvd (by norm_num) hdvd1
        norm_num at h
        exact h
      omega
    have h2n : 2 ≤ lab.n := Nat.succ_le_of_lt (Nat.lt_of_le_of_ne hlab.1 (Ne.symm hn1))
    exact Or.inl (key GGForkLatticeLabel ⟨hp5, h2n, hdvd'⟩)
  · rcases hlab7 with hlab7 | hlab7
    · exact Or.inr (Or.inr ⟨hp7, hlab7 ▸ hhas⟩)
    · exact Or.inr (Or.inl (key GGForkE6TwoLabel ⟨hp7, hlab7⟩))

end Transfer

end CFSG.StandardType
