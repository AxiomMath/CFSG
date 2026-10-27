module

public import CFSG.RankThree.PartTwo.Sec8.Hering88Cases
public import CFSG.RankThree.PartTwo.Sec8.Item8KFactsProofOuter

public section

namespace CFSG.RankThree.PartTwo.Sec8

namespace Hering88C

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)


variable {G : Type} [Group G] [Finite G]

@[expose] def IsL2Family (Q : Type) [Group Q] (m : ℕ) : Prop :=
  (IsoTrialityD4 Q m ∨ IsoGTwoEven Q (3 * m)) ∨ IsoSUThree Q (2 ^ (3 * m)) ∨
    Nonempty (Q ≃* projSU 3 2 (3 * m)) ∨ Nonempty (Q ≃* projSp 2 (GaloisField 2 (3 * m)))

theorem mem_normalizer_residual_centralizer {Y : Subgroup G} {x d : G}
    (hxN : x ∈ Subgroup.normalizer (Y : Set G)) (hdx : d * x = x * d) :
    x ∈ Subgroup.normalizer
      (inSubgroup perfectResidual (Y ⊓ Subgroup.centralizer ({d} : Set G)) : Set G) := by
  have hxC : x ∈ Subgroup.normalizer (Subgroup.centralizer ({d} : Set G) : Set G) :=
    Subgroup.le_normalizer (Subgroup.mem_centralizer_singleton_iff.mpr hdx.symm)
  have hxYd : x ∈ Subgroup.normalizer ((Y ⊓ Subgroup.centralizer ({d} : Set G) : Subgroup G) :
      Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    rw [Subgroup.mem_inf, Subgroup.mem_inf, (Subgroup.mem_normalizer_iff.mp hxN y),
      (Subgroup.mem_normalizer_iff.mp hxC y)]
  exact CFSG.RankThree.GroupTheory.SteinbergBY.normalizer_le_normalizer_inSubgroup_perfectResidual
    _ hxYd

theorem good88_of_outer {Y : Subgroup G} {x d : G} {m : ℕ} (hm1 : 1 ≤ m) (hx3 : x ^ 3 = 1)
    (hout : Sec4.InducesOuterTheta x
      (inSubgroup perfectResidual (Y ⊓ Subgroup.centralizer ({d} : Set G))))
    (eK : imageModTheta Y (inSubgroup perfectResidual (Y ⊓ Subgroup.centralizer ({d} : Set G))) ≃*
      projSL 2 (GaloisField 2 (3 * m))) :
    Good88 Y x d := by
  have hKY : inSubgroup perfectResidual (Y ⊓ Subgroup.centralizer ({d} : Set G)) ≤ Y :=
    (Item87Proof.residual_le _).trans inf_le_left
  have hθ : NoThetaNormal (imageModTheta Y
      (inSubgroup perfectResidual (Y ⊓ Subgroup.centralizer ({d} : Set G)))) :=
    Item87Proof.NoThetaNormal.of_mulEquiv eK (Item87Proof.noThetaNormal_projSL_two (by omega))
  obtain ⟨ψ⟩ := Item87Proof.nonempty_quot_mulEquiv_imageModTheta hKY hθ
  refine ⟨LocalCores.isQuasisimple_of_mulEquiv (ψ.trans eK).symm
    (Item87Proof.isQuasisimple_projSL_two (by omega)), ⟨m, hm1, Or.inr (Or.inl ⟨ψ.trans eK⟩)⟩, ?_⟩
  obtain ⟨e⟩ := Item86ResProof.nonempty_quot_mulEquiv_psl2 hm1 eK
  exact .psl2 (GaloisField 2 (3 * m)) ⟨e, KFacts.inducesKind_field_of_pow_three _ hx3 hout e⟩

theorem inducesOuterTheta_of_l2
    (h47 : Sec4.Inputs47ClassesD4) {Y : Subgroup G} {x d : G}
    {m : ℕ} (hm : Odd m)
    (hkind : KFacts.InducesStdKind Y x .field ∨ KFacts.InducesStdKind Y x .graphField)
    (hx3 : x ^ 3 = 1) (hdx : d * x = x * d)
    (hL : IsL2Family (Y ⧸ aschbacherSolvableCore 3 Y) m)
    (eK : imageModTheta Y (inSubgroup perfectResidual (Y ⊓ Subgroup.centralizer ({d} : Set G))) ≃*
      projSL 2 (GaloisField 2 (3 * m))) :
    Sec4.InducesOuterTheta x
      (inSubgroup perfectResidual (Y ⊓ Subgroup.centralizer ({d} : Set G))) := by
  have hxN : x ∈ Subgroup.normalizer (Y : Set G) := by
    rcases hkind with h | h
    · exact h.mem_normalizer
    · exact h.mem_normalizer
  by_contra hnot
  obtain ⟨k', hk'L, hk'a, hk'3, hle⟩ :=
    Item86ResProof.Item8KFactsOuter.exists_twist_of_not_outer hm.pos hxN
      (mem_normalizer_residual_centralizer hxN hdx) hx3 eK hnot
  exact Item86ResProof.Item8KFactsOuter.false_of_twist h47 hm hkind hx3 hk'L hk'a hk'3 eK hle hL

theorem good88_of_l2
    (h47 : Sec4.Inputs47ClassesD4) {Y : Subgroup G} {x d : G}
    {m : ℕ} (hm : Odd m)
    (hkind : KFacts.InducesStdKind Y x .field ∨ KFacts.InducesStdKind Y x .graphField)
    (hx3 : x ^ 3 = 1) (hdx : d * x = x * d)
    (hL : IsL2Family (Y ⧸ aschbacherSolvableCore 3 Y) m)
    (eK : imageModTheta Y (inSubgroup perfectResidual (Y ⊓ Subgroup.centralizer ({d} : Set G))) ≃*
      projSL 2 (GaloisField 2 (3 * m))) :
    Good88 Y x d :=
  good88_of_outer hm.pos hx3 (inducesOuterTheta_of_l2 h47 hm hkind hx3 hdx hL eK) eK

end Hering88C

end CFSG.RankThree.PartTwo.Sec8
