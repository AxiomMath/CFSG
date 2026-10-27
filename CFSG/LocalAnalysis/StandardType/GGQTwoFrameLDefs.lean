module

public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSPosDefs
public import CFSG.ClassicalInvolution.Phan.Defs

public section

namespace CFSG.StandardType.QTwo

open CFSG.StandardType CFSG.ClassicalInvolution.Phan

variable {G : Type} [Group G] [Finite G]

structure QTwoFrameL (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G) where
  F0 : Type
  [fieldF0 : Field F0]
  [finiteF0 : Finite F0]
  [charF0 : CharP F0 2]
  [factF0 : Fact (Nat.Prime 2)]
  hcardF0 : Nat.card F0 = 4
  m : ℕ
  hm : 5 ≤ m
  L0 : Type
  [groupL0 : Group L0]
  [finiteL0 : Finite L0]
  c : ↥L →* L0
  hc_surj : Function.Surjective c
  hc_ker : c.ker ≤ Subgroup.center ↥L
  hc_two : IsPGroup 2 c.ker
  πSU : Su F0 2 1 m →* L0
  hπ_surj : Function.Surjective πSU
  hπ_ker : πSU.ker ≤ Subgroup.center (Su F0 2 1 m)
  ρ : ↥Bs →* MulAut L0
  hdiag : ∀ b : ↥Bs, ∃ g : GL (Fin m) F0, ggIsDiagMat g ∧
    ∀ u : Su F0 2 1 m, ∃ u' : Su F0 2 1 m,
      (u' : GL (Fin m) F0) = g * (u : GL (Fin m) F0) * g⁻¹ ∧ ρ b (πSU u) = πSU u'
  hBsN : Bs ≤ Subgroup.normalizer (L : Set G)
  hρ_induced : ∀ (b : ↥Bs) (l : ↥L),
    c ⟨(b : G) * l * (b : G)⁻¹,
        (Subgroup.mem_normalizer_iff.mp (hBsN b.2) l).mp l.2⟩ = ρ b (c l)


end CFSG.StandardType.QTwo

end
