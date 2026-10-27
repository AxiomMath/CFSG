module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Classification
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.Definitions

namespace CFSG
end CFSG
open CFSG

/-!
# Quotient by the prime-to-p core under a normal p-complement

Glauberman's `NormalPComplement` condition says that `O_{p',p}(G)` is all of
`G`.  Mapping this equality to `G/O_{p'}(G)` identifies its `p`-core with the
top subgroup, so the quotient is a `p`-group.
-/

namespace CFSG.GorensteinWalter

universe u

/-- A group satisfying Glauberman's normal-`p`-complement condition has
`p`-group quotient by its prime-to-`p` core. -/
public theorem isPGroup_quotient_pPrimeCore_of_normalPComplement
    {p : ℕ} [Fact p.Prime]
    {G : Type u} [Group G] [Finite G]
    (hNPC : Glauberman.NormalPComplement p G) :
    IsPGroup p (G ⧸ pPrimeCore p G) := by
  let Q := G ⧸ pPrimeCore p G
  let q : G →* Q := QuotientGroup.mk' (pPrimeCore p G)
  have hOp : Op_p'p p G = ⊤ := Glauberman.normalPComplement_eq_top hNPC
  have hmap : (Op_p'p p G).map q = pCore p Q := by
    dsimp [Op_p'p, q, Q]
    exact Subgroup.map_comap_eq_self_of_surjective
      (QuotientGroup.mk'_surjective (pPrimeCore p G)) (pCore p Q)
  have hpcore : pCore p Q = ⊤ := by
    rw [hOp] at hmap
    rw [Subgroup.map_top_of_surjective q
      (QuotientGroup.mk'_surjective (pPrimeCore p G))] at hmap
    exact hmap.symm
  have htop : IsPGroup p (⊤ : Subgroup Q) := by
    rw [← hpcore]
    exact pCore_isPGroup
  exact htop.of_equiv Subgroup.topEquiv

end CFSG.GorensteinWalter
