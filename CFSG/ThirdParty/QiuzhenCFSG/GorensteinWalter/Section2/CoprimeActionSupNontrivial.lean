module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.CoprimeActionNontrivialTransfer

namespace CFSG
end CFSG
open CFSG

namespace CFSG.GorensteinWalter

universe u

/-- If `O ⊔ R` is subnormal and self-centralizing in `K`, a coprime actor
which centralizes `O` but acts nontrivially on `K` must act nontrivially on
`R`. -/
public theorem commutator_right_ne_bot_of_sup_subnormal_selfCentralizing_coprime
    {G : Type u} [Group G] [Finite G]
    (Q K O R : Subgroup G)
    (hQK : Q ≤ Subgroup.normalizer (K : Set G))
    (hOR_le_K : O ⊔ R ≤ K)
    (hsub : ((O ⊔ R).subgroupOf K).IsSubnormal)
    (hself : K ⊓ Subgroup.centralizer ((O ⊔ R : Subgroup G) : Set G) ≤ O ⊔ R)
    (hQO : Q ≤ Subgroup.centralizer (O : Set G))
    (hcop : Nat.Coprime (Nat.card Q) (Nat.card K))
    (hsolv : IsSolvable K)
    (hnontriv : ¬ Q ≤ Subgroup.centralizer (K : Set G)) :
    ⁅R, Q⁆ ≠ ⊥ := by
  intro hRQ
  have hQR : Q ≤ Subgroup.centralizer (R : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp (by
      simpa [Subgroup.commutator_comm] using hRQ)
  have hOQ : O ≤ Subgroup.centralizer (Q : Set G) :=
    Subgroup.le_centralizer_iff.mp hQO
  have hRQ' : R ≤ Subgroup.centralizer (Q : Set G) :=
    Subgroup.le_centralizer_iff.mp hQR
  have hQOR : Q ≤ Subgroup.centralizer ((O ⊔ R : Subgroup G) : Set G) :=
    Subgroup.le_centralizer_iff.mp (sup_le hOQ hRQ')
  exact hnontriv
    (centralizes_of_subnormal_selfCentralizing_coprime
      Q K (O ⊔ R) hQK hOR_le_K hsub hQOR hself hcop hsolv)

end CFSG.GorensteinWalter
