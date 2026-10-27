module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Classification

namespace CFSG
end CFSG
open CFSG

/-!
# Abelian Sylow 2-subgroups centralize normalized 2-subgroups

If an involution normalizes a `2`-subgroup, their join is again a
`2`-subgroup.  In a group with abelian Sylow `2`-subgroups that join embeds
in an abelian Sylow subgroup, forcing centralization.
-/

namespace CFSG.GorensteinWalter

universe u

/-- In a finite group with abelian Sylow `2`-subgroups, an involution
centralizes every `2`-subgroup that it normalizes. -/
public theorem twoSubgroup_le_centralizer_involution_of_hasAbelianSylow
    {X : Type u} [Group X] [Finite X]
    (N : Subgroup X)
    (hSylow : ∀ S : Sylow 2 X, IsMulCommutative (S : Subgroup X))
    (hNtwo : IsPGroup 2 N)
    {t : X} (ht : IsInvolution t)
    (htnormN : t ∈ Subgroup.normalizer (N : Set X)) :
    N ≤ Subgroup.centralizer ({t} : Set X) := by
  have htOrder : orderOf t = 2 := orderOf_eq_prime ht.2 ht.1
  have hTtwo : IsPGroup 2 (Subgroup.zpowers t) := by
    refine IsPGroup.of_card (p := 2) (G := Subgroup.zpowers t) (n := 1) ?_
    rw [Nat.card_zpowers, htOrder, pow_one]
  have hTnormN : Subgroup.zpowers t ≤ Subgroup.normalizer (N : Set X) :=
    Subgroup.zpowers_le.mpr htnormN
  have hjoinTwo : IsPGroup 2 (Subgroup.zpowers t ⊔ N : Subgroup X) :=
    IsPGroup.to_sup_of_normal_right' hTtwo hNtwo hTnormN
  obtain ⟨S, hjoinS⟩ := hjoinTwo.exists_le_sylow
  let : IsMulCommutative (S : Subgroup X) := hSylow S
  intro n hn
  apply Subgroup.mem_centralizer_singleton_iff.mpr
  have hnS : n ∈ (S : Subgroup X) :=
    hjoinS (Subgroup.mem_sup_right hn)
  have htS : t ∈ (S : Subgroup X) :=
    hjoinS (Subgroup.mem_sup_left (Subgroup.mem_zpowers t))
  have hcommS :
      (⟨n, hnS⟩ : S) * ⟨t, htS⟩ =
        (⟨t, htS⟩ : S) * ⟨n, hnS⟩ :=
    (IsMulCommutative.is_comm (M := (S : Subgroup X))).comm _ _
  exact congrArg Subtype.val hcommS

end CFSG.GorensteinWalter
