module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section10Proposition102Fitting

namespace CFSG
end CFSG
open CFSG

/-!
# Section 11, Proposition 11.1: nilpotent product core

This module isolates the source-independent centralization step in `(11A)`.
Inside a finite nilpotent group, a Sylow `r`-subgroup centralizes every normal
`r'`-subgroup.  The proof uses the checked internal direct-product
decomposition into the `r`-core and the `r'`-core.
-/

noncomputable section

namespace CFSG.BenderSuzuki

universe u

/-- In a finite nilpotent subgroup, an ambiently encoded Sylow `r`-subgroup
centralizes every normal subgroup whose order is prime to `r`. -/
public theorem proposition111_nilpotent_normal_coprime_core_commute
    {X : Type u} [Group X] [Finite X]
    {r : ℕ} {H R B : Subgroup X}
    (hr : r.Prime)
    (hRH : R ≤ H) (hBH : B ≤ H)
    (hRsyl : theorem4bIsSylowSubgroupOf r R H)
    (hBnormal : (B.subgroupOf H).Normal)
    (hBcop : Nat.Coprime r (Nat.card B))
    (hHnil : Group.IsNilpotent H) :
    R ≤ Subgroup.centralizer (B : Set X) := by
  letI : Fact r.Prime := ⟨hr⟩
  rcases hRsyl with ⟨S, hReq⟩
  have hRsubeq : R.subgroupOf H = (S : Subgroup H) := by
    rw [hReq]
    exact subgroupOf_map_subtype_eq (S : Subgroup H)
  have hSnormal : (S : Subgroup H).Normal :=
    Group.IsNilpotent.sylow_normal hHnil r S
  have hpCoreEq : pCore r H = R.subgroupOf H :=
    (proposition102_normal_sylow_eq_pCore hr S hSnormal).trans hRsubeq.symm
  have hBcard : Nat.card (B.subgroupOf H) = Nat.card B :=
    natCard_subgroupOf_eq B H hBH
  have hBcop' : Nat.Coprime r (Nat.card (B.subgroupOf H)) := by
    rw [hBcard]
    exact hBcop
  have hBcore : B.subgroupOf H ≤ pPrimeCore r H :=
    le_sSup ⟨hBnormal, hBcop'⟩
  have hprod :=
    proposition102_nilpotent_internalDirectProduct_pCore_pPrimeCore
      r hr hHnil
  intro x hxR
  rw [Subgroup.mem_centralizer_iff]
  intro y hyB
  let xH : H := ⟨x, hRH hxR⟩
  let yH : H := ⟨y, hBH hyB⟩
  have hxCore : xH ∈ pCore r H := by
    rw [hpCoreEq]
    exact hxR
  have hyCore : yH ∈ pPrimeCore r H := hBcore hyB
  exact (congrArg Subtype.val
    (hprod.commute xH hxCore yH hyCore)).symm

end CFSG.BenderSuzuki
