module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section11Lemma115Normalizer

namespace CFSG
end CFSG
open CFSG

/-!
# Section 11, Lemma 11.5: the centralizer of `P`

These helpers isolate the source step which puts `C_B(P)` inside the lifted
Sylow `f`-subgroup.  They use only the preceding quotient-lift package and
the part-(c) anti-fixed-set description of `B`.
-/

noncomputable section

namespace CFSG.BenderSuzuki

open PFAppendixIII PFchapter1section1
open scoped Pointwise

universe u

/-- The centralizer of `P` inside the Lemma 11.5 anti-fixed subgroup maps into
the lifted quotient Sylow subgroup. -/
public theorem lemma115_centralizer_P_le_lift_Q
    {X : Type u} [Group X] [Finite X]
    {M W : Subgroup X} {t : X}
    (d83 : Lemma83Data M t)
    (d : Lemma101Conclusion M W
      (M ⊓ rightConjugate M t)
      (W ⊓ (M ⊓ rightConjugate M t))
      (peterfalviV (M ⊓ rightConjugate M t) t) t)
    (d103 : Lemma103Conclusion M d.choice.P d83.u)
    {f : ℕ}
    (hL : Lemma115QuotientLiftConclusion d83 d d103 f)
    (B : Subgroup X)
    (hBset : (B : Set X) = peterfalviKSet
      (Subgroup.centralizer ({t * d83.u} : Set X)) d83.u)
    (hBodd : Odd (Nat.card B)) :
    B ⊓ Subgroup.centralizer (d.choice.P : Set X) ≤
      hL.Q.map (lemma103NStar d.choice.P).subtype := by
  classical
  let P : Subgroup X := d.choice.P
  let Nstar : Subgroup X := lemma103NStar P
  let Qx : Subgroup X := hL.Q.map Nstar.subtype
  letI : hL.Q.Normal := hL.Q_normal
  intro b hb
  have hbB : b ∈ B := hb.1
  have hbP : b ∈ Subgroup.centralizer (P : Set X) := by
    simpa [P] using hb.2
  have hbN : b ∈ Nstar := by
    exact centralizer_le_normalizer P hbP
  let bStar : Nstar := ⟨b, hbN⟩
  have hbOrder : Odd (orderOf bStar) := by
    have hdiv : orderOf b ∣ Nat.card B := by
      exact Subgroup.orderOf_dvd_natCard B hbB
    have hdiv' : orderOf bStar ∣ Nat.card B := by
      simpa [bStar, Subgroup.orderOf_coe] using hdiv
    exact hBodd.of_dvd_nat hdiv'
  have hbAnti : b ∈ peterfalviKSet
      (Subgroup.centralizer ({t * d83.u} : Set X)) d83.u := by
    rw [← hBset]
    exact hbB
  have hbInvStar : rightConjugateElem bStar d103.uStar = bStar⁻¹ := by
    apply Subtype.ext
    change (d103.uStar : X)⁻¹ * b * (d103.uStar : X) = b⁻¹
    rw [d103.uStar_eq]
    simpa [rightConjugateElem, d83.u_involution.inv_eq_self] using hbAnti.2
  have hbQ : bStar ∈ hL.Q :=
    lemma115_inverted_odd_order_mem_normal_factor hL.Q
      hL.Q_factorization hbOrder hbInvStar
  change b ∈ Qx
  exact Subgroup.mem_map.mpr ⟨bStar, hbQ, rfl⟩

/-- The preceding containment makes `C_B(P)` an `f`-group. -/
public theorem lemma115_centralizer_P_isPGroup
    {X : Type u} [Group X] [Finite X]
    {M W : Subgroup X} {t : X}
    (d83 : Lemma83Data M t)
    (d : Lemma101Conclusion M W
      (M ⊓ rightConjugate M t)
      (W ⊓ (M ⊓ rightConjugate M t))
      (peterfalviV (M ⊓ rightConjugate M t) t) t)
    (d103 : Lemma103Conclusion M d.choice.P d83.u)
    {f : ℕ}
    (hL : Lemma115QuotientLiftConclusion d83 d d103 f)
    (B : Subgroup X)
    (hBset : (B : Set X) = peterfalviKSet
      (Subgroup.centralizer ({t * d83.u} : Set X)) d83.u)
    (hBodd : Odd (Nat.card B)) :
    IsPGroup f (B ⊓ Subgroup.centralizer
      (d.choice.P : Set X) : Subgroup X) := by
  let Nstar : Subgroup X := lemma103NStar d.choice.P
  let Qx : Subgroup X := hL.Q.map Nstar.subtype
  let H : Subgroup X := B ⊓ Subgroup.centralizer (d.choice.P : Set X)
  have hHQ : H ≤ Qx := by
    simpa [H, Qx, Nstar] using
      lemma115_centralizer_P_le_lift_Q d83 d d103 hL B hBset hBodd
  have hQxp : IsPGroup f Qx := by
    simpa [Qx, Nstar] using hL.Q_isPGroup.map Nstar.subtype
  have hHsubp : IsPGroup f (H.subgroupOf Qx) :=
    hQxp.to_subgroup (H.subgroupOf Qx)
  have hHmap : IsPGroup f ((H.subgroupOf Qx).map Qx.subtype) :=
    hHsubp.map Qx.subtype
  have hmapEq : (H.subgroupOf Qx).map Qx.subtype = H :=
    Subgroup.map_subgroupOf_eq_of_le hHQ
  rw [hmapEq] at hHmap
  simpa [H] using hHmap

end CFSG.BenderSuzuki
