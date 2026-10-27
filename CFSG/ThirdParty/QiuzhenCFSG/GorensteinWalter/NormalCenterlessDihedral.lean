module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Classification
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.DihedralCore
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PPrimeCore

namespace CFSG
end CFSG
open CFSG

/-!
# Centralizers of normal centerless subgroups with dihedral Sylow 2-subgroups

If a centerless normal subgroup and its ambient finite group both have
dihedral Sylow `2`-subgroups, then the subgroup centralizer has odd order.
Indeed, an involution in the centralizer and a Sylow `2`-subgroup of the
normal subgroup lie in a common ambient Sylow subgroup.  Their intersection
with the normal subgroup is a normal noncyclic subgroup of a dihedral group,
whose centralizer is contained in that intersection.

When the ambient `2'`-core is trivial, the normal odd-order centralizer is
therefore trivial.  This is the generic 2-local reduction used in
Gorenstein--Walter Lemma 3.3(vi).
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

/-- A centerless normal subgroup with dihedral Sylow `2`-subgroups has an
odd-order centralizer inside an ambient group with dihedral Sylow
`2`-subgroups. -/
public theorem centralizer_card_coprime_two_of_normal_centerless_dihedral
    {G : Type u} [Group G] [Finite G]
    (hGd : HasDihedralSylowTwo G)
    (H : Subgroup G) (hHnormal : H.Normal)
    (hZ : Subgroup.center (↥H) = ⊥)
    (hHd : HasDihedralSylowTwo (↥H)) :
    Nat.Coprime 2 (Nat.card (↥(Subgroup.centralizer (H : Set G)))) := by
  rw [Nat.prime_two.coprime_iff_not_dvd]
  intro hdiv
  let C : Subgroup G := Subgroup.centralizer (H : Set G)
  have hdivC : 2 ∣ Nat.card C := by simpa [C] using hdiv
  obtain ⟨t, htord⟩ := exists_prime_orderOf_dvd_card' (G := C) 2 hdivC
  have htne : t ≠ (1 : C) := by
    intro ht
    have : (1 : ℕ) = 2 := by simpa [ht] using htord
    omega
  have ht2C : t ^ 2 = (1 : C) := by
    have htpow := pow_orderOf_eq_one t
    simpa [htord] using htpow
  let tG : G := t
  have htGne : tG ≠ (1 : G) := by
    intro h
    apply htne
    exact Subtype.ext h
  have htG2 : tG ^ 2 = (1 : G) := by
    simpa [tG] using congrArg (fun z : C => (z : G)) ht2C
  have htC : tG ∈ Subgroup.centralizer (H : Set G) := by
    simpa [C, tG] using t.property
  let P : Sylow 2 (↥H) := Classical.choice Sylow.nonempty
  let Pmap : Subgroup G := (P : Subgroup H).map H.subtype
  let T : Subgroup G := Subgroup.zpowers tG
  have hPmap : IsPGroup 2 Pmap := by
    simpa [Pmap] using
      IsPGroup.map (p := 2) (H := (P : Subgroup H)) P.isPGroup' H.subtype
  have hT : IsPGroup 2 T := by
    have hcard_dvd : Nat.card (Subgroup.zpowers tG) ∣ 2 := by
      simpa [Nat.card_zpowers] using (orderOf_dvd_of_pow_eq_one htG2)
    have hcard_dvd' : Nat.card (Subgroup.zpowers tG) ∣ 2 ^ 1 := by
      simpa using hcard_dvd
    rcases (Nat.dvd_prime_pow Nat.prime_two).1 hcard_dvd' with ⟨n, hn, hcard⟩
    simpa [T] using (IsPGroup.of_card hcard)
  have hPnorm : Pmap ≤ Subgroup.normalizer (T : Set G) := by
    rw [Subgroup.le_normalizer_iff]
    intro p hp k hk
    rcases (Subgroup.mem_zpowers_iff).mp hk with ⟨z, rfl⟩
    have hpH : p ∈ H := (Subgroup.map_subtype_le (P : Subgroup H)) hp
    have hpt : p * tG = tG * p :=
      (Subgroup.mem_centralizer_iff.mp htC) p hpH
    have hcomm : Commute p tG := hpt
    have hcommz : Commute p (tG ^ z) := hcomm.zpow_right z
    have hconj : p * tG ^ z * p⁻¹ = tG ^ z := by
      calc
        p * tG ^ z * p⁻¹ = (tG ^ z * p) * p⁻¹ := by rw [hcommz.eq]
        _ = tG ^ z := by group
    rw [hconj]
    exact ⟨z, rfl⟩
  have hsup : IsPGroup 2 (Pmap ⊔ T : Subgroup G) :=
    IsPGroup.to_sup_of_normal_right' hPmap hT hPnorm
  obtain ⟨S, hS⟩ := IsPGroup.exists_le_sylow hsup
  have hPmapS : Pmap ≤ (S : Subgroup G) := le_sup_left.trans hS
  have htS : tG ∈ (S : Subgroup G) :=
    (le_sup_right.trans hS) (Subgroup.mem_zpowers tG)
  obtain ⟨m, hm, eS⟩ := hGd S
  rcases eS with ⟨eS⟩
  have hInt : H ⊓ (S : Subgroup G) = Pmap := by
    let Dg : Subgroup G := H ⊓ (S : Subgroup G)
    have hDgH : Dg ≤ H := inf_le_left
    have hDgp : IsPGroup 2 Dg := by
      have htmp := S.isPGroup'.to_inf_left (K := H)
      rw [inf_comm] at htmp
      simpa [Dg] using htmp
    let Q : Subgroup H := Dg.subgroupOf H
    have hQp : IsPGroup 2 Q := by
      exact hDgp.of_equiv (Subgroup.subgroupOfEquivOfLe hDgH).symm
    have hPleQ : (P : Subgroup H) ≤ Q := by
      intro x hx
      change (x : G) ∈ Dg
      exact ⟨(Subgroup.map_subtype_le (P : Subgroup H))
        (Subgroup.mem_map_of_mem H.subtype hx),
        hPmapS (Subgroup.mem_map_of_mem H.subtype hx)⟩
    have hQeq : Q = (P : Subgroup H) := P.is_maximal' hQp hPleQ
    have hmapQ : Q.map H.subtype = Dg := by
      simpa [Q, Dg] using (Subgroup.map_subgroupOf_eq_of_le hDgH)
    calc
      H ⊓ (S : Subgroup G) = Dg := rfl
      _ = Q.map H.subtype := hmapQ.symm
      _ = Pmap := by rw [hQeq]
  let D : Subgroup S := (H ⊓ (S : Subgroup G)).subgroupOf (S : Subgroup G)
  have hDnormal : D.Normal := by
    apply (Subgroup.normal_subgroupOf_iff inf_le_right).2
    intro d s hd hs
    have hdH : (d : G) ∈ H := hd.1
    have hdS : (d : G) ∈ (S : Subgroup G) := hd.2
    have hconjH : (s : G) * (d : G) * (s : G)⁻¹ ∈ H :=
      hHnormal.conj_mem (d : G) hdH (s : G)
    have hconjS : (s : G) * (d : G) * (s : G)⁻¹ ∈ (S : Subgroup G) := by
      exact S.mul_mem (S.mul_mem hs hdS) (S.inv_mem hs)
    exact ⟨hconjH, hconjS⟩
  obtain ⟨k, hk, eP⟩ := hHd P
  rcases eP with ⟨eP⟩
  have ePmap : (P : Subgroup H) ≃* Pmap :=
    (P : Subgroup H).equivMapOfInjective H.subtype H.subtype_injective
  have hDeq : D = Pmap.subgroupOf (S : Subgroup G) := by
    dsimp [D]
    rw [hInt]
  have eDmap : D ≃* Pmap := by
    rw [hDeq]
    exact Subgroup.subgroupOfEquivOfLe hPmapS
  have eDP : D ≃* P := eDmap.trans ePmap.symm
  have eDD : D ≃* DihedralGroup (2 ^ k) := eDP.trans eP
  have hDnc : ¬ IsCyclic D := by
    intro hcyc
    have hcycDihedral : IsCyclic (DihedralGroup (2 ^ k)) := eDD.isCyclic.mp hcyc
    have hkne : 2 ^ k ≠ 1 := by
      intro hk1
      rcases (Nat.pow_eq_one.mp hk1) with hkbase | hk0
      · norm_num at hkbase
      · exfalso
        omega
    exact (DihedralGroup.not_isCyclic hkne) hcycDihedral
  have hleD : Subgroup.centralizer (D : Set S) ≤ D :=
    centralizer_le_of_normal_dihedral_of_mulEquiv hm eS D hDnormal hDnc
  have htDcent : (⟨tG, htS⟩ : S) ∈ Subgroup.centralizer (D : Set S) := by
    rw [Subgroup.mem_centralizer_iff]
    intro d hd
    have hdH : (d : G) ∈ H :=
      (show (d : G) ∈ H ⊓ (S : Subgroup G) from hd).1
    have hcomm := (Subgroup.mem_centralizer_iff.mp htC) (d : G) hdH
    apply Subtype.ext
    exact hcomm
  have htD : (⟨tG, htS⟩ : S) ∈ D := hleD htDcent
  have htH : tG ∈ H := htD.1
  have htcenter : (⟨tG, htH⟩ : H) ∈ Subgroup.center (↥H) := by
    rw [Subgroup.mem_center_iff]
    intro h
    have hcomm := (Subgroup.mem_centralizer_iff.mp htC) (h : G) h.property
    apply Subtype.ext
    exact hcomm
  have htcenterbot : (⟨tG, htH⟩ : H) ∈ (⊥ : Subgroup H) := by
    simpa [hZ] using htcenter
  have hteq : (⟨tG, htH⟩ : H) = 1 := htcenterbot
  apply htGne
  simpa using congrArg (fun z : H => (z : G)) hteq

/-- If the ambient `2'`-core is trivial, the odd centralizer from
`centralizer_card_coprime_two_of_normal_centerless_dihedral` is trivial. -/
public theorem centralizer_eq_bot_of_normal_centerless_dihedral_of_pPrimeCore_eq_bot
    {G : Type u} [Group G] [Finite G]
    (hGd : HasDihedralSylowTwo G) (hO : pPrimeCore 2 G = ⊥)
    (H : Subgroup G) (hHnormal : H.Normal)
    (hZ : Subgroup.center (↥H) = ⊥)
    (hHd : HasDihedralSylowTwo (↥H)) :
    Subgroup.centralizer (H : Set G) = ⊥ := by
  let C : Subgroup G := Subgroup.centralizer (H : Set G)
  let : H.Normal := hHnormal
  have hCnormal : C.Normal := by
    simpa [C] using (Subgroup.normal_centralizer (H := H))
  have hCodd : Nat.Coprime 2 (Nat.card C) := by
    simpa [C] using
      centralizer_card_coprime_two_of_normal_centerless_dihedral
        hGd H hHnormal hZ hHd
  have hCle : C ≤ pPrimeCore 2 G := le_sSup ⟨hCnormal, hCodd⟩
  rw [hO] at hCle
  exact le_bot_iff.mp hCle

end CFSG.GorensteinWalter
