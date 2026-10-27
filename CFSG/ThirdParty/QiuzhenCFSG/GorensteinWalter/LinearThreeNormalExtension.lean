module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.AutAlternatingFour
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.LinearThree
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.LinearThreeEquiv
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGroupExtension

namespace CFSG
end CFSG
open CFSG

/-!
# Normal `PSL₂(3)` extensions

A self-centralizing normal subgroup isomorphic to `PSL₂(3) ≃ A₄` embeds
the ambient group in `Aut(A₄) ≃ S₄`.  Cardinality leaves only the subgroup
itself and the full `S₄` extension, modeled respectively by `PSL₂(3)` and
`PGL₂(3)`.
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

/-- A self-centralizing normal `PSL₂(3)` subgroup in the Lemma 3.3(vi)
setting forces the ambient group to be a `D`-group. -/
public theorem psl2_three_normal_extension_isDGroup
    {G : Type u} [Group G] [Finite G]
    (hcore : pPrimeCore 2 G = ⊥)
    (hSylow : HasDihedralSylowTwo G)
    (H : Subgroup G) (hHnormal : H.Normal)
    (eH : H ≃* PSL2 (ZMod 3))
    (hCH : Subgroup.centralizer (H : Set G) = ⊥) :
    IsDGroup G := by
  let : H.Normal := hHnormal
  rcases quotient_centralizer_mulAut_embedding H with ⟨φ, hφ⟩
  let q : G ≃* G ⧸ Subgroup.centralizer (H : Set G) :=
    ((QuotientGroup.quotientMulEquivOfEq (G := G) hCH).trans
      (QuotientGroup.quotientBot (G := G))).symm
  let ψ : G →* MulAut H := φ.comp q.toMonoidHom
  have hψ : Function.Injective ψ := hφ.comp q.injective
  let eHA4 : H ≃* alternatingGroup (Fin 4) :=
    eH.trans psl2_three_equiv_alternatingGroup
  let c : Equiv.Perm (Fin 4) →* MulAut (alternatingGroup (Fin 4)) :=
    MulAut.conjNormal (H := alternatingGroup (Fin 4))
  have hc : Function.Bijective c :=
    GroupTheory.AutAlternating.aut_alternatingGroup_four_bijective_conj
  let eAut : Equiv.Perm (Fin 4) ≃* MulAut (alternatingGroup (Fin 4)) :=
    MulEquiv.ofBijective c hc
  have hHcard : Nat.card H = 12 := by
    exact (Nat.card_congr eH.toEquiv).trans nat_card_psl2_zmod3
  have hPermCard : Nat.card (Equiv.Perm (Fin 4)) = 24 := by
    rw [Nat.card_perm]
    norm_num [Nat.card_eq_fintype_card, Nat.factorial]
  have hAutAcard : Nat.card (MulAut (alternatingGroup (Fin 4))) = 24 :=
    (Nat.card_congr eAut.toEquiv).symm.trans hPermCard
  have hAutHcard : Nat.card (MulAut H) = 24 := by
    calc
      Nat.card (MulAut H) = Nat.card (MulAut (alternatingGroup (Fin 4))) :=
        Nat.card_congr (MulAut.congr eHA4).toEquiv
      _ = 24 := hAutAcard
  have hGle : Nat.card G ≤ 24 :=
    (Nat.card_le_card_of_injective ψ hψ).trans_eq hAutHcard
  have hHdvd : Nat.card H ∣ Nat.card G := H.card_subgroup_dvd_card
  obtain ⟨k, hk⟩ := hHdvd
  rw [hHcard] at hk
  have hkpos : 0 < k := by
    by_contra hk0
    have hkzero : k = 0 := Nat.eq_zero_of_not_pos hk0
    subst k
    exact Nat.card_pos.ne' hk
  have hkle : k ≤ 2 := by omega
  have hkcases : k = 1 ∨ k = 2 := by omega
  rcases hkcases with rfl | rfl
  · have hHtop : H = ⊤ := by
      apply Subgroup.eq_top_of_card_eq H
      rw [hHcard, hk]
    let eHG : H ≃* G :=
      (MulEquiv.subgroupCongr hHtop).trans (Subgroup.topEquiv (G := G))
    exact isDGroup_of_iso_PSL2_three hcore hSylow ⟨eHG.symm.trans eH⟩
  · have hGcard : Nat.card G = 24 := by
      simpa using hk
    have hψbij : Function.Bijective ψ :=
      (Nat.bijective_iff_injective_and_card ψ).mpr
        ⟨hψ, hGcard.trans hAutHcard.symm⟩
    let eGAut : G ≃* MulAut H := MulEquiv.ofBijective ψ hψbij
    let eGS4 : G ≃* Equiv.Perm (Fin 4) :=
      (eGAut.trans (MulAut.congr eHA4)).trans eAut.symm
    exact isDGroup_of_iso_PGL2_three hcore hSylow
      ⟨eGS4.trans pgl2_three_equiv_perm.symm⟩

end CFSG.GorensteinWalter
