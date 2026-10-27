module

public import CFSG.RankThree.GF2n.Tim81.Sec4.Sec41Split
public import CFSG.RankThree.GF2n.Tim81.Sec4.Sec45Main

public section

namespace CFSG.RankThree.GF2n.Tim81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Tim78
open scoped commutatorElement MatrixGroups

variable {G : Type} [Group G] [Finite G] {M V H : Subgroup G}

theorem ha5Statement :
    HA5Statement := by
  intro G _ _ M V h g hmem hVH
  refine ⟨fun e => ?_⟩
  have hcardSL4 : Nat.card (SL(2, GaloisField 2 2)) = 60 :=
    CFSG.Quasithin.A5Model.card_sl2_gf4
  obtain ⟨e5⟩ := CFSG.Quasithin.A5Model.sl2_four_equiv_alt5 (GaloisField 2 2)
    CFSG.Quasithin.A5Model.card_gf4 hcardSL4
  letI : Fintype (GaloisField 2 2) := Fintype.ofFinite _
  have h4 : 4 ≤ Fintype.card (GaloisField 2 2) := by
    rw [← Nat.card_eq_fintype_card, CFSG.Quasithin.A5Model.card_gf4]
  have hL : IsL2OrSz V (Pc M V ⊔ conjSubgroup g (Pc M V)) :=
    Or.inl ⟨GaloisField 2 2, inferInstance, inferInstance, inferInstance, h4,
      ⟨e.trans e5.symm⟩⟩
  have hS : Sec45Shape M V (Pc M V ⊔ conjSubgroup g (Pc M V)) g :=
    RootHyp.sec45Shape_of_isL2OrSz h hmem hVH hL
  obtain ⟨F, hField, hFintype, hCharP, l, hl, ψ, hsw⟩ := hS.shape
  letI := hField
  letI := hFintype
  letI := hCharP
  have hcardH : Nat.card (HBar V (Pc M V ⊔ conjSubgroup g (Pc M V))) = 60 := by
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup]
    norm_num
  have hdiv : 2 ^ (2 * l) ∣ 60 := by
    rw [← (Nat.card_congr ψ.toEquiv).symm.trans hcardH,
      CFSG.Quasithin.SL2Model.card_SL2, Nat.card_eq_fintype_card, hl]
    exact dvd_mul_right _ _
  have hl_le : l ≤ 1 := by
    by_contra hle
    have h2 : 2 ≤ l := by omega
    have h16 : 16 ∣ 4 ^ l := by
      obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h2
      rw [pow_add]
      simpa using dvd_mul_right 16 (4 ^ k)
    have hpow : 2 ^ (2 * l) = 4 ^ l := by
      rw [pow_mul]
      norm_num
    have h16dvd : 16 ∣ 60 := by
      rw [← hpow] at h16
      exact h16.trans hdiv
    norm_num at h16dvd
  have hl_eq : l = 1 := by
    have h1 := hsw.one_le
    omega
  have hV2 : Nat.card V = 2 := by
    simpa [hl_eq] using hsw.card_V
  have h4V : 4 ≤ Nat.card V := h.four_le_card
  rw [hV2] at h4V
  norm_num at h4V

end CFSG.RankThree.GF2n.Tim81
