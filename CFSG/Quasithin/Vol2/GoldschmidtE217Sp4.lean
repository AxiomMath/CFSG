module

public import CFSG.Quasithin.Vol2.GoldschmidtE217Lie
public import CFSG.Quasithin.Vol2.Ch3E213MP6BI
public import CFSG.Quasithin.Vol2.Ch3E213MP6D2
public import CFSG.Quasithin.Vol2.Ch3E213MP6EJ

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits B2F B6 E2 Ch3E213M

namespace E217R1

variable {G : Type} [Group G] [Finite G] {H T M V K : Subgroup G}

open CFSG.ComponentClassification.UnbalancedCatalog.SpChain (antiSp antiUnipotent
  antiUnipotentCenter antiUnipotentCenter_le)
open CFSG.Quasithin.SteinbergBS (rootLong)
open CFSG.ABGLocalTools (IsSylowOf isSylowOf_iff)

theorem false_of_coordSz (hS : Setting H T M V K)
    (hB : E2.IsBorelIn (E2.star M H K) (E2.star M H (M ⊓ K)))
    {k : Type} [Field k] [Finite k] [CharP k 2] (D : Sp4Data H T M V K k)
    {Y : Subgroup (antiSp k)} {g : antiSp k} (hgY : g ∈ Y)
    (hY : coordIn D.θ V ⊔ (coordIn D.θ V).map (MulAut.conj g).toMonoidHom = Y)
    (hSyl : IsSylowOf 2 (Y ⊓ antiUnipotent k) Y)
    (hcore : kerIn (Y ⊓ Subgroup.normalizer (antiUnipotent k : Set (antiSp k))) Y = ⊥)
    (hO2 : CFSG.inSubgroup (CFSG.pCore 2) Y = ⊥)
    (hO2B : CFSG.inSubgroup (CFSG.pCore 2)
      (Y ⊓ Subgroup.normalizer (antiUnipotent k : Set (antiSp k))) = Y ⊓ antiUnipotent k)
    (hexact : OddCoverExact ↥Y)
    (hstar : ∃ c ∈ Y, ∃ ℓ a : ℕ, ℓ.Prime ∧ ℓ ≠ 2 ∧ orderOf c = ℓ ^ (a + 1) ∧
      ∀ m : ℕ, 0 < m → ℓ ^ (a + 1) ∣ 2 ^ m - 1 → Nat.card (coordIn D.θ V) ^ 2 ≤ 2 ^ m)
    (hV16 : Nat.card V = 2 ^ 4)
    (hq : (((3 : ℚ) / 2 : ℚ) : WithTop ℚ) ≤ qhatOf (autI hS.hyp.elem H)) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨g', hg', hpair, hc2, hne, -, ⟨φ, hφs, hφk⟩, hVB⟩ :=
    exists_coord_member hS hB D hgY hY hSyl hcore hO2 hO2B hexact
  obtain ⟨c, hcY, ℓ, a, hℓ, hℓ2, hc, hm⟩ := hstar
  obtain ⟨x, hxo⟩ := exists_orderOf_eq_of_surj hφs (c := (⟨c, hcY⟩ : ↥Y))
    (n := ℓ ^ (a + 1)) (by rw [← Subgroup.orderOf_coe]; exact hc)
  have hstar' := relIndex_le_of_orderOf hpair hc2 x.2 hℓ hℓ2
    (by rw [Subgroup.orderOf_coe]; exact hxo) fun m hm0 hdvd =>
      (Nat.pow_le_pow_left hVB 2).trans (hm m hm0 hdvd)
  have hcard : (kerIn (M ⊓ Ch3n.pairI V g') (Ch3n.pairI V g')).relIndex (Ch3n.pairI V g') =
      Nat.card ↥Y := by
    rw [Subgroup.relIndex, Subgroup.index, ← hφk]
    exact Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective φ hφs).toEquiv
  have hWY : coordIn D.θ V ≤ Y ⊓ antiUnipotent k :=
    le_inf (hY ▸ le_sup_left) (D.V_le_center.trans antiUnipotentCenter_le)
  have hS2 : IsPGroup 2 ↥(Y ⊓ antiUnipotent k) := (isSylowOf_iff.1 hSyl).2.1
  have h4 : 4 ∣ Nat.card ↥Y := by
    obtain ⟨j, hj⟩ := IsPGroup.iff_card.1 hS2
    have hle : Nat.card (coordIn D.θ V) ≤ Nat.card ↥(Y ⊓ antiUnipotent k) :=
      Subgroup.card_le_of_le hWY
    have h4le := P6B.four_le_card_coordIn hS D
    have hj2 : 2 ≤ j := by
      by_contra hj2
      have : 2 ^ j ≤ 2 ^ 1 := Nat.pow_le_pow_right two_pos (by omega)
      omega
    have hdvd : Nat.card ↥(Y ⊓ antiUnipotent k) ∣ Nat.card ↥Y :=
      Subgroup.card_dvd_of_le inf_le_left
    refine Dvd.dvd.trans ?_ hdvd
    rw [hj]
    exact (pow_dvd_pow 2 hj2 : 2 ^ 2 ∣ 2 ^ j)
  exact false_of_member hS.hyp.elem hpair hc2 hne (pairI_le hS.hyp.le_H hg') hV16 hq hstar'
    (hcard ▸ h4)

theorem false_of_sp4
    (hIrr : IrrStatement)
    (hG41 : FactSp4TransvW) (hCTwo : FactSp4CTwo) (hS : Setting H T M V K) (h2 : Case2 H T M K)
    {n : ℕ} (hn : 1 ≤ n) (hSp : E2.IsSp4Prime n ↥(E2.star M H K))
    (hD : E2.IsDiagramNontrivial (E2.star M H T) (E2.star M H K) (E2.star M H (T ⊓ K)))
    (hB : E2.IsBorelIn (E2.star M H K) (E2.star M H (M ⊓ K))) (hV16 : Nat.card V = 2 ^ 4)
    (hq : (((3 : ℚ) / 2 : ℚ) : WithTop ℚ) ≤ qhatOf (autI hS.hyp.elem H)) : False := by
  rcases Nat.lt_or_ge n 2 with hlt | hge
  · obtain rfl : n = 1 := by omega
    obtain ⟨g, hg⟩ := member_sp4One hS h2 hSp hD hB
    exact false_of_sp4Member hS.hyp.elem hV16 hS.hyp.le_H hq hg
  · obtain ⟨k, _, _, _, hk, ⟨D⟩⟩ := exists_sp4Data hS h2 hge hSp
    by_cases hdiag : ∃ μ : k, μ ≠ 0 ∧ coordIn D.θ V ≤ zLine 1 μ
    · obtain ⟨μ, hμ, hle⟩ := hdiag
      obtain ⟨T', hT', hP⟩ := P6D.pair_of_sp4Diag hS hk D hμ hle
      exact false_of_pair hS hT' hP hV16 hq
    · push Not at hdiag
      by_cases hl : coordIn D.θ V ⊓ rootLong k = ⊥
      · obtain ⟨h, r, hh, hσ⟩ := P6B.swap_data hS D
        have hsp := P6B.spansCenter_coordIn D hdiag
        rcases P6B.exists_member_or_suzuki hG41 hCTwo hge hk D.V_le_center hl hsp hh hσ with
          ⟨F₀, c, g, hc, hgY, hY⟩ | ⟨F₀, a, ha, hcard, d, hd, hW⟩
        · obtain ⟨g', hg'⟩ := exists_sp4Member_of_subfieldSp hS hB D hc hgY hY
          exact false_of_sp4Member hS.hyp.elem hV16 hS.hyp.le_H hq hg'
        · obtain ⟨Y, g, hgY, hY, hSyl, hcore, hO2, hO2B, hexact, hstar⟩ :=
            P6B.exists_sz_member D.V_le_center (P6B.four_le_card_coordIn hS D) ha hcard hd hW
          exact false_of_coordSz hS hB D hgY hY hSyl hcore hO2 hO2B hexact hstar hV16 hq
      · obtain ⟨g, F₀, hg⟩ := exists_sp4Member_of_transv hIrr hG41 hS hB hk D hl
        exact false_of_sp4Member hS.hyp.elem hV16 hS.hyp.le_H hq hg

end E217R1

end CFSG.Quasithin
