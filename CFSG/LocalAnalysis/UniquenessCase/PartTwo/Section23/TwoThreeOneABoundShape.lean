module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.StatementsTwoThree
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ShapeDisjoint
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ProofsEightLayer
import CFSG.LocalAnalysis.UniquenessCase.UC22P20za
import CFSG.Fischer.Classification.Recognition.Basic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.Blueprint Subgroup

variable {G : Type} [Group G] [Finite G]

private theorem card_quot_center_of_isSimpleGroup {X : Type} [Group X] [IsSimpleGroup X]
    (hq : CFSG.Open.IsQuasisimple X) : Nat.card (X ⧸ Subgroup.center X) = Nat.card X :=
  uc22p21k_card_quot_center (uc22p21k_center_eq_bot hq)

private theorem ordA_one_ne_ordA_two_pow {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    ordA 1 (2 ^ a) ≠ ordA 2 (2 ^ b) := by
  intro h
  obtain ⟨r, hr, h1⟩ := (CFSG.Timmesfeld.Orders.profile_ordA (n := 1) (f := a) le_rfl ha).two
  obtain ⟨s, hs, h2⟩ :=
    (CFSG.Timmesfeld.Orders.profile_ordA (n := 2) (f := b) (by norm_num) hb).two
  have hab := CFSG.Timmesfeld.Orders.eq_of_two_pow_mul_odd hr hs (h1.symm.trans (h.trans h2))
  have ha3 : a = 3 * b := by norm_num at hab; omega
  have hq2 : 2 ≤ 2 ^ b := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ b := Nat.pow_le_pow_right (by norm_num) hb
  have h2a : 2 ^ a = (2 ^ b) ^ 3 := by rw [ha3, pow_mul']
  have hgcd : Nat.gcd 2 (2 ^ a - 1) = 1 :=
    Nat.coprime_two_left.mpr (CFSG.Timmesfeld.Orders.odd_two_pow_sub_one ha)
  have hL2 : ordA 1 (2 ^ a) = (2 ^ b) ^ 3 * (((2 ^ b) ^ 3) ^ 2 - 1) := by
    rw [CFSG.LocalAnalysis.UniquenessCase.UC6.N588.ordA_one_eq, hgcd, Nat.div_one, h2a]
  have hL3 : ordA 2 (2 ^ b) ≤ (2 ^ b) ^ 3 * (((2 ^ b) ^ 2 - 1) * ((2 ^ b) ^ 3 - 1)) := by
    unfold ordA
    rw [show 2 * (2 + 1) / 2 = 3 by rfl, show Finset.Icc 2 (2 + 1) = {2, 3} by rfl,
      Finset.prod_pair (by norm_num)]
    exact Nat.div_le_self _ _
  have hle : (2 ^ b) ^ 3 * (((2 ^ b) ^ 3) ^ 2 - 1) ≤
      (2 ^ b) ^ 3 * (((2 ^ b) ^ 2 - 1) * ((2 ^ b) ^ 3 - 1)) :=
    hL2.symm.le.trans (h.le.trans hL3)
  generalize 2 ^ b = q at hq2 hle
  have hle' : (q ^ 3) ^ 2 - 1 ≤ (q ^ 2 - 1) * (q ^ 3 - 1) :=
    Nat.le_of_mul_le_mul_left hle (by positivity)
  have hy : 0 < q ^ 3 - 1 := by
    have : 1 < q ^ 3 := Nat.one_lt_pow (by norm_num) (by omega)
    omega
  have hxy : q ^ 2 - 1 < q ^ 3 + 1 := by
    have : q ^ 2 ≤ q ^ 3 := Nat.pow_le_pow_right (by omega) (by norm_num)
    omega
  have hsq : (q ^ 3) ^ 2 - 1 = (q ^ 3 - 1) * (q ^ 3 + 1) := by
    simpa [mul_comm] using Nat.sq_sub_sq (q ^ 3) 1
  have hlt : (q ^ 2 - 1) * (q ^ 3 - 1) < (q ^ 3 + 1) * (q ^ 3 - 1) :=
    Nat.mul_lt_mul_of_pos_right hxy hy
  rw [hsq, mul_comm (q ^ 3 - 1) (q ^ 3 + 1)] at hle'
  exact absurd hle' (not_le.mpr hlt)

private theorem ordBC_two_ne_ordTwistedA_two_pow {f g : ℕ} (hf : 1 ≤ f) (hg : 1 ≤ g) :
    ordBC 2 (2 ^ f) ≠ ordTwistedA 2 (2 ^ g) :=
  CFSG.Timmesfeld.Orders.ne_ordTwistedA_of_dvd_closed (CFSG.Timmesfeld.Orders.profile_ordBC hf)
    CFSG.Timmesfeld.Orders.zBC_dvd_closed
    ((CFSG.Timmesfeld.Orders.profile_ordBC hf).ne_small (by omega) (by omega)) le_rfl hg

theorem not_isSL3_of_isSz {X : Type} [Group X] {a b : ℕ} (h : IsSz X a) : ¬ IsSL3 X b := by
  rintro ⟨-, hL3⟩
  have hcard : Nat.card (X ⧸ Subgroup.center X) = ordA 2 (2 ^ b) := by
    simpa [CFSG.EvenSmallLie.CatalogOrders.lieOrd] using hL3.card_eq_lieOrd (by norm_num)
  have h3 : 3 ∣ Nat.card (X ⧸ Subgroup.center X) := by
    rw [hcard]
    exact CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.three_dvd_ordA (by norm_num)
  exact CFSG.LocalAnalysis.EvenBN.GMSK.not_three_dvd_card_of_lieModel_twistedB2 h
    (h3.trans (Subgroup.card_quotient_dvd_card _))

theorem not_isSL3_of_isL2 {X : Type} [Group X] {a b : ℕ} (h : IsL2 X a) : ¬ IsSL3 X b := by
  rintro ⟨hq, hL3⟩
  have : IsSimpleGroup X :=
    LieModel.isSimpleGroup_of_mem_classicalTags (t := .PSL) (by decide) h
  have hA : Nat.card X = ordA 1 (2 ^ a) := by
    simpa [CFSG.EvenSmallLie.CatalogOrders.lieOrd] using h.card_eq_lieOrd (by norm_num)
  have hB : Nat.card (X ⧸ Subgroup.center X) = ordA 2 (2 ^ b) := by
    simpa [CFSG.EvenSmallLie.CatalogOrders.lieOrd] using hL3.card_eq_lieOrd (by norm_num)
  exact ordA_one_ne_ordA_two_pow h.admissible.2.1 hL3.admissible.2.1
    (hA.symm.trans ((card_quot_center_of_isSimpleGroup hq).symm.trans hB))

theorem not_isSL3_of_isSU3 {X : Type} [Group X] {a b : ℕ} (h : IsSU3 X a) : ¬ IsSL3 X b := by
  rintro ⟨-, hL3⟩
  have hA : Nat.card (X ⧸ Subgroup.center X) = ordTwistedA 2 (2 ^ a) := by
    simpa [CFSG.EvenSmallLie.CatalogOrders.lieOrd] using h.2.card_eq_lieOrd (by norm_num)
  have hB : Nat.card (X ⧸ Subgroup.center X) = ordA 2 (2 ^ b) := by
    simpa [CFSG.EvenSmallLie.CatalogOrders.lieOrd] using hL3.card_eq_lieOrd (by norm_num)
  exact CFSG.Timmesfeld.Orders.ordA_ne_ordTwistedA (by norm_num) hL3.admissible.2.1
    (by norm_num) h.2.admissible.2.1 (hB.symm.trans hA)

theorem not_isSp4_of_isSU3 {X : Type} [Group X] {a b : ℕ} (h : IsSU3 X a) : ¬ IsSp4 X b := by
  intro hSp
  have : IsSimpleGroup X :=
    LieModel.isSimpleGroup_of_mem_classicalTags (t := .PSp) (by decide) hSp
  have hA : Nat.card (X ⧸ Subgroup.center X) = ordTwistedA 2 (2 ^ a) := by
    simpa [CFSG.EvenSmallLie.CatalogOrders.lieOrd] using h.2.card_eq_lieOrd (by norm_num)
  have hB : Nat.card X = ordBC 2 (2 ^ b) := by
    simpa [CFSG.EvenSmallLie.CatalogOrders.lieOrd] using hSp.card_eq_lieOrd (by norm_num)
  exact ordBC_two_ne_ordTwistedA_two_pow hSp.admissible.2.1 h.2.admissible.2.1
    (hB.symm.trans ((card_quot_center_of_isSimpleGroup h.1).symm.trans hA))

theorem eq_of_mem_calC_of_isQuasisimple_bar2 {L K₁ K₂ : Subgroup G}
    (hq : CFSG.Open.IsQuasisimple (Bar2 L)) (h₁ : K₁ ∈ calC L) (h₂ : K₂ ∈ calC L) : K₁ = K₂ := by
  have htop : ∀ K ∈ calC L, barImage L K = ⊤ := fun K hK =>
    CFSG.Fischer.Classification.Recognition.IsComponentOf.eq_of_isQuasisimple
      (CFSG.Quasithin.A3.isComponentOf_top_iff.mpr (uc22p22l_barImage_isComponent hK))
      (CFSG.Open.IsQuasisimple.of_mulEquiv Subgroup.topEquiv hq)
  exact barImage_injOn_calC h₁ h₂ ((htop K₁ h₁).trans (htop K₂ h₂).symm)

theorem not_exists_calC_sup_eq_of_isQuasisimple_bar2 {L : Subgroup G}
    (hq : CFSG.Open.IsQuasisimple (Bar2 L)) :
    ¬ ∃ L₁ L₂ : Subgroup G, L₁ ∈ calC L ∧ L₂ ∈ calC L ∧ L = L₁ ⊔ L₂ ∧ L₁ ≠ L₂ :=
  fun ⟨_, _, h₁, h₂, _, hne⟩ => hne (eq_of_mem_calC_of_isQuasisimple_bar2 hq h₁ h₂)

omit [Finite G] in
private theorem barImage_sup_eq_top {L L₁ L₂ : Subgroup G} (h₁ : L₁ ≤ L) (h₂ : L₂ ≤ L)
    (hsup : L = L₁ ⊔ L₂) : barImage L L₁ ⊔ barImage L L₂ = ⊤ := by
  unfold barImage
  rw [← Subgroup.map_sup, ← Subgroup.subgroupOf_sup h₁ h₂, ← hsup, Subgroup.subgroupOf_self]
  exact Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)

theorem eq_or_eq_of_mem_calC_of_sup_eq {L L₁ L₂ K : Subgroup G} (h₁ : L₁ ∈ calC L)
    (h₂ : L₂ ∈ calC L) (hsup : L = L₁ ⊔ L₂) (hK : K ∈ calC L) : K = L₁ ∨ K = L₂ := by
  by_contra hcon
  obtain ⟨hK1, hK2⟩ := not_or.mp hcon
  have hc₁ := uc22p22l_barImage_commute hK h₁ hK1
  have hc₂ := uc22p22l_barImage_commute hK h₂ hK2
  have hgen := barImage_sup_eq_top (CFSG.Quasithin.A3.subnormal_le h₁.1)
    (CFSG.Quasithin.A3.subnormal_le h₂.1) hsup
  have hle : barImage L L₁ ⊔ barImage L L₂ ≤ Subgroup.centralizer (barImage L K : Set (Bar2 L)) :=
    sup_le (fun x hx => Subgroup.mem_centralizer_iff.mpr fun a ha => hc₁ a ha x hx)
      (fun x hx => Subgroup.mem_centralizer_iff.mpr fun a ha => hc₂ a ha x hx)
  have hcen : barImage L K ≤ Subgroup.center (Bar2 L) := fun a ha =>
    Subgroup.mem_center_iff.mpr fun g =>
      (Subgroup.mem_centralizer_iff.mp (hle (hgen ▸ Subgroup.mem_top g)) a ha).symm
  exact CFSG.Fischer.Classification.Recognition.IsQuasisimple.not_le_of_comm
    (CFSG.Quasithin.A3.isQuasisimple_iff_open.mp (uc22p22l_barImage_isComponent hK).1)
    (A := Subgroup.center (Bar2 L))
    (fun a _ b hb => Subgroup.mem_center_iff.mp hb a) hcen

theorem shape417_of (D : Data G) {L : Subgroup G} (hL : L ∈ calL D.T D.M) {n : ℕ}
    (hS : S20_10Shape D.T L) (hn : NParam L n) :
    (IsL2 (Bar2 L) n ∨ IsSz (Bar2 L) n ∨ IsSU3 (Bar2 L) n ∨
      ((IsSL3 (Bar2 L) n ∨ IsSp4 (Bar2 L) n) ∧ ∃ t ∈ D.T, ActsNontrivOnDiagram L t)) ∨
    ∃ L₁ L₂ : Subgroup G, L₁ ∈ calC L ∧ L₂ ∈ calC L ∧ L = L₁ ⊔ L₂ ∧ L₁ ≠ L₂ ∧
      (∃ t ∈ D.T, L₂ = L₁.map (MulAut.conj t).toMonoidHom) ∧
      ∀ L' ∈ ({L₁, L₂} : Set (Subgroup G)),
        IsSz (Bar2 L') n ∨ IsL2 (Bar2 L') n ∨ (n = 3 ∧ IsSU3 (Bar2 L') 3) := by
  rcases hn with hsingle | ⟨L₁, L₂, hL₁, hL₂, hsup, hne, hshape⟩
  · have hq := uc22pw_isQuasisimple_of_single D hL hsingle
    rcases hsingle with hSz | hL2 | hSU | hSL | hSp
    · exact Or.inl (Or.inr (Or.inl hSz))
    · exact Or.inl (Or.inl hL2)
    · exact Or.inl (Or.inr (Or.inr (Or.inl hSU)))
    · refine Or.inl (Or.inr (Or.inr (Or.inr ⟨Or.inl hSL, ?_⟩)))
      rcases hS with ⟨n', hn' | hn' | hn'⟩ | ⟨L₁', L₂', hL₁', hL₂', hsup', hne', -⟩ |
          ⟨n', -, hact⟩
      · exact (not_isSL3_of_isSz hn' hSL).elim
      · exact (not_isSL3_of_isL2 hn' hSL).elim
      · exact (not_isSL3_of_isSU3 hn' hSL).elim
      · exact (hne' (eq_of_mem_calC_of_isQuasisimple_bar2 hq hL₁' hL₂')).elim
      · exact hact
    · refine Or.inl (Or.inr (Or.inr (Or.inr ⟨Or.inr hSp, ?_⟩)))
      rcases hS with ⟨n', hn' | hn' | hn'⟩ | ⟨L₁', L₂', hL₁', hL₂', hsup', hne', -⟩ |
          ⟨n', -, hact⟩
      · exact (not_isSz_of_isSp4 hSp hn').elim
      · exact (not_isL2_of_isSp4 hSp hn').elim
      · exact (not_isSp4_of_isSU3 hn' hSp).elim
      · exact (hne' (eq_of_mem_calC_of_isQuasisimple_bar2 hq hL₁' hL₂')).elim
      · exact hact
  · rcases hS with ⟨n', hn'⟩ | ⟨L₁', L₂', hL₁', hL₂', hsup', hne', ht, -⟩ | ⟨n', hn', -⟩
    · have hq := uc22pw_isQuasisimple_of_single D hL (n := n')
        (by rcases hn' with h | h | h
            exacts [Or.inl h, Or.inr (Or.inl h), Or.inr (Or.inr (Or.inl h))])
      exact (not_exists_calC_sup_eq_of_isQuasisimple_bar2 hq ⟨L₁, L₂, hL₁, hL₂, hsup, hne⟩).elim
    · refine Or.inr ⟨L₁', L₂', hL₁', hL₂', hsup', hne', ht, fun L' hL' => ?_⟩
      have hLc : L' ∈ calC L := by
        rcases hL' with rfl | hL'
        · exact hL₁'
        · rw [Set.mem_singleton_iff] at hL'
          exact hL' ▸ hL₂'
      exact hshape L' (eq_or_eq_of_mem_calC_of_sup_eq hL₁ hL₂ hsup hLc)
    · have hq := uc22pw_isQuasisimple_of_single D hL (n := n')
        (by rcases hn' with h | h
            exacts [Or.inr (Or.inr (Or.inr (Or.inl h))), Or.inr (Or.inr (Or.inr (Or.inr h)))])
      exact (not_exists_calC_sup_eq_of_isQuasisimple_bar2 hq ⟨L₁, L₂, hL₁, hL₂, hsup, hne⟩).elim

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
