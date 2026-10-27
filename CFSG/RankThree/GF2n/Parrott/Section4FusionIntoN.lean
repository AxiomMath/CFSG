module

public import CFSG.RankThree.GF2n.Parrott.Section4EWeak
public import CFSG.Adapters.LieModelSimple
public import CFSG.Adapters.LieModelSmallOrders
public import CFSG.GroupTheory.IndexTwoSimpleQuotient
public import CFSG.RankThree.GF2n.Parrott.Section4Theorem4
public import CFSG.GF2Type.Aschbacher1976
public import CFSG.GroupTheory.Fitting.MulEquiv
public import CFSG.GroupTheory.PCore.Transport
public import CFSG.Holt.PSL2Natural.Defs
public import CFSG.Holt.PermFacts
public import CFSG.Holt.ThreePoint
public import CFSG.LocalAnalysis.EvenSmallLie.Children
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporJ4Quot
public import CFSG.LocalAnalysis.QuasithinUnique.K1.EvenClassicalBender
public import CFSG.LocalAnalysis.QuasithinUnique.K1.ExceptionalCatSuzuki
public import CFSG.LocalAnalysis.UniquenessCase.UC6Basic
public import CFSG.Quasithin.Background.E2NParamStar
public import CFSG.Quasithin.Vol2.Ch11StatementsInputsAS2
public import CFSG.Quasithin.Vol2.Ch11StatementsInputsAS3
public import CFSG.Quasithin.Vol2.E2TenEight
public import CFSG.RankThree.Holt.Basic
public import CFSG.RankThree.PartTwo.Sec21.HoltCatalog

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG CFSG.Open CFSG.ABGLocalTools Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {z : G}
private theorem commutator_mem_of_relIndex_two {X : Type*} [Group X] {N : Subgroup X}
    (hN : N.index = 2) (a b : X) : ⁅a, b⁆ ∈ N := by
  rw [commutatorElement_def, Subgroup.mul_mem_iff_of_index_two hN,
    Subgroup.mul_mem_iff_of_index_two hN, Subgroup.mul_mem_iff_of_index_two hN, inv_mem_iff,
    inv_mem_iff]
  tauto

omit [Finite G] in
private theorem card_eq_of_quotient_card {K E : Subgroup G} (hEK : E ≤ K) {n : ℕ}
    (hn : Nat.card (↥K ⧸ E.subgroupOf K) = n) : Nat.card K = n * Nat.card E := by
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (E.subgroupOf K), hn,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEK).toEquiv]

theorem mem_commutator_sup_of_conj_mem_of_hB2_hB6 (h : Tim79a.ParrottHyp z)
    (hZ : centerIn (J z) = centerIn (H z))
    (hH' : (⁅H z, H z⁆ ⊔ centerIn (J z)).relIndex (H z) = 2)
    {e : G} (he : e ∈ centerIn (J z))
    {U : Subgroup G} (hUi : U.relIndex (centralizer ({e} : Set G)) = 2) (hJU : J z ≤ U)
    {E : Subgroup G} (hEU : E ≤ U)
    (hQ : (E.subgroupOf (normalizer (E : Set G) ⊓ U)).Normal ∧
            Nat.card (↥(normalizer (E : Set G) ⊓ U) ⧸
              E.subgroupOf (normalizer (E : Set G) ⊓ U)) = 20160 ∧
            ∀ L : Subgroup G, E ≤ L → L ≤ normalizer (E : Set G) ⊓ U →
              L.relIndex (normalizer (E : Set G) ⊓ U) ≠ 2)
    {K : Subgroup G} (hEK : E ≤ K) (hKi : K.relIndex (normalizer (E : Set G)) = 2)
    (hKH : ¬ (normalizer (E : Set G) ⊓ H z ≤ K))
    (hKq : (E.subgroupOf K).Normal ∧ Nat.card (↥K ⧸ E.subgroupOf K) = 20160 ∧
             ∀ L : Subgroup G, E ≤ L → L ≤ K → L.relIndex K ≠ 2) :
    ∀ g ∈ centralizer ({e} : Set G), g * z * g⁻¹ ∈ H z →
      g * z * g⁻¹ ∈ ⁅H z, H z⁆ ⊔ centerIn (J z) := by
  intro g hgC hgH
  set N' : Subgroup G := normalizer (E : Set G) with hN'
  set C : Subgroup G := centralizer ({e} : Set G) with hC
  obtain ⟨hKnorm, hKcard, hKQ⟩ := hKq
  obtain ⟨hQnorm, hQcard, hQQ⟩ := hQ
  have hKN : K ≤ N' := (Subgroup.normal_subgroupOf_iff_le_normalizer hEK).mp hKnorm
  have hEK' : E ≤ N' ⊓ U := le_inf Subgroup.le_normalizer hEU
  have hcardK : Nat.card K = 20160 * Nat.card E := card_eq_of_quotient_card hEK hKcard
  have hcardK' : Nat.card ↥(N' ⊓ U) = 20160 * Nat.card E :=
    card_eq_of_quotient_card hEK' hQcard
  have hN'card : Nat.card N' = 2 * Nat.card K := by
    have h1 := Subgroup.relIndex_mul_card K N'
    rw [hKi, inf_eq_left.mpr hKN] at h1
    exact h1.symm
  have hK'i : (N' ⊓ U).relIndex N' = 2 := by
    have h1 := Subgroup.relIndex_mul_card (N' ⊓ U) N'
    rw [inf_eq_left.mpr (inf_le_left : N' ⊓ U ≤ N'), hcardK', hN'card, hcardK] at h1
    exact Nat.eq_of_mul_eq_mul_right (m := 20160 * Nat.card E)
      (Nat.mul_pos (by norm_num) Nat.card_pos) h1
  have hK'K : N' ⊓ U ≤ K :=
    CFSG.GroupTheory.le_of_relIndex_two_of_forall_relIndex_ne_two (N := N') inf_le_left hKi
      hEK hEK' hQQ
  have hHU : ¬ H z ≤ U := by
    intro hHU
    apply hKH
    intro n hn
    exact hK'K (mem_inf.mpr ⟨(mem_inf.mp hn).1, hHU (mem_inf.mp hn).2⟩)
  have heH : e ∈ centerIn (H z) := hZ ▸ he
  have hHC : H z ≤ C := fun x hx => by
    rw [hC, mem_centralizer_singleton_iff]
    exact mem_centralizer_iff.mp heH.2 x hx
  have hUH : (U ⊓ H z).relIndex (H z) = 2 := by
    rw [Subgroup.inf_relIndex_right]
    have hle : U.relIndex (H z) ≤ U.relIndex C :=
      Subgroup.relIndex_le_of_le_right hHC (by rw [hUi]; norm_num)
    rw [hUi] at hle
    have h0 : U.relIndex (H z) ≠ 0 := by
      intro h0
      have h1 := Subgroup.relIndex_mul_card U (H z)
      rw [h0, zero_mul] at h1
      exact absurd h1.symm Nat.card_pos.ne'
    have h1 : U.relIndex (H z) ≠ 1 := fun h1 => hHU (Subgroup.relIndex_eq_one.mp h1)
    omega
  have hcommle : ⁅H z, H z⁆ ≤ U ⊓ H z := by
    rw [Subgroup.commutator_le]
    intro g₁ hg₁ g₂ hg₂
    have hidx : ((U ⊓ H z).subgroupOf (H z)).index = 2 := hUH
    exact commutator_mem_of_relIndex_two hidx (⟨g₁, hg₁⟩ : ↥(H z)) ⟨g₂, hg₂⟩
  have hZJ : centerIn (J z) ≤ J z := inf_le_left
  have hNle : ⁅H z, H z⁆ ⊔ centerIn (J z) ≤ U ⊓ H z :=
    sup_le hcommle (fun x hx => mem_inf.mpr ⟨hJU (hZJ hx), J_le_H (hZJ hx)⟩)
  have hNeq : U ⊓ H z ≤ ⁅H z, H z⁆ ⊔ centerIn (J z) := by
    have hmul := Subgroup.relIndex_mul_relIndex (⁅H z, H z⁆ ⊔ centerIn (J z)) (U ⊓ H z) (H z)
      hNle inf_le_right
    rw [hH', hUH] at hmul
    have h1 : (⁅H z, H z⁆ ⊔ centerIn (J z)).relIndex (U ⊓ H z) = 1 := by omega
    exact Subgroup.relIndex_eq_one.mp h1
  have hzC : z ∈ C := by
    rw [hC, mem_centralizer_singleton_iff]
    exact mem_centralizer_iff.mp he.2 z (z_mem_J h)
  have hUn : (U.subgroupOf C).Normal := Subgroup.normal_of_index_eq_two hUi
  have hzU : (⟨z, hzC⟩ : ↥C) ∈ U.subgroupOf C := hJU (z_mem_J h)
  have hgU : g * z * g⁻¹ ∈ U := hUn.conj_mem _ hzU ⟨g, hgC⟩
  exact hNeq (mem_inf.mpr ⟨hgU, hgH⟩)

section Certified


theorem fusion_into_commutator_sup_of_hB2_hB6 (h : Tim79a.ParrottHyp z)
    (hZ : centerIn (J z) = centerIn (H z))
    (hB2 : ∀ z₁ ∈ centerIn (J z), z₁ ∉ Subgroup.zpowers z → orderOf z₁ = 2 →
      (∃ g ∈ centralizer ({z₁} : Set G), g * z * g⁻¹ ∈ H z ∧ g * z * g⁻¹ ≠ z) →
      ∃ U : Subgroup G, U ≤ centralizer ({z₁} : Set G) ∧
        U.relIndex (centralizer ({z₁} : Set G)) = 2 ∧ J z ≤ U ∧
        (∃ (_ : ((Subgroup.zpowers z₁).subgroupOf U).Normal) (X : Type) (_ : Group X),
          CFSG.Blueprint.LieModel X .PSU 6 2 1 ∧
            Nonempty (↥U ⧸ (Subgroup.zpowers z₁).subgroupOf U ≃* X)) ∧
        ∃ E : Subgroup G, IsParrottE z E ∧ E ≤ U ∧
          ((E.subgroupOf (normalizer (E : Set G) ⊓ U)).Normal ∧
             Nat.card (↥(normalizer (E : Set G) ⊓ U) ⧸
               E.subgroupOf (normalizer (E : Set G) ⊓ U)) = 20160 ∧
             ∀ L : Subgroup G, E ≤ L → L ≤ normalizer (E : Set G) ⊓ U →
               L.relIndex (normalizer (E : Set G) ⊓ U) ≠ 2) ∧
          (∀ T : Subgroup G, IsSylowOf 2 T (H z) → E ≤ T →
            ∀ g : G, CFSG.conjugate E g ≤ T → CFSG.conjugate E g = E) ∧
          (∀ y ∈ ⁅H z, H z⁆ ⊔ centerIn (J z), orderOf y = 2 → ∃ c ∈ H z, c * y * c⁻¹ ∈ E) ∧
          ∃ t' j₀ : G, t' ∈ E ∧ t' ∉ J z ∧ orderOf t' = 2 ∧ IsConj z t' ∧ j₀ ∈ J z ∧
            j₀ ∉ centerIn (J z) ∧ IsConj (t' * z) j₀)
    (hB3 : ∀ e ∈ centerIn (J z), e ≠ 1 → e ≠ z →
      (∃ g ∈ centralizer ({e} : Set G), g * z * g⁻¹ ∈ H z ∧ g * z * g⁻¹ ≠ z) →
      ∀ j ∈ J z, orderOf j = 2 → j ∉ Subgroup.zpowers z →
        ∀ g ∈ centralizer ({e} : Set G), g * z * g⁻¹ ≠ j)
    (hB6 : ∀ E : Subgroup G, IsParrottE z E →
      (∀ T : Subgroup G, IsSylowOf 2 T (H z) → E ≤ T →
        ∀ g : G, CFSG.conjugate E g ≤ T → CFSG.conjugate E g = E) →
      (∀ j ∈ J z, j ∉ Subgroup.zpowers z → ¬ IsConj z j) →
      (∃ e ∈ E, e ≠ z ∧ ∃ n ∈ normalizer (E : Set G), n * z * n⁻¹ = e) →
      ∃ K : Subgroup G, E ≤ K ∧ K.relIndex (normalizer (E : Set G)) = 2 ∧
        ¬ (normalizer (E : Set G) ⊓ H z ≤ K) ∧
        (E.subgroupOf K).Normal ∧ Nat.card (↥K ⧸ E.subgroupOf K) = 20160 ∧
          ∀ L : Subgroup G, E ≤ L → L ≤ K → L.relIndex K ≠ 2)
    (hH' : (⁅H z, H z⁆ ⊔ centerIn (J z)).relIndex (H z) = 2) :
    ∀ g : G, (∃ e ∈ centerIn (J z), e ≠ 1 ∧ e ≠ z ∧ g ∈ centralizer ({e} : Set G)) →
      g * z * g⁻¹ ∈ H z → g * z * g⁻¹ ∈ ⁅H z, H z⁆ ⊔ centerIn (J z) := by
  rintro g ⟨e, he, he1, hez, hge⟩ hgH
  by_cases hgz : g * z * g⁻¹ = z
  · rw [hgz]
    exact Subgroup.mem_sup_right (z_mem_centerIn_J h)
  · have hz2 : orderOf z = 2 := h.1
    have hezp : e ∉ Subgroup.zpowers z := by
      intro hmem
      rcases CFSG.GF2Type.Aschbacher1976Full.Z4Q8.mem_zpowers_two hz2 hmem with h1 | h1
      · exact he1 h1
      · exact hez h1
    have he2 : orderOf e = 2 :=
      orderOf_eq_prime (by rw [pow_two]; exact centerIn_J_sq h he) he1
    obtain ⟨U, hUC, hUi, hJU, hUq, E, hE, hEU, hQ, hweak, hconjE, t', j₀, ht'E, ht'J, ht'2, hzt',
      hj₀, hj₀c, hconj⟩ := hB2 e he hezp he2 ⟨g, hge, hgH, hgz⟩
    have hJ : ∀ j ∈ J z, j ∉ Subgroup.zpowers z → ¬ IsConj z j := fun j hj hjz =>
      not_isConj_of_mem_J_of_lemma32 h hZ hB3 hj hjz
    have hzE : z ∈ E := hE.2.2.1 (z_mem_centerIn_J h)
    have hzt'N : ∃ e ∈ E, e ≠ z ∧ ∃ n ∈ normalizer (E : Set G), n * z * n⁻¹ = e := by
      obtain ⟨n, hn, hnz⟩ := exists_mem_normalizer_of_isConj_of_mem h hZ hE hweak hzE ht'E hzt'
      exact ⟨t', ht'E, fun h1 => ht'J (by rw [h1]; exact z_mem_J h), n, hn, hnz⟩
    obtain ⟨K, hEK, hKi, hNH, hKq⟩ := hB6 E hE hweak hJ hzt'N
    exact mem_commutator_sup_of_conj_mem_of_hB2_hB6 h hZ hH' he hUi hJU hEU hQ hEK hKi hNH hKq g
      hge hgH

end Certified

end CFSG.RankThree.GF2n.Parrott
