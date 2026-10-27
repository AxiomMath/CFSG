module

public import CFSG.Quasithin.Vol2.Ch11SecS12C
public import CFSG.Quasithin.Vol2.Ch11SecS12K
public import CFSG.Quasithin.Vol2.Ch11SecS12M
public import CFSG.Quasithin.Vol2.Ch11SecSObl
public import CFSG.Quasithin.Vol2.Ch11SecSCartan
public import CFSG.Quasithin.Vol2.Ch11SecS12J

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecS

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.H13
open CFSG.Quasithin.Vol2.Ch11.SecS.C11AmS.S12

theorem obl11_1_2StarSL3_of (hB : LemmaB414Head) (hAb : Obl11_1_2StarSL3Ab)
    (hC : CartanFacts) (hN : SecA.NatFacts) (hG2 : SecA.FactG2DerivedOrder)
    (hFb : SecA.Facts12b) (h1102 : Stmt11_0_2) (h1103 : Stmt11_0_3) : Obl11_1_2StarSL3 := by
  classical
  intro G _ _ T L I V₁ V₂ X K h hSL3
  by_cases hU : conjClosure (fsuV T I) (Subgroup.normalizer (V₁ : Set G)) ≤ pCoreOf 2 (L ⊔ T)
  · exact hAb G T L I V₁ V₂ X K h hSL3 hU
  have hyp := almostSpecialL3Hyp_star h1102 h1103 hG2 h.hyp h.v₁ hSL3 hU
  obtain ⟨D⟩ := hyp.natural.nonempty_data
  let St : L3Setting 2 (fsuV T I) V₁ L T (Subgroup.normalizer (V₁ : Set G)) := ⟨hyp, D⟩
  have hc := (cartan_of hC hN hG2 h1102 h.hyp h.v₁ h.v₂ h.cartan).1
  have hV₁V : V₁ ≤ fsuV T I := SecA.IsVi.le_fsuV h.v₁
  obtain ⟨x, hx, hx1⟩ : ∃ x ∈ SecA.xOne X (LOf L V₁), x ≠ 1 := by
    have : Nontrivial ↥(SecA.xOne X (LOf L V₁)) := by
      rw [← Finite.one_lt_card_iff_nontrivial, hc.cardX₁]
      norm_num
    obtain ⟨⟨y, hy⟩, hy1⟩ := exists_ne (1 : ↥(SecA.xOne X (LOf L V₁)))
    exact ⟨y, hy, fun h => hy1 (Subtype.ext h)⟩
  have hX₁L : ∀ y ∈ SecA.xOne X (LOf L V₁), y ∈ L := fun y hy => (h.cartan.1 hy.1).1
  have hX₁N : SecA.xOne X (LOf L V₁) ≤ Subgroup.normalizer (V₁ : Set G) := fun y hy => by
    obtain ⟨c, -, hyc⟩ := exists_scalar_of_xOne hFb hN h1102 h.hyp h.v₁ h.v₂ h.cartan hSL3 D hy
      (hX₁L y hy)
    exact NatData3'.mem_normalizer_of_mem_Pt D hV₁V ⟨y, hX₁L y hy⟩ ⟨c, hyc _⟩
  have hxL := hX₁L x hx
  obtain ⟨c, hc3, hxc⟩ :=
    exists_scalar_of_xOne hFb hN h1102 h.hyp h.v₁ h.v₂ h.cartan hSL3 D hx hxL
  have hc1 : c ≠ 1 := scalar_ne_one_of_xOne D hc.cardX₁ hx hx1 hxL hxc
  have hYN : LOf L V₁ ⊔ SecA.xOne X (LOf L V₁) ≤ L ⊓ Subgroup.normalizer (V₁ : Set G) :=
    sup_le (perfectCore_le _) fun y hy => ⟨hX₁L y hy, hX₁N hy⟩
  have hxY : x ∈ LOf L V₁ ⊔ SecA.xOne X (LOf L V₁) :=
    (le_sup_right : SecA.xOne X (LOf L V₁) ≤ LOf L V₁ ⊔ SecA.xOne X (LOf L V₁)) hx
  obtain ⟨s, l₀, hl₀, hm₀⟩ :=
    L3Setting'.exists_labSeries St le_rfl hV₁V inf_le_right le_sup_left hYN hxY hxc
  have htop := L3Setting'.isLabFactor_top St le_rfl hV₁V inf_le_right le_sup_left hYN hxY hxc
  have hO := L3Setting'.commutator_le_top St le_rfl hV₁V
  have hc0 : c ≠ 0 := by
    rintro rfl
    norm_num at hc3
  have hci1 : c⁻¹ ≠ 1 := fun h1 => hc1 (inv_eq_one.mp h1)
  have hcic : c⁻¹ ≠ c := by
    intro h2
    have hsq : c ^ 2 = 1 := by
      rw [sq]
      nth_rewrite 1 [← h2]
      exact inv_mul_cancel₀ hc0
    apply hc1
    calc c = c ^ 3 * (c ^ 2)⁻¹ := by field_simp
      _ = 1 := by rw [hc3, hsq, inv_one, one_mul]
  have h1 : Multiset.count 1 (labMultiset l₀) = 1 := by
    rw [hm₀]
    simp [Multiset.count_replicate, hc1, Ne.symm hc1]
  have hωc : Multiset.count c (labMultiset l₀) = 1 := by
    rw [hm₀]
    simp [Multiset.count_replicate, hcic, hc1]
  have hUab : ∀ u ∈ conjClosure (fsuV T I) (Subgroup.normalizer (V₁ : Set G)),
      ∀ v ∈ conjClosure (fsuV T I) (Subgroup.normalizer (V₁ : Set G)), u * v * u⁻¹ * v⁻¹ ∈ V₁ :=
    fun u hu v hv => hyp.base.G22_commutator_mem hu hv
  have hΓV₁ : K ⊔ SecA.xOne X (LOf L V₁) ≤ Subgroup.normalizer (V₁ : Set G) :=
    sup_le h.K_le_normalizer_V₁ hX₁N
  have hVS : fsuV T I ≤ pCoreOf 2 (L ⊔ conjClosure (fsuV T I) (Subgroup.normalizer (V₁ : Set G))) :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((le_conjClosure _ _).trans le_sup_right) St.LU_le_normV St.isPGroup_V
  exact false_of_labels (Y := LOf L V₁ ⊔ SecA.xOne X (LOf L V₁))
    (Γ := K ⊔ SecA.xOne X (LOf L V₁)) (K := K) le_sup_left hxY (sup_le_sup_right h.L₁_le_K _)
    h.L₁_le_K (NatData3'.alpha0_surjective D le_rfl hV₁V)
    (le_inf (hV₁V.trans (le_conjClosure _ _)) (hV₁V.trans hVS)) htop.1 hUab hΓV₁
    (hΓV₁.trans (le_normalizer_conjClosure _ _)) hc1 hl₀ h1 hωc htop hO
    (hB_of_lemmaB414Head hB hN h1102 h hc St hV₁V hx hx1 hl₀)

end CFSG.Quasithin.Vol2.Ch11.SecS
