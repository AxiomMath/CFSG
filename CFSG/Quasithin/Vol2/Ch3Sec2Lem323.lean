module

public import CFSG.Quasithin.Vol2.Ch3Sec2IrrPlus
public import CFSG.Quasithin.H13.StatementsL4
public import CFSG.Quasithin.Background.BlueprintB2Reduced
public import CFSG.Quasithin.Vol2.Ch1Unique
public import CFSG.Quasithin.Vol2.Ch1A3Cat
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A3Native36

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique.Vol2Native
open scoped IsMulCommutative

theorem conjClosure_sup_eq {G : Type} [Group G] (L T : Subgroup G) :
    conjClosure L T ⊔ T = L ⊔ T := by
  apply le_antisymm
  · refine sup_le (conjClosure_le fun t ht l hl => ?_) le_sup_right
    exact (L ⊔ T).mul_mem ((L ⊔ T).mul_mem (Subgroup.mem_sup_right ht)
      (Subgroup.mem_sup_left hl)) ((L ⊔ T).inv_mem (Subgroup.mem_sup_right ht))
  · exact sup_le ((le_conjClosure L T).trans le_sup_left) le_sup_right

theorem le_normalizer_map_subtype {G : Type} [Group G] (Y : Subgroup G) (R : Subgroup ↥Y)
    [R.Normal] : Y ≤ Subgroup.normalizer ((R.map Y.subtype : Subgroup G) : Set G) := by
  have h := Subgroup.le_normalizer_map (H := R) Y.subtype
  rw [Subgroup.normalizer_eq_top, map_subtype_top] at h
  exact h

theorem stmt3_2_3_of (h37 : A37ForSQTKCat) (h38 : A38ForSQTKCat) (h39 : A39ForSQTKCat) :
    Stmt3_2_3 := by
  intro G _ _ T L hs hnab hK hT hL hLf hq
  have hsup : conjClosure L T ⊔ T = L ⊔ T := conjClosure_sup_eq L T
  have hU := lemma_1_2_7_three hK hs hnab (a37ForSQTK_of_cat h37) (a38ForSQTK_of_cat h38)
    (a39ForSQTK_of_cat h39) hT hL
  refine ⟨⟨hU.1.1, le_sup_right.trans hU.1.2⟩,
    ⟨hsup ▸ hU.1.2, fun M' hM' hle => hU.2 M' ⟨hM', hsup ▸ hle⟩⟩, fun I hI => ?_⟩
  set Y : Subgroup G := conjClosure L T ⊔ T with hY
  have hR := primeReducedAggregate_normal_elementaryAbelian (E := ↥Y) 2
  haveI := hR.1
  haveI := hR.2.1
  have hA2 : ∀ a ∈ reducedAggregate Y, a ^ 2 = 1 := by
    intro a ha
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 ha
    rw [← map_pow, CFSG.elemPow_eq_one_of_isElementaryAbelian y hy, map_one]
  have hYN := le_normalizer_map_subtype Y (primeReducedAggregate ↥Y 2)
  have hX : conjClosure L T ≤ Subgroup.normalizer ((reducedAggregate Y : Subgroup G) : Set G) :=
    le_sup_left.trans hYN
  have hTN : T ≤ Subgroup.normalizer ((reducedAggregate Y : Subgroup G) : Set G) :=
    le_sup_right.trans hYN
  obtain ⟨V₀, hV₀, hiso⟩ := exists_isIrrPlusIn_sectionIso hA2 hX hTN
    (le_normalizer_conjClosure L T) hT.1 hI
  refine ⟨V₀, hV₀, hiso, ⟨hs, hnab, hK, hT, hL, hLf, hq, ?_⟩⟩
  rw [← hsup]
  exact hV₀

theorem stmt3_2_3_of_a38_a39
    (h38 : A38ForSQTKCat) (h39 : A39ForSQTKCat) : Stmt3_2_3 :=
  stmt3_2_3_of a37ForSQTKCat_proved h38 h39

end CFSG.Quasithin.H13
