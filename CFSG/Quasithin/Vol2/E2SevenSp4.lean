module

public import CFSG.Quasithin.Vol2.E2SevenCases
public import CFSG.Quasithin.Vol2.E2TenEight

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique B6

namespace E2

variable {G : Type} [Group G] [Finite G] {H T M V : Subgroup G}

omit [Finite G] in
theorem isSimpleGroup_of_isSp4Prime {X : Type} [Group X] {n : ℕ} (h : IsSp4Prime n X) :
    IsSimpleGroup X := by
  unfold IsSp4Prime at h
  split_ifs at h with hn
  · obtain ⟨e⟩ := h
    have : IsSimpleGroup (alternatingGroup (Fin 6)) :=
      alternatingGroup.isSimpleGroup (by simp)
    exact e.isSimpleGroup
  · exact isSimpleGroup_of_isPSp4 h

theorem exists_isInIHTVC_of_sp4 (hKG7 : E27Sp4) (h : Hyp28 H T M V) (hJ : kerIn M H = ⊥)
    {K : Subgroup G} (hKc : K ∈ cComp H) (hHK : H = K ⊔ T)
    (hTK : T ≤ Subgroup.normalizer (K : Set G)) {n : ℕ} (hn1 : 1 ≤ n)
    (hSp : IsSp4Prime n ↥(star M H K))
    (hD : IsDiagramNontrivial (star M H T) (star M H K) (star M H (T ⊓ K)))
    (hB : IsBorelIn (star M H K) (star M H (M ⊓ K)))
    (hnstar : E1.nParam (⊤ : Subgroup (StarQuot M H)) = n) (hSQs : SQTKGroup (StarQuot M H))
    (hV4 : 4 ≤ Nat.card V) : ∃ I : Subgroup G, ASInputs.IsInIHTVC H T M V I := by
  have := E2P.finite_starQuot M H
  have hKH : K ≤ H := le_of_mem_cComp hKc
  have hY28 := h.star (sqtkGroup_top hSQs)
  have hC := starCase2_of h hKc hHK hTK (isSimpleGroup_of_isSp4Prime hSp)
  have hMK := star_inf_eq_of_isBorelIn h.minParabolic hC.normal hB
  rw [E2P.star_inf_T h.minParabolic.isSylow hKc.2.2.1 hKH] at hD
  have hV4s : 4 ≤ Nat.card ↥(star M H V) := by
    rw [card_star_of_kerIn_eq_bot hJ h.le_H]
    exact hV4
  obtain ⟨I₀, hI₀⟩ := hKG7 (StarQuot M H) ⊤ (star M H T) (star M H M) (star M H K)
    (star M H V) n hY28 (E2P.kerIn_star M H) le_top hC.normal
    (by rw [top_inf_eq]; exact hC.cent) hC.sup hn1 hSp hD hMK hnstar hV4s
  exact exists_isInIHTVC_of_star h (nParam_star_of_kerIn_eq_bot hJ) hI₀

end E2

end CFSG.Quasithin
