module

public import CFSG.Quasithin.EmptyFaithful.SzN28PLift
public import CFSG.Quasithin.EmptyFaithful.SzN28PTwLin
public import CFSG.Quasithin.EmptyFaithful.S142Bridge
public import CFSG.Quasithin.EmptyFaithful.S143VSq
public import CFSG.Quasithin.EmptyFaithful.S143WCl

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.G11

namespace SzN28P

theorem not_concl12 (h11 : StageLemma14111) (h113 : StageLemma14113)
    {G : Type} [Group G] [Finite G] {T M : Subgroup G} (hyp : Hyp1421 G T M)
    (hU : ¬ IsMulCommutative ↥(uOfL22 T M)) (D : HatModel T M) {g : G}
    (hg : GoodElt128 T (yOfL22 T M) g) :
    ¬ G112Concl12 (D.img (mcOf T)) (D.img (rconj (Hyp1281Two.wOfU T M) g)) := by
  intro hc
  have h1281 : Hyp1281Two G T M (yOfL22 T M) := hyp.hyp1281Two_of_inputs h11 h113
  obtain ⟨a, haV, haZ⟩ := h1281.exists_mem_VZ_not_mem
  have h101 := (h1281.lemma_12_8_12_three hU hg D haV haZ).toG101Hyp
  obtain ⟨hd, x, L, hxX, hLΓ, -, hdisj, hcomm, hcompl, hφψ, hX8, -⟩ := hc
  have hbot : D.img (rconj (centerOf (uOfL22 T M)) g) = ⊥ := by
    by_contra hne
    obtain ⟨k, hk⟩ := h101.exists_card_X
    have hrank := S143W.rank_le_of_ne_bot h101 hne hk
    have hk3 : k ≤ 3 := by
      by_contra hk4
      push Not at hk4
      have : 2 ^ 4 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk4
      omega
    omega
  have hZU := zu_eq_v1_of_img_rconj_bot h1281 hU hg D hbot
  have hker := S143V.centralizerHat_le_T h1281 hZU
  obtain ⟨E, hEle, hE9, hEc, hE3, hEfix⟩ := tw12_exists_E (h101.X_sq x hxX) hcomm hdisj hcompl hφψ
    h101.point (h101.X_fixes x hxX)
  have hxΓ : x ∈ D.img (mcOf T) := h101.X_le hxX
  have hEΓ : E ≤ D.img (mcOf T) := by
    refine hEle.trans (sup_le hLΓ ?_)
    rintro _ ⟨b, hb, rfl⟩
    exact (D.img (mcOf T)).mul_mem ((D.img (mcOf T)).mul_mem hxΓ (hLΓ hb))
      ((D.img (mcOf T)).inv_mem hxΓ)
  exact false_of_elem_three_two h1281 D hU haV haZ hZU hker hEΓ hE9 hEc hE3 hEfix

end SzN28P

end CFSG.Quasithin
