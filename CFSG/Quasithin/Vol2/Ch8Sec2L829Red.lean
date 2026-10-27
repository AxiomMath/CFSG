module

public import CFSG.Quasithin.Vol2.Ch8Sec2L829TA
public import CFSG.Quasithin.Vol2.Ch5Sec1Basic

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin

variable {G : Type} [Group G]

theorem ch82I_le_829 {H V : Subgroup G} {h : G} (hVH : V ≤ H) (hh : h ∈ H) :
    ch82I V h ≤ H := by
  refine sup_le hVH ?_
  intro x hx
  rw [B6.mem_conjSub] at hx
  have hx' := H.mul_mem (H.mul_mem hh (hVH hx)) (H.inv_mem hh)
  convert hx' using 1
  group

theorem T_normalizes_ch82I_829 [Finite G] {H M T V : Subgroup G} {h : G}
    (hT : QuasithinUnique.IsSylowTwoOf T H) (hVT : V ≤ T)
    (hTV : T ≤ Subgroup.normalizer (V : Set G)) (hh : h ∈ H) (hhI : h ∈ ch82I V h)
    (hP7 : H ⊓ M ≤ Subgroup.normalizer (V : Set G))
    (hY : oTwoUpper H ≤ ch82I V h ⊔ kerIn (H ⊓ M) H) :
    T ≤ Subgroup.normalizer (ch82I V h : Set G) := by
  have hTH : T ≤ H := hT.1
  have hVH : V ≤ H := hVT.trans hTH
  have hJV : kerIn (H ⊓ M) H ≤ Subgroup.normalizer (V : Set G) :=
    (kerIn_le).trans hP7
  have hIJ : ch82I V h ≤ Subgroup.normalizer (kerIn (H ⊓ M) H : Set G) :=
    (ch82I_le_829 hVH hh).trans (le_normalizer_kerIn _ _)
  have hTJ : T ≤ Subgroup.normalizer (kerIn (H ⊓ M) H : Set G) :=
    hTH.trans (le_normalizer_kerIn _ _)
  have hHY : H = oTwoUpper H ⊔ T := eq_oTwoUpper_sup_of_isSylowTwoOf' hT
  have hhY : h ∈ oTwoUpper H ⊔ T := by
    rw [← hHY]
    exact hh
  exact le_normalizer_ch82I_of_le_sup hhI hIJ hJV hTV hTJ
    (hTH.trans (le_normalizer_oTwoUpper H)) (hVH.trans (le_normalizer_oTwoUpper H)) hhY hY

theorem T_normalizes_pCore_ch82I_829 [Finite G] {H M T V : Subgroup G} {h : G}
    (hT : QuasithinUnique.IsSylowTwoOf T H) (hVT : V ≤ T)
    (hTV : T ≤ Subgroup.normalizer (V : Set G)) (hh : h ∈ H) (hhI : h ∈ ch82I V h)
    (hP7 : H ⊓ M ≤ Subgroup.normalizer (V : Set G))
    (hY : oTwoUpper H ≤ ch82I V h ⊔ kerIn (H ⊓ M) H) :
    T ≤ Subgroup.normalizer (pCoreOf 2 (ch82I V h) : Set G) :=
  (T_normalizes_ch82I_829 hT hVT hTV hh hhI hP7 hY).trans
    (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _)

end CFSG.Quasithin.H13
