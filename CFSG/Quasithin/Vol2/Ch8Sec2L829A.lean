module

public import CFSG.Quasithin.Vol2.Ch8Sec2L825H

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin.E3 CFSG.Quasithin.H CFSG.Quasithin.ASInputs

section L829A

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem not_le_normalizer_ch82I_82 {M V : Subgroup G} {h : G} (hV : IsElemAbelian 2 V)
    (hhI : h ∈ ch82I V h)
    (hker : kerIn (M ⊓ ch82I V h) (ch82I V h) = pCoreOf 2 (ch82I V h))
    (hnt : Nontrivial (E2.StarQuot (M ⊓ ch82I V h) (ch82I V h))) :
    ¬ ch82I V h ≤ Subgroup.normalizer (V : Set G) := by
  intro hIN
  apply star_ne_bot_82 hhI hker hnt
  have hVO : V ≤ pCoreOf 2 (ch82I V h) :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 le_sup_left hIN
      (B2F.isPGroup_of_isElemAbelian hV)
  rw [eq_bot_iff]
  rintro _ ⟨v, hv, rfl⟩
  rw [Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf,
    hker]
  exact hVO hv

theorem eq_ch82I_sup_82 {T M V H : Subgroup G} {h : G} (hT : quasithinIsSylowTwo T)
    (hH : IsHStar T M H) (hIH : ch82I V h ≤ H)
    (hMI : M ⊓ ch82I V h = ch82I V h ⊓ Subgroup.normalizer (V : Set G))
    (hIN : ¬ ch82I V h ≤ Subgroup.normalizer (V : Set G)) : H = ch82I V h ⊔ T := by
  obtain ⟨P, hP⟩ := exists_sylow_of_quasithinIsSylowTwo hT
  have hYH : ch82I V h ⊔ T ≤ H := sup_le hIH hH.1.1
  have hY : InH T (ch82I V h ⊔ T) := by
    have h1 := inH_of_le P (hP ▸ le_sup_right) hYH (hP ▸ hH.1)
    rwa [hP] at h1
  refine (hH.2.2 _ hY hYH fun hle => hIN ?_).symm
  have h1 : ch82I V h ≤ M ⊓ ch82I V h := le_inf (le_sup_left.trans hle) le_rfl
  rw [hMI] at h1
  exact h1.trans inf_le_right

end L829A

end CFSG.Quasithin.H13
