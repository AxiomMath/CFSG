module

public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4UF4
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4UFrameSmall

public section

namespace CFSG.StandardType.TableCRes

section Input

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.HardMathSupport.Timmesfeld.LangTorus
open CFSG.Assembly (LargeEvenLabel LargeEvenInLambda2)

@[expose] def LangFamilyCompFieldF4Data :
    Prop :=
  LangFamilyCompFieldF4

end Input

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.Blueprint CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.RankThree.PartOne.KE

theorem uFieldInputSmall_of_F4Data
    (hR : LangFamilyCompFieldF4Data) : UFieldInputSmall .F4 :=
  fun L _ _ _ p₀ p S hp hp2 ι a haT hap K hK => hR L p₀ p S hp hp2 ι a haT hap K hK

section Leaf

theorem card_le_F4_of_fieldData
    (hR : LangFamilyCompFieldF4Data)
    {X : Type} [Group X] [Finite X] {n f p : ℕ} {G₀ B D J L : Subgroup X} {x : X}
    {ψ : (ggU .F4 n f).K →* X} (h : GGTCHyp .F4 n f ψ p G₀ B D J L x)
    (hF : GGSixLSevenFieldExtCase J .F4 f) : Nat.card B ≤ p ^ 3 := by
  by_contra hlt
  push Not at hlt
  have hp := h.prime
  have hp2 := h.ne_two
  have hmod : UntwistedChevalleyModel (↥G₀ ⧸ Subgroup.center ↥G₀) .F4 (2 ^ f) :=
    ((LieModel.chevalleyExceptional_iff (by decide)).1 h.model).2.2
  have hBpos : 0 < Nat.card B := Nat.card_pos
  have hTor : UToralAt .F4 p (Nat.card B) := by
    by_cases hp3 : p = 3
    · subst hp3
      have hpg : IsPGroup 3 B := fun g => ⟨1, by
        rw [pow_one]
        exact Subtype.ext ((Subgroup.coe_pow _ g 3).trans (h.b_elem.2 g g.2))⟩
      obtain ⟨k, hk⟩ := hpg.exists_card_eq
      have hk4 : 4 ≤ k := by
        by_contra hk3
        push Not at hk3
        have := Nat.pow_le_pow_right (by norm_num : 0 < 3) (by omega : k ≤ 3)
        omega
      exact utoralAt_F4_three (by rw [hk]; exact Nat.pow_le_pow_right (by norm_num) hk4)
    · exact utoralAt_of_nonTorsion hp hp2 (fun _ => hp3) (fun h => by cases h) hBpos
  obtain ⟨t', m, f', hflt, hm, -⟩ := hF
  obtain ⟨Ψ, ρ, hΨ, hρR, hρ, horth, hcard, -⟩ :=
    uframe_main_small (uFieldInputSmall_of_F4Data hR)
    (Or.inl rfl) hp hp2 hmod h.b_norm h.inner_F4 h.b_faithful h.b_elem h.d_le h.d_card
    (h.j_comp.1.trans inf_le_left) (Assembly.isComponentOf_iff_open.1 h.j_comp) h.j_cent
    ⟨t', m, f', hflt, hm⟩ hTor
  have hr := f4_finrank_le_one hΨ hρR hρ horth
  exact absurd (hcard.trans (Nat.pow_le_pow_right hp.pos (by omega))) (not_le.2 hlt)

theorem ggTCAt_F4_of_fieldData
    (hR : LangFamilyCompFieldF4Data) : GGTCAt .F4 := by
  intro X _ _ n f ψ p G₀ B D J L x h hF _
  exfalso
  have h3 := card_le_F4_of_fieldData hR h hF
  have h4 := h.b_card
  have hlt := Nat.pow_lt_pow_right (by have := h.prime.two_le; omega : 1 < p) (by norm_num : 3 < 4)
  omega

end Leaf

end CFSG.StandardType.TableCRes
