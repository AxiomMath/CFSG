module

public import CFSG.LocalAnalysis.WeakClosure81.SixThirteen
public import CFSG.LocalAnalysis.WeakClosure81.SixFifteen
public import CFSG.LocalAnalysis.WeakClosure81.FourteenTwo
public import CFSG.LocalAnalysis.WeakClosure81.FourteenFour

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22
open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

structure Std15 (G : Type) [Group G] [Finite G] : Prop where
  charTwo : IsCharTwoType G
  localsK : ∀ H : Subgroup G, IsTwoLocal H → CFSG.Open.IsKGroup ↥H

structure Hyp15 (M V₀ V : Subgroup G) : Prop where
  h6 : Hyp6H M V₀ V
  ne_bot : V₀ ≠ ⊥
  even : Even ((M ⊓ centralizer (V : Set G)).relIndex (F11.CTilde M V₀ V))
  hyp14a : ∀ X : Subgroup G, X ≤ M → M ⊓ centralizer (V : Set G) ≤ X →
    (X : Set G) * (F11.CTilde M V₀ V : Set G) = (M : Set G) → UniqueMax M X
  hyp14b : ¬ M ⊓ centralizer (V₀ : Set G) ≤ F11.CTilde M V₀ V
  qclause : ∀ Q : Subgroup G, IsSylowIn 2 Q (M ⊓ centralizer (V : Set G)) →
    UniqueMax M (M ⊓ normalizer (Q : Set G))

structure Cex15 (M V₀ V U S : Subgroup G) : Prop where
  hyp : Hyp15 M V₀ V
  mbar : 1 < mBar M V₀ V hyp.h6.elemAbelian
  le : U ≤ V
  not_le : ¬ centralizer (U : Set G) ≤ M
  mquot : (E3.mQuot V U : ℕ∞) = rMV M V
  small : rMV M V ≤ (mSub V₀ : ℕ∞)
  sylow : IsSylowIn 2 S (M ⊓ centralizer (U : Set G))

theorem Hyp15.of_setting {D : Data G} {V₀ V : Subgroup G}
    (h : WeakClosureSetting D V₀ V) (hV₀ : V₀ ≠ ⊥) : Hyp15 D.M V₀ V := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact ⟨⟨h.pair.elemAbelian, h.normalizer_eq, h.pair.le, h.pair.le_normalizer₀,
    fun hh => (h.ti₀ hh).2, fun hh => (h.ti₀ hh).1, h.normalizer₀,
    fun hh v hv hv₀ => (h.gen hh v hv hv₀).symm⟩, hV₀, h.even hV₀, h.hyp14₂ hV₀,
    h.hyp14₁ hV₀, fun Q hQ => h.v1 Q ((CFSG.ABGLocalTools.isSylowOf_iff (p := 2)).2 hQ)⟩

theorem Std15.of_data (D : Data G) : Std15 G := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨D.standing.charTwo, fun H hH => ?_⟩
  obtain ⟨P, hP, hP2, rfl⟩ := hH
  refine D.standing.kProper.isKGroup _ fun htop => ?_
  haveI : P.Normal := Subgroup.normalizer_eq_top_iff.1 htop
  haveI := D.standing.simple
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal P with h | h
  · exact hP h
  · subst h
    have hG : IsPGroup 2 G := by
      intro g
      obtain ⟨k, hk⟩ := hP2 ⟨g, Subgroup.mem_top g⟩
      exact ⟨k, congrArg Subtype.val hk⟩
    obtain ⟨a, b, hab⟩ := D.standing.nonab
    haveI := hG.center_nontrivial
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center G) with hc | hc
    · obtain ⟨x, hx⟩ := exists_ne (1 : Subgroup.center G)
      exact hx (Subtype.ext ((Subgroup.mem_bot.1 (hc ▸ x.2))))
    · exact hab (Subgroup.mem_center_iff.1 (hc ▸ Subgroup.mem_top b) a)

namespace Hyp15

variable {M V₀ V : Subgroup G}

theorem le_M (h : Hyp15 M V₀ V) : V ≤ M := h.h6.le_M

theorem isTI (h : Hyp15 M V₀ V) : CFSG.CGT.Timmesfeld75.IsTI V₀ := h.h6.isTI h.ne_bot

theorem normalizer₀ (h : Hyp15 M V₀ V) : normalizer (V₀ : Set G) = M :=
  h.h6.normalizer₀ h.ne_bot

theorem isPGroup (h : Hyp15 M V₀ V) : IsPGroup 2 V := B2F.isPGroup_of_isElemAbelian h.h6.elemAbelian

theorem elemAbelian₀ (h : Hyp15 M V₀ V) : IsElemAbelian 2 V₀ :=
  CFSG.Open.IsElemAbelian.mono h.h6.elemAbelian h.h6.le

theorem centralizer_le (h : Hyp15 M V₀ V) {w : G} (hw : w ∈ V₀) (hw1 : w ≠ 1) :
    centralizer ({w} : Set G) ≤ M := by
  have := centralizer_le_normalizer_of_isTI h.isTI hw hw1
  rwa [h.normalizer₀] at this

theorem conj_inf_eq_bot (h : Hyp15 M V₀ V) {g : G} (hg : g ∉ M) :
    conjSubgroup V₀ g ⊓ V₀ = ⊥ :=
  conjSubgroup_inf_self_eq_bot h.normalizer₀ h.isTI hg

theorem uniqueMax_self (h : Hyp15 M V₀ V) : UniqueMax M M := by
  refine h.hyp14a M le_rfl inf_le_left ?_
  refine Set.Subset.antisymm ?_ fun x hx => ⟨x, hx, 1, (F11.CTilde M V₀ V).one_mem, mul_one x⟩
  rintro _ ⟨a, ha, b, hb, rfl⟩
  exact M.mul_mem ha (cTilde_le_M M V₀ V hb)

theorem isMax (h : Hyp15 M V₀ V) : rankThreeIsMaxTwoLocal M := by
  have h1 : calMOf M = {M} := h.uniqueMax_self
  have h2 : M ∈ calMOf M := by rw [h1]; exact Set.mem_singleton M
  exact h2.1

theorem s14c (h : Hyp15 M V₀ V) : FourteenTwo.S14c M V₀ V := by
  intro U hUV hU1 hCU hmul
  have hX : UniqueMax M (M ⊓ normalizer (U : Set G)) := by
    refine h.hyp14a _ inf_le_left hCU ?_
    refine Set.Subset.antisymm ?_ fun m hm => ?_
    · rintro _ ⟨a, ha, b, hb, rfl⟩
      exact M.mul_mem ha.1 (cTilde_le_M M V₀ V hb)
    · obtain ⟨x, hx, c, hc, rfl⟩ := hmul m hm
      exact ⟨x, hx, c, hc, rfl⟩
  exact normalizer_le_of_inCalU hX inf_le_right hU1 (h.isPGroup.to_le hUV)

theorem exists_cTilde_not_le (h : Hyp15 M V₀ V) :
    ∃ a ∈ F11.CTilde M V₀ V, a ∉ centralizer (V : Set G) := by
  by_contra hcon
  have hle : F11.CTilde M V₀ V ≤ M ⊓ centralizer (V : Set G) :=
    fun a ha => ⟨cTilde_le_M M V₀ V ha, by_contra fun hn => hcon ⟨a, ha, hn⟩⟩
  have h1 : (M ⊓ centralizer (V : Set G)).relIndex (F11.CTilde M V₀ V) = 1 :=
    Subgroup.relIndex_eq_one.2 hle
  have := h.even
  rw [h1] at this
  exact absurd this (by decide)

end Hyp15

end CFSG.LocalAnalysis.WeakClosure81
