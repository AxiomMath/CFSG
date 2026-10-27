module

public import CFSG.LocalAnalysis.StandardType.GGQ2TwoNodeBigHeart
public import CFSG.LocalAnalysis.StandardType.GGWAutDefs
import CFSG.LocalAnalysis.StandardType.GGQ2HypRestrict
import CFSG.LocalAnalysis.StandardType.GGWAutMonoNorm
import CFSG.LocalAnalysis.StandardType.GGWAutE
import CFSG.LocalAnalysis.StandardType.GGWAutCommon
import CFSG.LocalAnalysis.StandardType.GGLargeDepNoSymPerm

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Module QTwoLin

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V]

theorem ggQ2TN9_pm (hK : GGReflClassOmegaInput) [Module.Finite (ZMod 3) V]
    (A : Subgroup (V ≃ₗ[ZMod 3] V)) (hTF : TransvectionFree A)
    (hdim : Module.finrank (ZMod 3) V = 8) (c : Fin 8 → V) (α : Fin 8 → Module.Dual (ZMod 3) V)
    (hpair : ∀ i j, α i (c j) = (CartanMatrix.A 8 i j : ZMod 3))
    (s : Fin 8 → (V ≃ₗ[ZMod 3] V)) (hs : ∀ i v, s i v = v - α i v • c i) (hsA : ∀ i, s i ∈ A)
    (x : V) (hxH : x ∉ Submodule.span (ZMod 3) (Set.range c)) (hxfix : ∀ i, α i x = 0)
    (hStab : ∀ g ∈ A, g x = x → ∃ w ∈ Subgroup.closure (Set.range s), ∃ ε : ZMod 3,
      ∀ h ∈ Submodule.span (ZMod 3) (Set.range c), g h = ε • w h) :
    ∀ a ∈ A, ∃ r ∈ reflGp A, ∃ ε : ZMod 3, ε ≠ 0 ∧ a x = ε • r x := by
  classical
  obtain ⟨hH, hsup, -, hfix⟩ := ggQ2TN_heart hdim c α hpair x hxH hxfix
  have hconn := ggQ2TN_conn c α hpair
  have hαc : ∀ i, α i (c i) = 2 := by
    intro i
    rw [hpair i i]
    simp [CartanMatrix.A]
  have hsRefl : ∀ i, IsReflLin (s i) := by
    intro i
    refine ⟨c i, α i, hαc i, ?_⟩
    ext v
    rw [Module.reflection_apply, hs i v]
  have hsR : ∀ i, s i ∈ reflGp A := fun i => Subgroup.subset_closure ⟨hsA i, hsRefl i⟩
  have : Nonempty (Fin 8) := ⟨⟨0, by norm_num⟩⟩
  by_cases habs : ZS.AbsIrred 3 (reflGp A)
  swap
  · exact ggQ2Hyp_pm hK A hTF c α hαc s hs hsR x hfix hconn (by omega) (by omega) habs
  have hpm : ∀ a ∈ A, ∃ r ∈ reflGp A, (∀ v, a v = r v) ∨ (∀ v, a v = -(r v)) := by
    have hcardW : Nat.card (Subgroup.closure (Set.range s)) = (8 + 1).factorial :=
      l04fD5_P_card (p := 3) (by decide) (by norm_num) hpair s hs
    have hcard := ggQ2TN_card_le hdim A c s x hsup hcardW hStab
    have hRA : reflGp A ≤ A := ggWAut_reflGp_le A
    have hgen : reflGp A = Subgroup.closure {r | r ∈ reflGp A ∧ GGLinRefl r} :=
      ggWAut_reflGp_closure A
    have : Finite V := Module.finite_of_finite (ZMod 3)
    have : Finite (V ≃ₗ[ZMod 3] V) :=
      Finite.of_injective (fun g : V ≃ₗ[ZMod 3] V => (g : V → V)) DFunLike.coe_injective
    have : Finite A :=
      Finite.of_injective (fun a : A => (a : V ≃ₗ[ZMod 3] V)) Subtype.coe_injective
    have hbig : ¬ 3 ^ (8 * (8 - 1) / 2) ≤ 8 * Nat.card (reflGp A) := by
      intro h
      have h' := h.trans (Nat.mul_le_mul_left 8 ((Subgroup.card_le_of_le hRA).trans hcard))
      norm_num [Nat.factorial] at h'
    rcases hK.2 V 8 hdim (by norm_num) le_rfl (reflGp A) habs hgen with
      h1 | h2 | h3 | h4 | h5 | h6 | h7
    · exact ggWAut_imprim (by omega) A (reflGp A) hRA rfl habs h1
    · exact (ggWAut_SL_has_transvection (by omega) A (fun g hg => hRA (h2.1 g hg)) hTF).elim
    · exact (hbig h3.2).elim
    · exact absurd (by norm_num : 3 ∣ 8 + 1) h4.1
    · exact absurd h5.1 (by norm_num)
    · exact absurd h6.1 (by norm_num)
    · exact ggWAut_E8 A (reflGp A) hRA rfl habs h7.2
  intro a ha
  obtain ⟨r, hr, h | h⟩ := hpm a ha
  · exact ⟨r, hr, 1, one_ne_zero, by rw [h, one_smul]⟩
  · exact ⟨r, hr, -1, by decide, by rw [h, neg_one_smul]⟩

end CFSG.StandardType

end
