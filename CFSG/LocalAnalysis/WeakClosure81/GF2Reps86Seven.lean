module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps86SevenIrr
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps86Swap
import CFSG.Quasithin.Background.A7Q528Class
import CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive.Base7Nat
import CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive.ToolShape
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps86Tools

public section

namespace CFSG.LocalAnalysis.WeakClosure81.GF2Reps86

open CFSG.Quasithin CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive Equiv
open CFSG.LocalAnalysis.UniquenessCase.PartTwo (IsIrrOn)
open CFSG.RankThree.PartTwo (altHeart)
open CFSG.HardMathSupport.Cooperstein.Coordinator (altAct)

private theorem index_mul_index_le_card {V : Type} [CommGroup V] [Finite V]
    (hV : ∀ v : V, v ^ 2 = 1) {c : MulAut V} (hc : c ^ 2 = 1) :
    (fixV (Subgroup.zpowers c)).index * (fixV (Subgroup.zpowers c)).index ≤ Nat.card V := by
  have hle : commV (Subgroup.zpowers c) ≤ fixV (Subgroup.zpowers c) := fun v hv =>
    mem_fixV_zpowers_iff_apply.2 (apply_eq_of_mem_commV_zpowers hV hc hv)
  calc (fixV (Subgroup.zpowers c)).index * (fixV (Subgroup.zpowers c)).index
      = (fixV (Subgroup.zpowers c)).index * Nat.card (commV (Subgroup.zpowers c)) := by
        rw [card_commV_zpowers hV hc]
    _ ≤ (fixV (Subgroup.zpowers c)).index * Nat.card (fixV (Subgroup.zpowers c)) :=
        Nat.mul_le_mul_left _ (Subgroup.card_le_of_le hle)
    _ = Nat.card V := (fixV (Subgroup.zpowers c)).index_mul_card

private theorem coreHeart_seven_injective : Function.Injective (coreHeart 7) := by
  refine (injective_iff_map_eq_one _).2 fun m hm => ?_
  have h1 := (coreHeart_eq_one_iff (by norm_num) m).1 hm
  rw [Subgroup.mem_subgroupOf, zpowers_allOnes_inf_coreMod_seven, Subgroup.mem_bot] at h1
  exact Subtype.ext h1

theorem seven_irr {V : Type} [CommGroup V] [Finite V] (hV : ∀ v : V, v ^ 2 = 1)
    {H : Subgroup (MulAut V)} {ψ : ↥H →* Perm (Fin 7)} (hψ : Function.Injective ψ)
    (hA : alternatingGroup (Fin 7) ≤ ψ.range) (hirr : IsIrrOn H ⊤ ⊥) {t : ↥H}
    (ht : t ^ 2 = 1) (ht1 : ψ t ≠ 1) (hsw : ¬ (ψ t).IsSwap)
    (hidx : (fixV (Subgroup.zpowers (t : MulAut V))).index ≤ 8) :
    NatVia ψ ⊤ ∨ (Nat.card V = 2 ^ 4 ∧ ψ.range = alternatingGroup (Fin 7)) := by
  let _ : Module (ZMod 2) (Additive V) := AddCommGroup.zmodModule (n := 2) fun x => by
    rw [two_nsmul]
    apply Additive.toMul.injective
    rw [toMul_add, toMul_zero, ← sq]
    exact hV _
  have hfix := fixV_altPre_eq_bot (by norm_num) hA hirr
  have hLirr := isIrrOn_altPre_seven hV hψ hA hirr ht ht1 hsw hidx
  have hcard : Nat.card V ≤ 2 ^ 12 := by
    have h1 := card_commV_altPre_le_seven hψ hA ht ht1 hsw
    rw [commV_eq_top_of_fixV_eq_bot hLirr le_rfl hfix, Subgroup.card_top] at h1
    exact h1.trans ((Nat.pow_le_pow_left hidx 3).trans (by norm_num))
  rcases CFSG.Quasithin.A7Q528.classify4 (altPreEquiv hψ hA)
      (fun J hJ => hLirr.2.2.2 J hJ bot_le le_top) hfix hcard with ⟨β, hβ⟩ | ⟨-, -, Ψ, -⟩
  ·
    left
    let π : ↥(⊤ : Subgroup V) →* Multiplicative (altHeart 7) :=
      (coreHeart 7).comp (β.toMonoidHom.comp Subgroup.topEquiv.toMonoidHom)
    have hshape : NatShape (altRho hψ hA) (alternatingGroup (Fin 7)).subtype := by
      refine ⟨⊥, ⊤, bot_le, fun g v hv => ?_, fun g v => Subgroup.mem_top _, π, ?_, ?_, ?_⟩
      · rw [Subgroup.mem_bot] at hv
        rw [hv, map_one]
      · intro y
        obtain ⟨m, rfl⟩ := coreHeart_surjective 7 y
        refine ⟨⟨β.symm m, Subgroup.mem_top _⟩, ?_⟩
        change coreHeart 7 (β (β.symm m)) = coreHeart 7 m
        rw [MulEquiv.apply_symm_apply]
      · rw [Subgroup.bot_subgroupOf, MonoidHom.ker_eq_bot_iff]
        exact coreHeart_seven_injective.comp (β.injective.comp Subgroup.topEquiv.injective)
      · intro g u v huv
        have hb : β (v : V) = ⟨G6.permAct 7 (g : Perm (Fin 7)) (β (u : V)),
            G6.permAct_mem_coreMod _ (β (u : V)).2⟩ :=
          Subtype.ext (by rw [huv]; exact hβ g u)
        change Multiplicative.toAdd (coreHeart 7 (β (v : V))) =
          altAct (g : Perm (Fin 7)) (Multiplicative.toAdd (coreHeart 7 (β (u : V))))
        rw [hb, toAdd_coreHeart_permAct]
    have h := natVia_commV_of_natShape le_rfl hψ hA hshape
    rwa [commV_eq_top_of_fixV_eq_bot hirr altPre_le hfix] at h
  ·
    have hV16 : Nat.card V = 2 ^ 4 := by
      have h1 : Nat.card (CFSG.QuasithinUnique.Setup.X3E.Vec 4) = Nat.card (Additive V) :=
        Nat.card_congr Ψ.toEquiv
      have h2 : Nat.card (CFSG.QuasithinUnique.Setup.X3E.Vec 4) = 2 ^ 4 := by
        simp [Nat.card_eq_fintype_card]
      exact h1.symm.trans h2
    by_cases hr : ψ.range = alternatingGroup (Fin 7)
    · exact Or.inr ⟨hV16, hr⟩
    left
    obtain ⟨x, hxr, hxA⟩ : ∃ x ∈ ψ.range, x ∉ alternatingGroup (Fin 7) := by
      by_contra hc
      push Not at hc
      exact hr (le_antisymm hc hA)
    have hsx : Perm.sign x = -1 := by
      rw [Perm.mem_alternatingGroup] at hxA
      rcases Int.units_eq_one_or (Perm.sign x) with h | h
      · exact absurd h hxA
      · exact h
    obtain ⟨τ, hτ⟩ : swap (0 : Fin 7) 1 ∈ ψ.range := by
      have hy : x⁻¹ * swap (0 : Fin 7) 1 ∈ alternatingGroup (Fin 7) := by
        rw [Perm.mem_alternatingGroup, Perm.sign_mul, Perm.sign_inv, hsx,
          Perm.sign_swap (by decide), Int.units_mul_self]
      have h := ψ.range.mul_mem hxr (hA hy)
      rwa [mul_inv_cancel_left] at h
    have hτ2 : (τ : MulAut V) ^ 2 = 1 := by
      have h1 : τ ^ 2 = 1 := hψ (by rw [map_pow, hτ, map_one, sq, swap_mul_self])
      simpa using congrArg Subtype.val h1
    have hidxτ : (fixV (Subgroup.zpowers (τ : MulAut V))).index ≤ 8 := by
      have h := index_mul_index_le_card hV hτ2
      rw [hV16] at h
      nlinarith
    exact natVia_top_of_swap hV le_rfl hψ hA hirr hfix ⟨0, 1, by decide, hτ⟩ hidxτ

end CFSG.LocalAnalysis.WeakClosure81.GF2Reps86

end
