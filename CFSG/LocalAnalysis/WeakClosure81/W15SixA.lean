module

public import CFSG.LocalAnalysis.WeakClosure81.W15Weak
public import CFSG.LocalAnalysis.QuasithinUnique.CharTwoInheritance
public import CFSG.LocalAnalysis.WeakClosure81.SevenThree

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22
open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

private theorem isElemAbelian_closure {S : Set G} (hcomm : ∀ a ∈ S, ∀ b ∈ S, a * b = b * a)
    (hsq : ∀ a ∈ S, a ^ 2 = 1) : IsElemAbelian 2 (Subgroup.closure S) := by
  have h1 : ∀ x ∈ Subgroup.closure S, ∀ b ∈ S, x * b = b * x := by
    intro x hx b hb
    have hle : Subgroup.closure S ≤ Subgroup.centralizer ({b} : Set G) := by
      rw [Subgroup.closure_le]
      intro a ha
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst hy
      exact hcomm y hb a ha
    exact (Subgroup.mem_centralizer_iff.1 (hle hx) b (Set.mem_singleton b)).symm
  have h2 : ∀ x ∈ Subgroup.closure S, ∀ y ∈ Subgroup.closure S, x * y = y * x := by
    intro x hx y hy
    have hle : Subgroup.closure S ≤ Subgroup.centralizer ({x} : Set G) := by
      rw [Subgroup.closure_le]
      intro a ha
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
      intro z hz
      rw [Set.mem_singleton_iff] at hz
      subst hz
      exact h1 z hx a ha
    exact Subgroup.mem_centralizer_iff.1 (hle hy) x (Set.mem_singleton x)
  refine ⟨⟨⟨fun a b => Subtype.ext (h2 a a.2 b b.2)⟩⟩, ?_⟩
  intro x hx
  induction hx using Subgroup.closure_induction with
  | mem a ha => exact hsq a ha
  | one => exact one_pow 2
  | mul a b ha hb iha ihb =>
    rw [(show Commute a b from h2 a ha b hb).mul_pow, iha, ihb, mul_one]
  | inv a ha iha => rw [inv_pow, iha, inv_one]

namespace Cex15

variable {M V₀ V U S : Subgroup G}

theorem V₀_le_centralizer (h : Cex15 M V₀ V U S) : V₀ ≤ centralizer (U : Set G) :=
  h.V₀_le_S.trans h.S_le_centralizer

theorem charTwo_centralizer (hS : Std15 G) (h : Cex15 M V₀ V U S) :
    CFSG.QuasithinUnique.CharTwo (centralizer (U : Set G)) := by
  have hU2 : IsPGroup 2 U := h.hyp.isPGroup.to_le h.le
  have hN : CFSG.QuasithinUnique.CharTwo (normalizer (U : Set G)) :=
    hS.charTwo _ ⟨U, h.ne_bot, hU2, rfl⟩
  have h1 := CFSG.QuasithinUnique.CharTwo.inf_centralizer hN Subgroup.le_normalizer hU2
  rwa [inf_eq_right.2 (Subgroup.centralizer_le_normalizer (U : Set G))] at h1

theorem isKGroup_of_le (hS : Std15 G) (h : Cex15 M V₀ V U S) {X : Subgroup G}
    (hX : X ≤ centralizer (U : Set G)) : CFSG.Open.IsKGroup ↥X := by
  have hU2 : IsPGroup 2 U := h.hyp.isPGroup.to_le h.le
  exact (hS.localsK _ ⟨U, h.ne_bot, hU2, rfl⟩).of_le
    (hX.trans (Subgroup.centralizer_le_normalizer (U : Set G)))

theorem isCalH (hS : Std15 G) (h : Cex15 M V₀ V U S) : IsCalH V₀ (centralizer (U : Set G)) := by
  refine ⟨h.V₀_le_centralizer, h.charTwo_centralizer hS, ?_⟩
  rw [h.hyp.normalizer₀]
  have hSle : S ≤ centralizer (U : Set G) ⊓ M := le_inf h.S_le_centralizer h.S_le_M
  have h1 := Subgroup.relIndex_mul_relIndex S (centralizer (U : Set G) ⊓ M)
    (centralizer (U : Set G)) hSle inf_le_left
  have hodd : ¬ 2 ∣ S.relIndex (centralizer (U : Set G)) := h.isSylowIn_centralizer.not_dvd_relIndex
  have hdvd : (centralizer (U : Set G) ⊓ M).relIndex (centralizer (U : Set G)) ∣
      S.relIndex (centralizer (U : Set G)) := h1 ▸ Dvd.intro_left _ rfl
  exact Nat.odd_iff.2 (by
    have : ¬ 2 ∣ (centralizer (U : Set G) ⊓ M).relIndex (centralizer (U : Set G)) :=
      fun hd => hodd (hd.trans hdvd)
    omega)

theorem isSylowIn_inf (h : Cex15 M V₀ V U S) :
    IsSylowIn 2 S (centralizer (U : Set G) ⊓ normalizer (V₀ : Set G)) := by
  rw [h.hyp.normalizer₀, inf_comm]
  exact h.sylow

theorem commute_conj_of_le_pCoreOf (hS : Std15 G) (h : Cex15 M V₀ V U S)
    (hCH : V₀ ≤ pCoreOf 2 (centralizer (U : Set G))) {x y : G}
    (hx : x ∈ centralizer (U : Set G)) (hy : y ∈ centralizer (U : Set G)) :
    ∀ u ∈ conjSubgroup V₀ x, ∀ v ∈ conjSubgroup V₀ y, u * v = v * u := by
  have hH := h.hyp
  have hCal := h.isCalH hS
  have hT := h.isSylowIn_inf
  have hZ : V₀ ⊓ centralizer (S : Set G) ≠ ⊥ :=
    inf_centralizer_ne_bot hH.elemAbelian₀ hH.ne_bot hCal hT
  have hE := eSub_isElemAbelian hH.elemAbelian₀ hCal hT
  have hCU : conjSubgroup V₀ x ⊓ centralizer (eSub V₀ (centralizer (U : Set G)) S : Set G) ≠ ⊥ := by
    intro hbot
    apply hZ
    have h1 : conjSubgroup (V₀ ⊓ centralizer (S : Set G)) x ≤
        conjSubgroup V₀ x ⊓ centralizer (eSub V₀ (centralizer (U : Set G)) S : Set G) := by
      refine le_inf (E3.conjSubgroup_mono_left x inf_le_left) ?_
      intro a ha
      have haE : a ∈ eSub V₀ (centralizer (U : Set G)) S := conjSubgroup_le_conjClosure _ _ hx ha
      exact Subgroup.mem_centralizer_iff.2 fun b hb => B2F.isElemAbelian_comm hE hb haE
    rw [hbot, le_bot_iff, conjSubgroup_eq_bot_iff] at h1
    exact h1
  rcases eight_two hH.elemAbelian₀ hH.isTI hH.ne_bot hCal hT ⟨x, rfl⟩
      (conjSubgroup_le_of_le h.V₀_le_centralizer hx) hCU with h2 | ⟨hnot, -⟩
  · exact h2 y hy
  · exact absurd ⟨hCal, hCH⟩ hnot

theorem conjClosure_isElemAbelian (hS : Std15 G) (h : Cex15 M V₀ V U S)
    (hCH : V₀ ≤ pCoreOf 2 (centralizer (U : Set G))) :
    IsElemAbelian 2 (conjClosure V₀ (centralizer (U : Set G))) := by
  have hel := h.hyp.elemAbelian₀
  have hmem : ∀ {a z : G}, z ∈ V₀ → a * z * a⁻¹ ∈ conjSubgroup V₀ a⁻¹ := fun {a z} hz =>
    mem_conjSubgroup_iff.2 (by simpa [mul_assoc] using hz)
  refine isElemAbelian_closure ?_ ?_
  · rintro _ ⟨a, ha, z, hz, rfl⟩ _ ⟨b, hb, w, hw, rfl⟩
    exact h.commute_conj_of_le_pCoreOf hS hCH (inv_mem ha) (inv_mem hb) _ (hmem hz) _ (hmem hw)
  · rintro _ ⟨a, ha, z, hz, rfl⟩
    have hz2 : z ^ 2 = 1 := hel.2 z hz
    rw [conj_pow, hz2]
    group

end Cex15

structure IsPair156 (M V₀ H A X : Subgroup G) : Prop where
  conj : ∃ g : G, A = conjSubgroup V₀ g
  le_H : X ≤ H
  A_le : A ≤ X
  A_le_M : A ≤ M
  not_le_ker : ¬ A ≤ kerMOf M X
  maxOver_eq : maxOver X (A ⊔ kerMOf M X) = {M ⊓ X}

end CFSG.LocalAnalysis.WeakClosure81
