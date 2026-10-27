module

public import CFSG.GroupTheory.QuasisimpleCommutingProductBound
public import CFSG.Quasithin.Background.F9Section
public import CFSG.Quasithin.EmptyFaithful.S145Two
public import CFSG.Quasithin.EmptyFaithful.S146A0

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G}

section Context

theorem Setting146.conjClosure_le_pCoreOf (S : Setting146 G T M) {H : Subgroup G} (hH : IsHTM T M H) :
    conjClosure (VZ T M) H ≤ pCoreOf 2 H :=
  (S.lemma_14_5_14 (S.isHz_iff.mpr hH)).2.toHypF91.conjClosure_Vp_le_pCoreOf

theorem Setting146.pCoreOf_le_T (S : Setting146 G T M) {H : Subgroup G} (hH : IsHTM T M H) :
    pCoreOf 2 H ≤ T :=
  pCoreOf_two_le_of_isSylowTwoOf (isSylowTwoOf_of_quasithinIsSylowTwo S.hyp.sylow hH.1.1)

omit [Finite G] in
theorem Z_le_conjClosure_VZ (T M H : Subgroup G) :
    quasithinOmegaOneCenter T ≤ conjClosure (VZ T M) H :=
  (le_conjClosure _ _ : quasithinOmegaOneCenter T ≤ VZ T M).trans (le_conjClosure _ _)

theorem Setting146.conjClosure_le_normalizer_Z (S : Setting146 G T M) {H : Subgroup G}
    (hH : IsHTM T M H) :
    conjClosure (VZ T M) H ≤ Subgroup.normalizer (quasithinOmegaOneCenter T : Set G) :=
  fun _ hx => Subgroup.centralizer_le_normalizer _
    (le_centralizer_quasithinOmegaOneCenter T ((S.pCoreOf_le_T hH) (S.conjClosure_le_pCoreOf hH hx)))

omit [Finite G] in
theorem uHi_le_conjClosure {H Hi : Subgroup G} (hHi : Hi ≤ H) :
    uHi T M H Hi ≤ conjClosure (VZ T M) H :=
  sup_le (S145.commutator_le_of_le_normalizer (hHi.trans (le_normalizer_conjClosure _ _)))
    (Z_le_conjClosure_VZ T M H)

omit [Finite G] in
theorem Z_le_uHi (T M H Hi : Subgroup G) : quasithinOmegaOneCenter T ≤ uHi T M H Hi := le_sup_right

end Context

section Ranks

theorem IsDec12.relIndex_uHi_sup (S : Setting146 G T M) {H PQ : Subgroup G} {p : ℕ}
    (hred : IsRedCE T M H PQ p) (hOF : IsOFourPlusOn T M H) {H₀ H₁ H₂ : Subgroup G} {t : G}
    (hdec : IsDec12 T M H p H₀ H₁ H₂ t) :
    (quasithinOmegaOneCenter T).relIndex (uHi T M H H₁ ⊔ uHi T M H H₂) = 16 := by
  have hH : IsHTM T M H := hred.isHTM
  have hHU : H ≤ Subgroup.normalizer (conjClosure (VZ T M) H : Set G) :=
    le_normalizer_conjClosure _ _
  have hUN := S.conjClosure_le_normalizer_Z hH
  have hKU : uK T M H ≤ conjClosure (VZ T M) H := S145.commutator_le_of_le_normalizer hHU
  have hZN : quasithinOmegaOneCenter T ≤ Subgroup.normalizer (quasithinOmegaOneCenter T : Set G) :=
    Subgroup.le_normalizer
  have hKN : uK T M H ≤ Subgroup.normalizer (quasithinOmegaOneCenter T : Set G) := hKU.trans hUN
  rw [hdec.dir_sup]
  have h1 := relIndex_secImg (A := Subgroup.normalizer (quasithinOmegaOneCenter T : Set G))
    (B := quasithinOmegaOneCenter T) (le_refl _)
    (le_sup_right : quasithinOmegaOneCenter T ≤ uK T M H ⊔ quasithinOmegaOneCenter T)
    (sup_le hKN hZN)
  have h2 : secImg (Subgroup.normalizer (quasithinOmegaOneCenter T : Set G))
      (quasithinOmegaOneCenter T) (quasithinOmegaOneCenter T) = ⊥ := tildeOf_eq_bot_of_le le_rfl
  rw [h2, Subgroup.relIndex_bot_left] at h1
  have h3 : tildeOf (quasithinOmegaOneCenter T) (uK T M H ⊔ quasithinOmegaOneCenter T) =
      tildeOf (quasithinOmegaOneCenter T) (uK T M H) := tildeOf_sup_self hKN
  rw [← h1]
  change Nat.card ↥(tildeOf (quasithinOmegaOneCenter T) (uK T M H ⊔ quasithinOmegaOneCenter T)) = 16
  rw [h3]
  exact hOF.1.1

theorem IsDec12.relIndex_uHi_eq_four (S : Setting146 G T M) {H PQ : Subgroup G} {p : ℕ}
    (hred : IsRedCE T M H PQ p) (hp3 : p = 3) (hOF : IsOFourPlusOn T M H)
    {H₀ H₁ H₂ : Subgroup G} {t : G} (hdec : IsDec12 T M H p H₀ H₁ H₂ t) :
    (quasithinOmegaOneCenter T).relIndex (uHi T M H H₁) = 4 ∧
      (quasithinOmegaOneCenter T).relIndex (uHi T M H H₂) = 4 := by
  have hH : IsHTM T M H := hred.isHTM
  have hHU : H ≤ Subgroup.normalizer (conjClosure (VZ T M) H : Set G) :=
    le_normalizer_conjClosure _ _
  have hH₁H : H₁ ≤ H := hdec.le₁.trans hdec.le
  have hH₂H : H₂ ≤ H := hdec.le₂.trans hdec.le
  have hUQ := S.conjClosure_le_pCoreOf hH
  have hU₁ : uHi T M H H₁ ≤ conjClosure (VZ T M) H := uHi_le_conjClosure hH₁H
  have hU₂ : uHi T M H H₂ ≤ conjClosure (VZ T M) H := uHi_le_conjClosure hH₂H
  have hUab : IsElemAbelian 2 (conjClosure (VZ T M) H) := S.lemma_14_5_15_two hH
  have hc : ∀ x ∈ uHi T M H H₁, ∀ y ∈ uHi T M H H₂, x * y = y * x := fun x hx y hy =>
    isElemAbelian_comm hUab (hU₁ hx) (hU₂ hy)
  obtain ⟨hprod, -⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute (uHi T M H H₁)
    (uHi T M H H₂) hc
  rw [hdec.dir_inf] at hprod
  have hZpos : 0 < Nat.card (quasithinOmegaOneCenter T) := by rw [S.card_Z]; norm_num
  have eS := Subgroup.relIndex_mul_card (quasithinOmegaOneCenter T)
    (uHi T M H H₁ ⊔ uHi T M H H₂)
  rw [inf_eq_left.mpr (le_sup_right.trans le_sup_left)] at eS
  have e1 := Subgroup.relIndex_mul_card (quasithinOmegaOneCenter T) (uHi T M H H₁)
  rw [inf_eq_left.mpr (Z_le_uHi T M H H₁)] at e1
  have e2 := Subgroup.relIndex_mul_card (quasithinOmegaOneCenter T) (uHi T M H H₂)
  rw [inf_eq_left.mpr (Z_le_uHi T M H H₂)] at e2
  have hrS := hdec.relIndex_uHi_sup S hred hOF
  have hmul : (quasithinOmegaOneCenter T).relIndex (uHi T M H H₁ ⊔ uHi T M H H₂) =
      (quasithinOmegaOneCenter T).relIndex (uHi T M H H₁) *
        (quasithinOmegaOneCenter T).relIndex (uHi T M H H₂) := by
    have hZ2 : 0 < Nat.card (quasithinOmegaOneCenter T) * Nat.card (quasithinOmegaOneCenter T) :=
      Nat.mul_pos hZpos hZpos
    refine Nat.eq_of_mul_eq_mul_right hZ2 ?_
    rw [← eS, ← e1, ← e2] at hprod
    calc (quasithinOmegaOneCenter T).relIndex (uHi T M H H₁ ⊔ uHi T M H H₂) *
          (Nat.card (quasithinOmegaOneCenter T) * Nat.card (quasithinOmegaOneCenter T))
        = ((quasithinOmegaOneCenter T).relIndex (uHi T M H H₁ ⊔ uHi T M H H₂) *
            Nat.card (quasithinOmegaOneCenter T)) * Nat.card (quasithinOmegaOneCenter T) := by ring
      _ = ((quasithinOmegaOneCenter T).relIndex (uHi T M H H₁) *
            Nat.card (quasithinOmegaOneCenter T)) *
          ((quasithinOmegaOneCenter T).relIndex (uHi T M H H₂) *
            Nat.card (quasithinOmegaOneCenter T)) := hprod
      _ = ((quasithinOmegaOneCenter T).relIndex (uHi T M H H₁) *
            (quasithinOmegaOneCenter T).relIndex (uHi T M H H₂)) *
          (Nat.card (quasithinOmegaOneCenter T) * Nat.card (quasithinOmegaOneCenter T)) := by ring
  have hp1 : IsPGroup 2 (uHi T M H H₁) := (pCoreOf_isPGroup 2 H).to_le (hU₁.trans hUQ)
  have hp2 : IsPGroup 2 (uHi T M H H₂) := (pCoreOf_isPGroup 2 H).to_le (hU₂.trans hUQ)
  rw [HypF98.relIndex_eq_two_pow_mIdx hp1, HypF98.relIndex_eq_two_pow_mIdx hp2] at hmul
  rw [hrS] at hmul
  rw [HypF98.relIndex_eq_two_pow_mIdx hp1, HypF98.relIndex_eq_two_pow_mIdx hp2]
  have hr1 := hdec.rank₁.2 hp3
  have hr2 := hdec.rank₂.2 hp3
  rw [← pow_add] at hmul
  have hab : mIdx (uHi T M H H₁) (quasithinOmegaOneCenter T) +
      mIdx (uHi T M H H₂) (quasithinOmegaOneCenter T) = 4 := by
    have h24 : (2 : ℕ) ^ (mIdx (uHi T M H H₁) (quasithinOmegaOneCenter T) +
        mIdx (uHi T M H H₂) (quasithinOmegaOneCenter T)) = 2 ^ 4 := by
      rw [← hmul]
      norm_num
    exact Nat.pow_right_injective le_rfl h24
  have ha : mIdx (uHi T M H H₁) (quasithinOmegaOneCenter T) = 2 := by omega
  have hb : mIdx (uHi T M H H₂) (quasithinOmegaOneCenter T) = 2 := by omega
  rw [ha, hb]
  norm_num

end Ranks

end CFSG.Quasithin
