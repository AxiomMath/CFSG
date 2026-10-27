module

import Mathlib.Tactic.Group
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

private lemma n924x_map_conj_mem {X Y U W H : Subgroup G}
    (hYX : Y ≤ normalizer (X : Set G)) (hUY : Y ≤ normalizer (U : Set G))
    (hWY : Y ≤ normalizer (W : Set G)) (hWH : W ≤ H) (hHU : H ≤ U)
    (hUH : U ≤ normalizer (H : Set G)) (hXH : X ≤ normalizer (H : Set G))
    {y : G} (hy : y ∈ Y) :
    W ≤ H.map (MulAut.conj y).toMonoidHom ∧ H.map (MulAut.conj y).toMonoidHom ≤ U ∧
      U ≤ normalizer (H.map (MulAut.conj y).toMonoidHom : Set G) ∧
      X ≤ normalizer (H.map (MulAut.conj y).toMonoidHom : Set G) := by
  have hW : W.map (MulAut.conj y).toMonoidHom = W :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (hWY hy)
  have hU : U.map (MulAut.conj y).toMonoidHom = U :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (hUY hy)
  have hX : X.map (MulAut.conj y).toMonoidHom = X :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (hYX hy)
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← hW]; exact Subgroup.map_mono hWH
  · rw [← hU]; exact Subgroup.map_mono hHU
  · rw [← hU]
    exact (Subgroup.map_mono hUH).trans
      (Subgroup.le_normalizer_map (MulAut.conj y).toMonoidHom)
  · rw [← hX]
    exact (Subgroup.map_mono hXH).trans
      (Subgroup.le_normalizer_map (MulAut.conj y).toMonoidHom)

private lemma n924x_map_conj_mul {U₁ Y : Subgroup G} {y' : G} (hy' : y' ∈ Y) (y : ↥Y) :
    (U₁.map (MulAut.conj (y : G)).toMonoidHom).map (MulAut.conj y').toMonoidHom =
      U₁.map (MulAut.conj (y' * (y : G))).toMonoidHom := by
  rw [Subgroup.map_map]
  have hcomp : (MulAut.conj y').toMonoidHom.comp (MulAut.conj (y : G)).toMonoidHom =
      (MulAut.conj (y' * (y : G))).toMonoidHom := by
    ext t
    simp [MulAut.conj_apply, mul_assoc]
  rw [hcomp]

private lemma n924x_conj_eq_or_comm {X U W A B U₁ : Subgroup G}
    (hWA : W ≤ A) (hWB : W ≤ B) (hAU : A ≤ U) (hBU : B ≤ U)
    (hUA : U ≤ normalizer (A : Set G)) (hUB : U ≤ normalizer (B : Set G))
    (hXA : X ≤ normalizer (A : Set G)) (hXB : X ≤ normalizer (B : Set G))
    (hcardA : Nat.card A = Nat.card U₁) (hcardB : Nat.card B = Nat.card U₁)
    (hmin : ∀ T : Subgroup G, W ≤ T → T ≤ U → U ≤ normalizer (T : Set G) →
      X ≤ normalizer (T : Set G) → T ≠ W → Nat.card U₁ ≤ Nat.card T) :
    A = B ∨ ∀ a ∈ A, ∀ b ∈ B, ⁅a, b⁆ ∈ W := by
  by_cases h : A ⊓ B = W
  · right
    intro a ha b hb
    have hmemA : ⁅a, b⁆ ∈ A := by
      have hbN : b ∈ normalizer (A : Set G) := hUA (hBU hb)
      have hba : b * a⁻¹ * b⁻¹ ∈ A :=
        (Subgroup.mem_normalizer_iff.mp hbN a⁻¹).mp (A.inv_mem ha)
      have heq : ⁅a, b⁆ = a * (b * a⁻¹ * b⁻¹) := by
        simp only [commutatorElement_def, mul_assoc]
      rw [heq]
      exact A.mul_mem ha hba
    have hmemB : ⁅a, b⁆ ∈ B := by
      have haN : a ∈ normalizer (B : Set G) := hUB (hAU ha)
      have hab : a * b * a⁻¹ ∈ B := (Subgroup.mem_normalizer_iff.mp haN b).mp hb
      have heq : ⁅a, b⁆ = (a * b * a⁻¹) * b⁻¹ := by
        simp only [commutatorElement_def]
      rw [heq]
      exact B.mul_mem hab (B.inv_mem hb)
    have hmem : ⁅a, b⁆ ∈ A ⊓ B := ⟨hmemA, hmemB⟩
    rwa [h] at hmem
  · left
    have hT1 : W ≤ A ⊓ B := le_inf hWA hWB
    have hT2 : A ⊓ B ≤ U := inf_le_left.trans hAU
    have hT3 : U ≤ normalizer (A ⊓ B : Set G) :=
      (le_inf hUA hUB).trans Subgroup.inf_normalizer_le_normalizer_inf
    have hT4 : X ≤ normalizer (A ⊓ B : Set G) :=
      (le_inf hXA hXB).trans Subgroup.inf_normalizer_le_normalizer_inf
    have hcard : Nat.card U₁ ≤ Nat.card ↥(A ⊓ B) := hmin (A ⊓ B) hT1 hT2 hT3 hT4 h
    have hEq : A ⊓ B = A := by
      refine Subgroup.eq_of_le_of_card_ge inf_le_left ?_
      rw [hcardA]; exact hcard
    have hAB : A ≤ B := by
      intro a ha
      have ha' : a ∈ A ⊓ B := by rw [hEq]; exact ha
      exact (Subgroup.mem_inf.mp ha').2
    exact Subgroup.eq_of_le_of_card_ge hAB (by rw [hcardB, hcardA])

theorem exists_xInvariant_piece_of_nonabelian_chief {X Y U W : Subgroup G} (hXY : X ≤ Y)
    (hYX : Y ≤ normalizer (X : Set G)) (hUY : Y ≤ normalizer (U : Set G)) (hWle : W ≤ U)
    (hWU : U ≤ normalizer (W : Set G)) (hWY : Y ≤ normalizer (W : Set G))
    (hWmax : ∀ X' : Subgroup G, W ≤ X' → X' ≤ U → U ≤ normalizer (X' : Set G) →
      Y ≤ normalizer (X' : Set G) → X' ≠ U → X' = W)
    (hcomm : ¬ ⁅U, U⁆ ≤ W) :
    ∃ U₁ : Subgroup G, W ≤ U₁ ∧ U₁ ≤ U ∧ U ≤ normalizer (U₁ : Set G) ∧
      X ≤ normalizer (U₁ : Set G) ∧ ¬ ⁅U₁, U₁⁆ ≤ W ∧
      (∀ X' : Subgroup G, W ≤ X' → X' ≤ U₁ → U₁ ≤ normalizer (X' : Set G) →
        X ≤ normalizer (X' : Set G) → X' ≠ U₁ → X' = W) ∧
      U ≤ ⨆ y : ↥Y, U₁.map (MulAut.conj (y : G)).toMonoidHom := by
  classical
  have hPU : W ≤ U ∧ U ≤ U ∧ U ≤ normalizer (U : Set G) ∧ X ≤ normalizer (U : Set G) ∧
      U ≠ W :=
    ⟨hWle, le_rfl, Subgroup.le_normalizer, hXY.trans hUY,
      fun h => hcomm (h ▸ Subgroup.commutator_le_self U)⟩
  have hex : ∃ n : ℕ, ∃ T : Subgroup G,
      W ≤ T ∧ T ≤ U ∧ U ≤ normalizer (T : Set G) ∧ X ≤ normalizer (T : Set G) ∧ T ≠ W ∧
        n = Nat.card T :=
    ⟨_, U, hPU.1, hPU.2.1, hPU.2.2.1, hPU.2.2.2.1, hPU.2.2.2.2, rfl⟩
  obtain ⟨U₁, hWU₁, hU₁U, hU₁N, hXU₁N, hU₁neW, hU₁card⟩ := Nat.find_spec hex
  have hmin : ∀ T : Subgroup G, W ≤ T → T ≤ U → U ≤ normalizer (T : Set G) →
      X ≤ normalizer (T : Set G) → T ≠ W → Nat.card U₁ ≤ Nat.card T := by
    intro T h1 h2 h3 h4 hne
    rw [← hU₁card]
    exact Nat.find_min' hex ⟨T, h1, h2, h3, h4, hne, rfl⟩
  let Uc : ↥Y → Subgroup G := fun y => U₁.map (MulAut.conj (y : G)).toMonoidHom
  have hUcP : ∀ y : ↥Y, W ≤ Uc y ∧ Uc y ≤ U ∧ U ≤ normalizer (Uc y : Set G) ∧
      X ≤ normalizer (Uc y : Set G) ∧ Nat.card (Uc y) = Nat.card U₁ := by
    intro y
    obtain ⟨h1, h2, h3, h4⟩ := n924x_map_conj_mem hYX hUY hWY hWU₁ hU₁U hU₁N hXU₁N y.2
    exact ⟨h1, h2, h3, h4,
      Subgroup.card_map_of_injective (MulAut.conj (y : G)).injective⟩
  have hpair : ∀ y y' : ↥Y, ∀ a ∈ Uc y, ∀ b ∈ Uc y', Uc y = Uc y' ∨ ⁅a, b⁆ ∈ W := by
    intro y y' a ha b hb
    rcases n924x_conj_eq_or_comm (A := Uc y) (B := Uc y') (U₁ := U₁)
      (hUcP y).1 (hUcP y').1 (hUcP y).2.1 (hUcP y').2.1
      (hUcP y).2.2.1 (hUcP y').2.2.1 (hUcP y).2.2.2.1 (hUcP y').2.2.2.1
      (hUcP y).2.2.2.2 (hUcP y').2.2.2.2 hmin with hEq | hc
    · exact Or.inl hEq
    · exact Or.inr (hc a ha b hb)
  let V : Subgroup G := ⨆ y : ↥Y, Uc y
  have hUc1 : Uc 1 = U₁ := by
    have hconj1 : (MulAut.conj (1 : G)).toMonoidHom = MonoidHom.id G := by
      ext t
      simp [MulAut.conj_apply]
    show U₁.map (MulAut.conj (1 : G)).toMonoidHom = U₁
    rw [hconj1, Subgroup.map_id]
  have hU₁V : U₁ ≤ V := by
    rw [← hUc1]
    exact le_iSup (fun y : ↥Y => Uc y) 1
  have hWV : W ≤ V := hWU₁.trans hU₁V
  have hVU : V ≤ U := iSup_le (fun y => (hUcP y).2.1)
  have hUV : U ≤ normalizer (V : Set G) := by
    rw [Subgroup.le_normalizer_iff]
    intro u hu v hv
    refine Subgroup.iSup_induction (fun y : ↥Y => Uc y)
      (C := fun x => u * x * u⁻¹ ∈ V) hv ?_ ?_ ?_
    · intro y a ha
      have hmem : u * a * u⁻¹ ∈ Uc y :=
        (Subgroup.mem_normalizer_iff.mp ((hUcP y).2.2.1 hu) a).mp ha
      exact le_iSup (fun z : ↥Y => Uc z) y hmem
    · simpa using V.one_mem
    · intro x y hx hy
      rw [show u * (x * y) * u⁻¹ = (u * x * u⁻¹) * (u * y * u⁻¹) by group]
      exact V.mul_mem hx hy
  have hYV : Y ≤ normalizer (V : Set G) := by
    rw [Subgroup.le_normalizer_iff]
    intro y' hy' v hv
    refine Subgroup.iSup_induction (fun y : ↥Y => Uc y)
      (C := fun x => y' * x * y'⁻¹ ∈ V) hv ?_ ?_ ?_
    · intro y a ha
      have hmem : (MulAut.conj y') a ∈
          Uc (⟨y' * (y : G), Y.mul_mem hy' y.2⟩ : ↥Y) := by
        show (MulAut.conj y') a ∈ U₁.map (MulAut.conj (y' * (y : G))).toMonoidHom
        rw [← n924x_map_conj_mul (U₁ := U₁) hy' y]
        exact Subgroup.mem_map_of_mem (MulAut.conj y').toMonoidHom ha
      rw [MulAut.conj_apply] at hmem
      exact le_iSup (fun z : ↥Y => Uc z) ⟨y' * (y : G), Y.mul_mem hy' y.2⟩ hmem
    · simpa using V.one_mem
    · intro x y hx hy
      rw [show y' * (x * y) * y'⁻¹ = (y' * x * y'⁻¹) * (y' * y * y'⁻¹) by group]
      exact V.mul_mem hx hy
  have hVneW : V ≠ W := by
    intro hVW
    exact hU₁neW (le_antisymm (hVW ▸ hU₁V) hWU₁)
  have hVU_eq : V = U := by
    by_contra hVneU
    exact hVneW (hWmax V hWV hVU hUV hYV hVneU)
  have hUD : ¬ ⁅U₁, U₁⁆ ≤ W := by
    intro hUcomm
    have hconj : ∀ y : ↥Y, ⁅Uc y, Uc y⁆ ≤ W := by
      intro y
      have h : (⁅U₁, U₁⁆).map (MulAut.conj (y : G)).toMonoidHom = ⁅Uc y, Uc y⁆ := by
        rw [Subgroup.map_commutator]
      rw [← h]
      exact (Subgroup.map_mono hUcomm).trans
        (le_of_eq (Subgroup.mem_normalizer_iff_map_conj_eq.mp (hWY y.2)))
    have hcommVV : ∀ a ∈ V, ∀ b ∈ V, ⁅a, b⁆ ∈ W := by
      have houter : ∀ a ∈ V, a ∈ V ∧ ∀ b ∈ V, ⁅a, b⁆ ∈ W := by
        intro a ha
        refine Subgroup.iSup_induction (fun y : ↥Y => Uc y)
          (C := fun a => a ∈ V ∧ ∀ b ∈ V, ⁅a, b⁆ ∈ W) ha ?_ ?_ ?_
        · intro z a ha'
          refine ⟨le_iSup (fun y : ↥Y => Uc y) z ha', ?_⟩
          intro b hb
          refine (Subgroup.iSup_induction (fun y : ↥Y => Uc y)
            (C := fun b => b ∈ V ∧ ⁅a, b⁆ ∈ W) hb ?_ ?_ ?_).2
          · intro y b hb'
            refine ⟨le_iSup (fun y : ↥Y => Uc y) y hb', ?_⟩
            rcases hpair z y a ha' b hb' with hEq | hc
            · exact Subgroup.commutator_le.mp (hconj z) a ha' b (hEq.symm ▸ hb')
            · exact hc
          · exact ⟨V.one_mem, by simp⟩
          · intro x y hx hy
            refine ⟨V.mul_mem hx.1 hy.1, ?_⟩
            have hxU : x ∈ U := hVU hx.1
            have hxW : x ∈ normalizer (W : Set G) := hWU hxU
            have hconjxy : x * ⁅a, y⁆ * x⁻¹ ∈ W :=
              (Subgroup.mem_normalizer_iff.mp hxW ⁅a, y⁆).mp hy.2
            rw [commutatorElement_mul_right_eq_mul_conj]
            simpa only [mul_assoc] using W.mul_mem hx.2 hconjxy
        · exact ⟨V.one_mem, by intro b _; simp⟩
        · intro x y hx hy
          refine ⟨V.mul_mem hx.1 hy.1, ?_⟩
          intro b hb
          have hxU : x ∈ U := hVU hx.1
          have hxW : x ∈ normalizer (W : Set G) := hWU hxU
          have hconjyx : x * ⁅y, b⁆ * x⁻¹ ∈ W :=
            (Subgroup.mem_normalizer_iff.mp hxW ⁅y, b⁆).mp (hy.2 b hb)
          rw [commutatorElement_mul_left_eq_conj_mul]
          simpa only [mul_assoc] using W.mul_mem hconjyx (hx.2 b hb)
      intro a ha b hb
      exact (houter a ha).2 b hb
    apply hcomm
    rw [← hVU_eq]
    exact Subgroup.commutator_le.mpr hcommVV
  have hXmax : ∀ X' : Subgroup G, W ≤ X' → X' ≤ U₁ → U₁ ≤ normalizer (X' : Set G) →
      X ≤ normalizer (X' : Set G) → X' ≠ U₁ → X' = W := by
    intro X' hWX' hX'U₁ hU₁NX' hXNX' hX'ne
    by_contra hX'neW
    have hX'U : X' ≤ U := hX'U₁.trans hU₁U
    have hUX'N : U ≤ normalizer (X' : Set G) := by
      have hgen : ∀ y : ↥Y, Uc y ≤ normalizer (X' : Set G) := by
        intro y
        by_cases hEq : Uc y = U₁
        · rw [hEq]; exact hU₁NX'
        · have hcommPair : ∀ a ∈ Uc y, ∀ b ∈ U₁, ⁅a, b⁆ ∈ W := by
            rcases n924x_conj_eq_or_comm (A := Uc y) (B := U₁) (U₁ := U₁)
              (hUcP y).1 hWU₁ (hUcP y).2.1 hU₁U (hUcP y).2.2.1 hU₁N
              (hUcP y).2.2.2.1 hXU₁N (hUcP y).2.2.2.2 rfl hmin with hEq' | hc
            · exact absurd hEq' hEq
            · exact hc
          rw [Subgroup.le_normalizer_iff]
          intro a ha t ht
          have hc : ⁅a, t⁆ ∈ W := hcommPair a ha t (hX'U₁ ht)
          have heq : a * t * a⁻¹ = ⁅a, t⁆ * t := by
            simp only [commutatorElement_def]; group
          rw [heq]
          exact X'.mul_mem (hWX' hc) ht
      have hVle : V ≤ normalizer (X' : Set G) := iSup_le hgen
      rwa [hVU_eq] at hVle
    have hcard : Nat.card U₁ ≤ Nat.card X' := hmin X' hWX' hX'U hUX'N hXNX' hX'neW
    exact hX'ne (Subgroup.eq_of_le_of_card_ge hX'U₁ hcard)
  refine ⟨U₁, hWU₁, hU₁U, hU₁N, hXU₁N, hUD, hXmax, ?_⟩
  show U ≤ V
  rw [hVU_eq]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
