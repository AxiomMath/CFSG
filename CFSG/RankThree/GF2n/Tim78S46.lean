module

public import CFSG.RankThree.GF2n.Tim78S45
import CFSG.RankThree.GF2n.Tim77TI
import CFSG.RankThree.GF2n.Tim78Involution
import CFSG.RankThree.PartTwo.Sec6.Item612Plus

public section

namespace CFSG.RankThree.GF2n.Tim78

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.RankThree.GF2n
open scoped commutatorElement

variable {G : Type} [Group G]

namespace Hyp4

variable [Finite G] {M B Q P T : Subgroup G} (H : Hyp4 M B Q P T)
include H

section Certified

theorem T_le_conj_M_of_conj_B_le_P {g : G} (hBgP : conjSubgroup g B ≤ P) :
    T ≤ conjSubgroup g M ∧ conjSubgroup g T ≤ M := by
  have hBgP' := H.conj_inv_le_P_of_conj_le_P hBgP
  obtain ⟨⟨x, hxB⟩, hx1⟩ : ∃ x : ↥(conjSubgroup g B), x ≠ 1 := by
    apply Subgroup.ne_bot_iff_exists_ne_one.mp
    intro h
    apply H.B_ne_bot
    apply Subgroup.eq_bot_of_card_eq
    have := card_conjSubgroup g B
    rw [h, Subgroup.card_bot] at this
    exact this.symm
  have hx1' : x ≠ 1 := fun h => hx1 (Subtype.ext h)
  obtain ⟨⟨y, hyB⟩, hy1⟩ : ∃ y : ↥B, y ≠ 1 := Subgroup.ne_bot_iff_exists_ne_one.mp H.B_ne_bot
  have hy1' : y ≠ 1 := fun h => hy1 (Subtype.ext h)
  refine ⟨fun t ht => H.centralizer_le_conj hxB hx1' (Subgroup.mem_centralizer_singleton_iff.mpr
    (Subgroup.mem_centralizer_iff.mp (H.T_le_centralizer_P ht) x (hBgP hxB)).symm), ?_⟩
  intro s hs
  rw [mem_conjSubgroup] at hs
  refine H.normalizer_eq_and_centralizer_le.2 y hyB hy1'
    (Subgroup.mem_centralizer_singleton_iff.mpr ?_)
  have hyg : g⁻¹ * y * g ∈ P := by
    refine hBgP' ?_
    rw [mem_conjSubgroup, inv_inv, show g * (g⁻¹ * y * g) * g⁻¹ = y by group]
    exact hyB
  have := Subgroup.mem_centralizer_iff.mp (H.T_le_centralizer_P hs) _ hyg
  calc s * y = g * ((g⁻¹ * s * g) * (g⁻¹ * y * g)) * g⁻¹ := by group
    _ = g * ((g⁻¹ * y * g) * (g⁻¹ * s * g)) * g⁻¹ := by rw [← this]
    _ = y * s := by group

theorem exists_mem_P_not_normalizer {g : G}
    (hBgP : conjSubgroup g B ≤ P) (hBgB : conjSubgroup g B ≠ B) :
    ∃ a ∈ P, conjSubgroup a (conjSubgroup g B) ≠ conjSubgroup g B := by
  by_contra hcon
  push Not at hcon
  have hbot : conjSubgroup g B = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    have hyP := hBgP hy
    have hcomm : ∀ p ∈ P, p * y = y * p := by
      intro p hp
      have hpN : p ∈ Subgroup.normalizer (conjSubgroup g B : Set G) :=
        conjSubgroup_eq_self_iff.mp (hcon p hp)
      have h1 : ⁅p, y⁆ ∈ conjSubgroup g B := by
        have e0 : ⁅p, y⁆ = (p * y * p⁻¹) * y⁻¹ := rfl
        rw [e0]
        exact (conjSubgroup g B).mul_mem ((Subgroup.mem_normalizer_iff.mp hpN y).mp hy)
          ((conjSubgroup g B).inv_mem hy)
      have h2 : ⁅p, y⁆ ∈ B := H.commutator_mem (H.P_le_Q hp) (H.P_le_Q hyP)
      have h3 : ⁅p, y⁆ ∈ B ⊓ conjSubgroup g B := ⟨h2, h1⟩
      rw [inf_conjSubgroup_eq_bot_of_isTI H.ti hBgB, Subgroup.mem_bot,
        commutatorElement_eq_one_iff_mul_comm] at h3
      exact h3
    have hyB : y ∈ B := by
      have : y ∈ P ⊓ Subgroup.centralizer (P : Set G) :=
        ⟨hyP, Subgroup.mem_centralizer_iff.mpr fun p hp => hcomm p hp⟩
      rwa [H.inf_centralizer_P] at this
    have : y ∈ B ⊓ conjSubgroup g B := ⟨hyB, hy⟩
    rwa [inf_conjSubgroup_eq_bot_of_isTI H.ti hBgB] at this
  apply H.B_ne_bot
  apply Subgroup.eq_bot_of_card_eq
  have := card_conjSubgroup g B
  rw [hbot, Subgroup.card_bot] at this
  exact this.symm

theorem conj_conj_le_sup {g a : G} (hBgP : conjSubgroup g B ≤ P)
    (haP : a ∈ P) : conjSubgroup a (conjSubgroup g B) ≤ B ⊔ conjSubgroup g B := by
  intro x hx
  rw [mem_conjSubgroup] at hx
  have e0 : x = ⁅a, a⁻¹ * x * a⁆ * (a⁻¹ * x * a) := by
    simp only [commutatorElement_def]; group
  rw [e0]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (H.commutator_mem (H.P_le_Q haP)
    (H.P_le_Q (hBgP hx)))) (Subgroup.mem_sup_right hx)

end Certified

section Root

theorem inf_B_conj_T_eq_bot (hCen : BenderCenterInput) (hU : UnitaryTwoGenerationInput) {g : G}
    (hBgB : conjSubgroup g B ≠ B) : B ⊓ conjSubgroup g T = ⊥ := by
  rw [eq_bot_iff]
  intro b hb
  obtain ⟨hbB, hbTg⟩ := Subgroup.mem_inf.mp hb
  have hb' : g⁻¹ * b * g ∈ T := by
    have := hbTg
    rwa [mem_conjSubgroup] at this
  have h1 := H.tim78_4_3 hCen hU b hbB g⁻¹ (by rwa [inv_inv])
  rw [inv_inv] at h1
  have hbBg : b ∈ conjSubgroup g B := by
    rw [mem_conjSubgroup]
    exact h1
  have : b ∈ B ⊓ conjSubgroup g B := ⟨hbB, hbBg⟩
  rwa [inf_conjSubgroup_eq_bot_of_isTI H.ti hBgB] at this

theorem tim78_4_6_alpha (hCen : BenderCenterInput) (hU : UnitaryTwoGenerationInput) {g : G}
    (hg : g ∉ M) (hE : conjSubgroup g B ⊓ Q ≠ ⊥) :
    T ⊓ conjSubgroup g T = ⊥ ∧ ∀ a ∈ T, ∀ b ∈ conjSubgroup g T, a * b = b * a := by
  have hBgP := H.tim78_4_5 hCen hU g hE
  have hBgB : conjSubgroup g B ≠ B := fun h => hg (H.conj_eq_iff.mp h)
  obtain ⟨hTMg, hTgM⟩ := H.T_le_conj_M_of_conj_B_le_P hBgP
  set Tg := conjSubgroup g T with hTgdef
  have hTNTg : T ≤ Subgroup.normalizer (Tg : Set G) := fun t ht =>
    mem_normalizer_conj_of_mem_conj H.M_le_normalizer_T (hTMg ht)
  have hTTg : T ⊓ Tg = ⊥ := by
    by_contra hne
    obtain ⟨b, hbD, hbB, hb1⟩ := H.exists_mem_B_of_normalizes H.T_le_Q H.B_le_T
      H.M_le_normalizer_T (inf_le_left : T ⊓ Tg ≤ T) hne
      (fun t ht => mem_normalizer_inf (Subgroup.le_normalizer ht) (hTNTg ht))
    have : b ∈ B ⊓ Tg := ⟨hbB, hbD.2⟩
    rw [H.inf_B_conj_T_eq_bot hCen hU hBgB, Subgroup.mem_bot] at this
    exact hb1 this
  refine ⟨hTTg, fun a ha b hb => ?_⟩
  have h1 : ⁅a, b⁆ ∈ T := by
    have e0 : ⁅a, b⁆ = a * (b * a⁻¹ * b⁻¹) := by simp only [commutatorElement_def]; group
    rw [e0]
    exact T.mul_mem ha ((Subgroup.mem_normalizer_iff.mp (H.M_le_normalizer_T (hTgM hb)) a⁻¹).mp
      (T.inv_mem ha))
  have h2 : ⁅a, b⁆ ∈ Tg := by
    have e0 : ⁅a, b⁆ = (a * b * a⁻¹) * b⁻¹ := rfl
    rw [e0]
    exact Tg.mul_mem ((Subgroup.mem_normalizer_iff.mp (hTNTg ha) b).mp hb) (Tg.inv_mem hb)
  have h3 : ⁅a, b⁆ ∈ T ⊓ Tg := ⟨h1, h2⟩
  rw [hTTg, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h3
  exact h3

theorem exists_swap (hCen : BenderCenterInput) (hU : UnitaryTwoGenerationInput) {g : G}
    (hg : g ∉ M) (hE : conjSubgroup g B ⊓ Q ≠ ⊥) :
    ∃ a ∈ P, conjSubgroup a (conjSubgroup g B) ≠ conjSubgroup g B ∧
      conjSubgroup g T ⊓ conjSubgroup a (conjSubgroup g T) = ⊥ ∧
      ∀ s ∈ conjSubgroup g T, ∀ s' ∈ conjSubgroup a (conjSubgroup g T), s * s' = s' * s := by
  have hBgP := H.tim78_4_5 hCen hU g hE
  have hBgB : conjSubgroup g B ≠ B := fun h => hg (H.conj_eq_iff.mp h)
  obtain ⟨a, haP, haN⟩ := H.exists_mem_P_not_normalizer hBgP hBgB
  refine ⟨a, haP, haN, ?_⟩
  set h' := g⁻¹ * a * g with hh'
  have hBa : conjSubgroup a (conjSubgroup g B) ≤ B ⊔ conjSubgroup g B := by
    intro x hx
    rw [mem_conjSubgroup] at hx
    have e0 : x = ⁅a, a⁻¹ * x * a⁆ * (a⁻¹ * x * a) := by
      simp only [commutatorElement_def]; group
    rw [e0]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (H.commutator_mem (H.P_le_Q haP)
      (H.P_le_Q (hBgP hx)))) (Subgroup.mem_sup_right hx)
  have hBh' : conjSubgroup h' B = conjSubgroup g⁻¹ (conjSubgroup a (conjSubgroup g B)) := by
    rw [hh', ← conjSubgroup_mul, ← conjSubgroup_mul, mul_assoc]
  have hBh'P : conjSubgroup h' B ≤ P := by
    rw [hBh']
    refine (Subgroup.map_mono hBa).trans ?_
    have hsup : conjSubgroup g⁻¹ (B ⊔ conjSubgroup g B) =
        conjSubgroup g⁻¹ B ⊔ conjSubgroup g⁻¹ (conjSubgroup g B) := Subgroup.map_sup _ _ _
    have hBinv : conjSubgroup g⁻¹ (conjSubgroup g B) = B := by
      rw [← conjSubgroup_mul, inv_mul_cancel, conjSubgroup_one]
    show conjSubgroup g⁻¹ (B ⊔ conjSubgroup g B) ≤ P
    rw [hsup, hBinv]
    exact sup_le (H.conj_inv_le_P_of_conj_le_P hBgP) H.B_le_P
  have hh'M : h' ∉ M := by
    intro hM
    apply haN
    have h1 : conjSubgroup h' B = B := H.conj_eq_iff.mpr hM
    rw [hBh'] at h1
    have h2 : conjSubgroup g (conjSubgroup g⁻¹ (conjSubgroup a (conjSubgroup g B))) =
        conjSubgroup g B := by rw [h1]
    rwa [← conjSubgroup_mul, mul_inv_cancel, conjSubgroup_one] at h2
  have hh'E : conjSubgroup h' B ⊓ Q ≠ ⊥ := by
    rw [inf_of_le_left (hBh'P.trans H.P_le_Q)]
    intro hbot
    apply H.B_ne_bot
    apply Subgroup.eq_bot_of_card_eq
    have := card_conjSubgroup h' B
    rw [hbot, Subgroup.card_bot] at this
    exact this.symm
  obtain ⟨hα1, hα2⟩ := H.tim78_4_6_alpha hCen hU hh'M hh'E
  have hconjT : conjSubgroup g (conjSubgroup h' T) = conjSubgroup a (conjSubgroup g T) := by
    rw [← conjSubgroup_mul, ← conjSubgroup_mul, hh']
    congr 1
    group
  refine ⟨?_, fun s hs s' hs' => ?_⟩
  · rw [← hconjT, ← conjSubgroup_inf, hα1]
    exact Subgroup.map_bot _
  · rw [← hconjT] at hs'
    rw [mem_conjSubgroup] at hs hs'
    have := hα2 _ hs _ hs'
    calc s * s' = g * ((g⁻¹ * s * g) * (g⁻¹ * s' * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * s' * g) * (g⁻¹ * s * g)) * g⁻¹ := by rw [this]
      _ = s' * s := by group

theorem tim78_4_6_beta (hCen : BenderCenterInput) (hU : UnitaryTwoGenerationInput) {g : G}
    (hg : g ∉ M) (hE : conjSubgroup g B ⊓ Q ≠ ⊥) : P ⊓ conjSubgroup g T = conjSubgroup g B := by
  have hBgP := H.tim78_4_5 hCen hU g hE
  have hBgB : conjSubgroup g B ≠ B := fun h => hg (H.conj_eq_iff.mp h)
  have hBgTg : conjSubgroup g B ≤ conjSubgroup g T := Subgroup.map_mono H.B_le_T
  refine le_antisymm ?_ (le_inf hBgP hBgTg)
  obtain ⟨a, haP, haN, hTT, hTc⟩ := H.exists_swap hCen hU hg hE
  set Bg := conjSubgroup g B with hBgdef
  set Tg := conjSubgroup g T with hTgdef
  set Ba := conjSubgroup a Bg with hBadef
  have hBgM : Bg ≤ M := hBgP.trans H.P_le_M
  have hBBg : B ⊓ Bg = ⊥ := inf_conjSubgroup_eq_bot_of_isTI H.ti hBgB
  have hWel : Assembly.IsElemAbelian 2 (B ⊔ Bg) :=
    Tim77.tim77_2_3 H.elemAb H.ti (by rw [H.normalizer_B]; exact hBgM)
  have hcomm : ∀ x ∈ B ⊔ Bg, ∀ y ∈ B ⊔ Bg, x * y = y * x := fun x hx y hy =>
    comm_of_isElemAbelian hWel hx hy
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).mp H.isPGroup_B
  have hWcard : Nat.card (B ⊔ Bg : Subgroup G) = 2 ^ (2 * n) := by
    have := PartTwo.Sec6.card_sup_mul_card_inf (X := B) (N := Bg)
      (le_normalizer_of_comm fun x hx y hy => H.commute_of_conj_le_M hBgM x hx y hy)
    rw [hBBg, Subgroup.card_bot, mul_one, hn, hBgdef, card_conjSubgroup, hn, ← pow_add,
      ← two_mul] at this
    exact this
  have hBaW : Ba ≤ B ⊔ Bg := H.conj_conj_le_sup hBgP haP
  have hBgW : Bg ≤ B ⊔ Bg := le_sup_right
  have hBaBg : Ba ⊓ Bg = ⊥ := by
    rw [inf_comm]
    exact inf_conjSubgroup_eq_bot_of_isTI (isTI_conjSubgroup H.ti g) haN
  have hsupW : Ba ⊔ Bg = B ⊔ Bg :=
    sup_eq_of_inf_eq_bot hWel hWcard hBaW hBgW (by rw [hBadef, card_conjSubgroup, hBgdef,
      card_conjSubgroup, hn]) (by rw [hBgdef, card_conjSubgroup, hn]) hBaBg
  have hBgNBa : Bg ≤ Subgroup.normalizer (Ba : Set G) := le_normalizer_of_comm fun x hx y hy =>
    hcomm x (hBgW hx) y (hBaW hy)
  have hBaTa : Ba ≤ conjSubgroup a Tg := Subgroup.map_mono hBgTg
  intro u hu
  obtain ⟨huP, huTg⟩ := Subgroup.mem_inf.mp hu
  have hb₀ : ⁅a, u⁆ ∈ B ⊔ Bg := Subgroup.mem_sup_left (H.commutator_mem (H.P_le_Q haP)
    (H.P_le_Q huP))
  rw [← hsupW] at hb₀
  obtain ⟨γ, hγ, β, hβ, hγβ⟩ := exists_mul_of_mem_sup hBgNBa hb₀
  have hxTa : a * u * a⁻¹ ∈ conjSubgroup a Tg := by
    rw [mem_conjSubgroup, show a⁻¹ * (a * u * a⁻¹) * a = u by group]
    exact huTg
  have hβu : β * u ∈ Tg := Tg.mul_mem (hBgTg hβ) huTg
  have hx : a * u * a⁻¹ = γ * (β * u) := by
    have e0 : a * u * a⁻¹ = ⁅a, u⁆ * u := by simp only [commutatorElement_def]; group
    rw [e0, hγβ]
    group
  have h1 : β * u ∈ Tg ⊓ conjSubgroup a Tg := by
    refine ⟨hβu, ?_⟩
    have : β * u = γ⁻¹ * (a * u * a⁻¹) := by rw [hx]; group
    rw [this]
    exact (conjSubgroup a Tg).mul_mem ((conjSubgroup a Tg).inv_mem (hBaTa hγ)) hxTa
  rw [hTT, Subgroup.mem_bot] at h1
  have hxBa : a * u * a⁻¹ ∈ Ba := by
    rw [hx, h1, mul_one]
    exact hγ
  rw [hBadef, mem_conjSubgroup, show a⁻¹ * (a * u * a⁻¹) * a = u by group] at hxBa
  exact hxBa

end Root

end Hyp4

end CFSG.RankThree.GF2n.Tim78
