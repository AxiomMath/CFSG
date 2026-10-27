module

public import CFSG.RankThree.GF2n.Tim78S48EndFrame
public import CFSG.RankThree.GF2n.Tim78S48EndAsm
public import CFSG.RankThree.GF2n.Tim78S45

public section

namespace CFSG.RankThree.GF2n.Tim78

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.RankThree.GF2n
open scoped commutatorElement Matrix
open EndHelp

variable {G : Type} [Group G]

namespace EndgameData

variable [Finite G] {M B Q P T : Subgroup G} {g : G} {C L : Subgroup G}

theorem of_conj_eq (E : EndgameData M B Q P T g C L) {g' : G}
    (h : conjSubgroup g B = conjSubgroup g' B) : EndgameData M B Q P T g' C L where
  hC := fun c => by rw [← h]; exact E.hC c
  hL := by rw [← h]; exact E.hL
  B_le_C := E.B_le_C
  C_elem := E.C_elem
  C_cent := fun c hc y hy => E.C_cent c hc y (by rw [h]; exact hy)
  C_inf := by rw [← h]; exact E.C_inf
  card_C := E.card_C
  L_elem := E.L_elem
  relIndex_L := E.relIndex_L
  Q_norm := E.Q_norm
  Q_comm := E.Q_comm
  T_comm := E.T_comm
  T_rel := E.T_rel
  part := E.part
  trans := E.trans
  Bg_inf := by rw [← h]; exact E.Bg_inf

variable (E : EndgameData M B Q P T g C L) (H : Hyp4 M B Q P T)
include E H

theorem false_of_normalizing (h45 : Meet45 B Q P)
    (hphase1 : ∀ g' : G, Hyp48 M B T g' → ¬ conjSubgroup g' B ≤ P → Phase1 B T g')
    (hg : g ∈ Subgroup.normalizer (L : Set G)) : False := by
  obtain ⟨r₁, hr₁, r₂, hr₂, hD₁, hD₂, hnp⟩ := E.exists_pair H h45 hg
  have S := E.C_split H h45 hg
  have hg'N : r₁⁻¹ * r₂ ∈ Subgroup.normalizer (L : Set G) :=
    Subgroup.mul_mem _ (Subgroup.inv_mem _ hr₁) hr₂
  obtain ⟨n, hn, hnat, -⟩ :=
    hphase1 (r₁⁻¹ * r₂) (E.hyp48_of_mem H hg'N) (E.not_le_P_pair H hr₁ hr₂ hnp)
  have hn2 : 2 ≤ n := by
    have h4 := H.q4
    rw [hn] at h4
    by_contra hlt
    interval_cases n <;> simp at h4
  have hnat' := inducesNaturalSL2_conj hnat r₁
  have e₁ : conjSubgroup r₁ (T ⊔ conjSubgroup (r₁⁻¹ * r₂) T) =
      conjSubgroup r₁ T ⊔ conjSubgroup r₂ T := by
    rw [conj_sup, ← conjSubgroup_mul, mul_inv_cancel_left]
  have e₂ : conjSubgroup r₁ (B ⊔ conjSubgroup (r₁⁻¹ * r₂) B) =
      conjSubgroup r₁ B ⊔ conjSubgroup r₂ B := by
    rw [conj_sup, ← conjSubgroup_mul, mul_inv_cancel_left]
  rw [e₁, e₂] at hnat'
  obtain ⟨b', hb', hb'1⟩ : ∃ b' ∈ conjSubgroup g B, b' ≠ 1 := by
    obtain ⟨⟨b', hb'⟩, h1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp (E.Bg_ne_bot H)
    exact ⟨b', hb', fun h => h1 (Subtype.ext h)⟩
  obtain ⟨hB₁, hBg₁⟩ := E.perp_of_le_L₀ H h45 hg hr₁ hD₁
  obtain ⟨hB₂, hBg₂⟩ := E.perp_of_le_L₀ H h45 hg hr₂ hD₂
  have hXB : ∀ x ∈ conjSubgroup r₁ T ⊔ conjSubgroup r₂ T, ∀ β ∈ B, x * β = β * x :=
    sup_comm_of (fun x hx y hy => E.conjT_comm_conjC H hx (hB₁ hy))
      (fun x hx y hy => E.conjT_comm_conjC H hx (hB₂ hy))
  have hXBg : ∀ x ∈ conjSubgroup r₁ T ⊔ conjSubgroup r₂ T, ∀ β ∈ conjSubgroup g B,
      x * β = β * x :=
    sup_comm_of (fun x hx y hy => E.conjT_comm_conjC H hx (hBg₁ hy))
      (fun x hx y hy => E.conjT_comm_conjC H hx (hBg₂ hy))
  have hXL : conjSubgroup r₁ T ⊔ conjSubgroup r₂ T ≤ Subgroup.normalizer (L : Set G) :=
    sup_le (E.conjT_le_normalizer_L H hr₁) (E.conjT_le_normalizer_L H hr₂)
  have hXM : conjSubgroup r₁ T ⊔ conjSubgroup r₂ T ≤ M := by
    rw [← H.normalizer_B]
    exact le_normalizer_of_comm hXB
  have hXMg : conjSubgroup r₁ T ⊔ conjSubgroup r₂ T ≤ conjSubgroup g M := by
    rw [← H.normalizer_conj_eq g]
    exact le_normalizer_of_comm hXBg
  have hXL₀ : conjSubgroup r₁ T ⊔ conjSubgroup r₂ T ≤
      Subgroup.normalizer ((C ⊓ conjSubgroup g C : Subgroup G) : Set G) := by
    intro x hx
    have hxQ : x ∈ Subgroup.normalizer (Q : Set G) := H.M_le_normalizer_Q (hXM hx)
    have hxQg : x ∈ Subgroup.normalizer (conjSubgroup g Q : Set G) := by
      rw [normalizer_conjSubgroup]
      exact Subgroup.map_mono H.M_le_normalizer_Q (hXMg hx)
    have hxC : x ∈ Subgroup.normalizer (C : Set G) := by
      rw [← E.L_inf_Q H]
      exact mem_normalizer_inf (hXL hx) hxQ
    have hxCg : x ∈ Subgroup.normalizer (conjSubgroup g C : Set G) := by
      rw [← E.conj_inf_Q H hg]
      exact mem_normalizer_inf (hXL hx) hxQg
    exact mem_normalizer_inf hxC hxCg
  have hN₀ : conjSubgroup r₁ B ⊔ conjSubgroup r₂ B ≤ C ⊓ conjSubgroup g C := sup_le hD₁ hD₂
  have hN₀L : conjSubgroup r₁ B ⊔ conjSubgroup r₂ B ≤ L :=
    sup_le (conj_le_of_mem_normalizer hr₁ E.B_le_L) (conj_le_of_mem_normalizer hr₂ E.B_le_L)
  have hXN₀ : conjSubgroup r₁ T ⊔ conjSubgroup r₂ T ≤
      Subgroup.normalizer ((conjSubgroup r₁ B ⊔ conjSubgroup r₂ B : Subgroup G) : Set G) :=
    sup_le (fun x hx => E.conjT_normalizes hr₁ hx hN₀L le_sup_left)
      (fun x hx => E.conjT_normalizes hr₂ hx hN₀L le_sup_right)
  have hXL₁ : ∀ x ∈ conjSubgroup r₁ T ⊔ conjSubgroup r₂ T,
      ∀ l ∈ C ⊓ conjSubgroup g C ⊓ conjSubgroup r₁ C ⊓ conjSubgroup r₂ C, x * l = l * x :=
    sup_comm_of (fun x hx y hy => E.conjT_comm_conjC H hx hy.1.2)
      (fun x hx y hy => E.conjT_comm_conjC H hx hy.2)
  exact E.false_of_frame H hb' hb'1 hn2 S hXB (fun x hx => hXBg x hx b' hb') hXL₀ hN₀
    (inf_le_left.trans inf_le_left) (E.L₀_le_sup H h45 hg hr₁ hr₂ hD₁ hD₂ hnp) hXN₀ hXL₁ hnat'

end EndgameData

namespace Hyp4

variable [Finite G] {M B Q P T : Subgroup G} (H : Hyp4 M B Q P T)
include H

section Root


theorem endgame (hCen : BenderCenterInput) (hU : UnitaryTwoGenerationInput)
    (hphase1 : ∀ g' : G, Hyp48 M B T g' → ¬ conjSubgroup g' B ≤ P → Phase1 B T g')
    {g : G} {C L : Subgroup G} (E : EndgameData M B Q P T g C L) : False := by
  obtain ⟨r, hr, hBr⟩ := E.trans (conjSubgroup g B) ⟨⟨g, rfl⟩, E.Bg_le_L⟩
  exact (E.of_conj_eq hBr).false_of_normalizing H (H.tim78_4_5 hCen hU) hphase1 hr

end Root

end Hyp4

end CFSG.RankThree.GF2n.Tim78
