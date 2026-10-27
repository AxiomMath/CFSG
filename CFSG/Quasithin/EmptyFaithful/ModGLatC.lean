module

public import CFSG.Quasithin.EmptyFaithful.ModGLatB

public section

namespace CFSG.Quasithin.ModG

open scoped Pointwise
open MulAction CFSG.Blueprint CFSG.QuasithinUnique.Vol2Native.L239 CFSG.QuasithinUnique.Setup.X1
  CFSG.Sporadic.Mathieu

structure M22Lat (S D P₁ P₂ E : Subgroup Mg) : Prop where
  sylow : IsPGroup 2 ↥S ∧ ¬ 2 ∣ S.index
  S_le₁ : S ≤ P₁
  S_le₂ : S ≤ P₂
  le₁ : P₁ ≤ D
  le₂ : P₂ ≤ D
  cos₁ : ∃ reps : Fin 3 → Mg, (∀ i, reps i ∈ P₁) ∧ ∀ p ∈ P₁, ∃ i, (reps i)⁻¹ * p ∈ S
  cos₂ : ∃ reps : Fin 3 → Mg, (∀ i, reps i ∈ P₂) ∧ ∀ p ∈ P₂, ∃ i, (reps i)⁻¹ * p ∈ S
  gen : D ≤ P₁ ⊔ P₂
  lat : ∀ Z : Subgroup Mg, S ≤ Z → Group.IsSolvable ↥Z → Z ≤ D
  odd : D ≤ Subgroup.closure {x : Mg | x ∈ D ∧ Odd (orderOf x)}
  selfnorm : ∀ g : Mg, g ∈ Subgroup.normalizer (D : Set Mg) → g ∈ D
  inv : ∀ α : MulAut Mg, S.map α.toMonoidHom = S →
    D.map α.toMonoidHom = D ∧ P₁.map α.toMonoidHom = P₁ ∧ P₂.map α.toMonoidHom = P₂
  alt : Alt2Struct D E 6

theorem Dg_le_gen :
    Dg ≤ Subgroup.closure ({x | x ∈ Ls} ∪ {u1, u2}) := by
  intro x hx
  obtain ⟨d, hd, hds⟩ := Dg_cosets x hx
  obtain ⟨j, -, rfl⟩ := exists_di d hd
  have : x = di j * ((di j)⁻¹ * x) := by group
  rw [this]
  refine Subgroup.mul_mem _ (di_mem_gen j) ?_
  have hS : Sg ≤ Subgroup.closure ({x | x ∈ Ls} ∪ {u1, u2}) := by
    rw [Sg]
    exact Subgroup.closure_mono Set.subset_union_left
  exact hS hds

theorem gen_le_P : Subgroup.closure ({x | x ∈ Ls} ∪ {u1, u2}) ≤ P1 ⊔ P2 := by
  rw [Subgroup.closure_le]
  rintro x (hx | rfl | rfl)
  · exact Subgroup.mem_sup_left (Ls_le_P1 (Subgroup.subset_closure hx))
  · exact Subgroup.mem_sup_left u1_mem_P1
  · exact Subgroup.mem_sup_right u2_mem_P2

theorem odd_orderOf {x : Mg} (h : x ^ 15 = 1) : Odd (orderOf x) :=
  Odd.of_dvd_nat (by decide : Odd 15) (orderOf_dvd_of_pow_eq_one h)

theorem Dg_ne_top :
    Dg ≠ ⊤ := by
  obtain ⟨E, -, -, hcard, -⟩ := m22_struct
  intro h
  rw [h, Subgroup.card_top, card_M22] at hcard
  omega

theorem Dg_ne_bot : Dg ≠ ⊥ := by
  obtain ⟨E, -, -, hcard, -⟩ := m22_struct
  intro h
  rw [h, Subgroup.card_bot] at hcard
  omega

theorem m22Lat :
    ∃ E : Subgroup Mg, M22Lat Sg Dg P1 P2 E := by
  obtain ⟨E, halt, hmax, hcard, -⟩ := m22_struct
  refine ⟨E, ?_, Ls_le_P1, Ls_le_P2, P1_le_Dg, P2_le_Dg, ?_, ?_, ?_, ?_, ?_, ?_, ?_, halt⟩
  · refine ⟨IsPGroup.of_card (n := 7) (by rw [card_Sg]; norm_num), ?_⟩
    have h1 := Subgroup.card_mul_index Sg
    rw [card_Sg, card_M22] at h1
    have : Sg.index = 3465 := by omega
    rw [this]
    norm_num
  · refine ⟨fun i => ev (alph4 u1) (rW1.getD i []), fun i => rep_mem_P1 _, fun p hp => ?_⟩
    obtain ⟨w, hw, h⟩ := P1_cosets p hp
    obtain ⟨i, hi, hiw⟩ := List.getElem_of_mem hw
    have hlen : rW1.length = 3 := by decide +kernel
    have hi3 : i < 3 := by omega
    refine ⟨⟨i, hi3⟩, ?_⟩
    show (ev (alph4 u1) (rW1.getD i []))⁻¹ * p ∈ Sg
    rw [List.getD_eq_getElem _ _ hi, hiw]
    exact h
  · refine ⟨fun i => ev (alph4 u2) (rW2.getD i []), fun i => rep_mem_P2 _, fun p hp => ?_⟩
    obtain ⟨w, hw, h⟩ := P2_cosets p hp
    obtain ⟨i, hi, hiw⟩ := List.getElem_of_mem hw
    have hlen : rW2.length = 3 := by decide +kernel
    have hi3 : i < 3 := by omega
    refine ⟨⟨i, hi3⟩, ?_⟩
    show (ev (alph4 u2) (rW2.getD i []))⁻¹ * p ∈ Sg
    rw [List.getD_eq_getElem _ _ hi, hiw]
    exact h
  · exact (Dg_le_gen).trans gen_le_P
  · intro Z hSZ hZ
    exact lat Z hSZ hZ
  · refine (Dg_le_gen).trans (gen_le_odd.trans ?_)
    rw [Subgroup.closure_le]
    rintro x (rfl | rfl)
    · exact Subgroup.subset_closure ⟨o1_mem_Dg, odd_orderOf o1_pow⟩
    · exact Subgroup.subset_closure ⟨o2_mem_Dg, odd_orderOf o2_pow⟩
  · intro g hg
    have hnorm : Subgroup.normalizer (Dg : Set Mg) = Dg ∨ Subgroup.normalizer (Dg : Set Mg) = ⊤ :=
      hmax _ (Subgroup.le_normalizer)
    rcases hnorm with h | h
    · rw [← h]
      exact hg
    · exfalso
      have hN : Dg.Normal := Subgroup.normalizer_eq_top_iff.1 h
      have hsimple : IsSimpleGroup Mg := (fam_m22_simplicity).2.2
      rcases hsimple.eq_bot_or_eq_top_of_normal Dg with h' | h'
      · exact Dg_ne_bot h'
      · exact Dg_ne_top h'
  · intro α hα
    exact aut_inv α hα

end CFSG.Quasithin.ModG
