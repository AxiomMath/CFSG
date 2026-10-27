module

public import CFSG.Quasithin.Vol2.Ch10SecA314NC
public import CFSG.Quasithin.Vol2.Ch10SecQ9H68
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.G3A314Model
public import CFSG.Quasithin.Vol2.Ch11SecA11Comp

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecF.A5N

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

theorem absurd_of_isExt_dvd {X : Type} [Group X] (hX : Nat.card X = 60)
    {PV PY : ∀ (V : Type) [Group V], Prop} (h : IsExt X PV PY) {m : ℕ} (hm : ¬ m ∣ 60)
    (hPV : ∀ (V : Type) [Group V], PV V → m ∣ Nat.card V) {C : Prop} : C := by
  obtain ⟨V, -, hV, -⟩ := h
  exact (hm ((hPV _ hV).trans (hX ▸ Subgroup.card_subgroup_dvd_card V))).elim

theorem eight_dvd_of_isE2 {n : ℕ} (hn : 3 ≤ n) (V : Type) [Group V] (h : IsE2 n V) :
    8 ∣ Nat.card V := by
  rw [C10KH.card_isElemAbelianOfRank h]
  exact (pow_dvd_pow 2 hn : 2 ^ 3 ∣ 2 ^ n)

theorem eight_dvd_of_isExtraspecial2 {m : ℕ} (hm : 1 ≤ m) (V : Type) [Group V]
    (h : IsExtraspecial2 m V) : 8 ∣ Nat.card V := by
  rw [h.2]
  exact (pow_dvd_pow 2 (by omega) : 2 ^ 3 ∣ 2 ^ (1 + 2 * m))

theorem eight_dvd_of_isZ4StarExtra2 (V : Type) [Group V] (h : IsZ4StarExtra2 V) :
    8 ∣ Nat.card V := by
  obtain ⟨-, E, -, -, hE, -⟩ := h
  exact (eight_dvd_of_isExtraspecial2 (m := 2) (by norm_num) _ hE).trans
    (Subgroup.card_subgroup_dvd_card E)

theorem eight_dvd_of_isZ4Cubed (V : Type) [Group V] (h : IsZ4Cubed V) : 8 ∣ Nat.card V := by
  obtain ⟨e⟩ := h
  rw [Nat.card_congr e.toEquiv, Nat.card_congr (Multiplicative.toAdd :
    Multiplicative (Fin 3 → ZMod 4) ≃ (Fin 3 → ZMod 4)), Nat.card_pi]
  simp

theorem not_sq_dvd_sixty {p : ℕ} (hp3 : 3 < p) : ¬ p ^ 2 ∣ 60 := by
  intro h
  have hle := Nat.le_of_dvd (by norm_num) h
  have hp7 : p ≤ 7 := by nlinarith
  interval_cases p <;> norm_num at h

theorem sl2_card_ne_sixty {p : ℕ} (hp5 : 5 ≤ p) : p * (p ^ 2 - 1) ≠ 60 := by
  intro h
  have h25 : 24 ≤ p ^ 2 - 1 := by
    have : 25 ≤ p ^ 2 := by nlinarith
    omega
  have : 5 * 24 ≤ p * (p ^ 2 - 1) := Nat.mul_le_mul hp5 h25
  omega

theorem alt5_overgroup_cases' (h312 : Vol2Native.A312ListFactsCat)
    {Y : Type} [Group Y] [Finite Y] (hq : CFSG.IsQuasisimple Y)
    (hS : CFSG.SectionRank.IsSQTKCat Y) (hO : CFSG.pCore 2 Y = ⊥) {S B : Subgroup Y}
    (hSyl : IsSylowTwoOf S ⊤) (hSB : S ≤ Subgroup.normalizer (B : Set Y)) (hne : B ≠ ⊤)
    (hB : IsAlt 5 ↥B) :
    IsAlt 7 Y ∨ IsHat Y ↥(alternatingGroup (Fin 7)) ∨ IsPSL 2 5 2 Y ∨
      (∃ p : ℕ, p.Prime ∧ 11 ≤ p ∧ (p % 8 = 3 ∨ p % 8 = 5) ∧ IsPSL 2 p 1 Y) ∨
      IsSporadic .J1 Y := by
  have hcard : Nat.card ↥B = 60 := A314.card_isAlt_five hB
  have hBne : B ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hcard
    omega
  have hNorm : (B.subgroupOf (B ⊔ S)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
      (sup_le Subgroup.le_normalizer hSB)
  have hsub : IsSubnormal B (B ⊔ S) := A3.subnormal_of_normal le_sup_left hNorm
  have hBfam : B ∈ lFamily S := Vol2.Ch11.SecA.mem_cComp_of_quasisimple hBne
    (C10KH.commutator_eq_of_isAlt_five hB) (C10KH.isQuasisimple_modO2_of_isAlt_five hB) hsub
  have hA := C10KH.isAlt_modRadical_of_isAlt_five hB
  have hM : A314ModelFacts := A5.G3.a314ModelFacts
  have hO2 : Group.IsSolvable ↥(CFSG.pCore 2 ↥B) := A314.solvable_pCore_two _
  have h8 : ¬ 8 ∣ 60 := by norm_num
  rcases h312 Y hq hS hO S hSyl B hBfam hne with h | h | h | h | h | h | h | h | h | h | h | h |
      h | h | h | h | h | h | h
  ·
    obtain ⟨-, hrk, P, hP, hBP⟩ := h
    rw [hBP] at hB
    exact (rank2NoA5 Y ⊤ P hrk hP hB).elim
  · obtain ⟨f, hf, -⟩ := h
    exact (A314.excl_model_mod hM _ hO2 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨f, hf⟩)))))
      hA).elim
  · exact (A314.excl_model_mod hM _ hO2 (Or.inl h.1) hA).elim
  · exact (A314.excl_model_mod hM _ hO2 (Or.inr (Or.inl h.1)) hA).elim
  ·
    rcases h.2 with hL | hL
    · exact Or.inl (IsAlt.of_mulEquiv Subgroup.topEquiv hL)
    · exact Or.inr (Or.inl (IsHat.of_mulEquiv Subgroup.topEquiv hL))
  · rcases h with ⟨h6, -⟩ | ⟨h6, -⟩
    · exact (A314.card_ne_sixty_of_isAlt_six h6 hcard).elim
    · exact (A314.excl_hat_self h6 A314.hS_alt_six hA).elim
  ·
    rcases h with ⟨p, hp, hp3, hBp, hLp⟩ | ⟨-, p, hp, hLp, h5, h8'⟩
    · have hp5 : p = 5 := A314.p_eq_five_of_div hp hp3
        (by rw [← (hM.2.2 p hp hp3 ↥B hBp).2.2]; exact hcard)
      subst hp5
      exact Or.inr (Or.inr (Or.inl
        (CFSG.LieType.CurtisTits.statedClassicalModel_of_mulEquiv Subgroup.topEquiv hLp)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨p, hp, C10KH.eleven_le_of_mod hp h5 h8', h8',
        CFSG.LieType.CurtisTits.statedClassicalModel_of_mulEquiv Subgroup.topEquiv hLp⟩)))
  · rcases h with ⟨s, p, hp, hp3, hSL, -⟩ | ⟨h6, -⟩ | ⟨h6, -⟩
    · have hp4 : p ≠ 4 := by
        rintro rfl
        norm_num at hp
      exact (sl2_card_ne_sixty (by omega) ((A313.IsSL2.card_eq hp hSL).symm.trans hcard)).elim
    · exact (A314.card_ne_sixty_of_isAlt_six h6 hcard).elim
    · exact (A314.excl_hat_self h6 A314.hS_alt_six hA).elim
  · obtain ⟨p, -, hp3, hE, -⟩ := h
    exact absurd_of_isExt_dvd hcard hE (not_sq_dvd_sixty hp3)
      (fun V _ hV => (C10KH.card_isElemAbelianOfRank hV).symm ▸ dvd_rfl)
  · exact (A314.card_ne_sixty_of_isAlt_six h.1 hcard).elim
  · rcases h with ⟨hE | hE, -⟩ | ⟨hE | hE, -⟩ <;>
      exact absurd_of_isExt_dvd hcard hE h8 (eight_dvd_of_isE2 (by norm_num))
  · obtain ⟨hB' | hB' | hE | hE | hE | hE | hE, -⟩ := h
    · exact (A314.excl_model_self hM (Or.inr (Or.inr (Or.inr (Or.inl hB')))) hA).elim
    · exact (A314.excl_model_self hM (Or.inr (Or.inr (Or.inl hB'))) hA).elim
    all_goals exact absurd_of_isExt_dvd hcard hE h8 (eight_dvd_of_isE2 (by norm_num))
  · obtain ⟨hE | hE | hE | hE, -⟩ := h
    · exact absurd_of_isExt_dvd hcard hE h8 (eight_dvd_of_isE2 (by norm_num))
    · exact absurd_of_isExt_dvd hcard hE h8 (eight_dvd_of_isE2 (by norm_num))
    · exact absurd_of_isExt_dvd hcard hE h8 (eight_dvd_of_isExtraspecial2 (by norm_num))
    · exact absurd_of_isExt_dvd hcard hE h8 (eight_dvd_of_isE2 (by norm_num))
  ·
    obtain ⟨e⟩ := h.2
    exact Or.inr (Or.inr (Or.inr (Or.inr ⟨Subgroup.topEquiv.symm.trans e⟩)))
  · exact absurd_of_isExt_dvd hcard h.1 h8 (eight_dvd_of_isExtraspecial2 (by norm_num))
  ·
    obtain ⟨e⟩ := h.1
    exact ((SecB.C10KH.kgJ4NoA5Block_holds Y ⟨Subgroup.topEquiv.symm.trans e⟩ S hSyl B
      hBfam).1 hB).elim
  · rcases h with ⟨hE | hE, -⟩
    · exact absurd_of_isExt_dvd hcard hE h8 eight_dvd_of_isZ4StarExtra2
    · exact absurd_of_isExt_dvd hcard hE h8 eight_dvd_of_isZ4Cubed
  · rcases h with ⟨hE | hE, -⟩
    · exact absurd_of_isExt_dvd hcard hE h8 (eight_dvd_of_isExtraspecial2 (by norm_num))
    · exact absurd_of_isExt_dvd hcard hE h8 (eight_dvd_of_isE2 (by norm_num))
  · obtain ⟨-, h11, -⟩ := h
    rw [C10KH.pCore_eq_bot_of_isAlt_five hB, Subgroup.card_bot] at h11
    norm_num at h11

end CFSG.Quasithin.Vol2.Ch10.SecF.A5N
