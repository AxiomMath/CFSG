module

public import CFSG.Quasithin.Background.HM22RowT0Data
public import CFSG.Quasithin.Background.H12OneHatM22PfModel

public section

namespace CFSG.Quasithin.H.Mathieu.M22Row

open CFSG.Quasithin.H13.MatNCert CFSG.Quasithin.H.Mathieu.H12Cert Matrix

theorem t0Check_parts :
    (∀ p ∈ t0D, evalW 12 tG p.2 = p.1) ∧ (∀ x ∈ t0L, ∀ g ∈ tG, mulN g x ∈ t0L) ∧
      one12 ∈ t0L ∧ (∀ g ∈ tG, validB 12 g = true) ∧
      (∀ x ∈ t0L, mulN x x = one12 → x ≠ one12 → ∃ q ∈ invD, q.1 = x) ∧
      (∀ q ∈ invD, q.2.1 ∈ invMasks ∧ fixOK q.1 q.2.1 = true ∧
        (∀ b ∈ q.2.2, b < 4096 ∧ mvN q.1 b = b) ∧
        ∀ q' ∈ invD, q'.1 = q.1 ∨ ∃ b ∈ q.2.2, mvN q'.1 b ≠ b) ∧
      ∀ m ∈ invMasks, maskCard m ≤ 256 := by
  have h := t0Check_eq
  simp only [t0Check, Bool.and_eq_true, List.all_eq_true, beq_iff_eq, List.contains_iff_mem,
    Bool.or_eq_true, bne_iff_ne, ne_eq, List.any_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := h
  refine ⟨h1, h2, h3, h4, fun x hx hxx hx1 => ?_, fun q hq => ?_, h7⟩
  · rcases h5 x hx with (h | h) | h
    · exact absurd hxx h
    · exact absurd h hx1
    · exact h
  · obtain ⟨⟨⟨hm, hf⟩, hb⟩, hq'⟩ := h6 q hq
    refine ⟨hm, hf, hb, fun q' hq'' => ?_⟩
    rcases hq' q' hq'' with h | h
    · exact Or.inl h
    · exact Or.inr h

theorem validN_tG : ∀ g ∈ tG, ValidN 12 g := fun g hg => validB_iff.mp (t0Check_parts.2.2.2.1 g hg)

theorem mem_T0_iff' (u : GL (Fin 12) (ZMod 2)) :
    u ∈ T0 ↔ colsN (u : Matrix (Fin 12) (Fin 12) (ZMod 2)) ∈ t0L := by
  refine mem_genSubN_iff tG t0L validN_tG tG_unit (fun x hx => ?_) t0Check_parts.2.2.1
    t0Check_parts.2.1 u
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
  exact ⟨p.2, (t0Check_parts.1 p hp).symm⟩

theorem exists_invD {t : GL (Fin 12) (ZMod 2)} (ht : t ∈ T0)
    (ht2 : t * t = 1) (ht1 : t ≠ 1) :
    ∃ q ∈ invD, q.1 = colsN (t : Matrix (Fin 12) (Fin 12) (ZMod 2)) := by
  refine t0Check_parts.2.2.2.2.1 _ ((mem_T0_iff' t).mp ht) ?_ ?_
  · rw [← colsN_mul, ← Units.val_mul, ht2, Units.val_one, colsN_one]
  · intro h
    apply ht1
    apply eq_of_colsN_eq
    rw [h, Units.val_one, colsN_one]

theorem card_fix_le_of_mem_T0 {t : GL (Fin 12) (ZMod 2)}
    (ht : t ∈ T0) (ht2 : t * t = 1) (ht1 : t ≠ 1) :
    Nat.card {u : Fin 12 → ZMod 2 //
      ((t : GL (Fin 12) (ZMod 2)) : Matrix (Fin 12) (Fin 12) (ZMod 2)) *ᵥ u = u} ≤ 256 := by
  obtain ⟨q, hq, hqt⟩ := exists_invD ht ht2 ht1
  obtain ⟨hm, hf, -, -⟩ := t0Check_parts.2.2.2.2.2.1 q hq
  have h1 := card_fix_le (validN_colsN _) (hqt ▸ hf)
  rw [decN_colsN] at h1
  exact h1.trans (t0Check_parts.2.2.2.2.2.2 _ hm)

theorem exists_fix_of_mem_T0 {t t' : GL (Fin 12) (ZMod 2)}
    (ht : t ∈ T0) (ht' : t' ∈ T0) (ht2 : t * t = 1) (ht'2 : t' * t' = 1) (ht1 : t ≠ 1)
    (ht'1 : t' ≠ 1) (hne : t ≠ t') :
    ∃ u : Fin 12 → ZMod 2,
      ((t : GL (Fin 12) (ZMod 2)) : Matrix (Fin 12) (Fin 12) (ZMod 2)) *ᵥ u = u ∧
        ((t' : GL (Fin 12) (ZMod 2)) : Matrix (Fin 12) (Fin 12) (ZMod 2)) *ᵥ u ≠ u := by
  obtain ⟨q, hq, hqt⟩ := exists_invD ht ht2 ht1
  obtain ⟨q', hq', hqt'⟩ := exists_invD ht' ht'2 ht'1
  obtain ⟨-, -, hb, hall⟩ := t0Check_parts.2.2.2.2.2.1 q hq
  rcases hall q' hq' with h | ⟨b, hbq, hb'⟩
  · exact absurd (eq_of_colsN_eq (hqt.symm.trans (h.symm.trans hqt'))) hne
  obtain ⟨hb4, hbt⟩ := hb b hbq
  have hval : ∀ s : GL (Fin 12) (ZMod 2), ((s : GL (Fin 12) (ZMod 2)) :
      Matrix (Fin 12) (Fin 12) (ZMod 2)) *ᵥ vecN 12 b =
        vecN 12 (mvN (colsN (s : Matrix (Fin 12) (Fin 12) (ZMod 2))) b) := fun s => by
    conv_lhs => rw [← decN_colsN (s : Matrix (Fin 12) (Fin 12) (ZMod 2))]
    exact decN_mulVec (validN_colsN _).1 b
  refine ⟨vecN 12 b, ?_, ?_⟩
  · rw [hval, ← hqt, hbt]
  · have hv' : ValidN 12 q'.1 := by rw [hqt']; exact validN_colsN _
    rw [hval]
    intro h
    rw [← hqt'] at h
    exact hb' (vecN_inj (mvN_lt hv'.2 _) hb4 h)

end CFSG.Quasithin.H.Mathieu.M22Row
