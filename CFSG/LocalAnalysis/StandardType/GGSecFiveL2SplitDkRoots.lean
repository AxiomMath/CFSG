module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveL2SplitDkRootsPairs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveL2SplitDkRootsWeyl
public import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelCLLDType

public section

namespace CFSG.StandardType

open CFSG.LieType.RootSystem CFSG.LieType.Universal.Spin

theorem GGDReflRoot.of_pm {k : ℕ} {t : ggWeylD k} {γ X : Fin k → ℤ} (h : GGDReflRoot k t γ)
    (hX : γ = X ∨ γ = -X) : GGDReflRoot k t X := by
  rcases hX with rfl | rfl
  · exact h
  · simpa only [neg_neg] using h.neg

theorem ggDk_orth_dichotomy {k : ℕ} (hk : 4 ≤ k) {t t' : ggWeylD k}
    (ht : ∃ γ, GGDReflRoot k t γ) (ht' : ∃ γ, GGDReflRoot k t' γ) (hne : t ≠ t')
    (hcomm : t * t' = t' * t) : GGDSameSupp k t t' ∨ GGDDisjSupp k t t' := by
  obtain ⟨γ, hγ⟩ := ht
  obtain ⟨γ', hγ'⟩ := ht'
  have hk2 : 2 ≤ k := by omega
  have hmem := hγ.mem (by omega)
  have hmem' := hγ'.mem (by omega)
  obtain ⟨w, i, -, hw⟩ := id hγ
  have key : toStdD k (weylAction (isFiniteType_cartanD k) (t * t')
        (weylAction (isFiniteType_cartanD k) w (Pi.single i 1))) =
      toStdD k (weylAction (isFiniteType_cartanD k) (t' * t)
        (weylAction (isFiniteType_cartanD k) w (Pi.single i 1))) := by
    rw [hcomm]
  rw [weylAction_mul_apply, weylAction_mul_apply, hγ.action hk2, hγ'.action hk2,
    hγ'.action hk2, hγ.action hk2, hw] at key
  rcases ggDReflect_comm_dot (ggDDot_self_of_mem hmem) (ggDDot_self_of_mem hmem') key with
    h0 | h0 | h0
  · rcases ggDRootSet_orth hmem hmem' h0 with
      ⟨a, b, s, hab, hs, hγe, hγ'e⟩ | ⟨a, b, c, d, s, s', u, u', h1, h2, h3, h4, h5, h6, h7, h8,
        h9, h10, rfl, rfl⟩
    · exact Or.inl ⟨a, b, s, hab, hs, hγ.of_pm hγe, hγ'.of_pm hγ'e⟩
    · exact Or.inr ⟨a, b, c, d, s, s', u, u', h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, hγ, hγ'⟩
  · exact absurd (hγ.unique hk2 hγ' (Or.inl h0)) hne
  · exact absurd (hγ.unique hk2 hγ' (Or.inr h0)) hne

private theorem simple_root_of_lt {k : ℕ} {a : Fin k} (h : a.val + 1 < k) :
    GGDReflRoot k ((coxeterMatrix (isFiniteType_cartanD k)).simple a)
      (Pi.single a 1 + Pi.single ⟨a.val + 1, h⟩ (-1)) := by
  have := ggDReflRoot_simple k a
  rwa [toStdD_single_of_lt k h, sub_eq_add_neg, ← Pi.single_neg] at this

private theorem simple_root_last {k : ℕ} (hk : 2 ≤ k) {a : Fin k} (h : ¬a.val + 1 < k) :
    GGDReflRoot k ((coxeterMatrix (isFiniteType_cartanD k)).simple a)
      (Pi.single ⟨k - 2, by omega⟩ 1 + Pi.single a 1) := by
  have := ggDReflRoot_simple k a
  rwa [toStdD_single_of_not_lt k h hk] at this

theorem ggCoxeterMatrixD_label_two {k : ℕ} (hk : 4 ≤ k) {a b : Fin k} (hab : a ≠ b)
    (h2 : ggCoxeterMatrixD k a b = 2) :
    ((a.val + 2 = k ∧ b.val + 1 = k) ∨ (a.val + 1 = k ∧ b.val + 2 = k)) ∨
      GGDDisjSupp k ((coxeterMatrix (isFiniteType_cartanD k)).simple a)
        ((coxeterMatrix (isFiniteType_cartanD k)).simple b) := by
  have hD : CartanMatrix.D k a b = 0 := by
    rw [ggCoxeterMatrixD_apply, if_neg hab] at h2
    by_contra hne
    rw [if_neg hne] at h2
    omega
  have hab' : a.val ≠ b.val := fun e => hab (Fin.ext e)
  have key : ¬(a.val + 1 = b.val ∧ b.val + 2 < k) ∧ ¬(b.val + 1 = a.val ∧ a.val + 2 < k) ∧
      ¬(a.val + 3 = k ∧ (b.val + 2 = k ∨ b.val + 1 = k)) ∧
      ¬(b.val + 3 = k ∧ (a.val + 2 = k ∨ a.val + 1 = k)) := by
    simp only [CartanMatrix.D, Matrix.of_apply] at hD
    split_ifs at hD <;> omega
  by_cases ha : a.val + 1 < k
  · by_cases hb : b.val + 1 < k
    · refine Or.inr ⟨a, ⟨a.val + 1, ha⟩, b, ⟨b.val + 1, hb⟩, 1, -1, 1, -1,
        Fin.ne_of_val_ne (by simp only; omega), Fin.ne_of_val_ne (by simp only; omega), hab,
        Fin.ne_of_val_ne (by simp only; omega), Fin.ne_of_val_ne (by simp only; omega),
        Fin.ne_of_val_ne (by simp only; omega), Or.inl rfl, Or.inr rfl, Or.inl rfl, Or.inr rfl,
        simple_root_of_lt ha, simple_root_of_lt hb⟩
    · by_cases ha2 : a.val + 2 = k
      · exact Or.inl (Or.inl ⟨ha2, by omega⟩)
      · refine Or.inr ⟨a, ⟨a.val + 1, ha⟩, ⟨k - 2, by omega⟩, b, 1, -1, 1, 1,
          Fin.ne_of_val_ne (by simp only; omega), Fin.ne_of_val_ne (by simp only; omega),
          Fin.ne_of_val_ne (by simp only; omega), hab, Fin.ne_of_val_ne (by simp only; omega),
          Fin.ne_of_val_ne (by simp only; omega), Or.inl rfl, Or.inr rfl, Or.inl rfl, Or.inl rfl,
          simple_root_of_lt ha, simple_root_last (by omega) hb⟩
  · have hb : b.val + 1 < k := by omega
    by_cases hb2 : b.val + 2 = k
    · exact Or.inl (Or.inr ⟨by omega, hb2⟩)
    · refine Or.inr ⟨⟨k - 2, by omega⟩, a, b, ⟨b.val + 1, hb⟩, 1, 1, 1, -1,
        Fin.ne_of_val_ne (by simp only; omega), Fin.ne_of_val_ne (by simp only; omega),
        Fin.ne_of_val_ne (by simp only; omega), Fin.ne_of_val_ne (by simp only; omega), hab,
        Fin.ne_of_val_ne (by simp only; omega), Or.inl rfl, Or.inl rfl, Or.inl rfl, Or.inr rfl,
        simple_root_last (by omega) ha, simple_root_of_lt hb⟩

end CFSG.StandardType

end
