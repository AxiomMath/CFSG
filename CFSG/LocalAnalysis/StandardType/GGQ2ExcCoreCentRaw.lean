module

public import CFSG.LocalAnalysis.StandardType.GGQ2ExcRaw

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

public section

namespace CFSG.StandardType.GGQ2Frame.ExcRaw

@[expose] def AdjIndep (m : Fin 6) : Prop :=
  ∀ i j : Root m, i ≠ j → Adj m i j →
    ((pairing m i j : ℤ) : ZMod 3) ≠ 0 ∧ ((pairing m j i : ℤ) : ZMod 3) ≠ 0 ∧
      ∀ a b : ZMod 3, a • coroot m i + b • coroot m j = 0 → a = 0 ∧ b = 0

private theorem cent_root_reflection (m : Fin 6) (k l : Root m) (v : V m) :
    root m k (reflection m l v) =
      root m k v - root m l v * ((pairing m k l : ℤ) : ZMod 3) := by
  rw [reflection_apply, map_sub, map_smul, smul_eq_mul, pairing_eq]

private theorem cent_reflection_reflection (m : Fin 6) (i j : Root m) (v : V m) :
    reflection m i (reflection m j v) =
      v + (- root m i v + root m j v * ((pairing m i j : ℤ) : ZMod 3)) • coroot m i +
        (- root m j v) • coroot m j := by
  rw [reflection_apply, cent_root_reflection m i j v, reflection_apply]
  funext k
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem root_eq_zero_of_reflection_fix {m : Fin 6} (hA : AdjIndep m) {i j : Root m}
    (hij : i ≠ j) (hadj : Adj m i j) {u : V m}
    (hu : reflection m i (reflection m j (reflection m i (reflection m j u))) = u) :
    root m i u = 0 := by
  obtain ⟨hP, hP', hindep⟩ := hA i j hij hadj
  have hri : root m i (reflection m i (reflection m j u)) =
      root m i u + (- root m i u + root m j u * ((pairing m i j : ℤ) : ZMod 3)) * 2 +
        (- root m j u) * ((pairing m i j : ℤ) : ZMod 3) := by
    rw [cent_reflection_reflection m i j u, map_add, map_add, map_smul, map_smul,
      root_coroot, pairing_eq, smul_eq_mul, smul_eq_mul]
  have hrj : root m j (reflection m i (reflection m j u)) =
      root m j u + (- root m i u + root m j u * ((pairing m i j : ℤ) : ZMod 3)) *
        ((pairing m j i : ℤ) : ZMod 3) + (- root m j u) * 2 := by
    rw [cent_reflection_reflection m i j u, map_add, map_add, map_smul, map_smul,
      root_coroot, pairing_eq, smul_eq_mul, smul_eq_mul]
  have hsq : reflection m i (reflection m j (reflection m i (reflection m j u))) =
      u + (((pairing m i j : ℤ) : ZMod 3) *
          ((- root m i u + root m j u * ((pairing m i j : ℤ) : ZMod 3)) *
              ((pairing m j i : ℤ) : ZMod 3) + (- root m j u))) • coroot m i +
        (-((- root m i u + root m j u * ((pairing m i j : ℤ) : ZMod 3)) *
              ((pairing m j i : ℤ) : ZMod 3))) • coroot m j := by
    rw [cent_reflection_reflection m i j (reflection m i (reflection m j u)), hri, hrj,
      cent_reflection_reflection m i j u]
    funext k
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hzero : (((pairing m i j : ℤ) : ZMod 3) *
        ((- root m i u + root m j u * ((pairing m i j : ℤ) : ZMod 3)) *
            ((pairing m j i : ℤ) : ZMod 3) + (- root m j u))) • coroot m i +
      (-((- root m i u + root m j u * ((pairing m i j : ℤ) : ZMod 3)) *
            ((pairing m j i : ℤ) : ZMod 3))) • coroot m j = 0 := by
    have h := hu
    rw [hsq] at h
    have h' : u + ((((pairing m i j : ℤ) : ZMod 3) *
          ((- root m i u + root m j u * ((pairing m i j : ℤ) : ZMod 3)) *
              ((pairing m j i : ℤ) : ZMod 3) + (- root m j u))) • coroot m i +
        (-((- root m i u + root m j u * ((pairing m i j : ℤ) : ZMod 3)) *
              ((pairing m j i : ℤ) : ZMod 3))) • coroot m j) = u + 0 := by
      rw [add_zero, ← add_assoc]
      exact h
    exact add_left_cancel h'
  obtain ⟨hcoef, hcoef'⟩ := hindep _ _ hzero
  have hxP' : (- root m i u + root m j u * ((pairing m i j : ℤ) : ZMod 3)) *
      ((pairing m j i : ℤ) : ZMod 3) = 0 := neg_eq_zero.mp hcoef'
  have hx : - root m i u + root m j u * ((pairing m i j : ℤ) : ZMod 3) = 0 := by
    rcases mul_eq_zero.mp hxP' with h | h
    · exact h
    · exact absurd h hP'
  have hb : root m j u = 0 := by
    have h := hcoef
    rw [hx, zero_mul, zero_add] at h
    have h' : - root m j u = 0 := by
      rcases mul_eq_zero.mp h with h2 | h2
      · exact absurd h2 hP
      · exact h2
    exact neg_eq_zero.mp h'
  have h := hx
  rw [hb, zero_mul, add_zero] at h
  exact neg_eq_zero.mp h

private abbrev centAdjCheck (m : Fin 6) : Prop :=
  ∀ i j : Root m, i ≠ j → (pairing m i j ≠ 0 ∨ pairing m j i ≠ 0) →
    pairing m i j % 3 ≠ 0 ∧ pairing m j i % 3 ≠ 0 ∧
      ∃ k l : Fin (dim m), (H m i k * H m j l - H m i l * H m j k) % 3 ≠ 0

private theorem cent_adjIndep_of_check {m : Fin 6} (h : centAdjCheck m) : AdjIndep m := by
  intro i j hij hadj
  obtain ⟨hp, hp', k, l, hkl⟩ := h i j hij hadj
  have hne : ((H m i k * H m j l - H m i l * H m j k : ℤ) : ZMod 3) ≠ 0 := by
    intro h0
    exact hkl (Int.dvd_iff_emod_eq_zero.mp
      ((ZMod.intCast_zmod_eq_zero_iff_dvd (H m i k * H m j l - H m i l * H m j k) 3).1 h0))
  refine ⟨?_, ?_, ?_⟩
  · intro h0
    exact hp (Int.dvd_iff_emod_eq_zero.mp
      ((ZMod.intCast_zmod_eq_zero_iff_dvd (pairing m i j) 3).1 h0))
  · intro h0
    exact hp' (Int.dvd_iff_emod_eq_zero.mp
      ((ZMod.intCast_zmod_eq_zero_iff_dvd (pairing m j i) 3).1 h0))
  · intro a b hab
    have hk : a * ((H m i k : ℤ) : ZMod 3) + b * ((H m j k : ℤ) : ZMod 3) = 0 := by
      have h1 := congrFun hab k
      simpa only [Pi.add_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul, coroot] using h1
    have hl : a * ((H m i l : ℤ) : ZMod 3) + b * ((H m j l : ℤ) : ZMod 3) = 0 := by
      have h1 := congrFun hab l
      simpa only [Pi.add_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul, coroot] using h1
    have hk' : a * ((H m i k : ℤ) : ZMod 3) = -(b * ((H m j k : ℤ) : ZMod 3)) :=
      eq_neg_of_add_eq_zero_left hk
    have hl' : a * ((H m i l : ℤ) : ZMod 3) = -(b * ((H m j l : ℤ) : ZMod 3)) :=
      eq_neg_of_add_eq_zero_left hl
    have hk'' : b * ((H m j k : ℤ) : ZMod 3) = -(a * ((H m i k : ℤ) : ZMod 3)) :=
      eq_neg_of_add_eq_zero_right hk
    have hl'' : b * ((H m j l : ℤ) : ZMod 3) = -(a * ((H m i l : ℤ) : ZMod 3)) :=
      eq_neg_of_add_eq_zero_right hl
    have ha : a * ((H m i k * H m j l - H m i l * H m j k : ℤ) : ZMod 3) = 0 := by
      push_cast
      calc a * ((H m i k : ZMod 3) * (H m j l : ZMod 3) - (H m i l : ZMod 3) * (H m j k : ZMod 3))
          = a * (H m i k : ZMod 3) * (H m j l : ZMod 3) -
              a * (H m i l : ZMod 3) * (H m j k : ZMod 3) := by ring
        _ = -(b * (H m j k : ZMod 3)) * (H m j l : ZMod 3) -
              (-(b * (H m j l : ZMod 3))) * (H m j k : ZMod 3) := by rw [hk', hl']
        _ = 0 := by ring
    have hb : b * ((H m i k * H m j l - H m i l * H m j k : ℤ) : ZMod 3) = 0 := by
      push_cast
      calc b * ((H m i k : ZMod 3) * (H m j l : ZMod 3) - (H m i l : ZMod 3) * (H m j k : ZMod 3))
          = b * (H m j l : ZMod 3) * (H m i k : ZMod 3) -
              b * (H m j k : ZMod 3) * (H m i l : ZMod 3) := by ring
        _ = (-(a * (H m i l : ZMod 3))) * (H m i k : ZMod 3) -
              (-(a * (H m i k : ZMod 3))) * (H m i l : ZMod 3) := by rw [hl'', hk'']
        _ = 0 := by ring
    refine ⟨?_, ?_⟩
    · rcases mul_eq_zero.mp ha with h | h
      · exact h
      · exact absurd h hne
    · rcases mul_eq_zero.mp hb with h | h
      · exact h
      · exact absurd h hne

theorem adjIndep_one : AdjIndep 1 :=
  cent_adjIndep_of_check (by decide +kernel)

theorem adjIndep_two : AdjIndep 2 :=
  cent_adjIndep_of_check (by decide +kernel)

theorem adjIndep_three : AdjIndep 3 :=
  cent_adjIndep_of_check (by decide +kernel)

theorem adjIndep_zero : AdjIndep 0 :=
  cent_adjIndep_of_check (by decide +kernel)

theorem adjIndep_four : AdjIndep 4 :=
  cent_adjIndep_of_check (by decide +kernel)

theorem adjIndep_five : AdjIndep 5 :=
  cent_adjIndep_of_check (by decide +kernel)

theorem not_largeEvenInLambda2_label_singleton {m : Fin 6} (hm : m.val ≠ 1) (i : Root m) :
    ¬ CFSG.Assembly.LargeEvenInLambda2 (label m {i}) := by
  have hlab : label m {i} = ⟨.A, 1, 1⟩ := by
    unfold label
    rw [Finset.card_singleton]
    split
    · rfl
    · exact absurd ‹m.val = 1› hm
    · rfl
  rw [hlab]
  simp [CFSG.Assembly.LargeEvenInLambda2]

end CFSG.StandardType.GGQ2Frame.ExcRaw

end
