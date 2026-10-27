module

public import CFSG.LocalAnalysis.StandardType.GGFrameModelNumB

public section

namespace CFSG.StandardType.FrameRoute

open CFSG SpCoord Multiplicative

variable {k : ℕ}

private abbrev frameST_V (k : ℕ) := Fin k → Multiplicative (ZMod 3)

private theorem frameST_sgnAut_coord (i j : Fin k) (f : frameST_V k) :
    (sgnAut i : MulAut (frameST_V k)) f j = if j = i then (f j)⁻¹ else f j := by
  rw [sgnAut_apply, Function.update_apply]
  split_ifs with h
  · rw [h]
    rfl
  · rfl

private theorem frameST_permAut_swap_coord (a b j : Fin k) (f : frameST_V k) :
    (permAut (Equiv.swap a b) : MulAut (frameST_V k)) f j = f (Equiv.swap a b j) := by
  rw [permAut_apply, Function.comp_apply, Equiv.swap_inv]

private theorem frameST_negSwapAut_comm (a b : Fin k) :
    (negSwapAut a b : MulAut (frameST_V k)) = negSwapAut b a := by
  rw [negSwapAut, negSwapAut, sgnAut_mul_comm a b, Equiv.swap_comm]

private theorem frameST_swap_apply_self_iff {a b i : Fin k} (hab : a ≠ b) :
    Equiv.swap a b i = i ↔ i ≠ a ∧ i ≠ b := by
  constructor
  · intro h
    constructor
    · intro hia
      rw [hia, Equiv.swap_apply_left] at h
      exact hab h.symm
    · intro hib
      rw [hib, Equiv.swap_apply_right] at h
      exact hab h
  · rintro ⟨hia, hib⟩
    exact Equiv.swap_apply_of_ne_of_ne hia hib

private theorem frameST_swap_mul_comm {a b c d : Fin k}
    (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) :
    Equiv.swap a b * Equiv.swap c d = Equiv.swap c d * Equiv.swap a b := by
  have h1 : Equiv.swap a b * Equiv.swap c d =
      Equiv.swap c d * Equiv.swap (Equiv.swap c d a) (Equiv.swap c d b) := by
    simpa only [Equiv.swap_inv] using Equiv.swap_mul_eq_mul_swap (Equiv.swap c d) a b
  rwa [Equiv.swap_apply_of_ne_of_ne hac had, Equiv.swap_apply_of_ne_of_ne hbc hbd] at h1

private theorem frameST_sgnAut_basis_same (i : Fin k) (c : ZMod 3) :
    (sgnAut i : MulAut (frameST_V k)) (Pi.mulSingle i (ofAdd c)) =
      Pi.mulSingle i (ofAdd (-c)) := by
  rw [sgnAut_mulSingle_self, ← Pi.mulSingle_inv, ← ofAdd_neg]
  rfl

private theorem frameST_sgnAut_basis_of_ne {i j : Fin k} (h : j ≠ i) (c : ZMod 3) :
    (sgnAut i : MulAut (frameST_V k)) (Pi.mulSingle j (ofAdd c)) = Pi.mulSingle j (ofAdd c) :=
  sgnAut_mulSingle_of_ne h (ofAdd c)

private theorem frameST_permAut_swap_basis (a b j : Fin k) (c : ZMod 3) :
    (permAut (Equiv.swap a b) : MulAut (frameST_V k)) (Pi.mulSingle j (ofAdd c)) =
      Pi.mulSingle (Equiv.swap a b j) (ofAdd c) :=
  permAut_mulSingle (Equiv.swap a b) j (ofAdd c)

private theorem frameST_negSwapAut_basis_self {a b : Fin k} (hab : a ≠ b) (c : ZMod 3) :
    (negSwapAut a b : MulAut (frameST_V k)) (Pi.mulSingle a (ofAdd c)) =
      Pi.mulSingle b (ofAdd (-c)) := by
  rw [negSwapAut, MulAut.mul_apply, MulAut.mul_apply, frameST_permAut_swap_basis,
    Equiv.swap_apply_left, frameST_sgnAut_basis_same, frameST_sgnAut_basis_of_ne (Ne.symm hab)]

private theorem frameST_negSwapAut_basis_other {a b : Fin k} (hab : a ≠ b) (c : ZMod 3) :
    (negSwapAut a b : MulAut (frameST_V k)) (Pi.mulSingle b (ofAdd c)) =
      Pi.mulSingle a (ofAdd (-c)) := by
  rw [frameST_negSwapAut_comm, frameST_negSwapAut_basis_self (Ne.symm hab)]

private theorem frameST_negSwapAut_basis_of_ne {a b j : Fin k}
    (hja : j ≠ a) (hjb : j ≠ b) (c : ZMod 3) :
    (negSwapAut a b : MulAut (frameST_V k)) (Pi.mulSingle j (ofAdd c)) =
      Pi.mulSingle j (ofAdd c) := by
  rw [negSwapAut, MulAut.mul_apply, MulAut.mul_apply, frameST_permAut_swap_basis,
    Equiv.swap_apply_of_ne_of_ne hja hjb, frameST_sgnAut_basis_of_ne hjb,
    frameST_sgnAut_basis_of_ne hja]

private theorem frameST_eq_of_forall_eval {x y : Fin k}
    (h : ∀ f : frameST_V k, f x = f y) : x = y := by
  by_contra hxy
  have h1 := congrArg toAdd (h (Pi.mulSingle x (ofAdd 1)))
  rw [Pi.mulSingle_eq_same, Pi.mulSingle_eq_of_ne (Ne.symm hxy)] at h1
  exact (by decide : (1 : ZMod 3) ≠ 0) (by simpa using h1)

private theorem frameST_sgnAut_mul_permAut_swap_apply (a b i j : Fin k) (f : frameST_V k) :
    (sgnAut i * permAut (Equiv.swap a b) : MulAut (frameST_V k)) f j =
      if j = i then (f (Equiv.swap a b j))⁻¹ else f (Equiv.swap a b j) := by
  rw [MulAut.mul_apply, frameST_sgnAut_coord i j (permAut (Equiv.swap a b) f),
    frameST_permAut_swap_coord a b j f]

private theorem frameST_permAut_swap_mul_sgnAut_apply (a b i j : Fin k) (f : frameST_V k) :
    (permAut (Equiv.swap a b) * sgnAut i : MulAut (frameST_V k)) f j =
      if Equiv.swap a b j = i then (f (Equiv.swap a b j))⁻¹ else f (Equiv.swap a b j) := by
  rw [MulAut.mul_apply, frameST_permAut_swap_coord a b j (sgnAut i f),
    frameST_sgnAut_coord i (Equiv.swap a b j) f]

private theorem frameST_permAut_swap_mul_permAut_swap_apply (a b c d j : Fin k) (f : frameST_V k) :
    (permAut (Equiv.swap a b) * permAut (Equiv.swap c d) : MulAut (frameST_V k)) f j =
      f (Equiv.swap c d (Equiv.swap a b j)) := by
  rw [MulAut.mul_apply, frameST_permAut_swap_coord a b j (permAut (Equiv.swap c d) f),
    frameST_permAut_swap_coord c d (Equiv.swap a b j) f]

private theorem frameST_permAut_swap_mul_sgnAut_left {a b : Fin k} (hab : a ≠ b) :
    (permAut (Equiv.swap a b) : MulAut (frameST_V k)) * sgnAut a =
      sgnAut b * permAut (Equiv.swap a b) := by
  refine MulEquiv.ext fun f => funext fun j => ?_
  rw [MulAut.mul_apply, MulAut.mul_apply,
    frameST_permAut_swap_coord a b j (sgnAut a f),
    frameST_sgnAut_coord a (Equiv.swap a b j) f,
    frameST_sgnAut_coord b j (permAut (Equiv.swap a b) f),
    frameST_permAut_swap_coord a b j f]
  by_cases h : j = b
  · subst h
    simp only [if_pos rfl, if_neg hab, Equiv.swap_apply_left, Equiv.swap_apply_right,
      if_true, if_false]
  · have h' : Equiv.swap a b j ≠ a := by
      intro hh
      have h1 : j = b :=
        calc j = Equiv.swap a b (Equiv.swap a b j) := (Equiv.swap_apply_self a b j).symm
          _ = Equiv.swap a b a := by rw [hh]
          _ = b := Equiv.swap_apply_left a b
      exact h h1
    simp only [if_neg h, if_neg h']

private theorem frameST_permAut_swap_mul_sgnAut_right {a b : Fin k} (hab : a ≠ b) :
    (permAut (Equiv.swap a b) : MulAut (frameST_V k)) * sgnAut b =
      sgnAut a * permAut (Equiv.swap a b) := by
  refine MulEquiv.ext fun f => funext fun j => ?_
  rw [MulAut.mul_apply, MulAut.mul_apply,
    frameST_permAut_swap_coord a b j (sgnAut b f),
    frameST_sgnAut_coord b (Equiv.swap a b j) f,
    frameST_sgnAut_coord a j (permAut (Equiv.swap a b) f),
    frameST_permAut_swap_coord a b j f]
  by_cases h : j = a
  · subst h
    simp only [if_pos rfl, if_neg hab, Equiv.swap_apply_left, Equiv.swap_apply_right,
      if_true, if_false]
  · have h' : Equiv.swap a b j ≠ b := by
      intro hh
      have h1 : j = a :=
        calc j = Equiv.swap a b (Equiv.swap a b j) := (Equiv.swap_apply_self a b j).symm
          _ = Equiv.swap a b b := by rw [hh]
          _ = a := Equiv.swap_apply_right a b
      exact h h1
    simp only [if_neg h, if_neg h']

private theorem frameST_permAut_swap_commute_sgnAut_mul_sgnAut {a b : Fin k} (hab : a ≠ b) :
    Commute (permAut (Equiv.swap a b) : MulAut (frameST_V k)) (sgnAut a * sgnAut b) := by
  rw [commute_iff_eq]
  calc (permAut (Equiv.swap a b) : MulAut (frameST_V k)) * (sgnAut a * sgnAut b)
      = (permAut (Equiv.swap a b) * sgnAut a) * sgnAut b := by rw [mul_assoc]
    _ = (sgnAut b * permAut (Equiv.swap a b)) * sgnAut b := by
          rw [frameST_permAut_swap_mul_sgnAut_left hab]
    _ = sgnAut b * (permAut (Equiv.swap a b) * sgnAut b) := by rw [mul_assoc]
    _ = sgnAut b * (sgnAut a * permAut (Equiv.swap a b)) := by
          rw [frameST_permAut_swap_mul_sgnAut_right hab]
    _ = (sgnAut a * sgnAut b) * permAut (Equiv.swap a b) := by
          rw [← mul_assoc, sgnAut_mul_comm b a]

private theorem frameST_permAut_swap_not_commute_negSwapAut_shared {a b d : Fin k}
    (hab : a ≠ b) (had : a ≠ d) (hbd : b ≠ d) :
    ¬ Commute (permAut (Equiv.swap a b) : MulAut (frameST_V k)) (negSwapAut a d) := by
  intro h
  rw [commute_iff_eq] at h
  have h2 := congrArg (fun u : MulAut (frameST_V k) => u (Pi.mulSingle a (ofAdd 1))) h
  simp only [MulAut.mul_apply, frameST_negSwapAut_basis_self had, frameST_permAut_swap_basis,
    Equiv.swap_apply_of_ne_of_ne (Ne.symm had) (Ne.symm hbd), Equiv.swap_apply_left,
    frameST_negSwapAut_basis_of_ne (Ne.symm hab) hbd] at h2
  exact hbd (SpCoord.mulSingle_ofAdd_eq_iff (x := -1) (y := 1) (by decide) h2).1.symm

private theorem frameST_negSwapAut_not_commute_negSwapAut_shared {a b d : Fin k}
    (hab : a ≠ b) (had : a ≠ d) (hbd : b ≠ d) :
    ¬ Commute (negSwapAut a b : MulAut (frameST_V k)) (negSwapAut a d) := by
  intro h
  rw [commute_iff_eq] at h
  have h2 := congrArg (fun u : MulAut (frameST_V k) => u (Pi.mulSingle a (ofAdd 1))) h
  simp only [MulAut.mul_apply, frameST_negSwapAut_basis_self had,
    frameST_negSwapAut_basis_of_ne (Ne.symm had) (Ne.symm hbd), frameST_negSwapAut_basis_self hab,
    frameST_negSwapAut_basis_of_ne (Ne.symm hab) hbd] at h2
  exact hbd (SpCoord.mulSingle_ofAdd_eq_iff (x := -1) (y := -1) (by decide) h2).1.symm

theorem sgnAut_injective :
    Function.Injective (sgnAut : Fin k → MulAut (Fin k → Multiplicative (ZMod 3))) := by
  intro i j h
  by_contra hne
  have h1 := congrArg
    (fun u : MulAut (Fin k → Multiplicative (ZMod 3)) =>
      toAdd (u (Pi.mulSingle i (ofAdd 1)) i)) h
  rw [frameST_sgnAut_basis_same, frameST_sgnAut_basis_of_ne hne] at h1
  rw [Pi.mulSingle_eq_same, Pi.mulSingle_eq_same, toAdd_ofAdd, toAdd_ofAdd] at h1
  exact (by decide : (-1 : ZMod 3) ≠ 1) h1

theorem permAut_swap_eq_permAut_swap_iff {a b c d : Fin k} (hab : a ≠ b) (hcd : c ≠ d) :
    (permAut (Equiv.swap a b) : MulAut (Fin k → Multiplicative (ZMod 3))) =
        permAut (Equiv.swap c d) ↔
      (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  constructor
  · intro h
    have h1 := congrArg (fun u : MulAut (Fin k → Multiplicative (ZMod 3)) =>
      u (Pi.mulSingle a (ofAdd 1))) h
    rw [frameST_permAut_swap_basis, frameST_permAut_swap_basis,
      Equiv.swap_apply_left] at h1
    have hb : b = Equiv.swap c d a :=
      (SpCoord.mulSingle_ofAdd_eq_iff (x := 1) (y := 1) (by decide) h1).1
    by_cases hac : a = c
    · rw [hac] at hb ⊢
      exact Or.inl ⟨rfl, by rwa [Equiv.swap_apply_left] at hb⟩
    · by_cases had : a = d
      · rw [had] at hb ⊢
        exact Or.inr ⟨rfl, by rwa [Equiv.swap_apply_right] at hb⟩
      · exfalso
        rw [Equiv.swap_apply_of_ne_of_ne hac had] at hb
        exact hab hb.symm
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · rfl
    · rw [Equiv.swap_comm]

theorem negSwapAut_eq_negSwapAut_iff {a b c d : Fin k} (hab : a ≠ b) (hcd : c ≠ d) :
    negSwapAut a b = negSwapAut c d ↔ (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  constructor
  · intro h
    have h1 := congrArg (fun u : MulAut (Fin k → Multiplicative (ZMod 3)) =>
      u (Pi.mulSingle a (ofAdd 1))) h
    rw [frameST_negSwapAut_basis_self hab] at h1
    by_cases hac : a = c
    · rw [hac] at h1 ⊢
      rw [frameST_negSwapAut_basis_self hcd] at h1
      exact Or.inl ⟨rfl, (SpCoord.mulSingle_ofAdd_eq_iff (x := -1) (y := -1)
        (by decide) h1).1⟩
    · by_cases had : a = d
      · rw [had] at h1 ⊢
        rw [frameST_negSwapAut_basis_other hcd] at h1
        exact Or.inr ⟨rfl, (SpCoord.mulSingle_ofAdd_eq_iff (x := -1) (y := -1)
          (by decide) h1).1⟩
      · exfalso
        rw [frameST_negSwapAut_basis_of_ne hac had] at h1
        exact hab (SpCoord.mulSingle_ofAdd_eq_iff (x := -1) (y := 1)
          (by decide) h1).1.symm
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · rfl
    · exact frameST_negSwapAut_comm _ _

theorem sgnAut_ne_permAut_swap (i : Fin k) {a b : Fin k} (hab : a ≠ b) :
    (sgnAut i : MulAut (Fin k → Multiplicative (ZMod 3))) ≠ permAut (Equiv.swap a b) := by
  intro h
  have h1 := congrArg (fun u : MulAut (Fin k → Multiplicative (ZMod 3)) =>
    toAdd (u (Pi.mulSingle a (ofAdd 1)) b)) h
  rw [frameST_sgnAut_coord i b (Pi.mulSingle a (ofAdd 1)), frameST_permAut_swap_basis,
    Equiv.swap_apply_left, Pi.mulSingle_eq_of_ne (Ne.symm hab)] at h1
  by_cases hbi : b = i
  · rw [if_pos hbi, toAdd_inv, toAdd_one, Pi.mulSingle_eq_same, toAdd_ofAdd] at h1
    exact (by decide : (0 : ZMod 3) ≠ 1) h1
  · rw [if_neg hbi, Pi.mulSingle_eq_same, toAdd_ofAdd] at h1
    exact (by decide : (0 : ZMod 3) ≠ 1) h1

theorem sgnAut_ne_negSwapAut (i : Fin k) {a b : Fin k} (hab : a ≠ b) :
    sgnAut i ≠ negSwapAut a b := by
  intro h
  have h1 := congrArg (fun u : MulAut (Fin k → Multiplicative (ZMod 3)) =>
    toAdd (u (Pi.mulSingle a (ofAdd 1)) b)) h
  rw [frameST_sgnAut_coord i b (Pi.mulSingle a (ofAdd 1)),
    frameST_negSwapAut_basis_self hab, Pi.mulSingle_eq_of_ne (Ne.symm hab),
    Pi.mulSingle_eq_same, toAdd_ofAdd] at h1
  by_cases hbi : b = i
  · rw [if_pos hbi, toAdd_inv, toAdd_one] at h1
    exact (by decide : (0 : ZMod 3) ≠ -1) h1
  · rw [if_neg hbi, toAdd_one] at h1
    exact (by decide : (0 : ZMod 3) ≠ -1) h1

theorem permAut_swap_ne_negSwapAut {a b c d : Fin k} (hab : a ≠ b) (hcd : c ≠ d) :
    permAut (Equiv.swap a b) ≠ negSwapAut c d := by
  intro h
  have h1 := congrArg (fun u : MulAut (Fin k → Multiplicative (ZMod 3)) =>
    u (Pi.mulSingle a (ofAdd 1))) h
  rw [frameST_permAut_swap_basis, Equiv.swap_apply_left] at h1
  by_cases hac : a = c
  · rw [hac] at h1
    rw [frameST_negSwapAut_basis_self hcd] at h1
    exact (by decide : (1 : ZMod 3) ≠ -1)
      ((SpCoord.mulSingle_ofAdd_eq_iff (x := 1) (y := -1) (by decide) h1).2)
  · by_cases had : a = d
    · rw [had] at h1
      rw [frameST_negSwapAut_basis_other hcd] at h1
      exact (by decide : (1 : ZMod 3) ≠ -1)
        ((SpCoord.mulSingle_ofAdd_eq_iff (x := 1) (y := -1) (by decide) h1).2)
    · rw [frameST_negSwapAut_basis_of_ne hac had] at h1
      exact hab ((SpCoord.mulSingle_ofAdd_eq_iff (x := 1) (y := 1)
        (by decide) h1).1.symm)

theorem sgnAut_commute_sgnAut (i j : Fin k) :
    Commute (sgnAut i : MulAut (Fin k → Multiplicative (ZMod 3))) (sgnAut j) := by
  exact sgnAut_mul_comm i j

theorem sgnAut_commute_permAut_swap_iff (i : Fin k) {a b : Fin k} (hab : a ≠ b) :
    Commute (sgnAut i : MulAut (Fin k → Multiplicative (ZMod 3))) (permAut (Equiv.swap a b)) ↔
      i ≠ a ∧ i ≠ b := by
  constructor
  · intro h
    rw [commute_iff_eq] at h
    by_cases hsi : Equiv.swap a b i = i
    · exact (frameST_swap_apply_self_iff hab).1 hsi
    · have h2 := congrArg (fun u : MulAut (Fin k → Multiplicative (ZMod 3)) =>
        toAdd (u (Pi.mulSingle (Equiv.swap a b i) (ofAdd 1)) i)) h
      rw [frameST_sgnAut_mul_permAut_swap_apply,
        frameST_permAut_swap_mul_sgnAut_apply, if_neg hsi] at h2
      rw [if_pos rfl, Pi.mulSingle_eq_same, toAdd_inv, toAdd_ofAdd] at h2
      exact absurd h2 (by decide)
  · rintro ⟨hia, hib⟩
    rw [commute_iff_eq]
    have hsi : Equiv.swap a b i = i := (frameST_swap_apply_self_iff hab).2 ⟨hia, hib⟩
    refine MulEquiv.ext fun f => funext fun j => ?_
    rw [frameST_sgnAut_mul_permAut_swap_apply, frameST_permAut_swap_mul_sgnAut_apply]
    by_cases hji : j = i
    · rw [hji, if_pos rfl, if_pos hsi]
    · rw [if_neg hji, if_neg (by
        intro hh
        exact hji ((Equiv.swap a b).injective (hh.trans hsi.symm)))]

theorem sgnAut_commute_negSwapAut_iff (i : Fin k) {a b : Fin k} (hab : a ≠ b) :
    Commute (sgnAut i) (negSwapAut a b) ↔ i ≠ a ∧ i ≠ b := by
  constructor
  · intro h
    rw [commute_iff_eq] at h
    constructor
    · intro hia
      have h1 := congrArg (fun u : MulAut (Fin k → Multiplicative (ZMod 3)) =>
        toAdd (u (Pi.mulSingle a (ofAdd 1)) b)) h
      rw [hia] at h1
      rw [MulAut.mul_apply, MulAut.mul_apply, frameST_negSwapAut_basis_self hab,
        frameST_sgnAut_basis_of_ne (Ne.symm hab), frameST_sgnAut_basis_same,
        frameST_negSwapAut_basis_self hab, Pi.mulSingle_eq_same, Pi.mulSingle_eq_same,
        toAdd_ofAdd, toAdd_ofAdd] at h1
      exact (by decide : (-1 : ZMod 3) ≠ -(-1)) h1
    · intro hib
      have h1 := congrArg (fun u : MulAut (Fin k → Multiplicative (ZMod 3)) =>
        toAdd (u (Pi.mulSingle b (ofAdd 1)) a)) h
      rw [hib] at h1
      rw [MulAut.mul_apply, MulAut.mul_apply, frameST_negSwapAut_basis_other hab,
        frameST_sgnAut_basis_of_ne hab, frameST_sgnAut_basis_same,
        frameST_negSwapAut_basis_other hab, Pi.mulSingle_eq_same, Pi.mulSingle_eq_same,
        toAdd_ofAdd, toAdd_ofAdd] at h1
      exact (by decide : (-1 : ZMod 3) ≠ -(-1)) h1
  · rintro ⟨hia, hib⟩
    rw [negSwapAut]
    exact ((sgnAut_commute_sgnAut i a).mul_right (sgnAut_commute_sgnAut i b)).mul_right
      ((sgnAut_commute_permAut_swap_iff i hab).2 ⟨hia, hib⟩)

theorem permAut_swap_commute_permAut_swap_iff {a b c d : Fin k} (hab : a ≠ b) (hcd : c ≠ d) :
    Commute (permAut (Equiv.swap a b) : MulAut (Fin k → Multiplicative (ZMod 3)))
        (permAut (Equiv.swap c d)) ↔
      (a = c ∧ b = d) ∨ (a = d ∧ b = c) ∨ (a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d) := by
  constructor
  · intro h
    rw [commute_iff_eq] at h
    have hA : Equiv.swap c d b = Equiv.swap a b (Equiv.swap c d a) := by
      refine frameST_eq_of_forall_eval fun f => ?_
      have h2 := congrArg (fun u : MulAut (Fin k → Multiplicative (ZMod 3)) => u f a) h
      simp only [MulAut.mul_apply, frameST_permAut_swap_coord] at h2
      simpa using h2
    have hB : Equiv.swap c d a = Equiv.swap a b (Equiv.swap c d b) := by
      refine frameST_eq_of_forall_eval fun f => ?_
      have h2 := congrArg (fun u : MulAut (Fin k → Multiplicative (ZMod 3)) => u f b) h
      simp only [MulAut.mul_apply, frameST_permAut_swap_coord] at h2
      simpa using h2
    have hτ : (Equiv.swap c d a = a ∧ Equiv.swap c d b = b) ∨
        (Equiv.swap c d a = b ∧ Equiv.swap c d b = a) := by
      by_cases hfa : Equiv.swap c d a = a
      · refine Or.inl ⟨hfa, ?_⟩
        rw [hA, hfa, Equiv.swap_apply_left]
      · by_cases hfb : Equiv.swap c d a = b
        · refine Or.inr ⟨hfb, ?_⟩
          rw [hA, hfb, Equiv.swap_apply_right]
        · exfalso
          have h3 : Equiv.swap a b (Equiv.swap c d a) = Equiv.swap c d a :=
            Equiv.swap_apply_of_ne_of_ne hfa hfb
          exact hab ((Equiv.swap c d).injective (hA.trans h3)).symm
    rcases hτ with ⟨hfa, hfb⟩ | ⟨hfa, hfb⟩
    · exact Or.inr (Or.inr
        ⟨((frameST_swap_apply_self_iff hcd).1 hfa).1, ((frameST_swap_apply_self_iff hcd).1 hfa).2,
         ((frameST_swap_apply_self_iff hcd).1 hfb).1,
         ((frameST_swap_apply_self_iff hcd).1 hfb).2⟩)
    · have hne1 : Equiv.swap c d a ≠ a := by
        rw [hfa]
        exact fun hh => hab hh.symm
      have hne2 : Equiv.swap c d b ≠ b := by
        rw [hfb]
        exact fun hh => hab hh
      have h1 : a = c ∨ a = d := Equiv.eq_or_eq_of_swap_apply_ne_self hne1
      have h2 : b = c ∨ b = d := Equiv.eq_or_eq_of_swap_apply_ne_self hne2
      rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
      · exact absurd (h1.trans h2.symm) hab
      · exact Or.inl ⟨h1, h2⟩
      · exact Or.inr (Or.inl ⟨h1, h2⟩)
      · exact absurd (h1.trans h2.symm) hab
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨hac, had, hbc, hbd⟩)
    · exact Commute.refl _
    · rw [Equiv.swap_comm]
    · rw [commute_iff_eq]
      refine MulEquiv.ext fun f => funext fun j => ?_
      rw [frameST_permAut_swap_mul_permAut_swap_apply,
        frameST_permAut_swap_mul_permAut_swap_apply]
      have h1 := frameST_swap_mul_comm hac had hbc hbd
      have h2 : Equiv.swap c d (Equiv.swap a b j) = Equiv.swap a b (Equiv.swap c d j) := by
        rw [← Equiv.Perm.mul_apply, ← Equiv.Perm.mul_apply, h1]
      exact congrArg f h2

theorem permAut_swap_commute_negSwapAut_iff {a b c d : Fin k} (hab : a ≠ b) (hcd : c ≠ d) :
    Commute (permAut (Equiv.swap a b)) (negSwapAut c d) ↔
      (a = c ∧ b = d) ∨ (a = d ∧ b = c) ∨ (a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d) := by
  constructor
  · intro h
    by_cases hac : a = c
    · by_cases hbd : b = d
      · exact Or.inl ⟨hac, hbd⟩
      · exfalso
        rw [← hac] at h
        exact frameST_permAut_swap_not_commute_negSwapAut_shared hab
          (fun hh => hcd (hac.symm.trans hh)) hbd h
    · by_cases had : a = d
      · by_cases hbc : b = c
        · exact Or.inr (Or.inl ⟨had, hbc⟩)
        · exfalso
          rw [← had, frameST_negSwapAut_comm] at h
          exact frameST_permAut_swap_not_commute_negSwapAut_shared hab
            (fun hh => hcd (had.symm.trans hh).symm) hbc h
      · by_cases hbc : b = c
        · exfalso
          rw [Equiv.swap_comm, ← hbc] at h
          exact frameST_permAut_swap_not_commute_negSwapAut_shared (Ne.symm hab)
            (fun hh => hcd (hbc.symm.trans hh)) had h
        · by_cases hbd : b = d
          · exfalso
            rw [Equiv.swap_comm, ← hbd, frameST_negSwapAut_comm] at h
            exact frameST_permAut_swap_not_commute_negSwapAut_shared (Ne.symm hab) hbc hac h
          · exact Or.inr (Or.inr ⟨hac, had, hbc, hbd⟩)
  · rintro (⟨hac, hbd⟩ | ⟨had, hbc⟩ | ⟨hac, had, hbc, hbd⟩)
    · rw [hac, hbd, negSwapAut]
      exact (frameST_permAut_swap_commute_sgnAut_mul_sgnAut hcd).mul_right (Commute.refl _)
    · rw [had, hbc, frameST_negSwapAut_comm, negSwapAut]
      exact (frameST_permAut_swap_commute_sgnAut_mul_sgnAut (Ne.symm hcd)).mul_right
        (Commute.refl _)
    · have h1 : Commute (permAut (Equiv.swap a b))
          (sgnAut c : MulAut (Fin k → Multiplicative (ZMod 3))) :=
        ((sgnAut_commute_permAut_swap_iff c hab).2 ⟨Ne.symm hac, Ne.symm hbc⟩).symm
      have h2 : Commute (permAut (Equiv.swap a b))
          (sgnAut d : MulAut (Fin k → Multiplicative (ZMod 3))) :=
        ((sgnAut_commute_permAut_swap_iff d hab).2 ⟨Ne.symm had, Ne.symm hbd⟩).symm
      have h3 : Commute (permAut (Equiv.swap a b))
          (permAut (Equiv.swap c d) : MulAut (Fin k → Multiplicative (ZMod 3))) :=
        (permAut_swap_commute_permAut_swap_iff hab hcd).2 (Or.inr (Or.inr ⟨hac, had, hbc, hbd⟩))
      rw [negSwapAut]
      exact (h1.mul_right h2).mul_right h3

theorem negSwapAut_commute_negSwapAut_iff {a b c d : Fin k} (hab : a ≠ b) (hcd : c ≠ d) :
    Commute (negSwapAut a b) (negSwapAut c d) ↔
      (a = c ∧ b = d) ∨ (a = d ∧ b = c) ∨ (a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d) := by
  constructor
  · intro h
    by_cases hac : a = c
    · by_cases hbd : b = d
      · exact Or.inl ⟨hac, hbd⟩
      · exfalso
        rw [← hac] at h
        exact frameST_negSwapAut_not_commute_negSwapAut_shared hab
          (fun hh => hcd (hac.symm.trans hh)) hbd h
    · by_cases had : a = d
      · by_cases hbc : b = c
        · exact Or.inr (Or.inl ⟨had, hbc⟩)
        · exfalso
          rw [← had] at h
          nth_rewrite 2 [frameST_negSwapAut_comm] at h
          exact frameST_negSwapAut_not_commute_negSwapAut_shared hab
            (fun hh => hcd (had.symm.trans hh).symm) hbc h
      · by_cases hbc : b = c
        · exfalso
          rw [← hbc] at h
          nth_rewrite 1 [frameST_negSwapAut_comm] at h
          exact frameST_negSwapAut_not_commute_negSwapAut_shared (Ne.symm hab)
            (fun hh => hcd (hbc.symm.trans hh)) had h
        · by_cases hbd : b = d
          · exfalso
            rw [← hbd] at h
            nth_rewrite 1 [frameST_negSwapAut_comm] at h
            nth_rewrite 2 [frameST_negSwapAut_comm] at h
            exact frameST_negSwapAut_not_commute_negSwapAut_shared (Ne.symm hab) hbc hac h
          · exact Or.inr (Or.inr ⟨hac, had, hbc, hbd⟩)
  · rintro (⟨hac, hbd⟩ | ⟨had, hbc⟩ | ⟨hac, had, hbc, hbd⟩)
    · rw [hac, hbd]
    · rw [had, hbc]
      nth_rewrite 1 [frameST_negSwapAut_comm]
      exact Commute.refl _
    · have h1 : Commute (sgnAut a)
          (negSwapAut c d : MulAut (Fin k → Multiplicative (ZMod 3))) := by
        rw [negSwapAut]
        exact ((sgnAut_commute_sgnAut a c).mul_right (sgnAut_commute_sgnAut a d)).mul_right
          ((sgnAut_commute_permAut_swap_iff a hcd).2 ⟨hac, had⟩)
      have h2 : Commute (sgnAut b)
          (negSwapAut c d : MulAut (Fin k → Multiplicative (ZMod 3))) := by
        rw [negSwapAut]
        exact ((sgnAut_commute_sgnAut b c).mul_right (sgnAut_commute_sgnAut b d)).mul_right
          ((sgnAut_commute_permAut_swap_iff b hcd).2 ⟨hbc, hbd⟩)
      have h3 : Commute (permAut (Equiv.swap a b))
          (negSwapAut c d : MulAut (Fin k → Multiplicative (ZMod 3))) := by
        rw [negSwapAut]
        exact (((sgnAut_commute_permAut_swap_iff c hab).2 ⟨Ne.symm hac, Ne.symm hbc⟩).symm.mul_right
          ((sgnAut_commute_permAut_swap_iff d hab).2 ⟨Ne.symm had, Ne.symm hbd⟩).symm).mul_right
          ((permAut_swap_commute_permAut_swap_iff hab hcd).2
            (Or.inr (Or.inr ⟨hac, had, hbc, hbd⟩)))
      rw [negSwapAut]
      exact (h1.mul_left h2).mul_left h3

end CFSG.StandardType.FrameRoute

end
