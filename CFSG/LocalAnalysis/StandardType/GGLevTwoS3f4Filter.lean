module

public import CFSG.LocalAnalysis.StandardType.GGLevTwoS3f4Sem
public import CFSG.LocalAnalysis.StandardType.GGLevTwoS3bDisc
public import Mathlib.Data.Nat.Bitwise

public section

namespace CFSG.StandardType.LevTwo

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open CFSG.LieType.RootSystem
open scoped Matrix

@[expose] def levTwoS3f4_popCount (m : ℕ) : ℕ :=
  (List.range 5).foldl (fun a i => if m.testBit i then a + 1 else a) 0

@[expose] def levTwoS3f4_patSet (m l : ℕ) : Finset (Fin (Tag.rank Tag.F4) → ℤ) :=
  (((List.range 48).filter (fun i => (levTwoS3f4_patMask m l).testBit i)).map
    (fun i => levTwoS3f4_vec (Tag.rank Tag.F4) (levTwoS3f4_roots.getD i []))).toFinset

@[expose] def levTwoS3f4_irreducible (m l : ℕ) : Prop :=
  ∀ α ∈ (levTwoS3f4_patSet m l : Set (Fin (Tag.rank Tag.F4) → ℤ)),
    ∀ β ∈ (levTwoS3f4_patSet m l : Set (Fin (Tag.rank Tag.F4) → ℤ)),
      Relation.ReflTransGen
        (fun a b => b ∈ (levTwoS3f4_patSet m l : Set (Fin (Tag.rank Tag.F4) → ℤ)) ∧
          iform a b ≠ 0) α β

@[expose] def levTwoS3f4_hasThreeInd (m l : ℕ) : Prop :=
  ∃ s : Finset (Fin (Tag.rank Tag.F4) → ℤ),
    (s : Set (Fin (Tag.rank Tag.F4) → ℤ)) ⊆
        (levTwoS3f4_patSet m l : Set (Fin (Tag.rank Tag.F4) → ℤ)) ∧
      LinearIndependent ℚ
        (fun x : s => (fun i => (((x : Fin (Tag.rank Tag.F4) → ℤ) i : ℤ) : ℚ))) ∧
      3 ≤ s.card

@[expose] def levTwoS3f4_survivors : List (ℕ × ℕ) :=
  [(7, 4), (14, 4), (15, 4), (23, 4), (28, 2), (29, 2), (30, 2), (30, 4)]

@[expose] def levTwoS3f4_sideOf (idx : List ℕ) : Finset (Fin (Tag.rank Tag.F4) → ℤ) :=
  (idx.map (fun i => levTwoS3f4_vec (Tag.rank Tag.F4) (levTwoS3f4_roots.getD i []))).toFinset

abbrev levTwoS3f4_sideCert (m l : ℕ)
    (side : Finset (Fin (Tag.rank Tag.F4) → ℤ)) : Prop :=
  side.Nonempty ∧ side ⊆ levTwoS3f4_patSet m l ∧
    (∃ j ∈ levTwoS3f4_patSet m l, j ∉ side) ∧
    (∀ i ∈ side, ∀ j ∈ levTwoS3f4_patSet m l, iform i j ≠ 0 → j ∈ side)

abbrev levTwoS3f4_spanCert (m l : ℕ) (u v : List ℤ)
    (coeffs : List (ℤ × ℤ × ℤ)) : Prop :=
  ∀ r ∈ levTwoS3f4_patSet m l, ∃ abc ∈ coeffs,
    abc.2.2 ≠ 0 ∧
      abc.2.2 • r = abc.1 • levTwoS3f4_vec (Tag.rank Tag.F4) u +
        abc.2.1 • levTwoS3f4_vec (Tag.rank Tag.F4) v

theorem levTwoS3f4_not_irred_of_sideCert {m l : ℕ}
    {side : Finset (Fin (Tag.rank Tag.F4) → ℤ)}
    (h : levTwoS3f4_sideCert m l side) : ¬ levTwoS3f4_irreducible m l := by
  obtain ⟨hne, hsub, hproper, hcl⟩ := h
  exact levTwoS3d_not_irred_of_side (P := (levTwoS3f4_patSet m l : Set _))
    (S := (side : Set _)) (r := fun a b => iform a b ≠ 0)
    (fun x hx => hsub (by simpa using hx))
    (by obtain ⟨x, hx⟩ := hne; exact ⟨x, by simpa using hx⟩)
    (by obtain ⟨y, hy, hys⟩ := hproper; exact ⟨y, by simpa using hy, by simpa using hys⟩)
    (fun a b ha hb hab => hcl a (by simpa using ha) b (by simpa using hb) hab)

theorem levTwoS3f4_noThree_of_spanCert {m l : ℕ} {u v : List ℤ}
    {coeffs : List (ℤ × ℤ × ℤ)} (h : levTwoS3f4_spanCert m l u v coeffs) :
    ¬ levTwoS3f4_hasThreeInd m l := by
  rintro ⟨s, hs, hli, hcard⟩
  have hspan : ∀ x ∈ s,
      (fun i => (((x : Fin (Tag.rank Tag.F4) → ℤ) i : ℤ) : ℚ)) ∈
        Submodule.span ℚ
          ({(fun i => ((levTwoS3f4_vec (Tag.rank Tag.F4) u) i : ℚ)),
            (fun i => ((levTwoS3f4_vec (Tag.rank Tag.F4) v) i : ℚ))} :
              Set (Fin (Tag.rank Tag.F4) → ℚ)) := by
    intro x hx
    have hx' : x ∈ levTwoS3f4_patSet m l := by simpa using hs hx
    obtain ⟨abc, -, hc, heq⟩ := h x hx'
    have hcast : (abc.2.2 : ℚ) •
          (fun i => (((x : Fin (Tag.rank Tag.F4) → ℤ) i : ℤ) : ℚ)) =
        (abc.1 : ℚ) • (fun i => ((levTwoS3f4_vec (Tag.rank Tag.F4) u) i : ℚ)) +
          (abc.2.1 : ℚ) • (fun i => ((levTwoS3f4_vec (Tag.rank Tag.F4) v) i : ℚ)) := by
      funext i
      have hi := congrFun heq i
      simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul] at hi
      have hcast' := congrArg (fun z : ℤ => (z : ℚ)) hi
      push_cast at hcast'
      simpa using hcast'
    have hcQ : (abc.2.2 : ℚ) ≠ 0 := by exact_mod_cast hc
    have hmul : (abc.2.2 : ℚ) •
        (fun i => (((x : Fin (Tag.rank Tag.F4) → ℤ) i : ℤ) : ℚ)) ∈
        Submodule.span ℚ
          ({(fun i => ((levTwoS3f4_vec (Tag.rank Tag.F4) u) i : ℚ)),
            (fun i => ((levTwoS3f4_vec (Tag.rank Tag.F4) v) i : ℚ))} :
              Set (Fin (Tag.rank Tag.F4) → ℚ)) := by
      rw [hcast]
      exact Submodule.add_mem _
        (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
        (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
    have heq2 : (fun i => (((x : Fin (Tag.rank Tag.F4) → ℤ) i : ℤ) : ℚ)) =
        (abc.2.2 : ℚ)⁻¹ • ((abc.2.2 : ℚ) •
          (fun i => (((x : Fin (Tag.rank Tag.F4) → ℤ) i : ℤ) : ℚ))) := by
      rw [smul_smul, inv_mul_cancel₀ hcQ, one_smul]
    rw [heq2]
    exact Submodule.smul_mem _ _ hmul
  have hle := levTwoS3d_card_le_two_of_span s
    (fun i => ((levTwoS3f4_vec (Tag.rank Tag.F4) u) i : ℚ))
    (fun i => ((levTwoS3f4_vec (Tag.rank Tag.F4) v) i : ℚ)) hspan hli
  omega

inductive levTwoS3f4_Cert where
  | side (idx : List ℕ)
  | span (u v : List ℤ) (coeffs : List (ℤ × ℤ × ℤ))
  | survivor

@[expose] def levTwoS3f4_certOK : levTwoS3f4_Cert → ℕ → ℕ → Prop
  | .side idx, m, l => levTwoS3f4_sideCert m l (levTwoS3f4_sideOf idx)
  | .span u v cs, m, l => levTwoS3f4_spanCert m l u v cs
  | .survivor, m, l => (m, l) ∈ levTwoS3f4_survivors

theorem levTwoS3f4_cert_sound {c : levTwoS3f4_Cert} {m l : ℕ}
    (h : levTwoS3f4_certOK c m l) :
    (m, l) ∈ levTwoS3f4_survivors ∨ ¬ levTwoS3f4_irreducible m l ∨
      ¬ levTwoS3f4_hasThreeInd m l := by
  cases c with
  | survivor => exact Or.inl h
  | side idx => exact Or.inr (Or.inl (levTwoS3f4_not_irred_of_sideCert h))
  | span u v cs => exact Or.inr (Or.inr (levTwoS3f4_noThree_of_spanCert h))

@[expose] def levTwoS3f4_cert (m l : ℕ) : levTwoS3f4_Cert :=
  if m = 0 then (if l = 2 then .survivor
      else .survivor)
  else if m = 1 then (if l = 2 then .survivor
      else .survivor)
  else if m = 2 then (if l = 2 then .survivor
      else .survivor)
  else if m = 3 then (if l = 2 then .survivor
      else .survivor)
  else if m = 4 then (if l = 2 then .survivor
      else .survivor)
  else if m = 5 then (if l = 2 then .survivor
      else .survivor)
  else if m = 6 then (if l = 2 then .survivor
      else .survivor)
  else if m = 7 then (if l = 2 then .span [] [] []
      else .survivor)
  else if m = 8 then (if l = 2 then .survivor
      else .survivor)
  else if m = 9 then (if l = 2 then .survivor
      else .survivor)
  else if m = 10 then (if l = 2 then .survivor
      else .survivor)
  else if m = 11 then (if l = 2 then .span [0, 0, -1, 0] [0, 0, -1, 0] [(1, 0, 1), (-1, 0, 1)]
      else .span [-2, -3, -4, -2] [-1, -3, -4, -2] [(1, 0, 1), (0, 1, 1), (1, -1, 1), (-1, 1, 1), (0, -1, 1), (-1, 0, 1)])
  else if m = 12 then (if l = 2 then .survivor
      else .survivor)
  else if m = 13 then (if l = 2 then .side [19, 28]
      else .side [0, 47])
  else if m = 14 then (if l = 2 then .side [12, 35]
      else .survivor)
  else if m = 15 then (if l = 2 then .side [3, 44]
      else .survivor)
  else if m = 16 then (if l = 2 then .survivor
      else .survivor)
  else if m = 17 then (if l = 2 then .survivor
      else .survivor)
  else if m = 18 then (if l = 2 then .survivor
      else .survivor)
  else if m = 19 then (if l = 2 then .span [0, 0, 0, -1] [0, 0, 0, -1] [(1, 0, 1), (-1, 0, 1)]
      else .span [-2, -3, -4, -2] [-1, -3, -4, -2] [(1, 0, 1), (0, 1, 1), (1, -1, 1), (-1, 1, 1), (0, -1, 1), (-1, 0, 1)])
  else if m = 20 then (if l = 2 then .survivor
      else .survivor)
  else if m = 21 then (if l = 2 then .span [0, 0, 0, -1] [0, 0, 0, -1] [(1, 0, 1), (-1, 0, 1)]
      else .side [0, 47])
  else if m = 22 then (if l = 2 then .span [0, 0, 0, -1] [0, 0, 0, -1] [(1, 0, 1), (-1, 0, 1)]
      else .span [-1, -1, 0, 0] [-1, 0, 0, 0] [(1, 0, 1), (0, 1, 1), (1, -1, 1), (-1, 1, 1), (0, -1, 1), (-1, 0, 1)])
  else if m = 23 then (if l = 2 then .span [0, 0, 0, -1] [0, 0, 0, -1] [(1, 0, 1), (-1, 0, 1)]
      else .survivor)
  else if m = 24 then (if l = 2 then .survivor
      else .survivor)
  else if m = 25 then (if l = 2 then .span [0, 0, -1, -1] [0, 0, -1, 0] [(1, 0, 1), (0, 1, 1), (1, -1, 1), (-1, 1, 1), (0, -1, 1), (-1, 0, 1)]
      else .span [-2, -3, -4, -2] [-2, -3, -4, -2] [(1, 0, 1), (-1, 0, 1)])
  else if m = 26 then (if l = 2 then .span [0, 0, -1, -1] [0, 0, -1, 0] [(1, 0, 1), (0, 1, 1), (1, -1, 1), (-1, 1, 1), (0, -1, 1), (-1, 0, 1)]
      else .span [-1, 0, 0, 0] [-1, 0, 0, 0] [(1, 0, 1), (-1, 0, 1)])
  else if m = 27 then (if l = 2 then .span [0, 0, -1, -1] [0, 0, -1, 0] [(1, 0, 1), (0, 1, 1), (1, -1, 1), (-1, 1, 1), (0, -1, 1), (-1, 0, 1)]
      else .span [-2, -3, -4, -2] [-1, -3, -4, -2] [(1, 0, 1), (0, 1, 1), (1, -1, 1), (-1, 1, 1), (0, -1, 1), (-1, 0, 1)])
  else if m = 28 then (if l = 2 then .survivor
      else .side [15, 32])
  else if m = 29 then (if l = 2 then .survivor
      else .side [0, 47])
  else if m = 30 then (if l = 2 then .survivor
      else .survivor)
  else .survivor

@[expose] def levTwoS3f4_certCheckB : levTwoS3f4_Cert → ℕ → ℕ → Bool
  | .side idx, m, l => decide (levTwoS3f4_sideCert m l (levTwoS3f4_sideOf idx))
  | .span u v cs, m, l => decide (levTwoS3f4_spanCert m l u v cs)
  | .survivor, m, l => decide ((m, l) ∈ levTwoS3f4_survivors)

theorem levTwoS3f4_certCheckB_sound {c : levTwoS3f4_Cert} {m l : ℕ}
    (h : levTwoS3f4_certCheckB c m l = true) : levTwoS3f4_certOK c m l := by
  cases c with
  | side idx => simpa [levTwoS3f4_certOK, levTwoS3f4_certCheckB] using of_decide_eq_true h
  | span u v cs => simpa [levTwoS3f4_certOK, levTwoS3f4_certCheckB] using of_decide_eq_true h
  | survivor => simpa [levTwoS3f4_certOK, levTwoS3f4_certCheckB] using of_decide_eq_true h

theorem levTwoS3f4_cert_all_check :
    ((List.range 31).all (fun m => [2, 4].all (fun l =>
        !decide (3 ≤ levTwoS3f4_popCount m) ||
          levTwoS3f4_certCheckB (levTwoS3f4_cert m l) m l))) = true := by
  decide +kernel

theorem levTwoS3f4_cert_all :
    ∀ m ∈ List.range 31, ∀ l ∈ [2, 4], 3 ≤ levTwoS3f4_popCount m →
      levTwoS3f4_certOK (levTwoS3f4_cert m l) m l := by
  intro m hm l hl hp
  have h1 : [2, 4].all (fun l => !decide (3 ≤ levTwoS3f4_popCount m) ||
      levTwoS3f4_certCheckB (levTwoS3f4_cert m l) m l) = true :=
    (List.all_eq_true.mp levTwoS3f4_cert_all_check) m hm
  have h2 : !decide (3 ≤ levTwoS3f4_popCount m) ||
      levTwoS3f4_certCheckB (levTwoS3f4_cert m l) m l = true :=
    (List.all_eq_true.mp h1) l hl
  have hc : levTwoS3f4_certCheckB (levTwoS3f4_cert m l) m l = true := by
    simpa [hp] using h2
  exact levTwoS3f4_certCheckB_sound hc

theorem levTwoS3f4_irred_mask_cases :
    ∀ m < 31, ∀ l ∈ [2, 4], 3 ≤ levTwoS3f4_popCount m →
      levTwoS3f4_irreducible m l → levTwoS3f4_hasThreeInd m l →
        (m, l) ∈ levTwoS3f4_survivors := by
  intro m hm l hl hp hI h3
  have hv := levTwoS3f4_cert_all m (List.mem_range.mpr hm) l hl hp
  rcases levTwoS3f4_cert_sound hv with hmem | hneg
  · exact hmem
  · rcases hneg with h | h
    · exact absurd hI h
    · exact absurd h3 h

end CFSG.StandardType.LevTwo
