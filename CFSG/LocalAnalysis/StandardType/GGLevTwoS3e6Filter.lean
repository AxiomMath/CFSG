module

public import CFSG.LocalAnalysis.StandardType.GGLevTwoS3e6Sem
public import CFSG.LocalAnalysis.StandardType.GGLevTwoS3bDisc

public section

namespace CFSG.StandardType.LevTwo

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open CFSG.LocalAnalysis.GLTheoremB.MovingAround.InputsL33d
open CFSG.LieType.RootSystem
open scoped Matrix

@[expose] def levTwoS3e6_patSet (m : ℕ) : Set (Fin (Tag.rank Tag.E6) → ℤ) :=
  {β | ∃ i < 72, levTwoS3e6_vec (Tag.rank Tag.E6) (levTwoS3e6_roots.getD i []) = β ∧
    (levTwoS3e6_patMask m).testBit i = true}

@[expose] def levTwoS3e6_irred (m : ℕ) : Prop :=
  ∀ α ∈ levTwoS3e6_patSet m, ∀ β ∈ levTwoS3e6_patSet m,
    Relation.ReflTransGen
      (fun a b => b ∈ levTwoS3e6_patSet m ∧ iform (τ := Tag.E6) a b ≠ 0) α β

@[expose] def levTwoS3e6_survivors : List ℕ :=
  [29, 30, 31, 53, 58, 60, 61, 62, 63, 116, 117, 120, 122, 124, 125, 126]

@[expose] def levTwoS3e6_maskPop (m : ℕ) : ℕ :=
  (List.range 7).foldl (fun a i => if m.testBit i then a + 1 else a) 0

@[expose] def levTwoS3e6_sideSet (s : ℕ) : Set (Fin (Tag.rank Tag.E6) → ℤ) :=
  {β | ∃ i < 72, s.testBit i = true ∧
    levTwoS3e6_vec (Tag.rank Tag.E6) (levTwoS3e6_roots.getD i []) = β}

abbrev levTwoS3e6_sideOK (m s : ℕ) : Prop :=
  (∀ i : Fin 72, s.testBit i.val = true → (levTwoS3e6_patMask m).testBit i.val = true) ∧
  (∃ i : Fin 72, s.testBit i.val = true) ∧
  (∃ i : Fin 72, (levTwoS3e6_patMask m).testBit i.val = true ∧ s.testBit i.val = false) ∧
  (∀ i : Fin 72, s.testBit i.val = true → ∀ j : Fin 72,
    (levTwoS3e6_patMask m).testBit j.val = true →
    levTwoS3e6_ipf (levTwoS3e6_roots.getD i.val []) (levTwoS3e6_roots.getD j.val []) ≠ 0 →
    s.testBit j.val = true)

theorem levTwoS3e6_roots_nodup : levTwoS3e6_roots.Nodup :=
  levTwoS3e6_keys_nodup.of_map levTwoS3e6_key

theorem levTwoS3e6_getD_inj {i j : ℕ} (hi : i < 72) (hj : j < 72)
    (h : levTwoS3e6_roots.getD i [] = levTwoS3e6_roots.getD j []) : i = j := by
  have hlen : levTwoS3e6_roots.length = 72 := by decide +kernel
  have hi' : i < levTwoS3e6_roots.length := by omega
  have hj' : j < levTwoS3e6_roots.length := by omega
  have h' : levTwoS3e6_roots[i] = levTwoS3e6_roots[j] := by
    rw [← List.getD_eq_getElem _ _ hi', ← List.getD_eq_getElem _ _ hj']
    exact h
  exact (List.Nodup.getElem_inj levTwoS3e6_roots_nodup).mp h'

theorem levTwoS3e6_roots_all_length :
    levTwoS3e6_roots.all (fun v => decide (v.length = 6)) = true := by
  decide +kernel

theorem levTwoS3e6_roots_length6 {i : ℕ} (hi : i < 72) :
    (levTwoS3e6_roots.getD i []).length = 6 := by
  have hlen : levTwoS3e6_roots.length = 72 := by decide +kernel
  have hmem : levTwoS3e6_roots.getD i [] ∈ levTwoS3e6_roots := by
    rw [List.getD_eq_getElem _ _ (by omega)]
    exact List.getElem_mem (by omega)
  have hall := List.all_eq_true.mp levTwoS3e6_roots_all_length _ hmem
  simpa using hall

theorem levTwoS3e6_roots_length {i : ℕ} (hi : i < 72) :
    (levTwoS3e6_roots.getD i []).length = Tag.rank Tag.E6 :=
  levTwoS3e6_roots_length6 hi

theorem levTwoS3e6_vec_injOn {v w : List ℤ} (hv : v.length = Tag.rank Tag.E6)
    (hw : w.length = Tag.rank Tag.E6)
    (h : levTwoS3e6_vec (Tag.rank Tag.E6) v = levTwoS3e6_vec (Tag.rank Tag.E6) w) : v = w := by
  have hv' : List.ofFn (levTwoS3e6_vec (Tag.rank Tag.E6) v) = v :=
    levTwoS3e6_ofFn_vec (Tag.rank Tag.E6) hv
  have hw' : List.ofFn (levTwoS3e6_vec (Tag.rank Tag.E6) w) = w :=
    levTwoS3e6_ofFn_vec (Tag.rank Tag.E6) hw
  rw [← hv', ← hw', h]

theorem levTwoS3e6_not_irred_of_sideOK {m s : ℕ} (h : levTwoS3e6_sideOK m s) :
    ¬ levTwoS3e6_irred m := by
  obtain ⟨hsub, hne, hnot, hclosed⟩ := h
  refine levTwoS3d_not_irred_of_side (levTwoS3e6_patSet m) (levTwoS3e6_sideSet s)
    (fun a b => iform (τ := Tag.E6) a b ≠ 0) ?_ ?_ ?_ ?_
  · rintro a ⟨i, hi, hsi, rfl⟩
    exact ⟨i, hi, rfl, hsub ⟨i, hi⟩ hsi⟩
  · obtain ⟨i, hsi⟩ := hne
    exact ⟨levTwoS3e6_vec (Tag.rank Tag.E6) (levTwoS3e6_roots.getD i.val []), i.val, i.isLt, hsi, rfl⟩
  · obtain ⟨i, hpi, hsi⟩ := hnot
    refine ⟨levTwoS3e6_vec (Tag.rank Tag.E6) (levTwoS3e6_roots.getD i.val []), ⟨i.val, i.isLt, rfl, hpi⟩, ?_⟩
    rintro ⟨j, hj, hsj, hji⟩
    have hroots : levTwoS3e6_roots.getD j [] = levTwoS3e6_roots.getD i.val [] :=
      levTwoS3e6_vec_injOn (levTwoS3e6_roots_length hj) (levTwoS3e6_roots_length i.isLt) hji
    have hij : j = i.val := levTwoS3e6_getD_inj hj i.isLt hroots
    have hcontra : s.testBit i.val = true := hij ▸ hsj
    rw [hsi] at hcontra
    exact Bool.false_ne_true hcontra
  · rintro a b ⟨i, hi, hsi, rfl⟩ ⟨j, hj, rfl, hpj⟩ hif
    have hif' : levTwoS3e6_ipf (levTwoS3e6_roots.getD i [])
        (levTwoS3e6_roots.getD j []) ≠ 0 := by
      rw [levTwoS3e6_ipf_eq_iform_of_length (levTwoS3e6_roots_length hi)
        (levTwoS3e6_roots_length hj)]
      exact hif
    exact ⟨j, hj, hclosed ⟨i, hi⟩ hsi ⟨j, hj⟩ hpj hif', rfl⟩

@[expose] def levTwoS3e6_cert : ℕ → ℕ
  | 15 => 3541774932521011642371
  | 23 => 4132070884171273207815
  | 27 => 2361183241434822606849
  | 39 => 3541774932521011642371
  | 43 => 2361183241434822606849
  | 45 => 3541774932521011642371
  | 46 => 216177180697214976
  | 47 => 3541774932521011642371
  | 51 => 2361183241434822606849
  | 54 => 72057594037960704
  | 55 => 4427219072081889067023
  | 57 => 2361183241434822606849
  | 59 => 2361183241434822606849
  | 71 => 3541774932521011642371
  | 75 => 2361183241434822606849
  | 77 => 3541774932521011642371
  | 78 => 216177180697214976
  | 79 => 3541774932521011642371
  | 83 => 2361183241434822606849
  | 85 => 4132070884171273207815
  | 86 => 72057594037960704
  | 87 => 4132070884171273207815
  | 89 => 2361183241434822606849
  | 90 => 504416907261173760
  | 91 => 2361183241434822606849
  | 92 => 1350755187425280
  | 93 => 4205858999560965193767
  | 94 => 2811596922666673152
  | 95 => 4208705274525463471143
  | 99 => 2361183241434822606849
  | 101 => 3541774932521011642371
  | 102 => 72057594037960704
  | 103 => 3541774932521011642371
  | 105 => 2361183241434822606849
  | 106 => 216177180697214976
  | 107 => 2361183241434822606849
  | 108 => 70368777732096
  | 109 => 3541774932521011642371
  | 110 => 216177180697214976
  | 111 => 3541774932521011642371
  | 113 => 2361183241434822606849
  | 114 => 72057594037960704
  | 115 => 2361183241434822606849
  | 118 => 72057594037960704
  | 119 => 4574793590208167149599
  | 121 => 2361183241434822606849
  | 123 => 2361183241434822606849
  | _ => 0

@[expose] def levTwoS3e6_refuteOK (m : ℕ) : Bool :=
  if m ∈ levTwoS3e6_survivors then true
  else if levTwoS3e6_maskPop m < 4 then true
  else decide (levTwoS3e6_sideOK m (levTwoS3e6_cert m))

theorem levTwoS3e6_refuteOK_all : (List.range 127).all levTwoS3e6_refuteOK = true := by
  decide +kernel

theorem levTwoS3e6_refuteOK_sound {m : ℕ} (h : levTwoS3e6_refuteOK m = true) :
    m ∈ levTwoS3e6_survivors ∨ levTwoS3e6_maskPop m < 4 ∨ ¬ levTwoS3e6_irred m := by
  by_cases hmem : m ∈ levTwoS3e6_survivors
  · exact Or.inl hmem
  · by_cases hlt : levTwoS3e6_maskPop m < 4
    · exact Or.inr (Or.inl hlt)
    · refine Or.inr (Or.inr ?_)
      rw [levTwoS3e6_refuteOK, if_neg hmem, if_neg hlt] at h
      exact levTwoS3e6_not_irred_of_sideOK (of_decide_eq_true h)

theorem levTwoS3e6_irred_mask_cases (m : ℕ) (hm : m < 127)
    (h4 : 4 ≤ levTwoS3e6_maskPop m) (hirr : levTwoS3e6_irred m) :
    m ∈ levTwoS3e6_survivors := by
  have h := List.all_eq_true.mp levTwoS3e6_refuteOK_all m (List.mem_range.mpr hm)
  rcases levTwoS3e6_refuteOK_sound h with hmem | hlt | hni
  · exact hmem
  · omega
  · exact absurd hirr hni

end CFSG.StandardType.LevTwo
