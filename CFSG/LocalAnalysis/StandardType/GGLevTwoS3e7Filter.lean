module

public import CFSG.LocalAnalysis.StandardType.GGLevTwoS3e7Sem
public import CFSG.LocalAnalysis.StandardType.GGLevTwoS3bDisc

public section

namespace CFSG.StandardType.LevTwo

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open CFSG.LocalAnalysis.GLTheoremB.MovingAround.InputsL33d
open CFSG.LieType.RootSystem
open scoped Matrix

@[expose] def levTwoS3e7_patSet (m : ℕ) : Set (Fin (Tag.rank Tag.E7) → ℤ) :=
  {β | ∃ i < 126, levTwoS3e7_vec (Tag.rank Tag.E7) (levTwoS3e7_roots.getD i []) = β ∧
    (levTwoS3e7_patMask m).testBit i = true}

@[expose] def levTwoS3e7_irred (m : ℕ) : Prop :=
  ∀ α ∈ levTwoS3e7_patSet m, ∀ β ∈ levTwoS3e7_patSet m,
    Relation.ReflTransGen
      (fun a b => b ∈ levTwoS3e7_patSet m ∧ iform (τ := Tag.E7) a b ≠ 0) α β

@[expose] def levTwoS3e7_survivors : List ℕ :=
  [63, 123, 126, 127, 250, 251, 252, 254]

@[expose] def levTwoS3e7_maskPop (m : ℕ) : ℕ :=
  (List.range 8).foldl (fun a i => if m.testBit i then a + 1 else a) 0

@[expose] def levTwoS3e7_sideSet (s : ℕ) : Set (Fin (Tag.rank Tag.E7) → ℤ) :=
  {β | ∃ i < 126, s.testBit i = true ∧
    levTwoS3e7_vec (Tag.rank Tag.E7) (levTwoS3e7_roots.getD i []) = β}

abbrev levTwoS3e7_sideOK (m s : ℕ) : Prop :=
  (∀ i : Fin 126, s.testBit i.val = true → (levTwoS3e7_patMask m).testBit i.val = true) ∧
  (∃ i : Fin 126, s.testBit i.val = true) ∧
  (∃ i : Fin 126, (levTwoS3e7_patMask m).testBit i.val = true ∧ s.testBit i.val = false) ∧
  (∀ i : Fin 126, s.testBit i.val = true → ∀ j : Fin 126,
    (levTwoS3e7_patMask m).testBit j.val = true →
    levTwoS3e7_ipf (levTwoS3e7_roots.getD i.val []) (levTwoS3e7_roots.getD j.val []) ≠ 0 →
    s.testBit j.val = true)

theorem levTwoS3e7_roots_nodup : levTwoS3e7_roots.Nodup :=
  levTwoS3e7_keys_nodup.of_map levTwoS3e7_key

theorem levTwoS3e7_getD_inj {i j : ℕ} (hi : i < 126) (hj : j < 126)
    (h : levTwoS3e7_roots.getD i [] = levTwoS3e7_roots.getD j []) : i = j := by
  have hlen : levTwoS3e7_roots.length = 126 := levTwoS3e7_roots_length
  have hi' : i < levTwoS3e7_roots.length := by omega
  have hj' : j < levTwoS3e7_roots.length := by omega
  have h' : levTwoS3e7_roots[i] = levTwoS3e7_roots[j] := by
    rw [← List.getD_eq_getElem _ _ hi', ← List.getD_eq_getElem _ _ hj']
    exact h
  exact (List.Nodup.getElem_inj levTwoS3e7_roots_nodup).mp h'

theorem levTwoS3e7_roots_all_length :
    levTwoS3e7_roots.all (fun v => decide (v.length = Tag.rank Tag.E7)) = true := by
  decide +kernel

theorem levTwoS3e7_roots_getD_length {i : ℕ} (hi : i < 126) :
    (levTwoS3e7_roots.getD i []).length = Tag.rank Tag.E7 := by
  have hlen : levTwoS3e7_roots.length = 126 := levTwoS3e7_roots_length
  have hmem : levTwoS3e7_roots.getD i [] ∈ levTwoS3e7_roots := by
    rw [List.getD_eq_getElem _ _ (by omega)]
    exact List.getElem_mem (by omega)
  have hall := List.all_eq_true.mp levTwoS3e7_roots_all_length _ hmem
  simpa using hall

theorem levTwoS3e7_vec_injOn {v w : List ℤ} (hv : v.length = Tag.rank Tag.E7)
    (hw : w.length = Tag.rank Tag.E7)
    (h : levTwoS3e7_vec (Tag.rank Tag.E7) v = levTwoS3e7_vec (Tag.rank Tag.E7) w) : v = w := by
  have hv' : List.ofFn (levTwoS3e7_vec (Tag.rank Tag.E7) v) = v := levTwoS3e7_ofFn_vec _ hv
  have hw' : List.ofFn (levTwoS3e7_vec (Tag.rank Tag.E7) w) = w := levTwoS3e7_ofFn_vec _ hw
  rw [← hv', ← hw', h]

theorem levTwoS3e7_not_irred_of_sideOK {m s : ℕ} (h : levTwoS3e7_sideOK m s) :
    ¬ levTwoS3e7_irred m := by
  obtain ⟨hsub, hne, hnot, hclosed⟩ := h
  refine levTwoS3d_not_irred_of_side (levTwoS3e7_patSet m) (levTwoS3e7_sideSet s)
    (fun a b => iform (τ := Tag.E7) a b ≠ 0) ?_ ?_ ?_ ?_
  · rintro a ⟨i, hi, hsi, rfl⟩
    exact ⟨i, hi, rfl, hsub ⟨i, hi⟩ hsi⟩
  · obtain ⟨i, hsi⟩ := hne
    exact ⟨levTwoS3e7_vec (Tag.rank Tag.E7) (levTwoS3e7_roots.getD i.val []),
      i.val, i.isLt, hsi, rfl⟩
  · obtain ⟨i, hpi, hsi⟩ := hnot
    refine ⟨levTwoS3e7_vec (Tag.rank Tag.E7) (levTwoS3e7_roots.getD i.val []),
      ⟨i.val, i.isLt, rfl, hpi⟩, ?_⟩
    rintro ⟨j, hj, hsj, hji⟩
    have hroots : levTwoS3e7_roots.getD j [] = levTwoS3e7_roots.getD i.val [] :=
      levTwoS3e7_vec_injOn (levTwoS3e7_roots_getD_length hj) (levTwoS3e7_roots_getD_length i.isLt) hji
    have hij : j = i.val := levTwoS3e7_getD_inj hj i.isLt hroots
    have hcontra : s.testBit i.val = true := hij ▸ hsj
    rw [hsi] at hcontra
    exact Bool.false_ne_true hcontra
  · rintro a b ⟨i, hi, hsi, rfl⟩ ⟨j, hj, rfl, hpj⟩ hif
    have hif' : levTwoS3e7_ipf (levTwoS3e7_roots.getD i [])
        (levTwoS3e7_roots.getD j []) ≠ 0 := by
      rw [levTwoS3e7_ipf_eq_iform_of_length (levTwoS3e7_roots_getD_length hi)
        (levTwoS3e7_roots_getD_length hj)]
      exact hif
    exact ⟨j, hj, hclosed ⟨i, hi⟩ hsi ⟨j, hj⟩ hpj hif', rfl⟩

@[expose] def levTwoS3e7_cert : ℕ → ℕ
  | 95 => 80085987449201730682045735611790262415
  | 111 => 74436767793665859270199791318638526471
  | 119 => 63802943807579482213665781096944500739
  | 125 => 42535295865117307932921825928971026433
  | 159 => 80085987449201730682045735611790262415
  | 175 => 74436767793665859270199791318638526471
  | 183 => 63802943807579482213665781096944500739
  | 187 => 82412135887217656792779266722025701407
  | 189 => 42535295865117307932921825928971026433
  | 190 => 661228526764039142111913634234368
  | 191 => 82932351176550449505899503548144748959
  | 207 => 74436767793665859270199791318638526471
  | 215 => 63802943807579482213665781096944500739
  | 219 => 79753679816419623498783239588743741455
  | 221 => 42535295865117307932921825928971026433
  | 222 => 703160549339591360229899501568
  | 223 => 80085987449201730682045735611790262415
  | 231 => 63802943807579482213665781096944500739
  | 235 => 74436767793665859270199791318638526471
  | 237 => 42535295865117307932921825928971026433
  | 238 => 29710570387586595942939230208
  | 239 => 74436767793665859270199791318638526471
  | 243 => 63802943807579482213665781096944500739
  | 245 => 42535295865117307932921825928971026433
  | 246 => 9903520314283042203487961088
  | 247 => 63802943807579482213665781096944500739
  | 249 => 42535295865117307932921825928971026433
  | 253 => 42535295865117307932921825928971026433
  | _ => 0

@[expose] def levTwoS3e7_refuteOK (m : ℕ) : Bool :=
  if m ∈ levTwoS3e7_survivors then true
  else if levTwoS3e7_maskPop m < 6 then true
  else decide (levTwoS3e7_sideOK m (levTwoS3e7_cert m))

theorem levTwoS3e7_refuteOK_all : (List.range 255).all levTwoS3e7_refuteOK = true := by
  decide +kernel

theorem levTwoS3e7_refuteOK_sound {m : ℕ} (h : levTwoS3e7_refuteOK m = true) :
    m ∈ levTwoS3e7_survivors ∨ levTwoS3e7_maskPop m < 6 ∨ ¬ levTwoS3e7_irred m := by
  by_cases hmem : m ∈ levTwoS3e7_survivors
  · exact Or.inl hmem
  · by_cases hlt : levTwoS3e7_maskPop m < 6
    · exact Or.inr (Or.inl hlt)
    · refine Or.inr (Or.inr ?_)
      rw [levTwoS3e7_refuteOK, if_neg hmem, if_neg hlt] at h
      exact levTwoS3e7_not_irred_of_sideOK (of_decide_eq_true h)

theorem levTwoS3e7_irred_mask_cases (m : ℕ) (hm : m < 255)
    (h6 : 6 ≤ levTwoS3e7_maskPop m) (hirr : levTwoS3e7_irred m) :
    m ∈ levTwoS3e7_survivors := by
  have h := List.all_eq_true.mp levTwoS3e7_refuteOK_all m (List.mem_range.mpr hm)
  rcases levTwoS3e7_refuteOK_sound h with hmem | hlt | hni
  · exact hmem
  · omega
  · exact absurd hirr hni

end CFSG.StandardType.LevTwo
