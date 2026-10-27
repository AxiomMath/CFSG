module

public import CFSG.LocalAnalysis.StandardType.GGLevTwoS3bE8Link
public import CFSG.LocalAnalysis.StandardType.GGLevTwoS3bDisc

public section

namespace CFSG.StandardType.LevTwo

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open CFSG.HardMathSupport.Timmesfeld.CrossChar
open CFSG.LieType.RootSystem
open scoped Matrix

@[expose] def levTwoS3b_e8_irredSet (S : Set (Fin (Tag.rank Tag.E8) → ℤ)) : Prop :=
  ∀ α ∈ S, ∀ β ∈ S, Relation.ReflTransGen
    (fun a b => b ∈ S ∧ iform (τ := Tag.E8) a b ≠ 0) α β

@[expose] def levTwoS3b_e8_irred (m : ℕ) : Prop :=
  levTwoS3b_e8_irredSet (levTwoS3b_e8_patSet m)

@[expose] def levTwoS3b_e8_survivors : List ℕ :=
  [254, 501, 505, 506, 507, 508, 509, 510]

@[expose] def levTwoS3b_e8_maskPop (m : ℕ) : ℕ :=
  (List.range 9).foldl (fun a i => if m.testBit i then a + 1 else a) 0

@[expose] def levTwoS3b_e8_sideSet (s : ℕ) : Set (Fin (Tag.rank Tag.E8) → ℤ) :=
  {β | ∃ i < 240, s.testBit i = true ∧
    levTwoS3b_vec (Tag.rank Tag.E8) (levTwoS3b_roots.getD i []) = β}

abbrev levTwoS3b_e8_sideOK (m s : ℕ) : Prop :=
  (∀ i : Fin 240, s.testBit i.val = true →
    levTwoS3b_inPat m (levTwoS3b_roots.getD i.val []) = true) ∧
  (∃ i : Fin 240, s.testBit i.val = true) ∧
  (∃ i : Fin 240, levTwoS3b_inPat m (levTwoS3b_roots.getD i.val []) = true ∧
    s.testBit i.val = false) ∧
  (∀ i : Fin 240, s.testBit i.val = true → ∀ j : Fin 240,
    levTwoS3b_inPat m (levTwoS3b_roots.getD j.val []) = true →
    levTwoS3b_ipf (levTwoS3b_roots.getD i.val []) (levTwoS3b_roots.getD j.val []) ≠ 0 →
    s.testBit j.val = true)

theorem levTwoS3b_e8_roots_nodup : levTwoS3b_roots.Nodup := by
  simpa [levTwoS3b_roots] using nodup_artifactRoots Tag.E8

theorem levTwoS3b_e8_getD_inj {i j : ℕ} (hi : i < 240)
    (hj : j < 240) (h : levTwoS3b_roots.getD i [] = levTwoS3b_roots.getD j []) : i = j := by
  have hlen : levTwoS3b_roots.length = 240 := levTwoS3b_e8_roots_length240
  have hi' : i < levTwoS3b_roots.length := by rw [hlen]; exact hi
  have hj' : j < levTwoS3b_roots.length := by rw [hlen]; exact hj
  have h' : levTwoS3b_roots[i] = levTwoS3b_roots[j] := by
    rw [← List.getD_eq_getElem levTwoS3b_roots [] hi',
      ← List.getD_eq_getElem levTwoS3b_roots [] hj']
    exact h
  exact (List.Nodup.getElem_inj levTwoS3b_e8_roots_nodup).mp h'

theorem levTwoS3b_e8_not_irred_of_sideOK {m s : ℕ}
    (h : levTwoS3b_e8_sideOK m s) : ¬ levTwoS3b_e8_irred m := by
  obtain ⟨hsub, hne, hnot, hclosed⟩ := h
  refine levTwoS3d_not_irred_of_side (levTwoS3b_e8_patSet m) (levTwoS3b_e8_sideSet s)
    (fun a b => iform (τ := Tag.E8) a b ≠ 0) ?_ ?_ ?_ ?_
  · rintro a ⟨i, hi, hsi, rfl⟩
    exact ⟨i, hi, rfl, hsub ⟨i, hi⟩ hsi⟩
  · obtain ⟨i, hsi⟩ := hne
    exact ⟨levTwoS3b_vec (Tag.rank Tag.E8) (levTwoS3b_roots.getD i.val []), i.val, i.isLt, hsi, rfl⟩
  · obtain ⟨i, hpi, hsi⟩ := hnot
    refine ⟨levTwoS3b_vec (Tag.rank Tag.E8) (levTwoS3b_roots.getD i.val []),
      ⟨i.val, i.isLt, rfl, hpi⟩, ?_⟩
    rintro ⟨j, hj, hsj, hji⟩
    have hroots : levTwoS3b_roots.getD j [] = levTwoS3b_roots.getD i.val [] :=
      levTwoS3b_e8_vec_injOn (levTwoS3b_e8_roots_length hj) (levTwoS3b_e8_roots_length i.isLt) hji
    have hij : j = i.val := levTwoS3b_e8_getD_inj hj i.isLt hroots
    have hcontra : s.testBit i.val = true := hij ▸ hsj
    rw [hsi] at hcontra
    exact Bool.false_ne_true hcontra
  · rintro a b ⟨i, hi, hsi, rfl⟩ ⟨j, hj, rfl, hpj⟩ hif
    have hif' : levTwoS3b_ipf (levTwoS3b_roots.getD i []) (levTwoS3b_roots.getD j []) ≠ 0 := by
      rw [levTwoS3b_ipf_eq_iform_of_length (levTwoS3b_e8_roots_length hi)
        (levTwoS3b_e8_roots_length hj)]
      exact hif
    exact ⟨j, hj, hclosed ⟨i, hi⟩ hsi ⟨j, hj⟩ hpj hif', rfl⟩

@[expose] def levTwoS3b_e8_cert : ℕ → ℕ
  | 127 => 883423532389192164791648750371459257913741948437809479060803100646309889
  | 191 => 883423532389192164791648750371459257913741948437809479060803100646309889
  | 223 => 883423532389192164791648750371459257913741948437809479060803100646309889
  | 239 => 883423532389192164791648750371459257913741948437809479060803100646309889
  | 247 => 883423532389192164791648750371459257913741948437809479060803100646309889
  | 251 => 883423532389192164791648750371459257913741948437809479060803100646309889
  | 253 => 883423532389192164791648750371459257913741948437809479060803100646309889
  | 255 => 883423532389192164791648750371459257913741948437809479060803100646309889
  | 319 => 1325135298583788247187473125557188888864454916334088027946915241389981699
  | 351 => 10716900716015884225286944423510278144
  | 367 => 2787593149816644805342021841431419364048896
  | 375 => 5846006549323611672814739481980859530452377010176
  | 379 => 1325135298583788247187473125557188888864454916334088027946915241389981699
  | 381 => 1325135298583788247187473125557188888864454916334088027946915241389981699
  | 382 => 1993841993677373809355710590420516864
  | 383 => 1325135298583788247187473125557188888864454916334088027946915241389981699
  | 415 => 1545991181681086288385385313150053711816718876572379087473886025838755847
  | 431 => 2787593149816644805342021841431419364048896
  | 439 => 5846006549323611672814739481980859530452377010176
  | 443 => 1545991181681086288385385313150053711816718876572379087473886025838755847
  | 445 => 1545991181681086288385385313150053711816718876572379087473886025838755847
  | 446 => 10467670466806212499117480599707713536
  | 447 => 1545991181681086288385385313150053711816718876572379087473886025838755847
  | 463 => 2787593149816644805342021841431419364048896
  | 471 => 5846006549323611672814739481980859530452377010176
  | 475 => 40922045977294840754488021126628754476825227296768
  | 477 => 186900770596739233976643003567862447456911360
  | 478 => 85049822542800476555329529872625172480
  | 479 => 1656419123229735308984341406946486193638088696121369328568535686337003535
  | 487 => 5846006549323611672814739481980859530452377010176
  | 491 => 17538019691526978004606751146232607588827743125504
  | 493 => 2787593149816644805342021841431419364048896
  | 494 => 2787593149816644805342021841431419364048896
  | 495 => 2787593149816644805342021841431419364048896
  | 499 => 5846006549323611672814739481980859530452377010176
  | 502 => 5846006549323611672814739481980859530452377010176
  | 503 => 5846006549323611672814739481980859530452377010176
  | _ => 0

@[expose] def levTwoS3b_e8_refuteOK (m : ℕ) : Bool :=
  if m ∈ levTwoS3b_e8_survivors then true
  else if levTwoS3b_e8_maskPop m < 7 then true
  else decide (levTwoS3b_e8_sideOK m (levTwoS3b_e8_cert m))

theorem levTwoS3b_e8_refuteOK_chunk_0 :
    (List.range 64).all (fun i => levTwoS3b_e8_refuteOK i) = true := by
  decide +kernel

theorem levTwoS3b_e8_refuteOK_chunk_1 :
    (List.range 64).all (fun i => levTwoS3b_e8_refuteOK (64 + i)) = true := by
  decide +kernel

theorem levTwoS3b_e8_refuteOK_chunk_2 :
    (List.range 64).all (fun i => levTwoS3b_e8_refuteOK (128 + i)) = true := by
  decide +kernel

theorem levTwoS3b_e8_refuteOK_chunk_3 :
    (List.range 64).all (fun i => levTwoS3b_e8_refuteOK (192 + i)) = true := by
  decide +kernel

theorem levTwoS3b_e8_refuteOK_chunk_4 :
    (List.range 64).all (fun i => levTwoS3b_e8_refuteOK (256 + i)) = true := by
  decide +kernel

theorem levTwoS3b_e8_refuteOK_chunk_5 :
    (List.range 64).all (fun i => levTwoS3b_e8_refuteOK (320 + i)) = true := by
  decide +kernel

theorem levTwoS3b_e8_refuteOK_chunk_6 :
    (List.range 64).all (fun i => levTwoS3b_e8_refuteOK (384 + i)) = true := by
  decide +kernel

theorem levTwoS3b_e8_refuteOK_chunk_7 :
    (List.range 63).all (fun i => levTwoS3b_e8_refuteOK (448 + i)) = true := by
  decide +kernel

theorem levTwoS3b_e8_refuteOK_all : ∀ m < 511, levTwoS3b_e8_refuteOK m = true := by
  intro m hm
  have h0 := List.all_eq_true.mp levTwoS3b_e8_refuteOK_chunk_0
  have h1 := List.all_eq_true.mp levTwoS3b_e8_refuteOK_chunk_1
  have h2 := List.all_eq_true.mp levTwoS3b_e8_refuteOK_chunk_2
  have h3 := List.all_eq_true.mp levTwoS3b_e8_refuteOK_chunk_3
  have h4 := List.all_eq_true.mp levTwoS3b_e8_refuteOK_chunk_4
  have h5 := List.all_eq_true.mp levTwoS3b_e8_refuteOK_chunk_5
  have h6 := List.all_eq_true.mp levTwoS3b_e8_refuteOK_chunk_6
  have h7 := List.all_eq_true.mp levTwoS3b_e8_refuteOK_chunk_7
  by_cases hm0 : m < 64
  · exact h0 m (List.mem_range.mpr hm0)
  · by_cases hm1 : m < 128
    · have he : 64 + (m - 64) = m := by omega
      rw [← he]
      exact h1 (m - 64) (List.mem_range.mpr (by omega))
    · by_cases hm2 : m < 192
      · have he : 128 + (m - 128) = m := by omega
        rw [← he]
        exact h2 (m - 128) (List.mem_range.mpr (by omega))
      · by_cases hm3 : m < 256
        · have he : 192 + (m - 192) = m := by omega
          rw [← he]
          exact h3 (m - 192) (List.mem_range.mpr (by omega))
        · by_cases hm4 : m < 320
          · have he : 256 + (m - 256) = m := by omega
            rw [← he]
            exact h4 (m - 256) (List.mem_range.mpr (by omega))
          · by_cases hm5 : m < 384
            · have he : 320 + (m - 320) = m := by omega
              rw [← he]
              exact h5 (m - 320) (List.mem_range.mpr (by omega))
            · by_cases hm6 : m < 448
              · have he : 384 + (m - 384) = m := by omega
                rw [← he]
                exact h6 (m - 384) (List.mem_range.mpr (by omega))
              · by_cases hm7 : m < 511
                · have he : 448 + (m - 448) = m := by omega
                  rw [← he]
                  exact h7 (m - 448) (List.mem_range.mpr (by omega))
                · omega
theorem levTwoS3b_e8_refuteOK_sound {m : ℕ}
    (h : levTwoS3b_e8_refuteOK m = true) :
    m ∈ levTwoS3b_e8_survivors ∨ levTwoS3b_e8_maskPop m < 7 ∨ ¬ levTwoS3b_e8_irred m := by
  by_cases hmem : m ∈ levTwoS3b_e8_survivors
  · exact Or.inl hmem
  · by_cases hlt : levTwoS3b_e8_maskPop m < 7
    · exact Or.inr (Or.inl hlt)
    · refine Or.inr (Or.inr ?_)
      rw [levTwoS3b_e8_refuteOK, if_neg hmem, if_neg hlt] at h
      exact levTwoS3b_e8_not_irred_of_sideOK (of_decide_eq_true h)

end CFSG.StandardType.LevTwo
