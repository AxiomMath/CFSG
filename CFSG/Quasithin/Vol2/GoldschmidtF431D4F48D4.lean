module

public import CFSG.Quasithin.Vol2.GoldschmidtF431D4Lines
public import CFSG.Quasithin.Vol2.GoldschmidtF431D4F48Rigid
public import Certificates.Certificate4236

public section

namespace CFSG.Quasithin.D4Hex

open CFSG.LargeExtraspecial.S63 CFSG.D4Hex CFSG.Monster.B.Co2

section Setting


theorem hexAct_D4 : HexAct act d4H d4N :=
  ⟨fun x => mem_d4H_iff_act x, fun x => mem_d4N_iff_image x⟩

theorem d4_hlines : ∀ x ∈ d4H, ∃ l < 2457, HexOnLine lineTab l 0 ∧
    ∀ p ∈ f48L0, HexOnLine lineTab l (act x p : ℕ) := by
  intro x hx
  have h0 : act x pt0 = pt0 := (mem_d4H_iff_act x).1 hx
  refine ⟨((x • (0 : Fin 2457) : Fin 2457) : ℕ), (x • (0 : Fin 2457)).2, ?_, fun p hp => ?_⟩
  · have hmem : pt0 ∈ lineSet (x • (0 : Fin 2457)) := by
      rw [lineSet_smul, lineSet_zero, Finset.mem_image]
      exact ⟨pt0, by simp [line0], h0⟩
    exact (mem_lineSet_iff _ _).1 hmem
  · have hmem : act x p ∈ lineSet (x • (0 : Fin 2457)) := by
      rw [lineSet_smul, lineSet_zero]
      exact Finset.mem_image_of_mem _ hp
    exact (mem_lineSet_iff _ _).1 hmem

theorem d4_gen_rep : ∀ j < permArrs.size, Rep 819 permArrs[j]! (act (d4GenG j)) :=
  fun _ hj => act_gen (by simpa [permArrs_size] using hj)

theorem f48WordVal_d4GenG (w : List ℕ) : f48WordVal d4GenG w = d4Word w := by
  induction w with
  | nil => simp [f48WordVal, d4Word]
  | cons l w ih => simp only [f48WordVal, d4Word, List.map_cons, List.prod_cons] at ih ⊢; rw [ih]

theorem d4_nn : d4Word f48NWord * d4Word f48NWord = 1 := by
  have := (gens_hyp 3 (by rw [d4Gens_size']; decide)).2
  simpa [f48NWord, d4Word] using this

end Setting

section Rigid


theorem d4_fixed_point {w : Fin 819} (hw : ∀ x ∈ d4B, act x w = w) : w = pt0 :=
  hex_fixed_point hexAct_D4 Certificates.certificate4236.1 d4GenG d4_gen_rep hw

theorem d4_nH : d4Word f48NWord ∈ d4H := by
  rw [← f48WordVal_d4GenG]
  exact hex_n_mem hexAct_D4 Certificates.certificate4236.1 d4GenG d4_gen_rep

theorem d4_qN : d4Word f48QWord ∈ d4N := by
  rw [← f48WordVal_d4GenG]
  exact hex_q_mem hexAct_D4 Certificates.certificate4236.1 d4GenG d4_gen_rep

theorem d4_rigid (π : ↥d4H →* Equiv.Perm (Fin 819))
    (hB : ∀ (x : D) (hx : x ∈ d4H), x ∈ d4N → π ⟨x, hx⟩ = act x)
    (hNear : ∀ (x : D) (hx : x ∈ d4H) (p : Fin 819), lay0[(p : ℕ)]! ≤ 4 →
      π ⟨x, hx⟩ p = act x p)
    (hX : (π ⟨d4Word f48NWord, d4_nH⟩ * act (d4Word f48QWord)) ^ f48Order = 1)
    (y : ↥d4H) : π y = act y := by
  have hnH : f48WordVal d4GenG f48NWord ∈ d4H := by
    rw [f48WordVal_d4GenG]
    exact d4_nH
  have e : (⟨f48WordVal d4GenG f48NWord, hnH⟩ : ↥d4H) = ⟨d4Word f48NWord, d4_nH⟩ :=
    Subtype.ext (f48WordVal_d4GenG _)
  have hX' : (π ⟨f48WordVal d4GenG f48NWord, hnH⟩ *
      act (f48WordVal d4GenG f48QWord)) ^ f48Order = 1 := by
    rw [e, f48WordVal_d4GenG f48QWord]
    exact hX
  have hnn : f48WordVal d4GenG f48NWord * f48WordVal d4GenG f48NWord = 1 := by
    rw [f48WordVal_d4GenG]
    exact d4_nn
  exact hex_rigid_words hexAct_D4 Certificates.certificate4236.1 d4GenG d4_gen_rep π hB
    hNear hnH hnn hX' d4_hlines y

end Rigid

end CFSG.Quasithin.D4Hex
