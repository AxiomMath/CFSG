module

public import CFSG.Quasithin.Vol2.GoldschmidtF431D4F48D4
public import CFSG.Quasithin.EmptyFaithful.S1421Inputs
public import CFSG.Quasithin.Vol2.GoldschmidtF431D4AutLn

public section

namespace CFSG.Quasithin.D4Hex

open CFSG.LargeExtraspecial.S63 CFSG.Quasithin CFSG.D4Hex CFSG.Monster.B.Co2

section Rigid


theorem autLn_zero_iff (α : MulAut D) : autLn α 0 = 0 ↔ f48L0.image (autPt α) = f48L0 := by
  have h : f48L0 = line0 := rfl
  rw [h, ← lineSet_zero]
  constructor
  · intro h0
    rw [← lineSet_autLn, h0]
  · intro h0
    apply lineSet_injective
    rw [lineSet_autLn, h0]

theorem hexAct_D3 (hH : ∀ α : MulAut D, α ∈ autStab d4H ↔ autPt α pt0 = pt0)
    (hN : ∀ α : MulAut D, α ∈ autStab d4N ↔ autLn α 0 = 0) :
    HexAct autPt (autStab d4H) (autStab d4N) :=
  ⟨fun α => hH α, fun α => (hN α).trans (autLn_zero_iff α)⟩

@[expose] noncomputable def d3Gen (j : ℕ) : MulAut D := MulAut.conj (d4GenG j)

theorem d3_gen_rep : ∀ j < permArrs.size, Rep 819 permArrs[j]! (autPt (d3Gen j)) :=
  fun j hj => by
    rw [d3Gen, autPt_conj]
    exact d4_gen_rep j hj

theorem f48WordVal_d3Gen (w : List ℕ) :
    f48WordVal d3Gen w = MulAut.conj (d4Word w) := by
  rw [← f48WordVal_d4GenG]
  exact (map_f48WordVal (MulAut.conj : D →* MulAut D) d4GenG w).symm

theorem d3_hlines (hH : ∀ α : MulAut D, α ∈ autStab d4H ↔ autPt α pt0 = pt0) :
    ∀ x ∈ autStab d4H, ∃ l < 2457, HexOnLine lineTab l 0 ∧
      ∀ p ∈ f48L0, HexOnLine lineTab l (autPt x p : ℕ) := by
  intro x hx
  have h0 : autPt x pt0 = pt0 := (hH x).1 hx
  refine ⟨((autLn x 0 : Fin 2457) : ℕ), (autLn x 0).2, ?_, fun p hp => ?_⟩
  · have hmem : pt0 ∈ lineSet (autLn x 0) := by
      rw [lineSet_autLn, lineSet_zero, Finset.mem_image]
      exact ⟨pt0, by simp [line0], h0⟩
    exact (mem_lineSet_iff _ _).1 hmem
  · have hmem : autPt x p ∈ lineSet (autLn x 0) := by
      rw [lineSet_autLn, lineSet_zero]
      exact Finset.mem_image_of_mem _ hp
    exact (mem_lineSet_iff _ _).1 hmem

theorem d3_nH (hH : ∀ α : MulAut D, α ∈ autStab d4H ↔ autPt α pt0 = pt0) :
    MulAut.conj (d4Word f48NWord) ∈ autStab d4H := by
  rw [hH, autPt_conj]
  exact (mem_d4H_iff_act _).1 d4_nH

theorem d3_rigid (hH : ∀ α : MulAut D, α ∈ autStab d4H ↔ autPt α pt0 = pt0)
    (hN : ∀ α : MulAut D, α ∈ autStab d4N ↔ autLn α 0 = 0)
    (π : ↥(autStab d4H) →* Equiv.Perm (Fin 819))
    (hB : ∀ (x : MulAut D) (hx : x ∈ autStab d4H), x ∈ autStab d4N → π ⟨x, hx⟩ = autPt x)
    (hNear : ∀ (x : MulAut D) (hx : x ∈ autStab d4H) (p : Fin 819), lay0[(p : ℕ)]! ≤ 4 →
      π ⟨x, hx⟩ p = autPt x p)
    (hX : (π ⟨MulAut.conj (d4Word f48NWord), d3_nH hH⟩ *
      autPt (MulAut.conj (d4Word f48QWord))) ^ f48Order3 = 1)
    (y : ↥(autStab d4H)) : π y = autPt y := by
  have hnH : f48WordVal d3Gen f48NWord ∈ autStab d4H := by
    rw [f48WordVal_d3Gen]
    exact d3_nH hH
  have hnn : f48WordVal d3Gen f48NWord * f48WordVal d3Gen f48NWord = 1 := by
    rw [f48WordVal_d3Gen, ← map_mul, d4_nn, map_one]
  have e : (⟨f48WordVal d3Gen f48NWord, hnH⟩ : ↥(autStab d4H)) =
      ⟨MulAut.conj (d4Word f48NWord), d3_nH hH⟩ := Subtype.ext (f48WordVal_d3Gen _)
  have hX' : (π ⟨f48WordVal d3Gen f48NWord, hnH⟩ *
      autPt (f48WordVal d3Gen f48QWord)) ^ f48Order3 = 1 := by
    rw [e, f48WordVal_d3Gen f48QWord]
    exact hX
  exact hex_rigid_words (hexAct_D3 hH hN) Certificates.certificate4236.2 d3Gen
    d3_gen_rep π hB hNear hnH hnn hX' (d3_hlines hH) y

end Rigid

end CFSG.Quasithin.D4Hex
