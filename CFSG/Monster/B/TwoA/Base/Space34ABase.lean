
module

public import CFSG.Monster.B.TwoA.Base.PairSpace
public import CFSG.Monster.B.TwoA.Base.Space34AInputs
public import CFSG.Monster.B.TwoA.Base.SevenPairA

@[expose] public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Lifts CFSG.Monster.Visible
  CFSG.Monster.VisQuot CFSG.Monster.ScalarKernel CFSG.Monster.SpinLattice
  CFSG.Monster.B.Short CFSG.Monster.B.Co2 CFSG.Monster.VisCert CFSG.Sporadic.Mathieu

private theorem zmod2_cases : ∀ t : ZMod 2, t = 0 ∨ t = 1 := by decide

theorem offPair7 (i : Fin 7) : OffPair (pa7 i) (pb7 i) :=
  ⟨by fin_cases i <;> decide, by fin_cases i <;> decide, by fin_cases i <;> decide,
    by fin_cases i <;> decide, by fin_cases i <;> decide⟩

def sP
    (i : Fin 7) : Wv v0 := pairW (pa7 i) (pb7 i) (offPair7 i) 0

def gen3 :
    Fin 3 → Wv v0 := ![wFr, sW, pairW 4 5 offPair45 0]

def gen4 :

    Fin 4 → Wv v0 := ![wFr, sW, pairW 4 5 offPair45 0, pairW 8 9 offPair89 0]

def U3 :

    Submodule (ZMod 2) (Wv v0) := Submodule.span (ZMod 2) (Set.range gen3)

def U4 :

    Submodule (ZMod 2) (Wv v0) := Submodule.span (ZMod 2) (Set.range gen4)

def gcode : Fin 4 → ℕ := ![31, 12288, 49152, 393216]

theorem gen4_eq
    (i : Fin 4) : gen4 i = decW (gcode i) := by
  fin_cases i
  · exact wFr_eq_decW
  · exact pairW23_eq_decW
  · exact pairW45_eq_decW
  · exact pairW89_eq_decW

theorem gen3_eq
    (i : Fin 3) : gen3 i = decW (gcode i.castSucc) := by
  fin_cases i
  · exact wFr_eq_decW
  · exact pairW23_eq_decW
  · exact pairW45_eq_decW

theorem smul_decW (t : ZMod 2) (m : ℕ) : t • decW m = decW (sel t m) := by
  rcases zmod2_cases t with rfl | rfl
  · rw [zero_smul, sel, ite_eq_right (by decide), decW_zero]
  · rw [one_smul, sel, ite_eq_left rfl]

theorem sum_gen4
    (c : Fin 4 → ZMod 2) : ∑ i, c i • gen4 i = decW (xsel4 c) := by
  rw [Fin.sum_univ_four, gen4_eq, gen4_eq, gen4_eq, gen4_eq, smul_decW, smul_decW, smul_decW,
    smul_decW, xsel4, decW_xor, decW_xor, decW_xor]
  rfl

theorem sum_gen3
    (c : Fin 3 → ZMod 2) : ∑ i, c i • gen3 i = decW (xsel3 c) := by
  rw [Fin.sum_univ_three, gen3_eq, gen3_eq, gen3_eq, smul_decW, smul_decW, smul_decW, xsel3,
    decW_xor, decW_xor]
  rfl

theorem mem_U4_iff_exists
    (z : Wv v0) : z ∈ U4 ↔ ∃ c : Fin 4 → ZMod 2, z = decW (xsel4 c) := by
  rw [U4, Submodule.mem_span_range_iff_exists_fun]
  exact ⟨fun ⟨c, hc⟩ => ⟨c, hc.symm.trans (sum_gen4 c)⟩,
    fun ⟨c, hc⟩ => ⟨c, (sum_gen4 c).trans hc.symm⟩⟩

theorem mem_U3_iff_exists
    (z : Wv v0) : z ∈ U3 ↔ ∃ c : Fin 3 → ZMod 2, z = decW (xsel3 c) := by
  rw [U3, Submodule.mem_span_range_iff_exists_fun]
  exact ⟨fun ⟨c, hc⟩ => ⟨c, hc.symm.trans (sum_gen3 c)⟩,
    fun ⟨c, hc⟩ => ⟨c, (sum_gen3 c).trans hc.symm⟩⟩

theorem duad7_mem_A3 (i : Fin 7) : duad (pa7 i) (pb7 i) (offPair7 i).ne ∈ A3 := by
  fin_cases i <;> decide

theorem duad7_mem_A2 (i : Fin 7) (hi : (i : ℕ) < 3) :
    duad (pa7 i) (pb7 i) (offPair7 i).ne ∈ A2 := by
  fin_cases i <;> first | decide | (exfalso; simp at hi)

theorem A3_eq_duad7 : ∀ D ∈ A3, ∃ i : Fin 7, D = duad (pa7 i) (pb7 i) (offPair7 i).ne := by
  intro D hD
  simp only [A3, Finset.mem_insert, Finset.mem_singleton] at hD
  rcases hD with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨0, rfl⟩
  · exact ⟨1, rfl⟩
  · exact ⟨2, rfl⟩
  · exact ⟨3, rfl⟩
  · exact ⟨4, rfl⟩
  · exact ⟨5, rfl⟩
  · exact ⟨6, rfl⟩

theorem A2_eq_duad7 : ∀ D ∈ A2, ∃ i : Fin 7, (i : ℕ) < 3 ∧
    D = duad (pa7 i) (pb7 i) (offPair7 i).ne := by
  intro D hD
  simp only [A2, Finset.mem_insert, Finset.mem_singleton] at hD
  rcases hD with rfl | rfl | rfl
  · exact ⟨0, by decide, rfl⟩
  · exact ⟨1, by decide, rfl⟩
  · exact ⟨2, by decide, rfl⟩

theorem pairW_of_duad_eq
    {x y : Fin 24} (h : OffPair x y) {i : Fin 7}
    (hD : duad x y h.ne = duad (pa7 i) (pb7 i) (offPair7 i).ne) (b : ZMod 2) :
    pairW x y h b = pairW (pa7 i) (pb7 i) (offPair7 i) b := by
  rcases (duad_eq_duad_iff h.ne (offPair7 i).ne).1 hD with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rfl
  · exact pairW_comm _ _

end CFSG.Monster.B.TwoA
