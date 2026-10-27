module

public import Certificates.Data.Kernel.PermCent.SmallK12
public import CFSG.LocalAnalysis.ComponentClassification.M12CoverSylow

public section

namespace CFSG.Certificates.Kernel.PkCV.S7M12C

open CFSG.ComponentClassification.M12Cover.SylowTable CFSG.KC.Enum

@[expose] def codeOK (c : List ℕ) : Bool :=
  (List.range 12).all fun a => decide (nth 0 c a < 12) &&
    (List.range 12).all fun b => a == b || nth 0 c a != nth 0 c b

theorem codeOK_lt {c : List ℕ} (h : codeOK c = true) : ∀ x < 12, nth 0 c x < 12 := by
  intro x hx
  simp only [codeOK, List.all_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq] at h
  exact (h x hx).1

theorem codeOK_inj {c : List ℕ} (h : codeOK c = true) :
    ∀ a < 12, ∀ b < 12, nth 0 c a = nth 0 c b → a = b := by
  intro a ha b hb e
  simp only [codeOK, List.all_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq,
    Bool.or_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at h
  rcases (h a ha).2 b hb with h' | h'
  · exact h'
  · exact absurd e h'

@[expose] noncomputable def cvL (c : List ℕ) : CV 12 :=
  if h : codeOK c = true then ⟨pmk 12 (wC 12) (nth 0 c), canon_pmk Small.lt (codeOK_lt h)
    (codeOK_inj h)⟩ else 1

@[expose] def wordC {G : Type*} [Group G] (x y : G) (w : List ℕ) : G :=
  (w.map fun k => if k = 0 then x else if k = 1 then y else y⁻¹).prod

@[expose] def aL : List ℕ := [3, 1, 9, 0, 10, 11, 6, 7, 8, 2, 4, 5]

@[expose] def bL : List ℕ := [7, 2, 3, 1, 11, 9, 5, 8, 0, 6, 4, 10]

@[expose] def d0L : List ℕ := [11, 1, 3, 6, 0, 5, 2, 7, 10, 8, 9, 4]

@[expose] noncomputable def Ac : CV 12 := cvL aL

@[expose] noncomputable def Bc : CV 12 := cvL bL

@[expose] noncomputable def D0c : CV 12 := cvL d0L

@[expose] noncomputable def eC (x : ℕ) : CV 12 := cvL (code x)

@[expose] noncomputable def SLc : List (CV 12) := (List.range 64).map eC

@[expose] noncomputable def CZc : List (CV 12) :=
  (List.range 64).flatMap fun x => [eC x, eC x * D0c, eC x * D0c * D0c]

@[expose] noncomputable def CLc : List (CV 12) :=
  [wordC Ac Bc [], wordC Ac Bc [2, 0, 2, 0, 1], wordC Ac Bc [2, 0, 1, 0, 1]]

@[expose] noncomputable def Ec : CV 12 := wordC Ac Bc [2, 0, 1, 0, 1]

@[expose] noncomputable def FAc : List (CV 12) :=
  [Ec, D0c, Ec⁻¹, eC 1, D0c, Ec⁻¹, D0c, Ec, D0c, Ec⁻¹, eC 3, D0c, Ec⁻¹, D0c]

@[expose] noncomputable def FBc : List (CV 12) := [D0c, Ec⁻¹, D0c, Ec, D0c, Ec⁻¹, D0c, Ec]

@[expose] noncomputable def fpC (c : CV 12) : ℕ :=
  ((List.finRange 12).filter fun i => decide (ev c i = i)).length

end CFSG.Certificates.Kernel.PkCV.S7M12C

end
