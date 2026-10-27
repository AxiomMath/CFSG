module

public import CFSG.Quasithin.H13.GoldschmidtU43ModPerm
public import CFSG.LieType.Multipliers.U43Bridge

public section

namespace CFSG.Quasithin.H13.U43

open CFSG.KGroups.U43 CFSG.Monster.B.Co2 CFSG.LieType.Multipliers.U43
open CFSG.Sporadic.Bridge.TwoGen (img2)

@[expose] noncomputable def g2 : ℕ → X₀ := img2 xElt yElt

@[expose] noncomputable def mdA : X₀ := evalG g2 wordA

@[expose] noncomputable def mdS : X₀ := evalG g2 wordS

@[expose] noncomputable def mdU : X₀ := evalG g2 wordU

@[expose] noncomputable def mdV : X₀ := evalG g2 wordV

@[expose] noncomputable def mdPhi : X₀ := evalG g2 wordPhi

theorem rep_genAB : ∀ i < 2, Rep 820 (genAB tabA tabB)[i]! (psi (g2 i)) := by
  intro i hi
  interval_cases i
  · simpa [g2, img2, genAB] using rep_tabA
  · simpa [g2, img2, genAB] using rep_tabB

theorem rep_genAB_inv (h : invsOK 820 (genAB tabA tabB) (invArrs 820 (genAB tabA tabB)) = true) :
    ∀ i < 2, Rep 820 (invArrs 820 (genAB tabA tabB))[i]! (psi (g2 i))⁻¹ :=
  rep_invs psi rep_genAB h (by simp [genAB])

theorem rep_wArr (h : invsOK 820 (genAB tabA tabB) (invArrs 820 (genAB tabA tabB)) = true)
    {w : Word} (hw : ∀ l ∈ w, l.1 < 2) : Rep 820 (wArr 820 tabA tabB w) (psi (evalG g2 w)) :=
  rep_evalArr psi rep_genAB (rep_genAB_inv h) w hw

theorem gensWith_get0 (n : ℕ) (tA tB last : Array ℕ) :
    (gensWith n tA tB last)[0]! = wArr n tA tB wordA := rfl

theorem gensWith_get1 (n : ℕ) (tA tB last : Array ℕ) :
    (gensWith n tA tB last)[1]! = wArr n tA tB wordS := rfl

theorem gensWith_get2 (n : ℕ) (tA tB last : Array ℕ) :
    (gensWith n tA tB last)[2]! = wArr n tA tB wordU := rfl

theorem gensWith_get3 (n : ℕ) (tA tB last : Array ℕ) :
    (gensWith n tA tB last)[3]! = wArr n tA tB wordV := rfl

theorem gensWith_get4 (n : ℕ) (tA tB last : Array ℕ) : (gensWith n tA tB last)[4]! = last := rfl

theorem rep_gensWith (h : invsOK 820 (genAB tabA tabB) (invArrs 820 (genAB tabA tabB)) = true)
    {last : Array ℕ} {x : X₀} (hx : Rep 820 last (psi x)) :
    ∀ i < 5, Rep 820 (gensWith 820 tabA tabB last)[i]! (psi (gen5 mdA mdS mdU mdV x i)) := by
  intro i hi
  interval_cases i
  · rw [gensWith_get0]
    exact rep_wArr h (by decide)
  · rw [gensWith_get1]
    exact rep_wArr h (by decide)
  · rw [gensWith_get2]
    exact rep_wArr h (by decide)
  · rw [gensWith_get3]
    exact rep_wArr h (by decide)
  · rw [gensWith_get4]
    exact hx

theorem rep_phiArr (h : invsOK 820 (genAB tabA tabB) (invArrs 820 (genAB tabA tabB)) = true) :
    Rep 820 (phiArr 820 tabA tabB) (psi mdPhi) :=
  rep_wArr h (by decide)

@[expose] noncomputable def hVal (w : Word) : X₀ := evalG (gen5 mdA mdS mdU mdV 1) w

theorem rep_hGens (h : invsOK 820 (genAB tabA tabB) (invArrs 820 (genAB tabA tabB)) = true) :
    ∀ i < 5, Rep 820 (hGens 820 tabA tabB)[i]! (psi (gen5 mdA mdS mdU mdV 1 i)) :=
  rep_gensWith h (x := 1) (by rw [map_one]; exact rep_idA)

theorem rep_hGens_inv (h1 : invsOK 820 (genAB tabA tabB) (invArrs 820 (genAB tabA tabB)) = true)
    (hE : invsOK 820 (hGens 820 tabA tabB) (invArrs 820 (hGens 820 tabA tabB)) = true) :
    ∀ i < 5, Rep 820 (invArrs 820 (hGens 820 tabA tabB))[i]!
      (psi (gen5 mdA mdS mdU mdV 1 i))⁻¹ :=
  rep_invs psi (rep_hGens h1) hE (by simp [hGens, gensWith])

theorem rep_hWord (h1 : invsOK 820 (genAB tabA tabB) (invArrs 820 (genAB tabA tabB)) = true)
    (hE : invsOK 820 (hGens 820 tabA tabB) (invArrs 820 (hGens 820 tabA tabB)) = true)
    {w : Word} (hw : ∀ l ∈ w, l.1 < 5) :
    Rep 820 (evalArr 820 (hGens 820 tabA tabB) (invArrs 820 (hGens 820 tabA tabB)) w)
      (psi (hVal w)) :=
  rep_evalArr psi (rep_hGens h1) (rep_hGens_inv h1 hE) w hw

theorem map_evalG {K L : Type*} [Group K] [Group L] (f : K →* L) (g : ℕ → K)
    (w : List (ℕ × Bool)) : f (evalG g w) = evalG (fun i => f (g i)) w := by
  simp only [evalG, map_list_prod, List.map_map]
  congr 1
  apply List.map_congr_left
  intro l _
  by_cases hb : l.2 = true <;> simp [letterVal, hb]

theorem map_gen5 {K L : Type*} [Group K] [Group L] (f : K →* L) (a s u v φ : K) (i : ℕ) :
    f (gen5 a s u v φ i) = gen5 (f a) (f s) (f u) (f v) (f φ) i := by
  rcases i with _ | _ | _ | _ | _ | i <;> simp [gen5, map_one]

end CFSG.Quasithin.H13.U43
