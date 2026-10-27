module

public import CFSG.Quasithin.H13.GoldschmidtU43ModOrb
public import CFSG.Quasithin.H13.GoldschmidtU43ModSimple

public section

namespace CFSG.Quasithin.H13.U43

open CFSG.KGroups.U43 CFSG.KGroups.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.LieType.Multipliers.U43

@[expose] noncomputable def sylGen (j : ℕ) : X₀ :=
  [hVal sylWord0, hVal sylWord1, hVal sylWord2].getD j 1

@[expose] noncomputable def Ssub : Subgroup X₀ := Subgroup.closure (sylGen '' Set.Iio 3)

theorem sylGens_get0 (n : ℕ) (tA tB : Array ℕ) : (sylGens n tA tB)[0]! =
    evalArr n (hGens n tA tB) (invArrs n (hGens n tA tB)) sylWord0 := rfl

theorem sylGens_get1 (n : ℕ) (tA tB : Array ℕ) : (sylGens n tA tB)[1]! =
    evalArr n (hGens n tA tB) (invArrs n (hGens n tA tB)) sylWord1 := rfl

theorem sylGens_get2 (n : ℕ) (tA tB : Array ℕ) : (sylGens n tA tB)[2]! =
    evalArr n (hGens n tA tB) (invArrs n (hGens n tA tB)) sylWord2 := rfl

theorem rep_sylGens (h1 : invsOK 820 (genAB tabA tabB) (invArrs 820 (genAB tabA tabB)) = true)
    (hE : invsOK 820 (hGens 820 tabA tabB) (invArrs 820 (hGens 820 tabA tabB)) = true) :
    ∀ j < 3, Rep 820 (sylGens 820 tabA tabB)[j]! (psi (sylGen j)) := by
  intro j hj
  interval_cases j
  · rw [sylGens_get0]
    exact rep_hWord h1 hE (by decide)
  · rw [sylGens_get1]
    exact rep_hWord h1 hE (by decide)
  · rw [sylGens_get2]
    exact rep_hWord h1 hE (by decide)

theorem not_eqA_one {t : Array ℕ} {x : X₀} (hx : Rep 820 t (psi x)) (h1 : x ≠ 1) :
    eqA 820 t (idA 820) = false := by
  by_contra hc
  have h := (eqA_iff hx (g := psi x) (h := 1) rep_idA).1 (by simpa using hc)
  exact h1 (psi_inj (by rw [h, map_one]))

theorem isInvolA_of_orderOf {t : Array ℕ} {x : X₀} (hx : Rep 820 t (psi x)) (h2 : orderOf x = 2) :
    isInvolA 820 t = true := by
  have hx1 : x ≠ 1 := by
    rintro rfl
    simp at h2
  have hsq : x * x = 1 := by rw [← pow_two, ← h2]; exact pow_orderOf_eq_one x
  unfold isInvolA
  simp only [Bool.and_eq_true, Bool.not_eq_true']
  refine ⟨(eqA_iff (rep_compA hx hx) (g := psi x * psi x) (h := 1) rep_idA).2 ?_,
    not_eqA_one hx hx1⟩
  rw [← map_mul, hsq, map_one]

theorem syl_sound (ho : orbCheck 820 tabA tabB = true) (hs : sylCheck 820 tabA tabB = true) :
    Nat.card Ssub = 128 ∧ ∀ s ∈ Ssub, orderOf s = 2 → s ∈ conjClass := by
  unfold sylCheck at hs
  simp only [Bool.and_eq_true] at hs
  obtain ⟨⟨⟨⟨⟨⟨h1, hE⟩, hS⟩, hd⟩, hk⟩, hc⟩, hi⟩ := hs
  have hrS := rep_sylGens h1 hE
  have hrSi := rep_invs psi hrS hS (by simp [sylGens])
  obtain ⟨hsz, h0⟩ := derivOK_size hd
  have hid : Rep 820 (bfsRec (leftStep 820 (sylGens 820 tabA tabB)) 3 200 (idA 820)).L[0]!
      (1 : Equiv.Perm (Fin 820)) := rep_of_eqA rep_idA h0
  have hex := deriv_sound psi (Ssub : Set X₀) (leftStep 820 (sylGens 820 tabA tabB))
    (fun j x => sylGen j * x) (one_mem Ssub) (by rw [map_one]; exact rep_idA)
    (fun j hj x hx => Ssub.mul_mem (Subgroup.subset_closure ⟨j, hj, rfl⟩) hx)
    (fun j hj t x hx => by
      unfold leftStep
      simpa [map_mul] using rep_compA (hrS j hj) hx) hd
  have hlow : 128 ≤ Nat.card Ssub := card_ge_of_deriv psi (by norm_num) (Ssub : Set X₀) hsz hk hex
  have hup := closure_sound psi sylGen (S := sylGens 820 tabA tabB) (k := 3) (by simp [sylGens])
    hrS hrSi hid (by omega) hc
  have hcard : Nat.card Ssub ≤ 128 := by
    choose! f hf using hup
    let F : Ssub → Fin 128 := fun x => ⟨f x, hsz ▸ (hf x x.2).1⟩
    have hinj : Function.Injective F := by
      intro x y hxy
      have hfe : f x = f y := congrArg Fin.val hxy
      have h1 := (hf x x.2).2
      have h2 := (hf y y.2).2
      rw [← hfe] at h2
      exact Subtype.ext (psi_inj (h1.unique h2))
    simpa using Nat.card_le_card_of_injective F hinj
  refine ⟨le_antisymm hcard hlow, ?_⟩
  intro s hsS hso
  obtain ⟨i, hi', hri⟩ := hup s hsS
  have hi128 : i < 128 := hsz ▸ hi'
  have h5 := allLt_spec hi hi128
  simp only [isInvolA_of_orderOf hri hso, Bool.not_true, Bool.false_or] at h5
  obtain ⟨j, hj, hej⟩ := Array.any_eq_true.1 h5
  obtain ⟨hosz, -, hexo⟩ := orb_sound ho
  obtain ⟨x, hx, hrx⟩ := hexo j (hosz ▸ hj)
  rw [← getElem!_pos (orbRec 820 tabA tabB).L j hj] at hej
  exact psi_inj ((eqA_iff hri hrx).1 hej) ▸ hx

end CFSG.Quasithin.H13.U43
