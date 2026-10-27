module

public import CFSG.LocalAnalysis.StandardType.GGStdPosDTorus

public section

namespace CFSG.StandardType.KGCentOm

open CFSG.LieType.Universal CFSG.LieType.Universal.Spin

theorem exists_mem_ggTorus_vec_eq_smul {n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    (hn : 3 ≤ n) (c : Fin n → Kˣ) : ∃ h ∈ ggTorus (plusDatum n K hn), ∀ i : Fin n,
      spinAction (quadPlus n K) h ((plusFrame n K hn).vec i true) =
          (c i : K) • (plusFrame n K hn).vec i true ∧
        spinAction (quadPlus n K) h ((plusFrame n K hn).vec i false) =
          (c i : K)⁻¹ • (plusFrame n K hn).vec i false := by
  let P : (Fin n → Kˣ) → Prop := fun c => ∃ h : spinGroup (quadPlus n K), ∀ i : Fin n,
    spinAction (quadPlus n K) h ((plusFrame n K hn).vec i true) =
        (c i : K) • (plusFrame n K hn).vec i true ∧
      spinAction (quadPlus n K) h ((plusFrame n K hn).vec i false) =
        (c i : K)⁻¹ • (plusFrame n K hn).vec i false
  have hone : P 1 := ⟨1, fun i => by simp⟩
  have hmul : ∀ c c', P c → P c' → P (c * c') := by
    rintro c c' ⟨h, hc⟩ ⟨h', hc'⟩
    refine ⟨h * h', fun i => ⟨?_, ?_⟩⟩
    · rw [map_mul, LinearEquiv.mul_apply, (hc' i).1, map_smul, (hc i).1, smul_smul, Pi.mul_apply,
        Units.val_mul, mul_comm]
    · rw [map_mul, LinearEquiv.mul_apply, (hc' i).2, map_smul, (hc i).2, smul_smul, Pi.mul_apply,
        Units.val_mul, mul_inv, mul_comm]
  have hsingle : ∀ (i : Fin n) (a : Kˣ), P (Pi.mulSingle i a) := by
    intro i a
    obtain ⟨j, hji, -⟩ := exists_ne_and_ne hn i i
    obtain ⟨d, hd⟩ := isSquare_of_charTwo' (a : K)
    have hd0 : d ≠ 0 := by
      rintro rfl
      exact a.ne_zero (by rw [hd, mul_zero])
    obtain ⟨u, hu⟩ : ∃ u : Kˣ, (u : K) = d := ⟨Units.mk0 d hd0, rfl⟩
    have hu2 : ((u ^ (2 : ℤ) : Kˣ) : K) = a := by
      rw [zpow_two, Units.val_mul, hu, ← hd]
    have hu2' : ((u ^ (-2 : ℤ) : Kˣ) : K) = (a : K)⁻¹ := by
      rw [zpow_neg, Units.val_inv_eq_inv_val, hu2]
    set F := plusFrame n K hn
    have hact : ∀ (m : Fin n) (r : Bool),
        spinAction (quadPlus n K) (F.longTorus hji.symm true true u *
          F.longTorus hji.symm true false u) (F.vec m r) =
        ((u ^ (longCoroot i j true false m r + longCoroot i j true true m r) : Kˣ) : K) •
          F.vec m r := by
      intro m r
      rw [map_mul, LinearEquiv.mul_apply, F.spinAction_longTorus_vec, map_smul,
        F.spinAction_longTorus_vec, smul_smul, ← Units.val_mul, ← zpow_add]
    refine ⟨F.longTorus hji.symm true true u * F.longTorus hji.symm true false u, fun m => ?_⟩
    by_cases hmi : m = i
    · rw [hmi, Pi.mulSingle_eq_same, hact, hact]
      have h1 : longCoroot i j true false i true + longCoroot i j true true i true = 2 := by
        simp [longCoroot, hji.symm]
      have h2 : longCoroot i j true false i false + longCoroot i j true true i false = -2 := by
        simp [longCoroot, hji.symm]
      rw [h1, h2, hu2, hu2']
      exact ⟨rfl, rfl⟩
    · have h0 : ∀ r, longCoroot i j true false m r + longCoroot i j true true m r = 0 := by
        intro r
        by_cases hmj : m = j
        · rw [hmj]
          cases r <;> simp [longCoroot, hji]
        · simp [longCoroot, hmi, hmj]
      rw [Pi.mulSingle_eq_of_ne hmi, hact, hact, h0, h0, zpow_zero, Units.val_one, inv_one,
        one_smul]
      exact ⟨rfl, rfl⟩
  have hP : P c := by
    have h := Finset.prod_induction (s := Finset.univ) (fun x => Pi.mulSingle x (c x)) P hmul
      hone (fun x _ => hsingle x (c x))
    rwa [Finset.univ_prod_mulSingle] at h
  obtain ⟨h, hh⟩ := hP
  refine ⟨h, StdPosD.mem_ggTorus_of_lines hn fun k => ?_, hh⟩
  rcases k with m | m
  · have h1 := (hh m).1
    rw [plusFrame_vec, plusVec_true] at h1
    exact ⟨_, h1⟩
  · have h1 := (hh m).2
    rw [plusFrame_vec, plusVec_false] at h1
    exact ⟨_, h1⟩

end CFSG.StandardType.KGCentOm

end
