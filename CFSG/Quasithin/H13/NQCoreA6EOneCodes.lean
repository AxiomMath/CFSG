module

public import Certificates.Data.A6EOne
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X3AutBridge

public section

namespace CFSG.Quasithin.H13.A6EOne

open CFSG.QuasithinUnique CFSG.QuasithinUnique.A6Facts
open CFSG.QuasithinUnique.A6Facts.Core (cmul cid autL pslLit autReps autRepsInv pslGenC)
open CFSG.QuasithinUnique.Setup.X3Aut (invC code_inv)

theorem isSubC_spec {L : List (List ℕ)} (h : isSubC L = true) :
    cid ∈ L ∧ (∀ a ∈ L, ∀ b ∈ L, cmul a b ∈ L) ∧ ∀ a ∈ L, invC a ∈ L := by
  simpa [isSubC, and_assoc] using h

@[expose] def cSub (L : List (List ℕ)) : Subgroup P10 := Subgroup.closure {x | code x ∈ L}

theorem mem_cSub {L : List (List ℕ)} (h : isSubC L = true) {x : P10} :
    x ∈ cSub L ↔ code x ∈ L := by
  obtain ⟨h1, h2, h3⟩ := isSubC_spec h
  let H : Subgroup P10 :=
    { carrier := {x | code x ∈ L}
      mul_mem' := fun {x y} hx hy => by
        show code (x * y) ∈ L
        rw [code_mul]
        exact h2 _ hx _ hy
      one_mem' := by
        show code 1 ∈ L
        rw [code_one]
        exact h1
      inv_mem' := fun {x} hx => by
        show code x⁻¹ ∈ L
        rw [code_inv]
        exact h3 _ hx }
  have hH : cSub L = H := H.closure_eq
  rw [hH]
  rfl

theorem exists_dc (n : ℕ) : ∃ x : P10, x ∈ A6Models.autA6 ∧ code x = dc n := by
  obtain ⟨y, hy⟩ := Setup.X3Aut.exists_cd_getD n
  exact ⟨y, y.2, hy⟩

theorem card_eq_length {H : Subgroup P10} {L : List (List ℕ)} (hL : L.Nodup)
    (hmem : ∀ x, x ∈ H ↔ code x ∈ L) (hreal : ∀ c ∈ L, ∃ x : P10, code x = c) :
    Nat.card H = L.length := by
  classical
  let e : H ≃ {c // c ∈ L} :=
    { toFun := fun x => ⟨code x, (hmem x).mp x.2⟩
      invFun := fun c => ⟨(hreal c.1 c.2).choose,
        (hmem _).mpr (by rw [(hreal c.1 c.2).choose_spec]; exact c.2)⟩
      left_inv := fun x =>
        Subtype.ext (code_injective (hreal (code x) ((hmem x).mp x.2)).choose_spec)
      right_inv := fun c => Subtype.ext (hreal c.1 c.2).choose_spec }
  rw [Nat.card_congr e, Nat.card_congr (List.Nodup.getEquiv L hL).symm, Nat.card_eq_fintype_card,
    Fintype.card_fin]

theorem card_cSub {L : List (List ℕ)} (h : isSubC L = true) (hL : L.Nodup)
    (hreal : ∀ c ∈ L, ∃ x : P10, code x = c) : Nat.card (cSub L) = L.length :=
  card_eq_length hL (fun _ => mem_cSub h) hreal

theorem codes_realized (L : List ℕ) : ∀ c ∈ codes L, ∃ x : P10, code x = c := by
  intro c hc
  obtain ⟨n, -, rfl⟩ := List.mem_map.mp hc
  obtain ⟨x, -, hx⟩ := exists_dc n
  exact ⟨x, hx⟩

@[expose] def rep (i : ℕ) : P10 := autRepsP.getD i 1

theorem code_rep (i : ℕ) : code (rep i) = autReps.getD i cid := by
  rcases (show i < 4 ∨ 4 ≤ i by omega) with hi | hi
  · interval_cases i <;> decide +kernel
  · rw [rep, List.getD_eq_default _ _ (by simp [autRepsP]; omega),
      List.getD_eq_default _ _ (by simp [Core.autReps]; omega), code_one]

theorem code_rep_inv (i : ℕ) : code (rep i)⁻¹ = autRepsInv.getD i cid := by
  rcases (show i < 4 ∨ 4 ≤ i by omega) with hi | hi
  · interval_cases i <;> decide +kernel
  · rw [rep, List.getD_eq_default _ _ (by simp [autRepsP]; omega),
      List.getD_eq_default _ _ (by simp [Core.autRepsInv]; omega), inv_one, code_one]

theorem rep_mem_autA6 (i : ℕ) : rep i ∈ A6Models.autA6 := by
  rw [A6Models.autA6.mem_carrier.symm]
  rcases (show i < 4 ∨ 4 ≤ i by omega) with hi | hi
  · rw [autA6_eq, rep, List.getD_eq_getElem _ _ (by simpa [autRepsP] using hi)]
    exact autReps_mem_closure _ (List.getElem_mem _)
  · rw [rep, List.getD_eq_default _ _ (by simp [autRepsP]; omega)]
    exact Subgroup.one_mem _

variable {X : Subgroup P10}

theorem mem_of_inX (hpsl : A6Models.psl29 ≤ X) {I : List ℕ} (hI : ∀ i ∈ I, rep i ∈ X) {x : P10}
    (h : inX I (code x) = true) : x ∈ X := by
  simp only [inX, List.any_eq_true, List.contains_eq_mem, decide_eq_true_eq] at h
  obtain ⟨i, hi, hc⟩ := h
  rw [← code_rep_inv, ← code_mul, ← mem_psl29_iff] at hc
  have := X.mul_mem (hpsl hc) (hI i hi)
  rwa [inv_mul_cancel_right] at this

theorem inX_of_mem (hpsl : A6Models.psl29 ≤ X) (haut : X ≤ A6Models.autA6) {I : List ℕ}
    (hI : ∀ i < 4, rep i ∈ X → i ∈ I) {x : P10} (hx : x ∈ X) : inX I (code x) = true := by
  obtain ⟨r, hr, hxr⟩ := (mem_autA6_iff_exists x).mp (haut hx)
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hr
  have hri : autRepsP[i] = rep i := by
    rw [rep, List.getD_eq_getElem]
  rw [hri] at hxr
  have hi4 : i < 4 := by simpa [autRepsP] using hi
  have hrX : rep i ∈ X := by
    have := X.mul_mem (X.inv_mem (hpsl hxr)) hx
    rwa [mul_inv_rev, inv_inv, inv_mul_cancel_right] at this
  simp only [inX, List.any_eq_true, List.contains_eq_mem, decide_eq_true_eq]
  refine ⟨i, hI i hi4 hrX, ?_⟩
  rw [← code_rep_inv, ← code_mul, ← mem_psl29_iff]
  exact hxr

theorem mem_xList_iff {I : List ℕ} {c : List ℕ} :
    c ∈ xList I ↔ ∃ i ∈ I, ∃ y ∈ pslLit, c = cmul y (autReps.getD i cid) := by
  simp only [xList, List.mem_flatMap, List.mem_map]
  constructor
  · rintro ⟨i, hi, y, hy, rfl⟩
    exact ⟨i, hi, y, hy, rfl⟩
  · rintro ⟨i, hi, y, hy, rfl⟩
    exact ⟨i, hi, y, hy, rfl⟩

theorem card_eq_xList (hpsl : A6Models.psl29 ≤ X) (haut : X ≤ A6Models.autA6) {I : List ℕ}
    (hI : ∀ i < 4, rep i ∈ X ↔ i ∈ I) (hI4 : ∀ i ∈ I, i < 4) (hnd : (xList I).Nodup) :
    Nat.card X = (xList I).length := by
  refine card_eq_length hnd (fun x => ?_) ?_
  · constructor
    · intro hx
      have h := inX_of_mem hpsl haut (fun i hi h => (hI i hi).mp h) hx
      simp only [inX, List.any_eq_true, List.contains_eq_mem, decide_eq_true_eq] at h
      obtain ⟨i, hi, hc⟩ := h
      rw [mem_xList_iff]
      refine ⟨i, hi, _, hc, ?_⟩
      rw [← code_rep_inv, ← code_rep, ← code_mul, ← code_mul, inv_mul_cancel_right]
    · intro hx
      obtain ⟨i, hi, y, hy, hc⟩ := mem_xList_iff.mp hx
      obtain ⟨y', hy', rfl⟩ := exists_psl29_of_code hy
      rw [← code_rep, ← code_mul] at hc
      rw [code_injective hc]
      exact X.mul_mem (hpsl hy') ((hI i (hI4 i hi)).mpr hi)
  · intro c hc
    obtain ⟨i, -, y, hy, rfl⟩ := mem_xList_iff.mp hc
    obtain ⟨y', -, rfl⟩ := exists_psl29_of_code hy
    exact ⟨y' * rep i, by rw [code_mul, code_rep]⟩

end CFSG.Quasithin.H13.A6EOne
