module

public import CFSG.Quasithin.EmptyFaithful.A38c6Defs
public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.Quasithin.A38c6

open CFSG.Quasithin.A38c5.Fm

open Equiv

private theorem tst_swap_mem {T : Subgroup P8} (hD : D8 ≤ T) (x : Fin 8) :
    swap x (partner x) ∈ T := by
  have h0 : swap (0 : Fin 8) 1 ∈ T := hD (Subgroup.subset_closure (by simp))
  have h1 : swap (2 : Fin 8) 3 ∈ T := hD (Subgroup.subset_closure (by simp))
  have h2 : swap (4 : Fin 8) 5 ∈ T := hD (Subgroup.subset_closure (by simp))
  have h3 : swap (6 : Fin 8) 7 ∈ T := hD (Subgroup.subset_closure (by simp))
  have h0' : swap (1 : Fin 8) 0 ∈ T := by rwa [swap_comm]
  have h1' : swap (3 : Fin 8) 2 ∈ T := by rwa [swap_comm]
  have h2' : swap (5 : Fin 8) 4 ∈ T := by rwa [swap_comm]
  have h3' : swap (7 : Fin 8) 6 ∈ T := by rwa [swap_comm]
  fin_cases x
  · exact h0
  · exact h0'
  · exact h1
  · exact h1'
  · exact h2
  · exact h2'
  · exact h3
  · exact h3'

private theorem tst_not_three_cycle {T : Subgroup P8} (hT : IsPGroup 2 ↥T) {y : P8}
    (hy : y ∈ T) (h3 : y.IsThreeCycle) : False := by
  obtain ⟨k, hk⟩ := hT ⟨y, hy⟩
  have hk' : y ^ 2 ^ k = 1 := by
    have := congrArg Subtype.val hk
    simpa [Subgroup.coe_pow] using this
  have h1 : 3 ∣ 2 ^ k := h3.orderOf ▸ orderOf_dvd_of_pow_eq_one hk'
  have h2 : 3 ∣ 2 := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h1
  omega

theorem le_Smu_of_D8_le {T : Subgroup P8} (hT : IsPGroup 2 ↥T) (hD : D8 ≤ T) : T ≤ Smu := by
  intro g hg x
  by_contra hne
  have h1 : swap (g x) (g (partner x)) ∈ T := by
    rw [swap_apply_apply]
    exact T.mul_mem (T.mul_mem hg (tst_swap_mem hD x)) (T.inv_mem hg)
  have h2 : swap (g x) (partner (g x)) ∈ T := tst_swap_mem hD (g x)
  have hab : g x ≠ partner (g x) := fun h => partner_ne (g x) h.symm
  have hac : g x ≠ g (partner x) := fun h => partner_ne x (g.injective h).symm
  have hbc : partner (g x) ≠ g (partner x) := fun h => hne h.symm
  exact tst_not_three_cycle hT (T.mul_mem h2 h1)
    (Perm.isThreeCycle_swap_mul_swap_same hab hac hbc)

private def tstV (a b c d : Fin 8) (x : Fin 8) : Fin 8 :=
  let u := if x.val < 4 then (if x.val < 2 then a else b) else (if x.val < 6 then c else d)
  if x.val % 2 = 0 then u else partner u

private abbrev tstValid (a b c d : Fin 8) : Prop :=
  a.val / 2 ≠ b.val / 2 ∧ a.val / 2 ≠ c.val / 2 ∧ a.val / 2 ≠ d.val / 2 ∧
  b.val / 2 ≠ c.val / 2 ∧ b.val / 2 ≠ d.val / 2 ∧ c.val / 2 ≠ d.val / 2

private theorem tst_eq_V (g : P8) (hg : g ∈ Smu) : ⇑g = tstV (g 0) (g 2) (g 4) (g 6) := by
  have h : ∀ x, g (partner x) = partner (g x) := hg
  funext x
  fin_cases x
  · rfl
  · exact h 0
  · rfl
  · exact h 2
  · rfl
  · exact h 4
  · rfl
  · exact h 6

private theorem tst_cls (x y : Fin 8) (h : x.val / 2 = y.val / 2) : y = x ∨ y = partner x := by
  revert x y; decide

private theorem tst_partner_div (x : Fin 8) : (partner x).val / 2 = x.val / 2 := by
  revert x; decide

private theorem tst_cls_ne {g : P8} (hg : g ∈ Smu) {x y : Fin 8} (h : x.val / 2 ≠ y.val / 2) :
    (g x).val / 2 ≠ (g y).val / 2 := by
  intro e
  have hg' : ∀ x, g (partner x) = partner (g x) := hg
  rcases tst_cls _ _ e with h1 | h1
  · exact h (by rw [g.injective h1])
  · rw [← hg' x] at h1
    exact h (by rw [g.injective h1, tst_partner_div])

private theorem tst_valid_of_smu {g : P8} (hg : g ∈ Smu) : tstValid (g 0) (g 2) (g 4) (g 6) :=
  ⟨tst_cls_ne hg (by decide), tst_cls_ne hg (by decide), tst_cls_ne hg (by decide),
    tst_cls_ne hg (by decide), tst_cls_ne hg (by decide), tst_cls_ne hg (by decide)⟩

private theorem tst_sq_fix {B : Finset (Fin 8)} {q : P8} (hq : q ∈ PStab B) (x : Fin 8) :
    (q * q) x ∈ B ↔ x ∈ B := by
  rcases hq with hq | hq
  · simp only [Perm.mul_apply, hq (q x), hq x]
  · simp only [Perm.mul_apply, hq (q x), hq x, not_not]

private theorem tst_nodup {f : Fin 8 → Fin 8} (hf : Function.Injective f) :
    (List.map f (List.finRange 8)).Nodup :=
  (List.nodup_map_iff_inj_on (List.nodup_finRange 8)).2 fun _ _ _ _ h => hf h

private theorem tst_bij_of_nodup {f : Fin 8 → Fin 8}
    (h : (List.map f (List.finRange 8)).Nodup) : Function.Bijective f :=
  Finite.injective_iff_bijective.1 fun x y hxy =>
    (List.nodup_map_iff_inj_on (List.nodup_finRange 8)).1 h x (List.mem_finRange x) y
      (List.mem_finRange y) hxy

private theorem tst_compat {B : Finset (Fin 8)} {g : P8} (hg : g ∈ PStab B) {x y : Fin 8}
    (hx : x ∈ B) (hy : y ∈ B) : (g x ∈ B ∧ g y ∈ B) ∨ (g x ∉ B ∧ g y ∉ B) := by
  rcases hg with hg | hg
  · exact Or.inl ⟨(hg x).2 hx, (hg y).2 hy⟩
  · exact Or.inr ⟨fun h => (hg x).1 h hx, fun h => (hg y).1 h hy⟩

private abbrev TstFin1 (S : Finset (Fin 8)) (cl : Fin 6 → P8) : Prop :=
  ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, ∀ d ∈ S, a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d →
    ∃ i, swap a b * swap c d = cl i

private abbrev TstFin (B : Finset (Fin 8)) (cl : Fin 6 → P8) : Prop :=
  TstFin1 B cl ∧ TstFin1 Bᶜ cl

private abbrev TstCore (B : Finset (Fin 8)) (k : Fin 8) (cl : Fin 6 → P8) : Prop :=
  ∀ a b c d : Fin 8, tstValid a b c d →
    ((tstV a b c d 0 ∈ B ∧ tstV a b c d k ∈ B) ∨ (tstV a b c d 0 ∉ B ∧ tstV a b c d k ∉ B)) →
    ∀ h : (List.map (tstV a b c d) (List.finRange 8)).Nodup,
      Perm.sign (Equiv.ofBijective _ (tst_bij_of_nodup h)) = 1 →
      ∀ (i : Fin 6) (x : Fin 8),
        tstV a b c d (tstV a b c d (cl i x)) = cl i (tstV a b c d (tstV a b c d x))

private theorem tst_abstract {B : Finset (Fin 8)} {k : Fin 8} {cl : Fin 6 → P8}
    (h0 : (0 : Fin 8) ∈ B) (hk : k ∈ B) (hfin : TstFin B cl) (hcore : TstCore B k cl) {q : P8}
    (hqS : q ∈ Smu) (hqP : q ∈ PStab B) (hqA : q ∈ alternatingGroup (Fin 8)) :
    q * q ∈ Vsub B := by
  have hCl : ∀ c ∈ dts B ∪ dts Bᶜ, ∃ i, c = cl i := by
    rintro c (⟨a, b, c', d, hab, hac, had, hbc, hbd, hcd, hS, rfl⟩ |
      ⟨a, b, c', d, hab, hac, had, hbc, hbd, hcd, hS, rfl⟩)
    · have ha : a ∈ B := by rw [← hS]; simp
      have hb : b ∈ B := by rw [← hS]; simp
      have hc : c' ∈ B := by rw [← hS]; simp
      have hd : d ∈ B := by rw [← hS]; simp
      obtain ⟨i, hi⟩ := hfin.1 a ha b hb c' hc d hd hab hac had hbc hbd hcd
      exact ⟨i, hi⟩
    · have ha : a ∈ Bᶜ := by rw [← hS]; simp
      have hb : b ∈ Bᶜ := by rw [← hS]; simp
      have hc : c' ∈ Bᶜ := by rw [← hS]; simp
      have hd : d ∈ Bᶜ := by rw [← hS]; simp
      obtain ⟨i, hi⟩ := hfin.2 a ha b hb c' hc d hd hab hac had hbc hbd hcd
      exact ⟨i, hi⟩
  have hv := tst_valid_of_smu hqS
  have hf := tst_eq_V q hqS
  have hb : Function.Bijective (tstV (q 0) (q 2) (q 4) (q 6)) := hf ▸ q.bijective
  have hnd := tst_nodup hb.1
  have he : Equiv.ofBijective _ (tst_bij_of_nodup hnd) = q :=
    Equiv.ext fun x => (congrFun hf x).symm
  have hs : Perm.sign (Equiv.ofBijective _ (tst_bij_of_nodup hnd)) = 1 := by
    rw [he]; exact Perm.mem_alternatingGroup.1 hqA
  have hcp : (tstV (q 0) (q 2) (q 4) (q 6) 0 ∈ B ∧ tstV (q 0) (q 2) (q 4) (q 6) k ∈ B) ∨
      (tstV (q 0) (q 2) (q 4) (q 6) 0 ∉ B ∧ tstV (q 0) (q 2) (q 4) (q 6) k ∉ B) := by
    rw [← hf]; exact tst_compat hqP h0 hk
  have hmain := hcore _ _ _ _ hv hcp hnd hs
  rw [mem_Vsub]
  refine ⟨fun c hc => ?_, tst_sq_fix hqP⟩
  obtain ⟨i, rfl⟩ := hCl c hc
  refine Equiv.ext fun x => ?_
  have := hmain i x
  rw [← hf] at this
  exact this

private def tstCl1 : Fin 6 → P8 :=
  ![swap 0 1 * swap 2 3, swap 0 2 * swap 1 3, swap 0 3 * swap 1 2,
    swap 4 5 * swap 6 7, swap 4 6 * swap 5 7, swap 4 7 * swap 5 6]

private def tstCl2 : Fin 6 → P8 :=
  ![swap 0 1 * swap 4 5, swap 0 4 * swap 1 5, swap 0 5 * swap 1 4,
    swap 2 3 * swap 6 7, swap 2 6 * swap 3 7, swap 2 7 * swap 3 6]

private def tstCl3 : Fin 6 → P8 :=
  ![swap 0 1 * swap 6 7, swap 0 6 * swap 1 7, swap 0 7 * swap 1 6,
    swap 2 3 * swap 4 5, swap 2 4 * swap 3 5, swap 2 5 * swap 3 4]

set_option maxRecDepth 100000 in
set_option synthInstance.maxSize 1024 in
private theorem tst_fin1 : TstFin {0, 1, 2, 3} tstCl1 := ⟨by decide +kernel, by decide +kernel⟩

set_option maxRecDepth 100000 in
set_option synthInstance.maxSize 1024 in
private theorem tst_fin2 : TstFin {0, 1, 4, 5} tstCl2 := ⟨by decide +kernel, by decide +kernel⟩

set_option maxRecDepth 100000 in
set_option synthInstance.maxSize 1024 in
private theorem tst_fin3 : TstFin {0, 1, 6, 7} tstCl3 := ⟨by decide +kernel, by decide +kernel⟩

set_option maxRecDepth 100000 in
set_option synthInstance.maxSize 1024 in
private theorem tst_core1 : TstCore {0, 1, 2, 3} 2 tstCl1 := by decide +kernel

set_option maxRecDepth 100000 in
set_option synthInstance.maxSize 1024 in
private theorem tst_core2 : TstCore {0, 1, 4, 5} 4 tstCl2 := by decide +kernel

set_option maxRecDepth 100000 in
set_option synthInstance.maxSize 1024 in
private theorem tst_core3 : TstCore {0, 1, 6, 7} 6 tstCl3 := by decide +kernel

theorem sq_mem_Vsub {B : Finset (Fin 8)} (hB : B ∈ blocks3) {T : Subgroup P8}
    (hT : T ≤ Smu ⊓ PStab B) {q : P8} (hq : q ∈ T) (hqA : q ∈ alternatingGroup (Fin 8)) :
    q * q ∈ Vsub B := by
  have hqS : q ∈ Smu := (hT hq).1
  have hqP : q ∈ PStab B := (hT hq).2
  simp only [blocks3, List.mem_cons, List.not_mem_nil, or_false] at hB
  rcases hB with rfl | rfl | rfl
  · exact tst_abstract (by decide) (by decide) tst_fin1 tst_core1 hqS hqP hqA
  · exact tst_abstract (by decide) (by decide) tst_fin2 tst_core2 hqS hqP hqA
  · exact tst_abstract (by decide) (by decide) tst_fin3 tst_core3 hqS hqP hqA

private theorem tst_not_mem_Vsub {B : Finset (Fin 8)} (hB : B ∈ blocks3) :
    ∃ y : Fin 8, swap y (partner y) * swap 0 1 ∉ Vsub B := by
  simp only [blocks3, List.mem_cons, List.not_mem_nil, or_false] at hB
  rcases hB with rfl | rfl | rfl
  · refine ⟨4, fun h => ?_⟩
    have h1 := (mem_Vsub.1 h).1 (swap 0 2 * swap 1 3)
      (Or.inl ⟨0, 2, 1, 3, by decide, by decide, by decide, by decide, by decide, by decide,
        by decide, rfl⟩)
    revert h1
    decide
  · refine ⟨2, fun h => ?_⟩
    have h1 := (mem_Vsub.1 h).1 (swap 0 4 * swap 1 5)
      (Or.inl ⟨0, 4, 1, 5, by decide, by decide, by decide, by decide, by decide, by decide,
        by decide, rfl⟩)
    revert h1
    decide
  · refine ⟨2, fun h => ?_⟩
    have h1 := (mem_Vsub.1 h).1 (swap 0 6 * swap 1 7)
      (Or.inl ⟨0, 6, 1, 7, by decide, by decide, by decide, by decide, by decide, by decide,
        by decide, rfl⟩)
    revert h1
    decide

theorem exists_comm_not_mem_Vsub {B : Finset (Fin 8)} (hB : B ∈ blocks3) {T : Subgroup P8}
    (hT : T ≤ Smu ⊓ PStab B) (hD : D8 ≤ T) (htrans : ∀ x y : Fin 8, ∃ g ∈ T, g x = y) :
    ∃ g ∈ T, ∃ h ∈ T, g * h * g⁻¹ * h⁻¹ ∉ Vsub B := by
  obtain ⟨y, hy⟩ := tst_not_mem_Vsub hB
  obtain ⟨s, hsT, hs0⟩ := htrans 0 y
  have hsS : ∀ x, s (partner x) = partner (s x) := (hT hsT).1
  have hs1 : s 1 = partner y := by
    have h := hsS 0
    rw [hs0] at h
    exact h
  have h01 : swap (0 : Fin 8) 1 ∈ T := hD (Subgroup.subset_closure (by simp))
  refine ⟨s, hsT, swap 0 1, h01, ?_⟩
  have e : s * swap 0 1 * s⁻¹ * (swap 0 1)⁻¹ = swap y (partner y) * swap 0 1 := by
    rw [← swap_apply_apply, hs0, hs1, swap_inv]
  rw [e]
  exact hy

theorem relIndex_inf_alt {T : Subgroup P8} (hD : D8 ≤ T) :
    (T ⊓ alternatingGroup (Fin 8)).relIndex T = 2 := by
  rw [Subgroup.relIndex_eq_two_iff]
  have h0 : swap (0 : Fin 8) 1 ∈ T := hD (Subgroup.subset_closure (by simp))
  refine ⟨swap 0 1, h0, fun b hb => ?_⟩
  have hs : Perm.sign (swap (0 : Fin 8) 1) = -1 := Perm.sign_swap (by decide)
  have hmem : b * swap 0 1 ∈ T ⊓ alternatingGroup (Fin 8) ↔ Perm.sign b = -1 := by
    rw [Subgroup.mem_inf, Perm.mem_alternatingGroup, map_mul, hs]
    simp only [T.mul_mem hb h0, true_and]
    rcases Int.units_eq_one_or (Perm.sign b) with h | h <;> simp [h]
  have hmem' : b ∈ T ⊓ alternatingGroup (Fin 8) ↔ Perm.sign b = 1 := by
    rw [Subgroup.mem_inf, Perm.mem_alternatingGroup]
    simp only [hb, true_and]
  rw [hmem, hmem']
  rcases Int.units_eq_one_or (Perm.sign b) with h | h <;> simp [h]

end CFSG.Quasithin.A38c6
