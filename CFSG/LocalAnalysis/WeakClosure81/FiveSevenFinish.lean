module

public import CFSG.Holt.PSL2Natural.Basic
public import CFSG.LocalAnalysis.WeakClosure81.FiveSevenPar
public import CFSG.Quasithin.Background.B6Defs

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Holt Equiv

theorem eq_one_of_isNaturalPSL2_of_fixes_three {Δ : Type*} {m : ℕ} {P : Subgroup (Perm Δ)}
    (hP : IsNaturalPSL2 P m) {g : Perm Δ} (hg : g ∈ P) {a b c : Δ} (hab : a ≠ b)
    (hac : a ≠ c) (hbc : b ≠ c) (ha : g a = a) (hb : g b = b) (hc : g c = c) : g = 1 := by
  have h := hP.stabilizer_inf_inf_eq_bot hab hac hbc
  have hmem : (⟨g, hg⟩ : ↥P) ∈ MulAction.stabilizer ↥P a ⊓ MulAction.stabilizer ↥P b ⊓
      MulAction.stabilizer ↥P c := by
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · exact ha
    · exact hb
    · exact hc
  rw [h] at hmem
  exact congrArg Subtype.val (Subgroup.mem_bot.1 hmem)

theorem le_of_maxOver_eq_stabilizer_of_isNaturalPSL2 {n m : ℕ} (hn : 4 < n)
    {K A P : Subgroup (Perm (Fin n))} (hAlt : alternatingGroup (Fin n) ≤ K) {α : Fin n}
    (hM : maxOver K A = {K ⊓ MulAction.stabilizer (Perm (Fin n)) α})
    (hP : IsNaturalPSL2 P m) (hAP : A ≤ P) : K ≤ P := by
  obtain ⟨-, hAM, hu⟩ := isUniqueMaxOver_iff.1 hM
  have hAK : A ≤ K := hAM.trans inf_le_left
  have hcard3 : 3 ≤ Nat.card (Fin n) := by
    rw [Nat.card_eq_fintype_card, Fintype.card_fin]
    omega
  by_contra hKP
  have hlt : K ⊓ P < K := lt_of_le_of_ne inf_le_left (fun h => hKP (h ▸ inf_le_right))
  obtain ⟨N, hN, hBN⟩ := exists_isMaxSubgroupIn hlt
  have hNM : N = K ⊓ MulAction.stabilizer (Perm (Fin n)) α :=
    hu N hN ((le_inf hAK hAP).trans hBN)
  obtain ⟨k, hk, hkα⟩ := exists_mem_inf_alternatingGroup_smul_ne hP.isPretransitive hcard3 α
  have hkB : k ∈ K ⊓ P :=
    Subgroup.mem_inf.2 ⟨hAlt (Subgroup.mem_inf.1 hk).2, (Subgroup.mem_inf.1 hk).1⟩
  have h1 : k ∈ K ⊓ MulAction.stabilizer (Perm (Fin n)) α := hNM ▸ hBN hkB
  exact hkα (MulAction.mem_stabilizer_iff.1 (Subgroup.mem_inf.1 h1).2)

theorem eq_five_of_alternatingGroup_le_isNaturalPSL2 {n m : ℕ} (hn : 4 < n)
    {P : Subgroup (Perm (Fin n))} (hP : IsNaturalPSL2 P m)
    (hAltP : alternatingGroup (Fin n) ≤ P) : n = 5 := by
  by_contra hne
  have h6 : 6 ≤ n := by omega
  set p0 : Fin n := ⟨0, by omega⟩ with hp0
  set p1 : Fin n := ⟨1, by omega⟩ with hp1
  set p2 : Fin n := ⟨2, by omega⟩ with hp2
  set p3 : Fin n := ⟨3, by omega⟩ with hp3
  set p4 : Fin n := ⟨4, by omega⟩ with hp4
  set p5 : Fin n := ⟨5, by omega⟩ with hp5
  have h01 : p0 ≠ p1 := fun h => by simp [hp0, hp1, Fin.ext_iff] at h
  have h12 : p1 ≠ p2 := fun h => by simp [hp1, hp2, Fin.ext_iff] at h
  have h02 : p0 ≠ p2 := fun h => by simp [hp0, hp2, Fin.ext_iff] at h
  have h34 : p3 ≠ p4 := fun h => by simp [hp3, hp4, Fin.ext_iff] at h
  have h35 : p3 ≠ p5 := fun h => by simp [hp3, hp5, Fin.ext_iff] at h
  have h45 : p4 ≠ p5 := fun h => by simp [hp4, hp5, Fin.ext_iff] at h
  have hne3 : ∀ q : Fin n, 3 ≤ q.val → q ≠ p0 ∧ q ≠ p1 ∧ q ≠ p2 := fun q hq =>
    ⟨fun h => by simp [hp0, Fin.ext_iff] at h; omega,
      fun h => by simp [hp1, Fin.ext_iff] at h; omega,
      fun h => by simp [hp2, Fin.ext_iff] at h; omega⟩
  have hc : swap p0 p1 * swap p1 p2 ∈ alternatingGroup (Fin n) := by
    rw [Perm.mem_alternatingGroup, Perm.sign_mul, Perm.sign_swap h01, Perm.sign_swap h12]
    decide
  have hfix : ∀ q : Fin n, 3 ≤ q.val → (swap p0 p1 * swap p1 p2) q = q := by
    intro q hq
    obtain ⟨a, b, c⟩ := hne3 q hq
    rw [Perm.mul_apply, swap_apply_of_ne_of_ne b c, swap_apply_of_ne_of_ne a b]
  have h1 := eq_one_of_isNaturalPSL2_of_fixes_three hP (hAltP hc) h34 h35 h45
    (hfix p3 (by simp [hp3])) (hfix p4 (by simp [hp4])) (hfix p5 (by simp [hp5]))
  have h2 := congrArg (fun g : Perm (Fin n) => g p0) h1
  simp only [Perm.mul_apply, Perm.one_apply] at h2
  rw [swap_apply_of_ne_of_ne h01 h02, swap_apply_left] at h2
  exact h01 h2.symm

theorem eq_alternatingGroup_of_le_isNaturalPSL2 {n m : ℕ} (hn5 : n = 5)
    {K P : Subgroup (Perm (Fin n))} (hAlt : alternatingGroup (Fin n) ≤ K) (hKP : K ≤ P)
    (hP : IsNaturalPSL2 P m) : K = alternatingGroup (Fin n) := by
  by_contra hne
  obtain ⟨k, hkK, hkA⟩ := SetLike.exists_of_lt (lt_of_le_of_ne hAlt (Ne.symm hne))
  set p0 : Fin n := ⟨0, by omega⟩ with hp0
  set p1 : Fin n := ⟨1, by omega⟩ with hp1
  set p2 : Fin n := ⟨2, by omega⟩ with hp2
  set p3 : Fin n := ⟨3, by omega⟩ with hp3
  set p4 : Fin n := ⟨4, by omega⟩ with hp4
  have h01 : p0 ≠ p1 := fun h => by simp [hp0, hp1, Fin.ext_iff] at h
  have h23 : p2 ≠ p3 := fun h => by simp [hp2, hp3, Fin.ext_iff] at h
  have h24 : p2 ≠ p4 := fun h => by simp [hp2, hp4, Fin.ext_iff] at h
  have h34 : p3 ≠ p4 := fun h => by simp [hp3, hp4, Fin.ext_iff] at h
  have hk : Perm.sign k = -1 := by
    rcases Int.units_eq_one_or (Perm.sign k) with h | h
    · exact absurd (Perm.mem_alternatingGroup.2 h) hkA
    · exact h
  have hsk : swap p0 p1 * k⁻¹ ∈ alternatingGroup (Fin n) := by
    rw [Perm.mem_alternatingGroup, Perm.sign_mul, Perm.sign_inv, Perm.sign_swap h01, hk]
    decide
  have hsK : swap p0 p1 ∈ K := by
    have := K.mul_mem (hAlt hsk) hkK
    rwa [inv_mul_cancel_right] at this
  have hfix : ∀ q : Fin n, q ≠ p0 → q ≠ p1 → swap p0 p1 q = q := fun q a b =>
    swap_apply_of_ne_of_ne a b
  have h1 := eq_one_of_isNaturalPSL2_of_fixes_three hP (hKP hsK) h23 h24 h34
    (hfix p2 (fun h => by simp [hp2, hp0, Fin.ext_iff] at h)
      (fun h => by simp [hp2, hp1, Fin.ext_iff] at h))
    (hfix p3 (fun h => by simp [hp3, hp0, Fin.ext_iff] at h)
      (fun h => by simp [hp3, hp1, Fin.ext_iff] at h))
    (hfix p4 (fun h => by simp [hp4, hp0, Fin.ext_iff] at h)
      (fun h => by simp [hp4, hp1, Fin.ext_iff] at h))
  have h2 := congrArg (fun g : Perm (Fin n) => g p0) h1
  simp only [Perm.one_apply, swap_apply_left] at h2
  exact h01 h2.symm

theorem eq_five_of_isNaturalPSL2 {n m : ℕ} (hn : 4 < n) {K A P : Subgroup (Perm (Fin n))}
    (hAlt : alternatingGroup (Fin n) ≤ K) {α : Fin n}
    (hM : maxOver K A = {K ⊓ MulAction.stabilizer (Perm (Fin n)) α})
    (hP : IsNaturalPSL2 P m) (hAP : A ≤ P) :
    n = 5 ∧ K = alternatingGroup (Fin n) := by
  have hKP := le_of_maxOver_eq_stabilizer_of_isNaturalPSL2 hn hAlt hM hP hAP
  have h5 := eq_five_of_alternatingGroup_le_isNaturalPSL2 hn hP (hAlt.trans hKP)
  exact ⟨h5, eq_alternatingGroup_of_le_isNaturalPSL2 h5 hAlt hKP hP⟩

end CFSG.LocalAnalysis.WeakClosure81
