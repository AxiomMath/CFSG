module

public import CFSG.YGroups.Y443.Native.Align
public import CFSG.YGroups.Y443.Native.Hom
public import CFSG.YGroups.Y443.CentralProjection

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.YGroups.Y443

open CFSG.Monster CFSG.Monster.AxisCount CFSG.Monster.Griess CFSG.Monster.Generated CFSG.Open
open CFSG.Certificates.CosetEnumeration (evalWord evalWord_nil evalWord_cons evalWord_append)

@[expose] noncomputable def axL (s : ℕ) : MonsterY443Derived :=
  ⟨y443Gen 0 * y443Gen s, by
    rw [y443_mem_derived_iff]
    simp only [y443Gen, map_mul, y443Parity_of]
    exact Y443.z2_eps_mul_self⟩

theorem coe_axL (s : ℕ) : ((axL s : MonsterY443Derived) : MonsterY443) = y443Gen 0 * y443Gen s :=
  rfl

theorem axL_zero : axL 0 = 1 := Subtype.ext (y443Gen_mul_self 0)

theorem coe_axL_inv_mul (s r : ℕ) :
    (((axL s)⁻¹ * axL r : MonsterY443Derived) : MonsterY443) = y443Gen s * y443Gen r := by
  have h0 := y443Gen_mul_self 0
  have hs := y443Gen_mul_self s
  show (y443Gen 0 * y443Gen s)⁻¹ * (y443Gen 0 * y443Gen r) = _
  rw [mul_inv_rev, inv_eq_of_mul_eq_one_right hs, inv_eq_of_mul_eq_one_right h0, mul_assoc,
    ← mul_assoc (y443Gen 0), h0, one_mul]

@[expose] noncomputable def evalM : List ℕ → MonsterY443Derived
  | a :: b :: l => (axL a)⁻¹ * axL b * evalM l
  | _ => 1

theorem coe_evalM : ∀ l : List ℕ, Even l.length →
    ((evalM l : MonsterY443Derived) : MonsterY443) = evalWord y443Gen l
  | [], _ => rfl
  | [_], h => by simp at h
  | a :: b :: l, h => by
    have h2 : Even (l.length + 2) := h
    have hl : Even l.length := (Nat.even_add.1 h2).2 even_two
    rw [evalM, Subgroup.coe_mul, coe_axL_inv_mul, coe_evalM l hl, evalWord_cons, evalWord_cons,
      mul_assoc]

@[expose] noncomputable def gL (s : ℕ) : SpaceB ≃ₗ[ℚ] SpaceB := if s = 0 then 1 else M (s - 1)

@[expose] noncomputable def evalGL : List ℕ → (SpaceB ≃ₗ[ℚ] SpaceB)
  | a :: b :: l => (gL a)⁻¹ * gL b * evalGL l
  | _ => 1

theorem exists_gen_of_letter : ∀ s : Fin 12, 1 ≤ s.val →
    ∃ g : E443Gen, y443GenOfLetter s.val = some g ∧ wIdx g = s.val - 1 := by
  decide

theorem fM_axL
    {s : ℕ} (hs : s ≤ 11) :
    ((fM (axL s) : Gmat) : SpaceB ≃ₗ[ℚ] SpaceB) = gL s := by
  by_cases h0 : s = 0
  · subst h0
    rw [axL_zero, map_one]
    simp [gL]
  · obtain ⟨g, hg, hw⟩ := exists_gen_of_letter ⟨s, by omega⟩ (show 1 ≤ s from Nat.pos_of_ne_zero h0)
    have h1 : axL s = axElt g := by
      apply Subtype.ext
      show y443Gen 0 * y443Gen s = _
      simp only [y443Gen, hg]
      rfl
    rw [h1, fM_ax, coe_gGen, gL, ite_eq_right h0]
    simp only at hw
    rw [hw]

theorem fM_evalM :
    ∀ l : List ℕ, (∀ c ∈ l, c ≤ 11) →
    ((fM (evalM l) : Gmat) : SpaceB ≃ₗ[ℚ] SpaceB) = evalGL l
  | [], _ => by simp [evalM, evalGL]
  | [_], _ => by simp [evalM, evalGL]
  | a :: b :: l, h => by
    simp only [evalM, evalGL, map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv]
    rw [fM_axL (h a (by simp)), fM_axL (h b (by simp)),
      fM_evalM l (fun c hc => h c (by simp [hc]))]

theorem wordLin_Lw (s : ℕ) : wordLin (Lw s) = gL s := by
  unfold Lw gL
  split_ifs
  · rfl
  · rfl

theorem wordLin_invWs
    {s : ℕ} (hs : s ≤ 11) : wordLin (invWs s) = (gL s)⁻¹ := by
  unfold invWs gL
  split_ifs with h
  · simp [wordLin_nil]
  · exact (M_inv_eq_wordLin (by omega)).symm

theorem wordLin_pairFactor
    {p : ℕ × ℕ} (h1 : p.1 ≤ 11) :
    wordLin (pairFactor p) = (gL p.1)⁻¹ * gL p.2 := by
  rw [pairFactor, wordLin_append, wordLin_invWs h1, wordLin_Lw p.2]

theorem wcWordOf_cons (a b : ℕ) (l : List ℕ) :
    wcWordOf (a :: b :: l) = wcWordOf l ++ pairFactor (a, b) := by
  simp [wcWordOf, pairUp, List.reverse_cons, List.flatten_append]

theorem wordLin_wcWordOf :
    ∀ l : List ℕ, (∀ c ∈ l, c ≤ 11) →
    wordLin (wcWordOf l) = evalGL l
  | [], _ => rfl
  | [_], _ => rfl
  | a :: b :: l, h => by
    rw [wcWordOf_cons, wordLin_append, wordLin_pairFactor (h a (by simp)),
      wordLin_wcWordOf l (fun c hc => h c (by simp [hc])), evalGL]

theorem evalWord_slet : evalWord y443Gen slet = y443F0 * y443Z := by
  rw [slet, evalWord_append, Y443.evalWord_replicate_flatten, Y443.evalWord_replicate_flatten]
  simp only [evalWord_cons, evalWord_nil, mul_one, y443F0, y443Z, mul_assoc]

theorem slet_le : ∀ c ∈ slet, c ≤ 11 := by decide +kernel

theorem slet_even : Even slet.length := by decide +kernel

theorem y443C_eq_evalM : y443C = evalM slet :=
  Subtype.ext (by rw [coe_evalM slet slet_even, evalWord_slet]; rfl)

theorem fM_y443C_eq :
    ((fM y443C : Gmat) : SpaceB ≃ₗ[ℚ] SpaceB) = wordLin wcWord := by
  rw [y443C_eq_evalM, fM_evalM slet slet_le, wcWord, wordLin_wcWordOf slet slet_le]

end CFSG.YGroups.Y443
