module

public import CFSG.Quasithin.Vol2.Ch11SecU1L33G
public import CFSG.Quasithin.Vol2.Ch11SecU1L3IP
public import CFSG.Quasithin.Vol2.Ch11SecU1L3IQ

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecU1.L33

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.E1 CFSG.Quasithin.E2P.Asc80
  CFSG.QuasithinUnique.Vol2Native.L239.L33Insp
open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G]

theorem isSolvable_gl2 : Group.IsSolvable (GL (Fin 2) (ZMod 3)) := by
  have : Fintype (GL (Fin 2) (ZMod 3)) := Fintype.ofFinite _
  refine CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow (a := 4)
    (b := 1) Nat.prime_two Nat.prime_three (by norm_num) ?_
  rw [← Nat.card_eq_fintype_card, Matrix.card_GL_field, ZMod.card, Fin.prod_univ_two]
  norm_num

theorem isSolvable_centralizer {L : Subgroup G} (hAS : SecE3.AlmostSimple L) (e : ↥L ≃* PSL3 3)
    {z : G} (hzL : z ∈ L) (hz2 : orderOf z = 2) :
    Group.IsSolvable ↥(Subgroup.centralizer ({z} : Set G)) := by
  obtain ⟨e', he'⟩ := L3I.exists_equiv_zc (by norm_num) e hzL hz2
  have hCL := L3I.inf_centralizer_eq_map_leviC (by norm_num) e' hzL he'
  have := isSolvable_gl2
  have hB : Group.IsSolvable ↥(leviC 3) := by
    rw [← L3I.leviPsi_range]
    exact Group.isSolvable_of_surjective (L3I.leviPsi 3).rangeRestrict_surjective
  have hLC : Group.IsSolvable ↥(L ⊓ Subgroup.centralizer ({z} : Set G)) := by
    rw [hCL]
    exact Group.isSolvable_of_surjective
      ((L.subtype.comp e'.symm.toMonoidHom).subgroupMap_surjective _)
  have h := L3I.isSolvable_centralizer_of_inf hAS (Y := Subgroup.closure {z})
    (by rwa [Subgroup.centralizer_closure])
  rwa [Subgroup.centralizer_closure] at h

namespace Model

variable {L : Subgroup G} (M : Model L)

omit [Finite G] in
theorem code_ne_cone {g : G} (hg : g ≠ 1) : M.code g ≠ cone := fun h =>
  hg (M.code_inj (by rw [h, code_one]))

omit [Finite G] in
theorem code_sq {g : G} (hg : g * g = 1) : cmul (M.code g) (M.code g) = cone := by
  rw [← code_mul, hg, code_one]

omit [Finite G] in
theorem code_comm {g h : G} (e : g * h = h * g) :
    cmul (M.code g) (M.code h) = cmul (M.code h) (M.code g) := by
  rw [← code_mul, ← code_mul, e]

omit [Finite G] in
theorem conj_eq_of_code {g x x' : G}
    (h : cmul (M.code g) (M.code x) = cmul (M.code x') (M.code g)) : g * x * g⁻¹ = x' := by
  have h1 : g * x = x' * g := M.code_inj (by rw [code_mul, code_mul]; exact h)
  rw [h1, mul_inv_cancel_right]

omit [Finite G] in
theorem not_K0_le {z : G} (hz : M.code z = z0c) :
    ¬ M.K0 ≤ Subgroup.centralizer ({z} : Set G) := by
  intro hle
  obtain ⟨k, hk, hkz⟩ := z0_check.2.2.2.2.2
  obtain ⟨g, hg, hgc⟩ := M.exists_mem k0l_facts hk
  have h1 := Subgroup.mem_centralizer_singleton_iff.mp (hle hg)
  apply hkz
  rw [← hgc, ← hz, ← code_mul, ← code_mul, h1]

omit [Finite G] in
theorem conjSub_le_T0 {g : G} (hg : g ∈ M.T0) {A : Subgroup G} (hAT : A ≤ M.T0) :
    A1b.conjSub g A ≤ M.T0 := by
  intro w hw
  rw [A1b.mem_conjSub_iff] at hw
  have h3 := M.T0.mul_mem (M.T0.mul_mem hg (hAT hw)) (M.T0.inv_mem hg)
  simpa [mul_assoc] using h3

theorem exists_member (hO2 : pCoreOf 2 (⊤ : Subgroup G) = ⊥) {z : G} (hz : M.code z = z0c)
    {A : Subgroup G} (hAT : A ≤ M.T0) (hA : IsElemAbelian 2 A) (hA4 : 4 ≤ Nat.card A) :
    ∃ g : G, A1b.conjSub g A ≤ M.T0 ∧ ∃ K : Subgroup G, IsE 1 ⊤ M.T0 (A1b.conjSub g A) K ∧
      ¬ K ≤ Subgroup.centralizer {z} := by
  have hsq : ∀ a ∈ A, a * a = 1 := fun a ha => by rw [← sq]; exact hA.2 a ha
  have hcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb =>
    Subgroup.mem_centralizer_singleton_iff.mp (le_centralizer_of_isElemAbelian hA hb ha)
  have hmem : ∀ (g x : G), x ∈ A → g * x * g⁻¹ ∈ A1b.conjSub g A := fun _ x hx => ⟨x, hx, rfl⟩
  have hTc : ∀ a ∈ A, M.code a ∈ tl := fun a ha => hAT ha
  have hKz := M.not_K0_le hz
  by_cases hI : ∃ x ∈ A, x ∈ L ∧ x ≠ 1 ∧ ∃ y ∈ A, y ∈ L ∧ y ≠ 1 ∧ x ≠ y
  · obtain ⟨x, hxA, hxL, hx1, y, hyA, hyL, hy1, hxy⟩ := hI
    obtain ⟨e, -, -, -, hg, hx', hy', hgx, hgy, hcov, hnq⟩ := caseA_check _ (hTc x hxA) _
      (hTc y hyA) ((M.mem_iff_code x).mp hxL) ((M.mem_iff_code y).mp hyL) (M.code_ne_cone hx1)
      (M.code_ne_cone hy1) (fun h => hxy (M.code_inj h)) (M.code_sq (hsq x hxA))
      (M.code_sq (hsq y hyA)) (M.code_comm (hcomm x hxA y hyA))
    obtain ⟨g, hgT, hgc⟩ := M.exists_mem tl_facts hg
    obtain ⟨x', -, hx'c⟩ := M.exists_mem tl_facts hx'
    obtain ⟨y', -, hy'c⟩ := M.exists_mem tl_facts hy'
    have h1 : g * x * g⁻¹ = x' := M.conj_eq_of_code (by rw [hgc, hx'c]; exact hgx)
    have h2 : g * y * g⁻¹ = y' := M.conj_eq_of_code (by rw [hgc, hy'c]; exact hgy)
    have hAT' := M.conjSub_le_T0 hgT hAT
    refine ⟨g, hAT', M.K0, M.isE_K0 hO2 hAT' (isElemAbelian_conjSub hA g)
      (h1 ▸ hmem g x hxA) (h2 ▸ hmem g y hyA) ?_ ?_, hKz⟩
    · rw [hx'c, hy'c]
      exact hcov
    · rw [hx'c, hy'c]
      exact hnq
  push Not at hI
  obtain ⟨x₁, hx₁A, hx₁1, -⟩ := SecU1.exists_mem_ne_ne (by omega : 3 ≤ Nat.card A) 1 1
  obtain ⟨x₂, hx₂A, hx₂1, hx₂x₁⟩ := SecU1.exists_mem_ne_ne (by omega : 3 ≤ Nat.card A) 1 x₁
  have hout : ∀ t : G, t ∉ L → (M.code t).2 = true := fun t ht => by
    have h := (M.mem_iff_code t).not.mp ht
    simpa using h
  have hpair : ∀ t₁ t₂ : G, t₁ ∉ L → t₂ ∉ L → t₁ * t₂ ∈ L := fun t₁ t₂ h₁ h₂ => by
    rw [M.mem_iff_code, code_mul]
    simp [cmul, hout t₁ h₁, hout t₂ h₂]
  have hinv : ∀ x ∈ A, x⁻¹ = x := fun x hx => inv_eq_of_mul_eq_one_left (hsq x hx)
  obtain ⟨v, hvA, hvL, hv1⟩ : ∃ v ∈ A, v ∈ L ∧ v ≠ 1 := by
    by_cases h₁ : x₁ ∈ L
    · exact ⟨x₁, hx₁A, h₁, hx₁1⟩
    by_cases h₂ : x₂ ∈ L
    · exact ⟨x₂, hx₂A, h₂, hx₂1⟩
    refine ⟨x₁ * x₂, A.mul_mem hx₁A hx₂A, hpair _ _ h₁ h₂, fun e => hx₂x₁ ?_⟩
    calc x₂ = x₁⁻¹ * (x₁ * x₂) := by group
      _ = x₁ := by rw [e, mul_one, hinv x₁ hx₁A]
  obtain ⟨b, hbA, hbL⟩ : ∃ b ∈ A, b ∉ L := by
    by_contra hcon
    push Not at hcon
    exact hx₂x₁ (hI x₂ hx₂A (hcon x₂ hx₂A) hx₂1 x₁ hx₁A (hcon x₁ hx₁A) hx₁1)
  have hA4' : ∀ x ∈ A, x = 1 ∨ x = v ∨ x = b ∨ x = v * b := by
    intro x hx
    by_cases hx1 : x = 1
    · exact Or.inl hx1
    by_cases hxL : x ∈ L
    · exact Or.inr (Or.inl (hI x hx hxL hx1 v hvA hvL hv1))
    have hxb : x * b ∈ L := hpair x b hxL hbL
    have hxe : x = x * b * b := by rw [mul_assoc, hsq b hbA, mul_one]
    by_cases hxb1 : x * b = 1
    · exact Or.inr (Or.inr (Or.inl (by rw [hxe, hxb1, one_mul])))
    · exact Or.inr (Or.inr (Or.inr (by
        rw [hxe, hI (x * b) (A.mul_mem hx hbA) hxb hxb1 v hvA hvL hv1])))
  obtain ⟨e, -, -, -, hgv, hgn, hv', hb', hw', hcv, hcb, hcw, hcov, hnq⟩ := caseB_check _
    (hTc v hvA) _ (hTc b hbA) ((M.mem_iff_code v).mp hvL) (hout b hbL) (M.code_ne_cone hv1)
    (M.code_sq (hsq v hvA)) (M.code_sq (hsq b hbA)) (M.code_comm (hcomm v hvA b hbA))
  obtain ⟨g, hgc⟩ := M.exists_code (mem_nL.mpr ⟨hgv, hgn⟩)
  obtain ⟨v', hv'T, hv'c⟩ := M.exists_mem tl_facts hv'
  obtain ⟨b', hb'T, hb'c⟩ := M.exists_mem tl_facts hb'
  obtain ⟨w', hw'T, hw'c⟩ := M.exists_mem tl_facts hw'
  have h1 : g * v * g⁻¹ = v' := M.conj_eq_of_code (by rw [hgc, hv'c]; exact hcv)
  have h2 : g * b * g⁻¹ = b' := M.conj_eq_of_code (by rw [hgc, hb'c]; exact hcb)
  have h3 : g * (v * b) * g⁻¹ = w' := M.conj_eq_of_code (by rw [hgc, hw'c, code_mul]; exact hcw)
  have hAT' : A1b.conjSub g A ≤ M.T0 := by
    intro w hw
    rw [A1b.mem_conjSub_iff] at hw
    have hwe : w = g * (g⁻¹ * w * g) * g⁻¹ := by group
    rcases hA4' _ hw with h | h | h | h <;> rw [h] at hwe <;> rw [hwe]
    · rw [mul_one, mul_inv_cancel]
      exact M.T0.one_mem
    · rw [h1]
      exact hv'T
    · rw [h2]
      exact hb'T
    · rw [h3]
      exact hw'T
  refine ⟨g, hAT', M.K0, M.isE_K0 hO2 hAT' (isElemAbelian_conjSub hA g)
    (h1 ▸ hmem g v hvA) (h2 ▸ hmem g b hbA) ?_ ?_, hKz⟩
  · rw [hv'c, hb'c]
    exact hcov
  · rw [hv'c, hb'c]
    exact hnq

end Model

end CFSG.Quasithin.Vol2.Ch11.SecU1.L33
