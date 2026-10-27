module

public import CFSG.LieType.Steinberg.Classical.SpecialLinearSteinberg
public import CFSG.Timmesfeld.LieEmbed.A5Roots

public noncomputable section

namespace CFSG.Timmesfeld.LieEmbed

open CFSG.Blueprint.Chevalley CFSG.LieType CFSG.LieType.Steinberg Matrix
open scoped commutatorElement

section Steinberg

variable {n : ℕ} {F : Type} [Field F] {G : Type*} [Group G]

@[expose] def stGenOf (x : Fin n → Fin n → F → G) (s : Fin n × Fin n × F) : G :=
  if s.1 = s.2.1 then 1 else x s.1 s.2.1 s.2.2

omit [Field F] in
theorem stGenOf_of_ne (x : Fin n → Fin n → F → G) {i j : Fin n} (hij : i ≠ j) (c : F) :
    stGenOf x (i, j, c) = x i j c := by
  simp [stGenOf, hij]

theorem stGenOf_rels {x : Fin n → Fin n → F → G}
    (hadd : ∀ i j : Fin n, i ≠ j → ∀ c d : F, x i j c * x i j d = x i j (c + d))
    (hcomm : ∀ i j k l : Fin n, i ≠ j → k ≠ l → ¬ (k = j ∧ l = i) → ∀ c d : F,
      ⁅x i j c, x k l d⁆ =
        if j = k then x i l (c * d) else if i = l then x k j (-(c * d)) else 1) :
    ∀ r ∈ CFSG.Open.steinbergSLRels n F, FreeGroup.lift (stGenOf x) r = 1 := by
  rintro r ((⟨i, c, rfl⟩ | ⟨i, j, c, d, hij, rfl⟩) | ⟨i, j, k, l, c, d, hij, hkl, hex, rfl⟩)
  · simp [stGenOf]
  · simp only [map_mul, map_inv, FreeGroup.lift_apply_of, stGenOf_of_ne x hij]
    rw [hadd i j hij c d, mul_inv_cancel]
  · have hc := hcomm i j k l hij hkl hex c d
    simp only [map_mul, map_inv, FreeGroup.lift_apply_of, stGenOf_of_ne x hij,
      stGenOf_of_ne x hkl]
    by_cases hjk : j = k
    · subst hjk
      have hil : i ≠ l := fun h => hex ⟨rfl, h.symm⟩
      rw [ite_eq_left rfl] at hc ⊢
      rw [FreeGroup.lift_apply_of, stGenOf_of_ne x hil, ← hc, commutatorElement_def,
        mul_inv_cancel]
    · rw [ite_eq_right hjk] at hc ⊢
      by_cases hil : i = l
      · subst hil
        rw [ite_eq_left rfl] at hc ⊢
        have hkj : k ≠ j := fun h => hjk h.symm
        rw [FreeGroup.lift_apply_of, stGenOf_of_ne x hkj, ← hc, commutatorElement_def,
          mul_inv_cancel]
      · rw [ite_eq_right hil] at hc ⊢
        rw [map_one, inv_one, mul_one, ← commutatorElement_def, hc]

theorem exists_hom_of_steinbergRels [Finite F] {m : ℕ} (hm : 2 ≤ m)
    {x : Fin (m + 1) → Fin (m + 1) → F → G}
    (hadd : ∀ i j : Fin (m + 1), i ≠ j → ∀ c d : F, x i j c * x i j d = x i j (c + d))
    (hcomm : ∀ i j k l : Fin (m + 1), i ≠ j → k ≠ l → ¬ (k = j ∧ l = i) → ∀ c d : F,
      ⁅x i j c, x k l d⁆ =
        if j = k then x i l (c * d) else if i = l then x k j (-(c * d)) else 1) :
    ∃ ρ : SpecialLinearGroup (Fin (m + 1)) F →* G, ∀ (i j : Fin (m + 1)) (hij : i ≠ j) (c : F),
      ρ (SpecialLinearGroup.transvection hij c) = x i j c := by
  obtain ⟨φ, hφ⟩ := SL.exists_steinbergSLRels_equiv (m := m) (F := F) hm
  let ψ : PresentedGroup (CFSG.Open.steinbergSLRels (m + 1) F) →* G :=
    PresentedGroup.toGroup (stGenOf_rels hadd hcomm)
  refine ⟨ψ.comp φ.symm.toMonoidHom, fun i j hij c => ?_⟩
  have hφ' : SpecialLinearGroup.transvection hij c = φ (PresentedGroup.of (i, j, c)) := by
    apply Subtype.ext
    rw [hφ i j c hij, SpecialLinearGroup.transvection_coe]
    rfl
  rw [MonoidHom.comp_apply, hφ', MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply]
  change PresentedGroup.toGroup (stGenOf_rels hadd hcomm) (PresentedGroup.of (i, j, c)) =
    x i j c
  rw [PresentedGroup.toGroup.of, stGenOf_of_ne x hij]

end Steinberg

section E6

open Minuscule

variable {k : Type} [Field k] [CharP k 2]

theorem isSign_eq_one {σ : k} (h : IsSign σ) : σ = 1 := by
  rcases h with h | h
  · exact h
  · rw [h, CharTwo.neg_eq]

theorem a5_commutator {i j k' l : Fin 6} (hij : i ≠ j) (hkl : k' ≠ l)
    (hex : ¬ (k' = j ∧ l = i)) (c d : k) :
    ⁅e6Data_valid.xm k (a5Root i j) c, e6Data_valid.xm k (a5Root k' l) d⁆ =
      if j = k' then e6Data_valid.xm k (a5Root i l) (c * d)
      else if i = l then e6Data_valid.xm k (a5Root k' j) (-(c * d)) else 1 := by
  obtain ⟨hroot, hnot⟩ := e6Data_valid.commutator_xm k (isRoot_a5Root hij) (isRoot_a5Root hkl)
    (a5Root_add_ne_zero hij hkl hex)
  by_cases hjk : j = k'
  · subst hjk
    have hil : i ≠ l := fun h => hex ⟨rfl, h.symm⟩
    rw [ite_eq_left rfl]
    have hs : a5Root i j + a5Root j l = a5Root i l := a5Root_add i j l
    obtain ⟨σ, hσ, h⟩ := hroot (hs ▸ isRoot_a5Root hil)
    rw [h, isSign_eq_one hσ, one_mul, hs]
  · rw [ite_eq_right hjk]
    by_cases hil : i = l
    · subst hil
      rw [ite_eq_left rfl]
      have hkj : k' ≠ j := fun h => hjk h.symm
      have hs : a5Root i j + a5Root k' i = a5Root k' j := by
        rw [add_comm, a5Root_add]
      obtain ⟨σ, hσ, h⟩ := hroot (hs ▸ isRoot_a5Root hkj)
      rw [h, isSign_eq_one hσ, one_mul, hs, CharTwo.neg_eq]
    · rw [ite_eq_right hil]
      exact hnot (not_isRoot_a5Root_add hij hkl hex hjk hil) c d

variable [Finite k]

theorem exists_slToE6 : ∃ φ : SpecialLinearGroup (Fin 6) k →* e6Data_valid.minGroup k,
    ∀ (i j : Fin 6) (hij : i ≠ j) (c : k),
      φ (SpecialLinearGroup.transvection hij c) = e6Data_valid.xm k (a5Root i j) c :=
  exists_hom_of_steinbergRels (m := 5) (by norm_num)
    (x := fun i j c => e6Data_valid.xm k (a5Root i j) c)
    (fun i j _ c d => (e6Data_valid.xm_add k _ c d).symm) fun i j k' l hij hkl hex c d =>
      a5_commutator hij hkl hex c d

end E6

end CFSG.Timmesfeld.LieEmbed
