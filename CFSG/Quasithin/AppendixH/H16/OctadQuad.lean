module

public import CFSG.Quasithin.AppendixH.H16.OctadBetaMask

public section

open scoped Pointwise

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.ASVolI.H16

open CFSG.ASVolI.ChH CFSG.Quasithin CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H.Mathieu.H16Pf
  CFSG.Quasithin.H.ModChk CFSG.Quasithin.H.Coc CFSG.Quasithin.H.FixSyl CFSG.Quasithin.H.LU24
  CFSG.Monster.Code CFSG.ASVolI.AppH CFSG.Quasithin.H156

@[expose] def wtO (c : Fin 24 → ZMod 2) : ℕ :=
  (Finset.univ.filter fun i : Fin 24 => (i : ℕ) < 8 ∧ c i ≠ 0).card

private theorem mem_octad0_iff' {i : Fin 24} : i ∈ octad0 ↔ (i : ℕ) < 8 := by
  simp [octad0]

private theorem zmod2_add_one_ne_zero_iff : ∀ a : ZMod 2, a + 1 ≠ 0 ↔ ¬ (a ≠ 0) := by decide

private theorem card_filter_not {α : Type*} [DecidableEq α] (A : Finset α) (p : α → Prop)
    [DecidablePred p] : (A.filter fun x => ¬ p x).card = A.card - (A.filter p).card := by
  rw [Finset.filter_not, Finset.card_sdiff, Finset.inter_eq_left.2 (Finset.filter_subset p A)]

private theorem div_two_mod_two_of (w w' : ℕ) (hw : w ≤ 8) (he : w % 2 = 0)
    (h : w' = w ∨ w' = 8 - w) : w' / 2 % 2 = w / 2 % 2 := by
  rcases h with rfl | rfl
  · rfl
  · interval_cases w <;> simp_all <;> decide

theorem wtO_le (c : Fin 24 → ZMod 2) : wtO c ≤ 8 := by
  unfold wtO
  calc (Finset.univ.filter fun i : Fin 24 => (i : ℕ) < 8 ∧ c i ≠ 0).card
      ≤ (Finset.univ.filter fun i : Fin 24 => (i : ℕ) < 8).card := by
        apply Finset.card_le_card
        intro i hi
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
        exact hi.1
    _ = 8 := by decide

theorem wtO_bvec (c : ℕ) : wtO (bvec 24 c) = popc 8 c := by
  rw [← hammingNorm_bvec 8 c]
  unfold wtO hammingNorm
  symm
  refine Finset.card_bij (fun j (_ : j ∈ Finset.univ.filter fun j : Fin 8 => bvec 8 c j ≠ 0) =>
      (⟨j, by omega⟩ : Fin 24)) ?_ ?_ ?_
  · intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
    exact ⟨j.2, hj⟩
  · intro j₁ _ j₂ _ h
    exact Fin.ext (congrArg (fun x : Fin 24 => x.val) h)
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
    exact ⟨⟨i, hi.1⟩, by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact hi.2, rfl⟩

theorem lt_eight_iff_of_mem_octStab {γ : S24} (hγ : γ ∈ octStab octad0) (i : Fin 24) :
    ((γ i : Fin 24) : ℕ) < 8 ↔ (i : ℕ) < 8 := by
  have hfix : γ • octad0 = octad0 := (mem_octStab_iff.1 hγ).2
  have h : γ i ∈ γ • octad0 ↔ i ∈ octad0 := by
    rw [smul_finset_eq_map, Finset.mem_map_equiv]
    simp
  rw [← mem_octad0_iff' (i := γ i), ← hfix, h]
  exact mem_octad0_iff'

theorem wtO_permAct {γ : S24} (hγ : ∀ i : Fin 24, ((γ i : Fin 24) : ℕ) < 8 ↔ (i : ℕ) < 8)
    (x : G6.PermMod 24) :
    wtO (Multiplicative.toAdd (G6.permAct 24 γ x)) = wtO (Multiplicative.toAdd x) := by
  unfold wtO
  apply Finset.card_bij (fun i _ => γ⁻¹ i)
  · intro i hi
    have hmem : (i : ℕ) < 8 ∧ Multiplicative.toAdd (G6.permAct 24 γ x) i ≠ 0 := by
      simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨(hγ (γ⁻¹ i)).mp (by simpa using hmem.1),
      by simpa only [G6.permAct_apply] using hmem.2⟩
  · intro i₁ _ i₂ _ h
    exact (γ⁻¹).injective h
  · intro i hi
    have hmem : (i : ℕ) < 8 ∧ Multiplicative.toAdd x i ≠ 0 := by
      simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hi
    refine ⟨γ i, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨(hγ i).mpr hmem.1, by simpa [G6.permAct_apply] using hmem.2⟩
    · simp

theorem wtO_add_allOnes (c : Fin 24 → ZMod 2) : wtO (c + Ω) = 8 - wtO c := by
  have hAcard : (Finset.univ.filter fun i : Fin 24 => (i : ℕ) < 8).card = 8 := by decide
  have hc : wtO c =
      ((Finset.univ.filter fun i : Fin 24 => (i : ℕ) < 8).filter fun i => c i ≠ 0).card := by
    rw [wtO, ← Finset.filter_filter]
  have hc' : wtO (c + Ω) =
      ((Finset.univ.filter fun i : Fin 24 => (i : ℕ) < 8).filter fun i => ¬ (c i ≠ 0)).card := by
    rw [wtO, ← Finset.filter_filter]
    congr 1
    apply Finset.filter_congr
    intro i _
    simp only [Pi.add_apply, Ω, Pi.one_apply]
    exact zmod2_add_one_ne_zero_iff (c i)
  rw [hc, hc', card_filter_not, hAcard]

theorem wtO_liftC_even (w : Fin 11 → ZMod 2) : wtO (liftC w) % 2 = 0 := by
  obtain ⟨m, hm, hmw⟩ := toW_surj 11 (Multiplicative.ofAdd w)
  have hw : w = bvec 11 m := by
    have h1 : Multiplicative.toAdd (toW 11 m) = w := by
      simpa using congrArg Multiplicative.toAdd hmw
    rw [toAdd_toW] at h1
    exact h1.symm
  rw [hw, liftC_bvec, wtO_bvec]
  exact octWeight_even_masks m hm

@[expose] noncomputable def octQ (x : W11) : ZMod 2 :=
  ((wtO (liftC (Multiplicative.toAdd x)) / 2 : ℕ) : ZMod 2)

theorem octQ_toW (m : ℕ) : octQ (toW 11 m) = (octQmask (actM liftCCols m) : ZMod 2) := by
  unfold octQ octQmask
  rw [toAdd_toW, liftC_bvec, wtO_bvec]
  rw [ZMod.natCast_mod (popc 8 (actM liftCCols m) / 2) 2]

theorem qPlus6_octBeta (x : W11) : qPlus6 (Multiplicative.toAdd (octBeta x)) = octQ x := by
  obtain ⟨m, hm, rfl⟩ := toW_surj 11 x
  rw [octBeta_toW, qPlus6_toW, octBeta_q_masks m hm, ← octQ_toW]

theorem octQ_rhoC11 (γ : ↥AutPerm) (hγ : (γ : S24) ∈ octStab octad0) (x : W11) :
    octQ (rhoC11 AutPerm le_rfl γ x) = octQ x := by
  set c : Fin 24 → ZMod 2 := liftC (Multiplicative.toAdd x) with hc
  set c₂ : Fin 24 → ZMod 2 :=
    Multiplicative.toAdd (G6.permAct 24 (γ : S24) (Multiplicative.ofAdd c)) with hc₂
  set c' : Fin 24 → ZMod 2 := liftC (κC c₂) with hc'
  have hrho : rhoC11 AutPerm le_rfl γ x = Multiplicative.ofAdd (κC c₂) := by
    rw [hc₂, hc]
    rfl
  have hL : octQ (Multiplicative.ofAdd (κC c₂)) = ((wtO c' / 2 : ℕ) : ZMod 2) := by
    rw [octQ, toAdd_ofAdd, ← hc']
  have hR : octQ x = ((wtO c / 2 : ℕ) : ZMod 2) := by
    rw [octQ, ← hc]
  rw [hrho, hL, hR]
  have hcC : c ∈ C := by rw [hc]; exact liftC_mem _
  have hc₂C : c₂ ∈ C := by
    rw [hc₂]
    have hmem : Multiplicative.ofAdd c ∈ golayC := (mem_golayC_iff _).2 (by simpa using hcC)
    exact (mem_golayC_iff _).1 ((preserves_code γ.2).1 _ hmem)
  have hc'C : c' ∈ C := by rw [hc']; exact liftC_mem _
  have hsub : c' - c₂ ∈ C := C.sub_mem hc'C hc₂C
  have hker : κC (c' - c₂) = 0 := by
    rw [hc', map_sub, κC_liftC, sub_self]
  have hperm : wtO c₂ = wtO c := by
    rw [hc₂]
    have := wtO_permAct (lt_eight_iff_of_mem_octStab hγ) (Multiplicative.ofAdd c)
    simpa using this
  have heven : wtO c % 2 = 0 := by
    rw [hc]
    exact wtO_liftC_even (Multiplicative.toAdd x)
  have hle : wtO c ≤ 8 := wtO_le c
  have hmod : wtO c' / 2 % 2 = wtO c / 2 % 2 := by
    rcases (κC_eq_zero_iff hsub).1 hker with h0 | hΩ
    · rw [sub_eq_zero.1 h0, hperm]
    · have hc'eq : c' = c₂ + Ω := by
        rw [add_comm c₂ Ω]
        exact sub_eq_iff_eq_add.1 hΩ
      rw [hc'eq, wtO_add_allOnes, hperm]
      exact div_two_mod_two_of (wtO c) (8 - wtO c) hle heven (Or.inr rfl)
  rw [← ZMod.natCast_mod (wtO c' / 2) 2, ← ZMod.natCast_mod (wtO c / 2) 2]
  exact congrArg (fun k : ℕ => (k : ZMod 2)) hmod

theorem qPlus6_octBeta_rhoC11 (γ : ↥AutPerm) (hγ : (γ : S24) ∈ octStab octad0) (x : W11) :
    qPlus6 (Multiplicative.toAdd (octBeta (rhoC11 AutPerm le_rfl γ x))) =
      qPlus6 (Multiplicative.toAdd (octBeta x)) := by
  rw [qPlus6_octBeta, qPlus6_octBeta]
  exact octQ_rhoC11 γ hγ x

end CFSG.ASVolI.H16
