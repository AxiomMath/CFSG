module

public import CFSG.LocalAnalysis.StandardType.GGFrameModelNumB

public section

namespace CFSG.StandardType.FrameRoute

open CFSG SpCoord Multiplicative

variable {k : ℕ}

@[expose] def evenSignedPermSet (k : ℕ) : Set (MulAut (Fin k → Multiplicative (ZMod 3))) :=
  {u | ∃ (π : Equiv.Perm (Fin k)) (ε : Fin k → ZMod 3), (∀ i, ε i = 1 ∨ ε i = -1) ∧
    ∏ i, ε i = 1 ∧ ∀ f i, toAdd (u f (π i)) = ε i * toAdd (f i)}

private theorem frameMD_even_subset_signed
    {u : MulAut (Fin k → Multiplicative (ZMod 3))} (hu : u ∈ evenSignedPermSet k) :
    u ∈ signedPermSet k := by
  obtain ⟨π, ε, hε, -, hu⟩ := hu
  exact ⟨π, ε, hε, hu⟩

private theorem frameMD_modelReflSet_even_iff
    (u : MulAut (Fin k → Multiplicative (ZMod 3))) :
    u ∈ modelReflSet (evenSignedPermSet k) ↔
      u ∈ evenSignedPermSet k ∧ u ∈ modelReflSet (signedPermSet k) := by
  constructor
  · rintro ⟨hu, hsq, hcard⟩
    exact ⟨hu, ⟨frameMD_even_subset_signed hu, hsq, hcard⟩⟩
  · rintro ⟨hu, hmem⟩
    exact ⟨hu, hmem.2⟩

private theorem frameMD_sgnAut_apply_basis (i j : Fin k) :
    sgnAut i (Pi.mulSingle j (ofAdd (1 : ZMod 3))) =
      Pi.mulSingle j (ofAdd (if j = i then (-1 : ZMod 3) else 1)) := by
  by_cases h : j = i
  · subst h
    rw [sgnAut_mulSingle_self, ← Pi.mulSingle_inv, if_pos rfl]
    congr 1
  · simp [sgnAut_apply, h]
    decide

private theorem frameMD_sgnAut_not_mem_even (i0 : Fin k) :
    sgnAut i0 ∉ evenSignedPermSet k := by
  rintro ⟨π, ε, hε, hprod, hu⟩
  have hvalues : ∀ i : Fin k,
      π i = i ∧ ε i = (if i = i0 then (-1 : ZMod 3) else 1) := by
    intro i
    have happ := IsSignedPerm.apply_mulSingle (u := sgnAut i0) (π := π) (ε := ε) hu i 1
    have hleft := frameMD_sgnAut_apply_basis i0 i
    have heq : (Pi.mulSingle i (ofAdd (if i = i0 then (-1 : ZMod 3) else 1)) :
        Fin k → Multiplicative (ZMod 3)) =
        (Pi.mulSingle (π i) (ofAdd (ε i)) : Fin k → Multiplicative (ZMod 3)) := by
      rw [← hleft]
      simpa using happ
    obtain ⟨hpi, heps⟩ := mulSingle_ofAdd_eq_iff (p := 3)
      (x := (if i = i0 then (-1 : ZMod 3) else 1))
      (by
        by_cases hi : i = i0
        · rw [if_pos hi]; decide
        · rw [if_neg hi]; decide) heq
    exact ⟨hpi.symm, heps.symm⟩
  have hεi0 : ε i0 = -1 := by simpa using (hvalues i0).2
  have hεne : ∀ i : Fin k, i ≠ i0 → ε i = 1 := by
    intro i hi
    have h := (hvalues i).2
    simp [hi] at h
    exact h
  have hprod' : ∏ i, ε i = -1 := by
    rw [Finset.prod_eq_single i0]
    · exact hεi0
    · intro b _ hb
      exact hεne b hb
    · intro h
      exact absurd (Finset.mem_univ i0) h
  rw [hprod'] at hprod
  exact (by decide : (-1 : ZMod 3) ≠ 1) hprod

theorem mul_sgnAut_not_mem_evenSignedPermSet {u : MulAut (Fin k → Multiplicative (ZMod 3))}
    (hu : u ∈ evenSignedPermSet k) (i₀ : Fin k) : u * sgnAut i₀ ∉ evenSignedPermSet k := by
  obtain ⟨π, ε, hε, hprod, hu⟩ := hu
  rintro ⟨π', ε', -, hprod', hu'⟩
  have hvalues : ∀ i : Fin k, ε' i = ε i * (if i = i₀ then (-1 : ZMod 3) else 1) := by
    intro i
    have h1 := IsSignedPerm.apply_mulSingle hu' i 1
    rw [MulAut.mul_apply, frameMD_sgnAut_apply_basis, IsSignedPerm.apply_mulSingle hu] at h1
    have hx : ε i * (if i = i₀ then (-1 : ZMod 3) else 1) ≠ 0 := by
      by_cases hi : i = i₀
      · rw [if_pos hi]
        rcases hε i with h | h <;> rw [h] <;> decide
      · rw [if_neg hi]
        rcases hε i with h | h <;> rw [h] <;> decide
    obtain ⟨-, heps⟩ := mulSingle_ofAdd_eq_iff (p := 3) hx h1
    rw [heps, mul_one]
  have hsgn : ∏ i, (if i = i₀ then (-1 : ZMod 3) else 1) = -1 := by
    rw [Finset.prod_eq_single i₀ (fun b _ hb => if_neg hb)
      (fun h => absurd (Finset.mem_univ i₀) h), if_pos rfl]
  rw [Finset.prod_congr rfl fun i _ => hvalues i, Finset.prod_mul_distrib, hprod, hsgn,
    one_mul] at hprod'
  exact (by decide : (-1 : ZMod 3) ≠ 1) hprod'

private theorem frameMD_permAut_swap_mem_even (a b : Fin k) :
    permAut (Equiv.swap a b) ∈ evenSignedPermSet k := by
  refine ⟨Equiv.swap a b, fun _ => (1 : ZMod 3), fun _ => Or.inl rfl, by simp, ?_⟩
  intro f i
  simp [permAut_apply]

private theorem frameMD_negSwapAut_apply {a b : Fin k} (hab : a ≠ b)
    (f : Fin k → Multiplicative (ZMod 3)) (j : Fin k) :
    negSwapAut a b f j = if j = a then (f b)⁻¹ else if j = b then (f a)⁻¹ else f j := by
  rw [negSwapAut, MulAut.mul_apply, MulAut.mul_apply, sgnAut_apply, sgnAut_apply,
    permAut_apply]
  simp only [Function.comp_apply, Equiv.swap_inv, Function.update_apply]
  by_cases hja : j = a
  · subst hja
    simp [hab]
    rfl
  · by_cases hjb : j = b
    · subst hjb
      simp [hja, Ne.symm hab]
      rfl
    · rw [Equiv.swap_apply_of_ne_of_ne hja hjb]
      simp [hja, hjb]

section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

private theorem frameMD_negSwapAut_mem_even {a b : Fin k} (hab : a ≠ b) :
    negSwapAut a b ∈ evenSignedPermSet k := by
  refine ⟨Equiv.swap a b, fun i => if i = a ∨ i = b then (-1 : ZMod 3) else 1, ?_, ?_, ?_⟩
  · intro i
    by_cases h : i = a ∨ i = b
    · simp [h]
      exact Or.inr rfl
    · simp [h]
  · have hinner : (∏ i ∈ Finset.univ.erase a,
        (if i = a ∨ i = b then (-1 : ZMod 3) else 1)) = -1 := by
      rw [Finset.prod_eq_single b]
      · rw [if_pos (Or.inr rfl)]
      · intro c hc hcb
        have hca : c ≠ a := Finset.ne_of_mem_erase hc
        rw [if_neg (by tauto)]
      · intro hb
        exact absurd (Finset.mem_erase.mpr ⟨Ne.symm hab, Finset.mem_univ b⟩) hb
    rw [← Finset.mul_prod_erase Finset.univ
      (fun i => if i = a ∨ i = b then (-1 : ZMod 3) else 1) (Finset.mem_univ a), hinner]
    rw [if_pos (Or.inl rfl)]
    decide
  · intro f i
    dsimp only
    by_cases hia : i = a
    · subst hia
      rw [Equiv.swap_apply_left, frameMD_negSwapAut_apply hab]
      rw [if_neg (Ne.symm hab), if_pos rfl, if_pos (Or.inl rfl), toAdd_inv, neg_one_mul]
      rfl
    · by_cases hib : i = b
      · subst hib
        rw [Equiv.swap_apply_right, frameMD_negSwapAut_apply hab]
        rw [if_pos rfl, if_pos (Or.inr rfl), toAdd_inv, neg_one_mul]
        rfl
      · rw [Equiv.swap_apply_of_ne_of_ne hia hib, frameMD_negSwapAut_apply hab]
        rw [if_neg hia, if_neg hib, if_neg (by tauto), one_mul]

end

theorem mem_modelReflSet_evenSignedPermSet_iff (u : MulAut (Fin k → Multiplicative (ZMod 3))) :
    u ∈ modelReflSet (evenSignedPermSet k) ↔
      ∃ a b : Fin k, a ≠ b ∧ (u = permAut (Equiv.swap a b) ∨ u = negSwapAut a b) := by
  rw [frameMD_modelReflSet_even_iff]
  constructor
  · rintro ⟨huEven, huRefl⟩
    rcases (mem_modelReflSet_signedPermSet_iff u).mp huRefl with h | ⟨a, b, hab, h⟩
    · obtain ⟨i, rfl⟩ := h
      exact absurd huEven (frameMD_sgnAut_not_mem_even i)
    · exact ⟨a, b, hab, h⟩
  · rintro ⟨a, b, hab, rfl | rfl⟩
    · exact ⟨frameMD_permAut_swap_mem_even a b,
        (mem_modelReflSet_signedPermSet_iff _).mpr (Or.inr ⟨a, b, hab, Or.inl rfl⟩)⟩
    · exact ⟨frameMD_negSwapAut_mem_even hab,
        (mem_modelReflSet_signedPermSet_iff _).mpr (Or.inr ⟨a, b, hab, Or.inr rfl⟩)⟩

end CFSG.StandardType.FrameRoute

end
