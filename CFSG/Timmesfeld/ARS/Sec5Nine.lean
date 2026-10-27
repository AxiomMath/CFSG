module

public import CFSG.Timmesfeld.ARS.Sec5Conj
public import CFSG.Timmesfeld.ARS.Sec5Seven

public section

namespace CFSG.Timmesfeld.ARS

open scoped commutatorElement

variable {G : Type*} [Group G] {R : Set (Subgroup G)}

namespace Sec5

theorem opposite_of_conjSub (hR : IsRootClass R) {A D : Subgroup G} (hA : A ∈ R) (hD : D ∈ R)
    {d : G} (hd : d ∈ D) (hne : conjSub A d ≠ A) (hnc : ¬ Commuting A (conjSub A d)) :
    Opposite A D := by
  have hAD : A ≠ D := fun e => hne (conjSub_of_mem (e ▸ hd))
  rcases hR.rel A hA D hD hAD with h | h | h
  · exact absurd (conjSub_of_forall_commute fun x hx => (h x hx d hd).symm) hne
  · exact h
  · exact absurd (commuting_conjSub_of_special hR hA h hd) hnc

section Nine

variable [Finite G] (hR : IsRootClass R) (hiso : NoIsolated R) (hnd : IsNondegenerate R)
  (hΩ : ∀ A ∈ R, ∀ B ∈ R, omegaSet R B = omegaSet R A → B = A) {Δ : Set (Subgroup G)}
include hR hiso hnd hΩ

theorem exists_opposite_of_forall_not_commuting (hΔ : IsWeakTI R Δ) {E : Subgroup G}
    (hE : E ∈ R) (hEΔ : ∀ D ∈ Δ, ¬ Commuting E D) : ∃ A ∈ Δ, Opposite A E := by
  by_contra! hno
  have hsp : ∀ D ∈ Δ, Special R D E := by
    intro D hD
    have hne : D ≠ E := fun e => hEΔ D hD (e ▸ hR.commuting_self (hΔ.1 hD))
    rcases hR.rel D (hΔ.1 hD) E hE hne with h | h | h
    · exact absurd h.symm (hEΔ D hD)
    · exact absurd h (hno D hD)
    · exact h
  obtain ⟨P, hP, -⟩ := hΔ.2.1
  have hPR := hΔ.1 hP
  have hPE := hsp P hP
  have hP'R : ⁅P, E⁆ ∈ R := hPE.1
  have hlam := mem_lambdaSet_commutator hR hiso hPR hE hPE
  have hP'l : ⁅P, E⁆ ∈ lambdaSet R P := mem_lambdaSet_comm hP'R hlam.1
  have hP'E : Commuting ⁅P, E⁆ E := hPE.2.2
  have hP'Δ : ⁅P, E⁆ ∉ Δ := fun h => hEΔ _ h hP'E.symm
  obtain ⟨Q, hQ, hQs, hQP⟩ := exists_special hR hiso hnd hΩ hΔ hP hP'l hP'Δ
  have hQR := hΔ.1 hQ
  have hQE := hsp Q hQ
  obtain ⟨q, hq, hq1⟩ := hR.exists_ne_one hQR
  obtain ⟨e, he, he1⟩ := hR.exists_ne_one hE
  obtain ⟨p', hp', hp'1⟩ := hR.exists_ne_one hP'R
  have hep' : e * p' ∈ rootElts R := by
    have hl : ⁅P, E⁆ ∈ lambdaSet R E := mem_lambdaSet_comm hP'R hlam.2
    have hne : e * p' ≠ 1 := by
      intro h1
      have hmem : e ∈ E ⊓ ⁅P, E⁆ :=
        ⟨he, by rw [eq_inv_of_mul_eq_one_left h1]; exact Subgroup.inv_mem _ hp'⟩
      rw [inf_eq_bot hR hiso hE hP'R hl.1.2.1.symm, Subgroup.mem_bot] at hmem
      exact he1 hmem
    obtain ⟨F, hF, -, hF'⟩ :=
      hl.2 _ (Subgroup.mul_mem _ (Subgroup.mem_sup_left he) (Subgroup.mem_sup_right hp')) hne
    exact ⟨F, hF, hF', hne⟩
  have key := commutator_conjSub_eq hR hiso hE hQR hP'R hQE.symm hQs hP'E.symm he he1 hp' hp'1
    hep' hq hq1
  have h1 : ⁅E, conjSub ⁅P, E⁆ q⁆ = ⁅P, E⁆ := by
    rw [commutator_conjSub_right_eq hR hiso hQR hP'R hQs hq hq1 hP'E.symm, hQP,
      Subgroup.commutator_comm]
  rcases commuting_or_special_conjSub hR hiso hE hQR hP'R hQE.symm hQs hP'E.symm hq hq1 with
    ⟨hX, -⟩ | ⟨-, hY⟩
  · rw [commuting_iff_commutator_eq_bot.1 hX] at h1
    exact hR.ne_bot _ hP'R h1.symm
  · apply hY.symm.ne_commutator hR
    rw [Subgroup.commutator_comm ⁅P, E⁆ (conjSub E q), ← key, h1]

theorem exists_mem_stabSet_conjSub_eq_of_commuting (hΔ : IsWeakTI R Δ)
    (hsec : ∀ P ∈ Δ, ∃ g : G, P ∈ conjSet Δ g ∧ conjSet Δ g ≠ Δ) {E E' D D' : Subgroup G}
    (hE : E ∈ R) (hEΔ : E ∉ Δ) (hD : D ∈ Δ) (hED : Commuting E D) (hE' : E' ∈ R)
    (hE'Δ : E' ∉ Δ) (hD' : D' ∈ Δ) (hE'D' : Commuting E' D') :
    ∃ r ∈ stabSet Δ, conjSub E r = E' := by
  obtain ⟨P, hP, hEl⟩ := exists_mem_lambdaSet_of_commuting hR hiso hnd hΩ hΔ hE hEΔ hD hED
  obtain ⟨P', hP', hE'l⟩ := exists_mem_lambdaSet_of_commuting hR hiso hnd hΩ hΔ hE' hE'Δ hD' hE'D'
  obtain ⟨v, hv, hvE, hvE'⟩ := exists_mem_notMem_notMem
    (not_gen_le_axis hR hiso hnd hΩ hΔ hP hEl hEΔ) (not_gen_le_axis hR hiso hnd hΩ hΔ hP' hE'l hE'Δ)
  have hv1 : v ≠ 1 := fun h => hvE (h ▸ Subgroup.one_mem _)
  obtain ⟨P'', hP'', -, hvP''⟩ := exists_mem_le_of_mem_gen hR hiso hnd hΩ hΔ subset_rfl hv hv1
  have hP''E : ¬ Commuting P'' E := fun h => hvE ((le_axis_iff hP'').2 h hvP'')
  have hP''E' : ¬ Commuting P'' E' := fun h => hvE' ((le_axis_iff hP'').2 h hvP'')
  have hPP'' : P ≠ P'' := fun e => hP''E (e ▸ hEl.1.2.2)
  have hP'P'' : P' ≠ P'' := fun e => hP''E' (e ▸ hE'l.1.2.2)
  obtain ⟨g, hP''g, hg⟩ := hsec P'' hP''
  have hΔ'' := isWeakTI_conjSet hR hΔ g
  have hint : ∀ X ∈ Δ, X ∈ conjSet Δ g → X = P'' := fun X hX hXg => by
    by_contra hXP
    exact hg (eq_of_mem_of_mem hR hiso hnd hΩ hΔ hΔ'' (card_conjSet Δ g) hP'' hP''g hX hXg
      (Ne.symm hXP))
  have hPl : P ∈ lambdaSet R P'' :=
    mem_lambdaSet hR hiso hnd hΩ hΔ hP'' hP (Ne.symm hPP'')
  have hP'l : P' ∈ lambdaSet R P'' :=
    mem_lambdaSet hR hiso hnd hΩ hΔ hP'' hP' (Ne.symm hP'P'')
  have hPΔ'' : P ∉ conjSet Δ g := fun h => hPP'' (hint P hP h)
  have hP'Δ'' : P' ∉ conjSet Δ g := fun h => hP'P'' (hint P' hP' h)
  obtain ⟨w, hw, hwP, hwP'⟩ := exists_mem_notMem_notMem
    (not_gen_le_axis hR hiso hnd hΩ hΔ'' hP''g hPl hPΔ'')
    (not_gen_le_axis hR hiso hnd hΩ hΔ'' hP''g hP'l hP'Δ'')
  have hw1 : w ≠ 1 := fun h => hwP (h ▸ Subgroup.one_mem _)
  obtain ⟨E'', hE'', -, hwE''⟩ := exists_mem_le_of_mem_gen hR hiso hnd hΩ hΔ'' subset_rfl hw hw1
  have hE''P : ¬ Commuting E'' P := fun h => hwP ((le_axis_iff hE'').2 h hwE'')
  have hE''P' : ¬ Commuting E'' P' := fun h => hwP' ((le_axis_iff hE'').2 h hwE'')
  have hE''P'' : E'' ≠ P'' := fun e => hE''P (e ▸ hPl.1.2.2)
  obtain ⟨hE''l, hE''Δ⟩ := mem_lambdaSet_notMem hR hiso hnd hΩ hΔ'' hint hP''g hE'' hE''P''
  have h1 : Opposite E E'' := opposite_of_centre hR hiso hnd hΩ hΔ hP hP'' hPP'' hEl hEΔ hE''l
    hE''Δ (fun h => hE''P h.symm) hP''E
  have h2 : Opposite E'' E' := (opposite_of_centre hR hiso hnd hΩ hΔ hP' hP'' hP'P'' hE'l hE'Δ
    hE''l hE''Δ (fun h => hE''P' h.symm) hP''E').symm
  have hE''s : E'' ≤ stabSet Δ :=
    le_stabSet_of_commuting hR hΔ hE''l.1.1 hP'' hE''l.1.2.2.symm
  have hEs : E ≤ stabSet Δ := le_stabSet_of_commuting hR hΔ hE hP hEl.1.2.2.symm
  have hE's : E' ≤ stabSet Δ := le_stabSet_of_commuting hR hΔ hE' hP' hE'l.1.2.2.symm
  obtain ⟨-, -, -, w₁, -, -, hw₁, hEw₁, -⟩ := exists_swap hR hE hE''l.1.1 h1
  obtain ⟨-, -, -, w₂, -, -, hw₂, hEw₂, -⟩ := exists_swap hR hE''l.1.1 hE' h2
  refine ⟨w₂ * w₁, Subgroup.mul_mem _ (sup_le hE''s hE's hw₂) (sup_le hEs hE''s hw₁), ?_⟩
  rw [conjSub_mul, hEw₁, hEw₂]

theorem mem_conjSet_of_mem_lambdaSet (hΔ : IsWeakTI R Δ)
    (hsec : ∀ P ∈ Δ, ∃ g : G, P ∈ conjSet Δ g ∧ conjSet Δ g ≠ Δ)
    (h2 : ∀ (X : Subgroup G) (g₁ g₂ g₃ : G), X ∈ conjSet Δ g₁ → X ∈ conjSet Δ g₂ →
      X ∈ conjSet Δ g₃ → conjSet Δ g₁ = conjSet Δ g₂ ∨ conjSet Δ g₁ = conjSet Δ g₃ ∨
        conjSet Δ g₂ = conjSet Δ g₃)
    {B E : Subgroup G} (hB : B ∈ Δ) (hE : E ∈ lambdaSet R B) (hEΔ : E ∉ Δ) {g : G}
    (hBg : B ∈ conjSet Δ g) (hg : conjSet Δ g ≠ Δ) : E ∈ conjSet Δ g := by
  have hΔg := isWeakTI_conjSet hR hΔ g
  have hint : ∀ X ∈ Δ, X ∈ conjSet Δ g → X = B := fun X hX hXg => by
    by_contra hXB
    exact hg (eq_of_mem_of_mem hR hiso hnd hΩ hΔ hΔg (card_conjSet Δ g) hB hBg hX hXg
      (Ne.symm hXB))
  obtain ⟨F, hF, hFB⟩ : ∃ F ∈ conjSet Δ g, F ≠ B := by
    obtain ⟨X, hX, Y, hY, hXY⟩ := hΔg.2.1
    by_cases h : X = B
    · exact ⟨Y, hY, fun e => hXY (h.trans e.symm)⟩
    · exact ⟨X, hX, h⟩
  obtain ⟨hFl, hFΔ⟩ := mem_lambdaSet_notMem hR hiso hnd hΩ hΔg hint hBg hF hFB
  obtain ⟨r, hr, hFr⟩ := exists_mem_stabSet_conjSub_eq_of_commuting hR hiso hnd hΩ hΔ hsec
    hFl.1.1 hFΔ hB hFl.1.2.2.symm hE.1.1 hEΔ hB hE.1.2.2.symm
  have hBr : conjSub B r = B := by
    have hV : conjSub (gen Δ) r = gen Δ := by rw [conjSub_gen, mem_stabSet.1 hr]
    calc conjSub B r = conjSub ⁅gen Δ, F⁆ r := by
          rw [commutator_gen_eq hR hiso hnd hΩ hΔ hB hFl hFΔ]
      _ = ⁅conjSub (gen Δ) r, conjSub F r⁆ := Subgroup.map_commutator _ _ _
      _ = ⁅gen Δ, E⁆ := by rw [hV, hFr]
      _ = B := commutator_gen_eq hR hiso hnd hΩ hΔ hB hE hEΔ
  have hB' : B ∈ conjSet Δ (r * g) := by
    rw [conjSet_mul, ← hBr]
    exact conjSub_mem_conjSet hBg r
  have hE' : E ∈ conjSet Δ (r * g) := by
    rw [conjSet_mul, ← hFr]
    exact conjSub_mem_conjSet hF r
  rcases h2 B 1 g (r * g) (by rw [conjSet_one]; exact hB) hBg hB' with h | h | h
  · rw [conjSet_one] at h
    exact absurd h.symm hg
  · rw [conjSet_one] at h
    exact absurd (h ▸ hE') hEΔ
  · exact h ▸ hE'

end Nine

end Sec5

end CFSG.Timmesfeld.ARS
