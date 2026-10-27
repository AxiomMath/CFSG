module

public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec5.Thm51
public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec5.RF10

public section

open CFSG.Open

universe u

namespace CFSG.SignalizerFunctorTheorem.McBride.Near

namespace Counterexample

variable {p : ℕ} {G : Type u} [Group G] [Finite G] {A : Subgroup G} {θ : G → Subgroup G}

theorem exists_not_kOf_le (h : Counterexample p A θ) {X : Subgroup G}
    (hX : X ∈ assoc p A θ) : ∃ a ∈ A, a ≠ 1 ∧ ¬ kOf (θ a) ≤ X := by
  by_contra hcon
  push Not at hcon
  have hp := h.hyp.prime
  have hA := h.hyp.elemAbelian
  have hθ := h.hyp.isFunctor
  have hP := h.hyp.near
  have hrank3 : p ^ 3 ≤ Nat.card A := h.hyp.card.ge
  have hrank2 : p ^ 2 ≤ Nat.card A := (Nat.pow_le_pow_right hp.pos (by norm_num)).trans hrank3
  obtain ⟨hAX, hcopX, hXθ, hnearX⟩ := mem_assoc_iff.mp hX
  by_cases hXbot : X = ⊥
  · refine h.notComplete ((isCompleteIn_iff_exists_apply_le hp hA hrank2 hθ hP).mpr
      ⟨X, hX, fun a ha ha1 => ?_⟩)
    have hθa : θ a = ⊥ := by
      by_contra hne
      exact Thm52Aux.kOf_ne_bot hne (le_bot_iff.mp (hXbot ▸ hcon a ha ha1))
    rw [hθa]
    exact bot_le
  have hKX : kOf X ≠ ⊥ := Thm52Aux.kOf_ne_bot hXbot
  have hAK : Admits A (kOf X) := hAX.trans (Thm52Aux.normalizer_le_normalizer_kOf X)
  have hcopK : Nat.Coprime p (Nat.card (kOf X)) :=
    hcopX.coprime_dvd_right (Subgroup.card_dvd_of_le (kOf_le X))
  have hKmem : kOf X ∈ assoc p A θ := mem_assoc_of_le hp hX (kOf_le X) hAK
  have hCb : ∀ b ∈ A, b ≠ 1 → cenIn (kOf X) {b} ≤ kOf (θ b) := by
    intro b hb hb1
    have h1 := cenIn_kOf_le_kOf_cenIn hp hA hAX hnearX.1 hb hb1
    have hle : kOf (θ b) ≤ cenIn X {b} :=
      le_inf (hcon b hb hb1) ((kOf_le _).trans (hθ.le_centralizer b hb hb1))
    have heq : kOf (cenIn X {b}) = kOf (θ b) := kOf_eq_of_kOf_le (hXθ b hb hb1) hle
    exact heq ▸ h1
  have hnormB : ∀ B ∈ signalizerFunctorEk p 2 A,
      thetaOf θ B ≤ Subgroup.normalizer (kOf X : Set G) := by
    intro B hB
    set W : Subgroup G := ⨆ (b : G) (_ : b ∈ B) (_ : b ≠ 1), kOf (θ b) with hW
    have hBel : IsElemAbelian p B :=
      CFSG.SignalizerFunctor.Helpers.elementary_abelian_of_le p hA hB.1
    have hKW : kOf X ≤ W := by
      refine (iSup_inf_centralizer hp hBel hB.2.ge (hB.1.trans hAK) hcopK).symm.le.trans ?_
      refine iSup_le fun b => iSup_le fun hb => iSup_le fun hb1 => ?_
      exact (hCb b (hB.1 hb) hb1).trans (le_iSup₂_of_le b hb (le_iSup_of_le hb1 le_rfl))
    have hWX : W ≤ X :=
      iSup_le fun b => iSup_le fun hb => iSup_le fun hb1 => hcon b (hB.1 hb) hb1
    have hkW : kOf W = kOf X := kOf_eq_of_kOf_le hWX hKW
    have hnormW : thetaOf θ B ≤ Subgroup.normalizer (W : Set G) := by
      refine Thm52Aux.le_normalizer_iSup _ fun b => Thm52Aux.le_normalizer_iSup _ fun hb =>
        Thm52Aux.le_normalizer_iSup _ fun hb1 => ?_
      exact (thetaOf_le_apply hb hb1).trans (Thm52Aux.le_normalizer_kOf (θ b))
    exact hkW ▸ hnormW.trans (Thm52Aux.normalizer_le_normalizer_kOf W)
  have hnorm : ∀ b ∈ A, b ≠ 1 → θ b ≤ Subgroup.normalizer (kOf X : Set G) := by
    intro b hb hb1
    rw [hθ.apply_eq_iSup_thetaOf hp hA hrank3 hb hb1]
    exact iSup_le fun B => iSup_le fun hBA => iSup_le fun hBc => iSup_le fun _ =>
      hnormB B ⟨hBA, hBc⟩
  exact h.notComplete (isCompleteIn_of_isLocallyCompleteIn hp hA hθ hP h.isLocallyComplete hKmem
    hKX le_rfl hrank2 hnorm)

theorem exists_not_kOf_le_thetaOf
    (h : Counterexample p A θ) {X : Subgroup G}
    (hX : X ∈ assoc p A θ) :
    ∃ B ∈ signalizerFunctorEk p 2 A, ¬ kOf (thetaOf θ B) ≤ X := by
  by_contra hcon
  push Not at hcon
  obtain ⟨a, ha, ha1, hnot⟩ := h.exists_not_kOf_le hX
  refine hnot ?_
  have hp := h.hyp.prime
  have hA := h.hyp.elemAbelian
  have hθ := h.hyp.isFunctor
  have hrank3 : p ^ 3 ≤ Nat.card A := h.hyp.card.ge
  have hza : Subgroup.zpowers a ∈ signalizerFunctorEk p 1 A :=
    zpowers_mem_signalizerFunctorEk_one hp hA ha ha1
  have hAK : Admits A (kOf (θ a)) :=
    (hθ.normalized a ha ha1).trans (Thm52Aux.normalizer_le_normalizer_kOf _)
  have hcopK : Nat.Coprime p (Nat.card (kOf (θ a))) :=
    (hθ.coprime a ha ha1).coprime_dvd_right (Subgroup.card_dvd_of_le (kOf_le _))
  have hrank : p ^ 2 * Nat.card (Subgroup.zpowers a) ≤ Nat.card A := by
    rw [hza.2, pow_one, ← pow_succ]
    exact hrank3
  rw [← iSup_inf_centralizer_sdiff hp hA hza.1 hrank hAK hcopK]
  refine iSup_le fun b => iSup_le fun hb => iSup_le fun hbE => ?_
  have hb1 : b ≠ 1 := fun h1 => hbE (h1 ▸ one_mem _)
  have hzb := zpowers_mem_signalizerFunctorEk_one hp hA hb hb1
  have hdisj : Subgroup.zpowers a ⊓ Subgroup.zpowers b = ⊥ :=
    CFSG.SignalizerFunctorTheorem.inf_eq_bot_of_not_le hp (by rw [hzb.2, pow_one])
      (fun hle => hbE (hle (Subgroup.mem_zpowers b)))
  have hB : Subgroup.zpowers a ⊔ Subgroup.zpowers b ∈ signalizerFunctorEk p 2 A := by
    simpa using CFSG.SignalizerFunctorTheorem.sup_mem_Ek_succ hA hza hzb hdisj
  exact (kOf_apply_inf_centralizer_le h.hyp.nearFunctor ha ha1 hb hb1).trans (hcon _ hB)

end Counterexample

end CFSG.SignalizerFunctorTheorem.McBride.Near
