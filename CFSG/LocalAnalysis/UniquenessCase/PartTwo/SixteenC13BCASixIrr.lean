module

public import CFSG.Quasithin.Background.F918V2F
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC13BCAFour

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin Subgroup

open scoped Pointwise

section Helpers

variable {W : Type} [CommGroup W]

private lemma s16c13bcA_smul_eq_map (x : MulAut W) (I : Subgroup W) :
    x • I = I.map x.toMonoidHom := by
  have hf : MulDistribMulAction.toMonoidEnd _ _ x = x.toMonoidHom := by
    ext y
    rfl
  rw [Subgroup.pointwise_smul_def, hf]

private lemma s16c13bcA_map_one (I : Subgroup W) :
    I.map (1 : MulAut W).toMonoidHom = I := by
  have h : (1 : MulAut W).toMonoidHom = MonoidHom.id W := MonoidHom.ext fun _ => rfl
  rw [h, Subgroup.map_id]

private lemma s16c13bcA_map_mul_map (a b : MulAut W) (I : Subgroup W) :
    (I.map a.toMonoidHom).map b.toMonoidHom = I.map (b * a).toMonoidHom := by
  rw [Subgroup.map_map]
  rfl

private lemma s16c13bcA_map_inv_map (σ : MulAut W) (I : Subgroup W) :
    (I.map σ⁻¹.toMonoidHom).map σ.toMonoidHom = I := by
  rw [s16c13bcA_map_mul_map, mul_inv_cancel, s16c13bcA_map_one]

private lemma s16c13bcA_map_zsq (z : MulAut W) (I : Subgroup W) :
    (I.map z.toMonoidHom).map z.toMonoidHom = I.map (z ^ 2).toMonoidHom := by
  rw [s16c13bcA_map_mul_map, pow_two]

private lemma s16c13bcA_map_zcube (z : MulAut W) (I : Subgroup W) :
    (I.map (z ^ 2).toMonoidHom).map z.toMonoidHom = I.map (z ^ 3).toMonoidHom := by
  rw [s16c13bcA_map_mul_map, show z * z ^ 2 = z ^ 3 from (pow_succ' z 2).symm]

private lemma s16c13bcA_isIrr_map {L : Subgroup (MulAut W)} {σ : MulAut W}
    (hσ : σ ∈ Subgroup.normalizer (L : Set (MulAut W))) {J : Subgroup W}
    (hJ : XMod.IsIrr ↥L J) : XMod.IsIrr ↥L (J.map σ.toMonoidHom) := by
  obtain ⟨hinv, hlt, hirr⟩ := hJ
  have hmem : ∀ a ∈ L, σ⁻¹ * a * σ ∈ L :=
    fun a ha => (Subgroup.mem_normalizer_iff''.1 hσ a).1 ha
  refine ⟨?_, ?_, ?_⟩
  · intro a u hu
    obtain ⟨j, hj, rfl⟩ := hu
    exact ⟨((⟨σ⁻¹ * a * σ, hmem a a.2⟩ : ↥L) • j), hinv _ j hj, by
      show σ ((σ⁻¹ * (a : MulAut W) * σ) j) = (a : MulAut W) (σ j)
      simp [MulAut.mul_apply]⟩
  · refine bot_lt_iff_ne_bot.mpr fun hb => hlt.ne' ?_
    rw [eq_bot_iff]
    intro x hx
    have hx' : σ x ∈ J.map σ.toMonoidHom := ⟨x, hx, rfl⟩
    rw [hb, Subgroup.mem_bot] at hx'
    rw [Subgroup.mem_bot]
    exact σ.injective (by simpa using hx')
  · intro J' hJ'inv _ hJ'le
    have hle : J'.map σ⁻¹.toMonoidHom ≤ J := by
      intro y hy
      obtain ⟨j', hj', rfl⟩ := hy
      obtain ⟨j, hj, hjj⟩ := hJ'le hj'
      have h2 : σ⁻¹ j' = j := by
        rw [← hjj]
        exact σ.symm_apply_apply j
      show σ⁻¹ j' ∈ J
      rw [h2]
      exact hj
    have hinv' : XMod.IsInv ↥L (J'.map σ⁻¹.toMonoidHom) := by
      intro a y hy
      obtain ⟨j', hj', rfl⟩ := hy
      refine ⟨(σ * (a : MulAut W) * σ⁻¹) j',
        hJ'inv ⟨σ * (a : MulAut W) * σ⁻¹, (Subgroup.mem_normalizer_iff.1 hσ a).1 a.2⟩ j' hj', ?_⟩
      show σ⁻¹ ((σ * (a : MulAut W) * σ⁻¹) j') = (a : MulAut W) (σ⁻¹ j')
      simp [MulAut.mul_apply]
    rcases hirr _ hinv' bot_le hle with h1 | h1
    · left
      rw [← s16c13bcA_map_inv_map σ J', h1, Subgroup.map_bot]
    · right
      rw [← s16c13bcA_map_inv_map σ J', h1]

private lemma s16c13bcA_closure {L : Subgroup (MulAut W)} {J₀ J₁ : Subgroup W} {x : MulAut W}
    (hxL : x ∈ Subgroup.normalizer (L : Set (MulAut W)))
    (hxW : (J₀ ⊔ J₁).map x.toMonoidHom = J₀ ⊔ J₁)
    {I : Subgroup W} (hI : XMod.IsIrr ↥L I) (hIle : I ≤ J₀ ⊔ J₁) :
    XMod.IsIrr ↥L (I.map x.toMonoidHom) ∧ I.map x.toMonoidHom ≤ J₀ ⊔ J₁ :=
  ⟨s16c13bcA_isIrr_map hxL hI, (Subgroup.map_mono hIle).trans (le_of_eq hxW)⟩

private lemma s16c13bcA_fix_of_fixes {L : Subgroup (MulAut W)} {J : Subgroup W}
    (hJ : XMod.IsIrr ↥L J) (hE : Z391.EndUnitsTrivial L J)
    {c : MulAut W} (hc : ∀ l ∈ L, c * l = l * c) (hcJ : J.map c.toMonoidHom = J) :
    ∀ x ∈ J, c x = x := by
  have hcJ' : c • J = J := by rw [s16c13bcA_smul_eq_map]; exact hcJ
  have hpt := Z391.v2f_smul_eq_self (Λ := L) (c := c) hc (P := J) (R := J)
    hE hJ.1 (XMod.Iso.refl J) hcJ'
  intro x hx
  simpa [MulAut.smul_def] using hpt x hx

end Helpers

theorem s16c13bcA_members {W : Type} [CommGroup W] {L : Subgroup (MulAut W)}
    {J₀ J₁ : Subgroup W} (hJ₀ : XMod.IsIrr ↥L J₀) (hJ₁ : XMod.IsIrr ↥L J₁) (hinf : J₀ ⊓ J₁ = ⊥)
    (hE₀ : Z391.EndUnitsTrivial L J₀) (hE₁ : Z391.EndUnitsTrivial L J₁)
    {z : MulAut W} (hz3 : z ^ 3 = 1) (hzL : ∀ l ∈ L, z * l = l * z)
    (hzW : (J₀ ⊔ J₁).map z.toMonoidHom = J₀ ⊔ J₁) (hzne : ∃ u ∈ J₀ ⊔ J₁, z u ≠ u) :
    J₀.map z.toMonoidHom ≠ J₀ ∧ J₀.map (z ^ 2).toMonoidHom ≠ J₀ ∧
      J₀.map z.toMonoidHom ≠ J₀.map (z ^ 2).toMonoidHom ∧
      ∀ I : Subgroup W, XMod.IsIrr ↥L I → I ≤ J₀ ⊔ J₁ →
        I = J₀ ∨ I = J₀.map z.toMonoidHom ∨ I = J₀.map (z ^ 2).toMonoidHom := by
  classical
  have hJ0ne : J₀ ≠ ⊥ := hJ₀.2.1.ne'
  have hJ01 : J₀ ≠ J₁ := by
    intro h
    have h' : J₀ ⊓ J₁ = J₀ := by rw [h, inf_idem]
    rw [hinf] at h'
    exact hJ0ne h'.symm
  have hzN : z ∈ Subgroup.normalizer (L : Set (MulAut W)) :=
    Subgroup.centralizer_le_normalizer (L : Set (MulAut W))
      (Subgroup.mem_centralizer_iff.2 fun l hl => (hzL l hl).symm)
  have hz2N : z ^ 2 ∈ Subgroup.normalizer (L : Set (MulAut W)) := pow_mem hzN 2
  have hz2W : (J₀ ⊔ J₁).map (z ^ 2).toMonoidHom = J₀ ⊔ J₁ := by
    rw [← s16c13bcA_map_zsq, hzW, hzW]
  have hP0irr : XMod.IsIrr ↥L (J₀.map z.toMonoidHom) ∧
      J₀.map z.toMonoidHom ≤ J₀ ⊔ J₁ := s16c13bcA_closure hzN hzW hJ₀ le_sup_left
  have hP1irr : XMod.IsIrr ↥L (J₀.map (z ^ 2).toMonoidHom) ∧
      J₀.map (z ^ 2).toMonoidHom ≤ J₀ ⊔ J₁ := s16c13bcA_closure hz2N hz2W hJ₀ le_sup_left
  by_cases hz0 : J₀.map z.toMonoidHom = J₀
  · exfalso
    have hfix0 := s16c13bcA_fix_of_fixes hJ₀ hE₀ hzL hz0
    have hz1 : J₁.map z.toMonoidHom = J₁ := by
      by_contra hz1ne
      have hR := s16c13bcA_closure hzN hzW hJ₁ le_sup_right
      have hR' := s16c13bcA_closure hz2N hz2W hJ₁ le_sup_right
      have hRne0 : J₁.map z.toMonoidHom ≠ J₀ := by
        intro h
        have h2 : J₁.map (z ^ 2).toMonoidHom = J₀ := by
          have h1 := congrArg (fun I : Subgroup W => I.map z.toMonoidHom) h
          rw [s16c13bcA_map_zsq, hz0] at h1
          exact h1
        have h1 := congrArg (fun I : Subgroup W => I.map z.toMonoidHom) h2
        rw [s16c13bcA_map_zcube, hz3, s16c13bcA_map_one, hz0] at h1
        exact hJ01 h1.symm
      have hR'ne0 : J₁.map (z ^ 2).toMonoidHom ≠ J₀ := by
        intro h
        have h1 := congrArg (fun I : Subgroup W => I.map z.toMonoidHom) h
        rw [s16c13bcA_map_zcube, hz3, s16c13bcA_map_one, hz0] at h1
        exact hJ01 h1.symm
      have hR'ne1 : J₁.map (z ^ 2).toMonoidHom ≠ J₁ := by
        intro h
        have h1 := congrArg (fun I : Subgroup W => I.map z.toMonoidHom) h
        rw [s16c13bcA_map_zcube, hz3, s16c13bcA_map_one] at h1
        exact hz1ne h1.symm
      have heq := Z391.v2f_eq_of_le_sup (A := ↥L) (P := J₀) (P' := J₁)
        (R := J₁.map z.toMonoidHom) (R' := J₁.map (z ^ 2).toMonoidHom)
        hJ₀ hJ₁ hE₀ hR.1 hR'.1 hR.2 hR'.2 hRne0 hz1ne hR'ne0 hR'ne1
      have h1 := congrArg (fun I : Subgroup W => I.map z.toMonoidHom) heq
      rw [s16c13bcA_map_zsq, s16c13bcA_map_zcube, hz3, s16c13bcA_map_one] at h1
      exact hR'ne1 h1
    have hfix1 := s16c13bcA_fix_of_fixes hJ₁ hE₁ hzL hz1
    obtain ⟨u, hu, hzu⟩ := hzne
    obtain ⟨a, ha, b, hb, rfl⟩ := Subgroup.mem_sup.1 hu
    exact hzu (by rw [map_mul, hfix0 a ha, hfix1 b hb])
  · have hP0ne : J₀.map z.toMonoidHom ≠ J₀ := hz0
    have hP1ne : J₀.map (z ^ 2).toMonoidHom ≠ J₀ := by
      intro h
      have h3 := congrArg (fun I : Subgroup W => I.map z.toMonoidHom) h
      rw [s16c13bcA_map_zcube, hz3, s16c13bcA_map_one] at h3
      exact hz0 h3.symm
    have hP0P1 : J₀.map z.toMonoidHom ≠ J₀.map (z ^ 2).toMonoidHom := by
      intro h
      have h1 := congrArg (fun I : Subgroup W => I.map z.toMonoidHom) h
      rw [s16c13bcA_map_zsq, s16c13bcA_map_zcube, hz3, s16c13bcA_map_one] at h1
      exact hP1ne h1
    have hJ1mem : J₁ = J₀.map z.toMonoidHom ∨ J₁ = J₀.map (z ^ 2).toMonoidHom := by
      by_cases h0 : J₁ = J₀.map z.toMonoidHom
      · exact Or.inl h0
      · refine Or.inr ?_
        by_contra h1
        have h := Z391.v2f_eq_of_le_sup (A := ↥L) (P := J₀) (P' := J₁)
          (R := J₀.map z.toMonoidHom) (R' := J₀.map (z ^ 2).toMonoidHom)
          hJ₀ hJ₁ hE₀ hP0irr.1 hP1irr.1 hP0irr.2 hP1irr.2 hP0ne
          (fun h => h0 h.symm) hP1ne (fun h => h1 h.symm)
        exact hP0P1 h
    have htri : ∀ I : Subgroup W, XMod.IsIrr ↥L I → I ≤ J₀ ⊔ J₁ →
        I = J₀ ∨ I = J₀.map z.toMonoidHom ∨ I = J₀.map (z ^ 2).toMonoidHom := by
      intro I hI hIle
      by_cases hI0 : I = J₀
      · exact Or.inl hI0
      by_cases hI1 : I = J₁
      · rcases hJ1mem with h | h
        · exact Or.inr (Or.inl (hI1.trans h))
        · exact Or.inr (Or.inr (hI1.trans h))
      · by_cases hP0J1 : J₀.map z.toMonoidHom = J₁
        · have hP1ne1 : J₀.map (z ^ 2).toMonoidHom ≠ J₁ :=
            fun h => hP0P1 (hP0J1.trans h.symm)
          have h := Z391.v2f_eq_of_le_sup (A := ↥L) (P := J₀) (P' := J₁)
            (R := I) (R' := J₀.map (z ^ 2).toMonoidHom)
            hJ₀ hJ₁ hE₀ hI hP1irr.1 hIle hP1irr.2 hI0 hI1 hP1ne hP1ne1
          exact Or.inr (Or.inr h)
        · have h := Z391.v2f_eq_of_le_sup (A := ↥L) (P := J₀) (P' := J₁)
            (R := I) (R' := J₀.map z.toMonoidHom)
            hJ₀ hJ₁ hE₀ hI hP0irr.1 hIle hP0irr.2 hI0 hI1 hP0ne hP0J1
          exact Or.inr (Or.inl h)
    exact ⟨hP0ne, hP1ne, hP0P1, htri⟩

theorem s16c13bcA_stable_member {W : Type} [CommGroup W] {L : Subgroup (MulAut W)}
    {J₀ J₁ : Subgroup W} (hJ₀ : XMod.IsIrr ↥L J₀) (hJ₁ : XMod.IsIrr ↥L J₁) (hinf : J₀ ⊓ J₁ = ⊥)
    (hE₀ : Z391.EndUnitsTrivial L J₀) (hE₁ : Z391.EndUnitsTrivial L J₁)
    {z : MulAut W} (hz3 : z ^ 3 = 1) (hzL : ∀ l ∈ L, z * l = l * z)
    (hzW : (J₀ ⊔ J₁).map z.toMonoidHom = J₀ ⊔ J₁) (hzne : ∃ u ∈ J₀ ⊔ J₁, z u ≠ u)
    {N : Subgroup (MulAut W)} (hN : IsPGroup 2 N)
    (hNL : ∀ w ∈ N, w ∈ Subgroup.normalizer (L : Set (MulAut W)))
    (hNW : ∀ w ∈ N, (J₀ ⊔ J₁).map w.toMonoidHom = J₀ ⊔ J₁) :
    ∃ k : ℕ, k < 3 ∧ ∀ w ∈ N,
      (J₀.map (z ^ k).toMonoidHom).map w.toMonoidHom = J₀.map (z ^ k).toMonoidHom := by
  classical
  obtain ⟨hne1, hne2, hne12, htri⟩ := s16c13bcA_members hJ₀ hJ₁ hinf hE₀ hE₁ hz3 hzL hzW hzne
  have hzN : z ∈ Subgroup.normalizer (L : Set (MulAut W)) :=
    Subgroup.centralizer_le_normalizer (L : Set (MulAut W))
      (Subgroup.mem_centralizer_iff.2 fun l hl => (hzL l hl).symm)
  have hzpowW : ∀ k : ℕ, (J₀ ⊔ J₁).map (z ^ k).toMonoidHom = J₀ ⊔ J₁ := by
    intro k
    induction k with
    | zero => rw [pow_zero, s16c13bcA_map_one]
    | succ k ih =>
      rw [pow_succ', ← s16c13bcA_map_mul_map, ih, hzW]
  let Y : Fin 3 → Subgroup W := fun i => J₀.map (z ^ (i : ℕ)).toMonoidHom
  have hY0 : Y 0 = J₀ := by
    show J₀.map (z ^ 0).toMonoidHom = J₀
    rw [pow_zero, s16c13bcA_map_one]
  have hY1 : Y 1 = J₀.map z.toMonoidHom := by
    show J₀.map (z ^ 1).toMonoidHom = J₀.map z.toMonoidHom
    rw [pow_one]
  have hY2 : Y 2 = J₀.map (z ^ 2).toMonoidHom := rfl
  have hYinj : Function.Injective Y := by
    intro i j hij
    fin_cases i <;> fin_cases j
    · rfl
    · exact absurd (hY0.symm.trans (hij.trans hY1)) (fun h => hne1 h.symm)
    · exact absurd (hY0.symm.trans (hij.trans hY2)) (fun h => hne2 h.symm)
    · exact absurd (hY1.symm.trans (hij.trans hY0)) hne1
    · rfl
    · exact absurd (hY1.symm.trans (hij.trans hY2)) hne12
    · exact absurd (hY2.symm.trans (hij.trans hY0)) hne2
    · exact absurd (hY2.symm.trans (hij.trans hY1)) (fun h => hne12 h.symm)
    · rfl
  have hYirr : ∀ i, XMod.IsIrr ↥L (Y i) ∧ Y i ≤ J₀ ⊔ J₁ := fun i =>
    s16c13bcA_closure (pow_mem hzN (i : ℕ)) (hzpowW i) hJ₀ le_sup_left
  have hperm : ∀ w ∈ N, ∀ i, ∃ j, (Y i).map w.toMonoidHom = Y j := by
    intro w hw i
    have h := s16c13bcA_closure (hNL w hw) (hNW w hw) (hYirr i).1 (hYirr i).2
    rcases htri _ h.1 h.2 with h0 | h0 | h0
    · exact ⟨0, h0.trans hY0.symm⟩
    · exact ⟨1, h0.trans hY1.symm⟩
    · exact ⟨2, h0.trans hY2.symm⟩
  obtain ⟨i, hi⟩ := s16c13bcA_exists_stable_index hYinj hN hperm
    (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; exact ⟨1, rfl⟩)
  exact ⟨i, i.2, hi⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
