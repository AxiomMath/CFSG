module

public import CFSG.RankThree.PartTwo.Sec4.E27.L3FUnitaryFaith

public section

open CFSG.Open CFSG.LieType.Seitz CFSG.LieType.SeitzGeneration

namespace CFSG.RankThree.PartTwo.Sec4.E27

open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.RankThree.PartTwo.KFacts Matrix

section Pair

variable {p f e : ℕ} {K : Type} [Field K] {k : Subfield K} (h : UnitaryFieldData p f K)
  (h₀ : UnitaryFieldData p e k) (hbar : ∀ x : k, h.bar (x : K) = ((h₀.bar x : k) : K))

theorem lineU_ker [Finite K] (h3 : (3 : K) ≠ 0) (hQ : p ^ f % 3 = 2) (hq : 2 < p ^ f)
    {E : Subgroup (MulAut (unitaryPSU h 3))} (hE : IsElemAbelian 3 E) (hc : Nat.card E = 27)
    {σ : K ≃+* K} (hσ : orderOf σ = 3) (hk : ∀ x, x ∈ k ↔ σ x = x) {H : unitaryIsom3 h}
    (hφE : psuConj h H * psuField h σ * (psuConj h H)⁻¹ ∈ E)
    (hφN : psuConj h H * psuField h σ * (psuConj h H)⁻¹ ∉ (psuConj h).range) :
    ∀ x ∈ E, (∀ l ∈ lineU h h₀ hbar H, x l = l) →
      x ∈ Subgroup.zpowers (psuConj h H * psuField h σ * (psuConj h H)⁻¹) := by
  intro x hx hfix
  obtain ⟨b, hb, a, rfl⟩ := exists_eq_mul_zpow_of_card hE hc
    (card_inf_psuConj_range_eq_nine h3 hq hE hc) hφE hφN x hx
  obtain ⟨B, rfl⟩ := hb.2
  have hσ3 : σ ^ 3 = 1 := by rw [← hσ]; exact pow_orderOf_eq_one σ
  have hb1 : psuConj h B = 1 := by
    refine psuConj_eq_one_of_fixes h hQ hq hσ3 hk (H := H) (B := B) fun g hg => ?_
    have hl : unitaryProj h 3 (suConj h H g) ∈ lineU h h₀ hbar H :=
      (mem_lineU_iff h h₀ hbar).2 ⟨g, hg, rfl⟩
    have h1 := hfix _ hl
    rw [MulAut.mul_apply, zpow_apply_eq_of_fixes (fieldLineU_fixes_lineU h h₀ hbar hq hk hl) a]
      at h1
    exact h1
  rw [hb1, one_mul]
  exact Subgroup.zpow_mem_zpowers _ a

theorem lineU_sup_eq_top (hfe : f = 3 * e) (hq : p ^ e ≠ 2)
    {H H' : unitaryIsom3 h}
    (hne : ¬ ∀ g : unitarySU p f K 3,
      (∀ i j, ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) i j ∈ k) →
        ∀ i j, (((suConj h (H'⁻¹ * H) g : unitarySU p f K 3) : GL (Fin 3) K) :
          Matrix (Fin 3) (Fin 3) K) i j ∈ k) :
    lineU h h₀ hbar H ⊔ lineU h h₀ hbar H' = ⊤ := by
  set Y : Subgroup (unitarySU p f K 3) :=
    (lineU h h₀ hbar H ⊔ lineU h h₀ hbar H').comap (unitaryProj h 3) with hY
  have hYtop : Y = ⊤ := Sec19.Item19Res6Proof.eq_top_of_two_conj_su h h₀ hbar hfe hq H H'
    (fun g hg => Subgroup.mem_sup_left ((mem_lineU_iff h h₀ hbar).2 ⟨g, hg, rfl⟩))
    (fun g hg => Subgroup.mem_sup_right ((mem_lineU_iff h h₀ hbar).2 ⟨g, hg, rfl⟩)) hne
  rw [eq_top_iff]
  intro x _
  obtain ⟨s, rfl⟩ := unitaryProj_surjective h 3 x
  have : s ∈ Y := by rw [hYtop]; trivial
  exact this

end Pair

section Second

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K) {k : Subfield K}

theorem conj_moves_of_second (hQ : p ^ f % 3 = 2) (hq : 2 < p ^ f) {σ σ' : K ≃+* K}
    (hσ : orderOf σ = 3) (hk : ∀ x, x ∈ k ↔ σ x = x) (hk' : ∀ x, x ∈ k ↔ σ' x = x)
    {H H' : unitaryIsom3 h} {y : MulAut (unitaryPSU h 3)} (hyN : y ∈ (psuConj h).range)
    (hy1 : y ≠ 1)
    (hψH : psuConj h H * psuField h σ * (psuConj h H)⁻¹ * y =
      psuConj h H' * psuField h σ' * (psuConj h H')⁻¹) :
    ¬ ∀ g : unitarySU p f K 3,
      (∀ i j, ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) i j ∈ k) →
        ∀ i j, (((suConj h (H'⁻¹ * H) g : unitarySU p f K 3) : GL (Fin 3) K) :
          Matrix (Fin 3) (Fin 3) K) i j ∈ k := by
  intro hall
  apply hy1
  obtain ⟨B, rfl⟩ := hyN
  have hσ3 : σ ^ 3 = 1 := by rw [← hσ]; exact pow_orderOf_eq_one σ
  refine psuConj_eq_one_of_fixes h hQ hq hσ3 hk (H := H) (B := B) fun g hg => ?_
  have hgσ : ∀ i j, σ (((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) i j) =
      ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) i j := fun i j => (hk _).1 (hg i j)
  have hx1 : (psuConj h H * psuField h σ * (psuConj h H)⁻¹) (unitaryProj h 3 (suConj h H g)) =
      unitaryProj h 3 (suConj h H g) := by
    rw [fieldLineU_apply_proj hq, Sec19.Item19Res6Proof.conj_suField_fix H σ g hgσ]
  have hxH' : suConj h H g = suConj h H' (suConj h (H'⁻¹ * H) g) := by
    rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel_left]
  have hx2 : (psuConj h H' * psuField h σ' * (psuConj h H')⁻¹) (unitaryProj h 3 (suConj h H g)) =
      unitaryProj h 3 (suConj h H g) := by
    rw [hxH', fieldLineU_apply_proj hq,
      Sec19.Item19Res6Proof.conj_suField_fix H' σ' _ fun i j => (hk' _).1 (hall g hg i j)]
  rw [← hψH, MulAut.mul_apply] at hx2
  exact (psuConj h H * psuField h σ * (psuConj h H)⁻¹).injective (hx2.trans hx1.symm)

end Second

end CFSG.RankThree.PartTwo.Sec4.E27
