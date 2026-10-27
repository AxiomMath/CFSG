module

public import CFSG.Timmesfeld.Transvection.RankThreeA2

public section

namespace CFSG.Timmesfeld.Transvection

open CFSG.Timmesfeld.ARS RankThree
open scoped commutatorElement

variable {G : Type*} [Group G] {Δ : Set (Subgroup G)} {r : ℕ} {P Q : Fin r → Subgroup G}

namespace RankThree

theorem commutator_commutator_eq {x y p : G} (hx : x * x = 1) (hp : p * p = 1)
    (hyp : Commute y p) : ⁅⁅x, y⁆, p⁆ = x * ⁅y, ⁅x, p⁆⁆ * x⁻¹ := by
  have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx
  have hpinv : p⁻¹ = p := inv_eq_of_mul_eq_one_right hp
  have h1 : p * x * p⁻¹ = x * ⁅x, p⁆ := by
    rw [commutatorElement_def]
    calc p * x * p⁻¹ = x * x * p * x * p⁻¹ := by rw [hx, one_mul]
      _ = x * (x * p * x⁻¹ * p⁻¹) := by rw [hxinv]; group
  have h2 : p * y * p⁻¹ = y := by rw [hyp.symm.eq, mul_inv_cancel_right]
  have h3 : p * ⁅x, y⁆ * p⁻¹ = x * ⁅⁅x, p⁆, y⁆ * x⁻¹ * ⁅x, y⁆ := by
    rw [conj_commutatorElement, h1, h2, commutatorElement_mul_left']
  calc ⁅⁅x, y⁆, p⁆ = ⁅x, y⁆ * (p * ⁅x, y⁆ * p⁻¹)⁻¹ := by
        rw [commutatorElement_def]
        group
    _ = x * ⁅y, ⁅x, p⁆⁆ * x⁻¹ := by
        rw [h3, ← commutatorElement_inv]
        group

end RankThree

namespace IsFrame

variable (hF : IsFrame Δ P Q) (hΔ : IsTransvectionClass Δ) {i j k : Fin r}
include hF hΔ

theorem exists_commutator_commutator_eq (hij : i ≠ j) (hik : i ≠ k) {x y p v d : G}
    (hx : x ∈ shortRootGroup Δ (Q i) (P i) (P j) (Q j))
    (hy : y ∈ shortRootGroup Δ (Q j) (P j) (P k) (Q k)) (hp : p ∈ P i)
    (hv : v ∈ shortRootGroup Δ (P i) (Q i) (P j) (Q j)) (hd : d ∈ P j) (hxp : ⁅x, p⁆ = v * d)
    (hyv : ⁅y, v⁆ ∈ shortRootGroup Δ (P i) (Q i) (P k) (Q k))
    (hxu : ∀ u ∈ shortRootGroup Δ (P i) (Q i) (P k) (Q k),
      ⁅x, u⁆ ∈ shortRootGroup Δ (P j) (Q j) (P k) (Q k)) :
    ∃ c₁ ∈ shortRootGroup Δ (P j) (Q j) (P k) (Q k),
      ∃ c₂ ∈ shortRootGroup Δ (P i) (Q i) (P k) (Q k), ⁅⁅x, y⁆, p⁆ = c₁ * c₂ * ⁅y, d⁆ := by
  have hR := hΔ.root
  obtain ⟨⟨hxL, -⟩, -⟩ := mem_shortRootGroup.1 hx
  obtain ⟨⟨hyL, hyS⟩, -⟩ := mem_shortRootGroup.1 hy
  obtain ⟨⟨hvL, -⟩, -⟩ := mem_shortRootGroup.1 hv
  have hx2 : x * x = 1 := mul_self_of_mem_lineGroup hΔ (hF.memQ i) (hF.memP j)
    (hF.commuting_QP hij) hxL
  have hp2 : p * p = 1 := hR.mul_self _ (hF.memP i) p hp
  have hyp : Commute y p := ((hF.commuting_framePt_lineGroup hR (a := Sum.inl i)
    (c := Sum.inr j) (d := Sum.inl k) (by simpa using hij.symm) (by simp)) p hp y hyL).symm
  have hydL : ⁅y, d⁆ ∈ lineGroup Δ (P j) (P k) := by
    rw [commutatorElement_def]
    refine Subgroup.mul_mem _ ?_
      (Subgroup.inv_mem _ (le_lineGroup (left_mem_lineOf (hF.memP j)) hd))
    refine le_lineGroup ((mem_lineStab_iff.1 hyS (P j)).2 (left_mem_lineOf (hF.memP j))) ?_
    exact conj_mem_conjSub y hd
  have hvyd : Commute v ⁅y, d⁆ :=
    (hF.commuting_lineGroup_lineGroup hR (a := Sum.inl i) (b := Sum.inl j) (c := Sum.inl j)
      (d := Sum.inl k) (by simp) (by simp) (by simp) (by simp)) v hvL _ hydL
  have hxyd : Commute x ⁅y, d⁆ :=
    (hF.commuting_lineGroup_lineGroup hR (a := Sum.inr i) (b := Sum.inl j) (c := Sum.inl j)
      (d := Sum.inl k) (by simpa using hij.symm) (by simp) (by simpa using hik.symm) (by simp))
      x hxL _ hydL
  refine ⟨⁅x, ⁅y, v⁆⁆, hxu _ hyv, ⁅y, v⁆, hyv, ?_⟩
  calc ⁅⁅x, y⁆, p⁆ = x * ⁅y, v * d⁆ * x⁻¹ := by
        rw [commutator_commutator_eq hx2 hp2 hyp, hxp]
    _ = x * (⁅y, v⁆ * ⁅y, d⁆) * x⁻¹ := by
        rw [commutatorElement_mul_right', hvyd.eq, mul_inv_cancel_right]
    _ = x * ⁅y, v⁆ * x⁻¹ * (x * ⁅y, d⁆ * x⁻¹) := by group
    _ = ⁅x, ⁅y, v⁆⁆ * ⁅y, v⁆ * ⁅y, d⁆ := by
        rw [hxyd.eq, mul_inv_cancel_right, commutatorElement_def]
        group

theorem eq_one_of_mem_of_eq_mul (hij : i ≠ j) (hik : i ≠ k) {hi : G} (hiX : hi ∈ P i ⊔ Q i)
    (hifpf : ∀ u ∈ shortRootGroup Δ (P i) (Q i) (P k) (Q k), Commute u hi → u = 1)
    (hinf : shortRootGroup Δ (P j) (Q j) (P k) (Q k) ⊓ P k = ⊥)
    {e c₁ c₂ : G} (he : e ∈ P k) (hc₁ : c₁ ∈ shortRootGroup Δ (P j) (Q j) (P k) (Q k))
    (hc₂ : c₂ ∈ shortRootGroup Δ (P i) (Q i) (P k) (Q k)) (heq : e = c₁ * c₂) : e = 1 := by
  have hR := hΔ.root
  have he' : Commute hi e := (hF.commuting_sup_framePt hR (i := i) (a := Sum.inl k)
    (by simpa using hik.symm)) hi hiX e he
  have hc₁' : Commute hi c₁ := (hF.commuting_sup_shortRootGroup hR (i := i) (a := Sum.inl j)
    (b := Sum.inl k) (by simpa using hij.symm) (by simpa using hik.symm)) hi hiX c₁ hc₁
  have hc₂' : Commute c₂ hi := by
    have h1 : hi * (c₁ * c₂) * hi⁻¹ = c₁ * c₂ := by
      rw [← heq, he'.eq, mul_inv_cancel_right]
    have h2 : hi * c₂ * hi⁻¹ = c₂ := by
      have : hi * (c₁ * c₂) * hi⁻¹ = c₁ * (hi * c₂ * hi⁻¹) := by
        rw [show hi * (c₁ * c₂) * hi⁻¹ = (hi * c₁ * hi⁻¹) * (hi * c₂ * hi⁻¹) by group,
          hc₁'.eq, mul_inv_cancel_right]
      rw [this] at h1
      exact mul_left_cancel h1
    have : hi * c₂ = c₂ * hi := by
      calc hi * c₂ = hi * c₂ * hi⁻¹ * hi := by group
        _ = c₂ * hi := by rw [h2]
    exact this.symm
  have hc₂1 := hifpf c₂ hc₂ hc₂'
  rw [hc₂1, mul_one] at heq
  subst heq
  have : e ∈ shortRootGroup Δ (P j) (Q j) (P k) (Q k) ⊓ P k := ⟨hc₁, he⟩
  rw [hinf, Subgroup.mem_bot] at this
  exact this

end IsFrame

end CFSG.Timmesfeld.Transvection
