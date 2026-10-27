module

public import CFSG.Timmesfeld.Transvection.RankThreeA2

public section

namespace CFSG.Timmesfeld.Transvection

open CFSG.Timmesfeld.ARS RankThree
open scoped commutatorElement

variable {G : Type*} [Group G] {Δ : Set (Subgroup G)} {r : ℕ} {P Q : Fin r → Subgroup G}

private theorem conj_eq_of_commute_mul {a b y : G} (h : Commute (a * b) y) :
    b * y * b⁻¹ = a⁻¹ * y * a := by
  have h1 : a * b * y = y * (a * b) := h.eq
  calc b * y * b⁻¹ = a⁻¹ * (a * b * y) * b⁻¹ := by group
    _ = a⁻¹ * (y * (a * b)) * b⁻¹ := by rw [h1]
    _ = a⁻¹ * y * a * (b * b⁻¹) := by group
    _ = a⁻¹ * y * a := by rw [mul_inv_cancel, mul_one]

namespace IsFrame

variable (hF : IsFrame Δ P Q) (hΔ : IsTransvectionClass Δ) {o i j : Fin r}
include hF hΔ

theorem commute_mul_of_commute_mul (hoi : o ≠ i) (hoj : o ≠ j) (hij : i ≠ j) {a b c : G}
    (haX : a ∈ P o ⊔ Q o) (hbX : b ∈ P i ⊔ Q i) (hcX : c ∈ P j ⊔ Q j)
    (haP : conjSub (P o) a = P o) (haQ : conjSub (Q o) a = Q o)
    (hbP : conjSub (P i) b = P i) (hbQ : conjSub (Q i) b = Q i)
    (hcP : conjSub (P j) c = P j) (hcQ : conjSub (Q j) c = Q j)
    (hab : ∀ y ∈ shortRootGroup Δ (Q o) (P o) (P i) (Q i), Commute (a * b) y)
    (hac : ∀ z ∈ shortRootGroup Δ (Q o) (P o) (P j) (Q j), Commute (a * c) z)
    (hA2 : ∀ y ∈ shortRootGroup Δ (Q o) (P o) (P i) (Q i),
      ∀ x ∈ shortRootGroup Δ (Q i) (P i) (P j) (Q j),
        ⁅y, x⁆ ∈ shortRootGroup Δ (Q o) (P o) (P j) (Q j))
    (hB5 : ∀ y ∈ shortRootGroup Δ (Q o) (P o) (P i) (Q i),
      ∀ x ∈ shortRootGroup Δ (Q i) (P i) (P j) (Q j), x ≠ 1 → ⁅y, x⁆ = 1 → y = 1)
    {y₀ : G} (hy₀ : y₀ ∈ shortRootGroup Δ (Q o) (P o) (P i) (Q i)) (hy₀1 : y₀ ≠ 1)
    {x : G} (hx : x ∈ shortRootGroup Δ (Q i) (P i) (P j) (Q j)) : Commute (b * c) x := by
  have hR := hΔ.root
  have hcy : ∀ y ∈ shortRootGroup Δ (Q o) (P o) (P i) (Q i), Commute c y := fun y hy =>
    (hF.commuting_sup_shortRootGroup hR (i := j) (a := Sum.inr o) (b := Sum.inl i)
      (by simpa using hoj) (by simpa using hij)) c hcX y hy
  have hbz : ∀ z ∈ shortRootGroup Δ (Q o) (P o) (P j) (Q j), Commute b z := fun z hz =>
    (hF.commuting_sup_shortRootGroup hR (i := i) (a := Sum.inr o) (b := Sum.inl j)
      (by simpa using hoi) (by simpa using hij.symm)) b hbX z hz
  have hax : Commute a x :=
    (hF.commuting_sup_shortRootGroup hR (i := o) (a := Sum.inr i) (b := Sum.inl j)
      (by simpa using hoi.symm) (by simpa using hoj.symm)) a haX x hx
  have hfix : ∀ {l m : Fin r}, l ≠ m → ∀ {t : G}, t ∈ P l ⊔ Q l →
      conjSub (P m) t = P m ∧ conjSub (Q m) t = Q m := fun {l m} hlm {t} ht =>
    ⟨conjSub_of_forall_commute fun p hp => (hF.commuting_sup_framePt hR (i := l)
      (a := Sum.inl m) (by simpa using hlm.symm)) t ht p hp,
     conjSub_of_forall_commute fun p hp => (hF.commuting_sup_framePt hR (i := l)
      (a := Sum.inr m) (by simpa using hlm.symm)) t ht p hp⟩
  have hXio : conjSub (shortRootGroup Δ (Q o) (P o) (P i) (Q i)) a =
      shortRootGroup Δ (Q o) (P o) (P i) (Q i) := by
    rw [← shortRootGroup_conjSub hR, haQ, haP, (hfix hoi haX).1, (hfix hoi haX).2]
  have hXjo : conjSub (shortRootGroup Δ (Q o) (P o) (P j) (Q j)) a =
      shortRootGroup Δ (Q o) (P o) (P j) (Q j) := by
    rw [← shortRootGroup_conjSub hR, haQ, haP, (hfix hoj haX).1, (hfix hoj haX).2]
  have hXjib : conjSub (shortRootGroup Δ (Q i) (P i) (P j) (Q j)) b =
      shortRootGroup Δ (Q i) (P i) (P j) (Q j) := by
    rw [← shortRootGroup_conjSub hR, hbQ, hbP, (hfix hij hbX).1, (hfix hij hbX).2]
  have hXjic : conjSub (shortRootGroup Δ (Q i) (P i) (P j) (Q j)) c =
      shortRootGroup Δ (Q i) (P i) (P j) (Q j) := by
    rw [← shortRootGroup_conjSub hR, (hfix hij.symm hcX).2, (hfix hij.symm hcX).1, hcP, hcQ]
  set y := a * y₀ * a⁻¹ with hy_def
  have hy : y ∈ shortRootGroup Δ (Q o) (P o) (P i) (Q i) := hXio ▸ conj_mem_conjSub a hy₀
  have hz := hA2 y hy x hx
  have hgy : b * c * y * (b * c)⁻¹ = y₀ := by
    calc b * c * y * (b * c)⁻¹ = b * (c * y * c⁻¹) * b⁻¹ := by group
      _ = b * y * b⁻¹ := by rw [(hcy y hy).eq, mul_inv_cancel_right]
      _ = a⁻¹ * y * a := conj_eq_of_commute_mul (hab y hy)
      _ = y₀ := by rw [hy_def]; group
  have hgz : b * c * ⁅y, x⁆ * (b * c)⁻¹ = ⁅y₀, x⁆ := by
    have hz' : a⁻¹ * ⁅y, x⁆ * a ∈ shortRootGroup Δ (Q o) (P o) (P j) (Q j) := by
      have := conj_mem_conjSub a⁻¹ hz
      rwa [inv_inv, show conjSub (shortRootGroup Δ (Q o) (P o) (P j) (Q j)) a⁻¹ =
        shortRootGroup Δ (Q o) (P o) (P j) (Q j) by
          conv_lhs => rw [← hXjo]
          rw [← conjSub_mul, inv_mul_cancel, conjSub_one]] at this
    calc b * c * ⁅y, x⁆ * (b * c)⁻¹ = b * (c * ⁅y, x⁆ * c⁻¹) * b⁻¹ := by group
      _ = b * (a⁻¹ * ⁅y, x⁆ * a) * b⁻¹ := by
          rw [conj_eq_of_commute_mul (hac _ hz)]
      _ = a⁻¹ * ⁅y, x⁆ * a := by rw [(hbz _ hz').eq, mul_inv_cancel_right]
      _ = ⁅a⁻¹ * y * a⁻¹⁻¹, a⁻¹ * x * a⁻¹⁻¹⁆ := by rw [← conj_commutatorElement, inv_inv]
      _ = ⁅y₀, x⁆ := by
          have hxa : a⁻¹ * x * a = x := by rw [mul_assoc, ← hax.eq, inv_mul_cancel_left]
          have hya : a⁻¹ * y * a = y₀ := by rw [hy_def]; group
          rw [inv_inv, hxa, hya]
  have hgx : ⁅y₀, b * c * x * (b * c)⁻¹⁆ = ⁅y₀, x⁆ := by
    rw [← hgz, conj_commutatorElement, hgy]
  have hgxX : b * c * x * (b * c)⁻¹ ∈ shortRootGroup Δ (Q i) (P i) (P j) (Q j) := by
    have h1 : b * c * x * (b * c)⁻¹ = b * (c * x * c⁻¹) * b⁻¹ := by group
    rw [h1]
    refine hXjib ▸ conj_mem_conjSub b ?_
    exact hXjic ▸ conj_mem_conjSub c hx
  have hy₀x := hA2 y₀ hy₀ x hx
  have hL := shortRootGroup_le_lineGroup (Δ := Δ) (Q o) (P o) (P j) (Q j)
  have hw : ⁅y₀, b * c * x * (b * c)⁻¹ * x⁆ = 1 := by
    rw [hF.commutator_mul_right hΔ hoj hij hgxX (hL hy₀x), hgx]
    exact mul_self_of_mem_lineGroup hΔ (hF.memQ o) (hF.memP j) (hF.commuting_QP hoj) (hL hy₀x)
  have hw1 : b * c * x * (b * c)⁻¹ * x = 1 := by
    by_contra hne
    exact hy₀1 (hB5 y₀ hy₀ _ (Subgroup.mul_mem _ hgxX hx) hne hw)
  have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right (mul_self_of_mem_lineGroup hΔ (hF.memQ i)
    (hF.memP j) (hF.commuting_QP hij) ((mem_shortRootGroup.1 hx).1.1))
  have h2 : b * c * x * (b * c)⁻¹ = x := by
    have := eq_inv_of_mul_eq_one_left hw1
    rwa [hxinv] at this
  calc b * c * x = b * c * x * (b * c)⁻¹ * (b * c) := by group
    _ = x * (b * c) := by rw [h2]

end IsFrame

end CFSG.Timmesfeld.Transvection
