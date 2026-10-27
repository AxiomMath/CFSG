module

public import CFSG.Quasithin.MS93.S37RSm

public section

namespace CFSG.Quasithin.MS93.S37R

open CFSG.Quasithin.JonesParshall

variable {F : Type} [Field F]

@[expose] def qv (t : F × F × F) (x : Fin 2 → F) : F := t.1 * x 0 ^ 2 + t.2.2 * x 1 ^ 2

@[expose] def lc (t : F × F × F) (x : Fin 2 → F) : (Fin 2 → F) × F := (mv t x, qv t x)

@[expose] def sc (l : F) (v : (Fin 2 → F) × F) : (Fin 2 → F) × F := (l • v.1, l ^ 2 * v.2)

theorem lc_smul (t : F × F × F) (l : F) (x : Fin 2 → F) : lc t (l • x) = sc l (lc t x) := by
  refine Prod.ext (mv_smul_right t l x) ?_
  simp only [lc, sc, qv, Pi.smul_apply, smul_eq_mul]
  ring

variable [CharP F 2]

theorem qv_eq_dot (t : F × F × F) (x : Fin 2 → F) : qv t x = dot x (mv t x) := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  simp only [qv, dot, mv, Matrix.cons_val_zero, Matrix.cons_val_one]
  linear_combination -(t.2.1 * x 0 * x 1) * h2

theorem exists_scalar [Fintype F] (hq : 4 < Fintype.card F) (Φ : (Fin 2 → F) →+ F × F × F)
    (Φ' : (Fin 2 → F) → F × F × F) (Θ : (Fin 2 → F) × F ≃+ (Fin 2 → F) × F)
    (h1 : ∀ x y, Θ (lc (Φ' x) y) = lc (Φ y) x)
    (hgen : AddSubgroup.closure (Set.range fun p : (Fin 2 → F) × (Fin 2 → F) =>
      lc (Φ p.2) p.1) = ⊤)
    {x₁ x₂ : Fin 2 → F} (hind : x₁ 0 * x₂ 1 - x₁ 1 * x₂ 0 ≠ 0)
    (hg₁ : ∀ a, ∃ y, mv (Φ y) x₁ = a) (hg₂ : ∀ a, ∃ y, mv (Φ y) x₂ = a)
    {μ : F} (hμ0 : μ ≠ 0) (hμ1 : μ ≠ 1) :
    ∃ ω : F, ω ≠ 0 ∧ ω ≠ 1 ∧ ∀ v, Θ (sc μ (Θ.symm v)) = (ω • v.1, ω * v.2) := by
  have hscadd : ∀ (l : F) v w, sc l (v + w) = sc l v + sc l w := fun l v w => by
    simp only [sc, Prod.fst_add, Prod.snd_add, smul_add, mul_add, Prod.mk_add_mk]
  let S : F → (Fin 2 → F) × F →+ (Fin 2 → F) × F := fun l =>
    { toFun := sc l
      map_zero' := by simp [sc]
      map_add' := hscadd l }
  let T : (Fin 2 → F) × F →+ (Fin 2 → F) × F :=
    { toFun := fun v => Θ (sc μ (Θ.symm v))
      map_zero' := by simp [sc]
      map_add' := fun v w => by rw [map_add, hscadd, map_add] }
  have hTv : ∀ v, T v = Θ (sc μ (Θ.symm v)) := fun _ => rfl
  have hTL : ∀ x y, T (lc (Φ y) x) = lc (Φ (μ • y)) x := fun x y => by
    rw [hTv, ← h1 x y, AddEquiv.symm_apply_apply, ← lc_smul, h1]
  have hcomm : ∀ (l : F) v, T (sc l v) = sc l (T v) := fun l v => by
    have hv : v ∈ AddSubgroup.closure (Set.range fun p : (Fin 2 → F) × (Fin 2 → F) =>
        lc (Φ p.2) p.1) := by rw [hgen]; exact AddSubgroup.mem_top v
    have key : ((T.comp (S l)) : _ →+ _) = (S l).comp T := by
      refine AddMonoidHom.ext fun w => ?_
      have hw : w ∈ AddSubgroup.closure (Set.range fun p : (Fin 2 → F) × (Fin 2 → F) =>
          lc (Φ p.2) p.1) := by rw [hgen]; exact AddSubgroup.mem_top w
      induction hw using AddSubgroup.closure_induction with
      | mem w hw =>
        obtain ⟨⟨x, y⟩, rfl⟩ := hw
        show T (sc l (lc (Φ y) x)) = sc l (T (lc (Φ y) x))
        rw [← lc_smul, hTL, hTL, lc_smul]
      | zero => simp
      | add w w' _ _ h h' => rw [map_add, map_add, h, h']
      | neg w _ h => rw [map_neg, map_neg, h]
    exact DFunLike.congr_fun key v
  have hΓ : ∀ x ∈ ({x₁, x₂} : Set (Fin 2 → F)), ∀ a,
      (T (a, dot x a)).2 = dot x (T (a, dot x a)).1 := by
    intro x hx a
    obtain ⟨y, hy⟩ : ∃ y, mv (Φ y) x = a := by
      rcases hx with rfl | hx
      · exact hg₁ a
      · rw [Set.mem_singleton_iff.1 hx]; exact hg₂ a
    have e : (a, dot x a) = lc (Φ y) x := by
      rw [lc, ← hy, qv_eq_dot]
    rw [e, hTL]
    exact qv_eq_dot _ _
  obtain ⟨ω, hω⟩ := eq_smul_of_comm (by rwa [Nat.card_eq_fintype_card]) T
    (fun l v => hcomm l v) hind hΓ
  refine ⟨ω, ?_, ?_, fun v => hω v⟩
  · rintro rfl
    have h := hω (Θ (![1, 0], 0))
    rw [hTv, AddEquiv.symm_apply_apply] at h
    have h' : Θ (sc μ (![1, 0], 0)) = Θ 0 := by rw [h, map_zero]; simp
    have := congrArg (fun v => v.1 0) (Θ.injective h')
    simp [sc] at this
    exact hμ0 this
  · rintro rfl
    have h := hω (Θ (![1, 0], 0))
    rw [hTv, AddEquiv.symm_apply_apply, one_smul, one_mul] at h
    have := congrArg (fun v => v.1 0) (Θ.injective h)
    simp [sc] at this
    exact hμ1 this

section Fin

variable [Fintype F] (hq : 4 < Fintype.card F) (Φ : (Fin 2 → F) →+ F × F × F)
  (Φ' : (Fin 2 → F) → F × F × F) (Θ : (Fin 2 → F) × F ≃+ (Fin 2 → F) × F)
  (h1 : ∀ x y, Θ (lc (Φ' x) y) = lc (Φ y) x)
  (hgen : AddSubgroup.closure (Set.range fun p : (Fin 2 → F) × (Fin 2 → F) =>
    lc (Φ p.2) p.1) = ⊤)
  {x₁ x₂ : Fin 2 → F} (hind : x₁ 0 * x₂ 1 - x₁ 1 * x₂ 0 ≠ 0)
  (hg₁ : ∀ a, ∃ y, mv (Φ y) x₁ = a) (hg₂ : ∀ a, ∃ y, mv (Φ y) x₂ = a)
include hq h1 hgen hind hg₁ hg₂

theorem exists_scalar' : ∃ μ ω : F, ω ≠ 0 ∧ ω ≠ 1 ∧
    (∀ w, Θ (sc μ w) = (ω • (Θ w).1, ω * (Θ w).2)) ∧ ∀ y, Φ (μ • y) = ω • Φ y := by
  obtain ⟨μ, hμ0, hμ1⟩ := exists_ne_zero_ne_one' (F := F)
    (by rw [Nat.card_eq_fintype_card]; omega)
  obtain ⟨ω, hω0, hω1, hω⟩ := exists_scalar hq Φ Φ' Θ h1 hgen hind hg₁ hg₂ hμ0 hμ1
  have hΘ : ∀ w, Θ (sc μ w) = (ω • (Θ w).1, ω * (Θ w).2) := fun w => by
    rw [← hω (Θ w), AddEquiv.symm_apply_apply]
  refine ⟨μ, ω, hω0, hω1, hΘ, fun y => ?_⟩
  have hL : ∀ x, lc (Φ (μ • y)) x = (ω • (lc (Φ y) x).1, ω * (lc (Φ y) x).2) := fun x => by
    rw [← h1, ← h1, lc_smul, hΘ]
  have k0 := congrArg Prod.fst (hL ![1, 0])
  have k1 := congrArg Prod.fst (hL ![0, 1])
  have a0 := congrFun k0 0
  have a1 := congrFun k0 1
  have b1 := congrFun k1 1
  simp [lc, mv] at a0 a1 b1
  exact Prod.ext a0 (Prod.ext a1 b1)

theorem eq_zero_of_scalar {B : F} {C'' : F × F × F} (hB : ∀ y, (Θ (lc C'' y)).1 = B • sd (Φ y))
    (hdiag : ∃ y, (Φ y).1 ≠ 0 ∨ (Φ y).2.2 ≠ 0) : B = 0 := by
  obtain ⟨μ, ω, hω0, hω1, hΘ, hΦ⟩ := exists_scalar' hq Φ Φ' Θ h1 hgen hind hg₁ hg₂
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have hs : sqrtF ω + ω ≠ 0 := fun h => by
    have e := eq_of_add_eq_zero' h
    have e2 : ω + ω ^ 2 = 0 := by
      have := congrArg (· ^ 2) e
      simp only [sqrtF_sq] at this
      linear_combination this + ω ^ 2 * h2
    rcases eq_zero_or_one_of_add_sq e2 with h0 | h1'
    · exact hω0 h0
    · exact hω1 h1'
  obtain ⟨y, hy⟩ := hdiag
  have k := hB (μ • y)
  rw [lc_smul, hΘ, hB y, hΦ y] at k
  have k0 := congrFun k 0
  have k1 := congrFun k 1
  simp only [sd, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, Pi.smul_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, sqrtF_mul] at k0 k1
  have e0 : B * (sqrtF ω + ω) * sqrtF (Φ y).1 = 0 := by
    linear_combination k0 + B * sqrtF ω * sqrtF (Φ y).1 * h2
  have e1 : B * (sqrtF ω + ω) * sqrtF (Φ y).2.2 = 0 := by
    linear_combination k1 + B * sqrtF ω * sqrtF (Φ y).2.2 * h2
  by_contra hB0
  have hBs : B * (sqrtF ω + ω) ≠ 0 := mul_ne_zero hB0 hs
  rcases hy with h | h
  · exact h (by
      have := (mul_eq_zero.1 e0).resolve_left hBs
      rw [← sqrtF_sq (Φ y).1, this]; ring)
  · exact h (by
      have := (mul_eq_zero.1 e1).resolve_left hBs
      rw [← sqrtF_sq (Φ y).2.2, this]; ring)

theorem false_of_scalar {C : F × F × F} (hC : C ≠ 0) (hA : ∀ x, ∃ s, lc C x = Θ (0, s)) :
    False := by
  obtain ⟨μ, ω, hω0, hω1, hΘ, -⟩ := exists_scalar' hq Φ Φ' Θ h1 hgen hind hg₁ hg₂
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  let ι : F →+ (Fin 2 → F) × F := AddMonoidHom.inr _ _
  have hinj : Function.Injective (Θ.toAddMonoidHom.comp ι) := fun s s' h => by
    have := Θ.injective h
    exact congrArg Prod.snd this
  set A' := (Θ.toAddMonoidHom.comp ι).range with hA'def
  have hmem : ∀ s, Θ (0, s) ∈ A' := fun s => ⟨s, rfl⟩
  have hcard : Nat.card A' = Fintype.card F := by
    rw [← Nat.card_eq_fintype_card]
    exact (Nat.card_congr (AddMonoidHom.ofInjective hinj).toEquiv).symm
  have hωA : ∀ s, (ω • (Θ (0, s)).1, ω * (Θ (0, s)).2) ∈ A' := fun s => by
    rw [← hΘ]
    simpa [sc] using hmem (μ ^ 2 * s)
  have hA'' : ∀ x, lc C x ∈ A' := fun x => by
    obtain ⟨s, hs⟩ := hA x
    rw [hs]
    exact hmem s
  let f : ↥A' →+ (Fin 2 → F) := (AddMonoidHom.fst _ _).comp A'.subtype
  have hkr := AddSubgroup.card_ker_mul_card_range f
  rw [hcard] at hkr
  have hq1 : 1 < Fintype.card F := by omega
  by_cases hex : ∃ x₀, qv C x₀ ≠ 0
  · obtain ⟨x₀, hx₀⟩ := hex
    set m₀ := mv C x₀
    have hm₀ : m₀ ≠ 0 := fun h => hx₀ (by rw [qv_eq_dot, show mv C x₀ = m₀ from rfl, h,
      dot_zero_right])
    have hr : Fintype.card F ≤ Nat.card f.range := by
      let g : F → ↥f.range := fun c => ⟨c • m₀, ⟨⟨lc C (c • x₀), hA'' _⟩,
        by simp [f, lc, mv_smul_right, m₀]⟩⟩
      have hg : Function.Injective g := fun c c' h => by
        have h' : c • m₀ = c' • m₀ := congrArg Subtype.val h
        exact smul_left_injective F hm₀ h'
      have : Finite ↥f.range := Subtype.finite
      rw [← Nat.card_eq_fintype_card]
      exact Nat.card_le_card_of_injective g hg
    set v₀ := lc C x₀
    obtain ⟨s₀, hs₀⟩ := hA x₀
    have hd : (ω • v₀.1, ω * v₀.2) - lc C (ω • x₀) ∈ A' := by
      refine A'.sub_mem ?_ (hA'' _)
      rw [show v₀ = Θ (0, s₀) from hs₀]
      exact hωA s₀
    have hdk : (⟨_, hd⟩ : ↥A') ∈ f.ker := by
      show ((ω • v₀.1, ω * v₀.2) - lc C (ω • x₀)).1 = 0
      rw [lc_smul]
      simp [sc, v₀]
    have hd0 : (⟨_, hd⟩ : ↥A') ≠ 0 := fun h => by
      have h' := congrArg (fun v : ↥A' => (v : (Fin 2 → F) × F).2) h
      simp only [AddSubgroup.coe_zero, Prod.snd_zero, lc_smul, sc, Prod.snd_sub, v₀] at h'
      have e : (ω + ω ^ 2) * qv C x₀ = 0 := by
        simp only [lc] at h'
        linear_combination h' + ω ^ 2 * qv C x₀ * h2
      rcases mul_eq_zero.1 e with e1 | e1
      · rcases eq_zero_or_one_of_add_sq e1 with e2 | e2
        · exact hω0 e2
        · exact hω1 e2
      · exact hx₀ e1
    have hk2 : 2 ≤ Nat.card f.ker := by
      have : Finite ↥f.ker := Subtype.finite
      have h0k : (0 : ↥f.ker) ≠ ⟨_, hdk⟩ := fun h => hd0 (congrArg Subtype.val h).symm
      exact Finite.one_lt_card_iff_nontrivial.2 ⟨⟨0, _, h0k⟩⟩
    have : 2 * Fintype.card F ≤ Fintype.card F := by
      calc 2 * Fintype.card F ≤ Nat.card f.ker * Nat.card f.range := Nat.mul_le_mul hk2 hr
        _ = Fintype.card F := hkr
    omega
  · push Not at hex
    have hb : C.1 = 0 := by simpa [qv] using hex ![1, 0]
    have hd' : C.2.2 = 0 := by simpa [qv] using hex ![0, 1]
    have hc : C.2.1 ≠ 0 := fun h => hC (Prod.ext hb (Prod.ext h hd'))
    have htop : f.range = ⊤ := by
      refine eq_top_iff.2 fun a _ => ?_
      refine ⟨⟨lc C ![a 1 / C.2.1, a 0 / C.2.1], hA'' _⟩, ?_⟩
      show mv C ![a 1 / C.2.1, a 0 / C.2.1] = a
      refine vec2_ext ?_ ?_
      · simp [mv, hb, mul_div_cancel₀ _ hc]
      · simp [mv, hd', mul_div_cancel₀ _ hc]
    have hr : Nat.card f.range = Fintype.card F ^ 2 := by
      rw [htop, Nat.card_congr (AddEquiv.ofBijective (AddSubgroup.subtype ⊤)
        ⟨Subtype.val_injective, fun y => ⟨⟨y, AddSubgroup.mem_top y⟩, rfl⟩⟩).toEquiv,
        Nat.card_fun, Nat.card_eq_fintype_card (α := Fin 2), Fintype.card_fin,
        Nat.card_eq_fintype_card]
    have hk1 : 1 ≤ Nat.card f.ker := Nat.card_pos
    have : Fintype.card F ^ 2 ≤ Fintype.card F := by
      calc Fintype.card F ^ 2 = 1 * Nat.card f.range := by rw [hr, one_mul]
        _ ≤ Nat.card f.ker * Nat.card f.range := Nat.mul_le_mul_right _ hk1
        _ = Fintype.card F := hkr
    nlinarith

end Fin

end CFSG.Quasithin.MS93.S37R
