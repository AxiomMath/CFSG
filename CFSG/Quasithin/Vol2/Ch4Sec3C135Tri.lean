module

public import CFSG.Quasithin.Vol2.Ch4Sec3C136Uni
public import CFSG.Quasithin.Vol2.Ch4Sec3C136Off3

public section

namespace CFSG.Quasithin.H13.Ch4.C135

open Matrix CFSG.Quasithin CFSG.Quasithin.H13.Ch4
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

variable {F : Type} [Field F]

theorem card_fix_sq_le [Finite F] (Y : AddSubgroup (Fin 3 → F))
    (hY : ∀ (c : F) (y : Fin 3 → F), y ∈ Y → c • y ∈ Y) (φ : (Fin 3 → F) →+ (Fin 3 → F))
    {τ : F ≃+* F} (hτ : τ ≠ 1) (hφ : ∀ (c : F) (v : Fin 3 → F), φ (c • v) = τ c • φ v) :
    Nat.card {y // y ∈ Y ∧ φ y = y} ^ 2 ≤ Nat.card Y := by
  obtain ⟨θ, hθ⟩ : ∃ θ : F, τ θ ≠ θ := by
    by_contra h
    push Not at h
    exact hτ (RingEquiv.ext h)
  have hne : θ - τ θ ≠ 0 := sub_ne_zero.mpr (Ne.symm hθ)
  set C := {y // y ∈ Y ∧ φ y = y} with hC
  rw [sq, ← Nat.card_prod]
  refine Nat.card_le_card_of_injective (fun c : C × C =>
    (⟨(c.1 : Fin 3 → F) + θ • (c.2 : Fin 3 → F), Y.add_mem c.1.2.1 (hY θ _ c.2.2.1)⟩ : Y))
    fun c d h => ?_
  obtain ⟨⟨c₁, hc₁⟩, ⟨c₂, hc₂⟩⟩ := c
  obtain ⟨⟨d₁, hd₁⟩, ⟨d₂, hd₂⟩⟩ := d
  have e : c₁ + θ • c₂ = d₁ + θ • d₂ := congrArg Subtype.val h
  have e' := congrArg φ e
  rw [map_add, map_add, hφ, hφ, hc₁.2, hc₂.2, hd₁.2, hd₂.2] at e'
  have e2 : (θ - τ θ) • c₂ = (θ - τ θ) • d₂ := by
    rw [sub_smul, sub_smul]
    have := congrArg₂ (· - ·) e e'
    rw [add_sub_add_left_eq_sub, add_sub_add_left_eq_sub] at this
    exact this
  have hcd2 : c₂ = d₂ := smul_right_injective (Fin 3 → F) hne e2
  subst hcd2
  have hcd1 : c₁ = d₁ := add_right_cancel e
  subst hcd1
  rfl

section Ut

variable {u u' : SpecialLinearGroup (Fin 3) F}

theorem ut_entries (hu : u ∈ unitriangular 3 F) :
    (u : Matrix (Fin 3) (Fin 3) F) = !![1, (u : Matrix (Fin 3) (Fin 3) F) 0 1,
      (u : Matrix (Fin 3) (Fin 3) F) 0 2; 0, 1, (u : Matrix (Fin 3) (Fin 3) F) 1 2; 0, 0, 1] := by
  obtain ⟨h1, h2⟩ := hu
  ext i j
  fin_cases i <;> fin_cases j <;> simp [h2] <;> exact h1 _ _ (by decide)

theorem ut_mulVec (hu : u ∈ unitriangular 3 F) (v : Fin 3 → F) :
    (u : Matrix (Fin 3) (Fin 3) F) *ᵥ v = ![v 0 + (u : Matrix (Fin 3) (Fin 3) F) 0 1 * v 1 +
      (u : Matrix (Fin 3) (Fin 3) F) 0 2 * v 2, v 1 + (u : Matrix (Fin 3) (Fin 3) F) 1 2 * v 2,
        v 2] := by
  rw [ut_entries hu]
  funext i
  fin_cases i <;> simp [mulVec, dotProduct, Fin.sum_univ_three]

theorem ut_tmulVec (hu : u ∈ unitriangular 3 F) (v : Fin 3 → F) :
    (u : Matrix (Fin 3) (Fin 3) F)ᵀ *ᵥ v = ![v 0, (u : Matrix (Fin 3) (Fin 3) F) 0 1 * v 0 + v 1,
      (u : Matrix (Fin 3) (Fin 3) F) 0 2 * v 0 + (u : Matrix (Fin 3) (Fin 3) F) 1 2 * v 1 +
        v 2] := by
  rw [ut_entries hu]
  funext i
  fin_cases i <;> simp [mulVec, dotProduct, Fin.sum_univ_three]

theorem ut_mul (hu : u ∈ unitriangular 3 F) (hu' : u' ∈ unitriangular 3 F) :
    ((u * u' : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 0 1 =
      (u : Matrix (Fin 3) (Fin 3) F) 0 1 + (u' : Matrix (Fin 3) (Fin 3) F) 0 1 ∧
    ((u * u' : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 1 2 =
      (u : Matrix (Fin 3) (Fin 3) F) 1 2 + (u' : Matrix (Fin 3) (Fin 3) F) 1 2 ∧
    ((u * u' : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 0 2 =
      (u : Matrix (Fin 3) (Fin 3) F) 0 2 + (u' : Matrix (Fin 3) (Fin 3) F) 0 2 +
        (u : Matrix (Fin 3) (Fin 3) F) 0 1 * (u' : Matrix (Fin 3) (Fin 3) F) 1 2 := by
  have e : ((u * u' : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      (u : Matrix (Fin 3) (Fin 3) F) * (u' : Matrix (Fin 3) (Fin 3) F) := rfl
  rw [e, ut_entries hu, ut_entries hu']
  simp [Matrix.mul_apply, Fin.sum_univ_three]
  refine ⟨by ring, by ring, by ring⟩

theorem ut_ext (hu : u ∈ unitriangular 3 F) (hu' : u' ∈ unitriangular 3 F)
    (h01 : (u : Matrix (Fin 3) (Fin 3) F) 0 1 = (u' : Matrix (Fin 3) (Fin 3) F) 0 1)
    (h02 : (u : Matrix (Fin 3) (Fin 3) F) 0 2 = (u' : Matrix (Fin 3) (Fin 3) F) 0 2)
    (h12 : (u : Matrix (Fin 3) (Fin 3) F) 1 2 = (u' : Matrix (Fin 3) (Fin 3) F) 1 2) : u = u' := by
  apply Subtype.ext
  rw [ut_entries hu, ut_entries hu', h01, h02, h12]

theorem ut_one_iff (hu : u ∈ unitriangular 3 F) :
    u = 1 ↔ (u : Matrix (Fin 3) (Fin 3) F) 0 1 = 0 ∧ (u : Matrix (Fin 3) (Fin 3) F) 0 2 = 0 ∧
      (u : Matrix (Fin 3) (Fin 3) F) 1 2 = 0 := by
  constructor
  · rintro rfl
    exact ⟨one_apply_ne (by decide), one_apply_ne (by decide), one_apply_ne (by decide)⟩
  · rintro ⟨h1, h2, h3⟩
    exact ut_ext hu (unitriangular 3 F).one_mem (by simp [h1]) (by simp [h2]) (by simp [h3])

theorem ut_sq [CharP F 2] (hu : u ∈ unitriangular 3 F) (hs : u * u = 1) :
    (u : Matrix (Fin 3) (Fin 3) F) 0 1 * (u : Matrix (Fin 3) (Fin 3) F) 1 2 = 0 := by
  have h := (ut_mul hu hu).2.2
  rw [hs] at h
  have h0 : ((1 : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 0 2 = 0 :=
    one_apply_ne (by decide)
  rw [h0] at h
  have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
  linear_combination -h - (u : Matrix (Fin 3) (Fin 3) F) 0 2 * h2

end Ut

theorem exists_indep_of_card [Finite F] {ι : Type*} [Finite ι] (p : ι → F × F)
    (hp : Function.Injective p) (hcard : Nat.card F < Nat.card ι) {i₀ : ι} (hi₀ : p i₀ ≠ 0) :
    ∃ i j, (p i).1 * (p j).2 ≠ (p j).1 * (p i).2 := by
  by_contra h
  push Not at h
  by_cases ha : (p i₀).1 = 0
  ·
    have hc : (p i₀).2 ≠ 0 := fun hc => hi₀ (Prod.ext ha hc)
    have h1 : ∀ i, (p i).1 = 0 := fun i => by
      have := h i i₀
      rw [ha, zero_mul] at this
      exact (mul_eq_zero.mp this).resolve_right hc
    have hinj : Function.Injective (fun i => (p i).2) := fun i j hij =>
      hp (Prod.ext (by rw [h1, h1]) hij)
    have := Nat.card_le_card_of_injective _ hinj
    omega
  · have hinj : Function.Injective (fun i => (p i).1) := by
      intro i j hij
      apply hp
      have e1 := h i i₀
      have e2 := h j i₀
      simp only at hij
      refine Prod.ext hij ?_
      have e3 : (p i₀).1 * ((p i).2 - (p j).2) = 0 := by
        rw [hij] at e1
        linear_combination e2 - e1
      exact sub_eq_zero.mp ((mul_eq_zero.mp e3).resolve_left ha)
    have := Nat.card_le_card_of_injective _ hinj
    omega

theorem card_le_sq_of_lin [Finite F] {S : Set (Fin 3 → F)} {a c : F} (hac : (a, c) ≠ 0)
    (h : ∀ v ∈ S, a * v 1 + c * v 2 = 0) : Nat.card S ≤ Nat.card F ^ 2 := by
  rw [sq, ← Nat.card_prod]
  by_cases hc : c = 0
  · have ha : a ≠ 0 := fun ha => hac (by rw [ha, hc]; rfl)
    refine Nat.card_le_card_of_injective (fun v => ((v : Fin 3 → F) 0, (v : Fin 3 → F) 2))
      fun v w hvw => Subtype.ext ?_
    simp only [Prod.mk.injEq] at hvw
    have e1 := h v v.2
    have e2 := h w w.2
    rw [hc, zero_mul, add_zero] at e1 e2
    have h1 := (mul_eq_zero.mp e1).resolve_left ha
    have h2 := (mul_eq_zero.mp e2).resolve_left ha
    funext i
    fin_cases i
    · exact hvw.1
    · exact h1.trans h2.symm
    · exact hvw.2
  · refine Nat.card_le_card_of_injective (fun v => ((v : Fin 3 → F) 0, (v : Fin 3 → F) 1))
      fun v w hvw => Subtype.ext ?_
    simp only [Prod.mk.injEq] at hvw
    have e1 := h v v.2
    have e2 := h w w.2
    have h3 : c * ((v : Fin 3 → F) 2 - (w : Fin 3 → F) 2) = 0 := by
      rw [hvw.2] at e1
      linear_combination e1 - e2
    funext i
    fin_cases i
    · exact hvw.1
    · exact hvw.2
    · exact sub_eq_zero.mp ((mul_eq_zero.mp h3).resolve_left hc)

theorem card_le_of_two_lin [Finite F] {S : Set (Fin 3 → F)} {a c a' c' : F}
    (hdet : a * c' ≠ a' * c) (h : ∀ v ∈ S, a * v 1 + c * v 2 = 0 ∧ a' * v 1 + c' * v 2 = 0) :
    Nat.card S ≤ Nat.card F := by
  refine Nat.card_le_card_of_injective (fun v => (v : Fin 3 → F) 0) fun v w hvw => Subtype.ext ?_
  have hz : ∀ x ∈ S, x 1 = 0 ∧ x 2 = 0 := by
    intro x hx
    obtain ⟨e1, e2⟩ := h x hx
    have hne : a * c' - a' * c ≠ 0 := sub_ne_zero.mpr hdet
    refine ⟨?_, ?_⟩
    · have e : (a * c' - a' * c) * x 1 = 0 := by linear_combination c' * e1 - c * e2
      exact (mul_eq_zero.mp e).resolve_left hne
    · have e : (a * c' - a' * c) * x 2 = 0 := by linear_combination a * e2 - a' * e1
      exact (mul_eq_zero.mp e).resolve_left hne
  funext i
  fin_cases i
  · exact hvw
  · exact (hz _ v.2).1.trans (hz _ w.2).1.symm
  · exact (hz _ v.2).2.trans (hz _ w.2).2.symm

theorem card_le_sq_of_coord [Finite F] {S : Set (Fin 3 → F)} {k : Fin 3}
    (h : ∀ v ∈ S, v k = 0) : Nat.card S ≤ Nat.card F ^ 2 := by
  classical
  rw [sq, ← Nat.card_prod]
  obtain ⟨i, j, hik, hjk, hij⟩ : ∃ i j : Fin 3, i ≠ k ∧ j ≠ k ∧ i ≠ j := by
    fin_cases k
    · exact ⟨1, 2, by decide, by decide, by decide⟩
    · exact ⟨0, 2, by decide, by decide, by decide⟩
    · exact ⟨0, 1, by decide, by decide, by decide⟩
  refine Nat.card_le_card_of_injective (fun v => ((v : Fin 3 → F) i, (v : Fin 3 → F) j))
    fun v w hvw => Subtype.ext ?_
  simp only [Prod.mk.injEq] at hvw
  funext l
  by_cases hli : l = i
  · rw [hli]; exact hvw.1
  by_cases hlj : l = j
  · rw [hlj]; exact hvw.2
  have hlk : l = k := by
    fin_cases l <;> fin_cases i <;> fin_cases j <;> fin_cases k <;> simp_all
  rw [hlk, h _ v.2, h _ w.2]

theorem card_mul_le_of_ut [Finite F] [CharP F 2] {Pg : Subgroup (SpecialLinearGroup (Fin 3) F)}
    (hU : Pg ≤ unitriangular 3 F) (hs : ∀ x ∈ Pg, x * x = 1) (hne : Pg ≠ ⊥) :
    Nat.card Pg * Nat.card F * Nat.card {v : Fin 3 → F // ∀ X ∈ Pg,
      (X : Matrix (Fin 3) (Fin 3) F) *ᵥ v = v} *
      Nat.card {v : Fin 3 → F // ∀ X ∈ Pg, (X : Matrix (Fin 3) (Fin 3) F)ᵀ *ᵥ v = v} ≤
        Nat.card F ^ 6 ∧ Nat.card Pg ≤ Nat.card F ^ 2 := by
  classical
  set q := Nat.card F with hq
  obtain ⟨u₀, hu₀, hu₀1⟩ := (Pg.bot_or_exists_ne_one).resolve_left hne
  have hu₀U := hU hu₀
  set f₀ := Nat.card {v : Fin 3 → F // ∀ X ∈ Pg, (X : Matrix (Fin 3) (Fin 3) F) *ᵥ v = v}
  set f₁ := Nat.card {v : Fin 3 → F // ∀ X ∈ Pg, (X : Matrix (Fin 3) (Fin 3) F)ᵀ *ᵥ v = v}
  have hq0 : 0 < q := Nat.card_pos
  have htype : (∀ u ∈ Pg, (u : Matrix (Fin 3) (Fin 3) F) 1 2 = 0) ∨
      (∀ u ∈ Pg, (u : Matrix (Fin 3) (Fin 3) F) 0 1 = 0) := by
    by_contra h
    push Not at h
    obtain ⟨⟨u, hu, hu12⟩, ⟨u', hu', hu'01⟩⟩ := h
    have h1 := ut_sq (hU hu) (hs u hu)
    have h2 := ut_sq (hU hu') (hs u' hu')
    have h3 := ut_sq (hU (Pg.mul_mem hu hu')) (hs _ (Pg.mul_mem hu hu'))
    obtain ⟨e01, e12, -⟩ := ut_mul (hU hu) (hU hu')
    rw [e01, e12] at h3
    have ha : (u : Matrix (Fin 3) (Fin 3) F) 0 1 = 0 := (mul_eq_zero.mp h1).resolve_right hu12
    have hb : (u' : Matrix (Fin 3) (Fin 3) F) 1 2 = 0 := (mul_eq_zero.mp h2).resolve_left hu'01
    rw [ha, hb, zero_add, add_zero] at h3
    exact (mul_ne_zero hu'01 hu12) h3
  rcases htype with hA | hB
  ·
    have hpinj : Function.Injective (fun u : ↥Pg =>
        ((u : Matrix (Fin 3) (Fin 3) F) 0 1, (u : Matrix (Fin 3) (Fin 3) F) 0 2)) := by
      intro u u' h
      simp only [Prod.mk.injEq] at h
      exact Subtype.ext (ut_ext (hU u.2) (hU u'.2) h.1 h.2 (by rw [hA _ u.2, hA _ u'.2]))
    have hcard : Nat.card Pg ≤ q ^ 2 := by
      rw [sq, ← Nat.card_prod]
      exact Nat.card_le_card_of_injective _ hpinj
    have hu₀ac : ((u₀ : Matrix (Fin 3) (Fin 3) F) 0 1, (u₀ : Matrix (Fin 3) (Fin 3) F) 0 2) ≠
        0 := by
      intro h0
      apply hu₀1
      rw [ut_one_iff hu₀U]
      exact ⟨congrArg Prod.fst h0, congrArg Prod.snd h0, hA _ hu₀⟩
    have hnat : ∀ v, (∀ X ∈ Pg, (X : Matrix (Fin 3) (Fin 3) F) *ᵥ v = v) → ∀ u ∈ Pg,
        (u : Matrix (Fin 3) (Fin 3) F) 0 1 * v 1 + (u : Matrix (Fin 3) (Fin 3) F) 0 2 * v 2 =
          0 := by
      intro v hv u hu
      have h1 := congrFun (hv u hu) 0
      rw [ut_mulVec (hU hu)] at h1
      simp only [Matrix.cons_val_zero] at h1
      linear_combination h1
    have hdual : f₁ ≤ q ^ 2 := by
      refine card_le_sq_of_coord (S := {v | ∀ X ∈ Pg, (X : Matrix (Fin 3) (Fin 3) F)ᵀ *ᵥ v = v})
        (k := 0) fun v hv => ?_
      have h1 := congrFun (hv u₀ hu₀) 1
      have h2 := congrFun (hv u₀ hu₀) 2
      rw [ut_tmulVec hu₀U] at h1 h2
      simp only [Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
        Matrix.cons_val_zero] at h1 h2
      rw [hA _ hu₀] at h2
      by_contra hv0
      apply hu₀ac
      refine Prod.ext ?_ ?_
      · exact (mul_eq_zero.mp (by linear_combination h1)).resolve_right hv0
      · exact (mul_eq_zero.mp (by linear_combination h2)).resolve_right hv0
    refine ⟨?_, hcard⟩
    by_cases hsmall : Nat.card Pg ≤ q
    · have hf₀ : f₀ ≤ q ^ 2 := card_le_sq_of_lin
        (S := {v | ∀ X ∈ Pg, (X : Matrix (Fin 3) (Fin 3) F) *ᵥ v = v}) hu₀ac
        fun v hv => hnat v hv u₀ hu₀
      calc Nat.card Pg * q * f₀ * f₁ ≤ q * q * q ^ 2 * q ^ 2 := by gcongr
        _ = q ^ 6 := by ring
    · push Not at hsmall
      obtain ⟨u, u', hdet⟩ := exists_indep_of_card _ hpinj hsmall (i₀ := ⟨u₀, hu₀⟩) hu₀ac
      have hf₀ : f₀ ≤ q := card_le_of_two_lin
        (S := {v | ∀ X ∈ Pg, (X : Matrix (Fin 3) (Fin 3) F) *ᵥ v = v}) hdet
        fun v hv => ⟨hnat v hv u u.2, hnat v hv u' u'.2⟩
      calc Nat.card Pg * q * f₀ * f₁ ≤ q ^ 2 * q * q * q ^ 2 := by gcongr
        _ = q ^ 6 := by ring
  ·
    have hpinj : Function.Injective (fun u : ↥Pg =>
        ((u : Matrix (Fin 3) (Fin 3) F) 1 2, (u : Matrix (Fin 3) (Fin 3) F) 0 2)) := by
      intro u u' h
      simp only [Prod.mk.injEq] at h
      exact Subtype.ext (ut_ext (hU u.2) (hU u'.2) (by rw [hB _ u.2, hB _ u'.2]) h.2 h.1)
    have hcard : Nat.card Pg ≤ q ^ 2 := by
      rw [sq, ← Nat.card_prod]
      exact Nat.card_le_card_of_injective _ hpinj
    have hu₀bc : ((u₀ : Matrix (Fin 3) (Fin 3) F) 1 2, (u₀ : Matrix (Fin 3) (Fin 3) F) 0 2) ≠
        0 := by
      intro h0
      apply hu₀1
      rw [ut_one_iff hu₀U]
      exact ⟨hB _ hu₀, congrArg Prod.snd h0, congrArg Prod.fst h0⟩
    have hdu : ∀ v, (∀ X ∈ Pg, (X : Matrix (Fin 3) (Fin 3) F)ᵀ *ᵥ v = v) → ∀ u ∈ Pg,
        (u : Matrix (Fin 3) (Fin 3) F) 1 2 * v 1 + (u : Matrix (Fin 3) (Fin 3) F) 0 2 * v 0 =
          0 := by
      intro v hv u hu
      have h1 := congrFun (hv u hu) 2
      rw [ut_tmulVec (hU hu)] at h1
      simp only [Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at h1
      linear_combination h1
    let sw : (Fin 3 → F) → (Fin 3 → F) := fun v => ![v 2, v 1, v 0]
    have hsw_inj : Function.Injective sw := by
      intro v w h
      funext i
      have h0 := congrFun h 0
      have h1 := congrFun h 1
      have h2 := congrFun h 2
      simp only [sw, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.head_cons, Matrix.tail_cons] at h0 h1 h2
      fin_cases i
      · exact h2
      · exact h1
      · exact h0
    have hnat : f₀ ≤ q ^ 2 := by
      refine card_le_sq_of_coord (S := {v | ∀ X ∈ Pg, (X : Matrix (Fin 3) (Fin 3) F) *ᵥ v = v})
        (k := 2) fun v hv => ?_
      have h0 := congrFun (hv u₀ hu₀) 0
      have h1 := congrFun (hv u₀ hu₀) 1
      rw [ut_mulVec hu₀U] at h0 h1
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h1
      rw [hB _ hu₀, zero_mul, add_zero] at h0
      by_contra hv2
      apply hu₀bc
      refine Prod.ext ?_ ?_
      · exact (mul_eq_zero.mp (by linear_combination h1)).resolve_right hv2
      · exact (mul_eq_zero.mp (by linear_combination h0)).resolve_right hv2
    let S₁ : Set (Fin 3 → F) := {v | ∀ X ∈ Pg, (X : Matrix (Fin 3) (Fin 3) F)ᵀ *ᵥ v = v}
    let S₂ : Set (Fin 3 → F) := sw '' S₁
    have hS₂ : Nat.card S₂ = f₁ := Nat.card_image_of_injective hsw_inj S₁
    have hlin₂ : ∀ u ∈ Pg, ∀ w ∈ S₂, (u : Matrix (Fin 3) (Fin 3) F) 1 2 * w 1 +
        (u : Matrix (Fin 3) (Fin 3) F) 0 2 * w 2 = 0 := by
      rintro u hu _ ⟨v, hv, rfl⟩
      have := hdu v hv u hu
      simpa [sw] using this
    refine ⟨?_, hcard⟩
    by_cases hsmall : Nat.card Pg ≤ q
    · have hf₁ : f₁ ≤ q ^ 2 := by
        rw [← hS₂]
        exact card_le_sq_of_lin hu₀bc (hlin₂ u₀ hu₀)
      calc Nat.card Pg * q * f₀ * f₁ ≤ q * q * q ^ 2 * q ^ 2 := by gcongr
        _ = q ^ 6 := by ring
    · push Not at hsmall
      obtain ⟨u, u', hdet⟩ := exists_indep_of_card _ hpinj hsmall (i₀ := ⟨u₀, hu₀⟩) hu₀bc
      have hf₁ : f₁ ≤ q := by
        rw [← hS₂]
        exact card_le_of_two_lin hdet fun w hw => ⟨hlin₂ u u.2 w hw, hlin₂ u' u'.2 w hw⟩
      calc Nat.card Pg * q * f₀ * f₁ ≤ q ^ 2 * q * q ^ 2 * q := by gcongr
        _ = q ^ 6 := by ring

theorem lin_offender [Finite F] [CharP F 2] {Pg : Subgroup (SpecialLinearGroup (Fin 3) F)}
    (hs : ∀ x ∈ Pg, x * x = 1) (hne : Pg ≠ ⊥) :
    Nat.card Pg * Nat.card F * Nat.card {v : Fin 3 → F // ∀ X ∈ Pg,
      (X : Matrix (Fin 3) (Fin 3) F) *ᵥ v = v} *
      Nat.card {v : Fin 3 → F // ∀ X ∈ Pg, (X : Matrix (Fin 3) (Fin 3) F)ᵀ *ᵥ v = v} ≤
        Nat.card F ^ 6 ∧ Nat.card Pg ≤ Nat.card F ^ 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP2 : IsPGroup 2 Pg := fun x => ⟨1, Subtype.ext (by
    simpa [pow_one, sq] using hs x x.2)⟩
  obtain ⟨g, hg⟩ := exists_conj_unitriangular_of_isPGroup hP2
  set Pg' := Pg.map (MulAut.conj g⁻¹).toMonoidHom with hPg'
  have hconj : ∀ y, (MulAut.conj g⁻¹).toMonoidHom y = g⁻¹ * y * g := fun y => by
    simp
  have hU : Pg' ≤ unitriangular 3 F := by
    rintro _ ⟨y, hy, rfl⟩
    rw [hconj]
    exact hg y hy
  have hs' : ∀ x ∈ Pg', x * x = 1 := by
    rintro _ ⟨y, hy, rfl⟩
    rw [← map_mul, hs y hy, map_one]
  have hne' : Pg' ≠ ⊥ := fun h =>
    hne ((Subgroup.map_eq_bot_iff_of_injective _ (MulAut.conj g⁻¹).injective).mp h)
  obtain ⟨h1, h2⟩ := card_mul_le_of_ut hU hs' hne'
  have hcard : Nat.card Pg' = Nat.card Pg :=
    Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective
  rw [hcard] at h1 h2
  refine ⟨le_trans ?_ h1, h2⟩
  have hg1 : (g : Matrix (Fin 3) (Fin 3) F) * ((g⁻¹ : SpecialLinearGroup (Fin 3) F) :
      Matrix (Fin 3) (Fin 3) F) = 1 :=
    congrArg Subtype.val (mul_inv_cancel g)
  have hg2 : ((g⁻¹ : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *
      (g : Matrix (Fin 3) (Fin 3) F) = 1 :=
    congrArg Subtype.val (inv_mul_cancel g)
  have hcoe : ∀ y : SpecialLinearGroup (Fin 3) F,
      (((MulAut.conj g⁻¹).toMonoidHom y : SpecialLinearGroup (Fin 3) F) :
        Matrix (Fin 3) (Fin 3) F) = ((g⁻¹ : SpecialLinearGroup (Fin 3) F) :
          Matrix (Fin 3) (Fin 3) F) * y * g := fun y => by
    rw [hconj]
    rfl
  gcongr ?_ * _ * ?_ * ?_
  · exact le_of_eq rfl
  · refine Nat.card_le_card_of_injective (fun v => ⟨((g⁻¹ : SpecialLinearGroup (Fin 3) F) :
      Matrix (Fin 3) (Fin 3) F) *ᵥ v.1, ?_⟩) fun v w hvw => ?_
    · rintro _ ⟨y, hy, rfl⟩
      rw [hcoe, mulVec_mulVec, Matrix.mul_assoc, Matrix.mul_assoc, hg1, Matrix.mul_one,
        ← mulVec_mulVec, v.2 y hy]
    · have h := congrArg (fun x : {x : Fin 3 → F // _} => (g : Matrix (Fin 3) (Fin 3) F) *ᵥ x.1)
        hvw
      simp only [mulVec_mulVec, hg1, one_mulVec] at h
      exact Subtype.ext h
  · refine Nat.card_le_card_of_injective (fun v => ⟨(g : Matrix (Fin 3) (Fin 3) F)ᵀ *ᵥ v.1,
      ?_⟩) fun v w hvw => ?_
    · rintro _ ⟨y, hy, rfl⟩
      rw [hcoe, transpose_mul, transpose_mul, mulVec_mulVec, Matrix.mul_assoc,
        Matrix.mul_assoc, ← transpose_mul, hg1, transpose_one, Matrix.mul_one,
        ← mulVec_mulVec, v.2 y hy]
    · have h0 : (g : Matrix (Fin 3) (Fin 3) F)ᵀ *ᵥ v.1 = (g : Matrix (Fin 3) (Fin 3) F)ᵀ *ᵥ w.1 :=
        congrArg Subtype.val hvw
      have h : ((g⁻¹ : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)ᵀ *ᵥ
          ((g : Matrix (Fin 3) (Fin 3) F)ᵀ *ᵥ v.1) =
          ((g⁻¹ : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)ᵀ *ᵥ
            ((g : Matrix (Fin 3) (Fin 3) F)ᵀ *ᵥ w.1) := by rw [h0]
      rw [mulVec_mulVec, mulVec_mulVec, ← transpose_mul, hg1, transpose_one, one_mulVec,
        one_mulVec] at h
      exact Subtype.ext h

section Semi

omit [Field F] in
theorem card_fun3' [Finite F] : Nat.card (Fin 3 → F) = Nat.card F ^ 3 := by
  rw [Nat.card_fun, Nat.card_fin]

variable {E : Type*} [Group E]

abbrev fixAll (ρ : E →* Equiv.Perm (Fin 3 → F)) : Type _ := {v : Fin 3 → F // ∀ x, ρ x v = v}

theorem tri_offender [Finite F] [CharP F 2] (ρ₀ ρ₁ ρ₂ : E →* Equiv.Perm (Fin 3 → F))
    (σ σ₁ σ₂ : E → (F ≃+* F)) (hsq : ∀ x : E, x * x = 1)
    (hadd₀ : ∀ x v w, ρ₀ x (v + w) = ρ₀ x v + ρ₀ x w)
    (hadd₁ : ∀ x v w, ρ₁ x (v + w) = ρ₁ x v + ρ₁ x w)
    (hadd₂ : ∀ x v w, ρ₂ x (v + w) = ρ₂ x v + ρ₂ x w)
    (hsemi₀ : ∀ x (c : F) v, ρ₀ x (c • v) = σ x c • ρ₀ x v)
    (hsemi₁ : ∀ x (c : F) v, ρ₁ x (c • v) = σ₁ x c • ρ₁ x v)
    (hsemi₂ : ∀ x (c : F) v, ρ₂ x (c • v) = σ₂ x c • ρ₂ x v)
    (hnl₁ : ∀ x, σ x ≠ 1 → σ₁ x ≠ 1) (hnl₂ : ∀ x, σ x ≠ 1 → σ₂ x ≠ 1)
    (hlin : ∀ x, σ x = 1 → ∃ P : SpecialLinearGroup (Fin 3) F,
      (∀ v, ρ₀ x v = (P : Matrix (Fin 3) (Fin 3) F) *ᵥ v) ∧
      (∀ v, ρ₁ x v = (P : Matrix (Fin 3) (Fin 3) F)ᵀ *ᵥ v) ∧
      (∀ v, ρ₂ x v = (P : Matrix (Fin 3) (Fin 3) F)ᵀ *ᵥ v))
    (hne : ρ₀.range ≠ ⊥) :
    Nat.card ρ₀.range * Nat.card F * Nat.card (fixAll ρ₀) * Nat.card (fixAll ρ₁) <
        2 * Nat.card F ^ 6 ∧
      Nat.card ρ₀.range * Nat.card (fixAll ρ₀) * Nat.card (fixAll ρ₂) < 2 * Nat.card F ^ 6 := by
  classical
  set q := Nat.card F with hq
  have hq2 : 2 ≤ q := two_le_card_field
  have hq0 : 0 < q := by omega
  have e0 : (Pi.single 0 1 : Fin 3 → F) ≠ 0 := fun h => by simpa using congrFun h 0
  have hσmul : ∀ x y, σ (x * y) = σ x * σ y := by
    intro x y
    refine RingEquiv.ext fun c => ?_
    have h1 := hsemi₀ (x * y) c (Pi.single 0 1)
    rw [map_mul, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hsemi₀, hsemi₀] at h1
    have hzero : ∀ z, ρ₀ z 0 = 0 := fun z => by
      have := hadd₀ z 0 0
      rw [add_zero] at this
      exact (left_eq_add.mp this)
    have hne0 : ρ₀ x (ρ₀ y (Pi.single 0 1)) ≠ 0 := by
      intro h0
      apply e0
      have := (ρ₀ x).injective (h0.trans (hzero x).symm)
      exact (ρ₀ y).injective (this.trans (hzero y).symm)
    exact (smul_left_injective F hne0 h1).symm
  have hσone : σ 1 = 1 := by
    refine RingEquiv.ext fun c => ?_
    have h1 := hsemi₀ 1 c (Pi.single 0 1)
    rw [map_one, Equiv.Perm.one_apply, Equiv.Perm.one_apply] at h1
    exact (smul_left_injective F e0 h1).symm
  have hσsq : ∀ x, σ x * σ x = 1 := fun x => by rw [← hσmul, hsq, hσone]
  let EL : Subgroup E :=
    { carrier := {x | σ x = 1}
      mul_mem' := fun {x y} hx hy => by
        show σ (x * y) = 1
        rw [hσmul, show σ x = 1 from hx, show σ y = 1 from hy, one_mul]
      one_mem' := hσone
      inv_mem' := fun {x} hx => by
        have e : x⁻¹ = x := inv_eq_of_mul_eq_one_right (hsq x)
        show σ x⁻¹ = 1
        rw [e]
        exact hx }
  have hmemEL : ∀ x, x ∈ EL ↔ σ x = 1 := fun x => Iff.rfl
  choose! P hP using hlin
  have hPunique : ∀ {A B : SpecialLinearGroup (Fin 3) F},
      (∀ v, (A : Matrix (Fin 3) (Fin 3) F) *ᵥ v = (B : Matrix (Fin 3) (Fin 3) F) *ᵥ v) → A = B :=
    fun h => Subtype.ext (matrix_eq_of_mulVec_eq h)
  let PH : ↥EL →* SpecialLinearGroup (Fin 3) F :=
    { toFun := fun x => P x
      map_one' := hPunique fun v => by
        show (P 1 : Matrix (Fin 3) (Fin 3) F) *ᵥ v =
          ((1 : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ v
        rw [← (hP 1 hσone).1, map_one, Equiv.Perm.one_apply]
        exact (one_mulVec v).symm
      map_mul' := fun x y => hPunique fun v => by
        show (P ((x : E) * y) : Matrix (Fin 3) (Fin 3) F) *ᵥ v =
          ((P x : Matrix (Fin 3) (Fin 3) F) * (P y : Matrix (Fin 3) (Fin 3) F)) *ᵥ v
        rw [← (hP ((x : E) * y) (x * y).2).1, ← mulVec_mulVec, ← (hP (y : E) y.2).1,
          ← (hP (x : E) x.2).1, map_mul, Equiv.Perm.mul_apply] }
  set Pg := PH.range with hPg
  have hPH : ∀ x : ↥EL, PH x = P x := fun x => rfl
  have hfixEL₀ : ∀ v, (∀ x ∈ EL, ρ₀ x v = v) ↔ ∀ X ∈ Pg, (X : Matrix (Fin 3) (Fin 3) F) *ᵥ v = v :=
    fun v => ⟨fun h => by
      rintro _ ⟨x, rfl⟩
      rw [hPH, ← (hP _ x.2).1]
      exact h x x.2, fun h x hx => by
      rw [(hP x hx).1]
      exact h _ ⟨⟨x, hx⟩, rfl⟩⟩
  have hfixEL₁ : ∀ v, (∀ x ∈ EL, ρ₁ x v = v) ↔
      ∀ X ∈ Pg, (X : Matrix (Fin 3) (Fin 3) F)ᵀ *ᵥ v = v :=
    fun v => ⟨fun h => by
      rintro _ ⟨x, rfl⟩
      rw [hPH, ← (hP _ x.2).2.1]
      exact h x x.2, fun h x hx => by
      rw [(hP x hx).2.1]
      exact h _ ⟨⟨x, hx⟩, rfl⟩⟩
  have hfixEL₂ : ∀ v, (∀ x ∈ EL, ρ₂ x v = v) ↔
      ∀ X ∈ Pg, (X : Matrix (Fin 3) (Fin 3) F)ᵀ *ᵥ v = v :=
    fun v => ⟨fun h => by
      rintro _ ⟨x, rfl⟩
      rw [hPH, ← (hP _ x.2).2.2]
      exact h x x.2, fun h x hx => by
      rw [(hP x hx).2.2]
      exact h _ ⟨⟨x, hx⟩, rfl⟩⟩
  have hcardEL : Nat.card (EL.map ρ₀) = Nat.card Pg := by
    refine Nat.card_congr (Equiv.ofBijective (fun y => ⟨P (Classical.choose y.2),
      ⟨⟨_, (Classical.choose_spec y.2).1⟩, rfl⟩⟩) ⟨fun y y' h => ?_, fun X => ?_⟩)
    · have h1 := congrArg Subtype.val h
      simp only at h1
      apply Subtype.ext
      rw [← (Classical.choose_spec y.2).2, ← (Classical.choose_spec y'.2).2]
      refine Equiv.ext fun v => ?_
      rw [(hP _ (Classical.choose_spec y.2).1).1, (hP _ (Classical.choose_spec y'.2).1).1, h1]
    · obtain ⟨_, ⟨x, rfl⟩⟩ := X
      refine ⟨⟨ρ₀ x, ⟨x, x.2, rfl⟩⟩, Subtype.ext (hPunique fun v => ?_)⟩
      simp only
      rw [← (hP _ (Classical.choose_spec (⟨ρ₀ x, ⟨x, x.2, rfl⟩⟩ : ↥(EL.map ρ₀)).2).1).1,
        (Classical.choose_spec (⟨ρ₀ x, ⟨x, x.2, rfl⟩⟩ : ↥(EL.map ρ₀)).2).2, hPH,
        ← (hP _ x.2).1]
  have hle_EL : Nat.card (EL.map ρ₀) ≤ Nat.card ρ₀.range :=
    Subgroup.card_le_of_le (by rintro _ ⟨x, -, rfl⟩; exact ⟨x, rfl⟩)
  have hPgs : ∀ X ∈ Pg, X * X = 1 := by
    rintro _ ⟨x, rfl⟩
    rw [← map_mul, show x * x = 1 from Subtype.ext (hsq x), map_one]
  have hPgfix₀ : Nat.card {v // ∀ x ∈ EL, ρ₀ x v = v} =
      Nat.card {v : Fin 3 → F // ∀ X ∈ Pg, (X : Matrix (Fin 3) (Fin 3) F) *ᵥ v = v} :=
    Nat.card_congr (Equiv.subtypeEquivRight hfixEL₀)
  have hPgfix₁ : Nat.card {v // ∀ x ∈ EL, ρ₁ x v = v} =
      Nat.card {v : Fin 3 → F // ∀ X ∈ Pg, (X : Matrix (Fin 3) (Fin 3) F)ᵀ *ᵥ v = v} :=
    Nat.card_congr (Equiv.subtypeEquivRight hfixEL₁)
  have hPgfix₂ : Nat.card {v // ∀ x ∈ EL, ρ₂ x v = v} =
      Nat.card {v : Fin 3 → F // ∀ X ∈ Pg, (X : Matrix (Fin 3) (Fin 3) F)ᵀ *ᵥ v = v} :=
    Nat.card_congr (Equiv.subtypeEquivRight hfixEL₂)
  have hsqlt : ∀ a b : ℕ, a ^ 2 < b ^ 2 → a < b := fun a b h =>
    lt_of_pow_lt_pow_left₀ 2 (Nat.zero_le b) h
  by_cases hall : ∀ x, σ x = 1
  ·
    have hrange : ρ₀.range = EL.map ρ₀ := by
      ext y
      exact ⟨fun ⟨x, hx⟩ => ⟨x, hall x, hx⟩, fun ⟨x, _, hx⟩ => ⟨x, hx⟩⟩
    have hPg1 : Pg ≠ ⊥ := by
      intro h
      apply hne
      rw [eq_bot_iff]
      rintro _ ⟨x, rfl⟩
      rw [Subgroup.mem_bot]
      have h1 : PH ⟨x, hall x⟩ ∈ Pg := ⟨_, rfl⟩
      rw [h, Subgroup.mem_bot, hPH] at h1
      refine Equiv.ext fun v => ?_
      rw [(hP x (hall x)).1, h1]
      exact one_mulVec v
    obtain ⟨l1, -⟩ := lin_offender hPgs hPg1
    have e₀ : Nat.card (fixAll ρ₀) = Nat.card {v // ∀ x ∈ EL, ρ₀ x v = v} :=
      Nat.card_congr (Equiv.subtypeEquivRight fun v => ⟨fun h x _ => h x, fun h x => h x (hall x)⟩)
    have e₁ : Nat.card (fixAll ρ₁) = Nat.card {v // ∀ x ∈ EL, ρ₁ x v = v} :=
      Nat.card_congr (Equiv.subtypeEquivRight fun v => ⟨fun h x _ => h x, fun h x => h x (hall x)⟩)
    have e₂ : Nat.card (fixAll ρ₂) = Nat.card {v // ∀ x ∈ EL, ρ₂ x v = v} :=
      Nat.card_congr (Equiv.subtypeEquivRight fun v => ⟨fun h x _ => h x, fun h x => h x (hall x)⟩)
    rw [hrange, hcardEL, e₀, e₁, e₂, hPgfix₀, hPgfix₁, hPgfix₂]
    rw [← hq] at l1
    set g₀ := Nat.card {v : Fin 3 → F // ∀ X ∈ Pg, (X : Matrix (Fin 3) (Fin 3) F) *ᵥ v = v}
    set g₁ := Nat.card {v : Fin 3 → F // ∀ X ∈ Pg, (X : Matrix (Fin 3) (Fin 3) F)ᵀ *ᵥ v = v}
    set N := Nat.card Pg
    have hq6 : 0 < q ^ 6 := pow_pos hq0 6
    have h2 : N * g₀ * g₁ ≤ N * q * g₀ * g₁ := by
      calc N * g₀ * g₁ = N * 1 * g₀ * g₁ := by ring
        _ ≤ N * q * g₀ * g₁ := by gcongr; omega
    exact ⟨by omega, by omega⟩
  ·
    push Not at hall
    obtain ⟨s, hs⟩ := hall
    set τ := σ s with hτdef
    have hτsq : τ * τ = 1 := hσsq s
    have hσout : ∀ x, σ x ≠ 1 → σ x = τ := fun x hx => eq_of_mul_self_eq_one (hσsq x) hτsq hx hs
    have hsx : ∀ x, σ x ≠ 1 → s * x ∈ EL := fun x hx => by
      show σ (s * x) = 1
      rw [hσmul, hσout x hx, hτsq]
    have hidx : Nat.card ρ₀.range ≤ 2 * Nat.card (EL.map ρ₀) := by
      rw [two_mul, ← Nat.card_sum]
      refine Nat.card_le_card_of_injective (fun y => if h : (y : Equiv.Perm (Fin 3 → F)) ∈
        EL.map ρ₀ then Sum.inl ⟨y, h⟩ else Sum.inr ⟨ρ₀ s * y, ?_⟩) ?_
      · obtain ⟨x, hx⟩ := y.2
        have hx' : σ x ≠ 1 := fun h1 => h ⟨x, h1, hx⟩
        exact ⟨s * x, hsx x hx', by rw [map_mul, hx]⟩
      · intro y y' hyy
        by_cases h : (y : Equiv.Perm (Fin 3 → F)) ∈ EL.map ρ₀ <;>
          by_cases h' : (y' : Equiv.Perm (Fin 3 → F)) ∈ EL.map ρ₀
        · simp only [h, h', dite_true, Sum.inl.injEq] at hyy
          exact Subtype.ext (Subtype.mk.inj hyy)
        · simp [h, h'] at hyy
        · simp [h, h'] at hyy
        · simp only [h, h', dite_false, Sum.inr.injEq] at hyy
          exact Subtype.ext (mul_left_cancel (Subtype.mk.inj hyy))
    have hhalf : ∀ (ρ : E →* Equiv.Perm (Fin 3 → F)) (τ' : E → (F ≃+* F))
        (hadd : ∀ x v w, ρ x (v + w) = ρ x v + ρ x w)
        (hsemi : ∀ x (c : F) v, ρ x (c • v) = τ' x c • ρ x v) (hτ' : τ' s ≠ 1)
        (hlinρ : ∀ x ∈ EL, ∀ (c : F) v, ρ x (c • v) = c • ρ x v),
        Nat.card (fixAll ρ) ^ 2 ≤ Nat.card {v // ∀ x ∈ EL, ρ x v = v} := by
      intro ρ τ' hadd hsemi hτ' hlinρ
      have hz : ∀ x, ρ x 0 = 0 := fun x => by
        have := hadd x 0 0
        rw [add_zero] at this
        exact left_eq_add.mp this
      let Y : AddSubgroup (Fin 3 → F) :=
        { carrier := {v | ∀ x ∈ EL, ρ x v = v}
          add_mem' := fun {v w} hv hw x hx => by rw [hadd, hv x hx, hw x hx]
          zero_mem' := fun x _ => hz x
          neg_mem' := fun {v} hv x hx => by
            have h1 := hadd x v (-v)
            rw [add_neg_cancel, hz, hv x hx] at h1
            exact (neg_eq_of_add_eq_zero_right h1.symm).symm }
      have hY : ∀ (c : F) y, y ∈ Y → c • y ∈ Y := fun c y hy x hx => by
        rw [hlinρ x hx, hy x hx]
      let φ : (Fin 3 → F) →+ (Fin 3 → F) :=
        { toFun := ρ s
          map_zero' := hz s
          map_add' := hadd s }
      have h1 := card_fix_sq_le Y hY φ hτ' (hsemi s)
      have h2 : Nat.card (fixAll ρ) ≤ Nat.card {y // y ∈ Y ∧ φ y = y} :=
        Nat.card_le_card_of_injective (fun v => ⟨v.1, fun x _ => v.2 x, v.2 s⟩)
          fun v w h => Subtype.ext (by
            have := congrArg Subtype.val h
            exact this)
      calc Nat.card (fixAll ρ) ^ 2 ≤ Nat.card {y // y ∈ Y ∧ φ y = y} ^ 2 := by gcongr
        _ ≤ Nat.card Y := h1
        _ = _ := rfl
    have hlin₀ : ∀ x ∈ EL, ∀ (c : F) v, ρ₀ x (c • v) = c • ρ₀ x v := fun x hx c v => by
      rw [(hP x hx).1, (hP x hx).1, mulVec_smul]
    have hlin₁ : ∀ x ∈ EL, ∀ (c : F) v, ρ₁ x (c • v) = c • ρ₁ x v := fun x hx c v => by
      rw [(hP x hx).2.1, (hP x hx).2.1, mulVec_smul]
    have hlin₂ : ∀ x ∈ EL, ∀ (c : F) v, ρ₂ x (c • v) = c • ρ₂ x v := fun x hx c v => by
      rw [(hP x hx).2.2, (hP x hx).2.2, mulVec_smul]
    have h₀ := hhalf ρ₀ σ hadd₀ hsemi₀ hs hlin₀
    have h₁ := hhalf ρ₁ σ₁ hadd₁ hsemi₁ (hnl₁ s hs) hlin₁
    have h₂ := hhalf ρ₂ σ₂ hadd₂ hsemi₂ (hnl₂ s hs) hlin₂
    rw [hPgfix₀] at h₀
    rw [hPgfix₁] at h₁
    rw [hPgfix₂] at h₂
    rw [hcardEL] at hidx
    set f₀ := Nat.card (fixAll ρ₀)
    set f₁ := Nat.card (fixAll ρ₁)
    set f₂ := Nat.card (fixAll ρ₂)
    set g₀ := Nat.card {v : Fin 3 → F // ∀ X ∈ Pg, (X : Matrix (Fin 3) (Fin 3) F) *ᵥ v = v}
    set g₁ := Nat.card {v : Fin 3 → F // ∀ X ∈ Pg, (X : Matrix (Fin 3) (Fin 3) F)ᵀ *ᵥ v = v}
    set N := Nat.card Pg
    set M := Nat.card ρ₀.range
    have hq6 : 0 < q ^ 6 := pow_pos hq0 6
    by_cases hPg1 : Pg = ⊥
    · have hN : N = 1 := by
        show Nat.card Pg = 1
        rw [hPg1]
        exact Subgroup.card_bot
      have hg₀ : g₀ ≤ q ^ 3 := by
        rw [← card_fun3']
        exact Nat.card_le_card_of_injective Subtype.val Subtype.val_injective
      have hg₁ : g₁ ≤ q ^ 3 := by
        rw [← card_fun3']
        exact Nat.card_le_card_of_injective Subtype.val Subtype.val_injective
      rw [hN] at hidx
      have hf01 : f₀ * f₁ ≤ q ^ 3 := by
        refine le_of_pow_le_pow_left₀ (n := 2) (by norm_num) (Nat.zero_le _) ?_
        calc (f₀ * f₁) ^ 2 = f₀ ^ 2 * f₁ ^ 2 := by ring
          _ ≤ g₀ * g₁ := Nat.mul_le_mul h₀ h₁
          _ ≤ q ^ 3 * q ^ 3 := Nat.mul_le_mul hg₀ hg₁
          _ = (q ^ 3) ^ 2 := by ring
      have hf02 : f₀ * f₂ ≤ q ^ 3 := by
        refine le_of_pow_le_pow_left₀ (n := 2) (by norm_num) (Nat.zero_le _) ?_
        calc (f₀ * f₂) ^ 2 = f₀ ^ 2 * f₂ ^ 2 := by ring
          _ ≤ g₀ * g₁ := Nat.mul_le_mul h₀ h₂
          _ ≤ q ^ 3 * q ^ 3 := Nat.mul_le_mul hg₀ hg₁
          _ = (q ^ 3) ^ 2 := by ring
      have hq4 : q ^ 4 < q ^ 6 := Nat.pow_lt_pow_right (by omega) (by norm_num)
      have hq3 : q ^ 3 < q ^ 6 := Nat.pow_lt_pow_right (by omega) (by norm_num)
      constructor
      · calc M * q * f₀ * f₁ = M * q * (f₀ * f₁) := by ring
          _ ≤ (2 * 1) * q * q ^ 3 := by gcongr
          _ = 2 * q ^ 4 := by ring
          _ < 2 * q ^ 6 := by omega
      · calc M * f₀ * f₂ = M * (f₀ * f₂) := by ring
          _ ≤ (2 * 1) * q ^ 3 := by gcongr
          _ < 2 * q ^ 6 := by omega
    · obtain ⟨l1, l2⟩ := lin_offender hPgs hPg1
      rw [← hq] at l1 l2
      have k1 : N * q * f₀ * f₁ < q ^ 6 := by
        refine hsqlt _ _ ?_
        calc (N * q * f₀ * f₁) ^ 2 = N * q * (N * q) * (f₀ ^ 2 * f₁ ^ 2) := by ring
          _ ≤ N * q * (N * q) * (g₀ * g₁) := by gcongr
          _ = N * q * (N * q * g₀ * g₁) := by ring
          _ ≤ (q ^ 2 * q) * q ^ 6 := by gcongr
          _ = q ^ 9 := by ring
          _ < q ^ 12 := Nat.pow_lt_pow_right (by omega) (by norm_num)
          _ = (q ^ 6) ^ 2 := by ring
      have k2 : N * f₀ * f₂ < q ^ 6 := by
        refine hsqlt _ _ ?_
        have hNg : N * g₀ * g₁ * q ≤ q ^ 5 * q := by
          calc N * g₀ * g₁ * q = N * q * g₀ * g₁ := by ring
            _ ≤ q ^ 6 := l1
            _ = q ^ 5 * q := by ring
        have hNg' : N * g₀ * g₁ ≤ q ^ 5 := Nat.le_of_mul_le_mul_right hNg hq0
        calc (N * f₀ * f₂) ^ 2 = N * N * (f₀ ^ 2 * f₂ ^ 2) := by ring
          _ ≤ N * N * (g₀ * g₁) := by gcongr
          _ = N * (N * g₀ * g₁) := by ring
          _ ≤ q ^ 2 * q ^ 5 := by gcongr
          _ = q ^ 7 := by ring
          _ < q ^ 12 := Nat.pow_lt_pow_right (by omega) (by norm_num)
          _ = (q ^ 6) ^ 2 := by ring
      constructor
      · calc M * q * f₀ * f₁ ≤ (2 * N) * q * f₀ * f₁ := by gcongr
          _ = 2 * (N * q * f₀ * f₁) := by ring
          _ < 2 * q ^ 6 := by omega
      · calc M * f₀ * f₂ ≤ (2 * N) * f₀ * f₂ := by gcongr
          _ = 2 * (N * f₀ * f₂) := by ring
          _ < 2 * q ^ 6 := by omega

end Semi

end CFSG.Quasithin.H13.Ch4.C135

end
