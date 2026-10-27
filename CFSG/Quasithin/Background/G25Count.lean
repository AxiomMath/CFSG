module

public import CFSG.Quasithin.Background.G25Six

public section

namespace CFSG.Quasithin

open CFSG.Quasithin.SL2Model CFSG.Quasithin.SL3Model CFSG.Quasithin.G1
open scoped MatrixGroups Pointwise commutatorElement

variable {G : Type*} [Group G] {F : Type*} [Field F]

theorem card_eq_card_inf_mul_card_range {Y Sx N : Subgroup G} {M : Type*} [Group M]
    (φ : ↥Sx →* M) (hφ : ∀ x : ↥Sx, φ x = 1 ↔ (x : G) ∈ N) (hY : Y ≤ Sx) :
    Nat.card ↥Y = Nat.card ↥(Y ⊓ N) * Nat.card ↥(φ.comp (Subgroup.inclusion hY)).range := by
  have h := Subgroup.card_ker_mul_card_range (φ.comp (Subgroup.inclusion hY))
  have hker : Nat.card ↥(φ.comp (Subgroup.inclusion hY)).ker = Nat.card ↥(Y ⊓ N) :=
    Nat.card_congr
      { toFun := fun y => ⟨(y.1 : G), y.1.2, (hφ _).1 y.2⟩
        invFun := fun g => ⟨⟨g.1, g.2.1⟩, (hφ ⟨g.1, hY g.2.1⟩).2 g.2.2⟩
        left_inv := fun y => rfl
        right_inv := fun g => rfl }
  rw [hker] at h
  exact h.symm

theorem card_supp_zero (r : ℕ) :
    Nat.card {v : Multiplicative (Fin r → Fin 3 → F) //
      ∀ (l : Fin r) (j : Fin 3), j ≠ 0 → Multiplicative.toAdd v l j = 0} = Nat.card F ^ r := by
  have e : {v : Multiplicative (Fin r → Fin 3 → F) //
      ∀ (l : Fin r) (j : Fin 3), j ≠ 0 → Multiplicative.toAdd v l j = 0} ≃ (Fin r → F) :=
    { toFun := fun v l => Multiplicative.toAdd v.1 l 0
      invFun := fun c => ⟨Multiplicative.ofAdd (fun l => Pi.single 0 (c l)), fun l j hj => by
        simp [hj]⟩
      left_inv := fun v => by
        apply Subtype.ext
        apply Multiplicative.toAdd.injective
        funext l j
        by_cases hj : j = 0
        · subst hj
          simp
        · simp [hj, v.2 l j hj]
      right_inv := fun c => by
        funext l
        simp }
  rw [Nat.card_congr e, Nat.card_fun, Nat.card_eq_fintype_card (α := Fin r), Fintype.card_fin]

theorem card_supp_one_two (s : ℕ) :
    Nat.card {v : Multiplicative (Fin s → Fin 3 → F) //
      ∀ l : Fin s, Multiplicative.toAdd v l 0 = 0} = Nat.card F ^ (2 * s) := by
  have e : {v : Multiplicative (Fin s → Fin 3 → F) //
      ∀ l : Fin s, Multiplicative.toAdd v l 0 = 0} ≃ (Fin s → F × F) :=
    { toFun := fun v l => (Multiplicative.toAdd v.1 l 1, Multiplicative.toAdd v.1 l 2)
      invFun := fun c => ⟨Multiplicative.ofAdd (fun l => ![0, (c l).1, (c l).2]), fun l => by
        simp⟩
      left_inv := fun v => by
        apply Subtype.ext
        apply Multiplicative.toAdd.injective
        funext l j
        fin_cases j
        · simp [v.2 l]
        · simp
        · simp
      right_inv := fun c => by
        funext l
        simp }
  rw [Nat.card_congr e, Nat.card_fun, Nat.card_eq_fintype_card (α := Fin s), Fintype.card_fin,
    Nat.card_prod, ← pow_two, ← pow_mul]

theorem exists_pairFam_coord (S : Subgroup G) (Uk : Fin 3 → Subgroup G) {s : ℕ}
    (φ : ↥(TripleGrp.S₃ S Uk) →* Multiplicative (Fin s → Fin 3 → F))
    (hs : Function.Surjective φ)
    (hc : ∀ (k : Fin 3) (x : ↥(TripleGrp.S₃ S Uk)), (x : G) ∈ pairFam S Uk k ↔
      ∀ (l : Fin s) (j : Fin 3), j ≠ k → Multiplicative.toAdd (φ x) l j = 0)
    (k : Fin 3) (c : Fin s → F) :
    ∃ a : ↥(TripleGrp.S₃ S Uk), (a : G) ∈ pairFam S Uk k ∧
      φ a = Multiplicative.ofAdd (fun l => (Pi.single k (c l) : Fin 3 → F)) := by
  obtain ⟨a, ha⟩ := hs (Multiplicative.ofAdd (fun l => (Pi.single k (c l) : Fin 3 → F)))
  refine ⟨a, (hc k a).2 fun l j hj => ?_, ha⟩
  rw [ha]
  simp [hj]

namespace TripleL3

variable [CharP F 2] {I S : Subgroup G} {Uk : Fin 3 → Subgroup G} {Φ : ↥I →* SL(3, F)}
  {p : Fin 3 → Fin 3 → F} {Q : SL(3, F)} {lam : Fin 3 → F}
  (hT : TripleL3 I S Uk Φ p Q lam)

include hT

omit [CharP F 2] in
theorem card_Qv_p_zero : Nat.card ↥(Qv (p 0)) = Nat.card F ^ 2 := by
  rw [← hT.Qv_Q 0, ← Qv_map_conj Q (vE F 0)]
  exact (Nat.card_congr (Subgroup.equivMapOfInjective (Qv (vE F 0)) (MulAut.conj Q).toMonoidHom
    (MulAut.conj Q).injective).toEquiv).symm.trans card_Qv

omit [CharP F 2] in
theorem card_Uk_zero :
    Nat.card ↥(Uk 0) = Nat.card ↥(TripleGrp.W S Uk 0) * Nat.card F ^ 2 := by
  have h := card_eq_card_inf_mul_card_range Φ hT.ker (hT.tg.Uk_le_I 0)
  have hrange : (Φ.comp (Subgroup.inclusion (hT.tg.Uk_le_I 0))).range = Qv (p 0) := by
    ext z
    constructor
    · rintro ⟨y, rfl⟩
      exact hT.mem_Qv 0 (Subgroup.inclusion (hT.tg.Uk_le_I 0) y) y.2
    · intro hz
      obtain ⟨x, hxU, rfl⟩ := hT.lift 0 z hz
      exact ⟨⟨x, hxU⟩, rfl⟩
  rw [hrange, hT.card_Qv_p_zero] at h
  exact h

omit [CharP F 2] in
theorem card_W_zero {r : ℕ} (φ : ↥S →* Multiplicative (Fin r → Fin 3 → F))
    (hs : Function.Surjective φ) (hk : ∀ x : ↥S, φ x = 1 ↔ (x : G) ∈ TripleGrp.S₃ S Uk)
    (hc : ∀ (k : Fin 3) (x : ↥S), (x : G) ∈ TripleGrp.W S Uk k ⊔ TripleGrp.S₃ S Uk ↔
      ∀ (l : Fin r) (j : Fin 3), j ≠ k → Multiplicative.toAdd (φ x) l j = 0) :
    Nat.card ↥(TripleGrp.W S Uk 0) =
      Nat.card ↥(TripleGrp.W S Uk 0 ⊓ TripleGrp.S₃ S Uk) * Nat.card F ^ r := by
  have hW : TripleGrp.W S Uk 0 ≤ S := inf_le_right
  have h := card_eq_card_inf_mul_card_range φ hk hW
  have hrange : ∀ v : Multiplicative (Fin r → Fin 3 → F),
      v ∈ (φ.comp (Subgroup.inclusion hW)).range ↔
        ∀ (l : Fin r) (j : Fin 3), j ≠ 0 → Multiplicative.toAdd v l j = 0 := by
    intro v
    constructor
    · rintro ⟨w, rfl⟩
      exact (hc 0 (Subgroup.inclusion hW w)).1 (Subgroup.mem_sup_left w.2)
    · intro hv
      obtain ⟨x, rfl⟩ := hs v
      have hx : (x : G) ∈ TripleGrp.W S Uk 0 ⊔ TripleGrp.S₃ S Uk := (hc 0 x).2 hv
      obtain ⟨w, hw, z, hz, hwz⟩ := hT.tg.mem_W₀_sup_S₃ hx
      have hzS₃ : z ∈ TripleGrp.S₃ S Uk :=
        TripleGrp.Wij_le_S₃ (by decide : (1 : Fin 3) ≠ 2) hz
      have hzS : z ∈ S := TripleGrp.S₃_le_S hzS₃
      refine ⟨⟨w, hw⟩, ?_⟩
      have hxe : x = ⟨w, hW hw⟩ * ⟨z, hzS⟩ := Subtype.ext hwz.symm
      show φ ⟨w, hW hw⟩ = φ x
      rw [hxe, map_mul, (hk ⟨z, hzS⟩).2 hzS₃, mul_one]
  rw [h, Nat.card_congr (Equiv.subtypeEquivRight hrange), card_supp_zero]

omit [CharP F 2] in
theorem card_W_inf_S₃ {s : ℕ} (φ : ↥(TripleGrp.S₃ S Uk) →* Multiplicative (Fin s → Fin 3 → F))
    (hs : Function.Surjective φ)
    (hk : ∀ x : ↥(TripleGrp.S₃ S Uk), φ x = 1 ↔ (x : G) ∈ TripleGrp.S₂ Uk)
    (hc : ∀ (k : Fin 3) (x : ↥(TripleGrp.S₃ S Uk)), (x : G) ∈ pairFam S Uk k ↔
      ∀ (l : Fin s) (j : Fin 3), j ≠ k → Multiplicative.toAdd (φ x) l j = 0) :
    Nat.card ↥(TripleGrp.W S Uk 0 ⊓ TripleGrp.S₃ S Uk) =
      Nat.card ↥(TripleGrp.S₂ Uk) * Nat.card F ^ (2 * s) := by
  have hY : TripleGrp.W S Uk 0 ⊓ TripleGrp.S₃ S Uk ≤ TripleGrp.S₃ S Uk := inf_le_right
  have h := card_eq_card_inf_mul_card_range φ hk hY
  have hS₂Y : TripleGrp.S₂ Uk ≤ TripleGrp.W S Uk 0 ⊓ TripleGrp.S₃ S Uk :=
    le_inf (hT.tg.S₂_le_W 0) hT.tg.S₂_le_S₃
  rw [inf_eq_right.2 hS₂Y] at h
  have hW0 : ∀ k : Fin 3, k ≠ 0 → pairFam S Uk k ≤ TripleGrp.W S Uk 0 := fun k hk y hy =>
    (mem_pairFam_iff S Uk k y).1 hy 0 (Ne.symm hk)
  have hrange : ∀ v : Multiplicative (Fin s → Fin 3 → F),
      v ∈ (φ.comp (Subgroup.inclusion hY)).range ↔
        ∀ l : Fin s, Multiplicative.toAdd v l 0 = 0 := by
    intro v
    constructor
    · rintro ⟨x, rfl⟩
      set x' : ↥(TripleGrp.S₃ S Uk) := Subgroup.inclusion hY x with hx'
      have hxW : (x' : G) ∈ TripleGrp.W S Uk 0 := x.2.1
      obtain ⟨a₀, ha₀, ha₀v⟩ := exists_pairFam_coord S Uk φ hs hc 0
        (fun l => Multiplicative.toAdd (φ x') l 0)
      obtain ⟨a₁, ha₁, ha₁v⟩ := exists_pairFam_coord S Uk φ hs hc 1
        (fun l => Multiplicative.toAdd (φ x') l 1)
      obtain ⟨a₂, ha₂, ha₂v⟩ := exists_pairFam_coord S Uk φ hs hc 2
        (fun l => Multiplicative.toAdd (φ x') l 2)
      have hdecomp : φ x' = φ a₀ * φ a₁ * φ a₂ := by
        rw [ha₀v, ha₁v, ha₂v]
        apply Multiplicative.toAdd.injective
        funext l j
        fin_cases j <;> simp
      have hz : ((x' * (a₀ * a₁ * a₂)⁻¹ : ↥(TripleGrp.S₃ S Uk)) : G) ∈ TripleGrp.S₂ Uk := by
        refine (hk _).1 ?_
        rw [map_mul, map_inv, map_mul, map_mul, ← hdecomp]
        simp
      have ha₀W : (a₀ : G) ∈ TripleGrp.W S Uk 0 := by
        have e : (a₀ : G) = ((x' * (a₀ * a₁ * a₂)⁻¹ : ↥(TripleGrp.S₃ S Uk)) : G)⁻¹ * x' *
            ((a₁ : G) * a₂)⁻¹ := by
          simp only [Subgroup.coe_mul, Subgroup.coe_inv]
          group
        rw [e]
        refine (TripleGrp.W S Uk 0).mul_mem
          ((TripleGrp.W S Uk 0).mul_mem ((TripleGrp.W S Uk 0).inv_mem (hT.tg.S₂_le_W 0 hz)) hxW)
          ((TripleGrp.W S Uk 0).inv_mem ((TripleGrp.W S Uk 0).mul_mem
            (hW0 1 (by decide) ha₁) (hW0 2 (by decide) ha₂)))
      have ha₀S₂ : (a₀ : G) ∈ TripleGrp.S₂ Uk := by
        refine TripleGrp.mem_S₂_of_forall fun m => ?_
        rcases TripleGrp.fin_three_cases 0 1 2 m (by decide) (by decide) (by decide) with
          rfl | rfl | rfl
        · exact ha₀W.1
        · exact ((mem_pairFam_iff S Uk 0 a₀).1 ha₀ 1 (by decide)).1
        · exact ((mem_pairFam_iff S Uk 0 a₀).1 ha₀ 2 (by decide)).1
      have h1 : φ a₀ = 1 := (hk a₀).2 ha₀S₂
      rw [ha₀v] at h1
      intro l
      have := congrFun (congrFun (congrArg Multiplicative.toAdd h1) l) 0
      simpa using this
    · intro hv
      obtain ⟨a₁, ha₁, ha₁v⟩ := exists_pairFam_coord S Uk φ hs hc 1
        (fun l => Multiplicative.toAdd v l 1)
      obtain ⟨a₂, ha₂, ha₂v⟩ := exists_pairFam_coord S Uk φ hs hc 2
        (fun l => Multiplicative.toAdd v l 2)
      have hmem : ((a₁ * a₂ : ↥(TripleGrp.S₃ S Uk)) : G) ∈
          TripleGrp.W S Uk 0 ⊓ TripleGrp.S₃ S Uk :=
        ⟨(TripleGrp.W S Uk 0).mul_mem (hW0 1 (by decide) ha₁) (hW0 2 (by decide) ha₂),
          (a₁ * a₂).2⟩
      refine ⟨⟨(a₁ * a₂ : ↥(TripleGrp.S₃ S Uk)), hmem⟩, ?_⟩
      show φ (a₁ * a₂) = v
      rw [map_mul, ha₁v, ha₂v]
      apply Multiplicative.toAdd.injective
      funext l j
      fin_cases j
      · simp [hv l]
      · simp
      · simp
  rw [h, Nat.card_congr (Equiv.subtypeEquivRight hrange), card_supp_one_two, mul_comm]

omit [CharP F 2] in
theorem card_Uk_zero_formula {r s : ℕ} (φ₇ : ↥S →* Multiplicative (Fin r → Fin 3 → F))
    (hs₇ : Function.Surjective φ₇)
    (hk₇ : ∀ x : ↥S, φ₇ x = 1 ↔ (x : G) ∈ TripleGrp.S₃ S Uk)
    (hc₇ : ∀ (k : Fin 3) (x : ↥S), (x : G) ∈ TripleGrp.W S Uk k ⊔ TripleGrp.S₃ S Uk ↔
      ∀ (l : Fin r) (j : Fin 3), j ≠ k → Multiplicative.toAdd (φ₇ x) l j = 0)
    (φ₆ : ↥(TripleGrp.S₃ S Uk) →* Multiplicative (Fin s → Fin 3 → F))
    (hs₆ : Function.Surjective φ₆)
    (hk₆ : ∀ x : ↥(TripleGrp.S₃ S Uk), φ₆ x = 1 ↔ (x : G) ∈ TripleGrp.S₂ Uk)
    (hc₆ : ∀ (k : Fin 3) (x : ↥(TripleGrp.S₃ S Uk)), (x : G) ∈ pairFam S Uk k ↔
      ∀ (l : Fin s) (j : Fin 3), j ≠ k → Multiplicative.toAdd (φ₆ x) l j = 0) :
    Nat.card ↥(Uk 0) = Nat.card F ^ (2 * s + r + 2) * Nat.card ↥(TripleGrp.S₂ Uk) := by
  rw [hT.card_Uk_zero, hT.card_W_zero φ₇ hs₇ hk₇ hc₇, hT.card_W_inf_S₃ φ₆ hs₆ hk₆ hc₆]
  ring

end TripleL3

end CFSG.Quasithin
