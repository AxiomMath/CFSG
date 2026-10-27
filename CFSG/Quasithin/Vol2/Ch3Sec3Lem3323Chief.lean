module

public import CFSG.Quasithin.Vol2.Ch3Sec3Setup
public import CFSG.Quasithin.Background.B1ChiefCount
public import CFSG.Quasithin.Background.C4Defs

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.ChiefCount
open scoped commutatorElement

namespace Chief3323

variable {G : Type} [Group G]

theorem hasNoncentralTwoChief_iff {X : Subgroup G} {k : ℕ} :
    HasNoncentralTwoChief X k ↔ HasNCBetween X ⊥ X k := by
  constructor
  · rintro ⟨A, B, hAB, hle⟩
    exact ⟨A, B, fun i => ⟨(hAB i).1, (hAB i).2, bot_le, (hAB i).1.2.1⟩, hle⟩
  · rintro ⟨A, B, hAB, hle⟩
    exact ⟨A, B, fun i => ⟨(hAB i).1, (hAB i).2.1⟩, hle⟩

theorem hasNoncentralTwoChief_two {X A₀ B₀ A₁ B₁ : Subgroup G}
    (h₀ : IsTwoChiefFactor X A₀ B₀ ∧ ¬ ⁅A₀, X⁆ ≤ B₀)
    (h₁ : IsTwoChiefFactor X A₁ B₁ ∧ ¬ ⁅A₁, X⁆ ≤ B₁) (h : A₀ ≤ B₁) :
    HasNoncentralTwoChief X 2 := by
  refine ⟨![A₀, A₁], ![B₀, B₁], fun i => ?_, fun i j hij => ?_⟩
  · fin_cases i
    · exact h₀
    · exact h₁
  · fin_cases i <;> fin_cases j
    · exact absurd hij (lt_irrefl _)
    · exact h
    · exact absurd hij (by decide)
    · exact absurd hij (lt_irrefl _)

section Irred

variable {F : Type} [Field F]

theorem transvection_mulVec_sub {i j : Fin 3} (c : F) (u : Fin 3 → F) :
    (Matrix.transvection i j c).mulVec u - u = Pi.single i (c * u j) := by
  rw [Matrix.transvection, Matrix.add_mulVec, Matrix.one_mulVec, add_sub_cancel_left,
    Matrix.single_mulVec]
  funext k
  by_cases hk : k = i
  · subst hk
    simp
  · simp [hk]

@[expose] def tv {i j : Fin 3} (hij : i ≠ j) (c : F) : Matrix.SpecialLinearGroup (Fin 3) F :=
  ⟨Matrix.transvection i j c, Matrix.det_transvection_of_ne i j hij c⟩

theorem eq_top_of_invariant (W : AddSubgroup (Fin 3 → F))
    (hW : ∀ g : Matrix.SpecialLinearGroup (Fin 3) F, ∀ w ∈ W,
      (g : Matrix (Fin 3) (Fin 3) F).mulVec w ∈ W)
    {w : Fin 3 → F} (hw : w ∈ W) (hw0 : w ≠ 0) (v : Fin 3 → F) : v ∈ W := by
  have hmove : ∀ {i j : Fin 3} (hij : i ≠ j) (c : F) {u : Fin 3 → F}, u ∈ W →
      Pi.single i (c * u j) ∈ W := by
    intro i j hij c u hu
    rw [← transvection_mulVec_sub]
    exact W.sub_mem (hW (tv hij c) u hu) hu
  obtain ⟨j, hj⟩ : ∃ j, w j ≠ 0 := by
    by_contra h
    push Not at h
    exact hw0 (funext h)
  obtain ⟨i, hij⟩ : ∃ i : Fin 3, i ≠ j := ⟨j + 1, by
    intro h
    have := congrArg (fun x : Fin 3 => (x : ℕ)) h
    fin_cases j <;> simp_all⟩
  have hi : ∀ a : F, Pi.single i a ∈ W := by
    intro a
    have := hmove hij (a / w j) hw
    rwa [div_mul_cancel₀ a hj] at this
  have hk : ∀ (k : Fin 3) (a : F), Pi.single k a ∈ W := by
    intro k a
    by_cases hki : k = i
    · subst hki
      exact hi a
    · have := hmove hki a (hi 1)
      simpa using this
  rw [← Finset.univ_sum_single v]
  exact W.sum_mem fun k _ => hk k (v k)

end Irred

theorem surj_moduleAct {F : Type} [Field F] (dual : Bool) {X : Subgroup G}
    {α : ↥X →* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F)} (hα : Function.Surjective α)
    (g : Matrix.SpecialLinearGroup (Fin 3) F) :
    ∃ x : ↥X, moduleAct dual (α x : Matrix.GeneralLinearGroup (Fin 3) F) =
      (g : Matrix (Fin 3) (Fin 3) F) := by
  cases dual
  · obtain ⟨x, hx⟩ := hα (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 F g)
    refine ⟨x, ?_⟩
    simp only [moduleAct, hx, Bool.false_eq_true, ite_false]
    rfl
  · let h : Matrix.SpecialLinearGroup (Fin 3) F :=
      ⟨((g : Matrix (Fin 3) (Fin 3) F)⁻¹).transpose, by
        rw [Matrix.det_transpose, Matrix.det_nonsing_inv, g.2, Ring.inverse_one]⟩
    obtain ⟨x, hx⟩ := hα (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 F h)
    refine ⟨x, ?_⟩
    have hdet : IsUnit (g : Matrix (Fin 3) (Fin 3) F).det := by
      rw [g.2]
      exact isUnit_one
    have hxm : ((α x : Matrix.GeneralLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
        ((g : Matrix (Fin 3) (Fin 3) F)⁻¹).transpose := by
      rw [hx]
      rfl
    simp only [moduleAct, ite_true]
    rw [Matrix.coe_units_inv, hxm, ← Matrix.transpose_nonsing_inv, Matrix.transpose_transpose,
      Matrix.nonsing_inv_nonsing_inv _ hdet]

theorem isTwoChiefFactor_of_coords {F : Type} [Field F] [Fintype F] (hF : Fintype.card F = 2)
    {X A B : Subgroup G} (hBA : B ≤ A) (hAX : A ≤ X) (hXA : X ≤ Subgroup.normalizer (A : Set G))
    (hXB : X ≤ Subgroup.normalizer (B : Set G)) (act : ↥X → Matrix (Fin 3) (Fin 3) F)
    (hsurj : ∀ g : Matrix.SpecialLinearGroup (Fin 3) F, ∃ x : ↥X,
      act x = (g : Matrix (Fin 3) (Fin 3) F))
    (β : ↥A →* Multiplicative (Fin 3 → F)) (hβs : Function.Surjective β)
    (hβk : β.ker = B.subgroupOf A)
    (hβe : ∀ (x : ↥X) (u v : ↥A), (v : G) = x * u * x⁻¹ →
      Multiplicative.toAdd (β v) = (act x).mulVec (Multiplicative.toAdd (β u))) :
    IsTwoChiefFactor X A B ∧ ¬ ⁅A, X⁆ ≤ B := by
  have hker : ∀ a : ↥A, (a : G) ∈ B ↔ β a = 1 := by
    intro a
    rw [← MonoidHom.mem_ker, hβk, Subgroup.mem_subgroupOf]
  have h2 : (2 : F) = 0 := by
    have := FiniteField.cast_card_eq_zero F
    rwa [hF, Nat.cast_ofNat] at this
  have hmov : ∃ (g : Matrix.SpecialLinearGroup (Fin 3) F) (w : Fin 3 → F),
      (g : Matrix (Fin 3) (Fin 3) F).mulVec w ≠ w := by
    refine ⟨tv (show (0 : Fin 3) ≠ 1 by decide) 1, Pi.single 1 1, fun h => ?_⟩
    have h1 := transvection_mulVec_sub (i := 0) (j := 1) (1 : F) (Pi.single 1 1)
    have h3 : (Matrix.transvection (0 : Fin 3) 1 (1 : F)).mulVec (Pi.single 1 1) =
        Pi.single 1 1 := h
    rw [h3, sub_self] at h1
    have := congrFun h1 0
    simp at this
  refine ⟨⟨lt_of_le_of_ne hBA fun hAB => ?_, hAX, hXA, hXB, fun C hC1 hC2 hXC => ?_,
    fun a ha => ⟨1, ?_⟩⟩, fun hc => ?_⟩
  ·
    obtain ⟨g, w, hgw⟩ := hmov
    obtain ⟨a, ha⟩ := hβs (Multiplicative.ofAdd w)
    have h1 : β a = 1 := (hker a).mp (by rw [hAB]; exact a.2)
    have hw : w = 0 := by
      have := congrArg Multiplicative.toAdd (ha.symm.trans h1)
      simpa using this
    exact hgw (by rw [hw, Matrix.mulVec_zero])
  ·
    let W : AddSubgroup (Fin 3 → F) :=
      { carrier := {w | ∃ c : ↥A, (c : G) ∈ C ∧ Multiplicative.toAdd (β c) = w}
        add_mem' := by
          rintro _ _ ⟨c₁, h₁, rfl⟩ ⟨c₂, h₂, rfl⟩
          exact ⟨c₁ * c₂, C.mul_mem h₁ h₂, by rw [map_mul, toAdd_mul]⟩
        zero_mem' := ⟨1, C.one_mem, by rw [map_one, toAdd_one]⟩
        neg_mem' := by
          rintro _ ⟨c, hc, rfl⟩
          exact ⟨c⁻¹, C.inv_mem hc, by rw [map_inv, toAdd_inv]⟩ }
    have hmemW : ∀ c : ↥A, (c : G) ∈ C → Multiplicative.toAdd (β c) ∈ W := fun c hc =>
      ⟨c, hc, rfl⟩
    have hWinv : ∀ g : Matrix.SpecialLinearGroup (Fin 3) F, ∀ w ∈ W,
        (g : Matrix (Fin 3) (Fin 3) F).mulVec w ∈ W := by
      rintro g _ ⟨c, hc, rfl⟩
      obtain ⟨x, hx⟩ := hsurj g
      have hxc : (x : G) * c * (x : G)⁻¹ ∈ A :=
        (Subgroup.mem_normalizer_iff.mp (hXA x.2) c).mp c.2
      have := hβe x c ⟨_, hxc⟩ rfl
      rw [← hx, ← this]
      exact hmemW _ ((Subgroup.mem_normalizer_iff.mp (hXC x.2) c).mp hc)
    obtain ⟨c, hcC, hcB⟩ := Set.exists_of_ssubset hC1
    have hcA : c ∈ A := hC2.le hcC
    have hc0 : Multiplicative.toAdd (β ⟨c, hcA⟩) ≠ 0 := fun h => hcB ((hker _).mpr
      (Multiplicative.toAdd.injective (by rw [h, toAdd_one])))
    apply (not_le_of_gt hC2)
    intro a ha
    obtain ⟨d, hdC, hda⟩ := eq_top_of_invariant W hWinv (hmemW ⟨c, hcA⟩ hcC) hc0
      (Multiplicative.toAdd (β ⟨a, ha⟩))
    have hb : ((d⁻¹ * ⟨a, ha⟩ : ↥A) : G) ∈ B := by
      rw [hker, map_mul, map_inv, Multiplicative.toAdd.injective hda, inv_mul_cancel]
    have := C.mul_mem hdC (hC1.le hb)
    simpa using this
  ·
    have e : (⟨a ^ 2 ^ 1, A.pow_mem ha _⟩ : ↥A) = ⟨a, ha⟩ ^ 2 := Subtype.ext (by simp)
    have h := (hker ⟨a ^ 2 ^ 1, A.pow_mem ha _⟩).mpr (by
      rw [e, map_pow]
      apply Multiplicative.toAdd.injective
      rw [toAdd_pow, toAdd_one, two_smul, ← two_smul F, h2, zero_smul])
    exact h
  ·
    obtain ⟨g, w, hgw⟩ := hmov
    obtain ⟨x, hx⟩ := hsurj g
    obtain ⟨a, ha⟩ := hβs (Multiplicative.ofAdd w)
    have hxa : (x : G) * a * (x : G)⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.mp (hXA x.2) a).mp a.2
    have hcomm : ⁅(a : G), (x : G)⁆ ∈ B := hc (Subgroup.commutator_mem_commutator a.2 x.2)
    have e : ⁅(a : G), (x : G)⁆ = ((a * (⟨_, hxa⟩ : ↥A)⁻¹ : ↥A) : G) := by
      simp only [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rw [e, hker, map_mul, map_inv, mul_inv_eq_one] at hcomm
    have h1 := hβe x a ⟨_, hxa⟩ rfl
    rw [← hcomm, ha, hx] at h1
    simp only [toAdd_ofAdd] at h1
    exact hgw h1.symm

end Chief3323

end CFSG.Quasithin.H13
