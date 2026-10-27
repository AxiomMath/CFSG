module

public import CFSG.Quasithin.EmptyFaithful.S153QPD1
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7aOvergroup
public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagOrder
public import CFSG.LinearAlgebra.LinearGroups.Perfect
public import CFSG.Assembly.Defs

public section

namespace CFSG.Quasithin.QP

open Matrix Module CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.QuasithinUnique.Setup.X7a

section Counting

variable {n : ℕ} {F : Type} [Field F]

@[expose] def fixSp (g : Matrix (Fin n) (Fin n) F) : Submodule F (Fin n → F) :=
  LinearMap.eqLocus (Matrix.mulVecLin g) LinearMap.id

theorem natCard_eq_two_pow (hF : Nat.card F = 2) {V : Type*} [AddCommGroup V] [Module F V]
    [Module.Finite F V] [Finite F] : Nat.card V = 2 ^ finrank F V := by
  rw [Module.natCard_eq_pow_finrank (K := F), hF]

theorem card_modEq_fixSp [Finite F] (hF : Nat.card F = 2) {g : Matrix (Fin n) (Fin n) F}
    (hg : g ^ 5 = 1) (W : Submodule F (Fin n → F)) (hW : ∀ w ∈ W, g *ᵥ w ∈ W) :
    2 ^ finrank F W ≡ 2 ^ finrank F ↥(W ⊓ fixSp g) [MOD 5] := by
  classical
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  let f : Function.End ↥W := fun w => ⟨g *ᵥ (w : Fin n → F), hW w w.2⟩
  have hit : ∀ k : ℕ, ∀ w : ↥W,
      (((f : ↥W → ↥W)^[k] w : ↥W) : Fin n → F) = (g ^ k) *ᵥ (w : Fin n → F) := by
    intro k
    induction k with
    | zero => intro w; rw [Function.iterate_zero_apply, pow_zero, Matrix.one_mulVec]
    | succ k ih =>
      intro w
      rw [Function.iterate_succ_apply', pow_succ', ← Matrix.mulVec_mulVec, ← ih w]
  have hf5 : f ^ 5 ^ 1 = 1 := by
    funext w
    apply Subtype.ext
    show (((f : ↥W → ↥W)^[5 ^ 1] w : ↥W) : Fin n → F) = (w : Fin n → F)
    rw [hit, pow_one, hg, Matrix.one_mulVec]
  have : Fintype F := Fintype.ofFinite F
  have : Fintype ↥W := Fintype.ofFinite ↥W
  have hmod := Equiv.Perm.card_fixedPoints_modEq (p := 5) (n := 1) hf5
  have h1 : Nat.card ↥W ≡ Nat.card (Function.fixedPoints f) [MOD 5] := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card] at hmod
    exact hmod
  have h2 : Nat.card (Function.fixedPoints f) = Nat.card ↥(W ⊓ fixSp g) := by
    refine Nat.card_congr
      { toFun := fun w => ⟨(w.1 : Fin n → F), ⟨w.1.2, ?_⟩⟩
        invFun := fun v => ⟨⟨(v : Fin n → F), v.2.1⟩, ?_⟩
        left_inv := fun w => rfl
        right_inv := fun v => rfl }
    · have := w.2
      exact congrArg Subtype.val this
    · exact Subtype.ext v.2.2
  rw [h2, natCard_eq_two_pow hF (V := ↥W), natCard_eq_two_pow hF (V := ↥(W ⊓ fixSp g))] at h1
  exact h1

theorem eq_one_of_fixSp_eq_top {g : Matrix (Fin n) (Fin n) F} (h : fixSp g = ⊤) : g = 1 := by
  ext i j
  have h1 : (Pi.single j (1 : F) : Fin n → F) ∈ fixSp g := by rw [h]; trivial
  have h2 : g *ᵥ (Pi.single j (1 : F)) = Pi.single j 1 := h1
  rw [Matrix.mulVec_single_one] at h2
  have := congrFun h2 i
  simpa [Pi.single_apply, Matrix.one_apply] using this

theorem finrank_fixSp_four [Finite F] (hF : Nat.card F = 2) {g : Matrix (Fin 4) (Fin 4) F}
    (hg5 : g ^ 5 = 1) (hg1 : g ≠ 1) : finrank F (fixSp g) = 0 := by
  have hmod := card_modEq_fixSp hF hg5 ⊤ (fun w _ => trivial)
  rw [top_inf_eq, finrank_top, Module.finrank_fin_fun] at hmod
  have hle : finrank F (fixSp g) ≤ 4 := by
    have := Submodule.finrank_le (fixSp g)
    rwa [Module.finrank_fin_fun] at this
  have hne : finrank F (fixSp g) ≠ 4 := by
    intro h4
    apply hg1
    apply eq_one_of_fixSp_eq_top
    apply Submodule.eq_top_of_finrank_eq
    rw [h4, Module.finrank_fin_fun]
  generalize finrank F (fixSp g) = c at hle hne hmod
  interval_cases c <;> simp_all [Nat.ModEq]

theorem false_of_stable_four [Finite F] (hF : Nat.card F = 2) {g : Matrix (Fin 4) (Fin 4) F}
    (hg5 : g ^ 5 = 1) (hg1 : g ≠ 1) {W : Submodule F (Fin 4 → F)} (hW : ∀ w ∈ W, g *ᵥ w ∈ W)
    (h1 : 1 ≤ finrank F W) (h3 : finrank F W ≤ 3) : False := by
  have hmod := card_modEq_fixSp hF hg5 W hW
  have hc : finrank F ↥(W ⊓ fixSp g) = 0 := by
    have h0 := finrank_fixSp_four hF hg5 hg1
    have := Submodule.finrank_mono (inf_le_right : W ⊓ fixSp g ≤ fixSp g)
    omega
  rw [hc] at hmod
  generalize finrank F W = d at h1 h3 hmod
  interval_cases d <;> simp_all [Nat.ModEq]

theorem finrank_fixSp_five [Finite F] (hF : Nat.card F = 2) {g : Matrix (Fin 5) (Fin 5) F}
    (hg5 : g ^ 5 = 1) (hg1 : g ≠ 1) : finrank F (fixSp g) = 1 := by
  have hmod := card_modEq_fixSp hF hg5 ⊤ (fun w _ => trivial)
  rw [top_inf_eq, finrank_top, Module.finrank_fin_fun] at hmod
  have hle : finrank F (fixSp g) ≤ 5 := by
    have := Submodule.finrank_le (fixSp g)
    rwa [Module.finrank_fin_fun] at this
  have hne : finrank F (fixSp g) ≠ 5 := by
    intro h4
    apply hg1
    apply eq_one_of_fixSp_eq_top
    apply Submodule.eq_top_of_finrank_eq
    rw [h4, Module.finrank_fin_fun]
  generalize finrank F (fixSp g) = c at hle hne hmod
  interval_cases c <;> simp_all [Nat.ModEq]

theorem false_of_stable_five [Finite F] (hF : Nat.card F = 2) {g : Matrix (Fin 5) (Fin 5) F}
    (hg5 : g ^ 5 = 1) (hg1 : g ≠ 1) {W : Submodule F (Fin 5 → F)} (hW : ∀ w ∈ W, g *ᵥ w ∈ W)
    (h2 : 2 ≤ finrank F W) (h3 : finrank F W ≤ 3) : False := by
  have hmod := card_modEq_fixSp hF hg5 W hW
  have hc : finrank F ↥(W ⊓ fixSp g) ≤ 1 := by
    have h0 := finrank_fixSp_five hF hg5 hg1
    have := Submodule.finrank_mono (inf_le_right : W ⊓ fixSp g ≤ fixSp g)
    omega
  generalize finrank F ↥(W ⊓ fixSp g) = c at hc hmod
  generalize finrank F W = d at h2 h3 hmod
  interval_cases d <;> interval_cases c <;> simp_all [Nat.ModEq]

end Counting

section Cardinality

variable {F : Type} [Field F] [Finite F]

theorem card_sl_over_two (hF : Nat.card F = 2) (n : ℕ) [NeZero n] :
    Nat.card (SpecialLinearGroup (Fin n) F) = ∏ i : Fin n, (2 ^ n - 2 ^ (i : ℕ)) := by
  have : Fintype F := Fintype.ofFinite F
  have hF' : Fintype.card F = 2 := by rw [← Nat.card_eq_fintype_card]; exact hF
  have h1 : Nat.card (SpecialLinearGroup (Fin n) F) * Nat.card Fˣ = Nat.card (GL (Fin n) F) :=
    Matrix.card_SL_mul_card_units
  have h2 : Nat.card (GL (Fin n) F) =
      ∏ i : Fin n, (Fintype.card F ^ n - Fintype.card F ^ (i : ℕ)) := Matrix.card_GL_field n
  have h3 : Nat.card Fˣ = 1 := by rw [Nat.card_units, hF]
  rw [h3, mul_one, h2, hF'] at h1
  exact h1

theorem seven_dvd_card_sl_four (hF : Nat.card F = 2) :
    7 ∣ Nat.card (SpecialLinearGroup (Fin 4) F) := by
  rw [card_sl_over_two hF, Fin.prod_univ_four]
  norm_num

theorem seven_dvd_card_sl_five (hF : Nat.card F = 2) :
    7 ∣ Nat.card (SpecialLinearGroup (Fin 5) F) := by
  rw [card_sl_over_two hF, Fin.prod_univ_five]
  norm_num

end Cardinality

theorem not_seven_dvd_two_pow_mul_sixty (b : ℕ) : ¬ 7 ∣ 2 ^ b * 60 := by
  intro h
  rcases (Nat.Prime.dvd_mul (by norm_num : Nat.Prime 7)).1 h with h | h
  · exact absurd (Nat.Prime.dvd_of_dvd_pow (by norm_num) h) (by norm_num)
  · exact absurd h (by norm_num)

section Overgroup

variable {K : Type*} [Field K] {n : ℕ}

theorem exists_le_stabilizer_of_ne_top {A : Subgroup (SpecialLinearGroup (Fin n) K)}
    (hVA : unitriangular n K ≤ A) (hAt : A ≠ ⊤) :
    ∃ i : ℕ, 1 ≤ i ∧ i < n ∧ A ≤ stabilizer (flagSpace n K i) := by
  obtain ⟨hle, hiff⟩ :=
    (linear_unitriangular_overgroup_subflag_containment (n := n) (K := K)).1 A hVA
  have hne : borelOvergroupCuts A ≠ ∅ := fun he => hAt (hiff.mp he)
  obtain ⟨i, hi⟩ := Set.nonempty_iff_ne_empty.mpr hne
  obtain ⟨hi1, hin, -⟩ := id hi
  exact ⟨i, hi1, hin, fun g hg => mem_flagStabilizer.mp (hle hg) i hi⟩

theorem mulVec_mem_of_mem_stabilizer {W : Submodule K (Fin n → K)} {g : SpecialLinearGroup (Fin n) K}
    (hg : g ∈ stabilizer W) {w : Fin n → K} (hw : w ∈ W) :
    (g : Matrix (Fin n) (Fin n) K) *ᵥ w ∈ W := by
  have : (g : Matrix (Fin n) (Fin n) K) *ᵥ w ∈ W.map (mulVecLin (g : Matrix (Fin n) (Fin n) K)) :=
    ⟨w, hw, rfl⟩
  rwa [mem_stabilizer.mp hg] at this

end Overgroup

section Four

variable {F : Type} [Field F] [Finite F]

theorem false_of_normalizes_sl4 (hF : Nat.card F = 2) {Y : Type} [Group Y] [Finite Y]
    (ι : Y →* SpecialLinearGroup (Fin 4) F) (hι : IsPGroup 2 ι.ker)
    (hN : unitriangular 4 F ≤ Subgroup.normalizer (ι.range : Set (SpecialLinearGroup (Fin 4) F)))
    {N : Type} [Group N] [Finite N] [IsSimpleGroup N] (hN60 : Nat.card N = 60)
    (θ : Y →* N) (hθ : Function.Surjective θ) (hk : IsPGroup 2 θ.ker) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set U := unitriangular 4 F with hU
  have hUp : IsPGroup 2 U :=
    IsPGroup.of_card (n := 6) (by rw [hU, card_unitriangular, hF])
  set X := ι.range with hX
  set A := X ⊔ U with hA
  have : Group.IsPerfect (SpecialLinearGroup (Fin 4) F) :=
    CFSG.LinearGroups.special_linear_isPerfect (by norm_num) (Or.inl (by norm_num))
  by_cases hAtop : A = ⊤
  · have hXtop : X = ⊤ := eq_top_of_sup_isPGroup_of_isPerfect hUp hN hAtop
    obtain ⟨b, hb⟩ := card_dvd_two_pow_mul_of_surjective ι (MonoidHom.range_eq_top.1 hXtop) θ hθ hk
      hN60
    exact not_seven_dvd_two_pow_mul_sixty b ((seven_dvd_card_sl_four hF).trans hb)
  · obtain ⟨i, hi1, hi4, hAi⟩ := exists_le_stabilizer_of_ne_top (le_sup_right : U ≤ A) hAtop
    obtain ⟨a, ha5⟩ := exists_orderOf_five hN60 θ hθ
    have hga5 : (ι a) ^ 5 = 1 := by
      rw [← map_pow, ← ha5, pow_orderOf_eq_one, map_one]
    have hga1 : ι a ≠ 1 := by
      intro h1
      have hmem : a ∈ ι.ker := h1
      obtain ⟨k, hk'⟩ := hι ⟨a, hmem⟩
      have h2 : a ^ 2 ^ k = 1 := congrArg Subtype.val hk'
      have h3 : 5 ∣ 2 ^ k := ha5 ▸ orderOf_dvd_of_pow_eq_one h2
      exact absurd (Nat.Prime.dvd_of_dvd_pow (by norm_num) h3) (by norm_num)
    have hmem : ι a ∈ stabilizer (flagSpace 4 F i) := hAi (Subgroup.mem_sup_left ⟨a, rfl⟩)
    refine false_of_stable_four hF (g := ((ι a : SpecialLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F))
      ?_ ?_ (W := flagSpace 4 F i) (fun w hw => mulVec_mem_of_mem_stabilizer hmem hw) ?_ ?_
    · rw [← Matrix.SpecialLinearGroup.coe_pow, hga5, Matrix.SpecialLinearGroup.coe_one]
    · exact fun h => hga1 (Subtype.ext h)
    · rw [finrank_flagSpace hi4.le]; exact hi1
    · rw [finrank_flagSpace hi4.le]; omega

end Four

end CFSG.Quasithin.QP
