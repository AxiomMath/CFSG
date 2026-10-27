module

public import CFSG.Quasithin.Background.FFC4Five

public section

namespace CFSG.Quasithin

namespace FFC

open CFSG.Assembly.LowTwoRank Equiv Equiv.Perm Matrix

section Three

variable {K : Type} [Field K]

@[expose] def matThree : Matrix (Fin 2) (Fin 2) K := !![0, -1; 1, -1]

theorem det_matThree : (matThree : Matrix (Fin 2) (Fin 2) K).det = 1 := by
  simp [matThree, Matrix.det_fin_two]

@[expose] def slThree : SpecialLinearGroup (Fin 2) K := ⟨matThree, det_matThree⟩

theorem matThree_pow : (matThree : Matrix (Fin 2) (Fin 2) K) ^ 3 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [matThree, pow_succ, Matrix.mul_apply, Fin.sum_univ_two]

theorem slThree_pow : (slThree : SpecialLinearGroup (Fin 2) K) ^ 3 = 1 := by
  ext i j
  have h : ((slThree : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = matThree := rfl
  simp [h, matThree_pow]

theorem slThree_ne_one : (slThree : SpecialLinearGroup (Fin 2) K) ≠ 1 := by
  intro h
  have := congrArg (fun g : SpecialLinearGroup (Fin 2) K => (g : Matrix (Fin 2) (Fin 2) K) 0 0) h
  simp [slThree, matThree] at this

theorem eq_zero_of_fixed_matThree [CharP K 2] (v : Fin 2 → K)
    (h : (matThree : Matrix (Fin 2) (Fin 2) K).mulVec v = v) : v = 0 := by
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  simp [matThree, Matrix.mulVec, dotProduct, Fin.sum_univ_two] at h0 h1
  have h2 : (2 : K) = 0 := by exact_mod_cast CharP.cast_eq_zero K 2
  have h3 : v 0 = 0 := by linear_combination h1 + v 1 * h2
  have h4 : v 1 = 0 := by linear_combination -h0 - h3
  funext i
  fin_cases i
  · simpa using h3
  · simpa using h4

@[expose] noncomputable def stThree (K : Type) [Field K] : ↥(StatedSL 2 K) :=
  specialLinearGroupEquivStatedSL 2 K slThree

theorem stThree_pow : (stThree K) ^ 3 = 1 := by
  unfold stThree
  rw [← map_pow, slThree_pow, map_one]

theorem stThree_ne_one : (stThree K) ≠ 1 := fun h =>
  slThree_ne_one ((specialLinearGroupEquivStatedSL 2 K).injective (h.trans (map_one _).symm))

theorem eq_one_of_fixed_stThree [CharP K 2] (m : Multiplicative (Fin 2 → K))
    (h : natAct (StatedSL 2 K) (stThree K) m = m) : m = 1 := by
  have h1 : (matThree : Matrix (Fin 2) (Fin 2) K).mulVec (Multiplicative.toAdd m) =
      Multiplicative.toAdd m := congrArg Multiplicative.toAdd h
  have h2 := eq_zero_of_fixed_matThree _ h1
  rw [← ofAdd_toAdd m, h2]
  rfl

end Three

section Transfer

variable {W : Type} [CommGroup W]

theorem false_of_sl2_sym5 {H L : Subgroup (MulAut W)} (hLH : L ≤ H) {U Z : Subgroup W} {K : Type}
    [Field K] [CharP K 2] {ρ : ↥(StatedSL 2 K) →* ↥L}
    (hρ : (FFModel.nat (StatedSL 2 K)).RealizesVia L U Z ρ) {π : Perm (Fin 5) →* ↥H}
    (hπ : (FFModel.symDn 5).RealizesVia H U Z π) : False := by
  have hρinj : Function.Injective ρ := injective_of_faithful_sec (FFModel.nat_faithful _) hρ
  have hπinj : Function.Injective π :=
    injective_of_faithful_sec (symDn_faithful (by norm_num)) hπ
  obtain ⟨f₁, hf₁s, hf₁k, hf₁e⟩ := RealizesVia.secMap (D := FFModel.nat (StatedSL 2 K)) rfl hρ
  obtain ⟨f₂, hf₂s, hf₂k, hf₂e⟩ := RealizesVia.secMap (D := FFModel.symDn 5) symDn_ker_five hπ
  have hgH : ((ρ (stThree K) : ↥L) : MulAut W) ∈ H := hLH (ρ (stThree K)).2
  obtain ⟨σ, hσ⟩ : ∃ σ : Perm (Fin 5), π σ = ⟨((ρ (stThree K) : ↥L) : MulAut W), hgH⟩ :=
    hπ.1 ⟨((ρ (stThree K) : ↥L) : MulAut W), hgH⟩
  have hσe : ((π σ : ↥H) : MulAut W) = ((ρ (stThree K) : ↥L) : MulAut W) :=
    congrArg Subtype.val hσ
  have hσ3 : σ ^ 3 = 1 := by
    apply hπinj
    rw [map_pow, map_one]
    apply Subtype.ext
    have h3 : (ρ (stThree K)) ^ 3 = 1 := by rw [← map_pow, stThree_pow, map_one]
    have h4 : (((ρ (stThree K)) ^ 3 : ↥L) : MulAut W) = 1 := congrArg Subtype.val h3
    rw [Subgroup.coe_pow] at h4 ⊢
    rw [hσe]
    exact h4
  have hσ1 : σ ≠ 1 := by
    intro h
    rw [h, map_one] at hσe
    have h5 : ρ (stThree K) = 1 := Subtype.ext hσe.symm
    exact stThree_ne_one (hρinj (h5.trans (map_one ρ).symm))
  obtain ⟨m, hm0, hmne, hmfix⟩ := exists_fix_three σ hσ3 hσ1
  have hy : Multiplicative.ofAdd m ∈ G6.coreMod 5 := hm0
  have hy1 : (Multiplicative.ofAdd m : G6.PermMod 5) ≠ 1 := fun h => hmne (by
    have := congrArg Multiplicative.toAdd h
    simpa using this)
  have hyfix : G6.permAct 5 σ (Multiplicative.ofAdd m) = Multiplicative.ofAdd m := by
    apply Multiplicative.toAdd.injective
    funext i
    exact hmfix i
  obtain ⟨u, hu⟩ := hf₂s ⟨Multiplicative.ofAdd m, hy⟩
  have hu' : ((π σ : ↥H) : MulAut W) (u : W) ∈ U := hπ.2.2.2.1 (π σ) u u.2
  have key₂ : f₂ ⟨((π σ : ↥H) : MulAut W) (u : W), hu'⟩ = f₂ u := by
    apply Subtype.ext
    have h6 := hf₂e σ u hu'
    rw [hu] at h6 ⊢
    exact h6.trans hyfix
  have hvZ : (((⟨((π σ : ↥H) : MulAut W) (u : W), hu'⟩ : ↥U) * u⁻¹ : ↥U) : W) ∈ Z := by
    refine (hf₂k _).1 ?_
    rw [map_mul, map_inv, key₂, mul_inv_cancel]
  have hv1 : f₁ ((⟨((π σ : ↥H) : MulAut W) (u : W), hu'⟩ : ↥U) * u⁻¹) = 1 := (hf₁k _).2 hvZ
  have hkey₁ : f₁ ⟨((π σ : ↥H) : MulAut W) (u : W), hu'⟩ = f₁ u := by
    have h7 : (⟨((π σ : ↥H) : MulAut W) (u : W), hu'⟩ : ↥U) =
        ((⟨((π σ : ↥H) : MulAut W) (u : W), hu'⟩ : ↥U) * u⁻¹) * u := by
      rw [inv_mul_cancel_right]
    rw [h7, map_mul, hv1, one_mul]
  have hu'' : ((ρ (stThree K) : ↥L) : MulAut W) (u : W) ∈ U := hρ.2.2.2.1 (ρ (stThree K)) u u.2
  have h8 := hf₁e (stThree K) u hu''
  have h9 : (⟨((ρ (stThree K) : ↥L) : MulAut W) (u : W), hu''⟩ : ↥U) =
      ⟨((π σ : ↥H) : MulAut W) (u : W), hu'⟩ := by
    apply Subtype.ext
    show ((ρ (stThree K) : ↥L) : MulAut W) (u : W) = ((π σ : ↥H) : MulAut W) (u : W)
    rw [hσe]
  have h8' : (f₁ ⟨((π σ : ↥H) : MulAut W) (u : W), hu'⟩).1 =
      (FFModel.nat (StatedSL 2 K)).act (stThree K) (f₁ u).1 :=
    (congrArg (fun z : ↥U => (f₁ z).1) h9).symm.trans h8
  rw [hkey₁] at h8'
  have h10 : natAct (StatedSL 2 K) (stThree K) (f₁ u).1 = (f₁ u).1 := h8'.symm
  have h11 := eq_one_of_fixed_stThree _ h10
  have h12 : f₁ u = 1 := Subtype.ext h11
  have h13 : (u : W) ∈ Z := (hf₁k u).1 h12
  have h14 : f₂ u = 1 := (hf₂k u).2 h13
  rw [hu] at h14
  exact hy1 (congrArg Subtype.val h14)

end Transfer

section Card

theorem card_sec_nat {d : ℕ} {K : Type} [Field K] (Γ : Subgroup (Matrix.GeneralLinearGroup (Fin d) K)) :
    Nat.card ↥(FFModel.nat Γ).sec = Nat.card K ^ d := by
  show Nat.card ↥(⊤ : Subgroup (Multiplicative (Fin d → K))) = _
  rw [Subgroup.card_top, Nat.card_congr (Multiplicative.toAdd : Multiplicative (Fin d → K) ≃ (Fin d → K)),
    Nat.card_fun, Nat.card_eq_fintype_card (α := Fin d), Fintype.card_fin]

variable {W : Type} [CommGroup W] [Finite W]

theorem false_of_sl3_sym5 {H L : Subgroup (MulAut W)} {U Z : Subgroup W} {K : Type} [Field K]
    (hK : Nat.card K = 2) {ρ : ↥(StatedSL 3 K) →* ↥L}
    (hρ : (FFModel.nat (StatedSL 3 K)).RealizesVia L U Z ρ) {π : Perm (Fin 5) →* ↥H}
    (hπ : (FFModel.symDn 5).RealizesVia H U Z π) : False := by
  have h1 := card_eq_of_realizes (D := FFModel.nat (StatedSL 3 K)) rfl hρ
  have h2 := card_eq_of_realizes (D := FFModel.symDn 5) symDn_ker_five hπ
  rw [card_sec_nat, hK] at h1
  rw [show Nat.card ↥(FFModel.symDn 5).sec = 16 from card_coreMod_five] at h2
  have hZ : 0 < Nat.card Z := Nat.card_pos
  omega

end Card

end FFC

end CFSG.Quasithin
