module

public import CFSG.Quasithin.Background.B69Alt
public import CFSG.Quasithin.Background.GoldschmidtE23Nat

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.Assembly.LowTwoRank G6

namespace GE23

theorem sl2_sq_eq_one_of_fixed {K : Type} [Field K] (h2 : (2 : K) = 0)
    (γ : Matrix.SpecialLinearGroup (Fin 2) K) {v : Fin 2 → K} (hv : v ≠ 0)
    (h : (γ : Matrix (Fin 2) (Fin 2) K).mulVec v = v) : γ ^ 2 = 1 := by
  have hdet : (γ : Matrix (Fin 2) (Fin 2) K).det = 1 := γ.2
  have hker : ((γ : Matrix (Fin 2) (Fin 2) K) - 1).mulVec v = 0 := by
    rw [Matrix.sub_mulVec, h, Matrix.one_mulVec, sub_self]
  have hdet0 : ((γ : Matrix (Fin 2) (Fin 2) K) - 1).det = 0 :=
    Matrix.exists_mulVec_eq_zero_iff.1 ⟨v, hv, hker⟩
  rw [Matrix.det_fin_two] at hdet hdet0
  simp only [Matrix.sub_apply, Matrix.one_apply_eq, Matrix.one_apply_ne, ne_eq, Fin.zero_eq_one_iff,
    OfNat.ofNat_ne_one, not_false_eq_true, sub_zero, one_ne_zero] at hdet0
  have htr : (γ : Matrix (Fin 2) (Fin 2) K) 0 0 + (γ : Matrix (Fin 2) (Fin 2) K) 1 1 = 0 := by
    linear_combination (-1 : K) * hdet0 + hdet + h2
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_pow, pow_two, Matrix.SpecialLinearGroup.coe_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  · linear_combination (γ : Matrix (Fin 2) (Fin 2) K) 0 0 * htr - hdet - h2
  · linear_combination (γ : Matrix (Fin 2) (Fin 2) K) 0 1 * htr
  · linear_combination (γ : Matrix (Fin 2) (Fin 2) K) 1 0 * htr
  · linear_combination (γ : Matrix (Fin 2) (Fin 2) K) 1 1 * htr - hdet - h2


theorem two_eq_zero_of_card {K : Type} [Field K] [Finite K] {e : ℕ} (hK : Nat.card K = 2 ^ e) :
    (2 : K) = 0 := by
  have hfin : Fintype K := Fintype.ofFinite K
  have h1 := FiniteField.cast_card_eq_zero K
  rw [← Nat.card_eq_fintype_card, hK] at h1
  have he : e ≠ 0 := by
    rintro rfl
    have : Nat.card K = 1 := by simpa using hK
    have h3 : Nat.card K ≠ 1 := by
      rw [Nat.card_eq_fintype_card]
      exact (Fintype.one_lt_card_iff_nontrivial.2 inferInstance).ne'
    exact h3 this
  push_cast at h1
  exact pow_eq_zero_iff he |>.1 h1

theorem not_nat_and_alt_aux {V : Type} [CommGroup V] {A L : Subgroup (MulAut V)} {W : Subgroup V}
    {e n : ℕ} (hn : Odd n) (hn5 : 5 ≤ n) {π : Equiv.Perm (Fin n) →* ↥(L ⊔ A)}
    (hreal : (FFModel.symDn n).RealizesVia (L ⊔ A) W ⊥ π)
    (hLeq : L = (alternatingGroup (Fin n)).map ((L ⊔ A).subtype.comp π))
    (hnat : BinaryNaturalSL L W (W ⊓ fixV L) 2 e) : False := by
  classical
  have hUinv := hreal.2.2.2.1
  obtain ⟨e', he'⟩ := B69.exists_core_equiv hn hreal
  let a : Fin n := ⟨0, by omega⟩
  let b : Fin n := ⟨1, by omega⟩
  let c : Fin n := ⟨2, by omega⟩
  let d : Fin n := ⟨3, by omega⟩
  have hab : a ≠ b := Fin.ne_of_val_ne (by simp [a, b])
  have hac : a ≠ c := Fin.ne_of_val_ne (by simp [a, c])
  have hbc : b ≠ c := Fin.ne_of_val_ne (by simp [b, c])
  have hda : d ≠ a := Fin.ne_of_val_ne (by simp [a, d])
  have hdb : d ≠ b := Fin.ne_of_val_ne (by simp [b, d])
  have hdc : d ≠ c := Fin.ne_of_val_ne (by simp [c, d])
  set c₁ : Equiv.Perm (Fin n) := Equiv.swap a b * Equiv.swap a c with hc₁
  set c₂ : Equiv.Perm (Fin n) := Equiv.swap d a * Equiv.swap d b with hc₂
  have h3₁ : c₁.IsThreeCycle := Equiv.Perm.isThreeCycle_swap_mul_swap_same hab hac hbc
  have h3₂ : c₂.IsThreeCycle := Equiv.Perm.isThreeCycle_swap_mul_swap_same hda hdb hab
  have hc₁A : c₁ ∈ alternatingGroup (Fin n) := Equiv.Perm.mem_alternatingGroup.2 h3₁.sign
  have hc₂A : c₂ ∈ alternatingGroup (Fin n) := Equiv.Perm.mem_alternatingGroup.2 h3₂.sign
  have hc₁d : c₁ d = d := by
    simp only [hc₁, Equiv.Perm.mul_apply]
    rw [Equiv.swap_apply_of_ne_of_ne hda hdc, Equiv.swap_apply_of_ne_of_ne hda hdb]
  have hc₁a : c₁ a ≠ a := by
    simp only [hc₁, Equiv.Perm.mul_apply]
    rw [Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne hac.symm hbc.symm]
    exact hac.symm
  have hc₂d : c₂ d ≠ d := by
    simp only [hc₂, Equiv.Perm.mul_apply]
    rw [Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne hdb.symm hab.symm]
    exact hdb.symm
  have hmemL : ∀ σ ∈ alternatingGroup (Fin n), ((π σ : ↥(L ⊔ A)) : MulAut V) ∈ L := fun σ hσ =>
    hLeq.ge (Subgroup.mem_map.2 ⟨σ, hσ, rfl⟩)
  let wpt : Fin n → ↥W := fun i => e'.symm (B69.uCore hn i)
  have hwfix : ∀ (σ : Equiv.Perm (Fin n)) (i : Fin n), σ i = i →
      ((π σ : ↥(L ⊔ A)) : MulAut V) ((wpt i : ↥W) : V) = (wpt i : V) := by
    intro σ i hσ
    have hu := hUinv (π σ) ((wpt i : ↥W) : V) (wpt i).2
    have h1 := he' σ (wpt i) hu
    have e1 : e' (wpt i) = B69.uCore hn i := e'.apply_symm_apply _
    rw [e1, B69.coreAct_uCore, hσ] at h1
    have h2 : (⟨_, hu⟩ : ↥W) = wpt i := e'.injective (h1.trans e1.symm)
    exact congrArg Subtype.val h2
  have hwmove : ∀ (σ : Equiv.Perm (Fin n)) (i : Fin n), σ i ≠ i →
      ((π σ : ↥(L ⊔ A)) : MulAut V) ((wpt i : ↥W) : V) ≠ (wpt i : V) := by
    intro σ i hσ heq
    have hu := hUinv (π σ) ((wpt i : ↥W) : V) (wpt i).2
    have h1 := he' σ (wpt i) hu
    have e1 : e' (wpt i) = B69.uCore hn i := e'.apply_symm_apply _
    rw [e1, B69.coreAct_uCore] at h1
    have h2 : (⟨_, hu⟩ : ↥W) = wpt i := Subtype.ext heq
    have h3 : e' ⟨_, hu⟩ = e' (wpt i) := by rw [h2]
    rw [h1, e1] at h3
    exact hσ (B69.uVec_injective (congrArg Subtype.val h3))
  obtain ⟨K, instK, instF, hK, π', β', hπs', hβs, hβz, hUinv', hβeq⟩ :=
    natData_of_binaryNatural hnat
  have h2K : (2 : K) = 0 := two_eq_zero_of_card hK
  have hxL : ((π c₁ : ↥(L ⊔ A)) : MulAut V) ∈ L := hmemL c₁ hc₁A
  obtain ⟨γ, hγ⟩ := hπs' ⟨_, hxL⟩
  set w₀ : ↥W := wpt d with hw₀
  have hnotfix : (w₀ : V) ∉ fixV L := by
    intro hfix
    exact hwmove c₂ d hc₂d (hfix _ (hmemL c₂ hc₂A))
  have hβu : β' w₀ ≠ 1 := fun h1 => hnotfix ((hβz w₀).1 h1).2
  have hu : ((π' γ : ↥L) : MulAut V) (w₀ : V) ∈ W := hUinv' _ _ w₀.2
  have hxw : ((π' γ : ↥L) : MulAut V) (w₀ : V) = w₀ := by
    rw [hγ]
    exact hwfix c₁ d hc₁d
  have key := hβeq γ w₀ hu
  have hwu : (⟨((π' γ : ↥L) : MulAut V) (w₀ : V), hu⟩ : ↥W) = w₀ := Subtype.ext hxw
  rw [hwu] at key
  have hfixv : (γ : Matrix (Fin 2) (Fin 2) K).mulVec (Multiplicative.toAdd (β' w₀)) =
      Multiplicative.toAdd (β' w₀) := by
    have h1 := congrArg Multiplicative.toAdd key
    simpa using h1.symm
  have hm0 : Multiplicative.toAdd (β' w₀) ≠ 0 := by
    intro h0
    apply hβu
    apply Multiplicative.toAdd.injective
    simpa using h0
  have hsq := sl2_sq_eq_one_of_fixed h2K γ hm0 hfixv
  have hx2 : (((π c₁ : ↥(L ⊔ A)) : MulAut V)) ^ 2 = 1 := by
    have h1 : (π' γ) ^ 2 = 1 := by
      rw [← map_pow, hsq, map_one]
    rw [hγ] at h1
    exact congrArg Subtype.val h1
  have hx3 : (((π c₁ : ↥(L ⊔ A)) : MulAut V)) ^ 3 = 1 := by
    have h1 : c₁ ^ 3 = 1 := by rw [← h3₁.orderOf]; exact pow_orderOf_eq_one c₁
    have h2 : (π c₁) ^ 3 = 1 := by rw [← map_pow, h1, map_one]
    exact congrArg Subtype.val h2
  have hx1 : ((π c₁ : ↥(L ⊔ A)) : MulAut V) = 1 := by
    have : ((π c₁ : ↥(L ⊔ A)) : MulAut V) = ((π c₁ : ↥(L ⊔ A)) : MulAut V) ^ 3 *
        (((π c₁ : ↥(L ⊔ A)) : MulAut V) ^ 2)⁻¹ := by group
    rw [this, hx2, hx3]
    simp
  exact hwmove c₁ a hc₁a (by rw [hx1]; rfl)

theorem altShape_data {V : Type} [CommGroup V] {M A L : Subgroup (MulAut V)} {W : Subgroup V}
    (hperf : Group.IsPerfect ↥L) (hnt : Nontrivial ↥L) (halt : B69.AltShape M A L W) :
    ∃ k : ℕ, 2 ≤ k ∧ ∃ π : Equiv.Perm (Fin (2 * k + 1)) →* ↥(L ⊔ A), Function.Surjective π ∧
      (FFModel.symDn (2 * k + 1)).RealizesVia (L ⊔ A) W ⊥ π ∧
      L = (alternatingGroup (Fin (2 * k + 1))).map ((L ⊔ A).subtype.comp π) ∧
      (∃ i j : Fin (2 * k + 1), i ≠ j ∧
        A = (Subgroup.zpowers (Equiv.swap i j)).map ((L ⊔ A).subtype.comp π)) := by
  classical
  obtain ⟨k, hk, π, hπs, hreal, hLeq, hA, -⟩ := halt
  refine ⟨k, ?_, π, hπs, hreal, hLeq, hA⟩
  by_contra hlt
  have hk1 : k = 1 := by omega
  subst hk1
  refine Group.IsPerfect.not_isMulCommutative ↥L
    (IsMulCommutative.of_setLike_mul_comm fun a ha b hb => ?_)
  rw [hLeq] at ha hb
  obtain ⟨σ₁, hσ₁, rfl⟩ := Subgroup.mem_map.1 ha
  obtain ⟨σ₂, hσ₂, rfl⟩ := Subgroup.mem_map.1 hb
  have hcomm : ∀ a b : alternatingGroup (Fin (2 * 1 + 1)), a * b = b * a := by decide
  have := congrArg (fun x : alternatingGroup (Fin (2 * 1 + 1)) =>
      ((L ⊔ A).subtype.comp π) (x : Equiv.Perm (Fin (2 * 1 + 1))))
    (hcomm ⟨σ₁, hσ₁⟩ ⟨σ₂, hσ₂⟩)
  simpa using this

theorem not_nat_and_alt {V : Type} [CommGroup V] {M A L : Subgroup (MulAut V)} {W : Subgroup V}
    {e : ℕ} (hperf : Group.IsPerfect ↥L) (hnt : Nontrivial ↥L)
    (hnat : BinaryNaturalSL L W (W ⊓ fixV L) 2 e) (halt : B69.AltShape M A L W) : False := by
  obtain ⟨k, hk, π, -, hreal, hLeq, -⟩ := altShape_data hperf hnt halt
  exact not_nat_and_alt_aux (odd_two_mul_add_one k) (by omega) hreal hLeq hnat

end GE23

end CFSG.Quasithin
