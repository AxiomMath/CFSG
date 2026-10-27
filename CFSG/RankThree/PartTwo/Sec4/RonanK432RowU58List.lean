module

public import CFSG.RankThree.PartTwo.KFacts.KS21AutThreeU58
public import CFSG.RankThree.PartTwo.Sec4.RonanK432Sylow
public import CFSG.RankThree.PartTwo.Sec4.RonanK432SylowCenter
public import CFSG.RankThree.PartTwo.Sec4.RonanK432Transport

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK432

open Matrix CFSG.RankThree.PartTwo.KFacts.KS21 CFSG.RankThree.PartTwo.KFacts.KS21.U58
  CFSG.RankThree.PartTwo.KFacts.KS21.DFT
open CFSG.Assembly.RankThreeEven (projSU)

@[expose] noncomputable def u58Chi : Multiplicative (ZMod 9) →* Kˣ :=
  expHom ζ9 ζ9_pow_nine

theorem u58Chi_inj {a b : ZMod 9} (h : u58Chi (.ofAdd a) = u58Chi (.ofAdd b)) : a = b :=
  Multiplicative.ofAdd.injective (expHom_injective ζ9_pow_nine orderOf_ζ9 h)

@[expose] noncomputable def u58DE (E : Fin 5 → ZMod 9) : GL (Fin 5) K :=
  TauCeti.diagGL fun i => u58Chi (.ofAdd (E i))

theorem u58DE_mul (E F : Fin 5 → ZMod 9) : u58DE E * u58DE F = u58DE (E + F) := by
  unfold u58DE
  rw [← map_mul]
  congr 1
  funext i
  simp only [Pi.mul_apply, Pi.add_apply, ofAdd_add, map_mul]

theorem u58DE_zero : u58DE 0 = 1 := by
  unfold u58DE
  have h : (fun i => u58Chi (.ofAdd ((0 : Fin 5 → ZMod 9) i))) = 1 := by
    funext i
    simp
  rw [h, map_one]

theorem u58DE_neg (E : Fin 5 → ZMod 9) : (u58DE E)⁻¹ = u58DE (-E) := by
  unfold u58DE
  rw [← map_inv]
  congr 1
  funext i
  simp only [Pi.inv_apply, Pi.neg_apply, ofAdd_neg, map_inv]

theorem u58DE_inj {E F : Fin 5 → ZMod 9} (h : u58DE E = u58DE F) : E = F := by
  have h' := TauCeti.diagGL_injective (k := K) h
  funext i
  exact u58Chi_inj (congrFun h' i)

theorem u58DE_perm (σ : Equiv.Perm (Fin 5)) (E : Fin 5 → ZMod 9) :
    TauCeti.permutationGL (k := K) σ * u58DE E * (TauCeti.permutationGL (k := K) σ)⁻¹ =
      u58DE (fun i => E (σ⁻¹ i)) := by
  unfold u58DE
  rw [TauCeti.permutationGL_mul_diagGL_mul_inv]

theorem u58_sign_cast (τ : Equiv.Perm (Fin 5)) :
    (((Equiv.Perm.sign τ : ℤˣ) : ℤ) : K) = 1 := by
  rcases Int.units_eq_one_or (Equiv.Perm.sign τ) with h | h
  · rw [h]
    simp
  · rw [h]
    simp only [Units.val_neg, Units.val_one, Int.cast_neg, Int.cast_one]
    exact CharTwo.neg_eq 1

theorem u58_perm_det (σ : Equiv.Perm (Fin 5)) :
    ((TauCeti.permutationGL (k := K) σ : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K).det = 1 := by
  rw [TauCeti.permutationGL_coe, Matrix.det_permutation, u58_sign_cast]

theorem u58_perm_unitary (σ : Equiv.Perm (Fin 5)) :
    (((TauCeti.permutationGL (k := K) σ : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K).map
        (· ^ (2 ^ 3)))ᵀ *
      ((TauCeti.permutationGL (k := K) σ : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) = 1 := by
  rw [TauCeti.permutationGL_coe]
  have hmap : (Equiv.Perm.permMatrix K σ⁻¹).map (· ^ (2 ^ 3)) = Equiv.Perm.permMatrix K σ⁻¹ := by
    ext i j
    rw [Matrix.map_apply]
    simp only [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply]
    split_ifs <;> simp
  rw [hmap, Matrix.transpose_permMatrix, inv_inv, ← Matrix.permMatrix_mul, inv_mul_cancel,
    Matrix.permMatrix_one]

theorem u58_perm_mem (σ : Equiv.Perm (Fin 5)) : TauCeti.permutationGL (k := K) σ ∈ SUI :=
  Subgroup.subset_closure ⟨u58_perm_det σ, u58_perm_unitary σ⟩

theorem u58_witness_perm {u : SUI} {E : Fin 5 → ZMod 9}
    (hu : ((u : SUI) : GL (Fin 5) K) = u58DE E) (hu3 : u ^ 3 = 1) (σ : Equiv.Perm (Fin 5))
    (h0 : (fun i => E (σ⁻¹ i)) ≠ 0) (h1 : (fun i => E (σ⁻¹ i)) ≠ E)
    (h2 : (fun i => E (σ⁻¹ i)) ≠ -E) :
    ∃ g : SUI, (g * u * g⁻¹) * u = u * (g * u * g⁻¹) ∧ g * u * g⁻¹ ∉ Subgroup.zpowers u := by
  set g : SUI := ⟨TauCeti.permutationGL (k := K) σ, u58_perm_mem σ⟩ with hg
  have hc : ((g * u * g⁻¹ : SUI) : GL (Fin 5) K) = u58DE (fun i => E (σ⁻¹ i)) := by
    rw [← u58DE_perm σ E, ← hu]
    rfl
  refine ⟨g, ?_, ?_⟩
  · apply Subtype.ext
    change ((g * u * g⁻¹ : SUI) : GL (Fin 5) K) * (u : GL (Fin 5) K) =
      (u : GL (Fin 5) K) * ((g * u * g⁻¹ : SUI) : GL (Fin 5) K)
    rw [hc, hu, u58DE_mul, u58DE_mul, add_comm]
  · intro hmem
    rcases mem_zpowers_cases_of_pow_three hu3 hmem with h | h | h
    · have h' := congrArg Subtype.val h
      have h'' : u58DE (fun i => E (σ⁻¹ i)) = u58DE 0 := by
        rw [u58DE_zero, ← hc]
        exact h'
      exact h0 (u58DE_inj h'')
    · have h' := congrArg Subtype.val h
      rw [hc, hu] at h'
      exact h1 (u58DE_inj h')
    · have h' := congrArg Subtype.val h
      rw [hc, Subgroup.coe_inv, hu, u58DE_neg] at h'
      exact h2 (u58DE_inj h')

theorem u58_comb03 : ∀ a d : ZMod 9, 3 * a = 0 → 3 * d = 0 → (a ≠ 0 ∨ d ≠ 0) → a ≠ d →
    (fun i => (![a, a, a, d, -(a + a + a + d)] : Fin 5 → ZMod 9) ((Equiv.swap (0 : Fin 5) 3)⁻¹ i))
        ≠ 0 ∧
    (fun i => (![a, a, a, d, -(a + a + a + d)] : Fin 5 → ZMod 9) ((Equiv.swap (0 : Fin 5) 3)⁻¹ i))
        ≠ ![a, a, a, d, -(a + a + a + d)] ∧
    (fun i => (![a, a, a, d, -(a + a + a + d)] : Fin 5 → ZMod 9) ((Equiv.swap (0 : Fin 5) 3)⁻¹ i))
        ≠ -![a, a, a, d, -(a + a + a + d)] := by
  decide

theorem u58_comb34 : ∀ a d : ZMod 9, 3 * a = 0 → 3 * d = 0 → (a ≠ 0 ∨ d ≠ 0) → a = d →
    (fun i => (![a, a, a, d, -(a + a + a + d)] : Fin 5 → ZMod 9) ((Equiv.swap (3 : Fin 5) 4)⁻¹ i))
        ≠ 0 ∧
    (fun i => (![a, a, a, d, -(a + a + a + d)] : Fin 5 → ZMod 9) ((Equiv.swap (3 : Fin 5) 4)⁻¹ i))
        ≠ ![a, a, a, d, -(a + a + a + d)] ∧
    (fun i => (![a, a, a, d, -(a + a + a + d)] : Fin 5 → ZMod 9) ((Equiv.swap (3 : Fin 5) 4)⁻¹ i))
        ≠ -![a, a, a, d, -(a + a + a + d)] := by
  decide

theorem u58_witness_central {a d : ZMod 9} (h3a : 3 * a = 0) (h3d : 3 * d = 0)
    (hne : a ≠ 0 ∨ d ≠ 0) {u : SUI}
    (hu : ((u : SUI) : GL (Fin 5) K) = u58DE ![a, a, a, d, -(a + a + a + d)])
    (hu3 : u ^ 3 = 1) :
    ∃ g : SUI, (g * u * g⁻¹) * u = u * (g * u * g⁻¹) ∧ g * u * g⁻¹ ∉ Subgroup.zpowers u := by
  by_cases had : a = d
  · obtain ⟨h0, h1, h2⟩ := u58_comb34 a d h3a h3d hne had
    exact u58_witness_perm hu hu3 (Equiv.swap 3 4) h0 h1 h2
  · obtain ⟨h0, h1, h2⟩ := u58_comb03 a d h3a h3d hne had
    exact u58_witness_perm hu hu3 (Equiv.swap 0 3) h0 h1 h2

theorem u58_coe_tau (a d : ZMod 9) :
    ((τS (.ofAdd ((fun _ => a), d)) : SUI) : GL (Fin 5) K) =
      u58DE ![a, a, a, d, -(a + a + a + d)] := by
  have hmul : ∀ x y : Multiplicative (ZMod 9), u58Chi (x * y) = u58Chi x * u58Chi y :=
    fun x y => map_mul _ x y
  have hinv : ∀ x : Multiplicative (ZMod 9), u58Chi x⁻¹ = (u58Chi x)⁻¹ := fun x => map_inv _ x
  have h4 : (u58Chi (.ofAdd a) * u58Chi (.ofAdd a) * u58Chi (.ofAdd a) * u58Chi (.ofAdd d))⁻¹ =
      u58Chi (.ofAdd (-(a + a + a + d))) := by
    rw [← hmul, ← hmul, ← hmul, ← hinv]
    congr 1
  rw [coe_τS]
  unfold u58DE
  congr 1
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact h4

theorem u58_tau_mul (x y : (Fin 3 → ZMod 9) × ZMod 9) :
    τS (.ofAdd x) * τS (.ofAdd y) = τS (.ofAdd (x + y)) := by
  rw [← map_mul, ← ofAdd_add]

theorem u58_central_form {u : SUI} (hu : u ∈ P₀) (hu3 : orderOf u = 3)
    (hc : ∀ q ∈ P₀, q * u = u * q) :
    ∃ a d : ZMod 9, 3 * a = 0 ∧ 3 * d = 0 ∧ (a ≠ 0 ∨ d ≠ 0) ∧
      u = τS (.ofAdd ((fun _ => a), d)) := by
  obtain ⟨⟨v1, dv⟩, j, rfl⟩ := hu
  have hmem : ∀ x : (Fin 3 → ZMod 9) × ZMod 9, τS (.ofAdd x) ∈ P₀ :=
    fun x => ⟨x, 0, by rw [pow_zero, mul_one]⟩
  have hwS : wS ∈ P₀ := ⟨0, 1, by rw [ofAdd_zero, map_one, one_mul, pow_one]⟩
  have hTc : ∀ x : (Fin 3 → ZMod 9) × ZMod 9,
      τS (.ofAdd x) * (τS (.ofAdd (v1, dv)) * wS ^ j) =
        τS (.ofAdd (v1, dv)) * wS ^ j * τS (.ofAdd x) :=
    fun x => hc _ (hmem x)
  have hwj : wS ^ j = wS ^ (j % 3) := pow_eq_pow_mod j wS_pow_three
  have hj3 : j % 3 = 0 ∨ j % 3 = 1 ∨ j % 3 = 2 := by omega
  rcases hj3 with h0 | h1 | h2
  ·
    have hu' : τS (.ofAdd (v1, dv)) * wS ^ j = τS (.ofAdd (v1, dv)) := by
      rw [hwj, h0, pow_zero, mul_one]
    rw [hu'] at hu3 hc ⊢
    have hwc := hc wS hwS
    rw [wS_mul_τS] at hwc
    have hr : τS (.ofAdd (rot9 (v1, dv))) = τS (.ofAdd (v1, dv)) := mul_right_cancel hwc
    have hr' : rot9 (v1, dv) = (v1, dv) := Multiplicative.ofAdd.injective (τS_injective hr)
    rw [rot9_apply] at hr'
    have hv1 : v1 = fun _ => v1 0 := rot3_fixed (congrArg Prod.fst hr')
    have h3 : (τS (.ofAdd (v1, dv))) ^ 3 = 1 := by
      have := pow_orderOf_eq_one (τS (.ofAdd (v1, dv)))
      rwa [hu3] at this
    have h4 : τS (.ofAdd (3 • (v1, dv))) = τS (.ofAdd 0) := by
      rw [ofAdd_zero, map_one, ofAdd_nsmul, map_pow, h3]
    have h5 : (3 • (v1, dv) : (Fin 3 → ZMod 9) × ZMod 9) = 0 :=
      Multiplicative.ofAdd.injective (τS_injective h4)
    rw [Prod.smul_mk, Prod.mk_eq_zero] at h5
    obtain ⟨h5a, h5b⟩ := h5
    have ha3 : 3 * v1 0 = 0 := by
      have := congrFun h5a 0
      simpa [nsmul_eq_mul] using this
    have hd3 : 3 * dv = 0 := by simpa [nsmul_eq_mul] using h5b
    refine ⟨v1 0, dv, ha3, hd3, ?_, ?_⟩
    · by_contra hcon
      simp only [not_or, not_not] at hcon
      obtain ⟨ha0, hd0⟩ := hcon
      have hv0 : (v1, dv) = 0 := by
        rw [Prod.mk_eq_zero]
        refine ⟨?_, hd0⟩
        rw [hv1, ha0]
        rfl
      rw [hv0, ofAdd_zero, map_one, orderOf_one] at hu3
      exact absurd hu3 (by decide)
    · rw [← hv1]
  ·
    exfalso
    have key : ∀ x : (Fin 3 → ZMod 9) × ZMod 9, rot9 x = x := by
      intro x
      have hx := hTc x
      rw [hwj, h1, pow_one] at hx
      have e1 : τS (.ofAdd x) * (τS (.ofAdd (v1, dv)) * wS) =
          τS (.ofAdd (x + (v1, dv))) * wS := by
        rw [← mul_assoc, u58_tau_mul]
      have e2 : τS (.ofAdd (v1, dv)) * wS * τS (.ofAdd x) =
          τS (.ofAdd ((v1, dv) + rot9 x)) * wS := by
        rw [mul_assoc, wS_mul_τS, ← mul_assoc, u58_tau_mul]
      rw [e1, e2] at hx
      have h3 := Multiplicative.ofAdd.injective (τS_injective (mul_right_cancel hx))
      have h4 : (v1, dv) + x = (v1, dv) + rot9 x := by
        rw [add_comm]
        exact h3
      exact (add_left_cancel h4).symm
    exact absurd (key (![1, 0, 0], 0)) (by decide)
  ·
    exfalso
    have key : ∀ x : (Fin 3 → ZMod 9) × ZMod 9, rot9 (rot9 x) = x := by
      intro x
      have hx := hTc x
      rw [hwj, h2] at hx
      have hw2 : wS ^ 2 * τS (.ofAdd x) = τS (.ofAdd (rot9 (rot9 x))) * wS ^ 2 :=
        pow_mul_tau wS_mul_τS 2 x
      have e1 : τS (.ofAdd x) * (τS (.ofAdd (v1, dv)) * wS ^ 2) =
          τS (.ofAdd (x + (v1, dv))) * wS ^ 2 := by
        rw [← mul_assoc, u58_tau_mul]
      have e2 : τS (.ofAdd (v1, dv)) * wS ^ 2 * τS (.ofAdd x) =
          τS (.ofAdd ((v1, dv) + rot9 (rot9 x))) * wS ^ 2 := by
        rw [mul_assoc, hw2, ← mul_assoc, u58_tau_mul]
      rw [e1, e2] at hx
      have h3 := Multiplicative.ofAdd.injective (τS_injective (mul_right_cancel hx))
      have h4 : (v1, dv) + x = (v1, dv) + rot9 (rot9 x) := by
        rw [add_comm]
        exact h3
      exact (add_left_cancel h4).symm
    exact absurd (key (![1, 0, 0], 0)) (by decide)

theorem u58_hw : ∀ u ∈ P₀, orderOf u = 3 → (∀ q ∈ P₀, q * u = u * q) →
    ∃ g : SUI, (g * u * g⁻¹) * u = u * (g * u * g⁻¹) ∧ g * u * g⁻¹ ∉ Subgroup.zpowers u := by
  intro u hu hu3 hc
  obtain ⟨a, d, h3a, h3d, hne, rfl⟩ := u58_central_form hu hu3 hc
  refine u58_witness_central h3a h3d hne (u58_coe_tau a d) ?_
  have h := pow_orderOf_eq_one (τS (.ofAdd ((fun _ => a), d)))
  rwa [hu3] at h

theorem u58_card_P₀ : Nat.card P₀ = 3 ^ 9 := by
  rw [card_torusExt τS_injective wS_pow_three wS_mul_τS rot9_ne, card_V9]
  norm_num

theorem u58_not_dvd : ¬ 3 ^ (9 + 1) ∣ Nat.card SUI := by
  rw [card_SUI]
  norm_num

theorem u58_listRow_SUI : ListRow SUI :=
  listRow_of_sylow_center 9 P₀ u58_card_P₀ u58_not_dvd u58_hw

theorem listRow_u58 : ListRow (projSU 5 2 3) :=
  ListRow.of_mulEquiv equivSUI.symm u58_listRow_SUI

end CFSG.RankThree.PartTwo.Sec4.RonanK432
