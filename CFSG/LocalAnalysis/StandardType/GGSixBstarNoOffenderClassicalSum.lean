module

public import CFSG.LocalAnalysis.StandardType.GGSixBstarNoOffenderClassicalCore

public section

namespace CFSG.StandardType

open CFSG.Assembly

namespace NoOffenderClassical

section SumZero

variable {G : Type*} [Group G] {F : Type*} [Field F] {ι : Type*} [Fintype ι] [DecidableEq ι]

structure CoordsOne (p : ℕ) (Bs : Subgroup G) (κ : G → ι → Fˣ) : Prop where
  mul : ∀ a ∈ Bs, ∀ b ∈ Bs, κ (a * b) = κ a * κ b
  inj : ∀ a ∈ Bs, ∀ b ∈ Bs, κ a = κ b → a = b
  prod : ∀ b ∈ Bs, ∏ i, κ b i = 1
  surj : ∀ t : ι → Fˣ, (∀ i, t i ^ p = 1) → ∏ i, t i = 1 → ∃ b ∈ Bs, κ b = t

variable {p : ℕ} {Bs E : Subgroup G} {κ : G → ι → Fˣ}

@[expose] def twoPoint (ζ : Fˣ) (i j : ι) : ι → Fˣ :=
  fun k => if k = i then ζ else if k = j then ζ⁻¹ else 1

omit [Fintype ι] in
theorem twoPoint_pow {ζ : Fˣ} (hζp : ζ ^ p = 1) (i j : ι) (k : ι) : twoPoint ζ i j k ^ p = 1 := by
  unfold twoPoint
  split_ifs
  · exact hζp
  · rw [inv_pow, hζp, inv_one]
  · exact one_pow p

theorem twoPoint_prod (ζ : Fˣ) {i j : ι} (hij : i ≠ j) : ∏ k, twoPoint ζ i j k = 1 := by
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i),
    ← Finset.mul_prod_erase _ _ (Finset.mem_erase.mpr ⟨Ne.symm hij, Finset.mem_univ j⟩)]
  rw [Finset.prod_eq_one]
  · simp [twoPoint, Ne.symm hij]
  · intro k hk
    rw [Finset.mem_erase, Finset.mem_erase] at hk
    simp [twoPoint, hk.1, hk.2.1]

omit [Fintype ι] in
theorem twoPoint_ne_one {ζ : Fˣ} (hζ1 : ζ ≠ 1) {i j : ι} (hij : i ≠ j) {k : ι} :
    twoPoint ζ i j k ≠ 1 ↔ k = i ∨ k = j := by
  unfold twoPoint
  constructor
  · intro h
    by_contra hk
    push Not at hk
    rw [ite_eq_right hk.1, ite_eq_right hk.2] at h
    exact h rfl
  · rintro (rfl | rfl)
    · rw [ite_eq_left rfl]
      exact hζ1
    · rw [ite_eq_right (Ne.symm hij), ite_eq_left rfl]
      exact inv_ne_one.mpr hζ1

theorem eq_of_supp_two {ζ : Fˣ} (hζ1 : ζ ≠ 1) (hζp : ζ ^ p = 1) (h : CoordsOne p Bs κ)
    (hι : 3 ≤ Fintype.card ι) {e : G} {τ τ' : Equiv.Perm ι}
    (hτ : ∀ b ∈ Bs, ∀ i, κ (e * b * e⁻¹) (τ i) = 1 ↔ κ b i = 1)
    (hτ' : ∀ b ∈ Bs, ∀ i, κ (e * b * e⁻¹) (τ' i) = 1 ↔ κ b i = 1) : τ = τ' := by
  classical
  ext i
  obtain ⟨j, k, hji, hki, hjk⟩ : ∃ j k : ι, j ≠ i ∧ k ≠ i ∧ j ≠ k := by
    by_contra hne
    push Not at hne
    obtain ⟨j, hj⟩ : ∃ j, j ≠ i := by
      by_contra h1
      push Not at h1
      have : Fintype.card ι ≤ 1 := Fintype.card_le_one_iff.mpr fun a b => (h1 a).trans (h1 b).symm
      omega
    have hsub : (Finset.univ : Finset ι) ⊆ {i, j} := fun k _ => by
      by_cases hk : k = i
      · simp [hk]
      · simp [hne j k hj hk]
    have := Finset.card_le_card hsub
    rw [Finset.card_univ] at this
    have h2 := Finset.card_le_two (a := i) (b := j)
    omega
  have key : ∀ l, l ≠ i → τ'.symm (τ i) = i ∨ τ'.symm (τ i) = l := by
    intro l hl
    obtain ⟨b, hb, hbt⟩ := h.surj (twoPoint ζ i l) (twoPoint_pow hζp i l)
      (twoPoint_prod ζ (Ne.symm hl))
    have h1 : κ (e * b * e⁻¹) (τ i) ≠ 1 := fun h0 => by
      have := (hτ b hb i).mp h0
      rw [hbt] at this
      exact (twoPoint_ne_one hζ1 (Ne.symm hl)).mpr (Or.inl rfl) this
    have h2 : κ b (τ'.symm (τ i)) ≠ 1 := fun h0 => by
      apply h1
      have := (hτ' b hb _).mpr h0
      rwa [Equiv.apply_symm_apply] at this
    rw [hbt] at h2
    exact (twoPoint_ne_one hζ1 (Ne.symm hl)).mp h2
  have hfix : τ'.symm (τ i) = i := by
    rcases key j hji with h1 | h1
    · exact h1
    rcases key k hki with h2 | h2
    · exact h2
    exact absurd (h1.symm.trans h2) hjk
  have h3 : τ' (τ'.symm (τ i)) = τ i := Equiv.apply_symm_apply _ _
  rw [hfix] at h3
  exact h3.symm

theorem exists_hom_of_supp_two [Finite G] {ζ : Fˣ} (hζ1 : ζ ≠ 1) (hζp : ζ ^ p = 1)
    (h : CoordsOne p Bs κ) (hι : 3 ≤ Fintype.card ι)
    (hEN : E ≤ Subgroup.normalizer (Bs : Set G))
    (hmono : ∀ e ∈ E, ∃ τ : Equiv.Perm ι, ∀ b ∈ Bs, ∀ i,
      κ (e * b * e⁻¹) (τ i) = 1 ↔ κ b i = 1) :
    ∃ T : ↥E →* Equiv.Perm ι, ∀ e : ↥E, ∀ b ∈ Bs, ∀ i,
      κ ((e : G) * b * (e : G)⁻¹) (T e i) = 1 ↔ κ b i = 1 := by
  choose τ hτ using hmono
  have hconj : ∀ e ∈ E, ∀ b ∈ Bs, e * b * e⁻¹ ∈ Bs := fun e he b hb =>
    (Subgroup.mem_normalizer_iff.mp (hEN he) b).mp hb
  refine ⟨{ toFun := fun e => τ e e.2, map_one' := ?_, map_mul' := ?_ }, fun e => hτ e e.2⟩
  · refine (eq_of_supp_two hζ1 hζp h hι (hτ 1 E.one_mem) fun b _ i => ?_)
    simp only [one_mul, inv_one, mul_one, Equiv.Perm.one_apply]
  · intro a b
    refine eq_of_supp_two hζ1 hζp h hι (hτ _ (a * b).2) fun x hx i => ?_
    simp only [Subgroup.coe_mul, Equiv.Perm.mul_apply, mul_inv_rev]
    have e1 : (a : G) * b * x * ((b : G)⁻¹ * (a : G)⁻¹) = a * (b * x * (b : G)⁻¹) * (a : G)⁻¹ := by
      group
    rw [e1, hτ a a.2 _ (hconj b b.2 x hx), hτ b b.2 x hx]

end SumZero

section Main

variable {G : Type*} [Group G] [Finite G] {F : Type*} [Field F] {ι : Type*} [Fintype ι]
  [LinearOrder ι]

theorem card_mul_lt_of_coordsOne {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {ζ : F}
    (hζ : IsPrimitiveRoot ζ p) {Bs E : Subgroup G} {κ : G → ι → Fˣ} (h : CoordsOne p Bs κ)
    (hι3 : 3 ≤ Fintype.card ι) (hpι : ¬ p ∣ Fintype.card ι)
    (hBs : IsElemAbelian p Bs) (hE : IsElemAbelian p E)
    (hEN : E ≤ Subgroup.normalizer (Bs : Set G))
    (hmono : ∀ e ∈ E, ∃ τ : Equiv.Perm ι, ∀ b ∈ Bs, ∀ i,
      κ (e * b * e⁻¹) (τ i) = 1 ↔ κ b i = 1)
    (hEC : ¬ E ≤ Subgroup.centralizer (Bs : Set G)) :
    Nat.card (Bs ⊓ Subgroup.centralizer (E : Set G) : Subgroup G) * Nat.card E <
      Nat.card Bs * Nat.card (E ⊓ Subgroup.centralizer (Bs : Set G) : Subgroup G) := by
  classical
  have : NeZero p := ⟨hp.ne_zero⟩
  have : Fact p.Prime := ⟨hp⟩
  set ζu : Fˣ := (hζ.isUnit hp.ne_zero).unit with hζudef
  have hζu : (ζu : F) = ζ := IsUnit.unit_spec _
  have hζup : ζu ^ p = 1 :=
    Units.ext (by rw [Units.val_pow_eq_pow_val, hζu, hζ.pow_eq_one, Units.val_one])
  have hζu1 : ζu ≠ 1 := fun h1 => hζ.ne_one hp.one_lt (by rw [← hζu, h1, Units.val_one])
  obtain ⟨T, hT⟩ := exists_hom_of_supp_two hζu1 hζup h hι3 hEN hmono
  let _ : MulAction ↥E ι := MulAction.compHom ι T
  have hEp : IsPGroup p ↥E := TableB.isPGroup_of_isElemAbelian hE
  obtain ⟨z, hz⟩ := hEp.nonempty_fixed_point_of_prime_not_dvd_card ι
    (by rwa [Nat.card_eq_fintype_card])
  have hTz : ∀ g : ↥E, T g z = z := fun g => hz g
  set κ' : G → {i // i ≠ z} → Fˣ := fun b i => κ b i.1 with hκ'
  have hprod : ∀ t : ι → Fˣ, ∏ i, t i = t z * ∏ i : {i // i ≠ z}, t i := fun t => by
    rw [← Finset.mul_prod_erase Finset.univ t (Finset.mem_univ z)]
    congr 1
    exact Finset.prod_subtype _ (fun x => by simp) t
  have hc : Coords p Bs κ' := {
    mul := fun a ha b hb => funext fun i => by simp only [hκ', h.mul a ha b hb, Pi.mul_apply]
    inj := fun a ha b hb hab => by
      apply h.inj a ha b hb
      funext i
      by_cases hi : i = z
      · rw [hi]
        have h1 := h.prod a ha
        have h2 := h.prod b hb
        rw [hprod] at h1 h2
        have h3 : ∏ j : {i // i ≠ z}, κ a j = ∏ j : {i // i ≠ z}, κ b j :=
          Finset.prod_congr rfl fun j _ => congrFun hab j
        rw [h3] at h1
        exact mul_right_cancel (h1.trans h2.symm)
      · exact congrFun hab ⟨i, hi⟩
    surj := fun t ht => by
      set t₀ : ι → Fˣ := fun i => if hi : i = z then (∏ j : {i // i ≠ z}, t j)⁻¹ else t ⟨i, hi⟩
        with ht₀
      have ht₀z : t₀ z = (∏ j : {i // i ≠ z}, t j)⁻¹ := by rw [ht₀]; exact dite_eq_left rfl
      have ht₀ne : ∀ j : {i // i ≠ z}, t₀ j = t j := fun j => by
        rw [ht₀]
        exact dite_eq_right j.2
      obtain ⟨b, hb, hbt⟩ := h.surj t₀ (fun i => by
          by_cases hi : i = z
          · rw [hi, ht₀z, inv_pow, ← Finset.prod_pow, Finset.prod_eq_one fun j _ => ht j,
              inv_one]
          · rw [show t₀ i = t ⟨i, hi⟩ from ht₀ne ⟨i, hi⟩]
            exact ht _)
        (by
          rw [hprod, ht₀z, Finset.prod_congr rfl fun j _ => ht₀ne j, inv_mul_cancel])
      refine ⟨b, hb, funext fun j => ?_⟩
      simp only [hκ', hbt, ht₀ne j] }
  refine card_mul_lt_of_coords hp hp2 hζ hc hBs hE hEN (fun e he => ?_) hEC
  have hTe : ∀ x, T ⟨e, he⟩ x ≠ z ↔ x ≠ z := fun x => by
    constructor
    · intro h1 h2
      exact h1 (by rw [h2, hTz])
    · intro h1 h2
      exact h1 ((T ⟨e, he⟩).injective (h2.trans (hTz _).symm))
  refine ⟨(T ⟨e, he⟩).subtypePerm hTe, fun b hb i => ?_⟩
  simp only [hκ', Equiv.Perm.subtypePerm_apply]
  exact hT ⟨e, he⟩ b hb i.1

end Main

end NoOffenderClassical

end CFSG.StandardType
