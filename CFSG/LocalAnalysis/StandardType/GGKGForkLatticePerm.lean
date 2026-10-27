module

public import CFSG.LocalAnalysis.StandardType.GGForkJrPumpDefs
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyUElt

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly SpCoord Multiplicative UCoord

private def ggKGPm_projFun (p : ℕ) {d : ℕ} (f : Fin d → Multiplicative (ZMod p)) :
    Fin d → Multiplicative (ZMod p) :=
  fun i => ofAdd (toAdd (f i) - (∑ j, toAdd (f j)) * (d : ZMod p)⁻¹)

private theorem ggKGPm_projFun_mem {p d : ℕ} (hp : p.Prime) (hpd : ¬ p ∣ d)
    (f : Fin d → Multiplicative (ZMod p)) : ggKGPm_projFun p f ∈ sumZero d p := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hd0 : (d : ZMod p) ≠ 0 := fun h => hpd ((ZMod.natCast_eq_zero_iff d p).mp h)
  rw [mem_sumZero]
  have hsplit : ∑ i, toAdd (ggKGPm_projFun p f i)
      = ∑ i, (toAdd (f i) - (∑ j, toAdd (f j)) * (d : ZMod p)⁻¹) := rfl
  rw [hsplit]
  have hsum : ∑ i, (toAdd (f i) - (∑ j, toAdd (f j)) * (d : ZMod p)⁻¹)
      = (∑ i, toAdd (f i)) - (d : ZMod p) * ((∑ j, toAdd (f j)) * (d : ZMod p)⁻¹) := by
    calc ∑ i, (toAdd (f i) - (∑ j, toAdd (f j)) * (d : ZMod p)⁻¹)
        = (∑ i, (fun i => toAdd (f i)) i)
          - ∑ i, ((fun _ => (∑ j, toAdd (f j)) * (d : ZMod p)⁻¹) i) :=
          Finset.sum_sub_distrib (s := Finset.univ) (f := fun i => toAdd (f i))
            (g := fun _ => (∑ j, toAdd (f j)) * (d : ZMod p)⁻¹)
      _ = (∑ i, toAdd (f i)) - (d : ZMod p) * ((∑ j, toAdd (f j)) * (d : ZMod p)⁻¹) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [hsum]
  have hcancel : (d : ZMod p) * ((∑ j, toAdd (f j)) * (d : ZMod p)⁻¹) = ∑ j, toAdd (f j) := by
    rw [mul_comm (∑ j, toAdd (f j)) (d : ZMod p)⁻¹, ← mul_assoc, mul_inv_cancel₀ hd0, one_mul]
  rw [hcancel, sub_self]

private def ggKGPm_P {p d : ℕ} (hp : p.Prime) (hpd : ¬ p ∣ d)
    (f : Fin d → Multiplicative (ZMod p)) : ↥(sumZero d p) :=
  ⟨ggKGPm_projFun p f, ggKGPm_projFun_mem hp hpd f⟩

private theorem ggKGPm_P_one {p d : ℕ} (hp : p.Prime) (hpd : ¬ p ∣ d) :
    ggKGPm_P hp hpd (1 : Fin d → Multiplicative (ZMod p)) = 1 := by
  apply Subtype.ext
  funext i
  change ggKGPm_projFun p (1 : Fin d → Multiplicative (ZMod p)) i =
    (1 : Fin d → Multiplicative (ZMod p)) i
  simp only [ggKGPm_projFun, Pi.one_apply, toAdd_one, Finset.sum_const_zero, zero_mul,
    sub_zero, ofAdd_zero]

private theorem ggKGPm_P_mul {p d : ℕ} (hp : p.Prime) (hpd : ¬ p ∣ d)
    (f g : Fin d → Multiplicative (ZMod p)) :
    ggKGPm_P hp hpd (f * g) = ggKGPm_P hp hpd f * ggKGPm_P hp hpd g := by
  apply Subtype.ext
  funext i
  change ggKGPm_projFun p (f * g) i = (ggKGPm_projFun p f * ggKGPm_projFun p g) i
  simp only [ggKGPm_projFun, Pi.mul_apply, toAdd_mul, Finset.sum_add_distrib]
  rw [← ofAdd_add]
  congr 1
  ring

private theorem ggKGPm_P_id {p d : ℕ} (hp : p.Prime) (hpd : ¬ p ∣ d) {f : ↥(sumZero d p)} :
    ggKGPm_P hp hpd (f : Fin d → Multiplicative (ZMod p)) = f := by
  apply Subtype.ext
  funext i
  change ggKGPm_projFun p (f : Fin d → Multiplicative (ZMod p)) i =
    (f : Fin d → Multiplicative (ZMod p)) i
  simp only [ggKGPm_projFun]
  rw [show ∑ j, toAdd ((f : Fin d → Multiplicative (ZMod p)) j) = 0 from f.2]
  simp

private theorem ggKGPm_P_perm {p d : ℕ} (hp : p.Prime) (hpd : ¬ p ∣ d)
    (σ : Equiv.Perm (Fin d)) (f : Fin d → Multiplicative (ZMod p)) :
    ggKGPm_P hp hpd (permAut σ f) = permAutV σ (ggKGPm_P hp hpd f) := by
  apply Subtype.ext
  funext i
  change ggKGPm_projFun p (permAut σ f) i = ggKGPm_projFun p f (σ⁻¹ i)
  simp only [ggKGPm_projFun, permAut_apply, Function.comp_apply]
  rw [Equiv.sum_comp σ⁻¹ (fun j => toAdd (f j))]

private def ggKGPm_red (p : ℕ) {d : ℕ} (y : Fin d → ℤ) : Fin d → Multiplicative (ZMod p) :=
  fun i => ofAdd ((y i : ZMod p))

private theorem ggKGPm_red_add {p d : ℕ} (y z : Fin d → ℤ) :
    ggKGPm_red p (y + z) = ggKGPm_red p y * ggKGPm_red p z := by
  funext i
  simp only [ggKGPm_red, Pi.add_apply, Pi.mul_apply, Int.cast_add, ofAdd_add]

private theorem ggKGPm_red_zero {p d : ℕ} :
    ggKGPm_red p (0 : Fin d → ℤ) = 1 := by
  funext i
  simp only [ggKGPm_red, Pi.zero_apply, Int.cast_zero, ofAdd_zero, Pi.one_apply]

private def ggKGPm_pi {p d : ℕ} {L' : Type} [Group L'] {A : Subgroup (MulAut L')}
    (hp : p.Prime) (hpd : ¬ p ∣ d) (Θ : ↥(sumZero d p) ≃* ↥A) :
    (Fin d → ℤ) →+ Additive ↥A where
  toFun y := Additive.ofMul (Θ (ggKGPm_P hp hpd (ggKGPm_red p y)))
  map_zero' := by
    show Additive.ofMul (Θ (ggKGPm_P hp hpd (ggKGPm_red p 0))) = 0
    rw [ggKGPm_red_zero, ggKGPm_P_one, map_one, ofMul_one]
  map_add' y z := by
    show Additive.ofMul (Θ (ggKGPm_P hp hpd (ggKGPm_red p (y + z)))) =
      Additive.ofMul (Θ (ggKGPm_P hp hpd (ggKGPm_red p y))) +
      Additive.ofMul (Θ (ggKGPm_P hp hpd (ggKGPm_red p z)))
    rw [ggKGPm_red_add, ggKGPm_P_mul, map_mul, ofMul_mul]

private theorem ggKGPm_pi_surjective {p d : ℕ} {L' : Type} [Group L'] {A : Subgroup (MulAut L')}
    (hp : p.Prime) (hpd : ¬ p ∣ d) (Θ : ↥(sumZero d p) ≃* ↥A) :
    Function.Surjective (ggKGPm_pi hp hpd Θ) := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  intro a
  refine ⟨fun i => ((crd (Θ.symm (Additive.toMul a)) i).val : ℤ), ?_⟩
  have hy : ggKGPm_red p (fun i => ((crd (Θ.symm (Additive.toMul a)) i).val : ℤ)) =
      (Θ.symm (Additive.toMul a) : Fin d → Multiplicative (ZMod p)) := by
    funext i
    simp only [ggKGPm_red, crd]
    rw [Int.cast_natCast, ZMod.natCast_zmod_val, ofAdd_toAdd]
  have hP : ggKGPm_P hp hpd
      (ggKGPm_red p (fun i => ((crd (Θ.symm (Additive.toMul a)) i).val : ℤ))) =
      Θ.symm (Additive.toMul a) := by
    rw [hy, ggKGPm_P_id]
  change Additive.ofMul (Θ (ggKGPm_P hp hpd
    (ggKGPm_red p (fun i => ((crd (Θ.symm (Additive.toMul a)) i).val : ℤ))))) = a
  rw [hP, MulEquiv.apply_symm_apply]
  rfl

private theorem ggKGPm_latForm_one (d : ℕ) :
    GGLatForm (1 : Matrix (Fin d) (Fin d) ℤ) := by
  refine ⟨Matrix.transpose_one, fun y hy => ?_⟩
  rw [Matrix.one_mulVec]
  have hnn : 0 ≤ dotProduct y y := by
    rw [dotProduct]
    exact Finset.sum_nonneg fun i _ => mul_self_nonneg (y i)
  have hne : dotProduct y y ≠ 0 := fun h => hy (dotProduct_self_eq_zero.mp h)
  exact lt_of_le_of_ne hnn hne.symm

private def ggKGPm_w {d : ℕ} (i j : Fin d) : Fin d → ℤ :=
  Pi.single i (1 : ℤ) - Pi.single j (1 : ℤ)

private theorem ggKGPm_dot_y_w {d : ℕ} (i j : Fin d) (y : Fin d → ℤ) :
    dotProduct y (ggKGPm_w i j) = y i - y j := by
  simp only [ggKGPm_w, dotProduct_sub, dotProduct_single, mul_one]

private theorem ggKGPm_dot_w_w {d : ℕ} {i j : Fin d} (hij : i ≠ j) :
    dotProduct (ggKGPm_w i j) (ggKGPm_w i j) = 2 := by
  simp only [ggKGPm_w, sub_dotProduct, dotProduct_sub, single_dotProduct, Pi.single_apply,
    if_true, if_neg hij, if_neg (Ne.symm hij)]
  norm_num

private theorem ggKGPm_cartan {d : ℕ} {i j : Fin d} (hij : i ≠ j) (y : Fin d → ℤ) :
    ggLatCartan (1 : Matrix (Fin d) (Fin d) ℤ) y (ggKGPm_w i j) = y i - y j := by
  rw [ggLatCartan, Matrix.one_mulVec, ggKGPm_dot_y_w, ggKGPm_dot_w_w hij,
    Int.mul_ediv_cancel_left (y i - y j) (by norm_num : (2 : ℤ) ≠ 0)]

private theorem ggKGPm_refl {d : ℕ} {i j : Fin d} (hij : i ≠ j) (y : Fin d → ℤ) :
    ggLatRefl (1 : Matrix (Fin d) (Fin d) ℤ) (ggKGPm_w i j) y =
      fun k => y (Equiv.swap i j k) := by
  funext k
  rw [ggLatRefl, ggKGPm_cartan hij]
  simp only [ggKGPm_w, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  by_cases hki : k = i
  · subst hki
    simp [Pi.single_eq_same, Pi.single_eq_of_ne, hij, Ne.symm hij, Equiv.swap_apply_left]
  · by_cases hkj : k = j
    · subst hkj
      simp [Pi.single_eq_same, Pi.single_eq_of_ne, hij, Ne.symm hij, Equiv.swap_apply_right]
    · simp [Pi.single_eq_of_ne, hki, hkj, Equiv.swap_apply_of_ne_of_ne hki hkj]

private theorem ggKGPm_root {d : ℕ} {i j : Fin d} (hij : i ≠ j) :
    GGLatRoot (1 : Matrix (Fin d) (Fin d) ℤ) (ggKGPm_w i j) := by
  refine ⟨?_, ?_⟩
  · intro h
    have h1 : ggKGPm_w i j i = 1 := by simp [ggKGPm_w, hij]
    have h2 : ggKGPm_w i j i = 0 := by rw [h]; rfl
    rw [h1] at h2
    exact one_ne_zero h2
  · intro y
    rw [Matrix.one_mulVec, ggKGPm_dot_w_w hij]
    exact dvd_mul_right 2 (dotProduct y (ggKGPm_w i j))

private theorem ggKGPm_red_swap {p d : ℕ} (i j : Fin d) (y : Fin d → ℤ) :
    ggKGPm_red p (fun k => y (Equiv.swap i j k)) = permAut (Equiv.swap i j) (ggKGPm_red p y) := by
  funext k
  simp only [ggKGPm_red, permAut_apply, Function.comp_apply, Equiv.swap_inv]

private theorem ggKGPm_card_sumZero_le (m p : ℕ) [NeZero p] :
    Nat.card ↥(sumZero (m + 1) p) ≤ p ^ m := by
  let F : ↥(sumZero (m + 1) p) → (Fin m → Multiplicative (ZMod p)) :=
    fun f i => (f : Fin (m + 1) → Multiplicative (ZMod p)) (Fin.castSucc i)
  have hF : Function.Injective F := by
    intro f g hfg
    have hi : ∀ i : Fin m, crd f (Fin.castSucc i) = crd g (Fin.castSucc i) := fun i =>
      congrArg Multiplicative.toAdd (congrFun hfg i)
    refine ext_crd fun k => ?_
    induction k using Fin.lastCases with
    | last =>
      have hf := sum_crd f
      have hg := sum_crd g
      rw [Fin.sum_univ_castSucc] at hf hg
      simp only [hi] at hf
      exact add_left_cancel (hf.trans hg.symm)
    | cast i => exact hi i
  calc Nat.card ↥(sumZero (m + 1) p) ≤ Nat.card (Fin m → Multiplicative (ZMod p)) :=
        Nat.card_le_card_of_injective F hF
    _ = p ^ m := by
        rw [Nat.card_fun, Nat.card_fin]
        congr 1
        exact Nat.card_zmod p

private theorem ggKGPm_four_le_d {p d : ℕ} {L' : Type} [Group L'] {A : Subgroup (MulAut L')}
    (hp : p.Prime) (hpd : ¬ p ∣ d) (h3 : p ^ 3 ≤ Nat.card ↥A)
    (Θ : ↥(sumZero d p) ≃* ↥A) : 4 ≤ d := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hcard : p ^ 3 ≤ Nat.card ↥(sumZero d p) := by
    rw [Nat.card_congr Θ.toEquiv]; exact h3
  have hdpos : 0 < d := by
    rcases Nat.eq_zero_or_pos d with h | h
    · exact absurd (h ▸ dvd_zero p) hpd
    · exact h
  obtain ⟨m, rfl⟩ : ∃ m, d = m + 1 := ⟨d - 1, by omega⟩
  have hle := ggKGPm_card_sumZero_le m p
  have hm : 3 ≤ m := (Nat.pow_le_pow_iff_right hp.one_lt).mp (hcard.trans hle)
  omega

private theorem ggKGPm_congr_symm_congr {M N : Type*} [Group M] [Group N] (e : M ≃* N)
    (f : MulAut M) : MulAut.congr e.symm (MulAut.congr e f) = f := by
  ext x
  simp

theorem ggTorusLattice_of_permModel {p d : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpd : ¬ p ∣ d)
    {L' : Type} [Group L'] {A : Subgroup (MulAut L')} (h3 : p ^ 3 ≤ Nat.card ↥A)
    (Θ : ↥(sumZero d p) ≃* ↥A)
    (hS : ∀ (n : L') (hn : MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut L'))),
      ∃ π : Equiv.Perm (Fin d), ggConjAut A hn = MulAut.congr Θ (permAutV π)) :
    ∃ (m : ℕ) (Q : Matrix (Fin m) (Fin m) ℤ) (π : (Fin m → ℤ) →+ Additive ↥A),
      GGLatForm Q ∧ Function.Surjective π ∧
      ∀ φ ∈ ggAutomizer (MulAut.conj : L' →* MulAut L').range A, GGIsReflection p φ →
        ∃ w : Fin m → ℤ, GGLatRoot Q w ∧ ∀ y : Fin m → ℤ,
          φ (Additive.toMul (π y)) = Additive.toMul (π (ggLatRefl Q w y)) := by
  have hd4 : 4 ≤ d := ggKGPm_four_le_d hp hpd h3 Θ
  refine ⟨d, 1, ggKGPm_pi hp hpd Θ, ggKGPm_latForm_one d, ggKGPm_pi_surjective hp hpd Θ, ?_⟩
  intro φ hφmem hφrefl
  rw [mem_ggAutomizer_iff] at hφmem
  obtain ⟨g, hgH, hgnorm, hgapply⟩ := hφmem
  obtain ⟨n, rfl⟩ := hgH
  obtain ⟨π₀, hπ₀⟩ := hS n hgnorm
  have hφeq : φ = MulAut.congr Θ (permAutV π₀) := by
    rw [← hπ₀]
    refine MulEquiv.ext fun b => Subtype.ext ?_
    rw [hgapply b, ggConjAut_apply]
  have hps : GGIsPseudoReflection p (permAutV π₀ : MulAut ↥(sumZero d p)) := by
    have h1 : GGIsPseudoReflection p φ :=
      GGIsReflection.isPseudoReflection (hp.odd_of_ne_two hp2) hφrefl
    rw [hφeq] at h1
    have h2 := GGIsPseudoReflection.congr (e := Θ.symm) h1
    rwa [ggKGPm_congr_symm_congr] at h2
  obtain ⟨i, j, hij, hπ₀eq⟩ := isSwap_of_isPseudoReflection hp hp2 hd4 hps
  refine ⟨ggKGPm_w i j, ggKGPm_root hij, fun y => ?_⟩
  have hkey : ggKGPm_P hp hpd (ggKGPm_red p (ggLatRefl (1 : Matrix (Fin d) (Fin d) ℤ)
        (ggKGPm_w i j) y))
      = permAutV (Equiv.swap i j) (ggKGPm_P hp hpd (ggKGPm_red p y)) := by
    rw [ggKGPm_refl hij y, ggKGPm_red_swap i j y,
      ggKGPm_P_perm hp hpd (Equiv.swap i j) (ggKGPm_red p y)]
  change φ (Θ (ggKGPm_P hp hpd (ggKGPm_red p y))) =
    Θ (ggKGPm_P hp hpd (ggKGPm_red p (ggLatRefl (1 : Matrix (Fin d) (Fin d) ℤ)
      (ggKGPm_w i j) y)))
  have hφ' : φ = MulAut.congr Θ (permAutV (Equiv.swap i j)) := by rw [hφeq, hπ₀eq]
  rw [hφ']
  simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply, hkey]

end CFSG.StandardType
