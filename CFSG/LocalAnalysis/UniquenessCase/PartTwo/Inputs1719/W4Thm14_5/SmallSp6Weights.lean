module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.SmallSp6Count
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.SmallSp6Smith
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotRecognizeSwap

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5

open CFSG.LieType.Universal.Symplectic CFSG.LieType.Universal.Symplectic.SpExtras CFSG.Open
  CFSG.ClassicalInvolution.Models.SymplecticPairs CFSG.Quasithin.SmithCurtis Module

section Characters

variable {K : Type} [Field K] [Fintype K] {k : Type*} [Field k]

theorem exists_units_ne_one' (hK : 3 ≤ Fintype.card K) : ∃ a : Kˣ, a ≠ 1 := by
  classical
  have h : 1 < Fintype.card Kˣ := by
    rw [Fintype.card_units]
    omega
  exact Fintype.exists_ne_of_one_lt_card h 1

theorem exists_ringHom_ne_one (hK : 3 ≤ Fintype.card K) (φ : K →+* k) :
    ∃ a : Kˣ, φ a ≠ 1 := by
  obtain ⟨a, ha⟩ := exists_units_ne_one' hK
  exact ⟨a, fun h => ha (Units.ext (φ.injective (h.trans (map_one φ).symm)))⟩

variable [CharP k 2]

theorem exists_ringHom_mul_ne_one [CharP K 2] (hK : 5 ≤ Fintype.card K) (φ φ' : K →+* k) :
    ∃ a : Kˣ, φ a * φ' a ≠ 1 := by
  classical
  by_contra hcon
  push Not at hcon
  have hroot : ∀ c : K, c ≠ 0 → c ≠ 1 → φ c * φ c + φ c + 1 = 0 := by
    intro c hc0 hc1
    have hc1' : c + 1 ≠ 0 := fun h => hc1 (by
      have : c = -1 := eq_neg_of_add_eq_zero_left h
      rwa [CharTwo.neg_eq] at this)
    have h1 := hcon (Units.mk0 c hc0)
    have h2 := hcon (Units.mk0 (c + 1) hc1')
    simp only [Units.val_mk0, map_add, map_one] at h1 h2
    have h3 : φ c + φ' c = 1 := by linear_combination h2 - h1 - CharTwo.two_eq_zero (R := k)
    linear_combination -h1 + φ c * h3 + φ c * CharTwo.two_eq_zero (R := k)
  have hpair : ∀ x y : k, x * x + x + 1 = 0 → y * y + y + 1 = 0 → x ≠ y → y = x + 1 := by
    intro x y hx hy hxy
    have h : (x - y) * (x + y + 1) = 0 := by linear_combination hx - hy
    have h' : x + y + 1 = 0 := (mul_eq_zero.mp h).resolve_left (sub_ne_zero.mpr hxy)
    linear_combination h' - (x + 1) * CharTwo.two_eq_zero (R := k)
  have hcard : 2 < ((Finset.univ.erase (0 : K)).erase 1).card := by
    rw [Finset.card_erase_of_mem (by simp), Finset.card_erase_of_mem (Finset.mem_univ _),
      Finset.card_univ]
    omega
  obtain ⟨c₁, c₂, c₃, h₁, h₂, h₃, h12, h13, h23⟩ := Finset.two_lt_card_iff.mp hcard
  simp only [Finset.mem_erase, Finset.mem_univ, and_true] at h₁ h₂ h₃
  have e2 := hpair _ _ (hroot c₁ h₁.2 h₁.1) (hroot c₂ h₂.2 h₂.1) (fun h => h12 (φ.injective h))
  have e3 := hpair _ _ (hroot c₁ h₁.2 h₁.1) (hroot c₃ h₃.2 h₃.1) (fun h => h13 (φ.injective h))
  exact h23 (φ.injective (e2.trans e3.symm))

theorem exists_ringHom_mul_sq_ne_one [CharP K 2] (hK : 5 ≤ Fintype.card K) (φ φ' : K →+* k) :
    ∃ a : Kˣ, φ a * φ' a ^ 2 ≠ 1 := by
  obtain ⟨a, ha⟩ := exists_ringHom_mul_ne_one hK φ (φ'.comp (frobenius K 2))
  refine ⟨a, ?_⟩
  simpa [frobenius_def, map_pow] using ha

theorem ne_of_mul_eq_one_charTwo {x y : k} (hx : x ≠ 1) (hxy : x * y = 1) : x ≠ y := by
  rintro rfl
  exact hx (eq_one_of_sq_eq_one_charTwo (by rw [sq, hxy]))

end Characters

section Weyl

variable {n : ℕ} {K : Type} [Field K]

theorem sw_inv_conj_diagHom {i j : Fin n} (hij : i ≠ j) (t : Fin n → Kˣ) :
    (sw hij)⁻¹ * diagHom n K t * sw hij = diagHom n K (t ∘ Equiv.swap i j) := by
  have h := sw_conj_diagHom (F := K) hij (t ∘ Equiv.swap i j)
  have e : (t ∘ Equiv.swap i j) ∘ Equiv.swap i j = t := by
    funext x
    simp [Equiv.swap_apply_self]
  rw [e] at h
  rw [← h]
  group

theorem lw_inv_conj_diagHom (c : Fin n) (t : Fin n → Kˣ) :
    (lw c)⁻¹ * diagHom n K t * lw c = diagHom n K (Function.update t c (t c)⁻¹) := by
  have h := lw_conj_diagHom (F := K) c (Function.update t c (t c)⁻¹)
  have e : Function.update (Function.update t c (t c)⁻¹) c
      ((Function.update t c (t c)⁻¹) c)⁻¹ = t := by
    rw [Function.update_self, inv_inv, Function.update_idem, Function.update_eq_self]
  rw [e] at h
  rw [← h]
  group

theorem mulSingle_comp_swap [DecidableEq (Fin n)] (i j c : Fin n) (a : Kˣ) :
    (Pi.mulSingle c a : Fin n → Kˣ) ∘ Equiv.swap i j = Pi.mulSingle (Equiv.swap i j c) a := by
  funext x
  simp only [Function.comp_apply, Pi.mulSingle_apply, Equiv.swap_apply_eq_iff]

theorem update_mulSingle_self [DecidableEq (Fin n)] (c : Fin n) (a : Kˣ) :
    Function.update (Pi.mulSingle c a : Fin n → Kˣ) c ((Pi.mulSingle c a : Fin n → Kˣ) c)⁻¹ =
      Pi.mulSingle c a⁻¹ := by
  rw [Pi.mulSingle_eq_same, Pi.mulSingle, Function.update_idem]
  rfl

theorem update_mulSingle_of_ne [DecidableEq (Fin n)] {c d : Fin n} (h : c ≠ d) (a : Kˣ) :
    Function.update (Pi.mulSingle c a : Fin n → Kˣ) d ((Pi.mulSingle c a : Fin n → Kˣ) d)⁻¹ =
      Pi.mulSingle c a := by
  have e : ((Pi.mulSingle c a : Fin n → Kˣ) d)⁻¹ = (Pi.mulSingle c a : Fin n → Kˣ) d := by
    rw [Pi.mulSingle_eq_of_ne h.symm, inv_one]
  rw [e, Function.update_eq_self]

theorem diagHom_mulSingle_succ (c : Fin 2) (a : Kˣ) :
    diagHom 3 K (Pi.mulSingle c.succ a) =
      spEmbed Fin.succ (Fin.succ_injective 2) (diagHom 2 K (Pi.mulSingle c a)) := by
  rw [← diagHom_cons_one]
  congr 1
  funext x
  refine Fin.cases ?_ (fun x => ?_) x
  · simp [Fin.succ_ne_zero]
  · simp [Pi.mulSingle_apply, Fin.succ_inj]

end Weyl

section Weights

variable {K : Type} [Field K] [Fintype K] [CharP K 2]
  {k V : Type*} [Field k] [CharP k 2] [AddCommGroup V] [Module k V]
  {ρ : Representation k (StatedSp 3 K) V} {y₀ : V} {χ : StatedSp 3 K → k} {μ : Fin 3 → k}

@[expose] noncomputable def epsChar (χ : StatedSp 3 K → k) (c : Fin 3) (a : Kˣ) : k :=
  χ (diagHom 3 K (Pi.mulSingle c a))

omit [CharP k 2] in
theorem rep_diagHom_y₀ (ht : (spCurtisDatum 3 K).IsCurtisType ρ y₀ χ μ) (t : Fin 3 → Kˣ) :
    ρ (diagHom 3 K t) y₀ = χ (diagHom 3 K t) • y₀ :=
  ht.2.2.1 _ (diagHom_mem_H_three t)

omit [CharP k 2] in
theorem chi_diagHom_mul (ht : (spCurtisDatum 3 K).IsCurtisType ρ y₀ χ μ) (t t' : Fin 3 → Kˣ) :
    χ (diagHom 3 K (t * t')) = χ (diagHom 3 K t) * χ (diagHom 3 K t') := by
  apply smul_left_injective k ht.2.1
  change χ (diagHom 3 K (t * t')) • y₀ = (χ (diagHom 3 K t) * χ (diagHom 3 K t')) • y₀
  rw [← rep_diagHom_y₀ ht, map_mul, map_mul, Module.End.mul_apply, rep_diagHom_y₀ ht t',
    map_smul, rep_diagHom_y₀ ht t, smul_smul, mul_comm]

omit [CharP k 2] in
theorem chi_diagHom_one (ht : (spCurtisDatum 3 K).IsCurtisType ρ y₀ χ μ) :
    χ (diagHom 3 K 1) = 1 := by
  apply smul_left_injective k ht.2.1
  change χ (diagHom 3 K 1) • y₀ = (1 : k) • y₀
  rw [← rep_diagHom_y₀ ht, map_one, map_one, Module.End.one_apply, one_smul]

omit [CharP k 2] in
theorem epsChar_mul (ht : (spCurtisDatum 3 K).IsCurtisType ρ y₀ χ μ) (c : Fin 3) (a b : Kˣ) :
    epsChar χ c (a * b) = epsChar χ c a * epsChar χ c b := by
  rw [epsChar, Pi.mulSingle_mul, chi_diagHom_mul ht]
  rfl

omit [CharP k 2] in
theorem epsChar_one (ht : (spCurtisDatum 3 K).IsCurtisType ρ y₀ χ μ) (c : Fin 3) :
    epsChar χ c 1 = 1 := by
  rw [epsChar, Pi.mulSingle_one, chi_diagHom_one ht]

omit [CharP k 2] in
theorem epsChar_mul_inv (ht : (spCurtisDatum 3 K).IsCurtisType ρ y₀ χ μ) (c : Fin 3) (a : Kˣ) :
    epsChar χ c a * epsChar χ c a⁻¹ = 1 := by
  rw [← epsChar_mul ht, mul_inv_cancel, epsChar_one ht]

omit [CharP k 2] in
theorem epsChar_inv (ht : (spCurtisDatum 3 K).IsCurtisType ρ y₀ χ μ) (c : Fin 3) (a : Kˣ) :
    epsChar χ c a⁻¹ = (epsChar χ c a)⁻¹ :=
  (eq_inv_of_mul_eq_one_right (epsChar_mul_inv ht c a))

omit [CharP k 2] in
theorem chi_diagHom_eq (ht : (spCurtisDatum 3 K).IsCurtisType ρ y₀ χ μ) (t : Fin 3 → Kˣ) :
    χ (diagHom 3 K t) = epsChar χ 0 (t 0) * epsChar χ 1 (t 1) * epsChar χ 2 (t 2) := by
  have e : t = Pi.mulSingle 0 (t 0) * Pi.mulSingle 1 (t 1) * Pi.mulSingle 2 (t 2) := by
    funext x
    fin_cases x <;> simp
  conv_lhs => rw [e]
  rw [chi_diagHom_mul ht, chi_diagHom_mul ht]
  rfl

omit [CharP k 2] in
theorem chi_corootSp_two (ht : (spCurtisDatum 3 K).IsCurtisType ρ y₀ χ μ) (a : Kˣ) :
    χ (corootSp 2 a) = epsChar χ 2 a := by
  rw [corootSp_apply, chi_diagHom_eq ht]
  simp [corootVec, epsChar_one ht]

omit [CharP k 2] in
theorem chi_corootSp_one (ht : (spCurtisDatum 3 K).IsCurtisType ρ y₀ χ μ) (a : Kˣ) :
    χ (corootSp 1 a) = epsChar χ 1 a * (epsChar χ 2 a)⁻¹ := by
  rw [corootSp_apply, chi_diagHom_eq ht]
  simp [corootVec, epsChar_one ht, epsChar_inv ht]

omit [CharP k 2] in
theorem chi_corootSp_zero (ht : (spCurtisDatum 3 K).IsCurtisType ρ y₀ χ μ) (a : Kˣ) :
    χ (corootSp 0 a) = epsChar χ 0 a * (epsChar χ 1 a)⁻¹ := by
  rw [corootSp_apply, chi_diagHom_eq ht]
  simp [corootVec, epsChar_one ht, epsChar_inv ht]

omit [CharP k 2] in
theorem epsChar_ne_zero (ht : (spCurtisDatum 3 K).IsCurtisType ρ y₀ χ μ) (c : Fin 3) (a : Kˣ) :
    epsChar χ c a ≠ 0 :=
  left_ne_zero_of_mul_eq_one (epsChar_mul_inv ht c a)

omit [CharP k 2] in
theorem rep_diagHom_weyl (ht : (spCurtisDatum 3 K).IsCurtisType ρ y₀ χ μ) {n : StatedSp 3 K}
    {π : (Fin 3 → Kˣ) → (Fin 3 → Kˣ)} (hπ : ∀ t, n⁻¹ * diagHom 3 K t * n = diagHom 3 K (π t))
    (t : Fin 3 → Kˣ) : ρ (diagHom 3 K t) (ρ n y₀) = χ (diagHom 3 K (π t)) • ρ n y₀ := by
  rw [← Module.End.mul_apply, ← map_mul,
    show diagHom 3 K t * n = n * (n⁻¹ * diagHom 3 K t * n) by group, hπ, map_mul,
    Module.End.mul_apply, rep_diagHom_y₀ ht, map_smul]

omit [CharP k 2] in
theorem rep_ne_zero (ht : (spCurtisDatum 3 K).IsCurtisType ρ y₀ χ μ) (n : StatedSp 3 K) :
    ρ n y₀ ≠ 0 := by
  intro h
  apply ht.2.1
  have := congrArg (ρ n⁻¹) h
  rwa [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply,
    map_zero] at this

omit [CharP k 2] in
theorem le_finrank_of_weyl (hK : 4 ≤ Fintype.card K) [FiniteDimensional k V]
    (ht : (spCurtisDatum 3 K).IsCurtisType ρ y₀ χ μ) {z : StatedSp 2 K} (hz : z ≠ 1) {m : ℕ}
    (n : Fin m → StatedSp 3 K) (π : Fin m → (Fin 3 → Kˣ) → (Fin 3 → Kˣ))
    (hπ : ∀ j t, (n j)⁻¹ * diagHom 3 K t * n j = diagHom 3 K (π j t))
    (hb : Function.Injective fun j (a : Kˣ) => χ (diagHom 3 K (π j (Pi.mulSingle 0 a))))
    (hmove : ∀ j, ∃ (c : Fin 2) (a : Kˣ), χ (diagHom 3 K (π j (Pi.mulSingle c.succ a))) ≠ 1) :
    m ≤ finrank k (LinearMap.range (ρ (spEmbed Fin.succ (Fin.succ_injective 2) z) - 1)) := by
  have : IsSimpleGroup (StatedSp 2 K) :=
    CFSG.SeitzReduction.SymplecticPilot.isSimpleGroup_statedSp_of_four_le
      (by rwa [Nat.card_eq_fintype_card]) (by norm_num)
  refine card_le_finrank_range_sub_one ρ (spEmbed Fin.succ (Fin.succ_injective 2))
    (fun a : Kˣ => diagHom 3 K (Pi.mulSingle 0 a))
    (fun a g => diagHom_mulSingle_commute_spEmbed a g) hz _ hb (fun j => ρ (n j) y₀)
    (fun j a => rep_diagHom_weyl ht (hπ j) _) (fun j => ?_)
  obtain ⟨c, a, hca⟩ := hmove j
  refine ⟨diagHom 2 K (Pi.mulSingle c a), fun h => hca ?_⟩
  rw [← diagHom_mulSingle_succ, rep_diagHom_weyl ht (hπ j)] at h
  have h' : (χ (diagHom 3 K (π j (Pi.mulSingle c.succ a))) - 1) • ρ (n j) y₀ = 0 := by
    rw [sub_smul, h, one_smul, sub_self]
  exact sub_eq_zero.mp ((smul_eq_zero.mp h').resolve_right (rep_ne_zero ht (n j)))

end Weights

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5
