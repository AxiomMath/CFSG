module

public import CFSG.Quasithin.Background.SmithB45L2Inner
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7Basic
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesFour
public import CFSG.Quasithin.Background.Harris.L2.Numerics
public import CFSG.Timmesfeld.Bridge.RootStructR2HigmanIrr

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Quasithin.B45L2 CFSG.Quasithin.G11.Harris.L2 CFSG.Timmesfeld.Bridge.Higman
open CFSG.ProperTwoGeneratedCore.LocalCriterionSquareField
open CFSG.QuasithinUnique.Setup.SL2Modules CFSG.QuasithinUnique.Setup.X7
open scoped MatrixGroups

section DegeneratePair

variable {F : Type*} [Field F] {k : Type*} [Field k] [Algebra F k] [CharP k 2]

theorem eq_zero_of_fixed_degenerate_pair (e : I3 → ℕ) {t₁ t₂ : F} (ht₁ : t₁ ≠ 0) {κ : k}
    (hκ0 : κ ≠ 0) (hκ1 : κ ≠ 1)
    (hκ : ∀ i : I3, (algebraMap F k t₂) ^ (2 ^ e i) = κ * (algebraMap F k t₁) ^ (2 ^ e i))
    (f : (I3 → Fin 2) → k) (hf₁ : tensorRep F k e (uElt t₁) f = f)
    (hf₂ : tensorRep F k e (uElt t₂) f = f)
    (h000 : f (pt 0 0 0) = 0) (h001 : f (pt 0 0 1) = 0) (h010 : f (pt 0 1 0) = 0) :
    f = 0 := by
  obtain ⟨h111₁, h101₁, h011₁, hfull₁⟩ := fixed_eqs e t₁ f hf₁
  obtain ⟨h111₂, h101₂, h011₂, hfull₂⟩ := fixed_eqs e t₂ f hf₂
  set τ₀ : k := (algebraMap F k t₁) ^ (2 ^ e none) with hτ₀def
  set τ₁ : k := (algebraMap F k t₁) ^ (2 ^ e (some none)) with hτ₁def
  set τ₂ : k := (algebraMap F k t₁) ^ (2 ^ e (some (some none))) with hτ₂def
  have hτ₀ : τ₀ ≠ 0 := by rw [hτ₀def]; exact pow_ne_zero _ ((map_ne_zero (algebraMap F k)).mpr ht₁)
  have hτ₁ : τ₁ ≠ 0 := by rw [hτ₁def]; exact pow_ne_zero _ ((map_ne_zero (algebraMap F k)).mpr ht₁)
  have hτ₂ : τ₂ ≠ 0 := by rw [hτ₂def]; exact pow_ne_zero _ ((map_ne_zero (algebraMap F k)).mpr ht₁)
  have hτ₀' : (algebraMap F k t₂) ^ (2 ^ e none) = κ * τ₀ := by rw [hκ none, hτ₀def]
  have hτ₁' : (algebraMap F k t₂) ^ (2 ^ e (some none)) = κ * τ₁ := by rw [hκ (some none), hτ₁def]
  have hτ₂' : (algebraMap F k t₂) ^ (2 ^ e (some (some none))) = κ * τ₂ := by
    rw [hκ (some (some none)), hτ₂def]
  have h111 : f (pt 1 1 1) = 0 :=
    (mul_eq_zero.mp h111₁).resolve_left hτ₂
  rw [h111, mul_zero, add_zero] at h101₁ h011₁ hfull₁ h101₂ h011₂ hfull₂
  rw [hτ₂', hτ₁'] at h101₂
  rw [hτ₂', hτ₀'] at h011₂
  rw [hτ₂', hτ₁', hτ₀'] at hfull₂
  have hfull₁' : τ₂ * f (pt 0 0 1) + τ₁ * f (pt 0 1 0) + τ₁ * τ₂ * f (pt 0 1 1) +
      τ₀ * f (pt 1 0 0) + τ₀ * τ₂ * f (pt 1 0 1) + τ₀ * τ₁ * f (pt 1 1 0) = 0 := by
    linear_combination hfull₁
  have hfull₂' : κ * (τ₂ * f (pt 0 0 1) + τ₁ * f (pt 0 1 0) + τ₀ * f (pt 1 0 0)) +
      κ ^ 2 * (τ₁ * τ₂ * f (pt 0 1 1) + τ₀ * τ₂ * f (pt 1 0 1) +
        τ₀ * τ₁ * f (pt 1 1 0)) = 0 := by
    linear_combination hfull₂
  set A : k := τ₁ * τ₂ * f (pt 0 1 1) + τ₀ * τ₂ * f (pt 1 0 1) +
    τ₀ * τ₁ * f (pt 1 1 0) with hAdef
  set B : k := τ₂ * f (pt 0 0 1) + τ₁ * f (pt 0 1 0) + τ₀ * f (pt 1 0 0) with hBdef
  have hfull₁'' : (1 : k) * A + 1 * B = 0 := by
    rw [hAdef, hBdef]
    linear_combination hfull₁'
  have hfull₂'' : κ ^ 2 * A + κ * B = 0 := by
    rw [hAdef, hBdef]
    linear_combination hfull₂
  have hκsq : κ ^ 2 ≠ κ := by
    intro h
    have hzero : κ * (1 + κ) = 0 := by
      calc κ * (1 + κ) = κ + κ ^ 2 := by ring
        _ = κ + κ := by rw [h]
        _ = 0 := CharTwo.add_self_eq_zero κ
    rcases mul_eq_zero.mp hzero with h1 | h2
    · exact hκ0 h1
    · exfalso
      apply hκ1
      have h' : κ + 1 = 0 := by simpa [add_comm] using h2
      have : κ = -1 := (eq_neg_iff_add_eq_zero).mpr h'
      rw [this, CharTwo.neg_eq]
  have hdet : (1 : k) * κ ≠ κ ^ 2 * 1 := by
    simpa using hκsq.symm
  obtain ⟨hA, hB⟩ := eq_zero_of_det (α₁ := (1 : k)) (β₁ := 1) (α₂ := κ ^ 2) (β₂ := κ)
    (x := A) (y := B) hdet hfull₁'' hfull₂''
  have h011 : f (pt 0 1 1) = 0 := by
    have h : τ₁ * τ₂ * f (pt 0 1 1) = 0 := by
      rw [hAdef] at hA
      linear_combination hA - τ₀ * h101₁
    exact (mul_eq_zero.mp h).resolve_left (mul_ne_zero hτ₁ hτ₂)
  have h110 : f (pt 1 1 0) = 0 := by
    have h : τ₀ * f (pt 1 1 0) = 0 := by
      linear_combination h011₁ - τ₂ * h011
    exact (mul_eq_zero.mp h).resolve_left hτ₀
  have h101 : f (pt 1 0 1) = 0 := by
    have h : τ₂ * f (pt 1 0 1) = 0 := by
      linear_combination h101₁ - τ₁ * h110
    exact (mul_eq_zero.mp h).resolve_left hτ₂
  have hB' : τ₂ * f (pt 0 0 1) + τ₁ * f (pt 0 1 0) + τ₀ * f (pt 1 0 0) = 0 := by
    rw [← hBdef]; exact hB
  have h100 : f (pt 1 0 0) = 0 := by
    have h : τ₀ * f (pt 1 0 0) = 0 := by
      linear_combination hB' - τ₂ * h001 - τ₁ * h010
    exact (mul_eq_zero.mp h).resolve_left hτ₀
  funext x
  rw [eq_pt x]
  rcases zero_or_one (x none) with a | a <;> rcases zero_or_one (x (some none)) with b | b <;>
    rcases zero_or_one (x (some (some none))) with c | c <;> rw [a, b, c] <;>
    simp [h000, h001, h010, h100, h101, h110, h011, h111]
  where
  zero_or_one (a : Fin 2) : a = 0 ∨ a = 1 := by fin_cases a <;> simp


theorem card_fixed_degenerate_pair_le [Finite k] (e : I3 → ℕ) {t₁ t₂ : F} (ht₁ : t₁ ≠ 0)
    {κ : k} (hκ0 : κ ≠ 0) (hκ1 : κ ≠ 1)
    (hκ : ∀ i : I3, (algebraMap F k t₂) ^ (2 ^ e i) = κ * (algebraMap F k t₁) ^ (2 ^ e i)) :
    Nat.card {f : (I3 → Fin 2) → k //
      tensorRep F k e (uElt t₁) f = f ∧ tensorRep F k e (uElt t₂) f = f} ≤ Nat.card k ^ 3 := by
  let φ : {f : (I3 → Fin 2) → k //
      tensorRep F k e (uElt t₁) f = f ∧ tensorRep F k e (uElt t₂) f = f} → (k × k) × k :=
    fun f => ((f.1 (pt 0 0 0), f.1 (pt 0 0 1)), f.1 (pt 0 1 0))
  have hφ : Function.Injective φ := by
    intro f f' h
    have h1 : f.1 (pt 0 0 0) = f'.1 (pt 0 0 0) := by
      simpa [φ] using congrArg (fun x => x.1.1) h
    have h2 : f.1 (pt 0 0 1) = f'.1 (pt 0 0 1) := by
      simpa [φ] using congrArg (fun x => x.1.2) h
    have h3 : f.1 (pt 0 1 0) = f'.1 (pt 0 1 0) := by
      simpa [φ] using congrArg (fun x => x.2) h
    have hzero := eq_zero_of_fixed_degenerate_pair e ht₁ hκ0 hκ1 hκ (f.1 - f'.1)
      (by rw [map_sub, f.2.1, f'.2.1]) (by rw [map_sub, f.2.2, f'.2.2])
      (by simp [h1]) (by simp [h2]) (by simp [h3])
    exact Subtype.ext (sub_eq_zero.mp hzero)
  have h := Nat.card_le_card_of_injective φ hφ
  rw [Nat.card_prod, Nat.card_prod] at h
  have hcube : Nat.card k * Nat.card k * Nat.card k = Nat.card k ^ 3 := by ring
  rwa [hcube] at h

end DegeneratePair


section Descent

variable {F : Type*} [Field F] {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
  (ρ : Representation (ZMod 2) SL(2, F) W) [Fact ρ.IsIrreducible]

theorem natCard_fixW_degenerate_pair_le {m : ℕ} (b : Module.Basis (Fin m) (EndRing ρ) W)
    {E : Type*} [Field E] [Finite E] [CharP E 2] (ιF : F →+* E) (ιD : EndRing ρ →+* E)
    (J : Finset ℕ) (hJ : J.card = 3)
    (Φ : (letI := ιF.toAlgebra; (matRepE b ιD).Equiv (frobTensor F E J)))
    {a b' : ℕ} (ha : a ∈ J) (hb : b' ∈ J) (hab : a ≠ b') {t₁ t₂ : F} (ht₁ : t₁ ≠ 0)
    {κ : E} (hκ0 : κ ≠ 0) (hκ1 : κ ≠ 1)
    (hκ : ∀ i : J, (ιF t₂) ^ (2 ^ (i : ℕ)) = κ * (ιF t₁) ^ (2 ^ (i : ℕ))) :
    Nat.card {w : W // ρ (uElt t₁) w = w ∧ ρ (uElt t₂) w = w} ≤ Nat.card (EndRing ρ) ^ 3 := by
  classical
  let _ := ιF.toAlgebra
  have hfinD : Finite (EndRing ρ) := finite_endRing ρ
  obtain ⟨σ, hσa, hσb⟩ := exists_equiv_I3 hJ ha hb hab
  let e : I3 → ℕ := fun i => (σ i : ℕ)
  let ψ := reindexEquiv (F := F) (k := E) σ e (fun i : J => (i : ℕ)) (fun _ => rfl)
  let s : Bool → SL(2, F) := fun x => if x then uElt t₂ else uElt t₁
  have h1 := natCard_fixW_pow ρ b s ιF ιD J Φ
  have h2 : Nat.card {y : (J → Fin 2) → E // ∀ x, frobTensor F E J (s x) y = y} =
      Nat.card {f : (I3 → Fin 2) → E //
        tensorRep F E e (uElt t₁) f = f ∧ tensorRep F E e (uElt t₂) f = f} := by
    refine (Nat.card_congr (Equiv.subtypeEquiv ψ.toLinearEquiv.toEquiv fun f => ?_)).symm
    have key : ∀ g : SL(2, F), frobTensor F E J g (ψ f) = ψ f ↔ tensorRep F E e g f = f := by
      intro g
      have h := equiv_apply ψ g f
      change tensorRep F E (fun i : J => (i : ℕ)) g (ψ f) = ψ f ↔ _
      rw [← h]
      exact ψ.toLinearEquiv.injective.eq_iff
    simp only [Bool.forall_bool, s, Bool.false_eq_true, ↓reduceIte]
    change _ ↔ frobTensor F E J (uElt t₁) (ψ f) = ψ f ∧ frobTensor F E J (uElt t₂) (ψ f) = ψ f
    rw [key, key]
  have hκ' : ∀ i : I3, (algebraMap F E t₂) ^ (2 ^ e i) = κ * (algebraMap F E t₁) ^ (2 ^ e i) := by
    intro i
    change (ιF t₂) ^ (2 ^ e i) = κ * (ιF t₁) ^ (2 ^ e i)
    simpa only [e] using hκ (σ i)
  have h3 := card_fixed_degenerate_pair_le (k := E) e ht₁ hκ0 hκ1 hκ'
  have h4 : Nat.card {w : W // ∀ x, ρ (s x) w = w} =
      Nat.card {w : W // ρ (uElt t₁) w = w ∧ ρ (uElt t₂) w = w} := by
    refine Nat.card_congr (Equiv.subtypeEquivRight fun w => ?_)
    simp only [Bool.forall_bool, s, Bool.false_eq_true, ↓reduceIte]
  have ht : 0 < (letI := ιD.toAlgebra; Module.finrank (EndRing ρ) E) := by
    let _ := ιD.toAlgebra
    have : Module.Finite (EndRing ρ) E := Module.Finite.of_finite
    exact Module.finrank_pos
  rw [h2, h4] at h1
  rw [natCard_E_eq ιD, ← pow_mul, mul_comm, pow_mul] at h3
  rw [← h1] at h3
  exact (Nat.pow_le_pow_iff_left ht.ne').mp h3

end Descent


theorem exists_sorted_orbit {n l : ℕ} (hl : 1 ≤ l) (hn : n = 3 * l) {J : Finset ℕ}
    (hJ3 : J.card = 3) (hJne : J.Nonempty) (hJn : ∀ i ∈ J, i < n)
    (hshift : J.image (fun i => (i + l) % n) = J) :
    ∃ a : ℕ, a + 2 * l < n ∧ J = {a, a + l, a + 2 * l} := by
  classical
  set a := J.min' hJne with hadef
  have haJ : a ∈ J := Finset.min'_mem J hJne
  have ha_lt : a < n := hJn a haJ
  have hmin : ∀ i ∈ J, a ≤ i := fun i hi => Finset.min'_le J i hi
  have hln : l < n := by omega
  have h2ln : 2 * l < n := by omega
  have ha_l_mem : (a + l) % n ∈ J := by
    have h : (a + l) % n ∈ J.image (fun i => (i + l) % n) := by
      simp only [Finset.mem_image, Finset.mem_univ, true_and]
      exact ⟨a, haJ, rfl⟩
    rwa [hshift] at h
  have ha_l : a + l < n := by
    by_contra h
    push Not at h
    have hmod : (a + l) % n = a + l - n := by
      rw [Nat.mod_eq_sub_mod h, Nat.mod_eq_of_lt]
      omega
    have hge : a ≤ (a + l) % n := hmin _ ha_l_mem
    omega
  have ha_lJ : a + l ∈ J := by simpa [ha_l, Nat.mod_eq_of_lt ha_l] using ha_l_mem
  have ha_2l_mem : (a + 2 * l) % n ∈ J := by
    have h : ((a + l) + l) % n ∈ J.image (fun i => (i + l) % n) := by
      simp only [Finset.mem_image, Finset.mem_univ, true_and]
      exact ⟨a + l, ha_lJ, by ring_nf⟩
    rw [hshift] at h
    simpa [two_mul, add_assoc] using h
  have ha_2l : a + 2 * l < n := by
    by_contra h
    push Not at h
    have hmod : (a + 2 * l) % n = a + 2 * l - n := by
      rw [Nat.mod_eq_sub_mod h, Nat.mod_eq_of_lt]
      omega
    have hge : a ≤ (a + 2 * l) % n := hmin _ ha_2l_mem
    omega
  have ha_2lJ : a + 2 * l ∈ J := by simpa [ha_2l, Nat.mod_eq_of_lt ha_2l] using ha_2l_mem
  refine ⟨a, ha_2l, ?_⟩
  have hsub : ({a, a + l, a + 2 * l} : Finset ℕ) ⊆ J := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl <;> assumption
  have hcard : ({a, a + l, a + 2 * l} : Finset ℕ).card = 3 := by
    have h1 : a ∉ ({a + l, a + 2 * l} : Finset ℕ) := by
      simp only [Finset.mem_insert, Finset.mem_singleton]; omega
    have h2 : a + l ∉ ({a + 2 * l} : Finset ℕ) := by
      simp only [Finset.mem_singleton]; omega
    rw [Finset.card_insert_of_notMem h1, Finset.card_insert_of_notMem h2,
      Finset.card_singleton]
  exact (Finset.eq_of_subset_of_card_le hsub (by rw [hJ3, hcard])).symm

section Main

theorem eightL_module_bound {n l : ℕ} (hn : n = 3 * l)
    {F : Type*} [Field F] [Fintype F] [CharP F 2] (hF : Fintype.card F = 2 ^ n)
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    (ρ : Representation (ZMod 2) SL(2, F) W) [Fact ρ.IsIrreducible]
    (hnt : ∃ g, ρ g ≠ 1) (hW : Nat.card W = 2 ^ (8 * l))
    (A : Subgroup SL(2, F)) (hA1 : A ≠ ⊥) (hA2 : ∀ a ∈ A, a * a = 1)
    (hoff : Nat.card W ≤ 2 ^ n * Nat.card A * Nat.card (fixedSub ρ A)) :
    l = 1 ∧ Nat.card A = 2 := by
  classical
  have hl : 1 ≤ l := by
    by_contra h
    have h0 : l = 0 := by omega
    have hW2 : 1 < Nat.card W := by
      obtain ⟨g, hg⟩ := hnt
      have hex : ∃ w : W, ρ g w ≠ w := by
        by_contra hall
        push Not at hall
        exact hg (LinearMap.ext hall)
      obtain ⟨w, hw⟩ := hex
      have hw0 : w ≠ 0 := fun hw' => hw (by rw [hw', map_zero])
      haveI : Nontrivial W := ⟨0, w, fun h' => hw0 h'.symm⟩
      exact Finite.one_lt_card
    rw [h0, mul_zero, pow_zero] at hW
    omega
  have hn1 : 1 ≤ n := by omega
  obtain ⟨d, hd1, hDcard, hdesc⟩ := binary_SL2_irreducible_Frobenius_descent hn1 hF ρ hnt
  have hfinD : Finite (EndRing ρ) := finite_endRing ρ
  have hfinW : Module.Finite (EndRing ρ) W := Module.Finite.of_finite
  let b := Module.finBasis (EndRing ρ) W
  obtain ⟨K, hKF, hKfin, hKchar, ιF, ιD, J, hJne, hJn, ⟨Φ⟩, hshift, hdim⟩ := hdesc b
  have hWcard : Nat.card W = 2 ^ (d * 2 ^ J.card) := by
    have h1 := natCard_eq_pow_finrank (ρ := ρ)
    rw [hDcard, hdim, ← pow_mul] at h1
    exact h1
  have hexp : d * 2 ^ J.card = 8 * l :=
    Nat.pow_right_injective (a := 2) (by norm_num) (by
      change 2 ^ (d * 2 ^ J.card) = 2 ^ (8 * l)
      rw [← hWcard, hW])
  have hlt : d * 2 ^ J.card < 4 * n := by rw [hexp, hn]; omega
  have hkg := le_card_mul_gcd_of_shift (n := n) (d := d) (J := J) (by omega) hJne hJn hshift
  have hcard3 : J.card ≤ 3 := by
    have hgd : Nat.gcd n d ≤ d := Nat.le_of_dvd hd1 (Nat.gcd_dvd_right n d)
    by_contra hk
    push Not at hk
    have h4k : 4 * J.card ≤ 2 ^ J.card := four_mul_le_two_pow hk
    have h1 : d * 2 ^ J.card < d * (4 * J.card) := by
      calc d * 2 ^ J.card < 4 * n := hlt
        _ ≤ 4 * (J.card * d) :=
          Nat.mul_le_mul_left 4 (hkg.trans (Nat.mul_le_mul_left J.card hgd))
        _ = d * (4 * J.card) := by ring
    have h2 : d * (4 * J.card) ≤ d * 2 ^ J.card := Nat.mul_le_mul_left d h4k
    omega
  have hcard1 : 1 ≤ J.card := Finset.card_pos.mpr hJne
  have hcases : J.card = 1 ∨ J.card = 2 ∨ J.card = 3 := by omega
  have hJ3 : J.card = 3 := by
    rcases hcases with hk | hk | hk
    · exfalso
      have hd4 : d = 4 * l := by
        rw [hk] at hexp
        norm_num at hexp
        omega
      obtain ⟨j, hjJ⟩ := Finset.card_eq_one.mp hk
      have hj : j < n := hJn j (by rw [hjJ]; simp)
      have hjd : (j + d) % n = j := by
        have h := congrArg (fun S : Finset ℕ => (j + d) % n ∈ S) hshift
        rw [hjJ] at h
        simpa using h
      have hnd : n ∣ d := by
        have h1 : (j + d) % n = (j + 0) % n := by rw [hjd, add_zero, Nat.mod_eq_of_lt hj]
        exact Nat.modEq_zero_iff_dvd.mp (Nat.ModEq.add_left_cancel' j h1)
      have h34 : 3 * l ∣ 4 * l := by simpa [hn, hd4] using hnd
      obtain ⟨c, hc⟩ := h34
      have h4 : 4 = 3 * c := by
        have h2 : 4 * l = (3 * c) * l := by rw [hc]; ring
        exact Nat.mul_right_cancel (by omega : 0 < l) h2
      omega
    · exfalso
      have hd2 : d = 2 * l := by
        rw [hk] at hexp
        norm_num at hexp
        omega
      have hkg' := hkg
      rw [hk, hn, hd2] at hkg'
      have hg : Nat.gcd (3 * l) (2 * l) = l := by
        apply Nat.dvd_antisymm
        · have h1 : Nat.gcd (3 * l) (2 * l) ∣ 3 * l := Nat.gcd_dvd_left _ _
          have h2 : Nat.gcd (3 * l) (2 * l) ∣ 2 * l := Nat.gcd_dvd_right _ _
          have h3 : Nat.gcd (3 * l) (2 * l) ∣ 3 * l - 2 * l := Nat.dvd_sub h1 h2
          rwa [show 3 * l - 2 * l = l by omega] at h3
        · exact Nat.dvd_gcd (dvd_mul_left l 3) (dvd_mul_left l 2)
      rw [hg] at hkg'
      omega
    · exact hk
  have hd_eq : d = l := by
    rw [hJ3] at hexp
    norm_num at hexp
    omega
  obtain ⟨x, hxU⟩ := exists_conj_le_rootGroup A hA2
  let A' : Subgroup SL(2, F) := A.map (MulAut.conj x⁻¹).toMonoidHom
  have hA'le : A' ≤ (upperUnipotent (F := F)).range := by
    rintro g ⟨a, ha, rfl⟩
    simpa [MulAut.conj_apply] using hxU a ha
  have hA'2inv : ∀ g ∈ A', g * g = 1 := by
    intro g hg
    obtain ⟨a, ha, hae⟩ := Subgroup.mem_map.mp hg
    have h1 : ((MulAut.conj x⁻¹) a) ^ 2 = 1 := by
      rw [pow_two, ← map_mul, hA2 a ha, map_one]
    rw [← hae]
    simpa [pow_two] using h1
  have hA'p : IsPGroup 2 A' := fun g => ⟨1, by
    apply Subtype.ext
    simpa [pow_two] using hA'2inv g g.2⟩
  have hmem : ∀ g, g ∈ A ↔ x⁻¹ * g * x ∈ A' := by
    intro g
    constructor
    · intro hg
      simpa [A', MulAut.conj_apply] using
        Subgroup.mem_map_of_mem (MulAut.conj x⁻¹).toMonoidHom hg
    · intro hg
      obtain ⟨a, ha, hae⟩ := Subgroup.mem_map.mp hg
      have : a = g := by
        simpa [MulAut.conj_apply] using congrArg (fun y => x * y * x⁻¹) hae
      simpa [this] using ha
  have hA'card : Nat.card A' = Nat.card A :=
    (Nat.card_congr (A.equivMapOfInjective _ (MulAut.conj x⁻¹).injective).toEquiv).symm
  have hC : Nat.card (fixedSub ρ A) =
      Nat.card {w : W // ∀ a ∈ A', ρ a w = w} := by
    simpa [fixedSub] using natCard_fixed_conj ρ A A' x hmem
  have hoff' : Nat.card W ≤
      2 ^ n * Nat.card A' * Nat.card {w : W // ∀ a ∈ A', ρ a w = w} := by
    rw [hA'card, ← hC]
    exact hoff
  let E : Finset F := Finset.univ.filter (fun t : F => uElt t ∈ A')
  have hE_mem : ∀ t : F, t ∈ E ↔ uElt t ∈ A' := by
    intro t; simp [E]
  have h0E : (0 : F) ∈ E := by
    rw [hE_mem, uElt_zero]
    exact A'.one_mem
  have hEcard : Nat.card A' = E.card := by
    have hinj : Function.Injective
        (fun t : E => (⟨uElt t, (hE_mem t).mp t.2⟩ : A')) := by
      intro t1 t2 h
      exact Subtype.ext (uElt_injective (congrArg Subtype.val h))
    have hsurj : Function.Surjective
        (fun t : E => (⟨uElt t, (hE_mem t).mp t.2⟩ : A')) := by
      intro a
      obtain ⟨t, ht⟩ := (mem_rootGroup_iff (a : SL(2, F))).mp (hA'le a.2)
      have htE : t ∈ E := (hE_mem t).mpr (by simpa [ht] using a.2)
      exact ⟨⟨t, htE⟩, Subtype.ext (by simpa using ht.symm)⟩
    have hEsub : Nat.card ↥E = E.card := by
      rw [Nat.card_eq_fintype_card, Fintype.card_coe]
    calc Nat.card ↥A' = Nat.card ↥E := (Nat.card_congr (Equiv.ofBijective _ ⟨hinj, hsurj⟩)).symm
      _ = E.card := hEsub
  have hA1lt : 1 < Nat.card A := (Subgroup.one_lt_card_iff_ne_bot A).mpr hA1
  by_cases hA2card : Nat.card A = 2
  · have hA'2 : Nat.card A' = 2 := by rw [hA'card, hA2card]
    obtain ⟨⟨a, haA'⟩, ha_ne, ha_unique⟩ :=
      (Nat.card_eq_two_iff' (1 : A')).mp hA'2
    have ha_val_ne : (a : SL(2, F)) ≠ 1 := by
      intro h'; exact ha_ne (Subtype.ext h')
    have ha_sq : (a : SL(2, F)) * (a : SL(2, F)) = 1 := hA'2inv a haA'
    have hfix_a : Nat.card {w : W // ∀ g ∈ A', ρ g w = w} =
        Nat.card {w : W // ρ (a : SL(2, F)) w = w} := by
      refine Nat.card_congr (Equiv.subtypeEquivRight fun w => ?_)
      constructor
      · intro h; exact h a haA'
      · intro h g hg
        by_cases hg1 : g = 1
        · subst hg1; exact rep_one_apply ρ w
        · have hga : (⟨g, hg⟩ : A') = ⟨a, haA'⟩ :=
            ha_unique ⟨g, hg⟩ (by intro h'; exact hg1 (congrArg Subtype.val h'))
          have hgval : g = (a : SL(2, F)) := congrArg Subtype.val hga
          rw [hgval]; exact h
    have hinv := natCard_fixW_involution ρ b ιF ιD J hJne Φ (a : SL(2, F)) ha_val_ne ha_sq
    have hCval : Nat.card {w : W // ∀ g ∈ A', ρ g w = w} = 2 ^ (4 * l) := by
      rw [hfix_a, hinv, hDcard, hJ3]
      norm_num
      rw [← pow_mul, hd_eq]
      ring
    have hineq : 2 ^ (8 * l) ≤ 2 ^ n * 2 * 2 ^ (4 * l) := by
      calc 2 ^ (8 * l) = Nat.card W := hW.symm
        _ ≤ 2 ^ n * Nat.card A' * Nat.card {w : W // ∀ g ∈ A', ρ g w = w} := hoff'
        _ = 2 ^ n * 2 * 2 ^ (4 * l) := by rw [hA'2, hCval]
    rw [hn] at hineq
    have hpow : 2 ^ (3 * l) * 2 * 2 ^ (4 * l) = 2 ^ (7 * l + 1) := by
      calc 2 ^ (3 * l) * 2 * 2 ^ (4 * l) = 2 ^ (3 * l) * 2 ^ 1 * 2 ^ (4 * l) := by
            rw [pow_one]
        _ = 2 ^ (3 * l + 1) * 2 ^ (4 * l) := by rw [← pow_add]
        _ = 2 ^ (3 * l + 1 + 4 * l) := by rw [← pow_add]
        _ = 2 ^ (7 * l + 1) := by congr 1; ring
    rw [hpow] at hineq
    have hle : 8 * l ≤ 7 * l + 1 :=
      (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp hineq
    exact ⟨by omega, hA2card⟩
  · have hA4 : 4 ≤ Nat.card A := by
      have hAp : IsPGroup 2 A' := fun g => ⟨1, by
        obtain ⟨a, ha, hae⟩ := Subgroup.mem_map.mp g.2
        have h1 : ((MulAut.conj x⁻¹) a) ^ 2 = 1 := by
          rw [pow_two, ← map_mul, hA2 a ha, map_one]
        apply Subtype.ext
        simpa [← hae] using h1⟩
      obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hAp
      have hkpos : 0 < k := by
        rcases Nat.eq_zero_or_pos k with rfl | h
        · exfalso
          have h1 : Nat.card A = 1 := by rw [← hA'card, hk]; norm_num
          omega
        · exact h
      have hkne1 : k ≠ 1 := by
        intro h
        apply hA2card
        rw [← hA'card, hk, h]
        norm_num
      have hk2 : 2 ≤ k := by omega
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk2
        _ = Nat.card A' := hk.symm
        _ = Nat.card A := hA'card
    have hEcard4 : 4 ≤ E.card := by rw [← hEcard, hA'card]; exact hA4
    by_cases hLine : ∃ v : F, v ≠ 0 ∧ ∀ t ∈ E, ∃ c : F, c ^ (2 ^ l) = c ∧ t = c * v
    ·
      obtain ⟨v, hv0, hline⟩ := hLine
      have hE1 : 1 < E.card := by omega
      obtain ⟨t1, ht1E, ht1ne0⟩ := Finset.exists_mem_ne hE1 0
      have hErase : 1 < (E.erase t1).card := by
        rw [Finset.card_erase_of_mem ht1E]; omega
      obtain ⟨t2, ht2erase, ht2ne0⟩ := Finset.exists_mem_ne hErase 0
      have ht2E : t2 ∈ E := Finset.mem_of_mem_erase ht2erase
      have ht2ne1 : t2 ≠ t1 := Finset.ne_of_mem_erase ht2erase
      have hu_fixed : (t2 / t1) ^ (2 ^ l) = t2 / t1 := by
        obtain ⟨c1, hc1fix, hc1eq⟩ := hline t1 ht1E
        obtain ⟨c2, hc2fix, hc2eq⟩ := hline t2 ht2E
        have hc1ne : c1 ≠ 0 := by
          intro h; apply ht1ne0; rw [hc1eq, h, zero_mul]
        have hdiv : (c2 * v) / (c1 * v) = c2 / c1 := by
          rw [mul_div_mul_right _ _ hv0]
        rw [hc1eq, hc2eq, hdiv, div_pow, hc1fix, hc2fix]
      have hu_ne1 : t2 / t1 ≠ 1 := by
        intro h
        have h' : t2 = t1 := by
          rw [div_eq_iff ht1ne0] at h
          simpa using h
        exact ht2ne1 h'
      obtain ⟨a, ha2l, hJeq⟩ := exists_sorted_orbit hl hn hJ3 hJne hJn
        (by simpa [hd_eq] using hshift)
      have haJ : a ∈ J := by rw [hJeq]; simp
      have halJ : a + l ∈ J := by rw [hJeq]; simp
      have hane : a ≠ a + l := by omega
      let κ : K := (ιF (t2 / t1)) ^ (2 ^ a)
      have hκ0 : κ ≠ 0 := by
        exact pow_ne_zero _ ((map_ne_zero ιF).mpr (div_ne_zero ht2ne0 ht1ne0))
      have hκ1 : κ ≠ 1 := by
        intro h
        have h1 : ιF (t2 / t1) = 1 := frob_pow_injective a (by
          simpa [κ] using h)
        have h2 : t2 / t1 = 1 := ιF.injective (by simpa using h1)
        exact hu_ne1 h2
      have htu : (ιF (t2 / t1)) ^ (2 ^ l) = ιF (t2 / t1) := by
        rw [← map_pow, hu_fixed]
      have hx_iter : ∀ j : ℕ, (ιF (t2 / t1)) ^ (2 ^ (j * l)) = ιF (t2 / t1) := by
        intro j
        induction j with
        | zero => simp
        | succ j ih =>
          rw [Nat.succ_mul, pow_add, pow_mul, ih, htu]
      have hx_a : ∀ j : ℕ, (ιF (t2 / t1)) ^ (2 ^ (a + j * l)) =
          (ιF (t2 / t1)) ^ (2 ^ a) := by
        intro j
        rw [show 2 ^ (a + j * l) = 2 ^ (j * l) * 2 ^ a by rw [← pow_add]; ring]
        rw [pow_mul, hx_iter j]
      have ht2_eq : t2 = (t2 / t1) * t1 := (div_mul_cancel₀ t2 ht1ne0).symm
      have hκJ : ∀ i : J, (ιF t2) ^ (2 ^ (i : ℕ)) = κ * (ιF t1) ^ (2 ^ (i : ℕ)) := by
        intro i
        have hi : (i : ℕ) ∈ ({a, a + l, a + 2 * l} : Finset ℕ) := by
          rw [← hJeq]; exact i.2
        simp only [Finset.mem_insert, Finset.mem_singleton] at hi
        rcases hi with h | h | h
        · rw [h, ht2_eq, map_mul, mul_pow]
        · rw [h, ht2_eq, map_mul, mul_pow]
          rw [show a + l = a + 1 * l by ring, hx_a 1]
        · rw [h, ht2_eq, map_mul, mul_pow]
          rw [hx_a 2]
      have hpair := natCard_fixW_degenerate_pair_le ρ b ιF ιD J hJ3 Φ haJ halJ hane
        ht1ne0 hκ0 hκ1 hκJ
      have hC_le : Nat.card {w : W // ∀ g ∈ A', ρ g w = w} ≤
          Nat.card {w : W // ρ (uElt t1) w = w ∧ ρ (uElt t2) w = w} := by
        refine Nat.card_le_card_of_injective
          (fun w => ⟨w.1, w.2 _ ((hE_mem t1).mp ht1E), w.2 _ ((hE_mem t2).mp ht2E)⟩) ?_
        intro w1 w2 h
        apply Subtype.ext
        exact congrArg (fun z : {w : W // ρ (uElt t1) w = w ∧ ρ (uElt t2) w = w} =>
          (z : W)) h
      have hCbound : Nat.card {w : W // ∀ g ∈ A', ρ g w = w} ≤ 2 ^ (3 * l) := by
        refine hC_le.trans (hpair.trans ?_)
        rw [hDcard, ← pow_mul, hd_eq]
        simp [mul_comm]
      have hoffn : 2 ^ (8 * l) ≤
          2 ^ (3 * l) * Nat.card A' * Nat.card {w : W // ∀ g ∈ A', ρ g w = w} := by
        rw [← hW]
        simpa [hn, Nat.card_eq_fintype_card] using hoff'
      obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hA'p
      have hlarge : 2 ^ (2 * l) ≤ Nat.card A' := by
        have h2 : 2 ^ (8 * l) ≤ 2 ^ (6 * l) * Nat.card A' := by
          calc 2 ^ (8 * l) ≤ 2 ^ (3 * l) * Nat.card A' *
                Nat.card {w : W // ∀ g ∈ A', ρ g w = w} := hoffn
            _ ≤ 2 ^ (3 * l) * Nat.card A' * 2 ^ (3 * l) := by
                exact Nat.mul_le_mul_left (2 ^ (3 * l) * Nat.card A') hCbound
            _ = (2 ^ (3 * l) * 2 ^ (3 * l)) * Nat.card A' := by ring
            _ = 2 ^ (6 * l) * Nat.card A' := by
                rw [← pow_add]; congr 1; ring
        rw [hk] at h2
        have h3 : 8 * l ≤ 6 * l + k := by
          rw [show 2 ^ (6 * l) * 2 ^ k = 2 ^ (6 * l + k) by rw [← pow_add]] at h2
          exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp h2
        rw [hk]
        exact Nat.pow_le_pow_right (by norm_num) (by omega)
      have hEcard_le : E.card ≤ 2 ^ l := by
        have hmap : E.image (fun t => t / v) ⊆
            Finset.univ.filter (fun c : F => c ^ (2 ^ l) = c) := by
          intro c hc
          obtain ⟨t, htE, rfl⟩ := Finset.mem_image.mp hc
          obtain ⟨c, hcfix, hceq⟩ := hline t htE
          have hdiv : t / v = c := by
            rw [hceq, mul_div_cancel_right₀ c hv0]
          rw [hdiv]
          simp [hcfix]
        have hcard_image : (E.image (fun t => t / v)).card = E.card := by
          apply Finset.card_image_of_injective
          intro t1' t2' h
          exact mul_right_cancel₀ hv0 (by
            simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using h)
        have hS : (Finset.univ.filter (fun c : F => c ^ (2 ^ l) = c)).card ≤ 2 ^ l :=
          card_le_of_frob_fixed hl _ (fun c hc => (Finset.mem_filter.mp hc).2)
        calc E.card = (E.image (fun t => t / v)).card := hcard_image.symm
          _ ≤ (Finset.univ.filter (fun c : F => c ^ (2 ^ l) = c)).card :=
              Finset.card_le_card hmap
          _ ≤ 2 ^ l := hS
      have hcontra : 2 ^ (2 * l) ≤ 2 ^ l := by
        calc 2 ^ (2 * l) ≤ Nat.card A' := hlarge
          _ = E.card := hEcard
          _ ≤ 2 ^ l := hEcard_le
      have hle : 2 * l ≤ l :=
        (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp hcontra
      omega
    ·
      have hE1 : 1 < E.card := by omega
      obtain ⟨v, hvE, hv0⟩ := Finset.exists_mem_ne hE1 0
      have hex : ∃ t ∈ E, (t / v) ^ (2 ^ l) ≠ t / v := by
        by_contra hall
        push Not at hall
        exact hLine ⟨v, hv0, fun t htE => ⟨t / v, hall t htE,
          by rw [div_mul_cancel₀ t hv0]⟩⟩
      obtain ⟨t, htE, htne⟩ := hex
      have ht0 : t ≠ 0 := by
        intro h0
        apply htne
        rw [h0, zero_div, zero_pow (by positivity)]
      have hvA' : uElt v ∈ A' := (hE_mem v).mp hvE
      have htA' : uElt t ∈ A' := (hE_mem t).mp htE
      obtain ⟨a, ha2l, hJeq⟩ := exists_sorted_orbit hl hn hJ3 hJne hJn
        (by simpa [hd_eq] using hshift)
      have haJ : a ∈ J := by rw [hJeq]; simp
      have halJ : a + l ∈ J := by rw [hJeq]; simp
      have hane : a ≠ a + l := by omega
      have ht_eq : t = (t / v) * v := (div_mul_cancel₀ t hv0).symm
      have hdet : (ιF v) ^ (2 ^ a) * (ιF t) ^ (2 ^ (a + l)) ≠
          (ιF t) ^ (2 ^ a) * (ιF v) ^ (2 ^ (a + l)) := by
        intro h
        rw [ht_eq, map_mul, mul_pow, mul_pow] at h
        have hfac : ((ιF (t / v)) ^ (2 ^ (a + l)) + (ιF (t / v)) ^ (2 ^ a)) *
            ((ιF v) ^ (2 ^ a) * (ιF v) ^ (2 ^ (a + l))) = 0 := by
          have h' : (ιF v) ^ (2 ^ a) *
                ((ιF (t / v)) ^ (2 ^ (a + l)) * (ιF v) ^ (2 ^ (a + l))) +
              ((ιF (t / v)) ^ (2 ^ a) * (ιF v) ^ (2 ^ a)) *
                (ιF v) ^ (2 ^ (a + l)) = 0 := by
            rw [← h]
            exact CharTwo.add_self_eq_zero _
          calc ((ιF (t / v)) ^ (2 ^ (a + l)) + (ιF (t / v)) ^ (2 ^ a)) *
                ((ιF v) ^ (2 ^ a) * (ιF v) ^ (2 ^ (a + l)))
              = (ιF v) ^ (2 ^ a) *
                  ((ιF (t / v)) ^ (2 ^ (a + l)) * (ιF v) ^ (2 ^ (a + l))) +
                ((ιF (t / v)) ^ (2 ^ a) * (ιF v) ^ (2 ^ a)) *
                  (ιF v) ^ (2 ^ (a + l)) := by ring
            _ = 0 := h'
        have hv_ne : (ιF v) ^ (2 ^ a) * (ιF v) ^ (2 ^ (a + l)) ≠ 0 :=
          mul_ne_zero (pow_ne_zero _ ((map_ne_zero ιF).mpr hv0))
            (pow_ne_zero _ ((map_ne_zero ιF).mpr hv0))
        have hsum : (ιF (t / v)) ^ (2 ^ (a + l)) +
            (ιF (t / v)) ^ (2 ^ a) = 0 :=
          (mul_eq_zero.mp hfac).resolve_right hv_ne
        have heq : (ιF (t / v)) ^ (2 ^ (a + l)) =
            (ιF (t / v)) ^ (2 ^ a) := by
          calc (ιF (t / v)) ^ (2 ^ (a + l))
              = (ιF (t / v)) ^ (2 ^ (a + l)) + ((ιF (t / v)) ^ (2 ^ a) +
                  (ιF (t / v)) ^ (2 ^ a)) := by rw [CharTwo.add_self_eq_zero, add_zero]
            _ = ((ιF (t / v)) ^ (2 ^ (a + l)) + (ιF (t / v)) ^ (2 ^ a)) +
                (ιF (t / v)) ^ (2 ^ a) := by abel
            _ = (ιF (t / v)) ^ (2 ^ a) := by rw [hsum, zero_add]
        have hx : (ιF (t / v)) ^ (2 ^ l) = ιF (t / v) := by
          apply frob_pow_injective a
          have hxpow : (ιF (t / v) ^ (2 ^ l)) ^ (2 ^ a) =
              ιF (t / v) ^ (2 ^ (a + l)) := by
            rw [← pow_mul]
            congr 1
            rw [← pow_add]; ring
          rw [hxpow]
          exact heq
        have hx' : (t / v) ^ (2 ^ l) = t / v := by
          apply ιF.injective
          simpa [map_pow] using hx
        exact htne hx'
      have hpair := natCard_fixW_pair_le ρ b ιF ιD J hJ3 Φ haJ halJ hane hv0 hdet
      have hC_le : Nat.card {w : W // ∀ g ∈ A', ρ g w = w} ≤
          Nat.card {w : W // ρ (uElt v) w = w ∧ ρ (uElt t) w = w} := by
        refine Nat.card_le_card_of_injective
          (fun w => ⟨w.1, w.2 _ hvA', w.2 _ htA'⟩) ?_
        intro w1 w2 h
        apply Subtype.ext
        exact congrArg (fun z : {w : W // ρ (uElt v) w = w ∧ ρ (uElt t) w = w} =>
          (z : W)) h
      have hCbound : Nat.card {w : W // ∀ g ∈ A', ρ g w = w} ≤ 2 ^ (2 * l) := by
        refine hC_le.trans (hpair.trans ?_)
        rw [hDcard, ← pow_mul, hd_eq]
        simp [mul_comm]
      have hoffn : 2 ^ (8 * l) ≤
          2 ^ (3 * l) * Nat.card A' * Nat.card {w : W // ∀ g ∈ A', ρ g w = w} := by
        rw [← hW]
        simpa [hn, Nat.card_eq_fintype_card] using hoff'
      obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hA'p
      have hlarge : 2 ^ (3 * l) ≤ Nat.card A' := by
        have h2 : 2 ^ (8 * l) ≤ 2 ^ (5 * l) * Nat.card A' := by
          calc 2 ^ (8 * l) ≤ 2 ^ (3 * l) * Nat.card A' *
                Nat.card {w : W // ∀ g ∈ A', ρ g w = w} := hoffn
            _ ≤ 2 ^ (3 * l) * Nat.card A' * 2 ^ (2 * l) := by
                exact Nat.mul_le_mul_left (2 ^ (3 * l) * Nat.card A') hCbound
            _ = (2 ^ (3 * l) * 2 ^ (2 * l)) * Nat.card A' := by ring
            _ = 2 ^ (5 * l) * Nat.card A' := by
                rw [← pow_add]; congr 1; ring
        rw [hk] at h2
        have h3 : 8 * l ≤ 5 * l + k := by
          rw [show 2 ^ (5 * l) * 2 ^ k = 2 ^ (5 * l + k) by rw [← pow_add]] at h2
          exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp h2
        rw [hk]
        exact Nat.pow_le_pow_right (by norm_num) (by omega)
      have hAleF : Nat.card A' ≤ 2 ^ (3 * l) := by
        calc Nat.card A' = Nat.card A' := rfl
          _ ≤ Nat.card F := card_le_of_involutions A' hA'2inv
          _ = 2 ^ (3 * l) := by rw [Nat.card_eq_fintype_card, hF, hn]
      have hAeq : Nat.card A' = 2 ^ (3 * l) := le_antisymm hAleF hlarge
      have hCroot : Nat.card {w : W // ∀ g ∈ A', ρ g w = w} = Nat.card (EndRing ρ) :=
        card_fixed_eq_of_card ρ hF b ιF ιD J hJn Φ A' hA'2inv (by rw [hAeq, hn])
      have hfinal : 2 ^ (8 * l) ≤ 2 ^ (7 * l) := by
        calc 2 ^ (8 * l) ≤ 2 ^ (3 * l) * Nat.card A' *
                Nat.card {w : W // ∀ g ∈ A', ρ g w = w} := hoffn
          _ = 2 ^ (3 * l) * 2 ^ (3 * l) * 2 ^ l := by
              rw [hAeq, hCroot, hDcard, hd_eq]
          _ = 2 ^ (7 * l) := by
              rw [show 2 ^ (3 * l) * 2 ^ (3 * l) * 2 ^ l = 2 ^ (7 * l) by
                rw [← pow_add, ← pow_add]; congr 1; ring]
      have hle : 8 * l ≤ 7 * l :=
        (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp hfinal
      omega

end Main

end CFSG.Quasithin.Stroth
