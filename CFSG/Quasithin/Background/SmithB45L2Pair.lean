module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesCount

public section

namespace CFSG.Quasithin.B45L2

open CFSG.QuasithinUnique.Setup.SL2Modules
open scoped MatrixGroups

section Option

variable {F : Type*} [Field F] {k : Type*} [Field k] [Algebra F k] [CharP k 2]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem tensorRep_uElt_optCons_zero (e : Option ι → ℕ) (t : F) (f : (Option ι → Fin 2) → k)
    (y : ι → Fin 2) :
    tensorRep F k e (uElt t) f (optCons 0 y) =
      tensorRep F k (fun i => e (some i)) (uElt t) (fun y => f (optCons 0 y)) y +
        (algebraMap F k t) ^ (2 ^ e none) *
          tensorRep F k (fun i => e (some i)) (uElt t) (fun y => f (optCons 1 y)) y := by
  rw [tensorRep_option_apply, Fin.sum_univ_two, twistMat_uElt]
  simp

theorem tensorRep_uElt_optCons_one (e : Option ι → ℕ) (t : F) (f : (Option ι → Fin 2) → k)
    (y : ι → Fin 2) :
    tensorRep F k e (uElt t) f (optCons 1 y) =
      tensorRep F k (fun i => e (some i)) (uElt t) (fun y => f (optCons 1 y)) y := by
  rw [tensorRep_option_apply, Fin.sum_univ_two, twistMat_uElt]
  simp

end Option

theorem tensorRep_empty_apply {F : Type*} [Field F] {k : Type*} [Field k] [Algebra F k]
    [CharP k 2] (e : Empty → ℕ) (g : SL(2, F)) (f : (Empty → Fin 2) → k) (y : Empty → Fin 2) :
    tensorRep F k e g f y = f y := by
  rw [tensorRep_apply, Fintype.sum_eq_single y]
  · have h : tmatE k e g y y = 1 := by simp [tmatE]
    rw [h, one_mul]
  · intro x hx
    exact absurd (Subsingleton.elim x y) hx

abbrev I3 : Type := Option (Option (Option Empty))

@[expose] def pt (a b c : Fin 2) : I3 → Fin 2 :=
  optCons a (optCons b (optCons c (fun z : Empty => z.elim)))

section Triple

variable {F : Type*} [Field F] {k : Type*} [Field k] [Algebra F k] [CharP k 2]

omit [CharP k 2] in
theorem eq_zero_of_add_eq_self {x y : k} (h : x + y = x) : y = 0 := by
  have := congrArg (fun z => z - x) h
  simpa using this

theorem fixed_eqs (e : I3 → ℕ) (t : F) (f : (I3 → Fin 2) → k)
    (hf : tensorRep F k e (uElt t) f = f) :
    (algebraMap F k t) ^ (2 ^ e (some (some none))) * f (pt 1 1 1) = 0 ∧
    (algebraMap F k t) ^ (2 ^ e (some (some none))) * f (pt 1 0 1) +
        (algebraMap F k t) ^ (2 ^ e (some none)) *
          (f (pt 1 1 0) + (algebraMap F k t) ^ (2 ^ e (some (some none))) * f (pt 1 1 1)) = 0 ∧
    (algebraMap F k t) ^ (2 ^ e (some (some none))) * f (pt 0 1 1) +
        (algebraMap F k t) ^ (2 ^ e none) *
          (f (pt 1 1 0) + (algebraMap F k t) ^ (2 ^ e (some (some none))) * f (pt 1 1 1)) = 0 ∧
    (algebraMap F k t) ^ (2 ^ e (some (some none))) * f (pt 0 0 1) +
        (algebraMap F k t) ^ (2 ^ e (some none)) *
          (f (pt 0 1 0) + (algebraMap F k t) ^ (2 ^ e (some (some none))) * f (pt 0 1 1)) +
        (algebraMap F k t) ^ (2 ^ e none) *
          (f (pt 1 0 0) + (algebraMap F k t) ^ (2 ^ e (some (some none))) * f (pt 1 0 1) +
            (algebraMap F k t) ^ (2 ^ e (some none)) *
              (f (pt 1 1 0) + (algebraMap F k t) ^ (2 ^ e (some (some none))) *
                f (pt 1 1 1))) = 0 := by
  have h110 := congrFun hf (pt 1 1 0)
  have h100 := congrFun hf (pt 1 0 0)
  have h010 := congrFun hf (pt 0 1 0)
  have h000 := congrFun hf (pt 0 0 0)
  simp only [pt, tensorRep_uElt_optCons_zero, tensorRep_uElt_optCons_one,
    tensorRep_empty_apply] at h110 h100 h010 h000
  simp only [pt]
  refine ⟨eq_zero_of_add_eq_self h110, ?_, ?_, ?_⟩
  · refine eq_zero_of_add_eq_self (x := f (optCons 1 (optCons 0 (optCons 0 fun z => z.elim))))
      (by linear_combination h100)
  · refine eq_zero_of_add_eq_self (x := f (optCons 0 (optCons 1 (optCons 0 fun z => z.elim))))
      (by linear_combination h010)
  · refine eq_zero_of_add_eq_self (x := f (optCons 0 (optCons 0 (optCons 0 fun z => z.elim))))
      (by linear_combination h000)

omit [CharP k 2] in
theorem eq_zero_of_det {α₁ β₁ α₂ β₂ x y : k} (hdet : α₁ * β₂ ≠ α₂ * β₁)
    (h₁ : α₁ * x + β₁ * y = 0) (h₂ : α₂ * x + β₂ * y = 0) : x = 0 ∧ y = 0 := by
  have hd : α₁ * β₂ - α₂ * β₁ ≠ 0 := sub_ne_zero.mpr hdet
  constructor
  · have : (α₁ * β₂ - α₂ * β₁) * x = 0 := by linear_combination β₂ * h₁ - β₁ * h₂
    exact (mul_eq_zero.mp this).resolve_left hd
  · have : (α₁ * β₂ - α₂ * β₁) * y = 0 := by linear_combination α₁ * h₂ - α₂ * h₁
    exact (mul_eq_zero.mp this).resolve_left hd

theorem eq_pt (x : I3 → Fin 2) :
    x = pt (x none) (x (some none)) (x (some (some none))) := by
  funext o
  rcases o with _ | _ | _ | z
  · rfl
  · rfl
  · rfl
  · exact z.elim

theorem eq_zero_of_fixed_pair (e : I3 → ℕ) {t₁ t₂ : F} (ht₁ : t₁ ≠ 0)
    (hdet : (algebraMap F k t₁) ^ (2 ^ e (some none)) *
        (algebraMap F k t₂) ^ (2 ^ e (some (some none))) ≠
      (algebraMap F k t₂) ^ (2 ^ e (some none)) *
        (algebraMap F k t₁) ^ (2 ^ e (some (some none))))
    (f : (I3 → Fin 2) → k) (hf₁ : tensorRep F k e (uElt t₁) f = f)
    (hf₂ : tensorRep F k e (uElt t₂) f = f) (h000 : f (pt 0 0 0) = 0) (h100 : f (pt 1 0 0) = 0) :
    f = 0 := by
  obtain ⟨a1, b1, c1, d1⟩ := fixed_eqs e t₁ f hf₁
  obtain ⟨-, b2, -, d2⟩ := fixed_eqs e t₂ f hf₂
  have hτ : ∀ m : ℕ, (algebraMap F k t₁) ^ (2 ^ m) ≠ 0 := fun m =>
    pow_ne_zero _ ((map_ne_zero (algebraMap F k)).mpr ht₁)
  have h111 : f (pt 1 1 1) = 0 := (mul_eq_zero.mp a1).resolve_left (hτ _)
  rw [h111, mul_zero, add_zero] at b1 b2 c1 d1 d2
  have hdet' : (algebraMap F k t₁) ^ (2 ^ e (some (some none))) *
      (algebraMap F k t₂) ^ (2 ^ e (some none)) ≠
      (algebraMap F k t₂) ^ (2 ^ e (some (some none))) *
        (algebraMap F k t₁) ^ (2 ^ e (some none)) := by
    intro h
    apply hdet
    linear_combination -h
  obtain ⟨h101, h110⟩ := eq_zero_of_det hdet' b1 b2
  rw [h110, mul_zero, add_zero] at c1
  have h011 : f (pt 0 1 1) = 0 := (mul_eq_zero.mp c1).resolve_left (hτ _)
  rw [h100, h101, h110, h011] at d1 d2
  simp only [mul_zero, add_zero] at d1 d2
  obtain ⟨h001, h010⟩ := eq_zero_of_det hdet' d1 d2
  funext x
  rw [eq_pt x]
  rcases zero_or_one (x none) with ha | ha <;> rcases zero_or_one (x (some none)) with hb | hb <;>
    rcases zero_or_one (x (some (some none))) with hc | hc <;> rw [ha, hb, hc] <;>
    assumption
where
  zero_or_one (a : Fin 2) : a = 0 ∨ a = 1 := by fin_cases a <;> simp

theorem card_fixed_pair_le [Finite k] (e : I3 → ℕ) {t₁ t₂ : F} (ht₁ : t₁ ≠ 0)
    (hdet : (algebraMap F k t₁) ^ (2 ^ e (some none)) *
        (algebraMap F k t₂) ^ (2 ^ e (some (some none))) ≠
      (algebraMap F k t₂) ^ (2 ^ e (some none)) *
        (algebraMap F k t₁) ^ (2 ^ e (some (some none)))) :
    Nat.card {f : (I3 → Fin 2) → k //
      tensorRep F k e (uElt t₁) f = f ∧ tensorRep F k e (uElt t₂) f = f} ≤ Nat.card k ^ 2 := by
  let φ : {f : (I3 → Fin 2) → k //
      tensorRep F k e (uElt t₁) f = f ∧ tensorRep F k e (uElt t₂) f = f} → k × k :=
    fun f => (f.1 (pt 0 0 0), f.1 (pt 1 0 0))
  have hφ : Function.Injective φ := by
    rintro ⟨f, hf₁, hf₂⟩ ⟨f', hf₁', hf₂'⟩ h
    simp only [φ, Prod.mk.injEq] at h
    have h1 := eq_zero_of_fixed_pair (k := k) e ht₁ hdet (f - f')
      (by rw [map_sub, hf₁, hf₁']) (by rw [map_sub, hf₂, hf₂'])
      (by simp [h.1]) (by simp [h.2])
    exact Subtype.ext (sub_eq_zero.mp h1)
  have h := Nat.card_le_card_of_injective φ hφ
  rwa [Nat.card_prod, ← sq] at h

end Triple

theorem exists_equiv_I3 {J : Finset ℕ} (hJ : J.card = 3) {a b : ℕ} (ha : a ∈ J) (hb : b ∈ J)
    (hab : a ≠ b) : ∃ σ : I3 ≃ J, (σ (some none) : ℕ) = a ∧ (σ (some (some none)) : ℕ) = b := by
  classical
  obtain ⟨c, hc⟩ : ((J.erase a).erase b).Nonempty := by
    rw [← Finset.card_pos, Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hab.symm, hb⟩),
      Finset.card_erase_of_mem ha, hJ]
    norm_num
  have hcb : c ≠ b := (Finset.mem_erase.mp hc).1
  have hca : c ≠ a := (Finset.mem_erase.mp (Finset.mem_erase.mp hc).2).1
  have hcJ : c ∈ J := (Finset.mem_erase.mp (Finset.mem_erase.mp hc).2).2
  let f : I3 → J := fun o => match o with
    | none => ⟨c, hcJ⟩
    | some none => ⟨a, ha⟩
    | some (some none) => ⟨b, hb⟩
    | some (some (some z)) => z.elim
  have hf : Function.Injective f := by
    intro x y hxy
    have h := congrArg Subtype.val hxy
    rcases x with _ | _ | _ | z <;> rcases y with _ | _ | _ | w <;>
      first | rfl | exact z.elim | exact w.elim | (simp [f] at h; omega)
  have hcard : Fintype.card I3 = Fintype.card J := by simp [hJ]
  refine ⟨Equiv.ofBijective f ((Fintype.bijective_iff_injective_and_card f).mpr ⟨hf, hcard⟩),
    rfl, rfl⟩

section Descent

variable {F : Type*} [Field F] {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
  (ρ : Representation (ZMod 2) SL(2, F) W) [Fact ρ.IsIrreducible]

theorem natCard_fixW_pair_le {m : ℕ} (b : Module.Basis (Fin m) (EndRing ρ) W) {E : Type*}
    [Field E] [Finite E] [CharP E 2] (ιF : F →+* E) (ιD : EndRing ρ →+* E) (J : Finset ℕ)
    (hJ : J.card = 3) (Φ : (letI := ιF.toAlgebra; (matRepE b ιD).Equiv (frobTensor F E J)))
    {a b' : ℕ} (ha : a ∈ J) (hb : b' ∈ J) (hab : a ≠ b') {t₁ t₂ : F} (ht₁ : t₁ ≠ 0)
    (hdet : (ιF t₁) ^ (2 ^ a) * (ιF t₂) ^ (2 ^ b') ≠ (ιF t₂) ^ (2 ^ a) * (ιF t₁) ^ (2 ^ b')) :
    Nat.card {w : W // ρ (uElt t₁) w = w ∧ ρ (uElt t₂) w = w} ≤ Nat.card (EndRing ρ) ^ 2 := by
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
  have hdet' : (algebraMap F E t₁) ^ (2 ^ e (some none)) *
      (algebraMap F E t₂) ^ (2 ^ e (some (some none))) ≠
      (algebraMap F E t₂) ^ (2 ^ e (some none)) *
        (algebraMap F E t₁) ^ (2 ^ e (some (some none))) := by
    simp only [e, hσa, hσb]
    exact hdet
  have h3 := card_fixed_pair_le (k := E) e ht₁ hdet'
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

end CFSG.Quasithin.B45L2
