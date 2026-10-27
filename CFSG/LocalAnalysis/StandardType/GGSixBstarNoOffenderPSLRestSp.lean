module

public import CFSG.LocalAnalysis.StandardType.GGSixBstarNoOffenderPSLRestNonsplit
public import CFSG.LocalAnalysis.StandardType.GGSixBstarNoOffenderClassicalSp
public import CFSG.Sporadic.Schreier.J4SProfileNode

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank Matrix CFSG.LieType.Universal.Symplectic
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher

namespace NoOffPSLRest

section Exp

variable {F : Type} [Field F] {e s r p : ℕ}

theorem mod_eq_of_pow_eq (he : e ≠ 0) (hp0 : 0 < p) {C : Matrix (Fin e) (Fin e) F}
    (hCp : C ^ p = 1) (hunit : ∀ j : ℕ, ¬ p ∣ j → ∀ c : F, IsUnit (C ^ j - c • 1)) {c : F}
    {a b : ℕ} (h : C ^ a = c • C ^ b) : a % p = b % p := by
  have hzero : C ^ (a + (p - 1) * b) - c • 1 = 0 := by
    have h1 : b + (p - 1) * b = p * b := by
      obtain ⟨p', rfl⟩ : ∃ p', p = p' + 1 := ⟨p - 1, by omega⟩
      simp only [Nat.add_sub_cancel]
      ring
    rw [pow_add, h, smul_mul_assoc, ← pow_add, h1, pow_mul, hCp, one_pow, sub_self]
  have hdvd : p ∣ a + (p - 1) * b := by
    by_contra hnd
    have : Nonempty (Fin e) := ⟨⟨0, Nat.pos_of_ne_zero he⟩⟩
    have hu := hunit _ hnd c
    rw [hzero] at hu
    exact not_isUnit_zero hu
  have h2 : a + (p - 1) * b + b = a + p * b := by
    obtain ⟨p', rfl⟩ : ∃ p', p = p' + 1 := ⟨p - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    ring
  calc a % p = (a + p * b) % p := (Nat.add_mul_mod_self_left _ _ _).symm
    _ = (a + (p - 1) * b + b) % p := by rw [h2]
    _ = b % p := by rw [Nat.add_mod, Nat.mod_eq_zero_of_dvd hdvd, zero_add, Nat.mod_mod]

theorem nsCore_congr {C : Matrix (Fin e) (Fin e) F} (hCp : C ^ p = 1) {k k' : Fin s → ℕ}
    (h : ∀ i, k i % p = k' i % p) : SLNS.nsCore (r := r) C k = SLNS.nsCore C k' := by
  have hpow : ∀ j : ℕ, C ^ j = C ^ (j % p) := fun j => by
    conv_lhs => rw [← Nat.mod_add_div j p, pow_add, pow_mul, hCp, one_pow, mul_one]
  rw [SLNS.nsCore, SLNS.nsCore]
  congr 2
  funext i
  rw [hpow (k i), hpow (k' i), h i]

theorem nsCore_eq_one_of_e_zero (h0 : e = 0) (C : Matrix (Fin e) (Fin e) F) (k : Fin s → ℕ) :
    SLNS.nsCore (r := r) C k = 1 := by
  subst h0
  ext (⟨a, i⟩ | u) (⟨b, j⟩ | v)
  · exact a.elim0
  · exact a.elim0
  · exact b.elim0
  · simp [SLNS.nsCore, Matrix.one_apply]

end Exp

section SpFrame

variable {G : Type} [Group G] {F : Type} [Field F] {n e s r p : ℕ}

@[expose] def SpFrameRep (ψ : StatedSp n F →* G) (A₀ : GL (Fin n ⊕ Fin n) F)
    (ε : Fin n ⊕ Fin n ≃ (Fin e × Fin s) ⊕ Fin r) (C : Matrix (Fin e) (Fin e) F) (b : G)
    (k : Fin s → ℕ) : Prop :=
  ∃ X : StatedSp n F, b = ψ X ∧
    ((X : GL (Fin n ⊕ Fin n) F) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) =
      (A₀ : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) * (SLNS.nsCore C k).submatrix ε ε *
        ((A₀⁻¹ : GL (Fin n ⊕ Fin n) F) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F)

@[expose] noncomputable def spExp (ψ : StatedSp n F →* G) (A₀ : GL (Fin n ⊕ Fin n) F)
    (ε : Fin n ⊕ Fin n ≃ (Fin e × Fin s) ⊕ Fin r) (C : Matrix (Fin e) (Fin e) F) (b : G) :
    Fin s → ℕ :=
  open Classical in
  if h : ∃ k, SpFrameRep ψ A₀ ε C b k then Classical.choose h else 0

@[expose] noncomputable def spCoord (ψ : StatedSp n F →* G) (A₀ : GL (Fin n ⊕ Fin n) F)
    (ε : Fin n ⊕ Fin n ≃ (Fin e × Fin s) ⊕ Fin r) (C : Matrix (Fin e) (Fin e) F) (ζ : ℂˣ)
    (b : G) : Fin s → ℂˣ :=
  fun i => ζ ^ spExp ψ A₀ ε C b i

variable {ψ : StatedSp n F →* G} {A₀ : GL (Fin n ⊕ Fin n) F}
  {ε : Fin n ⊕ Fin n ≃ (Fin e × Fin s) ⊕ Fin r} {C : Matrix (Fin e) (Fin e) F}

theorem spExp_spec {b : G} (h : ∃ k, SpFrameRep ψ A₀ ε C b k) :
    SpFrameRep ψ A₀ ε C b (spExp ψ A₀ ε C b) := by
  rw [spExp, dite_eq_left h]
  exact Classical.choose_spec h

theorem SpFrameRep.mul {b b' : G} {k k' : Fin s → ℕ} (h : SpFrameRep ψ A₀ ε C b k)
    (h' : SpFrameRep ψ A₀ ε C b' k') : SpFrameRep ψ A₀ ε C (b * b') (k + k') := by
  obtain ⟨X, rfl, hX⟩ := h
  obtain ⟨X', rfl, hX'⟩ := h'
  refine ⟨X * X', by rw [map_mul], ?_⟩
  have hA : ((A₀⁻¹ : GL (Fin n ⊕ Fin n) F) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) *
      (A₀ : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  rw [Subgroup.coe_mul, Units.val_mul, hX, hX', ← SLNS.nsCore_mul,
    ← submatrix_mul_equiv (SLNS.nsCore C k) (SLNS.nsCore C k') ε ε ε]
  calc (A₀ : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) * (SLNS.nsCore C k).submatrix ε ε *
        ((A₀⁻¹ : GL (Fin n ⊕ Fin n) F) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) *
      ((A₀ : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) * (SLNS.nsCore C k').submatrix ε ε *
        ((A₀⁻¹ : GL (Fin n ⊕ Fin n) F) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F)) =
      (A₀ : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) * (SLNS.nsCore C k).submatrix ε ε *
        (((A₀⁻¹ : GL (Fin n ⊕ Fin n) F) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) *
          (A₀ : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F)) * (SLNS.nsCore C k').submatrix ε ε *
        ((A₀⁻¹ : GL (Fin n ⊕ Fin n) F) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) := by
        simp only [Matrix.mul_assoc]
    _ = _ := by rw [hA, Matrix.mul_one, Matrix.mul_assoc _ ((SLNS.nsCore C k).submatrix ε ε)]

theorem SpFrameRep.eq {b b' : G} {k : Fin s → ℕ} (h : SpFrameRep ψ A₀ ε C b k)
    (h' : SpFrameRep ψ A₀ ε C b' k) : b = b' := by
  obtain ⟨X, rfl, hX⟩ := h
  obtain ⟨X', rfl, hX'⟩ := h'
  have : X = X' := Subtype.ext (Units.ext (hX.trans hX'.symm))
  rw [this]

theorem SpFrameRep.mod_eq (hψ : Function.Injective ψ) (he : e ≠ 0) (hp0 : 0 < p)
    (hCp : C ^ p = 1) (hunit : ∀ j : ℕ, ¬ p ∣ j → ∀ c : F, IsUnit (C ^ j - c • 1)) {b : G}
    {k k' : Fin s → ℕ} (h : SpFrameRep ψ A₀ ε C b k) (h' : SpFrameRep ψ A₀ ε C b k')
    (i : Fin s) : k i % p = k' i % p := by
  obtain ⟨X, hb, hX⟩ := h
  obtain ⟨X', hb', hX'⟩ := h'
  have hXX : X = X' := hψ (hb.symm.trans hb')
  subst hXX
  rw [hX] at hX'
  have hA : ((A₀⁻¹ : GL (Fin n ⊕ Fin n) F) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) *
      (A₀ : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have h1 := congrArg (fun M => ((A₀⁻¹ : GL (Fin n ⊕ Fin n) F) :
    Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) * M * (A₀ : Matrix (Fin n ⊕ Fin n)
      (Fin n ⊕ Fin n) F)) hX'
  simp only [← Matrix.mul_assoc, hA, Matrix.one_mul] at h1
  simp only [Matrix.mul_assoc, hA, Matrix.mul_one] at h1
  have hblock : C ^ k i = (1 : F) • C ^ k' i := by
    rw [one_smul]
    ext a b
    have h2 := congrFun (congrFun h1 (ε.symm (Sum.inl (a, i)))) (ε.symm (Sum.inl (b, i)))
    simpa [SLNS.nsCore, Matrix.submatrix_apply, blockDiagonal_apply_eq] using h2
  exact mod_eq_of_pow_eq he hp0 hCp hunit hblock

theorem spCoord_eq (hψ : Function.Injective ψ) (he : e ≠ 0) (hp0 : 0 < p) (hCp : C ^ p = 1)
    (hunit : ∀ j : ℕ, ¬ p ∣ j → ∀ c : F, IsUnit (C ^ j - c • 1)) {ζ : ℂˣ}
    (hord : orderOf ζ = p) {b : G} {k : Fin s → ℕ} (h : SpFrameRep ψ A₀ ε C b k) :
    spCoord ψ A₀ ε C ζ b = fun i => ζ ^ k i := by
  funext i
  have h2 := SpFrameRep.mod_eq hψ he hp0 hCp hunit (spExp_spec ⟨k, h⟩) h i
  change ζ ^ spExp ψ A₀ ε C b i = ζ ^ k i
  rw [pow_eq_pow_iff_modEq, hord]
  exact h2

theorem spCoords (hψ : Function.Injective ψ) (he : e ≠ 0) (hp : p.Prime) (hCp : C ^ p = 1)
    (hunit : ∀ j : ℕ, ¬ p ∣ j → ∀ c : F, IsUnit (C ^ j - c • 1)) {Bs : Subgroup G}
    (hframe : ∀ b ∈ Bs, ∃ k, SpFrameRep ψ A₀ ε C b k)
    (hreal : ∀ k : Fin s → ℕ, ∃ b ∈ Bs, SpFrameRep ψ A₀ ε C b k) {ζ : ℂˣ}
    (hord : orderOf ζ = p) : NoOffenderClassical.Coords p Bs (spCoord ψ A₀ ε C ζ) := by
  have hp0 := hp.pos
  have : NeZero p := ⟨hp.ne_zero⟩
  have hprim : IsPrimitiveRoot (ζ : ℂ) p :=
    IsPrimitiveRoot.coe_units_iff.mpr (IsPrimitiveRoot.iff_orderOf.mpr hord)
  refine ⟨fun a ha b hb => ?_, fun a ha b hb hab => ?_, fun t ht => ?_⟩
  · obtain ⟨ka, hka⟩ := hframe a ha
    obtain ⟨kb, hkb⟩ := hframe b hb
    rw [spCoord_eq hψ he hp0 hCp hunit hord (hka.mul hkb), spCoord_eq hψ he hp0 hCp hunit hord hka,
      spCoord_eq hψ he hp0 hCp hunit hord hkb]
    funext i
    simp only [Pi.add_apply, Pi.mul_apply, pow_add]
  · obtain ⟨ka, hka⟩ := hframe a ha
    obtain ⟨kb, hkb⟩ := hframe b hb
    rw [spCoord_eq hψ he hp0 hCp hunit hord hka, spCoord_eq hψ he hp0 hCp hunit hord hkb] at hab
    have hmod : ∀ i, kb i % p = ka i % p := fun i => by
      have h1 := congrFun hab i
      rw [pow_eq_pow_iff_modEq, hord] at h1
      exact h1.symm
    have hkb' : SpFrameRep ψ A₀ ε C b ka := by
      obtain ⟨X, hX1, hX2⟩ := hkb
      exact ⟨X, hX1, by rw [hX2, nsCore_congr hCp hmod]⟩
    exact hka.eq hkb'
  · have hpow : ∀ i, ∃ c, ζ ^ c = t i := fun i => by
      obtain ⟨c, -, hc'⟩ := hprim.eq_pow_of_pow_eq_one (ξ := (t i : ℂ))
        (by rw [← Units.val_pow_eq_pow_val, ht i, Units.val_one])
      exact ⟨c, Units.ext (by rw [Units.val_pow_eq_pow_val, hc'])⟩
    choose c hc' using hpow
    obtain ⟨b, hb, hbc⟩ := hreal c
    exact ⟨b, hb, by rw [spCoord_eq hψ he hp0 hCp hunit hord hbc]; exact funext hc'⟩

theorem noOffender_of_spFrame [Finite F] [CharP F 2] [Finite G] (hn : 3 ≤ n) (hp : p.Prime)
    (hp2 : p ≠ 2) (hψ : Function.Injective ψ) (hker : ψ.ker ≤ Subgroup.center (StatedSp n F))
    (hC : Subgroup.centralizer (ψ.range : Set G) = ⊥) {M Bs : Subgroup G}
    (hM : M ≤ Subgroup.normalizer (ψ.range : Set G)) (hBs : IsElemAbelian p Bs)
    (hCp : C ^ p = 1) (hcunit : ∀ j : ℕ, ¬ p ∣ j → ∀ c : F, IsUnit (C ^ j - c • 1))
    (hreal : ∀ k : Fin s → ℕ, ∃ b ∈ Bs, SpFrameRep ψ A₀ ε C b k)
    (hframe : ∀ b ∈ Bs, ∃ k, SpFrameRep ψ A₀ ε C b k) : GGNoOffender p M Bs := by
  classical
  intro E hEM hEN hE
  by_cases hEC : E ≤ Subgroup.centralizer (Bs : Set G)
  · exact Or.inl hEC
  right
  have he : e ≠ 0 := by
    intro he0
    apply hEC
    intro y _
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    obtain ⟨k, X, rfl, hX⟩ := hframe b hb
    have hX1 : X = 1 := by
      apply Subtype.ext
      apply Units.ext
      rw [hX, NoOffPSLRest.nsCore_eq_one_of_e_zero he0, Matrix.submatrix_one_equiv,
        Matrix.mul_one, ← Units.val_mul, mul_inv_cancel, Units.val_one]
      rfl
    rw [hX1, map_one, one_mul, mul_one]
  have hunit1 : ∀ j : ℕ, ¬ p ∣ j → IsUnit (C ^ j - 1) := fun j hj => by
    simpa using hcunit j hj 1
  have hζ : IsPrimitiveRoot (Complex.exp (2 * Real.pi * Complex.I / p)) p :=
    Complex.isPrimitiveRoot_exp p hp.ne_zero
  set ζu : ℂˣ := (hζ.isUnit hp.ne_zero).unit with hζudef
  have hζu : (ζu : ℂ) = Complex.exp (2 * Real.pi * Complex.I / p) := IsUnit.unit_spec _
  have hord : orderOf ζu = p :=
    ((IsPrimitiveRoot.coe_units_iff.mp (hζu ▸ hζ)).eq_orderOf).symm
  set κ := NoOffPSLRest.spCoord ψ A₀ ε C ζu with hκdef
  have hκ : NoOffenderClassical.Coords p Bs κ :=
    NoOffPSLRest.spCoords hψ he hp hCp hcunit hframe hreal hord
  have hκ1 : ∀ b (j : Fin s), κ b j = 1 ↔ p ∣ NoOffPSLRest.spExp ψ A₀ ε C b j := fun b j => by
    change ζu ^ _ = 1 ↔ _
    rw [← hord]
    exact orderOf_dvd_iff_pow_eq_one.symm
  refine NoOffenderClassical.card_mul_lt_of_coords hp hp2 hζ hκ hBs hE hEN
    (fun y hy => ?_) hEC
  have hyM : y ∈ Subgroup.normalizer (ψ.range : Set G) := hM (hEM hy)
  have hyB : y ∈ Subgroup.normalizer (Bs : Set G) := hEN hy
  obtain ⟨A, σ, hAσ⟩ := NoOffenderClassical.Sp.exists_conj_field hn hker hC hyM
  refine NoOffPSLRest.exists_supp_perm_of_single hp hζ hκ hBs.2 hyB (fun b hb i hbi => ?_)
  have hyb : y * b * y⁻¹ ∈ Bs := (Subgroup.mem_normalizer_iff.mp hyB b).mp hb
  set k := NoOffPSLRest.spExp ψ A₀ ε C b with hk
  set k' := NoOffPSLRest.spExp ψ A₀ ε C (y * b * y⁻¹) with hk'
  obtain ⟨X, hbX, hX⟩ := NoOffPSLRest.spExp_spec (hframe b hb)
  obtain ⟨X', hbX', hX'⟩ := NoOffPSLRest.spExp_spec (hframe _ hyb)
  have hXX : X' = conjSp n (F) A (fieldSp n (F) σ X) := by
    apply hψ
    rw [← hbX', hbX]
    exact hAσ X
  have hM₁ : ((X' : GL (Fin n ⊕ Fin n) (F)) :
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (F)) =
      ((A : GL (Fin n ⊕ Fin n) (F)) :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (F)) *
        ((X : GL (Fin n ⊕ Fin n) (F)) :
          Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (F)).map σ *
        (((A : GL (Fin n ⊕ Fin n) (F))⁻¹ : GL (Fin n ⊕ Fin n) (F)) :
          Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (F)) := by
    rw [hXX, coe_conjSp, Units.val_mul, Units.val_mul, coe_fieldSp]
  have hA₀ : (A₀ : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (F)) *
      ((A₀⁻¹ : GL (Fin n ⊕ Fin n) (F)) :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (F)) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hA₀' : ((A₀⁻¹ : GL (Fin n ⊕ Fin n) (F)) :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (F)) *
      (A₀ : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (F)) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hA : ((A : GL (Fin n ⊕ Fin n) (F)) :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (F)) *
      (((A : GL (Fin n ⊕ Fin n) (F))⁻¹ : GL (Fin n ⊕ Fin n) (F)) :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (F)) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hA' : (((A : GL (Fin n ⊕ Fin n) (F))⁻¹ : GL (Fin n ⊕ Fin n) (F)) :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (F)) *
      ((A : GL (Fin n ⊕ Fin n) (F)) :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (F)) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hfix : Nat.card {v : Fin n ⊕ Fin n → F //
        (SLNS.nsCore C k').submatrix ε ε *ᵥ v = v} =
      Nat.card {v : Fin n ⊕ Fin n → F //
        (SLNS.nsCore C k).submatrix ε ε *ᵥ v = v} := by
    rw [← NoOffPSLRest.card_fix_conj _ _ ((SLNS.nsCore C k').submatrix ε ε) hA₀ hA₀', ← hX', hM₁,
      NoOffPSLRest.card_fix_conj _ _ _ hA hA', NoOffPSLRest.card_fix_map, hX,
      NoOffPSLRest.card_fix_conj _ _ _ hA₀ hA₀']
  have hfilt : (Finset.univ.filter fun j => p ∣ k' j).card =
      (Finset.univ.filter fun j => p ∣ k j).card := by
    rw [NoOffPSLRest.card_fix_submatrix, NoOffPSLRest.card_fix_submatrix,
      NoOffPSLRest.card_fix_nsCore hCp hunit1, NoOffPSLRest.card_fix_nsCore hCp hunit1] at hfix
    have h2 := Nat.pow_right_injective (Finite.one_lt_card (α := F)) hfix
    exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero he) (Nat.add_right_cancel h2)
  have hone : (Finset.univ.filter fun j => ¬ p ∣ k j) = {i} := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    rw [← hbi j, ne_eq, hκ1]
  have hcount : (Finset.univ.filter fun j => ¬ p ∣ k' j).card = 1 := by
    have h1 := Finset.card_filter_add_card_filter_not (s := Finset.univ) (fun j => p ∣ k j)
    have h2 := Finset.card_filter_add_card_filter_not (s := Finset.univ) (fun j => p ∣ k' j)
    rw [hone, Finset.card_singleton] at h1
    omega
  obtain ⟨i', hi'⟩ := Finset.card_eq_one.mp hcount
  refine ⟨i', fun j => ?_⟩
  have h1 := Finset.ext_iff.mp hi' j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton] at h1
  rw [ne_eq, hκ1]
  exact h1

end SpFrame

end NoOffPSLRest

section Family

@[expose] def GGSpNonsplitFrameInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (n f : ℕ) (ψ : (ggU .PSp n f).K →* G),
    GGSixCtxV2 p B Bs x L D J (ggU .PSp n f).D .PSp n f ψ →
    Subgroup.centralizer (ggG0 p B x L D J : Set G) = ⊥ → ¬ p ∣ 2 ^ f - 1 →
      ∃ (e s r : ℕ) (C : Matrix (Fin e) (Fin e) (GaloisField 2 f))
        (ε : Fin n ⊕ Fin n ≃ (Fin e × Fin s) ⊕ Fin r) (A₀ : GL (Fin n ⊕ Fin n) (GaloisField 2 f)),
        C ^ p = 1 ∧ (∀ j : ℕ, ¬ p ∣ j → ∀ c : GaloisField 2 f, IsUnit (C ^ j - c • 1)) ∧
          (∀ k : Fin s → ℕ, ∃ b ∈ Bs, NoOffPSLRest.SpFrameRep ψ A₀ ε C b k) ∧
            ∀ b ∈ Bs, ∃ k : Fin s → ℕ, NoOffPSLRest.SpFrameRep ψ A₀ ε C b k

theorem ggSixBstarNoOffenderOn_PSpNonsplit_of_frame (hF : GGSpNonsplitFrameInput) :
    GGSixBstarNoOffenderOn GGPSpNonsplit := by
  classical
  intro G _ _ p B Bs x L D J t n f ψ hP hctx hC
  obtain ⟨rfl, hns⟩ := hP
  have hrk : 2 ≤ n := hctx.2.2.2.1.2
  have hker : ψ.ker ≤ Subgroup.center (StatedSp n (GaloisField 2 f)) := hctx.2.2.2.2.1.2
  have hCψ : Subgroup.centralizer (ψ.range : Set G) = ⊥ := by
    rw [hctx.range_eq]
    exact hC
  have hpp := hctx.prime
  have hp2 := hctx.ne_two
  have hBs := hctx.bstar.2.1
  have hdiag : ∀ b ∈ Bs, GGPsiInnerDiag (Symplectic.rootDatum n (GaloisField 2 f)) ψ b :=
    fun b hb => hctx.2.2.2.2.2.2.1.2 b hb
  have hBcard : Nat.card B = p ^ LargeEvenTwoLocalRank p G := hctx.sstar.1.2.1
  have hBBs : Nat.card B ≤ Nat.card Bs := Subgroup.card_le_of_le hctx.bstar.1
  have hr4 : 4 ≤ LargeEvenTwoLocalRank p G := hctx.beta.2.2.2
  have hcard : p ^ 4 ≤ Nat.card Bs :=
    calc p ^ 4 ≤ p ^ LargeEvenTwoLocalRank p G := Nat.pow_le_pow_right hpp.pos hr4
      _ = Nat.card B := hBcard.symm
      _ ≤ Nat.card Bs := hBBs
  have hn4 : 4 ≤ n :=
    AutPSp.four_le_of_bstar (K := GaloisField 2 f) hrk ψ hker hCψ hpp hp2 hBs hcard hdiag
  have : NeZero n := ⟨by omega⟩
  have hψ : Function.Injective ψ := by
    rw [injective_iff_map_eq_one]
    intro a ha
    have hz : a ∈ Subgroup.center (StatedSp n (GaloisField 2 f)) := hker ha
    rw [AutPSp.center_eq_bot] at hz
    exact Subgroup.mem_bot.mp hz
  obtain ⟨d, s, r, C, ε, A₀, hCp, hcunit, hreal, hframe⟩ := hF G p B Bs x L D J n f ψ hctx hC hns
  have hM : ggM p B x L D J ≤ Subgroup.normalizer (ψ.range : Set G) := fun y hy => by
    rw [hctx.range_eq]
    exact hy
  exact NoOffPSLRest.noOffender_of_spFrame (by omega) hpp hp2 hψ hker hCψ hM hBs hCp hcunit hreal
    hframe

end Family

end CFSG.StandardType
