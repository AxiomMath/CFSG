module

public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherPrimeFormRealization
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherAntiunitaryTransport
public import CFSG.CharacterTheory.Semidihedral.Principal.CoprimeFixedPointLifting
public import CFSG.RankThree.Chevalley.SteinbergBTCanonicalFieldCommon
public import CFSG.RankThree.Chevalley.SteinbergBTNoninnerLocalCore

public noncomputable section

namespace CFSG.RankThree.Classical

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.LieType.Chevalley

variable {ℓ f : ℕ} {K : Type} [Field K]

theorem dvd_and_card_fixSubfield_unitary (h : UnitaryFieldData ℓ f K) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {σ : K ≃+* K} (hσ : orderOf σ = p) :
    p ∣ f ∧ Nat.card (fixSubfield σ) = ℓ ^ (2 * (f / p)) := by
  obtain ⟨hdvd, hcard⟩ := CFSG.RankThree.Chevalley.SteinbergBT.card_fixSubfield h.prime
    (by have := h.one_le; omega) h.card σ
  rw [hσ] at hdvd hcard
  have hpf : p ∣ f :=
    Nat.Coprime.dvd_of_dvd_mul_left ((Nat.coprime_primes hp Nat.prime_two).2 hp2) hdvd
  exact ⟨hpf, by rw [hcard, Nat.mul_div_assoc _ hpf]⟩

theorem fixSubfield_unitaryFieldData (h : UnitaryFieldData ℓ f K) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {σ : K ≃+* K} (hσ : orderOf σ = p) :
    UnitaryFieldData ℓ (f / p) (fixSubfield σ) := by
  obtain ⟨hpf, hcard⟩ := dvd_and_card_fixSubfield_unitary h hp hp2 hσ
  exact ⟨h.prime, Nat.div_pos (Nat.le_of_dvd (by have := h.one_le; omega) hpf) hp.pos, hcard⟩

theorem fixSubfield_unitaryFieldData_bar (h : UnitaryFieldData ℓ f K) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {σ : K ≃+* K} (hσ : orderOf σ = p) (c : fixSubfield σ) :
    ((fixSubfield_unitaryFieldData h hp hp2 hσ).bar c : K) = h.bar c := by
  have := h.finite
  obtain ⟨hpf, hcard⟩ := dvd_and_card_fixSubfield_unitary h hp hp2 hσ
  obtain ⟨e, he⟩ := hpf
  have hep : f / p = e := by rw [he, Nat.mul_div_cancel_left _ hp.pos]
  rw [hep] at hcard
  have hc2 : (c : K) ^ ℓ ^ (2 * e) = c :=
    CFSG.RankThree.Chevalley.SteinbergBT.pow_card_eq_self_of_mem hcard c.2
  have hck : ∀ m : ℕ, (c : K) ^ (ℓ ^ (2 * e)) ^ m = c := by
    intro m
    induction m with
    | zero => simp
    | succ m ih => rw [pow_succ, pow_mul, ih, hc2]
  obtain ⟨m, hm⟩ := hp.odd_of_ne_two hp2
  rw [UnitaryFieldData.bar_apply, UnitaryFieldData.bar_apply, SubmonoidClass.coe_pow, hep, he,
    hm, show ℓ ^ ((2 * m + 1) * e) = (ℓ ^ (2 * e)) ^ m * ℓ ^ e by ring,
    pow_mul (c : K) ((ℓ ^ (2 * e)) ^ m) (ℓ ^ e), hck]

section Inclusion

variable (k : Subfield K) (n : ℕ)

@[expose] def subfieldGL : GL (Fin n) k →* GL (Fin n) K :=
  Units.map (RingHom.mapMatrix k.subtype).toMonoidHom

theorem coe_subfieldGL (g : GL (Fin n) k) :
    ((subfieldGL k n g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      (g : Matrix (Fin n) (Fin n) k).map k.subtype :=
  rfl

theorem subfieldGL_injective : Function.Injective (subfieldGL k n) := fun _ _ hgg' =>
  Units.ext (Matrix.map_injective Subtype.val_injective (congrArg Units.val hgg'))

end Inclusion

section SU

variable (h : UnitaryFieldData ℓ f K) {e : ℕ} {k : Subfield K} (h₀ : UnitaryFieldData ℓ e k)
  (hbar : ∀ c : k, (h₀.bar c : K) = h.bar c) (n : ℕ)

include hbar in
theorem map_subtype_map_bar (M : Matrix (Fin n) (Fin n) k) :
    (M.map k.subtype).map h.bar = (M.map h₀.bar).map k.subtype :=
  Matrix.ext fun i j => (hbar (M i j)).symm

include hbar in
theorem norm_subtype (c : k) : h.norm (c : K) = (h₀.norm c : K) := by
  rw [UnitaryFieldData.norm, UnitaryFieldData.norm, ← hbar, Subfield.coe_mul]

include hbar in
theorem subfieldGL_mem_gramSU {g : GL (Fin n) k}
    (hg : g ∈ gramSU h₀ ((1 : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)) :
    subfieldGL k n g ∈ gramSU h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
  obtain ⟨h1, h2⟩ := mem_gramSU.1 hg
  rw [Units.val_one, Matrix.mul_one] at h1
  refine mem_gramSU.2 ⟨?_, ?_⟩
  · rw [Units.val_one, Matrix.mul_one, coe_subfieldGL, map_subtype_map_bar h h₀ hbar,
      ← transpose_map, ← Matrix.map_mul, h1, Matrix.map_one _ (map_zero _) (map_one _)]
  · rw [coe_subfieldGL]
    change (k.subtype.mapMatrix (g : Matrix (Fin n) (Fin n) k)).det = 1
    rw [← RingHom.map_det, h2, map_one]

@[expose] def subfieldSU : gramSU h₀ ((1 : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) →*
    gramSU h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) :=
  ((subfieldGL k n).comp (gramSU h₀ _).subtype).codRestrict _ fun g =>
    subfieldGL_mem_gramSU h h₀ hbar n g.2

theorem coe_subfieldSU (g : gramSU h₀ ((1 : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)) :
    ((subfieldSU h h₀ hbar n g : gramSU h _) : GL (Fin n) K) = subfieldGL k n g :=
  rfl

theorem subfieldSU_injective : Function.Injective (subfieldSU h h₀ hbar n) := fun _ _ hgg' =>
  Subtype.ext (subfieldGL_injective k n (congrArg Subtype.val hgg'))

theorem subfieldGL_scalar (c : kˣ) :
    subfieldGL k n (GeneralLinearGroup.scalar (Fin n) c) =
      GeneralLinearGroup.scalar (Fin n) (Units.map k.subtype.toMonoidHom c) := by
  refine Units.ext ?_
  rw [coe_subfieldGL, GeneralLinearGroup.coe_scalar, GeneralLinearGroup.coe_scalar,
    scalar_apply, scalar_apply, diagonal_map (map_zero _)]
  rfl

theorem subfieldSU_mem_normOneScalars
    {g : gramSU h₀ ((1 : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)}
    (hg : g ∈ normOneScalars h₀ (gramSU h₀ _) n) :
    subfieldSU h h₀ hbar n g ∈ normOneScalars h (gramSU h _) n := by
  obtain ⟨c, hcN, hcn, hgc⟩ := hg
  refine ⟨Units.map k.subtype.toMonoidHom c, ?_, ?_, ?_⟩
  · change h.norm ((c : k) : K) = 1
    rw [norm_subtype h h₀ hbar, hcN, Subfield.coe_one]
  · rw [← map_pow, hcn, map_one]
  · rw [coe_subfieldSU, hgc, subfieldGL_scalar]

theorem comap_subfieldSU_normOneScalars (hn : 1 ≤ n) :
    (normOneScalars h (gramSU h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) n).comap
        (subfieldSU h h₀ hbar n) =
      normOneScalars h₀ (gramSU h₀ ((1 : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)) n := by
  refine le_antisymm (fun g hg => ?_) fun g hg => subfieldSU_mem_normOneScalars h h₀ hbar n hg
  obtain ⟨c, hcN, hcn, hgc⟩ := hg
  have hentry : ∀ i j, (((g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) i j : K) =
      if i = j then (c : K) else 0 := by
    intro i j
    have h1 := congrArg (fun x : GL (Fin n) K => (x : Matrix (Fin n) (Fin n) K) i j) hgc
    simp only [coe_subfieldSU, coe_subfieldGL, GeneralLinearGroup.coe_scalar, scalar_apply,
      diagonal_apply, Matrix.map_apply] at h1
    exact h1
  set i₀ : Fin n := ⟨0, hn⟩
  set c₀ : k := ((g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) i₀ i₀ with hc₀
  have hc₀c : (c₀ : K) = c := by
    rw [hc₀, hentry]
    simp
  have hc₀0 : c₀ ≠ 0 := fun h0 => c.ne_zero (by rw [← hc₀c, h0, Subfield.coe_zero])
  refine ⟨Units.mk0 c₀ hc₀0, ?_, ?_, ?_⟩
  · apply Subtype.val_injective
    rw [Units.val_mk0, ← norm_subtype h h₀ hbar, hc₀c, hcN, Subfield.coe_one]
  · apply Units.ext
    apply Subtype.val_injective
    rw [Units.val_pow_eq_pow_val, Units.val_mk0, SubmonoidClass.coe_pow, hc₀c,
      ← Units.val_pow_eq_pow_val, hcn, Units.val_one, Units.val_one, Subfield.coe_one]
  · apply subfieldGL_injective k n
    rw [show subfieldGL k n (g : GL (Fin n) k) =
      ((subfieldSU h h₀ hbar n g : gramSU h _) : GL (Fin n) K) from rfl, hgc, subfieldGL_scalar]
    congr 1
    exact Units.ext hc₀c.symm

@[expose] def subfieldPSU : primeFormP h₀ ((1 : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) →*
    primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) :=
  QuotientGroup.map _ _ (subfieldSU h h₀ hbar n) fun _ hg =>
    subfieldSU_mem_normOneScalars h h₀ hbar n hg

theorem subfieldPSU_mk (g : gramSU h₀ ((1 : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)) :
    subfieldPSU h h₀ hbar n (g : primeFormP h₀ _) =
      ((subfieldSU h h₀ hbar n g : gramSU h _) : primeFormP h _) :=
  rfl

theorem subfieldPSU_injective (hn : 1 ≤ n) : Function.Injective (subfieldPSU h h₀ hbar n) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  induction x using QuotientGroup.induction_on with
  | H g =>
    rw [subfieldPSU_mk, QuotientGroup.eq_one_iff] at hx
    rw [QuotientGroup.eq_one_iff, ← comap_subfieldSU_normOneScalars h h₀ hbar n hn]
    exact hx

end SU

section Fixed

variable (h : UnitaryFieldData ℓ f K) (n : ℕ)

@[expose] def fieldSUHom :
    (K ≃+* K) →* MulAut (gramSU h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) where
  toFun φ := primeFormFieldSU h isPrimeFormGram_one φ
  map_one' := MulEquiv.ext fun g => Subtype.ext (by
    change glAut 1 (g : GL (Fin n) K) = g
    rw [map_one]
    rfl)
  map_mul' φ ψ := MulEquiv.ext fun g => Subtype.ext (by
    change glAut (φ * ψ) (g : GL (Fin n) K) = glAut φ (glAut ψ (g : GL (Fin n) K))
    rw [map_mul]
    rfl)

theorem coe_fieldSUHom (φ : K ≃+* K)
    (g : gramSU h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) :
    ((fieldSUHom h n φ g : gramSU h _) : GL (Fin n) K) = glAut φ g :=
  rfl

theorem exists_subfieldGL_eq_of_fixed {σ : K ≃+* K} {g : GL (Fin n) K} (hg : glAut σ g = g) :
    ∃ g₀ : GL (Fin n) (fixSubfield σ), subfieldGL (fixSubfield σ) n g₀ = g := by
  have hgi : glAut σ g⁻¹ = g⁻¹ := by rw [map_inv, hg]
  have hent : ∀ x : GL (Fin n) K, glAut σ x = x →
      ∀ i j, σ ((x : Matrix (Fin n) (Fin n) K) i j) = (x : Matrix (Fin n) (Fin n) K) i j := by
    intro x hx i j
    have h1 := congrArg (fun y : GL (Fin n) K => (y : Matrix (Fin n) (Fin n) K) i j) hx
    simpa only [coe_glAut, Matrix.map_apply] using h1
  let M : Matrix (Fin n) (Fin n) (fixSubfield σ) :=
    Matrix.of fun i j => ⟨(g : Matrix (Fin n) (Fin n) K) i j, hent g hg i j⟩
  let N : Matrix (Fin n) (Fin n) (fixSubfield σ) :=
    Matrix.of fun i j => ⟨((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) i j, hent _ hgi i j⟩
  have hM : M.map (fixSubfield σ).subtype = g := Matrix.ext fun _ _ => rfl
  have hN : N.map (fixSubfield σ).subtype = ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) :=
    Matrix.ext fun _ _ => rfl
  have hinj := Matrix.map_injective (m := Fin n) (n := Fin n)
    (f := ((fixSubfield σ).subtype : fixSubfield σ → K)) Subtype.val_injective
  have hMN : M * N = 1 := hinj (by
    change (M * N).map (fixSubfield σ).subtype = (1 : Matrix (Fin n) (Fin n) (fixSubfield σ)).map
      (fixSubfield σ).subtype
    rw [Matrix.map_mul, hM, hN, Matrix.map_one _ (map_zero _) (map_one _), ← Units.val_mul,
      mul_inv_cancel, Units.val_one])
  have hNM : N * M = 1 := hinj (by
    change (N * M).map (fixSubfield σ).subtype = (1 : Matrix (Fin n) (Fin n) (fixSubfield σ)).map
      (fixSubfield σ).subtype
    rw [Matrix.map_mul, hM, hN, Matrix.map_one _ (map_zero _) (map_one _), ← Units.val_mul,
      inv_mul_cancel, Units.val_one])
  exact ⟨⟨M, N, hMN, hNM⟩, Units.ext hM⟩

variable {e : ℕ} {k : Subfield K} (h₀ : UnitaryFieldData ℓ e k)
  (hbar : ∀ c : k, (h₀.bar c : K) = h.bar c)

include hbar in
theorem mem_gramSU_of_subfieldGL {g₀ : GL (Fin n) k}
    (hg : subfieldGL k n g₀ ∈ gramSU h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) :
    g₀ ∈ gramSU h₀ ((1 : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) := by
  obtain ⟨h1, h2⟩ := mem_gramSU.1 hg
  rw [Units.val_one, Matrix.mul_one, coe_subfieldGL, map_subtype_map_bar h h₀ hbar,
    ← transpose_map, ← Matrix.map_mul] at h1
  refine mem_gramSU.2 ⟨?_, ?_⟩
  · rw [Units.val_one, Matrix.mul_one]
    refine Matrix.map_injective (f := (k.subtype : k → K)) Subtype.val_injective ?_
    change (((g₀ : Matrix (Fin n) (Fin n) k).map h₀.bar)ᵀ * g₀).map k.subtype =
      (1 : Matrix (Fin n) (Fin n) k).map k.subtype
    rw [h1, Matrix.map_one _ (map_zero _) (map_one _)]
  · rw [coe_subfieldGL] at h2
    change (k.subtype.mapMatrix (g₀ : Matrix (Fin n) (Fin n) k)).det = 1 at h2
    rw [← RingHom.map_det] at h2
    exact Subtype.val_injective (h2.trans (OneMemClass.coe_one _).symm)

end Fixed

section Range

variable (h : UnitaryFieldData ℓ f K) (n : ℕ) {σ : K ≃+* K} {e : ℕ}
  (h₀ : UnitaryFieldData ℓ e (fixSubfield σ)) (hbar : ∀ c : fixSubfield σ, (h₀.bar c : K) = h.bar c)

theorem range_subfieldPSU_le :
    (subfieldPSU h h₀ hbar n).range ≤
      (primeFormFieldHom h (isPrimeFormGram_one (n := n)) σ).toMonoidHom.eqLocus
        (MonoidHom.id _) := by
  rintro _ ⟨x, rfl⟩
  induction x using QuotientGroup.induction_on with
  | H g =>
    change primeFormFieldAut h isPrimeFormGram_one σ (subfieldPSU h h₀ hbar n (g : primeFormP h₀ _))
      = subfieldPSU h h₀ hbar n (g : primeFormP h₀ _)
    rw [subfieldPSU_mk, primeFormFieldAut_mk]
    congr 1
    refine Subtype.ext (Units.ext (Matrix.ext fun i j => ?_))
    change σ ((((g : GL (Fin n) (fixSubfield σ)) : Matrix (Fin n) (Fin n) (fixSubfield σ)) i j :
      fixSubfield σ) : K) = (((g : GL (Fin n) (fixSubfield σ)) : Matrix (Fin n) (Fin n)
        (fixSubfield σ)) i j : K)
    exact ((((g : GL (Fin n) (fixSubfield σ)) : Matrix (Fin n) (Fin n) (fixSubfield σ)) i j).2)

theorem range_subfieldPSU [Finite K] {p : ℕ} (hp : p.Prime) (hσ : orderOf σ = p)
    (hZ : ¬p ∣ Nat.card (normOneScalars h
      (gramSU h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) n)) :
    (subfieldPSU h h₀ hbar n).range =
      (primeFormFieldHom h (isPrimeFormGram_one (n := n)) σ).toMonoidHom.eqLocus
        (MonoidHom.id _) := by
  classical
  refine le_antisymm (range_subfieldPSU_le h n h₀ hbar) fun x hx => ?_
  have hx' : primeFormFieldHom h (isPrimeFormGram_one (n := n)) σ x = x := hx
  have : Fact p.Prime := ⟨hp⟩
  have : Finite (K ≃+* K) := Finite.of_injective (fun φ : K ≃+* K => (φ : K → K))
    DFunLike.coe_injective
  have : Finite (GL (Fin n) K) := Finite.of_injective (fun g : GL (Fin n) K =>
    (g : Matrix (Fin n) (Fin n) K)) Units.val_injective
  set A := Subgroup.zpowers σ with hA
  have hpA : IsPGroup p A := IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hσ, pow_one])
  set α := (fieldSUHom h n).comp A.subtype with hα
  set N := normOneScalars h (gramSU h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) n with hN
  have hNinv : ∀ a : A, ∀ z ∈ N, α a z ∈ N := fun a z hz => by
    have h1 := map_normOneScalars_field h (isPrimeFormGram_one (n := n)) (a : K ≃+* K)
    rw [← hN] at h1
    rw [← h1]
    exact ⟨z, hz, rfl⟩
  have hlift := CFSG.Semidihedral.Principal.coprime_fixed_point_lifting p hpA α N hNinv hZ
  have hxfix : x ∈ {q | ∀ a : A,
      CFSG.Semidihedral.Principal.CoprimeFixedPoint.quotientAction α N hNinv a q = q} := by
    intro a
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 a.2
    have e1 : CFSG.Semidihedral.Principal.CoprimeFixedPoint.quotientAction α N hNinv a =
        primeFormFieldHom h (isPrimeFormGram_one (n := n)) (a : K ≃+* K) := by
      refine MulEquiv.ext fun q => ?_
      induction q using QuotientGroup.induction_on with
      | H g => rfl
    have hst : primeFormFieldHom h (isPrimeFormGram_one (n := n)) σ ∈
        MulAction.stabilizer (MulAut (primeFormP h
          ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))) x := by
      rw [MulAction.mem_stabilizer_iff, MulAut.smul_def]
      exact hx'
    have h1 := Subgroup.zpow_mem _ hst m
    rw [MulAction.mem_stabilizer_iff, MulAut.smul_def, ← map_zpow, hm] at h1
    rw [e1]
    exact h1
  rw [hlift] at hxfix
  obtain ⟨c, hc, rfl⟩ := hxfix
  have hcσ : glAut σ (c : GL (Fin n) K) = c :=
    congrArg Subtype.val (hc ⟨σ, Subgroup.mem_zpowers σ⟩)
  obtain ⟨g₀, hg₀⟩ := exists_subfieldGL_eq_of_fixed n hcσ
  have hg₀mem := mem_gramSU_of_subfieldGL h n h₀ hbar (g₀ := g₀) (by rw [hg₀]; exact c.2)
  refine ⟨((⟨g₀, hg₀mem⟩ : gramSU h₀ _) : primeFormP h₀ _), ?_⟩
  rw [subfieldPSU_mk, QuotientGroup.mk'_apply]
  congr 1
  exact Subtype.ext hg₀

end Range

section Groups

variable (h : UnitaryFieldData ℓ f K) {n : ℕ}

theorem card_normOneScalars_one (hn : 1 ≤ n) :
    Nat.card (normOneScalars h (gramSU h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) n) =
      Nat.gcd n (ℓ ^ f + 1) := by
  have e : gramSU h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = unitarySU ℓ f K n := by
    rw [Units.val_one]
    exact (unitarySU_eq_gramSU h n).symm
  rw [e]
  exact card_unitaryScalars h hn

theorem isPerfect_gramSU_one (hn : 3 ≤ n) (hnq : ¬(n = 3 ∧ ℓ ^ f = 2)) :
    Group.IsPerfect (gramSU h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) := by
  have := h.finite
  have : Fact ℓ.Prime := ⟨h.prime⟩
  have := h.charP
  have : Group.IsPerfect (CFSG.Assembly.LowTwoRank.StatedSU n (ℓ ^ f) K) :=
    CFSG.ClassicalGroups.Unitary.isPerfect_statedSU h.card_eq_sq hn
      fun e => hnq (Prod.mk_inj.1 e)
  have e : CFSG.Assembly.LowTwoRank.StatedSU n (ℓ ^ f) K =
      gramSU h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
    rw [Units.val_one]
    exact unitarySU_eq_gramSU h n
  exact Group.IsPerfect.ofSurjective (f := (MulEquiv.subgroupCongr e).toMonoidHom)
    (MulEquiv.surjective _)

theorem isSimpleGroup_primeFormP_one (hn : 3 ≤ n) (hnq : ¬(n = 3 ∧ ℓ ^ f = 2)) :
    IsSimpleGroup (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) := by
  have := h.finite
  have : Fact ℓ.Prime := ⟨h.prime⟩
  obtain ⟨e₁⟩ := nonempty_primeFormP_mulEquiv h (isPrimeFormGram_one (n := n) (K := K))
  have := CFSG.ClassicalGroups.Unitary.isSimpleGroup_statedProj_statedSU K ℓ f h.card_eq_sq n hn
    fun e => hnq (Prod.mk_inj.1 e)
  exact (e₁.trans (unitaryPSUEquiv h (by omega))).isSimpleGroup

theorem not_commute_primeFormP_one (hn : 3 ≤ n) (hnq : ¬(n = 3 ∧ ℓ ^ f = 2)) :
    ¬∀ x y : primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K), x * y = y * x := by
  intro hc
  have := isSimpleGroup_primeFormP_one h hn hnq
  have := isPerfect_gramSU_one h hn hnq
  have : Group.IsPerfect (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) :=
    Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _)
  exact Group.IsPerfect.not_isMulCommutative _ ⟨⟨hc⟩⟩

end Groups

section Elements

variable {L : Type} [Field L] {n : ℕ}

@[expose] def unitaryDiagGL (d : Fin n → Lˣ) : GL (Fin n) L :=
  ⟨Matrix.diagonal fun i => (d i : L), Matrix.diagonal fun i => ((d i)⁻¹ : Lˣ),
    by rw [diagonal_mul_diagonal, ← diagonal_one]; congr 1; funext i; exact (d i).mul_inv,
    by rw [diagonal_mul_diagonal, ← diagonal_one]; congr 1; funext i; exact (d i).inv_mul⟩

theorem coe_unitaryDiagGL (d : Fin n → Lˣ) :
    ((unitaryDiagGL d : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) =
      Matrix.diagonal fun i => (d i : L) :=
  rfl

@[expose] def unitaryPermGL (π : Equiv.Perm (Fin n)) : GL (Fin n) L :=
  ⟨π.permMatrix L, (π⁻¹).permMatrix L,
    by rw [← Matrix.permMatrix_mul, inv_mul_cancel, Matrix.permMatrix_one],
    by rw [← Matrix.permMatrix_mul, mul_inv_cancel, Matrix.permMatrix_one]⟩

theorem coe_unitaryPermGL (π : Equiv.Perm (Fin n)) :
    ((unitaryPermGL π : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = π.permMatrix L :=
  rfl

theorem permMatrix_apply' (π : Equiv.Perm (Fin n)) (a b : Fin n) :
    (π.permMatrix L) a b = if π a = b then 1 else 0 := by
  rw [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply]
  simp only [Equiv.toPEquiv_apply, Option.mem_def, Option.some.injEq]

variable {e : ℕ} (h₀ : UnitaryFieldData ℓ e L)

theorem unitaryDiagGL_mem_gramSU {d : Fin n → Lˣ} (hd : ∀ i, h₀.norm (d i : L) = 1)
    (hdet : ∏ i, (d i : L) = 1) :
    unitaryDiagGL d ∈ gramSU h₀ ((1 : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) := by
  refine mem_gramSU.2 ⟨?_, ?_⟩
  · rw [Units.val_one, Matrix.mul_one, coe_unitaryDiagGL, diagonal_map (map_zero _),
      diagonal_transpose, diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext i
    rw [mul_comm]
    exact hd i
  · rw [coe_unitaryDiagGL, det_diagonal, hdet]

theorem unitaryPermGL_mem_gramSU {π : Equiv.Perm (Fin n)} (hπ : Equiv.Perm.sign π = 1) :
    unitaryPermGL π ∈ gramSU h₀ ((1 : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) := by
  have hmap : (π.permMatrix L).map h₀.bar = π.permMatrix L := Matrix.ext fun a b => by
    rw [Matrix.map_apply, permMatrix_apply']
    split_ifs <;> simp
  refine mem_gramSU.2 ⟨?_, ?_⟩
  · rw [Units.val_one, Matrix.mul_one, coe_unitaryPermGL, hmap, Matrix.transpose_permMatrix,
      ← Matrix.permMatrix_mul, mul_inv_cancel, Matrix.permMatrix_one]
  · rw [coe_unitaryPermGL, Matrix.det_permutation, hπ, Units.val_one, Int.cast_one]

theorem pairDiag_norm_prod {v : Lˣ} (hv : h₀.norm (v : L) = 1) (b c : Fin n) :
    (∀ i, h₀.norm (((Pi.mulSingle b v * Pi.mulSingle c v⁻¹ : Fin n → Lˣ) i : Lˣ) : L) = 1) ∧
      ∏ i, (((Pi.mulSingle b v * Pi.mulSingle c v⁻¹ : Fin n → Lˣ) i : Lˣ) : L) = 1 := by
  have hv' : h₀.norm ((v⁻¹ : Lˣ) : L) = 1 := by
    rw [Units.val_inv_eq_inv_val, norm_inv_eq h₀, hv, inv_one]
  have h1 : h₀.norm (1 : L) = 1 := by rw [UnitaryFieldData.norm, map_one, mul_one]
  refine ⟨fun i => ?_, ?_⟩
  · rw [Pi.mul_apply, Units.val_mul, norm_mul_eq h₀]
    have ha : h₀.norm (((Pi.mulSingle b v : Fin n → Lˣ) i : Lˣ) : L) = 1 := by
      by_cases hi : i = b
      · rw [hi, Pi.mulSingle_eq_same, hv]
      · rw [Pi.mulSingle_eq_of_ne hi, Units.val_one, h1]
    have hb : h₀.norm (((Pi.mulSingle c v⁻¹ : Fin n → Lˣ) i : Lˣ) : L) = 1 := by
      by_cases hi : i = c
      · rw [hi, Pi.mulSingle_eq_same, hv']
      · rw [Pi.mulSingle_eq_of_ne hi, Units.val_one, h1]
    rw [ha, hb, one_mul]
  · rw [← Units.coe_prod]
    simp only [Pi.mul_apply]
    rw [Finset.prod_mul_distrib, Fintype.prod_pi_mulSingle', Fintype.prod_pi_mulSingle',
      mul_inv_cancel, Units.val_one]

theorem exists_fin_ne_ne (hn : 3 ≤ n) (a b : Fin n) : ∃ c : Fin n, c ≠ a ∧ c ≠ b := by
  by_contra hc
  push Not at hc
  have h0 := hc ⟨0, by omega⟩
  have h1 := hc ⟨1, by omega⟩
  have h2 := hc ⟨2, by omega⟩
  simp only [ne_eq, Fin.ext_iff] at h0 h1 h2
  omega

end Elements

section Centralizer

variable (h : UnitaryFieldData ℓ f K) (n : ℕ) {σ : K ≃+* K} {e : ℕ}
  (h₀ : UnitaryFieldData ℓ e (fixSubfield σ))
  (hbar : ∀ c : fixSubfield σ, (h₀.bar c : K) = h.bar c)

theorem primeFormConjHom_scalar (c : Kˣ)
    (hc : GeneralLinearGroup.scalar (Fin n) c ∈
      primeFormUnitary h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) :
    primeFormConjHom h _ ⟨_, hc⟩ = 1 := by
  refine MulEquiv.ext fun x => QuotientGroup.induction_on x fun g => ?_
  rw [primeFormConjHom_mk, MulAut.one_apply]
  congr 1
  refine Subtype.ext ?_
  change GeneralLinearGroup.scalar (Fin n) c * (g : GL (Fin n) K) *
    (GeneralLinearGroup.scalar (Fin n) c)⁻¹ = g
  rw [← (commute_scalar c (g : GL (Fin n) K)).eq, mul_inv_cancel_right]

theorem primeFormFieldHom_apply_of_mem_range {τ : K ≃+* K} (hτ : ∀ c ∈ fixSubfield σ, τ c = c)
    {x : primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)}
    (hx : x ∈ (subfieldPSU h h₀ hbar n).range) :
    primeFormFieldHom h (isPrimeFormGram_one (n := n)) τ x = x := by
  obtain ⟨y, rfl⟩ := hx
  induction y using QuotientGroup.induction_on with
  | H g =>
    change primeFormFieldAut h isPrimeFormGram_one τ
      (subfieldPSU h h₀ hbar n (g : primeFormP h₀ _)) =
        subfieldPSU h h₀ hbar n (g : primeFormP h₀ _)
    rw [subfieldPSU_mk, primeFormFieldAut_mk]
    congr 1
    refine Subtype.ext (Units.ext (Matrix.ext fun i j => ?_))
    exact hτ _ ((((g : GL (Fin n) (fixSubfield σ)) : Matrix (Fin n) (Fin n) (fixSubfield σ))
      i j).2)

theorem eq_primeFormFieldHom_of_fix [Finite K] (hn : 3 ≤ n) (hq : ¬(n = 3 ∧ ℓ ^ f = 2))
    (hq₀ : ¬(n = 3 ∧ ℓ ^ e = 2))
    (β : MulAut (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)))
    (hβ : ∀ x ∈ (subfieldPSU h h₀ hbar n).range, β x = x) :
    ∃ τ : K ≃+* K, (∀ c ∈ fixSubfield σ, τ c = c) ∧
      β = primeFormFieldHom h (isPrimeFormGram_one (n := n)) τ := by
  classical
  have hC : IsPrimeFormGram (1 : GL (Fin n) K) := isPrimeFormGram_one
  have : Finite (fixSubfield σ) := Subtype.finite
  obtain ⟨τ, ⟨M, hM⟩, -⟩ := (unitary_prime_form_full_semilinear_realization h hC hn hq).2.2.2.2.1 β
  have hcen : ∀ g : gramSU h₀ ((1 : GL (Fin n) (fixSubfield σ)) :
      Matrix (Fin n) (Fin n) (fixSubfield σ)),
      (M : GL (Fin n) K) * glAut τ (subfieldGL _ n (g : GL (Fin n) (fixSubfield σ))) *
        (M : GL (Fin n) K)⁻¹ * (subfieldGL _ n (g : GL (Fin n) (fixSubfield σ)))⁻¹ ∈
          Subgroup.center (GL (Fin n) K) := by
    intro g
    have h1 := hβ _ ⟨(g : primeFormP h₀ _), rfl⟩
    rw [hM, subfieldPSU_mk] at h1
    change primeFormConjAut h _ M (primeFormFieldAut h hC τ
      ((subfieldSU h h₀ hbar n g : gramSU h _) : primeFormP h _)) =
        ((subfieldSU h h₀ hbar n g : gramSU h _) : primeFormP h _) at h1
    rw [primeFormFieldAut_mk, primeFormConjAut_mk, QuotientGroup.eq] at h1
    obtain ⟨c, -, -, hc⟩ := h1
    set A : GL (Fin n) K := (M : GL (Fin n) K) *
      glAut τ (subfieldGL _ n (g : GL (Fin n) (fixSubfield σ))) * (M : GL (Fin n) K)⁻¹ with hA
    set B : GL (Fin n) K := subfieldGL _ n (g : GL (Fin n) (fixSubfield σ)) with hB
    have hAB : A⁻¹ * B = GeneralLinearGroup.scalar (Fin n) c := hc
    have hBA : B = A * GeneralLinearGroup.scalar (Fin n) c := by rw [← hAB]; group
    have hs : Commute A (GeneralLinearGroup.scalar (Fin n) c)⁻¹ :=
      (commute_scalar c A).inv_right
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
    refine ⟨c⁻¹, ?_⟩
    calc GeneralLinearGroup.scalar (Fin n) c⁻¹ = (GeneralLinearGroup.scalar (Fin n) c)⁻¹ :=
          map_inv _ _
      _ = (GeneralLinearGroup.scalar (Fin n) c)⁻¹ * A * A⁻¹ := by group
      _ = A * (GeneralLinearGroup.scalar (Fin n) c)⁻¹ * A⁻¹ := by rw [← hs.eq]
      _ = A * B⁻¹ := by rw [hBA]; group
  let z : gramSU h₀ ((1 : GL (Fin n) (fixSubfield σ)) : Matrix (Fin n) (Fin n) (fixSubfield σ)) →*
      Subgroup.center (GL (Fin n) K) :=
    { toFun := fun g => ⟨_, hcen g⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun g₁ g₂ => Subtype.ext (by
        have hz := Subgroup.mem_center_iff.1 (hcen g₂)
          (subfieldGL _ n (g₁ : GL (Fin n) (fixSubfield σ)))⁻¹
        change (M : GL (Fin n) K) * glAut τ (subfieldGL _ n ((g₁ * g₂ : gramSU h₀ _) :
          GL (Fin n) (fixSubfield σ))) * (M : GL (Fin n) K)⁻¹ * (subfieldGL _ n
            ((g₁ * g₂ : gramSU h₀ _) : GL (Fin n) (fixSubfield σ)))⁻¹ =
          ((M : GL (Fin n) K) * glAut τ (subfieldGL _ n (g₁ : GL (Fin n) (fixSubfield σ))) *
            (M : GL (Fin n) K)⁻¹ * (subfieldGL _ n (g₁ : GL (Fin n) (fixSubfield σ)))⁻¹) *
          ((M : GL (Fin n) K) * glAut τ (subfieldGL _ n (g₂ : GL (Fin n) (fixSubfield σ))) *
            (M : GL (Fin n) K)⁻¹ * (subfieldGL _ n (g₂ : GL (Fin n) (fixSubfield σ)))⁻¹)
        rw [Subgroup.coe_mul, map_mul, map_mul]
        calc _ = ((M : GL (Fin n) K) * glAut τ (subfieldGL _ n (g₁ : GL (Fin n) (fixSubfield σ))) *
              (M : GL (Fin n) K)⁻¹) * (((M : GL (Fin n) K) *
                glAut τ (subfieldGL _ n (g₂ : GL (Fin n) (fixSubfield σ))) *
                  (M : GL (Fin n) K)⁻¹ * (subfieldGL _ n (g₂ : GL (Fin n) (fixSubfield σ)))⁻¹) *
                (subfieldGL _ n (g₁ : GL (Fin n) (fixSubfield σ)))⁻¹) := by group
          _ = _ := by rw [← hz]; group) }
  have hperf := isPerfect_gramSU_one h₀ hn hq₀
  have hz1 : ∀ g, z g = 1 := by
    have hle : commutator (gramSU h₀ ((1 : GL (Fin n) (fixSubfield σ)) :
        Matrix (Fin n) (Fin n) (fixSubfield σ))) ≤ z.ker := by
      rw [commutator_def, Subgroup.commutator_le]
      intro a _ b _
      rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact Subtype.ext (Subgroup.mem_center_iff.1 (z b).2 (z a))
    intro g
    exact hle (by rw [hperf.commutator_eq_top]; exact Subgroup.mem_top g)
  have hS1 : ∀ g : gramSU h₀ ((1 : GL (Fin n) (fixSubfield σ)) :
      Matrix (Fin n) (Fin n) (fixSubfield σ)),
      (M : GL (Fin n) K) * glAut τ (subfieldGL _ n (g : GL (Fin n) (fixSubfield σ))) =
        subfieldGL _ n (g : GL (Fin n) (fixSubfield σ)) * (M : GL (Fin n) K) := by
    intro g
    have h1 : (M : GL (Fin n) K) * glAut τ (subfieldGL _ n (g : GL (Fin n) (fixSubfield σ))) *
        (M : GL (Fin n) K)⁻¹ * (subfieldGL _ n (g : GL (Fin n) (fixSubfield σ)))⁻¹ = 1 :=
      congrArg Subtype.val (hz1 g)
    calc (M : GL (Fin n) K) * glAut τ (subfieldGL _ n (g : GL (Fin n) (fixSubfield σ))) =
        ((M : GL (Fin n) K) * glAut τ (subfieldGL _ n (g : GL (Fin n) (fixSubfield σ))) *
          (M : GL (Fin n) K)⁻¹ * (subfieldGL _ n (g : GL (Fin n) (fixSubfield σ)))⁻¹) *
            subfieldGL _ n (g : GL (Fin n) (fixSubfield σ)) * (M : GL (Fin n) K) := by group
      _ = _ := by rw [h1, one_mul]
  have hdiag : ∀ d : Fin n → (fixSubfield σ)ˣ, (∀ i, h₀.norm (d i : fixSubfield σ) = 1) →
      ∏ i, (d i : fixSubfield σ) = 1 → ∀ a b,
        ((M : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) a b * τ ((d b : fixSubfield σ) : K) =
          ((d a : fixSubfield σ) : K) * ((M : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) a b := by
    intro d hd hdet a b
    set g : gramSU h₀ ((1 : GL (Fin n) (fixSubfield σ)) : Matrix (Fin n) (Fin n) (fixSubfield σ)) :=
      ⟨unitaryDiagGL d, unitaryDiagGL_mem_gramSU h₀ hd hdet⟩ with hg
    have e1 : ((subfieldGL _ n (g : GL (Fin n) (fixSubfield σ)) : GL (Fin n) K) :
        Matrix (Fin n) (Fin n) K) = diagonal fun i => ((d i : fixSubfield σ) : K) := by
      rw [coe_subfieldGL]
      change ((unitaryDiagGL d : GL (Fin n) (fixSubfield σ)) :
        Matrix (Fin n) (Fin n) (fixSubfield σ)).map _ = _
      rw [coe_unitaryDiagGL, diagonal_map (map_zero _)]
      rfl
    have e2 : ((glAut τ (subfieldGL _ n (g : GL (Fin n) (fixSubfield σ))) : GL (Fin n) K) :
        Matrix (Fin n) (Fin n) K) = diagonal fun i => τ ((d i : fixSubfield σ) : K) := by
      rw [coe_glAut, e1, diagonal_map (map_zero _)]
    have h1 := congrArg (fun x : GL (Fin n) K => (x : Matrix (Fin n) (Fin n) K) a b) (hS1 g)
    rw [Units.val_mul, Units.val_mul, e1, e2, Matrix.mul_diagonal, Matrix.diagonal_mul] at h1
    exact h1
  obtain ⟨-, -, hcardker, -⟩ := unitary_field_norm h₀
  have : Finite (Units.map h₀.normHom).ker := Subtype.finite
  have hnt : Nontrivial (Units.map h₀.normHom).ker := by
    rw [← Finite.one_lt_card_iff_nontrivial, hcardker]
    have := h₀.one_lt_pow
    omega
  obtain ⟨⟨v₁, hv₁⟩, hv₁1⟩ := exists_ne (1 : (Units.map h₀.normHom).ker)
  have hv₁N : h₀.norm (v₁ : fixSubfield σ) = 1 := (UnitaryFieldData.mem_ker_normUnits h₀).1 hv₁
  have hv₁ne : v₁ ≠ 1 := fun h1 => hv₁1 (Subtype.ext h1)
  have hoff : ∀ a b, a ≠ b → ((M : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) a b = 0 := by
    intro a b hab
    obtain ⟨c, hca, hcb⟩ := exists_fin_ne_ne hn a b
    obtain ⟨hd, hdet⟩ := pairDiag_norm_prod h₀ hv₁N b c
    have h1 := hdiag _ hd hdet a b
    have hdb : (Pi.mulSingle b v₁ * Pi.mulSingle c v₁⁻¹ : Fin n → (fixSubfield σ)ˣ) b = v₁ := by
      rw [Pi.mul_apply, Pi.mulSingle_eq_same, Pi.mulSingle_eq_of_ne hcb.symm, mul_one]
    have hda : (Pi.mulSingle b v₁ * Pi.mulSingle c v₁⁻¹ : Fin n → (fixSubfield σ)ˣ) a = 1 := by
      rw [Pi.mul_apply, Pi.mulSingle_eq_of_ne hab, Pi.mulSingle_eq_of_ne hca.symm, mul_one]
    rw [hdb, hda] at h1
    simp only [Units.val_one, OneMemClass.coe_one, one_mul] at h1
    have hτv : τ ((v₁ : fixSubfield σ) : K) ≠ 1 := by
      intro h2
      apply hv₁ne
      have h3 : ((v₁ : fixSubfield σ) : K) = 1 := by
        rw [← map_one τ] at h2
        exact τ.injective h2
      exact Units.ext (Subtype.ext h3)
    have h4 : ((M : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) a b *
        (τ ((v₁ : fixSubfield σ) : K) - 1) = 0 := by
      rw [mul_sub, mul_one, h1, sub_self]
    exact (mul_eq_zero.1 h4).resolve_right (sub_ne_zero.2 hτv)
  have hMd : ((M : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      Matrix.diagonal fun a => ((M : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) a a := by
    ext a b
    rw [diagonal_apply]
    split_ifs with hab
    · rw [hab]
    · exact hoff a b hab
  have hM0 : ∀ a, ((M : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) a a ≠ 0 := by
    have hdet : ((M : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).det ≠ 0 :=
      ((Matrix.isUnit_iff_isUnit_det _).1 (M : GL (Fin n) K).isUnit).ne_zero
    rw [hMd, det_diagonal] at hdet
    exact fun a => Finset.prod_ne_zero_iff.1 hdet a (Finset.mem_univ a)
  set a₀ : Fin n := ⟨0, by omega⟩ with ha₀
  set b₀ : Fin n := ⟨1, by omega⟩ with hb₀
  have hab₀ : a₀ ≠ b₀ := fun h0 => Nat.zero_ne_one (Fin.mk.inj_iff.1 h0)
  have hτnorm : ∀ v : (fixSubfield σ)ˣ, h₀.norm (v : fixSubfield σ) = 1 →
      τ ((v : fixSubfield σ) : K) = (v : fixSubfield σ) := by
    intro v hv
    obtain ⟨hd, hdet⟩ := pairDiag_norm_prod h₀ hv a₀ b₀
    have h1 := hdiag _ hd hdet a₀ a₀
    have hda : (Pi.mulSingle a₀ v * Pi.mulSingle b₀ v⁻¹ : Fin n → (fixSubfield σ)ˣ) a₀ = v := by
      rw [Pi.mul_apply, Pi.mulSingle_eq_same, Pi.mulSingle_eq_of_ne hab₀, mul_one]
    rw [hda] at h1
    have h2 : ((M : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) a₀ a₀ *
        (τ ((v : fixSubfield σ) : K) - (v : fixSubfield σ)) = 0 := by
      rw [mul_sub, h1, mul_comm, sub_self]
    exact sub_eq_zero.1 ((mul_eq_zero.1 h2).resolve_left (hM0 a₀))
  have hτ₀ : fixSubfieldRestrict τ σ = 1 := by
    by_contra hne
    have : Finite (fixSubfield σ ≃+* fixSubfield σ) :=
      Finite.of_injective (fun φ : fixSubfield σ ≃+* fixSubfield σ => (φ : fixSubfield σ →
        fixSubfield σ)) DFunLike.coe_injective
    obtain ⟨-, hcard⟩ := CFSG.RankThree.Chevalley.SteinbergBT.card_fixSubfield h₀.prime
      (by have := h₀.one_le; omega) h₀.card (fixSubfieldRestrict τ σ)
    have hord : 2 ≤ orderOf (fixSubfieldRestrict τ σ) := by
      have h1 : orderOf (fixSubfieldRestrict τ σ) ≠ 1 := fun h1 => hne (orderOf_eq_one_iff.1 h1)
      have h0 := orderOf_pos (fixSubfieldRestrict τ σ)
      omega
    have hle : Nat.card (fixSubfield (fixSubfieldRestrict τ σ)) ≤ ℓ ^ e := by
      rw [hcard]
      exact Nat.pow_le_pow_right h₀.prime.pos (Nat.div_le_of_le_mul (by nlinarith))
    have hinj : Nat.card (Units.map h₀.normHom).ker ≤
        Nat.card (fixSubfield (fixSubfieldRestrict τ σ)) := by
      refine Nat.card_le_card_of_injective (fun u => ⟨((u : (fixSubfield σ)ˣ) : fixSubfield σ),
        (mem_fixSubfield (fixSubfieldRestrict τ σ)).2 (Subtype.ext (by
          rw [coe_fixSubfieldRestrict]
          exact hτnorm u ((UnitaryFieldData.mem_ker_normUnits h₀).1 u.2)))⟩) ?_
      intro u₁ u₂ h12
      exact Subtype.ext (Units.ext (congrArg Subtype.val h12))
    rw [hcardker] at hinj
    omega
  have hτK₀ : ∀ c ∈ fixSubfield σ, τ c = c := fun c hc => by
    have h1 := congrArg (fun ψ : fixSubfield σ ≃+* fixSubfield σ =>
      ((ψ ⟨c, hc⟩ : fixSubfield σ) : K)) hτ₀
    exact h1
  have hconst : ∀ a b, ((M : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) a a =
      ((M : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) b b := by
    intro a b
    by_cases hab : a = b
    · rw [hab]
    obtain ⟨c, hca, hcb⟩ := exists_fin_ne_ne hn a b
    set π : Equiv.Perm (Fin n) := Equiv.swap b c * Equiv.swap c a with hπ
    have hπa : π a = b := by
      rw [hπ, Equiv.Perm.mul_apply, Equiv.swap_apply_right, Equiv.swap_apply_right]
    have hsign : Equiv.Perm.sign π = 1 := by
      rw [hπ, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap (Ne.symm hcb),
        Equiv.Perm.sign_swap hca]
      decide
    have h1 := hS1 ⟨unitaryPermGL π, unitaryPermGL_mem_gramSU h₀ hsign⟩
    have hτg : glAut τ (subfieldGL _ n (unitaryPermGL π)) = subfieldGL _ n (unitaryPermGL π) :=
      Units.ext (Matrix.ext fun i j => hτK₀ _ ((((unitaryPermGL π : GL (Fin n) (fixSubfield σ)) :
        Matrix (Fin n) (Fin n) (fixSubfield σ)) i j).2))
    change (M : GL (Fin n) K) * glAut τ (subfieldGL _ n (unitaryPermGL π)) =
      subfieldGL _ n (unitaryPermGL π) * (M : GL (Fin n) K) at h1
    rw [hτg] at h1
    have h2 := congrArg (fun x : GL (Fin n) K => (x : Matrix (Fin n) (Fin n) K) a b) h1
    simp only [Units.val_mul] at h2
    rw [hMd, Matrix.diagonal_mul, Matrix.mul_diagonal, coe_subfieldGL, coe_unitaryPermGL,
      Matrix.map_apply, permMatrix_apply', ite_eq_left hπa] at h2
    simpa using h2
  have hm0 := hM0 a₀
  have hMs : (M : GL (Fin n) K) = GeneralLinearGroup.scalar (Fin n)
      (Units.mk0 (((M : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) a₀ a₀) hm0) := by
    refine Units.ext ?_
    rw [GeneralLinearGroup.coe_scalar, scalar_apply, Units.val_mk0, hMd]
    congr 1
    funext a
    exact hconst a a₀
  refine ⟨τ, hτK₀, ?_⟩
  have hMeq : M = ⟨_, hMs ▸ M.2⟩ := Subtype.ext hMs
  rw [hM, hMeq, primeFormConjHom_scalar, one_mul]

end Centralizer

section Assembly

variable (h : UnitaryFieldData ℓ f K) (n : ℕ) {σ : K ≃+* K} {e : ℕ}
  (h₀ : UnitaryFieldData ℓ e (fixSubfield σ))
  (hbar : ∀ c : fixSubfield σ, (h₀.bar c : K) = h.bar c)

theorem fixingSubgroup_fixSubfield [Finite K] (σ : K ≃+* K) :
    fixingSubgroup (K ≃+* K) (fixSubfield σ : Set K) = Subgroup.zpowers σ := by
  ext τ
  rw [mem_fixingSubgroup_iff]
  constructor
  · intro hτ
    refine CFSG.ComponentClassification.UnbalancedCatalog.mem_zpowers_of_fixed fun x hx => ?_
    have h1 := hτ x hx
    rwa [RingAut.smul_def] at h1
  · intro hτ x hx
    rw [RingAut.smul_def]
    have hst : σ ∈ MulAction.stabilizer (K ≃+* K) x := by
      rw [MulAction.mem_stabilizer_iff, RingAut.smul_def]
      exact hx
    have h1 := Subgroup.zpowers_le.2 hst hτ
    rwa [MulAction.mem_stabilizer_iff, RingAut.smul_def] at h1

theorem primeFormFieldHom_injective [Finite K] (hn : 3 ≤ n) (hq : ¬(n = 3 ∧ ℓ ^ f = 2)) :
    Function.Injective (primeFormFieldHom h (isPrimeFormGram_one (n := n) (K := K))) := by
  intro φ ψ hφψ
  have hfac :=
    (unitary_prime_form_full_semilinear_realization h isPrimeFormGram_one hn hq).2.2.2.2.2.1
  have h1 := hfac 1 φ
  have h2 := hfac 1 ψ
  rw [map_one, one_mul] at h1 h2
  rw [← h1, ← h2, hφψ]

theorem fixingSubgroup_range_subfieldPSU [Finite K] (hn : 3 ≤ n) (hq : ¬(n = 3 ∧ ℓ ^ f = 2))
    (hq₀ : ¬(n = 3 ∧ ℓ ^ e = 2)) :
    fixingSubgroup (MulAut (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)))
        ((subfieldPSU h h₀ hbar n).range :
          Set (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))) =
      (fixingSubgroup (K ≃+* K) (fixSubfield σ : Set K)).map
        (primeFormFieldHom h (isPrimeFormGram_one (n := n))) ∧
    (fixingSubgroup (K ≃+* K) (fixSubfield σ : Set K)).map
        (primeFormFieldHom h (isPrimeFormGram_one (n := n))) =
      Subgroup.zpowers (primeFormFieldHom h (isPrimeFormGram_one (n := n)) σ) ∧
    Nat.card (Subgroup.zpowers (primeFormFieldHom h (isPrimeFormGram_one (n := n)) σ)) =
      orderOf σ := by
  refine ⟨le_antisymm (fun β hβ => ?_) ?_, ?_, ?_⟩
  · have hfix : ∀ x ∈ (subfieldPSU h h₀ hbar n).range, β x = x := fun x hx => by
      have h1 := (mem_fixingSubgroup_iff _).1 hβ x hx
      rwa [MulAut.smul_def] at h1
    obtain ⟨τ, hτ, rfl⟩ := eq_primeFormFieldHom_of_fix h n h₀ hbar hn hq hq₀ β hfix
    refine ⟨τ, (mem_fixingSubgroup_iff _).2 fun c hc => ?_, rfl⟩
    rw [RingAut.smul_def]
    exact hτ c hc
  · rintro _ ⟨τ, hτ, rfl⟩
    refine (mem_fixingSubgroup_iff _).2 fun x hx => ?_
    rw [MulAut.smul_def]
    exact primeFormFieldHom_apply_of_mem_range h n h₀ hbar (fun c hc => by
      have h1 := (mem_fixingSubgroup_iff _).1 hτ c hc
      rwa [RingAut.smul_def] at h1) hx
  · rw [fixingSubgroup_fixSubfield, MonoidHom.map_zpowers]
  · rw [Nat.card_zpowers, orderOf_injective _ (primeFormFieldHom_injective h n hn hq) σ]

theorem card_primeFormP_three_two (hq : ℓ ^ f = 2) :
    Nat.card (primeFormP h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) = 72 := by
  have := h.finite
  have hB := gramForm_isSymm h (G := (1 : Matrix (Fin 3) (Fin 3) K)) (by
    rw [Matrix.map_one _ (map_zero h.bar) (map_one h.bar), transpose_one])
  have hBl := gramForm_separatingLeft h (G := (1 : Matrix (Fin 3) (Fin 3) K)) (by simp)
  have hdim : Module.finrank K (Fin 3 → K) = 3 := Module.finrank_fin_fun K
  have hS := (CFSG.LinearGroups.unitary_full_group_order h hB hBl hdim (by norm_num)).2.1
  rw [hq] at hS
  have hS' : Nat.card (gramSU h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) = 216 := by
    rw [Units.val_one, card_gramSU]
    have h1 : ((2 : ℕ) : ℤ) ^ (3 * (3 - 1) / 2) * ∏ i ∈ Finset.Icc 2 3,
        (((2 : ℕ) : ℤ) ^ i - (-1) ^ i) = 216 := by decide
    exact_mod_cast hS.trans h1
  have hZ := card_normOneScalars_one h (n := 3) (by norm_num)
  rw [hq] at hZ
  have h3 := Subgroup.card_eq_card_quotient_mul_card_subgroup
    (normOneScalars h (gramSU h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) 3)
  rw [hS', hZ] at h3
  change 216 = Nat.card (primeFormP h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) *
    Nat.gcd 3 (2 + 1) at h3
  rw [show Nat.gcd 3 (2 + 1) = 3 by decide] at h3
  omega

theorem apply_eq_self_of_pow_eq_one [Finite K] {p : ℕ} (hp : p.Prime) (hσ : orderOf σ = p)
    (hn : 0 < n) (hnp : n < p) {c : K} (hc : c ^ n = 1) : σ c = c := by
  classical
  have hmem : ∀ i : ℕ, (σ ^ i) c ∈ Polynomial.nthRootsFinset n (1 : K) := fun i =>
    (Polynomial.mem_nthRootsFinset hn 1).2 (by rw [← map_pow, hc, map_one])
  have hcard : (Polynomial.nthRootsFinset n (1 : K)).card ≤ n := by
    rw [Polynomial.nthRootsFinset_def]
    exact (Multiset.toFinset_card_le _).trans (Polynomial.card_nthRoots n 1)
  obtain ⟨i, hi, j, hj, hij, heq⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to
    (s := Finset.range p) (t := Polynomial.nthRootsFinset n (1 : K))
    (by rw [Finset.card_range]; omega) (f := fun i => (σ ^ i) c) (fun i _ => hmem i)
  rw [Finset.mem_range] at hi hj
  have key : ∀ a b : ℕ, a < b → b < p → (σ ^ a) c = (σ ^ b) c → σ c = c := by
    intro a b hab hbp hab'
    have hm : (σ ^ (b - a)) c = c := by
      have e : σ ^ b = σ ^ a * σ ^ (b - a) := by rw [← pow_add]; congr 1; omega
      rw [e, RingAut.mul_apply] at hab'
      exact ((σ ^ a).injective hab').symm
    obtain ⟨r, hr⟩ := CFSG.RankThree.Chevalley.exists_mul_mod_eq_one hp (by omega : 0 < b - a)
      (by omega : b - a < p)
    have hσr : (σ ^ (b - a)) ^ r = σ := by
      rw [← pow_mul, mul_comm]
      exact CFSG.RankThree.Chevalley.pow_eq_self_of_mod_eq_one hσ hr
    have hst : σ ^ (b - a) ∈ MulAction.stabilizer (K ≃+* K) c := by
      rw [MulAction.mem_stabilizer_iff, RingAut.smul_def]
      exact hm
    have h1 := Subgroup.pow_mem _ hst r
    rw [hσr, MulAction.mem_stabilizer_iff, RingAut.smul_def] at h1
    exact h1
  rcases lt_or_gt_of_ne hij with hlt | hlt
  · exact key i j hlt hj heq
  · exact key j i hlt hi heq.symm

theorem map_subfieldSU_normOneScalars (hfix : ∀ c : K, c ^ n = 1 → σ c = c) :
    (normOneScalars h₀ (gramSU h₀ ((1 : GL (Fin n) (fixSubfield σ)) :
      Matrix (Fin n) (Fin n) (fixSubfield σ))) n).map (subfieldSU h h₀ hbar n) =
      normOneScalars h (gramSU h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) n := by
  refine le_antisymm ?_ fun z hz => ?_
  · rintro _ ⟨g, hg, rfl⟩
    exact subfieldSU_mem_normOneScalars h h₀ hbar n hg
  obtain ⟨c, hcN, hcn, hzc⟩ := hz
  have hcσ : σ (c : K) = c := hfix c (by rw [← Units.val_pow_eq_pow_val, hcn, Units.val_one])
  set c₀ : fixSubfield σ := ⟨c, hcσ⟩ with hc₀
  have hc₀0 : c₀ ≠ 0 := fun h0 => c.ne_zero (congrArg Subtype.val h0)
  set u : (fixSubfield σ)ˣ := Units.mk0 c₀ hc₀0 with hu
  have huN : h₀.norm (u : fixSubfield σ) = 1 := by
    apply Subtype.val_injective
    rw [Units.val_mk0, ← norm_subtype h h₀ hbar, hcN, OneMemClass.coe_one]
  have hun : u ^ n = 1 := by
    apply Units.ext
    apply Subtype.val_injective
    rw [Units.val_pow_eq_pow_val, Units.val_mk0, SubmonoidClass.coe_pow,
      ← Units.val_pow_eq_pow_val, hcn, Units.val_one, Units.val_one, OneMemClass.coe_one]
  have hsc : GeneralLinearGroup.scalar (Fin n) u = unitaryDiagGL fun _ => u := by
    refine Units.ext ?_
    rw [GeneralLinearGroup.coe_scalar, scalar_apply, coe_unitaryDiagGL]
  have hmem : GeneralLinearGroup.scalar (Fin n) u ∈ gramSU h₀ ((1 : GL (Fin n) (fixSubfield σ)) :
      Matrix (Fin n) (Fin n) (fixSubfield σ)) := by
    rw [hsc]
    refine unitaryDiagGL_mem_gramSU h₀ (fun _ => huN) ?_
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← Units.val_pow_eq_pow_val, hun,
      Units.val_one]
  refine ⟨⟨_, hmem⟩, ⟨u, huN, hun, rfl⟩, Subtype.ext ?_⟩
  rw [coe_subfieldSU, hzc]
  change subfieldGL _ n (GeneralLinearGroup.scalar (Fin n) u) = _
  rw [subfieldGL_scalar]
  congr 1
  exact Units.ext rfl

end Assembly

section Prime

variable (h : UnitaryFieldData ℓ f K) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {σ : K ≃+* K}
  (hσ : orderOf σ = p) (n : ℕ)

abbrev primeSubfieldScalars : Subgroup (gramSU (fixSubfield_unitaryFieldData h hp hp2 hσ)
    ((1 : GL (Fin n) (fixSubfield σ)) : Matrix (Fin n) (Fin n) (fixSubfield σ))) :=
  normOneScalars (fixSubfield_unitaryFieldData h hp hp2 hσ) _ n

abbrev primeSubfieldSU := subfieldSU h (fixSubfield_unitaryFieldData h hp hp2 hσ)
  (fixSubfield_unitaryFieldData_bar h hp hp2 hσ) n

abbrev primeSubfieldPSU := subfieldPSU h (fixSubfield_unitaryFieldData h hp hp2 hσ)
  (fixSubfield_unitaryFieldData_bar h hp hp2 hσ) n

abbrev fieldFixedPSU (σ : K ≃+* K) :
    Subgroup (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) :=
  (primeFormFieldHom h (isPrimeFormGram_one (n := n)) σ).toMonoidHom.eqLocus (MonoidHom.id _)

theorem prime_subfield_fixed_group_package (hn : 3 ≤ n) (hq : ¬(n = 3 ∧ ℓ ^ f = 2))
    (hZ : ¬p ∣ Nat.card (normOneScalars h
      (gramSU h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) n)) :
    p ∣ f ∧ Nat.card (fixSubfield σ) = (ℓ ^ (f / p)) ^ 2 ∧
      (∀ c : fixSubfield σ, h.bar c = (c : K) ^ ℓ ^ (f / p)) ∧
      ((QuotientGroup.mk' (normOneScalars h
        (gramSU h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) n)).comp
          (primeSubfieldSU h hp hp2 hσ n)).ker = primeSubfieldScalars h hp hp2 hσ n ∧
      (normOneScalars h (gramSU h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) n).comap
          (primeSubfieldSU h hp hp2 hσ n) = primeSubfieldScalars h hp hp2 hσ n ∧
      Function.Injective (primeSubfieldPSU h hp hp2 hσ n) ∧
      (primeSubfieldPSU h hp hp2 hσ n).range = fieldFixedPSU h n σ ∧
      Nat.card (normOneScalars h (gramSU h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) n) =
        Nat.gcd n (ℓ ^ f + 1) ∧
      Nat.card (primeSubfieldScalars h hp hp2 hσ n) = Nat.gcd n (ℓ ^ (f / p) + 1) ∧
      (¬(n = 3 ∧ ℓ ^ (f / p) = 2) →
        IsSimpleGroup (fieldFixedPSU h n σ) ∧ (¬∀ x y : fieldFixedPSU h n σ, x * y = y * x) ∧
        fixingSubgroup (MulAut (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)))
            (fieldFixedPSU h n σ : Set (primeFormP h
              ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))) =
          (fixingSubgroup (K ≃+* K) (fixSubfield σ : Set K)).map
            (primeFormFieldHom h (isPrimeFormGram_one (n := n))) ∧
        (fixingSubgroup (K ≃+* K) (fixSubfield σ : Set K)).map
            (primeFormFieldHom h (isPrimeFormGram_one (n := n))) =
          Subgroup.zpowers (primeFormFieldHom h (isPrimeFormGram_one (n := n)) σ) ∧
        Nat.card (Subgroup.zpowers (primeFormFieldHom h (isPrimeFormGram_one (n := n)) σ)) = p) ∧
      (n = 3 ∧ ℓ ^ (f / p) = 2 → 3 < p →
        Nat.card (fieldFixedPSU h n σ) = 72 ∧ ∀ x ∈ fieldFixedPSU h n σ, orderOf x ≠ p) := by
  have := h.finite
  set h₀ := fixSubfield_unitaryFieldData h hp hp2 hσ with hh₀
  have hbar := fixSubfield_unitaryFieldData_bar h hp hp2 hσ
  obtain ⟨hpf, hcard⟩ := dvd_and_card_fixSubfield_unitary h hp hp2 hσ
  have hn1 : 1 ≤ n := by omega
  have hinj := subfieldPSU_injective h h₀ hbar n hn1
  have hrange := range_subfieldPSU h n h₀ hbar hp hσ hZ
  have hcomap := comap_subfieldSU_normOneScalars h h₀ hbar n hn1
  let eJ : primeFormP h₀ ((1 : GL (Fin n) (fixSubfield σ)) :
      Matrix (Fin n) (Fin n) (fixSubfield σ)) ≃* fieldFixedPSU h n σ :=
    (MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange)
  refine ⟨hpf, by rw [hcard, ← pow_mul, mul_comm], fun c => (hbar c).symm, ?_, hcomap, hinj,
    hrange, card_normOneScalars_one h hn1, card_normOneScalars_one h₀ hn1, fun hq₀ => ?_,
    fun hq₀ hp3 => ?_⟩
  · rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk']
    exact hcomap
  ·
    have := isSimpleGroup_primeFormP_one h₀ hn hq₀
    have hnc := not_commute_primeFormP_one h₀ hn hq₀
    obtain ⟨hfixing, hmap, hcardz⟩ := fixingSubgroup_range_subfieldPSU h n h₀ hbar hn hq hq₀
    refine ⟨eJ.symm.isSimpleGroup, fun hc => hnc fun x y => ?_, ?_, hmap, by rw [hcardz, hσ]⟩
    · have h1 := congrArg eJ.symm (hc (eJ x) (eJ y))
      rwa [map_mul, map_mul, MulEquiv.symm_apply_apply, MulEquiv.symm_apply_apply] at h1
    · rw [← hfixing, hrange]
  ·
    obtain ⟨rfl, hq2⟩ := hq₀
    have h72 : Nat.card (fieldFixedPSU h 3 σ) = 72 := by
      rw [← Nat.card_congr eJ.toEquiv]
      exact card_primeFormP_three_two h₀ hq2
    refine ⟨h72, fun x hx hxp => ?_⟩
    have h1 : orderOf x ∣ 72 := by
      rw [← h72]
      exact Subgroup.orderOf_dvd_natCard _ hx
    rw [hxp] at h1
    have h2 : p ∣ 2 ^ 3 * 3 ^ 2 := by norm_num; exact h1
    rcases (Nat.Prime.dvd_mul hp).1 h2 with h3 | h3
    · have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h3)
      omega
    · have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 (hp.dvd_of_dvd_pow h3)
      omega

end Prime

end CFSG.RankThree.Classical
