module

public import CFSG.RankThree.CentralLift.DefiningSymplectic
public import CFSG.ClassicalGroups.UnitaryFlag.WittBasis
public import CFSG.LinearAlgebra.LinearGroups.UnitaryOrder
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryPerfectFamily

public section

namespace CFSG.RankThree.CentralLift

open Matrix CFSG.LocalAnalysis.ComponentInitial
open CFSG.Assembly.LowTwoRank (StatedSp)
open CFSG.ClassicalGroups.UnitaryFlag (gramSU mem_gramSU gramForm gramForm_apply gramForm_isSymm
  gramForm_separatingLeft card_gramSU mem_gramSU_iff_isometry HypIndex hypGram hypGram_apply
  hypPartner exists_hypBasis)
open CFSG.RankThree.Classical (siegelRadicalSU mem_siegelRadicalSU siegel_radical_su
  siegel_radical_su_preimage_comm hypGram2 torusGL coe_torusGL torusGL_mem_gramSU
  torusGL_conj_siegelGL siegelGL coe_siegelGL siegelMat)
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag (unitriangular mem_unitriangular
  card_unitriangular)

section Gram

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)
  {V : Type*} [AddCommGroup V] [Module K V] {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
theorem form_eq_gramForm {B : V →ₛₗ[h.bar] V →ₗ[K] K} (e : Module.Basis ι K V)
    {G : Matrix ι ι K} (he : ∀ i j, B (e i) (e j) = G i j) (x y : V) :
    B x y = gramForm h G (e.equivFun x) (e.equivFun y) := by
  rw [gramForm_apply]
  conv_lhs => rw [← e.sum_equivFun x, ← e.sum_equivFun y]
  simp only [map_sum, map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, he,
    dotProduct, mulVec, Finset.mul_sum, RingHom.id_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem toLin'_basis_apply (e : Module.Basis ι K V) (M : GL ι K) (x : V) :
    ((Matrix.GeneralLinearGroup.toLin' e M : LinearMap.GeneralLinearGroup K V) : V →ₗ[K] V) x =
      e.equivFun.symm ((M : Matrix ι ι K) *ᵥ e.equivFun x) :=
  rfl

theorem equivFun_toLin'_basis_apply (e : Module.Basis ι K V) (M : GL ι K) (x : V) :
    e.equivFun (((Matrix.GeneralLinearGroup.toLin' e M : LinearMap.GeneralLinearGroup K V) :
      V →ₗ[K] V) x) = (M : Matrix ι ι K) *ᵥ e.equivFun x := by
  rw [toLin'_basis_apply, LinearEquiv.apply_symm_apply]

theorem det_toLin'_basis (e : Module.Basis ι K V) (M : GL ι K) :
    LinearMap.det ((Matrix.GeneralLinearGroup.toLin' e M : LinearMap.GeneralLinearGroup K V) :
      V →ₗ[K] V) = (M : Matrix ι ι K).det := by
  have hM : ((Matrix.GeneralLinearGroup.toLin' e M : LinearMap.GeneralLinearGroup K V) :
      V →ₗ[K] V) = Matrix.toLin e e M := by
    ext x
    rw [Matrix.toLin_apply, toLin'_basis_apply, Module.Basis.equivFun_symm_apply,
      Module.Basis.equivFun_apply]
  rw [hM, LinearMap.det_toLin]

theorem toLin'_mem_sesqSpecialUnitaryGroup_iff_gramSU {B : V →ₛₗ[h.bar] V →ₗ[K] K}
    (e : Module.Basis ι K V) {G : Matrix ι ι K} (he : ∀ i j, B (e i) (e j) = G i j)
    (M : GL ι K) :
    Matrix.GeneralLinearGroup.toLin' e M ∈ sesqSpecialUnitaryGroup B ↔ M ∈ gramSU h G := by
  rw [mem_sesqSpecialUnitaryGroup, mem_sesqUnitaryGroup, det_toLin'_basis,
    mem_gramSU_iff_isometry]
  constructor
  · rintro ⟨hiso, hdet⟩
    refine ⟨fun u v => ?_, hdet⟩
    have huv := hiso (e.equivFun.symm u) (e.equivFun.symm v)
    simpa only [form_eq_gramForm h e he, equivFun_toLin'_basis_apply,
      LinearEquiv.apply_symm_apply] using huv
  · rintro ⟨hiso, hdet⟩
    refine ⟨fun x y => ?_, hdet⟩
    rw [form_eq_gramForm h e he, form_eq_gramForm h e he, equivFun_toLin'_basis_apply,
      equivFun_toLin'_basis_apply, hiso]

theorem nonempty_sesqSpecialUnitaryGroup_mulEquiv_gramSU {B : V →ₛₗ[h.bar] V →ₗ[K] K}
    (e : Module.Basis ι K V) {G : Matrix ι ι K} (he : ∀ i j, B (e i) (e j) = G i j) :
    Nonempty (sesqSpecialUnitaryGroup B ≃* gramSU h G) := by
  let Ψ := Matrix.GeneralLinearGroup.toLin' e
  have hEq : (gramSU h G).map Ψ.toMonoidHom = sesqSpecialUnitaryGroup B := by
    ext g
    constructor
    · rintro ⟨M, hM, rfl⟩
      exact (toLin'_mem_sesqSpecialUnitaryGroup_iff_gramSU h e he M).2 hM
    · intro hg
      refine ⟨Ψ.symm g, (toLin'_mem_sesqSpecialUnitaryGroup_iff_gramSU h e he _).1 ?_, ?_⟩
      · change Ψ (Ψ.symm g) ∈ _
        rwa [MulEquiv.apply_symm_apply]
      · exact Ψ.apply_symm_apply g
  exact ⟨((Ψ.subgroupMap (gramSU h G)).trans (MulEquiv.subgroupCongr hEq)).symm⟩

variable (r : ℕ) in
@[expose] def hypIndexEquiv : Fin r ⊕ Fin r ≃ HypIndex r 0 where
  toFun := Sum.elim Sum.inl fun j => Sum.inr (Sum.inr j)
  invFun := Sum.elim Sum.inl (Sum.elim (fun k => k.elim0) Sum.inr)
  left_inv x := by rcases x with i | i <;> rfl
  right_inv x := by
    rcases x with i | k | i
    · rfl
    · exact k.elim0
    · rfl

theorem exists_basis_hypGram2 [FiniteDimensional K V] {B : V →ₛₗ[h.bar] V →ₗ[K] K}
    (hB : B.IsSymm) (hBl : B.SeparatingLeft) {r : ℕ} (hV : Module.finrank K V = 2 * r) :
    ∃ e : Module.Basis (Fin r ⊕ Fin r) K V, ∀ x y, B (e x) (e y) = hypGram2 r K x y := by
  obtain ⟨w, hw⟩ := exists_hypBasis h hB hBl (r := r) (ε := 0) (by rw [hV, add_zero])
  refine ⟨w.reindex (hypIndexEquiv r).symm, fun x y => ?_⟩
  rw [Module.Basis.reindex_apply, Module.Basis.reindex_apply, Equiv.symm_symm, hw,
    hypGram_apply]
  rcases x with i | i <;> rcases y with j | j <;>
    simp [hypIndexEquiv, hypGram2, hypPartner, one_apply, eq_comm]

end Gram

section Levi

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K) {r : ℕ}

theorem map_bar_bar (A : Matrix (Fin r) (Fin r) K) : (A.map h.bar).map h.bar = A := by
  ext i j
  simp only [map_apply, UnitaryFieldData.bar_bar]

variable (r) in
@[expose] noncomputable def leviUMat :
    SpecialLinearGroup (Fin r) K →* Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K where
  toFun A := fromBlocks (A : Matrix (Fin r) (Fin r) K) 0 0
    (((A⁻¹ : SpecialLinearGroup (Fin r) K) : Matrix (Fin r) (Fin r) K).map h.bar)ᵀ
  map_one' := by
    rw [inv_one]
    change fromBlocks (1 : Matrix (Fin r) (Fin r) K) 0 0
      ((1 : Matrix (Fin r) (Fin r) K).map h.bar)ᵀ = 1
    rw [Matrix.map_one _ (map_zero h.bar) (map_one h.bar), transpose_one, fromBlocks_one]
  map_mul' A B := by
    rw [_root_.mul_inv_rev]
    change fromBlocks ((A : Matrix (Fin r) (Fin r) K) * (B : Matrix (Fin r) (Fin r) K)) 0 0
        ((((B⁻¹ : SpecialLinearGroup (Fin r) K) : Matrix (Fin r) (Fin r) K) *
          ((A⁻¹ : SpecialLinearGroup (Fin r) K) : Matrix (Fin r) (Fin r) K)).map h.bar)ᵀ = _
    rw [fromBlocks_multiply, Matrix.map_mul, transpose_mul]
    simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]

theorem leviUMat_apply (A : SpecialLinearGroup (Fin r) K) :
    leviUMat h r A = fromBlocks (A : Matrix (Fin r) (Fin r) K) 0 0
      (((A⁻¹ : SpecialLinearGroup (Fin r) K) : Matrix (Fin r) (Fin r) K).map h.bar)ᵀ :=
  rfl

omit h in
theorem coe_mul_coe_inv (A : SpecialLinearGroup (Fin r) K) :
    (A : Matrix (Fin r) (Fin r) K) *
      ((A⁻¹ : SpecialLinearGroup (Fin r) K) : Matrix (Fin r) (Fin r) K) = 1 :=
  congrArg (fun M : SpecialLinearGroup (Fin r) K => (M : Matrix (Fin r) (Fin r) K))
    (mul_inv_cancel A)

omit h in
theorem coe_inv_mul_coe (A : SpecialLinearGroup (Fin r) K) :
    ((A⁻¹ : SpecialLinearGroup (Fin r) K) : Matrix (Fin r) (Fin r) K) *
      (A : Matrix (Fin r) (Fin r) K) = 1 :=
  congrArg (fun M : SpecialLinearGroup (Fin r) K => (M : Matrix (Fin r) (Fin r) K))
    (inv_mul_cancel A)

theorem barInvT_mul_barT (A : SpecialLinearGroup (Fin r) K) :
    (((A⁻¹ : SpecialLinearGroup (Fin r) K) : Matrix (Fin r) (Fin r) K).map h.bar)ᵀ *
      ((A : Matrix (Fin r) (Fin r) K).map h.bar)ᵀ = 1 := by
  rw [← transpose_mul, ← Matrix.map_mul, coe_mul_coe_inv,
    Matrix.map_one _ (map_zero h.bar) (map_one h.bar), transpose_one]

theorem barT_mul_barInvT (A : SpecialLinearGroup (Fin r) K) :
    ((A : Matrix (Fin r) (Fin r) K).map h.bar)ᵀ *
      (((A⁻¹ : SpecialLinearGroup (Fin r) K) : Matrix (Fin r) (Fin r) K).map h.bar)ᵀ = 1 := by
  rw [← transpose_mul, ← Matrix.map_mul, coe_inv_mul_coe,
    Matrix.map_one _ (map_zero h.bar) (map_one h.bar), transpose_one]

theorem leviUMat_mem (A : SpecialLinearGroup (Fin r) K) :
    ((leviUMat h r A).map h.bar)ᵀ * hypGram2 r K * leviUMat h r A = hypGram2 r K ∧
      (leviUMat h r A).det = 1 := by
  have hAA := coe_inv_mul_coe A
  have hd : ((A⁻¹ : SpecialLinearGroup (Fin r) K) : Matrix (Fin r) (Fin r) K).det = 1 :=
    (A⁻¹).2
  refine ⟨?_, ?_⟩
  · rw [leviUMat_apply, fromBlocks_map, fromBlocks_transpose, hypGram2, fromBlocks_multiply,
      fromBlocks_multiply, transpose_map, map_bar_bar, transpose_transpose]
    simp only [Matrix.map_zero _ (map_zero h.bar), transpose_zero, Matrix.mul_zero,
      Matrix.zero_mul, add_zero, zero_add, Matrix.mul_one, hAA, barT_mul_barInvT]
  · rw [leviUMat_apply, det_fromBlocks_zero₂₁, det_transpose, A.2, one_mul,
      ← RingHom.mapMatrix_apply, ← RingHom.map_det, hd, map_one]

variable (r) in
@[expose] noncomputable def leviU : SpecialLinearGroup (Fin r) K →* gramSU h (hypGram2 r K) :=
  (leviUMat h r).toHomUnits.codRestrict _ fun A => mem_gramSU.2 (leviUMat_mem h A)

theorem coe_leviU (A : SpecialLinearGroup (Fin r) K) :
    (((leviU h r A : gramSU h (hypGram2 r K)) : GL (Fin r ⊕ Fin r) K) :
      Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) = leviUMat h r A :=
  rfl

theorem leviU_injective : Function.Injective (leviU h r) := by
  intro A B hAB
  have h1 : leviUMat h r A = leviUMat h r B :=
    congrArg (fun g : gramSU h (hypGram2 r K) => ((g : GL (Fin r ⊕ Fin r) K) :
      Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)) hAB
  have h2 := congrArg toBlocks₁₁ h1
  rw [leviUMat_apply, leviUMat_apply, toBlocks_fromBlocks₁₁, toBlocks_fromBlocks₁₁] at h2
  exact Subtype.ext h2

theorem skewHerm_conj (A B : Matrix (Fin r) (Fin r) K) (hB : B + (B.map h.bar)ᵀ = 0) :
    A * B * (A.map h.bar)ᵀ + ((A * B * (A.map h.bar)ᵀ).map h.bar)ᵀ = 0 := by
  rw [Matrix.map_mul, Matrix.map_mul, transpose_map, map_bar_bar, transpose_mul,
    transpose_mul, transpose_transpose, Matrix.mul_assoc A B, ← Matrix.mul_add,
    ← Matrix.add_mul, hB, Matrix.zero_mul, Matrix.mul_zero]

theorem coe_leviU_conj (A : SpecialLinearGroup (Fin r) K) {x : gramSU h (hypGram2 r K)}
    {B : Matrix (Fin r) (Fin r) K}
    (hx : ((x : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) =
      fromBlocks 1 B 0 1) :
    (((leviU h r A * x * (leviU h r A)⁻¹ : gramSU h (hypGram2 r K)) : GL (Fin r ⊕ Fin r) K) :
      Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) =
      fromBlocks 1 ((A : Matrix (Fin r) (Fin r) K) * B *
        ((A : Matrix (Fin r) (Fin r) K).map h.bar)ᵀ) 0 1 := by
  have hAA := coe_mul_coe_inv A
  rw [← map_inv, Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul, coe_leviU,
    coe_leviU, hx, leviUMat_apply, leviUMat_apply, inv_inv, fromBlocks_multiply,
    fromBlocks_multiply]
  simp only [Matrix.mul_one, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, hAA,
    barInvT_mul_barT]

theorem leviU_conj_mem (A : SpecialLinearGroup (Fin r) K) {x : gramSU h (hypGram2 r K)}
    (hx : x ∈ siegelRadicalSU h r) :
    leviU h r A * x * (leviU h r A)⁻¹ ∈ siegelRadicalSU h r := by
  obtain ⟨B, hB, hxB⟩ := (mem_siegelRadicalSU h).1 hx
  exact (mem_siegelRadicalSU h).2 ⟨_, skewHerm_conj h _ B hB, coe_leviU_conj h A hxB⟩

variable (r) in
@[expose] noncomputable def leviUnipotentU : Subgroup (gramSU h (hypGram2 r K)) :=
  (unitriangular r K).map (leviU h r)

theorem leviUnipotentU_le_normalizer :
    leviUnipotentU h r ≤
      Subgroup.normalizer (siegelRadicalSU h r : Set (gramSU h (hypGram2 r K))) := by
  rintro _ ⟨A, -, rfl⟩
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => leviU_conj_mem h A hx, fun hx => ?_⟩
  have h1 := leviU_conj_mem h A⁻¹ hx
  rwa [map_inv, inv_inv, show (leviU h r A)⁻¹ * (leviU h r A * x * (leviU h r A)⁻¹) *
    leviU h r A = x by group] at h1

theorem siegelRadicalSU_inf_leviUnipotentU : siegelRadicalSU h r ⊓ leviUnipotentU h r = ⊥ := by
  rw [eq_bot_iff]
  rintro g ⟨hR, A, -, rfl⟩
  obtain ⟨B, -, hB⟩ := (mem_siegelRadicalSU h).1 hR
  have hB' : leviUMat h r A = fromBlocks 1 B 0 1 := hB
  have h1 := congrArg toBlocks₁₁ hB'
  rw [leviUMat_apply, toBlocks_fromBlocks₁₁, toBlocks_fromBlocks₁₁] at h1
  have hA : A = 1 := Subtype.ext h1
  rw [hA, map_one]
  exact one_mem _

end Levi

theorem card_sup_of_le_normalizer {G : Type*} [Group G] {R V : Subgroup G}
    (hVR : V ≤ Subgroup.normalizer (R : Set G)) (hRV : R ⊓ V = ⊥) :
    Nat.card (R ⊔ V : Subgroup G) = Nat.card R * Nat.card V := by
  have hset := Subgroup.coe_mul_of_right_le_normalizer_left R V hVR
  let φ : R × V → (R ⊔ V : Subgroup G) := fun x =>
    ⟨x.1 * x.2, mul_mem (Subgroup.mem_sup_left x.1.2) (Subgroup.mem_sup_right x.2.2)⟩
  have hφ : Function.Bijective φ := by
    refine ⟨fun x y hxy => ?_, fun z => ?_⟩
    · have h1 : (x.1 : G) * x.2 = y.1 * y.2 := congrArg Subtype.val hxy
      have h2 : ((y.1 : G))⁻¹ * x.1 = y.2 * (x.2 : G)⁻¹ := by
        rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, ← h1, mul_inv_cancel_right]
      have h3 : ((y.1 : G))⁻¹ * x.1 ∈ R ⊓ V :=
        Subgroup.mem_inf.2 ⟨R.mul_mem (R.inv_mem y.1.2) x.1.2,
          h2 ▸ V.mul_mem y.2.2 (V.inv_mem x.2.2)⟩
      rw [hRV, Subgroup.mem_bot, inv_mul_eq_one] at h3
      have h4 : (x.2 : G) = y.2 := by
        rw [← h3] at h1
        exact mul_left_cancel h1
      exact Prod.ext (Subtype.ext h3.symm) (Subtype.ext h4)
    · have hz : (z : G) ∈ ((R ⊔ V : Subgroup G) : Set G) := z.2
      rw [hset] at hz
      obtain ⟨x, hx, v, hv, hxv⟩ := hz
      exact ⟨(⟨x, hx⟩, ⟨v, hv⟩), Subtype.ext hxv⟩
  rw [← Nat.card_prod]
  exact (Nat.card_congr (Equiv.ofBijective φ hφ)).symm

theorem coprime_of_dvd_card_units {k : Type} [Field k] [Finite k] {p m : ℕ} (hp : p.Prime)
    (hk : Nat.card k = p ^ m) (hm : 1 ≤ m) {n : ℕ} (hn : n ∣ Nat.card kˣ) : Nat.Coprime n p := by
  rw [Nat.card_units, hk] at hn
  refine Nat.Coprime.coprime_dvd_left hn ?_
  rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hp]
  intro hdvd
  have h1p : 1 ≤ p ^ m := Nat.one_le_pow _ _ hp.pos
  have hpq : p ∣ p ^ m := dvd_pow_self p (by omega)
  have h3 : p ∣ p ^ m - (p ^ m - 1) := Nat.dvd_sub hpq hdvd
  rw [show p ^ m - (p ^ m - 1) = 1 by omega] at h3
  exact hp.one_lt.ne' (Nat.dvd_one.1 h3)

section Perfect

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K) {r : ℕ}

theorem hypGram2_hermitian : ((hypGram2 r K).map h.bar)ᵀ = hypGram2 r K := by
  rw [hypGram2, fromBlocks_map, fromBlocks_transpose]
  simp only [Matrix.map_zero _ (map_zero h.bar), Matrix.map_one _ (map_zero h.bar)
    (map_one h.bar), transpose_zero, transpose_one]

theorem det_hypGram2_ne_zero : (hypGram2 r K).det ≠ 0 := by
  have hsq : hypGram2 r K * hypGram2 r K = 1 := by
    rw [hypGram2, fromBlocks_multiply]
    simp [fromBlocks_one]
  intro h0
  have := congrArg det hsq
  rw [det_mul, h0, zero_mul, det_one] at this
  exact zero_ne_one this

theorem pow_factorization_card_gramSU (hr : 1 ≤ r) :
    p ^ (Nat.card (gramSU h (hypGram2 r K))).factorization p = (p ^ f) ^ (r * (2 * r - 1)) := by
  have hfin : Module.finrank K (Fin r ⊕ Fin r → K) = 2 * r := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]
    ring
  have h1 := (CFSG.LinearGroups.unitary_full_group_order h
    (gramForm_isSymm h (hypGram2_hermitian h)) (gramForm_separatingLeft h det_hypGram2_ne_zero)
    hfin (by omega)).2.2.2.2.2.2
  rw [card_gramSU, h1]
  congr 1
  rw [mul_assoc, Nat.mul_div_cancel_left _ two_pos]

theorem torusGL_const_mul (τ σ : Kˣ) :
    torusGL (fun _ : Fin r => τ * σ) = torusGL (fun _ => τ) * torusGL (fun _ => σ) := by
  refine Units.ext ?_
  rw [Units.val_mul, coe_torusGL, coe_torusGL, coe_torusGL, fromBlocks_multiply]
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, diagonal_mul_diagonal,
    Units.val_mul, _root_.mul_inv_rev, mul_comm]

theorem torusGL_const_one : torusGL (fun _ : Fin r => (1 : Kˣ)) = 1 := by
  refine Units.ext ?_
  rw [coe_torusGL, Units.val_one]
  simp only [inv_one, Units.val_one, diagonal_one, fromBlocks_one]

theorem torusGL_const_pow (τ : Kˣ) (n : ℕ) :
    torusGL (fun _ : Fin r => τ ^ n) = torusGL (fun _ => τ) ^ n := by
  induction n with
  | zero => simp only [pow_zero, torusGL_const_one]
  | succ n ih => rw [pow_succ, torusGL_const_mul, ih, pow_succ]

theorem torusGL_const_commute (τ : Kˣ) (A : SpecialLinearGroup (Fin r) K) :
    (torusGL (fun _ : Fin r => τ) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *
        leviUMat h r A = leviUMat h r A * torusGL (fun _ : Fin r => τ) := by
  rw [coe_torusGL, leviUMat_apply, fromBlocks_multiply, fromBlocks_multiply]
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]
  congr 1
  · ext i j
    simp [diagonal_mul, mul_diagonal, mul_comm]
  · ext i j
    simp [diagonal_mul, mul_diagonal, mul_comm]

theorem torusGL_const_conj {τ : Kˣ} (hτ : h.bar (τ : K) = τ) {n : ℕ} (hn : (τ : K) ^ 2 = n)
    {x : gramSU h (hypGram2 r K)} (hx : x ∈ siegelRadicalSU h r) :
    (⟨torusGL (fun _ : Fin r => τ), torusGL_mem_gramSU h fun _ => hτ⟩ :
      gramSU h (hypGram2 r K)) * x *
        (⟨torusGL (fun _ : Fin r => τ), torusGL_mem_gramSU h fun _ => hτ⟩ :
          gramSU h (hypGram2 r K))⁻¹ = x ^ n := by
  obtain ⟨B, -, hxB⟩ := (mem_siegelRadicalSU h).1 hx
  have hxs : (x : GL (Fin r ⊕ Fin r) K) = siegelGL B := Units.ext hxB
  refine Subtype.ext ?_
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_pow]
  change torusGL (fun _ : Fin r => τ) * (x : GL (Fin r ⊕ Fin r) K) *
    (torusGL (fun _ : Fin r => τ))⁻¹ = (x : GL (Fin r ⊕ Fin r) K) ^ n
  rw [hxs, torusGL_conj_siegelGL]
  refine Units.ext ?_
  rw [Units.val_pow_eq_pow_val, coe_siegelGL, coe_siegelGL, siegelMat_pow]
  congr 1
  ext i j
  simp only [mul_diagonal, diagonal_mul, Matrix.smul_apply, nsmul_eq_mul]
  rw [← hn]
  ring

theorem unitary_perfect_ker_eq_bot (hp3 : 3 < p) (hr : 2 ≤ r) {E : Type*} [Group E] [Finite E]
    [Group.IsPerfect E] (π : E →* gramSU h (hypGram2 r K)) (hπ : Function.Surjective π)
    (hC : π.ker ≤ Subgroup.center E) (hCp : IsPGroup p π.ker) : π.ker = ⊥ := by
  classical
  have hp := h.prime
  have : Fact p.Prime := ⟨hp⟩
  have := h.finite
  have : Fintype K := Fintype.ofFinite K
  have : CharP K p := h.charP
  have : Finite (gramSU h (hypGram2 r K)) := Finite.of_surjective π hπ
  have hp2 : p ≠ 2 := by omega
  have hp4 : p ≠ 4 := fun h4 => by
    rw [h4] at hp
    exact absurd hp (by decide)
  have hf := h.one_le
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero (by rw [ringChar.eq K p]; exact hp2)
  obtain ⟨hRel, hRcard⟩ := siegel_radical_su h r
  obtain ⟨lh, hlh, hlhu⟩ := existsUnique_lift_specialLinear hp hp3 hp (hp.odd_of_ne_two hp2)
    (by omega : 1 ≤ 2 * f) h.card hr π hπ hC hCp (leviU h r)
  have hlhA : ∀ A, π (lh A) = leviU h r A := fun A => DFunLike.congr_fun hlh A
  have hVhmap : ((unitriangular r K).map lh).map π = leviUnipotentU h r := by
    rw [Subgroup.map_map, hlh]
    rfl
  have hVhinj : π.ker ⊓ (unitriangular r K).map lh = ⊥ := by
    rw [eq_bot_iff]
    rintro _ ⟨h1, A, -, rfl⟩
    have hA : A = 1 := leviU_injective h (by rw [← hlhA, MonoidHom.mem_ker.1 h1, map_one])
    rw [hA, map_one]
    exact one_mem _
  set τ : Kˣ := Units.mk0 2 h2 with hτdef
  have hτ : h.bar (τ : K) = τ := by
    rw [hτdef, Units.val_mk0]
    exact map_ofNat h.bar 2
  set d : gramSU h (hypGram2 r K) := ⟨torusGL (fun _ : Fin r => τ),
    torusGL_mem_gramSU h fun _ => hτ⟩ with hd
  have hdcop : Nat.Coprime (orderOf d) p := by
    have h1 : orderOf d ∣ orderOf τ := by
      refine orderOf_dvd_of_pow_eq_one (Subtype.ext ?_)
      rw [Subgroup.coe_pow, Subgroup.coe_one]
      change torusGL (fun _ : Fin r => τ) ^ orderOf τ = 1
      rw [← torusGL_const_pow, pow_orderOf_eq_one, torusGL_const_one]
    exact coprime_of_dvd_card_units hp h.card (by omega) (h1.trans (orderOf_dvd_natCard τ))
  obtain ⟨a, ha, hacop⟩ := exists_coprime_lift hp π hπ hdcop
  have haV : a ∈ Subgroup.centralizer (((unitriangular r K).map lh : Subgroup E) : Set E) := by
    have hdl : ∀ A, d * leviU h r A * d⁻¹ = leviU h r A := fun A => by
      rw [mul_inv_eq_iff_eq_mul]
      exact Subtype.ext (Units.ext (torusGL_const_commute h τ A))
    have hβ : π.comp ((MulAut.conj a).toMonoidHom.comp lh) = leviU h r := by
      refine MonoidHom.ext fun A => ?_
      change π (a * lh A * a⁻¹) = leviU h r A
      rw [map_mul, map_mul, map_inv, ha, hlhA, hdl]
    have hβ' := hlhu _ hβ
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨A, -, rfl⟩
    have h1 : a * lh A * a⁻¹ = lh A := DFunLike.congr_fun hβ' A
    exact (mul_inv_eq_iff_eq_mul.1 h1).symm
  have h4 : (4 : ZMod p) ≠ 0 := by
    intro h0
    rw [show (4 : ZMod p) = ((4 : ℕ) : ZMod p) by norm_num, ZMod.natCast_eq_zero_iff] at h0
    have := Nat.le_of_dvd (by norm_num) h0
    omega
  have h41 : Units.mk0 (4 : ZMod p) h4 ≠ 1 := by
    intro h0
    have h' : ((3 : ℕ) : ZMod p) = 0 := by
      have := congrArg Units.val h0
      simp only [Units.val_mk0, Units.val_one] at this
      have h3 : ((3 : ℕ) : ZMod p) = (4 : ZMod p) - 1 := by norm_num
      rw [h3, this, sub_self]
    rw [ZMod.natCast_eq_zero_iff] at h'
    have := Nat.le_of_dvd (by norm_num) h'
    omega
  have hval : ((Units.mk0 (4 : ZMod p) h4 : (ZMod p)ˣ) : ZMod p).val = 4 := by
    rw [Units.val_mk0, show (4 : ZMod p) = ((4 : ℕ) : ZMod p) by norm_num, ZMod.val_natCast,
      Nat.mod_eq_of_lt (by omega)]
  have hcard : Nat.card (siegelRadicalSU h r ⊔ leviUnipotentU h r : Subgroup _) =
      p ^ (Nat.card (gramSU h (hypGram2 r K))).factorization p := by
    rw [card_sup_of_le_normalizer (leviUnipotentU_le_normalizer h)
      (siegelRadicalSU_inf_leviUnipotentU h), hRcard, leviUnipotentU,
      Subgroup.card_map_of_injective (leviU_injective h), card_unitriangular, h.card,
      pow_factorization_card_gramSU h (by omega)]
    obtain ⟨m, rfl⟩ : ∃ m, r = m + 1 := ⟨r - 1, by omega⟩
    have hev : 2 ∣ (m + 1) * m := by
      rw [mul_comm]
      exact even_iff_two_dvd.1 (Nat.even_mul_succ_self m)
    have h2t : 2 * ((m + 1) * m / 2) = (m + 1) * m := Nat.mul_div_cancel' hev
    rw [← pow_mul, ← pow_mul, ← pow_mul, ← pow_add]
    congr 1
    rw [Nat.add_sub_cancel, show 2 * (m + 1) - 1 = 2 * m + 1 by omega]
    calc f * (m + 1) ^ 2 + 2 * f * ((m + 1) * m / 2)
        = f * (m + 1) ^ 2 + f * (2 * ((m + 1) * m / 2)) := by ring
      _ = f * ((m + 1) * (2 * m + 1)) := by rw [h2t]; ring
  refine ker_eq_bot_of_radical_dilation π hπ hC hCp (siegelRadicalSU h r) (leviUnipotentU h r)
    (fun x hx y hy => congrArg Subtype.val (hRel.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩))
    hRel.2 (siegel_radical_su_preimage_comm h hp3 r π hπ hC)
    (siegelRadicalSU_inf_leviUnipotentU h) (leviUnipotentU_le_normalizer h)
    ⟨Sylow.ofCard _ hcard, Sylow.coe_ofCard _ hcard⟩ _ hVhmap hVhinj a hacop haV
    (Units.mk0 (4 : ZMod p) h4) h41 fun x hx => ?_
  rw [ha, hval]
  exact torusGL_const_conj h hτ (by rw [hτdef, Units.val_mk0]; norm_num) hx

end Perfect

universe u v

theorem unitary_defining_splitting {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)
    (hp3 : 3 < p) {V : Type*} [AddCommGroup V] [Module K V] {B : V →ₛₗ[h.bar] V →ₗ[K] K}
    (hB : B.IsSymm) (hBl : B.SeparatingLeft) {r : ℕ} (hr : 2 ≤ r)
    (hV : Module.finrank K V = 2 * r) {E : Type*} [Group E] [Finite E]
    (π : E →* sesqSpecialUnitaryGroup B) (hπ : Function.Surjective π)
    (hC : π.ker ≤ Subgroup.center E) (hCp : IsPGroup p π.ker) :
    (∃! s : sesqSpecialUnitaryGroup B →* E, π.comp s = MonoidHom.id _) ∧
      ∀ s : sesqSpecialUnitaryGroup B →* E, π.comp s = MonoidHom.id _ →
        ∃ e : π.ker × s.range ≃* E, ∀ c g, e (c, g) = (c : E) * g := by
  have : FiniteDimensional K V := FiniteDimensional.of_finrank_pos (by omega)
  obtain ⟨b, hb⟩ := exists_basis_hypGram2 h hB hBl hV
  obtain ⟨φ⟩ := nonempty_sesqSpecialUnitaryGroup_mulEquiv_gramSU h b hb
  have : Group.IsPerfect (sesqSpecialUnitaryGroup B) :=
    unitary_perfect h hB hBl (by omega) (fun h32 => by
      have := congrArg Prod.fst h32
      simp only at this
      omega)
  refine splitting_of_perfect_case π hπ hC fun D hD hDs => ?_
  have : Group.IsPerfect D := hD
  have hker := unitary_perfect_ker_eq_bot h hp3 hr (φ.toMonoidHom.comp (π.comp D.subtype))
    (φ.surjective.comp hDs)
    (by
      rw [MonoidHom.ker_comp_of_injective _ _ φ.injective]
      exact ker_comp_subtype_le_center π hC D)
    (by
      rw [MonoidHom.ker_comp_of_injective _ _ φ.injective]
      exact isPGroup_ker_comp_subtype π hCp D)
  rwa [MonoidHom.ker_comp_of_injective _ _ φ.injective] at hker

theorem defining_large_prime_symplectic_even_unitary_central_extension_splitting {p f : ℕ}
    (hp : p.Prime) (hp3 : 3 < p) (hf : 1 ≤ f) :
    (∀ (F : Type) [Field F] [Finite F], Nat.card F = p ^ f → ∀ r : ℕ, 1 ≤ r →
      ∀ (E : Type u) [Group E] [Finite E] (π : E →* StatedSp r F), Function.Surjective π →
        π.ker ≤ Subgroup.center E → IsPGroup p π.ker →
        (∃! s : StatedSp r F →* E, π.comp s = MonoidHom.id _) ∧
          ∀ s : StatedSp r F →* E, π.comp s = MonoidHom.id _ →
            ∃ e : π.ker × s.range ≃* E, ∀ c g, e (c, g) = (c : E) * g) ∧
    (∀ (K : Type) [Field K] (h : UnitaryFieldData p f K) (V : Type v) [AddCommGroup V]
      [Module K V] (B : V →ₛₗ[h.bar] V →ₗ[K] K), B.IsSymm → B.SeparatingLeft → ∀ r : ℕ, 2 ≤ r →
      Module.finrank K V = 2 * r →
      ∀ (E : Type u) [Group E] [Finite E] (π : E →* sesqSpecialUnitaryGroup B),
        Function.Surjective π → π.ker ≤ Subgroup.center E → IsPGroup p π.ker →
        (∃! s : sesqSpecialUnitaryGroup B →* E, π.comp s = MonoidHom.id _) ∧
          ∀ s : sesqSpecialUnitaryGroup B →* E, π.comp s = MonoidHom.id _ →
            ∃ e : π.ker × s.range ≃* E, ∀ c g, e (c, g) = (c : E) * g) :=
  ⟨fun _ _ _ hF _ _ _ _ _ π hπ hC hCp =>
      symplectic_defining_splitting hp hp3 hf hF π hπ hC hCp,
    fun _ _ h _ _ _ _ hB hBl _ hr hV _ _ _ π hπ hC hCp =>
      unitary_defining_splitting h hp3 hB hBl hr hV π hπ hC hCp⟩

end CFSG.RankThree.CentralLift
