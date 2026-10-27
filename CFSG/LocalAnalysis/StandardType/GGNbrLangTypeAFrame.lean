module

public import CFSG.LocalAnalysis.StandardType.GGNbrLangTypeAWeyl

public section

namespace CFSG.StandardType

namespace NbrLangTypeA

open Matrix CFSG.ComponentClassification CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.GroupTheory.SteinbergBK (semilinearFixedSubfield)
open scoped commutatorElement

variable {d : ℕ} {F : Type} [Field F]

theorem exists_frame_of_le_linear [Finite F] {p : ℕ} (hp : p.Prime) (hpF : p ∣ Nat.card F - 1)
    (hd : 0 < d) (hpd : Nat.Coprime p d) (E : Subgroup (MulAut (projectiveSL d F)))
    (hEc : ∀ φ ∈ E, ∀ ψ ∈ E, φ * ψ = ψ * φ) (hEp : ∀ φ ∈ E, φ ^ p = 1)
    (hElin : E ≤ linearAutGroup d F) :
    ∃ M : GL (Fin d) F, ∀ φ ∈ E, ∃ D₁ : GL (Fin d) F, (D₁ : Matrix (Fin d) (Fin d) F).IsDiag ∧
      φ = conjAut d F M * conjAut d F D₁ * (conjAut d F M)⁻¹ := by
  have hEI : ∀ x ∈ E, ∃ A : GL (Fin d) F, conjAut d F A = x := fun x hx =>
    mem_linearAutGroup_iff.mp (hElin hx)
  obtain ⟨A₀, hA₀, -, -⟩ := TypeA.exists_diagonalizing_slLift hp hpF hd hpd E hEc hEp hEI
  refine ⟨A₀⁻¹, fun φ hφ => ?_⟩
  obtain ⟨A, rfl⟩ := hEI φ hφ
  obtain ⟨g, hgp, hgA⟩ := TypeA.exists_slLift hd hpd (A := A) (hEp _ hφ)
  have hg : g ∈ TypeA.slLift hd hpd E hEc := ⟨hgp, hgA ▸ hφ⟩
  refine ⟨A₀ * Matrix.SpecialLinearGroup.toGL g * A₀⁻¹, fun i j hij => ?_, ?_⟩
  · have h1 := hA₀ g hg i j hij
    rw [TypeA.conjMat] at h1
    rw [Units.val_mul, Units.val_mul]
    exact h1
  · rw [← hgA, map_mul, map_mul, map_inv, inv_inv]
    group

theorem mem_zpowers_of_pow_eq_one {Γ : Type*} [Group Γ] [Finite Γ] [IsCyclic Γ] {p : ℕ}
    (hp : 0 < p) {σ τ : Γ} (hσ : orderOf σ = p) (hτ : τ ^ p = 1) : τ ∈ Subgroup.zpowers σ := by
  classical
  have := Fintype.ofFinite Γ
  by_contra hτσ
  have h1 := IsCyclic.card_pow_eq_one_le (α := Γ) hp
  have hsub : insert τ (Subgroup.zpowers σ : Set Γ).toFinset ⊆
      Finset.univ.filter (fun a : Γ => a ^ p = 1) := by
    intro a ha
    rw [Finset.mem_insert] at ha
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ a, ?_⟩
    rcases ha with rfl | ha
    · exact hτ
    · rw [Set.mem_toFinset] at ha
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
      rw [← zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul, zpow_natCast, ← hσ,
        pow_orderOf_eq_one, _root_.one_zpow]
  have hcard := Finset.card_le_card hsub
  have hzc : (Subgroup.zpowers σ : Set Γ).toFinset.card = p := by
    rw [← Nat.card_eq_card_toFinset]
    exact (Nat.card_zpowers σ).trans hσ
  rw [Finset.card_insert_of_notMem (by rwa [Set.mem_toFinset]), hzc] at hcard
  omega

theorem map_eq_of_mem_slLift [Finite F] {p : ℕ} (hd : 0 < d) (hpd : Nat.Coprime p d)
    {X : Subgroup (MulAut (projectiveSL d F))} (hXc : ∀ x ∈ X, ∀ y ∈ X, x * y = y * x)
    {σ : F ≃+* F} (hXσ : ∀ x ∈ X, fieldAut d F σ * x = x * fieldAut d F σ)
    {g : Matrix.SpecialLinearGroup (Fin d) F} (hg : g ∈ TypeA.slLift hd hpd X hXc) :
    Matrix.SpecialLinearGroup.map σ.toRingHom g = g := by
  refine TypeA.eq_of_slLift hd hpd (by rw [← map_pow, hg.1, map_one]) hg.1 ?_
  have htr := (standard_automorphism_transport (n := d) (K := F)).2.2.1 σ
    (Matrix.SpecialLinearGroup.toGL g)
  have h1 : Matrix.GeneralLinearGroup.map (σ : F →+* F) (Matrix.SpecialLinearGroup.toGL g) =
      Matrix.SpecialLinearGroup.toGL (Matrix.SpecialLinearGroup.map σ.toRingHom g) :=
    Units.ext rfl
  rw [← h1, ← htr, hXσ _ hg.2, mul_inv_cancel_right]

theorem exists_map_eq_of_map_eq {σ : F ≃+* F} {g : Matrix.SpecialLinearGroup (Fin d) F}
    (hg : Matrix.SpecialLinearGroup.map σ.toRingHom g = g) :
    ∃ g' : Matrix.SpecialLinearGroup (Fin d) (semilinearFixedSubfield σ),
      Matrix.SpecialLinearGroup.map (semilinearFixedSubfield σ).subtype g' = g := by
  have hfix : ∀ i j, σ ((g : Matrix (Fin d) (Fin d) F) i j) = (g : Matrix (Fin d) (Fin d) F) i j :=
    fun i j => congrArg (fun h : Matrix.SpecialLinearGroup (Fin d) F =>
      (h : Matrix (Fin d) (Fin d) F) i j) hg
  let m : Matrix (Fin d) (Fin d) (semilinearFixedSubfield σ) := fun i j =>
    ⟨(g : Matrix (Fin d) (Fin d) F) i j, hfix i j⟩
  have hm : (semilinearFixedSubfield σ).subtype.mapMatrix m = (g : Matrix (Fin d) (Fin d) F) := by
    ext i j
    rfl
  have hdet : m.det = 1 := by
    apply (semilinearFixedSubfield σ).subtype_injective
    rw [RingHom.map_det, hm, map_one, Matrix.SpecialLinearGroup.det_coe]
  exact ⟨⟨m, hdet⟩, Matrix.SpecialLinearGroup.ext _ _ fun i j => rfl⟩

theorem dvd_sub_one_of_dvd_pow_sub_one {p q₀ : ℕ} (hp : p.Prime) (hq : 1 ≤ q₀)
    (h : p ∣ q₀ ^ p - 1) : p ∣ q₀ - 1 := by
  have : Fact p.Prime := ⟨hp⟩
  have h1 : ((q₀ ^ p - 1 : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr h
  rw [Nat.cast_sub (Nat.one_le_pow _ _ hq), Nat.cast_pow, ZMod.pow_card, Nat.cast_one] at h1
  rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub hq, Nat.cast_one]
  exact h1

theorem map_pow_map_subtype {σ : F ≃+* F} (N₀ : GL (Fin d) (semilinearFixedSubfield σ)) (j : ℕ) :
    Matrix.GeneralLinearGroup.map ((σ ^ j : F ≃+* F) : F →+* F)
      (Matrix.GeneralLinearGroup.map (semilinearFixedSubfield σ).subtype N₀) =
      Matrix.GeneralLinearGroup.map (semilinearFixedSubfield σ).subtype N₀ := by
  apply Units.ext
  ext a b
  change (σ ^ j) (((N₀ : Matrix _ _ (semilinearFixedSubfield σ)) a b : F)) =
    ((N₀ : Matrix _ _ (semilinearFixedSubfield σ)) a b : F)
  have h0 : (((N₀ : Matrix (Fin d) (Fin d) (semilinearFixedSubfield σ)) a b :
      semilinearFixedSubfield σ) : F) ∈ semilinearFixedSubfield σ := Subtype.mem _
  exact Subgroup.pow_mem (fixingSubgroup _) h0 j

theorem exists_frame_of_not_le_linear [Finite F] {p : ℕ} (hp : p.Prime)
    (hpF : p ∣ Nat.card F - 1) (hd : 3 ≤ d) (hpd : ¬ p ∣ d)
    (E : Subgroup (MulAut (projectiveSL d F))) (hEc : ∀ φ ∈ E, ∀ ψ ∈ E, φ * ψ = ψ * φ)
    (hEp : ∀ φ ∈ E, φ ^ p = 1) (hEs : E ≤ semilinearAutGroup d F)
    {a : MulAut (projectiveSL d F)} (haE : a ∈ E) (haD : a ∉ linearAutGroup d F) :
    ∃ (M : GL (Fin d) F) (σ : F ≃+* F), σ ^ p = 1 ∧
      (∀ φ ∈ E, ∃ (D₁ : GL (Fin d) F) (k : ℕ), (D₁ : Matrix (Fin d) (Fin d) F).IsDiag ∧
        (∀ i, σ ((D₁ : Matrix (Fin d) (Fin d) F) i i) = (D₁ : Matrix (Fin d) (Fin d) F) i i) ∧
        φ = conjAut d F M * conjAut d F D₁ * fieldAut d F (σ ^ k) * (conjAut d F M)⁻¹) ∧
      ∃ ω : Fˣ, σ ω = ω ∧ ω ^ p = 1 ∧ ω ≠ 1 := by
  classical
  have := Fintype.ofFinite F
  have hd0 : 0 < d := by omega
  have hpd' : Nat.Coprime p d := (Nat.Prime.coprime_iff_not_dvd hp).mpr hpd
  have hℓ : (ringChar F).Prime := CharP.char_is_prime F (ringChar F)
  obtain ⟨f, -, hf⟩ := FiniteField.card F (ringChar F)
  have hcard : Nat.card F = ringChar F ^ (f : ℕ) := by rw [Nat.card_eq_fintype_card, hf]
  have hpℓ : p ≠ ringChar F := by
    intro h
    rw [hcard, ← h] at hpF
    have h1 : p ∣ p ^ (f : ℕ) := dvd_pow_self p f.ne_zero
    have h2 : p ∣ 1 := by
      have := Nat.dvd_sub h1 hpF
      rwa [Nat.sub_sub_self (Nat.one_le_pow _ _ hp.pos)] at this
    exact hp.one_lt.ne' (Nat.dvd_one.mp h2)
  have : Fact p.Prime := ⟨hp⟩
  have hao : orderOf a = p :=
    orderOf_eq_prime (hEp a haE) (fun h => haD (h ▸ Subgroup.one_mem _))
  obtain ⟨-, -, -, -, -, -, -, hdesc⟩ :=
    CFSG.RankThree.LinearDescent.higher_linear_prime_semilinear_field_descent (K := F) (n := d)
      hℓ f.pos hd hcard
  obtain ⟨hpf, σ, hσo, ⟨h, hhD, hah⟩, hF₀⟩ := hdesc p hp hpℓ a (hEs haE) haD hao
  obtain ⟨M₀, rfl⟩ := mem_linearAutGroup_iff.mp hhD
  set c := conjAut d F M₀ with hc
  set X : Subgroup (MulAut (projectiveSL d F)) :=
    (E ⊓ linearAutGroup d F).map (MulAut.conj c⁻¹).toMonoidHom with hX
  have hXmem : ∀ x ∈ X, ∃ φ ∈ E, φ ∈ linearAutGroup d F ∧ x = c⁻¹ * φ * c := by
    rintro _ ⟨φ, ⟨hφE, hφD⟩, rfl⟩
    exact ⟨φ, hφE, hφD, by rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]⟩
  have hXc : ∀ x ∈ X, ∀ y ∈ X, x * y = y * x := by
    intro x hx y hy
    obtain ⟨φ, hφ, -, rfl⟩ := hXmem x hx
    obtain ⟨ψ, hψ, -, rfl⟩ := hXmem y hy
    calc c⁻¹ * φ * c * (c⁻¹ * ψ * c) = c⁻¹ * (φ * ψ) * c := by group
      _ = c⁻¹ * (ψ * φ) * c := by rw [hEc φ hφ ψ hψ]
      _ = c⁻¹ * ψ * c * (c⁻¹ * φ * c) := by group
  have hXp : ∀ x ∈ X, x ^ p = 1 := by
    intro x hx
    obtain ⟨φ, hφ, -, rfl⟩ := hXmem x hx
    have h1 : c⁻¹ * φ * c = MulAut.conj c⁻¹ φ := by rw [MulAut.conj_apply, inv_inv]
    rw [h1, ← map_pow, hEp φ hφ, map_one]
  have hXσ : ∀ x ∈ X, fieldAut d F σ * x = x * fieldAut d F σ := by
    intro x hx
    obtain ⟨φ, hφ, -, rfl⟩ := hXmem x hx
    have h1 := hEc φ hφ a haE
    rw [hah] at h1
    calc fieldAut d F σ * (c⁻¹ * φ * c) = c⁻¹ * ((c * fieldAut d F σ * c⁻¹) * φ) * c := by group
      _ = c⁻¹ * (φ * (c * fieldAut d F σ * c⁻¹)) * c := by rw [h1]
      _ = c⁻¹ * φ * c * fieldAut d F σ := by group
  have hXI : ∀ x ∈ X, ∃ A : GL (Fin d) F, conjAut d F A = x := by
    intro x hx
    obtain ⟨φ, -, hφD, rfl⟩ := hXmem x hx
    obtain ⟨B, rfl⟩ := mem_linearAutGroup_iff.mp hφD
    exact ⟨M₀⁻¹ * B * M₀, by rw [map_mul, map_mul, map_inv]⟩
  have hq₀ : 1 ≤ ringChar F ^ ((f : ℕ) / p) := Nat.one_le_pow _ _ hℓ.pos
  have hpF₀ : p ∣ Nat.card (semilinearFixedSubfield σ) - 1 := by
    rw [hF₀]
    apply dvd_sub_one_of_dvd_pow_sub_one hp hq₀
    rw [← pow_mul, Nat.div_mul_cancel hpf, ← hcard]
    exact hpF
  obtain ⟨ζ, hζ⟩ := TypeA.exists_isPrimitiveRoot (K := semilinearFixedSubfield σ) hp hpF₀
  set Y : Subgroup (Matrix.SpecialLinearGroup (Fin d) (semilinearFixedSubfield σ)) :=
    (TypeA.slLift hd0 hpd' X hXc).comap
      (Matrix.SpecialLinearGroup.map (semilinearFixedSubfield σ).subtype) with hY
  have hmapinj : Function.Injective
      (Matrix.SpecialLinearGroup.map (n := Fin d) (semilinearFixedSubfield σ).subtype) := by
    intro g₁ g₂ hg
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    apply (semilinearFixedSubfield σ).subtype_injective
    exact congrArg (fun k : Matrix.SpecialLinearGroup (Fin d) F => (k : Matrix _ _ F) i j) hg
  have hYc : ∀ x ∈ Y, ∀ y ∈ Y, x * y = y * x := by
    intro x hx y hy
    apply hmapinj
    rw [map_mul, map_mul]
    exact TypeA.slLift_comm hd0 hpd' X hXc hx hy
  have hYp : ∀ x ∈ Y, x ^ p = 1 := by
    intro x hx
    apply hmapinj
    rw [map_pow, map_one]
    exact hx.1
  have : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨N₀, hN₀⟩ :=
    CFSG.RankThree.PartOne.exists_conj_diagonal_of_commuting_pow_eq_one hζ Y hYc hYp
  set N := Matrix.GeneralLinearGroup.map (semilinearFixedSubfield σ).subtype N₀ with hN
  have hIsCyc : IsCyclic (F ≃+* F) := by
    obtain ⟨φ₁, -, -, htop, -, -⟩ :=
      finite_field_automorphism_fixed_field_cardinality hℓ f.pos hcard
    exact isCyclic_iff_exists_zpowers_eq_top.mpr ⟨φ₁, htop⟩
  have : Finite (F ≃+* F) := Finite.of_injective _ DFunLike.coe_injective
  have hσfin : IsOfFinOrder σ := orderOf_pos_iff.mp (by rw [hσo]; exact hp.pos)
  refine ⟨M₀ * N⁻¹, σ, hσo ▸ pow_orderOf_eq_one σ, fun φ hφ => ?_, ?_⟩
  ·
    obtain ⟨B, τ, hBτ⟩ := mem_semilinearAutGroup_iff.mp (hEs hφ)
    have hτp : τ ^ p = 1 := by
      have h1 := hEp φ hφ
      rw [hBτ, CFSG.RankThree.LinearDescent.conjAut_mul_fieldAut_pow] at h1
      exact (eq_one_of_conjAut_mul_fieldAut_eq_one hd _ _ h1).1
    obtain ⟨j, hj⟩ : ∃ j : ℕ, σ ^ j = τ :=
      hσfin.mem_powers_iff_mem_zpowers.mpr (mem_zpowers_of_pow_eq_one hp.pos hσo hτp)
    have haj : a ^ j = c * fieldAut d F (σ ^ j) * c⁻¹ := by
      rw [hah, conj_pow, map_pow]
    set ψ := φ * (a ^ j)⁻¹ with hψ
    have hψE : ψ ∈ E := E.mul_mem hφ (E.inv_mem (E.pow_mem haE j))
    have hψD : ψ ∈ linearAutGroup d F := by
      have htr := (standard_automorphism_transport (n := d) (K := F)).2.2.1 τ M₀
      have e1 : ψ = conjAut d F B * (fieldAut d F τ * c * (fieldAut d F τ)⁻¹) * c⁻¹ := by
        rw [hψ, hBτ, haj, hj]
        group
      rw [e1, hc, htr]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (conjAut_mem_linearAutGroup B)
        (conjAut_mem_linearAutGroup _)) (Subgroup.inv_mem _ (conjAut_mem_linearAutGroup M₀))
    have hxX : c⁻¹ * ψ * c ∈ X :=
      ⟨ψ, ⟨hψE, hψD⟩, by rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]⟩
    obtain ⟨A, hA⟩ := hXI _ hxX
    obtain ⟨g, hgp, hgA⟩ := TypeA.exists_slLift hd0 hpd' (A := A) (by rw [hA]; exact hXp _ hxX)
    have hgL : g ∈ TypeA.slLift hd0 hpd' X hXc := ⟨hgp, by rw [hgA, hA]; exact hxX⟩
    obtain ⟨g', hg'⟩ := exists_map_eq_of_map_eq (map_eq_of_mem_slLift hd0 hpd' hXc hXσ hgL)
    have hg'Y : g' ∈ Y := by
      change Matrix.SpecialLinearGroup.map (semilinearFixedSubfield σ).subtype g' ∈
        TypeA.slLift hd0 hpd' X hXc
      rw [hg']
      exact hgL
    have hD₁ : ((N * Matrix.SpecialLinearGroup.toGL g * N⁻¹ : GL (Fin d) F) :
        Matrix (Fin d) (Fin d) F) = (semilinearFixedSubfield σ).subtype.mapMatrix
          ((N₀ : Matrix (Fin d) (Fin d) (semilinearFixedSubfield σ)) *
            (g' : Matrix (Fin d) (Fin d) (semilinearFixedSubfield σ)) *
            ((N₀⁻¹ : GL (Fin d) (semilinearFixedSubfield σ)) :
              Matrix (Fin d) (Fin d) (semilinearFixedSubfield σ))) := by
      rw [map_mul, map_mul, hN, ← hg', ← map_inv]
      rfl
    have hcomm : fieldAut d F (σ ^ j) * conjAut d F N = conjAut d F N * fieldAut d F (σ ^ j) := by
      have htr := (standard_automorphism_transport (n := d) (K := F)).2.2.1 (σ ^ j) N
      rw [hN, map_pow_map_subtype N₀ j, ← hN] at htr
      calc fieldAut d F (σ ^ j) * conjAut d F N
          = fieldAut d F (σ ^ j) * conjAut d F N * (fieldAut d F (σ ^ j))⁻¹ *
              fieldAut d F (σ ^ j) := by group
        _ = conjAut d F N * fieldAut d F (σ ^ j) := by rw [htr]
    have hNf : (conjAut d F N)⁻¹ * fieldAut d F (σ ^ j) * conjAut d F N =
        fieldAut d F (σ ^ j) := by
      rw [mul_assoc, hcomm, inv_mul_cancel_left]
    refine ⟨N * Matrix.SpecialLinearGroup.toGL g * N⁻¹, j, fun i i' hii' => ?_, fun i => ?_, ?_⟩
    · change ((N * Matrix.SpecialLinearGroup.toGL g * N⁻¹ : GL (Fin d) F) :
        Matrix (Fin d) (Fin d) F) i i' = 0
      rw [hD₁, RingHom.mapMatrix_apply, Matrix.map_apply, hN₀ g' hg'Y i i' hii', map_zero]
    · rw [hD₁, RingHom.mapMatrix_apply, Matrix.map_apply]
      exact (((N₀ : Matrix (Fin d) (Fin d) (semilinearFixedSubfield σ)) *
        (g' : Matrix (Fin d) (Fin d) (semilinearFixedSubfield σ)) *
        ((N₀⁻¹ : GL (Fin d) (semilinearFixedSubfield σ)) :
          Matrix (Fin d) (Fin d) (semilinearFixedSubfield σ))) i i).2
    · have hψeq : ψ = c * conjAut d F (Matrix.SpecialLinearGroup.toGL g) * c⁻¹ := by
        rw [hgA, hA]
        group
      calc φ = ψ * a ^ j := by rw [hψ, inv_mul_cancel_right]
        _ = c * conjAut d F (Matrix.SpecialLinearGroup.toGL g) * fieldAut d F (σ ^ j) * c⁻¹ := by
            rw [hψeq, haj]
            group
        _ = c * conjAut d F (Matrix.SpecialLinearGroup.toGL g) *
            ((conjAut d F N)⁻¹ * fieldAut d F (σ ^ j) * conjAut d F N) * c⁻¹ := by rw [hNf]
        _ = conjAut d F (M₀ * N⁻¹) * conjAut d F (N * Matrix.SpecialLinearGroup.toGL g * N⁻¹) *
            fieldAut d F (σ ^ j) * (conjAut d F (M₀ * N⁻¹))⁻¹ := by
            simp only [map_mul, map_inv, ← hc]
            group
  ·
    have hζ0 : (ζ : F) ≠ 0 := fun h0 => hζ.ne_zero hp.ne_zero (Subtype.ext h0)
    refine ⟨Units.mk0 (ζ : F) hζ0, ζ.2, Units.ext ?_, fun h1 => ?_⟩
    · rw [Units.val_pow_eq_pow_val, Units.val_mk0, Units.val_one]
      exact congrArg Subtype.val hζ.pow_eq_one
    · have h2 : (ζ : F) = 1 := congrArg Units.val h1
      exact hζ.ne_one hp.one_lt (Subtype.ext h2)

theorem isDiag_of_diagonal_mul_eq {t : Fin d → F} (ht : ∀ i j, i ≠ j → t i ≠ t j)
    {X : Matrix (Fin d) (Fin d) F} (h : diagonal t * X = X * diagonal t) : X.IsDiag := by
  intro i j hij
  have h1 := congrFun (congrFun h i) j
  rw [diagonal_mul, mul_diagonal] at h1
  have h2 : (t i - t j) * X i j = 0 := by
    rw [sub_mul, h1, mul_comm (t j), sub_self]
  rcases mul_eq_zero.mp h2 with h3 | h3
  · exact absurd (sub_eq_zero.mp h3) (ht i j hij)
  · exact h3

theorem isDiag_conj_of_commute {M D₁ : GL (Fin d) F}
    (hD₁ : (D₁ : Matrix (Fin d) (Fin d) F).IsDiag)
    (hdist : ∀ i k : Fin d, i ≠ k →
      (D₁ : Matrix (Fin d) (Fin d) F) i i ≠ (D₁ : Matrix (Fin d) (Fin d) F) k k)
    {X : Matrix (Fin d) (Fin d) F}
    (hX : ((M * D₁ * M⁻¹ : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) * X =
      X * ((M * D₁ * M⁻¹ : GL (Fin d) F) : Matrix (Fin d) (Fin d) F)) :
    (((M⁻¹ : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) * X *
      (M : Matrix (Fin d) (Fin d) F)).IsDiag := by
  set m := (M : Matrix (Fin d) (Fin d) F)
  set mi := ((M⁻¹ : GL (Fin d) F) : Matrix (Fin d) (Fin d) F)
  set D := (D₁ : Matrix (Fin d) (Fin d) F)
  have h1 : m * mi = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have h2 : mi * m = 1 := by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hDt : D = diagonal (diag D) := ((isDiag_iff_diagonal_diag _).mp hD₁).symm
  apply isDiag_of_diagonal_mul_eq (t := diag D) (fun i j hij => hdist i j hij)
  rw [← hDt]
  have hA : ((M * D₁ * M⁻¹ : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) = m * D * mi := by
    rw [Units.val_mul, Units.val_mul]
  rw [hA] at hX
  have e1 : D * (mi * X * m) = mi * ((m * D * mi * X) * m) := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc mi m, h2, Matrix.one_mul]
  have e2 : mi * ((X * (m * D * mi)) * m) = mi * X * m * D := by
    simp only [Matrix.mul_assoc]
    rw [h2, Matrix.mul_one]
  rw [e1, hX, e2]

end NbrLangTypeA

open NbrLangTypeA CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  Matrix CFSG.ComponentClassification
open scoped commutatorElement

theorem ggTypeARegularCentralizerInput_holds : GGTypeARegularCentralizerInput := by
  intro d F _ _ M D₁ _ hD₁ hdist
  set A := M * D₁ * M⁻¹ with hAdef
  have hαA : conjAut d F M * conjAut d F D₁ * (conjAut d F M)⁻¹ = conjAut d F A := by
    rw [hAdef, map_mul, map_mul, map_inv]
  rw [hαA]
  set H := (conjAut d F A).toMonoidHom.eqLocus (MonoidHom.id (projectiveSL d F)) with hH
  set C : Subgroup (Matrix.SpecialLinearGroup (Fin d) F) :=
    (CatalogueBHigherLinearAction.slConjugation d F A).toMonoidHom.eqLocus (MonoidHom.id _)
    with hC
  set m := (M : Matrix (Fin d) (Fin d) F)
  set mi := ((M⁻¹ : GL (Fin d) F) : Matrix (Fin d) (Fin d) F)
  have hm1 : m * mi = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hm2 : mi * m = 1 := by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have key : ∀ k ∈ C, (mi * (k : Matrix (Fin d) (Fin d) F) * m).IsDiag := by
    intro k hk
    apply isDiag_conj_of_commute hD₁ hdist
    have hk' : CatalogueBHigherLinearAction.slConjugation d F A k = k := hk
    have h1 := congrArg (fun z : Matrix.SpecialLinearGroup (Fin d) F =>
      (z : Matrix (Fin d) (Fin d) F)) hk'
    simp only [LinearFlag.coe_slConjugation] at h1
    have hA2 : ((A⁻¹ : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) *
        (A : Matrix (Fin d) (Fin d) F) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    calc (A : Matrix (Fin d) (Fin d) F) * (k : Matrix (Fin d) (Fin d) F)
        = (A : Matrix (Fin d) (Fin d) F) * (k : Matrix (Fin d) (Fin d) F) *
            (((A⁻¹ : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) *
              (A : Matrix (Fin d) (Fin d) F)) := by rw [hA2, Matrix.mul_one]
      _ = (k : Matrix (Fin d) (Fin d) F) * (A : Matrix (Fin d) (Fin d) F) := by
          rw [← Matrix.mul_assoc, h1]
  have hCcomm : ∀ g ∈ C, ∀ h ∈ C, g * h = h * g := by
    intro g hg h hh
    have hgd := key g hg
    have hhd := key h hh
    have hXY : (mi * (g : Matrix (Fin d) (Fin d) F) * m) *
        (mi * (h : Matrix (Fin d) (Fin d) F) * m) =
        (mi * (h : Matrix (Fin d) (Fin d) F) * m) *
        (mi * (g : Matrix (Fin d) (Fin d) F) * m) := by
      rw [← (isDiag_iff_diagonal_diag _).mp hgd, ← (isDiag_iff_diagonal_diag _).mp hhd,
        diagonal_mul_diagonal, diagonal_mul_diagonal]
      congr 1
      funext j
      exact mul_comm _ _
    have hg' : (g : Matrix (Fin d) (Fin d) F) =
        m * (mi * (g : Matrix (Fin d) (Fin d) F) * m) * mi := by
      simp only [Matrix.mul_assoc]
      rw [hm1, Matrix.mul_one, ← Matrix.mul_assoc, hm1, Matrix.one_mul]
    have hh' : (h : Matrix (Fin d) (Fin d) F) =
        m * (mi * (h : Matrix (Fin d) (Fin d) F) * m) * mi := by
      simp only [Matrix.mul_assoc]
      rw [hm1, Matrix.mul_one, ← Matrix.mul_assoc, hm1, Matrix.one_mul]
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hg', hh']
    have e : ∀ X Y : Matrix (Fin d) (Fin d) F, m * X * mi * (m * Y * mi) = m * (X * Y) * mi := by
      intro X Y
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc mi m, hm2, Matrix.one_mul]
    rw [e, e, hXY]
  set Q₀ := C.map (proj d F) with hQ₀def
  have hQ₀ : ∀ a ∈ Q₀, ∀ b ∈ Q₀, a * b = b * a := by
    rintro _ ⟨g, hg, rfl⟩ _ ⟨h, hh, rfl⟩
    rw [← map_mul, ← map_mul, hCcomm g hg h hh]
  have hz : ∀ g : Matrix.SpecialLinearGroup (Fin d) F, proj d F g ∈ H →
      g⁻¹ * CatalogueBHigherLinearAction.slConjugation d F A g ∈
        Subgroup.center (Matrix.SpecialLinearGroup (Fin d) F) := by
    intro g hg
    have hg' : conjAut d F A (proj d F g) = proj d F g := hg
    rw [conjAut_proj] at hg'
    have h1 := proj_eq_proj_iff.mp hg'.symm
    rwa [scalars_eq_center] at h1
  have hle : ⁅H, H⁆ ≤ Q₀ := by
    rw [Subgroup.commutator_le]
    intro q₁ hq₁ q₂ hq₂
    obtain ⟨g₁, rfl⟩ := proj_surjective d F q₁
    obtain ⟨g₂, rfl⟩ := proj_surjective d F q₂
    refine ⟨⁅g₁, g₂⁆, ?_, map_commutatorElement _ _ _⟩
    change CatalogueBHigherLinearAction.slConjugation d F A ⁅g₁, g₂⁆ = ⁅g₁, g₂⁆
    have e1 : CatalogueBHigherLinearAction.slConjugation d F A g₁ =
        g₁ * (g₁⁻¹ * CatalogueBHigherLinearAction.slConjugation d F A g₁) := by group
    have e2 : CatalogueBHigherLinearAction.slConjugation d F A g₂ =
        g₂ * (g₂⁻¹ * CatalogueBHigherLinearAction.slConjugation d F A g₂) := by group
    rw [map_commutatorElement, e1, e2, commutatorElement_mul_mem_center (hz g₁ hq₁) (hz g₂ hq₂)]
  have hmap : (commutator ↥H).map H.subtype = ⁅H, H⁆ := by
    rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hab : ∀ a b : ↥(commutator ↥H), a * b = b * a := by
    intro a b
    have ha : ((a : ↥H) : projectiveSL d F) ∈ Q₀ := hle (by rw [← hmap]; exact ⟨a, a.2, rfl⟩)
    have hb : ((b : ↥H) : projectiveSL d F) ∈ Q₀ := hle (by rw [← hmap]; exact ⟨b, b.2, rfl⟩)
    apply Subtype.ext
    apply Subtype.ext
    exact hQ₀ _ ha _ hb
  have : Group.IsSolvable ↥(commutator ↥H) := Group.isSolvable_of_comm hab
  have : Group.IsSolvable (Abelianization ↥H) := Group.isSolvable_of_comm mul_comm
  exact Group.isSolvable_of_ker_le_range (commutator ↥H).subtype Abelianization.of
    (by rw [Abelianization.ker_of, Subgroup.range_subtype])


theorem ggTypeASplitFrameInput_holds : GGTypeASplitFrameInput := by
  intro p d F _ _ hp _ hd hpF hpd E hEc hEp hEs
  by_cases hlin : E ≤ linearAutGroup d F
  · obtain ⟨M, hM⟩ := exists_frame_of_le_linear hp hpF (by omega)
      ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpd) E hEc hEp hlin
    obtain ⟨ζ, hζ⟩ := TypeA.exists_isPrimitiveRoot (K := F) hp hpF
    have hζ0 : ζ ≠ 0 := hζ.ne_zero hp.ne_zero
    refine ⟨M, 1, one_pow p, fun φ hφ => ?_, Units.mk0 ζ hζ0, rfl, Units.ext ?_, fun h => ?_⟩
    · obtain ⟨D₁, hD₁, rfl⟩ := hM φ hφ
      exact ⟨D₁, 0, hD₁, fun i => rfl, by rw [pow_zero, map_one, mul_one]⟩
    · rw [Units.val_pow_eq_pow_val, Units.val_mk0, Units.val_one]
      exact hζ.pow_eq_one
    · exact hζ.ne_one hp.one_lt (congrArg Units.val h)
  · obtain ⟨a, haE, haD⟩ := Set.not_subset.mp hlin
    exact exists_frame_of_not_le_linear hp hpF hd hpd E hEc hEp hEs haE haD

theorem ggNbrLangTorusAxisOn_typeASplit_holds :
    GGNbrLangTorusAxisOn GGTypeASplitCoprimeLabel :=
  ggNbrLangTorusAxisOn_typeASplit ggTypeASplitFrameInput_holds

theorem ggNbrInnerWeylOn_typeASplit_holds (hnonreg : GGNbrTypeAXNonRegularInput) :
    GGNbrInnerWeylOn GGTypeASplitCoprimeLabel :=
  ggNbrInnerWeylOn_typeASplit ggTypeASplitFrameInput_holds hnonreg

theorem ggNbrInnerWeylOn_typeASplit_of_repeated (hrep : GGNbrTypeAXRepeatedInput) :
    GGNbrInnerWeylOn GGTypeASplitCoprimeLabel :=
  ggNbrInnerWeylOn_typeASplit_holds (ggNbrTypeAXNonRegularInput_of_repeated hrep)

theorem ggNbrInnerWeylOn_typeASplit_of_subcomponent (hI3 : GGNbrSubcomponentInput) :
    GGNbrInnerWeylOn GGTypeASplitCoprimeLabel :=
  ggNbrInnerWeylOn_typeASplit_of_repeated
    (ggNbrTypeAXRepeatedInput_of_regular hI3 ggTypeARegularCentralizerInput_holds)

theorem ggNbrLangTorusAxisInput_of_typeASplit_rest
    (hrest : GGNbrLangTorusAxisOn fun p lab => ¬ GGTypeASplitCoprimeLabel p lab) :
    GGNbrLangTorusAxisInput :=
  ggNbrLangTorusAxisInput_of_typeASplit ggTypeASplitFrameInput_holds hrest

theorem ggXNotNormalInput_of_typeASplit_rest (hnorm : GGBstarNbrNormalInput)
    (hgraph : GGNbrGraphInput) (hI3 : GGNbrSubcomponentInput)
    (hlang : GGNbrLangTorusAxisOn fun p lab => ¬ GGTypeASplitCoprimeLabel p lab)
    (hweyl : GGNbrInnerWeylOn fun p lab => ¬ GGTypeASplitCoprimeLabel p lab) :
    GGXNotNormalInput :=
  ggXNotNormalInput_of_typeASplit hnorm hgraph ggTypeASplitFrameInput_holds
    (ggNbrTypeAXNonRegularInput_of_repeated
      (ggNbrTypeAXRepeatedInput_of_regular hI3 ggTypeARegularCentralizerInput_holds)) hlang hweyl

theorem ggNbrFieldTransvectionInput_of_typeASplit_rest
    (hlang : GGNbrLangTorusAxisOn fun p lab => ¬ GGTypeASplitCoprimeLabel p lab) :
    GGNbrFieldTransvectionInput :=
  ggNbrFieldTransvectionInput_of_typeASplit ggTypeASplitFrameInput_holds hlang

end CFSG.StandardType

end
