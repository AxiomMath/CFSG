module

public import CFSG.RankThree.PartTwo.KFacts.K71SU3
import CFSG.RankThree.PartTwo.KFacts.AutKindsUnique
import CFSG.Adapters.RankTwoModelTransports
import CFSG.RankThree.PartTwo.KFacts.AutPSUScalar

public section

namespace CFSG.RankThree.PartTwo.KFacts

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (glAut coe_glAut)
open CFSG.GH74.GLS.IVK (fixedField mem_fixedField_iff fixedField_apply fixedField_card_pow)
open CFSG.Assembly.LowTwoRank
open CFSG.Assembly.RankThreeEven (projImage)
open Matrix

theorem mem_of_pow_card_eq_one_of_isCyclic {C : Type*} [Group C] [Finite C] [IsCyclic C]
    (H : Subgroup C) {x : C} (hx : x ^ Nat.card H = 1) : x ∈ H := by
  classical
  have := Fintype.ofFinite C
  have hpos : 0 < Nat.card H := Nat.card_pos
  have hle := IsCyclic.card_pow_eq_one_le (α := C) hpos
  have hsub : (H : Set C).toFinset ⊆ Finset.univ.filter (fun a : C => a ^ Nat.card H = 1) := by
    intro y hy
    rw [Set.mem_toFinset] at hy
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    have h1 : (⟨y, hy⟩ : H) ^ Nat.card H = 1 := pow_card_eq_one'
    exact congrArg Subtype.val h1
  have hcard : (H : Set C).toFinset.card = Nat.card H := by
    rw [Set.toFinset_card, ← Nat.card_eq_fintype_card]
    rfl
  have heq := Finset.eq_of_subset_of_card_le hsub (by rw [hcard]; exact hle)
  have hxS : x ∈ Finset.univ.filter (fun a : C => a ^ Nat.card H = 1) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩
  rw [← heq, Set.mem_toFinset] at hxS
  exact hxS

theorem add_one_dvd_pow_three_add_one (q₀ : ℕ) : q₀ + 1 ∣ q₀ ^ 3 + 1 :=
  ⟨q₀ ^ 2 + 1 - q₀, by
    zify [show q₀ ≤ q₀ ^ 2 + 1 by nlinarith]
    ring⟩

theorem three_mul_dvd_pow_three_add_one {q₀ : ℕ} (h : 3 ∣ q₀ ^ 3 + 1) :
    3 * (q₀ + 1) ∣ q₀ ^ 3 + 1 := by
  have h1 : 3 ∣ q₀ + 1 := by
    have : q₀ % 3 = 0 ∨ q₀ % 3 = 1 ∨ q₀ % 3 = 2 := by omega
    rcases this with h0 | h0 | h0 <;>
      simp [Nat.dvd_iff_mod_eq_zero, Nat.add_mod, Nat.pow_mod, h0] at h ⊢
  obtain ⟨t, ht⟩ := h1
  have ht1 : 1 ≤ t := by omega
  refine ⟨3 * t ^ 2 + 1 - 3 * t, ?_⟩
  have hq : q₀ = 3 * t - 1 := by omega
  subst hq
  zify [show 1 ≤ 3 * t by omega, show 3 * t ≤ 3 * t ^ 2 + 1 by nlinarith]
  ring

theorem gcd_mul_dvd_pow_three_add_one (q₀ : ℕ) :
    (q₀ ^ 3 + 1).gcd 3 * (q₀ + 1) ∣ q₀ ^ 3 + 1 := by
  by_cases h3 : 3 ∣ q₀ ^ 3 + 1
  · rw [Nat.gcd_eq_right h3]
    exact three_mul_dvd_pow_three_add_one h3
  · have h1 : (q₀ ^ 3 + 1).gcd 3 = 1 := by
      have := Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3)
      exact this
    rw [h1, one_mul]
    exact add_one_dvd_pow_three_add_one q₀

section NormOne

variable {K : Type} [Field K] [Finite K]

abbrev normOneUnits (K : Type) [Field K] (q : ℕ) : Subgroup Kˣ :=
  (powMonoidHom (q + 1) : Kˣ →* Kˣ).ker

omit [Finite K] in
theorem mem_normOneUnits {q : ℕ} {c : Kˣ} : c ∈ normOneUnits K q ↔ c ^ (q + 1) = 1 :=
  Iff.rfl

omit [Finite K] in
theorem pow_three_add_one_eq_one {q₀ : ℕ} {δ : Kˣ} (hδ : δ ^ (q₀ + 1) = 1) :
    δ ^ (q₀ ^ 3 + 1) = 1 := by
  obtain ⟨m, hm⟩ := add_one_dvd_pow_three_add_one q₀
  rw [hm, pow_mul, hδ, one_pow]

theorem card_normOneUnits {q : ℕ} (hK : Nat.card K = q ^ 2) :
    Nat.card (normOneUnits K q) = q + 1 :=
  CFSG.SectionRank.OddCover.card_normOne hK

theorem exists_cube_root_normOne {q₀ : ℕ} (hK : Nat.card K = (q₀ ^ 3) ^ 2) {δ : Kˣ}
    (hδ : δ ^ (q₀ + 1) = 1) : ∃ c : Kˣ, c ^ (q₀ ^ 3 + 1) = 1 ∧ c ^ 3 = δ := by
  set U := normOneUnits K (q₀ ^ 3)
  have hU := card_normOneUnits hK
  have hδU : δ ∈ U := pow_three_add_one_eq_one hδ
  set R := (powMonoidHom 3 : U →* U).range
  have hR : Nat.card R = (q₀ ^ 3 + 1) / (q₀ ^ 3 + 1).gcd 3 := by
    rw [IsCyclic.card_powMonoidHom_range, hU]
  have hdvd : q₀ + 1 ∣ Nat.card R := by
    rw [hR]
    have hg : 0 < (q₀ ^ 3 + 1).gcd 3 := Nat.gcd_pos_of_pos_right _ (by norm_num)
    exact Nat.dvd_div_of_mul_dvd (gcd_mul_dvd_pow_three_add_one q₀)
  have hpow : (⟨δ, hδU⟩ : U) ^ Nat.card R = 1 := by
    obtain ⟨m, hm⟩ := hdvd
    apply Subtype.ext
    rw [hm, SubmonoidClass.coe_pow, pow_mul, hδ, one_pow]
    rfl
  obtain ⟨⟨c, hc⟩, hcd⟩ := mem_of_pow_card_eq_one_of_isCyclic R hpow
  exact ⟨c, hc, congrArg Subtype.val hcd⟩

theorem exists_normOne_field_mul_eq {q₀ : ℕ} (hK : Nat.card K = (q₀ ^ 3) ^ 2) (σ : K ≃+* K)
    (hfix : ∀ c : Kˣ, c ^ (q₀ ^ 3 + 1) = 1 → σ c = c → c ^ (q₀ + 1) = 1) {ω : Kˣ}
    (hω : ω ^ (q₀ ^ 3 + 1) = 1) (hω3 : ω ^ 3 = 1) :
    ∃ μ : Kˣ, μ ^ (q₀ ^ 3 + 1) = 1 ∧ Units.map (σ : K →* K) μ = ω * μ := by
  set U := normOneUnits K (q₀ ^ 3)
  have hU := card_normOneUnits hK
  have hσU : ∀ c ∈ U, Units.map (σ : K →* K) c ∈ U := by
    intro c hc
    rw [mem_normOneUnits] at hc ⊢
    rw [← map_pow, hc, map_one]
  let σU : U →* U :=
    ((Units.map (σ : K →* K)).comp U.subtype).codRestrict U fun c => hσU c c.2
  let θ : U →* U := σU / MonoidHom.id U
  have hθ : ∀ c : U, ((θ c : U) : Kˣ) = Units.map (σ : K →* K) c * (c : Kˣ)⁻¹ := fun c => rfl
  have hker : θ.ker ≤ (powMonoidHom (q₀ + 1) : U →* U).ker := by
    intro c hc
    rw [MonoidHom.mem_ker] at hc ⊢
    have h1 : Units.map (σ : K →* K) c = c := by
      have := congrArg Subtype.val hc
      rw [hθ, OneMemClass.coe_one, mul_inv_eq_one] at this
      exact this
    have h2 : σ ((c : Kˣ) : K) = ((c : Kˣ) : K) := by
      have := congrArg Units.val h1
      simpa using this
    apply Subtype.ext
    change (c : Kˣ) ^ (q₀ + 1) = 1
    exact hfix (c : Kˣ) c.2 h2
  have hkerdvd : Nat.card θ.ker ∣ q₀ + 1 := by
    have h1 := Subgroup.card_dvd_of_le hker
    rwa [IsCyclic.card_powMonoidHom_ker, hU,
      Nat.gcd_eq_right (add_one_dvd_pow_three_add_one q₀)] at h1
  have hcard : Nat.card θ.ker * Nat.card θ.range = q₀ ^ 3 + 1 := by
    rw [← hU, ← Subgroup.index_ker, Subgroup.card_mul_index]
  have hωg : ω ^ (q₀ ^ 3 + 1).gcd 3 = 1 := by
    rw [← orderOf_dvd_iff_pow_eq_one] at hω hω3 ⊢
    exact Nat.dvd_gcd hω hω3
  have hgdvd : (q₀ ^ 3 + 1).gcd 3 ∣ Nat.card θ.range := by
    obtain ⟨m, hm⟩ := gcd_mul_dvd_pow_three_add_one q₀
    obtain ⟨k, hk⟩ := hkerdvd
    set g := (q₀ ^ 3 + 1).gcd 3 with hg
    refine ⟨k * m, ?_⟩
    have hpos : 0 < Nat.card θ.ker := Nat.card_pos
    apply Nat.eq_of_mul_eq_mul_left hpos
    rw [hcard]
    calc q₀ ^ 3 + 1 = g * (q₀ + 1) * m := hm
      _ = Nat.card θ.ker * (g * (k * m)) := by rw [hk]; ring
  have hωU : ω ∈ U := hω
  have hpow : (⟨ω, hωU⟩ : U) ^ Nat.card θ.range = 1 := by
    obtain ⟨m, hm⟩ := hgdvd
    apply Subtype.ext
    rw [hm, SubmonoidClass.coe_pow, pow_mul, hωg, one_pow]
    rfl
  obtain ⟨μ, hμ⟩ := mem_of_pow_card_eq_one_of_isCyclic θ.range hpow
  refine ⟨μ, μ.2, ?_⟩
  have h1 : Units.map (σ : K →* K) μ * (μ : Kˣ)⁻¹ = ω := by
    rw [← hθ]
    exact congrArg Subtype.val hμ
  rw [← h1, inv_mul_cancel_right]

end NormOne

section Scalar

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)

theorem coe_scalar_mul (c : Kˣ) (M : GL (Fin 3) K) :
    ((GeneralLinearGroup.scalar (Fin 3) c * M : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      (c : K) • (M : Matrix (Fin 3) (Fin 3) K) := by
  rw [Units.val_mul, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
    ← Matrix.smul_eq_diagonal_mul]

theorem scalar_mul_mem_unitarySU {c : Kˣ} (hc : c ^ (p ^ f + 1) = 1) {M : GL (Fin 3) K}
    (hM : M ∈ unitaryIsom3 h) (hdet : (c : K) ^ 3 * (M : Matrix (Fin 3) (Fin 3) K).det = 1) :
    GeneralLinearGroup.scalar (Fin 3) c * M ∈ unitarySU p f K 3 := by
  have hN : h.bar (c : K) * c = 1 := by
    rw [mul_comm, ← UnitaryFieldData.norm, UnitaryFieldData.norm_eq_pow, ← Units.val_pow_eq_pow_val,
      hc, Units.val_one]
  refine (mem_unitarySU_iff h).mpr ⟨?_, ?_⟩
  · rw [coe_scalar_mul, Matrix.det_smul, Fintype.card_fin, hdet]
  · rw [coe_scalar_mul, map_bar_smul3, Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul,
      smul_smul, hN, one_smul]
    exact hM

theorem unitaryProj_scalar_eq {c c' : Kˣ} (hc : c ^ (p ^ f + 1) = 1) (hc' : c' ^ (p ^ f + 1) = 1)
    (h3 : c ^ 3 = c' ^ 3) {X : GL (Fin 3) K}
    (hX : GeneralLinearGroup.scalar (Fin 3) c * X ∈ unitarySU p f K 3)
    (hX' : GeneralLinearGroup.scalar (Fin 3) c' * X ∈ unitarySU p f K 3) :
    unitaryProj h 3 ⟨_, hX⟩ = unitaryProj h 3 ⟨_, hX'⟩ := by
  apply QuotientGroup.eq.mpr
  refine ⟨c⁻¹ * c', ?_, ?_, ?_⟩
  · rw [UnitaryFieldData.norm_eq_pow, ← Units.val_pow_eq_pow_val, mul_pow, inv_pow, hc, hc',
      inv_one, one_mul, Units.val_one]
  · rw [mul_pow, inv_pow, h3, inv_mul_cancel]
  · change (GeneralLinearGroup.scalar (Fin 3) c * X)⁻¹ *
        (GeneralLinearGroup.scalar (Fin 3) c' * X) =
      GeneralLinearGroup.scalar (Fin 3) (c⁻¹ * c')
    have h1 : GeneralLinearGroup.scalar (Fin 3) c' * X = X * GeneralLinearGroup.scalar (Fin 3) c' :=
      (commute_scalar c' X).eq.symm
    have h2 : (GeneralLinearGroup.scalar (Fin 3) c)⁻¹ * X =
        X * (GeneralLinearGroup.scalar (Fin 3) c)⁻¹ := by
      rw [← map_inv]
      exact (commute_scalar c⁻¹ X).eq.symm
    rw [map_mul, map_inv, _root_.mul_inv_rev, h1]
    calc X⁻¹ * (GeneralLinearGroup.scalar (Fin 3) c)⁻¹ * (X * GeneralLinearGroup.scalar (Fin 3) c')
        = X⁻¹ * ((GeneralLinearGroup.scalar (Fin 3) c)⁻¹ * X) *
            GeneralLinearGroup.scalar (Fin 3) c' := by group
      _ = X⁻¹ * (X * (GeneralLinearGroup.scalar (Fin 3) c)⁻¹) *
            GeneralLinearGroup.scalar (Fin 3) c' := by rw [h2]
      _ = (GeneralLinearGroup.scalar (Fin 3) c)⁻¹ * GeneralLinearGroup.scalar (Fin 3) c' := by
          group

end Scalar

section Incl

variable {K : Type} [Field K] (σ : K ≃+* K)

noncomputable abbrev glIncl : GL (Fin 3) (fixedField σ) →* GL (Fin 3) K :=
  GeneralLinearGroup.map (fixedField σ).subtype

variable {σ}

theorem coe_glIncl (A : GL (Fin 3) (fixedField σ)) :
    ((glIncl σ A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      (A : Matrix (Fin 3) (Fin 3) (fixedField σ)).map (fixedField σ).subtype := by
  ext i j
  rw [GeneralLinearGroup.map_apply, Matrix.map_apply]

theorem glIncl_injective : Function.Injective (glIncl σ) := by
  intro A B hAB
  apply GeneralLinearGroup.ext
  intro i j
  apply Subtype.ext
  have := congrArg (fun X : GL (Fin 3) K => (X : Matrix (Fin 3) (Fin 3) K) i j) hAB
  simpa [GeneralLinearGroup.map_apply] using this

theorem exists_glIncl_eq {X : GL (Fin 3) K} (hX : glAut σ X = X) :
    ∃ A : GL (Fin 3) (fixedField σ), glIncl σ A = X := by
  have hfix : ∀ i j, σ ((X : Matrix (Fin 3) (Fin 3) K) i j) =
      (X : Matrix (Fin 3) (Fin 3) K) i j := by
    intro i j
    have h1 := congrArg (fun Y : GL (Fin 3) K => (Y : Matrix (Fin 3) (Fin 3) K) i j) hX
    simpa [coe_glAut] using h1
  set M : Matrix (Fin 3) (Fin 3) (fixedField σ) :=
    fun i j => ⟨(X : Matrix (Fin 3) (Fin 3) K) i j, (mem_fixedField_iff σ _).mpr (hfix i j)⟩
  have hMmap : M.map (fixedField σ).subtype = (X : Matrix (Fin 3) (Fin 3) K) := rfl
  have hdet : M.det ≠ 0 := by
    intro h0
    have h1 : (fixedField σ).subtype M.det = (X : Matrix (Fin 3) (Fin 3) K).det := by
      rw [RingHom.map_det]
      exact congrArg Matrix.det hMmap
    rw [h0, map_zero] at h1
    exact X.isUnit.map Matrix.detMonoidHom |>.ne_zero h1.symm
  refine ⟨GeneralLinearGroup.mkOfDetNeZero M hdet, ?_⟩
  apply GeneralLinearGroup.ext
  intro i j
  rw [GeneralLinearGroup.map_apply]
  rfl

noncomputable def glInclDet (A : GL (Fin 3) (fixedField σ)) : Kˣ :=
  Units.map ((fixedField σ).subtype : fixedField σ →* K) (GeneralLinearGroup.det A)

theorem coe_glInclDet (A : GL (Fin 3) (fixedField σ)) :
    (glInclDet A : K) = ((glIncl σ A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det := by
  rw [coe_glIncl, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
  rfl

theorem glInclDet_mul (A B : GL (Fin 3) (fixedField σ)) :
    glInclDet (A * B) = glInclDet A * glInclDet B := by
  rw [glInclDet, glInclDet, glInclDet, map_mul, map_mul]

theorem glInclDet_one : glInclDet (1 : GL (Fin 3) (fixedField σ)) = 1 := by
  rw [glInclDet, map_one, map_one]

theorem glAut_glIncl (A : GL (Fin 3) (fixedField σ)) : glAut σ (glIncl σ A) = glIncl σ A := by
  apply Units.ext
  rw [coe_glAut, coe_glIncl]
  ext i j
  exact fixedField_apply σ _

theorem map_glInclDet (A : GL (Fin 3) (fixedField σ)) :
    Units.map (σ : K →* K) (glInclDet A) = glInclDet A := by
  apply Units.ext
  exact fixedField_apply σ _

end Incl

section Pgu

variable {p f : ℕ} {K : Type} [Field K] {σ : K ≃+* K} {f₀ : ℕ}

theorem glIncl_mem_unitaryIsom3 (h : UnitaryFieldData p f K)
    (h₀ : UnitaryFieldData p f₀ (fixedField σ))
    (hbar : ∀ x : fixedField σ, h.bar (x : K) = ((h₀.bar x : fixedField σ) : K))
    {A : GL (Fin 3) (fixedField σ)} (hA : A ∈ glPi false 3 (p ^ f₀) (fixedField σ)) :
    glIncl σ A ∈ unitaryIsom3 h := by
  rw [mem_unitaryIsom3, coe_glIncl, map_subtype_map_bar h h₀ hbar, ← Matrix.transpose_map,
    ← Matrix.map_mul, (mem_glPi_false h₀).mp hA, Matrix.map_one _ (map_zero _) (map_one _)]

theorem glInclDet_pow_eq_one (h₀ : UnitaryFieldData p f₀ (fixedField σ))
    {A : GL (Fin 3) (fixedField σ)} (hA : A ∈ glPi false 3 (p ^ f₀) (fixedField σ)) :
    glInclDet A ^ (p ^ f₀ + 1) = 1 := by
  have hu := (mem_glPi_false h₀).mp hA
  have hd := congrArg Matrix.det hu
  rw [Matrix.det_mul, Matrix.det_transpose, ← RingHom.mapMatrix_apply, ← RingHom.map_det,
    Matrix.det_one, mul_comm, ← UnitaryFieldData.norm, UnitaryFieldData.norm_eq_pow] at hd
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, glInclDet, Units.coe_map, Units.val_one,
    MonoidHom.coe_ofClass, ← map_pow, GeneralLinearGroup.val_det_apply, hd, map_one]

theorem card_eq_pow_six (h : UnitaryFieldData p f K) (hf : f = 3 * f₀) :
    Nat.card K = ((p ^ f₀) ^ 3) ^ 2 := by
  rw [h.card, hf, ← pow_mul, ← pow_mul]
  ring_nf

theorem pow_eq_pow_three (hf : f = 3 * f₀) : p ^ f = (p ^ f₀) ^ 3 := by
  rw [hf, ← pow_mul, mul_comm]

theorem exists_puRoot (h : UnitaryFieldData p f K) (hf : f = 3 * f₀)
    (h₀ : UnitaryFieldData p f₀ (fixedField σ)) {A : GL (Fin 3) (fixedField σ)}
    (hA : A ∈ glPi false 3 (p ^ f₀) (fixedField σ)) :
    ∃ c : Kˣ, c ^ (p ^ f + 1) = 1 ∧ c ^ 3 * glInclDet A = 1 := by
  have := h.finite
  have hδ : (glInclDet A)⁻¹ ^ (p ^ f₀ + 1) = 1 := by
    rw [inv_pow, glInclDet_pow_eq_one h₀ hA, inv_one]
  obtain ⟨c, hc, hc3⟩ := exists_cube_root_normOne (card_eq_pow_six h hf) hδ
  refine ⟨c, by rw [pow_eq_pow_three hf]; exact hc, ?_⟩
  rw [hc3, inv_mul_cancel]

noncomputable def puRoot (h : UnitaryFieldData p f K) (hf : f = 3 * f₀)
    (h₀ : UnitaryFieldData p f₀ (fixedField σ)) (A : glPi false 3 (p ^ f₀) (fixedField σ)) :
    Kˣ :=
  Classical.choose (exists_puRoot h hf h₀ A.2)

theorem puRoot_spec (h : UnitaryFieldData p f K) (hf : f = 3 * f₀)
    (h₀ : UnitaryFieldData p f₀ (fixedField σ)) (A : glPi false 3 (p ^ f₀) (fixedField σ)) :
    puRoot h hf h₀ A ^ (p ^ f + 1) = 1 ∧
      puRoot h hf h₀ A ^ 3 * glInclDet (A : GL (Fin 3) (fixedField σ)) = 1 :=
  Classical.choose_spec (exists_puRoot h hf h₀ A.2)

theorem scalar_mul_glIncl_mem (h : UnitaryFieldData p f K)
    (h₀ : UnitaryFieldData p f₀ (fixedField σ))
    (hbar : ∀ x : fixedField σ, h.bar (x : K) = ((h₀.bar x : fixedField σ) : K))
    {A : GL (Fin 3) (fixedField σ)} (hA : A ∈ glPi false 3 (p ^ f₀) (fixedField σ)) {c : Kˣ}
    (hc : c ^ (p ^ f + 1) = 1) (hc3 : c ^ 3 * glInclDet A = 1) :
    GeneralLinearGroup.scalar (Fin 3) c * glIncl σ A ∈ unitarySU p f K 3 := by
  refine scalar_mul_mem_unitarySU h hc (glIncl_mem_unitaryIsom3 h h₀ hbar hA) ?_
  rw [← coe_glInclDet, ← Units.val_pow_eq_pow_val, ← Units.val_mul, hc3, Units.val_one]

noncomputable def puElt (h : UnitaryFieldData p f K) (hf : f = 3 * f₀)
    (h₀ : UnitaryFieldData p f₀ (fixedField σ))
    (hbar : ∀ x : fixedField σ, h.bar (x : K) = ((h₀.bar x : fixedField σ) : K))
    (A : glPi false 3 (p ^ f₀) (fixedField σ)) : unitarySU p f K 3 :=
  ⟨_, scalar_mul_glIncl_mem h h₀ hbar A.2 (puRoot_spec h hf h₀ A).1 (puRoot_spec h hf h₀ A).2⟩

theorem unitaryProj_puElt_eq (h : UnitaryFieldData p f K) (hf : f = 3 * f₀)
    (h₀ : UnitaryFieldData p f₀ (fixedField σ))
    (hbar : ∀ x : fixedField σ, h.bar (x : K) = ((h₀.bar x : fixedField σ) : K))
    (A : glPi false 3 (p ^ f₀) (fixedField σ)) {c : Kˣ}
    (hc : c ^ (p ^ f + 1) = 1) (hc3 : c ^ 3 * glInclDet (A : GL (Fin 3) (fixedField σ)) = 1) :
    unitaryProj h 3 (puElt h hf h₀ hbar A) =
      unitaryProj h 3 ⟨_, scalar_mul_glIncl_mem h h₀ hbar A.2 hc hc3⟩ := by
  obtain ⟨hr, hr3⟩ := puRoot_spec h hf h₀ A
  refine unitaryProj_scalar_eq h hr hc ?_ _ _
  rw [eq_inv_of_mul_eq_one_left hr3, eq_inv_of_mul_eq_one_left hc3]

@[expose] noncomputable def puHom (h : UnitaryFieldData p f K) (hf : f = 3 * f₀)
    (h₀ : UnitaryFieldData p f₀ (fixedField σ))
    (hbar : ∀ x : fixedField σ, h.bar (x : K) = ((h₀.bar x : fixedField σ) : K)) :
    glPi false 3 (p ^ f₀) (fixedField σ) →* unitaryPSU h 3 where
  toFun A := unitaryProj h 3 (puElt h hf h₀ hbar A)
  map_one' := by
    rw [unitaryProj_puElt_eq h hf h₀ hbar 1 (c := 1) (by rw [one_pow])
      (by rw [one_pow, one_mul, OneMemClass.coe_one]; exact glInclDet_one),
      ← map_one (unitaryProj h 3)]
    congr 1
    apply Subtype.ext
    change GeneralLinearGroup.scalar (Fin 3) 1 * glIncl σ 1 = 1
    rw [map_one, map_one, one_mul]
  map_mul' A B := by
    obtain ⟨hA, hA3⟩ := puRoot_spec h hf h₀ A
    obtain ⟨hB, hB3⟩ := puRoot_spec h hf h₀ B
    have hc : (puRoot h hf h₀ A * puRoot h hf h₀ B) ^ (p ^ f + 1) = 1 := by
      rw [mul_pow, hA, hB, one_mul]
    have hc3 : (puRoot h hf h₀ A * puRoot h hf h₀ B) ^ 3 *
        glInclDet ((A * B : glPi false 3 (p ^ f₀) (fixedField σ)) : GL (Fin 3) (fixedField σ)) =
          1 := by
      rw [Subgroup.coe_mul, glInclDet_mul, mul_pow]
      calc puRoot h hf h₀ A ^ 3 * puRoot h hf h₀ B ^ 3 *
            (glInclDet (A : GL (Fin 3) (fixedField σ)) * glInclDet (B : GL (Fin 3) (fixedField σ)))
          = (puRoot h hf h₀ A ^ 3 * glInclDet (A : GL (Fin 3) (fixedField σ))) *
            (puRoot h hf h₀ B ^ 3 * glInclDet (B : GL (Fin 3) (fixedField σ))) :=
              mul_mul_mul_comm _ _ _ _
        _ = 1 := by rw [hA3, hB3, one_mul]
    change unitaryProj h 3 (puElt h hf h₀ hbar (A * B)) =
      unitaryProj h 3 (puElt h hf h₀ hbar A) * unitaryProj h 3 (puElt h hf h₀ hbar B)
    rw [unitaryProj_puElt_eq h hf h₀ hbar (A * B) hc hc3, ← map_mul]
    congr 1
    apply Subtype.ext
    change GeneralLinearGroup.scalar (Fin 3) (puRoot h hf h₀ A * puRoot h hf h₀ B) *
        glIncl σ ((A * B : glPi false 3 (p ^ f₀) (fixedField σ)) : GL (Fin 3) (fixedField σ)) =
      GeneralLinearGroup.scalar (Fin 3) (puRoot h hf h₀ A) * glIncl σ (A : GL _ _) *
        (GeneralLinearGroup.scalar (Fin 3) (puRoot h hf h₀ B) * glIncl σ (B : GL _ _))
    have hcomm := (commute_scalar (puRoot h hf h₀ B) (glIncl σ (A : GL (Fin 3) (fixedField σ)))).eq
    rw [Subgroup.coe_mul, map_mul, map_mul]
    calc GeneralLinearGroup.scalar (Fin 3) (puRoot h hf h₀ A) *
          GeneralLinearGroup.scalar (Fin 3) (puRoot h hf h₀ B) *
            (glIncl σ (A : GL (Fin 3) (fixedField σ)) * glIncl σ (B : GL (Fin 3) (fixedField σ)))
        = GeneralLinearGroup.scalar (Fin 3) (puRoot h hf h₀ A) *
            (GeneralLinearGroup.scalar (Fin 3) (puRoot h hf h₀ B) *
              glIncl σ (A : GL (Fin 3) (fixedField σ))) *
            glIncl σ (B : GL (Fin 3) (fixedField σ)) := by group
      _ = GeneralLinearGroup.scalar (Fin 3) (puRoot h hf h₀ A) *
            (glIncl σ (A : GL (Fin 3) (fixedField σ)) *
              GeneralLinearGroup.scalar (Fin 3) (puRoot h hf h₀ B)) *
            glIncl σ (B : GL (Fin 3) (fixedField σ)) := by rw [hcomm]
      _ = _ := by group

theorem puHom_apply (h : UnitaryFieldData p f K) (hf : f = 3 * f₀)
    (h₀ : UnitaryFieldData p f₀ (fixedField σ))
    (hbar : ∀ x : fixedField σ, h.bar (x : K) = ((h₀.bar x : fixedField σ) : K))
    (A : glPi false 3 (p ^ f₀) (fixedField σ)) :
    puHom h hf h₀ hbar A = unitaryProj h 3 (puElt h hf h₀ hbar A) :=
  rfl

theorem glAut_scalar (σ : K ≃+* K) (c : Kˣ) :
    glAut σ (GeneralLinearGroup.scalar (Fin 3) c) =
      GeneralLinearGroup.scalar (Fin 3) (Units.map (σ : K →* K) c) := by
  apply Units.ext
  rw [coe_glAut, GeneralLinearGroup.coe_scalar, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
    Matrix.scalar_apply, Matrix.diagonal_map (map_zero σ)]
  rfl

theorem pow_add_one_eq_of_mem_fixedField (h : UnitaryFieldData p f K)
    (h₀ : UnitaryFieldData p f₀ (fixedField σ))
    (hbar : ∀ x : fixedField σ, h.bar (x : K) = ((h₀.bar x : fixedField σ) : K))
    {c : K} (hc : c ∈ fixedField σ) : c ^ (p ^ f + 1) = c ^ (p ^ f₀ + 1) := by
  have h1 := hbar ⟨c, hc⟩
  rw [UnitaryFieldData.bar_apply, UnitaryFieldData.bar_apply, SubmonoidClass.coe_pow] at h1
  rw [pow_succ, h1, ← pow_succ]

theorem pow_eq_one_of_fixed (h : UnitaryFieldData p f K)
    (h₀ : UnitaryFieldData p f₀ (fixedField σ))
    (hbar : ∀ x : fixedField σ, h.bar (x : K) = ((h₀.bar x : fixedField σ) : K))
    {c : Kˣ} (hc : c ^ (p ^ f + 1) = 1) (hσc : σ c = c) : c ^ (p ^ f₀ + 1) = 1 := by
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, Units.val_one,
    ← pow_add_one_eq_of_mem_fixedField h h₀ hbar ((mem_fixedField_iff σ _).mpr hσc),
    ← Units.val_pow_eq_pow_val, hc, Units.val_one]

theorem scalar_mem_unitaryIsom3 (h : UnitaryFieldData p f K) {c : Kˣ}
    (hc : c ^ (p ^ f + 1) = 1) : GeneralLinearGroup.scalar (Fin 3) c ∈ unitaryIsom3 h :=
  CFSG.RankThree.PartTwo.KFacts.scalar_mem_unitaryIsom3_of_norm (by
    rw [UnitaryFieldData.norm_eq_pow, ← Units.val_pow_eq_pow_val, hc, Units.val_one])

theorem mem_range_puHom_iff (h : UnitaryFieldData p f K) (hf : f = 3 * f₀)
    (h₀ : UnitaryFieldData p f₀ (fixedField σ))
    (hbar : ∀ x : fixedField σ, h.bar (x : K) = ((h₀.bar x : fixedField σ) : K))
    (y : unitaryPSU h 3) : y ∈ (puHom h hf h₀ hbar).range ↔ psuField h σ y = y := by
  constructor
  · rintro ⟨A, rfl⟩
    obtain ⟨hA, hA3⟩ := puRoot_spec h hf h₀ A
    set c := puRoot h hf h₀ A
    have hσc : (Units.map (σ : K →* K) c) ^ (p ^ f + 1) = 1 := by rw [← map_pow, hA, map_one]
    have hσc3 : (Units.map (σ : K →* K) c) ^ 3 * glInclDet (A : GL (Fin 3) (fixedField σ)) = 1 := by
      rw [← map_glInclDet, ← map_pow, ← map_mul, hA3, map_one]
    rw [puHom_apply]
    change psuField h σ (puElt h hf h₀ hbar A : unitaryPSU h 3) = _
    rw [psuField_mk]
    have hmem := scalar_mul_glIncl_mem h h₀ hbar A.2 hσc hσc3
    have heq : suField h σ (puElt h hf h₀ hbar A) = ⟨_, hmem⟩ := by
      apply Subtype.ext
      change glAut σ (GeneralLinearGroup.scalar (Fin 3) c * glIncl σ (A : GL _ _)) = _
      rw [map_mul, glAut_scalar, glAut_glIncl]
    rw [heq, unitaryProj_puElt_eq h hf h₀ hbar A hσc hσc3]
    rfl
  · intro hy
    have := h.finite
    obtain ⟨g, rfl⟩ := unitaryProj_surjective h 3 y
    have hy' : ((suField h σ g : unitarySU p f K 3) : unitaryPSU h 3) = (g : unitaryPSU h 3) := by
      rw [← psuField_mk]
      exact hy
    obtain ⟨ω, hωN, hω3, hωg⟩ := QuotientGroup.eq.mp hy'
    have hω : ω ^ (p ^ f + 1) = 1 := by
      apply Units.ext
      rw [Units.val_pow_eq_pow_val, ← h.norm_eq_pow, hωN, Units.val_one]
    have hσg : glAut σ (g : GL (Fin 3) K) =
        (g : GL (Fin 3) K) * GeneralLinearGroup.scalar (Fin 3) ω⁻¹ := by
      have h1 : ((suField h σ g)⁻¹ * g : unitarySU p f K 3) = (GeneralLinearGroup.scalar (Fin 3) ω :
          GL (Fin 3) K) := hωg
      rw [Subgroup.coe_mul, Subgroup.coe_inv, coe_suField (h := h)] at h1
      rw [map_inv, ← h1]
      group
    have hω' : ω⁻¹ ^ ((p ^ f₀) ^ 3 + 1) = 1 := by
      rw [← pow_eq_pow_three hf, inv_pow, hω, inv_one]
    have hω'3 : ω⁻¹ ^ 3 = 1 := by rw [inv_pow, hω3, inv_one]
    obtain ⟨μ, hμ, hσμ⟩ := exists_normOne_field_mul_eq (card_eq_pow_six h hf) σ
      (fun c hc hσc => pow_eq_one_of_fixed h h₀ hbar (by rw [pow_eq_pow_three hf]; exact hc) hσc)
      hω' hω'3
    rw [← pow_eq_pow_three hf] at hμ
    set X : GL (Fin 3) K := GeneralLinearGroup.scalar (Fin 3) μ⁻¹ * (g : GL (Fin 3) K) with hX
    have hXfix : glAut σ X = X := by
      rw [hX, map_mul, glAut_scalar, hσg, map_inv, hσμ, _root_.mul_inv_rev, inv_inv, map_mul]
      have hc := (commute_scalar ω⁻¹ (g : GL (Fin 3) K)).eq
      calc GeneralLinearGroup.scalar (Fin 3) μ⁻¹ * GeneralLinearGroup.scalar (Fin 3) ω *
            ((g : GL (Fin 3) K) * GeneralLinearGroup.scalar (Fin 3) ω⁻¹)
          = GeneralLinearGroup.scalar (Fin 3) μ⁻¹ * GeneralLinearGroup.scalar (Fin 3) ω *
            (GeneralLinearGroup.scalar (Fin 3) ω⁻¹ * (g : GL (Fin 3) K)) := by rw [hc]
        _ = GeneralLinearGroup.scalar (Fin 3) μ⁻¹ * (g : GL (Fin 3) K) := by
          simp only [map_inv]
          group
    obtain ⟨A₀, hA₀⟩ := exists_glIncl_eq hXfix
    have hXu : X ∈ unitaryIsom3 h :=
      mul_mem (scalar_mem_unitaryIsom3 h (by rw [inv_pow, hμ, inv_one]))
        (unitarySU_le_unitaryIsom3 g.2)
    have hA₀u : A₀ ∈ glPi false 3 (p ^ f₀) (fixedField σ) := by
      rw [mem_glPi_false h₀]
      have key : (((A₀ : Matrix (Fin 3) (Fin 3) (fixedField σ)).map h₀.bar)ᵀ *
          (A₀ : Matrix (Fin 3) (Fin 3) (fixedField σ))).map (fixedField σ).subtype =
          (1 : Matrix (Fin 3) (Fin 3) (fixedField σ)).map (fixedField σ).subtype := by
        rw [Matrix.map_mul, Matrix.transpose_map, ← map_subtype_map_bar h h₀ hbar, ← coe_glIncl,
          hA₀, Matrix.map_one _ (map_zero _) (map_one _)]
        exact hXu
      exact Matrix.map_injective (fixedField σ).subtype_injective key
    have hdet : μ ^ 3 * glInclDet A₀ = 1 := by
      apply Units.ext
      rw [Units.val_mul, Units.val_pow_eq_pow_val, coe_glInclDet, hA₀, hX, coe_scalar_mul,
        Matrix.det_smul, Fintype.card_fin, ((mem_unitarySU_iff h).mp g.2).1, mul_one,
        ← mul_pow, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_pow]
    refine ⟨⟨A₀, hA₀u⟩, ?_⟩
    rw [puHom_apply, unitaryProj_puElt_eq h hf h₀ hbar ⟨A₀, hA₀u⟩ hμ hdet]
    congr 1
    apply Subtype.ext
    change GeneralLinearGroup.scalar (Fin 3) μ * glIncl σ A₀ = (g : GL (Fin 3) K)
    rw [hA₀, hX, ← mul_assoc, ← map_mul, mul_inv_cancel, map_one, one_mul]

theorem ker_puHom (h : UnitaryFieldData p f K) (hf : f = 3 * f₀)
    (h₀ : UnitaryFieldData p f₀ (fixedField σ))
    (hbar : ∀ x : fixedField σ, h.bar (x : K) = ((h₀.bar x : fixedField σ) : K)) :
    (puHom h hf h₀ hbar).ker =
      (StatedScalars (Fin 3) (fixedField σ)).subgroupOf (glPi false 3 (p ^ f₀) (fixedField σ)) := by
  ext A
  obtain ⟨hA, hA3⟩ := puRoot_spec h hf h₀ A
  set c := puRoot h hf h₀ A
  rw [MonoidHom.mem_ker, puHom_apply, Subgroup.mem_subgroupOf, StatedScalars, MonoidHom.mem_range]
  constructor
  · intro h1
    obtain ⟨d, -, -, hd⟩ := (QuotientGroup.eq_one_iff _).mp h1
    have hd' : GeneralLinearGroup.scalar (Fin 3) c * glIncl σ (A : GL (Fin 3) (fixedField σ)) =
        GeneralLinearGroup.scalar (Fin 3) d := hd
    have hentry : ∀ i j, (((A : GL (Fin 3) (fixedField σ)) i j : fixedField σ) : K) =
        ((c⁻¹ * d : Kˣ) : K) * (if i = j then 1 else 0) := by
      intro i j
      have h2 : glIncl σ (A : GL (Fin 3) (fixedField σ)) =
          GeneralLinearGroup.scalar (Fin 3) (c⁻¹ * d) := by
        rw [map_mul, map_inv, ← hd']
        group
      have h3 := congrArg (fun X : GL (Fin 3) K => (X : Matrix (Fin 3) (Fin 3) K) i j) h2
      simp only [GeneralLinearGroup.map_apply, GeneralLinearGroup.coe_scalar,
        Matrix.scalar_apply, Matrix.diagonal_apply] at h3
      have h3' : (((A : GL (Fin 3) (fixedField σ)) i j : fixedField σ) : K) =
          if i = j then ((c⁻¹ * d : Kˣ) : K) else 0 := h3
      rw [h3']
      split_ifs <;> simp
    have h00 : ((A : GL (Fin 3) (fixedField σ)) 0 0 : fixedField σ) ≠ 0 := by
      intro h0
      have := hentry 0 0
      rw [h0, ZeroMemClass.coe_zero] at this
      simp at this
    refine ⟨Units.mk0 _ h00, ?_⟩
    apply GeneralLinearGroup.ext
    intro i j
    apply Subtype.ext
    rw [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_apply, Units.val_mk0,
      hentry]
    split_ifs with hij
    · rw [hentry 0 0]
      simp
    · simp
  · rintro ⟨ν, hν⟩
    have hu := (mem_glPi_false h₀).mp A.2
    rw [← hν] at hu
    have hνN : h₀.bar (ν : fixedField σ) * ν = 1 := by
      have := congrFun (congrFun hu 0) 0
      simpa [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_apply,
        Matrix.mul_apply] using this
    have hνpow : (ν : fixedField σ) ^ (p ^ f₀ + 1) = 1 := by
      rw [← h₀.norm_eq_pow, UnitaryFieldData.norm, mul_comm, hνN]
    set ν' : Kˣ := Units.map ((fixedField σ).subtype : fixedField σ →* K) ν with hν'
    have hglIncl : glIncl σ (A : GL (Fin 3) (fixedField σ)) =
        GeneralLinearGroup.scalar (Fin 3) ν' := by
      rw [← hν]
      apply GeneralLinearGroup.ext
      intro i j
      rw [GeneralLinearGroup.map_apply, GeneralLinearGroup.coe_scalar,
        GeneralLinearGroup.coe_scalar,
        Matrix.scalar_apply, Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.diagonal_apply]
      split_ifs <;> simp [hν']
    have hν'pow : ν' ^ (p ^ f + 1) = 1 := by
      apply Units.ext
      have e : ((ν' : Kˣ) : K) = ((ν : fixedField σ) : K) := rfl
      rw [Units.val_pow_eq_pow_val, e,
        pow_add_one_eq_of_mem_fixedField h h₀ hbar (ν : fixedField σ).2, ← SubmonoidClass.coe_pow,
        hνpow, OneMemClass.coe_one, Units.val_one]
    have hdet : glInclDet (A : GL (Fin 3) (fixedField σ)) = ν' ^ 3 := by
      apply Units.ext
      rw [coe_glInclDet, hglIncl, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
        Matrix.det_diagonal, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
        Units.val_pow_eq_pow_val]
    apply (QuotientGroup.eq_one_iff _).mpr
    refine ⟨c * ν', ?_, ?_, ?_⟩
    · rw [UnitaryFieldData.norm_eq_pow, ← Units.val_pow_eq_pow_val, mul_pow, hA, hν'pow, one_mul,
        Units.val_one]
    · rw [mul_pow, ← hdet, hA3]
    · change GeneralLinearGroup.scalar (Fin 3) c * glIncl σ (A : GL (Fin 3) (fixedField σ)) = _
      rw [hglIncl, ← map_mul]

end Pgu

section Bar

open CFSG.Adapters.RankTwoModelTransports (statedProjEquivMapMk)

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem exists_barCentralizer_mulEquiv_pgu3 {p f : ℕ} {K : Type} [Field K]
    {h : UnitaryFieldData p f K} (hq : 2 < p ^ f) {a : G} (ha3 : a ^ 3 = 1)
    (ha : InducesKindPSU3 h L a .field) :
    ∃ σ : K ≃+* K, orderOf σ = 3 ∧ ∃ f₀ : ℕ, f = 3 * f₀ ∧
      ∃ _ : UnitaryFieldData p f₀ (fixedField σ),
        Nonempty (Sec8.barCentralizer (Subgroup.zpowers a) L ≃*
          projImage (glPi false 3 (p ^ f₀) (fixedField σ))) := by
  obtain ⟨e, hN, hfield⟩ := ha
  set α := inducedAutHom L e ⟨a, hN⟩ with hαdef
  have hα3 : α ^ 3 = 1 := inducedAutHom_pow_eq_one L e hN ha3
  have hD : α ∉ (psuConj h).range :=
    (stdPinnedPSU3_separated h).not_mem_inndiag_of_isField hfield
  obtain ⟨σ, hσ3, H, hαH⟩ := unitary_order_three_field_descent hq α hα3 hD
  obtain ⟨f₀, hf, hf₀, hcard⟩ := exists_card_fixedField_of_orderOf_eq_three h hσ3
  have h₀ : UnitaryFieldData p f₀ (fixedField σ) := ⟨h.prime, hf₀, hcard⟩
  have hbar := bar_coe_fixedField h hf h₀
  refine ⟨σ, hσ3, f₀, hf, h₀, ?_⟩
  set Φ := puHom h hf h₀ hbar
  have hker := ker_puHom h hf h₀ hbar
  have : ((StatedScalars (Fin 3) (fixedField σ)).subgroupOf
      (glPi false 3 (p ^ f₀) (fixedField σ))).Normal := hker ▸ Φ.normal_ker
  let Ψ : projImage (glPi false 3 (p ^ f₀) (fixedField σ)) ≃* Φ.range :=
    (statedProjEquivMapMk _).symm.trans
      ((QuotientGroup.quotientMulEquivOfEq hker.symm).trans (QuotientGroup.quotientKerEquivRange Φ))
  have hΨ : ∀ y, y ∈ (Φ.range.subtype.comp Ψ.toMonoidHom).range ↔ psuField h σ y = y := by
    intro y
    rw [← mem_range_puHom_iff h hf h₀ hbar]
    constructor
    · rintro ⟨x, rfl⟩
      exact (Ψ x).2
    · intro hy
      exact ⟨Ψ.symm ⟨y, hy⟩, by simp⟩
  refine nonempty_barCentralizer_mulEquiv hN e
    ((psuConj h H : unitaryPSU h 3 ≃* unitaryPSU h 3).toMonoidHom.comp
      (Φ.range.subtype.comp Ψ.toMonoidHom))
    ((psuConj h H).injective.comp (Subtype.val_injective.comp Ψ.injective)) fun z => ?_
  rw [← hαdef, hαH]
  exact mem_range_conj_comp_iff _ _ _ hΨ z

theorem isoPGUThree_barCentralizer_of_field {p f : ℕ} {K : Type} [Field K]
    {h : UnitaryFieldData p f K} (hq : 2 < p ^ f) {a : G} (ha3 : a ^ 3 = 1)
    (ha : InducesKindPSU3 h L a .field) :
    ∃ f₀ : ℕ, f = 3 * f₀ ∧
      Sec8.IsoPGUThree (Sec8.barCentralizer (Subgroup.zpowers a) L) (p ^ f₀) := by
  obtain ⟨σ, -, f₀, hf, h₀, ⟨ι⟩⟩ := exists_barCentralizer_mulEquiv_pgu3 hq ha3 ha
  have := h₀.finite
  refine ⟨f₀, hf, fixedField σ, inferInstance, inferInstance, ?_, ⟨ι⟩⟩
  rw [h₀.card, ← pow_mul, mul_comm]

end Bar

end CFSG.RankThree.PartTwo.KFacts
