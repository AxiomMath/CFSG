module

public import CFSG.Milestones.ASVolI.F429.aR5Gen
public import CFSG.Milestones.ASVolI.F429.Defs
public import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsU4
public import CFSG.Quasithin.H13.U4ParOuterO2
import CFSG.Milestones.ASVolI.F4
public import CFSG.Milestones.ASVolI.F429.aC4Gen
public import CFSG.Milestones.ASVolI.F429.aC7Gen
public import CFSG.Milestones.ASVolI.F429.aOddGen

public section

namespace CFSG.ASVolI

section U4Model

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.Quasithin.H13.U4Par CFSG.Quasithin.H13.Sec53F.Unit CFSG.ASVolI.ChF

variable {m : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 m K)

theorem burnsideF429a_U4_bar_comm (σ : K ≃+* K) (c : K) : σ (h.bar c) = h.bar (σ c) := by
  rw [UnitaryFieldData.bar_apply, UnitaryFieldData.bar_apply, map_pow]

theorem burnsideF429a_U4_fieldAut_mem_radQ (σ : K ≃+* K) {g : hypSU h 2 0} (hg : g ∈ radQ h) :
    fieldAut h σ g ∈ radQ h := by
  obtain ⟨x, y, c, hc, hG⟩ := hg
  refine ⟨σ x, σ y, σ c, ?_, ?_⟩
  · unfold SAdm at hc ⊢
    have := congrArg σ hc
    simpa only [map_add, map_mul, burnsideF429a_U4_bar_comm h] using this
  · rw [fieldAut_apply, mat_fieldHom, hG]
    ext i j
    rcases ix_cases i with rfl | rfl | rfl | rfl <;>
      rcases ix_cases j with rfl | rfl | rfl | rfl <;>
      simp [map_apply, sMat_apply, one_apply, ie1, ie2, if1, if2, burnsideF429a_U4_bar_comm h]

theorem burnsideF429a_U4_chi_fieldAut (σ : K ≃+* K) (g : hypSU h 2 0) :
    chi h (fieldAut h σ g) = σ (chi h g) := by
  show ((fieldAut h σ g : hypSU h 2 0) : GL Ix K) ie1 ie1 = σ (((g : GL Ix K) : Matrix Ix Ix K) ie1 ie1)
  rw [fieldAut_apply, mat_fieldHom]
  rfl

theorem burnsideF429a_U4_fieldAut_mem_parP (σ : K ≃+* K) {g : hypSU h 2 0} (hg : g ∈ parP h) :
    fieldAut h σ g ∈ parP h := by
  rw [mem_parP_iff] at hg ⊢
  intro a ha
  rw [fieldAut_apply, mat_fieldHom, map_apply, hg a ha, map_zero]

theorem burnsideF429a_U4_chi_of_mem_U {g : hypSU h 2 0} (hg : g ∈ hypUnitriangular h 2 0) :
    chi h g = 1 :=
  (mem_hypUnitriangular.mp hg).2 ie1

theorem burnsideF429a_U4_normalizer_le_parP :
    Subgroup.normalizer (hypUnitriangular h 2 0 : Set (hypSU h 2 0)) ≤ parP h := by
  intro g hg
  obtain ⟨u, hu, t, ht, rfl⟩ := normalizer_eq_mul h (by norm_num) (by norm_num) hg
  have hB : hypBorel h 2 0 ≤ parP h := by
    rw [← burnsideF4gU4Inv_parP_inf_parP2]
    exact inf_le_left
  exact hB ((hypBorel h 2 0).mul_mem (hypUnitriangular_le_hypBorel h hu)
    (hypTorus_le_hypBorel h ht))

theorem burnsideF429a_U4_normalizer_le_borel :
    Subgroup.normalizer (hypUnitriangular h 2 0 : Set (hypSU h 2 0)) ≤ parP h ⊓ parP2 h := by
  intro g hg
  obtain ⟨u, hu, t, ht, rfl⟩ := normalizer_eq_mul h (by norm_num) (by norm_num) hg
  rw [burnsideF4gU4Inv_parP_inf_parP2]
  exact (hypBorel h 2 0).mul_mem (hypUnitriangular_le_hypBorel h hu) (hypTorus_le_hypBorel h ht)

@[expose] noncomputable def burnsideF429a_U4_dSL (c : Kˣ) : Matrix.SpecialLinearGroup (Fin 2) K :=
  ⟨!![(c : K), 0; 0, ((c⁻¹ : Kˣ) : K)], by simp [Matrix.det_fin_two]⟩

theorem burnsideF429a_U4_lev2_d_mem_parP (c : Kˣ) :
    lev2Hom h (burnsideF429a_U4_dSL c) ∈ parP h := by
  rw [mem_parP_iff]
  intro a ha
  rw [coe_lev2Hom, lev2Mat_apply]
  rcases ix_cases a with rfl | rfl | rfl | rfl <;>
    simp_all [burnsideF429a_U4_dSL, ie1, ie2, if1, if2]

theorem burnsideF429a_U4_chi_lev2_d (c : Kˣ) :
    chi h (lev2Hom h (burnsideF429a_U4_dSL c)) = c := by
  show (((lev2Hom h (burnsideF429a_U4_dSL c) : hypSU h 2 0) : GL Ix K) : Matrix Ix Ix K) ie1 ie1 = c
  rw [coe_lev2Hom, lev2Mat_apply]
  simp [burnsideF429a_U4_dSL, ie1, ie2, if1, if2]

theorem burnsideF429a_U4_lev2_d_mem_oPPrime (c : Kˣ) :
    lev2Hom h (burnsideF429a_U4_dSL c) ∈ oPPrime 2 (parP2 h) := by
  have := h.charP
  have hdet : ∀ a : Kˣ, (!![0, (a : K); ((a⁻¹ : Kˣ) : K), 0] : Matrix (Fin 2) (Fin 2) K).det = 1 := by
    intro a
    rw [Matrix.det_fin_two_of, zero_mul, zero_sub, Units.mul_inv, CharTwo.neg_eq]
  let w : Kˣ → Matrix.SpecialLinearGroup (Fin 2) K := fun a => ⟨_, hdet a⟩
  have hw2 : ∀ a, w a * w a = 1 := by
    intro a
    apply Subtype.ext
    show (!![0, (a : K); ((a⁻¹ : Kˣ) : K), 0] : Matrix (Fin 2) (Fin 2) K) *
      !![0, (a : K); ((a⁻¹ : Kˣ) : K), 0] = 1
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  have hwd : burnsideF429a_U4_dSL c = w c * w 1 := by
    apply Subtype.ext
    show !![(c : K), 0; 0, ((c⁻¹ : Kˣ) : K)] =
      (!![0, (c : K); ((c⁻¹ : Kˣ) : K), 0] : Matrix (Fin 2) (Fin 2) K) *
        !![0, ((1 : Kˣ) : K); (((1 : Kˣ)⁻¹ : Kˣ) : K), 0]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  have hmem : ∀ a, lev2Hom h (w a) ∈ oPPrime 2 (parP2 h) := fun a =>
    burnsideF4gU4Inv_mem_oPPrime (lev2Hom_le_parP2 h ⟨w a, rfl⟩) (k := 1)
      (by rw [pow_one, pow_two, ← map_mul, hw2, map_one])
  rw [hwd, map_mul]
  exact (oPPrime 2 (parP2 h)).mul_mem (hmem c) (hmem 1)

theorem burnsideF429a_U4_fieldAut_eq_one_of_inner {τ : K ≃+* K}
    (hτ : fieldAut h τ ∈ (MulAut.conj : hypSU h 2 0 →* MulAut (hypSU h 2 0)).range) : τ = 1 := by
  obtain ⟨x, hx⟩ := hτ
  have hxy : ∀ y, fieldAut h τ y = x * y * x⁻¹ := fun y => by rw [← hx]; rfl
  have hxU : x ∈ Subgroup.normalizer (hypUnitriangular h 2 0 : Set (hypSU h 2 0)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    rw [← hxy]
    exact (fieldAut_mem_unitriangular h τ y).symm
  have hxP : x ∈ parP h := burnsideF429a_U4_normalizer_le_parP h hxU
  refine RingEquiv.ext fun c => ?_
  show τ c = c
  by_cases hc : c = 0
  · rw [hc, map_zero]
  have hbP := burnsideF429a_U4_lev2_d_mem_parP h (Units.mk0 c hc)
  have h1 : chi h (fieldAut h τ (lev2Hom h (burnsideF429a_U4_dSL (Units.mk0 c hc)))) =
      chi h (x * lev2Hom h (burnsideF429a_U4_dSL (Units.mk0 c hc)) * x⁻¹) := by rw [hxy]
  rw [burnsideF429a_U4_chi_fieldAut, chi_mul h ((parP h).inv_mem hxP), chi_mul h hbP,
    burnsideF429a_U4_chi_lev2_d, Units.val_mk0] at h1
  have hxx := chi_mul_inv h hxP
  calc τ c = chi h x * c * chi h x⁻¹ := h1
    _ = c * (chi h x * chi h x⁻¹) := by ring
    _ = c := by rw [hxx, mul_one]

theorem burnsideF429a_U4_oPPrime_le_parH : oPPrime 2 (parP h) ≤ parH h := by
  have := h.charP
  have hchi := burnsideF4gU4Inv_oPPrime_le_chiKer h
  unfold oPPrime
  refine (Subgroup.closure_le _).mpr ?_
  rintro x ⟨hxP, k, hk⟩
  have hxk : x ^ 2 ^ k = 1 := by rw [← hk]; exact pow_orderOf_eq_one x
  have hxo : x ∈ oPPrime 2 (parP h) := Subgroup.subset_closure ⟨hxP, k, hk⟩
  refine ⟨hxP, (hchi hxo).2, ?_⟩
  have hpow : ∀ n : ℕ, rho h (x ^ n) = rho h x ^ n := by
    intro n
    induction n with
    | zero => rw [pow_zero, pow_zero, rho_one]
    | succ n ih => rw [pow_succ, rho_mul h ((parP h).pow_mem hxP n) hxP, ih, pow_succ]
  have hdet : (rho h x).det ^ 2 ^ k = 1 := by
    rw [← Matrix.det_pow, ← hpow, hxk, rho_one, Matrix.det_one]
  have h1 : ((rho h x).det - 1) ^ 2 ^ k = 0 := by
    rw [sub_pow_char_pow, hdet, one_pow, sub_self]
  exact sub_eq_zero.mp (pow_eq_zero_iff (pow_ne_zero k two_ne_zero) |>.mp h1)

theorem burnsideF429a_U4_frob_mul_inv_mem_radQ {ℓ : hypSU h 2 0} (hℓ : ℓ ∈ oPPrime 2 (parP h)) :
    frobElt h ℓ * ℓ⁻¹ ∈ radQ h := by
  have hℓ' := parH_le_radQ_sup h (burnsideF429a_U4_oPPrime_le_parH h hℓ)
  have hN : (levHom h).range ≤ Subgroup.normalizer (radQ h : Set (hypSU h 2 0)) :=
    (levHom_le_parP h).trans (parP_le_normalizer_radQ h)
  obtain ⟨s, hs, l, ⟨A, rfl⟩, rfl⟩ := exists_mul_eq_of_mem_sup_of_le_normalizer hN hℓ'
  have hf : frobElt h (s * levHom h A) = frobElt h s * levHom h A := by
    rw [← frob_apply, map_mul, frob_apply, frob_apply, frobElt_levHom]
  rw [hf]
  have e : frobElt h s * levHom h A * (s * levHom h A)⁻¹ = frobElt h s * s⁻¹ := by group
  rw [e]
  exact (radQ h).mul_mem (frobElt_mem_radQ h hs) ((radQ h).inv_mem hs)

theorem burnsideF429a_sl2_eq_one_of_comm {F : Type} [Field F] (h2 : (2 : F) = 0)
    (X : Matrix.SpecialLinearGroup (Fin 2) F)
    (h₁ : (X : Matrix (Fin 2) (Fin 2) F) * !![1, 1; 0, 1] =
      !![1, 1; 0, 1] * (X : Matrix (Fin 2) (Fin 2) F))
    (h₂ : (X : Matrix (Fin 2) (Fin 2) F) * !![1, 0; 1, 1] =
      !![1, 0; 1, 1] * (X : Matrix (Fin 2) (Fin 2) F)) : X = 1 := by
  have e00 := congrFun (congrFun h₁ 0) 0
  have e01 := congrFun (congrFun h₁ 0) 1
  have f00 := congrFun (congrFun h₂ 0) 0
  simp [Matrix.mul_apply, Fin.sum_univ_two] at e00 e01 f00
  have hdet := X.2
  rw [Matrix.det_fin_two] at hdet
  have hc : (X : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := e00
  have hb : (X : Matrix (Fin 2) (Fin 2) F) 0 1 = 0 := f00
  have hd : (X : Matrix (Fin 2) (Fin 2) F) 1 1 = (X : Matrix (Fin 2) (Fin 2) F) 0 0 := by
    linear_combination -e01
  rw [hc, hb, hd, mul_zero, sub_zero] at hdet
  have ha : (X : Matrix (Fin 2) (Fin 2) F) 0 0 = 1 := by
    have h3 : ((X : Matrix (Fin 2) (Fin 2) F) 0 0 - 1) ^ 2 = 0 := by
      linear_combination hdet + (1 - (X : Matrix (Fin 2) (Fin 2) F) 0 0) * h2
    exact sub_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp h3)
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ha, hb, hc, hd]

theorem burnsideF429a_U4_mem_radQ_of_comm {x : hypSU h 2 0} (hx : x ∈ oPPrime 2 (parP h))
    (hc : ∀ l ∈ oPPrime 2 (parP h), x * l * x⁻¹ * l⁻¹ ∈ radQ h) : x ∈ radQ h := by
  have := h.charP
  have hxH : x ∈ parH h := burnsideF429a_U4_oPPrime_le_parH h hx
  have h2F : (2 : h.fixedField) = 0 := by
    have e : (2 : h.fixedField) = 1 + 1 := one_add_one_eq_two.symm
    rw [e]
    apply Subtype.ext
    show ((1 : h.fixedField) : K) + ((1 : h.fixedField) : K) = ((0 : h.fixedField) : K)
    rw [OneMemClass.coe_one, ZeroMemClass.coe_zero, one_add_one_eq_two]
    exact CharTwo.two_eq_zero
  have hcomm : ∀ N : Matrix.SpecialLinearGroup (Fin 2) h.fixedField, N * N = 1 →
      rhoF h ⟨x, hxH⟩ * N = N * rhoF h ⟨x, hxH⟩ := by
    intro N hN
    have hlP : levHom h N ∈ parP h := levHom_le_parP h ⟨N, rfl⟩
    have hl : levHom h N ∈ oPPrime 2 (parP h) :=
      burnsideF4gU4Inv_mem_oPPrime hlP (k := 1) (by rw [pow_one, pow_two, ← map_mul, hN, map_one])
    have hlH : levHom h N ∈ parH h := levHom_range_le_parH h ⟨N, rfl⟩
    have hq := hc _ hl
    have hqH : x * levHom h N * x⁻¹ * (levHom h N)⁻¹ ∈ parH h :=
      (parH h).mul_mem ((parH h).mul_mem ((parH h).mul_mem hxH hlH) ((parH h).inv_mem hxH))
        ((parH h).inv_mem hlH)
    have h1 : rhoF h ⟨_, hqH⟩ = 1 := by
      ext i j
      change rho h (x * levHom h N * x⁻¹ * (levHom h N)⁻¹) i j =
        (((1 : Matrix (Fin 2) (Fin 2) h.fixedField) i j : h.fixedField) : K)
      rw [(chi_rho_of_mem_radQ h hq).2]
      fin_cases i <;> fin_cases j <;> simp
    have e : (⟨_, hqH⟩ : parH h) = ⟨x, hxH⟩ * ⟨levHom h N, hlH⟩ * ⟨x, hxH⟩⁻¹ *
        ⟨levHom h N, hlH⟩⁻¹ := rfl
    rw [e, map_mul, map_mul, map_mul, map_inv, map_inv, rhoF_levHom] at h1
    calc rhoF h ⟨x, hxH⟩ * N =
        (rhoF h ⟨x, hxH⟩ * N * (rhoF h ⟨x, hxH⟩)⁻¹ * N⁻¹) * N * rhoF h ⟨x, hxH⟩ := by group
      _ = N * rhoF h ⟨x, hxH⟩ := by rw [h1, one_mul]
  let N₁ : Matrix.SpecialLinearGroup (Fin 2) h.fixedField :=
    ⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two]⟩
  let N₂ : Matrix.SpecialLinearGroup (Fin 2) h.fixedField :=
    ⟨!![1, 0; 1, 1], by simp [Matrix.det_fin_two]⟩
  have h11 : (1 : h.fixedField) + 1 = 0 := one_add_one_eq_two.trans h2F
  have hN₁ : N₁ * N₁ = 1 := by
    apply Subtype.ext
    show (!![1, 1; 0, 1] : Matrix (Fin 2) (Fin 2) h.fixedField) * !![1, 1; 0, 1] = 1
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, h11]
  have hN₂ : N₂ * N₂ = 1 := by
    apply Subtype.ext
    show (!![1, 0; 1, 1] : Matrix (Fin 2) (Fin 2) h.fixedField) * !![1, 0; 1, 1] = 1
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, h11]
  have hX : rhoF h ⟨x, hxH⟩ = 1 := by
    refine burnsideF429a_sl2_eq_one_of_comm h2F _ ?_ ?_
    · exact congrArg Subtype.val (hcomm N₁ hN₁)
    · exact congrArg Subtype.val (hcomm N₂ hN₂)
  exact CFSG.Quasithin.H13.U4V.mem_radQ_of_rhoF_eq_one h hX

theorem burnsideF429a_U4_fieldAut_eq_frob {τ : K ≃+* K} (hτ : ∀ c, τ c = h.bar c)
    (g : hypSU h 2 0) : fieldAut h τ g = frobElt h g := by
  apply hypSU_ext h
  ext i j
  rw [fieldAut_apply, mat_fieldHom, map_apply, frobElt_apply, hτ]

end U4Model

section Transport

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.Quasithin.H13.U4Par CFSG.Quasithin.H13.Sec53F.Unit CFSG.ASVolI.ChF CFSG.Open
  CFSG.Quasithin

theorem burnsideF429a_eq_of_conj {E : Type} [Group E] {Gp : Subgroup E} [Gp.Normal]
    (hc : Subgroup.centralizer (Gp : Set E) = ⊥) {C : Type} [Group C] (Ψ : C ≃* ↥Gp) {e : E}
    {g : C} (hg : ∀ x, ((Ψ (g * x * g⁻¹) : ↥Gp) : E) = e * ((Ψ x : ↥Gp) : E) * e⁻¹) :
    e = ((Ψ g : ↥Gp) : E) := by
  have hρ : burnsideF4d_rho Gp e = burnsideF4d_rho Gp ((Ψ g : ↥Gp) : E) := by
    refine MulEquiv.ext fun y => Subtype.ext ?_
    obtain ⟨x, rfl⟩ := Ψ.surjective y
    rw [burnsideF4d_rho_apply, burnsideF4d_rho_apply, ← hg x, map_mul, map_mul, map_inv]
    rfl
  exact burnsideF4d_rho_injective hc hρ

theorem burnsideF429a_U4_nf {E : Type} [Group E] [Finite E] {Gp M₁ M₂ : Subgroup E} [Gp.Normal]
    {m : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 m K) (Φ : hypSU h 2 0 ≃* ↥Gp)
    (hP₁ : M₁.subgroupOf Gp = (parP h).map Φ.toMonoidHom)
    (hP₂ : M₂.subgroupOf Gp = (parP2 h).map Φ.toMonoidHom) {e : E} (he : e ∈ M₁ ⊓ M₂) :
    ∃ g ∈ Subgroup.normalizer (hypUnitriangular h 2 0 : Set (hypSU h 2 0)), ∃ τ : K ≃+* K,
      ∀ x, ((Φ (g * fieldAut h τ x * g⁻¹) : ↥Gp) : E) = e * ((Φ x : ↥Gp) : E) * e⁻¹ := by
  set φ : hypSU h 2 0 →* E := Gp.subtype.comp Φ.toMonoidHom with hφdef
  have hφ : Function.Injective φ := Gp.subtype_injective.comp Φ.injective
  have hB : (M₁ ⊓ M₂).subgroupOf Gp = (parP h ⊓ parP2 h).map Φ.toMonoidHom := by
    rw [burnsideF429a_subgroupOf_inf, hP₁, hP₂, Subgroup.map_inf_eq _ _ _ Φ.injective]
  have hGB : Gp ⊓ (M₁ ⊓ M₂) = (parP h ⊓ parP2 h).map φ := burnsideF429_inf_eq_map Φ hB
  have hS : pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) = (hypUnitriangular h 2 0).map φ := by
    rw [hGB, CFSG.Quasithin.H13.U4Par.pCoreOf_map_of_inj hφ, burnsideF4gU4Inv_pCore_borel]
  have hrX : e ∈ Subgroup.normalizer ((Gp ⊓ (M₁ ⊓ M₂) : Subgroup E) : Set E) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · rintro ⟨hxG, hxM⟩
      exact ⟨(inferInstance : Gp.Normal).conj_mem x hxG e,
        (M₁ ⊓ M₂).mul_mem ((M₁ ⊓ M₂).mul_mem he hxM) ((M₁ ⊓ M₂).inv_mem he)⟩
    · rintro ⟨hxG, hxM⟩
      refine ⟨?_, ?_⟩
      · have := (inferInstance : Gp.Normal).conj_mem _ hxG e⁻¹
        simpa [mul_assoc] using this
      · have := (M₁ ⊓ M₂).mul_mem ((M₁ ⊓ M₂).mul_mem ((M₁ ⊓ M₂).inv_mem he) hxM) he
        simpa [mul_assoc] using this
  have hrN : e ∈ Subgroup.normalizer (pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) : Set E) :=
    CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _ hrX
  let β : MulAut (hypSU h 2 0) := (Φ.trans (burnsideF4d_rho Gp e)).trans Φ.symm
  have hβφ : ∀ x, φ (β x) = e * φ x * e⁻¹ := by
    intro x
    show ((Φ (Φ.symm (burnsideF4d_rho Gp e (Φ x))) : ↥Gp) : E) = e * ((Φ x : ↥Gp) : E) * e⁻¹
    rw [MulEquiv.apply_symm_apply]
    exact burnsideF4d_rho_apply e (Φ x)
  have hmemU : ∀ x, x ∈ hypUnitriangular h 2 0 ↔ φ x ∈ pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) := by
    intro x
    rw [hS]
    exact (Subgroup.mem_map_iff_mem hφ).symm
  have hβU : ∀ x, β x ∈ hypUnitriangular h 2 0 ↔ x ∈ hypUnitriangular h 2 0 := by
    intro x
    rw [hmemU, hmemU, hβφ]
    exact ((Subgroup.mem_normalizer_iff.1 hrN) (φ x)).symm
  obtain ⟨g, hg, σ, ⟨τ, rfl⟩, hβ⟩ := u4_normal_form h β hβU
  refine ⟨g, hg, τ, fun x => ?_⟩
  have e1 := hβφ x
  rw [hβ] at e1
  exact e1

end Transport

section R5

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.Quasithin.H13.U4Par CFSG.Quasithin.H13.Sec53F.Unit CFSG.ASVolI.ChF CFSG.Open
  CFSG.Quasithin

theorem burnsideF429a_U4_sylow_of_model {E : Type} [Group E] [Finite E] {Gp M₁ M₂ : Subgroup E}
    {m : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 m K) (Φ : hypSU h 2 0 ≃* ↥Gp)
    (hP₁ : M₁.subgroupOf Gp = (parP h).map Φ.toMonoidHom)
    (hP₂ : M₂.subgroupOf Gp = (parP2 h).map Φ.toMonoidHom) :
    ChF.IsSylowOf 2 (pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂))) Gp := by
  set φ : hypSU h 2 0 →* E := Gp.subtype.comp Φ.toMonoidHom with hφdef
  have hφ : Function.Injective φ := Gp.subtype_injective.comp Φ.injective
  have hB : (M₁ ⊓ M₂).subgroupOf Gp = (parP h ⊓ parP2 h).map Φ.toMonoidHom := by
    rw [burnsideF429a_subgroupOf_inf, hP₁, hP₂, Subgroup.map_inf_eq _ _ _ Φ.injective]
  have hGB : Gp ⊓ (M₁ ⊓ M₂) = (parP h ⊓ parP2 h).map φ := burnsideF429_inf_eq_map Φ hB
  have hS : pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) = (hypUnitriangular h 2 0).map φ := by
    rw [hGB, CFSG.Quasithin.H13.U4Par.pCoreOf_map_of_inj hφ, burnsideF4gU4Inv_pCore_borel]
  have htop : (⊤ : Subgroup (hypSU h 2 0)).map φ = Gp := by
    ext x
    constructor
    · rintro ⟨y, -, rfl⟩
      exact (Φ y).2
    · intro hx
      exact ⟨Φ.symm ⟨x, hx⟩, Subgroup.mem_top _, by simp [hφdef]⟩
  rw [hS, ← htop]
  exact burnsideF429_isSylowOf_map φ hφ
    (u4_sylow h : ChF.IsSylowOf 2 (hypUnitriangular h 2 0) ⊤)

theorem burnsideF429a_key2_U4_of_model {E : Type} [Group E] [Finite E] {Gp M₁ M₂ : Subgroup E}
    [Gp.Normal] (hc : Subgroup.centralizer (Gp : Set E) = ⊥)
    {m : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 m K) (Φ : hypSU h 2 0 ≃* ↥Gp)
    (hP₁ : M₁.subgroupOf Gp = (parP h).map Φ.toMonoidHom)
    (hP₂ : M₂.subgroupOf Gp = (parP2 h).map Φ.toMonoidHom) :
    ∀ r ∈ M₁ ⊓ M₂, ∀ k : ℕ, r ^ 2 ^ k = 1 →
      (∀ b ∈ oPPrime 2 (Gp ⊓ M₂) ⊓ (M₁ ⊓ M₂),
        r * b * r⁻¹ * b⁻¹ ∈ pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂))) → r ∈ Gp := by
  intro r hr _ _ hcomm
  set φ : hypSU h 2 0 →* E := Gp.subtype.comp Φ.toMonoidHom with hφdef
  have hφ : Function.Injective φ := Gp.subtype_injective.comp Φ.injective
  have hφx : ∀ x, φ x = ((Φ x : ↥Gp) : E) := fun x => rfl
  have hG₂ : Gp ⊓ M₂ = (parP2 h).map φ := burnsideF429_inf_eq_map Φ hP₂
  have hB : (M₁ ⊓ M₂).subgroupOf Gp = (parP h ⊓ parP2 h).map Φ.toMonoidHom := by
    rw [burnsideF429a_subgroupOf_inf, hP₁, hP₂, Subgroup.map_inf_eq _ _ _ Φ.injective]
  have hGB : Gp ⊓ (M₁ ⊓ M₂) = (parP h ⊓ parP2 h).map φ := burnsideF429_inf_eq_map Φ hB
  have hS : pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) = (hypUnitriangular h 2 0).map φ := by
    rw [hGB, CFSG.Quasithin.H13.U4Par.pCoreOf_map_of_inj hφ, burnsideF4gU4Inv_pCore_borel]
  have hL₂ : oPPrime 2 (Gp ⊓ M₂) = (oPPrime 2 (parP2 h)).map φ := by
    rw [hG₂, burnsideF4gU4Inv_oPPrime_map hφ]
  obtain ⟨g, hg, τ, hgτ⟩ := burnsideF429a_U4_nf h Φ hP₁ hP₂ hr
  have hgP : g ∈ parP h := burnsideF429a_U4_normalizer_le_parP h hg
  have hτ : τ = 1 := by
    refine RingEquiv.ext fun c => ?_
    show τ c = c
    by_cases hc0 : c = 0
    · rw [hc0, map_zero]
    have hbP := burnsideF429a_U4_lev2_d_mem_parP h (Units.mk0 c hc0)
    have hbP2 : lev2Hom h (burnsideF429a_U4_dSL (Units.mk0 c hc0)) ∈ parP2 h :=
      lev2Hom_le_parP2 h ⟨_, rfl⟩
    have hbO := burnsideF429a_U4_lev2_d_mem_oPPrime h (Units.mk0 c hc0)
    have hb : φ (lev2Hom h (burnsideF429a_U4_dSL (Units.mk0 c hc0))) ∈
        oPPrime 2 (Gp ⊓ M₂) ⊓ (M₁ ⊓ M₂) := by
      refine ⟨?_, ?_⟩
      · rw [hL₂]
        exact ⟨_, hbO, rfl⟩
      · have : φ (lev2Hom h (burnsideF429a_U4_dSL (Units.mk0 c hc0))) ∈ Gp ⊓ (M₁ ⊓ M₂) := by
          rw [hGB]
          exact ⟨_, ⟨hbP, hbP2⟩, rfl⟩
        exact this.2
    have h1 := hcomm _ hb
    rw [hS, hφx (lev2Hom h _), ← hgτ, ← hφx, ← hφx, ← map_inv, ← map_mul] at h1
    have h2 := (Subgroup.mem_map_iff_mem hφ).mp h1
    have h3 := burnsideF429a_U4_chi_of_mem_U h h2
    have hτbP := burnsideF429a_U4_fieldAut_mem_parP h τ hbP
    rw [chi_mul h ((parP h).inv_mem hbP), chi_mul h ((parP h).inv_mem hgP), chi_mul h hτbP,
      burnsideF429a_U4_chi_fieldAut, burnsideF429a_U4_chi_lev2_d, Units.val_mk0] at h3
    have hgg := chi_mul_inv h hgP
    have hbb := chi_mul_inv h hbP
    rw [burnsideF429a_U4_chi_lev2_d, Units.val_mk0] at hbb
    have hne : chi h (lev2Hom h (burnsideF429a_U4_dSL (Units.mk0 c hc0)))⁻¹ ≠ 0 := by
      intro h0
      rw [h0, mul_zero] at hbb
      exact zero_ne_one hbb
    apply mul_right_cancel₀ hne
    linear_combination h3 - hbb -
      τ c * chi h (lev2Hom h (burnsideF429a_U4_dSL (Units.mk0 c hc0)))⁻¹ * hgg
  have e1 : ∀ x, ((Φ (g * x * g⁻¹) : ↥Gp) : E) = r * ((Φ x : ↥Gp) : E) * r⁻¹ := by
    intro x
    have := hgτ x
    rwa [hτ, fieldAut_apply, fieldHom_one] at this
  rw [burnsideF429a_eq_of_conj hc Φ e1]
  exact (Φ g).2

end R5

section Main

open CFSG.Open CFSG.ASVolI.ChF CFSG.Quasithin

theorem burnsideF429a_r5_line {f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}
    (hyp : HypF_4_4 .U4 2 f Gp M₁ M₂) (_hev : ¬ Odd Gp.index) {T : Subgroup E}
    (hT : ChF.IsSylowOf 2 T (M₁ ⊓ M₂)) :
    pCoreOf 2 (oPPrime 2 (Gp ⊓ M₂) ⊔ T) = pCoreOf 2 (oPPrime 2 (Gp ⊓ M₂)) := by
  haveI := hyp.finite
  haveI := hyp.normal
  obtain ⟨marking, h1, h2⟩ := burnsideF4g_marking (c := .U4) hyp.toHypF_4_4g
  obtain ⟨Φ, e1, e2⟩ := burnsideF4gU4_exists_equiv marking
  exact burnsideF429a_c5_of_key (burnsideF429a_U4_sylow_of_model _ Φ (h1.trans e1) (h2.trans e2))
    inf_le_right hT
    (burnsideF429a_key2_U4_of_model hyp.centralizer_trivial _ Φ (h1.trans e1) (h2.trans e2))

end Main

end CFSG.ASVolI
