module

public import CFSG.GH74.KGroups.L3EpsUniInv
public import CFSG.GH74.KGroups.L3EpsCenter
public import CFSG.LocalAnalysis.UniquenessCase.UC22L3LinBasic
import CFSG.LocalAnalysis.ComponentInitial.UnitaryDiagonalOuterOrder
import CFSG.LocalAnalysis.ComponentInitial.FieldFiniteAutomorphism
import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherIsotropicRadical
public import CFSG.GH74.Generic.S45.LUniLift
public import CFSG.GH74.KGroups.L3EpsUniGraph
public import CFSG.Sporadic.Th.Max3.Packet
public import CFSG.Sporadic.Th.Max3.Quotient
public import Certificates.Certificate10091Base

public noncomputable section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.L3Uni

open Matrix Subgroup CFSG.ClassicalGroups.UnitaryFlag CFSG.GH74.KGroups.L3Eps
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open scoped MatrixGroups

variable {p f : ℕ} {F : Type} [Field F] (h : UnitaryFieldData p f F)

local notation "𝟙" => ((1 : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)

@[expose] def suEquiv : ↥(unitarySU p f F 3) ≃* gramSU h 𝟙 :=
  MulEquiv.subgroupCongr (unitarySU_eq_gramSU h 3)

theorem coe_suEquiv (g : ↥(unitarySU p f F 3)) : (suEquiv h g : GL (Fin 3) F) = g :=
  MulEquiv.subgroupCongr_apply _ _

@[expose] def proj : ↥(unitarySU p f F 3) →* primeFormP h 𝟙 :=
  (QuotientGroup.mk' (normOneScalars h (gramSU h 𝟙) 3)).comp (suEquiv h).toMonoidHom

theorem proj_surjective : Function.Surjective (proj h) :=
  (QuotientGroup.mk'_surjective _).comp (suEquiv h).surjective

theorem proj_isCover : Uni.IsCover h (proj h) := by
  refine ⟨proj_surjective h, ?_⟩
  ext g
  rw [MonoidHom.mem_ker, proj, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    ← MonoidHom.mem_ker, QuotientGroup.ker_mk', mem_unitaryScalars, mem_normOneScalars]
  change (∃ c : Fˣ, h.norm (c : F) = 1 ∧ c ^ 3 = 1 ∧
    ((suEquiv h g : gramSU h 𝟙) : GL (Fin 3) F) = GeneralLinearGroup.scalar (Fin 3) c) ↔ _
  rw [coe_suEquiv]

abbrev I : Subgroup (MulAut (primeFormP h 𝟙)) := (MulAut.conj : _ →* _).range

abbrev P : Subgroup (MulAut (primeFormP h 𝟙)) := primeFormD h 𝟙

theorem I_le_P : I h ≤ P h := by
  rintro _ ⟨x, rfl⟩
  obtain ⟨s, rfl⟩ := QuotientGroup.mk_surjective x
  exact ⟨⟨s, s.2.1⟩, primeFormConjHom_eq_conj h 𝟙 s⟩

theorem P_normal (h5 : 5 ≤ p ^ f) : (P h).Normal := by
  change (primeFormD h 𝟙).Normal
  rw [← ker_primeFormFieldFactor h isPrimeFormGram_one (by norm_num)
    (show ¬ (3 = 3 ∧ p ^ f = 2) by omega)]
  infer_instance

theorem mul_mem_P_of_not_mem (hf : f = 1) (g g' : MulAut (primeFormP h 𝟙))
    (hg : g ∉ P h) (hg' : g' ∉ P h) (h5 : 5 ≤ p ^ f) : g * g' ∈ P h := by
  subst hf
  have hbad : ¬ (3 = 3 ∧ p ^ 1 = 2) := by omega
  let δ := primeFormFieldFactor h isPrimeFormGram_one (by norm_num)
    hbad
  have hker : δ.ker = P h := ker_primeFormFieldFactor h isPrimeFormGram_one _ _
  have hc : Nat.card (F ≃+* F) = 2 := by
    obtain ⟨-, -, -, -, hc, -⟩ := finite_field_automorphism_fixed_field_cardinality h.prime
      (by norm_num : 1 ≤ 2) (by simpa using h.card)
    exact hc
  have hfinite : Finite (F ≃+* F) := Nat.finite_of_card_ne_zero (hc ▸ by decide)
  have hn : δ g ≠ 1 := by
    intro hn
    exact hg (hker ▸ (MonoidHom.mem_ker.2 hn))
  have hn' : δ g' ≠ 1 := by
    intro hn'
    exact hg' (hker ▸ (MonoidHom.mem_ker.2 hn'))
  have heq : δ g = δ g' := by
    obtain ⟨a, ha, huniq⟩ := (Nat.card_eq_two_iff' (1 : F ≃+* F)).1 hc
    exact (huniq (δ g) hn).trans (huniq (δ g') hn').symm
  have hsq : (δ g) ^ 2 = 1 := by
    rw [← hc]
    exact pow_card_eq_one'
  rw [← hker, MonoidHom.mem_ker, map_mul, heq, ← sq]
  simpa only [← heq] using hsq

theorem mem_I_of_two (h5 : 5 ≤ p ^ f) (g : MulAut (primeFormP h 𝟙)) (hg : g ∈ P h)
    (n : ℕ) (hn : g ^ 2 ^ n = 1) : g ∈ I h := by
  obtain ⟨A, rfl⟩ := hg
  exact conjHom_pow_inner h h5 A hn

@[expose] def e : MulAut (primeFormP h 𝟙) := MulAut.conj (eU h : primeFormP h 𝟙)

@[expose] def r : MulAut (primeFormP h 𝟙) := MulAut.conj (rU h : primeFormP h 𝟙)

theorem e_mem_I : e h ∈ I h := ⟨_, rfl⟩

theorem r_mem_I : r h ∈ I h := ⟨_, rfl⟩

theorem e_pow_four : e h ^ 4 = 1 := by
  rw [e, ← map_pow, ← QuotientGroup.mk_pow, eU_pow_four, QuotientGroup.mk_one, map_one]

theorem r_sq : r h ^ 2 = 1 := by
  rw [r, ← map_pow, ← QuotientGroup.mk_pow, rU_sq, QuotientGroup.mk_one, map_one]

theorem r_e : r h * e h * (r h)⁻¹ = (e h)⁻¹ := by
  rw [e, r, ← map_inv, ← map_inv, ← map_mul, ← map_mul, ← QuotientGroup.mk_inv,
    ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, rU_eU]

theorem coe_eU_sq : ((eU h ^ 2 : gramSU h 𝟙) : GL (Fin 3) F) = L3Lin.dG := by
  change (SpecialLinearGroup.toGL (eSL : SL(3, F))) ^ 2 = SpecialLinearGroup.toGL dNeg
  rw [← map_pow, L3Lin.eSL_sq]

@[expose] def d : primeFormUnitary h 𝟙 :=
  ⟨L3Lin.dG, coe_eU_sq h ▸ (eU h ^ 2).2.1⟩

theorem coe_d : ((d h : primeFormUnitary h 𝟙) : GL (Fin 3) F) = L3Lin.dG := rfl

theorem e_sq : e h ^ 2 = primeFormConjHom h 𝟙 (d h) := by
  rw [e, ← map_pow, ← QuotientGroup.mk_pow, ← primeFormConjHom_eq_conj]
  congr 1
  exact Subtype.ext (coe_eU_sq h)

theorem e_sq_ne (hq : Odd (p ^ f)) : e h ^ 2 ≠ 1 := by
  rw [e_sq]
  intro h1
  obtain ⟨c, -, hc⟩ := eq_scalar_of_primeFormConjHom_eq_one h isPrimeFormGram_one
    (by norm_num) h1
  have h00 := congrArg (fun A : GL (Fin 3) F => (A : Matrix (Fin 3) (Fin 3) F) 0 0) hc
  have h22 := congrArg (fun A : GL (Fin 3) F => (A : Matrix (Fin 3) (Fin 3) F) 2 2) hc
  simp [coe_d, L3Lin.coe_dG, coe_dNeg, GeneralLinearGroup.coe_scalar] at h00 h22
  apply Uni.two_ne_zero_of_odd_pow h hq
  linear_combination h22 - h00

theorem proj_dU (hq : Odd (p ^ f)) : proj h (Uni.dU hq) = ((eU h ^ 2 : gramSU h 𝟙) :
    primeFormP h 𝟙) := by
  change ((suEquiv h (Uni.dU hq) : gramSU h 𝟙) : primeFormP h 𝟙) = _
  congr 1
  apply Subtype.ext
  rw [coe_suEquiv, coe_eU_sq]
  apply Units.ext
  exact Uni.coe_dU hq |>.trans (by rw [L3Lin.coe_dG, Uni.dNeg_coe_eq_diagonal])

theorem isPGroup_D8 : IsPGroup 2 ↥(closure ({e h, r h} : Set (MulAut (primeFormP h 𝟙)))) :=
  isPGroup_closure_dihedral (e_pow_four h) (r_sq h) (r_e h)

@[expose] def K₀ (hq : Odd (p ^ f)) : Subgroup (primeFormP h 𝟙) := Uni.levS hq (proj h)

@[expose] def Kb (hq : Odd (p ^ f)) : Subgroup (MulAut (primeFormP h 𝟙)) :=
  (K₀ h hq).map (MulAut.conj : _ →* _)

theorem card_K₀ (hq : Odd (p ^ f)) : Nat.card ↥(K₀ h hq) = p ^ f * ((p ^ f) ^ 2 - 1) :=
  Uni.card_levS h (proj_isCover h) hq

theorem perfect_K₀ (hq : Odd (p ^ f)) (h5 : 5 ≤ p ^ f) : ⁅K₀ h hq, K₀ h hq⁆ = K₀ h hq := by
  have hperf := (Uni.quasisimple_levS h (proj_isCover h) hq (by omega)).1
  exact Subgroup.isPerfect_iff.1 hperf

end CFSG.LocalAnalysis.UniquenessCase.UC22.L3Uni
