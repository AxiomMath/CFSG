module

public import CFSG.RankThree.PartTwo.Sec6.HeringB3Tools
public import CFSG.RankThree.PartTwo.Sec6.HeringB3U4Eigen
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherPrimeFormRealization
import CFSG.RankThree.PartTwo.Sec6.BThreeCensusSL3
import CFSG.RankThree.PartTwo.Sec4.Item47WitnessU4
import CFSG.RankThree.PartTwo.Sec4.Item417Res6ProofSp4
import CFSG.RankThree.PartTwo.Sec13.Item13Res5ProofTools
import CFSG.RankThree.SubgroupLists.CentralThreeLift
import CFSG.Models.PGLSimple
import CFSG.RankThree.PartOne.N143.HeisenbergThree

public section

namespace CFSG.RankThree.PartTwo.Sec6.BThreeCensus

open CFSG CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.KFacts
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ClassicalGroups.UnitaryFlag Matrix

section Certs


variable {p f : ℕ} {K : Type} [Field K] [Finite K] (h : UnitaryFieldData p f K)

theorem scalar_fin4_injective : Function.Injective
    (GeneralLinearGroup.scalar (Fin 4) : Kˣ →* GL (Fin 4) K) := by
  intro a b hab
  have := congrArg (fun g : GL (Fin 4) K => (g : Matrix (Fin 4) (Fin 4) K) 0 0) hab
  apply Units.ext
  simpa [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply] using this

theorem eq_one_of_mem_normOneScalars_of_pow_three {Z : Subgroup (gramSU h
    ((1 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K))} (hZ : Z = normOneScalars h
    (gramSU h ((1 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)) 4)
    {e : gramSU h ((1 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)} (he : e ∈ Z) (he3 : e ^ 3 = 1) :
    e = 1 := by
  subst hZ
  obtain ⟨c, -, hc4, hec⟩ := he
  have hc3 : c ^ 3 = 1 := by
    have h1 : (GeneralLinearGroup.scalar (Fin 4) c) ^ 3 = 1 := by
      rw [← hec, ← Subgroup.coe_pow, he3, Subgroup.coe_one]
    rw [← map_pow] at h1
    exact scalar_fin4_injective (h1.trans (map_one _).symm)
  have hc1 : c = 1 := by
    calc c = c ^ 4 * (c ^ 3)⁻¹ := by group
      _ = 1 := by rw [hc4, hc3]; simp
  apply Subtype.ext
  rw [hec, hc1, map_one]
  rfl

theorem eq_bot_of_perfect_fixed_primeForm {ω : K} (hω : ω ^ 2 + ω + 1 = 0) (hbarω : h.bar ω = ω)
    (h3K : (3 : K) ≠ 0)
    {B : primeFormUnitary h ((1 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)}
    (hB3 : (B : GL (Fin 4) K) ^ 3 = 1) (hB1 : (B : GL (Fin 4) K) ≠ 1)
    (Y : Subgroup (primeFormP h ((1 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)))
    (hYfix : ∀ y ∈ Y, primeFormConjHom h _ B y = y) (hYp : Group.IsPerfect Y)
    (hY3 : ¬ 3 ∣ Nat.card Y) : Y = ⊥ := by
  have hC : IsPrimeFormGram (1 : GL (Fin 4) K) := Sec4.isPrimeFormGram_one_GL
  set S := gramSU h ((1 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) with hS
  set Z := normOneScalars h S 4 with hZ
  have hZc : Z ≤ Subgroup.center S := (unitary_prime_form_automorphism_data h hC).2.2.2.2.2.1
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set D : Subgroup S := ⁅Y.comap (QuotientGroup.mk' Z), Y.comap (QuotientGroup.mk' Z)⁆ with hD
  have hDp : Group.IsPerfect D :=
    CFSG.RankThree.SubgroupLists.isPerfect_commutator_comap hZc Y
  have hDmap : D.map (QuotientGroup.mk' Z) = Y :=
    CFSG.RankThree.SubgroupLists.map_commutator_comap Y
  have hmemD : ∀ d ∈ D, QuotientGroup.mk' Z d ∈ Y := fun d hd => by
    rw [← hDmap]
    exact ⟨d, hd, rfl⟩
  have hD3 : ¬ 3 ∣ Nat.card D := by
    intro h3D
    obtain ⟨e, he⟩ := exists_prime_orderOf_dvd_card' 3 h3D
    have he3 : (e : S) ^ 3 = 1 := by
      have h1 : e ^ 3 = 1 := by
        have := pow_orderOf_eq_one e
        rwa [he] at this
      exact congrArg Subtype.val h1
    have hpe1 : QuotientGroup.mk' Z (e : S) = 1 :=
      eq_one_of_pow_three_eq_one_of_not_three_dvd hY3 (hmemD _ e.2)
        (by rw [← map_pow, he3, map_one])
    have heZ : (e : S) ∈ Z := (QuotientGroup.eq_one_iff _).mp hpe1
    have he1 : (e : S) = 1 := eq_one_of_mem_normOneScalars_of_pow_three h hZ heZ he3
    have : e = 1 := Subtype.ext he1
    rw [this, orderOf_one] at he
    omega
  set D' : Subgroup (GL (Fin 4) K) := D.map S.subtype with hD'
  have hD'p : Group.IsPerfect D' := Group.IsPerfect.map _
  have hD'3 : ¬ 3 ∣ Nat.card D' := by
    rwa [hD', Subgroup.card_map_of_injective S.subtype_injective]
  have hscal : ∀ c : Kˣ, (GeneralLinearGroup.scalar (Fin 4) c : GL (Fin 4) K) ∈
      Subgroup.center (GL (Fin 4) K) := fun c => by
    rw [GeneralLinearGroup.center_eq_range_scalar]
    exact ⟨c, rfl⟩
  have hcen : ∀ y ∈ D', (MulAut.conj (B : GL (Fin 4) K)).toMonoidHom y * y⁻¹ ∈
      Subgroup.center (GL (Fin 4) K) := by
    rintro _ ⟨d, hd, rfl⟩
    have hfix := hYfix _ (hmemD d hd)
    rw [QuotientGroup.mk'_apply, primeFormConjHom_mk] at hfix
    obtain ⟨c, -, -, hc⟩ := (QuotientGroup.eq.mp hfix : _ ∈ Z)
    set u : GL (Fin 4) K := (B : GL (Fin 4) K) * (d : GL (Fin 4) K) * (B : GL (Fin 4) K)⁻¹
      with hu
    have hc' : u⁻¹ * (d : GL (Fin 4) K) = GeneralLinearGroup.scalar (Fin 4) c := by
      rw [← hc]
      rfl
    have hdu : (d : GL (Fin 4) K) = u * GeneralLinearGroup.scalar (Fin 4) c := by
      rw [← hc']
      group
    have hmem := inv_mem (hscal c)
    have hcomm := Subgroup.mem_center_iff.mp hmem u
    have : (MulAut.conj (B : GL (Fin 4) K)).toMonoidHom (S.subtype d) * (S.subtype d)⁻¹ =
        (GeneralLinearGroup.scalar (Fin 4) c)⁻¹ := by
      change (B : GL (Fin 4) K) * (d : GL (Fin 4) K) * (B : GL (Fin 4) K)⁻¹ *
        (d : GL (Fin 4) K)⁻¹ = _
      rw [← hu, hdu, _root_.mul_inv_rev, ← mul_assoc, hcomm, mul_assoc, mul_inv_cancel,
        mul_one]
    rw [this]
    exact hmem
  have hfixD : ∀ y ∈ D', (MulAut.conj (B : GL (Fin 4) K)).toMonoidHom y = y :=
    eq_of_mul_inv_mem_center hD'p _ hcen
  have hcomm' : ∀ y ∈ D', y * (B : GL (Fin 4) K) = (B : GL (Fin 4) K) * y := fun y hy => by
    have h1 := hfixD y hy
    change (B : GL (Fin 4) K) * y * (B : GL (Fin 4) K)⁻¹ = y at h1
    calc y * (B : GL (Fin 4) K) = ((B : GL (Fin 4) K) * y * (B : GL (Fin 4) K)⁻¹) *
          (B : GL (Fin 4) K) := by rw [h1]
      _ = (B : GL (Fin 4) K) * y := by group
  have hbu : (((B : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).map h.bar)ᵀ *
      ((B : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = 1 := by
    simpa using mem_primeFormUnitary.mp B.2
  have hD'bot := eq_bot_of_commute_of_unitary (n := Fin 4) (by simp) h.bar hω hbarω h3K hB3 hB1
    hbu D' hcomm' hD'p hD'3
  have hDbot : D = ⊥ :=
    (Subgroup.map_eq_bot_iff_of_injective D S.subtype_injective).mp hD'bot
  rw [← hDmap, hDbot, Subgroup.map_bot]

theorem exists_cubeRoot_fixed (hp3 : p ≠ 3) (hq : p ^ f % 3 = 1) :
    ∃ ω : K, ω ^ 2 + ω + 1 = 0 ∧ h.bar ω = ω ∧ (3 : K) ≠ 0 := by
  haveI : Fact p.Prime := ⟨h.prime⟩
  haveI : CharP K p := h.charP
  have hq3 : ¬ 3 ∣ p ^ f := by omega
  have hdvd : 3 ∣ Nat.card K - 1 := by
    rw [h.card, show 2 * f = f * 2 from mul_comm _ _, pow_mul]
    exact three_dvd_sq_sub_one hq3
  obtain ⟨ζ, hζ⟩ := Sec4.Res417Six.exists_primitiveRoot_three hdvd
  set ω : K := (ζ : K) with hωdef
  have hω3 : ω ^ 3 = 1 := by
    have := hζ.pow_eq_one
    rw [hωdef, ← Units.val_pow_eq_pow_val, this, Units.val_one]
  have hω1 : ω ≠ 1 := by
    intro h1
    have : ζ = 1 := Units.ext h1
    have h31 := hζ.eq_orderOf
    rw [this, orderOf_one] at h31
    omega
  refine ⟨ω, ?_, ?_, ?_⟩
  · have h' : (ω - 1) * (ω ^ 2 + ω + 1) = 0 := by linear_combination hω3
    exact (mul_eq_zero.mp h').resolve_left (sub_ne_zero.mpr hω1)
  · rw [h.bar_apply]
    obtain ⟨k, hk⟩ : ∃ k, p ^ f = 3 * k + 1 := ⟨p ^ f / 3, by omega⟩
    rw [hk, pow_succ, pow_mul, hω3, one_pow, one_mul]
  · intro h3
    have h3' : ((3 : ℕ) : K) = 0 := by exact_mod_cast h3
    rw [CharP.cast_eq_zero_iff K p] at h3'
    exact hp3 ((Nat.prime_dvd_prime_iff_eq h.prime Nat.prime_three).mp h3')

theorem exists_normalized_unitary (hq : p ^ f % 3 = 1)
    (A : primeFormUnitary h ((1 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)) {c : Kˣ}
    (hc : h.norm (c : K) = 1)
    (hA : (A : GL (Fin 4) K) ^ 3 = GeneralLinearGroup.scalar (Fin 4) c) :
    ∃ B : primeFormUnitary h ((1 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K),
      primeFormConjHom h _ B = primeFormConjHom h _ A ∧ (B : GL (Fin 4) K) ^ 3 = 1 := by
  haveI : Fact p.Prime := ⟨h.prime⟩
  have hc1 : c ^ (p ^ f + 1) = 1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_one, pow_succ]
    have : (c : K) * h.bar (c : K) = 1 := hc
    rw [h.bar_apply] at this
    rw [← this]
    ring
  obtain ⟨m, hm⟩ : ∃ m, 3 * m = p ^ f + 2 := ⟨(p ^ f + 2) / 3, by omega⟩
  set l : Kˣ := (c⁻¹) ^ m with hl
  have hl3 : l ^ 3 = c⁻¹ := by
    have e1 : l ^ 3 = (c⁻¹) ^ (p ^ f + 1 + 1) := by rw [hl, ← pow_mul, mul_comm m 3, hm]
    rw [e1, pow_succ, inv_pow, hc1, inv_one, one_mul]
  have hNl : h.norm (l : K) = 1 := by
    change (l : K) * h.bar (l : K) = 1
    rw [h.bar_apply, ← pow_succ']
    have : l ^ (p ^ f + 1) = 1 := by
      rw [hl, ← pow_mul, mul_comm, pow_mul, inv_pow, hc1, inv_one, one_pow]
    have h2 := congrArg Units.val this
    rw [Units.val_pow_eq_pow_val, Units.val_one] at h2
    exact h2
  have hlU : GeneralLinearGroup.scalar (Fin 4) l ∈
      primeFormUnitary h ((1 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) := by
    rw [mem_primeFormUnitary, GeneralLinearGroup.coe_scalar, scalar_barTranspose_mul_mul, hNl,
      one_smul]
  refine ⟨⟨_, mul_mem hlU A.2⟩, ?_, ?_⟩
  · have hmul : (⟨_, mul_mem hlU A.2⟩ : primeFormUnitary h
        ((1 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)) = ⟨_, hlU⟩ * A := rfl
    rw [hmul, map_mul, Sec4.WitnessU4.primeFormConjHom_scalar, one_mul]
  · change (GeneralLinearGroup.scalar (Fin 4) l * (A : GL (Fin 4) K)) ^ 3 = 1
    rw [(commute_scalar l (A : GL (Fin 4) K)).symm.mul_pow, hA, ← map_pow, hl3, ← map_mul,
      inv_mul_cancel, map_one]

theorem eq_one_of_pow_three_of_card_sq {K' : Type} [Field K'] [Finite K'] {p : ℕ} (hp : p.Prime)
    (hK : Nat.card K' = p ^ 2) (φ : K' ≃+* K') (hφ : φ ^ 3 = 1) : φ = 1 := by
  by_contra hne
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hord : orderOf φ = 3 := orderOf_eq_prime hφ hne
  have hcard := CFSG.GH74.GLS.IVK.fixedField_card_pow φ
  rw [hord, hK] at hcard
  set m := Nat.card (CFSG.GH74.GLS.IVK.fixedField φ) with hm
  have hpm : p ∣ m := hp.dvd_of_dvd_pow (n := 3) (by rw [hcard]; exact dvd_pow_self p (by norm_num))
  obtain ⟨k, hk⟩ := hpm
  have h1 : p ^ 3 * k ^ 3 = p ^ 2 := by rw [← hcard, hk]; ring
  have h2 : p * k ^ 3 = 1 := by
    have hpos : 0 < p ^ 2 := pow_pos hp.pos 2
    have : p ^ 2 * (p * k ^ 3) = p ^ 2 * 1 :=
      calc p ^ 2 * (p * k ^ 3) = p ^ 3 * k ^ 3 := by ring
        _ = p ^ 2 := h1
        _ = p ^ 2 * 1 := (mul_one _).symm
    exact Nat.eq_of_mul_eq_mul_left hpos this
  exact hp.one_lt.ne' (Nat.eq_one_of_mul_eq_one_right h2)

theorem threePrimeB3_primeFormP_four (hp3 : p ≠ 3) (hq : p ^ f % 3 = 1)
    (hno : ∀ φ : K ≃+* K, φ ^ 3 = 1 → φ = 1)
    (hsimple : IsSimpleGroup (primeFormP h ((1 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)))
    (h3 : ∃ x : primeFormP h ((1 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K), x ≠ 1 ∧ x ^ 3 = 1)
    (hn : ¬ (4 = 3 ∧ p ^ f = 2)) :
    ThreePrimeB3 (primeFormP h ((1 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)) := by
  have hC : IsPrimeFormGram (1 : GL (Fin 4) K) := Sec4.isPrimeFormGram_one_GL
  refine threePrimeB3_of_b3Fix fun β hβ C hC' => ?_
  obtain ⟨φ, ⟨A, hA⟩, -⟩ := existsUnique_primeFormFieldFactor h hC (by norm_num) hn β
  have hφ3 : φ ^ 3 = 1 := by
    have hΨ : primeFormPsi h hC (⟨A, φ⟩ * (⟨A, φ⟩ * ⟨A, φ⟩)) = 1 := by
      rw [← pow_three, map_pow, primeFormPsi_apply, ← hA, hβ]
    obtain ⟨hright, -⟩ := (primeFormPsi_eq_one_iff h hC (by norm_num) _).mp hΨ
    rw [SemidirectProduct.mul_right, SemidirectProduct.mul_right] at hright
    rw [pow_three]
    exact hright
  have hφ1 : φ = 1 := hno φ hφ3
  subst hφ1
  have hβA : β = primeFormConjHom h _ A := by rw [hA, map_one, mul_one]
  have hA3 : primeFormConjHom h _ (A ^ 3) = 1 := by rw [map_pow, ← hβA, hβ]
  obtain ⟨-, c, hc, hAc⟩ := (primeFormPsi_eq_one_iff h hC (by norm_num) ⟨A ^ 3, 1⟩).mp (by
    rw [primeFormPsi_apply, map_one, mul_one]
    exact hA3)
  have hAc' : (A : GL (Fin 4) K) ^ 3 = GeneralLinearGroup.scalar (Fin 4) c := hAc
  obtain ⟨B, hBA, hB3⟩ := exists_normalized_unitary h hq A hc hAc'
  have hβB : β = primeFormConjHom h _ B := by rw [hβA, hBA]
  by_cases hB1 : (B : GL (Fin 4) K) = 1
  ·
    have hβ1 : β = 1 := by rw [hβB, show B = 1 from Subtype.ext hB1, map_one]
    have hCtop : C = ⊤ := Subgroup.ext fun z => by
      refine ⟨fun _ => Subgroup.mem_top z, fun _ => ?_⟩
      rw [hC' z, hβ1]
      rfl
    rw [hCtop]
    obtain ⟨x, hx1, hx3⟩ := h3
    exact b3Fix_of_perfSubnormalBot (perfSubnormalBot_of_isSimpleGroup
      Subgroup.topEquiv.isSimpleGroup ⟨x, Subgroup.mem_top x, hx1, hx3⟩)
  · obtain ⟨ω, hω, hbarω, h3K⟩ := exists_cubeRoot_fixed h hp3 hq
    refine b3Fix_of_perfSubnormalBot fun Y hYC _ hYp hY3 => ?_
    exact eq_bot_of_perfect_fixed_primeForm h hω hbarω h3K hB3 hB1 Y
      (fun y hy => by rw [← hβB]; exact (hC' y).mp (hYC hy)) hYp hY3

end Certs

section Model


open CFSG.Assembly.RankThreeEven (projSU)


theorem threePrimeB3_projSU_four_prime {p : ℕ} [Fact p.Prime] (hp3 : 3 < p) (hq : p % 3 = 1) :
    ThreePrimeB3 (projSU 4 p 1) := by
  set K := GaloisField p (2 * 1) with hKdef
  have hU : UnitaryFieldData p 1 K := Sec4.unitaryFieldData_galoisField p 1 le_rfl
  haveI := hU.finite
  have hC : IsPrimeFormGram (1 : GL (Fin 4) K) := Sec4.isPrimeFormGram_one_GL
  have hn : ¬ (4 = 3 ∧ p ^ 1 = 2) := fun h' => absurd h'.1 (by norm_num)
  obtain ⟨⟨e₃⟩, -⟩ := unitary_prime_form_full_semilinear_realization hU hC (by norm_num) hn
  let e : projSU 4 p 1 ≃* primeFormP hU ((1 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) :=
    (Sec4.projSUEquivStatedProj 4 p 1).trans
      ((unitaryPSUEquiv hU (by norm_num)).symm.trans e₃.symm)
  haveI : Finite (projSU 4 p 1) := inferInstance
  haveI hsimple : IsSimpleGroup (projSU 4 p 1) :=
    CFSG.PGLModel.isSimpleGroup_projSU_of_admissible
      ⟨Fact.out, le_rfl, by norm_num, fun h' => by have := congrArg Prod.fst h'; simp at this⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' 3
    (Sec13.Res5Proof.three_dvd_card_projSU_four p 1)
  have hy3 : y ^ 3 = 1 := by
    have := pow_orderOf_eq_one y
    rwa [hy] at this
  have hy1 : y ≠ 1 := fun h' => by simp [h'] at hy
  have hno : ∀ φ : K ≃+* K, φ ^ 3 = 1 → φ = 1 :=
    eq_one_of_pow_three_of_card_sq Fact.out (by rw [hU.card])
  exact threePrimeB3_of_mulEquiv e (threePrimeB3_primeFormP_four hU (by omega)
    (by simpa using hq) hno e.symm.isSimpleGroup
    ⟨e y, fun h' => hy1 (e.injective (h'.trans (map_one e).symm)), by rw [← map_pow, hy3, map_one]⟩
    hn)

theorem threePrimeB3_of_projSU_four_prime {X : Type} [Group X] {p : ℕ} [Fact p.Prime]
    (hp3 : 3 < p) (hq : p % 3 = 1) (e : X ≃* projSU 4 p 1) : ThreePrimeB3 X :=
  threePrimeB3_of_mulEquiv e (threePrimeB3_projSU_four_prime hp3 hq)

end Model

end CFSG.RankThree.PartTwo.Sec6.BThreeCensus
