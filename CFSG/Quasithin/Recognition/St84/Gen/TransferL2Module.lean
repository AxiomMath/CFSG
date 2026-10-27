module

public import CFSG.LocalAnalysis.QuasithinUnique.PushingUp.Blocks

import CFSG.GroupTheory.NormalizerInfCentralizer
import CFSG.LocalAnalysis.EvenBN.Common.RadicalRank
import CFSG.Quasithin.Recognition.St84.Gen.SL2Semilinear
import CFSG.CGT.PushingUpLit.CGT6.SixFourU3Alg

public section

namespace CFSG.Quasithin.F112R.St84

open CFSG.Open CFSG.QuasithinUnique Matrix
open scoped commutatorElement MatrixGroups

variable {G : Type} [Group G]

private theorem conj_mul_conj_eq_of_mem {L Q : Subgroup G} {c l q : G}
    (hQ : IsMulCommutative ↥Q) (hcQ : c ∈ Subgroup.normalizer (Q : Set G))
    (hl : l ∈ L) (hLn : L ≤ Subgroup.normalizer (Q : Set G))
    (hcLQ : ⁅c, l⁆ ∈ Q) (hq : q ∈ Q) :
    c * (l * q * l⁻¹) * c⁻¹ = l * (c * q * c⁻¹) * l⁻¹ := by
  haveI : IsMulCommutative ↥Q := hQ
  have hquQ : c * q * c⁻¹ ∈ Q := (Subgroup.mem_normalizer_iff.mp hcQ q).mp hq
  have hlqQ : l * (c * q * c⁻¹) * l⁻¹ ∈ Q :=
    (Subgroup.mem_normalizer_iff.mp (hLn hl) (c * q * c⁻¹)).mp hquQ
  have hcomm : ⁅c, l⁆ * (l * (c * q * c⁻¹) * l⁻¹) =
      (l * (c * q * c⁻¹) * l⁻¹) * ⁅c, l⁆ :=
    congrArg Subtype.val (mul_comm' (⟨_, hcLQ⟩ : ↥Q) (⟨_, hlqQ⟩ : ↥Q))
  have hcl : c * l * c⁻¹ = ⁅c, l⁆ * l := by
    rw [commutatorElement_def]
    group
  calc c * (l * q * l⁻¹) * c⁻¹
      = (c * l * c⁻¹) * (c * q * c⁻¹) * (c * l * c⁻¹)⁻¹ := by group
    _ = (⁅c, l⁆ * l) * (c * q * c⁻¹) * (⁅c, l⁆ * l)⁻¹ := by rw [hcl]
    _ = l * (c * q * c⁻¹) * l⁻¹ := by
        have h1 : (⁅c, l⁆ * l) * (c * q * c⁻¹) * (⁅c, l⁆ * l)⁻¹ =
            ⁅c, l⁆ * (l * (c * q * c⁻¹) * l⁻¹) * ⁅c, l⁆⁻¹ := by group
        rw [h1, hcomm]
        group

private theorem exists_conjAddEnd {U : Type*} [Group U] {F : Type*} [Field F]
    (β : U →* Multiplicative (Fin 2 → F)) (hβ : Function.Surjective β)
    (φ : U ≃* U) (hN : β.ker ≤ (β.comp φ.toMonoidHom).ker) :
    ∃ E : (Fin 2 → F) →+ (Fin 2 → F), ∀ x : U,
      E (Multiplicative.toAdd (β x)) = Multiplicative.toAdd (β (φ x)) := by
  classical
  let ψ : U →* Multiplicative (Fin 2 → F) := β.comp φ.toMonoidHom
  let eβ : (U ⧸ β.ker) ≃* Multiplicative (Fin 2 → F) :=
    QuotientGroup.quotientKerEquivOfSurjective β hβ
  let ψbar : (U ⧸ β.ker) →* Multiplicative (Fin 2 → F) :=
    QuotientGroup.lift β.ker ψ hN
  let Em : Multiplicative (Fin 2 → F) →* Multiplicative (Fin 2 → F) :=
    ψbar.comp eβ.symm.toMonoidHom
  let E : (Fin 2 → F) →+ (Fin 2 → F) :=
    { toFun := fun v => Multiplicative.toAdd (Em (Multiplicative.ofAdd v))
      map_zero' := by simp
      map_add' := by
        intro x y
        change Multiplicative.toAdd (Em (Multiplicative.ofAdd (x + y))) =
          Multiplicative.toAdd (Em (Multiplicative.ofAdd x)) +
          Multiplicative.toAdd (Em (Multiplicative.ofAdd y))
        rw [show Multiplicative.ofAdd (x + y) =
          Multiplicative.ofAdd x * Multiplicative.ofAdd y from rfl, map_mul]
        rfl }
  refine ⟨E, fun x => ?_⟩
  have h1 : eβ.symm (β x) = QuotientGroup.mk x := by
    rw [MulEquiv.symm_apply_eq]
    rfl
  change Multiplicative.toAdd (Em (Multiplicative.ofAdd (Multiplicative.toAdd (β x)))) =
    Multiplicative.toAdd (β (φ x))
  change Multiplicative.toAdd (ψbar (eβ.symm (β x))) = Multiplicative.toAdd (β (φ x))
  rw [h1, QuotientGroup.lift_mk]
  rfl

private theorem ker_le_comp_normalizerMonoidHom {U Z : Subgroup G} {F : Type*} [Field F]
    {c : G} (β : ↥U →* Multiplicative (Fin 2 → F))
    (hβker : β.ker = Z.subgroupOf U)
    (φ : ↥U ≃* ↥U) (hφ : ∀ x : ↥U, (φ x : G) = c * (x : G) * c⁻¹)
    (hcZ : c ∈ Subgroup.normalizer (Z : Set G)) :
    β.ker ≤ (β.comp φ.toMonoidHom).ker := by
  intro x hx
  have hxZ : (x : G) ∈ Z := by
    have hxs : x ∈ Z.subgroupOf U := by
      rw [← hβker]
      exact hx
    simpa [Subgroup.mem_subgroupOf] using hxs
  have hφZ : ((φ x : ↥U) : G) ∈ Z := by
    rw [hφ x]
    exact (Subgroup.mem_normalizer_iff.mp hcZ (x : G)).mp hxZ
  show φ x ∈ β.ker
  rw [hβker]
  simpa [Subgroup.mem_subgroupOf] using hφZ

private theorem conjAddEnd_comm_SL2 {L U : Subgroup G} {F : Type*} [Field F] {c : G}
    (α : ↥L →* Matrix.SpecialLinearGroup (Fin 2) F) (hα : Function.Surjective α)
    (β : ↥U →* Multiplicative (Fin 2 → F)) (hβ : Function.Surjective β)
    (hβcomm : ∀ ℓ : ↥L, ∀ u v : ↥U, (v : G) = ℓ * u * ℓ⁻¹ →
      Multiplicative.toAdd (β v) = (α ℓ : Matrix (Fin 2) (Fin 2) F) *ᵥ
        Multiplicative.toAdd (β u))
    (hLU : L ≤ Subgroup.normalizer (U : Set G))
    (φ : ↥U ≃* ↥U) (hφ : ∀ x : ↥U, (φ x : G) = c * (x : G) * c⁻¹)
    (hconj : ∀ (l q : G), l ∈ L → q ∈ U →
      c * (l * q * l⁻¹) * c⁻¹ = l * (c * q * c⁻¹) * l⁻¹)
    (E : (Fin 2 → F) →+ (Fin 2 → F))
    (hE : ∀ x : ↥U, E (Multiplicative.toAdd (β x)) = Multiplicative.toAdd (β (φ x))) :
    ∀ (A : Matrix.SpecialLinearGroup (Fin 2) F) (v : Fin 2 → F),
      E ((A : Matrix (Fin 2) (Fin 2) F) *ᵥ v) =
        (A : Matrix (Fin 2) (Fin 2) F) *ᵥ (E v) := by
  intro A v
  obtain ⟨l, rfl⟩ := hα A
  obtain ⟨x, hx⟩ := hβ (Multiplicative.ofAdd v)
  have hxv : Multiplicative.toAdd (β x) = v := by rw [hx]; rfl
  rw [← hxv]
  let w : ↥U := ⟨(l : G) * (x : G) * (l : G)⁻¹,
    (Subgroup.mem_normalizer_iff.mp (hLU l.2) (x : G)).mp x.2⟩
  have hβw : Multiplicative.toAdd (β w) =
      (α l : Matrix (Fin 2) (Fin 2) F) *ᵥ Multiplicative.toAdd (β x) :=
    hβcomm l x w rfl
  rw [← hβw, hE w, hE x]
  have hφw : (φ w : G) = (l : G) * (φ x : G) * (l : G)⁻¹ := by
    rw [hφ w, hφ x]
    exact hconj (l : G) (x : G) l.2 x.2
  exact hβcomm l (φ x) (φ w) hφw

private theorem iterate_conjAddEnd {U : Type*} [Group U] {F : Type*} [Field F]
    (β : U →* Multiplicative (Fin 2 → F)) (φ : U ≃* U)
    (E : (Fin 2 → F) →+ (Fin 2 → F))
    (hE : ∀ x : U, E (Multiplicative.toAdd (β x)) = Multiplicative.toAdd (β (φ x)))
    (k : ℕ) (x : U) :
    (⇑E)^[k] (Multiplicative.toAdd (β x)) =
      Multiplicative.toAdd (β ((φ ^ k) x)) := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Function.iterate_succ_apply', ih, hE, pow_succ', MulAut.mul_apply]

private theorem conjAddEnd_iterate_eq_self {U : Type*} [Group U] {F : Type*} [Field F]
    {m : ℕ} (β : U →* Multiplicative (Fin 2 → F)) (hβ : Function.Surjective β)
    (φ : U ≃* U) (E : (Fin 2 → F) →+ (Fin 2 → F))
    (hE : ∀ x : U, E (Multiplicative.toAdd (β x)) = Multiplicative.toAdd (β (φ x)))
    (hφ : φ ^ (2 ^ m) = 1) :
    ∀ v : Fin 2 → F, (⇑E)^[2 ^ m] v = v := by
  intro v
  obtain ⟨x, hx⟩ := hβ (Multiplicative.ofAdd v)
  have hxv : Multiplicative.toAdd (β x) = v := by rw [hx]; rfl
  rw [← hxv, iterate_conjAddEnd β φ E hE (2 ^ m) x, hφ]
  simp

private theorem pow_eq_one_of_conjAddEnd {F : Type*} [Field F] {m : ℕ}
    {E : (Fin 2 → F) →+ (Fin 2 → F)} (hfix : ∀ v, (⇑E)^[2 ^ m] v = v)
    {z : F} (hz : ∀ v, E v = z • v) : z ^ (2 ^ m) = 1 := by
  have hiterz : ∀ (k : ℕ) (v : Fin 2 → F), (⇑E)^[k] v = z ^ k • v := by
    intro k
    induction k with
    | zero => intro v; simp
    | succ k ih =>
        intro v
        rw [Function.iterate_succ_apply', ih, hz, smul_smul, pow_succ']
  have h := hfix ![1, 0]
  rw [hiterz (2 ^ m) ![1, 0]] at h
  have h0 := congrFun h 0
  simpa using h0

private theorem eq_one_of_pow_two_pow_eq_one_of_card {F : Type*} [Field F] [Fintype F]
    {n m : ℕ} {z : F} (hcard : Fintype.card F = 2 ^ n)
    (hz : z ^ (2 ^ m) = 1) (hz' : z ^ (2 ^ n - 1) = 1) : z = 1 := by
  have hn1 : 1 ≤ n := by
    have h2 : 1 < Fintype.card F := Fintype.one_lt_card
    rw [hcard] at h2
    by_contra hn
    have hn0 : n = 0 := by omega
    rw [hn0, pow_zero] at h2
    exact lt_irrefl 1 h2
  have hdvd1 : orderOf z ∣ 2 ^ m := orderOf_dvd_of_pow_eq_one hz
  have hdvd2 : orderOf z ∣ 2 ^ n - 1 := orderOf_dvd_of_pow_eq_one hz'
  have hodd : Odd (2 ^ n - 1) :=
    Nat.Even.sub_odd Nat.one_le_two_pow
      (by rw [Nat.even_pow]; exact ⟨even_two, by omega⟩) odd_one
  have hcop : Nat.Coprime (2 ^ m) (2 ^ n - 1) :=
    Nat.Coprime.pow_left m (Nat.coprime_two_left.mpr hodd)
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop hdvd1 hdvd2)

private theorem conjAddEnd_eq_id_of_isLin2Type {L U Z : Subgroup G} {F : Type*}
    [Field F] [Fintype F] {c : G} {n m : ℕ}
    (α : ↥L →* Matrix.SpecialLinearGroup (Fin 2) F) (hα : Function.Surjective α)
    (β : ↥U →* Multiplicative (Fin 2 → F)) (hβ : Function.Surjective β)
    (hβcomm : ∀ ℓ : ↥L, ∀ u v : ↥U, (v : G) = ℓ * u * ℓ⁻¹ →
      Multiplicative.toAdd (β v) = (α ℓ : Matrix (Fin 2) (Fin 2) F) *ᵥ
        Multiplicative.toAdd (β u))
    (hLU : L ≤ Subgroup.normalizer (U : Set G))
    (φ : ↥U ≃* ↥U) (hφ : ∀ x : ↥U, (φ x : G) = c * (x : G) * c⁻¹)
    (hcZ : c ∈ Subgroup.normalizer (Z : Set G))
    (hβker : β.ker = Z.subgroupOf U)
    (hconj : ∀ (l q : G), l ∈ L → q ∈ U →
      c * (l * q * l⁻¹) * c⁻¹ = l * (c * q * c⁻¹) * l⁻¹)
    (hcard : Fintype.card F = 2 ^ n) (hφpow : φ ^ (2 ^ m) = 1) :
    ∀ x : ↥U, β (φ x) = β x := by
  have hN := ker_le_comp_normalizerMonoidHom β hβker φ hφ hcZ
  obtain ⟨E, hE⟩ := exists_conjAddEnd β hβ φ hN
  have hE_comm := conjAddEnd_comm_SL2 α hα β hβ hβcomm hLU φ hφ hconj E hE
  obtain ⟨z, hz⟩ := exists_eq_smul_of_commute_SL2 E hE_comm
  have hfix := conjAddEnd_iterate_eq_self β hβ φ E hE hφpow
  have hzpow : z ^ (2 ^ m) = 1 := pow_eq_one_of_conjAddEnd hfix hz
  have hz0 : z ≠ 0 := by
    intro h0
    have hm0 : 2 ^ m ≠ 0 := pow_ne_zero m (by norm_num)
    rw [h0, zero_pow hm0] at hzpow
    exact zero_ne_one hzpow
  have hzpow2 : z ^ (2 ^ n - 1) = 1 := by
    have h := FiniteField.pow_card_sub_one_eq_one z hz0
    rwa [hcard] at h
  have hz1 : z = 1 := eq_one_of_pow_two_pow_eq_one_of_card hcard hzpow hzpow2
  have hE_id : ∀ v : Fin 2 → F, E v = v := by
    intro v
    rw [hz v, hz1, one_smul]
  intro x
  have h := hE x
  rw [hE_id] at h
  exact (Multiplicative.toAdd.injective h).symm

private theorem commutatorElement_mem_blockZ_of_conj_eq {U Z : Subgroup G} {F : Type*}
    [Field F] {c : G} (β : ↥U →* Multiplicative (Fin 2 → F))
    (hβker : β.ker = Z.subgroupOf U)
    (φ : ↥U ≃* ↥U) (hφ : ∀ x : ↥U, (φ x : G) = c * (x : G) * c⁻¹)
    (hβconj : ∀ x : ↥U, β (φ x) = β x) {q : G} (hq : q ∈ U) :
    ⁅c, q⁆ ∈ Z := by
  let x : ↥U := ⟨q, hq⟩
  have hβeq : β (φ x) = β x := hβconj x
  have hprod : β (φ x * x⁻¹) = 1 := by
    rw [map_mul, map_inv, hβeq, mul_inv_cancel]
  have hmem : φ x * x⁻¹ ∈ β.ker := hprod
  rw [hβker] at hmem
  have hZs : ((φ x * x⁻¹ : ↥U) : G) ∈ Z := by
    simpa [Subgroup.mem_subgroupOf] using hmem
  simpa [x, hφ, commutatorElement_def, mul_assoc] using hZs

private theorem commutatorElementHom_conj {Q Z L : Subgroup G} {c : G}
    (χ : ↥Q →* ↥Z) (hχ : ∀ q : ↥Q, ((χ q : ↥Z) : G) = ⁅c, (q : G)⁆)
    (hZle : Z ≤ Subgroup.centralizer (L : Set G))
    (hχZ : ∀ q ∈ Q, ⁅c, q⁆ ∈ Z)
    (hconj : ∀ (l q : G), l ∈ L → q ∈ Q →
      c * (l * q * l⁻¹) * c⁻¹ = l * (c * q * c⁻¹) * l⁻¹)
    (hLQ : L ≤ Subgroup.normalizer (Q : Set G)) :
    ∀ (l q : G) (hl : l ∈ L) (hq : q ∈ Q),
      χ (⟨l * q * l⁻¹,
        (Subgroup.mem_normalizer_iff.mp (hLQ hl) q).mp hq⟩ : ↥Q) = χ ⟨q, hq⟩ := by
  intro l q hl hq
  apply Subtype.ext
  rw [hχ, hχ]
  have hkey := hconj l q hl hq
  calc ⁅c, l * q * l⁻¹⁆
      = c * (l * q * l⁻¹) * c⁻¹ * (l * q * l⁻¹)⁻¹ := by rw [commutatorElement_def]
    _ = (l * (c * q * c⁻¹) * l⁻¹) * (l * q * l⁻¹)⁻¹ := by rw [hkey]
    _ = l * (c * q * c⁻¹ * q⁻¹) * l⁻¹ := by group
    _ = l * ⁅c, q⁆ * l⁻¹ := by rw [commutatorElement_def]
    _ = ⁅c, q⁆ := by
        have hcent : l * ⁅c, q⁆ = ⁅c, q⁆ * l :=
          Subgroup.mem_centralizer_iff.mp (hZle (hχZ q hq)) l hl
        rw [hcent]
        group

private theorem commutatorElementHom_eq_one_of_commutator {Q Z L : Subgroup G}
    (χ : ↥Q →* ↥Z) (hLQ : L ≤ Subgroup.normalizer (Q : Set G))
    (hQU : ⁅Q, L⁆ = Q)
    (hχconj : ∀ (l q : G) (hl : l ∈ L) (hq : q ∈ Q),
      χ (⟨l * q * l⁻¹,
        (Subgroup.mem_normalizer_iff.mp (hLQ hl) q).mp hq⟩ : ↥Q) = χ ⟨q, hq⟩) :
    ∀ (q : G) (hq : q ∈ Q), χ ⟨q, hq⟩ = 1 := by
  have hχcomm : ⁅L, Q⁆ ≤ (χ.ker).map Q.subtype := by
    rw [Subgroup.commutator_le]
    intro l hl q hq
    have hmemQ : ⁅l, q⁆ ∈ Q := by
      have hmem := Subgroup.commutator_mem_commutator hl hq
      rwa [Subgroup.commutator_comm, hQU] at hmem
    have hsplit : (⟨⁅l, q⁆, hmemQ⟩ : ↥Q) =
        (⟨l * q * l⁻¹,
          (Subgroup.mem_normalizer_iff.mp (hLQ hl) q).mp hq⟩ : ↥Q) * ⟨q, hq⟩⁻¹ := by
      apply Subtype.ext
      simp [commutatorElement_def, mul_assoc]
    refine Subgroup.mem_map.mpr ⟨⟨⁅l, q⁆, hmemQ⟩, ?_, rfl⟩
    rw [MonoidHom.mem_ker, hsplit, map_mul, map_inv, hχconj l q hl hq, mul_inv_cancel]
  have hQker : Q ≤ (χ.ker).map Q.subtype := by
    have hcommLQ : ⁅L, Q⁆ = Q := by
      rw [Subgroup.commutator_comm]
      exact hQU
    rw [hcommLQ] at hχcomm
    exact hχcomm
  intro q hq
  obtain ⟨y, hy, hyq⟩ := Subgroup.mem_map.mp (hQker hq)
  have hyq' : y = ⟨q, hq⟩ := Subtype.ext hyq
  rw [hyq'] at hy
  rw [MonoidHom.mem_ker] at hy
  exact hy

private theorem commutatorElement_eq_one_of_conjAddEnd {L Q U Z : Subgroup G} {F : Type*}
    [Field F] {c : G} (β : ↥U →* Multiplicative (Fin 2 → F))
    (hβker : β.ker = Z.subgroupOf U)
    (φ : ↥U ≃* ↥U) (hφ : ∀ x : ↥U, (φ x : G) = c * (x : G) * c⁻¹)
    (hβconj : ∀ x : ↥U, β (φ x) = β x)
    (hZle : Z ≤ Subgroup.centralizer (L : Set G))
    (hQleL : Q ≤ L) (hUQ : U = Q)
    (hconj : ∀ (l q : G), l ∈ L → q ∈ U →
      c * (l * q * l⁻¹) * c⁻¹ = l * (c * q * c⁻¹) * l⁻¹)
    (hLQ : L ≤ Subgroup.normalizer (Q : Set G)) (hQU : ⁅Q, L⁆ = Q) :
    ∀ q ∈ Q, ⁅c, q⁆ = 1 := by
  have hZcent : Z ≤ Subgroup.centralizer (Q : Set G) :=
    hZle.trans (Subgroup.centralizer_le hQleL)
  have hχZ : ∀ q ∈ Q, ⁅c, q⁆ ∈ Z := by
    intro q hq
    exact commutatorElement_mem_blockZ_of_conj_eq β hβker φ hφ hβconj (hUQ.symm ▸ hq)
  let χ : ↥Q →* ↥Z :=
    CFSG.LocalAnalysis.EvenBN.Common.commutatorElementHom c hZcent hχZ
  have hχ_apply : ∀ q : ↥Q, ((χ q : ↥Z) : G) = ⁅c, (q : G)⁆ :=
    fun q => CFSG.LocalAnalysis.EvenBN.Common.commutatorElementHom_apply c hZcent hχZ q
  have hconjQ : ∀ (l q : G), l ∈ L → q ∈ Q →
      c * (l * q * l⁻¹) * c⁻¹ = l * (c * q * c⁻¹) * l⁻¹ := by
    intro l q hl hq
    exact hconj l q hl (hUQ.symm ▸ hq)
  have hχconj := commutatorElementHom_conj χ hχ_apply hZle hχZ hconjQ hLQ
  have hχtriv := commutatorElementHom_eq_one_of_commutator χ hLQ hQU hχconj
  intro q hq
  have h := congrArg Subtype.val (hχtriv q hq)
  simpa [hχ_apply] using h

private theorem map_ne_one_of_odd_orderOf {L H : Type*} [Group L] [Finite L] [Group H]
    (α : L →* H) (hker : α.ker = CFSG.pCore 2 L) {k : L}
    (hk : Odd (orderOf k)) (hk1 : k ≠ 1) : α k ≠ 1 := by
  intro hαk
  have hkP : k ∈ CFSG.pCore 2 L := by
    rw [← hker]
    exact hαk
  let P : Subgroup L := CFSG.pCore 2 L
  let x : ↥P := ⟨k, hkP⟩
  obtain ⟨j, hj⟩ := (IsPGroup.iff_orderOf.mp (CFSG.pCore_isPGroup (p := 2) (G := L))) x
  have hxodd : Odd (orderOf x) := by
    rw [← Subgroup.orderOf_coe x]
    exact hk
  have hj0 : j = 0 := by
    by_contra hne
    rw [hj] at hxodd
    have heven : Even (2 ^ j) := by
      rw [Nat.even_pow]
      exact ⟨even_two, hne⟩
    exact (Nat.not_even_iff_odd.mpr hxodd) heven
  have hx1 : x = 1 := orderOf_eq_one_iff.mp (by rw [hj, hj0, pow_zero])
  have hx1L : (x : L) = 1 := congrArg (fun y : ↥P => (y : L)) hx1
  exact hk1 (by simpa [x] using hx1L)

theorem centralizes_pCoreOf_of_isLin2Type {L : Subgroup G} [Finite ↥L] {n : ℕ}
    (hL : IsLin2Type L n) (hab : IsMulCommutative ↥(pCoreOf 2 L))
    (hU : ⁅pCoreOf 2 L, L⁆ = pCoreOf 2 L) {c : G} (hc2 : ∃ m, c ^ (2 ^ m) = 1)
    (hcL : c ∈ Subgroup.normalizer (L : Set G)) (hcLQ : ∀ l ∈ L, ⁅c, l⁆ ∈ pCoreOf 2 L) :
    ∀ q ∈ pCoreOf 2 L, ⁅c, q⁆ = 1 := by
  classical
  obtain ⟨m, hm⟩ := hc2
  obtain ⟨F, hField, hFintype, hcard, α, hαsurj, hαker, β, hβsurj, hβker, hβcomm⟩ := hL
  letI : Field F := hField
  letI : Fintype F := hFintype
  let Q : Subgroup G := pCoreOf 2 L
  let U : Subgroup G := blockU L
  let Z : Subgroup G := blockZ L
  have hQleL : Q ≤ L := CFSG.LieType.BorelTits.pCoreOf_le 2 L
  have hUQ : U = Q := by simpa [U, Q, blockU, blockQ] using hU
  have hQU : ⁅Q, L⁆ = Q := by simpa [Q] using hU
  haveI : IsMulCommutative ↥Q := hab
  have hcQ : c ∈ Subgroup.normalizer (Q : Set G) :=
    CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L hcL
  have hcU : c ∈ Subgroup.normalizer (U : Set G) := by rw [hUQ]; exact hcQ
  have hLU : L ≤ Subgroup.normalizer (U : Set G) := by
    rw [hUQ]
    exact CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L
  have hLQ : L ≤ Subgroup.normalizer (Q : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L
  have hcZ : c ∈ Subgroup.normalizer (Z : Set G) := by
    have h := CFSG.GroupTheory.mem_normalizer_inf_centralizer (L := L) (Q := U) hcL hcU
    simpa [Z, U, blockZ] using h
  let cN : Subgroup.normalizer (U : Set G) := ⟨c, hcU⟩
  let φ : ↥U ≃* ↥U := Subgroup.normalizerMonoidHom U cN
  have hφ_coe : ∀ x : ↥U, ((φ x : ↥U) : G) = c * (x : G) * c⁻¹ :=
    fun x => Subgroup.normalizerMonoidHom_apply_apply_coe U cN x
  have hconj : ∀ (l q : G), l ∈ L → q ∈ U →
      c * (l * q * l⁻¹) * c⁻¹ = l * (c * q * c⁻¹) * l⁻¹ := by
    intro l q hl hq
    have hqQ : q ∈ Q := by rwa [hUQ] at hq
    exact conj_mul_conj_eq_of_mem hab hcQ hl hLQ (hcLQ l hl) hqQ
  have hφpow : φ ^ (2 ^ m) = 1 := by
    have hcNpow : cN ^ (2 ^ m) = 1 := by
      apply Subtype.ext
      simpa using hm
    show Subgroup.normalizerMonoidHom U cN ^ (2 ^ m) = 1
    rw [← map_pow, hcNpow, map_one]
  have hβconj : ∀ x : ↥U, β (φ x) = β x :=
    conjAddEnd_eq_id_of_isLin2Type α hαsurj β hβsurj hβcomm hLU φ hφ_coe hcZ hβker
      hconj hcard hφpow
  have hZle : Z ≤ Subgroup.centralizer (L : Set G) := by
    simpa [Z, U, blockZ] using (inf_le_right : U ⊓ Subgroup.centralizer (L : Set G) ≤
      Subgroup.centralizer (L : Set G))
  exact commutatorElement_eq_one_of_conjAddEnd β hβker φ hφ_coe hβconj hZle hQleL hUQ
    hconj hLQ hQU

theorem mem_blockZ_of_mul_comm_of_odd {L : Subgroup G} [Finite ↥L] {n : ℕ}
    (hL : IsLin2Type L n) {k : G} (hkL : k ∈ L) (hk : Odd (orderOf k)) (hk1 : k ≠ 1)
    {u : G} (hu : u ∈ blockU L) (hku : k * u = u * k) : u ∈ blockZ L := by
  classical
  obtain ⟨F, hField, hFintype, hcard, α, hαsurj, hαker, β, hβsurj, hβker, hβcomm⟩ := hL
  letI : Field F := hField
  letI : Fintype F := hFintype
  have hcardNat : Nat.card F = 2 ^ n := by
    rwa [Nat.card_eq_fintype_card]
  have hn1 : 1 ≤ n := by
    have h2 : 1 < Fintype.card F := Fintype.one_lt_card
    rw [hcard] at h2
    by_contra hn
    have hn0 : n = 0 := by omega
    rw [hn0, pow_zero] at h2
    exact lt_irrefl 1 h2
  letI : CharP F 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
      Nat.prime_two hn1 hcardNat
  have hk' : Odd (orderOf (⟨k, hkL⟩ : ↥L)) := by
    rw [← Subgroup.orderOf_coe (⟨k, hkL⟩ : ↥L)]
    exact hk
  have hαk : α ⟨k, hkL⟩ ≠ 1 :=
    map_ne_one_of_odd_orderOf α hαker hk' (by
      intro h
      exact hk1 (by simpa using congrArg Subtype.val h))
  have hku' : k * u * k⁻¹ = u := by
    rw [hku]
    group
  let U : Subgroup G := blockU L
  let v : ↥U := ⟨u, hu⟩
  let w : ↥U := ⟨k * u * k⁻¹, by rw [hku']; exact hu⟩
  have hwv : w = v := Subtype.ext hku'
  have hβfix : (α ⟨k, hkL⟩ : Matrix (Fin 2) (Fin 2) F) *ᵥ Multiplicative.toAdd (β v) =
      Multiplicative.toAdd (β v) := by
    have h := hβcomm ⟨k, hkL⟩ v w rfl
    rw [hwv] at h
    exact h.symm
  have hoddα : Odd (orderOf (α ⟨k, hkL⟩)) := by
    have hdvd := orderOf_map_dvd α (⟨k, hkL⟩ : ↥L)
    rw [← Subgroup.orderOf_coe (⟨k, hkL⟩ : ↥L)] at hdvd
    exact Odd.of_dvd_nat hk hdvd
  have hv0 : Multiplicative.toAdd (β v) = 0 :=
    CFSG.CGT.PushingUpLit.CGT6.eq_zero_of_fixed_vec_of_odd_order hoddα hαk hβfix
  have hβv1 : β v = 1 := by simpa using hv0
  have hvker : v ∈ β.ker := hβv1
  rw [hβker] at hvker
  simpa [v, U, Subgroup.mem_subgroupOf] using hvker

end CFSG.Quasithin.F112R.St84
