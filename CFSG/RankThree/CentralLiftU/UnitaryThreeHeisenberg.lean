module

public import CFSG.LieType.Steinberg.CentralExt.SUThreeOrder
public import CFSG.LieType.Steinberg.CentralExt.SUThree
public import CFSG.RankThree.PerfectCover.HeisenbergDilation
public import CFSG.RankThree.CentralLiftU.PerfectSplit
import Mathlib.Tactic.LinearCombination
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LieType.Steinberg.CentralExt.PerfectLift

public section

namespace CFSG.RankThree.CentralLiftU

open Matrix CFSG.LieType.Steinberg CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits
open CFSG.LieType.Universal.Unitary.SUExtras (mat mat_apply mat_injective)
open scoped commutatorElement

variable {K : Type} [Field K] [Finite K] {ℓ f : ℕ} [Fact ℓ.Prime] [CharP K ℓ]

local notation "σ₀" => unitaryInvolution K ℓ f

section Heisenberg

variable (hK : Nat.card K = (ℓ ^ f) ^ 2)

noncomputable abbrev heisX : Subgroup (SU (unitaryInvolution K ℓ f) 3) :=
  rootGroup (unitaryInvolution K ℓ f) (unitaryInvolution_involutive hK) 3 (Pi.single 0 1)

@[expose] def heisM (σ : K ≃+* K) (a b : K) : Matrix (Fin 3) (Fin 3) K :=
  !![1, a, b; 0, 1, -σ a; 0, 0, 1]

omit [Finite K] in
theorem heisM_mul (σ : K ≃+* K) (a b a' b' : K) :
    heisM σ a b * heisM σ a' b' = heisM σ (a + a') (b + b' - a * σ a') := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [heisM, Matrix.mul_apply, Fin.sum_univ_three] <;> ring

include hK in
theorem mat_heisX (x : heisX hK) :
    mat σ₀ 3 (x : SU σ₀ 3) =
        heisM σ₀ (mat σ₀ 3 (x : SU σ₀ 3) 0 1) (mat σ₀ 3 (x : SU σ₀ 3) 0 2) ∧
      mat σ₀ 3 (x : SU σ₀ 3) 0 2 + σ₀ (mat σ₀ 3 (x : SU σ₀ 3) 0 2) +
        σ₀ (mat σ₀ 3 (x : SU σ₀ 3) 0 1) * mat σ₀ 3 (x : SU σ₀ 3) 0 1 = 0 := by
  obtain ⟨a, b, hab, hm⟩ := (mem_rootGroup_three (unitaryInvolution_involutive hK)).1 x.2
  have ha : mat σ₀ 3 (x : SU σ₀ 3) 0 1 = a := by rw [hm]; simp
  have hb : mat σ₀ 3 (x : SU σ₀ 3) 0 2 = b := by rw [hm]; simp
  rw [ha, hb]
  exact ⟨hm, hab⟩

include hK in
theorem heisM_isometry {a b : K} (hab : b + σ₀ b + σ₀ a * a = 0) :
    conjTr σ₀ (heisM σ₀ a b) * antidiag 3 * heisM σ₀ a b = antidiag 3 := by
  have h := heisenbergMatrix_isometry σ₀ (unitaryInvolution_involutive hK) (i := (0 : Fin 3))
    (k := 1) (by decide) (by decide) (by decide) hab
  rwa [heisenbergMatrix_three] at h

omit [Finite K] in
theorem det_heisM (σ : K ≃+* K) (a b : K) : (heisM σ a b).det = 1 := by
  simp [heisM, Matrix.det_fin_three]

@[expose] noncomputable def mkHeis {a b : K} (hab : b + σ₀ b + σ₀ a * a = 0) : heisX hK :=
  ⟨⟨Matrix.GeneralLinearGroup.mkOfDetNeZero (heisM σ₀ a b)
      (by rw [det_heisM]; exact one_ne_zero),
    by rw [Matrix.GeneralLinearGroup.val_mkOfDetNeZero, det_heisM],
    by rw [Matrix.GeneralLinearGroup.val_mkOfDetNeZero]; exact heisM_isometry hK hab⟩,
    (mem_rootGroup_three (unitaryInvolution_involutive hK)).2 ⟨a, b, hab, rfl⟩⟩

theorem mat_mkHeis {a b : K} (hab : b + σ₀ b + σ₀ a * a = 0) :
    mat σ₀ 3 ((mkHeis hK hab : heisX hK) : SU σ₀ 3) = heisM σ₀ a b :=
  rfl

@[expose] noncomputable def heisTheta : heisX hK →* Multiplicative K where
  toFun x := Multiplicative.ofAdd (mat σ₀ 3 (x : SU σ₀ 3) 0 1)
  map_one' := by simp [mat_apply]
  map_mul' x y := by
    rw [← ofAdd_add]
    congr 1
    rw [Subgroup.coe_mul, map_mul, (mat_heisX hK x).1, (mat_heisX hK y).1, heisM_mul]
    simp [heisM]

theorem heisTheta_apply (x : heisX hK) :
    heisTheta hK x = Multiplicative.ofAdd (mat σ₀ 3 (x : SU σ₀ 3) 0 1) :=
  rfl

theorem mem_center_of_heisTheta {x : heisX hK} (hx : heisTheta hK x = 1) :
    x ∈ Subgroup.center (heisX hK) := by
  have ha : mat σ₀ 3 (x : SU σ₀ 3) 0 1 = 0 := by
    rw [heisTheta_apply] at hx
    exact toAdd_eq_zero.mpr hx
  rw [Subgroup.mem_center_iff]
  intro y
  apply Subtype.ext
  apply mat_injective
  rw [Subgroup.coe_mul, Subgroup.coe_mul, map_mul, map_mul, (mat_heisX hK x).1,
    (mat_heisX hK y).1, heisM_mul, heisM_mul, ha, map_zero]
  congr 1 <;> ring

theorem bar_two_inv : σ₀ (2 : K)⁻¹ = (2 : K)⁻¹ := by
  rw [map_inv₀, map_ofNat]

theorem mem_commutator_of_heisTheta (hℓ2 : ℓ ≠ 2) {x : heisX hK} (hx : heisTheta hK x = 1) :
    x ∈ commutator (heisX hK) := by
  have hσ := unitaryInvolution_involutive hK
  have h2 : (2 : K) ≠ 0 := by
    intro h0
    have := (CharP.cast_eq_zero_iff K ℓ 2).1 (by exact_mod_cast h0)
    exact hℓ2 ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).1 this)
  have ha : mat σ₀ 3 (x : SU σ₀ 3) 0 1 = 0 := by
    rw [heisTheta_apply] at hx
    exact toAdd_eq_zero.mpr hx
  set c := mat σ₀ 3 (x : SU σ₀ 3) 0 2 with hc
  have hc0 : c + σ₀ c = 0 := by
    have := (mat_heisX hK x).2
    rw [ha, map_zero, zero_mul, add_zero] at this
    exact this
  have hσc : σ₀ c = -c := by linear_combination hc0
  have h2' : σ₀ (2 : K)⁻¹ = (2 : K)⁻¹ := bar_two_inv
  have hu : -(2 : K)⁻¹ + σ₀ (-(2 : K)⁻¹) + σ₀ 1 * 1 = 0 := by
    rw [map_neg, h2', map_one]
    field_simp
    ring
  set n₀ := σ₀ (c * (2 : K)⁻¹) * (c * (2 : K)⁻¹) with hn₀
  have hv : -(n₀ * (2 : K)⁻¹) + σ₀ (-(n₀ * (2 : K)⁻¹)) + σ₀ (c * (2 : K)⁻¹) * (c * (2 : K)⁻¹) =
      0 := by
    have hσn : σ₀ n₀ = n₀ := by
      rw [hn₀, map_mul, hσ, mul_comm]
    rw [map_neg, map_mul, hσn, h2', ← hn₀]
    field_simp
    ring
  set u := mkHeis hK hu
  set v := mkHeis hK hv
  have hkey : u * v = x * (v * u) := by
    apply Subtype.ext
    apply mat_injective
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_mul, map_mul, map_mul, map_mul,
      mat_mkHeis, mat_mkHeis, (mat_heisX hK x).1, heisM_mul, heisM_mul, heisM_mul, ha, ← hc]
    have hσ1 : σ₀ (1 : K) = 1 := map_one _
    have hσc2 : σ₀ (c * (2 : K)⁻¹) = -(c * (2 : K)⁻¹) := by rw [map_mul, hσc, h2', neg_mul]
    have h22 : (2 : K) * (2 : K)⁻¹ = 1 := mul_inv_cancel₀ h2
    rw [hσ1, hσc2]
    congr 1 <;> first | ring1 | linear_combination c * h22
  have hx' : x = ⁅u, v⁆ := by
    rw [commutatorElement_def, hkey]
    group
  rw [hx']
  exact Subgroup.commutator_mem_commutator (Subgroup.mem_top u) (Subgroup.mem_top v)

theorem heisX_lowerCentralSeries_two :
    (⊤ : Subgroup (heisX hK)).lowerCentralSeries 2 = ⊥ := by
  have hcomm : commutator (heisX hK) ≤ Subgroup.center (heisX hK) := by
    intro x hx
    exact mem_center_of_heisTheta hK (Abelianization.commutator_subset_ker (heisTheta hK) hx)
  rw [Subgroup.lowerCentralSeries_succ, Subgroup.lowerCentralSeries_succ,
    Subgroup.lowerCentralSeries_zero, eq_bot_iff, Subgroup.commutator_le]
  intro g hg h _
  have hgc : g ∈ Subgroup.center (heisX hK) := hcomm (by rwa [commutator_def])
  rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
  exact (Subgroup.mem_center_iff.1 hgc h).symm

theorem isElementaryAbelian_heisX (hℓ2 : ℓ ≠ 2) :
    CFSG.IsElementaryAbelian ℓ (heisX hK ⧸ commutator (heisX hK)) where
  is_comm := ⟨fun a b => by
    induction a using QuotientGroup.induction_on with
    | H x =>
      induction b using QuotientGroup.induction_on with
      | H y =>
        rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
        have : (x * y)⁻¹ * (y * x) = ⁅y⁻¹, x⁻¹⁆ := by
          rw [commutatorElement_def]
          group
        rw [this]
        exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)⟩
  exponent_dvd_p := by
    refine Monoid.exponent_dvd_of_forall_pow_eq_one fun z => ?_
    induction z using QuotientGroup.induction_on with
    | H x =>
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
      refine mem_commutator_of_heisTheta hK hℓ2 ?_
      rw [map_pow, heisTheta_apply, ← ofAdd_nsmul, nsmul_eq_mul, CharP.cast_eq_zero, zero_mul,
        ofAdd_zero]

end Heisenberg

section Dilation

variable (hK : Nat.card K = (ℓ ^ f) ^ 2)

@[expose] noncomputable def dilMat (t : K) : Matrix (Fin 3) (Fin 3) K := diagonal ![t, 1, t⁻¹]

omit [Finite K] in
theorem dilMat_mul_inv {t : K} (ht : t ≠ 0) : dilMat t * dilMat t⁻¹ = 1 := by
  rw [dilMat, dilMat, diagonal_mul_diagonal, ← diagonal_one]
  congr 1
  funext i
  fin_cases i <;> simp [ht]

omit [Finite K] in
theorem dilMat_inv_mul {t : K} (ht : t ≠ 0) : dilMat t⁻¹ * dilMat t = 1 := by
  rw [dilMat, dilMat, diagonal_mul_diagonal, ← diagonal_one]
  congr 1
  funext i
  fin_cases i <;> simp [ht]

@[expose] noncomputable def dilElt {t : K} (ht : t ≠ 0) (hσt : σ₀ t = t) : SU σ₀ 3 :=
  ⟨⟨dilMat t, dilMat t⁻¹, dilMat_mul_inv ht, dilMat_inv_mul ht⟩,
    by
      change (dilMat t).det = 1
      simp [dilMat, det_diagonal, Fin.prod_univ_three, ht],
    by
      change conjTr σ₀ (dilMat t) * antidiag 3 * dilMat t = antidiag 3
      rw [dilMat, conjTr_diagonal σ₀]
      have e : (fun i => σ₀ (![t, 1, t⁻¹] i)) = ![t, 1, t⁻¹] := by
        funext i
        fin_cases i
        · exact hσt
        · exact map_one _
        · change σ₀ t⁻¹ = t⁻¹
          rw [map_inv₀, hσt]
      rw [e]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [antidiag, Matrix.mul_apply, Fin.sum_univ_three, ht]⟩

theorem mat_dilElt {t : K} (ht : t ≠ 0) (hσt : σ₀ t = t) :
    mat σ₀ 3 (dilElt ht hσt) = dilMat t :=
  rfl

theorem mat_dilElt_inv {t : K} (ht : t ≠ 0) (hσt : σ₀ t = t) :
    mat σ₀ 3 (dilElt ht hσt)⁻¹ = dilMat t⁻¹ :=
  rfl

theorem dilMat_conj_heisM {t : K} (ht : t ≠ 0) (hσt : σ₀ t = t) (a b : K) :
    dilMat t * heisM σ₀ a b * dilMat t⁻¹ = heisM σ₀ (t * a) (t ^ 2 * b) := by
  have e : σ₀ (t * a) = t * σ₀ a := by rw [map_mul, hσt]
  rw [heisM, heisM, e]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [dilMat, Matrix.mul_apply, Fin.sum_univ_three, ht] <;> ring

theorem conj_dilElt_mem {t : K} (ht : t ≠ 0) (hσt : σ₀ t = t) {x : SU σ₀ 3}
    (hx : x ∈ heisX hK) :
    dilElt ht hσt * x * (dilElt ht hσt)⁻¹ ∈ heisX hK ∧
      mat σ₀ 3 (dilElt ht hσt * x * (dilElt ht hσt)⁻¹) 0 1 = t * mat σ₀ 3 x 0 1 := by
  obtain ⟨hm, hab⟩ := mat_heisX hK ⟨x, hx⟩
  set a := mat σ₀ 3 x 0 1
  set b := mat σ₀ 3 x 0 2
  have hmat : mat σ₀ 3 (dilElt ht hσt * x * (dilElt ht hσt)⁻¹) =
      heisM σ₀ (t * a) (t ^ 2 * b) := by
    rw [map_mul, map_mul, mat_dilElt, mat_dilElt_inv]
    change dilMat t * mat σ₀ 3 x * dilMat t⁻¹ = _
    rw [hm, dilMat_conj_heisM ht hσt]
  have hab' : t ^ 2 * b + σ₀ (t ^ 2 * b) + σ₀ (t * a) * (t * a) = 0 := by
    rw [map_mul, map_mul, map_pow, hσt]
    linear_combination t ^ 2 * hab
  refine ⟨?_, by rw [hmat]; simp [heisM]⟩
  exact (mem_rootGroup_three (unitaryInvolution_involutive hK)).2 ⟨t * a, t ^ 2 * b, hab', hmat⟩

end Dilation

section Main

variable (hK : Nat.card K = (ℓ ^ f) ^ 2)

theorem isPGroup_heisX : IsPGroup ℓ (heisX hK) :=
  IsPGroup.of_card (n := f * 3) (by rw [card_rootGroup_three hK, pow_mul])

theorem not_dvd_index_heisX : ¬ ℓ ∣ (heisX hK).index := by
  have hq : 1 < ℓ ^ f := CFSG.ClassicalGroups.Unitary.one_lt_pow_of_card hK
  set q := ℓ ^ f with hqdef
  have hf : f ≠ 0 := by
    rintro rfl
    simp [hqdef] at hq
  have h := Subgroup.card_mul_index (heisX hK)
  rw [card_rootGroup_three hK, card_SU_three hK] at h
  have hidx : (heisX hK).index = (q ^ 2 - 1) * (q ^ 3 + 1) := by
    have hpos : 0 < q ^ 3 := by positivity
    rw [mul_assoc] at h
    exact Nat.eq_of_mul_eq_mul_left hpos h
  rw [hidx]
  intro hdvd
  have hℓq : ℓ ∣ q := dvd_pow_self ℓ hf
  rcases (Nat.Prime.dvd_mul Fact.out).1 hdvd with h1 | h1
  · have h2 : ℓ ∣ q ^ 2 := hℓq.trans (dvd_pow_self q two_ne_zero)
    have h3 : ℓ ∣ q ^ 2 - (q ^ 2 - 1) := Nat.dvd_sub h2 h1
    rw [Nat.sub_sub_self (Nat.one_le_pow _ _ (by omega))] at h3
    exact (Nat.Prime.one_lt Fact.out).ne' (Nat.dvd_one.1 h3)
  · have h2 : ℓ ∣ q ^ 3 := hℓq.trans (dvd_pow_self q three_ne_zero)
    have h3 : ℓ ∣ q ^ 3 + 1 - q ^ 3 := Nat.dvd_sub h1 h2
    rw [Nat.add_sub_cancel_left] at h3
    exact (Nat.Prime.one_lt Fact.out).ne' (Nat.dvd_one.1 h3)

theorem exists_unit_sq_ne_one_cube_ne_one (hℓ3 : 3 < ℓ) :
    ∃ t : (ZMod ℓ)ˣ, t ^ 2 ≠ 1 ∧ t ^ 3 ≠ 1 := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (ZMod ℓ)ˣ)
  have hord : orderOf g = ℓ - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_eq_fintype_card, ZMod.card_units]
  refine ⟨g, fun h2 => ?_, fun h3 => ?_⟩
  · have := Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one h2)
    rw [hord] at this
    omega
  · have := Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one h3)
    rw [hord] at this
    have h4 : ℓ ≠ 4 := by
      intro h
      have hp : ℓ.Prime := Fact.out
      rw [h] at hp
      exact absurd hp (by decide)
    omega

include hK in
theorem ker_eq_bot_SU_three_of_eq_char (hℓ3 : 3 < ℓ) {R : Type*} [Group R] [Finite R]
    [Group.IsPerfect R] (ρ : R →* SU σ₀ 3) (hρ : Function.Surjective ρ)
    (hcen : ρ.ker ≤ Subgroup.center R) (hpk : IsPGroup ℓ ρ.ker) : ρ.ker = ⊥ := by
  have hℓ2 : ℓ ≠ 2 := by omega
  set X := heisX hK
  let XS : Sylow ℓ (SU σ₀ 3) := (isPGroup_heisX hK).toSylow (not_dvd_index_heisX hK)
  let P : Sylow ℓ R := XS.comapOfKerIsPGroup ρ hpk (by
    rw [MonoidHom.range_eq_top.2 hρ]
    exact le_top)
  have hPmem : ∀ y : R, y ∈ (P : Subgroup R) ↔ ρ y ∈ X := fun y => Iff.rfl
  let π' : (P : Subgroup R) →* X :=
    (ρ.comp (P : Subgroup R).subtype).codRestrict X fun y => (hPmem y).1 y.2
  have hπ'apply : ∀ y : (P : Subgroup R), ((π' y : X) : SU σ₀ 3) = ρ y := fun _ => rfl
  have hπ' : Function.Surjective π' := by
    rintro ⟨x, hx⟩
    obtain ⟨y, rfl⟩ := hρ x
    exact ⟨⟨y, (hPmem y).2 hx⟩, rfl⟩
  have hπ'ker : π'.ker = ρ.ker.subgroupOf (P : Subgroup R) := by
    ext y
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, MonoidHom.mem_ker]
    constructor
    · intro h
      have := congrArg Subtype.val h
      exact this
    · intro h
      exact Subtype.ext h
  obtain ⟨t, ht2, ht3⟩ := exists_unit_sq_ne_one_cube_ne_one hℓ3
  set k := (t : ZMod ℓ).val with hk
  set tK : K := (k : K) with htK
  have htK0 : tK ≠ 0 := by
    intro h0
    rw [htK, CharP.cast_eq_zero_iff K ℓ] at h0
    have hlt : k < ℓ := ZMod.val_lt _
    have hk0 : k ≠ 0 := by
      rw [hk, ZMod.val_ne_zero]
      exact t.ne_zero
    have := Nat.le_of_dvd (Nat.pos_of_ne_zero hk0) h0
    omega
  have hσt : σ₀ tK = tK := by rw [htK, map_natCast]
  set D := dilElt htK0 hσt
  obtain ⟨a, ha⟩ := hρ D
  have hDinv : (dilElt htK0 hσt)⁻¹ = dilElt (inv_ne_zero htK0) (by rw [map_inv₀, hσt]) := by
    apply Subtype.ext
    apply Units.ext
    rfl
  have hnorm : a ∈ Subgroup.normalizer ((P : Subgroup R) : Set R) := by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    rw [hPmem, hPmem, map_mul, map_mul, map_inv, ha]
    constructor
    · intro hy
      exact (conj_dilElt_mem hK htK0 hσt hy).1
    · intro hy
      have h := (conj_dilElt_mem hK (inv_ne_zero htK0) (by rw [map_inv₀, hσt]) hy).1
      rw [← hDinv, inv_inv] at h
      have e : D⁻¹ * (D * ρ y * D⁻¹) * D = ρ y := by group
      rwa [e] at h
  have hact : ∀ x y : (P : Subgroup R), (y : R) = a * x * a⁻¹ →
      (QuotientGroup.mk (π' y) : X ⧸ commutator X) =
        (QuotientGroup.mk (π' x) : X ⧸ commutator X) ^ (t : ZMod ℓ).val := by
    intro x y hxy
    have hy : ((π' y : X) : SU σ₀ 3) = D * (π' x : SU σ₀ 3) * D⁻¹ := by
      rw [hπ'apply, hπ'apply, hxy, map_mul, map_mul, map_inv, ha]
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq]
    refine mem_commutator_of_heisTheta hK hℓ2 ?_
    rw [map_mul, map_inv, map_pow, heisTheta_apply, heisTheta_apply, hy,
      (conj_dilElt_mem hK htK0 hσt (π' x).2).2, ← ofAdd_nsmul, ← ofAdd_neg, ← ofAdd_add,
      nsmul_eq_mul, ← htK, neg_add_cancel, ofAdd_zero]
  exact CFSG.RankThree.PerfectCover.perfect_central_prime_kernel_heisenberg_dilation_trivial'
    hℓ3 ρ.ker hcen hpk P π' hπ' hπ'ker (heisX_lowerCentralSeries_two hK)
    (isElementaryAbelian_heisX hK hℓ2) a hnorm t ht2 ht3 hact

end Main

end CFSG.RankThree.CentralLiftU
