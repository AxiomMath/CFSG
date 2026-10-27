module

public import CFSG.Quasithin.Vol2.Ch12Sec6KGCompU3D
import CFSG.Quasithin.Background.Harris.OrdinaryProofs.CoverSU3
import CFSG.CharacterTheory.Burnside
import CFSG.LocalAnalysis.ComponentInitial.QuasisimpleRankOne
public import CFSG.LieType.Universal.Unitary.Clause0

public section

namespace CFSG.Quasithin.H13.S126C

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.Assembly.LowTwoRank

theorem eq_one_of_inv_mul_mem_center {M : Type} [Group M] (hperf : Group.IsPerfect M)
    {ν : MulAut M} (hν : ∀ x, (ν x)⁻¹ * x ∈ Subgroup.center M) : ν = 1 := by
  have hc : ∀ x, x * (ν x)⁻¹ ∈ Subgroup.center M := fun x => by
    have h1 := hν x
    have h2 : x * (ν x)⁻¹ = x * ((ν x)⁻¹ * x) * x⁻¹ := by group
    rw [h2, Subgroup.mem_center_iff.mp h1 x, mul_assoc, mul_inv_cancel, mul_one]
    exact h1
  let φ : M →* Subgroup.center M :=
    { toFun := fun x => ⟨x * (ν x)⁻¹, hc x⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun x y => Subtype.ext (by
        change x * y * (ν (x * y))⁻¹ = x * (ν x)⁻¹ * (y * (ν y)⁻¹)
        have hy := Subgroup.mem_center_iff.mp (hc y) (ν x)⁻¹
        rw [map_mul, _root_.mul_inv_rev]
        calc x * y * ((ν y)⁻¹ * (ν x)⁻¹) = x * (y * (ν y)⁻¹ * (ν x)⁻¹) := by group
          _ = x * ((ν x)⁻¹ * (y * (ν y)⁻¹)) := by rw [hy]
          _ = x * (ν x)⁻¹ * (y * (ν y)⁻¹) := by group) }
  have hker : commutator M ≤ φ.ker := Abelianization.commutator_subset_ker φ
  rw [hperf.commutator_eq_top] at hker
  refine MulEquiv.ext fun x => ?_
  have h1 : φ x = 1 := hker (Subgroup.mem_top x)
  have h2 : x * (ν x)⁻¹ = 1 := congrArg Subtype.val h1
  rw [MulAut.one_apply]
  exact (mul_inv_eq_one.mp h2).symm

theorem exists_su3_inv_of_involution {p : ℕ} {F : Type} [Field F] (hUF : UnitaryFieldData p 1 F)
    (hp2 : p ≠ 2) (hp3 : p ≠ 3) {ν : MulAut ↥(StatedSU 3 (p ^ 1) F)} (hν2 : ν ^ 2 = 1)
    (hν1 : ν ≠ 1) : ∃ x : ↥(StatedSU 3 (p ^ 1) F), orderOf x = p ∧ ν x = x⁻¹ := by
  classical
  have : Fact p.Prime := ⟨hUF.prime⟩
  have : Finite F := hUF.finite
  have hq : Nat.card F = (p ^ 1) ^ 2 := by rw [hUF.card, pow_one]
  have hnq : ((3 : ℕ), p ^ 1) ≠ (3, 2) := by
    rw [pow_one]
    intro h0
    exact hp2 (Prod.mk.inj h0).2
  obtain ⟨-, hZ⟩ := CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card hq le_rfl hnq
  have hperf := CFSG.ClassicalGroups.Unitary.isPerfect_statedSU hq le_rfl hnq
  set M := ↥(StatedSU 3 (p ^ 1) F)
  set Z := Subgroup.center M with hZdef
  have hνZ : Z.map ν.toMonoidHom = Z := by
    apply le_antisymm
    · rintro _ ⟨z, hz, rfl⟩
      refine Subgroup.mem_center_iff.mpr fun g => ?_
      obtain ⟨g', rfl⟩ := ν.surjective g
      change ν g' * ν z = ν z * ν g'
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hz g']
    · intro z hz
      refine ⟨ν.symm z, Subgroup.mem_center_iff.mpr fun g => ?_, ν.apply_symm_apply z⟩
      apply ν.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply, Subgroup.mem_center_iff.mp hz (ν g)]
  set νb := QuotientGroup.congr Z Z ν hνZ with hνb
  have hνbmk : ∀ x : M, νb (QuotientGroup.mk x) = QuotientGroup.mk (ν x) := fun x =>
    QuotientGroup.congr_mk _ _ _ hνZ x
  have hνν : ∀ x : M, ν (ν x) = x := fun x => by
    have := DFunLike.congr_fun hν2 x
    rwa [pow_two] at this
  have hνb2 : νb ^ 2 = 1 := by
    refine MulEquiv.ext fun y => ?_
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
    rw [pow_two, MulAut.mul_apply, hνbmk, hνbmk, hνν]
    rfl
  have hνb1 : νb ≠ 1 := fun h1 => hν1 (eq_one_of_inv_mul_mem_center hperf fun x => by
    have := DFunLike.congr_fun h1 (QuotientGroup.mk x)
    rw [hνbmk, MulAut.one_apply, QuotientGroup.eq] at this
    exact this)
  obtain ⟨R, hR⟩ := exists_isHypTransport (r := 1) (ε := 1) hUF
  let e₁ : M ⧸ Z ≃* hypPSU hUF 1 1 :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans (hypPSUEquivStatedProj hUF hR (by norm_num)).symm
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hord : orderOf (MulAut.congr e₁ νb) = 2 := by
    refine orderOf_eq_prime ?_ fun h1 => hνb1 ?_
    · rw [← map_pow, hνb2, map_one]
    · exact (MulAut.congr e₁).injective (h1.trans (map_one _).symm)
  obtain ⟨g, hgo, -, hνg⟩ := exists_psu3_inv_of_involution hUF hp2 hord
  set x : M := hypTransport hUF hR g with hx
  have hxo : orderOf x = p := by rw [hx, MulEquiv.orderOf_eq, hgo]
  have he₁ : e₁ (QuotientGroup.mk x) = hypProj hUF 1 1 g := by
    apply (hypPSUEquivStatedProj hUF hR (by norm_num)).injective
    change (hypPSUEquivStatedProj hUF hR (by norm_num)) ((hypPSUEquivStatedProj hUF hR
      (by norm_num)).symm
      (QuotientGroup.quotientMulEquivOfEq hZ (QuotientGroup.mk x))) = _
    rw [MulEquiv.apply_symm_apply, hypPSUEquivStatedProj_hypProj,
      QuotientGroup.quotientMulEquivOfEq_mk]
  have hmk : QuotientGroup.mk (ν x) = (QuotientGroup.mk x⁻¹ : M ⧸ Z) := by
    rw [← hνbmk]
    apply e₁.injective
    have h1 : (MulAut.congr e₁ νb) (e₁ (QuotientGroup.mk x)) = e₁ (νb (QuotientGroup.mk x)) := by
      change e₁ (νb (e₁.symm (e₁ (QuotientGroup.mk x)))) = _
      rw [MulEquiv.symm_apply_apply]
    rw [← h1, he₁, hνg, map_inv, QuotientGroup.mk_inv, map_inv, he₁]
  rw [QuotientGroup.eq] at hmk
  have hwZ : ν x * x ∈ Z := by
    have h2 : x * ν x ∈ Z := by
      have := Z.inv_mem hmk
      rwa [_root_.mul_inv_rev, inv_inv, inv_inv] at this
    have h3 : ν x * x = x⁻¹ * (x * ν x) * x := by
      rw [mul_assoc, mul_assoc]
      exact (inv_mul_cancel_left x (ν x * x)).symm
    rw [h3, Subgroup.mem_center_iff.mp h2 x⁻¹, mul_assoc, inv_mul_cancel, mul_one]
    exact h2
  have hw3 : (ν x * x) ^ 3 = 1 := by
    have hwZ' := hwZ
    rw [hZ, Subgroup.mem_subgroupOf] at hwZ'
    obtain ⟨u, hu⟩ := hwZ'
    have hdet := CFSG.LieType.Universal.Unitary.det_eq_one_of_mem_statedSU (ν x * x).2
    rw [← hu, Matrix.GeneralLinearGroup.coe_scalar, scalar_apply, det_diagonal, Finset.prod_const,
      Finset.card_univ, Fintype.card_fin] at hdet
    have hu3 : u ^ 3 = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val, hdet, Units.val_one])
    apply Subtype.ext
    rw [Subgroup.coe_pow, ← hu, ← map_pow, hu3, map_one]
    rfl
  have hxp : x ^ p = 1 := by
    have := pow_orderOf_eq_one x
    rwa [hxo] at this
  have hνx : ν x = (ν x * x) * x⁻¹ := by rw [mul_inv_cancel_right]
  have hwp : (ν x * x) ^ p = 1 := by
    have h1 : (ν x) ^ p = 1 := by rw [← map_pow, hxp, map_one]
    have hcomm : Commute (ν x * x) x⁻¹ := (Subgroup.mem_center_iff.mp hwZ x⁻¹).symm
    rw [hνx, hcomm.mul_pow, inv_pow, hxp, inv_one, mul_one] at h1
    exact h1
  have hw1 : ν x * x = 1 := by
    have hcop : Nat.Coprime 3 p :=
      (Nat.coprime_primes Nat.prime_three hUF.prime).mpr (Ne.symm hp3)
    exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop
      (orderOf_dvd_of_pow_eq_one hw3) (orderOf_dvd_of_pow_eq_one hwp))
  refine ⟨x, hxo, ?_⟩
  rw [hνx, hw1, one_mul]

theorem eq_three_or_five_of_autConf_su3 {p : ℕ} {F : Type} [Field F]
    (hUF : UnitaryFieldData p 1 F) (hp2 : p ≠ 2) {ν : MulAut ↥(StatedSU 3 (p ^ 1) F)}
    {Lb Pb : Subgroup (MulAut ↥(StatedSU 3 (p ^ 1) F))}
    (hc : AutConf ↥(StatedSU 3 (p ^ 1) F) ν Lb Pb) : p = 3 ∨ p = 5 := by
  by_cases hp3 : p = 3
  · exact Or.inl hp3
  obtain ⟨x, hxo, hνx⟩ := exists_su3_inv_of_involution hUF hp2 hp3 hc.sq hc.ne_one
  rcases hc.inv x (by rw [hxo]; exact hUF.prime.odd_of_ne_two hp2) hνx with h3 | h5
  · have := orderOf_dvd_of_pow_eq_one h3
    rw [hxo] at this
    exact Or.inl ((Nat.prime_dvd_prime_iff_eq hUF.prime Nat.prime_three).mp this)
  · have := orderOf_dvd_of_pow_eq_one h5
    rw [hxo] at this
    exact Or.inr ((Nat.prime_dvd_prime_iff_eq hUF.prime (by norm_num)).mp this)

variable {Q : Type} [Group Q] {K L P T : Subgroup Q} {v : Q}

theorem Conf12626.eq_three_or_five_of_su3 (hQ : CFSG.QuasithinUnique.Vol2Native.SQTKHypCat Q)
    (hconf : Conf12626 K L P T v) {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    (hSU : CFSG.Quasithin.IsSLEps3 false q ↥K) : q = 3 ∨ q = 5 := by
  have := hQ.finite
  obtain ⟨F, _, _, hFc, ⟨e⟩⟩ := hSU
  have hUF : UnitaryFieldData q 1 F := ⟨hq, le_rfl, by rw [hFc]⟩
  exact eq_three_or_five_of_autConf_su3 hUF hq2
    (hconf.autConf.map (e.trans (MulEquiv.subgroupCongr (by rw [pow_one]))))

theorem not_isSU3_two_of_isQuasisimple {X : Type} [Group X] (hX : CFSG.IsQuasisimple X) :
    ¬ CFSG.Quasithin.IsSLEps3 false 2 X := by
  rintro ⟨F, _, _, hF, ⟨e⟩⟩
  have h216 : Nat.card X = 216 := by
    rw [Nat.card_congr e.toEquiv]
    exact CFSG.Quasithin.Background.Harris.OrdinaryProofs.card_statedSU_three_two_of_card_four
      (by rw [hF]; norm_num)
  have : Finite X := Nat.finite_of_card_ne_zero (by rw [h216]; norm_num)
  have : Fintype X := Fintype.ofFinite X
  apply CFSG.LocalAnalysis.ComponentInitial.not_isSolvable_of_isQuasisimple hX
  exact CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow (p := 2) (q := 3)
    (a := 3) (b := 3) Nat.prime_two Nat.prime_three (by norm_num)
    (by rw [← Nat.card_eq_fintype_card, h216]; norm_num)

end CFSG.Quasithin.H13.S126C
