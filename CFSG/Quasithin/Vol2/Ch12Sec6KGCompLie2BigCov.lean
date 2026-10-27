module

public import CFSG.Quasithin.Vol2.Ch12Sec6KGCompDescend
public import CFSG.Quasithin.Vol2.Ch12Sec6KGCompLie2BigL3
public import CFSG.Quasithin.Vol2.Ch12Sec6KGCompLie2BigU3
public import CFSG.LieType.Universal.Unitary.Clause0
public import CFSG.LieType.Universal.SpecialLinear
public import CFSG.Adapters.SpecialLinearPerfect
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Open.StatedAPI
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerFinal

public section

namespace CFSG.Quasithin.H13.S126C

open CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.Assembly.LowTwoRank (StatedSL StatedSU StatedProj StatedScalars StatedClassicalModel
  StatedLieAdmissible specialLinearGroupEquivStatedSL)

theorem odd_card_of_pow_three {G : Type} [Group G] [Finite G] (h : ∀ z : G, z ^ 3 = 1) :
    Odd (Nat.card G) := by
  rw [Nat.odd_iff]
  by_contra h2
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2' : 2 ∣ Nat.card G := Nat.dvd_of_mod_eq_zero (by omega)
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := G) 2 h2'
  have h3 := orderOf_dvd_of_pow_eq_one (h z)
  rw [hz] at h3
  omega

section SL3

variable {K : Type} [Field K]

theorem pow_three_of_mem_center_sl3 {A : Matrix.SpecialLinearGroup (Fin 3) K}
    (hA : A ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) K)) : A ^ 3 = 1 := by
  obtain ⟨r, hr, hrA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hA
  rw [Fintype.card_fin] at hr
  have hm : (A : Matrix (Fin 3) (Fin 3) K) ^ 3 = 1 := by rw [← hrA, ← map_pow, hr, map_one]
  exact Subtype.ext (by
    rw [Matrix.SpecialLinearGroup.coe_pow, hm, Matrix.SpecialLinearGroup.coe_one])

end SL3

theorem false_of_autConf_sl3 {M : Type} [Group M] {f : ℕ} (hf : 3 ≤ f) (hM : IsSL3 (2 ^ f) M)
    {ν : MulAut M} {Lb Pb : Subgroup (MulAut M)} (h : AutConf M ν Lb Pb) : False := by
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hM
  have : CharP K 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
      (by omega) hK
  have : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 3) K) :=
    CFSG.ClassicalModels.specialLinear_isPerfect_of_three_le le_rfl
  let e' : M ≃* Matrix.SpecialLinearGroup (Fin 3) K :=
    e.trans (specialLinearGroupEquivStatedSL 3 K).symm
  have hZ : Odd (Nat.card (Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) K))) :=
    odd_card_of_pow_three fun z => Subtype.ext (by
      rw [Subgroup.coe_pow, pow_three_of_mem_center_sl3 z.2, Subgroup.coe_one])
  have hadm : StatedLieAdmissible .PSL 3 2 f := ⟨Nat.prime_two, by omega, by norm_num, by simp,
    by simp⟩
  exact false_of_autConf_psl3 hf
    (CFSG.LieType.Universal.SpecialLinear.statedClassicalModel_center_quotient 2 K hadm hK)
    ((h.map e').descend le_rfl hZ)

theorem det_eq_one_of_mem_statedSU {n q : ℕ} {K : Type} [Field K] {g : GL (Fin n) K}
    (hg : g ∈ StatedSU n q K) : (g : Matrix (Fin n) (Fin n) K).det = 1 :=
  CFSG.Open.StatedAPI.det_of_mem_statedSU hg

theorem pow_three_of_mem_center_su3 {q : ℕ} {K : Type} [Field K]
    (hZc : Subgroup.center (StatedSU 3 q K) = (StatedScalars (Fin 3) K).subgroupOf (StatedSU 3 q K))
    {z : StatedSU 3 q K} (hz : z ∈ Subgroup.center (StatedSU 3 q K)) : z ^ 3 = 1 := by
  rw [hZc, Subgroup.mem_subgroupOf] at hz
  obtain ⟨c, hc⟩ := hz
  have hdet := det_eq_one_of_mem_statedSU z.2
  rw [← hc, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.det_diagonal,
    Fin.prod_univ_three] at hdet
  apply Subtype.ext
  apply Units.ext
  rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val, ← hc, Matrix.GeneralLinearGroup.coe_scalar,
    ← map_pow, Subgroup.coe_one, Units.val_one, pow_three', hdet, map_one]

theorem false_of_autConf_su3 {M : Type} [Group M] {f : ℕ} (hf : 3 ≤ f) (hM : IsSU3 (2 ^ f) M)
    {ν : MulAut M} {Lb Pb : Subgroup (MulAut M)} (h : AutConf M ν Lb Pb) : False := by
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hM
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK' : Nat.card K = 2 ^ (2 * f) := by rw [hK, ← pow_mul, mul_comm]
  have : CharP K 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
      (by omega) hK'
  have h8 : 2 ^ 3 ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  norm_num at h8
  obtain ⟨hq, hZc⟩ := CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card (F := K)
    (p := 2) (f := f) (n := 3) hK le_rfl (fun h2 => by simp only [Prod.mk.injEq] at h2; omega)
  have : Group.IsPerfect (StatedSU 3 (2 ^ f) K) := hq.1
  have hZ : Odd (Nat.card (Subgroup.center (StatedSU 3 (2 ^ f) K))) :=
    odd_card_of_pow_three fun z => Subtype.ext (by
      rw [Subgroup.coe_pow, pow_three_of_mem_center_su3 hZc z.2, Subgroup.coe_one])
  have hadm : StatedLieAdmissible .PSU 3 2 f :=
    ⟨Nat.prime_two, by omega, le_rfl, fun h2 => by simp only [Prod.mk.injEq] at h2; omega⟩
  have hmod : StatedClassicalModel (StatedSU 3 (2 ^ f) K ⧸ Subgroup.center (StatedSU 3 (2 ^ f) K))
      .PSU 3 2 f :=
    ⟨hadm, K, inferInstance, inferInstance, hK, ⟨QuotientGroup.quotientMulEquivOfEq hZc⟩⟩
  exact false_of_autConf_psu3 hf hmod ((h.map e).descend le_rfl hZ)

theorem false_of_autConf_slEps3 {M : Type} [Group M] {f : ℕ} (hf : 3 ≤ f) {s : Bool}
    (hM : IsSLEps3 s (2 ^ f) M) {ν : MulAut M} {Lb Pb : Subgroup (MulAut M)}
    (h : AutConf M ν Lb Pb) : False := by
  cases s
  · exact false_of_autConf_su3 hf hM h
  · exact false_of_autConf_sl3 hf hM h

end CFSG.Quasithin.H13.S126C
