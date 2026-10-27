module

public import CFSG.RankThree.PartTwo.Sec8.Hering88NLemmaB
public import CFSG.RankThree.PartTwo.Sec8.Hering88NG2Proof
public import CFSG.RankThree.PartTwo.Sec11.KS11Lie4ProofD4
import CFSG.RankThree.PartTwo.Sec11.KS11Lie6ProofBCent
import CFSG.RankThree.PartTwo.Sec21.Item219LieProofD4U2
import CFSG.RankThree.PartTwo.Sec8.Item812Res7ProofD4N

public section

namespace CFSG.RankThree.PartTwo.Sec8.Hering88N

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.PartTwo.Sec11.KS11Lie4Proof (d4ShortSL2 d4Outer)
open scoped commutatorElement

section Group

variable {M : Type*} [Group M]

theorem le_of_isPerfect_of_commutator_mem {P C S : Subgroup M} (hP : Group.IsPerfect P)
    (hPC : P ≤ C) (hS : ∀ x ∈ C, ∀ y ∈ C, x * y * x⁻¹ * y⁻¹ ∈ S) : P ≤ S := by
  have h1 : ⁅P, P⁆ = P := Subgroup.isPerfect_iff.mp hP
  rw [← h1]
  refine (Subgroup.commutator_mono hPC hPC).trans (Subgroup.commutator_le.mpr fun x hx y hy => ?_)
  rw [commutatorElement_def]
  exact hS x hx y hy

theorem isPerfect_map {M' : Type*} [Group M'] (f : M →* M') {P : Subgroup M}
    (hP : Group.IsPerfect P) : Group.IsPerfect (P.map f) :=
  hP.ofSurjective (f := f.subgroupMap P) (MonoidHom.subgroupMap_surjective f P)

theorem map_conj_le_centralizer {P : Subgroup M} {z : M}
    (hPz : P ≤ Subgroup.centralizer ({z} : Set M)) (h : M) :
    P.map (MulAut.conj h).toMonoidHom ≤ Subgroup.centralizer ({h * z * h⁻¹} : Set M) := by
  rintro _ ⟨p, hp, rfl⟩
  rw [Subgroup.mem_centralizer_singleton_iff]
  have hpz : p * z = z * p := Subgroup.mem_centralizer_singleton_iff.mp (hPz hp)
  change h * p * h⁻¹ * (h * z * h⁻¹) = h * z * h⁻¹ * (h * p * h⁻¹)
  calc h * p * h⁻¹ * (h * z * h⁻¹) = h * (p * z) * h⁻¹ := by group
    _ = h * (z * p) * h⁻¹ := by rw [hpz]
    _ = h * z * h⁻¹ * (h * p * h⁻¹) := by group

theorem pow_eq_one_of_conj_pow_eq_one (h y : M) {n : ℕ} (H : (h * y * h⁻¹) ^ n = 1) :
    y ^ n = 1 := by
  rw [conj_pow] at H
  calc y ^ n = h⁻¹ * (h * y ^ n * h⁻¹) * h := by group
    _ = 1 := by rw [H]; group

theorem conj_isTwoElt (h : M) {y : M} (h2 : ∃ k : ℕ, y ^ 2 ^ k = 1) :
    ∃ k : ℕ, (h * y * h⁻¹) ^ 2 ^ k = 1 := by
  obtain ⟨k, hk⟩ := h2
  exact ⟨k, by rw [conj_pow, hk, mul_one, mul_inv_cancel]⟩

end Group

section D4


theorem two_pow_mod_three {m : ℕ} (hodd : Odd m) : 2 ^ m % 3 = 2 := by
  obtain ⟨j, rfl⟩ := hodd
  rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
  norm_num

theorem d4_pow_four_eq_one_of_isPerfect {K : Type} [Field K] [Finite K] {m : ℕ} (hm : 1 ≤ m)
    (hodd : Odd m) {σ : K ≃+* K} (hK : Nat.card K = (2 ^ m) ^ 3) (hσ : ∀ c, σ c = c ^ 2 ^ m)
    {z : graphFixedRootGroup TwistTag.D4 K σ.toRingHom} (hz3 : z ^ 3 = 1) (hz1 : z ≠ 1)
    {P : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)} (hP : Group.IsPerfect P)
    (hPz : P ≤ Subgroup.centralizer ({z} : Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)))
    {y : graphFixedRootGroup TwistTag.D4 K σ.toRingHom} (hy : y ∈ P)
    (h2 : ∃ k : ℕ, y ^ 2 ^ k = 1) : y ^ 4 = 1 := by
  classical
  have h3q : ¬ 3 ∣ 2 ^ m := fun h => by
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h
    omega
  haveI : CharP K 2 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    Nat.prime_two (k := m * 3) (by omega) (by rw [hK, pow_mul])
  obtain ⟨h, hh⟩ := Sec11.KS11Lie6Proof.d4ThreeConj_holds K (2 ^ m) σ hK hσ h3q z hz3 hz1
  have hz'3 : (h * z * h⁻¹) ^ 3 = 1 := by rw [conj_pow, hz3, mul_one, mul_inv_cancel]
  have hz'1 : h * z * h⁻¹ ≠ 1 := fun h1 => hz1 (by
    have := congrArg (fun x => h⁻¹ * x * h) h1
    rwa [show h⁻¹ * (h * z * h⁻¹) * h = z by group, show h⁻¹ * 1 * h = 1 by group] at this)
  set P' := P.map (MulAut.conj h).toMonoidHom with hP'def
  have hP' : Group.IsPerfect P' := isPerfect_map _ hP
  have hP'z := map_conj_le_centralizer hPz h
  have hy' : h * y * h⁻¹ ∈ P' := ⟨y, hy, rfl⟩
  have h2' := conj_isTwoElt h h2
  refine pow_eq_one_of_conj_pow_eq_one h y ?_
  rcases hh with hS | hC
  ·
    obtain ⟨c, R, -, -, hcomm, U, -, ⟨ι⟩⟩ :=
      Sec21.Item219LieProof.d4_threeA_model_unitary_two Nat.prime_two hm (by norm_num)
        (two_pow_mod_three hodd) hK hσ hS hz'3 hz'1
    set P'' := P'.map (MulAut.conj c).toMonoidHom with hP''def
    have hP'' : Group.IsPerfect P'' := isPerfect_map _ hP'
    have hP''R : P'' ≤ R :=
      le_of_isPerfect_of_commutator_mem hP'' (map_conj_le_centralizer hP'z c) hcomm
    have hy'' : c * (h * y * h⁻¹) * c⁻¹ ∈ R := hP''R ⟨_, hy', rfl⟩
    refine pow_eq_one_of_conj_pow_eq_one c _ ?_
    haveI : CharP (AlgebraicClosure K) 2 :=
      charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
    set x : R := ⟨c * (h * y * h⁻¹) * c⁻¹, hy''⟩ with hx
    obtain ⟨k, hk⟩ := conj_isTwoElt c h2'
    have hxk : x ^ 2 ^ k = 1 := Subtype.ext (by rw [Subgroup.coe_pow, hx]; exact hk)
    have hι : ((ι x : U) : GL (Fin 3) (AlgebraicClosure K)) ^ 4 = 1 :=
      gl3_pow_four_eq_one _ ⟨k, by rw [← Subgroup.coe_pow, ← map_pow, hxk, map_one]; rfl⟩
    have hx4 : x ^ 4 = 1 := ι.injective (by
      rw [map_pow, map_one]
      exact Subtype.ext (by rw [Subgroup.coe_pow]; exact hι))
    have := congrArg Subtype.val hx4
    rwa [Subgroup.coe_pow] at this
  ·
    obtain ⟨hcomm, -⟩ :=
      Sec11.KS11Lie6Proof.d4ThreeBCent_holds K (2 ^ m) σ hK hσ h3q _ hC hz'3 hz'1
    have hP'S : P' ≤ d4ShortSL2 K σ.toRingHom := le_of_isPerfect_of_commutator_mem hP' hP'z hcomm
    have hmem : ((h * y * h⁻¹ : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :
        ModGL TwistTag.D4.tag K) ∈ (orbitRankOneHom TwistTag.D4 K σ.toRingHom d4Outer).range :=
      hP'S hy'
    haveI : CharP (orbitField TwistTag.D4 K σ.toRingHom d4Outer) 2 :=
      RingHom.charP (orbitField TwistTag.D4 K σ.toRingHom d4Outer).subtype
        Subtype.val_injective 2
    obtain ⟨k, hk⟩ := h2'
    have h2sq := pow_two_pow_eq_one_of_mem_range
      (orbitRankOneHom TwistTag.D4 K σ.toRingHom d4Outer) (j := 1)
      (fun t ht => by rw [pow_one]; exact sl2_pow_two_eq_one t ht) hmem
      ⟨k, by rw [← Subgroup.coe_pow, hk]; rfl⟩
    have hsq : (h * y * h⁻¹) ^ 2 = 1 := Subtype.ext (by
      rw [Subgroup.coe_pow]
      simpa using h2sq)
    rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul, hsq, one_pow]

end D4

section Q


theorem lemmaB {Q : Type} [Group Q] [Finite Q] {m : ℕ} (hodd : Odd m)
    (hQ : IsoTrialityD4 Q m ∨ IsoGTwoEven Q (3 * m)) {g : Q} (hg3 : g ^ 3 = 1) (hg1 : g ≠ 1)
    {P : Subgroup Q} (hP : Group.IsPerfect P) (hPg : P ≤ Subgroup.centralizer ({g} : Set Q))
    {y : Q} (hy : y ∈ P) (h2 : ∃ k : ℕ, y ^ 2 ^ k = 1) : y ^ 4 = 1 := by
  obtain ⟨k, hk⟩ := h2
  rcases hQ with hD | hG
  · obtain ⟨hm1, K, _, _, σ, hK, hσ, ⟨e⟩⟩ := Item812Res7.exists_trialityD4_model hD
    have hP' : Group.IsPerfect (P.map e.toMonoidHom) := isPerfect_map _ hP
    have hP'z : P.map e.toMonoidHom ≤ Subgroup.centralizer ({e g} : Set _) := by
      rintro _ ⟨p, hp, rfl⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hpg : p * g = g * p := Subgroup.mem_centralizer_singleton_iff.mp (hPg hp)
      change e p * e g = e g * e p
      rw [← map_mul, ← map_mul, hpg]
    have h4 := d4_pow_four_eq_one_of_isPerfect hm1 hodd hK hσ
      (by rw [← map_pow, hg3, map_one]) (fun h => hg1 (e.injective (h.trans (map_one e).symm)))
      hP' hP'z ⟨y, hy, rfl⟩ ⟨k, by rw [MulEquiv.coe_toMonoidHom, ← map_pow, hk, map_one]⟩
    exact e.injective (by rw [map_pow, map_one]; exact h4)
  · obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hG
    haveI : CharP K 2 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
      Nat.prime_two (k := 3 * m) (by have := hodd.pos; omega) hK
    have hring : ringChar K = 2 := ringChar.eq K 2
    have h3 : 3 ∣ Nat.card K + 1 := by
      rw [hK]
      obtain ⟨j, rfl⟩ := hodd
      have : 2 ^ (3 * (2 * j + 1)) = 8 * 64 ^ j := by
        rw [show 3 * (2 * j + 1) = 3 + 6 * j by ring, pow_add, pow_mul]
        norm_num
      rw [this]
      exact Nat.dvd_of_mod_eq_zero (by rw [Nat.add_mod, Nat.mul_mod, Nat.pow_mod]; norm_num)
    have hyg : e y ∈ Subgroup.centralizer ({e g} : Set _) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hyg' : y * g = g * y := Subgroup.mem_centralizer_singleton_iff.mp (hPg hy)
      rw [← map_mul, ← map_mul, hyg']
    have h4 := g2ThreeCentTwoExp_holds K hring h3 (e g) (by rw [← map_pow, hg3, map_one])
      (fun h => hg1 (e.injective (h.trans (map_one e).symm))) (e y) hyg
      ⟨k, by rw [← map_pow, hk, map_one]⟩
    exact e.injective (by rw [map_pow, h4, map_one])

end Q

end CFSG.RankThree.PartTwo.Sec8.Hering88N

end
