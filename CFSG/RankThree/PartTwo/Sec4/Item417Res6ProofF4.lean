module

public import CFSG.RankThree.PartTwo.Sec4.Item417Res5ProofChevTwo
public import CFSG.RankThree.PartTwo.Sec21.ReeF4ThreeLocalProofCent
import CFSG.RankThree.PartTwo.Sec4.Item417Res6ProofUnitary
import CFSG.RankThree.PartTwo.Sec21.ReeF4Cent2Proof
import CFSG.RankThree.SteinbergR3ELargeReeOrder
import CFSG.RankThree.PartTwo.Sec5.Tools
public import CFSG.LocalAnalysis.SectionRank.TitsCover

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
open CFSG.Assembly.LowTwoRank (StatedSU)

open CFSG.LieType.Universal.Unitary (SU equivStatedSU)

open CFSG.LieType.BorelTits (unitaryInvolution)

open Res417Three Res417Five

namespace Res417Six

theorem two_pow_odd_mod_three (a : ℕ) :
    2 ^ (2 * a + 1) % 3 = 2 ∧ (2 ^ (2 * a + 1)) ^ 2 % 3 = 1 ∧ (2 ^ (2 * a + 1)) ^ 4 % 3 = 1 := by
  have h := (two_pow_mod_three (2 * a + 1)).2 ⟨a, rfl⟩
  refine ⟨h, ?_, ?_⟩
  · rw [Nat.pow_mod, h]
  · rw [Nat.pow_mod, h]

theorem card_reeGamma_eq_mul (q : ℕ) (hq : 2 ≤ q) :
    q ^ 12 * (q - 1) ^ 2 * (q + 1) ^ 2 * (q ^ 2 + 1) ^ 2 * (q ^ 2 - q + 1) * (q ^ 4 - q ^ 2 + 1) =
      (q ^ 3 * (q ^ 2 - 1) * (q ^ 3 + 1)) *
        (q ^ 9 * (q - 1) * (q ^ 2 + 1) ^ 2 * (q ^ 4 - q ^ 2 + 1)) := by
  have h1 : 1 ≤ q := by omega
  have h2 : q ≤ q ^ 2 := Nat.le_self_pow (by norm_num) q
  have h24 : q ^ 2 ≤ q ^ 4 := Nat.pow_le_pow_right h1 (by norm_num)
  have h3 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ (by omega)
  zify [h1, h2, h24, h3]
  ring

theorem not_three_dvd_cofactor {q : ℕ} (h1 : q % 3 = 2) :
    ¬ 3 ∣ q ^ 9 * (q - 1) * (q ^ 2 + 1) ^ 2 * (q ^ 4 - q ^ 2 + 1) := by
  have h2 : q ^ 2 % 3 = 1 := by rw [Nat.pow_mod, h1]
  have h4 : q ^ 4 % 3 = 1 := by rw [Nat.pow_mod, h1]
  have h24 : q ^ 2 ≤ q ^ 4 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have hp := Nat.prime_three
  intro h
  rcases (Nat.Prime.dvd_mul hp).mp h with h | h
  · rcases (Nat.Prime.dvd_mul hp).mp h with h | h
    · rcases (Nat.Prime.dvd_mul hp).mp h with h | h
      · have := hp.dvd_of_dvd_pow h
        omega
      · omega
    · have := hp.dvd_of_dvd_pow h
      omega
  · generalize q ^ 4 = A at h h4 h24
    generalize q ^ 2 = B at h h2 h24
    omega

section Certs


theorem not_isDatum417_reeGamma (hC : Sec8.KF83ReeCentThree) {a : ℕ} (ha : 1 ≤ a) {K : Type}
    [Field K] [Finite K] [CharP K ReeTag.F4.prime] (hK : Nat.card K = 2 ^ (2 * a + 1))
    (D : Subgroup (ReeTag.F4.reeGamma K a)) : ¬ IsDatum417 (ReeTag.F4.reeGamma K a) D := by
  classical
  rintro ⟨hDe, -, F, hFD, hF9, T, hT2, hFT, hTF⟩
  have : Finite (ModGL ReeTag.F4.tag K) := finite_modGL
  have : Finite (ReeTag.F4.reeGamma K a) := Subtype.finite
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set q := 2 ^ (2 * a + 1) with hqdef
  have hq2 : 2 ≤ q := by
    rw [hqdef]
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (2 * a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hDcomm : ∀ x ∈ D, ∀ y ∈ D, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hDe.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hFe : CFSG.Assembly.IsElemAbelian 3 F :=
    ⟨⟨⟨fun x y => Subtype.ext (hDcomm _ (hFD x.2) _ (hFD y.2))⟩⟩, fun x hx => hDe.2 x (hFD hx)⟩
  have hFcomm : ∀ x ∈ F, ∀ y ∈ F, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hFe.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  apply hTF
  refine le_centralizer_of_unitary hFe hF9 hT2 hFT fun e heF he1 => ?_
  have he3 : orderOf e = 3 := orderOf_eq_prime (hFe.2 e heF) he1
  obtain ⟨K', hK'f, hK'fin, hK', ⟨φ⟩⟩ := hC a K ha hK e he3
  set H := Subgroup.centralizer ({e} : Set (ReeTag.F4.reeGamma K a)) with hH
  have hcharK' : CharP K' 2 := by
    have := Fintype.ofFinite K'
    refine charP_of_card_eq_prime_pow (p := 2) (f := 2 * (2 * a + 1)) ?_
    rw [Fintype.card_eq_nat_card, hK', ← pow_mul, mul_comm]
  have hSU : Nat.card (StatedSU 3 q K') = q ^ 3 * (q ^ 2 - 1) * (q ^ 3 + 1) := by
    rw [← Nat.card_congr (equivStatedSU (p := 2) (f := 2 * a + 1) hK' 3).toEquiv,
      CFSG.LieType.Steinberg.card_SU_three hK']
  have hNcard : Nat.card (inSubgroup perfectResidual H) = Nat.card (perfectResidual H) :=
    Subgroup.card_map_of_injective H.subtype_injective
  have hPcard : Nat.card (perfectResidual H) = q ^ 3 * (q ^ 2 - 1) * (q ^ 3 + 1) := by
    rw [← hNcard, Nat.card_congr φ.toEquiv, hSU]
  have hΓ := (CFSG.RankThree.LargeReeOrder.large_Ree_exact_native_order_and_prime_factor_exhaustion
    a K hK).1
  rw [← hqdef, card_reeGamma_eq_mul q hq2, ← hPcard] at hΓ
  have hidx : (perfectResidual H).index * H.index =
      q ^ 9 * (q - 1) * (q ^ 2 + 1) ^ 2 * (q ^ 4 - q ^ 2 + 1) := by
    have h1 := (perfectResidual H).card_mul_index
    have h2 := H.card_mul_index
    have hpos : 0 < Nat.card (perfectResidual H) := Nat.card_pos
    rw [← h1, mul_assoc] at h2
    rw [hΓ] at h2
    exact Nat.eq_of_mul_eq_mul_left hpos h2
  have hcop : Nat.Coprime 3 (perfectResidual H).index := by
    refine (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr fun h3 => ?_
    apply not_three_dvd_cofactor (two_pow_odd_mod_three a).1
    rw [← hqdef, ← hidx]
    exact Dvd.dvd.mul_right h3 _
  have hFH : F ≤ H := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hFcomm x hx e heF)
  have : (perfectResidual H).Characteristic :=
    CFSG.RankThreeCoreUniqueness.Helpers.perfectResidual_characteristic
  have hFN : F ≤ inSubgroup perfectResidual H := by
    intro x hx
    have h1 : (⟨x, hFH hx⟩ : H) ∈ perfectResidual H :=
      mem_of_coprime_index hcop (Subtype.ext (by simpa using hFe.2 x hx))
    exact ⟨⟨x, hFH hx⟩, h1, rfl⟩
  refine ⟨inSubgroup perfectResidual H,
    Subgroup.le_normalizer.trans
      (CFSG.RankThreeCoreUniqueness.Helpers.perfectResidualOf_normalizer_contains H), hFN,
    2 * a + 1, K',
    hK'f, (StatedSU 3 q K').subtype.comp φ.toMonoidHom,
    (StatedSU 3 q K').subtype_injective.comp φ.injective, ⟨Nat.prime_two, by omega, ?_⟩, ?_,
    fun x => (φ x).2⟩
  · show Nat.card K' = piCard false (2 ^ (2 * a + 1))
    rw [piCard, Bool.cond_false]
    exact hK'
  · show (2 ^ (2 * a + 1)) % 3 = 2
    exact (two_pow_odd_mod_three a).1

theorem not_isDatum417_of_twistedF4 (h : Sec8.ReeF4OrderThreeConj) {X : Type} [Group X] {f : ℕ}
    (hX : ReeTitsModel X .twistedF4 2 f) (D : Subgroup X) : ¬ IsDatum417 X D := by
  intro hD
  obtain ⟨-, a, ha, -, K, _, _, _, hK, ⟨ψ⟩⟩ := exists_mulEquiv_reeGamma hX
  exact not_isDatum417_reeGamma (Sec8.ReeF4Cent2Proof.kF83ReeCentThree_of_orderThreeConj h) ha hK
    _ (hD.map ψ)

end Certs

@[expose] def K417TitsCentThree : Prop :=
  ∀ (X : Type) [Group X] (f : ℕ), ReeTitsModel X .Tits 2 f → ∀ x : X, orderOf x = 3 →
    ∃ P : Subgroup X, IsPGroup 3 P ∧
      Subgroup.centralizer ({x} : Set X) ≤ Subgroup.normalizer (P : Set X) ∧
      ∀ y ∈ Subgroup.centralizer ({x} : Set X), y ^ 3 = 1 → y ∈ P

theorem eq_one_of_mem_pGroup_two_three {X : Type*} [Group X] {P T : Subgroup X}
    (hP : IsPGroup 3 P) (hT : IsPGroup 2 T) {x : X} (hxP : x ∈ P) (hxT : x ∈ T) : x = 1 := by
  obtain ⟨i, hi⟩ := hP ⟨x, hxP⟩
  obtain ⟨j, hj⟩ := hT ⟨x, hxT⟩
  have h1 : orderOf x ∣ 3 ^ i := orderOf_dvd_of_pow_eq_one (by simpa using congrArg Subtype.val hi)
  have h2 : orderOf x ∣ 2 ^ j := orderOf_dvd_of_pow_eq_one (by simpa using congrArg Subtype.val hj)
  have hcop : Nat.Coprime (3 ^ i) (2 ^ j) := Nat.Coprime.pow i j (by norm_num)
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop h1 h2)

theorem not_isDatum417_tits
    (hT3 : K417TitsCentThree) {X : Type} [Group X] {f : ℕ} (hX : ReeTitsModel X .Tits 2 f)
    (D : Subgroup X) : ¬ IsDatum417 X D := by
  classical
  rintro ⟨hDe, -, F, hFD, hF9, T, hT2, hFT, hTF⟩
  obtain ⟨K, _, _, _, -, ⟨ψ⟩⟩ := CFSG.SectionRank.exists_mulEquiv_titsGroup_of_model hX
  have : Finite (ModGL ReeTag.F4.tag K) := finite_modGL
  have : Finite (commutator (reeFixed ReeTag.F4 K 0)) := Subtype.finite
  have : Finite X := Finite.of_equiv _ ψ.symm.toEquiv
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hDcomm : ∀ x ∈ D, ∀ y ∈ D, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hDe.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hFe : CFSG.Assembly.IsElemAbelian 3 F :=
    ⟨⟨⟨fun x y => Subtype.ext (hDcomm _ (hFD x.2) _ (hFD y.2))⟩⟩, fun x hx => hDe.2 x (hFD hx)⟩
  have hFcomm : ∀ x ∈ F, ∀ y ∈ F, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hFe.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hcop : Nat.Coprime 3 (Nat.card T) := by
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := 2) (G := T)).mp hT2
    rw [hk]
    exact Nat.Coprime.pow_right k (by norm_num)
  apply hTF
  refine Sec5.le_of_forall_inf_centralizer_le Nat.prime_three hFe (by norm_num; exact hF9) hFT
    hcop fun e heF he1 => ?_
  obtain ⟨P, hP3, hCP, hPall⟩ := hT3 X f hX e (orderOf_eq_prime (hFe.2 e heF) he1)
  have hFP : ∀ r ∈ F, r ∈ P := fun r hr =>
    hPall r (Subgroup.mem_centralizer_singleton_iff.mpr (hFcomm r hr e heF)) (hFe.2 r hr)
  rintro w ⟨hwT, hwe⟩
  rw [Subgroup.mem_centralizer_iff]
  intro r hr
  have hcT : r * w * r⁻¹ * w⁻¹ ∈ T :=
    T.mul_mem ((Subgroup.mem_normalizer_iff.mp (hFT hr) w).mp hwT) (T.inv_mem hwT)
  have hcP : r * w * r⁻¹ * w⁻¹ ∈ P := by
    have h1 : w * r⁻¹ * w⁻¹ ∈ P :=
      (Subgroup.mem_normalizer_iff.mp (hCP hwe) r⁻¹).mp (P.inv_mem (hFP r hr))
    have : r * w * r⁻¹ * w⁻¹ = r * (w * r⁻¹ * w⁻¹) := by group
    rw [this]
    exact P.mul_mem (hFP r hr) h1
  have h1 := eq_one_of_mem_pGroup_two_three hP3 hT2 hcP hcT
  have key : r * w = (r * w * r⁻¹ * w⁻¹) * (w * r) := by group
  rw [key, h1, one_mul]

theorem k417NoDatumF4_of
    (h : Sec8.ReeF4OrderThreeConj) (hT3 : K417TitsCentThree) : K417NoDatumF4 := by
  intro X _ f hX D
  rcases hX with hF | hT
  · exact not_isDatum417_of_twistedF4 h hF D
  · exact not_isDatum417_tits hT3 hT D

end Res417Six

end CFSG.RankThree.PartTwo.Sec4
