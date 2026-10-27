module

import CFSG.RankThree.PartTwo.Sec16.Item169StepsProofHess
import CFSG.RankThree.PartTwo.Sec13.Item138NMod9
import CFSG.RankThree.PartTwo.Sec6.Item612Plus
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Monster.B.TwoA.Census.PermClasses
public import CFSG.RankThree.PartTwo.KFacts.KSL3PiOrder3TypeC
public import CFSG.RankThree.PartTwo.Sec4.Statements
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.SubgroupConj

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo

namespace Proof1513Res3

section Model

open CFSG.RankThree.PartTwo.Sec4 Matrix
open CFSG.Assembly.LowTwoRank (StatedScalars)
open CFSG.Assembly.RankThreeEven (projImage)
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)
open CFSG.RankThree.PartTwo.Sec16.ProofHess

variable {K : Type} [Field K] {f : ℕ} {π : Bool}

theorem eq_one_of_pow_two_pow (hK : PiField π 2 f K) {d : K} {k : ℕ} (hd : d ^ 2 ^ k = 1) :
    d = 1 := by
  have := hK.finite
  have : Fintype K := Fintype.ofFinite K
  have hd0 : d ≠ 0 := by
    rintro rfl
    rw [zero_pow (by positivity)] at hd
    exact zero_ne_one hd
  have h1 : d ^ (Fintype.card K - 1) = 1 := FiniteField.pow_card_sub_one_eq_one d hd0
  have hodd : Odd (Fintype.card K - 1) := by
    rw [← Nat.card_eq_fintype_card, hK.card]
    have hf : 1 ≤ f := hK.one_le
    cases π
    · change Odd ((2 ^ f) ^ 2 - 1)
      rw [← pow_mul]
      have h2 : 2 ∣ 2 ^ (f * 2) := dvd_pow_self 2 (by omega)
      have h3 : 1 ≤ 2 ^ (f * 2) := Nat.one_le_two_pow
      rw [Nat.odd_iff]
      omega
    · change Odd (2 ^ f - 1)
      have h2 : 2 ∣ 2 ^ f := dvd_pow_self 2 (by omega)
      have h3 : 1 ≤ 2 ^ f := Nat.one_le_two_pow
      rw [Nat.odd_iff]
      omega
  have ho1 : orderOf d ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hd
  have ho2 : orderOf d ∣ Fintype.card K - 1 := orderOf_dvd_of_pow_eq_one h1
  have hcop : Nat.Coprime (2 ^ k) (Fintype.card K - 1) :=
    Nat.Coprime.pow_left _ ((Nat.coprime_two_left).mpr hodd)
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop ho1 ho2)

theorem eq_one_of_commute_of_pow_two_pow (hK : PiField π 2 f K) (hq : ModThree π (2 ^ f))
    (h9 : ¬ 9 ∣ Nat.card K - 1) {x z : ProjGenLinGroup (Fin 3) K}
    (hxS : x ∈ projImage (slPi π 3 (2 ^ f) K)) (hzS : z ∈ projImage (slPi π 3 (2 ^ f) K))
    (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1) (hzx : z * x = x * z) {k : ℕ} (hz : z ^ 2 ^ k = 1) :
    z = 1 := by
  have := hK.finite
  have hπ : π = false → UnitaryFieldData 2 f K := fun h => by subst h; exact hK.unitary
  have h3 : (3 : K) ≠ 0 := hK.three_ne_zero hq
  obtain ⟨τ, hτ, hτ1⟩ := exists_tau hK hq
  obtain ⟨xh, hxhS, rfl⟩ := hxS
  have hxh3 : xh ^ 3 = 1 := pow_three_eq_one_of_lift hK h9 hxhS hx3
  have hdet : (xh : Matrix (Fin 3) (Fin 3) K).det = 1 := ((mem_slPi_iff hπ).mp hxhS).2
  have hxhs : ∀ c : K, (xh : Matrix (Fin 3) (Fin 3) K) ≠ c • 1 := by
    intro c hc
    apply hx1
    have hc0 : c ≠ 0 := by
      rintro rfl
      rw [zero_smul] at hc
      rw [hc, det_zero] at hdet
      exact zero_ne_one hdet
    exact KFacts.mk_eq_one_iff_mem_statedScalars'.mpr (mem_statedScalars_of_eq_smul hc hc0)
  have hxh3m : (xh : Matrix (Fin 3) (Fin 3) K) ^ 3 = 1 := by
    rw [← Units.val_pow_eq_pow_val, hxh3, Units.val_one]
  have hzo : orderOf z ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hz
  have hcop : Nat.Coprime 3 (orderOf z) :=
    Nat.Coprime.coprime_dvd_right hzo (Nat.Coprime.pow_right _ (by norm_num))
  obtain ⟨s, hsS, hsz, hso⟩ := exists_lift_pow_eq_one hK hzS hcop
  have hsk : s ^ 2 ^ k = 1 := by
    obtain ⟨t, ht⟩ := hzo
    rw [ht, pow_mul, hso, one_pow]
  have hsx : s * xh = xh * s := by
    refine commute_of_mk_commute hK hsS hxhS ?_ hcop.symm hso
    rw [hsz]
    exact hzx.symm
  obtain ⟨P, j, hP, hPD⟩ := exists_normal_form_det_one hτ hτ1 h3 hxh3m hdet hxhs
  set D : Matrix (Fin 3) (Fin 3) K := diagonal ![τ, τ ^ 2, 1] with hD
  set Y : Matrix (Fin 3) (Fin 3) K := τ ^ (j : ℕ) • (xh : Matrix (Fin 3) (Fin 3) K) with hY
  set Q := P⁻¹ with hQ
  have hPdet : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).mp hP
  have hPQ : P * Q = 1 := Matrix.mul_nonsing_inv P hPdet
  have hQP : Q * P = 1 := Matrix.nonsing_inv_mul P hPdet
  have hsY : (s : Matrix (Fin 3) (Fin 3) K) * Y = Y * s := by
    have h := congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K)) hsx
    simp only [Units.val_mul] at h
    rw [hY, Matrix.mul_smul, Matrix.smul_mul, h]
  set N := Q * (s : Matrix (Fin 3) (Fin 3) K) * P with hN
  have hND : N * D = D * N := conj_commute hPQ hQP hPD hsY
  have hNdiag := eq_diagonal_of_commute hτ hτ1 hND
  have hNk : N ^ 2 ^ k = 1 := by
    rw [hN, conj_pow hPQ hQP, ← Units.val_pow_eq_pow_val, hsk, Units.val_one, Matrix.mul_one,
      hQP]
  have hN1 : N = 1 := by
    rw [hNdiag, ← Matrix.diagonal_one]
    congr 1
    funext i
    apply eq_one_of_pow_two_pow hK (k := k)
    have h := congrFun (congrFun hNk i) i
    rw [hNdiag, diagonal_pow, diagonal_apply_eq, Matrix.one_apply_eq] at h
    exact h
  have hs1 : s = 1 := by
    apply Units.ext
    rw [Units.val_one]
    calc (s : Matrix (Fin 3) (Fin 3) K) = P * N * Q := by rw [hN, unconj hPQ]
      _ = 1 := by rw [hN1, Matrix.mul_one, hPQ]
  rw [← hsz, hs1, map_one]

theorem eq_one_of_commute_of_pow_two_pow' {X : Type} [Group X] {f : ℕ} (hf : 1 ≤ f)
    (hiso : Sec4.IsoLThreePi X 2 f) (h9 : ¬ (2 ^ f % 9 = 1 ∨ 2 ^ f % 9 = 8)) {x z : X}
    (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1) (hzx : z * x = x * z) {k : ℕ} (hz : z ^ 2 ^ k = 1) :
    z = 1 := by
  obtain ⟨π, K, _, hK, hq, ⟨φ⟩⟩ := Sec13.exists_projImage_model hf hiso
  have h9K := Sec16.not_nine_dvd_card_sub_one hK h9
  set S := projImage (slPi π 3 (2 ^ f) K) with hS
  set ψ : X →* ProjGenLinGroup (Fin 3) K := S.subtype.comp φ.toMonoidHom with hψ
  have hψinj : Function.Injective ψ := Subtype.val_injective.comp φ.injective
  apply hψinj
  rw [map_one]
  refine eq_one_of_commute_of_pow_two_pow hK hq h9K (φ x).2 (φ z).2 ?_ ?_ ?_ (k := k) ?_
  · change ψ x ^ 3 = 1
    rw [← map_pow, hx3, map_one]
  · change ψ x ≠ 1
    intro h
    exact hx1 (hψinj (h.trans (map_one ψ).symm))
  · change ψ z * ψ x = ψ x * ψ z
    rw [← map_mul, hzx, map_mul]
  · rw [← map_pow, hz, map_one]

end Model

section GroupTheory

variable {G : Type} [Group G]

variable [Finite G]

theorem le_of_le_sup_of_odd {S N X : Subgroup G} (hS2 : IsPGroup 2 S) (hX : ¬ 2 ∣ Nat.card X)
    (hSN : S ≤ Subgroup.normalizer (N : Set G)) (hXN : X ≤ Subgroup.normalizer (N : Set G))
    (hSX : S ≤ N ⊔ X) : S ≤ N := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 := Sec6.card_sup_mul_card_inf hSN
  have h2 := Sec6.card_sup_mul_card_inf hXN
  have hle : S ⊔ N ≤ X ⊔ N := sup_le (hSX.trans (sup_comm N X).le) le_sup_right
  have hd : Nat.card (S ⊔ N : Subgroup G) ∣ Nat.card (X ⊔ N : Subgroup G) :=
    Subgroup.card_dvd_of_le hle
  obtain ⟨r, hr⟩ : Nat.card N ∣ Nat.card (S ⊔ N : Subgroup G) :=
    Subgroup.card_dvd_of_le le_sup_right
  obtain ⟨r', hr'⟩ : Nat.card N ∣ Nat.card (X ⊔ N : Subgroup G) :=
    Subgroup.card_dvd_of_le le_sup_right
  have hN0 : 0 < Nat.card N := Nat.card_pos
  have hrS : r * Nat.card (S ⊓ N : Subgroup G) = Nat.card S := by
    rw [hr, mul_assoc] at h1
    have := Nat.eq_of_mul_eq_mul_left hN0 (h1.trans (mul_comm _ _))
    exact this
  have hrX : r' * Nat.card (X ⊓ N : Subgroup G) = Nat.card X := by
    rw [hr', mul_assoc] at h2
    exact Nat.eq_of_mul_eq_mul_left hN0 (h2.trans (mul_comm _ _))
  have hrr' : r ∣ r' := by
    rw [hr, hr'] at hd
    exact (Nat.mul_dvd_mul_iff_left hN0).mp hd
  have hr'X : r' ∣ Nat.card X := ⟨_, hrX.symm⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hS2
  have hrS' : r ∣ 2 ^ n := hn ▸ ⟨_, hrS.symm⟩
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hrS'
  have hr1 : r = 1 := by
    rcases i with _ | i
    · simpa using hi
    · exfalso
      apply hX
      rw [hi] at hrr'
      exact (dvd_pow_self 2 (Nat.succ_ne_zero i)).trans (hrr'.trans hr'X)
  have hcard : Nat.card (S ⊔ N : Subgroup G) = Nat.card N := by rw [hr, hr1, mul_one]
  have heq : N = S ⊔ N := Subgroup.eq_of_le_of_card_ge le_sup_right hcard.le
  rw [heq]
  exact le_sup_left

theorem le_of_forall_inf_centralizer_le {S E M : Subgroup G} (hS2 : IsPGroup 2 S)
    (hE : CFSG.Assembly.IsElemAbelian 3 E) (hE9 : Nat.card E = 9)
    (hES : E ≤ Subgroup.normalizer (S : Set G))
    (h : ∀ e ∈ E, e ≠ 1 → S ⊓ Subgroup.centralizer ({e} : Set G) ≤ M) : S ≤ M := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : IsMulCommutative E := hE.1
  let : CommGroup E := IsMulCommutative.instCommGroup
  have hE3 : IsPGroup 3 E := IsPGroup.of_card (n := 2) (by rw [hE9]; norm_num)
  have : Fact (IsPGroup 3 E) := ⟨hE3⟩
  have : Subgroup.Normalizes E S := ⟨hES⟩
  have hcop : Nat.Coprime 3 (Nat.card S) := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hS2
    rw [hn]
    exact Nat.Coprime.pow_right _ (by norm_num)
  have hncyc : ¬ IsCyclic E := by
    intro hcyc
    have hexp := IsCyclic.exponent_eq_card (α := E)
    have hdvd : Monoid.exponent E ∣ 3 := Monoid.exponent_dvd_of_forall_pow_eq_one fun x =>
      Subtype.ext (by simpa using hE.2 x x.2)
    rw [hexp, hE9] at hdvd
    norm_num at hdvd
  have hsup := CFSG.iSup_fixedPointSubgroup_zpowers_eq_top_of_noncyclic_abelian_pGroup_action
    (G := S) (A := E) 3 hcop hncyc
  intro s hs
  have hmem : (⟨s, hs⟩ : S) ∈ (⨆ (a : E) (_ : a ≠ 1),
      CFSG.fixedPointSubgroup (↥(Subgroup.zpowers a)) S) := by
    rw [hsup]
    exact Subgroup.mem_top _
  have hle : (⨆ (a : E) (_ : a ≠ 1), CFSG.fixedPointSubgroup (↥(Subgroup.zpowers a)) S) ≤
      M.subgroupOf S := by
    refine iSup₂_le fun a ha => ?_
    have hfix : CFSG.fixedPointSubgroup (↥(Subgroup.zpowers a)) S =
        (CFSG.elementCentralizerIn S (a : G)).subgroupOf S := by
      simpa using CFSG.fixedPointSubgroup_zpowers_subgroup_conj_eq_elementCentralizerIn
        (K := S) (R := E) hES a
    rw [hfix]
    intro x hx
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact h a a.2 (fun h1 => ha (Subtype.ext h1)) hx
  exact Subgroup.mem_subgroupOf.mp (hle hmem)

end GroupTheory

end Proof1513Res3

open CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank
  CFSG.GH74.GLS

end CFSG.RankThree.PartTwo.Sec15
