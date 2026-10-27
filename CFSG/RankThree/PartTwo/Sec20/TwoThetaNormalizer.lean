module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Foundations.Basic
import CFSG.RankThree.PartTwo.Sec20.TwoThetaNorm
import CFSG.Quasithin.Vol2.Ch11SecFO2L
import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.RankThree.PartTwo.Sec20

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL)
open scoped commutatorElement

section A4

variable {G : Type} [Group G] [Finite G]

theorem TwoTheta.mem_of_mul_pow_eq_one {Q : Type*} [Group Q] [Finite Q] {A B : Subgroup Q}
    (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) (hB : ¬ 3 ∣ Nat.card B) {a b : Q} (ha : a ∈ A)
    (hb : b ∈ B) {k : ℕ} (h : (a * b) ^ 3 ^ k = 1) : b ∈ A := by
  have hc : Commute a b := hAB a ha b hb
  rw [hc.mul_pow] at h
  have h1 : b ^ 3 ^ k = (a ^ 3 ^ k)⁻¹ := eq_inv_of_mul_eq_one_right h
  have h2 : b ^ 3 ^ k ∈ A := by rw [h1]; exact A.inv_mem (A.pow_mem ha _)
  have hord : Nat.Coprime (3 ^ k) (orderOf b) := by
    refine Nat.Coprime.pow_left k ?_
    rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_three]
    intro hd
    apply hB
    refine hd.trans ?_
    have h4 : orderOf (⟨b, hb⟩ : B) ∣ Nat.card B := orderOf_dvd_natCard _
    rwa [Subgroup.orderOf_mk] at h4
  obtain ⟨u, v, huv⟩ := Nat.isCoprime_iff_coprime.mpr hord
  have h5 : b = (b ^ 3 ^ k) ^ u := by
    calc b = b ^ (1 : ℤ) := (zpow_one b).symm
      _ = b ^ (u * ((3 ^ k : ℕ) : ℤ) + v * (orderOf b : ℤ)) := by rw [← huv]
      _ = (b ^ 3 ^ k) ^ u := by
        rw [zpow_add, mul_comm u, zpow_mul, zpow_natCast, mul_comm v, zpow_mul, zpow_natCast,
          pow_orderOf_eq_one, one_zpow, mul_one]
  rw [h5]
  exact A.zpow_mem h2 u

open scoped Pointwise in
theorem TwoTheta.mem_sup_pCoreOf_of_pow_eq_one {L Θ : Subgroup G}
    (hLΘ : L ≤ Subgroup.normalizer (Θ : Set G)) (h3 : Nat.Coprime 3 (Nat.card Θ))
    (hc : ⁅L, Θ⁆ ≤ CFSG.Open.pCoreOf 2 Θ) {u : G} (hu : u ∈ L ⊔ Θ) {k : ℕ}
    (huk : u ^ 3 ^ k = 1) : u ∈ L ⊔ CFSG.Open.pCoreOf 2 Θ := by
  set R := CFSG.Open.pCoreOf 2 Θ with hR
  have hu' : u ∈ (L : Set G) * (Θ : Set G) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right L Θ hLΘ]
    exact hu
  obtain ⟨l, hl, θ, hθ, rfl⟩ := Set.mem_mul.mp hu'
  set N : Subgroup G := Subgroup.normalizer (R : Set G) with hN
  have hLN : L ≤ N := hLΘ.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 Θ)
  have hΘN : Θ ≤ N := CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Θ
  have hRN : R ≤ N := Subgroup.le_normalizer
  haveI : (R.subgroupOf N).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hRN).mpr le_rfl
  set f : ↥N →* ↥N ⧸ R.subgroupOf N := QuotientGroup.mk' (R.subgroupOf N) with hf
  have hcomm : ∀ a ∈ (L.subgroupOf N).map f, ∀ b ∈ (Θ.subgroupOf N).map f, a * b = b * a := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul, hf, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq]
    have hx' : (x : G) ∈ L := Subgroup.mem_subgroupOf.mp hx
    have hy' : (y : G) ∈ Θ := Subgroup.mem_subgroupOf.mp hy
    rw [Subgroup.mem_subgroupOf]
    have h1 : (((x * y)⁻¹ * (y * x) : ↥N) : G) = ⁅(y : G)⁻¹, (x : G)⁻¹⁆ := by
      simp [commutatorElement_def, mul_assoc]
    rw [h1]
    refine hc ?_
    rw [← Subgroup.commutator_comm]
    exact Subgroup.commutator_mem_commutator (Θ.inv_mem hy') (L.inv_mem hx')
  have hB : ¬ 3 ∣ Nat.card ((Θ.subgroupOf N).map f) := by
    intro hd
    have h1 : Nat.card ((Θ.subgroupOf N).map f) ∣ Nat.card (Θ.subgroupOf N) :=
      Subgroup.card_map_dvd _ _
    have h2 : Nat.card (Θ.subgroupOf N) = Nat.card Θ :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hΘN).toEquiv
    rw [h2] at h1
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp h3 (hd.trans h1)
  set lN : ↥N := ⟨l, hLN hl⟩ with hlN
  set θN : ↥N := ⟨θ, hΘN hθ⟩ with hθN
  have hlA : f lN ∈ (L.subgroupOf N).map f := ⟨lN, Subgroup.mem_subgroupOf.mpr hl, rfl⟩
  have hθB : f θN ∈ (Θ.subgroupOf N).map f := ⟨θN, Subgroup.mem_subgroupOf.mpr hθ, rfl⟩
  have hpow : (f lN * f θN) ^ 3 ^ k = 1 := by
    rw [← map_mul, ← map_pow]
    have : (lN * θN) ^ 3 ^ k = 1 := Subtype.ext (by simpa using huk)
    rw [this, map_one]
  obtain ⟨y, hy, hyθ⟩ := TwoTheta.mem_of_mul_pow_eq_one hcomm hB hlA hθB hpow
  have h1 := Subgroup.mem_subgroupOf.mp (QuotientGroup.eq.mp hyθ)
  have hyL : (y : G) ∈ L := Subgroup.mem_subgroupOf.mp hy
  have h2 : l * θ = (l * y) * ((y : G)⁻¹ * θ) := by group
  rw [h2]
  exact Subgroup.mul_mem_sup (L.mul_mem hl hyL) (by simpa using h1)

theorem le_normalizer_of_comm_theta (L Y : Subgroup G)
    (hLY : L ≤ Subgroup.normalizer (Y : Set G)) (hLL : ⁅L, L⁆ = L)
    (hq : Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* projSL 3 (GaloisField 2 2)))
    (h1 : ⁅L, Y⁆ ≤ inSubgroup (CFSG.pPrimeCore 3) Y)
    (h2 : ⁅L, inSubgroup (CFSG.pPrimeCore 3) Y⁆ ≤
      CFSG.Open.pCoreOf 2 (inSubgroup (CFSG.pPrimeCore 3) Y))
    (h3 : CFSG.Open.pCoreOf 2 Y ≤ Subgroup.normalizer (L : Set G)) :
    Y ≤ Subgroup.normalizer (L : Set G) := by
  obtain ⟨e⟩ := hq
  haveI : Group.IsPerfect ↥L := by
    refine ⟨?_⟩
    apply Subgroup.map_injective L.subtype_injective
    rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype, hLL]
  set Θ := inSubgroup (CFSG.pPrimeCore 3) Y with hΘ
  set R := CFSG.Open.pCoreOf 2 Θ with hR
  have hΘY : Θ ≤ Y := Subgroup.map_subtype_le _
  have hnorm : Subgroup.normalizer (Y : Set G) ≤ Subgroup.normalizer (Θ : Set G) :=
    CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic
      (CFSG.pPrimeCore 3 ↥Y)
  have hYΘ : Y ≤ Subgroup.normalizer (Θ : Set G) := Subgroup.le_normalizer.trans hnorm
  have hLΘ : L ≤ Subgroup.normalizer (Θ : Set G) := hLY.trans hnorm
  have h3Θ : Nat.Coprime 3 (Nat.card Θ) := by
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have h := CFSG.pPrimeCore_coprime_card (p := 3) (G := ↥Y)
    rwa [← Subgroup.card_map_of_injective Y.subtype_injective] at h
  have hR2 : IsPGroup 2 R := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Θ
  have hYR : Y ≤ Subgroup.normalizer (R : Set G) :=
    hYΘ.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 Θ)
  have hRY : R ≤ CFSG.Open.pCoreOf 2 Y :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 Θ).trans hΘY) hYR hR2
  have hRL : R ≤ Subgroup.normalizer (L : Set G) := hRY.trans h3
  intro y hy
  have hgen : ∀ x ∈ L, y * x * y⁻¹ ∈ L ⊔ R := by
    let T : Subgroup ↥L := (L ⊔ R).comap ((MulAut.conj y).toMonoidHom.comp L.subtype)
    have hT : T = ⊤ := TwoTheta.eq_top_of_threeElements_subset e (by
      rintro x ⟨k, hk⟩
      show y * (x : G) * y⁻¹ ∈ L ⊔ R
      have hxk : (y * (x : G) * y⁻¹) ^ 3 ^ k = 1 := by
        have : (x : G) ^ 3 ^ k = 1 := by simpa using congrArg Subtype.val hk
        rw [conj_pow, this]
        simp
      have hcomm : ⁅y, (x : G)⁆ ∈ Θ := by
        apply h1
        rw [Subgroup.commutator_comm]
        exact Subgroup.commutator_mem_commutator hy x.2
      have hmem : y * (x : G) * y⁻¹ ∈ L ⊔ Θ := by
        have : y * (x : G) * y⁻¹ = ⁅y, (x : G)⁆ * x := by
          simp [commutatorElement_def]
        rw [this, sup_comm]
        exact Subgroup.mul_mem_sup hcomm x.2
      exact TwoTheta.mem_sup_pCoreOf_of_pow_eq_one hLΘ h3Θ h2 hmem hxk)
    intro x hx
    have hx' : (⟨x, hx⟩ : ↥L) ∈ T := hT ▸ Subgroup.mem_top _
    exact hx'
  have hperf : ⁅L.map (MulAut.conj y).toMonoidHom, L.map (MulAut.conj y).toMonoidHom⁆ =
      L.map (MulAut.conj y).toMonoidHom := by
    rw [← Subgroup.map_commutator, hLL]
  have hle : L.map (MulAut.conj y).toMonoidHom ≤ L :=
    Quasithin.Vol2.Ch11.SecF.le_of_le_sup_of_perfect hperf hR2 hRL (by
      rintro _ ⟨x, hx, rfl⟩
      exact hgen x hx)
  have heq : L.map (MulAut.conj y).toMonoidHom = L :=
    Subgroup.eq_of_le_of_card_ge hle (by
      rw [Subgroup.card_map_of_injective (MulAut.conj y).injective])
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr heq


end A4

end CFSG.RankThree.PartTwo.Sec20
