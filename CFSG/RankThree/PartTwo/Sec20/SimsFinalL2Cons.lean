module

public import CFSG.RankThree.PartTwo.Sec20.SimsFinalL2Statements
import CFSG.RankThree.PartTwo.Sec20.Item20Res8ProofL2Z
import CFSG.RankThree.PartTwo.Sec20.Item20Res6ProofTools
public import CFSG.RankThree.PartTwo.Sec20.Item20Res7ProofL2Z

public section

namespace CFSG.RankThree.PartTwo.Sec20

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late
open CFSG.Assembly.RankThreeEven (projSL)

namespace SimsFinalL2

theorem exists_pow_coprime_orderOf_map_eq {G Q : Type*} [Group G] [Group Q] {p : ℕ}
    (hp : p.Prime) (f : G →* Q) {y : G} (hy : IsOfFinOrder y)
    (hfy : Nat.Coprime (orderOf (f y)) p) :
    ∃ n : ℕ, Nat.Coprime (orderOf (y ^ n)) p ∧ f (y ^ n) = f y := by
  set a := p ^ (orderOf y).factorization p
  have h1 : Nat.Coprime (orderOf (y ^ a)) p := by
    have hdvd : orderOf (y ^ a) ∣ orderOf y / a := by
      apply orderOf_dvd_of_pow_eq_one
      rw [← pow_mul, Nat.mul_div_cancel' (Nat.ordProj_dvd _ _), pow_orderOf_eq_one]
    exact (Nat.coprime_ordCompl hp hy.orderOf_pos.ne').symm.coprime_dvd_left hdvd
  have h2 : Nat.Coprime a (orderOf (f y)) := Nat.Coprime.pow_left _ hfy.symm
  obtain ⟨r, hr⟩ := exists_pow_eq_self_of_coprime h2
  refine ⟨a * r, ?_, ?_⟩
  · rw [pow_mul]
    exact h1.coprime_dvd_left (orderOf_pow_dvd r)
  · rw [map_pow, pow_mul, hr]

end SimsFinalL2

theorem step204FinalL2ZNe_of_threePrime (hKF : KFactL2CentThreePrime)
    (hC : Step204FinalL2CYcThreePrime) : Step204FinalL2ZNe := by
  intro G _ _ A M L N c T i j P hset X hX hXM hm hL2 hYne hYM
  obtain ⟨m, ⟨e⟩⟩ := hL2
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hCY := hC G A M L N c T i j P hset X hX hXM hm ⟨m, ⟨e⟩⟩
  set K := kTwenty M c
  set Y := yTwenty X c
  set R := CFSG.Open.pCoreOf 2 (K ⊔ T)
  set W := Y ⊔ R
  set O' := oThreePrimeYR M X T c
  set π := QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥W) with hπ
  have hKX : K ≤ X := fun x hx => hX.2 (Subgroup.mem_sup_left hx)
  have hKY : K ≤ Y := Res6.kTwenty_le_yTwenty hset hKX
  have hYW : Y ≤ W := le_sup_left
  have hKW : K ≤ W := hKY.trans hYW
  have hcK : c ∈ K := self_mem_normalClosureIn M c
  have hcY : c ∈ Y := hKY hcK
  have hc := Res6.orderOf_c_of_setting204 hset
  have hO'W : W ≤ Subgroup.normalizer (O' : Set G) :=
    Res6.le_normalizer_inSubgroup_pPrimeCore 3 W
  have hO'3 : Nat.Coprime 3 (Nat.card O') := Res6.coprime_card_inSubgroup_pPrimeCore 3 W
  have hker : ∀ w : ↥W, π w = 1 ↔ (w : G) ∈ O' := by
    intro w
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    constructor
    · intro h
      exact ⟨w, h, rfl⟩
    · rintro ⟨w', hw', hww'⟩
      rwa [← Subtype.ext hww']
  have hCYK : ∀ y ∈ Y ⊓ Subgroup.centralizer ({c} : Set G), Nat.Coprime (orderOf y) 3 →
      y ∈ K ⊔ O' := fun y hy hy3 => sup_le hYM le_sup_right (hCY y hy hy3)
  have hKO' : K ≤ Subgroup.normalizer (O' : Set G) := hKW.trans hO'W
  have hφmem : ∀ k : ↥K, π ⟨k, hKW k.2⟩ ∈ yAlpha M X T c := fun k =>
    ⟨⟨k, hKW k.2⟩, Subgroup.mem_subgroupOf.mpr (hKY k.2), rfl⟩
  let φ : ↥K →* ↥(yAlpha M X T c) :=
    (π.comp (Subgroup.inclusion hKW)).codRestrict (yAlpha M X T c) hφmem
  have hφ : ∀ k : ↥K, ((φ k : ↥(yAlpha M X T c)) : ↥W ⧸ CFSG.pPrimeCore 3 ↥W) =
      π ⟨k, hKW k.2⟩ := fun k => rfl
  let ψ : ↥K →* ↥(projSL 2 (GaloisField 2 m)) := e.toMonoidHom.comp φ
  set H := ψ.range with hH
  have hpre : ∀ y : G, ∀ hy : y ∈ Y, ∀ k : ↥K,
      π ⟨y, hYW hy⟩ = π ⟨k, hKW k.2⟩ → y ∈ K ⊔ O' := by
    intro y hy k hk
    have h1 : π (⟨k, hKW k.2⟩⁻¹ * ⟨y, hYW hy⟩) = 1 := by
      rw [map_mul, map_inv, hk, inv_mul_cancel]
    rw [hker] at h1
    have h2 : (k : G)⁻¹ * y ∈ O' := by simpa using h1
    have : y = (k : G) * ((k : G)⁻¹ * y) := by group
    rw [this]
    exact Subgroup.mul_mem_sup k.2 h2
  have hperfK : Group.IsPerfect ↥K := isPerfect_of_mem_oTwoComponentsIn hset.mem_oTwoComponentsIn
  have hHperf : ⁅H, H⁆ = H := by
    rw [hH, ← map_commutator_eq, hperfK.commutator_eq_top, Subgroup.map_top]
  have hHtop : H ≠ ⊤ := by
    intro htop
    apply hYne
    intro y hy
    have hw : π ⟨y, hYW hy⟩ ∈ yAlpha M X T c :=
      ⟨⟨y, hYW hy⟩, Subgroup.mem_subgroupOf.mpr hy, rfl⟩
    have hz : e ⟨_, hw⟩ ∈ H := by rw [htop]; exact Subgroup.mem_top _
    obtain ⟨k, hk⟩ := hz
    have h1 : φ k = ⟨_, hw⟩ := e.injective hk
    have h2 : π ⟨k, hKW k.2⟩ = π ⟨y, hYW hy⟩ := by
      rw [← hφ k, h1]
    exact hpre y hy k h2.symm
  set x := ψ ⟨c, hcK⟩ with hx
  have hxH : x ∈ H := ⟨⟨c, hcK⟩, rfl⟩
  have hc3 : c ^ 3 = 1 := by rw [← hc]; exact pow_orderOf_eq_one c
  have hcO' : c ∉ O' := by
    intro h
    have hord : orderOf (⟨c, h⟩ : O') = 3 := by rw [Subgroup.orderOf_mk, hc]
    have := orderOf_dvd_natCard (⟨c, h⟩ : O')
    rw [hord] at this
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp hO'3 this
  have hx1 : x ≠ 1 := by
    intro h1
    apply hcO'
    have h2 : φ ⟨c, hcK⟩ = 1 := e.injective (by rw [map_one]; exact h1)
    have h3 : π ⟨c, hKW hcK⟩ = 1 := by
      have := congrArg Subtype.val h2
      rw [hφ] at this
      simpa using this
    exact (hker _).mp h3
  have hx3 : x ^ 3 = 1 := by
    rw [hx, ← map_pow]
    have : (⟨c, hcK⟩ : ↥K) ^ 3 = 1 := Subtype.ext (by simpa using hc3)
    rw [this, map_one]
  have hxord : orderOf x = 3 := orderOf_eq_prime hx3 hx1
  have hO'leW : O' ≤ W := Res6.inSubgroup_pPrimeCore_le 3 W
  have hcent : ∀ z ∈ Subgroup.centralizer ({x} : Set ↥(projSL 2 (GaloisField 2 m))),
      Nat.Coprime (orderOf z) 3 → z ∈ H := by
    intro z hz hz3
    rw [Subgroup.mem_centralizer_singleton_iff] at hz
    set w := e.symm z
    have hwz : e w = z := e.apply_symm_apply z
    have hw3 : Nat.Coprime (orderOf (w : ↥W ⧸ CFSG.pPrimeCore 3 ↥W)) 3 := by
      rwa [Subgroup.orderOf_coe, ← MulEquiv.orderOf_eq e, hwz]
    have hwc : w * φ ⟨c, hcK⟩ = φ ⟨c, hcK⟩ * w := by
      apply e.injective
      rw [map_mul, map_mul, hwz]
      exact hz
    have hwc' : (w : ↥W ⧸ CFSG.pPrimeCore 3 ↥W) * π ⟨c, hKW hcK⟩ =
        π ⟨c, hKW hcK⟩ * (w : ↥W ⧸ CFSG.pPrimeCore 3 ↥W) := by
      have h1 := congrArg Subtype.val hwc
      rw [Subgroup.coe_mul, Subgroup.coe_mul, hφ] at h1
      exact h1
    obtain ⟨⟨y, hyW⟩, hyY, hyw⟩ := w.2
    have hyY' : y ∈ Y := Subgroup.mem_subgroupOf.mp hyY
    have hcomm : π (⟨y, hyW⟩ * ⟨c, hKW hcK⟩ * ⟨y, hyW⟩⁻¹ * ⟨c, hKW hcK⟩⁻¹) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, hyw, hwc']
      group
    rw [hker] at hcomm
    have hcomm' : y * c * y⁻¹ * c⁻¹ ∈ O' := by simpa using hcomm
    obtain ⟨u, hu, y', hy', rfl⟩ := Res8.exists_mul_centralizer_of_comm_mem hcY hc hO'3
      (hYW.trans hO'W) hyY' hcomm'
    have hy'w : π ⟨y', hYW hy'.1⟩ = (w : ↥W ⧸ CFSG.pPrimeCore 3 ↥W) := by
      rw [← hyw]
      have hsplit : (⟨u * y', hyW⟩ : ↥W) = ⟨u, hO'leW hu.1⟩ * ⟨y', hYW hy'.1⟩ := rfl
      rw [hsplit, map_mul, (hker ⟨u, hO'leW hu.1⟩).mpr hu.1, one_mul]
    obtain ⟨n, hn3, hnw⟩ := SimsFinalL2.exists_pow_coprime_orderOf_map_eq Nat.prime_three π
      (isOfFinOrder_of_finite (⟨y', hYW hy'.1⟩ : ↥W)) (by rw [hy'w]; exact hw3)
    rw [hy'w] at hnw
    have hy'n3 : Nat.Coprime (orderOf (y' ^ n)) 3 := by
      rw [← Subgroup.orderOf_coe] at hn3
      exact hn3
    have hy'nK : y' ^ n ∈ ((K ⊔ O' : Subgroup G) : Set G) := hCYK _ (pow_mem hy' n) hy'n3
    rw [Subgroup.coe_mul_of_left_le_normalizer_right K O' hKO'] at hy'nK
    obtain ⟨k, hk, o, ho, hko⟩ := hy'nK
    refine ⟨⟨k, hk⟩, ?_⟩
    rw [← hwz]
    change e (φ ⟨k, hk⟩) = e w
    congr 1
    apply Subtype.ext
    rw [hφ, ← hnw]
    have hsplit : (⟨y', hYW hy'.1⟩ ^ n : ↥W) = ⟨k, hKW hk⟩ * ⟨o, hO'leW ho⟩ :=
      Subtype.ext hko.symm
    rw [hsplit, map_mul, (hker ⟨o, hO'leW ho⟩).mpr ho, mul_one]
  obtain ⟨g, hg, hg3, hgH⟩ := hKF m H hHperf hHtop x hxH hxord
  exact hgH (hcent g hg hg3)

end CFSG.RankThree.PartTwo.Sec20
