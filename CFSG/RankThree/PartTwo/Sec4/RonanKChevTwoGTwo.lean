module

public import CFSG.RankThree.PartTwo.Sec4.RonanKChevTwoBasic
public import CFSG.RankThree.Chevalley.SteinbergCEG2EvenLocalCoreIntersection
public import CFSG.RankThree.PartTwo.Sec11.KS11Lie7ProofConj
public import CFSG.RankThree.PartTwo.Sec11.KS11Lie7ProofCent

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanKChevTwo

open CFSG CFSG.RankThree.PartTwo.Sec4.Item462AltProof
open CFSG.Blueprint.Chevalley CFSG.RankThree.PartTwo.Sec11

private theorem three_dvd_two_pow_add_one {n : ℕ} (hn : Odd n) : 3 ∣ 2 ^ n + 1 := by
  obtain ⟨k, rfl⟩ := hn
  have h1 : 4 ^ k % 3 = 1 := by
    rw [Nat.pow_mod]
    norm_num
  have h2 : 2 ^ (2 * k + 1) = 2 * 4 ^ k := by
    rw [pow_succ, pow_mul]
    ring
  rw [h2]
  generalize 4 ^ k = d at h1 ⊢
  omega

private theorem four_le_two_pow {f : ℕ} (hf : 2 ≤ f) : 4 ≤ 2 ^ f :=
  calc 4 = 2 ^ 2 := by norm_num
    _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf

private theorem odd_two_pow_sq_sub_one {f : ℕ} (hf : 1 ≤ f) : Odd ((2 ^ f) ^ 2 - 1) := by
  have heven : Even ((2 ^ f) ^ 2) :=
    Nat.even_pow.mpr ⟨Nat.even_pow.mpr ⟨even_two, by omega⟩, two_ne_zero⟩
  have hpos : 1 ≤ (2 ^ f) ^ 2 := Nat.one_le_pow _ _ (by positivity)
  exact Nat.Even.sub_odd hpos heven odd_one

theorem gTwo_outer_false
    {f : ℕ} (hf : 2 ≤ f) {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2 ^ f)
    {β : MulAut (adjointGroup .G2 K)} (hβ : orderOf β = 3)
    (hout : β ∉ (MulAut.conj : adjointGroup .G2 K →* MulAut (adjointGroup .G2 K)).range) :
    ¬ PullDatum β := by
  intro h
  set B : Subgroup (MulAut (adjointGroup .G2 K)) :=
    (MulAut.conj : adjointGroup .G2 K →* MulAut (adjointGroup .G2 K)).range ⊔
      Subgroup.zpowers β
  have hInnB : (MulAut.conj : adjointGroup .G2 K →* MulAut (adjointGroup .G2 K)).range ≤ B :=
    le_sup_left
  have hβB : β ∈ B := Subgroup.mem_sup_right (Subgroup.mem_zpowers β)
  have hord : orderOf (⟨β, hβB⟩ : B) = 3 := by rw [Subgroup.orderOf_mk, hβ]
  exact h.false_of_localCore
    (conj_injective_of_center_eq_bot CFSG.LieType.Chevalley.center_adjointGroup_eq_bot) B hInnB
    le_rfl hβB
    (CFSG.RankThree.Chevalley.EvenG2.localCore_eq_bot_of_noninner hf hK Nat.prime_three hInnB
      hout hord)

private theorem conj_apply_eq_iff_mem_centralizer {G : Type*} [Group G] (z y : G) :
    MulAut.conj z y = y ↔ y ∈ Subgroup.centralizer ({z} : Set G) := by
  rw [Subgroup.mem_centralizer_singleton_iff, conj_apply_eq_iff]
  exact eq_comm

theorem gTwo_threeA_false
    {f : ℕ} (hf : 2 ≤ f) {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2 ^ f)
    (h3 : 3 ∣ Nat.card K + 1) {z : adjointGroup .G2 K} (hzS : z ∈ KS11Lie4Proof.g2ShortSL2 K)
    (hz3 : z ^ 3 = 1) (hz1 : z ≠ 1) : ¬ PullDatum (MulAut.conj z) := by
  intro h
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fintype K := Fintype.ofFinite K
  have : CharP K 2 := charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, hK])
  obtain ⟨L, _, _, _, -, hdeg, -⟩ := KS11Lie4Proof.exists_quadratic_ext' K
  have : CharP L 2 := charP_of_injective_algebraMap (algebraMap K L).injective 2
  obtain ⟨e⟩ := KS11Lie7Proof.nonempty_centralizer_mulEquiv_statedSU hK h3 hdeg hzS hz3 hz1
  have hL : Nat.card L = (2 ^ f) ^ 2 := by rw [KS11Lie4Proof.natCard_quadratic hdeg, hK]
  have hq : ((3 : ℕ), 2 ^ f) ≠ (3, 2) := by
    intro hq
    have h2 : 2 ^ f = 2 := (Prod.mk.inj hq).2
    have := four_le_two_pow hf
    omega
  obtain ⟨hSU, hZ⟩ := CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card hL le_rfl hq
  have hZcard : Nat.card (Subgroup.center (CFSG.Open.StatedSU 3 (2 ^ f) L)) =
      Nat.gcd 3 (2 ^ f + 1) := by
    rw [hZ]
    exact (CFSG.LinearGroups.unitary_scalar_kernel Nat.prime_two hL (by norm_num)).2.2
  refine h.false_of_quasisimple_fixed (Subgroup.centralizer ({z} : Set (adjointGroup .G2 K)))
    (fun x => (conj_apply_eq_iff_mem_centralizer z x).symm)
    (CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm hSU) ?_
  rw [Nat.card_congr (Subgroup.centerCongr e).toEquiv, hZcard]
  exact (by decide : Odd 3).of_dvd_nat (Nat.gcd_dvd_left 3 _)

theorem gTwo_threeB_false
    {f : ℕ} (hf : 2 ≤ f) {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2 ^ f)
    (h3 : 3 ∣ Nat.card K + 1) {z : adjointGroup .G2 K} (hzM : z ∈ KS11Lie4Proof.g2LongSL2 K)
    (hz3 : z ^ 3 = 1) (hz1 : z ≠ 1) : ¬ PullDatum (MulAut.conj z) := by
  intro h
  have h4 : 4 ≤ Nat.card K := hK ▸ four_le_two_pow hf
  obtain ⟨hcomm, hexp⟩ := KS11Lie4Proof.g2ThreeBCentMinus_holds K h3 h4 z hzM hz3 hz1
  have hSz : ∀ s ∈ KS11Lie4Proof.g2ShortSL2 K,
      s ∈ Subgroup.centralizer ({z} : Set (adjointGroup .G2 K)) := fun s hs =>
    Subgroup.mem_centralizer_singleton_iff.mpr (KS11Lie4Proof.g2Short_commute_g2Long hs hzM)
  refine h.false_of_quasisimple (KS11Lie4Proof.g2ShortSL2 K)
    (fun s hs => (conj_apply_eq_iff_mem_centralizer z s).mpr (hSz s hs)) ?_
    (KS11Lie4Proof.isQuasisimple_g2ShortSL2 h4) ?_
  · intro c hc s hs
    have hmem := hcomm c ((conj_apply_eq_iff_mem_centralizer z c).mp hc) s (hSz s hs)
    have hcs : c * s * c⁻¹ = (c * s * c⁻¹ * s⁻¹) * s := by group
    rw [hcs]
    exact mul_mem hmem hs
  · intro c hc hcS
    have hb : c ^ (Nat.card K ^ 2 - 1) = 1 :=
      hexp c ((conj_apply_eq_iff_mem_centralizer z c).mp hc)
        (Subgroup.mem_centralizer_iff.mpr fun s hs => (hcS s hs).symm)
    have hodd : Odd (Nat.card K ^ 2 - 1) := hK ▸ odd_two_pow_sq_sub_one (by omega)
    exact hodd.of_dvd_nat (orderOf_dvd_of_pow_eq_one hb)

theorem gTwo_inner_false
    {f : ℕ} (hf : 2 ≤ f) {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2 ^ f)
    (h3 : 3 ∣ Nat.card K + 1) {x : adjointGroup .G2 K} (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1) :
    ¬ PullDatum (MulAut.conj x) := by
  intro h
  have h4 : 4 ≤ Nat.card K := hK ▸ four_le_two_pow hf
  obtain ⟨g, hg⟩ := KS11Lie7Proof.g2ThreeConjSL2Minus_holds K h3 h4 x hx3 hx1
  have hz3 : (g * x * g⁻¹) ^ 3 = 1 := by rw [conj_pow, hx3, mul_one, mul_inv_cancel]
  have hz1 : g * x * g⁻¹ ≠ 1 := fun h1 => hx1 (conj_eq_one_iff.mp h1)
  rcases hg with hS | hM
  · exact gTwo_threeA_false hf hK h3 hS hz3 hz1 (h.conj_inner g)
  · exact gTwo_threeB_false hf hK h3 hM hz3 hz1 (h.conj_inner g)

theorem gTwo_not_pullDatum
    {f : ℕ} (hf : 2 ≤ f) {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2 ^ f)
    (h3 : 3 ∣ Nat.card K + 1) (β : MulAut (adjointGroup .G2 K)) (hβ : orderOf β = 3) :
    ¬ PullDatum β := by
  by_cases hin : β ∈ (MulAut.conj : adjointGroup .G2 K →* MulAut (adjointGroup .G2 K)).range
  · obtain ⟨x, rfl, hx3, hx1⟩ := exists_conj_of_isInnerAut
      (conj_injective_of_center_eq_bot CFSG.LieType.Chevalley.center_adjointGroup_eq_bot) hβ hin
    exact gTwo_inner_false hf hK h3 hx3 hx1
  · exact gTwo_outer_false hf hK hβ hin

theorem kChevTwo_gTwo
    (n : ℕ) (hn : Odd n) :
    ∀ (X : Type) [Group X] [Finite X], IsQuasisimple X →
      Blueprint.ChevalleyExceptionalModel X .G2 2 n →
        ∀ β : MulAut X, orderOf β = 3 → ¬ InnThetaNoncyclic β := by
  intro X _ _ _ hmod β hβ
  obtain ⟨hadm, K, _, _, hK, ⟨e⟩⟩ := hmod
  have hq3 : 3 ≤ 2 ^ n := hadm.2.2.2
  have hf : 2 ≤ n := by
    rcases Nat.lt_or_ge n 2 with hlt | hge
    · have : 2 ^ n ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    · exact hge
  have h3 : 3 ∣ Nat.card K + 1 := hK ▸ three_dvd_two_pow_add_one hn
  have hZK := CFSG.LieType.Chevalley.center_adjointGroup_eq_bot (τ := .G2) (K := K)
  let e' : X ≃* adjointGroup .G2 K :=
    e.trans ((QuotientGroup.quotientMulEquivOfEq hZK).trans QuotientGroup.quotientBot)
  have hZX : Subgroup.center X = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hx' : e' x ∈ Subgroup.center (adjointGroup .G2 K) := by
      rw [Subgroup.mem_center_iff] at hx ⊢
      intro g
      obtain ⟨y, rfl⟩ := e'.surjective g
      rw [← map_mul, ← map_mul, hx y]
    rw [hZK, Subgroup.mem_bot] at hx'
    rw [Subgroup.mem_bot]
    exact e'.injective (hx'.trans (map_one e').symm)
  exact not_innThetaNoncyclic_of_mulEquiv e' hZX (gTwo_not_pullDatum hf hK h3) β hβ

end CFSG.RankThree.PartTwo.Sec4.RonanKChevTwo

end
