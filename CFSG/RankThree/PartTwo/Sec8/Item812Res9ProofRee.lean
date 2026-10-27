module

public import CFSG.RankThree.PartTwo.Sec8.Item812Res8ProofJTwo
import CFSG.RankThree.PartTwo.Sec8.Item812Res8ProofSp4
import CFSG.RankThree.PartTwo.Sec8.Item812Res8ProofOmegaD4
import CFSG.RankThree.PartTwo.Sec8.Item87Res2ProofUnitary
import CFSG.RankThree.PartTwo.KFacts.K71Item89
import CFSG.RankThree.PartTwo.Sec21.ReeF4Cent2Proof
import CFSG.RankThree.PartOne.S11c.Sec66F4ReeK1
import CFSG.SignalizerFunctorTheorem.CatalogBridge.TitsDerived

public section

namespace CFSG.RankThree.PartTwo.Sec8

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
open CFSG.LieType.Simplicity.TitsBits CFSG.SignalizerFunctorTheorem.CatalogBridge

namespace Item812Res9

private def powBits (P : ℕ) : ℕ → ℕ
  | 0 => oneBits
  | n + 1 => mul P (powBits P n)

private def titsSixWord : List ℤ := [-4, -3, 4, -1, 3]

private theorem titsSix_letters : ∀ l ∈ titsSixWord, GoodLetter l := by decide

private theorem titsSix_even : Even (letterCount 2 titsSixWord) ∧ Even (letterCount 3 titsSixWord) ∧
    Even (letterCount 4 titsSixWord) := by decide

private theorem titsSix_pow_six :
    powBits (wordPair titsSixWord).1 6 % 2 ^ 2704 = oneBits % 2 ^ 2704 := by decide +kernel

private theorem titsSix_pow_two_ne :
    powBits (wordPair titsSixWord).1 2 % 2 ^ 2704 ≠ oneBits % 2 ^ 2704 := by decide +kernel

private theorem titsSix_pow_three_ne :
    powBits (wordPair titsSixWord).1 3 % 2 ^ 2704 ≠ oneBits % 2 ^ 2704 := by decide +kernel

theorem mem_normalizer_zpowers_of_commute {D : Type*} [Group D] {y t : D} (h : Commute t y) :
    y ∈ Subgroup.normalizer ((Subgroup.zpowers t : Subgroup D) : Set D) := by
  refine Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun h' hh' => ?_)
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh'
  exact (h.zpow_left j).eq

theorem zpowers_ne_bot_isPGroup_two {D : Type*} [Group D] {t : D} (ht1 : t ≠ 1)
    (ht2 : t ^ 2 = 1) : Subgroup.zpowers t ≠ ⊥ ∧ IsPGroup 2 (Subgroup.zpowers t) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨fun h => ht1 (Subgroup.zpowers_eq_bot.mp h), IsPGroup.of_card (n := 1) ?_⟩
  rw [Nat.card_zpowers, orderOf_eq_prime ht2 ht1, pow_one]

section Model


variable {k : Type} [Field k] [Finite k] [CharP k ReeTag.F4.prime]

omit [Finite k] in
private theorem hasBits_pow {x : adjointGroup ReeTag.F4.tag k} {P : ℕ} (hx : HasBits k x P) :
    ∀ n : ℕ, HasBits k (x ^ n) (powBits P n)
  | 0 => by simpa [powBits] using (hasBits_one (K := k))
  | n + 1 => by
    rw [pow_succ']
    exact hasBits_mul_prime hx (hasBits_pow hx n)

private theorem twoLocalThree_tits (hk : Nat.card k = 2) :
    TwoLocalThree (commutator (reeFixed ReeTag.F4 k 0)) := by
  have : CharP k 2 := ‹CharP k ReeTag.F4.prime›
  set R := reeFixed ReeTag.F4 k 0 with hR
  set D := commutator R with hD
  have hT := CFSG.LieType.Simplicity.titsData k hk
  set x : R := gWordG k titsSixWord with hx
  have hxD : x ∈ D := gWordG_mem_commutator_of_even _ titsSix_letters titsSix_even.1
    titsSix_even.2.1 titsSix_even.2.2
  have hpow := hasBits_pow (hasBits_gWordG (K := k) titsSixWord titsSix_letters).1
  have hval : ∀ n : ℕ, ((x ^ n : R) : adjointGroup ReeTag.F4.tag k) = 1 ↔
      powBits (wordPair titsSixWord).1 n % 2 ^ 2704 = oneBits % 2 ^ 2704 := fun n => by
    rw [Subgroup.coe_pow]
    exact (hpow n).eq_iff hasBits_one
  have h6 : x ^ 6 = 1 := Subtype.ext ((hval 6).mpr titsSix_pow_six)
  have h2 : x ^ 2 ≠ 1 := fun h => titsSix_pow_two_ne ((hval 2).mp (by rw [h]; rfl))
  have h3 : x ^ 3 ≠ 1 := fun h => titsSix_pow_three_ne ((hval 3).mp (by rw [h]; rfl))
  set X : D := ⟨x, hxD⟩ with hXdef
  have hXpow : ∀ n : ℕ, ((X ^ n : D) : R) = x ^ n := fun n => by rw [Subgroup.coe_pow]
  have hX6 : X ^ 6 = 1 := Subtype.ext (by rw [hXpow, h6]; rfl)
  have hX2 : X ^ 2 ≠ 1 := fun h => h2 (by rw [← hXpow, h]; rfl)
  have hX3 : X ^ 3 ≠ 1 := fun h => h3 (by rw [← hXpow, h]; rfl)
  have hy3 : (X ^ 2) ^ 3 = 1 := by rw [← pow_mul]; exact hX6
  have ht2 : (X ^ 3) ^ 2 = 1 := by rw [← pow_mul]; exact hX6
  have hyord : orderOf (X ^ 2) = 3 := orderOf_eq_prime hy3 hX2
  have hsimple : ∀ N : Subgroup D, N.Normal → N = ⊥ ∨ N = ⊤ := by
    intro N hN
    rcases hT.eq_bot_or_eq_of_le hk (N.map D.subtype) (Subgroup.map_subtype_le N)
        (by
          rintro d hd _ ⟨m, hm, rfl⟩
          exact ⟨⟨d, hd⟩ * m * ⟨d, hd⟩⁻¹, hN.conj_mem m hm ⟨d, hd⟩, rfl⟩) with h | h
    · exact Or.inl ((Subgroup.map_eq_bot_iff_of_injective _ D.subtype_injective).mp h)
    · right
      rw [eq_top_iff]
      intro m _
      have hm : (m : R) ∈ N.map D.subtype := by rw [h]; exact m.2
      obtain ⟨m₁, hm₁, he⟩ := hm
      rwa [show m = m₁ from Subtype.ext he.symm]
  have hZ : Subgroup.center D = ⊥ := by
    rcases hsimple (Subgroup.center D) inferInstance with h | h
    · exact h
    · exfalso
      obtain ⟨u, hu, v, hv, huv⟩ := hT.nonabelian
      have hmem : (⟨u, hu⟩ : D) ∈ Subgroup.center D := by rw [h]; exact Subgroup.mem_top _
      exact huv (congrArg Subtype.val ((Subgroup.mem_center_iff.mp hmem) ⟨v, hv⟩)).symm
  refine ⟨?_, X ^ 2, Subgroup.zpowers (X ^ 3), hy3, ?_,
    (zpowers_ne_bot_isPGroup_two hX3 ht2).1, (zpowers_ne_bot_isPGroup_two hX3 ht2).2,
    mem_normalizer_zpowers_of_commute (Commute.pow_pow_self X 3 2)⟩
  · intro N hN _ hN3
    rcases hsimple N hN with h | h
    · exact h
    · exfalso
      apply hN3
      rw [h, Subgroup.card_top, ← hyord]
      exact orderOf_dvd_natCard _
  · rw [hZ, Subgroup.mem_bot]
    exact hX2

theorem twoLocalThree_reeGamma_of_one_le {b : ℕ} (hb : 1 ≤ b)
    (hk : Nat.card k = 2 ^ (2 * b + 1)) : TwoLocalThree (ReeTag.F4.reeGamma k b) := by
  set Γ := ReeTag.F4.reeGamma k b with hΓ
  have : IsSimpleGroup Γ := CFSG.RankThree.PartOne.Sec66T.isSimpleGroup_reeGamma_F4' hb hk
  have hZ : Subgroup.center Γ = ⊥ := ReeTag.large_Ree_fixed_group_center_trivial b k hk
  obtain ⟨y, hy3, hiso⟩ := ReeF4Cent2Proof.reeF4CentThreeSome_holds b k hb hk
  have h3 : 3 ∣ Nat.card Γ := hy3 ▸ orderOf_dvd_natCard y
  set C := inSubgroup perfectResidual (Subgroup.centralizer ({y} : Set Γ)) with hC
  have hC2 : 2 ∣ Nat.card C := by
    rw [Item812Res8.card_of_isoSUThree hiso]
    refine Dvd.dvd.mul_right (Dvd.dvd.mul_right ?_ _) _
    exact dvd_pow (dvd_pow_self 2 (by omega)) (by norm_num)
  have : Finite Γ := Subtype.finite
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨t', ht'⟩ := exists_prime_orderOf_dvd_card' 2 hC2
  set t : Γ := (t' : Γ) with htdef
  have htord : orderOf t = 2 := by rw [htdef, Subgroup.orderOf_coe, ht']
  have ht1 : t ≠ 1 := by
    intro h
    rw [h, orderOf_one] at htord
    omega
  have ht2 : t ^ 2 = 1 := by rw [← htord]; exact pow_orderOf_eq_one t
  have htC : t ∈ Subgroup.centralizer ({y} : Set Γ) := Subgroup.map_subtype_le _ t'.2
  have hty : Commute t y := Subgroup.mem_centralizer_singleton_iff.mp htC
  refine ⟨Item812Res8.noThetaNormal_of_isSimpleGroup h3, y, Subgroup.zpowers t, ?_, ?_,
    (zpowers_ne_bot_isPGroup_two ht1 ht2).1, (zpowers_ne_bot_isPGroup_two ht1 ht2).2,
    mem_normalizer_zpowers_of_commute hty⟩
  · rw [← hy3]
    exact pow_orderOf_eq_one y
  · rw [hZ, Subgroup.mem_bot]
    intro h
    rw [h, orderOf_one] at hy3
    omega

end Model

end Item812Res9


open Item812Res9 in
theorem kF89ReeTwoLocal_holds : KF89ReeTwoLocal := by
  intro b k _ _ _ hk
  rcases Nat.eq_zero_or_pos b with rfl | hb
  · have hk2 : Nat.card k = 2 := by simpa using hk
    set R := reeFixed ReeTag.F4 k 0 with hR
    set eR : R ≃* ReeTag.F4.reeGamma k 0 := ReeTag.reeFixedEquivReeGamma k 0
    have hT := CFSG.LieType.Simplicity.titsData k hk2
    have hperf : Group.IsPerfect (commutator R) := hT.isPerfect hk2
    have heq : perfectResidual R = commutator R :=
      le_antisymm (Item812Res8.perfectResidual_le_commutator R)
        (Item87Res2Proof.le_perfectResidual_of_isPerfect hperf)
    exact TwoLocalThree.of_mulEquiv
      ((Item812Res8.perfectResidualCongr eR).symm.trans (MulEquiv.subgroupCongr heq))
      (twoLocalThree_tits hk2)
  · have hperf : Group.IsPerfect (ReeTag.F4.reeGamma k b) :=
      ⟨ReeTag.commutator_reeGamma_eq_top (t := ReeTag.F4) hb hk⟩
    have htop := KFacts.perfectResidual_eq_top_of_isPerfect hperf
    exact TwoLocalThree.of_mulEquiv ((MulEquiv.subgroupCongr htop).trans Subgroup.topEquiv)
      (twoLocalThree_reeGamma_of_one_le hb hk)

end CFSG.RankThree.PartTwo.Sec8
