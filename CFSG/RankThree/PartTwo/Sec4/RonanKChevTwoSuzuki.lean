module

public import CFSG.RankThree.PartTwo.Sec4.RonanKChevTwoBasic
public import CFSG.RankThree.PartOne.KE.SuzukiFinal

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanKChevTwo

open CFSG CFSG.RankThree.PartTwo.Sec4.Item462AltProof

section Suzuki

open CFSG.Blueprint CFSG.LieType.Ree

theorem not_three_dvd_card_suzukiGroup {a : ℕ} {K : Type} [Field K]
    [Finite K] (hK : Nat.card K = 2 ^ (2 * a + 1)) : ¬ 3 ∣ Nat.card (suzukiGroup a K) := by
  rw [suzuki_order hK]
  have hq : 2 ^ (2 * a + 1) % 3 = 2 := by
    rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
    norm_num
  set q := 2 ^ (2 * a + 1) with hqdef
  have hq2 : q ^ 2 % 3 = 1 := by
    rw [Nat.pow_mod, hq]
  intro h
  rcases (Nat.Prime.dvd_mul Nat.prime_three).mp h with h1 | h1
  · rcases (Nat.Prime.dvd_mul Nat.prime_three).mp h1 with h2 | h2
    · omega
    · omega
  · omega

theorem isQuasisimple_suzukiGroup {b : ℕ} {k : Type} [Field k]
    [Finite k] (hb : 1 ≤ b) (hk : Nat.card k = 2 ^ (2 * b + 1)) :
    IsQuasisimple (suzukiGroup b k) := by
  obtain ⟨-, hnt, hs⟩ := suzuki_simple hb hk
  have hZ := CFSG.RankThree.PartOne.KE.suzuki_center_eq_bot hb hk
  refine (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup ?_).1
  by_contra hcon
  push Not at hcon
  obtain ⟨x, y, hxy⟩ := hnt.exists_pair_ne
  have hx : x ∈ Subgroup.center (suzukiGroup b k) :=
    Subgroup.mem_center_iff.mpr fun g => hcon g x
  have hy : y ∈ Subgroup.center (suzukiGroup b k) :=
    Subgroup.mem_center_iff.mpr fun g => hcon g y
  rw [hZ, Subgroup.mem_bot] at hx hy
  exact hxy (hx.trans hy.symm)

theorem isCyclic_of_isPGroup_suzukiGroup_zero {k : Type} [Field k]
    [Finite k] (hk : Nat.card k = 2) (U : Subgroup (suzukiGroup 0 k)) (hU : IsPGroup 2 U) :
    IsCyclic U := by
  obtain ⟨-, P, hPn, hP5, hcent, -⟩ := suzuki_two_normal_five_complement_core_trivial hk
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hPcyc : IsCyclic P := isCyclic_of_prime_card hP5
  have hAut : IsCyclic (MulAut P) := by
    have hunits : IsCyclic (ZMod (Nat.card P))ˣ := by
      rw [hP5]
      exact ZMod.isCyclic_units_prime (by norm_num)
    exact isCyclic_of_surjective (IsCyclic.mulAutMulEquiv P).symm.toMonoidHom
      (IsCyclic.mulAutMulEquiv P).symm.surjective
  let φ : U →* MulAut P := (MulAut.conjNormal (H := P)).comp U.subtype
  have hφ : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro u hu
    have hcu : (u : suzukiGroup 0 k) ∈ Subgroup.centralizer (P : Set (suzukiGroup 0 k)) := by
      rw [Subgroup.mem_centralizer_iff]
      intro p hp
      have h := congrArg (fun f : MulAut P => ((f ⟨p, hp⟩ : P) : suzukiGroup 0 k)) hu
      simp only [φ, MonoidHom.comp_apply, Subgroup.coe_subtype, MulAut.conjNormal_apply,
        MulAut.one_apply] at h
      calc p * u = (u * p * (u : suzukiGroup 0 k)⁻¹) * u := by rw [h]
        _ = u * p := by group
    rw [hcent] at hcu
    have h5 : orderOf (u : suzukiGroup 0 k) ∣ 5 := hP5 ▸ Subgroup.orderOf_dvd_natCard P hcu
    exact Subtype.ext (eq_one_of_isPGroup_two_of_odd hU u.2 (Odd.of_dvd_nat (by decide) h5))
  exact isCyclic_of_surjective (MonoidHom.ofInjective hφ).symm.toMonoidHom
    (MonoidHom.ofInjective hφ).symm.surjective

theorem suzukiGroup_not_pullDatum {a : ℕ} {K : Type} [Field K]
    [Finite K] (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1))
    (β : MulAut (suzukiGroup a K)) (hβ : orderOf β = 3) : ¬ PullDatum β := by
  intro hD
  have : Finite (suzukiGroup a K) := finite_suzukiGroup hK
  by_cases hin : β ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner (suzukiGroup a K)
  ·
    obtain ⟨x, rfl⟩ := hin
    apply not_three_dvd_card_suzukiGroup hK
    rw [← hβ]
    exact (orderOf_map_dvd _ x).trans (orderOf_dvd_natCard x)
  · obtain ⟨σ, h, b, k, _, _, -, hb, hk, hconj, ⟨eC⟩⟩ :=
      CFSG.RankThree.PartOne.KE.suzukiPrimeFieldCosetDescent a ha K hK 3 Nat.prime_three
        (by norm_num) β hβ hin
    have hD' := hD.conj (MulAut.conj h)
    rw [hconj] at hD'
    set β' := CFSG.SignalizerFunctorTheorem.NearModels.Suzuki.szFieldAut a K σ with hβ'
    set C := β'.toMonoidHom.eqLocus (MonoidHom.id (suzukiGroup a K)) with hCdef
    have hC : ∀ x, x ∈ C ↔ β' x = x := fun _ => Iff.rfl
    rcases Nat.eq_zero_or_pos b with rfl | hb1
    ·
      have hk2 : Nat.card k = 2 := by rw [hk]; norm_num
      refine hD'.false_of_isCyclic_fixed fun P hP hPfix => ?_
      have hPC : P ≤ C := fun x hx => (hC x).mpr (hPfix x hx)
      let e : P ≃* (P.subgroupOf C).map eC.toMonoidHom :=
        (Subgroup.subgroupOfEquivOfLe hPC).symm.trans
          ((P.subgroupOf C).equivMapOfInjective eC.toMonoidHom eC.injective)
      have hcyc := isCyclic_of_isPGroup_suzukiGroup_zero hk2 _ (hP.of_equiv e)
      exact isCyclic_of_surjective e.symm.toMonoidHom e.symm.surjective
    ·
      refine hD'.false_of_quasisimple_fixed C hC ((isQuasisimple_suzukiGroup hb1 hk).of_mulEquiv eC)
        ?_
      rw [Nat.card_congr (Subgroup.centerCongr eC).toEquiv,
        CFSG.RankThree.PartOne.KE.suzuki_center_eq_bot hb1 hk, Subgroup.card_bot]
      exact odd_one

end Suzuki

theorem kChevTwo_suzuki (n : ℕ) (hn : Odd n) :
    ∀ (X : Type) [Group X] [Finite X], IsQuasisimple X → Blueprint.SuzukiModel X 2 n →
      ∀ β : MulAut X, orderOf β = 3 → ¬ InnThetaNoncyclic β := by
  intro X _ _ _ hm β hβ
  obtain ⟨-, a, ha, K, _, _, hn', hK, ⟨e⟩⟩ := hm
  rw [hn'] at hK
  have hZ : Subgroup.center X = ⊥ := by
    refine Subgroup.eq_bot_of_card_eq _ ?_
    rw [Nat.card_congr (Subgroup.centerCongr e).toEquiv,
      CFSG.RankThree.PartOne.KE.suzuki_center_eq_bot ha hK, Subgroup.card_bot]
  exact not_innThetaNoncyclic_of_mulEquiv e hZ
    (fun β' hβ' => suzukiGroup_not_pullDatum ha hK β' hβ') β hβ

end CFSG.RankThree.PartTwo.Sec4.RonanKChevTwo

end
