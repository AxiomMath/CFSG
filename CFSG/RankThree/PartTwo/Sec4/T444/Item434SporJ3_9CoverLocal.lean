module

public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SporJ3_9CoverGroup
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SporJ3_27Local
public import CFSG.RankThree.PartTwo.KFacts.K426J3

public section

namespace CFSG.RankThree.PartTwo.Sec4.Item434SporJ3

open CFSG.AGLEmbedding CFSG.RankThree.PartTwo.KFacts.K426 CFSG.Sporadic.Schreier

theorem not_five_dvd_card_normalizer {J : Type} [Group J] [Finite J] {T : Subgroup J}
    (hT : IsPGroup 3 T) (hF : J3SylowFacts J T) :
    ¬ 5 ∣ Nat.card (Subgroup.normalizer (T : Set J)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N := Subgroup.normalizer (T : Set J) with hN
  have hTN : T ≤ N := Subgroup.le_normalizer
  have hnorm : (T.subgroupOf N).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hTN).2 le_rfl
  have h3 : IsPGroup 3 (T.subgroupOf N) :=
    hT.of_surjective (Subgroup.subgroupOfEquivOfLe hTN).symm.toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hTN).symm.surjective
  have h2 : IsPGroup 2 (N ⧸ T.subgroupOf N) := by
    intro q
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨e, he⟩ := hF.two_top y.1 y.2
    refine ⟨e, ?_⟩
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    exact Subgroup.mem_subgroupOf.2 he
  obtain ⟨a, ha⟩ := h3.exists_card_eq
  obtain ⟨b, hb⟩ := h2.exists_card_eq
  have hcard : Nat.card N = Nat.card (N ⧸ T.subgroupOf N) * Nat.card (T.subgroupOf N) :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup _
  intro h5
  rw [hcard, ha, hb] at h5
  rcases (Nat.Prime.dvd_mul (by norm_num : Nat.Prime 5)).mp h5 with h | h
  · have := (Nat.prime_five.dvd_of_dvd_pow h)
    omega
  · have := (Nat.prime_five.dvd_of_dvd_pow h)
    omega

theorem card_centralizer_inf_conj {H : Type*} [Group H] (P : Subgroup H) {k : H} (hk : k ∈ P)
    (c : H) :
    Nat.card (Subgroup.centralizer ({k * c * k⁻¹} : Set H) ⊓ P : Subgroup H) =
      Nat.card (Subgroup.centralizer ({c} : Set H) ⊓ P : Subgroup H) := by
  have hmap : (Subgroup.centralizer ({c} : Set H) ⊓ P).map (MulAut.conj k).toMonoidHom =
      Subgroup.centralizer ({k * c * k⁻¹} : Set H) ⊓ P := by
    ext p
    constructor
    · rintro ⟨q, ⟨hq1, hq2⟩, rfl⟩
      have hq : q * c = c * q := Subgroup.mem_centralizer_singleton_iff.mp hq1
      refine ⟨Subgroup.mem_centralizer_singleton_iff.mpr ?_,
        P.mul_mem (P.mul_mem hk hq2) (P.inv_mem hk)⟩
      change k * q * k⁻¹ * (k * c * k⁻¹) = k * c * k⁻¹ * (k * q * k⁻¹)
      calc k * q * k⁻¹ * (k * c * k⁻¹) = k * (q * c) * k⁻¹ := by group
        _ = k * (c * q) * k⁻¹ := by rw [hq]
        _ = k * c * k⁻¹ * (k * q * k⁻¹) := by group
    · rintro ⟨hp1, hp2⟩
      have hp : p * (k * c * k⁻¹) = k * c * k⁻¹ * p :=
        Subgroup.mem_centralizer_singleton_iff.mp hp1
      refine ⟨k⁻¹ * p * k, ⟨Subgroup.mem_centralizer_singleton_iff.mpr ?_, ?_⟩, ?_⟩
      · calc k⁻¹ * p * k * c = k⁻¹ * (p * (k * c * k⁻¹)) * k := by group
          _ = k⁻¹ * (k * c * k⁻¹ * p) * k := by rw [hp]
          _ = c * (k⁻¹ * p * k) := by group
      · exact P.mul_mem (P.mul_mem (P.inv_mem hk) hp2) hk
      · change k * (k⁻¹ * p * k) * k⁻¹ = p
        group
  rw [← hmap, Subgroup.card_map_of_injective (MulAut.conj k).injective]

theorem centralizer_sq_eq {H : Type*} [Group H] {c : H} (hc : c ^ 3 = 1) :
    Subgroup.centralizer ({c ^ 2} : Set H) = Subgroup.centralizer ({c} : Set H) := by
  ext y
  rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    have h1 : Commute y (c ^ 2) := h
    have h2 : Commute y ((c ^ 2) ^ 2) := h1.pow_right 2
    have h3 : (c ^ 2) ^ 2 = c := by
      calc (c ^ 2) ^ 2 = c ^ 3 * c := by group
        _ = c := by rw [hc, one_mul]
    rw [h3] at h2
    exact h2
  · intro h
    exact (show Commute y c from h).pow_right 2

theorem dich_of_mulEquiv
    {J : Type*} [Group J] (φ : J ≃* j3P) (u : J)
    (hu : orderOf u = 3) :
    IsPGroup 3 (Subgroup.centralizer ({u} : Set J)) ∨
      5 ∣ Nat.card (Subgroup.centralizer ({u} : Set J)) := by
  let ψ : J →* Equiv.Perm (Fin 6156) := j3P.subtype.comp φ.toMonoidHom
  have hψinj : Function.Injective ψ := j3P.subtype_injective.comp φ.injective
  have hψmem : ∀ y, ψ y ∈ j3P := fun y => (φ y).2
  have hmap : (Subgroup.centralizer ({u} : Set J)).map ψ =
      Subgroup.centralizer ({ψ u} : Set (Equiv.Perm (Fin 6156))) ⊓ j3P := by
    ext p
    constructor
    · rintro ⟨y, hy, rfl⟩
      have hy' : y * u = u * y := Subgroup.mem_centralizer_singleton_iff.mp hy
      refine ⟨Subgroup.mem_centralizer_singleton_iff.mpr ?_, hψmem y⟩
      rw [← map_mul, ← map_mul, hy']
    · rintro ⟨hp1, hp2⟩
      obtain ⟨q, hq⟩ := φ.surjective ⟨p, hp2⟩
      have hqp : ψ q = p := congrArg Subtype.val hq
      refine ⟨q, Subgroup.mem_centralizer_singleton_iff.mpr ?_, hqp⟩
      apply hψinj
      rw [map_mul, map_mul, hqp]
      exact Subgroup.mem_centralizer_singleton_iff.mp hp1
  have hcard : Nat.card (Subgroup.centralizer ({u} : Set J)) =
      Nat.card (Subgroup.centralizer ({ψ u} : Set (Equiv.Perm (Fin 6156))) ⊓ j3P :
        Subgroup (Equiv.Perm (Fin 6156))) := by
    rw [← hmap, Subgroup.card_map_of_injective hψinj]
  have hro : orderOf (ψ u) = 3 := (orderOf_injective ψ hψinj u).trans hu
  obtain ⟨k, hk, c, hc, e, he, hre⟩ := j3t_fusion (hψmem u) hro
  have hc3 : c ^ 3 = 1 := by
    rcases hc with rfl | rfl
    · exact (j3tReps_spec (by norm_num : 0 < 2)).2
    · exact (j3tReps_spec (by norm_num : 1 < 2)).2
  have hcent : Subgroup.centralizer ({c ^ e} : Set (Equiv.Perm (Fin 6156))) =
      Subgroup.centralizer ({c} : Set (Equiv.Perm (Fin 6156))) := by
    rcases he with rfl | rfl
    · rw [pow_one]
    · exact centralizer_sq_eq hc3
  have hcard' : Nat.card (Subgroup.centralizer ({u} : Set J)) =
      Nat.card (Subgroup.centralizer ({c} : Set (Equiv.Perm (Fin 6156))) ⊓ j3P :
        Subgroup (Equiv.Perm (Fin 6156))) := by
    rw [hcard, hre, card_centralizer_inf_conj j3P hk, hcent]
  rcases hc with rfl | rfl
  · right
    rw [hcard', ← (j3t_caseA).1, (j3t_caseA).2]
    all_goals norm_num
  · left
    refine IsPGroup.of_card (n := 5) ?_
    rw [hcard', ← (j3t_caseB).1, (j3t_caseB).2]
    all_goals norm_num

theorem j3_e9_split
    (hOR : KFactJ3OuterRank)
    (J : Type) [Group J] [Finite J]
    (hJ : Nonempty (J ≃* (TauCeti.CFSGIndex.sporadic .J3).Group)) {U : Subgroup J}
    (hU : IsMulCommutative U) (hU3 : ∀ u ∈ U, u ^ 3 = 1) (hU9 : Nat.card U = 9) :
    (∀ u ∈ U, u ≠ 1 → IsPGroup 3 (Subgroup.centralizer ({u} : Set J))) ∨
      (⨆ u ∈ U, ⨆ (_ : u ≠ 1), Subgroup.centralizer ({u} : Set J)) = ⊤ := by
  obtain ⟨eJ⟩ := hJ
  obtain ⟨b⟩ : Nonempty (Blueprint.NativeSporadic.Carrier .J3 ≃*
      (TauCeti.CFSGIndex.sporadic .J3).Group) := CFSG.Sporadic.Bridge.J3.nonempty_mulEquiv
  obtain ⟨-, hover⟩ := j3CoverFacts J ⟨eJ⟩
  obtain ⟨S, Z, φ, hsetup⟩ := exists_outerSetup hOR J ⟨eJ⟩
  obtain ⟨z, hzU, hz1, T, hzT⟩ := exists_centralizer_sylow hsetup hU hU3 hU9
  refine e9_split_of_dichotomy hover (fun T => not_five_dvd_card_normalizer T.isPGroup'
    (kFactJ3Sylow J ⟨eJ⟩ T)) (fun u hu => ?_) hU3 hzU hz1 hzT
  exact dich_of_mulEquiv (eJ.trans (b.symm.trans j3PermEquiv)) u hu

end CFSG.RankThree.PartTwo.Sec4.Item434SporJ3
