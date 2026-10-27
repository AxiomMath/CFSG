module

public import CFSG.RankThree.PartTwo.Sec21.Item21Res9ProofLift
import CFSG.LieType.CurtisTits.Recognition
import CFSG.RankThree.PartTwo.Sec4.Census.CoverCenterThreeRestON
public import CFSG.RankThree.Native.ONTripleSylow
import CFSG.RankThree.Native.ONTripleUnique

public section

namespace CFSG.RankThree.PartTwo.Sec21.Item21Res9Proof

attribute [local irreducible] dotProduct

open Subgroup CFSG.RankThree.Native.ONTriple
open scoped commutatorElement

theorem exists_coprime_center (X : Type*) [Group X] [Finite X] :
    ∃ N : Subgroup X, N ≤ center X ∧ ¬ 3 ∣ Nat.card N ∧
      ∃ a : ℕ, ∀ z ∈ center X, z ^ 3 ^ a ∈ N := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨a, m, hm3, hn⟩ :=
    Nat.exists_eq_pow_mul_and_not_dvd (Nat.card_pos (α := center X)).ne' 3 (by norm_num)
  let N : Subgroup X :=
    { carrier := {z | z ∈ center X ∧ z ^ m = 1}
      mul_mem' := by
        rintro z w ⟨hz, hzm⟩ ⟨hw, hwm⟩
        refine ⟨mul_mem hz hw, ?_⟩
        rw [(Commute.mul_pow (mem_center_iff.mp hw z) m), hzm, hwm, one_mul]
      one_mem' := ⟨one_mem _, one_pow m⟩
      inv_mem' := by
        rintro z ⟨hz, hzm⟩
        exact ⟨inv_mem hz, by rw [inv_pow, hzm, inv_one]⟩ }
  refine ⟨N, fun z hz => hz.1, fun h3 => ?_, a, fun z hz => ⟨pow_mem hz _, ?_⟩⟩
  · obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' 3 h3
    have hgm : (g : X) ^ m = 1 := g.2.2
    have h1 : orderOf (g : X) ∣ m := orderOf_dvd_of_pow_eq_one hgm
    rw [Subgroup.orderOf_coe, hg] at h1
    exact hm3 h1
  · have hcard : (⟨z, hz⟩ : center X) ^ Nat.card (center X) = 1 := pow_card_eq_one'
    rw [← pow_mul, ← hn]
    exact congrArg Subtype.val hcard

theorem exists_noncentral_GM
    (P : Sylow 3 GM) :
    ∃ s ∈ (P : Subgroup GM), s ^ 3 = 1 ∧ ∃ t ∈ (P : Subgroup GM), s * t ≠ t * s := by
  obtain ⟨g, hg⟩ := sylow_eq_threeQ P
  have hr := relG_conj g
  rw [hg]
  refine ⟨_, ThreeQRel.v_mem 0, hr.vcube 0, _, ThreeQRel.v_mem 3, fun h => hr.x1 ?_⟩
  have hc := hr.comm 0 3
  rw [commutatorElement_eq_one_iff_mul_comm.mpr h, omegaZ_val,
    show omegaN (0 : Fin 4) (3 : Fin 4) = 1 by decide, pow_one] at hc
  exact hc.symm

theorem exists_noncentral_ON
    {X : Type} [Group X] [Finite X] (hX : IsQuasisimple X)
    (h3 : 3 ∣ Nat.card (center X)) (e : X ⧸ center X ≃* Blueprint.NativeSporadic.ON)
    (S : Sylow 3 X) :
    ∃ s ∈ (S : Subgroup X), s ^ 3 = 1 ∧ ∃ t ∈ (S : Subgroup X), s * t ≠ t * s := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨N, hNc, hN3, a, hpow⟩ := exists_coprime_center X
  have : N.Normal := normal_of_le_center hNc
  refine exists_noncentral_of_quotient_coprime N hN3 (fun Q => ?_) S
  set π := QuotientGroup.mk' N with hπ
  have hsurj : Function.Surjective π := QuotientGroup.mk'_surjective N
  have hker : π.ker ≤ center X := by rw [hπ, QuotientGroup.ker_mk']; exact hNc
  have hne : ∃ k, π k ≠ 1 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨-, -, u, v, huv⟩ := hX
    apply huv
    obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective u
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective v
    have hk : k ∈ center X := hNc ((QuotientGroup.eq_one_iff k).mp (hcon k))
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, mem_center_iff.mp hk l]
  have hX' : IsQuasisimple (X ⧸ N) :=
    CFSG.LieType.CurtisTits.isQuasisimple_of_surjective hX hsurj hne
  have : Group.IsPerfect (X ⧸ N) := hX'.1
  have hZ' := CFSG.LieType.CurtisTits.center_eq_map_center_of_isQuasisimple hX hsurj hker
  let eq' := CFSG.LieType.CurtisTits.centralQuotientEquivOfIsQuasisimple hX hsurj hker
  have hZp : IsPGroup 3 (center (X ⧸ N)) := by
    intro g
    have hg : (g : X ⧸ N) ∈ (center X).map π := hZ' ▸ g.2
    obtain ⟨z, hz, hzg⟩ := mem_map.mp hg
    refine ⟨a, Subtype.ext ?_⟩
    rw [SubmonoidClass.coe_pow, ← hzg, ← map_pow, OneMemClass.coe_one, hπ,
      QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact hpow z hz
  have hdvd : Nat.card (center (X ⧸ N)) ∣ 3 :=
    CFSG.RankThree.PartTwo.Sec4.Census.CoverCenterThreeRest.card_center_dvd_three_of_ON hX' hZp
      (eq'.symm.trans e)
  have h3' : 3 ∣ Nat.card (center (X ⧸ N)) := by
    obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' 3 h3
    have hzN : (z : X) ∉ N := fun hm => by
      have h1 : orderOf (⟨z, hm⟩ : N) ∣ Nat.card N := orderOf_dvd_natCard _
      rw [Subgroup.orderOf_mk, Subgroup.orderOf_coe, hz] at h1
      exact hN3 h1
    have hπz : π z ∈ center (X ⧸ N) := hZ' ▸ mem_map_of_mem π z.2
    have hord : orderOf (⟨π z, hπz⟩ : center (X ⧸ N)) = 3 := by
      rw [Subgroup.orderOf_mk]
      refine orderOf_eq_prime ?_ fun h1 => hzN ?_
      · have hz3 : z ^ 3 = 1 := orderOf_dvd_iff_pow_eq_one.mp (dvd_of_eq hz)
        rw [← map_pow, ← Subgroup.coe_pow, hz3, Subgroup.coe_one, map_one]
      · rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
        exact h1
    exact hord ▸ orderOf_dvd_natCard _
  have hcard : Nat.card (center (X ⧸ N)) = 3 := Nat.dvd_antisymm hdvd h3'
  have eK : center (X ⧸ N) ≃* Multiplicative (ZMod 3) :=
    mulEquivOfPrimeCardEq hcard (by rw [Nat.card_eq_fintype_card, Fintype.card_multiplicative,
      ZMod.card])
  obtain ⟨ψ⟩ := nonempty_equiv_FHat (center (X ⧸ N)) eK (eq'.symm.trans e)
  let φ : X ⧸ N ≃* GM := ψ.trans modelEquiv
  have hφs : Function.Surjective φ.toMonoidHom := φ.surjective
  obtain ⟨s', hs', hs3, t', ht', hst⟩ := exists_noncentral_GM (Q.mapSurjective hφs)
  rw [Sylow.coe_mapSurjective hφs Q] at hs' ht'
  obtain ⟨s, hs, rfl⟩ := mem_map.mp hs'
  obtain ⟨t, ht, rfl⟩ := mem_map.mp ht'
  refine ⟨s, hs, φ.injective (by rw [map_pow, map_one]; exact hs3), t, ht, fun h => hst ?_⟩
  change φ s * φ t = φ t * φ s
  rw [← map_mul, ← map_mul, h]

end CFSG.RankThree.PartTwo.Sec21.Item21Res9Proof
