module

public import CFSG.RankThree.PartTwo.Sec11.Item1120V0BarSylow
import CFSG.RankThree.PartTwo.Sec11.KS11LieProofCentCore
public import CFSG.RankThree.PartTwo.Sec11.KS11Lie2ProofExc

public section

namespace CFSG.RankThree.PartTwo.Sec11

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.ABGLocalTools (IsSylowOf)

namespace Item1120V0Bar

section Pure

variable {Z : Type} [Group Z] [Finite Z]

theorem fixes_of_mem_theta {J : Subgroup Z} (hJp : Group.IsPerfect J) (σ : MulAut Z)
    (hcent : ∀ t ∈ inSubgroup (aschbacherSolvableCore 3) J, ∀ k ∈ J, t * k = k * t)
    (h : ∀ j ∈ J, j⁻¹ * σ j ∈ inSubgroup (aschbacherSolvableCore 3) J) :
    ∀ j ∈ J, σ j = j := by
  refine KS11Lie2Proof.eq_of_mul_inv_mem_central (β := σ) hJp (fun j hj => ?_)
  have hθ : σ j * j⁻¹ ∈ inSubgroup (aschbacherSolvableCore 3) J := by
    have hc := KS11LieProof.conj_mem_inSubgroup hj (h j hj)
    rwa [mul_inv_cancel_left] at hc
  exact ⟨KS11Lie2Proof.mem_of_mem_theta hθ, fun k hk => hcent _ hθ k hk⟩

theorem orderOf_eq_three_pow_of_isSylowOf {J : Subgroup Z} {ξ : Z}
    (hξsyl : IsSylowOf 3 (Subgroup.zpowers ξ) J) :
    orderOf ξ = 3 ^ (Nat.card J).factorization 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [← Nat.card_zpowers]
  exact hξsyl.card_eq

theorem zpowers_inf_zpowers_eq_bot {J : Subgroup Z}
    (hJT : IsType424 (J ⧸ aschbacherSolvableCore 3 J)) {b ξ : Z} (hξJ : ξ ∈ J) (hξ3 : ∃ k : ℕ, ξ ^ 3 ^ k = 1) (hbJ : ∀ j ∈ J, b * j = j * b)
    (hb3 : ∃ k : ℕ, b ^ 3 ^ k = 1) :
    Subgroup.zpowers b ⊓ Subgroup.zpowers ξ = ⊥ := by
  obtain ⟨k, hk⟩ := hξ3
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨hxb, hxξ⟩ := Subgroup.mem_inf.mp hx
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hxb
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hxξ
  have hxJ : x ∈ J := by
    rw [← hn]
    exact J.zpow_mem hξJ n
  have hc : ∀ j ∈ J, x * j = j * x := by
    intro j hj
    rw [← hm]
    exact ((show Commute b j from hbJ j hj).zpow_left m).eq
  obtain ⟨y, hyθ, hye⟩ := KS11Lie2Proof.mem_theta_of_central hJT hxJ hc
  have hy : y = ⟨x, hxJ⟩ := Subtype.ext hye
  subst hy
  have hyk : (⟨x, hxJ⟩ : J) ^ 3 ^ k = 1 := by
    apply Subtype.ext
    show x ^ 3 ^ k = 1
    rw [← hn, ← zpow_natCast, ← zpow_mul, mul_comm n, zpow_mul, zpow_natCast, hk, one_zpow]
  have h1 : (⟨x, hxJ⟩ : J) = 1 := eq_one_of_mem_theta_of_pow_eq_one hyθ hyk
  rw [Subgroup.mem_bot]
  exact congrArg Subtype.val h1

theorem exists_big_elt_of_sylow {M J : Subgroup Z} (e : M ≃* J) {ξ z : Z}
    (hξsyl : IsSylowOf 3 (Subgroup.zpowers ξ) J) (hzM : z ∈ M) (hz3 : z ^ 3 = 1) :
    ∃ ζ ∈ M, z * ζ = ζ * z ∧ (∃ k : ℕ, ζ ^ 3 ^ k = 1) ∧ orderOf ζ = orderOf ξ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Finite (Sylow 3 ↥J) :=
    Finite.of_injective (fun P : Sylow 3 ↥J => (P : Set ↥J)) SetLike.coe_injective
  have hzP : IsPGroup 3 (Subgroup.zpowers z) := by
    refine IsPGroup.of_card_dvd_pow (n := 1) ?_
    rw [Nat.card_zpowers, pow_one]
    exact orderOf_dvd_of_pow_eq_one hz3
  obtain ⟨T, hT, hzT⟩ := exists_isSylowOf_ge (Subgroup.zpowers_le.mpr hzM) hzP
  have hTM : T ≤ M := hT.le
  have hTp : IsPGroup 3 ↥T := hT.isPGroup
  obtain ⟨Q, hQ⟩ := hT
  obtain ⟨Q₀, hQ₀⟩ := hξsyl
  obtain ⟨Q', hQ'⟩ : ∃ Q' : Sylow 3 ↥J,
      (Q' : Subgroup ↥J) = (Q : Subgroup ↥M).map e.toMonoidHom :=
    ⟨Sylow.mapSurjective (f := e.toMonoidHom) e.surjective Q, rfl⟩
  have Φ : ↥T ≃* ↥(Subgroup.zpowers ξ) :=
    (MulEquiv.subgroupCongr hQ.symm).trans <|
    (Subgroup.equivMapOfInjective (Q : Subgroup ↥M) M.subtype M.subtype_injective).symm.trans <|
    (Subgroup.equivMapOfInjective (Q : Subgroup ↥M) e.toMonoidHom e.injective).trans <|
    (MulEquiv.subgroupCongr hQ'.symm).trans <|
    (Sylow.equiv Q' Q₀).trans <|
    (Subgroup.equivMapOfInjective (Q₀ : Subgroup ↥J) J.subtype J.subtype_injective).trans
      (MulEquiv.subgroupCongr hQ₀)
  haveI : IsCyclic ↥T := (MulEquiv.isCyclic Φ).mpr inferInstance
  have hcard : Nat.card ↥T = Nat.card ↥(Subgroup.zpowers ξ) := Nat.card_congr Φ.toEquiv
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := ↥T)
  have hzg : (⟨z, hzT (Subgroup.mem_zpowers z)⟩ : ↥T) ∈ Subgroup.zpowers g := hg _
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hzg
  have hzm : (g : Z) ^ m = z := by
    have h2 := congrArg Subtype.val hm
    simpa using h2
  refine ⟨(g : Z), hTM g.2, ?_, ?_, ?_⟩
  · rw [← hzm]
    exact (Commute.refl (g : Z)).zpow_left m
  · obtain ⟨k, hk⟩ := hTp g
    exact ⟨k, by simpa using congrArg Subtype.val hk⟩
  · have h1 : orderOf (g : Z) = orderOf g :=
      orderOf_injective T.subtype Subtype.coe_injective g
    rw [h1, orderOf_eq_card_of_forall_mem_zpowers hg, hcard, Nat.card_zpowers]

theorem not_three_dvd_card_of_ringChar_ne {K : Type} [Field K] [Finite K] (h : ringChar K ≠ 3) :
    ¬ 3 ∣ Nat.card K := by
  intro h3
  haveI := Fintype.ofFinite K
  obtain ⟨n, hp, hcard⟩ := FiniteField.card K (ringChar K)
  rw [Nat.card_eq_fintype_card, hcard] at h3
  have h3p : 3 ∣ ringChar K := Nat.prime_three.dvd_of_dvd_pow h3
  exact h ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp h3p).symm

theorem nonempty_mulEquiv_commutator_of_isPerfect (hZ : Group.IsPerfect Z) :
    Nonempty (Z ≃* _root_.commutator Z) := by
  exact ⟨((MulEquiv.subgroupCongr hZ.commutator_eq_top).trans Subgroup.topEquiv).symm⟩

end Pure

end Item1120V0Bar

end CFSG.RankThree.PartTwo.Sec11

end
