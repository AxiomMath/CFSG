module

public import CFSG.RankThree.PartTwo.Sec19.Step1919NarrowRank
import CFSG.RankThree.PartTwo.Sec19.Step1911EndProof
import CFSG.RankThree.PartTwo.Sec19.Step1910O2Proof
public import CFSG.RankThree.PartTwo.Sec19.Step1910Proof

public section

namespace CFSG.RankThree.PartTwo.Sec19

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late CFSG.RankThree.PartTwo.Sec13

namespace Step1919NarrowTools

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem mk_mul_comm_iff {M : Subgroup G} (g h : M) :
    QuotientGroup.mk' (CFSG.pCore 2 M) g * QuotientGroup.mk' (CFSG.pCore 2 M) h =
        QuotientGroup.mk' (CFSG.pCore 2 M) h * QuotientGroup.mk' (CFSG.pCore 2 M) g ↔
      (g : G) * h * (g : G)⁻¹ * (h : G)⁻¹ ∈ CFSG.Open.pCoreOf 2 M := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have e : (g : G) * h * (g : G)⁻¹ * (h : G)⁻¹ = ((g * h * g⁻¹ * h⁻¹ : M) : G) := by simp
  rw [e, ← Step1911EndProof.mem_pCore_iff, ← QuotientGroup.eq_one_iff,
    QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
    QuotientGroup.mk_inv]
  simp only [QuotientGroup.mk'_apply]
  constructor
  · intro h1
    rw [h1]
    group
  · intro h1
    exact Step1910O2Proof.mul_comm_of_commutator_eq_one h1

omit [Finite G] in
theorem mk_mem_centralizer_iff {M K : Subgroup G} (hKM : K ≤ M) (u : M) :
    QuotientGroup.mk' (CFSG.pCore 2 M) u ∈ Subgroup.centralizer
        ((K.subgroupOf M).map (QuotientGroup.mk' (CFSG.pCore 2 M)) : Set (M ⧸ CFSG.pCore 2 M)) ↔
      ∀ k ∈ K, (u : G) * k * (u : G)⁻¹ * k⁻¹ ∈ CFSG.Open.pCoreOf 2 M := by
  rw [Subgroup.mem_centralizer_iff]
  constructor
  · intro h k hk
    exact (mk_mul_comm_iff u ⟨k, hKM hk⟩).mp
      (h _ ⟨⟨k, hKM hk⟩, Subgroup.mem_subgroupOf.mpr hk, rfl⟩).symm
  · rintro h _ ⟨m, hm, rfl⟩
    exact ((mk_mul_comm_iff u m).mpr (h m (Subgroup.mem_subgroupOf.mp hm))).symm

omit [Finite G] in
theorem mk_pow_three {M : Subgroup G} (u : M) (hu : (u : G) ^ 3 ∈ CFSG.Open.pCoreOf 2 M) :
    QuotientGroup.mk' (CFSG.pCore 2 M) u ^ 3 = 1 := by
  rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
    Step1911EndProof.mem_pCore_iff]
  simpa using hu

theorem four_le_localRank_of_components {M : Subgroup G} (hQ : CFSG.Open.pCoreOf 2 M ≠ ⊥)
    (u₁ u₂ u₃ u₄ : M)
    (hc12 : (u₁ : G) * u₂ * (u₁ : G)⁻¹ * (u₂ : G)⁻¹ ∈ CFSG.Open.pCoreOf 2 M)
    (hc13 : (u₁ : G) * u₃ * (u₁ : G)⁻¹ * (u₃ : G)⁻¹ ∈ CFSG.Open.pCoreOf 2 M)
    (hc14 : (u₁ : G) * u₄ * (u₁ : G)⁻¹ * (u₄ : G)⁻¹ ∈ CFSG.Open.pCoreOf 2 M)
    (hc23 : (u₂ : G) * u₃ * (u₂ : G)⁻¹ * (u₃ : G)⁻¹ ∈ CFSG.Open.pCoreOf 2 M)
    (hc24 : (u₂ : G) * u₄ * (u₂ : G)⁻¹ * (u₄ : G)⁻¹ ∈ CFSG.Open.pCoreOf 2 M)
    (hc34 : (u₃ : G) * u₄ * (u₃ : G)⁻¹ * (u₄ : G)⁻¹ ∈ CFSG.Open.pCoreOf 2 M)
    (h₁ : (u₁ : G) ^ 3 ∈ CFSG.Open.pCoreOf 2 M) (h₂ : (u₂ : G) ^ 3 ∈ CFSG.Open.pCoreOf 2 M)
    (h₃ : (u₃ : G) ^ 3 ∈ CFSG.Open.pCoreOf 2 M) (h₄ : (u₄ : G) ^ 3 ∈ CFSG.Open.pCoreOf 2 M)
    (hn₁ : (u₁ : G) ∉ CFSG.Open.pCoreOf 2 M) {K₂ K₃ K₄ : Subgroup G}
    (hK₂ : K₂ ≤ M) (hK₃ : K₃ ≤ M) (hK₄ : K₄ ≤ M)
    (h12 : ∀ k ∈ K₂, (u₁ : G) * k * (u₁ : G)⁻¹ * k⁻¹ ∈ CFSG.Open.pCoreOf 2 M)
    (h22 : ∃ k ∈ K₂, (u₂ : G) * k * (u₂ : G)⁻¹ * k⁻¹ ∉ CFSG.Open.pCoreOf 2 M)
    (h13 : ∀ k ∈ K₃, (u₁ : G) * k * (u₁ : G)⁻¹ * k⁻¹ ∈ CFSG.Open.pCoreOf 2 M)
    (h23 : ∀ k ∈ K₃, (u₂ : G) * k * (u₂ : G)⁻¹ * k⁻¹ ∈ CFSG.Open.pCoreOf 2 M)
    (h33 : ∃ k ∈ K₃, (u₃ : G) * k * (u₃ : G)⁻¹ * k⁻¹ ∉ CFSG.Open.pCoreOf 2 M)
    (h14 : ∀ k ∈ K₄, (u₁ : G) * k * (u₁ : G)⁻¹ * k⁻¹ ∈ CFSG.Open.pCoreOf 2 M)
    (h24 : ∀ k ∈ K₄, (u₂ : G) * k * (u₂ : G)⁻¹ * k⁻¹ ∈ CFSG.Open.pCoreOf 2 M)
    (h34 : ∀ k ∈ K₄, (u₃ : G) * k * (u₃ : G)⁻¹ * k⁻¹ ∈ CFSG.Open.pCoreOf 2 M)
    (h44 : ∃ k ∈ K₄, (u₄ : G) * k * (u₄ : G)⁻¹ * k⁻¹ ∉ CFSG.Open.pCoreOf 2 M) :
    4 ≤ CFSG.Assembly.RankThreeEven.localRank 3 G := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π := QuotientGroup.mk' (CFSG.pCore 2 M) with hπ
  have hnot : ∀ {K : Subgroup G} (hK : K ≤ M) (u : M),
      (∃ k ∈ K, (u : G) * k * (u : G)⁻¹ * k⁻¹ ∉ CFSG.Open.pCoreOf 2 M) →
      π u ∉ Subgroup.centralizer ((K.subgroupOf M).map π : Set (M ⧸ CFSG.pCore 2 M)) := by
    intro K hK u ⟨k, hk, hku⟩ h
    exact hku ((mk_mem_centralizer_iff hK u).mp h k hk)
  have hyes : ∀ {K : Subgroup G} (hK : K ≤ M) (u : M),
      (∀ k ∈ K, (u : G) * k * (u : G)⁻¹ * k⁻¹ ∈ CFSG.Open.pCoreOf 2 M) →
      Subgroup.zpowers (π u) ≤
        Subgroup.centralizer ((K.subgroupOf M).map π : Set (M ⧸ CFSG.pCore 2 M)) :=
    fun hK u h => Subgroup.zpowers_le.mpr ((mk_mem_centralizer_iff hK u).mpr h)
  refine Step1919NarrowRank.four_le_localRank_of_chain hQ ((mk_mul_comm_iff _ _).mpr hc12)
    ((mk_mul_comm_iff _ _).mpr hc13) ((mk_mul_comm_iff _ _).mpr hc14)
    ((mk_mul_comm_iff _ _).mpr hc23) ((mk_mul_comm_iff _ _).mpr hc24)
    ((mk_mul_comm_iff _ _).mpr hc34) (mk_pow_three _ h₁) (mk_pow_three _ h₂) (mk_pow_three _ h₃)
    (mk_pow_three _ h₄) ?_ (fun h => hnot hK₂ u₂ h22 (hyes hK₂ u₁ h12 h))
    (fun h => hnot hK₃ u₃ h33 (sup_le (hyes hK₃ u₁ h13) (hyes hK₃ u₂ h23) h))
    (fun h => hnot hK₄ u₄ h44 (sup_le (sup_le (hyes hK₄ u₁ h14) (hyes hK₄ u₂ h24))
      (hyes hK₄ u₃ h34) h))
  intro h
  apply hn₁
  have h1 : u₁ ∈ CFSG.pCore 2 M := by
    rw [← QuotientGroup.eq_one_iff]
    exact h
  rwa [Step1911EndProof.mem_pCore_iff] at h1

theorem exists_fixed_noncentral
    {M J H A : Subgroup G} (hJM : J ∈ oTwoComponentsIn M)
    (hlist : IsList194 (J ⧸ CFSG.pCore 2 J) ∨ IsSmall194 (J ⧸ CFSG.pCore 2 J))
    (hpar : (IsEmpty (J ⧸ CFSG.pCore 2 J ≃* alternatingGroup (Fin 10)) ∧
        IsProperParabolic (starIm J H)) ∨
      (Nonempty (J ⧸ CFSG.pCore 2 J ≃* alternatingGroup (Fin 10)) ∧
        Sec4.IsExtOf (starIm J H) (Equiv.Perm (Fin 5)) (Multiplicative (Fin 4 → ZMod 2))))
    (hA3 : IsPGroup 3 A) (hAe : ∀ a ∈ A, a ^ 3 = 1)
    (hAJ : A ≤ Subgroup.normalizer (J : Set G)) (hAH : A ≤ H) :
    ∃ y : J, (y : G) ^ 3 = 1 ∧ (∀ a ∈ A, a * y = (y : G) * a) ∧
      (y : J ⧸ CFSG.pCore 2 J) ∉ Subgroup.center (J ⧸ CFSG.pCore 2 J) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hperfJ : Group.IsPerfect (J ⧸ CFSG.pCore 2 J) :=
    (Sec18.isQuasisimple_of_mem_oTwoComponentsIn hJM).1
  by_cases hZ : ∃ z ∈ Subgroup.center (J ⧸ CFSG.pCore 2 J), z ≠ 1
  ·
    obtain ⟨z, hzZ, hz1⟩ := hZ
    obtain ⟨n, -, ⟨ψ⟩⟩ :=
      Step1911EndProof.exists_mulEquiv_SL_of_isList194_wide hlist hperfJ hzZ hz1
    have hψZ : ψ z ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 n)) := by
      rw [Subgroup.mem_center_iff] at hzZ ⊢
      intro s
      obtain ⟨t, rfl⟩ := ψ.surjective s
      rw [← map_mul, ← map_mul, hzZ t]
    obtain ⟨r, hr3, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hψZ
    rw [Fintype.card_fin] at hr3
    have hr1 : r ≠ 1 := by
      rintro rfl
      apply hz1
      apply ψ.injective
      rw [map_one]
      apply Subtype.ext
      rw [← hr, map_one]
      rfl
    have hparJ : IsProperParabolic (starIm J H) := by
      rcases hpar with ⟨-, h⟩ | ⟨⟨e⟩, -⟩
      · exact h
      · have := alternatingGroup.isSimpleGroup (α := Fin 10) (by simp)
        exact (KFacts.false_of_isSimpleGroup_of_mulEquiv e hperfJ hzZ hz1).elim
    obtain ⟨x, hx3, hxc, hxf⟩ :=
      Step1910Proof.exists_fixed_of_mulEquiv_SL hAJ hAH hAe hr1 hr3 ψ hparJ
    obtain ⟨y, hy3, hyA, hyc⟩ := Step1910Proof.exists_lift_of_fixed hA3 hAJ hxf hx3 hxc
    exact ⟨y, hy3, hyA, hyc⟩
  ·
    push Not at hZ
    obtain ⟨xb, hxb3, hxbc⟩ := Step1910Proof.exists_noncentral_of_isList194_wide hlist hperfJ
    have h3J : 3 ∣ Nat.card J := by
      have hxb1 : xb ≠ 1 := fun h => hxbc (h ▸ Subgroup.one_mem _)
      have h1 := orderOf_dvd_natCard xb
      rw [orderOf_eq_prime hxb3 hxb1] at h1
      exact h1.trans (by
        rw [(CFSG.pCore 2 J).card_eq_card_quotient_mul_card_subgroup]
        exact dvd_mul_right _ _)
    obtain ⟨y, hyJ, hy1, hy3, hyA⟩ := Step1910Proof.exists_mem_of_le_normalizer hA3 hAJ h3J
    refine ⟨⟨y, hyJ⟩, hy3, hyA, fun hc => ?_⟩
    have hyo : orderOf ((⟨y, hyJ⟩ : J) : G) = 3 := orderOf_eq_prime hy3 hy1
    exact Step1910Proof.mk_ne_one_of_orderOf hyo (hZ _ hc)

end Step1919NarrowTools

end CFSG.RankThree.PartTwo.Sec19
