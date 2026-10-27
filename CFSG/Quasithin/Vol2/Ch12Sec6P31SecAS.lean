module

public import CFSG.Quasithin.Background.A3StructureDefs
public import CFSG.Quasithin.Background.E1Defs
public import CFSG.Adapters.WholeGroupLayer
public import CFSG.Foundations.KCoreClosure
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.Quasithin.H13.P31Sec

open CFSG.Quasithin CFSG.Quasithin.A1b
open scoped Pointwise

@[expose] def EBound (S : Type) [Group S] (ν : ℕ∞) : Prop :=
  ∀ (G' : Type) [Group G'] [Finite G'] (T' : Subgroup G'), SQTKGroup G' →
    IsSimpleGroup ↥(CFSG.generalizedFitting G') → IsSylowIn 2 T' ⊤ →
    CFSG.generalizedFitting G' ⊔ T' = ⊤ → Nonempty (↥(CFSG.generalizedFitting G') ≃* S) →
    E1.nParam (⊤ : Subgroup G') ≤ ν

section AlmostSimple

variable {Γ : Type} [Group Γ] [Finite Γ] {I P : Subgroup Γ} [hIn : I.Normal]

theorem exists_mul_of_sup_eq_top (hIP : I ⊔ P = ⊤) (x : Γ) : ∃ i ∈ I, ∃ y ∈ P, x = i * y := by
  have hx : x ∈ ((I ⊔ P : Subgroup Γ) : Set Γ) := by
    rw [hIP]
    exact Subgroup.mem_top x
  have h : ((I ⊔ P : Subgroup Γ) : Set Γ) = (I : Set Γ) * (P : Set Γ) := Subgroup.normal_mul I P
  rw [h] at hx
  obtain ⟨i, hi, y, hy, rfl⟩ := hx
  exact ⟨i, hi, y, hy, rfl⟩

theorem mem_of_pow_prime_eq_one (hP : IsPGroup 2 ↥P) (hIP : I ⊔ P = ⊤) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {x : Γ} (hx : x ^ p = 1) : x ∈ I := by
  obtain ⟨i, hi, y, hy, rfl⟩ := exists_mul_of_sup_eq_top hIP x
  obtain ⟨k, hk⟩ := hP ⟨y, hy⟩
  have hyk : y ^ 2 ^ k = 1 := by
    have := congrArg Subtype.val hk
    simpa using this
  let π : Γ →* Γ ⧸ I := QuotientGroup.mk' I
  have hπi : π i = 1 := (QuotientGroup.eq_one_iff i).2 hi
  have h1 : (π y) ^ p = 1 := by
    have : π (i * y) ^ p = 1 := by rw [← map_pow, hx, map_one]
    rwa [map_mul, hπi, one_mul] at this
  have h2 : (π y) ^ 2 ^ k = 1 := by rw [← map_pow, hyk, map_one]
  have hcop : Nat.Coprime p (2 ^ k) :=
    Nat.Coprime.pow_right k ((Nat.coprime_primes hp Nat.prime_two).2 hp2)
  have hy1 : π y = 1 := by
    have hd1 : orderOf (π y) ∣ p := orderOf_dvd_of_pow_eq_one h1
    have hd2 : orderOf (π y) ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one h2
    exact orderOf_eq_one_iff.1 (Nat.eq_one_of_dvd_coprimes hcop hd1 hd2)
  have hyI : y ∈ I := (QuotientGroup.eq_one_iff y).1 hy1
  exact I.mul_mem hi hyI

theorem isPGroup_quotient (hP : IsPGroup 2 ↥P) (hIP : I ⊔ P = ⊤) : IsPGroup 2 (Γ ⧸ I) := by
  intro q
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
  obtain ⟨i, hi, y, hy, rfl⟩ := exists_mul_of_sup_eq_top hIP x
  obtain ⟨k, hk⟩ := hP ⟨y, hy⟩
  refine ⟨k, ?_⟩
  have hyk : y ^ 2 ^ k = 1 := by
    have := congrArg Subtype.val hk
    simpa using this
  have hπi : (QuotientGroup.mk i : Γ ⧸ I) = 1 := (QuotientGroup.eq_one_iff i).2 hi
  rw [QuotientGroup.mk_mul, hπi, one_mul, ← QuotientGroup.mk_pow, hyk]
  rfl

theorem pRank_top_le_of_sup_eq_top (hP : IsPGroup 2 ↥P) (hIP : I ⊔ P = ⊤) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) : CFSG.Open.pRank p (⊤ : Subgroup Γ) ≤ CFSG.Open.pRank p (⊤ : Subgroup ↥I) := by
  have hp1 : 1 < p := hp.one_lt
  obtain ⟨E, -, hE, hcard⟩ := CFSG.SectionRank.exists_pRank hp1 (⊤ : Subgroup Γ)
  have hEI : E ≤ I := fun x hx =>
    mem_of_pow_prime_eq_one hP hIP hp hp2 (by
      have := hE.2 x hx
      exact this)
  rw [← CFSG.SectionRank.pRank_eq_pRank_top_subgroup I]
  exact CFSG.SectionRank.le_pRank hp1 hEI hE hcard

theorem exists_isSylowIn_ge (hP : IsPGroup 2 ↥P) :
    ∃ T : Subgroup Γ, IsSylowIn 2 T ⊤ ∧ P ≤ T := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q, hQ⟩ := hP.exists_le_sylow
  refine ⟨(Q : Subgroup Γ), ⟨le_top, Q.isPGroup', ?_⟩, hQ⟩
  rw [Subgroup.relIndex_top_right]
  exact Q.not_dvd_index

theorem almostSimple_bound {S : Type} [Group S] {ν : ℕ∞} (hE : EBound S ν)
    (hI : IsSimpleGroup ↥I) (hnab : ∃ x y : ↥I, x * y ≠ y * x)
    (hC : Subgroup.centralizer (I : Set Γ) = ⊥) (hP : IsPGroup 2 ↥P) (hIP : I ⊔ P = ⊤)
    (e : ↥I ≃* S) (hK : CFSG.SectionRank.IsKGroupCat ↥I)
    (hrk : ∀ p : ℕ, p.Prime → p ≠ 2 → CFSG.Open.pRank p (⊤ : Subgroup ↥I) ≤ 2) :
    E1.nParam (⊤ : Subgroup Γ) ≤ ν := by
  haveI := hI
  have hF : CFSG.generalizedFitting Γ = I :=
    CFSG.Adapters.generalizedFitting_eq_of_normal_simple_of_centralizer_eq_bot I hnab hC
  obtain ⟨T, hT, hPT⟩ := exists_isSylowIn_ge (Γ := Γ) hP
  have hsimple : IsSimpleGroup ↥(CFSG.generalizedFitting Γ) := by
    rw [hF]
    exact hI
  have hFT : CFSG.generalizedFitting Γ ⊔ T = ⊤ := by
    rw [hF]
    exact top_le_iff.1 (hIP ▸ sup_le_sup_left hPT I)
  have hsolv : Group.IsSolvable (Γ ⧸ I) := by
    haveI : Finite (Γ ⧸ I) := inferInstance
    haveI := (isPGroup_quotient hP hIP).isNilpotent
    infer_instance
  have hKΓ : CFSG.SectionRank.IsKGroupCat Γ := by
    refine CFSG.KCore.KGroupAllSimple.of_ker CFSG.SectionRank.catalog_isoInvariant
      (QuotientGroup.mk' I) ?_ ?_
    · exact CFSG.SectionRank.IsKGroupCat.of_mulEquiv hK
        (MulEquiv.subgroupCongr (QuotientGroup.ker_mk' I))
    · exact CFSG.KCore.KGroupAllSimple.of_isSolvable CFSG.SectionRank.catalog_containsAbelianSimple
        hsolv
  have hSQT : CFSG.Open.SQTKTauCeti.StronglyQuasithin Γ := fun p hp hp2 =>
    (pRank_top_le_of_sup_eq_top hP hIP hp hp2).trans (hrk p hp hp2)
  exact hE Γ T ⟨hSQT, hKΓ⟩ hsimple hT hFT ⟨(MulEquiv.subgroupCongr hF).trans e⟩

end AlmostSimple

end CFSG.Quasithin.H13.P31Sec
