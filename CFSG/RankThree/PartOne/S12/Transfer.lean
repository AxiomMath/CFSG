module

public import CFSG.RankThree.PartOne.S9.Defs

public section

namespace CFSG.RankThree.PartOne

namespace Transfer

open MulAction Subgroup

theorem transfer_apply_eq_pow_index {G : Type*} [Group G] [Finite G] {P : Subgroup G}
    {A : Type*} [CommGroup A] (ϕ : P →* A) {p : ℕ} [Fact p.Prime] {c : G} (hc : c ∈ P)
    (hcp : orderOf c = p)
    (hconj : ∀ x : G, ∀ h : x⁻¹ * c * x ∈ P, ϕ ⟨x⁻¹ * c * x, h⟩ = ϕ ⟨c, hc⟩) :
    MonoidHom.transfer ϕ c = ϕ ⟨c, hc⟩ ^ P.index := by
  have : Fintype (Quotient (orbitRel (zpowers c) (G ⧸ P))) := Fintype.ofFinite _
  have hpow : c ^ p = 1 := hcp ▸ pow_orderOf_eq_one c
  have key : ∀ (k : ℕ) (x : G) (hk : x⁻¹ * c ^ k * x ∈ P), k = 1 ∨ k = p →
      ϕ ⟨x⁻¹ * c ^ k * x, hk⟩ = ϕ ⟨c, hc⟩ ^ k := by
    rintro k x hk (rfl | rfl)
    · simpa using hconj x (by simpa using hk)
    · have h1 : (⟨x⁻¹ * c ^ k * x, hk⟩ : P) = 1 := Subtype.ext (by simp [hpow])
      have h2 : (⟨c, hc⟩ : P) ^ k = 1 := Subtype.ext (by simp [hpow])
      rw [h1, ← map_pow, h2]
  rw [MonoidHom.transfer_eq_prod_quotient_orbitRel_zpowers_quot, index_eq_sum_minimalPeriod P c,
    ← Finset.prod_pow_eq_pow_sum]
  refine Finset.prod_congr rfl fun q _ => key _ _ _ ?_
  refine (Nat.dvd_prime Fact.out).mp (pow_smul_eq_iff_minimalPeriod_dvd.mp ?_)
  rw [hpow, one_smul]

end Transfer

open scoped IsMulCommutative in
theorem exists_normal_pGroup_quotient_notMem_of_fusion {G : Type} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] {P Q : Subgroup G} (hP : IsSylowOf p P ⊤) (hQP : Q ≤ P)
    (hQn : (Q.subgroupOf P).Normal)
    (hab : ∀ x y : P, x * y * x⁻¹ * y⁻¹ ∈ Q.subgroupOf P)
    {c : G} (hc : c ∈ P) (hcp : orderOf c = p) (hcQ : c ∉ Q)
    (hfus : ∀ g : G, g * c * g⁻¹ ∈ P → ∃ q ∈ Q, g * c * g⁻¹ = c * q) :
    ∃ N : Subgroup G, ∃ _ : N.Normal, c ∉ N ∧ IsPGroup p (G ⧸ N) := by
  have hcomm : _root_.commutator P ≤ Q.subgroupOf P := by
    rw [commutator_def, Subgroup.commutator_le]
    intro x _ y _
    simpa [commutatorElement_def] using hab x y
  have : IsMulCommutative (P ⧸ Q.subgroupOf P) :=
    Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr hcomm
  let ϕ : P →* P ⧸ Q.subgroupOf P := QuotientGroup.mk' (Q.subgroupOf P)
  have hconj : ∀ x : G, ∀ h : x⁻¹ * c * x ∈ P, ϕ ⟨x⁻¹ * c * x, h⟩ = ϕ ⟨c, hc⟩ := by
    intro x h
    obtain ⟨q, hq, hqe⟩ := hfus x⁻¹ (by simpa using h)
    have hsplit : (⟨x⁻¹ * c * x, h⟩ : P) = ⟨c, hc⟩ * ⟨q, hQP hq⟩ :=
      Subtype.ext (by simpa using hqe)
    have hq1 : ϕ ⟨q, hQP hq⟩ = 1 :=
      (QuotientGroup.eq_one_iff (N := Q.subgroupOf P) _).mpr (Subgroup.mem_subgroupOf.mpr hq)
    rw [hsplit, map_mul, hq1, mul_one]
  have hVc : MonoidHom.transfer ϕ c = ϕ ⟨c, hc⟩ ^ P.index :=
    Transfer.transfer_apply_eq_pow_index ϕ hc hcp hconj
  have hindex : ¬ p ∣ P.index := by
    simpa [Subgroup.relIndex_top_right] using hP.2.2
  have hpow : ϕ ⟨c, hc⟩ ^ p = 1 := by
    rw [← map_pow]
    have : (⟨c, hc⟩ : P) ^ p = 1 := Subtype.ext (by simp [← hcp])
    rw [this, map_one]
  have hne : ϕ ⟨c, hc⟩ ≠ 1 := fun h =>
    hcQ (Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff (N := Q.subgroupOf P) _).mp h))
  have hord : orderOf (ϕ ⟨c, hc⟩) = p := orderOf_eq_prime hpow hne
  have hVne : MonoidHom.transfer ϕ c ≠ 1 := by
    intro h
    rw [hVc] at h
    exact hindex (hord ▸ orderOf_dvd_of_pow_eq_one h)
  refine ⟨(MonoidHom.transfer ϕ).ker, inferInstance, fun h => hVne (MonoidHom.mem_ker.mp h), ?_⟩
  exact (hP.2.1.to_quotient (Q.subgroupOf P)).of_injective
    (QuotientGroup.kerLift (MonoidHom.transfer ϕ))
    (QuotientGroup.kerLift_injective (MonoidHom.transfer ϕ))

theorem exists_proper_normal_pGroup_quotient_of_fusion {G : Type} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] {P Q : Subgroup G} (hP : IsSylowOf p P ⊤) (hQP : Q ≤ P)
    (hQn : (Q.subgroupOf P).Normal)
    (hab : ∀ x y : P, x * y * x⁻¹ * y⁻¹ ∈ Q.subgroupOf P)
    {c : G} (hc : c ∈ P) (hcp : orderOf c = p) (hcQ : c ∉ Q)
    (hfus : ∀ g : G, g * c * g⁻¹ ∈ P → ∃ q ∈ Q, g * c * g⁻¹ = c * q) :
    ∃ N : Subgroup G, ∃ _ : N.Normal, N ≠ ⊤ ∧ IsPGroup p (G ⧸ N) := by
  obtain ⟨N, hN, hcN, hNp⟩ :=
    exists_normal_pGroup_quotient_notMem_of_fusion hP hQP hQn hab hc hcp hcQ hfus
  exact ⟨N, hN, fun h => hcN (h ▸ Subgroup.mem_top c), hNp⟩

theorem false_of_fusion_simple {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) {p : ℕ} [Fact p.Prime] {P Q : Subgroup G}
    (hP : IsSylowOf p P ⊤) (hQP : Q ≤ P) (hQn : (Q.subgroupOf P).Normal)
    (hab : ∀ x y : P, x * y * x⁻¹ * y⁻¹ ∈ Q.subgroupOf P)
    {c : G} (hc : c ∈ P) (hcp : orderOf c = p) (hcQ : c ∉ Q)
    (hfus : ∀ g : G, g * c * g⁻¹ ∈ P → ∃ q ∈ Q, g * c * g⁻¹ = c * q) : False := by
  obtain ⟨N, hN, hNtop, hNp⟩ :=
    exists_proper_normal_pGroup_quotient_of_fusion hP hQP hQn hab hc hcp hcQ hfus
  have hNbot : N = ⊥ := (IsSimpleGroup.eq_bot_or_eq_top_of_normal N).resolve_right hNtop
  subst hNbot
  have hG : IsPGroup p G := hNp.of_equiv QuotientGroup.quotientBot
  have hcenter : Subgroup.center G = ⊤ :=
    (IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center G)).resolve_left
      hG.bot_lt_center.ne'
  obtain ⟨a, b, hba⟩ := hnonab
  exact hba ((Subgroup.mem_center_iff.mp (hcenter ▸ Subgroup.mem_top b)) a)

end CFSG.RankThree.PartOne
