module

public import CFSG.RankThree.PartOne.S11c.Sec66Exc
public import CFSG.RankThree.Chevalley.SteinbergBTEvenE6Noninner

public section

namespace CFSG.RankThree.PartOne.Sec66T

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.Chevalley SteinbergBT
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.Assembly.LowTwoRank (StatedLieTag StatedLieAdmissible)

theorem admissible_E6 {f : ℕ} (hf : 1 ≤ f) : StatedLieAdmissible .E6 0 2 f :=
  ⟨Nat.prime_two, hf, rfl⟩

theorem untwistedTag_E6 : untwistedTag .E6 = some Tag.E6 := rfl

theorem sec66T_K2_E6 :
    Sec66T_K2 .E6 := by
  intro T _ _ p hp hp5 hmodel _ E hE hcard hEinn _hra
  obtain ⟨n, f, hadm, hM⟩ := hmodel
  obtain ⟨K, hKf, hKfin, hKcard, ⟨e⟩⟩ := exists_adjoint_equiv untwistedTag_E6 hM
  have hf : 1 ≤ f := hadm.2.1
  obtain ⟨Φ, -, -, hΦcard⟩ := exists_outer_hom_E (τ := Tag.E6) (K := K) (Or.inl rfl)
  have h3 : Nat.card Φ.ker ∣ 3 := by
    rw [det_cartan_E6] at hΦcard
    exact hΦcard
  have : IsCyclic (K ≃+* K) := isCyclic_ringAut hf hKcard
  let π : MulAut T →* Outer (adjointGroup Tag.E6 K) :=
    (QuotientGroup.mk' (CFSG.ComponentClassification.OuterAutomorphisms.inner _)).comp
      (MulAut.congr e).toMonoidHom
  let φ : MulAut T →* (K ≃+* K) := (MonoidHom.fst _ _).comp (Φ.comp π)
  refine no_plane_of_cyclic_quotient hp φ ?_ E hE hcard hEinn
  intro x hx hxp
  have hΦx : (Φ (π x)).1 = 1 := hx
  have hyp : (Φ (π x)) ^ p = 1 := by
    rw [← map_pow, ← map_pow, hxp, map_one, map_one]
  have hp2 : Odd p := hp.odd_of_ne_two (by omega)
  have hy2 : (Φ (π x)).2 = 1 := by
    have h1 : (Φ (π x)).2 ^ p = 1 := congrArg Prod.snd hyp
    have h2 : ∀ z : Multiplicative (ZMod (exactE Tag.E6)), z ^ 2 = 1 := by
      show ∀ z : Multiplicative (ZMod 2), z ^ 2 = 1
      decide
    obtain ⟨k, hk⟩ := hp2
    have h3' : (Φ (π x)).2 = (Φ (π x)).2 ^ p := by
      rw [hk, pow_succ, pow_mul, h2, one_pow, one_mul]
    rw [h3', h1]
  have hy1 : Φ (π x) = 1 := Prod.ext hΦx hy2
  have hker : π x ∈ Φ.ker := hy1
  have hord1 : orderOf (π x) ∣ p :=
    orderOf_dvd_of_pow_eq_one (by rw [← map_pow, hxp, map_one])
  have hord2 : orderOf (π x) ∣ 3 := by
    have h4 : orderOf (⟨π x, hker⟩ : Φ.ker) ∣ Nat.card Φ.ker := orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk] at h4
    exact h4.trans h3
  have hcop : Nat.Coprime p 3 := (Nat.coprime_primes hp Nat.prime_three).mpr (by omega)
  have hord : orderOf (π x) = 1 := Nat.eq_one_of_dvd_coprimes hcop hord1 hord2
  have hπ1 : π x = 1 := orderOf_eq_one_iff.mp hord
  have hmem : MulAut.congr e x ∈
      CFSG.ComponentClassification.OuterAutomorphisms.inner (adjointGroup Tag.E6 K) :=
    (QuotientGroup.eq_one_iff _).mp hπ1
  exact (mem_innerAut_congr e x).mp hmem

theorem sec66T_K1_E6 :
    Sec66T_K1 .E6 := by
  intro T _ _ p hp hp5 hmodel _ α q U hord hαinn hq1 hqp hαq hU1 hU2 hαU hqU _hmv _hra
  obtain ⟨n, f, hadmf, hM⟩ := hmodel
  have hn0 : n = 0 := ((lieModel_untwisted_iff untwistedTag_E6).mp hM).1
  subst hn0
  obtain ⟨K, hKf, hKfin, hKcard, ⟨e⟩⟩ := exists_adjoint_equiv untwistedTag_E6 hM
  have hf : 1 ≤ f := hadmf.2.1
  set α' : MulAut (adjointGroup Tag.E6 K) := MulAut.congr e α with hα'
  have hα'ord : orderOf α' = p := (orderOf_congr e α).trans hord
  have hα'inn : α' ∉ (MulAut.conj : adjointGroup Tag.E6 K →*
      MulAut (adjointGroup Tag.E6 K)).range :=
    fun h => hαinn ((mem_innerAut_congr e α).mp h)
  obtain ⟨Θ, -, hΘ, -⟩ := ordinary_E_field_graph_quotient_and_involutions Tag.E6 (Or.inl rfl) K
  obtain ⟨⟨σ, -, hσord, ψ, hψ⟩, hpf, -⟩ :=
    even_E6_noninner_large_prime_field_descent_and_local_core_trivial hf K hKcard Θ hΘ hp
      (by omega) ⊤ le_top ⟨α', Subgroup.mem_top _⟩ hα'inn
      (by rw [Subgroup.orderOf_mk]; exact hα'ord)
  obtain ⟨f', hff'⟩ := hpf
  have hf'pos : 1 ≤ f' := one_le_of_mul_eq hf hff'
  obtain ⟨σ₀, hσ₀, hzp⟩ := exists_canonical_generator hf hKcard hσord hp.pos hff'
  have hσ₀ord : orderOf σ₀ = p := by
    rw [← Nat.card_zpowers, ← hzp, Nat.card_zpowers, hσord]
  have hfix_eq : fixSub (ψ * MulAut.congr e α * ψ⁻¹) = fixSub (entrywiseAdjointAut Tag.E6 σ₀) := by
    have h1 : ψ * MulAut.congr e α * ψ⁻¹ = entrywiseAdjointAut Tag.E6 σ := hψ
    rw [h1]
    apply fixSub_eq_of_zpowers_eq
    have h2 := congrArg (Subgroup.map (entrywiseAdjointAutHom (τ := Tag.E6) (K := K))) hzp
    rw [MonoidHom.map_zpowers, MonoidHom.map_zpowers] at h2
    exact h2
  have hm : 2 ≤ p := hp.two_le
  have hK' : Nat.card K = 2 ^ (f' * p) := by rw [hKcard, hff', mul_comm]
  obtain ⟨-, -, hder, hJC0, hsimple0, hnc0, -⟩ :=
    even_E6_canonical_field_derived_subgroup_and_pointwise_centralizer hf'pos hm K hK' σ₀ hσ₀
  have hJC : fixedFieldImage Tag.E6 σ₀ ≤ adjointGroup Tag.E6 K := hJC0
  have hsimple : IsSimpleGroup ↥(fixedFieldImage Tag.E6 σ₀) := hsimple0
  have hnc : ¬∀ a b : ↥(fixedFieldImage Tag.E6 σ₀), a * b = b * a := hnc0
  set Γ : Subgroup ↥(adjointGroup Tag.E6 K) := fixSub (entrywiseAdjointAut Tag.E6 σ₀) with hΓ
  set N : Subgroup ↥(adjointGroup Tag.E6 K) :=
    (fixedFieldImage Tag.E6 σ₀).subgroupOf (adjointGroup Tag.E6 K) with hN
  have hder' : ⁅Γ, Γ⁆ = N := hder
  have hNsub : N.subgroupOf Γ = commutator ↥Γ := by
    rw [← hder', ← Subgroup.map_subtype_commutator]
    exact Subgroup.comap_map_eq_self_of_injective Γ.subtype_injective _
  have hNΓ : N ≤ Γ := hder' ▸ Subgroup.commutator_le_self Γ
  have hNnormal : (N.subgroupOf Γ).Normal := by
    rw [hNsub]
    exact inferInstance
  have hsolv : Group.IsSolvable (↥Γ ⧸ N.subgroupOf Γ) := by
    have : (N.subgroupOf Γ).Normal := hNnormal
    have : CommGroup (↥Γ ⧸ commutator ↥Γ) := inferInstanceAs (CommGroup (Abelianization ↥Γ))
    have : Group.IsSolvable (↥Γ ⧸ commutator ↥Γ) := inferInstance
    exact Group.isSolvable_of_surjective
      (f := (QuotientGroup.quotientMulEquivOfEq hNsub.symm).toMonoidHom)
      (QuotientGroup.quotientMulEquivOfEq hNsub.symm).surjective
  have hnc' : ∃ a b : ↥(fixedFieldImage Tag.E6 σ₀), a * b ≠ b * a := by
    push Not at hnc
    exact hnc
  have hJperf : Group.IsPerfect ↥(fixedFieldImage Tag.E6 σ₀) := by
    have := hsimple
    exact isPerfect_of_simple_nonabelian hnc'
  have hNperf : Group.IsPerfect ↥N :=
    Group.IsPerfect.ofSurjective (f := (Subgroup.subgroupOfEquivOfLe hJC).symm.toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hJC).symm.surjective
  have hZk : Subgroup.center (adjointGroup Tag.E6 (fixSubfield σ₀)) = ⊥ :=
    center_adjointGroup_eq_bot
  let eN : ↥N ⧸ Subgroup.center ↥N ≃* AdjointQuotient Tag.E6 (fixSubfield σ₀) :=
    centerQuotientCongr ((Subgroup.subgroupOfEquivOfLe hJC).trans (fixedFieldImageEquiv σ₀).symm)
  obtain ⟨hdvd, hkcard⟩ := card_fixSubfield Nat.prime_two hf hKcard σ₀
  have hkcard' : Nat.card (fixSubfield σ₀) = 2 ^ f' := by
    rw [hkcard, hσ₀ord, hff', Nat.mul_div_cancel_left f' hp.pos]
  have hXmodel : LieModel (AdjointQuotient Tag.E6 (fixSubfield σ₀)) .E6 0 2 f' :=
    (lieModel_untwisted_iff untwistedTag_E6).mpr ⟨rfl, admissible_E6 hf'pos, fixSubfield σ₀,
      inferInstance, inferInstance, hkcard', ⟨MulEquiv.refl _⟩⟩
  have hfix : LieModel (↥(fixRes (entrywiseAdjointAut Tag.E6 σ₀)) ⧸
      Subgroup.center ↥(fixRes (entrywiseAdjointAut Tag.E6 σ₀))) .E6 0 2 f' :=
    lieModel_fixRes_of_normal hNΓ hNnormal hNperf hsolv eN hXmodel
  exact fieldAutT_of_conj_fix' e hM hff' hf'pos α (entrywiseAdjointAut Tag.E6 σ₀) ψ hfix_eq hfix

end CFSG.RankThree.PartOne.Sec66T
