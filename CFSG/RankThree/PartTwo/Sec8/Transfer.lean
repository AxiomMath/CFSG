module

public import CFSG.RankThree.PartTwo.Setup
public import CFSG.GH74.GLS.Basic

public section

namespace CFSG.RankThree.PartTwo.Sec8

open CFSG

variable {G : Type*} [Group G]

theorem transfer_eq_pow_of_forall_map_conj {H : Subgroup G} [H.FiniteIndex] {A : Type*}
    [CommGroup A] (ϕ : H →* A) {g : G} (hg : g ∈ H)
    (key : ∀ (k : ℕ) (g₀ : G) (hk : g₀⁻¹ * g ^ k * g₀ ∈ H),
      ϕ ⟨g₀⁻¹ * g ^ k * g₀, hk⟩ = ϕ ⟨g, hg⟩ ^ k) :
    ϕ.transfer g = ϕ ⟨g, hg⟩ ^ H.index := by
  classical
  let := H.fintypeQuotientOfFiniteIndex
  rw [MonoidHom.transfer_eq_prod_quotient_orbitRel_zpowers_quot, H.index_eq_sum_minimalPeriod g,
    ← Finset.prod_pow_eq_pow_sum]
  exact Finset.prod_congr rfl fun q _ => key _ _ _

theorem commutator_ne_top_of_transfer {p : ℕ} [Fact p.Prime] [Finite G] (P : Sylow p G)
    {A : Type*} [CommGroup A] (ϕ : (P : Subgroup G) →* A) {r : G} (hr : r ∈ (P : Subgroup G))
    (hϕr : ϕ ⟨r, hr⟩ ≠ 1)
    (key : ∀ (k : ℕ) (g₀ : G) (hk : g₀⁻¹ * r ^ k * g₀ ∈ (P : Subgroup G)),
      ϕ ⟨g₀⁻¹ * r ^ k * g₀, hk⟩ = ϕ ⟨r, hr⟩ ^ k) :
    commutator G ≠ ⊤ := by
  intro htop
  have hT := transfer_eq_pow_of_forall_map_conj ϕ hr key
  have h1 : ϕ.transfer r = 1 := by
    have hmem : r ∈ commutator G := htop ▸ Subgroup.mem_top r
    exact MonoidHom.mem_ker.mp (Abelianization.commutator_subset_ker ϕ.transfer hmem)
  obtain ⟨n, hn⟩ := P.isPGroup' ⟨r, hr⟩
  have hpn : ϕ ⟨r, hr⟩ ^ p ^ n = 1 := by rw [← map_pow, hn, map_one]
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow (Fact.out : p.Prime)).mp (orderOf_dvd_of_pow_eq_one hpn)
  have hj0 : j ≠ 0 := by
    rintro rfl
    exact hϕr (orderOf_eq_one_iff.mp (by simpa using hj))
  have hdvd : orderOf (ϕ ⟨r, hr⟩) ∣ (P : Subgroup G).index :=
    orderOf_dvd_of_pow_eq_one (by rw [← hT]; exact h1)
  rw [hj] at hdvd
  exact P.not_dvd_index ((dvd_pow_self p hj0).trans hdvd)

theorem rank3II_transfer {p : ℕ} [Fact p.Prime] [Finite G] (P : Sylow p G) {U : Subgroup G}
    (hUn : ∀ x ∈ (P : Subgroup G), ∀ u ∈ U, x * u * x⁻¹ ∈ U)
    (habel : ∀ x ∈ (P : Subgroup G), ∀ y ∈ (P : Subgroup G), x * y * x⁻¹ * y⁻¹ ∈ U)
    {r : G} (hr : r ∈ (P : Subgroup G)) (hrU : r ∉ U)
    (hfus : ∀ (k : ℕ) (h : G), h⁻¹ * r ^ k * h ∈ (P : Subgroup G) →
      (r ^ k)⁻¹ * (h⁻¹ * r ^ k * h) ∈ U) :
    commutator G ≠ ⊤ := by
  set U' : Subgroup (P : Subgroup G) := U.subgroupOf P
  have hU'n : U'.Normal := ⟨fun u hu x => Subgroup.mem_subgroupOf.mpr
    (hUn x x.2 u (Subgroup.mem_subgroupOf.mp hu))⟩
  have hcomm : ∀ a b : (P : Subgroup G) ⧸ U', a * b = b * a := by
    intro a b
    induction a using QuotientGroup.induction_on with
    | H x =>
    induction b using QuotientGroup.induction_on with
    | H y =>
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
    refine Subgroup.mem_subgroupOf.mpr ?_
    have := habel (y : G)⁻¹ (Subgroup.inv_mem _ y.2) (x : G)⁻¹ (Subgroup.inv_mem _ x.2)
    simpa [mul_assoc] using this
  let : CommGroup ((P : Subgroup G) ⧸ U') :=
    { QuotientGroup.Quotient.group U' with mul_comm := hcomm }
  let ϕ : (P : Subgroup G) →* (P : Subgroup G) ⧸ U' := QuotientGroup.mk' U'
  refine commutator_ne_top_of_transfer P ϕ hr ?_ ?_
  · intro h1
    exact hrU (Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff _).mp h1))
  · intro k g₀ hk
    rw [← map_pow]
    change (QuotientGroup.mk' U' _ : _) = QuotientGroup.mk' U' _
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, eq_comm, QuotientGroup.eq]
    exact Subgroup.mem_subgroupOf.mpr (by simpa using hfus k g₀ hk)

theorem rank3II_transfer_false {G : Type} [Group G] [Finite G] (hG : TheoremFourHyp G)
    {p : ℕ} [Fact p.Prime] (P : Sylow p G) {U : Subgroup G}
    (hUn : ∀ x ∈ (P : Subgroup G), ∀ u ∈ U, x * u * x⁻¹ ∈ U)
    (habel : ∀ x ∈ (P : Subgroup G), ∀ y ∈ (P : Subgroup G), x * y * x⁻¹ * y⁻¹ ∈ U)
    {r : G} (hr : r ∈ (P : Subgroup G)) (hrU : r ∉ U)
    (hfus : ∀ (k : ℕ) (h : G), h⁻¹ * r ^ k * h ∈ (P : Subgroup G) →
      (r ^ k)⁻¹ * (h⁻¹ * r ^ k * h) ∈ U) :
    False := by
  refine rank3II_transfer P hUn habel hr hrU hfus ?_
  have := hG.isSimpleGroup
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator G) with h | h
  · obtain ⟨a, b, hab⟩ := hG.nonabelian
    exact absurd ((commutator_eq_bot_iff G).mp h) fun hc => hab (hc.is_comm.comm a b)
  · exact h

theorem exists_coprime_orderOf_ne_one {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (hnab : ∃ a b : G, a * b ≠ b * a) (p : ℕ) [hp : Fact p.Prime] :
    ∃ x : G, x ≠ 1 ∧ Nat.Coprime (orderOf x) p := by
  by_contra hcon
  have hP : IsPGroup p G := by
    intro g
    obtain ⟨a, m, hm, hn⟩ :=
      Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos g).ne' p hp.out.one_lt.ne'
    refine ⟨a, ?_⟩
    by_contra hne
    have hdvd : p ^ a ∣ orderOf g := ⟨m, hn⟩
    have hord : orderOf (g ^ p ^ a) = m := by
      rw [orderOf_pow_of_dvd (pow_ne_zero a hp.out.ne_zero) hdvd, hn,
        Nat.mul_div_cancel_left m (pow_pos hp.out.pos a)]
    have hcop : Nat.Coprime (orderOf (g ^ p ^ a)) p := by
      rw [hord]
      exact (Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hp.out).mpr hm))
    exact hcon ⟨g ^ p ^ a, hne, hcop⟩
  have : Nontrivial G := by
    obtain ⟨a, b, hab⟩ := hnab
    exact ⟨⟨a * b, b * a, hab⟩⟩
  have hZ := hP.bot_lt_center
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center G) with h | h
  · exact hZ.ne' h
  · obtain ⟨a, b, hab⟩ := hnab
    exact hab (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top b) a)

theorem _root_.CFSG.RankThree.PartTwo.TheoremFourHyp.oResidual_eq_top {G : Type} [Group G]
    [Finite G] (hG : TheoremFourHyp G) (p : ℕ) [Fact p.Prime] :
    CFSG.GH74.GLS.oResidual p G = ⊤ := by
  have := hG.isSimpleGroup
  obtain ⟨x, hx1, hx⟩ := exists_coprime_orderOf_ne_one hG.nonabelian p
  have hN : Subgroup.normalClosure ({x} : Set G) = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.normalClosure ({x} : Set G))
      with h | h
    · exact absurd ((Subgroup.mem_bot).mp (h ▸ Subgroup.subset_normalClosure rfl)) hx1
    · exact h
  rw [eq_top_iff, ← hN]
  refine Subgroup.closure_mono fun y hy => ?_
  obtain ⟨z, hz, hzy⟩ := Group.mem_conjugatesOfSet_iff.mp hy
  rw [Set.mem_singleton_iff] at hz
  subst hz
  obtain ⟨c, hc⟩ := hzy
  show Nat.Coprime (orderOf y) p
  rw [← SemiconjBy.orderOf_eq (c : G) hc]
  exact hx

end CFSG.RankThree.PartTwo.Sec8
