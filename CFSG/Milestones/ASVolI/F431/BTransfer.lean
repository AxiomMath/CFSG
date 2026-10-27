module

public import CFSG.Quasithin.Background.F7Basic
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.Basic

public section

namespace CFSG.Quasithin

open scoped IsMulCommutative

variable {G : Type*} [Group G]

theorem burnsideF4m_generalized_thompson_transfer_oTwoRes [Finite G] {H K : Subgroup G}
    (hindex : Nat.Coprime 2 H.index) (hK : K ≤ H ∧ (K.subgroupOf H).Normal)
    (habel : ⁅H, H⁆ ≤ K) (hH : IsPGroup 2 H) {g : G} (hg : g ∈ H) (hgK : g ∉ K)
    (hg2 : orderOf g = 2) (h : ∀ a : G, a⁻¹ * g * a ∈ H → g⁻¹ * (a⁻¹ * g * a) ∈ K) :
    g ∉ oTwoRes (⊤ : Subgroup G) := by
  classical
  have := hK.2
  have hcomm : IsMulCommutative (H ⧸ K.subgroupOf H) := by
    rw [Subgroup.Normal.quotient_commutative_iff_commutator_le, commutator_def,
      Subgroup.commutator_le]
    intro x _ y _
    rw [Subgroup.mem_subgroupOf]
    exact habel (Subgroup.commutator_mem_commutator x.2 y.2)
  have hg2' : g ^ 2 = 1 := hg2 ▸ pow_orderOf_eq_one g
  have h' : ∀ (m : ℤ) (a : G), a⁻¹ * g ^ m * a ∈ H → (g ^ m)⁻¹ * (a⁻¹ * g ^ m * a) ∈ K := by
    intro m a ha
    rcases Int.even_or_odd' m with ⟨j, rfl | rfl⟩
    · have : g ^ (2 * j) = 1 := by rw [zpow_mul]; simp [hg2']
      rw [this] at ha ⊢
      simp
    · have : g ^ (2 * j + 1) = g := by rw [zpow_add, zpow_mul]; simp [hg2']
      rw [this] at ha ⊢
      exact h a ha
  let ϕ : H →* H ⧸ K.subgroupOf H := QuotientGroup.mk' (K.subgroupOf H)
  have hV := transfer_eq_pow_of_forall ϕ hg (by
    intro k a ha
    rw [eq_comm, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq,
      Subgroup.mem_subgroupOf]
    have := h' k a (by simpa using ha)
    simpa using this)
  have hz2 : ϕ ⟨g, hg⟩ ^ 2 = 1 := by
    rw [← map_pow]
    have : (⟨g, hg⟩ : H) ^ 2 = 1 := Subtype.ext (by simpa using hg2')
    rw [this, map_one]
  have hz1 : ϕ ⟨g, hg⟩ ≠ 1 := by
    intro h1
    apply hgK
    exact Subgroup.mem_subgroupOf.1 ((QuotientGroup.eq_one_iff (⟨g, hg⟩ : H)).1 h1)
  have hVg : MonoidHom.transfer ϕ g ≠ 1 := by
    rw [hV]
    intro h1
    apply hz1
    have := pow_gcd_eq_one.2 ⟨hz2, h1⟩
    rwa [hindex, pow_one] at this
  have hq : IsPGroup 2 (H ⧸ K.subgroupOf H) := hH.to_quotient (K.subgroupOf H)
  have hker : oTwoRes (⊤ : Subgroup G) ≤ (MonoidHom.transfer ϕ).ker := by
    refine (Subgroup.closure_le _).2 ?_
    rintro x ⟨-, m, hm, hxm⟩
    rw [SetLike.mem_coe, MonoidHom.mem_ker]
    obtain ⟨k, hk⟩ := hq (MonoidHom.transfer ϕ x)
    have h1 : MonoidHom.transfer ϕ x ^ m = 1 := by rw [← map_pow, hxm, map_one]
    have hcop : Nat.Coprime m (2 ^ k) := Nat.Coprime.pow_right k (Odd.coprime_two_right hm)
    have := pow_gcd_eq_one.2 ⟨h1, hk⟩
    rwa [hcop, pow_one] at this
  intro hgres
  exact hVg (hker hgres)

end CFSG.Quasithin

namespace CFSG.QuasithinUnique.Lin2

open CFSG.Quasithin

variable {G : Type*} [Group G]

theorem burnsideF4m_transfer_contradiction_cyclic_oTwoRes [Finite G]
    (hres : oTwoRes (⊤ : Subgroup G) = ⊤)
    {T N : Subgroup G} (hT : IsSylowTwoOf T ⊤) (hNT : N ≤ T)
    (hN : T ≤ Subgroup.normalizer (N : Set G)) {t₀ : G} (hcyc : T = N ⊔ Subgroup.zpowers t₀)
    {t : G} (htT : t ∈ T) (htN : t ∉ N) (ht2 : t ^ 2 = 1)
    (hfus : ∀ g : G, g⁻¹ * t * g ∉ N) : False := by
  have hindex : Nat.Coprime 2 T.index := by
    rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_two]
    have := hT.2.2
    have e : (T.subgroupOf ⊤).index = T.index := Subgroup.relIndex_top_right T
    rwa [e] at this
  have hnorm : (N.subgroupOf T).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hN
  have hcomm := commutator_le_of_sup_zpowers hNT hN hcyc
  have hord : orderOf t = 2 := orderOf_eq_prime ht2 (fun h => htN (h ▸ N.one_mem))
  have key := burnsideF4m_generalized_thompson_transfer_oTwoRes hindex ⟨hNT, hnorm⟩ hcomm hT.2.1
    htT htN hord (by
    intro a ha
    have ha2 : (a⁻¹ * t * a) ^ 2 = 1 := by
      have : (a⁻¹ * t * a) ^ 2 = a⁻¹ * t ^ 2 * a := by simp only [pow_two]; group
      rw [this, ht2]; simp
    have := inv_mul_mem_of_sq_eq_one hNT hN hcyc htT ha ht2 ha2 htN (hfus a)
    simpa using this)
  exact key (by rw [hres]; exact Subgroup.mem_top t)

end CFSG.QuasithinUnique.Lin2
