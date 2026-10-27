module

public import CFSG.Quasithin.Background.A1cTransfer

public section

namespace CFSG.Quasithin

open scoped IsMulCommutative

theorem thompson_transfer_exists_normal {X : Type*} [Group X] [Finite X] (P : Sylow 2 X)
    {Q : Subgroup X} (hQP : Q ≤ P) (hindex : Q.relIndex (P : Subgroup X) = 2) {u : X}
    (hu : orderOf u = 2) (hQu : ∀ x : X, x⁻¹ * u * x ∉ Q) :
    ∃ N : Subgroup X, N.Normal ∧ (∀ x : X, x ^ 2 ∈ N) ∧ u ∉ N := by
  classical
  have hu2 : u ^ 2 = 1 := hu ▸ pow_orderOf_eq_one u
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hup : IsPGroup 2 (Subgroup.zpowers u) := by
    rw [IsPGroup.iff_card, Nat.card_zpowers, hu]
    exact ⟨1, by simp⟩
  obtain ⟨T, hT⟩ := hup.exists_le_sylow
  obtain ⟨y, hy⟩ := MulAction.exists_smul_eq X T P
  have hgP : y * u * y⁻¹ ∈ (P : Subgroup X) := by
    subst hy
    have hu' : u ∈ (T : Subgroup X) := hT (Subgroup.mem_zpowers u)
    have h2 : y * u * y⁻¹ ∈ ((y • T : Sylow 2 X) : Subgroup X) := by
      rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
      exact ⟨u, hu', by simp [MulAut.conj_apply]⟩
    exact h2
  set g := y * u * y⁻¹ with hgdef
  have hg2 : g ^ 2 = 1 := by
    rw [hgdef, conj_pow, hu2]; simp
  set P' : Subgroup X := (P : Subgroup X) with hP'
  set Q' : Subgroup P' := Q.subgroupOf P' with hQ'
  have hQ'index : Q'.index = 2 := hindex
  have : Q'.Normal := Subgroup.normal_of_index_eq_two hQ'index
  have hcard : Nat.card (P' ⧸ Q') = 2 := by rw [← Subgroup.index_eq_card]; exact hQ'index
  have : IsCyclic (P' ⧸ Q') := isCyclic_of_prime_card hcard
  let ϕ : P' →* P' ⧸ Q' := QuotientGroup.mk' Q'
  have hgnot : (⟨g, hgP⟩ : P') ∉ Q' := by
    intro hmem
    apply hQu y⁻¹
    simpa [hgdef] using Subgroup.mem_subgroupOf.1 hmem
  have hconjnot : ∀ (a : X) (ha : a⁻¹ * g * a ∈ P'), (⟨a⁻¹ * g * a, ha⟩ : P') ∉ Q' := by
    intro a ha hmem
    apply hQu (y⁻¹ * a)
    have := Subgroup.mem_subgroupOf.1 hmem
    simpa [hgdef, mul_assoc] using this
  have hV := transfer_eq_pow_of_forall ϕ hgP (by
    intro k a ha
    rcases Nat.even_or_odd' k with ⟨j, rfl | rfl⟩
    · have h1 : g ^ (2 * j) = 1 := by rw [pow_mul, hg2, one_pow]
      have h2 : (⟨a⁻¹ * g ^ (2 * j) * a, ha⟩ : P') = 1 := Subtype.ext (by simp [h1])
      have h3 : (⟨g ^ (2 * j), P'.pow_mem hgP _⟩ : P') = 1 := Subtype.ext (by simp [h1])
      rw [h2, h3]
    · have h1 : g ^ (2 * j + 1) = g := by rw [pow_succ, pow_mul, hg2, one_pow, one_mul]
      have e1 : (⟨g ^ (2 * j + 1), P'.pow_mem hgP _⟩ : P') = ⟨g, hgP⟩ := Subtype.ext h1
      have ha' : a⁻¹ * g * a ∈ P' := by rwa [h1] at ha
      have e2 : (⟨a⁻¹ * g ^ (2 * j + 1) * a, ha⟩ : P') = ⟨a⁻¹ * g * a, ha'⟩ :=
        Subtype.ext (by show a⁻¹ * g ^ (2 * j + 1) * a = a⁻¹ * g * a; rw [h1])
      rw [e1, e2, eq_comm, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq,
        Subgroup.mul_mem_iff_of_index_two hQ'index]
      simp only [inv_mem_iff]
      exact iff_of_false hgnot (hconjnot a ha'))
  set z : P' ⧸ Q' := ϕ ⟨g, hgP⟩ with hz
  have hz1 : z ≠ 1 := fun h => hgnot ((QuotientGroup.eq_one_iff _).1 h)
  have hsq : ∀ w : P' ⧸ Q', w ^ 2 = 1 := fun w => by
    simpa [hcard] using pow_card_eq_one' (G := P' ⧸ Q') (x := w)
  have hodd : Odd P'.index := by
    have := P.not_dvd_index
    exact Nat.odd_iff.2 (Nat.two_dvd_ne_zero.1 this)
  have hVg : MonoidHom.transfer ϕ g = z := by
    rw [hV]
    obtain ⟨k, hk⟩ := hodd
    rw [hk, pow_succ, pow_mul, hsq z, one_pow, one_mul]
  refine ⟨(MonoidHom.transfer ϕ).ker, inferInstance, fun x => ?_, fun hupres => ?_⟩
  · rw [MonoidHom.mem_ker, map_pow, hsq]
  · rw [MonoidHom.mem_ker] at hupres
    have hu' : u = y⁻¹ * g * y := by rw [hgdef]; group
    rw [hu', map_mul, map_mul, hVg, mul_comm (MonoidHom.transfer ϕ y⁻¹), mul_assoc,
      ← map_mul] at hupres
    simp at hupres
    exact hz1 hupres

variable {G : Type*} [Group G]

theorem thompson_transfer_exists_normal_subgroup [Finite G] {X P Q : Subgroup G} (hPX : P ≤ X)
    (hP2 : IsPGroup 2 P) (hPidx : ¬ 2 ∣ P.relIndex X) (hQP : Q ≤ P)
    (hQidx : Q.relIndex P = 2) {u : G} (huX : u ∈ X) (hu : orderOf u = 2)
    (hQu : ∀ x ∈ X, x⁻¹ * u * x ∉ Q) :
    ∃ N : Subgroup G, N ≤ X ∧ (N.subgroupOf X).Normal ∧ (∀ x ∈ X, x ^ 2 ∈ N) ∧ u ∉ N := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP2' : IsPGroup 2 (P.subgroupOf X) := hP2.of_equiv (Subgroup.subgroupOfEquivOfLe hPX).symm
  let S : Sylow 2 X := hP2'.toSylow (by simpa [Subgroup.relIndex] using hPidx)
  have hQPX : Q.subgroupOf X ≤ S := by
    intro x hx
    exact Subgroup.mem_subgroupOf.2 (hQP (Subgroup.mem_subgroupOf.1 hx))
  have hQidx' : (Q.subgroupOf X).relIndex (S : Subgroup X) = 2 := by
    have hS : (S : Subgroup X) = P.subgroupOf X := rfl
    rw [hS, Subgroup.relIndex_subgroupOf hPX]
    exact hQidx
  have hu' : orderOf (⟨u, huX⟩ : X) = 2 := by rw [Subgroup.orderOf_mk]; exact hu
  obtain ⟨N', hN'n, hN'sq, hN'u⟩ := thompson_transfer_exists_normal S hQPX hQidx' hu'
    (fun x => by
      have := hQu x x.2
      exact fun hmem => this (by simpa using Subgroup.mem_subgroupOf.1 hmem))
  refine ⟨N'.map X.subtype, Subgroup.map_subtype_le N', ?_, ?_, ?_⟩
  · have : (N'.map X.subtype).subgroupOf X = N' :=
      Subgroup.comap_map_eq_self_of_injective X.subtype_injective N'
    rw [this]
    exact hN'n
  · intro x hx
    exact ⟨⟨x, hx⟩ ^ 2, hN'sq ⟨x, hx⟩, rfl⟩
  · rintro ⟨n, hn, hnu⟩
    have : n = ⟨u, huX⟩ := Subtype.ext hnu
    exact hN'u (this ▸ hn)

theorem thompson_transfer_lemma_subgroup [Finite G] {X P Q : Subgroup G} (hPX : P ≤ X)
    (hP2 : IsPGroup 2 P) (hPidx : ¬ 2 ∣ P.relIndex X) (hQP : Q ≤ P)
    (hQidx : Q.relIndex P = 2) {u : G} (huX : u ∈ X) (hu : orderOf u = 2)
    (hQu : ∀ x ∈ X, x⁻¹ * u * x ∉ Q) : u ∉ pResidualOf 2 X := by
  obtain ⟨N, hNX, hNn, hsq, huN⟩ :=
    thompson_transfer_exists_normal_subgroup hPX hP2 hPidx hQP hQidx huX hu hQu
  rintro ⟨v, hv, hvu⟩
  have hres : pResidual 2 X ≤ N.subgroupOf X := by
    have := hNn
    exact pResidual_le fun x => ⟨1, Subgroup.mem_subgroupOf.2 (by simpa using hsq x x.2)⟩
  apply huN
  rw [← hvu]
  exact Subgroup.mem_subgroupOf.1 (hres hv)

theorem generalized_thompson_transfer_one_subgroup [Finite G] {p : ℕ} [Fact p.Prime]
    {X H K : Subgroup G} (hHX : H ≤ X) (hindex : Nat.Coprime p (H.relIndex X)) (hKH : K ≤ H)
    (hKn : ∀ h ∈ H, ∀ k ∈ K, h * k * h⁻¹ ∈ K) (habel : ⁅H, H⁆ ≤ K) {g : G} (hg : g ∈ H)
    (hgK : g ∉ K) (hgp : ∃ n : ℕ, g ^ p ^ n = 1)
    (h : ∀ (m : ℤ) (a : G), a ∈ X → a⁻¹ * g ^ m * a ∈ H → (g ^ m)⁻¹ * (a⁻¹ * g ^ m * a) ∈ K) :
    g ∉ ⁅X, X⁆ := by
  have hK' : K.subgroupOf X ≤ H.subgroupOf X := fun x hx =>
    Subgroup.mem_subgroupOf.2 (hKH (Subgroup.mem_subgroupOf.1 hx))
  have hKnormal : ((K.subgroupOf X).subgroupOf (H.subgroupOf X)).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hK']
    intro k a hk ha
    exact Subgroup.mem_subgroupOf.2 (hKn a (Subgroup.mem_subgroupOf.1 ha) k
      (Subgroup.mem_subgroupOf.1 hk))
  have habel' : ⁅H.subgroupOf X, H.subgroupOf X⁆ ≤ K.subgroupOf X := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    exact Subgroup.mem_subgroupOf.2 (habel (Subgroup.commutator_mem_commutator
      (Subgroup.mem_subgroupOf.1 ha) (Subgroup.mem_subgroupOf.1 hb)))
  have hmain := generalized_thompson_transfer_one (G := X) (p := p) (H := H.subgroupOf X)
    (K := K.subgroupOf X) hindex ⟨hK', hKnormal⟩ habel' (g := ⟨g, hHX hg⟩)
    (Subgroup.mem_subgroupOf.2 hg) (fun hmem => hgK (Subgroup.mem_subgroupOf.1 hmem))
    (by
      obtain ⟨n, hn⟩ := hgp
      exact ⟨n, Subtype.ext (by simpa using hn)⟩)
    (by
      intro m a ha
      have := h m a a.2 (Subgroup.mem_subgroupOf.1 ha)
      exact Subgroup.mem_subgroupOf.2 (by simpa using this))
  intro hgc
  apply hmain
  rw [← Subgroup.map_subtype_commutator] at hgc
  obtain ⟨c, hc, hcg⟩ := hgc
  have : c = ⟨g, hHX hg⟩ := Subtype.ext hcg
  exact this ▸ hc

theorem generalized_thompson_transfer_two_subgroup [Finite G] {X H K : Subgroup G}
    (hHX : H ≤ X) (hindex : Nat.Coprime 2 (H.relIndex X)) (hKH : K ≤ H)
    (hKn : ∀ h ∈ H, ∀ k ∈ K, h * k * h⁻¹ ∈ K) (habel : ⁅H, H⁆ ≤ K) {g : G} (hg : g ∈ H)
    (hgK : g ∉ K) (hg2 : orderOf g = 2)
    (h : ∀ a ∈ X, a⁻¹ * g * a ∈ H → g⁻¹ * (a⁻¹ * g * a) ∈ K) : g ∉ ⁅X, X⁆ := by
  have hg2' : g ^ 2 = 1 := hg2 ▸ pow_orderOf_eq_one g
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine generalized_thompson_transfer_one_subgroup (p := 2) hHX hindex hKH hKn habel hg hgK
    ⟨1, by simpa using hg2'⟩ ?_
  intro m a haX ha
  rcases Int.even_or_odd' m with ⟨j, rfl | rfl⟩
  · have : g ^ (2 * j) = 1 := by rw [zpow_mul]; simp [hg2']
    rw [this] at ha ⊢
    simp
  · have : g ^ (2 * j + 1) = g := by rw [zpow_add, zpow_mul]; simp [hg2']
    rw [this] at ha ⊢
    exact h a haX ha

end CFSG.Quasithin
