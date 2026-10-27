module

public import Mathlib.GroupTheory.Transfer
public import Mathlib.GroupTheory.Abelianization.Defs
public import Mathlib.GroupTheory.IndexNormal
public import CFSG.GroupTheory.AbelianNormalCoprimeComplementLifting

public section

namespace CFSG.Quasithin

open scoped Pointwise

variable {G : Type*} [Group G]

@[expose] def conjSubgroup (A : Subgroup G) (g : G) : Subgroup G :=
  A.map (MulAut.conj g⁻¹).toMonoidHom

theorem mem_conjSubgroup_iff {A : Subgroup G} {g x : G} :
    x ∈ conjSubgroup A g ↔ g * x * g⁻¹ ∈ A := by
  constructor
  · rintro ⟨a, ha, rfl⟩
    have : g * (g⁻¹ * a * g) * g⁻¹ = a := by group
    simpa [this] using ha
  · intro h
    exact ⟨g * x * g⁻¹, h, by simp [mul_assoc]⟩

theorem conjSubgroup_conjSubgroup (A : Subgroup G) (g h : G) :
    conjSubgroup (conjSubgroup A g) h = conjSubgroup A (g * h) := by
  ext x
  simp only [mem_conjSubgroup_iff]
  have : g * (h * x * h⁻¹) * g⁻¹ = (g * h) * x * (g * h)⁻¹ := by group
  rw [this]

theorem conjSubgroup_one (A : Subgroup G) : conjSubgroup A 1 = A := by
  ext x
  simp [mem_conjSubgroup_iff]

@[expose] def conjSet (S : Set G) (g : G) : Set G := (fun s => g⁻¹ * s * g) '' S

theorem mem_conjSet_iff {S : Set G} {g x : G} : x ∈ conjSet S g ↔ g * x * g⁻¹ ∈ S := by
  constructor
  · rintro ⟨s, hs, rfl⟩
    have : g * (g⁻¹ * s * g) * g⁻¹ = s := by group
    simpa [this] using hs
  · intro h
    exact ⟨g * x * g⁻¹, h, by simp [mul_assoc]⟩

theorem conjSet_conjSet (S : Set G) (g h : G) :
    conjSet (conjSet S g) h = conjSet S (g * h) := by
  ext x
  simp only [mem_conjSet_iff]
  have : g * (h * x * h⁻¹) * g⁻¹ = (g * h) * x * (g * h)⁻¹ := by group
  rw [this]

theorem conjSet_eq_iff_mem_normalizer {S : Set G} {g : G} :
    conjSet S g = S ↔ g ∈ Subgroup.normalizer S := by
  rw [Subgroup.mem_set_normalizer_iff, Set.ext_iff]
  simp only [mem_conjSet_iff]
  exact forall_congr' fun x => Iff.comm

theorem conjSubgroup_eq_iff_mem_normalizer {A : Subgroup G} {g : G} :
    conjSubgroup A g = A ↔ g ∈ Subgroup.normalizer (A : Set G) := by
  rw [Subgroup.mem_set_normalizer_iff, SetLike.ext_iff]
  simp only [mem_conjSubgroup_iff, SetLike.mem_coe]
  exact forall_congr' fun x => Iff.comm

@[expose] def IsWeaklyClosedIn (A B : Subgroup G) : Prop :=
  ∀ g : G, conjSubgroup A g ≤ B → conjSubgroup A g = A

theorem exists_conj_le_sylow_of_isPGroup [Finite G] {p : ℕ} [Fact p.Prime] (T : Sylow p G)
    {N Q₁ Q₂ : Subgroup G} (hQ₁N : Q₁ ≤ N) (hQ₂N : Q₂ ≤ N) (hQ₁ : IsPGroup p Q₁)
    (hQ₂ : IsPGroup p Q₂) :
    ∃ c ∈ N, ∃ y : G, conjSubgroup Q₁ y ≤ T ∧ conjSubgroup Q₂ (c * y) ≤ T := by
  have hp1 : IsPGroup p (Q₁.subgroupOf N) :=
    hQ₁.of_equiv (Subgroup.subgroupOfEquivOfLe hQ₁N).symm
  have hp2 : IsPGroup p (Q₂.subgroupOf N) :=
    hQ₂.of_equiv (Subgroup.subgroupOfEquivOfLe hQ₂N).symm
  obtain ⟨P₁, hP₁⟩ := hp1.exists_le_sylow
  obtain ⟨P₂, hP₂⟩ := hp2.exists_le_sylow
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq N P₁ P₂
  have hP₁G : IsPGroup p ((P₁ : Subgroup N).map N.subtype) := P₁.isPGroup'.map _
  obtain ⟨T', hT'⟩ := hP₁G.exists_le_sylow
  obtain ⟨y, hy⟩ := MulAction.exists_smul_eq G T T'
  have key : ∀ z : G, z ∈ (T' : Subgroup G) → y⁻¹ * z * y ∈ (T : Subgroup G) := by
    intro z hz
    subst hy
    have : z ∈ ((y • T : Sylow p G) : Subgroup G) := hz
    rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at this
    simpa [MulAut.conj_apply] using this
  refine ⟨c, c.2, y, ?_, ?_⟩
  · intro x hx
    rw [mem_conjSubgroup_iff] at hx
    have h1 : (⟨y * x * y⁻¹, hQ₁N hx⟩ : N) ∈ (P₁ : Subgroup N) :=
      hP₁ (Subgroup.mem_subgroupOf.2 hx)
    have h2 : y * x * y⁻¹ ∈ (T' : Subgroup G) := hT' ⟨_, h1, rfl⟩
    have h3 := key _ h2
    have h4 : y⁻¹ * (y * x * y⁻¹) * y = x := by group
    rwa [h4] at h3
  · intro x hx
    rw [mem_conjSubgroup_iff] at hx
    have h0 : (⟨(c * y) * x * (c * y)⁻¹, hQ₂N hx⟩ : N) ∈ (P₂ : Subgroup N) :=
      hP₂ (Subgroup.mem_subgroupOf.2 hx)
    have h1 : (c : N)⁻¹ * ⟨(c * y) * x * (c * y)⁻¹, hQ₂N hx⟩ * c ∈ (P₁ : Subgroup N) := by
      subst hc
      have : (⟨(c * y) * x * (c * y)⁻¹, hQ₂N hx⟩ : N) ∈ ((c • P₁ : Sylow p N) : Subgroup N) := h0
      rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at this
      simpa [MulAut.conj_apply] using this
    have h2 : y * x * y⁻¹ ∈ (T' : Subgroup G) := by
      refine hT' ⟨_, h1, ?_⟩
      simp only [Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv]
      group
    have h3 := key _ h2
    have h4 : y⁻¹ * (y * x * y⁻¹) * y = x := by group
    rwa [h4] at h3

theorem burnside_fusion_lemma [Finite G] {p : ℕ} [Fact p.Prime] (T : Sylow p G)
    {W : Subgroup G} (hWT : W ≤ T) (hW : IsWeaklyClosedIn W T) {A B : Set G}
    (hA : ∀ w ∈ W, conjSet A w = A) (hB : ∀ w ∈ W, conjSet B w = B) {g : G}
    (hg : conjSet A g = B) :
    ∃ n ∈ Subgroup.normalizer (W : Set G), conjSet A n = B := by
  have hWN : W ≤ Subgroup.normalizer B := fun w hw =>
    conjSet_eq_iff_mem_normalizer.1 (hB w hw)
  have hW'N : conjSubgroup W g ≤ Subgroup.normalizer B := by
    intro x hx
    rw [mem_conjSubgroup_iff] at hx
    rw [← conjSet_eq_iff_mem_normalizer, ← hg, conjSet_conjSet]
    have : g * x = (g * x * g⁻¹) * g := by group
    rw [this, ← conjSet_conjSet, hA _ hx]
  have hWp : IsPGroup p W := T.isPGroup'.to_le hWT
  have hW'p : IsPGroup p (conjSubgroup W g) := hWp.map _
  obtain ⟨c, hcN, y, hy1, hy2⟩ := exists_conj_le_sylow_of_isPGroup T hWN hW'N hWp hW'p
  have h1 : conjSubgroup W y = W := hW y hy1
  rw [conjSubgroup_conjSubgroup] at hy2
  have h2 : conjSubgroup W (g * (c * y)) = W := hW _ hy2
  refine ⟨g * c, ?_, ?_⟩
  · rw [← conjSubgroup_eq_iff_mem_normalizer]
    have h3 : conjSubgroup (conjSubgroup W (g * c)) y = W := by
      rw [conjSubgroup_conjSubgroup, mul_assoc]; exact h2
    have h4 : conjSubgroup W (g * c) =
        conjSubgroup (conjSubgroup (conjSubgroup W (g * c)) y) y⁻¹ := by
      rw [conjSubgroup_conjSubgroup, mul_inv_cancel, conjSubgroup_one]
    rw [h4, h3]
    exact conjSubgroup_eq_iff_mem_normalizer.2
      ((Subgroup.normalizer (W : Set G)).inv_mem (conjSubgroup_eq_iff_mem_normalizer.1 h1))
  · rw [← conjSet_conjSet, hg]
    exact conjSet_eq_iff_mem_normalizer.2 hcN

theorem conjSet_singleton (x g : G) : conjSet {x} g = {g⁻¹ * x * g} := by
  simp [conjSet]

theorem burnside_fusion_lemma_centralizer [Finite G] {p : ℕ} [Fact p.Prime] (T : Sylow p G)
    {W : Subgroup G} (hWT : W ≤ T) (hW : IsWeaklyClosedIn W T) {x y : G}
    (hx : x ∈ Subgroup.centralizer (W : Set G)) (hy : y ∈ Subgroup.centralizer (W : Set G))
    {g : G} (hg : g⁻¹ * x * g = y) :
    ∃ n ∈ Subgroup.normalizer (W : Set G), n⁻¹ * x * n = y := by
  have hfix : ∀ z ∈ Subgroup.centralizer (W : Set G), ∀ w ∈ W, conjSet {z} w = {z} := by
    intro z hz w hw
    rw [conjSet_singleton]
    have : w * z = z * w := Subgroup.mem_centralizer_iff.1 hz w hw
    have h' : w⁻¹ * z * w = z := by rw [mul_assoc, ← this, ← mul_assoc, inv_mul_cancel, one_mul]
    rw [h']
  obtain ⟨n, hn, hn'⟩ := burnside_fusion_lemma T hWT hW (hfix x hx) (hfix y hy) (g := g)
    (by rw [conjSet_singleton, hg])
  refine ⟨n, hn, ?_⟩
  rw [conjSet_singleton] at hn'
  exact Set.singleton_eq_singleton_iff.1 hn'

@[expose] def pResidual (p : ℕ) (X : Type*) [Group X] : Subgroup X :=
  ⨅ (N : Subgroup X) (_ : N.Normal) (_ : ∀ x : X, ∃ k : ℕ, x ^ p ^ k ∈ N), N

@[expose] def pResidualOf (p : ℕ) (X : Subgroup G) : Subgroup G :=
  (pResidual p X).map X.subtype

theorem pResidual_le {p : ℕ} {X : Type*} [Group X] {N : Subgroup X} [N.Normal]
    (hN : ∀ x : X, ∃ k : ℕ, x ^ p ^ k ∈ N) : pResidual p X ≤ N :=
  iInf_le_of_le N (iInf_le_of_le ‹N.Normal› (iInf_le_of_le hN le_rfl))

open scoped IsMulCommutative

theorem transfer_eq_pow_of_forall [Finite G] {H : Subgroup G} {A : Type*} [CommGroup A]
    (ϕ : H →* A) {g : G} (hg : g ∈ H)
    (h : ∀ (k : ℕ) (a : G) (ha : a⁻¹ * g ^ k * a ∈ H),
      ϕ ⟨a⁻¹ * g ^ k * a, ha⟩ = ϕ ⟨g ^ k, H.pow_mem hg k⟩) :
    MonoidHom.transfer ϕ g = ϕ ⟨g, hg⟩ ^ H.index := by
  classical
  have : Fintype (Quotient (MulAction.orbitRel (Subgroup.zpowers g) (G ⧸ H))) :=
    Fintype.ofFinite _
  rw [Subgroup.index_eq_sum_minimalPeriod H g, ← Finset.prod_pow_eq_pow_sum,
    MonoidHom.transfer_eq_prod_quotient_orbitRel_zpowers_quot]
  refine Finset.prod_congr rfl fun q _ => ?_
  rw [h, ← map_pow]
  rfl

theorem generalized_thompson_transfer_one [Finite G] {p : ℕ} [Fact p.Prime] {H K : Subgroup G}
    (hindex : Nat.Coprime p H.index) (hK : K ≤ H ∧ (K.subgroupOf H).Normal)
    (habel : ⁅H, H⁆ ≤ K) {g : G} (hg : g ∈ H) (hgK : g ∉ K) (hgp : ∃ n : ℕ, g ^ p ^ n = 1)
    (h : ∀ (m : ℤ) (a : G), a⁻¹ * g ^ m * a ∈ H → (g ^ m)⁻¹ * (a⁻¹ * g ^ m * a) ∈ K) :
    g ∉ commutator G := by
  classical
  have := hK.2
  have hcomm : IsMulCommutative (H ⧸ K.subgroupOf H) := by
    rw [Subgroup.Normal.quotient_commutative_iff_commutator_le, commutator_def,
      Subgroup.commutator_le]
    intro x _ y _
    rw [Subgroup.mem_subgroupOf]
    exact habel (Subgroup.commutator_mem_commutator x.2 y.2)
  let ϕ : H →* H ⧸ K.subgroupOf H := QuotientGroup.mk' (K.subgroupOf H)
  have hV := transfer_eq_pow_of_forall ϕ hg (by
    intro k a ha
    rw [eq_comm, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq,
      Subgroup.mem_subgroupOf]
    have := h k a (by simpa using ha)
    simpa using this)
  intro hgc
  have h1 : MonoidHom.transfer ϕ g = 1 := by
    have := Abelianization.commutator_subset_ker (MonoidHom.transfer ϕ) hgc
    simpa using this
  rw [hV] at h1
  obtain ⟨n, hn⟩ := hgp
  have hz1 : (ϕ ⟨g, hg⟩) ^ p ^ n = 1 := by
    rw [← map_pow]
    have : (⟨g, hg⟩ : H) ^ p ^ n = 1 := Subtype.ext (by simpa using hn)
    rw [this, map_one]
  have hcop : Nat.Coprime (p ^ n) H.index := Nat.Coprime.pow_left n hindex
  have hz2 : ϕ ⟨g, hg⟩ = 1 := by
    have := pow_gcd_eq_one.2 ⟨hz1, h1⟩
    rwa [hcop, pow_one] at this
  apply hgK
  have := (QuotientGroup.eq_one_iff (⟨g, hg⟩ : H)).1 hz2
  exact Subgroup.mem_subgroupOf.1 this

theorem generalized_thompson_transfer_two [Finite G] {H K : Subgroup G}
    (hindex : Nat.Coprime 2 H.index) (hK : K ≤ H ∧ (K.subgroupOf H).Normal)
    (habel : ⁅H, H⁆ ≤ K) {g : G} (hg : g ∈ H) (hgK : g ∉ K) (hg2 : orderOf g = 2)
    (h : ∀ a : G, a⁻¹ * g * a ∈ H → g⁻¹ * (a⁻¹ * g * a) ∈ K) :
    g ∉ commutator G := by
  have hg2' : g ^ 2 = 1 := hg2 ▸ pow_orderOf_eq_one g
  refine generalized_thompson_transfer_one (p := 2) hindex hK habel hg hgK ⟨1, by simpa using hg2'⟩
    ?_
  intro m a ha
  rcases Int.even_or_odd' m with ⟨j, rfl | rfl⟩
  · have : g ^ (2 * j) = 1 := by rw [zpow_mul]; simp [hg2']
    rw [this] at ha ⊢
    simp
  · have : g ^ (2 * j + 1) = g := by rw [zpow_add, zpow_mul]; simp [hg2']
    rw [this] at ha ⊢
    exact h a ha

theorem thompson_transfer_lemma {X : Type*} [Group X] [Finite X] (P : Sylow 2 X) {Q : Subgroup X}
    (hQP : Q ≤ P) (hindex : Q.relIndex (P : Subgroup X) = 2) {u : X} (hu : orderOf u = 2)
    (hQu : ∀ x : X, x⁻¹ * u * x ∉ Q) : u ∉ pResidual 2 X := by
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
  intro hupres
  have hker : pResidual 2 X ≤ (MonoidHom.transfer ϕ).ker := by
    refine pResidual_le fun x => ⟨1, ?_⟩
    rw [MonoidHom.mem_ker, pow_one, map_pow, hsq]
  have h1 := hker hupres
  rw [MonoidHom.mem_ker] at h1
  have hu' : u = y⁻¹ * g * y := by rw [hgdef]; group
  rw [hu', map_mul, map_mul, hVg, mul_comm (MonoidHom.transfer ϕ y⁻¹), mul_assoc, ← map_mul] at h1
  simp at h1
  exact hz1 h1

theorem exists_normal_isComplement'_of_isCyclic_sylow [Finite G] {p : ℕ} [Fact p.Prime]
    (hmin : ∀ q : ℕ, q.Prime → q ∣ Nat.card G → p ≤ q) (P : Sylow p G)
    (hP : IsCyclic (P : Subgroup G)) :
    ∃ N : Subgroup G, N.Normal ∧ N.IsComplement' (P : Subgroup G) := by
  by_cases hdvd : p ∣ Nat.card G
  · have hne : Nat.card G ≠ 1 := by
      intro h
      rw [h] at hdvd
      exact (Fact.out : p.Prime).one_lt.ne' (Nat.dvd_one.1 hdvd)
    have hminfac : (Nat.card G).minFac = p := by
      refine le_antisymm (Nat.minFac_le_of_dvd (Fact.out : p.Prime).two_le hdvd) ?_
      exact hmin _ (Nat.minFac_prime hne) (Nat.minFac_dvd _)
    exact ⟨_, MonoidHom.normal_ker _, IsCyclic.isComplement' hminfac hP⟩
  · have hbot : (P : Subgroup G) = ⊥ := by
      obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 P.isPGroup'
      have hk' : Nat.card (P : Subgroup G) ∣ Nat.card G := Subgroup.card_subgroup_dvd_card _
      rw [← Subgroup.card_eq_one]
      rcases k with _ | k
      · simpa using hk
      · exact absurd ((dvd_pow_self p k.succ_ne_zero).trans (hk ▸ hk')) hdvd
    refine ⟨⊤, inferInstance, ?_⟩
    rw [hbot]
    exact Subgroup.isComplement'_top_bot

theorem gaschutz [Finite G] {p : ℕ} [Fact p.Prime] {V : Subgroup G} [V.Normal]
    [IsMulCommutative V] (hVp : IsPGroup p V) (P : Sylow p G) :
    (∃ K : Subgroup G, V ⊓ K = ⊥ ∧ V ⊔ K = ⊤) ↔
      ∃ K : Subgroup G, K ≤ P ∧ V ⊓ K = ⊥ ∧ V ⊔ K = P := by
  have hVP : V ≤ P := hVp.le_sylow_of_normal P
  constructor
  · rintro ⟨K, hVK, hsup⟩
    refine ⟨K ⊓ P, inf_le_right, ?_, ?_⟩
    · exact eq_bot_iff.2 (hVK ▸ inf_le_inf_left V inf_le_left)
    · refine le_antisymm (sup_le hVP inf_le_right) fun x hx => ?_
      have hx' : x ∈ V ⊔ K := hsup ▸ Subgroup.mem_top x
      obtain ⟨v, hv, k, hk, rfl⟩ := Subgroup.mem_sup_of_normal_left.1 hx'
      have hkP : k ∈ (P : Subgroup G) := by
        have := (P : Subgroup G).mul_mem ((P : Subgroup G).inv_mem (hVP hv)) hx
        simpa using this
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hv) (Subgroup.mem_sup_right ⟨hk, hkP⟩)
  · rintro ⟨K, hKP, hVK, hsup⟩
    have hcop : Nat.Coprime (P : Subgroup G).index (Nat.card V) := by
      obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 hVp
      rw [hn]
      exact Nat.Coprime.pow_right n
        ((Nat.Prime.coprime_iff_not_dvd (Fact.out : p.Prime)).2 P.not_dvd_index).symm
    obtain ⟨D, -, hVD, hsupD⟩ :=
      CFSG.GroupTheory.abelian_normal_coprime_index_complement_lifting V (P : Subgroup G) K hcop
        hVK hsup
    exact ⟨D, hVD, hsupD⟩

end CFSG.Quasithin
