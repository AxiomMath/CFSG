module

public import CFSG.Walter.Bender1970.S3.ABar
public import CFSG.Walter.Bender1970.S3.HyperplaneCentralizer
public import CFSG.Walter.Bender1970.S3.Singleton
public import CFSG.Walter.Bender1970.S3.Extraspecial
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.QCoreConjugate
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.GeneralizedFittingSubgroupConjugate
import CFSG.Adapters.GeneralizedFitting

public section

namespace CFSG.Walter

open CFSG.GorensteinWalter
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace Bender35

theorem le_and_isSubnormal {H X : Subgroup G} {p : ℕ} (hp : p.Prime) (hX : X ≤ qCoreOf H p) :
    X ≤ generalizedFittingSubgroupOf H ∧
      (X.subgroupOf (generalizedFittingSubgroupOf H)).IsSubnormal := by
  have : Fact p.Prime := ⟨hp⟩
  have hn := qCoreOf_isNormalIn_generalizedFitting H hp
  refine ⟨hX.trans hn.1, isSubnormal_subgroupOf_trans hX ?_
    (isSubnormal_subgroupOf_of_isNormalIn hn)⟩
  exact isSubnormal_of_nilpotent (qCoreOf_isPGroup H p).isNilpotent _ hX

omit [Finite G] in
theorem commutator_self_le (V : Subgroup G) : ⁅V, V⁆ ≤ V := by
  rw [Subgroup.commutator_le]
  intro a ha b hb
  rw [commutatorElement_def]
  exact V.mul_mem (V.mul_mem (V.mul_mem ha hb) (V.inv_mem ha)) (V.inv_mem hb)

theorem odd_card_of_le {H X : Subgroup G} {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hX : X ≤ qCoreOf H p) : Odd (Nat.card X) := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨k, hk⟩ := ((qCoreOf_isPGroup H p).to_le hX).exists_card_eq
  rw [hk]
  exact (hp.odd_of_ne_two hp2).pow

theorem odd_orderOf_of_mem {H : Subgroup G} {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {x : G}
    (hx : x ∈ qCoreOf H p) : Odd (orderOf x) :=
  Odd.of_dvd_nat (odd_card_of_le hp hp2 le_rfl) (Subgroup.orderOf_dvd_natCard _ hx)

theorem commutator_commutator_eq {H X : Subgroup G} {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hX : X ≤ qCoreOf H p) {t : G} (ht : orderOf t = 2)
    (htX : t ∈ Subgroup.normalizer (X : Set G)) :
    ⁅⁅X, Subgroup.zpowers t⁆, Subgroup.zpowers t⁆ = ⁅X, Subgroup.zpowers t⁆ := by
  have : Fact p.Prime := ⟨hp⟩
  have hcop : Nat.Coprime (Nat.card (Subgroup.zpowers t)) (Nat.card X) := by
    obtain ⟨k, hk⟩ := ((qCoreOf_isPGroup H p).to_le hX).exists_card_eq
    rw [Nat.card_zpowers, ht, hk]
    exact Nat.Coprime.pow_right k ((Nat.coprime_primes Nat.prime_two hp).mpr (Ne.symm hp2))
  refine le_antisymm (commutator_zpowers_le_of_mem_normalizer ?_)
    (commutator_le_commutator_commutator X _ (Subgroup.zpowers_le.mpr htX) hcop)
  exact mem_normalizer_commutator htX (Subgroup.le_normalizer (Subgroup.mem_zpowers t))

section ABar

variable (hG : BenderCounterexample G) {t : G} (ht : orderOf t = 2) {H : Subgroup G}
  (hH : H ∈ benderM t) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
include hG ht hH hp hp2

theorem mem_of_invariant
    {X : Subgroup G} (hX : X ≤ qCoreOf H p) (hX1 : X ≠ ⊥)
    (hXC : Subgroup.centralizer ({t} : Set G) ≤ Subgroup.normalizer (X : Set G)) :
    X ∈ benderABar H :=
  have _ := hp2
  bender1970_3_1_i hG ht hH hX1 (le_and_isSubnormal hp hX).1 (le_and_isSubnormal hp hX).2 hXC

theorem mem_of_centralized {X : Subgroup G} (hX : X ≤ qCoreOf H p)
    (hXC : Subgroup.centralizer ({t} : Set G) ≤ Subgroup.normalizer (X : Set G))
    (hXt : ⁅X, Subgroup.zpowers t⁆ ≠ ⊥) {V : Subgroup G} (hV : V ≤ qCoreOf H p) (hV1 : V ≠ ⊥)
    (hVt : t ∈ Subgroup.normalizer (V : Set G))
    (hVX : V ≤ Subgroup.centralizer ((⁅X, Subgroup.zpowers t⁆ : Subgroup G) : Set G)) :
    V ∈ benderABar H := by
  have htC : t ∈ Subgroup.centralizer ({t} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have hWP : ⁅X, Subgroup.zpowers t⁆ ≤ qCoreOf H p :=
    (commutator_zpowers_le_of_mem_normalizer (hXC htC)).trans hX
  have hWC : Subgroup.centralizer ({t} : Set G) ≤
      Subgroup.normalizer ((⁅X, Subgroup.zpowers t⁆ : Subgroup G) : Set G) := by
    intro c hc
    refine mem_normalizer_commutator (hXC hc) (mem_normalizer_of_mem_centralizer ?_)
    rw [centralizer_zpowers_eq']
    exact hc
  have hWA := mem_of_invariant hG ht hH hp hp2 hWP hXt hWC
  exact bender1970_3_1_ii hG ht hH hV1 (le_and_isSubnormal hp hV).1 (le_and_isSubnormal hp hV).2
    hVt hWA (Subgroup.le_centralizer_iff.mp hVX)
    (commutator_commutator_eq hp hp2 hX ht (hXC htC))

omit hG ht hH in
theorem mem_of_commutator_eq {Z V : Subgroup G} (hZA : Z ∈ benderABar H) (hZ1 : Z ≠ ⊥)
    (hV : V ≤ qCoreOf H p) (hVZ : ⁅V, V⁆ = Z) : V ∈ benderABar H := by
  have : Fact p.Prime := ⟨hp⟩
  have hZV : Z ≤ V := hVZ ▸ commutator_self_le V
  refine ⟨(le_and_isSubnormal hp hV).1, (le_and_isSubnormal hp hV).2, fun hπ => ?_, fun hπ => ?_⟩
  · intro g hg
    have hgZ : g ∈ Subgroup.normalizer (Z : Set G) := by
      rw [← hVZ]
      exact mem_normalizer_commutator hg hg
    exact hZA.2.2.1 hπ hgZ
  · have h := hZA.2.2.2 hπ
    obtain ⟨q, hq, hFq, -, hπq⟩ := exists_isPGroup_of_card_primesOfOrder_eq_one hπ
    have hVp : IsPGroup p V := (qCoreOf_isPGroup H p).to_le hV
    have hqp : q = p := eq_of_isPGroup_of_isPGroup hq hp
      (hFq.to_le ((hZV.trans hV).trans (le_and_isSubnormal hp le_rfl).1)) (hVp.to_le hZV) hZ1
    subst hqp
    rw [hπq] at h ⊢
    have hCZ := isPGroup_of_primesOfOrder_subset hq h.le
    have hCV := bender1970_1_9_centralizer_pGroup q hq hZV hVp (hVp.to_le hZV) hCZ
    have hV1 : V ≠ ⊥ := fun h' => hZ1 (le_bot_iff.mp (h' ▸ hZV))
    exact primesOfOrder_generalizedFitting_eq_singleton hq hCV
      (centralizer_ne_bot_of_isPGroup hq hVp hV1)

end ABar

omit [Finite G] in
theorem mem_normalizer_centralizer {K : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (K : Set G)) :
    g ∈ Subgroup.normalizer ((Subgroup.centralizer (K : Set G) : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  rw [Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
  constructor
  · intro hx k hk
    have hk' : g⁻¹ * k * g ∈ K := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hg) k).mp hk
      simpa using this
    have := hx _ hk'
    calc k * (g * x * g⁻¹) = g * ((g⁻¹ * k * g) * x) * g⁻¹ := by group
      _ = g * (x * (g⁻¹ * k * g)) * g⁻¹ := by rw [this]
      _ = g * x * g⁻¹ * k := by group
  · intro hx k hk
    have hk' : g * k * g⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp hg k).mp hk
    have := hx _ hk'
    calc k * x = g⁻¹ * ((g * k * g⁻¹) * (g * x * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * x * g⁻¹) * (g * k * g⁻¹)) * g := by rw [this]
      _ = x * k := by group

theorem pResidualOf_zpowers_eq {p : ℕ} (hp : p.Prime) {t : G} (hcop : Nat.Coprime p (orderOf t)) :
    pResidualOf (Subgroup.zpowers t) p = Subgroup.zpowers t := by
  refine le_antisymm (pResidualOf_le _ p) fun x hx => ?_
  refine mem_pResidualOf_of_order_coprime _ p hp hx ?_
  exact Nat.Coprime.coprime_dvd_right (orderOf_dvd_of_mem_zpowers hx) hcop

section Negation

variable (hG : BenderCounterexample G) {t : G} (ht : orderOf t = 2) {H : Subgroup G}
  (hH : H ∈ benderM t) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)

def NoGood (t : G) (H : Subgroup G) (p : ℕ) : Prop :=
  ∀ Pbar ≤ qCoreOf H p, Subgroup.centralizer ({t} : Set G) ≤ Subgroup.normalizer (Pbar : Set G) →
    ⁅Pbar, Subgroup.zpowers t⁆ ≠ ⊥ →
      ∃ V ≤ Pbar, V ≠ ⊥ ∧ t ∈ Subgroup.normalizer (V : Set G) ∧ V ∉ benderABar H

include hH in
theorem centralizer_le_normalizer_qCoreOf :
    Subgroup.centralizer ({t} : Set G) ≤ Subgroup.normalizer (qCoreOf H p : Set G) :=
  (centralizer_le_of_mem_benderM hH).trans (le_normalizer_of_isNormalIn (qCoreOf_normal_in H p))

include hH in
theorem centralizer_le_normalizer_K :
    Subgroup.centralizer ({t} : Set G) ≤
      Subgroup.normalizer ((qCoreOf H p ⊓ Subgroup.centralizer ({t} : Set G) : Subgroup G) :
        Set G) := fun _ hc =>
  mem_normalizer_inf (centralizer_le_normalizer_qCoreOf hH hc) (Subgroup.le_normalizer hc)

include ht hH hp hp2 in
theorem commutator_centralizer_ne_bot
    (hpt : ⁅qCoreOf H p, Subgroup.zpowers t⁆ ≠ ⊥) :
    ⁅qCoreOf H p ⊓ Subgroup.centralizer
        ((qCoreOf H p ⊓ Subgroup.centralizer ({t} : Set G) : Subgroup G) : Set G),
      Subgroup.zpowers t⁆ ≠ ⊥ := by
  set P := qCoreOf H p
  set K := P ⊓ Subgroup.centralizer ({t} : Set G)
  intro h
  apply hpt
  have htC : t ∈ Subgroup.centralizer ({t} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have hcop : Nat.Coprime p (orderOf t) := by
    rw [ht]
    exact (Nat.coprime_primes hp Nat.prime_two).mpr hp2
  have hKt : ⁅K, Subgroup.zpowers t⁆ = ⊥ := by
    rw [Subgroup.commutator_comm, commutator_zpowers_eq_bot_iff]
    intro k hk
    exact Subgroup.mem_centralizer_singleton_iff.mp hk.2
  have h1 := bender1970_1_1_thompson p hp K (Subgroup.zpowers t) P
    ((qCoreOf_isPGroup H p).to_le inf_le_left) (qCoreOf_isPGroup H p)
    (pResidualOf_zpowers_eq hp hcop) (fun k hk => le_normalizer_of_isNormalIn
      (qCoreOf_normal_in H p) ((centralizer_le_of_mem_benderM hH) hk.2))
    (Subgroup.zpowers_le.mpr (centralizer_le_normalizer_qCoreOf hH htC)) hKt h
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
  exact Subgroup.le_centralizer_iff.mp h1

include hG ht hH hp hp2 in
theorem mem_of_le_K
    (hpt : ⁅qCoreOf H p, Subgroup.zpowers t⁆ ≠ ⊥) {U : Subgroup G}
    (hU : U ≤ qCoreOf H p ⊓ Subgroup.centralizer ({t} : Set G)) (hU1 : U ≠ ⊥) :
    U ∈ benderABar H := by
  set P := qCoreOf H p
  set K := P ⊓ Subgroup.centralizer ({t} : Set G)
  set X := P ⊓ Subgroup.centralizer (K : Set G)
  have hXC : Subgroup.centralizer ({t} : Set G) ≤ Subgroup.normalizer (X : Set G) := fun c hc =>
    mem_normalizer_inf (centralizer_le_normalizer_qCoreOf hH hc)
      (mem_normalizer_centralizer (centralizer_le_normalizer_K hH hc))
  have hXt := commutator_centralizer_ne_bot ht hH hp hp2 hpt
  have htC : t ∈ Subgroup.centralizer ({t} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have htU : t ∈ Subgroup.normalizer (U : Set G) := by
    refine Subgroup.centralizer_le_normalizer _ ?_
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    exact Subgroup.mem_centralizer_singleton_iff.mp (hU hu).2
  refine mem_of_centralized hG ht hH hp hp2 inf_le_left hXC hXt (hU.trans inf_le_left) hU1 htU ?_
  · intro u hu
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    have hwX : w ∈ X := (commutator_zpowers_le_of_mem_normalizer (hXC htC)) hw
    exact ((Subgroup.mem_centralizer_iff.mp hwX.2) u (hU hu)).symm

include hG ht hH hp hp2 in
theorem isCyclic_of_le_K
    (hneg : NoGood t H p) (hpt : ⁅qCoreOf H p, Subgroup.zpowers t⁆ ≠ ⊥)
    {A : Subgroup G} (hA : A ≤ qCoreOf H p ⊓ Subgroup.centralizer ({t} : Set G))
    (hAc : IsMulCommutative A) : IsCyclic A := by
  by_contra hcyc
  set P := qCoreOf H p
  set K := P ⊓ Subgroup.centralizer ({t} : Set G)
  set X := P ⊓ Subgroup.centralizer (K : Set G)
  have hXC : Subgroup.centralizer ({t} : Set G) ≤ Subgroup.normalizer (X : Set G) := fun c hc =>
    mem_normalizer_inf (centralizer_le_normalizer_qCoreOf hH hc)
      (mem_normalizer_centralizer (centralizer_le_normalizer_K hH hc))
  have hXt := commutator_centralizer_ne_bot ht hH hp hp2 hpt
  obtain ⟨V, hVX, hV1, hVt, hVA⟩ := hneg X inf_le_left hXC hXt
  apply hVA
  have hVP : V ≤ P := hVX.trans inf_le_left
  refine bender1970_3_1_iii hG ht hH hV1 (le_and_isSubnormal hp hVP).1
    (le_and_isSubnormal hp hVP).2 hVt (le_inf (hA.trans inf_le_right) ?_) hAc hcyc
    (odd_card_of_le hp hp2 (hA.trans inf_le_left)) fun a ha ha1 => ?_
  · intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    exact ((Subgroup.mem_centralizer_iff.mp (hVX hv).2) a (hA ha)).symm
  · refine mem_of_le_K hG ht hH hp hp2 hpt (Subgroup.zpowers_le.mpr (hA ha)) ?_
    rwa [Ne, Subgroup.zpowers_eq_bot]

include hG ht hH hp hp2 in
theorem le_centralizer_of_isMulCommutative
    (hneg : NoGood t H p) {A : Subgroup G}
    (hA : A ≤ qCoreOf H p)
    (hAC : Subgroup.centralizer ({t} : Set G) ≤ Subgroup.normalizer (A : Set G))
    (hAc : IsMulCommutative A) : A ≤ Subgroup.centralizer ({t} : Set G) := by
  by_contra hAt
  have hAt' : ⁅A, Subgroup.zpowers t⁆ ≠ ⊥ := by
    intro h
    apply hAt
    rw [Subgroup.commutator_comm, commutator_zpowers_eq_bot_iff] at h
    intro a ha
    exact Subgroup.mem_centralizer_singleton_iff.mpr (h a ha)
  obtain ⟨V, hVA, hV1, hVt, hVnA⟩ := hneg A hA hAC hAt'
  apply hVnA
  have htC : t ∈ Subgroup.centralizer ({t} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr rfl
  refine mem_of_centralized hG ht hH hp hp2 hA hAC hAt' (hVA.trans hA) hV1 hVt ?_
  intro v hv
  rw [Subgroup.mem_centralizer_iff]
  intro w hw
  have hwA : w ∈ A := (commutator_zpowers_le_of_mem_normalizer (hAC htC)) hw
  exact congrArg Subtype.val (hAc.is_comm.comm ⟨w, hwA⟩ ⟨v, hVA hv⟩)

end Negation

omit [Finite G] in
theorem mem_normalizer_of_isNormalIn {X H : Subgroup G} (hX : IsNormalIn X H) {h : G}
    (hh : h ∈ H) : h ∈ Subgroup.normalizer (X : Set G) :=
  le_normalizer_of_isNormalIn hX hh

theorem frattini_ne_top' {X : Type*} [Group X] [Finite X] [Nontrivial X] : frattini X ≠ ⊤ := by
  rcases eq_top_or_exists_le_coatom (⊥ : Subgroup X) with h | ⟨M, hM, -⟩
  · exact absurd h bot_ne_top
  · intro h
    exact hM.1 (top_le_iff.mp (h ▸ frattini_le_coatom hM))

section Minimal

variable {t : G} (ht : orderOf t = 2) {H : Subgroup G} {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
  {X₀ : Subgroup G} (hX₀P : X₀ ≤ qCoreOf H p) (hX₀H : IsNormalIn X₀ H)
  (hX₀t : ⁅X₀, Subgroup.zpowers t⁆ ≠ ⊥)
  (hmin : ∀ Y : Subgroup G, Y ≤ X₀ → IsNormalIn Y H → Y ≠ X₀ → ⁅Y, Subgroup.zpowers t⁆ = ⊥)
  (htH : t ∈ H)

include ht hp hp2 hX₀P hX₀H hX₀t hmin htH

theorem le_centralizer_of_isNormalIn {N : Subgroup G} (hNH : IsNormalIn N H)
    (hNt : ⁅N, Subgroup.zpowers t⁆ = ⊥) : X₀ ≤ Subgroup.centralizer (N : Set G) := by
  have ht2 : t * t = 1 := by rw [← pow_two, ← ht, pow_orderOf_eq_one]
  have hNt' : ∀ y ∈ N, t * y = y * t := by
    rw [Subgroup.commutator_comm, commutator_zpowers_eq_bot_iff] at hNt
    exact fun y hy => (hNt y hy).symm
  have htX₀ : t ∈ Subgroup.normalizer (X₀ : Set G) := mem_normalizer_of_isNormalIn hX₀H htH
  set Y := X₀ ⊓ Subgroup.centralizer (N : Set G) with hYdef
  have hWY : ⁅X₀, Subgroup.zpowers t⁆ ≤ Y := by
    rw [Subgroup.commutator_le]
    intro x hx τ hτ
    rcases eq_one_or_eq_of_mem_zpowers ht hτ with rfl | rfl
    · rw [commutatorElement_one_right]
      exact Y.one_mem
    · have hc : ⁅x, τ⁆ ∈ X₀ := commutator_zpowers_le_of_mem_normalizer htX₀
        (Subgroup.commutator_mem_commutator hx (Subgroup.mem_zpowers τ))
      refine ⟨hc, ?_⟩
      show ⁅x, τ⁆ ∈ Subgroup.centralizer (N : Set G)
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have hcH : ⁅x, τ⁆ ∈ H := hX₀H.1 hc
      refine (commute_of_conj_eq_inv ht2 (conj_commutatorElement_eq_inv ht2 x)
        (odd_orderOf_of_mem hp hp2 (hX₀P hc)) (hNt' y hy) (hNt' _ (hNH.2 _ hcH y hy))).symm
  by_contra hne
  have hYne : Y ≠ X₀ := fun h => hne (h ▸ inf_le_right)
  have hYH : IsNormalIn Y H := by
    refine ⟨inf_le_left.trans hX₀H.1, fun h hh y hy => ⟨hX₀H.2 h hh y hy.1, ?_⟩⟩
    exact (Subgroup.mem_normalizer_iff.mp
      (mem_normalizer_centralizer (mem_normalizer_of_isNormalIn hNH hh)) y).mp hy.2
  have h1 := hmin Y inf_le_left hYH hYne
  have h2 : ⁅⁅X₀, Subgroup.zpowers t⁆, Subgroup.zpowers t⁆ ≤ ⁅Y, Subgroup.zpowers t⁆ :=
    Subgroup.commutator_mono hWY le_rfl
  rw [h1, le_bot_iff, commutator_commutator_eq hp hp2 hX₀P ht htX₀] at h2
  exact hX₀t h2

theorem frattini_le :
    (frattini X₀).map X₀.subtype ≤ Subgroup.centralizer (X₀ : Set G) ⊓
      Subgroup.centralizer ({t} : Set G) := by
  set Φ := (frattini X₀).map X₀.subtype with hΦ
  have hΦH : IsNormalIn Φ H :=
    map_characteristic_isNormalIn_of_isNormalIn (frattini X₀) inferInstance hX₀H
  have hX₀1 : X₀ ≠ ⊥ := fun h => hX₀t (by rw [h, Subgroup.commutator_bot_left])
  have : Nontrivial X₀ := (Subgroup.nontrivial_iff_ne_bot X₀).mpr hX₀1
  have hΦne : Φ ≠ X₀ := by
    intro h
    apply frattini_ne_top' (X := X₀)
    apply Subgroup.map_injective X₀.subtype_injective
    rw [← hΦ, h, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hΦt := hmin Φ (Subgroup.map_subtype_le _) hΦH hΦne
  refine le_inf (Subgroup.le_centralizer_iff.mp
    (le_centralizer_of_isNormalIn ht hp hp2 hX₀P hX₀H hX₀t hmin htH hΦH hΦt)) ?_
  rw [Subgroup.commutator_comm, commutator_zpowers_eq_bot_iff] at hΦt
  intro x hx
  exact Subgroup.mem_centralizer_singleton_iff.mpr (hΦt x hx)

theorem commutatorElement_mem {a b : G} (ha : a ∈ X₀) (hb : b ∈ X₀) :
    ⁅a, b⁆ ∈ Subgroup.centralizer (X₀ : Set G) ⊓ Subgroup.centralizer ({t} : Set G) := by
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (IsPGroup p X₀) := ⟨(qCoreOf_isPGroup H p).to_le hX₀P⟩
  apply frattini_le ht hp hp2 hX₀P hX₀H hX₀t hmin htH
  have h := commutator_le_frattini_of_isPGroup (R := X₀) (p := p)
    (Subgroup.commutator_mem_commutator (Subgroup.mem_top (⟨a, ha⟩ : X₀))
      (Subgroup.mem_top (⟨b, hb⟩ : X₀)))
  exact ⟨_, h, rfl⟩

theorem pow_mem {x : G} (hx : x ∈ X₀) :
    x ^ p ∈ Subgroup.centralizer (X₀ : Set G) ⊓ Subgroup.centralizer ({t} : Set G) := by
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (IsPGroup p X₀) := ⟨(qCoreOf_isPGroup H p).to_le hX₀P⟩
  apply frattini_le ht hp hp2 hX₀P hX₀H hX₀t hmin htH
  exact ⟨_, pth_power_mem_frattini_of_isPGroup (R := X₀) (p := p) ⟨x, hx⟩, rfl⟩

theorem mul_pow_eq {x y : G} (hx : x ∈ X₀) (hy : y ∈ X₀) : (x * y) ^ p = x ^ p * y ^ p := by
  have hc := commutatorElement_mem ht hp hp2 hX₀P hX₀H hX₀t hmin htH hy hx
  have hcx : Commute ⁅y, x⁆ x := (Subgroup.mem_centralizer_iff.mp hc.1 x hx).symm
  have hcy : Commute ⁅y, x⁆ y := (Subgroup.mem_centralizer_iff.mp hc.1 y hy).symm
  rw [mul_pow_of_commute_commutator hcx hcy p]
  have hcp : ⁅y, x⁆ ^ p = 1 := by
    rw [← commutatorElement_pow_left hcy]
    have hyp := pow_mem ht hp hp2 hX₀P hX₀H hX₀t hmin htH hy
    rw [commutatorElement_eq_one_iff_mul_comm]
    exact ((Subgroup.mem_centralizer_iff.mp hyp.1) x hx).symm
  have hdvd : p ∣ p.choose 2 := by
    rw [Nat.choose_two_right]
    obtain ⟨k, hk⟩ := (hp.odd_of_ne_two hp2)
    refine ⟨k, ?_⟩
    rw [hk]
    have : (2 * k + 1) * (2 * k + 1 - 1) = 2 * ((2 * k + 1) * k) := by
      rw [Nat.add_sub_cancel]; ring
    rw [this, Nat.mul_div_cancel_left _ two_pos]
  obtain ⟨m, hm⟩ := hdvd
  rw [hm, pow_mul, hcp, one_pow, mul_one]

theorem pow_eq_one {x : G} (hx : x ∈ X₀) : x ^ p = 1 := by
  have ht2 : t * t = 1 := by rw [← pow_two, ← ht, pow_orderOf_eq_one]
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have htX₀ : t ∈ Subgroup.normalizer (X₀ : Set G) := mem_normalizer_of_isNormalIn hX₀H htH
  let Ω : Subgroup G :=
    { carrier := {y | y ∈ X₀ ∧ y ^ p = 1}
      mul_mem' := fun {a b} ha hb => ⟨X₀.mul_mem ha.1 hb.1, by
        rw [mul_pow_eq ht hp hp2 hX₀P hX₀H hX₀t hmin htH ha.1 hb.1, ha.2, hb.2, one_mul]⟩
      one_mem' := ⟨X₀.one_mem, one_pow p⟩
      inv_mem' := fun {a} ha => ⟨X₀.inv_mem ha.1, by rw [inv_pow, ha.2, inv_one]⟩ }
  by_contra hx1
  have hΩne : Ω ≠ X₀ := fun h => hx1 (h ▸ hx : x ∈ Ω).2
  have hΩH : IsNormalIn Ω H := by
    refine ⟨fun y hy => hX₀H.1 hy.1, fun h hh y hy => ⟨hX₀H.2 h hh y hy.1, ?_⟩⟩
    rw [← MulAut.conj_apply, ← map_pow, hy.2, map_one]
  have hΩt := hmin Ω (fun y hy => hy.1) hΩH hΩne
  rw [Subgroup.commutator_comm, commutator_zpowers_eq_bot_iff] at hΩt
  apply hX₀t
  rw [Subgroup.commutator_comm, commutator_zpowers_eq_bot_iff]
  intro y hy
  set ω := y⁻¹ * (t * y * t⁻¹) with hω
  have htyX : t * y * t⁻¹ ∈ X₀ := (Subgroup.mem_normalizer_iff.mp htX₀ y).mp hy
  have hωX : ω ∈ X₀ := X₀.mul_mem (X₀.inv_mem hy) htyX
  have hyp := pow_mem ht hp hp2 hX₀P hX₀H hX₀t hmin htH hy
  have hωp : ω ^ p = 1 := by
    rw [hω, mul_pow_eq ht hp hp2 hX₀P hX₀H hX₀t hmin htH (X₀.inv_mem hy) htyX, inv_pow,
      ← MulAut.conj_apply, ← map_pow, MulAut.conj_apply,
      (Subgroup.mem_centralizer_singleton_iff.mp hyp.2).symm, mul_inv_cancel_right, inv_mul_cancel]
  have hωt : ω * t = t * ω := hΩt ω ⟨hωX, hωp⟩
  have hyω : t * y * t⁻¹ = y * ω := by rw [hω]; group
  have hω2 : ω * ω = 1 := by
    have h1 : y = t * (t * y * t⁻¹) * t⁻¹ := by
      rw [htinv]
      calc y = (t * t) * y * (t * t) := by rw [ht2]; group
        _ = t * (t * y * t) * t := by group
    have h2 : t * ω * t⁻¹ = ω := by rw [← hωt, mul_inv_cancel_right]
    have h3 : y = y * ω * ω := by
      calc y = t * (y * ω) * t⁻¹ := by rw [← hyω]; exact h1
        _ = (t * y * t⁻¹) * (t * ω * t⁻¹) := by group
        _ = y * ω * ω := by rw [hyω, h2]
    calc ω * ω = y⁻¹ * (y * ω * ω) := by group
      _ = 1 := by rw [← h3, inv_mul_cancel]
  have hωo := odd_orderOf_of_mem hp hp2 (hX₀P hωX)
  have hω1 : ω = 1 := by
    obtain ⟨k, hk⟩ := exists_pow_sq_eq hωo
    rw [← hk, pow_two, hω2, one_pow]
  rw [hω] at hω1
  have := inv_mul_eq_one.mp hω1
  calc y * t = t * y * t⁻¹ * t := by rw [← this]
    _ = t * y := by group

end Minimal

omit [Finite G] in
theorem isMulCommutative_sup {A B : Subgroup G} (hA : IsMulCommutative A)
    (hB : IsMulCommutative B) (hAB : A ≤ Subgroup.centralizer (B : Set G)) :
    IsMulCommutative (A ⊔ B : Subgroup G) := by
  have hAA : A ≤ Subgroup.centralizer (A : Set G) := fun a ha => by
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact congrArg Subtype.val (hA.is_comm.comm ⟨b, hb⟩ ⟨a, ha⟩)
  have hBB : B ≤ Subgroup.centralizer (B : Set G) := fun a ha => by
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact congrArg Subtype.val (hB.is_comm.comm ⟨b, hb⟩ ⟨a, ha⟩)
  have hBA : B ≤ Subgroup.centralizer (A : Set G) := Subgroup.le_centralizer_iff.mp hAB
  have hle : A ⊔ B ≤ Subgroup.centralizer ((A ⊔ B : Subgroup G) : Set G) := by
    refine sup_le (fun a ha => fstar_centralizer_of_centralizes_join (hAA ha) (hAB ha))
      (fun b hb => fstar_centralizer_of_centralizes_join (hBA hb) (hBB hb))
  exact ⟨⟨fun a b => Subtype.ext
    ((Subgroup.mem_centralizer_iff.mp (hle a.2)) b b.2).symm⟩⟩

theorem card_le_of_isCyclic_of_pow_eq_one {A : Subgroup G} {p : ℕ} (hp : p.Prime)
    (hA : IsCyclic A) (hexp : ∀ x ∈ A, x ^ p = 1) : Nat.card A ≤ p := by
  obtain ⟨g, hg⟩ := isCyclic_iff_exists_orderOf_eq_natCard.mp hA
  rw [← hg]
  refine Nat.le_of_dvd hp.pos (orderOf_dvd_of_pow_eq_one ?_)
  exact Subtype.ext (hexp _ g.2)

section Structure

variable {t : G} (ht : orderOf t = 2) {H : Subgroup G} (hH : H ∈ benderM t) {p : ℕ}
  (hp : p.Prime) (hp2 : p ≠ 2)
  {X₀ : Subgroup G} (hX₀P : X₀ ≤ qCoreOf H p) (hX₀H : IsNormalIn X₀ H)
  (hX₀t : ⁅X₀, Subgroup.zpowers t⁆ ≠ ⊥)
  (hmin : ∀ Y : Subgroup G, Y ≤ X₀ → IsNormalIn Y H → Y ≠ X₀ → ⁅Y, Subgroup.zpowers t⁆ = ⊥)
  (hS2 : ∀ A ≤ qCoreOf H p ⊓ Subgroup.centralizer ({t} : Set G), IsMulCommutative A →
    IsCyclic A)
  (hS3 : ∀ A ≤ qCoreOf H p, Subgroup.centralizer ({t} : Set G) ≤
    Subgroup.normalizer (A : Set G) → IsMulCommutative A → A ≤ Subgroup.centralizer ({t} : Set G))

include ht hH hp hp2 hX₀P hX₀H hX₀t hmin hS2 hS3

omit hp hmin hS2 in
theorem center_props :
    IsNormalIn (X₀ ⊓ Subgroup.centralizer (X₀ : Set G)) H ∧
      IsMulCommutative (X₀ ⊓ Subgroup.centralizer (X₀ : Set G) : Subgroup G) ∧
      X₀ ⊓ Subgroup.centralizer (X₀ : Set G) ≤ Subgroup.centralizer ({t} : Set G) := by
  have _ := ht
  have _ := hp2
  have _ := hX₀t
  set Z := X₀ ⊓ Subgroup.centralizer (X₀ : Set G)
  have hZH : IsNormalIn Z H := by
    refine ⟨inf_le_left.trans hX₀H.1, fun h hh z hz => ⟨hX₀H.2 h hh z hz.1, ?_⟩⟩
    exact (Subgroup.mem_normalizer_iff.mp
      (mem_normalizer_centralizer (mem_normalizer_of_isNormalIn hX₀H hh)) z).mp hz.2
  have hZc : IsMulCommutative Z :=
    ⟨⟨fun a b => Subtype.ext ((Subgroup.mem_centralizer_iff.mp a.2.2) b b.2.1).symm⟩⟩
  refine ⟨hZH, hZc, hS3 Z (inf_le_left.trans hX₀P) ?_ hZc⟩
  exact fun c hc => mem_normalizer_of_isNormalIn hZH (centralizer_le_of_mem_benderM hH hc)

theorem card_center : Nat.card (X₀ ⊓ Subgroup.centralizer (X₀ : Set G) : Subgroup G) = p := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨hZH, hZc, hZt⟩ := center_props ht hH hp2 hX₀P hX₀H hX₀t hS3
  set Z := X₀ ⊓ Subgroup.centralizer (X₀ : Set G)
  have htH : t ∈ H := mem_of_mem_benderM hH
  have hcyc := hS2 Z (le_inf (inf_le_left.trans hX₀P) hZt) hZc
  have hle := card_le_of_isCyclic_of_pow_eq_one hp hcyc fun x hx =>
    pow_eq_one ht hp hp2 hX₀P hX₀H hX₀t hmin htH hx.1
  have hX₀1 : X₀ ≠ ⊥ := fun h => hX₀t (by rw [h, Subgroup.commutator_bot_left])
  have : Nontrivial X₀ := (Subgroup.nontrivial_iff_ne_bot X₀).mpr hX₀1
  have := ((qCoreOf_isPGroup H p).to_le hX₀P).center_nontrivial
  obtain ⟨z, hz⟩ := exists_ne (1 : Subgroup.center X₀)
  have hzZ : ((z : X₀) : G) ∈ Z := ⟨(z : X₀).2, by
    show ((z : X₀) : G) ∈ Subgroup.centralizer (X₀ : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    exact congrArg Subtype.val ((Subgroup.mem_center_iff.mp z.2) ⟨w, hw⟩)⟩
  have hZ1 : Z ≠ ⊥ := by
    intro h
    rw [h, Subgroup.mem_bot] at hzZ
    exact hz (Subtype.ext (Subtype.ext hzZ))
  obtain ⟨k, hk⟩ := ((qCoreOf_isPGroup H p).to_le (inf_le_left.trans hX₀P)).exists_card_eq
  have hk1 : k ≠ 0 := by
    rintro rfl
    rw [pow_zero, Subgroup.card_eq_one] at hk
    exact hZ1 hk
  rw [hk] at hle ⊢
  have : p ^ k ≤ p ^ 1 := by rw [pow_one]; exact hle
  have hk' : k = 1 := le_antisymm ((Nat.pow_le_pow_iff_right hp.one_lt).mp this)
    (Nat.one_le_iff_ne_zero.mpr hk1)
  rw [hk', pow_one]

theorem inf_centralizer_eq :
    X₀ ⊓ Subgroup.centralizer ({t} : Set G) = X₀ ⊓ Subgroup.centralizer (X₀ : Set G) := by
  obtain ⟨hZH, hZc, hZt⟩ := center_props ht hH hp2 hX₀P hX₀H hX₀t hS3
  have hZp := card_center ht hH hp hp2 hX₀P hX₀H hX₀t hmin hS2 hS3
  set Z := X₀ ⊓ Subgroup.centralizer (X₀ : Set G)
  have htH : t ∈ H := mem_of_mem_benderM hH
  refine le_antisymm (fun y hy => ?_) (le_inf inf_le_left hZt)
  set A := Z ⊔ Subgroup.zpowers y
  have hAc : IsMulCommutative A := by
    refine isMulCommutative_sup hZc inferInstance ?_
    intro z hz
    rw [← centralizer_zpowers_eq', Subgroup.mem_centralizer_iff] at *
    intro w hw
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
    exact (Subgroup.mem_centralizer_iff.mp hz.2) _ (X₀.zpow_mem hy.1 k)
  have hAX : A ≤ X₀ := sup_le inf_le_left (Subgroup.zpowers_le.mpr hy.1)
  have hAt : A ≤ Subgroup.centralizer ({t} : Set G) := sup_le hZt (Subgroup.zpowers_le.mpr hy.2)
  have hcyc := hS2 A (le_inf (hAX.trans hX₀P) hAt) hAc
  have hle := card_le_of_isCyclic_of_pow_eq_one hp hcyc fun x hx =>
    pow_eq_one ht hp hp2 hX₀P hX₀H hX₀t hmin htH (hAX hx)
  have hZA : Z = A := Subgroup.eq_of_le_of_card_ge le_sup_left (hZp ▸ hle)
  rw [hZA]
  exact (le_sup_right : Subgroup.zpowers y ≤ A) (Subgroup.mem_zpowers y)

omit hp hmin hS2 in
theorem not_isMulCommutative : ¬ IsMulCommutative X₀ := by
  intro hc
  have _ := ht
  have _ := hp2
  have hle := hS3 X₀ hX₀P (fun c hc' => mem_normalizer_of_isNormalIn hX₀H
    (centralizer_le_of_mem_benderM hH hc')) hc
  apply hX₀t
  rw [Subgroup.commutator_comm, commutator_zpowers_eq_bot_iff]
  exact fun x hx => Subgroup.mem_centralizer_singleton_iff.mp (hle hx)

theorem commutator_eq :
    ⁅X₀, X₀⁆ = X₀ ⊓ Subgroup.centralizer (X₀ : Set G) := by
  have hZp := card_center ht hH hp hp2 hX₀P hX₀H hX₀t hmin hS2 hS3
  have htH : t ∈ H := mem_of_mem_benderM hH
  have hle : ⁅X₀, X₀⁆ ≤ X₀ ⊓ Subgroup.centralizer (X₀ : Set G) := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    exact ⟨commutator_self_le X₀ (Subgroup.commutator_mem_commutator ha hb),
      (commutatorElement_mem ht hp hp2 hX₀P hX₀H hX₀t hmin htH ha hb).1⟩
  have hne : ⁅X₀, X₀⁆ ≠ ⊥ := by
    intro h
    apply not_isMulCommutative ht hH hp2 hX₀P hX₀H hX₀t hS3
    refine ⟨⟨fun a b => Subtype.ext ?_⟩⟩
    have := Subgroup.commutator_mem_commutator a.2 b.2
    rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at this
    exact this
  have : Fact p.Prime := ⟨hp⟩
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [hZp]
  have hdvd : Nat.card (⁅X₀, X₀⁆ : Subgroup G) ∣ p := hZp ▸ Subgroup.card_dvd_of_le hle
  rcases (Nat.dvd_prime hp).mp hdvd with h | h
  · exact absurd (Subgroup.card_eq_one.mp h) hne
  · exact h.ge

end Structure

omit [Finite G] in
theorem mem_normalizer_zpowers_of_conj_eq_inv {t w : G} (h : t * w * t⁻¹ = w⁻¹) :
    t ∈ Subgroup.normalizer ((Subgroup.zpowers w : Subgroup G) : Set G) := by
  have h' : t⁻¹ * w * t⁻¹⁻¹ = w⁻¹ := by
    have h1 : w = t⁻¹ * w⁻¹ * t := by rw [← h]; group
    have h2 : w⁻¹ = t⁻¹ * w * t := by
      calc w⁻¹ = (t⁻¹ * w⁻¹ * t)⁻¹ := by rw [← h1]
        _ = t⁻¹ * w * t := by group
    rw [inv_inv, ← h2]
  have key : ∀ g : G, g * w * g⁻¹ = w⁻¹ → ∀ y ∈ Subgroup.zpowers w,
      g * y * g⁻¹ ∈ Subgroup.zpowers w := by
    rintro g hg _ ⟨k, rfl⟩
    refine ⟨-k, ?_⟩
    simp only
    rw [← MulAut.conj_apply, map_zpow, MulAut.conj_apply, hg, inv_zpow', zpow_neg]
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨key t h y, fun hy => ?_⟩
  have := key t⁻¹ h' _ hy
  simpa [mul_assoc] using this

theorem card_ge_of_lt {A B : Subgroup G} {p : ℕ} (hp : p.Prime) (hBp : IsPGroup p B)
    (hAB : A < B) : p * Nat.card A ≤ Nat.card B := by
  have : Fact p.Prime := ⟨hp⟩
  have hle := hAB.le
  set i := (A.subgroupOf B).index
  have hcard : Nat.card A * i = Nat.card B := by
    rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv]
    exact (A.subgroupOf B).card_mul_index
  have hi1 : i ≠ 1 := by
    intro h
    rw [Subgroup.index_eq_one, Subgroup.subgroupOf_eq_top] at h
    exact hAB.ne (le_antisymm hle h)
  obtain ⟨n, hn⟩ := hBp.exists_card_eq
  have hidvd : i ∣ p ^ n := hn ▸ hcard ▸ dvd_mul_left i _
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow hp).mp hidvd
  have hk0 : k ≠ 0 := by rintro rfl; rw [pow_zero] at hk; exact hi1 hk
  have hpi : p ≤ i := by
    rw [hk]
    calc p = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ k := Nat.pow_le_pow_right hp.pos (Nat.one_le_iff_ne_zero.mpr hk0)
  rw [← hcard, mul_comm]
  exact Nat.mul_le_mul_left _ hpi

omit [Finite G] in
theorem mem_normalizer_of_map_conj_eq {A : Subgroup G} {c : G}
    (h : A.map (MulAut.conj c).toMonoidHom = A) : c ∈ Subgroup.normalizer (A : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    rw [← h]
    exact ⟨x, hx, rfl⟩
  · intro hx
    rw [← h] at hx
    obtain ⟨y, hy, hyx⟩ := hx
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hyx
    have : y = x := by simpa using hyx
    rwa [← this]

section Step6

variable (hG : BenderCounterexample G) {t : G} (ht : orderOf t = 2) {H : Subgroup G}
  (hH : H ∈ benderM t) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
  {X₀ : Subgroup G} (hX₀P : X₀ ≤ qCoreOf H p) (hX₀H : IsNormalIn X₀ H)
  (hX₀t : ⁅X₀, Subgroup.zpowers t⁆ ≠ ⊥)
  (hmin : ∀ Y : Subgroup G, Y ≤ X₀ → IsNormalIn Y H → Y ≠ X₀ → ⁅Y, Subgroup.zpowers t⁆ = ⊥)
  (hS2 : ∀ A ≤ qCoreOf H p ⊓ Subgroup.centralizer ({t} : Set G), IsMulCommutative A →
    IsCyclic A)
  (hS3 : ∀ A ≤ qCoreOf H p, Subgroup.centralizer ({t} : Set G) ≤
    Subgroup.normalizer (A : Set G) → IsMulCommutative A → A ≤ Subgroup.centralizer ({t} : Set G))

include hG ht hH hp hp2 hX₀P hX₀H hX₀t hmin hS2 hS3

theorem mem_of_commutator_ne_bot
    {V : Subgroup G} (hVX : V ≤ X₀) (hV : ⁅V, V⁆ ≠ ⊥) :
    V ∈ benderABar H := by
  have hZp := card_center ht hH hp hp2 hX₀P hX₀H hX₀t hmin hS2 hS3
  obtain ⟨hZH, -, -⟩ := center_props ht hH hp2 hX₀P hX₀H hX₀t hS3
  set Z := X₀ ⊓ Subgroup.centralizer (X₀ : Set G)
  have hZ1 : Z ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hZp
    exact hp.one_lt.ne hZp
  have hZA : Z ∈ benderABar H := mem_of_invariant hG ht hH hp hp2 (inf_le_left.trans hX₀P) hZ1
    fun c hc => mem_normalizer_of_isNormalIn hZH (centralizer_le_of_mem_benderM hH hc)
  have hle : ⁅V, V⁆ ≤ Z :=
    calc ⁅V, V⁆ ≤ ⁅X₀, X₀⁆ := Subgroup.commutator_mono hVX hVX
      _ = Z := commutator_eq ht hH hp hp2 hX₀P hX₀H hX₀t hmin hS2 hS3
  have hVZ : ⁅V, V⁆ = Z := by
    have : Fact p.Prime := ⟨hp⟩
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    rw [hZp]
    rcases (Nat.dvd_prime hp).mp (hZp ▸ Subgroup.card_dvd_of_le hle) with h | h
    · exact absurd (Subgroup.card_eq_one.mp h) hV
    · exact h.ge
  exact mem_of_commutator_eq hp hp2 hZA hZ1 (hVX.trans hX₀P) hVZ

theorem exists_inverted_not_mem
    {V : Subgroup G} (hVX : V ≤ X₀) (hV1 : V ≠ ⊥)
    (hVt : t ∈ Subgroup.normalizer (V : Set G)) (hVA : V ∉ benderABar H) :
    ∃ x ∈ X₀, x ≠ 1 ∧ t * x * t⁻¹ = x⁻¹ ∧ Subgroup.zpowers x ∉ benderABar H := by
  have ht2 : t * t = 1 := by rw [← pow_two, ← ht, pow_orderOf_eq_one]
  have htH : t ∈ H := mem_of_mem_benderM hH
  have htX₀ : t ∈ Subgroup.normalizer (X₀ : Set G) := mem_normalizer_of_isNormalIn hX₀H htH
  set W := X₀ ⊓ Subgroup.centralizer (V : Set G) with hWdef
  have htW : t ∈ Subgroup.normalizer (W : Set G) :=
    mem_normalizer_inf htX₀ (mem_normalizer_centralizer hVt)
  by_contra hcon
  push Not at hcon
  have hinv : ∀ w ∈ W, t * w * t⁻¹ = w⁻¹ → w = 1 := by
    intro w hw hwt
    by_contra hw1
    apply hVA
    have hwA := hcon w hw.1 hw1 hwt
    have hwo := odd_orderOf_of_mem hp hp2 (hX₀P hw.1)
    have hzt := mem_normalizer_zpowers_of_conj_eq_inv hwt
    have hwodd : Odd (Nat.card (Subgroup.zpowers w)) := by rwa [Nat.card_zpowers]
    have hinvz : ∀ y ∈ Subgroup.zpowers w, t * y * t⁻¹ = y⁻¹ := by
      rintro _ ⟨k, rfl⟩
      simp only
      rw [← MulAut.conj_apply, map_zpow, MulAut.conj_apply, hwt, inv_zpow']
      rw [zpow_neg]
    have hcomm := commutator_zpowers_eq_self_of_conj_eq_inv hzt hinvz hwodd
    refine bender1970_3_1_ii hG ht hH hV1 (le_and_isSubnormal hp (hVX.trans hX₀P)).1
      (le_and_isSubnormal hp (hVX.trans hX₀P)).2 hVt hwA ?_ hcomm
    rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
    intro v hv
    exact (Subgroup.mem_centralizer_iff.mp hw.2) v hv
  have hWt : W ≤ Subgroup.centralizer ({t} : Set G) := by
    intro w hw
    have hc : ⁅w, t⁆ ∈ W := by
      rw [commutatorElement_def]
      exact W.mul_mem (W.mul_mem hw ((Subgroup.mem_normalizer_iff.mp htW _).mp (W.inv_mem hw)))
        (W.one_mem) |> fun h => by simpa [mul_assoc] using h
    have h1 := hinv _ hc (conj_commutatorElement_eq_inv ht2 w)
    rw [commutatorElement_eq_one_iff_mul_comm] at h1
    exact Subgroup.mem_centralizer_singleton_iff.mpr h1
  have hWZ : W ≤ X₀ ⊓ Subgroup.centralizer (X₀ : Set G) := by
    rw [← inf_centralizer_eq ht hH hp hp2 hX₀P hX₀H hX₀t hmin hS2 hS3]
    exact le_inf inf_le_left hWt
  by_cases hab : ⁅V, V⁆ = ⊥
  ·
    apply hVA
    have hVW : V ≤ W := by
      refine le_inf hVX fun v hv => ?_
      rw [Subgroup.mem_centralizer_iff]
      intro w hw
      have := Subgroup.commutator_mem_commutator hw hv
      rw [hab, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at this
      exact this
    have hZp := card_center ht hH hp hp2 hX₀P hX₀H hX₀t hmin hS2 hS3
    obtain ⟨hZH, -, -⟩ := center_props ht hH hp2 hX₀P hX₀H hX₀t hS3
    have hVZ : V = X₀ ⊓ Subgroup.centralizer (X₀ : Set G) := by
      have hle := hVW.trans hWZ
      refine Subgroup.eq_of_le_of_card_ge hle ?_
      rw [hZp]
      rcases (Nat.dvd_prime hp).mp (hZp ▸ Subgroup.card_dvd_of_le hle) with h | h
      · exact absurd (Subgroup.card_eq_one.mp h) hV1
      · exact h.ge
    rw [hVZ]
    exact mem_of_invariant hG ht hH hp hp2 (inf_le_left.trans hX₀P) (hVZ ▸ hV1)
      fun c hc => mem_normalizer_of_isNormalIn hZH (centralizer_le_of_mem_benderM hH hc)
  · exact hVA (mem_of_commutator_ne_bot hG ht hH hp hp2 hX₀P hX₀H hX₀t hmin hS2 hS3 hVX hab)

omit hG in
theorem index_centralizer_le {x : G} (hx : x ∈ X₀) :
    ((X₀ ⊓ Subgroup.centralizer ({x} : Set G)).subgroupOf X₀).index ≤ p := by
  have htH : t ∈ H := mem_of_mem_benderM hH
  have hcm := fun {a b : G} (ha : a ∈ X₀) (hb : b ∈ X₀) =>
    commutatorElement_mem ht hp hp2 hX₀P hX₀H hX₀t hmin htH ha hb
  have hmemX : ∀ g ∈ X₀, ⁅g, x⁆ ∈ X₀ := fun g hg =>
    commutator_self_le X₀ (Subgroup.commutator_mem_commutator hg hx)
  let φ : X₀ →* X₀ :=
    { toFun := fun g => ⟨⁅(g : G), x⁆, hmemX g g.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun g h => Subtype.ext (by
        show ⁅(g : G) * h, x⁆ = ⁅(g : G), x⁆ * ⁅(h : G), x⁆
        have hc := (hcm h.2 hx).1
        exact commutatorElement_mul_left_of_commute
          ((Subgroup.mem_centralizer_iff.mp hc) g g.2)
          ((Subgroup.mem_centralizer_iff.mp hc) _ (hmemX g g.2))) }
  have hker : φ.ker = (X₀ ⊓ Subgroup.centralizer ({x} : Set G)).subgroupOf X₀ := by
    ext g
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro h
      have h' : ⁅(g : G), x⁆ = 1 := congrArg Subtype.val h
      rw [commutatorElement_eq_one_iff_mul_comm] at h'
      exact ⟨g.2, Subgroup.mem_centralizer_singleton_iff.mpr h'⟩
    · intro h
      apply Subtype.ext
      show ⁅(g : G), x⁆ = 1
      rw [commutatorElement_eq_one_iff_mul_comm]
      exact Subgroup.mem_centralizer_singleton_iff.mp h.2
  have hrange : φ.range ≤ (X₀ ⊓ Subgroup.centralizer (X₀ : Set G)).subgroupOf X₀ := by
    rintro _ ⟨g, rfl⟩
    exact ⟨hmemX g g.2, (hcm g.2 hx).1⟩
  rw [← hker, Subgroup.index_eq_card,
    Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv,
    ← card_center ht hH hp hp2 hX₀P hX₀H hX₀t hmin hS2 hS3]
  refine (Subgroup.card_le_of_le hrange).trans_eq ?_
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv

theorem card_le_pow_three {V : Subgroup G} (hVX : V ≤ X₀) (hV1 : V ≠ ⊥)
    (hVt : t ∈ Subgroup.normalizer (V : Set G)) (hVA : V ∉ benderABar H) :
    Nat.card X₀ ≤ p ^ 3 := by
  have : Fact p.Prime := ⟨hp⟩
  have ht2 : t * t = 1 := by rw [← pow_two, ← ht, pow_orderOf_eq_one]
  have htH : t ∈ H := mem_of_mem_benderM hH
  have hCH := centralizer_le_of_mem_benderM hH
  have htX₀ : t ∈ Subgroup.normalizer (X₀ : Set G) := mem_normalizer_of_isNormalIn hX₀H htH
  have hX₀p : IsPGroup p X₀ := (qCoreOf_isPGroup H p).to_le hX₀P
  have hZp := card_center ht hH hp hp2 hX₀P hX₀H hX₀t hmin hS2 hS3
  obtain ⟨hZH, hZc, hZt⟩ := center_props ht hH hp2 hX₀P hX₀H hX₀t hS3
  set Z := X₀ ⊓ Subgroup.centralizer (X₀ : Set G) with hZdef
  have hinf := inf_centralizer_eq ht hH hp hp2 hX₀P hX₀H hX₀t hmin hS2 hS3
  obtain ⟨x, hxX, hx1, hxt, hxA⟩ :=
    exists_inverted_not_mem hG ht hH hp hp2 hX₀P hX₀H hX₀t hmin hS2 hS3 hVX hV1 hVt hVA
  set A₁ := X₀ ⊓ Subgroup.centralizer ({x} : Set G) with hA₁def
  have hxN := mem_normalizer_zpowers_of_conj_eq_inv hxt
  have htA₁ : t ∈ Subgroup.normalizer (A₁ : Set G) := by
    refine mem_normalizer_inf htX₀ ?_
    rw [← centralizer_zpowers_eq']
    exact mem_normalizer_centralizer hxN
  set Y := ⁅A₁, Subgroup.zpowers t⁆ with hYdef
  have hYA₁ : Y ≤ A₁ := commutator_zpowers_le_of_mem_normalizer htA₁
  have hYnA : Y ∉ benderABar H := by
    intro hYA
    apply hxA
    have hzx : Subgroup.zpowers x ≤ qCoreOf H p := Subgroup.zpowers_le.mpr (hX₀P hxX)
    refine bender1970_3_1_ii hG ht hH (by rwa [Ne, Subgroup.zpowers_eq_bot])
      (le_and_isSubnormal hp hzx).1 (le_and_isSubnormal hp hzx).2 hxN hYA ?_
      (commutator_commutator_eq hp hp2 (inf_le_left.trans hX₀P) ht htA₁)
    intro y hy
    rw [centralizer_zpowers_eq']
    exact (hYA₁ hy).2
  have hYc : IsMulCommutative Y := by
    by_contra hnc
    apply hYnA
    refine mem_of_commutator_ne_bot hG ht hH hp hp2 hX₀P hX₀H hX₀t hmin hS2 hS3
      (hYA₁.trans inf_le_left) fun h => hnc ⟨⟨fun a b => Subtype.ext ?_⟩⟩
    have := Subgroup.commutator_mem_commutator a.2 b.2
    rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at this
    exact this
  have hA₁odd : Odd (Nat.card A₁) := odd_card_of_le hp hp2 (inf_le_left.trans hX₀P)
  have hA₁ZY : A₁ ≤ Z ⊔ Y := by
    intro a ha
    obtain ⟨c, hc, m, hm, rfl⟩ := exists_mem_centralizer_mul_mem_commutator ht2 htA₁ hA₁odd ha
    have hcZ : c ∈ Z := by
      have h : c ∈ X₀ ⊓ Subgroup.centralizer ({t} : Set G) := ⟨hc.1.1, hc.2⟩
      rw [hinf] at h
      exact h
    exact Subgroup.mul_mem_sup hcZ hm
  have hZYc : IsMulCommutative (Z ⊔ Y : Subgroup G) :=
    isMulCommutative_sup hZc hYc
      (inf_le_right.trans (Subgroup.centralizer_le (hYA₁.trans inf_le_left)))
  have hA₁c : IsMulCommutative A₁ :=
    ⟨⟨fun a b => Subtype.ext (show (a : G) * b = b * a from congrArg Subtype.val
      (hZYc.is_comm.comm ⟨a, hA₁ZY a.2⟩ ⟨b, hA₁ZY b.2⟩))⟩⟩
  obtain ⟨c, hc, hcA₁⟩ : ∃ c ∈ Subgroup.centralizer ({t} : Set G),
      c ∉ Subgroup.normalizer (A₁ : Set G) := by
    by_contra hcon
    push Not at hcon
    have hle := hS3 A₁ (inf_le_left.trans hX₀P) hcon hA₁c
    have hxC : x ∈ Subgroup.centralizer ({t} : Set G) :=
      hle ⟨hxX, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩
    have hx2 : x = x⁻¹ := by
      rw [← hxt, ← (Subgroup.mem_centralizer_singleton_iff.mp hxC), mul_inv_cancel_right]
    have hxx : x ^ 2 = 1 := by
      rw [pow_two]
      nth_rewrite 2 [hx2]
      exact mul_inv_cancel x
    obtain ⟨k, hk⟩ := exists_pow_sq_eq (odd_orderOf_of_mem hp hp2 (hX₀P hxX))
    exact hx1 (by rw [← hk, hxx, one_pow])
  set A₂ := A₁.map (MulAut.conj c).toMonoidHom with hA₂def
  have hcX₀ : c ∈ Subgroup.normalizer (X₀ : Set G) := mem_normalizer_of_isNormalIn hX₀H (hCH hc)
  have hA₂X : A₂ ≤ X₀ := by
    rintro _ ⟨a, ha, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp hcX₀ a).mp ha.1
  have hA₂card : Nat.card A₂ = Nat.card A₁ :=
    Subgroup.card_map_of_injective (MulAut.conj c).injective
  have hA₂ne : A₂ ≠ A₁ := fun h => hcA₁ (mem_normalizer_of_map_conj_eq h)
  have hA₂c : IsMulCommutative A₂ := Subgroup.map_isMulCommutative _ _
  have hcardi : ∀ A : Subgroup G, A ≤ X₀ →
      Nat.card A * (A.subgroupOf X₀).index = Nat.card X₀ := fun A hA => by
    rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA).toEquiv]
    exact (A.subgroupOf X₀).card_mul_index
  have hi₁ : (A₁.subgroupOf X₀).index ≤ p :=
    index_centralizer_le ht hH hp hp2 hX₀P hX₀H hX₀t hmin hS2 hS3 hxX |> fun h => by
      simpa [hA₁def] using h
  have hi₂ : (A₂.subgroupOf X₀).index ≤ p := by
    have h1 := hcardi A₁ inf_le_left
    have h2 := hcardi A₂ hA₂X
    rw [hA₂card] at h2
    have hpos : 0 < Nat.card A₁ := Nat.card_pos
    have : (A₂.subgroupOf X₀).index = (A₁.subgroupOf X₀).index :=
      Nat.eq_of_mul_eq_mul_left hpos (h2.trans h1.symm)
    rw [this]
    exact hi₁
  have hlt : A₁ < A₁ ⊔ A₂ := by
    refine lt_of_le_of_ne le_sup_left fun h => hA₂ne ?_
    exact Subgroup.eq_of_le_of_card_ge (h ▸ le_sup_right) hA₂card.symm.le
  have hsupX : A₁ ⊔ A₂ = X₀ := by
    refine Subgroup.eq_of_le_of_card_ge (sup_le inf_le_left hA₂X) ?_
    calc Nat.card X₀ = Nat.card A₁ * (A₁.subgroupOf X₀).index := (hcardi A₁ inf_le_left).symm
      _ ≤ Nat.card A₁ * p := Nat.mul_le_mul_left _ hi₁
      _ = p * Nat.card A₁ := mul_comm _ _
      _ ≤ Nat.card (A₁ ⊔ A₂ : Subgroup G) :=
          card_ge_of_lt hp (hX₀p.to_le (sup_le inf_le_left hA₂X)) hlt
  have hIZ : A₁ ⊓ A₂ ≤ Z := by
    intro z hz
    refine ⟨hz.1.1, ?_⟩
    show z ∈ Subgroup.centralizer (X₀ : Set G)
    have hle : A₁ ⊔ A₂ ≤ Subgroup.centralizer ({z} : Set G) := by
      refine sup_le (fun a ha => ?_) (fun a ha => ?_)
      · exact Subgroup.mem_centralizer_singleton_iff.mpr
          (congrArg Subtype.val (hA₁c.is_comm.comm ⟨a, ha⟩ ⟨z, hz.1⟩))
      · exact Subgroup.mem_centralizer_singleton_iff.mpr
          (congrArg Subtype.val (hA₂c.is_comm.comm ⟨a, ha⟩ ⟨z, hz.2⟩))
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle (hsupX ▸ hy))
  have hidx : ((A₁ ⊓ A₂).subgroupOf X₀).index ≤ p * p := by
    have : (A₁ ⊓ A₂).subgroupOf X₀ = A₁.subgroupOf X₀ ⊓ A₂.subgroupOf X₀ := by ext; rfl
    rw [this]
    exact Subgroup.index_inf_le.trans (Nat.mul_le_mul hi₁ hi₂)
  calc Nat.card X₀ = Nat.card (A₁ ⊓ A₂ : Subgroup G) * ((A₁ ⊓ A₂).subgroupOf X₀).index :=
        (hcardi _ (inf_le_left.trans inf_le_left)).symm
    _ ≤ p * (p * p) := Nat.mul_le_mul (hZp ▸ Subgroup.card_le_of_le hIZ) hidx
    _ = p ^ 3 := by ring

end Step6

section Step7

variable (hG : BenderCounterexample G) {t : G} (ht : orderOf t = 2) {H : Subgroup G}
  (hH : H ∈ benderM t) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
  {X₀ Z₀ : Subgroup G} (hX₀P : X₀ ≤ qCoreOf H p) (hX₀H : IsNormalIn X₀ H)
  (hX₀t : ⁅X₀, Subgroup.zpowers t⁆ ≠ ⊥)
  (hZ : X₀ ⊓ Subgroup.centralizer ({t} : Set G) ≤ Z₀) (hZ₀H : IsNormalIn Z₀ H)
  (hZ₀t : Z₀ ≤ Subgroup.centralizer ({t} : Set G))
  (hS1 : ∀ U ≤ qCoreOf H p ⊓ Subgroup.centralizer ({t} : Set G), U ≠ ⊥ → U ∈ benderABar H)

include hG ht hH hp hp2 hX₀P hX₀H hX₀t hZ hZ₀H hZ₀t hS1

theorem not_two_le_card_primesOfOrder :
    ¬ 2 ≤ Nat.card (primesOfOrder (generalizedFittingSubgroupOf H)) := by
  intro hπ
  have hsimple := hG.isSimpleGroup
  have : Fact p.Prime := ⟨hp⟩
  have htC : t ∈ Subgroup.centralizer ({t} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have hCH := centralizer_le_of_mem_benderM hH
  have htH : t ∈ H := hCH htC
  have hHco := isCoatom_of_mem_benderM hH
  obtain ⟨T, htT⟩ : ∃ T : Sylow 2 G, t ∈ (T : Subgroup G) := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hp' : IsPGroup 2 (Subgroup.zpowers t) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ht, pow_one])
    obtain ⟨T, hT⟩ := hp'.exists_le_sylow
    exact ⟨T, hT (Subgroup.mem_zpowers t)⟩
  have hTab := hG.hasAbelianSylowTwo T
  have hcommT : ∀ x ∈ (T : Subgroup G), ∀ y ∈ (T : Subgroup G), x * y = y * x :=
    fun x hx y hy => congrArg Subtype.val (hTab.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hTH : (T : Subgroup G) ≤ H := hG.sylow_le_of_mem_benderM T htT hH
  have hTX : (T : Subgroup G) ≤ Subgroup.normalizer (X₀ : Set G) := fun x hx =>
    mem_normalizer_of_isNormalIn hX₀H (hTH hx)
  have hX₀t' : ⁅Subgroup.zpowers t, X₀⁆ ≠ ⊥ := by rwa [Subgroup.commutator_comm]
  obtain ⟨R, hRT, hRr, hRt⟩ :=
    bender1970_3_4 T hTab htT ht hTX (odd_card_of_le hp hp2 hX₀P) hX₀t'
  obtain ⟨n, -, hnR⟩ := bender1970_1_3 hG.nonabelian T hTab hRT hRr htT ht
  set s := n * t * n⁻¹ with hsdef
  have hsT : s ∈ (T : Subgroup G) := hRT hnR
  set Y := X₀ ⊓ Subgroup.centralizer ({s} : Set G) with hYdef
  have hRY : X₀ ⊓ Subgroup.centralizer (R : Set G) ≤ Y :=
    inf_le_inf_left _ (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hnR))
  have hYt : ⁅Y, Subgroup.zpowers t⁆ ≠ ⊥ := by
    intro h
    apply hRt
    rw [Subgroup.commutator_comm, ← le_bot_iff, ← h]
    exact Subgroup.commutator_mono hRY le_rfl
  have hnH : n ∉ H := by
    intro hn
    apply hYt
    rw [Subgroup.commutator_comm, commutator_zpowers_eq_bot_iff]
    intro y hy
    have hy' : n⁻¹ * y * n ∈ X₀ ⊓ Subgroup.centralizer ({t} : Set G) := by
      refine ⟨?_, ?_⟩
      · have := hX₀H.2 n⁻¹ (H.inv_mem hn) y hy.1
        simpa using this
      · show n⁻¹ * y * n ∈ Subgroup.centralizer ({t} : Set G)
        rw [Subgroup.mem_centralizer_singleton_iff]
        have hys := Subgroup.mem_centralizer_singleton_iff.mp hy.2
        rw [hsdef] at hys
        calc n⁻¹ * y * n * t = n⁻¹ * (y * (n * t * n⁻¹)) * n := by group
          _ = n⁻¹ * ((n * t * n⁻¹) * y) * n := by rw [hys]
          _ = t * (n⁻¹ * y * n) := by group
    have hyZ : y ∈ Z₀ := by
      have := hZ₀H.2 n hn _ (hZ hy')
      simpa [mul_assoc] using this
    exact Subgroup.mem_centralizer_singleton_iff.mp (hZ₀t hyZ)
  set U := ⁅Y, Subgroup.zpowers t⁆ with hUdef
  have htCs : t ∈ Subgroup.centralizer ({s} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (hcommT t htT s hsT)
  have hUs : U ≤ Subgroup.centralizer ({s} : Set G) := by
    rw [hUdef, Subgroup.commutator_le]
    intro y hy τ hτ
    have hτ' : τ ∈ Subgroup.centralizer ({s} : Set G) := Subgroup.zpowers_le.mpr htCs hτ
    rw [commutatorElement_def]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hy.2 hτ')
      (Subgroup.inv_mem _ hy.2)) (Subgroup.inv_mem _ hτ')
  set Hs := H.map (MulAut.conj n).toMonoidHom with hHsdef
  have hHs : Hs ∈ benderM s := map_conj_mem_benderM n hH
  have hHsco := isCoatom_of_mem_benderM hHs
  have hHsA : IsAStar Hs := hG.isAStar_of_isCoatom hHsco
  have hCHs := centralizer_le_of_mem_benderM hHs
  have htHs : t ∈ Hs := hCHs htCs
  set P₀ := qCoreOf H p ⊓ Hs with hP₀def
  have hP₀ : IsPGroup p P₀ := (qCoreOf_isPGroup H p).to_le inf_le_left
  have hCP₀ : Hs ⊓ Subgroup.centralizer ({t} : Set G) ≤ Subgroup.normalizer (P₀ : Set G) :=
    fun c hc => mem_normalizer_inf (centralizer_le_normalizer_qCoreOf hH hc.2)
      (Subgroup.le_normalizer hc.1)
  have h24 := bender1970_2_4_pGroup_subgroup hHsA htHs ht hp hp2 inf_le_right hP₀ hCP₀
  have hYP₀ : Y ≤ P₀ := le_inf (inf_le_left.trans hX₀P) (inf_le_right.trans hCHs)
  have hUO : U ≤ qCoreOf Hs p := (Subgroup.commutator_mono hYP₀ le_rfl).trans h24
  have hOconj : qCoreOf Hs p = (qCoreOf H p).map (MulAut.conj n).toMonoidHom :=
    qCoreOf_conjugateSubgroup H n p
  set U' := U.map (MulAut.conj n⁻¹).toMonoidHom with hU'def
  have hU'K : U' ≤ qCoreOf H p ⊓ Subgroup.centralizer ({t} : Set G) := by
    rintro _ ⟨u, hu, rfl⟩
    have hu1 := hUO hu
    rw [hOconj] at hu1
    obtain ⟨v, hv, hvu⟩ := hu1
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hvu ⊢
    refine ⟨?_, ?_⟩
    · rw [← hvu]
      simpa [mul_assoc] using hv
    · show n⁻¹ * u * n⁻¹⁻¹ ∈ Subgroup.centralizer ({t} : Set G)
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hus := Subgroup.mem_centralizer_singleton_iff.mp (hUs hu)
      rw [hsdef] at hus
      calc n⁻¹ * u * n⁻¹⁻¹ * t = n⁻¹ * (u * (n * t * n⁻¹)) * n := by group
        _ = n⁻¹ * ((n * t * n⁻¹) * u) * n := by rw [hus]
        _ = t * (n⁻¹ * u * n⁻¹⁻¹) := by group
  have hU1 : U ≠ ⊥ := hYt
  have hU'1 : U' ≠ ⊥ := by
    rw [hU'def, Ne, Subgroup.map_eq_bot_iff_of_injective _ (MulAut.conj n⁻¹).injective]
    exact hU1
  have hU'A := hS1 U' hU'K hU'1
  have hUA : U ∈ benderABar Hs := by
    have h := map_conj_mem_benderABar n hU'A
    rwa [hU'def, map_conj_inv_map_conj] at h
  have hπs : 2 ≤ Nat.card (primesOfOrder (generalizedFittingSubgroupOf Hs)) := by
    rw [hHsdef]
    have hF := generalizedFittingSubgroupOf_conjugateSubgroup H n
    change 2 ≤ Nat.card (primesOfOrder (generalizedFittingSubgroupOf (conjugateSubgroup H n)))
    rw [hF, primesOfOrder_map_conj]
    exact hπ
  have hNU : Subgroup.normalizer (U : Set G) ≤ Hs := hUA.2.2.1 hπs
  have hUP : U ≤ qCoreOf H p :=
    (commutator_zpowers_le_of_mem_normalizer (mem_normalizer_inf
      (mem_normalizer_of_isNormalIn hX₀H htH)
      (Subgroup.le_normalizer htCs))).trans (inf_le_left.trans hX₀P)
  obtain ⟨hUF, hUsn⟩ := le_and_isSubnormal hp hUP
  have hHHs : H = Hs := bender1970_1_7_v_equalityOfMaximal hsimple H hHco (subnormalHull H U)
    (subnormalHull_le_generalizedFitting hUF) (isSubnormal_subnormalHull hUF hUsn)
    (generalizedFitting_inf_centralizer_subnormalHull_le H U)
    ((subnormalHull_le_sup_centralizer hUF hUsn).trans
      ((sup_centralizer_le_normalizer U).trans hNU)) hHsco (Or.inl hπ) hHsA ⟨n, rfl⟩
  exact hnH (hG.mem_of_map_conj_eq hHco hHHs.symm)

end Step7

theorem inf_centralizer_le_generalizedFitting (A : Subgroup G) :
    A ⊓ Subgroup.centralizer (generalizedFittingSubgroupOf A : Set G) ≤
      generalizedFittingSubgroupOf A := by
  rintro x ⟨hxA, hxC⟩
  rw [← generalizedFittingSubgroupOf_subgroup_top_eq A]
  refine ⟨⟨x, hxA⟩, CFSG.Adapters.centralizer_generalizedFittingSubgroupOf_top_le (G := A) ?_, rfl⟩
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  apply Subtype.ext
  have hy' : (y : G) ∈ generalizedFittingSubgroupOf A := by
    rw [← generalizedFittingSubgroupOf_subgroup_top_eq A]
    exact ⟨y, hy, rfl⟩
  exact (Subgroup.mem_centralizer_iff.mp hxC) y hy'

section Step89

variable (hG : BenderCounterexample G) {t : G} (ht : orderOf t = 2) {H : Subgroup G}
  (hH : H ∈ benderM t) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
  {X₀ : Subgroup G} (hX₀P : X₀ ≤ qCoreOf H p) (hX₀H : IsNormalIn X₀ H)
  (hX₀t : ⁅X₀, Subgroup.zpowers t⁆ ≠ ⊥)

include hG ht hH hp hp2 hX₀P hX₀H hX₀t

theorem centralizer_X₀_le (hneg : NoGood t H p) :
    qCoreOf H p ⊓ Subgroup.centralizer (X₀ : Set G) ≤ Subgroup.centralizer ({t} : Set G) := by
  set C₀ := qCoreOf H p ⊓ Subgroup.centralizer (X₀ : Set G) with hC₀def
  have hCH := centralizer_le_of_mem_benderM hH
  have hX₀C : Subgroup.centralizer ({t} : Set G) ≤ Subgroup.normalizer (X₀ : Set G) :=
    fun c hc => mem_normalizer_of_isNormalIn hX₀H (hCH hc)
  have hC₀C : Subgroup.centralizer ({t} : Set G) ≤ Subgroup.normalizer (C₀ : Set G) :=
    fun c hc => mem_normalizer_inf (centralizer_le_normalizer_qCoreOf hH hc)
      (mem_normalizer_centralizer (hX₀C hc))
  by_contra hcon
  have hC₀t : ⁅C₀, Subgroup.zpowers t⁆ ≠ ⊥ := by
    intro h
    apply hcon
    rw [Subgroup.commutator_comm, commutator_zpowers_eq_bot_iff] at h
    intro c hc
    exact Subgroup.mem_centralizer_singleton_iff.mpr (h c hc)
  obtain ⟨V, hVC, hV1, hVt, hVA⟩ := hneg C₀ inf_le_left hC₀C hC₀t
  apply hVA
  have htC : t ∈ Subgroup.centralizer ({t} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr rfl
  refine mem_of_centralized hG ht hH hp hp2 hX₀P hX₀C hX₀t (hVC.trans inf_le_left) hV1 hVt ?_
  intro v hv
  rw [Subgroup.mem_centralizer_iff]
  intro w hw
  have hwX : w ∈ X₀ := commutator_zpowers_le_of_mem_normalizer (hX₀C htC) hw
  exact ((Subgroup.mem_centralizer_iff.mp (hVC hv).2) w hwX)

omit ht hX₀t in
theorem eq_one_of_centralizes (hFp : IsPGroup p (generalizedFittingSubgroupOf H))
    (hC₀ : qCoreOf H p ⊓ Subgroup.centralizer (X₀ : Set G) ≤ Subgroup.centralizer ({t} : Set G))
    (hS2 : ∀ A ≤ qCoreOf H p ⊓ Subgroup.centralizer ({t} : Set G), IsMulCommutative A →
      IsCyclic A)
    (hZp : Nat.card (X₀ ⊓ Subgroup.centralizer (X₀ : Set G) : Subgroup G) = p)
    (hZ₀t : X₀ ⊓ Subgroup.centralizer (X₀ : Set G) ≤ Subgroup.centralizer ({t} : Set G))
    (hexp : ∀ x ∈ X₀, x ^ p = 1) (T : Sylow 2 G) (htT : t ∈ (T : Subgroup G))
    {e : G} (heT : e ∈ (T : Subgroup G)) (he2 : e * e = 1)
    (heX : X₀ ≤ Subgroup.centralizer ({e} : Set G)) : e = 1 := by
  have : Fact p.Prime := ⟨hp⟩
  set P := qCoreOf H p with hPdef
  set C₀ := P ⊓ Subgroup.centralizer (X₀ : Set G) with hC₀def
  set Z₀ := X₀ ⊓ Subgroup.centralizer (X₀ : Set G) with hZ₀def
  have hTH := hG.sylow_le_of_mem_benderM T htT hH
  have heH : e ∈ H := hTH heT
  have heP : e ∈ Subgroup.normalizer (P : Set G) :=
    mem_normalizer_of_isNormalIn (qCoreOf_normal_in H p) heH
  have heX₀ : e ∈ Subgroup.normalizer (X₀ : Set G) := mem_normalizer_of_isNormalIn hX₀H heH
  have heC₀ : e ∈ Subgroup.normalizer (C₀ : Set G) :=
    mem_normalizer_inf heP (mem_normalizer_centralizer heX₀)
  have hPp : IsPGroup p P := qCoreOf_isPGroup H p
  have heCen : ∀ c ∈ C₀, c * e = e * c := by
    by_contra hcon
    push Not at hcon
    obtain ⟨c, hc, hce⟩ := hcon
    set y := ⁅c, e⁆ with hydef
    have hy1 : y ≠ 1 := by
      rw [hydef, Ne, commutatorElement_eq_one_iff_mul_comm]
      exact fun h => hce h
    have hyC₀ : y ∈ C₀ := by
      have h1 : y = c * (e * c⁻¹ * e⁻¹) := by rw [hydef, commutatorElement_def]; group
      rw [h1]
      exact C₀.mul_mem hc ((Subgroup.mem_normalizer_iff.mp heC₀ _).mp (C₀.inv_mem hc))
    have hey : e * y * e⁻¹ = y⁻¹ := conj_commutatorElement_eq_inv he2 c
    have hpy : p ∣ Nat.card (Subgroup.zpowers y) := by
      rw [Nat.card_zpowers]
      have h1 : (⟨y, hyC₀⟩ : C₀) ≠ 1 := fun h => hy1 (congrArg Subtype.val h)
      have h2 := (hPp.to_le (inf_le_left : C₀ ≤ P)).dvd_orderOf h1
      rwa [Subgroup.orderOf_mk] at h2
    obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.zpowers y) p hpy
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp w.2
    have hwo : orderOf (w : G) = p := by rw [Subgroup.orderOf_coe]; exact hw
    have hew : e * (w : G) * e⁻¹ = (w : G)⁻¹ := by
      rw [← hk, ← MulAut.conj_apply, map_zpow, MulAut.conj_apply, hey, inv_zpow']
      rw [zpow_neg]
    have hwC₀ : (w : G) ∈ C₀ := by rw [← hk]; exact C₀.zpow_mem hyC₀ k
    set B := Z₀ ⊔ Subgroup.zpowers (w : G)
    have hBc : IsMulCommutative B := by
      refine isMulCommutative_sup ⟨⟨fun a b => Subtype.ext
        ((Subgroup.mem_centralizer_iff.mp a.2.2) b b.2.1).symm⟩⟩ inferInstance ?_
      intro z hz
      rw [Subgroup.mem_centralizer_iff]
      intro v hv
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hv
      exact ((Subgroup.mem_centralizer_iff.mp (C₀.zpow_mem hwC₀ j).2) z hz.1).symm
    have hBK : B ≤ P ⊓ Subgroup.centralizer ({t} : Set G) := by
      refine sup_le ?_ (Subgroup.zpowers_le.mpr ⟨hwC₀.1, hC₀ hwC₀⟩)
      intro z hz
      exact ⟨hX₀P hz.1, hZ₀t hz⟩
    have hBcyc := hS2 B hBK hBc
    have hBexp : ∀ x ∈ B, x ^ p = 1 := by
      intro x hx
      obtain ⟨z, hz, v, hv, rfl⟩ := GorensteinWalter.mem_sup_decompose_of_centralizes hx (by
        intro v hv
        rw [Subgroup.mem_centralizer_iff]
        intro z hz
        obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hv
        exact (Subgroup.mem_centralizer_iff.mp (C₀.zpow_mem hwC₀ j).2) z hz.1)
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hv
      have hzv : Commute z ((w : G) ^ j) :=
        ((Subgroup.mem_centralizer_iff.mp (C₀.zpow_mem hwC₀ j).2) z hz.1)
      rw [hzv.mul_pow, hexp z hz.1, one_mul, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul,
        zpow_natCast, ← hwo, pow_orderOf_eq_one, one_zpow]
    have hBle := card_le_of_isCyclic_of_pow_eq_one hp hBcyc hBexp
    have hZB : Z₀ = B := Subgroup.eq_of_le_of_card_ge le_sup_left (hZp ▸ hBle)
    have hwZ : (w : G) ∈ Z₀ := hZB ▸ (le_sup_right : Subgroup.zpowers (w : G) ≤ B)
      (Subgroup.mem_zpowers _)
    have hew' : e * (w : G) * e⁻¹ = w := by
      have := Subgroup.mem_centralizer_singleton_iff.mp (heX hwZ.1)
      rw [← this, mul_inv_cancel_right]
    rw [hew'] at hew
    have hww : (w : G) * w = 1 := by
      calc (w : G) * w = (w : G)⁻¹ * w := by rw [← hew]
        _ = 1 := inv_mul_cancel _
    have hw1 := eq_one_of_sq_eq_one hp hp2 hexp hwZ.1 hww
    rw [hw1, orderOf_one] at hwo
    exact hp.one_lt.ne hwo
  have hcop : Nat.Coprime p (orderOf e) := by
    have h2 : orderOf e ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two, he2])
    exact Nat.Coprime.coprime_dvd_right h2 ((Nat.coprime_primes hp Nat.prime_two).mpr hp2)
  have hX₀e : ⁅X₀, Subgroup.zpowers e⁆ = ⊥ := by
    rw [Subgroup.commutator_comm, commutator_zpowers_eq_bot_iff]
    exact fun x hx => Subgroup.mem_centralizer_singleton_iff.mp (heX hx)
  have hC₀e : ⁅C₀, Subgroup.zpowers e⁆ = ⊥ := by
    rw [Subgroup.commutator_comm, commutator_zpowers_eq_bot_iff]
    exact heCen
  have h11 := bender1970_1_1_thompson p hp X₀ (Subgroup.zpowers e) P
    ((qCoreOf_isPGroup H p).to_le hX₀P) hPp (pResidualOf_zpowers_eq hp hcop)
    (fun x hx => Subgroup.le_normalizer (hX₀P hx)) (Subgroup.zpowers_le.mpr heP) hX₀e hC₀e
  have heCP : e ∈ Subgroup.centralizer (P : Set G) := h11 (Subgroup.mem_zpowers e)
  have hFH := generalizedFittingSubgroupOf_isNormalIn H
  have hFP : generalizedFittingSubgroupOf H ≤ P :=
    le_qCoreOf_of_normal_isPGroup H _ p hFH.1
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hFH.1).mpr (le_normalizer_of_isNormalIn hFH))
      hFp
  have heF : e ∈ generalizedFittingSubgroupOf H :=
    inf_centralizer_le_generalizedFitting H ⟨heH, Subgroup.centralizer_le hFP heCP⟩
  have heo : Odd (orderOf e) := by
    obtain ⟨k, hk⟩ := hFp.exists_card_eq
    have h := Subgroup.orderOf_dvd_natCard _ heF
    rw [hk] at h
    exact Odd.of_dvd_nat (hp.odd_of_ne_two hp2).pow h
  obtain ⟨k, hk⟩ := exists_pow_sq_eq heo
  rw [← hk, pow_two, he2, one_pow]

end Step89

end Bender35

open Bender35 in
theorem bender1970_3_5
    (hG : BenderCounterexample G) {t : G} (ht : orderOf t = 2)
    {H : Subgroup G} (hH : H ∈ benderM t) {p : ℕ} (hp : p.Prime)
    (hpt : ⁅Subgroup.zpowers t, qCoreOf H p⁆ ≠ ⊥) :
    ∃ Pbar ≤ qCoreOf H p, Subgroup.centralizer ({t} : Set G) ≤ Subgroup.normalizer (Pbar : Set G) ∧
      ⁅Subgroup.zpowers t, Pbar⁆ ≠ ⊥ ∧
      ∀ V ≤ Pbar, V ≠ ⊥ → t ∈ Subgroup.normalizer (V : Set G) → V ∈ benderABar H := by
  have : Fact p.Prime := ⟨hp⟩
  have htC : t ∈ Subgroup.centralizer ({t} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have hCH := centralizer_le_of_mem_benderM hH
  have htH : t ∈ H := hCH htC
  set P := qCoreOf H p with hPdef
  have htP : t ∈ Subgroup.normalizer (P : Set G) :=
    mem_normalizer_of_isNormalIn (qCoreOf_normal_in H p) htH
  have hp2 : p ≠ 2 := by
    rintro rfl
    apply hpt
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have htp : IsPGroup 2 (Subgroup.zpowers t) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ht, pow_one])
    have hsup := htp.to_sup_of_normal_right' (qCoreOf_isPGroup H 2) (Subgroup.zpowers_le.mpr htP)
    obtain ⟨Q, hQ⟩ := hsup.exists_le_sylow
    have hQab := hG.hasAbelianSylowTwo Q
    rw [commutator_zpowers_eq_bot_iff]
    intro x hx
    have hxQ : x ∈ (Q : Subgroup G) :=
      hQ ((le_sup_right : qCoreOf H 2 ≤ Subgroup.zpowers t ⊔ qCoreOf H 2) hx)
    have htQ : t ∈ (Q : Subgroup G) :=
      hQ ((le_sup_left : Subgroup.zpowers t ≤ Subgroup.zpowers t ⊔ qCoreOf H 2)
        (Subgroup.mem_zpowers t))
    exact congrArg Subtype.val (hQab.is_comm.comm ⟨x, hxQ⟩ ⟨t, htQ⟩)
  by_contra hcon
  have hneg : NoGood t H p := by
    intro Pbar hPbar hPbarC hPbart
    by_contra h
    push Not at h
    exact hcon ⟨Pbar, hPbar, hPbarC, by rwa [Subgroup.commutator_comm], h⟩
  have hpt' : ⁅P, Subgroup.zpowers t⁆ ≠ ⊥ := by rwa [Subgroup.commutator_comm]
  have hS1 := fun U hU hU1 => mem_of_le_K hG ht hH hp hp2 hpt' (U := U) hU hU1
  have hS2 := fun A hA hAc => isCyclic_of_le_K hG ht hH hp hp2 hneg hpt' (A := A) hA hAc
  have hS3 := fun A hA hAC hAc =>
    le_centralizer_of_isMulCommutative hG ht hH hp hp2 hneg (A := A) hA hAC hAc
  set 𝒳 : Set (Subgroup G) :=
    {X | X ≤ P ∧ IsNormalIn X H ∧ ⁅X, Subgroup.zpowers t⁆ ≠ ⊥} with h𝒳
  have hP𝒳 : P ∈ 𝒳 := ⟨le_rfl, qCoreOf_normal_in H p, hpt'⟩
  obtain ⟨X₀, ⟨hX₀P, hX₀H, hX₀t⟩, hX₀min⟩ :=
    Set.exists_min_image 𝒳 (fun X => Nat.card X) (Set.toFinite _) ⟨P, hP𝒳⟩
  have hmin : ∀ Y : Subgroup G, Y ≤ X₀ → IsNormalIn Y H → Y ≠ X₀ →
      ⁅Y, Subgroup.zpowers t⁆ = ⊥ := by
    intro Y hYX hYH hYne
    by_contra hY
    exact hYne (Subgroup.eq_of_le_of_card_ge hYX
      (hX₀min Y ⟨hYX.trans hX₀P, hYH, hY⟩))
  obtain ⟨hZH, -, hZt⟩ := center_props ht hH hp2 hX₀P hX₀H hX₀t hS3
  have hZp := card_center ht hH hp hp2 hX₀P hX₀H hX₀t hmin hS2 hS3
  have hinf := inf_centralizer_eq ht hH hp hp2 hX₀P hX₀H hX₀t hmin hS2 hS3
  have hcomm := commutator_eq ht hH hp hp2 hX₀P hX₀H hX₀t hmin hS2 hS3
  have hexp : ∀ x ∈ X₀, x ^ p = 1 := fun x hx =>
    pow_eq_one ht hp hp2 hX₀P hX₀H hX₀t hmin htH hx
  have hX₀C : Subgroup.centralizer ({t} : Set G) ≤ Subgroup.normalizer (X₀ : Set G) :=
    fun c hc => mem_normalizer_of_isNormalIn hX₀H (hCH hc)
  obtain ⟨V, hVX, hV1, hVt, hVA⟩ := hneg X₀ hX₀P hX₀C hX₀t
  have hX₀3 :=
    card_le_pow_three hG ht hH hp hp2 hX₀P hX₀H hX₀t hmin hS2 hS3 hVX hV1 hVt hVA
  have hπ := not_two_le_card_primesOfOrder hG ht hH hp hp2 hX₀P hX₀H hX₀t hinf.le hZH hZt hS1
  have hH1 : H ≠ ⊥ := fun h => hG.bot_not_isCoatom (h ▸ isCoatom_of_mem_benderM hH)
  have hπ1 : Nat.card (primesOfOrder (generalizedFittingSubgroupOf H)) = 1 :=
    le_antisymm (by omega) (one_le_card_primesOfOrder (generalizedFittingSubgroupOf_ne_bot hH1))
  obtain ⟨q, hq, hFq, -, -⟩ := exists_isPGroup_of_card_primesOfOrder_eq_one hπ1
  have hX₀1 : X₀ ≠ ⊥ := fun h => hX₀t (by rw [h, Subgroup.commutator_bot_left])
  have hqp : q = p := eq_of_isPGroup_of_isPGroup hq hp
    (hFq.to_le (hX₀P.trans (le_and_isSubnormal hp le_rfl).1))
    ((qCoreOf_isPGroup H p).to_le hX₀P) hX₀1
  subst hqp
  have hC₀ := centralizer_X₀_le hG ht hH hq hp2 hX₀P hX₀H hX₀t hneg
  obtain ⟨T, htT⟩ : ∃ T : Sylow 2 G, t ∈ (T : Subgroup G) := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hp' : IsPGroup 2 (Subgroup.zpowers t) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ht, pow_one])
    obtain ⟨T, hT⟩ := hp'.exists_le_sylow
    exact ⟨T, hT (Subgroup.mem_zpowers t)⟩
  have hTab := hG.hasAbelianSylowTwo T
  have hcommT : ∀ x ∈ (T : Subgroup G), ∀ y ∈ (T : Subgroup G), x * y = y * x :=
    fun x hx y hy => congrArg Subtype.val (hTab.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  set E := omegaOneOfComm 2 (T : Subgroup G) hcommT with hEdef
  have hTH := hG.sylow_le_of_mem_benderM T htT hH
  have hEN : E ≤ Subgroup.normalizer (X₀ : Set G) := fun e he =>
    mem_normalizer_of_isNormalIn hX₀H (hTH he.1)
  have hEc : IsMulCommutative E :=
    ⟨⟨fun a b => Subtype.ext (hcommT _ a.2.1 _ b.2.1)⟩⟩
  have hE2 : ∀ e ∈ E, e * e = 1 := fun e he => by rw [← pow_two]; exact he.2
  have hfaith : ∀ e ∈ E, X₀ ≤ Subgroup.centralizer ({e} : Set G) → e = 1 := fun e he heX =>
    eq_one_of_centralizes hG hH hq hp2 hX₀P hX₀H hFq hC₀ hS2 hZp hZt hexp T htT he.1
      (hE2 e he) heX
  have hE4 := card_le_four_of_faithful hq hp2 ((qCoreOf_isPGroup H q).to_le hX₀P) hexp hZp hX₀3
    hcomm hEN hEc hE2 hfaith
  have hcardE : Nat.card E = 2 ^ CFSG.Open.pRank 2 (T : Subgroup G) :=
    card_omegaOneOfComm Nat.prime_two _ hcommT T.isPGroup'
  have h3 := hG.three_le_rank_sylow T
  rw [rank_eq_pRank_of_isPGroup Nat.prime_two T.isPGroup'] at h3
  have h8 : 8 ≤ Nat.card E := by
    rw [hcardE]
    exact (Nat.pow_le_pow_right two_pos h3 : 2 ^ 3 ≤ _)
  omega

end CFSG.Walter
