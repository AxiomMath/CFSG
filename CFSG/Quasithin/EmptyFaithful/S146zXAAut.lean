module

public import CFSG.Quasithin.EmptyFaithful.S146zXAXi
public import CFSG.Quasithin.EmptyFaithfulMultiple.Inputs5
public import CFSG.Quasithin.EmptyFaithful.S146F20

public section

namespace CFSG.Quasithin.S146zX

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open scoped commutatorElement Pointwise

section Generic

variable {Γ : Type*} [Group Γ]

theorem commutator_centralizes {Pb : Subgroup Γ} {c u₁ u₂ : Γ} {k₁ k₂ : ℕ}
    (hn : ∀ (k : ℕ), ∀ x ∈ Pb, c ^ k * x * (c ^ k)⁻¹ ∈ Pb)
    (h₁ : ∀ x ∈ Pb, u₁ * x * u₁⁻¹ = c ^ k₁ * x * (c ^ k₁)⁻¹)
    (h₂ : ∀ x ∈ Pb, u₂ * x * u₂⁻¹ = c ^ k₂ * x * (c ^ k₂)⁻¹) :
    ∀ x ∈ Pb, (u₁⁻¹ * u₂⁻¹ * u₁ * u₂) * x * (u₁⁻¹ * u₂⁻¹ * u₁ * u₂)⁻¹ = x := by
  intro x hx
  have e12 : (u₁ * u₂) * x * (u₁ * u₂)⁻¹ = (c ^ k₁ * c ^ k₂) * x * (c ^ k₁ * c ^ k₂)⁻¹ := by
    calc (u₁ * u₂) * x * (u₁ * u₂)⁻¹ = u₁ * (u₂ * x * u₂⁻¹) * u₁⁻¹ := by group
      _ = u₁ * (c ^ k₂ * x * (c ^ k₂)⁻¹) * u₁⁻¹ := by rw [h₂ x hx]
      _ = c ^ k₁ * (c ^ k₂ * x * (c ^ k₂)⁻¹) * (c ^ k₁)⁻¹ := h₁ _ (hn k₂ x hx)
      _ = (c ^ k₁ * c ^ k₂) * x * (c ^ k₁ * c ^ k₂)⁻¹ := by group
  have e21 : (u₂ * u₁) * x * (u₂ * u₁)⁻¹ = (c ^ k₂ * c ^ k₁) * x * (c ^ k₂ * c ^ k₁)⁻¹ := by
    calc (u₂ * u₁) * x * (u₂ * u₁)⁻¹ = u₂ * (u₁ * x * u₁⁻¹) * u₂⁻¹ := by group
      _ = u₂ * (c ^ k₁ * x * (c ^ k₁)⁻¹) * u₂⁻¹ := by rw [h₁ x hx]
      _ = c ^ k₂ * (c ^ k₁ * x * (c ^ k₁)⁻¹) * (c ^ k₂)⁻¹ := h₂ _ (hn k₁ x hx)
      _ = (c ^ k₂ * c ^ k₁) * x * (c ^ k₂ * c ^ k₁)⁻¹ := by group
  have hcomm : c ^ k₁ * c ^ k₂ = c ^ k₂ * c ^ k₁ := (Commute.pow_pow_self c k₁ k₂).eq
  have e : (u₁ * u₂) * x * (u₁ * u₂)⁻¹ = (u₂ * u₁) * x * (u₂ * u₁)⁻¹ := by
    rw [e12, e21, hcomm]
  calc (u₁⁻¹ * u₂⁻¹ * u₁ * u₂) * x * (u₁⁻¹ * u₂⁻¹ * u₁ * u₂)⁻¹
      = (u₂ * u₁)⁻¹ * ((u₁ * u₂) * x * (u₁ * u₂)⁻¹) * (u₂ * u₁) := by group
    _ = (u₂ * u₁)⁻¹ * ((u₂ * u₁) * x * (u₂ * u₁)⁻¹) * (u₂ * u₁) := by rw [e]
    _ = x := by group

end Generic

section Pi

variable {G : Type} [Group G] {H : Subgroup G}

theorem piQ_conj_eq_iff {a x y : G} (ha : a ∈ H) (hx : x ∈ H) (hy : y ∈ H) :
    a * x * a⁻¹ * y⁻¹ ∈ pCoreOf 2 H ↔
      piQ H ⟨a, ha⟩ * piQ H ⟨x, hx⟩ * (piQ H ⟨a, ha⟩)⁻¹ = piQ H ⟨y, hy⟩ := by
  have hm : a * x * a⁻¹ * y⁻¹ ∈ H :=
    H.mul_mem (H.mul_mem (H.mul_mem ha hx) (H.inv_mem ha)) (H.inv_mem hy)
  have e : (⟨a * x * a⁻¹ * y⁻¹, hm⟩ : ↥H) =
      ⟨a, ha⟩ * ⟨x, hx⟩ * ⟨a, ha⟩⁻¹ * ⟨y, hy⟩⁻¹ := rfl
  rw [← piQ_eq_one_iff H ⟨_, hm⟩, e, map_mul, map_mul, map_mul, map_inv, map_inv]
  exact ⟨mul_inv_eq_one.mp, fun h1 => by rw [h1]; exact mul_inv_cancel _⟩

end Pi

section Aut

variable {G : Type} [Group G] [Finite G] {T M H PQ : Subgroup G} {p : ℕ}
  {H₀ H₁ H₂ : Subgroup G} {t : G}

theorem inf_pq_le_pCoreOf (S : Setting146 G T M) (hred : IsRedCE T M H PQ p) :
    T ⊓ PQ ≤ pCoreOf 2 H := by
  rintro z ⟨hzT, hzPQ⟩
  obtain ⟨m, hm⟩ := S.hyp.sylow.1 ⟨z, hzT⟩
  have hm' : z ^ 2 ^ m = 1 := by simpa using congrArg Subtype.val hm
  obtain ⟨j, hj⟩ := hred.pSec z hzPQ
  have hcop : Nat.Coprime (2 ^ m) (p ^ j) :=
    Nat.Coprime.pow m j ((Nat.coprime_primes Nat.prime_two hred.prime).mpr (Ne.symm hred.odd))
  have := mem_sup_of_pow_mem hcop (A := pCoreOf 2 H) (B := pCoreOf 2 H)
    (by rw [hm']; exact (pCoreOf 2 H).one_mem) hj
  simpa using this

theorem p_dvd_card_oTwoUpper (S : Setting146 G T M) (hred : IsRedCE T M H PQ p)
    (h : IsDecP T M H p H₀ H₁ H₂ t) : p ∣ Nat.card (oTwoUpper H) := by
  rw [card_eq_card_pCoreOf_mul_relIndex, relIndex_pCoreOf_oTwoUpper_of_isDecP S hred h]
  exact Dvd.dvd.mul_left (dvd_pow_self p two_ne_zero) _

theorem exists_star_rep (S : Setting146 G T M) (hred : IsRedCE T M H PQ p)
    (h : IsDecP T M H p H₀ H₁ H₂ t) {P : Subgroup G} (hP : IsSylowIn p P (oTwoUpper H)) {y : G}
    (hy : y ∈ PQ) :
    ∃ (x : G) (hx : x ∈ P),
      piQ H ⟨y, hred.le hy⟩ = piQ H ⟨x, (hP.le.trans (oTwoUpper_le H)) hx⟩ := by
  have : Fact p.Prime := ⟨hred.prime⟩
  have hX := isXi_oTwoUpper S hred h
  have hpX := p_dvd_card_oTwoUpper S hred h
  have hKP : pCoreOf 2 (oTwoUpper H) ⊔ P = oTwoUpper H := hX.pCoreOf_sup_eq hred.odd hpX hP
  have hpK : pCoreOf 2 (oTwoUpper H) = oTwoUpper H ⊓ pCoreOf 2 H :=
    S152Y.pCoreOf_eq_inf_of_normalizer (oTwoUpper_le H) (le_normalizer_oTwoUpper H)
  obtain ⟨q, hq, k, hk, rfl⟩ := exists_mul_of_mem_pq hred hy
  have hk' : k ∈ pCoreOf 2 (oTwoUpper H) ⊔ P := by
    rw [hKP]
    exact hk
  obtain ⟨q', hq', a, ha, rfl⟩ :=
    (Ch1Sec3.mem_sup_iff_of_le_normalizer hP.le_normalizer_pCoreOf_two).mp hk'
  refine ⟨a, ha, ?_⟩
  have hq'Q : q' ∈ pCoreOf 2 H := (hpK ▸ hq' : q' ∈ oTwoUpper H ⊓ pCoreOf 2 H).2
  have hqH : q ∈ H := pCoreOf_le 2 H hq
  have hq'H : q' ∈ H := pCoreOf_le 2 H hq'Q
  have haH : a ∈ H := (hP.le.trans (oTwoUpper_le H)) ha
  have e : (⟨q * (q' * a), H.mul_mem hqH (H.mul_mem hq'H haH)⟩ : ↥H) =
      ⟨q, hqH⟩ * (⟨q', hq'H⟩ * ⟨a, haH⟩) := rfl
  rw [e, map_mul, map_mul, (piQ_eq_one_iff H ⟨q, hqH⟩).mpr hq,
    (piQ_eq_one_iff H ⟨q', hq'H⟩).mpr hq'Q, one_mul, one_mul]

theorem act_mod_pCoreOf (S : Setting146 G T M) (hred : IsRedCE T M H PQ p)
    (h : IsDecP T M H p H₀ H₁ H₂ t) {P : Subgroup G} (hP : IsSylowIn p P (oTwoUpper H)) {c : G}
    (hcyc : ∀ s ∈ T ⊓ Subgroup.normalizer (P : Set G),
      ∃ k : ℕ, ∀ x ∈ P, s * x * s⁻¹ = c ^ k * x * (c ^ k)⁻¹) {u : G} (hu : u ∈ T) :
    ∃ k : ℕ, ∀ x ∈ P, u * x * u⁻¹ * (c ^ k * x * (c ^ k)⁻¹)⁻¹ ∈ pCoreOf 2 H := by
  have : Fact p.Prime := ⟨hred.prime⟩
  have hX := isXi_oTwoUpper S hred h
  have hpX := p_dvd_card_oTwoUpper S hred h
  have hTeq := hX.eq_pCoreOf_sup_normalizer S.hyp.sylow hred.odd hpX hP
  have hKH : oTwoUpper H ≤ H := oTwoUpper_le H
  have hTH : T ≤ H := hred.isHTM.1.1
  have hpK : pCoreOf 2 (oTwoUpper H) = oTwoUpper H ⊓ pCoreOf 2 H :=
    S152Y.pCoreOf_eq_inf_of_normalizer hKH (le_normalizer_oTwoUpper H)
  have hTN : T ⊓ Subgroup.normalizer (P : Set G) ≤
      Subgroup.normalizer (pCoreOf 2 (oTwoUpper H) : Set G) :=
    inf_le_left.trans (hX.2.1.trans (normalizer_le_normalizer_pCoreOf 2 (oTwoUpper H)))
  have hu' : u ∈ pCoreOf 2 (oTwoUpper H) ⊔ (T ⊓ Subgroup.normalizer (P : Set G)) := by
    rw [← hTeq]
    exact hu
  obtain ⟨q, hq, s, hs, rfl⟩ := (Ch1Sec3.mem_sup_iff_of_le_normalizer hTN).mp hu'
  obtain ⟨k, hk⟩ := hcyc s hs
  refine ⟨k, fun x hx => ?_⟩
  have hqQ : q ∈ pCoreOf 2 H := (hpK ▸ hq : q ∈ oTwoUpper H ⊓ pCoreOf 2 H).2
  have hxH : x ∈ H := hKH (hP.le hx)
  have hsH : s ∈ H := hTH hs.1
  have hyH : s * x * s⁻¹ ∈ H := H.mul_mem (H.mul_mem hsH hxH) (H.inv_mem hsH)
  rw [← hk x hx]
  have e : q * s * x * (q * s)⁻¹ * (s * x * s⁻¹)⁻¹ =
      q * ((s * x * s⁻¹) * q⁻¹ * (s * x * s⁻¹)⁻¹) := by group
  rw [e]
  exact (pCoreOf 2 H).mul_mem hqQ
    ((Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 H hyH) q⁻¹).mp
      ((pCoreOf 2 H).inv_mem hqQ))

theorem commutator_mem_pCoreOf (S : Setting146 G T M) (hred : IsRedCE T M H PQ p)
    (h : IsDecP T M H p H₀ H₁ H₂ t) {P : Subgroup G} (hP : IsSylowIn p P (oTwoUpper H)) {c : G}
    (hcN : c ∈ T ⊓ Subgroup.normalizer (P : Set G))
    (hcyc : ∀ s ∈ T ⊓ Subgroup.normalizer (P : Set G),
      ∃ k : ℕ, ∀ x ∈ P, s * x * s⁻¹ = c ^ k * x * (c ^ k)⁻¹) {u₁ u₂ : G} (hu₁ : u₁ ∈ T)
    (hu₂ : u₂ ∈ T) : u₁⁻¹ * u₂⁻¹ * u₁ * u₂ ∈ pCoreOf 2 H := by
  have hTH : T ≤ H := hred.isHTM.1.1
  have hPH : P ≤ H := hP.le.trans (oTwoUpper_le H)
  have hcH : c ∈ H := hTH hcN.1
  have hu₁H : u₁ ∈ H := hTH hu₁
  have hu₂H : u₂ ∈ H := hTH hu₂
  obtain ⟨k₁, hk₁⟩ := act_mod_pCoreOf S hred h hP hcyc hu₁
  obtain ⟨k₂, hk₂⟩ := act_mod_pCoreOf S hred h hP hcyc hu₂
  set Pb : Subgroup (↥H ⧸ (pCoreOf 2 H).subgroupOf H) := (P.subgroupOf H).map (piQ H) with hPb
  have hPbmem : ∀ z ∈ Pb, ∃ (x : G) (hx : x ∈ P), z = piQ H ⟨x, hPH hx⟩ := by
    rintro z ⟨y, hy, rfl⟩
    exact ⟨y, Subgroup.mem_subgroupOf.mp hy, rfl⟩
  have hconjc : ∀ (k : ℕ) (x : G), x ∈ P → c ^ k * x * (c ^ k)⁻¹ ∈ P := fun k x hx =>
    (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer (P : Set G)).pow_mem hcN.2 k) x).mp hx
  have hyH : ∀ (k : ℕ) (x : G), x ∈ P → c ^ k * x * (c ^ k)⁻¹ ∈ H := fun k x hx =>
    hPH (hconjc k x hx)
  have hcpow : ∀ (k : ℕ) (x : G) (hx : x ∈ P),
      piQ H ⟨c ^ k * x * (c ^ k)⁻¹, hyH k x hx⟩ =
        piQ H ⟨c, hcH⟩ ^ k * piQ H ⟨x, hPH hx⟩ * (piQ H ⟨c, hcH⟩ ^ k)⁻¹ := by
    intro k x hx
    have e : (⟨c ^ k * x * (c ^ k)⁻¹, hyH k x hx⟩ : ↥H) =
        ⟨c, hcH⟩ ^ k * ⟨x, hPH hx⟩ * (⟨c, hcH⟩ ^ k)⁻¹ := rfl
    rw [e, map_mul, map_mul, map_inv, map_pow]
  have hn : ∀ (k : ℕ), ∀ z ∈ Pb, piQ H ⟨c, hcH⟩ ^ k * z * (piQ H ⟨c, hcH⟩ ^ k)⁻¹ ∈ Pb := by
    intro k z hz
    obtain ⟨x, hx, rfl⟩ := hPbmem z hz
    rw [← hcpow k x hx]
    exact ⟨⟨c ^ k * x * (c ^ k)⁻¹, hyH k x hx⟩,
      Subgroup.mem_subgroupOf.mpr (hconjc k x hx), rfl⟩
  have hact : ∀ (u : G) (hu : u ∈ H) (k : ℕ),
      (∀ x ∈ P, u * x * u⁻¹ * (c ^ k * x * (c ^ k)⁻¹)⁻¹ ∈ pCoreOf 2 H) →
        ∀ z ∈ Pb, piQ H ⟨u, hu⟩ * z * (piQ H ⟨u, hu⟩)⁻¹ =
          piQ H ⟨c, hcH⟩ ^ k * z * (piQ H ⟨c, hcH⟩ ^ k)⁻¹ := by
    intro u hu k hk z hz
    obtain ⟨x, hx, rfl⟩ := hPbmem z hz
    rw [← hcpow k x hx]
    exact (piQ_conj_eq_iff hu (hPH hx) (hyH k x hx)).mp (hk x hx)
  have hcent := commutator_centralizes hn (hact u₁ hu₁H k₁ hk₁) (hact u₂ hu₂H k₂ hk₂)
  have hωT : u₁⁻¹ * u₂⁻¹ * u₁ * u₂ ∈ T :=
    T.mul_mem (T.mul_mem (T.mul_mem (T.inv_mem hu₁) (T.inv_mem hu₂)) hu₁) hu₂
  have hωH : u₁⁻¹ * u₂⁻¹ * u₁ * u₂ ∈ H := hTH hωT
  have hωbar : piQ H ⟨u₁⁻¹ * u₂⁻¹ * u₁ * u₂, hωH⟩ =
      (piQ H ⟨u₁, hu₁H⟩)⁻¹ * (piQ H ⟨u₂, hu₂H⟩)⁻¹ * piQ H ⟨u₁, hu₁H⟩ * piQ H ⟨u₂, hu₂H⟩ := by
    have e : (⟨u₁⁻¹ * u₂⁻¹ * u₁ * u₂, hωH⟩ : ↥H) =
        ⟨u₁, hu₁H⟩⁻¹ * ⟨u₂, hu₂H⟩⁻¹ * ⟨u₁, hu₁H⟩ * ⟨u₂, hu₂H⟩ := rfl
    rw [e, map_mul, map_mul, map_mul, map_inv, map_inv]
  have hωPQ : ∀ y ∈ PQ, (u₁⁻¹ * u₂⁻¹ * u₁ * u₂) * y * (u₁⁻¹ * u₂⁻¹ * u₁ * u₂)⁻¹ * y⁻¹ ∈
      pCoreOf 2 H := by
    intro y hy
    obtain ⟨x, hx, hxy⟩ := exists_star_rep S hred h hP hy
    rw [cent_iff hωH (hred.le hy), hxy, hωbar]
    exact hcent _ ⟨⟨x, hPH hx⟩, Subgroup.mem_subgroupOf.mpr hx, rfl⟩
  have hωin : u₁⁻¹ * u₂⁻¹ * u₁ * u₂ ∈ PQ :=
    hred.centralizer_le_pq S (pq_section S hred h).1 hωH hωPQ
  exact inf_pq_le_pCoreOf S hred ⟨hωT, hωin⟩

theorem not_autCyclic_aux (S : Setting146 G T M) (hred : IsRedCE T M H PQ p)
    (h : IsDecP T M H p H₀ H₁ H₂ t) {P : Subgroup G} (hP : IsSylowIn p P (oTwoUpper H)) :
    ¬ EmptyFaithfulMultiple.AutCyclic T P := by
  rintro ⟨c, hc, hcyc⟩
  obtain ⟨-, -, hidx⟩ := h.isSylowTwoOf_inf_H₁ S hred
  obtain ⟨σ, hσ, hσQ⟩ := exists_mem_not_mem_of_relIndex_two hidx
  have hσT : σ ∈ T := hσ.1.1
  have hσH₁ : σ ∈ H₁ := hσ.2
  have hω := commutator_mem_pCoreOf S hred h hP hc hcyc (T.inv_mem h.t_mem) hσT
  have hm : t * σ⁻¹ * t⁻¹ ∈ H₂ := by
    rw [h.conj]
    exact mul_mem_conjSub (H₁.inv_mem hσH₁)
  have hσH₂ : σ ∈ H₂ := by
    have e : σ = (t * σ⁻¹ * t⁻¹)⁻¹ * ((t⁻¹)⁻¹ * σ⁻¹ * t⁻¹ * σ) := by group
    rw [e]
    exact H₂.mul_mem (H₂.inv_mem hm) (h.Q₂ hω)
  exact hσQ (by rw [← h.inf]; exact ⟨hσH₁, hσH₂⟩)

set_option linter.unusedVariables false in
theorem not_autCyclic_of_isDecP (S : Setting146 G T M) (hred : IsRedCE T M H PQ p)
    (h : IsDecP T M H p H₀ H₁ H₂ t) {P : Subgroup G} (hP : IsSylowIn p P (oTwoUpper H))
    (hPc : Nat.card P = p ^ 2) : ¬ EmptyFaithfulMultiple.AutCyclic T P :=
  not_autCyclic_aux S hred h hP

end Aut

end CFSG.Quasithin.S146zX
