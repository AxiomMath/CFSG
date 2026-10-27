module

public import CFSG.GroupTheory.ABGLocalTools.PStabilityChief
public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoDefs
import CFSG.LocalAnalysis.UniquenessCase.UCFront09R93d
import CFSG.LocalAnalysis.UniquenessCase.UCFront09R93f
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC8R95S1

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.F09

open Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

private theorem r95s_exists_minimal_even {K O M : Subgroup G}
    (hKO : K ≤ normalizer (O : Set G)) (hOeven : 2 ∣ (O ⊓ M).relIndex O) :
    ∃ U : Subgroup G, U ≤ O ∧ K ≤ normalizer (U : Set G) ∧ 2 ∣ (U ⊓ M).relIndex U ∧
      ∀ V : Subgroup G, V ≤ O → K ≤ normalizer (V : Set G) → 2 ∣ (V ⊓ M).relIndex V →
        Nat.card U ≤ Nat.card V := by
  classical
  have hex : ∃ n : ℕ, ∃ U : Subgroup G, U ≤ O ∧
      K ≤ normalizer (U : Set G) ∧ 2 ∣ (U ⊓ M).relIndex U ∧ n = Nat.card U :=
    ⟨Nat.card O, O, le_rfl, hKO, hOeven, rfl⟩
  obtain ⟨U, hUle, hUK, hUeven, hUcard⟩ := Nat.find_spec hex
  refine ⟨U, hUle, hUK, hUeven, fun V hVle hVK hVeven => ?_⟩
  rw [← hUcard]
  exact Nat.find_min' hex ⟨V, hVle, hVK, hVeven, rfl⟩

theorem r95s_exists_min_even (hSch : CFSG.AGLEmbedding.KFactCatalogSchreier)
    {K Z O M : Subgroup G} (hKG : CFSG.Open.IsKGroup ↥(O ⊔ K)) (hZK : Z ≤ K)
    (hZ3 : Nat.card Z = 3) (hKM : K ≤ M) (hCZ : centralizer (Z : Set G) ≤ M)
    (hKperf : ⁅K, K⁆ = K)
    (hKgen : ∀ B : Subgroup G, B ≤ K → K ≤ normalizer (B : Set G) → Z ≤ B → B = K)
    (hKO : K ≤ normalizer (O : Set G)) (hO3 : ¬ 3 ∣ Nat.card O)
    (hOeven : 2 ∣ (O ⊓ M).relIndex O) :
    ∃ U W : Subgroup G, U ≤ O ∧ K ≤ normalizer (U : Set G) ∧ W ≤ U ∧
      U ≤ normalizer (W : Set G) ∧ K ≤ normalizer (W : Set G) ∧ W ≠ U ∧
      (∀ X : Subgroup G, W ≤ X → X ≤ U → U ≤ normalizer (X : Set G) →
        K ≤ normalizer (X : Set G) → X ≠ U → X = W) ∧
      ⁅U, U⁆ ≤ W ∧ 2 ∣ ((U ⊓ M) ⊔ W).relIndex U := by
  classical
  obtain ⟨U, hUle, hUK, hUeven, hUmin⟩ := r95s_exists_minimal_even hKO hOeven
  have hUbot : U ≠ ⊥ := by
    intro h
    have h1 : (U ⊓ M).relIndex U = 1 := by
      rw [h, bot_inf_eq, Subgroup.relIndex_bot_right]
    rw [h1] at hUeven
    exact absurd hUeven (by norm_num)
  obtain ⟨W, hWle, hWU, hWK, hWne, hWmax⟩ := exists_maximal_invariant_normal (K := K) hUbot
  have hWodd : ¬ 2 ∣ (W ⊓ M).relIndex W := by
    intro hWeven
    have hcard : Nat.card U ≤ Nat.card W := hUmin W (hWle.trans hUle) hWK hWeven
    have hlt : Nat.card W < Nat.card U := Subgroup.card_lt_of_lt (lt_of_le_of_ne hWle hWne)
    omega
  have hsplit := r95s_relIndex_split (H := U) (A := U ⊓ M) (B := W) inf_le_left hWle hWU
  have hinf : (U ⊓ M) ⊓ W = W ⊓ M := by
    rw [inf_assoc, inf_comm M W, ← inf_assoc, inf_eq_right.mpr hWle]
  have h2 : 2 ∣ ((U ⊓ M) ⊔ W).relIndex U := by
    have hprod : 2 ∣ ((U ⊓ M) ⊔ W).relIndex U * ((U ⊓ M) ⊓ W).relIndex W := by
      rw [← hsplit]
      exact hUeven
    rw [hinf] at hprod
    rcases (Nat.Prime.dvd_mul Nat.prime_two).1 hprod with h | h
    · exact h
    · exact absurd h hWodd
  have hU3 : ¬ 3 ∣ Nat.card U := fun h => hO3 (h.trans (Subgroup.card_dvd_of_le hUle))
  have hKGU : CFSG.Open.IsKGroup ↥(U ⊔ K) :=
    CFSG.Open.IsKGroup.of_le hKG (sup_le_sup_right hUle K)
  have hcomm : ⁅U, U⁆ ≤ W := by
    by_contra hcon
    have hle : U ≤ (U ⊓ M) ⊔ W :=
      le_inf_sup_of_not_commutator_le hSch hKGU hZK hZ3 hKM hCZ hKperf hKgen hU3
        hUK hWle hWU hWK hWmax hcon
    have heq : (U ⊓ M) ⊔ W = U := le_antisymm (sup_le inf_le_left hWle) hle
    have h1 : ((U ⊓ M) ⊔ W).relIndex U = 1 := by rw [heq, Subgroup.relIndex_self]
    rw [h1] at h2
    exact absurd h2 (by norm_num)
  exact ⟨U, W, hUle, hUK, hWle, hWU, hWK, hWne, hWmax, hcomm, h2⟩

theorem r95s_chief_factor_two {K Z M U W : Subgroup G} (hZK : Z ≤ K) (hZ3 : Nat.card Z = 3)
    (hKM : K ≤ M) (hCZ : centralizer (Z : Set G) ≤ M) (hU3 : ¬ 3 ∣ Nat.card U)
    (hUK : K ≤ normalizer (U : Set G)) (hWle : W ≤ U) (hWU : U ≤ normalizer (W : Set G))
    (hWK : K ≤ normalizer (W : Set G)) (hWne : W ≠ U)
    (hWmax : ∀ X : Subgroup G, W ≤ X → X ≤ U → U ≤ normalizer (X : Set G) →
      K ≤ normalizer (X : Set G) → X ≠ U → X = W)
    (hcomm : ⁅U, U⁆ ≤ W) (heven : 2 ∣ ((U ⊓ M) ⊔ W).relIndex U) :
    CFSG.ABGLocalTools.IsChiefFactorUnder 2 K U W ∧
      ∀ u ∈ U, (∀ x ∈ Z, x * u * x⁻¹ * u⁻¹ ∈ W) → u ∈ W := by
  classical
  have hNX : ∀ X : Subgroup G, W ≤ X → X ≤ U → U ≤ normalizer (X : Set G) := by
    intro X hWX hXU
    rw [Subgroup.le_normalizer_iff]
    intro u hu x hx
    have hc : ⁅u, x⁆ ∈ W := (Subgroup.commutator_le.mp hcomm) u hu x (hXU hx)
    have hux : u * x * u⁻¹ = ⁅u, x⁆ * x := by
      rw [commutatorElement_def]
      group
    rw [hux]
    exact X.mul_mem (hWX hc) hx
  have hKSupW : K ≤ normalizer (((U ⊓ M) ⊔ W : Subgroup G) : Set G) := fun b hb =>
    Subgroup.inf_normalizer_le_normalizer_sup (U ⊓ M) W (Subgroup.mem_inf.mpr
      ⟨Subgroup.inf_normalizer_le_normalizer_inf (H := U) (K := M) (Subgroup.mem_inf.mpr
        ⟨hUK hb, Subgroup.le_normalizer (hKM hb)⟩), hWK hb⟩)
  have hX0ne : (U ⊓ M) ⊔ W ≠ U := by
    intro hX0
    have h1 : ((U ⊓ M) ⊔ W).relIndex U = 1 := by rw [hX0, Subgroup.relIndex_self]
    rw [h1] at heven
    exact absurd heven (by norm_num)
  have hUMleW : U ⊓ M ≤ W := by
    have hXle : (U ⊓ M) ⊔ W ≤ U := sup_le inf_le_left hWle
    have hXeq : (U ⊓ M) ⊔ W = W :=
      hWmax ((U ⊓ M) ⊔ W) le_sup_right hXle (hNX _ le_sup_right hXle) hKSupW hX0ne
    rw [← hXeq]
    exact le_sup_left
  have h2 : 2 ∣ Nat.card (↥U ⧸ W.subgroupOf U) := by
    have hsup : (U ⊓ M) ⊔ W = W := le_antisymm (sup_le hUMleW le_rfl) le_sup_right
    rw [hsup] at heven
    have heven' : 2 ∣ (W.subgroupOf U).index := heven
    rwa [Subgroup.index_eq_card] at heven'
  haveI : (W.subgroupOf U).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hWle).mpr hWU
  have hQcomm : IsMulCommutative (↥U ⧸ W.subgroupOf U) := by
    refine isMulCommutative_iff.mpr fun a b => ?_
    obtain ⟨a', rfl⟩ := QuotientGroup.mk_surjective (s := W.subgroupOf U) a
    obtain ⟨b', rfl⟩ := QuotientGroup.mk_surjective (s := W.subgroupOf U) b
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
    have hmem : ⁅b'⁻¹, a'⁻¹⁆ ∈ W.subgroupOf U := by
      rw [Subgroup.mem_subgroupOf]
      have hval : ((⁅b'⁻¹, a'⁻¹⁆ : ↥U) : G) = ⁅(b' : G)⁻¹, (a' : G)⁻¹⁆ := by
        rw [commutatorElement_def, commutatorElement_def]
        push_cast
        rfl
      rw [hval]
      exact hcomm (Subgroup.commutator_mem_commutator
        (Subgroup.inv_mem U b'.2) (Subgroup.inv_mem U a'.2))
    have hcomm' : (a' * b')⁻¹ * (b' * a') = ⁅b'⁻¹, a'⁻¹⁆ := by
      rw [commutatorElement_def]
      group
    rw [hcomm']
    exact hmem
  let T : Subgroup (↥U ⧸ W.subgroupOf U) :=
    { carrier := {q | q ^ 2 = 1},
      one_mem' := by simp,
      mul_mem' := by
        intro a b ha hb
        have hc : Commute a b := isMulCommutative_iff.mp hQcomm a b
        show (a * b) ^ 2 = 1
        rw [hc.mul_pow, ha, hb, mul_one],
      inv_mem' := by
        intro a ha
        show a⁻¹ ^ 2 = 1
        rw [inv_pow, ha, inv_one] }
  let XU : Subgroup ↥U := T.comap (QuotientGroup.mk' (W.subgroupOf U))
  let X : Subgroup G := XU.map U.subtype
  have hWX : W ≤ X := by
    intro w hw
    refine Subgroup.mem_map.mpr ⟨⟨w, hWle hw⟩, Subgroup.mem_comap.mpr ?_, rfl⟩
    rw [show (QuotientGroup.mk' (W.subgroupOf U)) ⟨w, hWle hw⟩ = 1 from
      (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr hw)]
    exact T.one_mem
  have hXU : X ≤ U := Subgroup.map_subtype_le XU
  have hKX : K ≤ normalizer (X : Set G) := by
    rw [Subgroup.le_normalizer_iff]
    intro b hb x hx
    obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hx
    have hupow : (u : G) ^ 2 ∈ W := by
      have h1 : ((QuotientGroup.mk' (W.subgroupOf U)) u) ^ 2 = 1 := Subgroup.mem_comap.mp hu
      rw [← map_pow] at h1
      exact Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff _).mp h1)
    have hconjU : b * (u : G) * b⁻¹ ∈ U :=
      (Subgroup.mem_normalizer_iff.mp (hUK hb) (u : G)).mp u.2
    refine Subgroup.mem_map.mpr ⟨⟨b * (u : G) * b⁻¹, hconjU⟩, Subgroup.mem_comap.mpr ?_, rfl⟩
    have hpow : (b * (u : G) * b⁻¹) ^ 2 ∈ W := by
      have hconj : (b * (u : G) * b⁻¹) ^ 2 = b * (u : G) ^ 2 * b⁻¹ := by
        rw [show b * (u : G) * b⁻¹ = (MulAut.conj b) (u : G) from
          (MulAut.conj_apply b (u : G)).symm, ← map_pow, MulAut.conj_apply]
      rw [hconj]
      exact (Subgroup.mem_normalizer_iff.mp (hWK hb) _).mp hupow
    show ((QuotientGroup.mk' (W.subgroupOf U)) ⟨b * (u : G) * b⁻¹, hconjU⟩) ^ 2 = 1
    rw [← map_pow]
    exact (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr hpow)
  have hprime : Nat.Prime 2 := Nat.prime_two
  haveI : Fact (Nat.Prime 2) := ⟨hprime⟩
  obtain ⟨q, hqord⟩ := exists_prime_orderOf_dvd_card' 2 h2
  obtain ⟨u₀, hu₀⟩ := QuotientGroup.mk_surjective (s := W.subgroupOf U) q
  have hu₀pow : ((QuotientGroup.mk' (W.subgroupOf U)) u₀) ^ 2 = 1 := by
    show (u₀ : ↥U ⧸ W.subgroupOf U) ^ 2 = 1
    rw [hu₀, ← hqord]
    exact pow_orderOf_eq_one q
  have hu₀W : (u₀ : G) ∉ W := by
    intro hmem
    have hq1 : q = 1 := by
      rw [← hu₀, QuotientGroup.eq_one_iff]
      exact Subgroup.mem_subgroupOf.mpr hmem
    rw [hq1, orderOf_one] at hqord
    exact hprime.ne_one hqord.symm
  have hXne : X ≠ W := by
    intro h
    have hu₀X : (u₀ : G) ∈ X :=
      Subgroup.mem_map.mpr ⟨u₀, Subgroup.mem_comap.mpr hu₀pow, rfl⟩
    rw [h] at hu₀X
    exact hu₀W hu₀X
  have hXeqU : X = U := by
    by_contra hXU'
    exact hXne (hWmax X hWX hXU (hNX X hWX hXU) hKX hXU')
  have hexp : ∀ u ∈ U, u ^ 2 ∈ W := by
    intro u hu
    have huX : u ∈ X := by rw [hXeqU]; exact hu
    obtain ⟨u', hu', rfl⟩ := Subgroup.mem_map.mp huX
    have h1 : ((QuotientGroup.mk' (W.subgroupOf U)) u') ^ 2 = 1 := Subgroup.mem_comap.mp hu'
    rw [← map_pow] at h1
    exact Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff _).mp h1)
  have hchief : CFSG.ABGLocalTools.IsChiefFactorUnder 2 K U W := by
    refine ⟨lt_of_le_of_ne hWle hWne, hUK, hWK, ?_, ?_, hexp, ?_⟩
    · intro x hx y hy
      exact (Subgroup.mem_normalizer_iff.mp (hWU hx) y).mp hy
    · intro x hx y hy
      exact (Subgroup.commutator_le.mp hcomm) x hx y hy
    · intro Y hWY hYU hKY
      by_cases hYU' : Y = U
      · exact Or.inr hYU'
      · exact Or.inl (hWmax Y hWY hYU (hNX Y hWY hYU) hKY hYU')
  refine ⟨hchief, ?_⟩
  intro u hu hcommZ
  have hq : ∀ x ∈ Z, u⁻¹ * ((1 : G) * x * (1 : G)⁻¹) * u *
      ((1 : G) * x * (1 : G)⁻¹)⁻¹ ∈ W := by
    intro x hx
    simpa only [one_mul, mul_one, inv_one, mul_assoc] using
      inv_mul_conj_mem_of_conj_mul_mem (hWU hu) (hcommZ x hx)
  have hW3 : ¬ 3 ∣ Nat.card W := fun h => hU3 (h.trans (Subgroup.card_dvd_of_le hWle))
  have hsup := mem_inf_sup_of_fixed_conj hZ3 hZK hKM hCZ hW3 hWle hWK (b := 1) K.one_mem hu hq
  rwa [show (U ⊓ M) ⊔ W = W from le_antisymm (sup_le hUMleW le_rfl) le_sup_right] at hsup

end CFSG.LocalAnalysis.UniquenessCase.UC22.F09
