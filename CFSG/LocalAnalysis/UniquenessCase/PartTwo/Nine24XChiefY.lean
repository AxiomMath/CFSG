module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Nine24XNonAb
public import CFSG.LocalAnalysis.UniquenessCase.UCFront09R93d
public import CFSG.GroupTheory.ABGLocalTools.PStabilityChief

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open Subgroup
open scoped commutatorElement
open CFSG.LocalAnalysis.UniquenessCase.UC22.F09

variable {G : Type} [Group G] [Finite G]

theorem exists_chief_factor_not_le_Y (hSch : CFSG.AGLEmbedding.KFactCatalogSchreier)
    {X Y Z O M : Subgroup G} (hKG : CFSG.Open.IsKGroup ↥(O ⊔ Y)) (hZX : Z ≤ X) (hXY : X ≤ Y)
    (hYX : Y ≤ normalizer (X : Set G)) (hZ3 : Nat.card Z = 3) (hYM : Y ≤ M)
    (hCZ : centralizer (Z : Set G) ≤ M) (hXperf : ⁅X, X⁆ = X)
    (hXgen : ∀ B : Subgroup G, B ≤ X → X ≤ normalizer (B : Set G) → Z ≤ B → B = X)
    (hYO : Y ≤ normalizer (O : Set G)) (hO3 : ¬ 3 ∣ Nat.card O) (hOM : ¬ O ≤ M) :
    ∃ (r : ℕ) (U W : Subgroup G), r.Prime ∧ r ≠ 3 ∧
      CFSG.ABGLocalTools.IsChiefFactorUnder r Y U W ∧ U ≤ O ∧ W ≤ M ∧
      U ⊓ M ≤ W ∧ ∀ u ∈ U, (∀ x ∈ Z, x * u * x⁻¹ * u⁻¹ ∈ W) → u ∈ W := by
  classical
  obtain ⟨U, hUle, hUY, hUnotM, hUmin⟩ := exists_minimal_invariant_not_le hYO hOM
  have hUbot : U ≠ ⊥ := fun h => hUnotM (h ▸ bot_le)
  obtain ⟨W, hWle, hWU, hWY, hWne, hWmax⟩ := exists_maximal_invariant_normal (K := Y) hUbot
  have hWM : W ≤ M := by
    by_contra hWnotM
    exact hWne (Subgroup.eq_of_le_of_card_ge hWle (hUmin W (hWle.trans hUle) hWY hWnotM))
  have hU3 : ¬ 3 ∣ Nat.card U := fun h => hO3 (h.trans (Subgroup.card_dvd_of_le hUle))
  have hKGU : CFSG.Open.IsKGroup ↥(U ⊔ X) :=
    CFSG.Open.IsKGroup.of_le hKG (sup_le_sup hUle hXY)
  have hcommU : ⁅U, U⁆ ≤ W := by
    by_contra hcon
    exact hUnotM ((le_inf_sup_of_nonabelian_chief hSch hKGU hZX hZ3 hXY hYX hYM hCZ hXperf
      hXgen hU3 hUY hWle hWU hWY hWmax hcon).trans (sup_le inf_le_right hWM))
  have hNY : ∀ B : Subgroup G, W ≤ B → B ≤ U → U ≤ normalizer (B : Set G) := by
    intro B hWB hBU
    rw [Subgroup.le_normalizer_iff]
    intro u hu x hx
    have hc : ⁅u, x⁆ ∈ W := (Subgroup.commutator_le.mp hcommU) u hu x (hBU hx)
    have hux : u * x * u⁻¹ = ⁅u, x⁆ * x := by
      rw [commutatorElement_def]
      group
    rw [hux]
    exact B.mul_mem (hWB hc) hx
  have hYSupW : Y ≤ normalizer (((U ⊓ M) ⊔ W : Subgroup G) : Set G) := fun b hb =>
    Subgroup.inf_normalizer_le_normalizer_sup (U ⊓ M) W (Subgroup.mem_inf.mpr
      ⟨Subgroup.inf_normalizer_le_normalizer_inf (H := U) (K := M) (Subgroup.mem_inf.mpr
        ⟨hUY hb, Subgroup.le_normalizer (hYM hb)⟩), hWY hb⟩)
  have hUMleW : U ⊓ M ≤ W := by
    have hXle : (U ⊓ M) ⊔ W ≤ U := sup_le inf_le_left hWle
    have hXne : (U ⊓ M) ⊔ W ≠ U := by
      intro h
      apply hUnotM
      rw [← h]
      exact sup_le inf_le_right hWM
    have hXeq : (U ⊓ M) ⊔ W = W :=
      hWmax ((U ⊓ M) ⊔ W) le_sup_right hXle (hNY _ le_sup_right hXle) hYSupW hXne
    rw [← hXeq]
    exact le_sup_left
  haveI : (W.subgroupOf U).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hWle).mpr hWU
  have hWsub_ne_top : W.subgroupOf U ≠ ⊤ := by
    intro htop
    apply hWne
    rw [← Subgroup.map_subgroupOf_eq_of_le hWle, htop, Subgroup.map_top, Subgroup.range_subtype]
  have hqne : Nat.card (↥U ⧸ W.subgroupOf U) ≠ 1 := by
    intro h
    apply hWsub_ne_top
    have hcm := Subgroup.card_mul_index (W.subgroupOf U)
    rw [Subgroup.index_eq_card, h, mul_one] at hcm
    exact Subgroup.eq_top_of_card_eq (W.subgroupOf U) hcm
  obtain ⟨r, hprime, hdvd⟩ := Nat.exists_prime_and_dvd hqne
  have hr3 : r ≠ 3 := by
    rintro rfl
    rw [← Subgroup.index_eq_card] at hdvd
    exact hU3 (hdvd.trans (Subgroup.index_dvd_card (W.subgroupOf U)))
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
      exact hcommU (Subgroup.commutator_mem_commutator
        (Subgroup.inv_mem U b'.2) (Subgroup.inv_mem U a'.2))
    have hcomm : (a' * b')⁻¹ * (b' * a') = ⁅b'⁻¹, a'⁻¹⁆ := by
      rw [commutatorElement_def]
      group
    rw [hcomm]
    exact hmem
  let T : Subgroup (↥U ⧸ W.subgroupOf U) :=
    { carrier := {q | q ^ r = 1},
      one_mem' := by simp,
      mul_mem' := by
        intro a b ha hb
        have hc : Commute a b := isMulCommutative_iff.mp hQcomm a b
        show (a * b) ^ r = 1
        rw [hc.mul_pow, ha, hb, mul_one],
      inv_mem' := by
        intro a ha
        show a⁻¹ ^ r = 1
        rw [inv_pow, ha, inv_one] }
  let XU : Subgroup ↥U := T.comap (QuotientGroup.mk' (W.subgroupOf U))
  let Xc : Subgroup G := XU.map U.subtype
  have hWXc : W ≤ Xc := by
    intro w hw
    refine Subgroup.mem_map.mpr ⟨⟨w, hWle hw⟩, Subgroup.mem_comap.mpr ?_, rfl⟩
    rw [show (QuotientGroup.mk' (W.subgroupOf U)) ⟨w, hWle hw⟩ = 1 from
      (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr hw)]
    exact T.one_mem
  have hXcU : Xc ≤ U := Subgroup.map_subtype_le XU
  have hYc : Y ≤ normalizer (Xc : Set G) := by
    rw [Subgroup.le_normalizer_iff]
    intro b hb x hx
    obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hx
    have hupow : (u : G) ^ r ∈ W := by
      have h1 : ((QuotientGroup.mk' (W.subgroupOf U)) u) ^ r = 1 := Subgroup.mem_comap.mp hu
      rw [← map_pow] at h1
      exact Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff _).mp h1)
    have hconjU : b * (u : G) * b⁻¹ ∈ U :=
      (Subgroup.mem_normalizer_iff.mp (hUY hb) (u : G)).mp u.2
    refine Subgroup.mem_map.mpr ⟨⟨b * (u : G) * b⁻¹, hconjU⟩, Subgroup.mem_comap.mpr ?_, rfl⟩
    have hpow : (b * (u : G) * b⁻¹) ^ r ∈ W := by
      have hconj : (b * (u : G) * b⁻¹) ^ r = b * (u : G) ^ r * b⁻¹ := by
        rw [show b * (u : G) * b⁻¹ = (MulAut.conj b) (u : G) from
          (MulAut.conj_apply b (u : G)).symm, ← map_pow, MulAut.conj_apply]
      rw [hconj]
      exact (Subgroup.mem_normalizer_iff.mp (hWY hb) _).mp hupow
    show ((QuotientGroup.mk' (W.subgroupOf U)) ⟨b * (u : G) * b⁻¹, hconjU⟩) ^ r = 1
    rw [← map_pow]
    exact (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr hpow)
  haveI : Fact r.Prime := ⟨hprime⟩
  obtain ⟨q, hqord⟩ := exists_prime_orderOf_dvd_card' r hdvd
  obtain ⟨u₀, hu₀⟩ := QuotientGroup.mk_surjective (s := W.subgroupOf U) q
  have hu₀pow : ((QuotientGroup.mk' (W.subgroupOf U)) u₀) ^ r = 1 := by
    show (u₀ : ↥U ⧸ W.subgroupOf U) ^ r = 1
    rw [hu₀, ← hqord]
    exact pow_orderOf_eq_one q
  have hu₀W : (u₀ : G) ∉ W := by
    intro hmem
    have hq1 : q = 1 := by
      rw [← hu₀, QuotientGroup.eq_one_iff]
      exact Subgroup.mem_subgroupOf.mpr hmem
    rw [hq1, orderOf_one] at hqord
    exact hprime.ne_one hqord.symm
  have hXcne : Xc ≠ W := by
    intro h
    have hu₀X : (u₀ : G) ∈ Xc :=
      Subgroup.mem_map.mpr ⟨u₀, Subgroup.mem_comap.mpr hu₀pow, rfl⟩
    rw [h] at hu₀X
    exact hu₀W hu₀X
  have hXceqU : Xc = U := by
    by_contra hXcU'
    exact hXcne (hWmax Xc hWXc hXcU (hNY Xc hWXc hXcU) hYc hXcU')
  have hexp : ∀ u ∈ U, u ^ r ∈ W := by
    intro u hu
    have huX : u ∈ Xc := by rw [hXceqU]; exact hu
    obtain ⟨u', hu', rfl⟩ := Subgroup.mem_map.mp huX
    have h1 : ((QuotientGroup.mk' (W.subgroupOf U)) u') ^ r = 1 := Subgroup.mem_comap.mp hu'
    rw [← map_pow] at h1
    exact Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff _).mp h1)
  have hchief : CFSG.ABGLocalTools.IsChiefFactorUnder r Y U W := by
    refine ⟨lt_of_le_of_ne hWle hWne, hUY, hWY, ?_, ?_, hexp, ?_⟩
    · intro x hx y hy
      exact (Subgroup.mem_normalizer_iff.mp (hWU hx) y).mp hy
    · intro x hx y hy
      exact (Subgroup.commutator_le.mp hcommU) x hx y hy
    · intro Y' hWY' hY'U hY'Y
      by_cases hY'U' : Y' = U
      · exact Or.inr hY'U'
      · exact Or.inl (hWmax Y' hWY' hY'U (hNY Y' hWY' hY'U) hY'Y hY'U')
  refine ⟨r, U, W, hprime, hr3, hchief, hUle, hWM, hUMleW, ?_⟩
  intro u hu hcommZ
  have hq : ∀ x ∈ Z, u⁻¹ * ((1 : G) * x * (1 : G)⁻¹) * u * ((1 : G) * x * (1 : G)⁻¹)⁻¹ ∈ W := by
    intro x hx
    simpa only [one_mul, mul_one, inv_one, mul_assoc] using
      inv_mul_conj_mem_of_conj_mul_mem (hWU hu) (hcommZ x hx)
  have hW3 : ¬ 3 ∣ Nat.card W := fun h => hU3 (h.trans (Subgroup.card_dvd_of_le hWle))
  have hsup := mem_inf_sup_of_fixed_conj hZ3 (hZX.trans hXY) hYM hCZ hW3 hWle hWY (b := 1)
    Y.one_mem hu hq
  rwa [show (U ⊓ M) ⊔ W = W from le_antisymm (sup_le hUMleW le_rfl) le_sup_right] at hsup

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
