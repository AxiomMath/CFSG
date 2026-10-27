module

public import CFSG.RankThree.Chevalley.G2SplitPrimeToralCentralizers
public import CFSG.RankThree.Chevalley.EvenPinnedRootSL2

public noncomputable section

namespace CFSG.RankThree.Chevalley

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.ComponentClassification.UnbalancedCatalog
open scoped Pointwise commutatorElement

namespace EvenG2

variable {K : Type} [Field K]

theorem mem_torusGroup_of_conj_rootSubgroups_of_charTwo [CharP K 2] {τ : Tag}
    {α : Fin τ.rank → ℤ} (hα : IsRoot τ α) {u : ModGL τ K}
    (hu : u ∈ rootSubgroup τ K α ⊔ rootSubgroup τ K (-α))
    (hup : ∀ x ∈ rootSubgroup τ K α, u * x * u⁻¹ ∈ rootSubgroup τ K α)
    (hdown : ∀ x ∈ rootSubgroup τ K (-α), u * x * u⁻¹ ∈ rootSubgroup τ K (-α)) :
    u ∈ torusGroup τ K := by
  obtain ⟨hinj, hrange, -, hUV, hNW, -⟩ := even_Chevalley_pinned_root_SL2_maps τ K hα
  rw [← hrange] at hu
  obtain ⟨A, rfl⟩ := hu
  obtain ⟨c, hc⟩ := mem_rootSubgroup.1 (hup _ (mem_rootSubgroup.2 ⟨1, rfl⟩))
  obtain ⟨c', hc'⟩ := mem_rootSubgroup.1 (hdown _ (mem_rootSubgroup.2 ⟨1, rfl⟩))
  have hAu : A * uSL 1 * A⁻¹ = uSL c := hinj (by
    rw [map_mul, map_mul, map_inv, (hUV 1).1, (hUV c).1, hc])
  have hAv : A * vSL 1 * A⁻¹ = vSL c' := hinj (by
    rw [map_mul, map_mul, map_inv, (hUV 1).2, (hUV c').2, hc'])
  obtain ⟨t, rfl⟩ := exists_eq_HSL_of_conj hAu hAv
  exact (hNW t).2.1

theorem even_card_of_charTwo [Finite K] [CharP K 2] : Even (Nat.card K) := by
  have : Fintype K := Fintype.ofFinite K
  rw [Nat.card_eq_fintype_card]
  exact Nat.even_iff.2 (FiniteField.even_card_iff_char_two.1 (ringChar.eq K 2))

theorem six_le_card_of_dvd [Finite K] {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hpq : p ∣ Nat.card K - 1) : 6 ≤ Nat.card K := by
  have h1 : 1 < Nat.card K := Finite.one_lt_card
  have := Nat.le_of_dvd (by omega) hpq
  have := five_le_of_prime_of_three_lt hp hp3
  omega

theorem toral_centralizer_cases_G2_of_charTwo (K : Type) [Field K] [Finite K] [CharP K 2]
    {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) (hpq : p ∣ Nat.card K - 1)
    (a : Fin Tag.G2.rank → Kˣ) (ha : orderOf (rootDiagUnit .G2 a) = p) :
    (rootCharKernel a = ∅ ∧ toralCentralizer .G2 K a = torusGroup .G2 K) ∨
    (∃ α : Fin Tag.G2.rank → ℤ, IsRoot .G2 α ∧ rootCharKernel a = {α, -α} ∧
      toralCentralizer .G2 K a =
        torusGroup .G2 K ⊔ (rootSubgroup .G2 K α ⊔ rootSubgroup .G2 K (-α)) ∧
      (toralCentralizer .G2 K a : Set (ModGL .G2 K)) =
        (torusGroup .G2 K : Set (ModGL .G2 K)) *
          ((rootSubgroup .G2 K α ⊔ rootSubgroup .G2 K (-α) : Subgroup (ModGL .G2 K)) :
            Set (ModGL .G2 K)) ∧
      ⁅toralCentralizer .G2 K a, toralCentralizer .G2 K a⁆ =
        rootSubgroup .G2 K α ⊔ rootSubgroup .G2 K (-α) ∧
      toralCentralizer .G2 K a ⊓ Subgroup.centralizer
          ((rootSubgroup .G2 K α ⊔ rootSubgroup .G2 K (-α) : Subgroup (ModGL .G2 K)) :
            Set (ModGL .G2 K)) =
        (Subgroup.center (toralCentralizer .G2 K a)).map (toralCentralizer .G2 K a).subtype ∧
      (Subgroup.center (toralCentralizer .G2 K a)).map (toralCentralizer .G2 K a).subtype ≤
        torusGroup .G2 K) := by
  classical
  have hq6 := six_le_card_of_dvd hp hp3 hpq
  have hTcomm := (triangular_borel_structure.{0, 0} .G2 K).1
  have hoa : orderOf a = p := by rw [← orderOf_rootDiagUnit (K := K), ha]
  have hap : a ^ p = 1 := hoa ▸ pow_orderOf_eq_one a
  have ha1 : a ≠ 1 := fun h => by
    rw [h, orderOf_one] at hoa
    exact hp.one_lt.ne hoa
  have hX := toralCentralizer_eq_toralRootGroup_of_le (K := K)
    (rootCharStabilizer_le_kernelReflectionGroup_G2 hp hp3 hap ha1)
  set X := toralCentralizer .G2 K a with hXdef
  rcases rootCharKernel_G2_cases hp hp3 hap ha1 with hker | ⟨α, hα, hker⟩
  ·
    refine Or.inl ⟨hker, ?_⟩
    rw [hX, toralRootGroup, hker]
    simp [rootSpan]
  ·
    set Q : Subgroup (ModGL .G2 K) := rootSubgroup .G2 K α ⊔ rootSubgroup .G2 K (-α) with hQdef
    have hXQ : X = torusGroup .G2 K ⊔ Q := by
      rw [hX, toralRootGroup, hker, rootSpan, iSup_insert, iSup_singleton]
    have hXset : (X : Set (ModGL .G2 K)) = (torusGroup .G2 K : Set (ModGL .G2 K)) * Q := by
      rw [hXQ]
      exact Subgroup.coe_mul_of_left_le_normalizer_right _ _ (torusGroup_le_normalizer_rootPair hα)
    have hQX : Q ≤ X := hXQ ▸ le_sup_right
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hfin⟩ := even_Chevalley_pinned_root_SL2_maps .G2 K hα
    have hperf : ⁅Q, Q⁆ = Q :=
      Subgroup.isPerfect_iff.1 (hfin inferInstance (by omega)).2.1
    have hcomm : ⁅X, X⁆ = Q := by
      refine le_antisymm ?_ (hperf ▸ Subgroup.commutator_mono hQX hQX)
      rw [Subgroup.commutator_le]
      intro x hx y hy
      rw [← SetLike.mem_coe, hXset] at hx hy
      obtain ⟨h, hh, q, hq, rfl⟩ := hx
      obtain ⟨h', hh', q', hq', rfl⟩ := hy
      have e1 : ⁅h * q, h' * q'⁆ = (h * h') * (h'⁻¹ * q * h' * (q' * q⁻¹)) * (h' * h)⁻¹ *
          (h' * q'⁻¹ * h'⁻¹) := by
        rw [commutatorElement_def]
        group
      rw [e1, ← hTcomm h hh h' hh']
      refine mul_mem (conj_mem_rootPair_of_mem_torusGroup (mul_mem hh hh') hα (mul_mem ?_
        (mul_mem hq' (inv_mem hq)))) (conj_mem_rootPair_of_mem_torusGroup hh' hα (inv_mem hq'))
      have := conj_mem_rootPair_of_mem_torusGroup (inv_mem hh') hα hq
      rwa [inv_inv] at this
    have hCT : X ⊓ Subgroup.centralizer (Q : Set (ModGL .G2 K)) ≤ torusGroup .G2 K := by
      intro z hz
      obtain ⟨hzX, hzC⟩ := Subgroup.mem_inf.1 hz
      have hzX' : z ∈ (X : Set (ModGL .G2 K)) := hzX
      rw [hXset] at hzX'
      obtain ⟨h, hh, u, hu, rfl⟩ := hzX'
      have hcz : ∀ x ∈ Q, (h * u) * x * (h * u)⁻¹ = x := fun x hx => by
        rw [← Subgroup.mem_centralizer_iff.1 hzC x hx, mul_inv_cancel_right]
      have hconj : ∀ x ∈ Q, u * x * u⁻¹ = h⁻¹ * x * h⁻¹⁻¹ := fun x hx => by
        have e2 : u * x * u⁻¹ = h⁻¹ * ((h * u) * x * (h * u)⁻¹) * h⁻¹⁻¹ := by group
        rw [e2, hcz x hx]
      have hup : ∀ x ∈ rootSubgroup .G2 K α, u * x * u⁻¹ ∈ rootSubgroup .G2 K α := fun x hx => by
        rw [hconj x (Subgroup.mem_sup_left hx)]
        exact conj_mem_rootSubgroup_of_mem_torusGroup (inv_mem hh) hα hx
      have hdown : ∀ x ∈ rootSubgroup .G2 K (-α), u * x * u⁻¹ ∈ rootSubgroup .G2 K (-α) :=
        fun x hx => by
          rw [hconj x (Subgroup.mem_sup_right hx)]
          exact conj_mem_rootSubgroup_of_mem_torusGroup (inv_mem hh) (IsRoot.neg hα) hx
      exact mul_mem hh (mem_torusGroup_of_conj_rootSubgroups_of_charTwo hα hu hup hdown)
    have hZ : X ⊓ Subgroup.centralizer (Q : Set (ModGL .G2 K)) =
        (Subgroup.center X).map X.subtype := by
      refine le_antisymm ?_ ?_
      · intro z hz
        obtain ⟨hzX, hzC⟩ := Subgroup.mem_inf.1 hz
        have hzT := hCT hz
        have hle : X ≤ Subgroup.centralizer {z} := by
          rw [hXQ]
          refine sup_le (fun t ht => ?_) (fun x hx => ?_)
          · rw [Subgroup.mem_centralizer_singleton_iff]
            exact (hTcomm z hzT t ht).symm
          · rw [Subgroup.mem_centralizer_singleton_iff]
            exact Subgroup.mem_centralizer_iff.1 hzC x hx
        refine ⟨⟨z, hzX⟩, Subgroup.mem_center_iff.2 fun g => Subtype.ext ?_, rfl⟩
        exact Subgroup.mem_centralizer_singleton_iff.1 (hle g.2)
      · rintro _ ⟨z, hz, rfl⟩
        refine ⟨z.2, Subgroup.mem_centralizer_iff.2 fun x hx => ?_⟩
        exact congrArg Subtype.val (Subgroup.mem_center_iff.1 hz ⟨x, hQX hx⟩)
    exact Or.inr ⟨α, hα, hker, hXQ, hXset, hcomm, hZ, hZ ▸ hCT⟩

end EvenG2

end CFSG.RankThree.Chevalley
