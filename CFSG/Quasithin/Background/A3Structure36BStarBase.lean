
module

public import CFSG.Quasithin.Background.A3Structure36BNilpotent
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.Nilpotent

@[expose] public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin.A36B

open scoped commutatorElement

variable {X : Type} [Group X]

theorem not_dvd_card_fitting_of_pCore_eq_bot [Finite X] {p : ℕ} [Fact p.Prime]
    (hp : CFSG.pCore p X = ⊥) : ¬ p ∣ Nat.card (CFSG.fittingSubgroup X) := by
  intro hdvd
  have hnil : Group.IsNilpotent (CFSG.fittingSubgroup X) := inferInstance
  obtain ⟨S⟩ : Nonempty (Sylow p (CFSG.fittingSubgroup X)) := inferInstance
  have hS : S.map (CFSG.fittingSubgroup X).subtype ≤ CFSG.pCore p X :=
    Sylow.map_le_pCore inferInstance hnil p S
  rw [hp, le_bot_iff] at hS
  have hS1 : (S : Subgroup (CFSG.fittingSubgroup X)) = ⊥ :=
    (Subgroup.map_eq_bot_iff_of_injective _ (CFSG.fittingSubgroup X).subtype_injective).1 hS
  have hcard : Nat.card S = 1 := by rw [hS1]; exact Subgroup.card_bot
  have hS2 : p ∣ Nat.card S := Sylow.dvd_card_of_dvd_card S hdvd
  rw [hcard] at hS2
  exact (Fact.out : p.Prime).one_lt.ne' (Nat.dvd_one.1 hS2)

theorem fitting_le_pCore_sup_pPrimeCore [Finite X] (q : ℕ) [Fact q.Prime] :
    CFSG.fittingSubgroup X ≤ CFSG.pCore q X ⊔ CFSG.pPrimeCore q X := by
  have h1 := CFSG.nilpotent_top_le_pCore_sup_pPrimeCore
    (Q := ↥(CFSG.fittingSubgroup X)) (p := q) inferInstance
  have h2 := Subgroup.map_mono (f := (CFSG.fittingSubgroup X).subtype) h1
  rw [Subgroup.map_sup, ← MonoidHom.range_eq_map, Subgroup.range_subtype] at h2
  refine h2.trans (sup_le_sup (map_pCore_le (CFSG.fittingSubgroup X) q) ?_)
  have hn : ((CFSG.pPrimeCore q ↥(CFSG.fittingSubgroup X)).map
      (CFSG.fittingSubgroup X).subtype).Normal := inferInstance
  refine le_sSup ⟨hn, ?_⟩
  rw [Subgroup.card_map_of_injective (CFSG.fittingSubgroup X).subtype_injective]
  exact CFSG.pPrimeCore_coprime_card (p := q) (G := ↥(CFSG.fittingSubgroup X))

theorem pCore_inf_pPrimeCore [Finite X] (q : ℕ) [Fact q.Prime] :
    CFSG.pCore q X ⊓ CFSG.pPrimeCore q X = ⊥ := by
  rw [eq_bot_iff]
  intro x ⟨hx1, hx2⟩
  obtain ⟨k, hk⟩ := CFSG.pCore_isPGroup (p := q) (G := X) ⟨x, hx1⟩
  have h1 : orderOf x ∣ q ^ k := orderOf_dvd_of_pow_eq_one (by simpa using congrArg Subtype.val hk)
  have h2 : orderOf x ∣ Nat.card (CFSG.pPrimeCore q X) := Subgroup.orderOf_dvd_natCard _ hx2
  have hcop : Nat.Coprime (q ^ k) (Nat.card (CFSG.pPrimeCore q X)) :=
    (CFSG.pPrimeCore_coprime_card (p := q) (G := X)).pow_left k
  have h3 : orderOf x = 1 := Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h1 hcop) h2
  rw [Subgroup.mem_bot]
  exact orderOf_eq_one_iff.1 h3

theorem fitting_le_pCore_sup_inf [Finite X] (q : ℕ) [Fact q.Prime] :
    CFSG.fittingSubgroup X ≤
      CFSG.pCore q X ⊔ (CFSG.fittingSubgroup X ⊓ CFSG.pPrimeCore q X) := by
  have hdec := fitting_le_pCore_sup_pPrimeCore (X := X) q
  have hRF : CFSG.pCore q X ≤ CFSG.fittingSubgroup X := CFSG.pCore_le_fitting X q
  exact (A3.eq_sup_inf_of_le_sup (L := CFSG.pCore q X) (N := CFSG.pPrimeCore q X)
    (P := CFSG.fittingSubgroup X)
    (by rw [Subgroup.normalizer_eq_top_iff.mpr inferInstance]; exact le_top) hRF hdec).le

theorem isPi_of_dvd_card_fitting (hF : A36CaseBFacts) (h : A36BHyp X) {K : Subgroup X}
    (hK : KernelSetup X K) {q : ℕ} (hq : q.Prime)
    (hqF : q ∣ Nat.card (CFSG.fittingSubgroup X)) : IsPi X q := by
  have hfin : Finite X := h.finite
  have hfq : Fact q.Prime := ⟨hq⟩
  by_contra hπ
  have hRc : CFSG.pCore q X ≤ Subgroup.center X := not_not.1 hπ
  have hKF : K = CFSG.fittingSubgroup X := kernel_eq_fitting h hK
  have hKD : IsKernelData X (CFSG.fittingSubgroup X) := hKF ▸ hK.data
  obtain ⟨r, hr, h5, hPSL⟩ := hK.psl
  set H : Subgroup X := CFSG.fittingSubgroup X ⊓ CFSG.pPrimeCore q X with hH
  have hHn : H.Normal := inferInstance
  have hFle : CFSG.fittingSubgroup X ≤ CFSG.pCore q X ⊔ H := fitting_le_pCore_sup_inf q
  have hcomm : ∀ k ∈ CFSG.fittingSubgroup X, ∀ g : X, ⁅k, g⁆ ∈ H := by
    intro k hk g
    obtain ⟨y, hy, z, hz, rfl⟩ := Subgroup.mem_sup_of_normal_right.1 (hFle hk)
    have hyc : y ∈ Subgroup.center X := hRc hy
    have h1 : y * z = z * y := (Subgroup.mem_center_iff.1 hyc z).symm
    rw [h1, commutatorElement_mul_center_left g hyc]
    have h2 : ⁅z, g⁆ = z * (g * z⁻¹ * g⁻¹) := by
      rw [commutatorElement_def]
      group
    rw [h2]
    exact H.mul_mem hz (hHn.conj_mem _ (H.inv_mem hz) g)
  have hHF : H = CFSG.fittingSubgroup X :=
    eq_of_commutator_le hF.l2mult h hr h5 hPSL hKD inf_le_left hcomm (odd_card_fitting h)
  have hRH : CFSG.pCore q X ≤ H := by
    rw [hHF]
    exact CFSG.pCore_le_fitting X q
  have hbot : CFSG.pCore q X = ⊥ := by
    have h1 : CFSG.pCore q X ≤ CFSG.pCore q X ⊓ CFSG.pPrimeCore q X :=
      le_inf le_rfl (hRH.trans inf_le_right)
    rw [pCore_inf_pPrimeCore] at h1
    exact le_bot_iff.1 h1
  exact not_dvd_card_fitting_of_pCore_eq_bot hbot hqF

end CFSG.Quasithin.A36B
