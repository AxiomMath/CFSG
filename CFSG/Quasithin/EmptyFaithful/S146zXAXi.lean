module

public import CFSG.Quasithin.EmptyFaithful.S146zXAPq
public import CFSG.Quasithin.EmptyFaithful.S146zHFaith
public import CFSG.Quasithin.Background.C1PackS15212A
public import CFSG.Quasithin.Background.C1PackS15348

public section

namespace CFSG.Quasithin.S146zX

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G] {T M H PQ : Subgroup G} {p : ℕ}
  {H₀ H₁ H₂ : Subgroup G} {t : G}

theorem isXi_oTwoUpper (S : Setting146 G T M) (hred : IsRedCE T M H PQ p)
    (h : IsDecP T M H p H₀ H₁ H₂ t) : IsXi T (oTwoUpper H) := by
  have hH : IsHTM T M H := hred.isHTM
  have hTH : T ≤ H := hH.1.1
  have hT2 : IsPGroup 2 T := S.hyp.sylow.1
  have hsyl : IsSylowTwoOf T H := isSylowTwoOf_of_quasithinIsSylowTwo S.hyp.sylow hTH
  have hKH : oTwoUpper H ≤ H := oTwoUpper_le H
  have hKPQ : oTwoUpper H ≤ PQ := hred.oTwoUpper_le_pq hT2
  have hQH : H ≤ Subgroup.normalizer (pCoreOf 2 H : Set G) := le_normalizer_pCoreOf 2 H
  have hpK : pCoreOf 2 (oTwoUpper H) = oTwoUpper H ⊓ pCoreOf 2 H :=
    S152Y.pCoreOf_eq_inf_of_normalizer hKH (le_normalizer_oTwoUpper H)
  obtain ⟨hcomm, hpow, -⟩ := pq_section S hred h
  have hsup : oTwoUpper H ⊔ T = H := C1Pack12.oTwoUpper_sup_eq_of_sylow hsyl
  refine ⟨(C1Pack153.oTwoUpper_idem' H).symm, hTH.trans (le_normalizer_oTwoUpper H), ?_, p,
    hred.prime, hred.odd, ?_, Or.inl (relIndex_pCoreOf_oTwoUpper_of_isDecP S hred h), ?_⟩
  · rw [hsup]
    exact hH.1.2
  · intro x hx
    rw [hpK]
    exact ⟨(oTwoUpper H).pow_mem hx p, hpow x (hKPQ hx)⟩
  · intro Y hY1 hY2 hYT
    have hO2K : pCoreOf 2 (oTwoUpper H) ≤ Y := le_sup_right.trans hY1
    have hconj : ∀ g ∈ PQ, ∀ y ∈ Y, g * y * g⁻¹ ∈ Y := by
      intro g hg y hy
      have hyK : y ∈ oTwoUpper H := hY2 hy
      have hgK : g * y * g⁻¹ ∈ oTwoUpper H :=
        (Subgroup.mem_normalizer_iff.mp (le_normalizer_oTwoUpper H (hred.le hg)) y).mp hyK
      have hc : g * y * g⁻¹ * y⁻¹ ∈ pCoreOf 2 (oTwoUpper H) := by
        rw [hpK]
        exact ⟨(oTwoUpper H).mul_mem hgK ((oTwoUpper H).inv_mem hyK), hcomm g hg y (hKPQ hyK)⟩
      have e : g * y * g⁻¹ = (g * y * g⁻¹ * y⁻¹) * y := by group
      rw [e]
      exact Y.mul_mem (hO2K hc) hy
    have hHY : H ≤ Subgroup.normalizer (Y : Set G) := by
      rw [hred.eq]
      exact sup_le (le_normalizer_of_forall_conj hconj) hYT
    have hYQsub : Y ⊔ pCoreOf 2 H ≤ PQ := sup_le (hY2.trans hKPQ) hred.lt.le
    have hHYQ : H ≤ Subgroup.normalizer ((Y ⊔ pCoreOf 2 H : Subgroup G) : Set G) := fun x hx =>
      Subgroup.inf_normalizer_le_normalizer_sup Y (pCoreOf 2 H) ⟨hHY hx, hQH hx⟩
    rcases hred.minimal (Y ⊔ pCoreOf 2 H) le_sup_right hYQsub hHYQ with hN | hN
    ·
      left
      have hYQ : Y ≤ pCoreOf 2 H := le_sup_left.trans hN.le
      have hYO : Y ≤ pCoreOf 2 (oTwoUpper H) := by
        rw [hpK]
        exact le_inf hY2 hYQ
      exact le_antisymm (hYO.trans le_sup_right) hY1
    ·
      right
      refine le_antisymm hY2 (fun k hk => ?_)
      have hkPQ : k ∈ pCoreOf 2 H ⊔ Y := by
        rw [sup_comm, hN]
        exact hKPQ hk
      obtain ⟨q, hq, a, ha, rfl⟩ := (Ch1Sec3.mem_sup_iff_of_le_normalizer
        (hY2.trans (hKH.trans hQH))).mp hkPQ
      have hqK : q ∈ oTwoUpper H := by
        have := (oTwoUpper H).mul_mem hk ((oTwoUpper H).inv_mem (hY2 ha))
        simpa using this
      have hqY : q ∈ Y := hO2K (by rw [hpK]; exact ⟨hqK, hq⟩)
      exact Y.mul_mem hqY ha

theorem card_eq_seventyTwo_mul (S : Setting146 G T M) (hred : IsRedCE T M H PQ 3)
    (h : IsDecP T M H 3 H₀ H₁ H₂ t) : Nat.card H = 72 * Nat.card (pCoreOf 2 H) := by
  rw [card_eq_card_pCoreOf_mul_relIndex, h.relIndex_pCoreOf_eq_72 S hred, mul_comm]

end CFSG.Quasithin.S146zX
