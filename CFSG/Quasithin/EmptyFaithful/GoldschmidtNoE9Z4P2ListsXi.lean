module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtNoE9Z4P2Sec
public import CFSG.Quasithin.Background.C1PackS15212A
public import CFSG.Quasithin.Background.C1PackS15348
public import CFSG.Quasithin.EmptyFaithful.S146zXAPq

public section

namespace CFSG.Quasithin.E9P2L

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G] {T M H PQ : Subgroup G} {p : ℕ}

theorem relIndex_pCoreOf_oTwoUpper (h35 : Lemma1435) (S : Setting146 G T M)
    (hred : IsRedCE T M H PQ p) (hshape : IsE9Z4Shape T H p) :
    (pCoreOf 2 (oTwoUpper H)).relIndex (oTwoUpper H) = 3 ^ 2 := by
  have hKH : oTwoUpper H ≤ H := oTwoUpper_le H
  have h1 := S146zX.relIndex_inf_pCoreOf_eq_card_map (H := H) (X := PQ) hred.le
  rw [inf_eq_right.2 hred.lt.le] at h1
  rw [S152Y.pCoreOf_eq_inf_of_normalizer hKH (le_normalizer_oTwoUpper H),
    S146zX.relIndex_inf_pCoreOf_eq_card_map hKH, S146zX.oTwoUpper_star_eq S hred, ← h1,
    (e9_pq_section h35 S hred hshape).1]
  norm_num

theorem isXi_oTwoUpper (h35 : Lemma1435) (S : Setting146 G T M) (hred : IsRedCE T M H PQ p)
    (hshape : IsE9Z4Shape T H p) : IsXi T (oTwoUpper H) := by
  have hrel := relIndex_pCoreOf_oTwoUpper h35 S hred hshape
  obtain ⟨-, hcomm, hpow⟩ := e9_pq_section h35 S hred hshape
  obtain rfl : p = 3 := hshape.1
  have hH : IsHTM T M H := hred.isHTM
  have hTH : T ≤ H := hH.1.1
  have hT2 : IsPGroup 2 T := S.hyp.sylow.1
  have hsyl : IsSylowTwoOf T H := isSylowTwoOf_of_quasithinIsSylowTwo S.hyp.sylow hTH
  have hKH : oTwoUpper H ≤ H := oTwoUpper_le H
  have hKPQ : oTwoUpper H ≤ PQ := hred.oTwoUpper_le_pq hT2
  have hQH : H ≤ Subgroup.normalizer (pCoreOf 2 H : Set G) := le_normalizer_pCoreOf 2 H
  have hpK : pCoreOf 2 (oTwoUpper H) = oTwoUpper H ⊓ pCoreOf 2 H :=
    S152Y.pCoreOf_eq_inf_of_normalizer hKH (le_normalizer_oTwoUpper H)
  have hsup : oTwoUpper H ⊔ T = H := C1Pack12.oTwoUpper_sup_eq_of_sylow hsyl
  refine ⟨(C1Pack153.oTwoUpper_idem' H).symm, hTH.trans (le_normalizer_oTwoUpper H), ?_, 3,
    hred.prime, hred.odd, ?_, Or.inl hrel, ?_⟩
  · rw [hsup]
    exact hH.1.2
  · intro x hx
    rw [hpK]
    exact ⟨(oTwoUpper H).pow_mem hx 3, hpow x (hKPQ hx)⟩
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
      exact sup_le (S146zX.le_normalizer_of_forall_conj hconj) hYT
    have hYQsub : Y ⊔ pCoreOf 2 H ≤ PQ := sup_le (hY2.trans hKPQ) hred.lt.le
    have hHYQ : H ≤ Subgroup.normalizer ((Y ⊔ pCoreOf 2 H : Subgroup G) : Set G) := fun x hx =>
      Subgroup.inf_normalizer_le_normalizer_sup Y (pCoreOf 2 H) ⟨hHY hx, hQH hx⟩
    rcases hred.minimal (Y ⊔ pCoreOf 2 H) le_sup_right hYQsub hHYQ with hN | hN
    · left
      have hYQ : Y ≤ pCoreOf 2 H := le_sup_left.trans hN.le
      have hYO : Y ≤ pCoreOf 2 (oTwoUpper H) := by
        rw [hpK]
        exact le_inf hY2 hYQ
      exact le_antisymm (hYO.trans le_sup_right) hY1
    · right
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

end CFSG.Quasithin.E9P2L
