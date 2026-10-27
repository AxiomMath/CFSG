module

public import CFSG.Quasithin.EmptyFaithful.S152QB
public import CFSG.Quasithin.EmptyFaithful.S151b111

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

namespace S152U

variable {G : Type} [Group G] [Finite G]

theorem lift_offender {H U A B₁ : Subgroup G} (hA : IsMaxElemAbelian H A) (hU : IsElemAbelian 2 U)
    (hUQ : U ≤ pCoreOf 2 H) (hB₁A : B₁ ≤ A)
    (hcard : Nat.card B₁ * Nat.card ↥(U ⊓ Subgroup.centralizer (B₁ : Set G)) =
      Nat.card A * Nat.card ↥(B₁ ⊓ U)) :
    IsMaxElemAbelian H (B₁ ⊔ (U ⊓ Subgroup.centralizer (B₁ : Set G))) ∧
      (B₁ ⊔ (U ⊓ Subgroup.centralizer (B₁ : Set G))) ⊔ pCoreOf 2 H = B₁ ⊔ pCoreOf 2 H := by
  set C := U ⊓ Subgroup.centralizer (B₁ : Set G) with hC
  have hUH : U ≤ H := hUQ.trans (pCoreOf_le 2 H)
  have hB₁e : IsElemAbelian 2 B₁ := B2F.isElemAbelian_mono hB₁A hA.2.1
  have hCe : IsElemAbelian 2 C := B2F.isElemAbelian_mono inf_le_left hU
  have hcomm : ∀ b ∈ B₁, ∀ c ∈ C, b * c = c * b := fun b hb c hc =>
    Subgroup.mem_centralizer_iff.1 hc.2 b hb
  have hDe : IsElemAbelian 2 (B₁ ⊔ C) := B2F.isElemAbelian_sup_of_commute hB₁e hCe hcomm
  have hDH : B₁ ⊔ C ≤ H := sup_le (hB₁A.trans hA.1) (inf_le_left.trans hUH)
  have hDcard : Nat.card ↥(B₁ ⊔ C) * Nat.card ↥(B₁ ⊓ C) = Nat.card B₁ * Nat.card C :=
    B2F.card_sup_mul_card_inf_of_commute hcomm
  have hinf : B₁ ⊓ C = B₁ ⊓ U := by
    apply le_antisymm
    · exact inf_le_inf_left _ inf_le_left
    · intro x hx
      refine ⟨hx.1, hx.2, Subgroup.mem_centralizer_iff.2 fun b hb => ?_⟩
      exact B2F.isElemAbelian_comm hA.2.1 (hB₁A hb) (hB₁A hx.1)
  rw [hinf] at hDcard
  have hpos : 0 < Nat.card ↥(B₁ ⊓ U) := Nat.card_pos
  have hDA : Nat.card ↥(B₁ ⊔ C) = Nat.card A := by
    refine Nat.eq_of_mul_eq_mul_right hpos ?_
    rw [hDcard]
    exact hcard
  refine ⟨⟨hDH, hDe, fun B hBH hB => (hA.2.2 B hBH hB).trans hDA.ge⟩, ?_⟩
  have hCQ : C ≤ pCoreOf 2 H := inf_le_left.trans hUQ
  rw [sup_assoc, sup_eq_right.2 hCQ]

theorem card_inf_centralizer_eq {H U A : Subgroup G} (hA : IsMaxElemAbelian H A)
    (hU : IsElemAbelian 2 U) (hUH : U ≤ H) :
    Nat.card ↥(U ⊓ Subgroup.centralizer (A : Set G)) = Nat.card ↥(A ⊓ U) := by
  have h : U ⊓ Subgroup.centralizer (A : Set G) = A ⊓ U := by
    apply Subgroup.ext
    intro x
    constructor
    · intro hx
      exact ⟨inf_centralizer_le_of_isMaxElemAbelian hU hUH hA hx, hx.1⟩
    · intro hx
      exact ⟨hx.2, Subgroup.mem_centralizer_iff.2 fun a ha =>
        B2F.isElemAbelian_comm hA.2.1 ha hx.1⟩
  rw [h]

end S152U

@[expose] def Input15209Offender : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M : Subgroup G), Setting152 T Mc M →
    ∀ H : Subgroup G, IsHStar T M H → Concl319 T M (V154 T Mc M) H True →
      Nonempty (OTwoQuot H ≃* S152N.W3) → ∀ A ∈ deltaSet H (V154 T Mc M),
        ∃ B₁ : Subgroup G, B₁ ≤ A ∧ (B₁ ⊓ pCoreOf 2 H).relIndex B₁ = 2 ∧
          Nat.card B₁ *
              Nat.card ↥(conjClosure (V154 T Mc M) H ⊓ Subgroup.centralizer (B₁ : Set G)) =
            Nat.card A * Nat.card ↥(B₁ ⊓ conjClosure (V154 T Mc M) H)

theorem input15209Lift_of_offender (h1511one : StageLemma15111One) (hO : Input15209Offender) :
    Input15209Lift := by
  intro G _ _ T Mc M hs H hH hc hW hne
  obtain ⟨A, hA⟩ := hne
  obtain ⟨B₁, hB₁A, hrel, hcard⟩ := hO G T Mc M hs H hH hc hW A hA
  have hVQ : V154 T Mc M ≤ pCoreOf 2 H := h1511one G T Mc M hs.qtfe hs.mf hs.ce H hH
  have hUQ : conjClosure (V154 T Mc M) H ≤ pCoreOf 2 H :=
    conjClosure_le fun h hh z hz =>
      (Subgroup.mem_normalizer_iff.1 (le_normalizer_pCoreOf 2 H hh) z).1 (hVQ hz)
  obtain ⟨hDmax, hDQ⟩ := S152U.lift_offender hA.1 hc.elemAbelian hUQ hB₁A hcard
  refine ⟨_, hDmax, ?_, ?_⟩
  · intro hDle
    have hB₁Q : B₁ ≤ pCoreOf 2 H := le_sup_left.trans hDle
    have h1 : (B₁ ⊓ pCoreOf 2 H).relIndex B₁ = 1 :=
      Subgroup.relIndex_eq_one.2 (le_inf le_rfl hB₁Q)
    omega
  · have hDH := hDmax.1
    rw [← Gap6.relIndex_sup_pCoreOf_eq hDH, hDQ, Gap6.relIndex_sup_pCoreOf_eq (hB₁A.trans hA.1.1)]
    exact hrel

end CFSG.Quasithin
