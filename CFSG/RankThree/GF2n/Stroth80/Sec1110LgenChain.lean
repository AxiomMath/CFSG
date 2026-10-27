module

public import CFSG.RankThree.GF2n.Stroth80.Sec1110CMLmConsumer
public import CFSG.RankThree.GF2n.Stroth80.Sec1110LgenSwap
import CFSG.RankThree.GF2n.Stroth80.Sec11CMThree

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open CFSG.Adapters.RankTwoModelTransports
open scoped commutatorElement Matrix

variable {G : Type} [Group G]

private theorem exists_globalModelGF_ringEquiv [Finite G]
    {M Q Z B : Subgroup G} (hc : Ctx M Q Z B) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = Nat.card Z) :
    ∃ (n₀ : ℕ) (γ₀ : G → GaloisField 2 n₀) (M₀₀ : Tim79.QuadModel Q Z (GaloisField 2 n₀) γ₀),
      Nat.card Z = 2 ^ n₀ ∧ GlobalModelData M Q Z γ₀ M₀₀ ∧
        Nat.card (GaloisField 2 n₀) = Nat.card Z ∧ Nonempty (K ≃+* GaloisField 2 n₀) := by
  obtain ⟨n₀, γ₀, M₀₀, hZcard, hD₀⟩ := stroth_globalModelDataGF hc.hyp
  have hn₀ : n₀ ≠ 0 := by
    rintro rfl
    simp only [pow_zero] at hZcard
    have := hc.hyp.q4
    omega
  have hK₀card : Nat.card (GaloisField 2 n₀) = Nat.card Z :=
    (GaloisField.card 2 n₀ hn₀).trans hZcard.symm
  letI : Fintype K := Fintype.ofFinite K
  letI : Fintype (GaloisField 2 n₀) := Fintype.ofFinite _
  have hcardEq : Fintype.card K = Fintype.card (GaloisField 2 n₀) := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hK, hK₀card]
  exact ⟨n₀, γ₀, M₀₀, hZcard, hD₀, hK₀card, ⟨FiniteField.ringEquivOfCardEq hcardEq⟩⟩

private theorem width_eq_of_chain [Finite G]
    {M Q Z B : Subgroup G} [(Q.subgroupOf M).Normal] (hc : Ctx M Q Z B) {n m : ℕ}
    (hw : Width Q Z n) {X₁ X₂ X₃ X₄ : Subgroup G} (hX₁ : X₁ = Z) (h₁₂ : X₁ ≤ X₂)
    (h₂₃ : X₂ ≤ X₃) (h₃₄ : X₃ ≤ X₄) (hX₄Q : X₄ = Q) (hX₃ : X₃ = X₂) {K : Type} [Field K]
    [Finite K] (hK : Nat.card K = Nat.card Z)
    (nat2 : NaturalRep (ι := Fin m) K (StatedSL m K) (XbarPre M Q Z B) X₂ X₁ Q)
    (nat4 : NaturalDualRep (ι := Fin m) K (StatedSL m K) (XbarPre M Q Z B) X₄ X₃ Q) :
    n = m := by
  have hZ₂ : 2 ≤ Nat.card Z := by have := hc.hyp.q4; omega
  have hZ₁ : Z ≤ X₁ := hX₁ ▸ le_rfl
  have hcardX₄ : Nat.card X₄ = Nat.card Z * Nat.card K ^ (2 * m) :=
    card_X₄_of_dualRep (K := K) (m := m) hX₁ hZ₁ h₁₂ h₂₃ h₃₄ hX₃ nat2 nat4
  have hQcard : Nat.card Q = Nat.card Z ^ (2 * m + 1) := by
    rw [← hX₄Q, hcardX₄, hK, ← pow_succ']
  have h := hw
  rw [Width, hQcard] at h
  have := Nat.pow_right_injective hZ₂ h
  omega

private theorem caseVICore_XbarPre_of_chain [Finite G]
    {M Q Z B : Subgroup G} [(Q.subgroupOf M).Normal] (hc : Ctx M Q Z B) {n m : ℕ}
    (hw : Width Q Z n) (hm : 3 ≤ m) {X₁ X₂ X₃ X₄ : Subgroup G} (hX₁ : X₁ = Z) (h₁₂ : X₁ ≤ X₂)
    (h₂₃ : X₂ ≤ X₃) (h₃₄ : X₃ ≤ X₄) (hX₄Q : X₄ = Q) (hX₂ : X₂ = Z ⊔ ⁅X₃, XbarPre M Q Z B⁆)
    (hX₃ : X₃ = X₂) (hX₄ : X₄ = Z ⊔ ⁅Q, XbarPre M Q Z B⁆) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = Nat.card Z)
    (nat2 : NaturalRep (ι := Fin m) K (StatedSL m K) (XbarPre M Q Z B) X₂ X₁ Q)
    (nat4 : NaturalDualRep (ι := Fin m) K (StatedSL m K) (XbarPre M Q Z B) X₄ X₃ Q) :
    CaseVICore M Q Z (XbarPre M Q Z B) n := by
  have hnm := width_eq_of_chain hc hw hX₁ h₁₂ h₂₃ h₃₄ hX₄Q hX₃ hK nat2 nat4
  obtain ⟨n₀, γ₀, M₀₀, -, hD₀, hK₀card, ⟨e⟩⟩ := exists_globalModelGF_ringEquiv hc hK
  have hw' : Width Q Z m := by
    rw [← hnm]
    exact hw
  have nat2K : NaturalRep (ι := Fin m) (GaloisField 2 n₀) (StatedSL m (GaloisField 2 n₀))
      (XbarPre M Q Z B) X₂ X₁ Q := by
    have h := naturalRep_of_ringEquiv (ι := Fin m) e nat2
    rwa [glCongr_statedSL] at h
  have nat4K : NaturalDualRep (ι := Fin m) (GaloisField 2 n₀)
      (StatedSL m (GaloisField 2 n₀)) (XbarPre M Q Z B) X₄ X₃ Q := by
    have h := naturalDualRep_of_ringEquiv (ι := Fin m) e nat4
    rwa [glCongr_statedSL] at h
  rw [hnm]
  exact caseVICore_of_chain_final_unconditional (K := GaloisField 2 n₀) (γ := γ₀)
    (M₀ := M₀₀) (n := m) hc hw' hm hD₀ hK₀card hX₁ h₁₂ h₂₃ h₃₄ hX₄Q.le hX₂ hX₃ hX₄ nat2K nat4K

private theorem false_of_l4Branch [Finite G]
    {M Q Z B : Subgroup G} [(Q.subgroupOf M).Normal] (hc : Ctx M Q Z B) {n : ℕ}
    (hw : Width Q Z n) (hn : 2 < n) {X₁ X₂ : Subgroup G} (hX₁ : X₁ = Z) (hX₂Q : X₂ = Q)
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = Nat.card Z)
    (nat : NaturalRep (ι := Fin 3 ⊕ Fin 3) K (StatedOmega (StatedQuadPlus 3 K))
      (XbarPre M Q Z B) X₂ X₁ Q) : False := by
  obtain ⟨n₀, γ₀, M₀₀, hZcard, hD₀, -, ⟨e⟩⟩ := exists_globalModelGF_ringEquiv hc hK
  letI : Fintype K := Fintype.ofFinite K
  haveI : CharP K 2 := by
    apply charP_of_card_eq_prime_pow (p := 2) (f := n₀)
    rw [Fintype.card_eq_nat_card, hK, hZcard]
  have natQ : NaturalRep (ι := Fin 3 ⊕ Fin 3) K (StatedOmega (StatedQuadPlus 3 K))
      (XbarPre M Q Z B) Q Z Q := by
    simpa [hX₂Q, hX₁] using nat
  have natC : NaturalRep (ι := Fin 3 ⊕ Fin 3) K (StatedOmega (StatedQuadPlus 3 K))
      (XbarPre M Q Z B) X₂ X₁ (XbarPreCenter M Q Z B) := by
    rw [XbarPreCenter_eq_Q_of_naturalRep_omega (K := K) hc natQ]
    exact nat
  have hQmap : ∀ v : Fin 3 ⊕ Fin 3 → K,
      StatedQuadPlus 3 (GaloisField 2 n₀) (e ∘ v) = e (StatedQuadPlus 3 K v) := by
    intro v
    unfold StatedQuadPlus
    simp [CFSG.MatrixModel.plusQuadCore, map_sum, map_mul]
  have hΩmap := CFSG.ClassicalInvolution.Upgrade.map_statedOmega (K := K)
    (L := GaloisField 2 n₀) (QK := StatedQuadPlus 3 K)
    (QL := StatedQuadPlus 3 (GaloisField 2 n₀)) e hQmap
  have natCK : NaturalRep (ι := Fin 3 ⊕ Fin 3) (GaloisField 2 n₀)
      (StatedOmega (StatedQuadPlus 3 (GaloisField 2 n₀))) (XbarPre M Q Z B) X₂ X₁
      (XbarPreCenter M Q Z B) := by
    have h := naturalRep_of_ringEquiv (ι := Fin 3 ⊕ Fin 3) e natC
    rwa [hΩmap] at h
  exact l4Orthogonal_case_false_of_chain (K := GaloisField 2 n₀) (γ := γ₀)
    (M₀ := M₀₀) hc hw (by omega) hD₀ hX₂Q hX₁ natCK

theorem caseVICore_XbarPre_of_CMLmChain [Finite G]
    {M Q Z B : Subgroup G} [(Q.subgroupOf M).Normal] (hc : Ctx M Q Z B)
    {n m x : ℕ} (hw : Width Q Z n) (hn : 2 < n)
    (ha2 : ∃ a ∈ LB M Q B, IsA2 Q Z a)
    (hC : CMLmChain) (hLm : CFSG.Blueprint.LieModel (XbarMod M Q Z B) .PSL m 2 x)
    (hm : 3 ≤ m) :
    CaseVICore M Q Z (XbarPre M Q Z B) n := by
  rcases hC G M Q Z B hc n m x hw hn ha2 hLm hm with
    ⟨X₁, X₂, X₃, X₄, hX₁, h₁₂, h₂₃, h₃₄, hX₄Q, -, hX₂, hX₃, hX₄, K, hKf, hKfin, hK, nat2,
      nat4⟩ | ⟨-, X₁, X₂, hX₁, -, hX₂Q, -, -, K, hKf, hKfin, hK, nat⟩
  · letI : Field K := hKf
    letI : Finite K := hKfin
    exact caseVICore_XbarPre_of_chain hc hw hm hX₁ h₁₂ h₂₃ h₃₄ hX₄Q hX₂ hX₃ hX₄ hK nat2 nat4
  · letI : Field K := hKf
    letI : Finite K := hKfin
    exact (false_of_l4Branch hc hw hn hX₁ hX₂Q hK nat).elim

theorem Lgen_le_XbarPre_of_CMLmChain [Finite G]
    {M Q Z B : Subgroup G} [(Q.subgroupOf M).Normal] (hc : Ctx M Q Z B)
    {n m x : ℕ} (hw : Width Q Z n) (hn : 2 < n)
    (ha2 : ∃ a ∈ LB M Q B, IsA2 Q Z a)
    (hC : CMLmChain) (hLm : CFSG.Blueprint.LieModel (XbarMod M Q Z B) .PSL m 2 x)
    (hm : 3 ≤ m) :
    Lgen M (LB M Q B) ≤ XbarPre M Q Z B :=
  (Lgen_le_XbarPre_iff hc).mpr (LB_le_XbarPre_of_caseVICore hc hw (by omega)
    (caseVICore_XbarPre_of_CMLmChain hc hw hn ha2 hC hLm hm))

theorem CMLmThree_of_CMLmChain (hC : CMLmChain) : CMLmThree := by
  intro G _ _ M Q Z B _ hc n x hw hn ha2 hLm _
  exact Lgen_le_XbarPre_of_CMLmChain hc hw hn ha2 hC hLm le_rfl

end CFSG.RankThree.GF2n.Stroth80
