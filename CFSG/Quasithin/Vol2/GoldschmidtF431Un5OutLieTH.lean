module

public import CFSG.Quasithin.Vol2.GoldschmidtF431Un5OutLieTE
public import CFSG.Quasithin.Vol2.GoldschmidtF431Un5OutLieTF

public noncomputable section

namespace CFSG.Quasithin.H13.F431.Un.OL5

open Matrix Subgroup CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.RankThree.PartOne.U5K.Hyp CFSG.Quasithin.H13.Sec53F.Unit CFSG.Quasithin.H13.F431
  CFSG.QuasithinUnique

variable {f : ℕ} {K : Type} [Field K] (hK : UnitaryFieldData 2 f K)

theorem un5_Sylow_Tf (hf : 2 ≤ f) {T : Subgroup (MulAut (hypPSU hK 2 1))} (hU : Uh hK ≤ T)
    (hT : ∀ τ ∈ T, ∃ u ∈ Uh hK, ∃ σ : K ≃+* K, τ = u * fieldP hK σ)
    (hb : fieldP hK (bar5 hK) ∈ T) {K₁ : Subgroup (MulAut (hypPSU hK 2 1))} (hP : Pi hK ≤ K₁)
    (hS : IsSylowTwoOf T K₁) {N : Subgroup (MulAut (hypPSU hK 2 1))} (hTN : T ≤ N)
    (hNK : N ≤ K₁) :
    IsSylowTwoOf (spTf T (fieldP hK (bar5 hK)))
      (Subgroup.centralizer ({fieldP hK (bar5 hK)} : Set (MulAut (hypPSU hK 2 1))) ⊓ N) := by
  have _hf := hf
  have _hb := hb
  have _hP := hP
  have := finite_mulAut_hyp hK
  have := fld5_finite hK
  set H := Subgroup.centralizer ({fieldP hK (bar5 hK)} : Set (MulAut (hypPSU hK 2 1))) ⊓ N
    with hH
  have hTf : spTf T (fieldP hK (bar5 hK)) ≤ H := fun x hx => ⟨hx.2, hTN hx.1⟩
  have hTf2 : IsPGroup 2 (spTf T (fieldP hK (bar5 hK))) := hS.2.1.to_le inf_le_left
  refine isSylowTwoOf_iff.2 ⟨hTf, hTf2, le_antisymm (card_le_twoPart hTf hTf2) ?_⟩
  obtain ⟨R, hR, hTfR⟩ := CFSG.QuasithinUnique.EscapingLocal.exists_isSylowTwoOf_ge hTf hTf2
  obtain ⟨hRH, hR2, hRcard⟩ := isSylowTwoOf_iff.1 hR
  rw [← hRcard]
  have hRK : R ≤ K₁ := hRH.trans (inf_le_right.trans hNK)
  have h1 : Nat.card ↥(R ⊓ Pi hK) ≤ (2 ^ f) ^ 4 :=
    un5tf_inner_fixed hK inf_le_right (hR2.to_le inf_le_left) fun ρ hρ =>
      Subgroup.mem_centralizer_singleton_iff.1 (hRH hρ.1).1
  have h2 := un5te_card_le (N := Pi hK) hS hR2 hRK
  rw [un5t_inf_Pi hK hU hT, un5tf_card_T hK hU hT] at h2
  have hpos : 0 < Nat.card (Uh hK) := Nat.card_pos
  have h3 : Nat.card R * Nat.card (Uh hK) ≤
      (2 ^ f) ^ 4 * Nat.card (un5tfFp hK T) * Nat.card (Uh hK) := by
    calc Nat.card R * Nat.card (Uh hK) ≤
        Nat.card ↥(R ⊓ Pi hK) * (Nat.card (Uh hK) * Nat.card (un5tfFp hK T)) := h2
      _ = Nat.card ↥(R ⊓ Pi hK) * Nat.card (un5tfFp hK T) * Nat.card (Uh hK) := by ring
      _ ≤ _ := Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ h1)
  rw [un5tf_card_Tf hK hU hT]
  exact Nat.le_of_mul_le_mul_right h3 hpos

end CFSG.Quasithin.H13.F431.Un.OL5
