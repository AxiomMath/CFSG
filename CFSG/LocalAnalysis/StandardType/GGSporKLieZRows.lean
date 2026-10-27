module

public import CFSG.LocalAnalysis.StandardType.GGSporKLamOrders
public import CFSG.LocalAnalysis.StandardType.GGSporKLieZSp
public import CFSG.LocalAnalysis.StandardType.GGSporKLieZOmega
public import CFSG.LocalAnalysis.StandardType.GGSporKLieZSL
public import CFSG.LocalAnalysis.StandardType.GGSporKLieZSU
public import CFSG.LocalAnalysis.StandardType.GGSporKLieZExc
public import CFSG.LocalAnalysis.StandardType.MarkingDict

public section

namespace CFSG.StandardType.SporadicShape

open CFSG CFSG.Open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley

@[expose] def sevenSqLabels : List LargeEvenLabel :=
  [⟨.F4, 0, 1⟩, ⟨.twE6, 0, 1⟩, ⟨.triD4, 0, 1⟩, ⟨.C, 2, 3⟩, ⟨.B, 2, 3⟩, ⟨.C, 6, 1⟩, ⟨.B, 6, 1⟩,
    ⟨.D, 6, 1⟩, ⟨.A, 5, 1⟩, ⟨.A, 5, 2⟩, ⟨.twA, 3, 3⟩, ⟨.twD, 3, 3⟩]

private theorem l937z_rw_charP {K : Type} [Field K] [Finite K] (f : ℕ)
    (hK : Nat.card K = 2 ^ f) : CharP K 2 := by
  haveI := Fintype.ofFinite K
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact charP_of_card_eq_prime_pow (f := f) (by rw [← Nat.card_eq_fintype_card, hK])

private theorem l937z_rw_psp {R : Type} [Group R] (n f : ℕ)
    (h : StatedClassicalModel R .PSp n 2 f) : LieZRow R := by
  obtain ⟨-, K, hF, hfin, hK, ⟨e⟩⟩ := h
  exact lieZRow_of_mulEquiv e.symm (@lieZRow_PSp K hF hfin (l937z_rw_charP f hK) n)

private theorem l937z_rw_psl {R : Type} [Group R] (n f : ℕ) (hf : f = 1 ∨ f = 2)
    (h : StatedClassicalModel R .PSL n 2 f) : LieZRow R := by
  obtain ⟨-, K, hF, hfin, hK, ⟨e⟩⟩ := h
  have h7 : ¬ 7 ∣ Nat.card K - 1 := by
    rcases hf with rfl | rfl <;> rw [hK] <;> norm_num
  exact lieZRow_of_mulEquiv e.symm (@lieZRow_PSL K hF hfin (l937z_rw_charP f hK) n h7)

private theorem l937z_rw_psu {R : Type} [Group R] (n f : ℕ) (hf : f = 3)
    (h : StatedClassicalModel R .PSU n 2 f) : LieZRow R := by
  obtain ⟨-, K, hF, hfin, hK, ⟨e⟩⟩ := h
  have h7 : Nat.Coprime 7 (2 ^ f + 1) := by subst hf; decide
  exact lieZRow_of_mulEquiv e.symm
    (@lieZRow_PSU K hF hfin (l937z_rw_charP (2 * f) (by rw [hK, ← pow_mul, mul_comm]))
      n (2 ^ f) hK h7)

private theorem l937z_rw_omegaPlus {R : Type} [Group R] (f : ℕ) (hf : f = 1)
    (h : StatedClassicalModel R .POmegaPlus 6 2 f) : LieZRow R := by
  obtain ⟨-, K, hF, hfin, hK, ⟨e⟩⟩ := h
  have h2 : Nat.card K = 2 := by subst hf; simpa using hK
  exact lieZRow_of_mulEquiv e.symm (@lieZRow_POmegaPlus_twelve K hF hfin h2)

private theorem l937z_rw_f4
    (hF4 : ∀ (G : Type) [Group G], UntwistedChevalleyModel G .F4 2 → LieZRow G)
    {R : Type} [Group R] (hR : MarkedModel ⟨.F4, 0, 1⟩ R) : LieZRow R := by
  rcases hR with ⟨hmem, -⟩ | ⟨-, -, hE⟩ | ⟨-, hmem, -⟩ | ⟨-, hbad, -⟩
  · simp [markTag, classicalTags] at hmem
  · exact hF4 R hE.2
  · simp [markTag, reeTitsTags] at hmem
  · simp [markTag] at hbad

private theorem l937z_rw_e6
    (hE6 : ∀ (G : Type) [Group G], TwistedChevalleyModel G .E6 2 → LieZRow G)
    {R : Type} [Group R] (hR : MarkedModel ⟨.twE6, 0, 1⟩ R) : LieZRow R := by
  rcases hR with ⟨hmem, -⟩ | ⟨-, -, hE⟩ | ⟨-, hmem, -⟩ | ⟨-, hbad, -⟩
  · simp [markTag, classicalTags] at hmem
  · exact hE6 R hE.2
  · simp [markTag, reeTitsTags] at hmem
  · simp [markTag] at hbad

private theorem l937z_rw_d4
    (hD4 : ∀ (G : Type) [Group G], TwistedChevalleyModel G .D4 2 → LieZRow G)
    {R : Type} [Group R] (hR : MarkedModel ⟨.triD4, 0, 1⟩ R) : LieZRow R := by
  rcases hR with ⟨hmem, -⟩ | ⟨-, -, hE⟩ | ⟨-, hmem, -⟩ | ⟨-, hbad, -⟩
  · simp [markTag, classicalTags] at hmem
  · exact hD4 R hE.2
  · simp [markTag, reeTitsTags] at hmem
  · simp [markTag] at hbad

theorem lieZRow_of_markedModel_sevenSq
    (hF4 : ∀ (G : Type) [Group G], UntwistedChevalleyModel G .F4 2 → LieZRow G)
    (hE6 : ∀ (G : Type) [Group G], TwistedChevalleyModel G .E6 2 → LieZRow G)
    (hD4 : ∀ (G : Type) [Group G], TwistedChevalleyModel G .D4 2 → LieZRow G)
    {lab : LargeEvenLabel} (hlab : lab ∈ sevenSqLabels) {R : Type} [Group R]
    (hR : MarkedModel lab R) : LieZRow R := by
  simp [sevenSqLabels] at hlab
  rcases hlab with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact l937z_rw_f4 hF4 hR
  · exact l937z_rw_e6 hE6 hR
  · exact l937z_rw_d4 hD4 hR
  · exact l937z_rw_psp 2 3 (LieModel.statedClassicalModel hR (by decide))
  · exact l937z_rw_psp 2 3 (LieModel.statedClassicalModel hR (by decide))
  · exact l937z_rw_psp 6 1 (LieModel.statedClassicalModel hR (by decide))
  · exact l937z_rw_psp 6 1 (LieModel.statedClassicalModel hR (by decide))
  · exact l937z_rw_omegaPlus 1 rfl (LieModel.statedClassicalModel hR (by decide))
  · exact l937z_rw_psl 6 1 (Or.inl rfl) (LieModel.statedClassicalModel hR (by decide))
  · exact l937z_rw_psl 6 2 (Or.inr rfl) (LieModel.statedClassicalModel hR (by decide))
  · exact l937z_rw_psu 4 3 rfl (LieModel.statedClassicalModel hR (by decide))
  · exact l937z_rw_psu 4 3 rfl (LieModel.statedClassicalModel hR (by decide))

theorem lieSevenOddCentre7sq_of_marked {K : Type} [Group K] [Finite K]
    (hF4 : ∀ (G : Type) [Group G], UntwistedChevalleyModel G .F4 2 → LieZRow G)
    (hE6 : ∀ (G : Type) [Group G], TwistedChevalleyModel G .E6 2 → LieZRow G)
    (hD4 : ∀ (G : Type) [Group G], TwistedChevalleyModel G .D4 2 → LieZRow G)
    (hrows : ∀ L : Subgroup K, IsSimpleGroup L →
      StandardType.LargeEvenMarking L (fun _ _ _ _ _ _ => True) →
        ∃ lab : LargeEvenLabel, MarkedModel lab ↥L ∧ Nat.card ↥L = labOrd lab ∧
          (7 ^ 2 ∣ labOrd lab → lab ∈ sevenSqLabels)) :
    LieSevenOddCentre7sq K := by
  refine lieSevenOddCentre7sq_of_rows (fun L hL hmark hsq => ?_)
  obtain ⟨lab, hM, hcard, hmem⟩ := hrows L hL hmark
  exact lieZRow_of_markedModel_sevenSq hF4 hE6 hD4 (hmem (by rw [← hcard]; exact hsq)) hM

end CFSG.StandardType.SporadicShape
