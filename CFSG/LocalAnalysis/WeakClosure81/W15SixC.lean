module

public import CFSG.LocalAnalysis.WeakClosure81.W15SixB
public import CFSG.LocalAnalysis.WeakClosure81.FiveFive
public import CFSG.LocalAnalysis.WeakClosure81.FiveInputs
public import CFSG.Quasithin.Background.C2Blocks
public import CFSG.Blueprint.LieModelAPI

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22
open Subgroup

variable {G : Type} [Group G] [Finite G]

theorem isL2_iff_isPSL {X : Type} [Group X] {n : ℕ} :
    CFSG.LocalAnalysis.UniquenessCase.UC22.IsL2 X n ↔ CFSG.Quasithin.IsPSL 2 2 n X :=
  CFSG.Blueprint.LieModel.classical_iff (t := .PSL) (by decide)

theorem isSz_iff_isSz {X : Type} [Group X] {n : ℕ} :
    CFSG.LocalAnalysis.UniquenessCase.UC22.IsSz X n ↔ CFSG.Quasithin.IsSz n X := by
  unfold CFSG.LocalAnalysis.UniquenessCase.UC22.IsSz CFSG.Quasithin.IsSz
  rw [CFSG.Blueprint.LieModel.twistedB2_iff]
  exact ⟨fun h => h.2, fun h => ⟨rfl, h⟩⟩

theorem one_lt_of_isPSL_or_isSz {X : Type} [Group X] {n : ℕ}
    (h : CFSG.Quasithin.IsPSL 2 2 n X ∨ CFSG.Quasithin.IsSz n X) : 1 < n := by
  rcases h with ⟨⟨-, h1, -, h2, -⟩, -⟩ | ⟨-, a, ha, -, -, -, hn, -⟩
  · by_contra hn
    have : n = 1 := by omega
    subst this
    exact h2 rfl
  · omega

theorem five_nine_borel (hB : Asc80ThmB) {X M A : Subgroup G} (h : IsPairAt M X A)
    (hA : IsElemAbelian 2 A) (hK : CFSG.Open.IsKGroup ↥X)
    (hbig : 2 < (A ⊓ kerMOf M X).relIndex A) :
    (∃ n : ℕ, CFSG.Quasithin.IsPSL 2 2 n (KerQuot M X) ∨
        CFSG.Quasithin.IsSz n (KerQuot M X)) ∧
      CFSG.Quasithin.IsBorelIn (⊤ : Subgroup (KerQuot M X)) (kerQuotImg M X M) := by
  have h5 : Sec5Hyp X M A := h.sec5Hyp hA
  have h' := sec5Hyp_kerQuot h5
  have hM' : maxOver ⊤ (kerQuotImg M X A) = {kerQuotImg M X M} :=
    maxOver_kerQuotImg_of_inf h.A_le h.maxOver_eq
  have hK' := kerMOf_kerQuotImg M X
  have hbot : ¬ kerQuotImg M X A ≤ pCoreOf 2 (⊤ : Subgroup (KerQuot M X)) := by
    rw [pCoreOf_two_eq_bot_of_maxOver_eq_singleton h' hM' hK', le_bot_iff,
      kerQuotImg_eq_bot_iff h.A_le]
    exact h.not_le_ker
  have hcard : Nat.card ↥(kerQuotImg M X A) = (A ⊓ kerMOf M X).relIndex A :=
    card_kerQuotImg h.A_le
  rcases five_five h' hM' hbot hK' with ⟨h2, _, _, _, _⟩ | ⟨L, hLs, hLnab, hFL, _⟩
  · exfalso
    rw [hcard] at h2
    omega
  · have hKq : CFSG.Open.IsKGroup (KerQuot M X) := hK.quotient _
    have hnab' : ∃ a b : ↥L, a * b ≠ b * a := by
      by_contra hcon
      apply hLnab
      intro x hx y hy
      by_contra hne
      exact hcon ⟨⟨x, hx⟩, ⟨y, hy⟩, fun heq => hne (congrArg Subtype.val heq)⟩
    have hcatL : IsCatalogGroup ↥L :=
      hKq.isCatalogGroup_of_surjective L hnab' (MonoidHom.id _) Function.surjective_id
    have hcat : IsCatalogGroup ↥(Fstar (⊤ : Subgroup (KerQuot M X))) := by
      rw [hFL]
      exact hcatL
    have hsimple : IsSimpleGroup ↥(Fstar (⊤ : Subgroup (KerQuot M X))) := by
      rw [hFL]
      exact hLs
    have hnabF : ∃ a b : ↥(Fstar (⊤ : Subgroup (KerQuot M X))), a * b ≠ b * a := by
      rw [hFL]
      exact hnab'
    obtain ⟨⟨n, hn⟩, S, hS, hMS⟩ := hB (⊤ : Subgroup (KerQuot M X))
      (kerQuotImg M X A) (kerQuotImg M X M) hsimple hnabF hcat le_top
      (isElemAbelian_kerQuotImg hA) hM'
    refine ⟨⟨n, ?_⟩, S, ⟨hS.1, hS.2.1, hS.2.2⟩, hMS⟩
    rcases hn with hn | hn
    · exact Or.inl (isL2_iff_isPSL.1 (CFSG.Blueprint.LieModel.of_mulEquiv Subgroup.topEquiv hn))
    · exact Or.inr (isSz_iff_isSz.1 (CFSG.Blueprint.LieModel.of_mulEquiv Subgroup.topEquiv hn))

end CFSG.LocalAnalysis.WeakClosure81
