module

public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutTrialityBridge
public import CFSG.RankThree.PartOne.KE.CTStatement
public import CFSG.RankThree.Lattice.SteinbergBIChecks
public import CFSG.LieType.Chevalley.HeightSeries

public section

namespace CFSG.StandardType.TriBridge

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Universal.Spin
  CFSG.RankThree.Lattice CFSG.RankThree.PartOne.KE CFSG.StandardType.Triality

@[expose] def d4NegWord : List (Fin Tag.D4.rank) := [0, 1, 3, 2, 0, 1, 3, 2, 0, 1, 3, 2]

@[expose] def d4NegMat : List (List ℤ) :=
  [[-1, 0, 0, 0], [0, -1, 0, 0], [0, 0, -1, 0], [0, 0, 0, -1]]

theorem d4NegWord_wordMat : wordMat Tag.D4 d4NegWord = toMat Tag.D4.rank d4NegMat :=
  wordMat_eq_toMat Tag.D4 _ (by decide +kernel)

theorem toMat_d4NegMat : toMat Tag.D4.rank d4NegMat = -1 := by decide +kernel

theorem exists_weyl_neg_D4 :
    ∃ w : WeylGroup Tag.D4, ∀ u : Fin Tag.D4.rank → ℤ, w • u = -u := by
  obtain ⟨w, hw⟩ := IsWeylMatrix.of_word Tag.D4 d4NegWord
  exact ⟨w, fun u => by
    rw [hw, d4NegWord_wordMat, toMat_d4NegMat, Matrix.neg_mulVec, Matrix.one_mulVec]⟩

theorem bLinv_sign_check : ∀ k < Tag.D4.rootCertificate.roots.length,
    (0 < height (Tag.D4.rootCertificate.root k) →
      0 ≤ toStdD 4 (bLinv0 (Tag.D4.rootCertificate.root k)) 1) ∧
    (height (Tag.D4.rootCertificate.root k) < 0 →
      toStdD 4 (bLinv0 (Tag.D4.rootCertificate.root k)) 1 ≤ 0) := by
  decide

theorem zero_le_toStdD_bLinv_one {β : Fin TwistTag.D4.tag.rank → ℤ}
    (hβ : IsRoot TwistTag.D4.tag β) (h : 0 < height β) : 0 ≤ toStdD 4 (bLinv β) 1 := by
  obtain ⟨k, hk, rfl⟩ :=
    (RootCertificate.isRoot_iff (Tag.rootCertificate_check Tag.D4)).1 hβ
  exact (bLinv_sign_check k hk).1 h

theorem toStdD_bLinv_one_nonpos {β : Fin TwistTag.D4.tag.rank → ℤ}
    (hβ : IsRoot TwistTag.D4.tag β) (h : height β < 0) : toStdD 4 (bLinv β) 1 ≤ 0 := by
  obtain ⟨k, hk, rfl⟩ :=
    (RootCertificate.isRoot_iff (Tag.rootCertificate_check Tag.D4)).1 hβ
  exact (bLinv_sign_check k hk).2 h

theorem height_bL_negOne {k : Fin 4} (hk : k ≠ 1) (r : Bool) :
    height (bL (fromStd (lv k 1 r false))) < 0 := by
  revert k r
  decide

theorem mem_of_mem_rootSpan_of_forall_pinnedX {τ : Tag}
    {K : Type} [Field K] {S : Set (Fin τ.rank → ℤ)} {H : Subgroup (adjointGroup τ K)}
    (h : ∀ γ ∈ S, ∀ c : K,
      (⟨pinnedX τ K γ c, pinnedX_mem_adjointGroup _ _⟩ : adjointGroup τ K) ∈ H)
    {u : adjointGroup τ K} (hu : (u : ModGL τ K) ∈ rootSpan τ K S) : u ∈ H := by
  have hle : rootSpan τ K S ≤ H.map (adjointGroup τ K).subtype := by
    rw [rootSpan_eq_closure, Subgroup.closure_le]
    rintro _ ⟨β, hβ, d, rfl⟩
    exact ⟨_, h β hβ d, rfl⟩
  obtain ⟨x, hx, hxu⟩ := hle hu
  rwa [show u = x from Subtype.ext hxu.symm]

end CFSG.StandardType.TriBridge

end
