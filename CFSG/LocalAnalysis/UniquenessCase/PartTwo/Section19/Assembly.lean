module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.NineteenGlueSix
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.CtxLemmas

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.UC22.F10 (LieAutVocab10)
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem sec19_false_at (D : Data G) (hσ : D.sig.Nonempty) {V₀ Vsub : Subgroup G}
    (h125 : Hyp125 D V₀ Vsub) (hbig : 1 < mSub V₀)
    (hglue1 : R19_glue_1At D V₀ Vsub h125 hbig hσ)
    (h10 : ∀ p L (h : Hyp19 D V₀ Vsub p L), R19_10At D V₀ Vsub p L h)
    (hglue4 : ∀ p L (h : Hyp19 D V₀ Vsub p L) (h1910 : Setting1910 D V₀ Vsub p L),
      R19_glue_4At D V₀ Vsub p L h h1910)
    (h22 : ∀ p L A t B r (h : Ctx19_10 D V₀ Vsub p L A t B r),
      R19_22At D V₀ Vsub p L A t B r h)
    (h23 : ∀ p L A t B r A₀ (h : Ctx19_22 D V₀ Vsub p L A t B r A₀),
      R19_23At D V₀ Vsub p L A t B r A₀ h)
    (V : LieAutVocab10)
    (h29 : ∀ p L A t B r A₀ H E K S (h : Ctx19_23 D V₀ Vsub p L A t B r A₀ H),
      R19_29At V D V₀ Vsub p L A t B r A₀ H E K S h)
    (hglue7 : ∀ p L A t B r A₀ H E K S (h : Ctx19_23 D V₀ Vsub p L A t B r A₀ H)
      (hE : E ≤ A) (hEel : IsElemAbelian r E) (hEcard : Nat.card E = r ^ 2)
      (hK : K ≤ H) (hKcomp : CFSG.IsComponent (K.subgroupOf H))
      (hfaith : ActsFaithfullyOn V₀ K) (hS : CFSG.ABGLocalTools.IsSylowOf 2 S (H ⊓ D.M))
      (h29 : P19_29 V K E A₀ S),
      R19_glue_7At V D V₀ Vsub p L A t B r A₀ H E K S h hE hEel hEcard hK hKcomp hfaith hS h29) :
    False := by
  classical
  have hglue6 : R19_glue_6 D := nineteen_glue_six_closed D
  obtain ⟨p, L, h19⟩ := hglue1
  have h1910 : Setting1910 D V₀ Vsub p L := h10 p L h19
  obtain ⟨A, t, B, r, hctx10⟩ := hglue4 p L h19 h1910
  obtain ⟨A₀, hctx22⟩ := h22 p L A t B r hctx10
  let H : Subgroup G := centralizer (A₀ : Set G)
  have hO2 : pCoreOf 2 H = ⊥ := h23 p L A t B r A₀ hctx22
  let hctx23 : Ctx19_23 D V₀ Vsub p L A t B r A₀ H := ⟨hctx22, rfl, hO2⟩
  obtain ⟨K, hKH, hKcomp, hfaith⟩ := hglue6 V₀ Vsub p L A t B r A₀ H hctx23
  have hr : r.Prime := hctx10.hr.1
  obtain ⟨E, hEA, hEel, hEcard⟩ :=
    exists_isElemAbelian_card_prime_sq_of_isZModSq hctx10.hAcard hr hctx10.hr.2
  obtain ⟨S, hS⟩ := CFSG.ABGLocalTools.exists_isSylowOf 2 (H ⊓ D.M)
  have h29' : P19_29 V K E A₀ S :=
    h29 p L A t B r A₀ H E K S hctx23 hEA hEel hEcard hKH hKcomp hfaith hS
  exact hglue7 p L A t B r A₀ H E K S hctx23 hEA hEel hEcard hKH hKcomp hfaith hS h29'

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19
