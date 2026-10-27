module

import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.S3AmalgamBound.MinParRankOne.FaithfulOdd
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.WeakClosure81.EightEightDefs

public section

namespace CFSG.LocalAnalysis.WeakClosure81.Chev2Orbit

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Open Subgroup
open CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound.MinParRankOne

variable {Q : Type} [Group Q] [Finite Q]

omit [Finite Q] in
private theorem normalizer_ne_top_of_ne {L X : Subgroup Q} (hLs : IsSimpleGroup ↥L)
    (hXL : X ≤ L) (hb : X ≠ ⊥) (hl : X ≠ L) :
    Subgroup.normalizer (X : Set Q) ≠ ⊤ := by
  intro htop
  have hXn : (X.subgroupOf L).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hXL, htop]
    exact le_top
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (X.subgroupOf L) with h | h
  · apply hb
    rw [eq_bot_iff]
    intro x hx
    have hx' : (⟨x, hXL hx⟩ : ↥L) ∈ X.subgroupOf L := hx
    rw [h, Subgroup.mem_bot] at hx'
    exact Subgroup.mem_bot.2 (congrArg Subtype.val hx')
  · apply hl
    apply le_antisymm hXL ?_
    intro x hxL
    have hx' : (⟨x, hxL⟩ : ↥L) ∈ X.subgroupOf L := by rw [h]; trivial
    exact hx'

omit [Finite Q] in
private theorem le_normalizer_inf_of_normal {L T : Subgroup Q} (hLn : L.Normal) :
    T ≤ Subgroup.normalizer ((T ⊓ L : Subgroup Q) : Set Q) := by
  intro t ht
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · rintro ⟨hxT, hxL⟩
    exact ⟨T.mul_mem (T.mul_mem ht hxT) (T.inv_mem ht), hLn.conj_mem x hxL t⟩
  · rintro ⟨hxT, hxL⟩
    refine ⟨?_, ?_⟩
    · simpa [mul_assoc] using T.mul_mem (T.mul_mem (T.inv_mem ht) hxT) ht
    · have := hLn.conj_mem (t * x * t⁻¹) hxL t⁻¹
      simpa [mul_assoc] using this

theorem false_of_le {L T M : Subgroup Q} (hLn : L.Normal) (hLs : IsSimpleGroup ↥L)
    (hnab : ∃ a b : ↥L, a * b ≠ b * a) (hT : IsSylowIn 2 T ⊤) (hTL : T ⊓ L ≠ ⊥) (hMt : M < ⊤)
    (hMax : ∀ X : Subgroup Q, T ≤ X → X < ⊤ → X ≤ M) (hLM : L ≤ M) : False := by
  have hT2 : IsSylowTwoOf T ⊤ := ⟨hT.1, hT.2.1, hT.2.2⟩
  have hS : IsSylowTwoOf (T ⊓ L) L :=
    A4.isSylowTwoOf_inf_normal hT2 le_top
      (Subgroup.normalizer_eq_top_iff.mpr hLn).ge
  have hSL : T ⊓ L ≠ L := by
    intro h
    have hLT : L ≤ T := h ▸ inf_le_left
    exact not_isPGroup_of_simple_nonabelian hLs hnab 2 (hT.2.1.to_le hLT)
  have hNne : Subgroup.normalizer ((T ⊓ L : Subgroup Q) : Set Q) ≠ ⊤ :=
    normalizer_ne_top_of_ne hLs inf_le_right hTL hSL
  have hfr : Subgroup.normalizer ((T ⊓ L : Subgroup Q) : Set Q) ⊔ L = ⊤ := by
    have h := Sylow.normalizer_sup_eq_top (G := Q) (N := L) (B6.toSylow2 hS)
    rw [B6.toSylow2_coe hS, Subgroup.map_subgroupOf_eq_of_le inf_le_right] at h
    exact h
  have hNM : Subgroup.normalizer ((T ⊓ L : Subgroup Q) : Set Q) ≤ M :=
    hMax _ (le_normalizer_inf_of_normal hLn) (lt_top_iff_ne_top.2 hNne)
  have htop : (⊤ : Subgroup Q) ≤ M := by
    rw [← hfr]
    exact sup_le hNM hLM
  exact hMt.not_ge htop

theorem false_of_invariant_pair {L T M X₁ X₂ : Subgroup Q} (hLn : L.Normal)
    (hLs : IsSimpleGroup ↥L) (hnab : ∃ a b : ↥L, a * b ≠ b * a) (hT : IsSylowIn 2 T ⊤)
    (hTL : T ⊓ L ≠ ⊥) (hMt : M < ⊤) (hMax : ∀ X : Subgroup Q, T ≤ X → X < ⊤ → X ≤ M)
    (h₁ : X₁ ≤ L) (h₂ : X₂ ≤ L) (hb₁ : X₁ ≠ ⊥) (hb₂ : X₂ ≠ ⊥) (hl₁ : X₁ ≠ L) (hl₂ : X₂ ≠ L)
    (hn₁ : T ≤ normalizer (X₁ : Set Q)) (hn₂ : T ≤ normalizer (X₂ : Set Q))
    (hsup : X₁ ⊔ X₂ = L) : False := by
  have hX₁M : X₁ ≤ M := by
    have hNne : Subgroup.normalizer (X₁ : Set Q) ≠ ⊤ :=
      normalizer_ne_top_of_ne hLs h₁ hb₁ hl₁
    exact (Subgroup.le_normalizer : X₁ ≤ Subgroup.normalizer (X₁ : Set Q)).trans
      (hMax _ hn₁ (lt_top_iff_ne_top.2 hNne))
  have hX₂M : X₂ ≤ M := by
    have hNne : Subgroup.normalizer (X₂ : Set Q) ≠ ⊤ :=
      normalizer_ne_top_of_ne hLs h₂ hb₂ hl₂
    exact (Subgroup.le_normalizer : X₂ ≤ Subgroup.normalizer (X₂ : Set Q)).trans
      (hMax _ hn₂ (lt_top_iff_ne_top.2 hNne))
  have hLM : L ≤ M := by
    rw [← hsup]
    exact sup_le hX₁M hX₂M
  exact false_of_le hLn hLs hnab hT hTL hMt hMax hLM

private theorem map_conj_ne_of_le_inf_normalizer {L T P : Subgroup Q} (hLn : L.Normal)
    (hT : IsSylowIn 2 T ⊤) {t : Q} (ht : t ∈ T) (hPL : P < L)
    (hN : L ⊓ normalizer ((T ⊓ L : Subgroup Q) : Set Q) ≤ P)
    (hne : P.map (MulAut.conj t).toMonoidHom ≠ P) :
    ∀ l ∈ L, conjSubgroup P (t⁻¹ * l) ≠ P := by
  intro l hl hconj
  have hT2 : IsSylowTwoOf T ⊤ := ⟨hT.1, hT.2.1, hT.2.2⟩
  have hS : IsSylowTwoOf (T ⊓ L) L :=
    A4.isSylowTwoOf_inf_normal hT2 le_top
      (Subgroup.normalizer_eq_top_iff.mpr hLn).ge
  have htS : t ∈ Subgroup.normalizer ((T ⊓ L : Subgroup Q) : Set Q) :=
    le_normalizer_inf_of_normal hLn ht
  have hNP' : L ⊓ normalizer ((T ⊓ L : Subgroup Q) : Set Q) ≤
      P.map (MulAut.conj t).toMonoidHom := by
    intro x hx
    have hmapN : (Subgroup.normalizer ((T ⊓ L : Subgroup Q) : Set Q)).map
        (MulAut.conj t⁻¹).toMonoidHom =
        Subgroup.normalizer ((T ⊓ L : Subgroup Q) : Set Q) := by
      rw [Subgroup.map_equiv_normalizer_eq]
      exact congrArg (fun K : Subgroup Q => (Subgroup.normalizer (K : Set Q) : Subgroup Q))
        (Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.inv_mem _ htS))
    have hyN : t⁻¹ * x * t ∈ Subgroup.normalizer ((T ⊓ L : Subgroup Q) : Set Q) := by
      have h := hmapN ▸ Subgroup.mem_map_of_mem (MulAut.conj t⁻¹).toMonoidHom hx.2
      simpa [MulAut.conj_apply] using h
    exact ⟨t⁻¹ * x * t,
      hN ⟨by simpa using hLn.conj_mem x hx.1 t⁻¹, hyN⟩, by
        simp [MulAut.conj_apply, mul_assoc]⟩
  have hSP : T ⊓ L ≤ P := (le_inf inf_le_right Subgroup.le_normalizer).trans hN
  have hSP' : T ⊓ L ≤ P.map (MulAut.conj t).toMonoidHom :=
    (le_inf inf_le_right Subgroup.le_normalizer).trans hNP'
  have hconj' : (P.map (MulAut.conj t).toMonoidHom).map
      (MulAut.conj l⁻¹).toMonoidHom = P := by
    rw [Subgroup.map_map]
    have hcomp : (MulAut.conj l⁻¹).toMonoidHom.comp (MulAut.conj t).toMonoidHom =
        (MulAut.conj (t⁻¹ * l)⁻¹).toMonoidHom := by
      ext x
      simp [MulAut.conj_apply, mul_assoc]
    rw [hcomp]
    exact hconj
  have hleP : (T ⊓ L).map (MulAut.conj l⁻¹).toMonoidHom ≤ P := by
    have h := Subgroup.map_mono (f := (MulAut.conj l⁻¹).toMonoidHom) hSP'
    rwa [hconj'] at h
  have hSylconj : IsSylowTwoOf ((T ⊓ L).map (MulAut.conj l⁻¹).toMonoidHom) L := by
    have h := B6.isSylowTwoOf_conjSub hS l⁻¹
    have hL : B6.conjSub l⁻¹ L = L :=
      B6.conjSub_eq_self (Subgroup.le_normalizer (L.inv_mem hl))
    rwa [hL] at h
  have hSPsyl : IsSylowTwoOf (T ⊓ L) P := A4.isSylowTwoOf_mono hS hSP hPL.le
  have hSP'syl : IsSylowTwoOf ((T ⊓ L).map (MulAut.conj l⁻¹).toMonoidHom) P :=
    A4.isSylowTwoOf_mono hSylconj hleP hPL.le
  obtain ⟨p, hpP, hpconj⟩ := B6.isSylowTwoOf_exists_conj hSPsyl hSP'syl
  have hxN : (l * p)⁻¹ ∈ Subgroup.normalizer ((T ⊓ L : Subgroup Q) : Set Q) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    change B6.conjSub (l * p)⁻¹ (T ⊓ L) = T ⊓ L
    have hpconjB : B6.conjSub l⁻¹ (T ⊓ L) = B6.conjSub p (T ⊓ L) := hpconj
    rw [show (l * p)⁻¹ = p⁻¹ * l⁻¹ by group, B6.conjSub_mul, hpconjB,
      ← B6.conjSub_mul, inv_mul_cancel, B6.conjSub_one]
  have hxL : l * p ∈ L := L.mul_mem hl (hPL.le hpP)
  have hxP' : l * p ∈ P.map (MulAut.conj t).toMonoidHom :=
    hNP' ⟨hxL, by simpa using Subgroup.inv_mem _ hxN⟩
  have hxinv : (l * p)⁻¹ ∈ P.map (MulAut.conj t).toMonoidHom := Subgroup.inv_mem _ hxP'
  have hmapx : B6.conjSub (l * p)⁻¹ (P.map (MulAut.conj t).toMonoidHom) =
      P.map (MulAut.conj t).toMonoidHom :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer hxinv)
  have hmapP : B6.conjSub (l * p)⁻¹ (P.map (MulAut.conj t).toMonoidHom) = P := by
    have hconjB : B6.conjSub l⁻¹ (P.map (MulAut.conj t).toMonoidHom) = P := hconj'
    have hpP' : B6.conjSub p⁻¹ P = P :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp
        (Subgroup.le_normalizer (P.inv_mem hpP))
    rw [show (l * p)⁻¹ = p⁻¹ * l⁻¹ by group, B6.conjSub_mul, hconjB, hpP']
  exact hne (hmapx.symm.trans hmapP)

theorem actsOnDynkinMod_bot_of_swap {L T P : Subgroup Q} (hLn : L.Normal)
    (hT : IsSylowIn 2 T ⊤) {t : Q} (ht : t ∈ T) (hPL : P < L)
    (hmax : ∀ Y : Subgroup Q, P < Y → Y ≤ L → Y = L)
    (hN : L ⊓ normalizer ((T ⊓ L : Subgroup Q) : Set Q) ≤ P)
    (hne : P.map (MulAut.conj t).toMonoidHom ≠ P) : ActsOnDynkinMod ⊥ L t := by
  have htn : t ∈ Subgroup.normalizer (L : Set Q) := by
    rw [Subgroup.normalizer_eq_top_iff.mpr hLn]
    exact Subgroup.mem_top t
  have hT2 : IsSylowTwoOf T ⊤ := ⟨hT.1, hT.2.1, hT.2.2⟩
  have hS : IsSylowTwoOf (T ⊓ L) L :=
    A4.isSylowTwoOf_inf_normal hT2 le_top
      (Subgroup.normalizer_eq_top_iff.mpr hLn).ge
  have hS2 : ∀ s ∈ T ⊓ L, ∃ k : ℕ, s ^ 2 ^ k = 1 := by
    rintro s ⟨hsT, -⟩
    obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp hT.2.1 ⟨s, hsT⟩
    exact ⟨k, by
      rw [← show orderOf s = 2 ^ k by simpa using hk]
      exact pow_orderOf_eq_one s⟩
  have hodd : ¬ 2 ∣ (T ⊓ L).relIndex L := hS.2.2
  refine ⟨htn, P, ⟨bot_le, hPL, hmax, T ⊓ L, bot_le, inf_le_right, ?_, hodd, hN⟩, ?_⟩
  · rintro s ⟨hsT, hsL⟩
    obtain ⟨k, hk⟩ := hS2 s ⟨hsT, hsL⟩
    exact ⟨k, by simpa using hk⟩
  · exact map_conj_ne_of_le_inf_normalizer hLn hT ht hPL hN hne

end CFSG.LocalAnalysis.WeakClosure81.Chev2Orbit
