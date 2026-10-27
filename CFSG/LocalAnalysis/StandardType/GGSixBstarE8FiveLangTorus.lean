module

public import CFSG.LocalAnalysis.StandardType.GGSixBstarE8FiveLangRational
public import CFSG.LocalAnalysis.StandardType.GGSixBstarE8FiveLangTorusOrder
public import CFSG.LocalAnalysis.StandardType.GGSixBstarE8FiveFrameCentralizer
public import CFSG.RankThree.PartOne.KE.A1Weyl

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.PartOne.KE
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

namespace NoOffE8Five

local instance noOffE8FiveFactFiveLT : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩

local instance noOffE8FiveNeZeroRankLT : NeZero Tag.E8.rank := ⟨by decide⟩

section LangTorus

variable {K L : Type} [Field K] [Field L] [Algebra K L]

@[expose] noncomputable def langPhi (K : Type) [Field K] [Algebra K L] (g₀ : ModGL Tag.E8 L) :
    adjointGroup Tag.E8 K →* ModGL Tag.E8 L :=
  (MulAut.conj g₀⁻¹).toMonoidHom.comp (adjEmb Tag.E8 K L)

theorem langPhi_apply (g₀ : ModGL Tag.E8 L) (y : adjointGroup Tag.E8 K) :
    langPhi K g₀ y = g₀⁻¹ * adjEmb Tag.E8 K L y * g₀ := by
  simp [langPhi, MulAut.conj_apply]

theorem langPhi_injective (g₀ : ModGL Tag.E8 L) : Function.Injective (langPhi (L := L) K g₀) :=
  (MulAut.conj g₀⁻¹).injective.comp adjEmb_injective

theorem adjEmb_eq_conj_langPhi (g₀ : ModGL Tag.E8 L) (y : adjointGroup Tag.E8 K) :
    adjEmb Tag.E8 K L y = g₀ * langPhi K g₀ y * g₀⁻¹ := by
  rw [langPhi_apply]
  group

@[expose] noncomputable def langTorusRat (K : Type) [Field K] [Algebra K L] (Fr : L →+* L)
    (g₀ : ModGL Tag.E8 L) : Subgroup (adjointGroup Tag.E8 K) :=
  (twistedTorus (canonicalRep (coxeterSystem Tag.E8) L NoOffRest.weylE8W) Fr).comap
    (langPhi K g₀)

theorem mem_langTorusRat {Fr : L →+* L} {g₀ : ModGL Tag.E8 L} {y : adjointGroup Tag.E8 K} :
    y ∈ langTorusRat K Fr g₀ ↔
      langPhi K g₀ y ∈ twistedTorus (canonicalRep (coxeterSystem Tag.E8) L NoOffRest.weylE8W) Fr :=
  Iff.rfl

theorem langTorusRat_comm {Fr : L →+* L} {g₀ : ModGL Tag.E8 L} {x y : adjointGroup Tag.E8 K}
    (hx : x ∈ langTorusRat K Fr g₀) (hy : y ∈ langTorusRat K Fr g₀) : x * y = y * x := by
  apply langPhi_injective (K := K) (L := L) g₀
  rw [map_mul, map_mul]
  exact torusGroup_comm (mem_twistedTorus.1 hx).1 (mem_twistedTorus.1 hy).1

end LangTorus

section LangTorusFacts

variable {K L : Type} [Field K] [Finite K] [Field L] [Algebra K L] [Algebra.IsAlgebraic K L]

theorem card_langTorusRat [IsAlgClosed L] {ℓ : ℕ} [Fact ℓ.Prime] [CharP L ℓ] {Fr : L →+* L}
    (hFr : ∀ c, Fr c = c ^ Nat.card K) (hℓK : ℓ ∣ Nat.card K) {g₀ : ModGL Tag.E8 L}
    (hg₀C : g₀ ∈ adjointGroup Tag.E8 L)
    (hg₀ : Units.map (entrywiseHom Fr) g₀ =
      g₀ * canonicalRep (coxeterSystem Tag.E8) L NoOffRest.weylE8W) :
    Nat.card (langTorusRat K Fr g₀) = (Nat.card K * Nat.card K + 1) ^ 4 := by
  have hle : twistedTorus (canonicalRep (coxeterSystem Tag.E8) L NoOffRest.weylE8W) Fr ≤
      (langPhi K g₀).range := by
    intro x hx
    obtain ⟨y, hy⟩ := conj_mem_adjEmb_range_of_mem_twistedTorus hFr hℓK hg₀C hg₀ hx
    refine ⟨y, ?_⟩
    rw [langPhi_apply, hy]
    group
  have h1 : Nat.card ((langTorusRat K Fr g₀).map (langPhi K g₀)) =
      Nat.card (langTorusRat K Fr g₀) :=
    Subgroup.card_map_of_injective (langPhi_injective (K := K) (L := L) g₀)
  have h2 : (langTorusRat K Fr g₀).map (langPhi K g₀) =
      twistedTorus (canonicalRep (coxeterSystem Tag.E8) L NoOffRest.weylE8W) Fr :=
    Subgroup.map_comap_eq_self hle
  rw [← h1, h2]
  exact natCard_twistedTorus_E8W (L := L) (ℓ := ℓ) (Fr := Fr) (q := Nat.card K) hFr hℓK

theorem mem_langTorusRat_of_commute {Fr : L →+* L} (hFr : ∀ c, Fr c = c ^ Nat.card K) {ζ : Lˣ}
    (hζo : orderOf ζ = 5) (hζ : ζ ^ 5 = 1) {lam : ZMod 5} (hlam : lam * lam = -1)
    {g₀ : ModGL Tag.E8 L} (hg₀C : g₀ ∈ adjointGroup Tag.E8 L)
    (hg₀ : Units.map (entrywiseHom Fr) g₀ =
      g₀ * canonicalRep (coxeterSystem Tag.E8) L NoOffRest.weylE8W)
    {y : adjointGroup Tag.E8 K}
    (hcomm : ∀ s ∈ NoOffRest.eigE8 5 lam,
      Commute (adjEmb Tag.E8 K L y)
        (g₀ * ExcFrames.frameDiag (τ := Tag.E8) ζ hζ s * g₀⁻¹)) :
    y ∈ langTorusRat K Fr g₀ := by
  have hzC : langPhi K g₀ y ∈ adjointGroup Tag.E8 L := by
    rw [langPhi_apply]
    exact mul_mem (mul_mem (inv_mem hg₀C) (adjEmb_mem y)) hg₀C
  have hzT : langPhi K g₀ y ∈ torusGroup Tag.E8 L := by
    refine mem_torusGroup_of_commute_frameDiag hζo hζ hlam hzC fun s hs => ?_
    have h := (hcomm s hs).eq
    rw [langPhi_apply]
    show g₀⁻¹ * adjEmb Tag.E8 K L y * g₀ * ExcFrames.frameDiag (τ := Tag.E8) ζ hζ s =
      ExcFrames.frameDiag (τ := Tag.E8) ζ hζ s * (g₀⁻¹ * adjEmb Tag.E8 K L y * g₀)
    calc g₀⁻¹ * adjEmb Tag.E8 K L y * g₀ * ExcFrames.frameDiag (τ := Tag.E8) ζ hζ s
        = g₀⁻¹ * (adjEmb Tag.E8 K L y *
            (g₀ * ExcFrames.frameDiag (τ := Tag.E8) ζ hζ s * g₀⁻¹)) * g₀ := by group
      _ = g₀⁻¹ * ((g₀ * ExcFrames.frameDiag (τ := Tag.E8) ζ hζ s * g₀⁻¹) *
            adjEmb Tag.E8 K L y) * g₀ := by rw [h]
      _ = ExcFrames.frameDiag (τ := Tag.E8) ζ hζ s * (g₀⁻¹ * adjEmb Tag.E8 K L y * g₀) := by
          group
  refine mem_langTorusRat.2 (mem_twistedTorus.2 ⟨hzT, ?_⟩)
  rw [langPhi_apply, map_mul, map_mul, map_inv, hg₀, adjEmb_frobenius Fr hFr y]
  group

theorem exists_centE8W_conj_of_langTorsion {ζ : Lˣ} (hζo : orderOf ζ = 5) (hζ : ζ ^ 5 = 1)
    {lam : ZMod 5} (hlam : lam * lam = -1) {g₀ : ModGL Tag.E8 L}
    (hg₀C : g₀ ∈ adjointGroup Tag.E8 L)
    {ι : Multiplicative (NoOffRest.eigE8 5 lam) →* adjointGroup Tag.E8 K}
    (hι : ∀ s : NoOffRest.eigE8 5 lam, adjEmb Tag.E8 K L (ι (Multiplicative.ofAdd s)) =
      g₀ * frameElt ζ hζ lam (Multiplicative.ofAdd s) * g₀⁻¹)
    {a : adjointGroup Tag.E8 K}
    (ha : ∀ s : NoOffRest.eigE8 5 lam, ∃ t : NoOffRest.eigE8 5 lam,
      a * ι (Multiplicative.ofAdd s) * a⁻¹ = ι (Multiplicative.ofAdd t)) :
    ∃ u : NoOffRest.centE8W, ∀ s : NoOffRest.eigE8 5 lam,
      a * ι (Multiplicative.ofAdd s) * a⁻¹ =
        ι (Multiplicative.ofAdd (NoOffRest.eigPerm 5 lam u s)) := by
  have hgC : g₀⁻¹ * adjEmb Tag.E8 K L a * g₀ ∈ adjointGroup Tag.E8 L :=
    mul_mem (mul_mem (inv_mem hg₀C) (adjEmb_mem a)) hg₀C
  have key : ∀ s t : NoOffRest.eigE8 5 lam,
      a * ι (Multiplicative.ofAdd s) * a⁻¹ = ι (Multiplicative.ofAdd t) →
        g₀⁻¹ * adjEmb Tag.E8 K L a * g₀ *
            ExcFrames.frameDiag (τ := Tag.E8) ζ hζ (s : Fin Tag.E8.rank → ZMod 5) *
            (g₀⁻¹ * adjEmb Tag.E8 K L a * g₀)⁻¹ =
          ExcFrames.frameDiag (τ := Tag.E8) ζ hζ (t : Fin Tag.E8.rank → ZMod 5) := by
    intro s t h
    have h1 := congrArg (adjEmb Tag.E8 K L) h
    rw [map_mul, map_mul, map_inv, hι s, hι t, frameElt_apply, frameElt_apply] at h1
    calc g₀⁻¹ * adjEmb Tag.E8 K L a * g₀ *
            ExcFrames.frameDiag (τ := Tag.E8) ζ hζ (s : Fin Tag.E8.rank → ZMod 5) *
            (g₀⁻¹ * adjEmb Tag.E8 K L a * g₀)⁻¹
        = g₀⁻¹ * (adjEmb Tag.E8 K L a *
            (g₀ * ExcFrames.frameDiag (τ := Tag.E8) ζ hζ (s : Fin Tag.E8.rank → ZMod 5) * g₀⁻¹) *
            (adjEmb Tag.E8 K L a)⁻¹) * g₀ := by group
      _ = ExcFrames.frameDiag (τ := Tag.E8) ζ hζ (t : Fin Tag.E8.rank → ZMod 5) := by
          rw [h1]; group
  obtain ⟨u, hu⟩ := exists_centE8W_conj_frameDiag hζo hζ hlam hgC (fun s hs => by
    obtain ⟨t, ht⟩ := ha ⟨s, hs⟩
    exact ⟨t, t.2, key ⟨s, hs⟩ t ht⟩)
  refine ⟨u, fun s => ?_⟩
  apply adjEmb_injective (K := K) (L := L) (τ := Tag.E8)
  rw [map_mul, map_mul, map_inv, hι s, hι (NoOffRest.eigPerm 5 lam u s), frameElt_apply,
    frameElt_apply]
  have h2 := hu s
  calc adjEmb Tag.E8 K L a *
        (g₀ * ExcFrames.frameDiag (τ := Tag.E8) ζ hζ (s : Fin Tag.E8.rank → ZMod 5) * g₀⁻¹) *
        (adjEmb Tag.E8 K L a)⁻¹
      = g₀ * (g₀⁻¹ * adjEmb Tag.E8 K L a * g₀ *
            ExcFrames.frameDiag (τ := Tag.E8) ζ hζ (s : Fin Tag.E8.rank → ZMod 5) *
            (g₀⁻¹ * adjEmb Tag.E8 K L a * g₀)⁻¹) * g₀⁻¹ := by group
    _ = g₀ * ExcFrames.frameDiag (τ := Tag.E8) ζ hζ
          ((NoOffRest.eigPerm 5 lam u s : NoOffRest.eigE8 5 lam) : Fin Tag.E8.rank → ZMod 5) *
          g₀⁻¹ := by rw [h2]

end LangTorusFacts

end NoOffE8Five

end CFSG.StandardType
