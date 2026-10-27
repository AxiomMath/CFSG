module

public import CFSG.LocalAnalysis.StandardType.GGIrred937F4Base
public import CFSG.LocalAnalysis.StandardType.GGIrred937F4Count

public section

namespace CFSG.StandardType

namespace Irred937

open CFSG CFSG.Open CFSG.StandardType CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.Torality CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

@[expose] noncomputable def langFixed (L : Type) [Field L] [CharP L 2]
    (f : ℕ) (w₀ : WeylGroup Tag.F4) :
    Subgroup (ModGL Tag.F4 L) :=
  CFSG.RankThree.PartOne.KE.twistedFixedPoints (canonicalRep (coxeterSystem Tag.F4) L w₀)
    (CFSG.LieType.AlgebraicGroups.entrywiseFrobGL Tag.F4 L 2 f)

@[expose] noncomputable def langEmbedding
    {K : Type} [Field K]
    (g : ModGL Tag.F4 (AlgebraicClosure K)) :
    adjointGroup Tag.F4 K →* ModGL Tag.F4 (AlgebraicClosure K) :=
  (MulAut.conj g⁻¹).toMonoidHom.comp
    ((baseChangeGL (algebraMap K (AlgebraicClosure K))).comp (adjointGroup Tag.F4 K).subtype)

theorem mem_langFixed {L : Type} [Field L] [CharP L 2]
    {f : ℕ} {w₀ : WeylGroup Tag.F4} {y : ModGL Tag.F4 L} :
    y ∈ langFixed L f w₀ ↔
      canonicalRep (coxeterSystem Tag.F4) L w₀ *
        CFSG.LieType.AlgebraicGroups.entrywiseFrobGL Tag.F4 L 2 f y *
          (canonicalRep (coxeterSystem Tag.F4) L w₀)⁻¹ = y :=
  Iff.rfl

theorem langEmbedding_injective
    {K : Type} [Field K] (g : ModGL Tag.F4 (AlgebraicClosure K)) :
    Function.Injective (langEmbedding g) :=
  (MulAut.conj g⁻¹).injective.comp
    ((baseChangeGL_injective (algebraMap K (AlgebraicClosure K))).comp Subtype.val_injective)

theorem langEmbedding_mem_of_mem_ggFix
    {K : Type} [Field K] [Finite K] [CharP K 2] {f : ℕ} (hq : Nat.card K = 2 ^ f)
    (w₀ : WeylGroup Tag.F4) (e : adjointGroup Tag.F4 K)
    {g : ModGL Tag.F4 (AlgebraicClosure K)} (hg : g ∈ adjointGroup Tag.F4 (AlgebraicClosure K))
    (hgF : g⁻¹ * CFSG.LieType.AlgebraicGroups.entrywiseFrobGL Tag.F4 (AlgebraicClosure K) 2 f g =
      canonicalRep (coxeterSystem Tag.F4) (AlgebraicClosure K) w₀)
    (a : Fin Tag.F4.rank → (AlgebraicClosure K)ˣ)
    (hga : baseChangeGL (algebraMap K (AlgebraicClosure K)) (e : ModGL Tag.F4 K) =
      g * rootDiagUnit Tag.F4 a * g⁻¹)
    {x : adjointGroup Tag.F4 K} (hx : x ∈ ggFix (MulAut.conj e)) :
    langEmbedding g x ∈
      toralCentralizer Tag.F4 (AlgebraicClosure K) a ⊓ langFixed (AlgebraicClosure K) f w₀:= by
  classical
  have hFrg : CFSG.LieType.AlgebraicGroups.entrywiseFrobGL Tag.F4 (AlgebraicClosure K) 2 f g =
      g * canonicalRep (coxeterSystem Tag.F4) (AlgebraicClosure K) w₀ := by
    rw [← hgF]; group
  have hfix : CFSG.LieType.AlgebraicGroups.entrywiseFrobGL Tag.F4 (AlgebraicClosure K) 2 f
      (baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL Tag.F4 K)) =
      baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL Tag.F4 K) :=
    units_map_entrywiseHom_baseChangeGL_algebraMap (iterateFrobenius (AlgebraicClosure K) 2 f)
      (fun c => by rw [iterateFrobenius_def, hq]) _
  have hxe : (e : ModGL Tag.F4 K) * x = x * e := by
    have h : MulAut.conj e x = x := hx
    rw [MulAut.conj_apply, mul_inv_eq_iff_eq_mul] at h
    exact congrArg Subtype.val h
  have hyd : langEmbedding g x =
      g⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL Tag.F4 K) * g := by
    change (MulAut.conj g⁻¹) (baseChangeGL (algebraMap K (AlgebraicClosure K))
      (x : ModGL Tag.F4 K)) = _
    rw [MulAut.conj_apply, inv_inv]
  have hyG : g⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL Tag.F4 K) * g ∈
      adjointGroup Tag.F4 (AlgebraicClosure K) :=
    (adjointGroup Tag.F4 (AlgebraicClosure K)).mul_mem
      ((adjointGroup Tag.F4 (AlgebraicClosure K)).mul_mem
        ((adjointGroup Tag.F4 (AlgebraicClosure K)).inv_mem hg)
        (CFSG.LieType.Chevalley.baseChangeGL_mem_adjointGroup _ x.2)) hg
  have hcomm : rootDiagUnit Tag.F4 a * (g⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
      (x : ModGL Tag.F4 K) * g) = (g⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
      (x : ModGL Tag.F4 K) * g) * rootDiagUnit Tag.F4 a := by
    have hd' : rootDiagUnit Tag.F4 a = g⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
        (e : ModGL Tag.F4 K) * g := by rw [hga]; group
    have hc : baseChangeGL (algebraMap K (AlgebraicClosure K)) (e : ModGL Tag.F4 K) *
        baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL Tag.F4 K) =
        baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL Tag.F4 K) *
        baseChangeGL (algebraMap K (AlgebraicClosure K)) (e : ModGL Tag.F4 K) := by
      rw [← map_mul, ← map_mul, hxe]
    rw [hd']
    calc g⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (e : ModGL Tag.F4 K) * g *
          (g⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL Tag.F4 K) * g)
        = g⁻¹ * (baseChangeGL (algebraMap K (AlgebraicClosure K)) (e : ModGL Tag.F4 K) *
            baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL Tag.F4 K)) * g := by group
      _ = g⁻¹ * (baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL Tag.F4 K) *
            baseChangeGL (algebraMap K (AlgebraicClosure K)) (e : ModGL Tag.F4 K)) * g := by
          rw [hc]
      _ = g⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL Tag.F4 K) * g *
          (g⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (e : ModGL Tag.F4 K) * g) := by
          group
  rw [hyd, Subgroup.mem_inf]
  refine ⟨?_, ?_⟩
  · rw [toralCentralizer, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
    refine ⟨hyG, ?_⟩
    first
      | exact hcomm
      | exact hcomm.symm
  · rw [mem_langFixed]
    rw [map_mul, map_mul, map_inv, hfix, hFrg]
    group

theorem exists_mem_ggFix_langEmbedding_eq
    {K : Type} [Field K] [Finite K] [CharP K 2] {f : ℕ} (hq : Nat.card K = 2 ^ f)
    (w₀ : WeylGroup Tag.F4) (e : adjointGroup Tag.F4 K)
    {g : ModGL Tag.F4 (AlgebraicClosure K)} (hg : g ∈ adjointGroup Tag.F4 (AlgebraicClosure K))
    (hgF : g⁻¹ * CFSG.LieType.AlgebraicGroups.entrywiseFrobGL Tag.F4 (AlgebraicClosure K) 2 f g =
      canonicalRep (coxeterSystem Tag.F4) (AlgebraicClosure K) w₀)
    (a : Fin Tag.F4.rank → (AlgebraicClosure K)ˣ)
    (hga : baseChangeGL (algebraMap K (AlgebraicClosure K)) (e : ModGL Tag.F4 K) =
      g * rootDiagUnit Tag.F4 a * g⁻¹)
    {y : ModGL Tag.F4 (AlgebraicClosure K)}
    (hy : y ∈ toralCentralizer Tag.F4 (AlgebraicClosure K) a ⊓
      langFixed (AlgebraicClosure K) f w₀) :
    ∃ x ∈ ggFix (MulAut.conj e), langEmbedding g x = y:= by
  classical
  obtain ⟨hyM, hyS⟩ := Subgroup.mem_inf.1 hy
  rw [toralCentralizer, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff] at hyM
  obtain ⟨hyG, hyd⟩ := hyM
  rw [mem_langFixed] at hyS
  have hFrg : CFSG.LieType.AlgebraicGroups.entrywiseFrobGL Tag.F4 (AlgebraicClosure K) 2 f g =
      g * canonicalRep (coxeterSystem Tag.F4) (AlgebraicClosure K) w₀ := by
    rw [← hgF]; group
  have hzG : g * y * g⁻¹ ∈ adjointGroup Tag.F4 (AlgebraicClosure K) :=
    (adjointGroup Tag.F4 (AlgebraicClosure K)).mul_mem
      ((adjointGroup Tag.F4 (AlgebraicClosure K)).mul_mem hg hyG)
      ((adjointGroup Tag.F4 (AlgebraicClosure K)).inv_mem hg)
  have hzF : Units.map (entrywiseHom (iterateFrobenius (AlgebraicClosure K) 2 f))
      (g * y * g⁻¹) = g * y * g⁻¹ := by
    have h1 : CFSG.LieType.AlgebraicGroups.entrywiseFrobGL Tag.F4 (AlgebraicClosure K) 2 f
        (g * y * g⁻¹) = g * y * g⁻¹ := by
      rw [map_mul, map_mul, map_inv, hFrg]
      calc g * canonicalRep (coxeterSystem Tag.F4) (AlgebraicClosure K) w₀ *
            CFSG.LieType.AlgebraicGroups.entrywiseFrobGL Tag.F4 (AlgebraicClosure K) 2 f y *
            (g * canonicalRep (coxeterSystem Tag.F4) (AlgebraicClosure K) w₀)⁻¹
          = g * (canonicalRep (coxeterSystem Tag.F4) (AlgebraicClosure K) w₀ *
            CFSG.LieType.AlgebraicGroups.entrywiseFrobGL Tag.F4 (AlgebraicClosure K) 2 f y *
            (canonicalRep (coxeterSystem Tag.F4) (AlgebraicClosure K) w₀)⁻¹) * g⁻¹ := by group
        _ = g * y * g⁻¹ := by rw [hyS]
    exact h1
  obtain ⟨c, hc⟩ := f4_exists_rational_of_fixed (K := K) (L := AlgebraicClosure K)
    (iterateFrobenius (AlgebraicClosure K) 2 f) (fun c => by rw [iterateFrobenius_def, hq])
    hzG hzF
  refine ⟨c, ?_, ?_⟩
  · show MulAut.conj e c = c
    apply Subtype.ext
    apply baseChangeGL_injective (algebraMap K (AlgebraicClosure K))
    have hd' : baseChangeGL (algebraMap K (AlgebraicClosure K)) (c : ModGL Tag.F4 K) =
        g * y * g⁻¹ := hc
    change baseChangeGL (algebraMap K (AlgebraicClosure K))
      ((e : ModGL Tag.F4 K) * (c : ModGL Tag.F4 K) * (e : ModGL Tag.F4 K)⁻¹) = _
    rw [map_mul, map_mul, map_inv, hga, hd']
    have hyd' : rootDiagUnit Tag.F4 a * y = y * rootDiagUnit Tag.F4 a := hyd.symm
    calc g * rootDiagUnit Tag.F4 a * g⁻¹ * (g * y * g⁻¹) * (g * rootDiagUnit Tag.F4 a * g⁻¹)⁻¹
        = g * (rootDiagUnit Tag.F4 a * y * (rootDiagUnit Tag.F4 a)⁻¹) * g⁻¹ := by group
      _ = g * y * g⁻¹ := by rw [hyd']; group
  · change (MulAut.conj g⁻¹) (baseChangeGL (algebraMap K (AlgebraicClosure K))
      (c : ModGL Tag.F4 K)) = y
    rw [hc, MulAut.conj_apply]
    group

theorem map_ggFix_langEmbedding
    {K : Type} [Field K] [Finite K] [CharP K 2] {f : ℕ} (hq : Nat.card K = 2 ^ f)
    (w₀ : WeylGroup Tag.F4) (e : adjointGroup Tag.F4 K)
    {g : ModGL Tag.F4 (AlgebraicClosure K)} (hg : g ∈ adjointGroup Tag.F4 (AlgebraicClosure K))
    (hgF : g⁻¹ * CFSG.LieType.AlgebraicGroups.entrywiseFrobGL Tag.F4 (AlgebraicClosure K) 2 f g =
      canonicalRep (coxeterSystem Tag.F4) (AlgebraicClosure K) w₀)
    (a : Fin Tag.F4.rank → (AlgebraicClosure K)ˣ)
    (hga : baseChangeGL (algebraMap K (AlgebraicClosure K)) (e : ModGL Tag.F4 K) =
      g * rootDiagUnit Tag.F4 a * g⁻¹) :
    (ggFix (MulAut.conj e)).map (langEmbedding g) =
      toralCentralizer Tag.F4 (AlgebraicClosure K) a ⊓ langFixed (AlgebraicClosure K) f w₀:= by
  ext y
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact langEmbedding_mem_of_mem_ggFix hq w₀ e hg hgF a hga hx
  · intro hy
    exact exists_mem_ggFix_langEmbedding_eq hq w₀ e hg hgF a hga hy

theorem exists_map_ggFix_langEmbedding
    {K : Type} [Field K] [Finite K] [CharP K 2] {f : ℕ} (hf : 1 ≤ f) (hq : Nat.card K = 2 ^ f)
    (h3q : 3 ∣ Nat.card K + 1) (w₀ : WeylGroup Tag.F4)
    (hw₀ : ∀ v : Fin Tag.F4.rank → ℤ, w₀ • v = -v) (e : adjointGroup Tag.F4 K)
    {g : ModGL Tag.F4 (AlgebraicClosure K)} (hg : g ∈ adjointGroup Tag.F4 (AlgebraicClosure K))
    (a : Fin Tag.F4.rank → (AlgebraicClosure K)ˣ) (ha : ∀ i, a i ^ 3 = 1)
    (hga : baseChangeGL (algebraMap K (AlgebraicClosure K)) (e : ModGL Tag.F4 K) =
      g * rootDiagUnit Tag.F4 a * g⁻¹) :
    ∃ g' ∈ adjointGroup Tag.F4 (AlgebraicClosure K),
      (ggFix (MulAut.conj e)).map (langEmbedding g') =
        toralCentralizer Tag.F4 (AlgebraicClosure K) a ⊓ langFixed (AlgebraicClosure K) f w₀:= by
  obtain ⟨g', hg', hga', hgF⟩ := exists_lang_w0_F4_three hq hf h3q w₀ hw₀ e hg a ha hga
  exact ⟨g', hg', map_ggFix_langEmbedding hq w₀ e hg' hgF a hga'⟩

end Irred937

end CFSG.StandardType

end
