module

public import CFSG.RankThree.Chevalley.SteinbergCEF4EvenQPlusTorus
public import CFSG.LieType.Chevalley.OrthogonalFixedOrbitMaps

public noncomputable section

namespace CFSG.RankThree.Chevalley

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.ComponentClassification.UnbalancedCatalog CFSG.Timmesfeld.ExceptionalOrders
  CFSG.RankThree.QuadraticSL2 CFSG.RankThree.Classical CFSG.LieType.Steinberg.Adjoint F4Weyl
  EvenG2 EvenF4QPlus CFSG.RankThree.E6
open scoped Pointwise

namespace EvenF4QPlus

section CharTwo

variable {τ : Tag} {M : Type} [Field M] [CharP M 2]

theorem weylElt_mul_canonicalRep_of_charTwo
    (i : Fin τ.rank) (w : WeylGroup τ) :
    weylElt τ M i 1 * canonicalRep (coxeterSystem τ) M w =
      canonicalRep (coxeterSystem τ) M ((coxeterSystem τ).simple i * w) := by
  rw [weylElt_mul_canonicalRep]
  split_ifs
  · rfl
  · rw [show (-1 : Mˣ) = 1 from Units.ext (CharTwo.neg_eq (1 : M)), torusElt_one, one_mul]

theorem canonicalRep_wordProd_mul_of_charTwo
    (ω : List (Fin τ.rank)) (v : WeylGroup τ) :
    canonicalRep (coxeterSystem τ) M ((coxeterSystem τ).wordProd ω * v) =
      (ω.map fun i => weylElt τ M i 1).prod * canonicalRep (coxeterSystem τ) M v := by
  induction ω with
  | nil => rw [CoxeterSystem.wordProd_nil, one_mul, List.map_nil, List.prod_nil, one_mul]
  | cons i ω ih =>
    rw [CoxeterSystem.wordProd_cons, mul_assoc, ← weylElt_mul_canonicalRep_of_charTwo, ih,
      List.map_cons, List.prod_cons, mul_assoc]

theorem canonicalRep_wordProd_of_charTwo
    (ω : List (Fin τ.rank)) :
    canonicalRep (coxeterSystem τ) M ((coxeterSystem τ).wordProd ω) =
      (ω.map fun i => weylElt τ M i 1).prod := by
  have h := canonicalRep_wordProd_mul_of_charTwo (M := M) ω 1
  rwa [mul_one, canonicalRep_one, mul_one] at h

theorem canonicalRep_mul_of_charTwo
    (w v : WeylGroup τ) :
    canonicalRep (coxeterSystem τ) M (w * v) =
      canonicalRep (coxeterSystem τ) M w * canonicalRep (coxeterSystem τ) M v := by
  obtain ⟨ω, -, rfl⟩ := (coxeterSystem τ).exists_isReduced w
  rw [canonicalRep_wordProd_mul_of_charTwo, canonicalRep_wordProd_of_charTwo]

theorem canonicalRep_inv_of_charTwo
    (w : WeylGroup τ) :
    (canonicalRep (coxeterSystem τ) M w)⁻¹ = canonicalRep (coxeterSystem τ) M w⁻¹ := by
  rw [inv_eq_iff_mul_eq_one, ← canonicalRep_mul_of_charTwo, mul_inv_cancel, canonicalRep_one]

theorem canonicalRep_injective
    (τ : Tag) (M : Type) [Field M] :
    Function.Injective (canonicalRep (coxeterSystem τ) M) := by
  intro w v h
  have hw := weylQuotientHom_eq (g := ⟨_, canonicalRep_mem_monomialSubgroup M w⟩)
    (mapsRootLines_canonicalRep (R := M) w)
  have hv := weylQuotientHom_eq (g := ⟨_, canonicalRep_mem_monomialSubgroup M v⟩)
    (mapsRootLines_canonicalRep (R := M) v)
  have e : (⟨_, canonicalRep_mem_monomialSubgroup M w⟩ : monomialSubgroup τ M) =
      ⟨_, canonicalRep_mem_monomialSubgroup M v⟩ := Subtype.ext h
  rw [← hw, ← hv, e]

theorem rootWeylSL2_one_eq_canonicalRep_of_charTwo
    {α : Fin τ.rank → ℤ} (hα : IsRoot τ α) :
    rootWeylSL2 τ M α 1 = canonicalRep (coxeterSystem τ) M (rootReflection α) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, h10, -⟩ := exceptional_Lang_root_rank_one_data τ M α
  have hW : pinnedWeyl τ M α =
      canonicalRep (coxeterSystem τ) M ((coxeterSystem τ).wordProd (pinnedWord τ α)) := by
    rw [pinnedWeyl_eq_list_prod, canonicalRep_wordProd_of_charTwo]
  rw [h10, hW, ← canonicalRep_simple (coxeterSystem τ) (R := M), canonicalRep_inv_of_charTwo,
    ← canonicalRep_mul_of_charTwo, ← canonicalRep_mul_of_charTwo,
    rootReflection_eq_conj (wordProd_pinnedWord_smul hα)]

end CharTwo

@[expose] def negOneF4 : WeylGroup .F4 :=
  rootReflection (qplusRoot 0) * rootReflection (qplusRoot 1) * rootReflection (qplusRoot 2) *
    rootReflection (qplusRoot 3)

theorem negOneF4_smul
    (v : Fin Tag.F4.rank → ℤ) : negOneF4 • v = -v :=
  rootReflection_qplusRoot_prod_smul v

theorem eq_negOneF4
    {w : WeylGroup .F4} (hw : ∀ v : Fin Tag.F4.rank → ℤ, w • v = -v) :
    w = negOneF4 :=
  ext_single fun i => by rw [hw, negOneF4_smul]

theorem negOneF4_mul_comm
    (w : WeylGroup .F4) : negOneF4 * w = w * negOneF4 :=
  ext_single fun i => by rw [mul_smul, mul_smul, negOneF4_smul, negOneF4_smul, smul_neg]

theorem qplusHom_nSL_eq_canonicalRep
    (L : Type) [Field L] [CharP L 2] :
    qplusHom L (nSL 1) = canonicalRep (coxeterSystem .F4) L negOneF4 := by
  rw [negOneF4, canonicalRep_mul_of_charTwo, canonicalRep_mul_of_charTwo,
    canonicalRep_mul_of_charTwo,
    ← rootWeylSL2_one_eq_canonicalRep_of_charTwo (isRoot_qplusRoot 0),
    ← rootWeylSL2_one_eq_canonicalRep_of_charTwo (isRoot_qplusRoot 1),
    ← rootWeylSL2_one_eq_canonicalRep_of_charTwo (isRoot_qplusRoot 2),
    ← rootWeylSL2_one_eq_canonicalRep_of_charTwo (isRoot_qplusRoot 3)]
  rfl

section QPlus

variable {K K₂ : Type} [Field K] [Finite K] [Field K₂] [Algebra K K₂]

omit [Finite K] in
theorem qplus_z_eq_canonicalRep
    [CharP K 2] (σ : K₂ ≃+* K₂) {ω : K₂} {P : SL2 K₂}
    (hω : ω + σ ω = 1) (hP : (P : Matrix (Fin 2) (Fin 2) K₂) = !![ω, ω + 1; 1, 1])
    {g z : ModGL .F4 K₂}
    (hgdef : g = rootSL2 .F4 K₂ (qplusRoot 0) P⁻¹ * rootSL2 .F4 K₂ (qplusRoot 1) P⁻¹ *
      rootSL2 .F4 K₂ (qplusRoot 2) P⁻¹ * rootSL2 .F4 K₂ (qplusRoot 3) P⁻¹)
    (hzdef : z = g * (Units.map (entrywiseHom (σ : K₂ →+* K₂)) g)⁻¹) :
    z = canonicalRep (coxeterSystem .F4) K₂ negOneF4 := by
  have : CharP K₂ 2 := charP_of_injective_algebraMap (algebraMap K K₂).injective 2
  have h2 : (2 : K₂) = 0 := CharTwo.two_eq_zero
  have hσω : σ ω = ω + 1 := by linear_combination hω - ω * h2
  have hPeq : P = evenQuadraticP ω := Subtype.ext (by rw [hP]; rfl)
  have hPn := evenQuadraticP_mul_nSL σ hσω
  rw [← hPeq] at hPn
  have hg' : g = qplusHom K₂ P⁻¹ := hgdef
  rw [hzdef, hg', qplusHom_mul_entrywise_inv_eq K₂ (σ : K₂ →+* K₂) hPn,
    qplusHom_nSL_eq_canonicalRep]

theorem canonicalRep_mem_conjEntrywiseImage
    [CharP K₂ 2] (hdeg : Module.finrank K K₂ = 2)
    (σ : K₂ ≃+* K₂) (hσ : ∀ c, σ c = c ^ Nat.card K) {g z : ModGL .F4 K₂}
    (hg : g ∈ adjointGroup .F4 K₂)
    (hzdef : z = g * (Units.map (entrywiseHom (σ : K₂ →+* K₂)) g)⁻¹)
    (hz : z = canonicalRep (coxeterSystem .F4) K₂ negOneF4) (w : WeylGroup .F4) :
    canonicalRep (coxeterSystem .F4) K₂ w ∈ conjEntrywiseImage K g := by
  obtain ⟨hfin, -, -⟩ := quadratic_frobenius hdeg σ hσ
  have : Finite K₂ := hfin
  rw [conjEntrywiseImage_eq_fixed_of_tag (Or.inr rfl) σ hσ hg hzdef]
  refine ⟨canonicalRep_mem_adjointGroup _ K₂ w, ?_⟩
  have hfix := entrywise_canonicalRep σ w
  rw [RingEquiv.toRingHom_eq_coe] at hfix
  change twistedEntrywise z (σ : K₂ →+* K₂) (canonicalRep (coxeterSystem .F4) K₂ w) =
    canonicalRep (coxeterSystem .F4) K₂ w
  rw [twistedEntrywise_apply, hfix, hz, canonicalRep_inv_of_charTwo,
    ← canonicalRep_mul_of_charTwo, ← canonicalRep_mul_of_charTwo, negOneF4_mul_comm, mul_assoc,
    mul_inv_cancel, mul_one]

theorem canonicalRep_mem_normalizer_qplusTorus
    [CharP K₂ 2] (hdeg : Module.finrank K K₂ = 2)
    (σ : K₂ ≃+* K₂) (hσ : ∀ c, σ c = c ^ Nat.card K) {g z : ModGL .F4 K₂}
    (hg : g ∈ adjointGroup .F4 K₂)
    (hzdef : z = g * (Units.map (entrywiseHom (σ : K₂ →+* K₂)) g)⁻¹)
    (hz : z = canonicalRep (coxeterSystem .F4) K₂ negOneF4) (w : WeylGroup .F4) :
    canonicalRep (coxeterSystem .F4) K₂ w ∈ Subgroup.normalizer
      ((torusGroup .F4 K₂ ⊓ conjEntrywiseImage K g : Subgroup (ModGL .F4 K₂)) :
        Set (ModGL .F4 K₂)) := by
  have hN := mem_normalizer_torusGroup_of_mem_monomialSubgroup
    (canonicalRep_mem_monomialSubgroup K₂ w)
  have hΓ := canonicalRep_mem_conjEntrywiseImage hdeg σ hσ hg hzdef hz w
  rw [Subgroup.mem_normalizer_iff]
  intro h
  rw [Subgroup.mem_inf, Subgroup.mem_inf, Subgroup.mem_normalizer_iff.1 hN h]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, mul_mem (mul_mem hΓ h2) (inv_mem hΓ)⟩
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    have e : h = (canonicalRep (coxeterSystem .F4) K₂ w)⁻¹ *
        (canonicalRep (coxeterSystem .F4) K₂ w * h * (canonicalRep (coxeterSystem .F4) K₂ w)⁻¹) *
          canonicalRep (coxeterSystem .F4) K₂ w := by group
    rw [e]
    exact mul_mem (mul_mem (inv_mem hΓ) h2) hΓ

end QPlus

theorem survivingRoots_canonicalRep_conj
    {L : Type} [Field L] {x : ModGL .F4 L}
    (hx : x ∈ torusGroup .F4 L) (w : WeylGroup .F4) :
    {β | IsRoot .F4 β ∧ torusRootChar (canonicalRep (coxeterSystem .F4) L w * x *
        (canonicalRep (coxeterSystem .F4) L w)⁻¹) β = 1} =
      (fun α => w • α) '' {α | IsRoot .F4 α ∧ torusRootChar x α = 1} := by
  obtain ⟨a, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hx
  have hy : canonicalRep (coxeterSystem .F4) L w * rootDiagUnit .F4 a *
      (canonicalRep (coxeterSystem .F4) L w)⁻¹ ∈ torusGroup .F4 L :=
    (Subgroup.mem_normalizer_iff.1 (mem_normalizer_torusGroup_of_mem_monomialSubgroup
      (canonicalRep_mem_monomialSubgroup L w)) _).1 hx
  obtain ⟨b, hb⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hy
  have hchar := (rootDiagUnit_eq_conj_canonicalRep_iff b a w).1 hb.symm
  rw [hb]
  ext β
  constructor
  · rintro ⟨hβ, h1⟩
    refine ⟨w⁻¹ • β, ⟨IsRoot.smul hβ w⁻¹, ?_⟩, smul_inv_smul w β⟩
    rw [torusRootChar_rootDiagUnit a (IsRoot.smul hβ w⁻¹), ← hchar, smul_inv_smul,
      ← torusRootChar_rootDiagUnit b hβ, h1]
  · rintro ⟨α, ⟨hα, h1⟩, rfl⟩
    refine ⟨IsRoot.smul hα w, ?_⟩
    rw [torusRootChar_rootDiagUnit b (IsRoot.smul hα w), hchar,
      ← torusRootChar_rootDiagUnit a hα, h1]

end EvenF4QPlus

open EvenF4QPlus

theorem even_F4_qplus_canonical_Weyl_rational_normalization :
    (∃ w₀ : WeylGroup .F4, ∀ v : Fin Tag.F4.rank → ℤ, w₀ • v = -v) ∧
    (∀ (M : Type) [Field M] [CharP M 2],
      (∀ w w' : WeylGroup .F4, canonicalRep (coxeterSystem .F4) M (w * w') =
        canonicalRep (coxeterSystem .F4) M w * canonicalRep (coxeterSystem .F4) M w') ∧
      Function.Injective (canonicalRep (coxeterSystem .F4) M) ∧
      (∀ w : WeylGroup .F4, canonicalRep (coxeterSystem .F4) M w ∈ adjointGroup .F4 M) ∧
      ∀ α : Fin Tag.F4.rank → ℤ, IsRoot .F4 α →
        rootWeylSL2 .F4 M α 1 = canonicalRep (coxeterSystem .F4) M (rootReflection α)) ∧
    ∀ (K : Type) [Field K] [Finite K] [CharP K 2] (K₂ : Type) [Field K₂] [Algebra K K₂],
      Module.finrank K K₂ = 2 → ∀ σ : K₂ ≃+* K₂, (∀ c, σ c = c ^ Nat.card K) →
      ∀ (ω : K₂) (P : SL2 K₂), ω + σ ω = 1 →
        (P : Matrix (Fin 2) (Fin 2) K₂) = !![ω, ω + 1; 1, 1] →
      ∀ g z : ModGL .F4 K₂,
        g = rootSL2 .F4 K₂ (qplusRoot 0) P⁻¹ * rootSL2 .F4 K₂ (qplusRoot 1) P⁻¹ *
          rootSL2 .F4 K₂ (qplusRoot 2) P⁻¹ * rootSL2 .F4 K₂ (qplusRoot 3) P⁻¹ →
        z = g * (Units.map (entrywiseHom (σ : K₂ →+* K₂)) g)⁻¹ →
        (∀ w₀ : WeylGroup .F4, (∀ v : Fin Tag.F4.rank → ℤ, w₀ • v = -v) →
          z = canonicalRep (coxeterSystem .F4) K₂ w₀) ∧
        (∀ w : WeylGroup .F4, canonicalRep (coxeterSystem .F4) K₂ w ∈ conjEntrywiseImage K g ∧
          canonicalRep (coxeterSystem .F4) K₂ w ∈ Subgroup.normalizer
            ((torusGroup .F4 K₂ ⊓ conjEntrywiseImage K g : Subgroup (ModGL .F4 K₂)) :
              Set (ModGL .F4 K₂))) ∧
        ∀ x ∈ torusGroup .F4 K₂ ⊓ conjEntrywiseImage K g, ∀ w : WeylGroup .F4,
          {β | IsRoot .F4 β ∧ torusRootChar (canonicalRep (coxeterSystem .F4) K₂ w * x *
              (canonicalRep (coxeterSystem .F4) K₂ w)⁻¹) β = 1} =
            (fun α => w • α) '' {α | IsRoot .F4 α ∧ torusRootChar x α = 1} := by
  refine ⟨⟨negOneF4, negOneF4_smul⟩, fun M _ _ =>
    ⟨fun w w' => canonicalRep_mul_of_charTwo (M := M) w w', canonicalRep_injective .F4 M,
    canonicalRep_mem_adjointGroup _ M,
    fun α hα => rootWeylSL2_one_eq_canonicalRep_of_charTwo hα⟩,
    fun K _ _ _ K₂ _ _ hdeg σ hσ ω P hω hP g z hgdef hzdef => ?_⟩
  have : CharP K₂ 2 := charP_of_injective_algebraMap (algebraMap K K₂).injective 2
  have hz := qplus_z_eq_canonicalRep (K := K) σ hω hP hgdef hzdef
  have hg : g ∈ adjointGroup .F4 K₂ := by
    rw [show g = qplusHom K₂ P⁻¹ from hgdef]
    exact qplusHom_mem_adjointGroup K₂ _
  exact ⟨fun w₀ hw₀ => by rw [hz, eq_negOneF4 hw₀], fun w =>
    ⟨canonicalRep_mem_conjEntrywiseImage hdeg σ hσ hg hzdef hz w,
      canonicalRep_mem_normalizer_qplusTorus hdeg σ hσ hg hzdef hz w⟩,
    fun x hx w => survivingRoots_canonicalRep_conj hx.1 w⟩

end CFSG.RankThree.Chevalley
