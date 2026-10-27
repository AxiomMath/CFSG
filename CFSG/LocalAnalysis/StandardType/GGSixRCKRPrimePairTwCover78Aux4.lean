module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimePairTwCover78Aux1
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimePairTwCover78Aux2
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.InnerQuasisimpleSplit
public import CFSG.ClassicalInvolution.ModelFacts.PairFrameExcLang
public import CFSG.RankThree.PartOne.KE.ConjRootSpan

public section

namespace CFSG.StandardType.RCKRP

variable {CoeffField : Type} [Field CoeffField] [IsAlgClosed CoeffField] [CharP CoeffField 2]
attribute [local instance] ZMod.algebra


open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Universal
  CFSG.StandardType CFSG.StandardType.GGFinModel CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.PartOne.KE6 CFSG.RankThree.PartOne.KE CFSG.RankThree.PartOne.KD4T
  CFSG.LieType.Steinberg.TwistedE6 CFSG.LieType.Steinberg.Adjoint
  CFSG.ClassicalInvolution.ModelFacts.Levi

theorem rckTw78_untwist
    {τ : Tag} [M27Ok τ] [E6Sub τ] {p₀ : ℕ} (S : LangSetup τ CoeffField p₀)
    (v : WeylGroup τ) (nv nw hL n₁ : ModGL τ CoeffField) {h : ℕ} (σ : CoeffField ≃+* CoeffField)
    (hnv : nv = canonicalRep (coxeterSystem τ) CoeffField v) (hn : S.D.n = nw)
    (hΦ : S.D.Φ = Units.map (entrywiseHom (iterateFrobenius CoeffField 2 h)))
    (hpt : ∀ g : ModGL τ CoeffField,
      (nv⁻¹ * nw * nv) * Units.map (entrywiseHom (iterateFrobenius CoeffField 2 h)) g *
          (nv⁻¹ * nw * nv)⁻¹ =
        hL⁻¹ * (n₁ * Units.map (entrywiseHom (iterateFrobenius CoeffField 2 h)) (hL * g * hL⁻¹) *
          n₁⁻¹) * hL)
    (hn₁fix : ∀ g ∈ rootSpan τ CoeffField
      ({(Pi.single (e6Idx 1) 1 : Fin τ.rank → ℤ), -(Pi.single (e6Idx 1) 1)} :
        Set (Fin τ.rank → ℤ)), n₁ * g * n₁⁻¹ = g)
    (hσ : ∀ c, σ c = c ^ 2 ^ h) :
    ∀ g ∈ rootSpan τ CoeffField ({(v • Pi.single (e6Idx 1) 1 : Fin τ.rank → ℤ),
        -(v • Pi.single (e6Idx 1) 1)} : Set (Fin τ.rank → ℤ)),
      S.D.step ((nv * hL⁻¹ * nv⁻¹) * g * (nv * hL⁻¹ * nv⁻¹)⁻¹) =
        (nv * hL⁻¹ * nv⁻¹) * frobGL σ g * (nv * hL⁻¹ * nv⁻¹)⁻¹ := by
  intro g hg
  have hΦnv : Units.map (entrywiseHom (iterateFrobenius CoeffField 2 h)) nv = nv := by
    rw [hnv]
    have hσ' : σ.toRingHom = iterateFrobenius CoeffField 2 h := by
      ext c
      rw [iterateFrobenius_def]
      exact hσ c
    show Units.map (entrywiseHom (iterateFrobenius CoeffField 2 h))
      (canonicalRep (coxeterSystem τ) CoeffField v) = canonicalRep (coxeterSystem τ) CoeffField v
    rw [← hσ']
    exact entrywise_canonicalRep σ v
  have hstep : ∀ u : ModGL τ CoeffField,
      S.D.step (nv * u * nv⁻¹) =
        nv * ((nv⁻¹ * nw * nv) * Units.map (entrywiseHom (iterateFrobenius CoeffField 2 h)) u *
          (nv⁻¹ * nw * nv)⁻¹) * nv⁻¹ := by
    intro u
    rw [LangDatum.step, MonoidHom.comp_apply, hn, hΦ]
    change nw * (Units.map (entrywiseHom (iterateFrobenius CoeffField 2 h))) (nv * u * nv⁻¹) * nw⁻¹ =
      nv * ((nv⁻¹ * nw * nv) * (Units.map (entrywiseHom (iterateFrobenius CoeffField 2 h))) u *
        (nv⁻¹ * nw * nv)⁻¹) * nv⁻¹
    rw [map_mul, map_mul, map_inv, hΦnv]
    group
  have hgnv : nv⁻¹ * g * nv ∈ rootSpan τ CoeffField
      ({(Pi.single (e6Idx 1) 1 : Fin τ.rank → ℤ), -(Pi.single (e6Idx 1) 1)} :
        Set (Fin τ.rank → ℤ)) := by
    have hnvM : nv ∈ monomialSubgroup τ CoeffField := by
      rw [hnv]; exact canonicalRep_mem_monomialSubgroup CoeffField v
    have hmapv : MapsRootLines nv v := by rw [hnv]; exact mapsRootLines_canonicalRep v
    have hm := map_conj_rootSpan_of_mem_monomialSubgroup (τ := τ) (K := CoeffField) hnvM
      (S := ({(Pi.single (e6Idx 1) 1 : Fin τ.rank → ℤ), -(Pi.single (e6Idx 1) 1)} :
        Set (Fin τ.rank → ℤ)))
      (fun δ hδ => by
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hδ
        rcases hδ with rfl | rfl
        · exact isRoot_single τ (e6Idx 1)
        · exact IsRoot.neg (isRoot_single τ (e6Idx 1)))
    have hset : (fun δ => v • δ) ''
        ({(Pi.single (e6Idx 1) 1 : Fin τ.rank → ℤ), -(Pi.single (e6Idx 1) 1)} :
          Set (Fin τ.rank → ℤ)) =
        ({(v • Pi.single (e6Idx 1) 1 : Fin τ.rank → ℤ), -(v • Pi.single (e6Idx 1) 1)} :
          Set (Fin τ.rank → ℤ)) := by
      ext x
      constructor
      · rintro ⟨δ, hδ, rfl⟩
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hδ ⊢
        rcases hδ with rfl | rfl
        · exact Or.inl rfl
        · exact Or.inr (by simp only [smul_neg])
      · intro hx
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
        rcases hx with rfl | rfl
        · exact ⟨_, Or.inl rfl, rfl⟩
        · exact ⟨_, Or.inr rfl, by simp only [smul_neg]⟩
    have hw : weylQuotientHom τ CoeffField ⟨nv, hnvM⟩ = v := weylQuotientHom_eq hmapv
    have hmem : g ∈ (rootSpan τ CoeffField
        ({(Pi.single (e6Idx 1) 1 : Fin τ.rank → ℤ), -(Pi.single (e6Idx 1) 1)} :
          Set (Fin τ.rank → ℤ))).map (MulAut.conj nv).toMonoidHom := by
      rw [hm]
      rw [show (fun δ => weylQuotientHom τ CoeffField ⟨nv, hnvM⟩ • δ) =
          (fun δ => v • δ) from by rw [hw]]
      rw [hset]
      exact hg
    obtain ⟨y, hy, hyg⟩ := Subgroup.mem_map.1 hmem
    change nv * y * nv⁻¹ = g at hyg
    rw [← hyg]
    convert hy using 1
    group
  have hΦgn : Units.map (entrywiseHom (iterateFrobenius CoeffField 2 h)) (nv⁻¹ * g * nv) ∈
      rootSpan τ CoeffField ({(Pi.single (e6Idx 1) 1 : Fin τ.rank → ℤ), -(Pi.single (e6Idx 1) 1)} :
        Set (Fin τ.rank → ℤ)) := by
    have hle := map_entrywiseFrobGL_rootSpan_le (τ := τ) (k := CoeffField) 2 h
      ({(Pi.single (e6Idx 1) 1 : Fin τ.rank → ℤ), -(Pi.single (e6Idx 1) 1)} :
        Set (Fin τ.rank → ℤ))
    exact hle ⟨_, hgnv, rfl⟩
  have hfix : n₁ * Units.map (entrywiseHom (iterateFrobenius CoeffField 2 h)) (nv⁻¹ * g * nv) *
      n₁⁻¹ = Units.map (entrywiseHom (iterateFrobenius CoeffField 2 h)) (nv⁻¹ * g * nv) :=
    hn₁fix _ hΦgn
  have hΦg : Units.map (entrywiseHom (iterateFrobenius CoeffField 2 h)) g =
      nv * Units.map (entrywiseHom (iterateFrobenius CoeffField 2 h)) (nv⁻¹ * g * nv) * nv⁻¹ := by
    rw [show nv⁻¹ * g * nv = nv⁻¹ * g * nv from rfl]
    rw [map_mul, map_mul, map_inv, hΦnv]
    group
  calc S.D.step ((nv * hL⁻¹ * nv⁻¹) * g * (nv * hL⁻¹ * nv⁻¹)⁻¹)
      = S.D.step (nv * (hL⁻¹ * (nv⁻¹ * g * nv) * hL) * nv⁻¹) := by
          rw [show (nv * hL⁻¹ * nv⁻¹) * g * (nv * hL⁻¹ * nv⁻¹)⁻¹ =
            nv * (hL⁻¹ * (nv⁻¹ * g * nv) * hL) * nv⁻¹ from by group]
    _ = nv * ((nv⁻¹ * nw * nv) *
          Units.map (entrywiseHom (iterateFrobenius CoeffField 2 h)) (hL⁻¹ * (nv⁻¹ * g * nv) * hL) *
          (nv⁻¹ * nw * nv)⁻¹) * nv⁻¹ := hstep _
    _ = nv * (hL⁻¹ * (n₁ *
          Units.map (entrywiseHom (iterateFrobenius CoeffField 2 h)) (nv⁻¹ * g * nv) * n₁⁻¹) *
          hL) * nv⁻¹ := by
        rw [hpt (hL⁻¹ * (nv⁻¹ * g * nv) * hL)]
        congr 1
        rw [show hL * (hL⁻¹ * (nv⁻¹ * g * nv) * hL) * hL⁻¹ = nv⁻¹ * g * nv from by group]
    _ = nv * (hL⁻¹ * Units.map (entrywiseHom (iterateFrobenius CoeffField 2 h)) (nv⁻¹ * g * nv) *
          hL) * nv⁻¹ := by rw [hfix]
    _ = (nv * hL⁻¹ * nv⁻¹) * Units.map (entrywiseHom (iterateFrobenius CoeffField 2 h)) g *
          (nv * hL⁻¹ * nv⁻¹)⁻¹ := by rw [hΦg]; group
    _ = (nv * hL⁻¹ * nv⁻¹) * frobGL σ g * (nv * hL⁻¹ * nv⁻¹)⁻¹ := by
        congr 2
        have : σ.toRingHom = iterateFrobenius CoeffField 2 h := by
          ext c; rw [iterateFrobenius_def]; exact hσ c
        rw [frobGL, this]

omit [IsAlgClosed CoeffField] [CharP CoeffField 2] in
theorem rckTw78_pin_conj
    {τ : Tag} (v : WeylGroup τ) (α : Fin τ.rank → ℤ) (hα : IsRoot τ α) (σ : CoeffField ≃+* CoeffField) :
    ((rootSubgroup τ ↥(fixSubfield σ) (v • α)).map
        (baseChangeGL (fixSubfield σ).subtype)).map
        (MulAut.conj (canonicalRep (coxeterSystem τ) CoeffField v)⁻¹).toMonoidHom =
      (rootSubgroup τ ↥(fixSubfield σ) α).map (baseChangeGL (fixSubfield σ).subtype) := by
  have h1 : (rootSubgroup τ ↥(fixSubfield σ) α).map
      (MulAut.conj (canonicalRep (coxeterSystem τ) ↥(fixSubfield σ) v)).toMonoidHom =
      rootSubgroup τ ↥(fixSubfield σ) (v • α) := map_conj_rootSubgroup (L := ↥(fixSubfield σ)) v hα
  have h2 : (baseChangeGL (fixSubfield σ).subtype).comp
      (MulAut.conj (canonicalRep (coxeterSystem τ) ↥(fixSubfield σ) v)).toMonoidHom =
      (MulAut.conj (canonicalRep (coxeterSystem τ) CoeffField v)).toMonoidHom.comp
        (baseChangeGL (fixSubfield σ).subtype) := by
    ext x
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul,
      map_inv, baseChangeGL_canonicalRep]
  have h3 : (MulAut.conj (canonicalRep (coxeterSystem τ) CoeffField v)⁻¹).toMonoidHom.comp
      ((MulAut.conj (canonicalRep (coxeterSystem τ) CoeffField v)).toMonoidHom.comp
        (baseChangeGL (fixSubfield σ).subtype)) = baseChangeGL (fixSubfield σ).subtype := by
    ext x
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, mul_inv_rev,
      inv_inv]
    group
  rw [← h1, Subgroup.map_map, Subgroup.map_map, MonoidHom.comp_assoc, h2, h3]

end CFSG.StandardType.RCKRP

end
