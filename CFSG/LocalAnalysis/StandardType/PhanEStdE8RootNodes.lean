module

public import CFSG.LocalAnalysis.StandardType.PhanEStdRootNodes
public import CFSG.LieType.SeitzGeneration.ExcHigh.E8FrameFamily

public noncomputable section

namespace CFSG.ClassicalInvolution.Phan.PhanE

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Universal
  CFSG.LieType.CurtisTits CFSG.LieType.RootSystem CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Adjoint CFSG.Timmesfeld CFSG.Timmesfeld.LevisExtras
  CFSG.StandardType CFSG.StandardType.PsiDiagChar CFSG.StandardType.RankOneXfer


variable {k : Type} [Field k] [Finite k] [CharP k 2]

theorem exists_e8_primitive_simpleNode (i : Fin (Tag.rank .E8)) :
    ∃ φ : Matrix.SpecialLinearGroup (Fin 2) k →* adjointGroup .E8 k,
      Function.Injective φ ∧ φ.range = rankOne (e8Datum k).rootGroup i ∧
      (sl2UpperUniSub k).map φ = (e8Datum k).rootGroup (Pi.single i 1) ∧
      ∀ a : kˣ, φ (sl2Diag a) ∈ ggTorus (e8Datum k) := by
  let D := simplyLacedLevis_e8 k
  obtain ⟨φ, hφ, hUL⟩ := D.sl2 i
  have hu (c : k) : φ (sl2Upper c) = e8Par k (Pi.single i 1) c := by
    rw [← tv01_eq_sl2Upper]
    exact (hUL c).1
  have hl (c : k) : φ (sl2Lower c) = e8Par k (-Pi.single i 1) c := by
    rw [← tv10_eq_sl2Lower]
    exact (hUL c).2
  have hpos : (Pi.single i 1 : Fin (Tag.rank .E8) → ℤ) ∈ (e8Datum k).roots :=
    (mem_adjDatum_roots).2 (isRoot_single .E8 i)
  have hneg : (-Pi.single i 1 : Fin (Tag.rank .E8) → ℤ) ∈ (e8Datum k).roots :=
    neg_mem_roots hpos
  have hle : rankOne (e8Datum k).rootGroup i ≤ φ.range := by
    apply sup_le
    · intro z hz
      obtain ⟨c, hc⟩ := D.surj _ hpos z hz
      exact ⟨sl2Upper c, (hu c).trans hc⟩
    · intro z hz
      obtain ⟨c, hc⟩ := D.surj _ hneg z hz
      exact ⟨sl2Lower c, (hl c).trans hc⟩
  have hR : rankOne (e8Datum k).rootGroup i = φ.range :=
    CFSG.ClassicalInvolution.ModelFacts.rankOne_eq_range_of_sl2 φ
      (fun c => by rw [hu c]; exact D.mem _ hpos c)
      (fun c => by rw [hl c]; exact D.mem _ hneg c) hle
  obtain ⟨O⟩ := nonempty_commOrder_ofCartan (e8Datum k).isFiniteType
    (Dv := (e8Datum k).divisible) rfl
  have hE := e8_chevalleyExtras k O _
    (commutatorFormula_commC e8Data_valid noG2_E8 _ (adjDatum_roots _ k) O)
  refine ⟨φ, hφ, hR.symm, ?_, fun a => map_sl2Diag_mem_ggTorus hE i φ hu hl a⟩
  apply Subgroup.ext
  intro z
  constructor
  · intro hz
    obtain ⟨A, hA, rfl⟩ := Subgroup.mem_map.1 hz
    obtain ⟨c, rfl⟩ := mem_sl2UpperUniSub_iff.1 hA
    rw [hu c]
    exact D.mem _ hpos c
  · intro hz
    obtain ⟨c, hc⟩ := D.surj _ hpos z hz
    exact Subgroup.mem_map.2
      ⟨sl2Upper c, mem_sl2UpperUniSub_iff.2 ⟨c, rfl⟩, (hu c).trans hc⟩

section FrameLang


open CFSG.LieType.SeitzGeneration.ExcHigh CFSG.StandardType.TableBExcTwo
  CFSG.StandardType.TableBExcTwoFusion CFSG.RankThree.Chevalley.EvenF4QPlus
  CFSG.SeitzReduction.E8Pilot CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.BorelTits

private theorem frameE8_root_seven :
    frameE8.root (7 : Fin 8) = Pi.single (1 : Fin 8) 1 := by
  change frameE8Root (7 : Fin 8) = Pi.single (1 : Fin 8) 1
  ext i
  fin_cases i <;> decide +kernel

theorem coe_e8_nrep (w : WeylGroup .E8) :
    ((nrep (e8_isCTGroupDatum k) w : adjointGroup .E8 k) : ModGL .E8 k) =
      canonicalRep (coxeterSystem .E8) k w := by
  obtain ⟨ω, hω, rfl⟩ := (coxeterSystem .E8).exists_isReduced w
  simp only [nrep_wordProd (e8_isCTGroupDatum k) hω, canonicalRep_wordProd hω,
    SubmonoidClass.coe_list_prod, List.map_map, Function.comp_def,
    CFSG.LieType.Chevalley.weylElement]

private theorem e8N0_eq_frameProd :
    nrep (e8_isCTGroupDatum k) (e8W0 k) = frameProd k frameE8 (nSL 1) := by
  have hY : ((frameProd k frameE8 (nSL 1) : adjointGroup .E8 k) : ModGL .E8 k) =
      canonicalRep (coxeterSystem .E8) k
        (List.ofFn fun i => rootReflection (frameE8.root i)).prod := by
    have hroots : ∀ β ∈ List.ofFn frameE8.root, IsRoot .E8 β := by
      intro β hβ
      obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hβ
      exact frameE8.isRoot i
    simpa only [frameProd, SubmonoidClass.coe_list_prod, List.map_ofFn,
      Function.comp_def, coe_rho, rootListProd] using
      rootListProd_nSL_eq_canonicalRep (L := k) hroots
  have hprod : (List.ofFn fun i => rootReflection (frameE8.root i)).prod = frameW8 := by
    rfl
  have hw : (e8W0 k : WeylGroup .E8) = frameW8 := by
    apply CFSG.LieType.Chevalley.ext_single (τ := .E8)
    intro i
    change weylAction (e8Datum k).isFiniteType (e8W0 k) (Pi.single i 1) =
      frameW8 • (Pi.single i 1)
    rw [e8W0_table, frameW8_smul_single]
    rfl
  apply Subtype.ext
  rw [coe_e8_nrep, hw, hY, hprod]

private theorem range_rho_frameE8_seven :
    (rho k frameE8 (7 : Fin 8)).range =
      rootPairSL2 .E8 k (Pi.single (1 : Fin 8) 1) := by
  apply Subgroup.map_injective (adjointGroup .E8 k).subtype_injective
  rw [← MonoidHom.range_comp, rootPairSL2, Subgroup.map_subgroupOf_eq_of_le
    (sup_le (rootSubgroup_le_adjointGroup _) (rootSubgroup_le_adjointGroup _))]
  change (rootSL2 .E8 k (frameE8.root (7 : Fin 8))).range = _
  rw [CFSG.RankThree.Chevalley.range_rootSL2_of_isRoot (frameE8.isRoot 7),
    frameE8_root_seven]
  rfl

theorem exists_e8_oneNormalizer_lang {f : ℕ}
    (hK : Nat.card k = (2 ^ f) ^ 2) (hf : 1 ≤ f) :
    ∃ g : adjointGroup .E8 k,
      g ∈ Subgroup.normalizer
        (rootPairSL2 .E8 k (Pi.single (1 : Fin 8) 1) : Set (adjointGroup .E8 k)) ∧
      g⁻¹ * adjointBaseChangeHom .E8 (unitaryInvolution k 2 f).toRingHom g =
        nrep (e8_isCTGroupDatum k) (e8W0 k) := by
  obtain ⟨P, hP⟩ := exists_sl2_fieldLang_swap (unitaryInvolution k 2 f)
    (unitaryInvolution_involutive hK) (unitaryInvolution_ne hK hf)
  let A := rootPairSL2 .E8 k (Pi.single (1 : Fin 8) 1)
  let g := frameProd k frameE8 P
  have hρ : (rho k frameE8 (7 : Fin 8)).range = A := range_rho_frameE8_seven
  have hn (i : Fin 8) : rho k frameE8 i P ∈
      Subgroup.normalizer (A : Set (adjointGroup .E8 k)) := by
    by_cases hi : i = 7
    · subst i
      apply A.le_normalizer
      rw [← hρ]
      exact ⟨P, rfl⟩
    · apply Subgroup.centralizer_le_normalizer (A : Set (adjointGroup .E8 k))
      apply Subgroup.mem_centralizer_iff.2
      intro x hx
      rw [← hρ] at hx
      obtain ⟨B, rfl⟩ := hx
      exact (commute_rho frameE8 hi P B).symm.eq
  have hgN : g ∈ Subgroup.normalizer (A : Set (adjointGroup .E8 k)) := by
    dsimp only [g, frameProd]
    apply Subgroup.list_prod_mem
    intro x hx
    obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hx
    exact hn i
  have heq : adjointBaseChangeHom .E8 (unitaryInvolution k 2 f).toRingHom =
      adjointMap .E8 (unitaryInvolution k 2 f).toRingHom := by
    apply DFunLike.ext
    intro x
    apply Subtype.ext
    rw [coe_adjointBaseChangeHom, coe_adjointMap]
  refine ⟨g, hgN, ?_⟩
  dsimp only [g]
  rw [heq, adjointMap_frameProd, hP, frameProd_mul, e8N0_eq_frameProd, nSL_one]
  group

end FrameLang

section OriginalImages


open CFSG.SeitzReduction.E8Pilot CFSG.LieType.BorelTits

theorem rankOne_e8Datum_eq_rootPairSL2 (i : Fin (Tag.rank .E8)) :
    rankOne (e8Datum k).rootGroup i = rootPairSL2 .E8 k (Pi.single i 1) := by
  apply Subgroup.map_injective (adjointGroup .E8 k).subtype_injective
  rw [rankOne, Subgroup.map_sup, map_subtype_rootGroup_E8 (isRoot_single .E8 i),
    map_subtype_rootGroup_E8 (IsRoot.neg (isRoot_single .E8 i)), rootPairSL2,
    Subgroup.map_subgroupOf_eq_of_le
      (sup_le (rootSubgroup_le_adjointGroup _) (rootSubgroup_le_adjointGroup _))]

theorem e8_frob_phi_eq_baseChangeHom (θ : k →+* k) (hθ : ∀ c, θ (θ c) = c) :
    (e8Frob θ hθ).φ = adjointBaseChangeHom .E8 θ := by
  apply DFunLike.ext
  intro x
  apply Subtype.ext
  rfl

theorem e8_actualFieldEmbed_range {f : ℕ}
    (hK : Nat.card k = (2 ^ f) ^ 2) (hf : 1 ≤ f) :
    (adjointBaseChangeHom .E8 (fqEmbed hK hf)).range =
      MonoidHom.eqLocus (adjointBaseChangeHom .E8 (unitaryInvolution k 2 f).toRingHom)
        (MonoidHom.id (adjointGroup .E8 k)) := by
  let θ : k →+* k := (unitaryInvolution k 2 f : k →+* k)
  have hθ : ∀ c, θ (θ c) = c := fun c => by
    simpa only [θ, RingEquiv.coe_toRingHom] using unitaryInvolution_involutive hK c
  let e := e8FrobFixEquiv θ hθ
    (exists_mul_unitaryInvolution_eq hK) (fqEmbed hK hf)
    (unitaryInvolution_fqEmbed hK hf) (exists_fqEmbed_eq hK hf)
  let E0 := (frobFix (e8Frob θ hθ)).subtype.comp e.toMonoidHom
  have hENat : adjointBaseChangeHom .E8 (fqEmbed hK hf) = E0 := by
    apply DFunLike.ext
    intro x
    rfl
  have hE0 : E0.range = frobFix (e8Frob θ hθ) := by
    apply Subgroup.ext
    intro x
    constructor
    · rintro ⟨g, rfl⟩
      exact (e g).2
    · intro hx
      obtain ⟨g, hg⟩ := e.surjective ⟨x, hx⟩
      exact ⟨g, congrArg Subtype.val hg⟩
  rw [hENat, hE0]
  apply Subgroup.ext
  intro x
  change (e8Frob θ hθ).φ x = x ↔ _
  rw [e8_frob_phi_eq_baseChangeHom]
  rfl

theorem exists_e8_stdConfig_primitive_node {f : ℕ}
    (hK : Nat.card k = (2 ^ f) ^ 2) (hf : 1 ≤ f) :
    ∃ φ : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 f) →* (ggU .E8 0 f).K,
      Function.Injective φ ∧
      (sl2UpperUniSub (GaloisField 2 f)).map φ =
        (ggU .E8 0 f).D.rootGroup (Pi.single (1 : Fin 8) 1) ∧
      (∀ a : (GaloisField 2 f)ˣ, φ (PsiDiagChar.sl2Diag a) ∈ ggTorus (ggU .E8 0 f).D) ∧
      ∃ v : (ggU .E8 0 f).K,
        φ.range.map (MulAut.conj v).toMonoidHom =
          ((e8StdConfig k f hK hf).S.ι (1 : Fin 8)).range := by
  change ∃ φ : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 f) →*
      adjointGroup .E8 (GaloisField 2 f),
    Function.Injective φ ∧
    (sl2UpperUniSub (GaloisField 2 f)).map φ =
      (e8Datum (GaloisField 2 f)).rootGroup (Pi.single (1 : Fin 8) 1) ∧
    (∀ a : (GaloisField 2 f)ˣ, φ (PsiDiagChar.sl2Diag a) ∈ ggTorus (e8Datum (GaloisField 2 f))) ∧
    ∃ v : adjointGroup .E8 (GaloisField 2 f),
      φ.range.map (MulAut.conj v).toMonoidHom =
        ((e8StdConfig k f hK hf).S.ι (1 : Fin 8)).range
  let θ : k →+* k := (unitaryInvolution k 2 f : k →+* k)
  have hθ : ∀ c, θ (θ c) = c := fun c => by
    simpa only [θ, RingEquiv.coe_toRingHom] using unitaryInvolution_involutive hK c
  let S := e8StdInput θ hθ (unitaryInvolution_ne hK hf) (exists_mul_unitaryInvolution_eq hK)
  let e : adjointGroup .E8 (GaloisField 2 f) ≃* frobFix S.F :=
    e8FrobFixEquiv θ hθ (exists_mul_unitaryInvolution_eq hK) (fqEmbed hK hf)
      (unitaryInvolution_fqEmbed hK hf) (exists_fqEmbed_eq hK hf)
  let E := adjointBaseChangeHom .E8 (fqEmbed hK hf)
  let F := adjointBaseChangeHom .E8 θ
  let n0 := nrep (e8_isCTGroupDatum k) (e8W0 k)
  let z := S.lang
  let B := rootPairSL2 .E8 k (Pi.single (1 : Fin 8) 1)
  let N := ((S.family e (RingEquiv.refl k) (fun _ => rfl)).ι (1 : Fin 8)).range
  obtain ⟨φ, hφ, hR, hU, hT⟩ :=
    exists_e8_primitive_simpleNode (k := GaloisField 2 f) (1 : Fin 8)
  obtain ⟨g, hgN, hg0⟩ := exists_e8_oneNormalizer_lang hK hf
  have hg : g⁻¹ * F g = n0 := by
    simpa only [F, n0, θ, RingEquiv.toRingHom_eq_coe] using hg0
  have hz : z⁻¹ * F z = n0 := by
    have h := S.lang_spec
    change z⁻¹ * (e8Frob θ hθ).φ z = n0 at h
    rw [e8_frob_phi_eq_baseChangeHom] at h
    exact h
  have hei : Function.Injective E := adjointBaseChangeHom_injective .E8 (fqEmbed hK hf)
  have hErange : E.range = MonoidHom.eqLocus F (MonoidHom.id (adjointGroup .E8 k)) := by
    simpa only [E, F, θ, RingEquiv.toRingHom_eq_coe] using e8_actualFieldEmbed_range hK hf
  have hfix : ∀ x : k, unitaryInvolution k 2 f x = x ↔ x ∈ Set.range (fqEmbed hK hf) := by
    intro x
    constructor
    · exact exists_fqEmbed_eq hK hf x
    · rintro ⟨c, rfl⟩
      exact unitaryInvolution_fqEmbed hK hf c
  have hRimage : φ.range.map E =
      B ⊓ MonoidHom.eqLocus F (MonoidHom.id (adjointGroup .E8 k)) := by
    erw [hR, rankOne_e8Datum_eq_rootPairSL2]
    simpa only [E, B, F, θ, RingEquiv.toRingHom_eq_coe] using
      map_rootPairSL2_eq_inf_fixed_of_charTwo .E8 (fqEmbed hK hf)
        (unitaryInvolution k 2 f) hfix (isRoot_single .E8 (1 : Fin 8))
  have hρ : S.rho e = (MulAut.conj z⁻¹).toMonoidHom.comp E := by
    apply DFunLike.ext
    intro x
    change S.lang⁻¹ * (e x : adjointGroup .E8 k) * S.lang = z⁻¹ * E x * z
    rfl
  have hNimage : N.map ((MulAut.conj z⁻¹).toMonoidHom.comp E) =
      B ⊓ MonoidHom.eqLocus ((MulAut.conj n0).toMonoidHom.comp F)
        (MonoidHom.id (adjointGroup .E8 k)) := by
    rw [← hρ]
    change (((S.family e (RingEquiv.refl k) (fun _ => rfl)).ι (1 : Fin 8)).range).map
      (S.rho e) = _
    erw [S.map_node_family_eq_rankOne_inf_stdFix e (RingEquiv.refl k) (fun _ => rfl)]
    change rankOne (e8Datum k).rootGroup (1 : Fin 8) ⊓ stdFix (e8Frob θ hθ) n0 = _
    erw [rankOne_e8Datum_eq_rootPairSL2]
    apply congrArg (fun A : Subgroup (adjointGroup .E8 k) => B ⊓ A)
    apply Subgroup.ext
    intro x
    change n0 * (e8Frob θ hθ).φ x * n0⁻¹ = x ↔ n0 * F x * n0⁻¹ = x
    rw [e8_frob_phi_eq_baseChangeHom]
  obtain ⟨v, hv⟩ := Subgroup.exists_conj_of_lang_node_images F hz hg B hgN E hei hErange
    N φ.range hNimage hRimage
  refine ⟨φ, hφ, hU, hT, v, ?_⟩
  erw [e8StdConfig, PhanEConfig.iota_ofEq]
  exact hv

end OriginalImages

end CFSG.ClassicalInvolution.Phan.PhanE
