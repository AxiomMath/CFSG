module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight91GammaDefs
import CFSG.LieType.SeitzGeneration.ClassicalSeitzStatus
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanIdentOffCharBase
import CFSG.Adapters.LieModelSimple
import CFSG.Adapters.ClassicalCatalogLinearUnitary
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Index
public import CFSG.LieType.SeitzGeneration.Dispatch

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Open Subgroup
open CFSG.Blueprint (LieModel)
open CFSG.Adapters.RankTwoModelTransports

private theorem exists_noncommuting_of_card_nine {X : Type} [Group X] [Finite X]
    [IsSimpleGroup X] {E : Subgroup X} (hE9 : Nat.card E = 9) :
    ∃ a b : X, a * b ≠ b * a := by
  by_contra h
  have hcomm : ∀ a b : X, a * b = b * a := by
    intro a b
    by_contra hab
    exact h ⟨a, b, hab⟩
  letI : CommGroup X := { ‹Group X› with mul_comm := hcomm }
  have hp : (Nat.card X).Prime := IsSimpleGroup.prime_card
  obtain ⟨k, hk⟩ : 9 ∣ Nat.card X := by
    have hdvd := Subgroup.card_dvd_of_le (H := E) (K := ⊤) le_top
    rw [Subgroup.card_top] at hdvd
    simpa [hE9] using hdvd
  have hpos : 0 < k := by
    have hle : 9 ≤ Nat.card X := hE9 ▸ Subgroup.card_le_card_group E
    omega
  have hk' : Nat.card X = 3 * (3 * k) := by
    rw [hk]
    ring
  rw [hk'] at hp
  exact Nat.not_prime_mul (by omega) (by omega) hp

section Plane


private theorem glbCore_eq_top_of_classicalIndex {X : Type} [Group X] [Finite X]
    (hs : IsSimpleGroup X) (hnab : ∃ a b : X, a * b ≠ b * a)
    (d : TauCeti.ValidLieTypeIndex) (e : X ≃* CFSG.LieType.SeitzGeneration.Cat d)
    (hd : CFSG.LieType.SeitzGeneration.IsClassicalIndex d.1) (h3 : 3 ≠ d.1.characteristic)
    (hex : ¬ CFSG.AGLEmbeddingD2.IsD2SeitzException 3 d.1) (E : Subgroup X)
    (hE : IsElemAbelian 3 E) (hE9 : Nat.card E = 9) : GLBCore 3 1 E = ⊤ := by
  let ψ : X →* MulAut (CFSG.LieType.SeitzGeneration.Cat d) :=
    (MulAut.congr e).toMonoidHom.comp MulAut.conj
  have hψ : Function.Injective ψ :=
    (MulAut.congr e).injective.comp (CFSG.AGLEmbedding.conj_injective_of_simple hs hnab)
  have hψel : IsElemAbelian 3 (E.map ψ) :=
    CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map 3 hE ψ
  have hclos : Subgroup.closure {k : CFSG.LieType.SeitzGeneration.Cat d |
      ∃ ε ∈ E.map ψ, ε ≠ 1 ∧ ε k = k} = ⊤ :=
    CFSG.LieType.SeitzGeneration.seitzInnerThreeClassical_holds d 3 Nat.prime_three
      (by norm_num) h3 hex (E.map ψ) hψel
      (by rw [Subgroup.card_map_of_injective hψ, hE9]; norm_num)
      ⟨CFSG.LieType.SeitzGeneration.InnerPlane.map_congr_conj e E 3, rfl, hd⟩
  have hle : (⊤ : Subgroup (CFSG.LieType.SeitzGeneration.Cat d)) ≤
      (GLBCore 3 1 E).map e.toMonoidHom := by
    rw [← hclos, Subgroup.closure_le]
    rintro c ⟨ε, hε, hε1, hεc⟩
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hε
    have hx1 : x ≠ 1 := by
      rintro rfl
      exact hε1 (map_one ψ)
    refine ⟨e.symm c, CFSG.AGLEmbedding.mem_glbCore_of_commute Nat.prime_three hE hx hx1 ?_,
      by simp⟩
    have h1 : ψ x c = e (x * e.symm c * x⁻¹) := by
      simp [ψ, MulAut.congr_apply]
    rw [h1] at hεc
    have h2 : x * e.symm c * x⁻¹ = e.symm c := by
      apply e.injective
      rw [hεc]
      simp
    rw [mul_inv_eq_iff_eq_mul] at h2
    exact h2.symm
  rw [eq_top_iff]
  intro k _
  obtain ⟨k', hk', hk'e⟩ := Subgroup.mem_map.mp (hle (Subgroup.mem_top (e k)))
  exact e.injective hk'e ▸ hk'

end Plane

private theorem psl_three_catalog_equiv {X : Type} [Group X] {p f : ℕ} (hp : p.Prime)
    (hf : 1 ≤ f) (h : LieModel X .PSL 3 p f) (h1 : p ^ f % 3 = 1) :
    ∃ hv : (TauCeti.LieTypeIndex.A 2 ⟨p, f, hp, hf⟩).Valid,
      Nonempty (X ≃* CFSG.LieType.SeitzGeneration.Cat
        ⟨TauCeti.LieTypeIndex.A 2 ⟨p, f, hp, hf⟩, hv⟩) := by
  let q : TauCeti.PrimePower := ⟨p, f, hp, hf⟩
  let _ : Fact p.Prime := ⟨hp⟩
  have hadm : CFSG.Open.StatedLieAdmissible .PSL 3 p f := h.admissible
  have hdup : ¬ (TauCeti.LieTypeIndex.A 2 q).IsDuplicateRepresentative := by
    rw [TauCeti.LieTypeIndex.isDuplicateRepresentative_iff]
    simp only [TauCeti.PrimePower.card_def, q]
    intro hd
    omega
  have hv : (TauCeti.LieTypeIndex.A 2 q).Valid :=
    CFSG.ClassicalModels.linearCatalog_index_valid 3 p f hadm hdup
  obtain ⟨-, K, hfield, hfinite, hKcard, ⟨e⟩⟩ := h.statedClassicalModel (by decide)
  let _ := hfield
  let _ := hfinite
  let eK := CFSG.ClassicalModels.statedLinearModelEquivGaloisPSL K 3 p f (by omega) hKcard
  have eC := CFSG.ClassicalModels.linearCatalogCandidateEquivPSL 2 q hv
  have eC' : TauCeti.ValidLieTypeIndex.Group ⟨TauCeti.LieTypeIndex.A 2 q, hv⟩ ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 3) (GaloisField p f) := by
    simpa using eC
  exact ⟨hv, ⟨(e.trans eK).trans eC'.symm⟩⟩

private theorem not_isD2SeitzException_A_two {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f)
    (h4 : p ^ f ≠ 4) :
    ¬ CFSG.AGLEmbeddingD2.IsD2SeitzException 3
      (TauCeti.LieTypeIndex.A 2 ⟨p, f, hp, hf⟩) := by
  let q : TauCeti.PrimePower := ⟨p, f, hp, hf⟩
  intro h
  rw [CFSG.AGLEmbeddingD2.IsD2SeitzException] at h
  rcases h with ⟨-, hA⟩ | ⟨h5, -⟩
  · rcases hA with h | h | h | h | h
    · obtain ⟨q', -, -, hEq⟩ := h
      cases hEq
    · obtain ⟨q', hq'p, hq'e, hEq⟩ := h
      injection hEq with _ hqq
      have hcard : q'.card = 4 := by
        rw [TauCeti.PrimePower.card_def, hq'p, hq'e]
        norm_num
      rw [← hqq] at hcard
      exact h4 (by simpa [q, TauCeti.PrimePower.card_def] using hcard)
    · obtain ⟨q', -, -, hEq⟩ := h
      cases hEq
    · obtain ⟨q', -, -, hEq | hEq⟩ := h
      · cases hEq
      · cases hEq
    · cases h
  · exact absurd h5 (by norm_num)

private theorem psu_three_catalog_equiv {X : Type} [Group X] {p f : ℕ} (hp : p.Prime)
    (hf : 1 ≤ f) (h : LieModel X .PSU 3 p f) :
    ∃ hv : (TauCeti.LieTypeIndex.twistedA 2 ⟨p, f, hp, hf⟩).Valid,
      Nonempty (X ≃* CFSG.LieType.SeitzGeneration.Cat
        ⟨TauCeti.LieTypeIndex.twistedA 2 ⟨p, f, hp, hf⟩, hv⟩) := by
  obtain ⟨hadm, K, hfield, hfinite, hK, ⟨e⟩⟩ := h.statedClassicalModel (by decide)
  let _ := hfield
  let _ := hfinite
  let _ : Fact p.Prime := ⟨hp⟩
  have hv := CFSG.ClassicalModels.unitaryCatalog_index_valid 3 p f hadm
  let q : TauCeti.PrimePower := ⟨p, f, hp, hf⟩
  have hv' : (TauCeti.LieTypeIndex.twistedA 2 q).Valid := by simpa using hv
  let L := GaloisField p (2 * f)
  let _ : Fintype K := Fintype.ofFinite K
  let _ : Fintype L := Fintype.ofFinite L
  have hcard : Fintype.card K = Fintype.card L := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hK,
      GaloisField.card p (2 * f) (by omega), ← pow_mul, mul_comm]
  let φ : K ≃+* L := FiniteField.ringEquivOfCardEq hcard
  let e1 := statedProjCongr (glCongr (ι := Fin 3) φ) (glCongr_statedSU φ 3 (p ^ f))
    (glCongr_statedScalars φ)
  let eT := CFSG.QuasithinUnique.SQTK.typeTwistedAGroupEquivStatedProj 2 q hv'
  exact ⟨hv', ⟨(e.trans e1).trans eT.symm⟩⟩

private theorem not_isD2SeitzException_twistedA_two {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f) :
    ¬ CFSG.AGLEmbeddingD2.IsD2SeitzException 3
      (TauCeti.LieTypeIndex.twistedA 2 ⟨p, f, hp, hf⟩) := by
  simp [CFSG.AGLEmbeddingD2.IsD2SeitzException]

theorem r891GammaL3_holds :
    R891GammaL3 := by
  intro X _ _ p f h1 h4 h E hE hE9
  have hp : p.Prime := h.admissible.1
  have hf : 1 ≤ f := h.admissible.2.1
  obtain ⟨hv, ⟨e⟩⟩ := psl_three_catalog_equiv hp hf h h1
  let q : TauCeti.PrimePower := ⟨p, f, hp, hf⟩
  let d : TauCeti.ValidLieTypeIndex := ⟨TauCeti.LieTypeIndex.A 2 q, hv⟩
  have hchar : d.1.characteristic = p := TauCeti.LieTypeIndex.characteristic_A 2 q
  have h3 : 3 ≠ d.1.characteristic := by
    rw [hchar]
    rintro rfl
    have h0 : 3 ^ f % 3 = 0 := Nat.mod_eq_zero_of_dvd (dvd_pow_self 3 (by omega))
    omega
  have hd : CFSG.LieType.SeitzGeneration.IsClassicalIndex d.1 := trivial
  have hex : ¬ CFSG.AGLEmbeddingD2.IsD2SeitzException 3 d.1 := by
    simpa [d, q] using not_isD2SeitzException_A_two hp hf h4
  have hs : IsSimpleGroup X :=
    CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) h
  have hnab := exists_noncommuting_of_card_nine (X := X) (E := E) hE9
  have hcore := glbCore_eq_top_of_classicalIndex hs hnab d e hd h3 hex E hE hE9
  simpa [rankThreeGamma] using hcore

theorem r891GammaU3_holds :
    R891GammaU3 := by
  intro X _ _ p f h1 h E hE hE9
  have hp : p.Prime := h.admissible.1
  have hf : 1 ≤ f := h.admissible.2.1
  obtain ⟨hv, ⟨e⟩⟩ := psu_three_catalog_equiv hp hf h
  let q : TauCeti.PrimePower := ⟨p, f, hp, hf⟩
  let d : TauCeti.ValidLieTypeIndex := ⟨TauCeti.LieTypeIndex.twistedA 2 q, hv⟩
  have hchar : d.1.characteristic = p := TauCeti.LieTypeIndex.characteristic_twistedA 2 q
  have h3 : 3 ≠ d.1.characteristic := by
    rw [hchar]
    rintro rfl
    have h0 : 3 ^ f % 3 = 0 := Nat.mod_eq_zero_of_dvd (dvd_pow_self 3 (by omega))
    omega
  have hd : CFSG.LieType.SeitzGeneration.IsClassicalIndex d.1 := trivial
  have hex : ¬ CFSG.AGLEmbeddingD2.IsD2SeitzException 3 d.1 := by
    simpa [d, q] using not_isD2SeitzException_twistedA_two hp hf
  have hs : IsSimpleGroup X :=
    CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) h
  have hnab := exists_noncommuting_of_card_nine (X := X) (E := E) hE9
  have hcore := glbCore_eq_top_of_classicalIndex hs hnab d e hd h3 hex E hE hE9
  simpa [rankThreeGamma] using hcore

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
