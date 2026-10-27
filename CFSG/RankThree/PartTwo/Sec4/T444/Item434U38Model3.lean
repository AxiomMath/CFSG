module

public import Certificates.Certificate188001
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434U38Facts
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434U38Model2
public import CFSG.Models.PGLOrders
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.SignalizerFunctorTheorem.McBride.Models.UnitaryOut
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.RankOneModelTransport
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionModels
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointDataModelWitness
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSemilinearDataCompatibility
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasFive
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalStandardFormsRegular
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalTailModelBorel
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalTailPolar
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenOrthogonalModel
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.II.theorem_1_12
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldFixedSubfieldCard
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis

public section

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates CFSG.Certificates.Native
  CFSG.RankThree.Native CFSG.RankThree.PartOne CFSG.Monster.B.Fischer CFSG.YGroups
  CFSG.BenderSuzuki.MatrixGroups CFSG.BenderSuzuki.External CFSG.UnitaryThreeRecognition.Model

namespace CFSG.RankThree.PartTwo.Sec4.Item434U38

@[expose] def X' : Subgroup (Equiv.Perm (Fin 513)) := arrClosure 513 gensX

theorem gensX_size : gensX.size = 7 := by
  simp [gensX, gensO_size]

theorem strong3_size : strong3.size = 11 := by simp [strong3, gensX_size]

theorem strong3_getElem (i : ℕ) (hi : i < 7) : strong3[i]! = gensX[i]! := by
  have hi' : i < gensX.size := by rw [gensX_size]; exact hi
  rw [getElem!_pos strong3 i (by rw [strong3_size]; omega), getElem!_pos gensX i hi']
  simp only [strong3]
  rw [Array.getElem_append_left hi']

theorem gensX_getElem (i : ℕ) (hi : i < 7) : gensX[i]! = gensO[i]! := by
  have hi' : i < gensO.size := by rw [gensO_size]; omega
  have hi'' : i < gensX.size := by rw [gensX_size]; exact hi
  rw [getElem!_pos gensX i hi'', getElem!_pos gensO i hi']
  simp [gensX, Array.getElem_extract]

theorem base3L_nodup : base3L.Nodup := by decide

theorem hk3 : 7 ≤ strong3.size := by rw [strong3_size]; omega

@[expose] noncomputable def Q3 : RawSchreierDatum 513 :=
  RawSchreierDatum.ofArrays 513 (by norm_num) strong3 7 hk3 base3L base3L_nodup words3

theorem Q3_group : Q3.originalSubgroup = X' :=
  originalSubgroup_ofArrays_eq_arrClosure gensX_size (fun i hi => strong3_getElem i hi)

section Chain3

theorem chain3_ok :
    rawChainOK 513 (strong3.extract 0 7) strong3 (base3L.map Fin.val).toArray words3 1 = true :=
  Certificates.certificate188002.chain.1.1

theorem chain3_sizes :
    rawOrbitSizes 513 strong3 (base3L.map Fin.val).toArray = [513, 512, 7, 3] := Certificates.certificate188002.chain.1.2

theorem Q3_arrays :
    ChainArrays Q3 (strong3.extract 0 7) strong3 (base3L.map Fin.val).toArray words3 :=
  chainArrays_ofArrays (chainCheckFacts chain3_ok).strong_inv

theorem Q3_valid : ValidSchreier Q3 :=
  (validSchreier_of_chainOK Q3_arrays (by norm_num) chain3_ok).1

theorem card_X' : Nat.card X' = 5515776 := by
  have h := card_arrClosure_of_rawChainOK (n := 513) (by norm_num) (O := gensX) (S := strong3)
    (W := words3) (base := base3L) base3L_nodup (chunks := 1) (by norm_num)
    (by rw [gensX_size]; exact hk3)
    (fun i hi => strong3_getElem i (by rw [gensX_size] at hi; exact hi))
    (by rw [gensX_size]; exact chain3_ok)
  rw [chain3_sizes] at h
  exact h

theorem Q3_baseCount : Q3.baseCount = 4 := by
  change base3L.length = 4
  rfl

theorem X'_twoTransitive :
    ∀ a b a' b' : Fin 513, a ≠ b → a' ≠ b' → ∃ g ∈ X', g a = a' ∧ g b = b' := by
  have hsz := (validSchreier_of_chainOK Q3_arrays (by norm_num) chain3_ok).2
  have hlev : ((rawLevels 513 strong3 (base3L.map Fin.val).toArray).toList.map
      fun L => L.pts.size) = [513, 512, 7, 3] := chain3_sizes
  have h0 : Q3.orbitSize ⟨0, by rw [Q3_baseCount]; omega⟩ = 513 := by
    rw [hsz ⟨0, by rw [Q3_baseCount]; omega⟩]
    exact levels_size_get hlev (i := 0) (by simp)
  have h1 : Q3.orbitSize ⟨1, by rw [Q3_baseCount]; omega⟩ = 512 := by
    rw [hsz ⟨1, by rw [Q3_baseCount]; omega⟩]
    exact levels_size_get hlev (i := 1) (by simp)
  rw [← Q3_group]
  exact chain_twoTransitive Q3 Q3_valid (by rw [Q3_baseCount]; omega) h0 h1

end Chain3

theorem conj_closure_mem {G : Type*} [Group G] (S : Set G) (K : Subgroup G) (g : G)
    (hS : ∀ s ∈ S, g * s * g⁻¹ ∈ K) : ∀ h ∈ Subgroup.closure S, g * h * g⁻¹ ∈ K := by
  intro h hh
  induction hh using Subgroup.closure_induction with
  | mem x hx => exact hS x hx
  | one => simpa using K.one_mem
  | mul x y _ _ hx hy =>
    have : g * (x * y) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) := by group
    rw [this]
    exact K.mul_mem hx hy
  | inv x _ hx =>
    have : g * x⁻¹ * g⁻¹ = (g * x * g⁻¹)⁻¹ := by group
    rw [this]
    exact K.inv_mem hx

section Normalizer

theorem sift3_mem {t : Array ℕ} {T : Equiv.Perm (Fin 513)} (hT : Rep 513 t T)
    (hs : siftA 513 (rawLevels 513 strong3 (base3L.map Fin.val).toArray)
      (base3L.map Fin.val).toArray 0 t = true) : T ∈ X' := by
  rw [← Q3_group]
  exact mem_of_siftA Q3_arrays chain3_ok hT hs

theorem gensO_valid (k : ℕ) (hk : k < 9) : validA 513 gensO[k]! = true :=
  allLt_spec Certificates.certificate188002.chain.2.1 hk

theorem conj_gen_mem (a : ℕ) (ha : a < 2) (i : ℕ) (hi : i < 7) :
    permOfArr 513 gensO[7 + a]! * permOfArr 513 gensO[i]! * (permOfArr 513 gensO[7 + a]!)⁻¹ ∈ X' ∧
      (permOfArr 513 gensO[7 + a]!)⁻¹ * permOfArr 513 gensO[i]! * permOfArr 513 gensO[7 + a]! ∈ X' := by
  have h1 := allLt_spec Certificates.certificate188002.chain.2.2 ha
  have h2 := allLt_spec h1 hi
  rw [Bool.and_eq_true] at h2
  have hg : validA 513 gensO[7 + a]! = true := gensO_valid (7 + a) (by omega)
  have hy : validA 513 gensO[i]! = true := gensO_valid i (by omega)
  exact ⟨sift3_mem (rep_conjA hg (rep_of_validA hy)) h2.1,
    sift3_mem (rep_conjInvA hg (rep_of_validA hy)) h2.2⟩

theorem outer_mem_normalizer (a : ℕ) (ha : a < 2) :
    permOfArr 513 gensO[7 + a]! ∈ Subgroup.normalizer (X' : Set (Equiv.Perm (Fin 513))) := by
  set g := permOfArr 513 gensO[7 + a]! with hg
  have hgen : ∀ s ∈ {x | ∃ k < gensX.size, permOfArr 513 gensX[k]! = x}, g * s * g⁻¹ ∈ X' := by
    rintro s ⟨k, hk, rfl⟩
    have hk7 : k < 7 := by rw [gensX_size] at hk; exact hk
    rw [gensX_getElem k hk7]
    exact (conj_gen_mem a ha k hk7).1
  have hgen' : ∀ s ∈ {x | ∃ k < gensX.size, permOfArr 513 gensX[k]! = x}, g⁻¹ * s * g⁻¹⁻¹ ∈ X' := by
    rintro s ⟨k, hk, rfl⟩
    have hk7 : k < 7 := by rw [gensX_size] at hk; exact hk
    rw [gensX_getElem k hk7, inv_inv]
    exact (conj_gen_mem a ha k hk7).2
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    exact conj_closure_mem _ X' g hgen h hh
  · intro hh
    have := conj_closure_mem _ X' g⁻¹ hgen' (g * h * g⁻¹) hh
    simpa [mul_assoc] using this

theorem U38G_le_normalizer : U38G ≤ Subgroup.normalizer (X' : Set (Equiv.Perm (Fin 513))) := by
  unfold U38G arrClosure
  rw [Subgroup.closure_le]
  rintro _ ⟨k, hk, rfl⟩
  have hk9 : k < 9 := by rw [gensO_size] at hk; exact hk
  by_cases h7 : k < 7
  · have hmem : permOfArr 513 gensO[k]! ∈ X' := by
      apply Subgroup.subset_closure
      refine ⟨k, by rw [gensX_size]; exact h7, ?_⟩
      rw [gensX_getElem k h7]
    exact Subgroup.le_normalizer hmem
  · obtain ⟨a, ha, rfl⟩ : ∃ a, a < 2 ∧ k = 7 + a := ⟨k - 7, by omega, by omega⟩
    exact outer_mem_normalizer a ha

end Normalizer

theorem eq_one_of_commutes_twoTransitive {n : ℕ} (hn : 3 ≤ n) {X : Subgroup (Equiv.Perm (Fin n))}
    (h2 : ∀ a b a' b' : Fin n, a ≠ b → a' ≠ b' → ∃ g ∈ X, g a = a' ∧ g b = b')
    {g : Equiv.Perm (Fin n)} (hg : ∀ x ∈ X, g * x = x * g) : g = 1 := by
  refine Equiv.ext fun a => ?_
  show g a = a
  by_contra hne
  have hne' : g a ≠ a := hne
  have hcard : ({a, g a} : Finset (Fin n)).card < (Finset.univ : Finset (Fin n)).card := by
    calc ({a, g a} : Finset (Fin n)).card ≤ 2 := Finset.card_le_two
      _ < n := by omega
      _ = (Finset.univ : Finset (Fin n)).card := by simp
  obtain ⟨c, -, hc⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
  have hca : c ≠ a := fun h => hc (by simp [h])
  have hcb : c ≠ g a := fun h => hc (by simp [h])
  obtain ⟨x, hx, hxa, hxb⟩ := h2 a (g a) a c (Ne.symm hne') (Ne.symm hca)
  have := congrArg (fun σ : Equiv.Perm (Fin n) => σ a) (hg x hx)
  simp only [Equiv.Perm.mul_apply, hxa, hxb] at this
  exact hcb this.symm

section Rho

@[expose] noncomputable def rhoU38 : U38G →* MulAut X' :=
  (Subgroup.normalizerMonoidHom (H := X')).comp (Subgroup.inclusion U38G_le_normalizer)

theorem rhoU38_apply (g : U38G) (x : X') :
    ((rhoU38 g x : X') : Equiv.Perm (Fin 513)) =
      (g : Equiv.Perm (Fin 513)) * x * (g : Equiv.Perm (Fin 513))⁻¹ :=
  rfl

theorem rhoU38_injective : Function.Injective (rhoU38) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  have hcomm : ∀ x ∈ X', (g : Equiv.Perm (Fin 513)) * x = x * g := by
    intro x hx
    have h := congrArg (fun φ : MulAut X' => ((φ ⟨x, hx⟩ : X') : Equiv.Perm (Fin 513))) hg
    simp only [rhoU38_apply, MulAut.one_apply] at h
    exact mul_inv_eq_iff_eq_mul.1 h
  exact Subtype.ext (eq_one_of_commutes_twoTransitive (by norm_num) X'_twoTransitive hcomm)

end Rho

section Psi

theorem hK8 : Nat.card GF64 = 8 ^ 2 := by
  rw [card_GF64]; norm_num

theorem hfix8 : Nat.card {x : GF64 // J64.conj x = x} = 8 := by
  rw [J64_fix]; norm_num

abbrev P0 : Type := ProjectiveSpecialUnitaryMatrixGroup J64

instance : Finite P0 := inferInstance

theorem card_P0 : Nat.card P0 = 5515776 := by
  rw [card_psu J64 J64_form 8 hK8 hfix8]
  norm_num

@[expose] noncomputable def psiU38 : P0 →* Equiv.Perm (Fin 513) :=
  (Equiv.permCongrHom ptsE).toMonoidHom.comp (MulAction.toPermHom P0 (IsoPoint J64))

theorem psiU38_apply (g : P0) (j : Fin 513) : psiU38 g j = ptsE (g • ptsE.symm j) := rfl

theorem psiU38_injective : Function.Injective (psiU38) := by
  haveI := faithfulSMul_isoPoint J64 J64_form 8 hK8 hfix8
  have h1 : Function.Injective (MulAction.toPermHom P0 (IsoPoint J64)) :=
    MulAction.toPerm_injective
  exact (Equiv.permCongrHom ptsE).injective.comp h1

theorem psiU38_genElt (k : Fin 7) : psiU38 (genElt k) = permOfArr 513 gensO[k.val]! := by
  refine Equiv.ext fun j => ?_
  rw [psiU38_apply]
  have := genElt_smul k (ptsE.symm j)
  rw [Equiv.apply_symm_apply] at this
  exact this

theorem X'_eq_range : X' = (psiU38).range := by
  have hle : X' ≤ (psiU38).range := by
    unfold X' arrClosure
    rw [Subgroup.closure_le]
    rintro _ ⟨k, hk, rfl⟩
    have hk7 : k < 7 := by rw [gensX_size] at hk; exact hk
    rw [gensX_getElem k hk7]
    exact ⟨genElt ⟨k, hk7⟩, psiU38_genElt ⟨k, hk7⟩⟩
  have hcard : Nat.card ((psiU38).range) = 5515776 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective psiU38_injective).toEquiv, card_P0]
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [hcard, card_X'])

end Psi

section Iso

open CFSG.Open CFSG.Open.StatedAPI CFSG.Blueprint.EvenSource
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)
open CFSG.PGLModel (projSU)

theorem statedModel_P0 : StatedClassicalModel P0 .PSU 3 2 3 := by
  obtain ⟨e⟩ := nonempty_psu_equiv_statedProj_of_conj_eq_pow J64 2 3 Nat.prime_two
    card_GF64 (fun x => by rw [J64_conj, conj8_eq_pow]; norm_num)
  exact ⟨⟨Nat.prime_two, by norm_num, le_rfl, by decide⟩, GF64, inferInstance, inferInstance,
    card_GF64, ⟨e⟩⟩

theorem nonempty_equiv_P0 {X : Type} [Group X] (hX : Nonempty (X ≃* projSU 3 2 3)) :
    Nonempty (X ≃* P0) := by
  obtain ⟨e⟩ := hX
  exact nonempty_mulEquiv_of_statedClassicalModel
    (CFSG.PGLModel.statedClassicalModel_of_mulEquiv_projSU
      ⟨Nat.prime_two, by norm_num, le_rfl, by decide⟩ e) statedModel_P0

theorem nonempty_equiv_X' {X : Type} [Group X] (hX : Nonempty (X ≃* projSU 3 2 3)) :
    Nonempty (X ≃* X') := by
  obtain ⟨e⟩ := nonempty_equiv_P0 hX
  refine ⟨e.trans ((MonoidHom.ofInjective psiU38_injective).trans
    (MulEquiv.subgroupCongr X'_eq_range.symm))⟩

end Iso

section Card

open CFSG.Open CFSG.Open.StatedAPI CFSG.Blueprint.EvenSource
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)
open CFSG.PGLModel (projSU)

theorem statedModel_PSU3 : StatedClassicalModel (↥(CFSG.Open.PSU3 2 3)) .PSU 3 2 3 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨⟨Nat.prime_two, by norm_num, le_rfl, by decide⟩, GaloisField 2 (2 * 3), inferInstance,
    inferInstance, ?_, ⟨?_⟩⟩
  · rw [GaloisField.card 2 (2 * 3) (by norm_num), ← pow_mul]
  · exact (CFSG.ShultStronglyClosedTI.glaSUCanonicalEquivNative 3).symm

theorem card_mulAut_le {X : Type} [Group X] [Finite X] (hX : Nonempty (X ≃* projSU 3 2 3)) :
    Nat.card (MulAut X) ≤ 99283968 := by
  obtain ⟨e⟩ := hX
  have hXm := CFSG.PGLModel.statedClassicalModel_of_mulEquiv_projSU
    ⟨Nat.prime_two, by norm_num, le_rfl, by decide⟩ e
  obtain ⟨eP⟩ := nonempty_mulEquiv_of_statedClassicalModel hXm statedModel_PSU3
  have hout : Nat.card (Outer X) = 18 := by
    rw [Nat.card_congr
      (CFSG.ComponentClassification.OuterAutomorphisms.equivalence eP).toEquiv,
      CFSG.SignalizerFunctorTheorem.McBride.UnitaryOut.card_outer_psu3 (p := 3) (by norm_num)]
    norm_num
  have hXcard : Nat.card X = 5515776 := by
    rw [Nat.card_congr e.toEquiv, CFSG.PGLModel.card_projSU_three_eight]
  have h1 : Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.inner X) ≤ Nat.card X := by
    have hsurj : Function.Surjective (MulAut.conj : X →* MulAut X).rangeRestrict :=
      MonoidHom.rangeRestrict_surjective _
    exact Nat.card_le_card_of_surjective _ hsurj
  have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup
    (CFSG.ComponentClassification.OuterAutomorphisms.inner X)
  have h3 : Nat.card (MulAut X ⧸ CFSG.ComponentClassification.OuterAutomorphisms.inner X) = 18 :=
    hout
  rw [h2, h3]
  calc 18 * Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.inner X) ≤
        18 * Nat.card X := Nat.mul_le_mul_left _ h1
    _ = 99283968 := by rw [hXcard]

end Card

section Final

open CFSG.PGLModel (projSU)

theorem rhoU38_bijective {X : Type} [Group X] [Finite X] (hX : Nonempty (X ≃* projSU 3 2 3)) :
    Function.Bijective (rhoU38) := by
  obtain ⟨eX⟩ := nonempty_equiv_X' hX
  have hc : Nat.card (MulAut X') ≤ 99283968 := by
    rw [← Nat.card_congr (MulAut.congr eX).toEquiv]
    exact card_mulAut_le hX
  have hinj := rhoU38_injective
  refine hinj.bijective_of_nat_card_le ?_
  rw [card_U38G]
  exact hc

theorem exists_injective_hom {X : Type} [Group X] [Finite X] (hX : Nonempty (X ≃* projSU 3 2 3)) :
    ∃ κ : MulAut X →* U38G, Function.Injective κ := by
  obtain ⟨eX⟩ := nonempty_equiv_X' hX
  let ρ' : U38G ≃* MulAut X' := MulEquiv.ofBijective rhoU38 (rhoU38_bijective hX)
  exact ⟨ρ'.symm.toMonoidHom.comp (MulAut.congr eX).toMonoidHom,
    ρ'.symm.injective.comp (MulAut.congr eX).injective⟩

theorem u38_K0_of_equiv {X : Type} [Group X] [Finite X] (hX : Nonempty (X ≃* projSU 3 2 3)) :
    ∀ E : Subgroup (MulAut X), CFSG.Open.IsElemAbelian 3 E → Nat.card E = 27 →
      ∀ Y : Subgroup (MulAut X), ¬ 3 ∣ Nat.card Y →
        E ≤ Subgroup.normalizer (Y : Set (MulAut X)) → Y = ⊥ := by
  obtain ⟨κ, hκ⟩ := exists_injective_hom hX
  intro E hE hE27 Y hY3 hEY
  have hmap : Y.map κ = ⊥ := by
    refine u38_K0_perm (E.map κ) (Y.map κ) (hE.map κ)
      (by rw [Subgroup.card_map_of_injective hκ, hE27])
      (by rw [Subgroup.card_map_of_injective hκ]; exact hY3) ?_
    intro x hx
    obtain ⟨e, he, rfl⟩ := Subgroup.mem_map.1 hx
    rw [Subgroup.mem_normalizer_iff]
    intro z
    have hnorm := Subgroup.mem_normalizer_iff.1 (hEY he)
    constructor
    · intro hz
      obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hz
      exact Subgroup.mem_map.2 ⟨e * y * e⁻¹, (hnorm y).1 hy, by simp⟩
    · intro hz
      obtain ⟨w, hw, hwz⟩ := Subgroup.mem_map.1 hz
      have hnorm' := Subgroup.mem_normalizer_iff.1 (hEY (E.inv_mem he))
      have hw' : e⁻¹ * w * e ∈ Y := by
        have := (hnorm' w).1 hw
        simpa using this
      refine Subgroup.mem_map.2 ⟨e⁻¹ * w * e, hw', ?_⟩
      rw [map_mul, map_mul, map_inv, hwz]
      group
  exact (Subgroup.map_eq_bot_iff_of_injective _ hκ).1 hmap

end Final

end CFSG.RankThree.PartTwo.Sec4.Item434U38
