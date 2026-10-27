module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23bSL3Natural
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplitRankOneIsL2
public import CFSG.GroupTheory.PCoreSurjective

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.Quasithin Subgroup CFSG.LocalAnalysis.UniquenessCase.PartTwo
open QuadraticMap
open scoped Pointwise commutatorElement Matrix

@[expose] def OmegaPlus6Line (W : Type) [CommGroup W] (H : Subgroup (MulAut W)) (n : ℕ) : Prop :=
  letI : MulDistribMulAction ↥H W := MulDistribMulAction.compHom W H.subtype
  letI : MulAction ↥H W := MulAction.compHom W H.subtype
  letI : MulAction ↥H (Set W) := Set.mulActionSet
  ∀ S : Sylow 2 ↥H,
    letI : MulDistribMulAction ↥S W :=
      MulDistribMulAction.compHom W (H.subtype.comp (S : Subgroup ↥H).subtype)
    let ℓ : Subgroup W := fixedPointSubgroup ↥S W
    let Pℓ : Subgroup ↥H := MulAction.stabilizer ↥H (ℓ : Set W)
    ∀ Tstar : Subgroup (MulAut W),
      Tstar ≤ Subgroup.normalizer (H : Set (MulAut W)) →
      IsPGroup 2 ↥Tstar →
      (S : Subgroup ↥H).map H.subtype ≤ Tstar →
      let Good : Subgroup ↥H → Prop := fun Pstar =>
        IsParabolicTwo ↥H Pstar ∧ (S : Subgroup ↥H) ≤ Pstar ∧
        (∀ t ∈ Tstar,
          (Pstar.map H.subtype).map (MulAut.conj t).toMonoidHom = Pstar.map H.subtype) ∧
        ¬ Pstar ≤ Pℓ
      ∀ Pstar : Subgroup ↥H, Minimal Good Pstar →
        Pstar ≠ ⊤ ∧ (IsL2 (Bar2 (Hinf Pstar)) n ∨ (n = 1 ∧ Hinf Pstar = ⊥))

section Transport

variable {W V : Type} [CommGroup W] [CommGroup V] [Finite W] [Finite V]

theorem omegaPlus6Line_of_map_congr (H : Subgroup (MulAut W)) (H' : Subgroup (MulAut V))
    (n : ℕ) (e : W ≃* V) (hH' : H' = H.map (CFSG.Quasithin.H.congrHom e))
    (h : OmegaPlus6Line V H' n) : OmegaPlus6Line W H n := by
  letI : MulDistribMulAction ↥H W := MulDistribMulAction.compHom W H.subtype
  letI : MulAction ↥H W := MulAction.compHom W H.subtype
  letI : MulAction ↥H (Set W) := Set.mulActionSet
  intro S
  letI : MulDistribMulAction ↥S W :=
    MulDistribMulAction.compHom W (H.subtype.comp (S : Subgroup ↥H).subtype)
  let ℓ : Subgroup W := fixedPointSubgroup ↥S W
  let Pℓ : Subgroup ↥H := MulAction.stabilizer ↥H (ℓ : Set W)
  dsimp only
  intro Tstar hTnorm hT2 hST
  letI : MulDistribMulAction ↥H' V := MulDistribMulAction.compHom V H'.subtype
  letI : MulAction ↥H' V := MulAction.compHom V H'.subtype
  letI : MulAction ↥H' (Set V) := Set.mulActionSet
  let eH : ↥H ≃* ↥H' :=
    ((MulAut.congr e).subgroupMap H).trans (MulEquiv.subgroupCongr hH'.symm)
  let S' : Sylow 2 ↥H' := S.mapSurjective (f := eH.toMonoidHom) eH.surjective
  letI : MulDistribMulAction ↥S' V :=
    MulDistribMulAction.compHom V (H'.subtype.comp (S' : Subgroup ↥H').subtype)
  let ℓ' : Subgroup V := fixedPointSubgroup ↥S' V
  let Pℓ' : Subgroup ↥H' := MulAction.stabilizer ↥H' (ℓ' : Set V)
  let Tstar' : Subgroup (MulAut V) := Tstar.map (CFSG.Quasithin.H.congrHom e)
  have heHcoe : ∀ g : ↥H, (eH g : MulAut V) = MulAut.congr e (g : MulAut W) := by
    intro g
    change ((MulEquiv.subgroupMap (MulAut.congr e) H g : MulAut V)) =
      MulAut.congr e (g : MulAut W)
    rw [MulEquiv.coe_subgroupMap_apply]
  have hcomp : H'.subtype.comp eH.toMonoidHom =
      (CFSG.Quasithin.H.congrHom e).comp H.subtype :=
    MonoidHom.ext fun g => heHcoe g
  have hmapEH : ∀ P : Subgroup ↥H, (P.map eH.toMonoidHom).map eH.symm.toMonoidHom = P := by
    intro P
    rw [Subgroup.map_map]
    convert Subgroup.map_id P using 2
    ext x
    simp
  have hmapEH' : ∀ P : Subgroup ↥H', (P.map eH.symm.toMonoidHom).map eH.toMonoidHom = P := by
    intro P
    rw [Subgroup.map_map]
    convert Subgroup.map_id P using 2
    ext x
    simp
  have hℓ : ℓ = CFSG.Quasithin.fixV ((S : Subgroup ↥H).map H.subtype) := by
    ext w
    constructor
    · intro hw x hx
      obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.mp hx
      have h := hw ⟨s, hs⟩
      rw [MulAction.compHom_smul_def] at h
      change (s : MulAut W) w = w at h
      exact h
    · intro hw s
      have h := hw (s : MulAut W) (Subgroup.mem_map_of_mem _ s.2)
      rw [MulAction.compHom_smul_def]
      change (s : MulAut W) w = w
      exact h
  have hℓ' : ℓ' = CFSG.Quasithin.fixV ((S' : Subgroup ↥H').map H'.subtype) := by
    ext v
    constructor
    · intro hv x hx
      obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.mp hx
      have h := hv ⟨s, hs⟩
      rw [MulAction.compHom_smul_def] at h
      change (s : MulAut V) v = v at h
      exact h
    · intro hv s
      have h := hv (s : MulAut V) (Subgroup.mem_map_of_mem _ s.2)
      rw [MulAction.compHom_smul_def]
      change (s : MulAut V) v = v
      exact h
  have hS'coe : (S' : Subgroup ↥H') = (S : Subgroup ↥H).map eH.toMonoidHom :=
    Sylow.coe_mapSurjective _ _
  have hA : ((S : Subgroup ↥H).map eH.toMonoidHom).map H'.subtype =
      ((S : Subgroup ↥H).map H.subtype).map (CFSG.Quasithin.H.congrHom e) := by
    rw [Subgroup.map_map, Subgroup.map_map, hcomp]
  have hfix : ℓ' = ℓ.map e.toMonoidHom := by
    rw [hℓ', hS'coe, hA, hℓ, CFSG.Quasithin.H.fixV_map_congrHom e]
  have hstab : Pℓ' = Pℓ.map eH.toMonoidHom := by
    have hfixset : Equiv.setCongr e.toEquiv (ℓ : Set W) = (ℓ' : Set V) := by
      rw [hfix]
      rfl
    have h := CFSG.ProperTwoGeneratedCore.LocalCriterionNumerator.stabilizer_map_of_equivariant
      eH (Equiv.setCongr e.toEquiv) ?_ (ℓ : Set W)
    · rw [hfixset] at h
      exact h.symm
    · intro g z
      change Equiv.setCongr e.toEquiv ((g : MulAut W) '' z) =
        (eH g : MulAut V) '' (Equiv.setCongr e.toEquiv z)
      rw [heHcoe g]
      ext y
      simp [Equiv.setCongr, MulAut.congr_apply, Set.image_image]
  have hTnorm' : Tstar' ≤ Subgroup.normalizer (H' : Set (MulAut V)) := by
    rw [hH', ← Subgroup.map_equiv_normalizer_eq H (MulAut.congr e)]
    exact Subgroup.map_mono hTnorm
  have hT2' : IsPGroup 2 ↥Tstar' := hT2.map (CFSG.Quasithin.H.congrHom e)
  have hST' : (S' : Subgroup ↥H').map H'.subtype ≤ Tstar' := by
    rw [hS'coe, Subgroup.map_map, hcomp, ← Subgroup.map_map]
    exact Subgroup.map_mono hST
  let Good : Subgroup ↥H → Prop := fun Pstar =>
    IsParabolicTwo ↥H Pstar ∧ (S : Subgroup ↥H) ≤ Pstar ∧
    (∀ t ∈ Tstar,
      (Pstar.map H.subtype).map (MulAut.conj t).toMonoidHom = Pstar.map H.subtype) ∧
    ¬ Pstar ≤ Pℓ
  let Good' : Subgroup ↥H' → Prop := fun Pstar =>
    IsParabolicTwo ↥H' Pstar ∧ (S' : Subgroup ↥H') ≤ Pstar ∧
    (∀ t ∈ Tstar',
      (Pstar.map H'.subtype).map (MulAut.conj t).toMonoidHom = Pstar.map H'.subtype) ∧
    ¬ Pstar ≤ Pℓ'
  have hconj : ∀ t : MulAut W,
      (MulAut.conj (CFSG.Quasithin.H.congrHom e t)).toMonoidHom.comp
        (CFSG.Quasithin.H.congrHom e) =
      (CFSG.Quasithin.H.congrHom e).comp (MulAut.conj t).toMonoidHom := by
    intro t
    ext x
    simp [MulAut.conj_apply]
  have hgoodmap : ∀ Pstar : Subgroup ↥H, Good Pstar ↔ Good' (Pstar.map eH.toMonoidHom) := by
    intro Pstar
    have hpar : IsParabolicTwo ↥H Pstar ↔ IsParabolicTwo ↥H' (Pstar.map eH.toMonoidHom) :=
      ⟨fun hp => hp.map eH.toMonoidHom eH.surjective, fun hp => by
        have h1 : IsParabolicTwo ↥H ((Pstar.map eH.toMonoidHom).map eH.symm.toMonoidHom) :=
          hp.map eH.symm.toMonoidHom eH.symm.surjective
        rwa [hmapEH] at h1⟩
    have hSle : (S : Subgroup ↥H) ≤ Pstar ↔
        (S' : Subgroup ↥H') ≤ Pstar.map eH.toMonoidHom := by
      rw [hS'coe, Subgroup.map_le_map_iff_of_injective eH.injective]
    have hPℓle : Pstar ≤ Pℓ ↔ Pstar.map eH.toMonoidHom ≤ Pℓ' := by
      rw [hstab, Subgroup.map_le_map_iff_of_injective eH.injective]
    have hA' : (Pstar.map eH.toMonoidHom).map H'.subtype =
        (Pstar.map H.subtype).map (CFSG.Quasithin.H.congrHom e) := by
      rw [Subgroup.map_map, Subgroup.map_map, hcomp]
    have hTinv : (∀ t ∈ Tstar,
        (Pstar.map H.subtype).map (MulAut.conj t).toMonoidHom = Pstar.map H.subtype) ↔
        (∀ t ∈ Tstar',
          ((Pstar.map eH.toMonoidHom).map H'.subtype).map (MulAut.conj t).toMonoidHom =
            (Pstar.map eH.toMonoidHom).map H'.subtype) := by
      constructor
      · rintro hh t' ht'
        obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.mp ht'
        rw [hA']
        conv_lhs => rw [Subgroup.map_map, hconj t, ← Subgroup.map_map]
        rw [hh t ht]
      · rintro hh t ht
        have h1 := hh (CFSG.Quasithin.H.congrHom e t) (Subgroup.mem_map_of_mem _ ht)
        rw [hA'] at h1
        conv_lhs at h1 => rw [Subgroup.map_map, hconj t, ← Subgroup.map_map]
        exact (Subgroup.map_injective (CFSG.Quasithin.H.congrHom_injective e)).eq_iff.mp h1
    exact and_congr hpar (and_congr hSle (and_congr hTinv (not_congr hPℓle)))
  intro Pstar hmin
  have hgood : Good Pstar := hmin.1
  have hmin' : Minimal Good' (Pstar.map eH.toMonoidHom) := by
    refine ⟨(hgoodmap Pstar).mp hgood, ?_⟩
    intro Q' hQ' hQle
    have hQ : Good (Q'.map eH.symm.toMonoidHom) :=
      (hgoodmap _).mpr (by rwa [hmapEH'])
    have hQle' : Q'.map eH.symm.toMonoidHom ≤ Pstar := by
      have h2 := Subgroup.map_mono (f := eH.symm.toMonoidHom) hQle
      rwa [hmapEH] at h2
    have hle' : Pstar.map eH.toMonoidHom ≤ Q' := by
      have h2 := Subgroup.map_mono (f := eH.toMonoidHom) (hmin.2 hQ hQle')
      rwa [hmapEH'] at h2
    exact hle'
  obtain ⟨hne', hres'⟩ := h S' Tstar' hTnorm' hT2' hST' (Pstar.map eH.toMonoidHom) hmin'
  refine ⟨?_, ?_⟩
  · intro htop
    apply hne'
    rw [htop, Subgroup.map_top_of_surjective _ eH.surjective]
  · rcases hres' with hL2 | ⟨hn, hbot⟩
    · left
      have hHinf : (Hinf Pstar).map eH.toMonoidHom = Hinf (Pstar.map eH.toMonoidHom) :=
        Hinf_map eH.toMonoidHom Pstar
      let eSub : ↥(Hinf Pstar) ≃* ↥(Hinf (Pstar.map eH.toMonoidHom)) :=
        ((Hinf Pstar).equivMapOfInjective eH.toMonoidHom eH.injective).trans
          (MulEquiv.subgroupCongr hHinf)
      obtain ⟨ebar⟩ := nonempty_bar2_mulEquiv_of_equiv eSub
      exact CFSG.Blueprint.LieModel.of_mulEquiv ebar.symm hL2
    · right
      refine ⟨hn, ?_⟩
      have hHinf : (Hinf Pstar).map eH.toMonoidHom = Hinf (Pstar.map eH.toMonoidHom) :=
        Hinf_map eH.toMonoidHom Pstar
      rw [← hHinf] at hbot
      exact (Subgroup.map_eq_bot_iff_of_injective (H := Hinf Pstar)
        (f := eH.toMonoidHom) eH.injective).mp hbot

end Transport

section Model

open CFSG.Quasithin.H

variable {ι : Type} {K : Type} [Field K]

@[expose] noncomputable def linMulAut (f : (ι → K) ≃ₗ[K] (ι → K)) : MulAut (StdMod ι K) :=
  (LinearEquiv.toAddEquiv f).toMultiplicative

theorem linMulAut_apply (f : (ι → K) ≃ₗ[K] (ι → K)) (v : ι → K) :
    Multiplicative.toAdd (linMulAut f (Multiplicative.ofAdd v)) = f v := rfl

theorem linMulAut_apply_ofAdd (f : (ι → K) ≃ₗ[K] (ι → K)) (v : ι → K) :
    linMulAut f (Multiplicative.ofAdd v) = Multiplicative.ofAdd (f v) := rfl

@[expose] noncomputable def linMulAutHom :
    ((ι → K) ≃ₗ[K] (ι → K)) →* MulAut (StdMod ι K) where
  toFun := linMulAut
  map_one' := rfl
  map_mul' f g := rfl

theorem linMulAutHom_apply (f : (ι → K) ≃ₗ[K] (ι → K)) :
    linMulAutHom f = linMulAut f := rfl

theorem linMulAutHom_injective : Function.Injective (linMulAutHom (ι := ι) (K := K)) := by
  intro f g h
  apply LinearEquiv.ext
  intro v
  have h' := congrArg (fun e : MulAut (StdMod ι K) =>
    Multiplicative.toAdd (e (Multiplicative.ofAdd v))) h
  rw [linMulAutHom_apply, linMulAutHom_apply, linMulAut_apply, linMulAut_apply] at h'
  exact h'

theorem linMulAut_toLinEquiv [Fintype ι] [DecidableEq ι] (A : Matrix.GeneralLinearGroup ι K) :
    linMulAut (CFSG.ClassicalGroups.Orthogonal.toLinEquiv ι K A) = matAut A := by
  ext x
  conv_lhs => rw [← ofAdd_toAdd x]
  conv_rhs => rw [← ofAdd_toAdd x]
  rfl

end Model

section NaturalImage

open CFSG.Quasithin.H CFSG.ComponentClassification.CatalogueBOrthogonalPointPlusBorel
open CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin
open CFSG.LocalAnalysis.ComponentInitial

variable {K : Type} [Field K]

theorem map_toLinEquiv_statedOmega_eq_orth {n : ℕ} (h3 : 3 ≤ n) :
    (StatedOmega (StatedQuadPlus n K)).map
        (CFSG.ClassicalGroups.Orthogonal.toLinEquiv (Fin n ⊕ Fin n) K).toMonoidHom =
      orthElementaryGroup (quadPlus n K) := by
  ext f
  constructor
  · rintro ⟨A, hA, rfl⟩
    exact (plusDerivedEquiv n K h3 ⟨A, hA⟩).2
  · intro hf
    let A : StatedOmega (StatedQuadPlus n K) := (plusDerivedEquiv n K h3).symm ⟨f, hf⟩
    refine Subgroup.mem_map.mpr ⟨A.val, A.2, ?_⟩
    have h := plusDerivedEquiv_val n K h3 A
    rw [MulEquiv.apply_symm_apply] at h
    simpa using h.symm

theorem natImage_statedOmega_eq_map {n : ℕ} (h3 : 3 ≤ n) :
    natImage (StatedOmega (StatedQuadPlus n K)) =
      (orthElementaryGroup (quadPlus n K)).map
        (linMulAutHom (ι := Fin n ⊕ Fin n) (K := K)) := by
  have hcomp : (CFSG.Quasithin.H.matHom (ι := Fin n ⊕ Fin n) (K := K)) =
      (linMulAutHom (ι := Fin n ⊕ Fin n) (K := K)).comp
        (CFSG.ClassicalGroups.Orthogonal.toLinEquiv (Fin n ⊕ Fin n) K).toMonoidHom := by
    apply MonoidHom.ext
    intro A
    apply MulEquiv.ext
    intro x
    simp only [MonoidHom.comp_apply, linMulAutHom_apply, matHom_apply]
    change (matAut A) x = (linMulAut
      (CFSG.ClassicalGroups.Orthogonal.toLinEquiv (Fin n ⊕ Fin n) K A)) x
    rw [linMulAut_toLinEquiv]
  rw [CFSG.Quasithin.H.natImage_eq_map]
  conv_lhs => rw [hcomp]
  rw [← Subgroup.map_map, map_toLinEquiv_statedOmega_eq_orth h3]

end NaturalImage

section SplitModel

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit
open CFSG.ComponentClassification.CatalogueBOrthogonalPointPlusBorel
open CFSG.LieType.Universal.Spin CFSG.ClassicalGroups.Orthogonal

variable {K : Type} [Field K] [Finite K] [CharP K 2]

noncomputable abbrev splitE (K : Type) [Field K] : Subgroup
    ((Fin 3 ⊕ Fin 3 → K) ≃ₗ[K] (Fin 3 ⊕ Fin 3 → K)) :=
  orthElementaryGroup (quadPlus 3 K)

noncomputable def splitU (K : Type) [Field K] : Subgroup ↥(splitE K) :=
  (posUnip 3 K).subgroupOf (splitE K)

theorem splitU_isSylow :
    ∃ S : Sylow 2 ↥(splitE K), (S : Subgroup ↥(splitE K)) = splitU K := by
  obtain ⟨S, hS⟩ := posUnip_isSylow (K := K) (p := 2) (r := 3) (by norm_num)
    (fun a ha => map_flag_top_ne_Xstar (K := K) (by norm_num) ha)
  exact ⟨S, hS⟩

theorem normalizer_splitU :
    Subgroup.normalizer (splitU K : Set ↥(splitE K)) =
      (flagStab 3 K).subgroupOf (splitE K) := by
  exact normalizer_posUnip (K := K) (r := 3) (by norm_num)
    (fun a ha => map_flag_top_ne_Xstar (K := K) (by norm_num) ha)

theorem flagStab_eq_borel :
    flagStab 3 K = borel 3 K := by
  refine le_antisymm ?_ ?_
  · intro b hb
    rw [mem_borel]
    obtain ⟨hbE, hbF⟩ := mem_flagStab.mp hb
    refine ⟨hbE, fun i hi hir => ?_⟩
    by_cases hir' : i ≤ 2
    · exact hbF i hi hir'
    · have hi3 : i = 3 := by omega
      subst hi3
      have hbO := orthElementaryGroup_le (quadPlus 3 K) hbE
      have hsing : ∀ v ∈ flag 3 K 3,
          quadPlus 3 K v = 0 := fun v hv => (flag_singular (r := 3) (K := K) 3) v hv
      have hmap : (flag 3 K 3).map
          (b : (Fin 3 ⊕ Fin 3 → K) →ₗ[K] (Fin 3 ⊕ Fin 3 → K)) = flag 3 K 3 := by
        have h1 : ∀ x ∈ (flag 3 K 3).map
            (b : (Fin 3 ⊕ Fin 3 → K) →ₗ[K] (Fin 3 ⊕ Fin 3 → K)),
            quadPlus 3 K x = 0 := by
          rintro _ ⟨v, hv, rfl⟩
          rw [LinearEquiv.coe_coe, map_of_mem hbO]
          exact hsing v hv
        have h2 : Module.finrank K ((flag 3 K 3).map
            (b : (Fin 3 ⊕ Fin 3 → K) →ₗ[K] (Fin 3 ⊕ Fin 3 → K))) = 3 := by
          rw [LinearEquiv.finrank_map_eq, finrank_flag_of_le le_rfl]
        have hF2 : flag 3 K (3 - 1) ≤ (flag 3 K 3).map
            (b : (Fin 3 ⊕ Fin 3 → K) →ₗ[K] (Fin 3 ⊕ Fin 3 → K)) := by
          have hfix2 : (flag 3 K 2).map
              (b : (Fin 3 ⊕ Fin 3 → K) →ₗ[K] (Fin 3 ⊕ Fin 3 → K)) = flag 3 K 2 :=
            hbF 2 (by norm_num) (by norm_num)
          rw [← hfix2]
          exact Submodule.map_mono (flag_le_flag_of_le (K := K) (by norm_num : 2 ≤ 3))
        rcases eq_flag_top_or_Xstar (K := K) (r := 3) (by norm_num)
          (W := (flag 3 K 3).map
            (b : (Fin 3 ⊕ Fin 3 → K) →ₗ[K] (Fin 3 ⊕ Fin 3 → K))) h1 h2 hF2 with h | h
        · exact h
        · exact absurd h (map_flag_top_ne_Xstar (K := K) (by norm_num) hbE)
      exact hmap
  · intro b hb
    rw [mem_flagStab]
    have h := (mem_borel.mp hb)
    exact ⟨h.1, fun i hi hir => h.2 i hi (by omega)⟩

section PointFix

open CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit

@[expose] def subMulSub (K : Type) [Field K]
    (W : Submodule K (Fin 3 ⊕ Fin 3 → K)) :
    Subgroup (CFSG.Quasithin.H.StdMod (Fin 3 ⊕ Fin 3) K) where
  carrier := {x | Multiplicative.toAdd x ∈ W}
  one_mem' := by simp
  mul_mem' := by
    intro x y hx hy
    change Multiplicative.toAdd (x * y) ∈ W
    rw [toAdd_mul]
    exact W.add_mem hx hy
  inv_mem' := by
    intro x hx
    change Multiplicative.toAdd x⁻¹ ∈ W
    rw [toAdd_inv]
    exact W.neg_mem hx

@[expose] noncomputable def pointSub (K : Type) [Field K] :
    Subgroup (CFSG.Quasithin.H.StdMod (Fin 3 ⊕ Fin 3) K) :=
  subMulSub K (flag 3 K 1)

theorem mem_pointSub {K : Type} [Field K]
    {x : CFSG.Quasithin.H.StdMod (Fin 3 ⊕ Fin 3) K} :
    x ∈ pointSub K ↔ Multiplicative.toAdd x ∈ flag 3 K 1 := Iff.rfl

@[expose] noncomputable def splitH (K : Type) [Field K] :
    Subgroup (MulAut (CFSG.Quasithin.H.StdMod (Fin 3 ⊕ Fin 3) K)) :=
  (splitE K).map (linMulAutHom (ι := Fin 3 ⊕ Fin 3) (K := K))

section FixCoords

open CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin QuadraticMap

variable {K : Type} [Field K] [CharP K 2]

theorem eichler_inl_inr_apply {i j : Fin 3} (hij : i < j)
    (v : Fin 3 ⊕ Fin 3 → K) :
    eichler (quadPlus 3 K) (Pi.single (Sum.inl i) 1) (Pi.single (Sum.inr j) 1) v =
      v + (v (Sum.inr i)) • Pi.single (Sum.inr j) 1 +
        (v (Sum.inl j)) • Pi.single (Sum.inl i) 1 := by
  have hu : quadPlus 3 K (Pi.single (Sum.inl i) 1) = 0 := by
    simp [quadPlus_apply]
  have hw : polar (quadPlus 3 K) (Pi.single (Sum.inl i) 1)
      (Pi.single (Sum.inr j) 1) = 0 := by
    rw [polar_quadPlus_single_inr]
    simp [Pi.single_apply, hij.ne]
  rw [eichler_apply hu hw]
  simp only [polar_quadPlus_single_inl, polar_quadPlus_single_inr, one_smul,
    quadPlus_apply, Pi.single_eq_same, Pi.single_eq_of_ne' (Sum.inl_ne_inr),
    Pi.single_eq_of_ne' (Sum.inr_ne_inl), mul_zero, zero_mul, mul_one,
    Finset.sum_const_zero, add_zero]
  rw [sub_eq_add_neg, ← neg_smul, CharTwo.neg_eq]

theorem eichler_inl_inl_apply {i j : Fin 3} (hij : i < j)
    (v : Fin 3 ⊕ Fin 3 → K) :
    eichler (quadPlus 3 K) (Pi.single (Sum.inl i) 1) (Pi.single (Sum.inl j) 1) v =
      v + (v (Sum.inr i)) • Pi.single (Sum.inl j) 1 +
        (v (Sum.inr j)) • Pi.single (Sum.inl i) 1 := by
  have hu : quadPlus 3 K (Pi.single (Sum.inl i) 1) = 0 := by
    simp [quadPlus_apply]
  have hw : polar (quadPlus 3 K) (Pi.single (Sum.inl i) 1)
      (Pi.single (Sum.inl j) 1) = 0 := by
    rw [polar_quadPlus_single_inl]
    simp [Pi.single_apply, hij.ne]
  rw [eichler_apply hu hw]
  simp only [polar_quadPlus_single_inl, polar_quadPlus_single_inr, one_smul,
    quadPlus_apply, Pi.single_eq_same, Pi.single_eq_of_ne' (Sum.inl_ne_inr),
    Pi.single_eq_of_ne' (Sum.inr_ne_inl), mul_zero, zero_mul, mul_one,
    Finset.sum_const_zero, add_zero]
  rw [sub_eq_add_neg, ← neg_smul, CharTwo.neg_eq]

theorem eichler_inl_inr_coord {i j : Fin 3} (hij : i < j)
    {v : Fin 3 ⊕ Fin 3 → K}
    (hfix : eichler (quadPlus 3 K) (Pi.single (Sum.inl i) 1)
      (Pi.single (Sum.inr j) 1) v = v) :
    v (Sum.inr i) = 0 ∧ v (Sum.inl j) = 0 := by
  have h := congrFun hfix (Sum.inr j)
  rw [eichler_inl_inr_apply (K := K) hij v] at h
  simp only [Pi.add_apply, Pi.smul_apply, Pi.single_eq_same, Pi.single_eq_of_ne
    (Sum.inr_ne_inl), smul_eq_mul, mul_one, mul_zero, add_zero] at h
  have h1 : v (Sum.inr i) = 0 := by
    have h2 : v (Sum.inr j) + 0 = v (Sum.inr j) + v (Sum.inr i) := by
      simpa using h.symm
    exact (add_left_cancel h2).symm
  have h' := congrFun hfix (Sum.inl i)
  rw [eichler_inl_inr_apply (K := K) hij v] at h'
  simp only [Pi.add_apply, Pi.smul_apply, Pi.single_eq_of_ne' (Sum.inl_ne_inr),
    Pi.single_eq_same, smul_eq_mul, mul_one, mul_zero, zero_add] at h'
  refine ⟨h1, ?_⟩
  have h2 : v (Sum.inl i) + 0 = v (Sum.inl i) + v (Sum.inl j) := by
    simpa using h'.symm
  exact (add_left_cancel h2).symm

theorem eichler_inl_inl_coord {i j : Fin 3} (hij : i < j)
    {v : Fin 3 ⊕ Fin 3 → K}
    (hfix : eichler (quadPlus 3 K) (Pi.single (Sum.inl i) 1)
      (Pi.single (Sum.inl j) 1) v = v) :
    v (Sum.inr i) = 0 ∧ v (Sum.inr j) = 0 := by
  have hne : Sum.inl i ≠ (Sum.inl j : Fin 3 ⊕ Fin 3) := fun h => hij.ne (Sum.inl.inj h)
  have h := congrFun hfix (Sum.inl j)
  rw [eichler_inl_inl_apply (K := K) hij v] at h
  simp only [Pi.add_apply, Pi.smul_apply, Pi.single_eq_same, Pi.single_eq_of_ne' hne,
    Pi.single_eq_of_ne' (Sum.inl_ne_inr), Pi.single_eq_of_ne' (Sum.inr_ne_inl),
    smul_eq_mul, mul_one, mul_zero, add_zero] at h
  have h1 : v (Sum.inr i) = 0 := by
    have h2 : v (Sum.inl j) + 0 = v (Sum.inl j) + v (Sum.inr i) := by
      simpa using h.symm
    exact (add_left_cancel h2).symm
  have h' := congrFun hfix (Sum.inl i)
  rw [eichler_inl_inl_apply (K := K) hij v] at h'
  simp only [Pi.add_apply, Pi.smul_apply, Pi.single_eq_of_ne' (Ne.symm hne),
    Pi.single_eq_of_ne' (Sum.inl_ne_inr), Pi.single_eq_of_ne' (Sum.inr_ne_inl),
    Pi.single_eq_same, smul_eq_mul, mul_one, mul_zero, zero_add] at h'
  refine ⟨h1, ?_⟩
  have h2 : v (Sum.inl i) + 0 = v (Sum.inl i) + v (Sum.inr j) := by
    simpa using h'.symm
  exact (add_left_cancel h2).symm

end FixCoords

section PosUnipFix

open CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin QuadraticMap

variable {K : Type} [Field K] [CharP K 2]

theorem eichler_inl_inr_mem_posUnip {i j : Fin 3} (hij : i < j) :
    eichler (quadPlus 3 K) (Pi.single (Sum.inl i) 1) (Pi.single (Sum.inr j) 1) ∈
      posUnip 3 K := by
  rw [posUnip_eq_closure]
  refine Subgroup.subset_closure (Or.inl ⟨i, j, -1, hij, ?_⟩)
  rw [neg_neg, one_smul]

theorem eichler_inl_inl_mem_posUnip {i j : Fin 3} (hij : i < j) :
    eichler (quadPlus 3 K) (Pi.single (Sum.inl i) 1) (Pi.single (Sum.inl j) 1) ∈
      posUnip 3 K := by
  rw [posUnip_eq_closure]
  refine Subgroup.subset_closure (Or.inr ⟨i, j, -1, hij, ?_⟩)
  rw [neg_neg, one_smul]

theorem flag_one_eq_span_single :
    flag 3 K 1 = K ∙ (Pi.single (Sum.inl (0 : Fin 3)) (1 : K) : Fin 3 ⊕ Fin 3 → K) := by
  rw [flag]
  have hset : (fun j : Fin 3 => (Pi.single (Sum.inl j) (1 : K) : Fin 3 ⊕ Fin 3 → K)) ''
      {j | (j : ℕ) < 1} =
      Set.singleton (Pi.single (Sum.inl (0 : Fin 3)) (1 : K) : Fin 3 ⊕ Fin 3 → K) := by
    ext x
    constructor
    · rintro ⟨j, hj, rfl⟩
      have hj0 : j = 0 := by
        apply Fin.ext
        simpa using hj
      subst hj0
      rfl
    · rintro rfl
      exact ⟨0, by norm_num, rfl⟩
  rw [hset]
  change Submodule.span K (Set.singleton
    (Pi.single (Sum.inl (0 : Fin 3)) (1 : K) : Fin 3 ⊕ Fin 3 → K)) = _
  rfl

theorem single_inl_zero_mem_flag :
    Pi.single (Sum.inl (0 : Fin 3)) (1 : K) ∈ flag 3 K 1 := by
  rw [flag_one_eq_span_single]
  exact Submodule.mem_span_singleton_self _

theorem posUnip_apply_single_inl_zero {g : (Fin 3 ⊕ Fin 3 → K) ≃ₗ[K] (Fin 3 ⊕ Fin 3 → K)}
    (hg : g ∈ posUnip 3 K) :
    g (Pi.single (Sum.inl (0 : Fin 3)) 1) = Pi.single (Sum.inl (0 : Fin 3)) 1 := by
  set e₀ : Fin 3 ⊕ Fin 3 → K := Pi.single (Sum.inl (0 : Fin 3)) 1 with he₀
  have hgen : ∀ g ∈ posUnipGens 3 K, g e₀ = e₀ := by
    rintro g (⟨i, j, t, hij, rfl⟩ | ⟨i, j, t, hij, rfl⟩)
    · apply eichler_apply_of_polar_eq_zero
      · rw [polar_quadPlus_single_inl]
        simp [he₀, Pi.single_apply]
      · rw [polar_smul_right, polar_quadPlus_single_inr]
        simp [he₀, Pi.single_apply, (show j ≠ 0 by omega)]
    · apply eichler_apply_of_polar_eq_zero
      · rw [polar_quadPlus_single_inl]
        simp [he₀, Pi.single_apply]
      · rw [polar_smul_right, polar_quadPlus_single_inl]
        simp [he₀, Pi.single_apply, (show j ≠ 0 by omega)]
  rw [posUnip_eq_closure] at hg
  induction hg using Subgroup.closure_induction with
  | mem g hg => exact hgen g hg
  | one => rfl
  | mul g h _ _ hg hh => rw [LinearEquiv.mul_apply, hh, hg]
  | inv g _ hg =>
      have h1 : g.symm (g e₀) = e₀ := LinearEquiv.symm_apply_apply g e₀
      rwa [hg] at h1

theorem fixV_posUnip_map :
    fixV ((posUnip 3 K).map (linMulAutHom (ι := Fin 3 ⊕ Fin 3) (K := K))) = pointSub K := by
  ext v
  rw [mem_fixV, mem_pointSub]
  constructor
  · intro hv
    set w : Fin 3 ⊕ Fin 3 → K := Multiplicative.toAdd v with hw
    have hfix : ∀ g ∈ posUnip 3 K, g w = w := by
      intro g hg
      have h := hv (linMulAutHom g) (Subgroup.mem_map_of_mem _ hg)
      have h' := congrArg Multiplicative.toAdd h
      have hv' : v = Multiplicative.ofAdd w := by
        rw [hw]; exact (ofAdd_toAdd v).symm
      rw [hv', linMulAutHom_apply, linMulAut_apply] at h'
      exact h'
    have h01r := (eichler_inl_inr_coord (K := K) (by norm_num : (0 : Fin 3) < 1)
      (hfix _ (eichler_inl_inr_mem_posUnip (by norm_num : (0 : Fin 3) < 1)))).2
    have h02r := (eichler_inl_inr_coord (K := K) (by norm_num : (0 : Fin 3) < 2)
      (hfix _ (eichler_inl_inr_mem_posUnip (by norm_num : (0 : Fin 3) < 2)))).2
    have h01l := (eichler_inl_inl_coord (K := K) (by norm_num : (0 : Fin 3) < 1)
      (hfix _ (eichler_inl_inl_mem_posUnip (by norm_num : (0 : Fin 3) < 1)))).2
    have h02l := (eichler_inl_inl_coord (K := K) (by norm_num : (0 : Fin 3) < 2)
      (hfix _ (eichler_inl_inl_mem_posUnip (by norm_num : (0 : Fin 3) < 2)))).1
    have h00 : w (Sum.inr 0) = 0 :=
      (eichler_inl_inl_coord (K := K) (by norm_num : (0 : Fin 3) < 1)
        (hfix _ (eichler_inl_inl_mem_posUnip (by norm_num : (0 : Fin 3) < 1)))).1
    have hy1 : w (Sum.inr 1) = 0 :=
      (eichler_inl_inl_coord (K := K) (by norm_num : (0 : Fin 3) < 1)
        (hfix _ (eichler_inl_inl_mem_posUnip (by norm_num : (0 : Fin 3) < 1)))).2
    have hy2 : w (Sum.inr 2) = 0 :=
      (eichler_inl_inl_coord (K := K) (by norm_num : (0 : Fin 3) < 2)
        (hfix _ (eichler_inl_inl_mem_posUnip (by norm_num : (0 : Fin 3) < 2)))).2
    have hweq : w = w (Sum.inl (0 : Fin 3)) • Pi.single (Sum.inl (0 : Fin 3)) 1 := by
      funext c
      rcases c with i | i
      · fin_cases i
        · simp
        · simpa using h01r
        · simpa using h02r
      · fin_cases i
        · simpa using h00
        · simpa using hy1
        · simpa using hy2
    rw [hweq]
    exact Submodule.smul_mem (flag 3 K 1) (w (Sum.inl (0 : Fin 3)))
      single_inl_zero_mem_flag
  · intro hv
    rw [flag_one_eq_span_single] at hv
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hv
    intro x hx
    obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp hx
    have hx0 : g (Pi.single (Sum.inl (0 : Fin 3)) 1) =
        Pi.single (Sum.inl (0 : Fin 3)) 1 :=
      posUnip_apply_single_inl_zero (K := K) (g := g) hg
    have hxw : g (Multiplicative.toAdd v) = Multiplicative.toAdd v := by
      rw [← hc, map_smul, hx0]
    apply Multiplicative.toAdd.injective
    rw [show v = Multiplicative.ofAdd (Multiplicative.toAdd v) from (ofAdd_toAdd v).symm]
    rw [linMulAutHom_apply, linMulAut_apply]
    exact hxw

end PosUnipFix

section Classification

open CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin QuadraticMap
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit

variable {K : Type} [Field K]

@[expose] noncomputable def rankOneParabolic (K : Type) [Field K] (r : ℕ) (i : Fin r) :
    Subgroup ((Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)) :=
  Subgroup.closure ((borel r K : Set _) ∪ {weylElt r K i})

theorem borel_le_rankOneParabolic (r : ℕ) (i : Fin r) :
    borel r K ≤ rankOneParabolic K r i :=
  fun _ hb => Subgroup.subset_closure (Or.inl hb)

theorem weylElt_mem_rankOneParabolic (r : ℕ) (i : Fin r) :
    weylElt r K i ∈ rankOneParabolic K r i :=
  Subgroup.subset_closure (Or.inr rfl)

@[expose] noncomputable def pointStab (K : Type) [Field K] :
    Subgroup ((Fin 3 ⊕ Fin 3 → K) ≃ₗ[K] (Fin 3 ⊕ Fin 3 → K)) :=
  MulAction.stabilizer ((Fin 3 ⊕ Fin 3 → K) ≃ₗ[K] (Fin 3 ⊕ Fin 3 → K)) (flag 3 K 1)

theorem mem_pointStab {g : (Fin 3 ⊕ Fin 3 → K) ≃ₗ[K] (Fin 3 ⊕ Fin 3 → K)} :
    g ∈ pointStab K ↔ g • (flag 3 K 1) = flag 3 K 1 :=
  MulAction.mem_stabilizer_iff

theorem borel_le_pointStab :
    borel 3 K ≤ pointStab K := by
  intro b hb
  rw [mem_pointStab]
  exact (mem_borel.1 hb).2 1 (by norm_num) (by norm_num)

theorem weylElt_one_mem_pointStab :
    weylElt 3 K 1 ∈ pointStab K := by
  rw [mem_pointStab]
  exact weylElt_smul_flag_of_ne (K := K) (r := 3) (by norm_num) (by norm_num) (by norm_num)
    (by decide)

theorem weylElt_two_mem_pointStab :
    weylElt 3 K 2 ∈ pointStab K := by
  rw [mem_pointStab]
  exact weylElt_smul_flag_of_ne (K := K) (r := 3) (by norm_num) (by norm_num) (by norm_num)
    (by decide)

theorem weylElt_zero_not_mem_pointStab :
    weylElt 3 K 0 ∉ pointStab K := by
  intro h
  rw [mem_pointStab] at h
  exact weylElt_smul_flag_ne (K := K) (r := 3) (by norm_num) (j := (0 : Fin 3))
    (by norm_num) h

theorem le_pointStab_iff_of_borel_le {M : Subgroup
    ((Fin 3 ⊕ Fin 3 → K) ≃ₗ[K] (Fin 3 ⊕ Fin 3 → K))}
    (hME : M ≤ splitE K) (hBM : borel 3 K ≤ M) :
    M ≤ pointStab K ↔ weylElt 3 K 0 ∉ M := by
  have hgen := eq_closure_of_borel_le (K := K) (r := 3) (by norm_num) hME hBM
  constructor
  · intro hMP h0
    exact weylElt_zero_not_mem_pointStab (hMP h0)
  · intro h0
    rw [hgen, Subgroup.closure_le]
    rintro _ (hb | ⟨i, hi, rfl⟩)
    · exact borel_le_pointStab hb
    · fin_cases i
      · exact absurd hi h0
      · exact weylElt_one_mem_pointStab
      · exact weylElt_two_mem_pointStab

theorem rankOneParabolic_le_xParab :
    rankOneParabolic K 3 0 ≤
      MulAction.stabilizer ((Fin 3 ⊕ Fin 3 → K) ≃ₗ[K] (Fin 3 ⊕ Fin 3 → K)) (flag 3 K 3) := by
  rw [rankOneParabolic, Subgroup.closure_le]
  rintro _ (hb | rfl)
  · exact MulAction.mem_stabilizer_iff.mpr ((mem_borel.1 hb).2 3 (by norm_num) (by norm_num))
  · exact MulAction.mem_stabilizer_iff.mpr
      (weylElt_smul_flag_top_and_Xstar (K := K) (r := 3) (by norm_num)
        (j := 0) (by norm_num)).1

theorem rankOneParabolic_le_xstarParab :
    rankOneParabolic K 3 0 ≤
      MulAction.stabilizer ((Fin 3 ⊕ Fin 3 → K) ≃ₗ[K] (Fin 3 ⊕ Fin 3 → K))
        (Xstar 3 K (by norm_num)) := by
  rw [rankOneParabolic, Subgroup.closure_le]
  rintro _ (hb | rfl)
  · exact borel_le_stabilizer_Xstar (K := K) (r := 3) (by norm_num) hb
  · exact MulAction.mem_stabilizer_iff.mpr
      (weylElt_smul_flag_top_and_Xstar (K := K) (r := 3) (by norm_num)
        (j := 0) (by norm_num)).2

end Classification

section MaxParab

open CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin QuadraticMap
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit

variable {K : Type} [Field K]

@[expose] noncomputable def xStab (K : Type) [Field K] :
    Subgroup ((Fin 3 ⊕ Fin 3 → K) ≃ₗ[K] (Fin 3 ⊕ Fin 3 → K)) :=
  MulAction.stabilizer ((Fin 3 ⊕ Fin 3 → K) ≃ₗ[K] (Fin 3 ⊕ Fin 3 → K)) (flag 3 K 3)

@[expose] noncomputable def xstarStab (K : Type) [Field K] :
    Subgroup ((Fin 3 ⊕ Fin 3 → K) ≃ₗ[K] (Fin 3 ⊕ Fin 3 → K)) :=
  MulAction.stabilizer ((Fin 3 ⊕ Fin 3 → K) ≃ₗ[K] (Fin 3 ⊕ Fin 3 → K))
    (Xstar 3 K (by norm_num))

theorem borel_le_maxParab_point : borel 3 K ≤ splitE K ⊓ pointStab K :=
  le_inf borel_le borel_le_pointStab

theorem borel_le_maxParab_x : borel 3 K ≤ splitE K ⊓ xStab K := by
  refine le_inf borel_le ?_
  intro b hb
  exact MulAction.mem_stabilizer_iff.mpr ((mem_borel.1 hb).2 3 (by norm_num) (by norm_num))

theorem borel_le_maxParab_xstar : borel 3 K ≤ splitE K ⊓ xstarStab K :=
  le_inf borel_le (borel_le_stabilizer_Xstar (K := K) (r := 3) (by norm_num))

theorem weylElt_zero_mem_xStab : weylElt 3 K 0 ∈ xStab K :=
  MulAction.mem_stabilizer_iff.mpr
    (weylElt_smul_flag_top_and_Xstar (K := K) (r := 3) (by norm_num)
      (j := 0) (by norm_num)).1

theorem weylElt_one_mem_xStab : weylElt 3 K 1 ∈ xStab K :=
  MulAction.mem_stabilizer_iff.mpr
    (weylElt_penult_smul (K := K) (r := 3) (by norm_num)).2

theorem weylElt_two_not_mem_xStab : weylElt 3 K 2 ∉ xStab K := by
  intro h
  exact (weylElt_last_smul (K := K) (r := 3) (by norm_num)).1
    (MulAction.mem_stabilizer_iff.mp h)

theorem weylElt_zero_mem_xstarStab : weylElt 3 K 0 ∈ xstarStab K :=
  MulAction.mem_stabilizer_iff.mpr
    (weylElt_smul_flag_top_and_Xstar (K := K) (r := 3) (by norm_num)
      (j := 0) (by norm_num)).2

theorem weylElt_one_not_mem_xstarStab : weylElt 3 K 1 ∉ xstarStab K := by
  intro h
  exact (weylElt_penult_smul (K := K) (r := 3) (by norm_num)).1
    (MulAction.mem_stabilizer_iff.mp h)

theorem weylElt_two_mem_xstarStab : weylElt 3 K 2 ∈ xstarStab K :=
  MulAction.mem_stabilizer_iff.mpr
    (weylElt_last_smul (K := K) (r := 3) (by norm_num)).2

theorem maxParab_x_eq :
    splitE K ⊓ xStab K =
      Subgroup.closure (((borel 3 K : Set ((Fin 3 ⊕ Fin 3 → K) ≃ₗ[K]
        (Fin 3 ⊕ Fin 3 → K)))) ∪ {weylElt 3 K 0, weylElt 3 K 1}) := by
  have hgen := eq_closure_of_borel_le (K := K) (r := 3) (by norm_num)
    (inf_le_left : splitE K ⊓ xStab K ≤ splitE K) borel_le_maxParab_x
  rw [hgen]
  congr 1
  ext x
  simp only [Set.mem_union, Set.mem_image, Set.mem_setOf_eq, Set.mem_insert_iff,
    Set.mem_singleton_iff]
  constructor
  · rintro (hb | ⟨i, hi, rfl⟩)
    · exact Or.inl hb
    · fin_cases i
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr rfl)
      · exact absurd (Subgroup.mem_inf.mp hi).2 weylElt_two_not_mem_xStab
  · rintro (hb | rfl | rfl)
    · exact Or.inl hb
    · exact Or.inr ⟨0, Subgroup.mem_inf.mpr ⟨weylElt_mem 0, weylElt_zero_mem_xStab⟩, rfl⟩
    · exact Or.inr ⟨1, Subgroup.mem_inf.mpr ⟨weylElt_mem 1, weylElt_one_mem_xStab⟩, rfl⟩

theorem maxParab_xstar_eq :
    splitE K ⊓ xstarStab K =
      Subgroup.closure (((borel 3 K : Set ((Fin 3 ⊕ Fin 3 → K) ≃ₗ[K]
        (Fin 3 ⊕ Fin 3 → K)))) ∪ {weylElt 3 K 0, weylElt 3 K 2}) := by
  have hgen := eq_closure_of_borel_le (K := K) (r := 3) (by norm_num)
    (inf_le_left : splitE K ⊓ xstarStab K ≤ splitE K) borel_le_maxParab_xstar
  rw [hgen]
  congr 1
  ext x
  simp only [Set.mem_union, Set.mem_image, Set.mem_setOf_eq, Set.mem_insert_iff,
    Set.mem_singleton_iff]
  constructor
  · rintro (hb | ⟨i, hi, rfl⟩)
    · exact Or.inl hb
    · fin_cases i
      · exact Or.inr (Or.inl rfl)
      · exact absurd (Subgroup.mem_inf.mp hi).2 weylElt_one_not_mem_xstarStab
      · exact Or.inr (Or.inr rfl)
  · rintro (hb | rfl | rfl)
    · exact Or.inl hb
    · exact Or.inr ⟨0, Subgroup.mem_inf.mpr ⟨weylElt_mem 0, weylElt_zero_mem_xstarStab⟩, rfl⟩
    · exact Or.inr ⟨2, Subgroup.mem_inf.mpr ⟨weylElt_mem 2, weylElt_two_mem_xstarStab⟩, rfl⟩

end MaxParab

section OvergroupList

open CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin QuadraticMap
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit

variable {K : Type} [Field K]

theorem overgroup_with_n0_cases {M : Subgroup
    ((Fin 3 ⊕ Fin 3 → K) ≃ₗ[K] (Fin 3 ⊕ Fin 3 → K))}
    (hME : M ≤ splitE K) (hBM : borel 3 K ≤ M) (h0 : weylElt 3 K 0 ∈ M) :
    M = rankOneParabolic K 3 0 ∨ M = splitE K ⊓ xStab K ∨
      M = splitE K ⊓ xstarStab K ∨ M = splitE K := by
  have hgen := eq_closure_of_borel_le (K := K) (r := 3) (by norm_num) hME hBM
  by_cases h1 : weylElt 3 K 1 ∈ M
  · by_cases h2 : weylElt 3 K 2 ∈ M
    · right; right; right
      refine le_antisymm hME ?_
      rw [show splitE K = Subgroup.closure
        (↑(borel 3 K) ∪ Set.range (weylElt 3 K)) from
        orthogonal_geometry_split_Borel_Weyl_generation (K := K) (r := 3) (by norm_num),
        Subgroup.closure_le]
      rintro _ (hb | ⟨i, rfl⟩)
      · exact hBM hb
      · fin_cases i
        · exact h0
        · exact h1
        · exact h2
    · right; left
      refine le_antisymm ?_ ?_
      · rw [hgen, Subgroup.closure_le]
        rintro _ (hb | ⟨i, hi, rfl⟩)
        · exact borel_le_maxParab_x hb
        · fin_cases i
          · exact Subgroup.mem_inf.mpr ⟨weylElt_mem 0, weylElt_zero_mem_xStab⟩
          · exact Subgroup.mem_inf.mpr ⟨weylElt_mem 1, weylElt_one_mem_xStab⟩
          · exact absurd hi h2
      · rw [maxParab_x_eq, Subgroup.closure_le]
        rintro _ (hb | hmem)
        · exact hBM hb
        · rcases hmem with rfl | rfl
          · exact h0
          · exact h1
  · by_cases h2 : weylElt 3 K 2 ∈ M
    · right; right; left
      refine le_antisymm ?_ ?_
      · rw [hgen, Subgroup.closure_le]
        rintro _ (hb | ⟨i, hi, rfl⟩)
        · exact borel_le_maxParab_xstar hb
        · fin_cases i
          · exact Subgroup.mem_inf.mpr ⟨weylElt_mem 0, weylElt_zero_mem_xstarStab⟩
          · exact absurd hi h1
          · exact Subgroup.mem_inf.mpr ⟨weylElt_mem 2, weylElt_two_mem_xstarStab⟩
      · rw [maxParab_xstar_eq, Subgroup.closure_le]
        rintro _ (hb | hmem)
        · exact hBM hb
        · rcases hmem with rfl | rfl
          · exact h0
          · exact h2
    · left
      refine le_antisymm ?_ ?_
      · rw [hgen, Subgroup.closure_le]
        rintro _ (hb | ⟨i, hi, rfl⟩)
        · exact borel_le_rankOneParabolic 3 0 hb
        · fin_cases i
          · exact weylElt_mem_rankOneParabolic 3 0
          · exact absurd hi h1
          · exact absurd hi h2
      · rw [rankOneParabolic, Subgroup.closure_le]
        rintro _ (hb | hmem)
        · exact hBM hb
        · rcases hmem with rfl
          · exact h0

theorem maxParab_point_max {M : Subgroup
    ((Fin 3 ⊕ Fin 3 → K) ≃ₗ[K] (Fin 3 ⊕ Fin 3 → K))}
    (hME : M ≤ splitE K) (hBM : borel 3 K ≤ M)
    (hle : splitE K ⊓ pointStab K ≤ M) (hne : M ≠ splitE K ⊓ pointStab K) :
    M = splitE K := by
  have h1 : weylElt 3 K 1 ∈ M :=
    hle (Subgroup.mem_inf.mpr ⟨weylElt_mem 1, weylElt_one_mem_pointStab⟩)
  have h2 : weylElt 3 K 2 ∈ M :=
    hle (Subgroup.mem_inf.mpr ⟨weylElt_mem 2, weylElt_two_mem_pointStab⟩)
  by_contra htop
  have h0 : weylElt 3 K 0 ∈ M := by
    by_contra h0
    apply hne
    refine le_antisymm ?_ hle
    have hgen := eq_closure_of_borel_le (K := K) (r := 3) (by norm_num) hME hBM
    rw [hgen, Subgroup.closure_le]
    rintro a (hb | ⟨i, hi, rfl⟩)
    · exact Subgroup.mem_inf.mpr ⟨borel_le hb, borel_le_pointStab hb⟩
    · fin_cases i
      · exact absurd hi h0
      · exact Subgroup.mem_inf.mpr ⟨weylElt_mem 1, weylElt_one_mem_pointStab⟩
      · exact Subgroup.mem_inf.mpr ⟨weylElt_mem 2, weylElt_two_mem_pointStab⟩
  rcases overgroup_with_n0_cases hME hBM h0 with h | h | h | h
  · exfalso
    have h1P : weylElt 3 K 1 ∈ rankOneParabolic K 3 0 := by
      rw [← h]
      exact hle (Subgroup.mem_inf.mpr ⟨weylElt_mem 1, weylElt_one_mem_pointStab⟩)
    exact weylElt_one_not_mem_xstarStab (rankOneParabolic_le_xstarParab h1P)
  · exfalso
    have h2A : weylElt 3 K 2 ∈ splitE K ⊓ xStab K := by
      rw [← h]
      exact hle (Subgroup.mem_inf.mpr ⟨weylElt_mem 2, weylElt_two_mem_pointStab⟩)
    exact weylElt_two_not_mem_xStab (Subgroup.mem_inf.mp h2A).2
  · exfalso
    have h1A : weylElt 3 K 1 ∈ splitE K ⊓ xstarStab K := by
      rw [← h]
      exact hle (Subgroup.mem_inf.mpr ⟨weylElt_mem 1, weylElt_one_mem_pointStab⟩)
    exact weylElt_one_not_mem_xstarStab (Subgroup.mem_inf.mp h1A).2
  · exact htop h

end OvergroupList

end PointFix

end SplitModel

theorem kTab23b_OmegaPlus6_line_of_natural (W : Type) [CommGroup W] [Finite W]
    (H : Subgroup (MulAut W)) (n : ℕ)
    (hnat : IsNaturalClassicalModule H n) (hperf : ⁅H, H⁆ = H)
    (hline : IsOmegaPlus ↥H 6 n ∧ NatOmegaPlus H ⊤ ⊥ 6 n)
    (hNat : ∀ (K : Type) [Field K] [Finite K] (m : ℕ), Nat.card K = 2 ^ m →
      OmegaPlus6Line (CFSG.Quasithin.H.StdMod (Fin 3 ⊕ Fin 3) K)
        (CFSG.Quasithin.H.natImage
          (CFSG.Open.StatedOmega (CFSG.Open.StatedQuadPlus 3 K))) m) :
    letI : MulDistribMulAction ↥H W := MulDistribMulAction.compHom W H.subtype
    letI : MulAction ↥H W := MulAction.compHom W H.subtype
    letI : MulAction ↥H (Set W) := Set.mulActionSet
    ∀ S : Sylow 2 ↥H,
      letI : MulDistribMulAction ↥S W :=
        MulDistribMulAction.compHom W (H.subtype.comp (S : Subgroup ↥H).subtype)
      let ℓ : Subgroup W := fixedPointSubgroup ↥S W
      let Pℓ : Subgroup ↥H := MulAction.stabilizer ↥H (ℓ : Set W)
      ∀ Tstar : Subgroup (MulAut W),
        Tstar ≤ Subgroup.normalizer (H : Set (MulAut W)) →
        IsPGroup 2 ↥Tstar →
        (S : Subgroup ↥H).map H.subtype ≤ Tstar →
        let Good : Subgroup ↥H → Prop := fun Pstar =>
          IsParabolicTwo ↥H Pstar ∧ (S : Subgroup ↥H) ≤ Pstar ∧
          (∀ t ∈ Tstar,
            (Pstar.map H.subtype).map (MulAut.conj t).toMonoidHom = Pstar.map H.subtype) ∧
          ¬ Pstar ≤ Pℓ
        ∀ Pstar : Subgroup ↥H, Minimal Good Pstar →
          Pstar ≠ ⊤ ∧ (IsL2 (Bar2 (Hinf Pstar)) n ∨ (n = 1 ∧ Hinf Pstar = ⊥)) := by
  obtain ⟨-, K, hF, hFin, hK, hReal⟩ := hline.2
  letI : Field K := hF
  letI : Finite K := hFin
  obtain ⟨π, e, he⟩ :=
    CFSG.LocalAnalysis.UniquenessCase.UC22.KTabC.exists_natEquiv
      (ι := Fin 3 ⊕ Fin 3)
      (Γ := CFSG.Open.StatedOmega (CFSG.Open.StatedQuadPlus 3 K)) (H := H) hReal
  have he' : ∀ (γ : ↥(CFSG.Open.StatedOmega (CFSG.Open.StatedQuadPlus 3 K))) (w : W),
      e (((π γ : ↥H) : MulAut W) w) =
        CFSG.Quasithin.natAct (CFSG.Open.StatedOmega (CFSG.Open.StatedQuadPlus 3 K)) γ
          (e w) := by
    intro γ w
    have h1 := he γ w
    change e (((π γ : ↥H) : MulAut W) w) = Multiplicative.ofAdd
      (((γ : Matrix.GeneralLinearGroup (Fin 3 ⊕ Fin 3) K) :
        Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K) *ᵥ
        Multiplicative.toAdd (e w))
    rw [← h1, ofAdd_toAdd]
  have hmodel :
      CFSG.Quasithin.H.natImage
          (CFSG.Open.StatedOmega (CFSG.Open.StatedQuadPlus 3 K)) =
        H.map (CFSG.Quasithin.H.congrHom e) :=
    (CFSG.Quasithin.H.map_congrHom_eq_natImage
      (Γ := CFSG.Open.StatedOmega (CFSG.Open.StatedQuadPlus 3 K))
      (H := H) (π := π) π.surjective e he').symm
  exact omegaPlus6Line_of_map_congr H _ n e hmodel (hNat K n hK)

section RankOneFacts

open CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin QuadraticMap
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem rankOneParabolic_ne_top : rankOneParabolic K 3 0 ≠ splitE K := by
  intro h
  have h1 : weylElt 3 K 1 ∈ rankOneParabolic K 3 0 := by
    rw [h]; exact weylElt_mem 1
  exact weylElt_one_not_mem_xstarStab (rankOneParabolic_le_xstarParab h1)

theorem rankOneParabolic_not_le_pointStab :
    ¬ rankOneParabolic K 3 0 ≤ pointStab K := by
  intro h
  exact weylElt_zero_not_mem_pointStab
    (h (weylElt_mem_rankOneParabolic 3 0))

theorem isParabolicTwo_rankOne :
    IsParabolicTwo ↥(splitE K) ((rankOneParabolic K 3 0).subgroupOf (splitE K)) := by
  obtain ⟨S, hS⟩ := splitU_isSylow (K := K)
  refine ⟨S, ?_⟩
  have hnorm : Subgroup.normalizer
      ((splitU K : Subgroup ↥(splitE K)) : Set (↥(splitE K))) ≤
      (rankOneParabolic K 3 0).subgroupOf (splitE K) := by
    rw [normalizer_splitU, flagStab_eq_borel]
    exact Subgroup.subgroupOf_mono _ (borel_le_rankOneParabolic (K := K) 3 0)
  rw [← hS] at hnorm
  exact hnorm

end RankOneFacts

section NaturalModel

open CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin QuadraticMap
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit
open CFSG.QuasithinUnique

variable {K : Type} [Field K] [Finite K] [CharP K 2]

instance finite_splitE : Finite ↥(splitE K) :=
  Finite.of_injective
    (fun g : ↥(splitE K) =>
      (g : (Fin 3 ⊕ Fin 3 → K) → (Fin 3 ⊕ Fin 3 → K)))
    (fun a b h => Subtype.ext (LinearEquiv.ext (congrFun h)))

@[expose] noncomputable def eSplitH :
    ↥(splitE K) ≃* ↥(splitH K) :=
  (splitE K).equivMapOfInjective (linMulAutHom (ι := Fin 3 ⊕ Fin 3) (K := K))
    linMulAutHom_injective

theorem eSplitH_surjective : Function.Surjective (eSplitH (K := K)) :=
  (eSplitH (K := K)).surjective

theorem eSplitH_injective : Function.Injective (eSplitH (K := K)) :=
  (eSplitH (K := K)).injective

theorem subtype_comp_eSplitH :
    (splitH K).subtype.comp (eSplitH (K := K)).toMonoidHom =
      (linMulAutHom (ι := Fin 3 ⊕ Fin 3) (K := K)).comp (splitE K).subtype := by
  ext g
  rfl

@[expose] noncomputable def natStdS : Subgroup (splitH K) :=
  (splitU K).map (eSplitH (K := K)).toMonoidHom

@[expose] noncomputable def natStdB : Subgroup (splitH K) :=
  ((borel 3 K).subgroupOf (splitE K)).map (eSplitH (K := K)).toMonoidHom

@[expose] noncomputable def natStdP : Subgroup (splitH K) :=
  ((splitE K ⊓ pointStab K).subgroupOf (splitE K)).map (eSplitH (K := K)).toMonoidHom

@[expose] noncomputable def natStdP0 : Subgroup (splitH K) :=
  ((rankOneParabolic K 3 0).subgroupOf (splitE K)).map (eSplitH (K := K)).toMonoidHom

theorem rankOneParabolic_le_splitE : rankOneParabolic K 3 0 ≤ splitE K := by
  rw [rankOneParabolic, Subgroup.closure_le]
  rintro _ (hb | rfl)
  · exact borel_le hb
  · exact weylElt_mem 0

theorem natStdS_map_subtype :
    (natStdS (K := K)).map (splitH K).subtype =
      (posUnip 3 K).map (linMulAutHom (ι := Fin 3 ⊕ Fin 3) (K := K)) := by
  rw [natStdS, Subgroup.map_map, subtype_comp_eSplitH, ← Subgroup.map_map]
  rw [splitU, Subgroup.map_subgroupOf_eq_of_le
    (posUnip_le_orthElementaryGroup (r := 3) (K := K))]

theorem natStdP_map_subtype :
    (natStdP (K := K)).map (splitH K).subtype =
      (splitE K ⊓ pointStab K).map (linMulAutHom (ι := Fin 3 ⊕ Fin 3) (K := K)) := by
  rw [natStdP, Subgroup.map_map, subtype_comp_eSplitH, ← Subgroup.map_map,
    Subgroup.map_subgroupOf_eq_of_le inf_le_left]

theorem normalizer_natStdS :
    Subgroup.normalizer (natStdS (K := K) : Set (splitH K)) = natStdB (K := K) := by
  rw [natStdS, natStdB, ← Subgroup.map_equiv_normalizer_eq (splitU K) (eSplitH (K := K))]
  congr 1
  rw [normalizer_splitU, flagStab_eq_borel]

theorem fixV_natStdS :
    CFSG.Quasithin.fixV ((natStdS (K := K)).map (splitH K).subtype) = pointSub K := by
  rw [natStdS_map_subtype, fixV_posUnip_map]

theorem isSylowTwoOf_natStdS :
    CFSG.QuasithinUnique.IsSylowTwoOf (natStdS (K := K)) ⊤ := by
  obtain ⟨S, hS⟩ := splitU_isSylow (K := K)
  have hS' : CFSG.QuasithinUnique.IsSylowTwoOf (S : Subgroup ↥(splitE K)) ⊤ :=
    CFSG.QuasithinUnique.isSylowTwoOf_top_of_sylow S
  have h := CFSG.Quasithin.H13.A5.isSylowTwoOf_map hS'
    (eSplitH (K := K)).toMonoidHom
  rw [Subgroup.map_top_of_surjective _ (eSplitH_surjective (K := K))] at h
  rwa [natStdS, ← hS]

theorem smul_pointSub (f : (Fin 3 ⊕ Fin 3 → K) ≃ₗ[K] (Fin 3 ⊕ Fin 3 → K)) :
    (linMulAut f : MulAut (CFSG.Quasithin.H.StdMod (Fin 3 ⊕ Fin 3) K)) •
        (pointSub K : Set (CFSG.Quasithin.H.StdMod (Fin 3 ⊕ Fin 3) K)) =
      Multiplicative.ofAdd ''
        ((flag 3 K 1).map (f : (Fin 3 ⊕ Fin 3 → K) →ₗ[K] (Fin 3 ⊕ Fin 3 → K)) :
          Set (Fin 3 ⊕ Fin 3 → K)) := by
  ext x
  constructor
  · intro hx
    rw [Set.mem_smul_set] at hx
    obtain ⟨y, hy, hyx⟩ := hx
    rw [MulAut.smul_def] at hyx
    have hy' : Multiplicative.toAdd y ∈ flag 3 K 1 := hy
    refine ⟨f (Multiplicative.toAdd y), Submodule.mem_map_of_mem hy', ?_⟩
    calc Multiplicative.ofAdd (f (Multiplicative.toAdd y))
        = (linMulAut f : MulAut _) (Multiplicative.ofAdd (Multiplicative.toAdd y)) :=
          (linMulAut_apply f _).symm
      _ = (linMulAut f : MulAut _) y := by rw [ofAdd_toAdd]
      _ = x := hyx
  · rintro ⟨v, hv, rfl⟩
    rw [Set.mem_smul_set]
    obtain ⟨w, hw, hwv⟩ := Submodule.mem_map.mp hv
    exact ⟨Multiplicative.ofAdd w, hw, by
      rw [MulAut.smul_def, linMulAut_apply_ofAdd]
      exact congrArg Multiplicative.ofAdd hwv⟩

theorem smul_pointSub_eq_iff (f : (Fin 3 ⊕ Fin 3 → K) ≃ₗ[K] (Fin 3 ⊕ Fin 3 → K)) :
    (linMulAut f : MulAut (CFSG.Quasithin.H.StdMod (Fin 3 ⊕ Fin 3) K)) •
        (pointSub K : Set (CFSG.Quasithin.H.StdMod (Fin 3 ⊕ Fin 3) K)) = pointSub K ↔
      (flag 3 K 1).map (f : (Fin 3 ⊕ Fin 3 → K) →ₗ[K] (Fin 3 ⊕ Fin 3 → K)) =
        flag 3 K 1 := by
  have hpt : (pointSub K : Set (CFSG.Quasithin.H.StdMod (Fin 3 ⊕ Fin 3) K)) =
      Multiplicative.ofAdd '' (flag 3 K 1 : Set (Fin 3 ⊕ Fin 3 → K)) := by
    ext x
    constructor
    · intro hx
      exact ⟨Multiplicative.toAdd x, hx, (ofAdd_toAdd x).symm⟩
    · rintro ⟨v, hv, rfl⟩
      exact hv
  rw [smul_pointSub, hpt]
  have himg : (Multiplicative.ofAdd '' ((flag 3 K 1).map
      (f : (Fin 3 ⊕ Fin 3 → K) →ₗ[K] (Fin 3 ⊕ Fin 3 → K)) :
        Set (Fin 3 ⊕ Fin 3 → K)) =
      Multiplicative.ofAdd '' (flag 3 K 1 : Set (Fin 3 ⊕ Fin 3 → K))) ↔
      (((flag 3 K 1).map (f : (Fin 3 ⊕ Fin 3 → K) →ₗ[K] (Fin 3 ⊕ Fin 3 → K)) :
        Set (Fin 3 ⊕ Fin 3 → K)) = (flag 3 K 1 : Set (Fin 3 ⊕ Fin 3 → K))) := by
    constructor
    · intro h
      ext v
      constructor
      · intro hv
        have hmem : Multiplicative.ofAdd v ∈
            Multiplicative.ofAdd '' ((flag 3 K 1).map
              (f : (Fin 3 ⊕ Fin 3 → K) →ₗ[K] (Fin 3 ⊕ Fin 3 → K)) :
                Set (Fin 3 ⊕ Fin 3 → K)) := ⟨v, hv, rfl⟩
        rw [h] at hmem
        obtain ⟨w, hw, hwv⟩ := hmem
        exact Multiplicative.ofAdd.injective hwv ▸ hw
      · intro hv
        have hmem : Multiplicative.ofAdd v ∈
            Multiplicative.ofAdd '' (flag 3 K 1 : Set (Fin 3 ⊕ Fin 3 → K)) :=
          ⟨v, hv, rfl⟩
        rw [← h] at hmem
        obtain ⟨w, hw, hwv⟩ := hmem
        exact Multiplicative.ofAdd.injective hwv ▸ hw
    · intro h
      rw [h]
  exact himg.trans ⟨fun h => SetLike.coe_injective h,
    fun h => congrArg (fun W : Submodule K (Fin 3 ⊕ Fin 3 → K) =>
      (W : Set (Fin 3 ⊕ Fin 3 → K))) h⟩

theorem linMulAut_mem_stabilizer_pointSub_iff
    (f : (Fin 3 ⊕ Fin 3 → K) ≃ₗ[K] (Fin 3 ⊕ Fin 3 → K)) :
    linMulAut f ∈ MulAction.stabilizer
        (MulAut (CFSG.Quasithin.H.StdMod (Fin 3 ⊕ Fin 3) K))
        (pointSub K : Set (CFSG.Quasithin.H.StdMod (Fin 3 ⊕ Fin 3) K)) ↔
      f ∈ pointStab K := by
  rw [MulAction.mem_stabilizer_iff, smul_pointSub_eq_iff]
  change (flag 3 K 1).map (f : (Fin 3 ⊕ Fin 3 → K) →ₗ[K] (Fin 3 ⊕ Fin 3 → K)) =
      flag 3 K 1 ↔ f ∈ MulAction.stabilizer
        ((Fin 3 ⊕ Fin 3 → K) ≃ₗ[K] (Fin 3 ⊕ Fin 3 → K)) (flag 3 K 1)
  exact (Submodule.mem_stabilizer_submodule_iff_map_eq
    (G := (Fin 3 ⊕ Fin 3 → K) ≃ₗ[K] (Fin 3 ⊕ Fin 3 → K))
    (S := flag 3 K 1) (e := f)).symm

theorem stabilizer_pointSub_eq_natStdP :
    letI : MulDistribMulAction ↥(splitH K)
      (CFSG.Quasithin.H.StdMod (Fin 3 ⊕ Fin 3) K) :=
      MulDistribMulAction.compHom _ (splitH K).subtype
    letI : MulAction ↥(splitH K)
      (CFSG.Quasithin.H.StdMod (Fin 3 ⊕ Fin 3) K) :=
      MulAction.compHom _ (splitH K).subtype
    letI : MulAction ↥(splitH K)
      (Set (CFSG.Quasithin.H.StdMod (Fin 3 ⊕ Fin 3) K)) := Set.mulActionSet
    MulAction.stabilizer ↥(splitH K)
        (pointSub K : Set (CFSG.Quasithin.H.StdMod (Fin 3 ⊕ Fin 3) K)) = natStdP (K := K) := by
  letI : MulDistribMulAction ↥(splitH K)
      (CFSG.Quasithin.H.StdMod (Fin 3 ⊕ Fin 3) K) :=
      MulDistribMulAction.compHom _ (splitH K).subtype
  letI : MulAction ↥(splitH K)
      (CFSG.Quasithin.H.StdMod (Fin 3 ⊕ Fin 3) K) :=
      MulAction.compHom _ (splitH K).subtype
  letI : MulAction ↥(splitH K)
      (Set (CFSG.Quasithin.H.StdMod (Fin 3 ⊕ Fin 3) K)) := Set.mulActionSet
  apply Subgroup.map_injective (f := (splitH K).subtype) (splitH K).subtype_injective
  rw [map_subtype_stabilizer_eq_inf (splitH K) (pointSub K), natStdP_map_subtype]
  ext x
  constructor
  · rintro ⟨hxst, hxH⟩
    obtain ⟨f, hfE, rfl⟩ := Subgroup.mem_map.mp hxH
    refine Subgroup.mem_map.mpr ⟨f, Subgroup.mem_inf.mpr ⟨hfE, ?_⟩, rfl⟩
    exact (linMulAut_mem_stabilizer_pointSub_iff (K := K) f).mp hxst
  · rintro ⟨f, hf, rfl⟩
    exact ⟨(linMulAut_mem_stabilizer_pointSub_iff (K := K) f).mpr hf.2,
      Subgroup.mem_map_of_mem (linMulAutHom (ι := Fin 3 ⊕ Fin 3) (K := K)) hf.1⟩

theorem rankOneParabolic_le_of_borel_le_of_not_le_pointStab
    {M : Subgroup ((Fin 3 ⊕ Fin 3 → K) ≃ₗ[K] (Fin 3 ⊕ Fin 3 → K))}
    (hME : M ≤ splitE K) (hBM : borel 3 K ≤ M) (hnot : ¬ M ≤ pointStab K) :
    rankOneParabolic K 3 0 ≤ M := by
  have h0 : weylElt 3 K 0 ∈ M := by
    by_contra h
    exact hnot ((le_pointStab_iff_of_borel_le hME hBM).mpr h)
  rcases overgroup_with_n0_cases hME hBM h0 with h | h | h | h
  · rw [h]
  · rw [h]
    exact le_inf (rankOneParabolic_le_splitE (K := K)) (rankOneParabolic_le_xParab (K := K))
  · rw [h]
    exact le_inf (rankOneParabolic_le_splitE (K := K)) (rankOneParabolic_le_xstarParab (K := K))
  · rw [h]; exact rankOneParabolic_le_splitE (K := K)

theorem rankOneParabolic_subgroupOf_le_of_borel_le_of_not_le_pointStab
    {M : Subgroup ↥(splitE K)}
    (hBM : (borel 3 K).subgroupOf (splitE K) ≤ M)
    (hnot : ¬ M ≤ (pointStab K).subgroupOf (splitE K)) :
    (rankOneParabolic K 3 0).subgroupOf (splitE K) ≤ M := by
  let M' : Subgroup ((Fin 3 ⊕ Fin 3 → K) ≃ₗ[K] (Fin 3 ⊕ Fin 3 → K)) :=
    M.map (splitE K).subtype
  have hM'E : M' ≤ splitE K := Subgroup.map_subtype_le _
  have hBM' : borel 3 K ≤ M' := by
    rw [← Subgroup.map_subgroupOf_eq_of_le (borel_le (r := 3) (K := K))]
    exact Subgroup.map_mono hBM
  have hnot' : ¬ M' ≤ pointStab K := by
    intro h
    apply hnot
    intro x hx
    exact h (Subgroup.mem_map_of_mem (splitE K).subtype hx)
  have hP0 := rankOneParabolic_le_of_borel_le_of_not_le_pointStab hM'E hBM' hnot'
  intro x hx
  have hxP : (x : (Fin 3 ⊕ Fin 3 → K) ≃ₗ[K] (Fin 3 ⊕ Fin 3 → K)) ∈
      rankOneParabolic K 3 0 := Subgroup.mem_subgroupOf.mp hx
  have hxM' : (x : (Fin 3 ⊕ Fin 3 → K) ≃ₗ[K] (Fin 3 ⊕ Fin 3 → K)) ∈ M' := hP0 hxP
  obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hxM'
  have hyx' : y = x := Subtype.ext hyx
  rwa [hyx'] at hy

theorem natStdP0_map_conj_le_of_borel_le_of_not_le_point
    (h : ↥(splitH K)) {P : Subgroup ↥(splitH K)}
    (hB : (natStdB (K := K)).map (MulAut.conj h).toMonoidHom ≤ P)
    (hnot : ¬ P ≤ (natStdP (K := K)).map (MulAut.conj h).toMonoidHom) :
    (natStdP0 (K := K)).map (MulAut.conj h).toMonoidHom ≤ P := by
  classical
  let P' : Subgroup ↥(splitH K) := P.map (MulAut.conj h⁻¹).toMonoidHom
  have hcomp : ((MulAut.conj h⁻¹).toMonoidHom.comp (MulAut.conj h).toMonoidHom) =
      MonoidHom.id ↥(splitH K) := by
    ext x
    simp [MulAut.conj_apply, mul_assoc]
  have hcomp' : ((MulAut.conj h).toMonoidHom.comp (MulAut.conj h⁻¹).toMonoidHom) =
      MonoidHom.id ↥(splitH K) := by
    ext x
    simp [MulAut.conj_apply, mul_assoc]
  have hB' : natStdB (K := K) ≤ P' := by
    intro x hx
    have hxP : (MulAut.conj h).toMonoidHom x ∈ P :=
      hB (Subgroup.mem_map_of_mem (MulAut.conj h).toMonoidHom hx)
    have hxeq : x = (MulAut.conj h⁻¹).toMonoidHom ((MulAut.conj h).toMonoidHom x) := by
      simp [MulAut.conj_apply, mul_assoc]
    rw [hxeq]
    exact Subgroup.mem_map_of_mem (MulAut.conj h⁻¹).toMonoidHom hxP
  have hnot' : ¬ P' ≤ natStdP (K := K) := by
    intro hle
    apply hnot
    have h3 := Subgroup.map_mono (f := (MulAut.conj h).toMonoidHom) hle
    rw [Subgroup.map_map, hcomp', Subgroup.map_id] at h3
    exact h3
  let M : Subgroup ↥(splitE K) := P'.comap (eSplitH (K := K)).toMonoidHom
  have hMmap : M.map (eSplitH (K := K)).toMonoidHom = P' :=
    Subgroup.map_comap_eq_self_of_surjective (eSplitH_surjective (K := K)) P'
  have hBM : (borel 3 K).subgroupOf (splitE K) ≤ M := by
    intro x hx
    rw [Subgroup.mem_comap]
    exact hB' (Subgroup.mem_map_of_mem (eSplitH (K := K)).toMonoidHom hx)
  have hPeq : (pointStab K).subgroupOf (splitE K) =
      (splitE K ⊓ pointStab K).subgroupOf (splitE K) := by
    rw [inf_comm]
    exact (Subgroup.inf_subgroupOf_right (pointStab K) (splitE K)).symm
  have hnotM : ¬ M ≤ (pointStab K).subgroupOf (splitE K) := by
    intro hle
    apply hnot'
    have h2 : M.map (eSplitH (K := K)).toMonoidHom ≤ natStdP (K := K) := by
      rw [natStdP, ← hPeq]
      exact Subgroup.map_mono hle
    rwa [hMmap] at h2
  have hP0 : (rankOneParabolic K 3 0).subgroupOf (splitE K) ≤ M :=
    rankOneParabolic_subgroupOf_le_of_borel_le_of_not_le_pointStab hBM hnotM
  have hmap1 : natStdP0 (K := K) ≤ P' := by
    rw [natStdP0, ← hMmap]
    exact Subgroup.map_mono (f := (eSplitH (K := K)).toMonoidHom) hP0
  have h3 := Subgroup.map_mono (f := (MulAut.conj h).toMonoidHom) hmap1
  have h4 : P'.map (MulAut.conj h).toMonoidHom = P := by
    change (P.map (MulAut.conj h⁻¹).toMonoidHom).map
      (MulAut.conj h).toMonoidHom = P
    rw [Subgroup.map_map, hcomp', Subgroup.map_id]
  rwa [h4] at h3

end NaturalModel

section NaturalLineFinal

open CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin QuadraticMap
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit

variable {K : Type} [Field K] [Finite K] [CharP K 2]

instance finite_gl : Finite
    ((Fin 3 ⊕ Fin 3 → K) ≃ₗ[K] (Fin 3 ⊕ Fin 3 → K)) :=
  Finite.of_injective
    (fun f : (Fin 3 ⊕ Fin 3 → K) ≃ₗ[K] (Fin 3 ⊕ Fin 3 → K) =>
      (f : (Fin 3 ⊕ Fin 3 → K) → (Fin 3 ⊕ Fin 3 → K)))
    (fun a b h => LinearEquiv.ext (congrFun h))

theorem natStdS_le_natStdP0 : natStdS (K := K) ≤ natStdP0 (K := K) := by
  rw [natStdS, natStdP0]
  have hpb : CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit.posUnip 3 K ≤
      borel 3 K := by
    rw [← flagStab_eq_borel (K := K)]
    exact posUnip_le_flagStab
  refine Subgroup.map_mono (Subgroup.subgroupOf_mono _ ?_)
  exact hpb.trans (borel_le_rankOneParabolic (K := K) 3 0)

theorem isParabolicTwo_natStdP0 :
    IsParabolicTwo ↥(splitH K) (natStdP0 (K := K)) := by
  have h := (isParabolicTwo_rankOne (K := K)).map (eSplitH (K := K)).toMonoidHom
    (eSplitH_surjective (K := K))
  rwa [natStdP0]

theorem natStdP0_ne_top : natStdP0 (K := K) ≠ ⊤ := by
  intro htop
  have h1 : ((rankOneParabolic K 3 0).subgroupOf (splitE K)) = ⊤ := by
    apply Subgroup.map_injective (f := (eSplitH (K := K)).toMonoidHom)
      (eSplitH_injective (K := K))
    rw [natStdP0] at htop
    rw [htop, Subgroup.map_top_of_surjective _ (eSplitH_surjective (K := K))]
  have h2 : rankOneParabolic K 3 0 = splitE K := by
    have hmap := congrArg (fun M : Subgroup ↥(splitE K) =>
      M.map (splitE K).subtype) h1
    rw [Subgroup.map_subgroupOf_eq_of_le (rankOneParabolic_le_splitE (K := K)),
      ← Subgroup.top_subgroupOf (H := splitE K), Subgroup.subgroupOf_map_subtype,
      top_inf_eq] at hmap
    exact hmap
  exact rankOneParabolic_ne_top (K := K) h2

theorem natStdP0_not_le_natStdP : ¬ natStdP0 (K := K) ≤ natStdP (K := K) := by
  intro hle
  apply rankOneParabolic_not_le_pointStab (K := K)
  intro x hx
  have hxE : x ∈ splitE K := rankOneParabolic_le_splitE (K := K) hx
  let xE : ↥(splitE K) := ⟨x, hxE⟩
  have hx0 : eSplitH (K := K) xE ∈ natStdP0 (K := K) := by
    rw [natStdP0]
    exact Subgroup.mem_map_of_mem (eSplitH (K := K)).toMonoidHom
      (Subgroup.mem_subgroupOf.mpr hx)
  have hx1 : eSplitH (K := K) xE ∈ natStdP (K := K) := hle hx0
  rw [natStdP] at hx1
  obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hx1
  have hy' : y.val ∈ splitE K ⊓ pointStab K := Subgroup.mem_subgroupOf.mp hy
  have hxy : y = xE := eSplitH_injective (K := K) hyx
  rw [hxy] at hy'
  exact hy'.2

theorem isL2_bar2_hinf_subgroupOf {G : Type} [Group G] [Finite G]
    {P E : Subgroup G} (hPE : P ≤ E) {n : ℕ}
    (h : IsL2 (Bar2 (Hinf P)) n) :
    IsL2 (Bar2 (Hinf (P.subgroupOf E))) n := by
  have hsub : (Hinf P).subgroupOf E = Hinf (P.subgroupOf E) :=
    CFSG.perfectResidual_subtype_subgroupOf P E hPE
  have hHinfle : Hinf P ≤ E := by
    rw [Hinf]
    exact (Subgroup.map_subtype_le _).trans hPE
  let eSub : ↥(Hinf (P.subgroupOf E)) ≃* ↥(Hinf P) :=
    (MulEquiv.subgroupCongr hsub).symm.trans
      (Subgroup.subgroupOfEquivOfLe hHinfle)
  obtain ⟨ebar⟩ := nonempty_bar2_mulEquiv_of_equiv eSub
  exact CFSG.Blueprint.LieModel.of_mulEquiv (t := .PSL) (n := 2) (p := 2) (f := n)
    ebar.symm h

theorem isL2_natStdP0_of_surjection {n : ℕ} (hn : 2 ≤ n)
    (hK : Nat.card K = 2 ^ n)
    (f : ↥(Hinf (rankOneParabolic K 3 0)) →* Matrix.SpecialLinearGroup (Fin 2) K)
    (hf : Function.Surjective f) (hker : IsPGroup 2 f.ker) :
    IsL2 (Bar2 (Hinf (natStdP0 (K := K)))) n := by
  have hstd : IsL2 (Bar2 (Hinf (rankOneParabolic K 3 0))) n :=
    isL2_rankOneParabolic_split_of_surjection (r := 3) (K := K) 0 hn hK f hf hker
  have hsub : IsL2 (Bar2 (Hinf ((rankOneParabolic K 3 0).subgroupOf
      (splitE K)))) n :=
    isL2_bar2_hinf_subgroupOf (rankOneParabolic_le_splitE (K := K)) hstd
  exact isL2_bar2_hinf_map_equiv (eSplitH (K := K))
    ((rankOneParabolic K 3 0).subgroupOf (splitE K)) hsub

theorem hinf_natStdP0_eq_bot
    (h : Hinf (rankOneParabolic K 3 0) = ⊥) :
    Hinf (natStdP0 (K := K)) = ⊥ := by
  have hsub : (Hinf (rankOneParabolic K 3 0)).subgroupOf (splitE K) =
      Hinf ((rankOneParabolic K 3 0).subgroupOf (splitE K)) :=
    CFSG.perfectResidual_subtype_subgroupOf _ _
      (rankOneParabolic_le_splitE (K := K))
  have h' : Hinf ((rankOneParabolic K 3 0).subgroupOf (splitE K)) = ⊥ := by
    rw [← hsub, h, Subgroup.bot_subgroupOf]
  rw [natStdP0, ← Hinf_map, h', Subgroup.map_bot]

theorem omegaPlus6Line_natural_of_condition (K : Type) [Field K] [Finite K]
    (m : ℕ) [CharP K 2] (hK : Nat.card K = 2 ^ m)
    (hmain : m ≠ 1 → ∃ f : ↥(Hinf (rankOneParabolic K 3 0)) →*
      Matrix.SpecialLinearGroup (Fin 2) K,
      Function.Surjective f ∧ IsPGroup 2 f.ker)
    (hbot : m = 1 → Hinf (rankOneParabolic K 3 0) = ⊥) :
    OmegaPlus6Line (CFSG.Quasithin.H.StdMod (Fin 3 ⊕ Fin 3) K)
      (CFSG.Quasithin.H.natImage
        (CFSG.Open.StatedOmega (CFSG.Open.StatedQuadPlus 3 K))) m := by
  rw [show CFSG.Quasithin.H.natImage
      (CFSG.Open.StatedOmega (CFSG.Open.StatedQuadPlus 3 K)) = splitH K from
    natImage_statedOmega_eq_map (n := 3) (K := K) (by norm_num)]
  unfold OmegaPlus6Line
  intro S
  intro ℓ Pℓ
  intro Tstar hTnorm hT2 hST
  intro Good Pstar hmin
  classical
  have hSylS : CFSG.QuasithinUnique.IsSylowTwoOf (S : Subgroup ↥(splitH K)) ⊤ :=
    CFSG.QuasithinUnique.isSylowTwoOf_top_of_sylow S
  have hSylStd : CFSG.QuasithinUnique.IsSylowTwoOf (natStdS (K := K)) ⊤ :=
    isSylowTwoOf_natStdS (K := K)
  obtain ⟨h, -, hconj⟩ := CFSG.QuasithinUnique.IsSylowTwoOf.exists_conj hSylStd hSylS
  let SH : Subgroup (MulAut (CFSG.Quasithin.H.StdMod (Fin 3 ⊕ Fin 3) K)) :=
    (S : Subgroup ↥(splitH K)).map (splitH K).subtype
  have hcomp : (splitH K).subtype.comp (MulAut.conj h).toMonoidHom =
      (MulAut.conj ((h : ↥(splitH K)) :
        MulAut (CFSG.Quasithin.H.StdMod (Fin 3 ⊕ Fin 3) K))).toMonoidHom.comp
        (splitH K).subtype := by
    ext x
    rfl
  have hSH : SH = ((natStdS (K := K)).map (splitH K).subtype).map
      (MulAut.conj ((h : ↥(splitH K)) :
        MulAut (CFSG.Quasithin.H.StdMod (Fin 3 ⊕ Fin 3) K))).toMonoidHom := by
    dsimp [SH]
    rw [hconj, Subgroup.map_map, hcomp, ← Subgroup.map_map]
    rfl
  have hℓ : ℓ = (pointSub K).map
      (((h : ↥(splitH K)) :
        MulAut (CFSG.Quasithin.H.StdMod (Fin 3 ⊕ Fin 3) K))).toMonoidHom := by
    have h1 : ℓ = CFSG.Quasithin.fixV SH := by
      dsimp [ℓ, SH]
      rw [fixedPointSubgroup_sylow_map S, fixedPointSubgroup_eq_fixV]
    rw [h1, hSH, fixV_map_conj, fixV_natStdS]
  have hPℓ : Pℓ = (natStdP (K := K)).map (MulAut.conj h).toMonoidHom := by
    have hstab := stabilizer_map_conj_subgroup (H := splitH K) h (pointSub K)
    dsimp [Pℓ]
    rw [hℓ]
    exact hstab.trans (congrArg (fun X : Subgroup ↥(splitH K) =>
      X.map (MulAut.conj h).toMonoidHom)
      (stabilizer_pointSub_eq_natStdP (K := K)))
  have hTstarH : Tstar ⊓ splitH K = SH := by
    have hX2 : IsPGroup 2 ↥(Tstar ⊓ splitH K) := by
      intro x
      obtain ⟨k, hk⟩ := hT2 ⟨(x : MulAut _), x.2.1⟩
      exact ⟨k, Subtype.ext (by simpa using congrArg Subtype.val hk)⟩
    have hX2sub : IsPGroup 2 ((Tstar ⊓ splitH K).subgroupOf (splitH K)) :=
      hX2.of_equiv (Subgroup.subgroupOfEquivOfLe inf_le_right).symm
    have hSX : (S : Subgroup ↥(splitH K)) ≤
        (Tstar ⊓ splitH K).subgroupOf (splitH K) := by
      intro x hx
      exact ⟨hST (Subgroup.mem_map_of_mem (splitH K).subtype hx), x.2⟩
    have hEq : (Tstar ⊓ splitH K).subgroupOf (splitH K) =
        (S : Subgroup ↥(splitH K)) :=
      S.is_maximal' hX2sub hSX
    have h1 := congrArg (fun X : Subgroup ↥(splitH K) =>
      X.map (splitH K).subtype) hEq
    rw [Subgroup.map_subgroupOf_eq_of_le inf_le_right] at h1
    simpa [SH] using h1
  have hSH_normal : ∀ t ∈ Tstar, SH.map (MulAut.conj t).toMonoidHom = SH := by
    intro t ht
    have hle : SH.map (MulAut.conj t).toMonoidHom ≤ SH := by
      rintro x ⟨s, hs, rfl⟩
      obtain ⟨s0, hs0, rfl⟩ := Subgroup.mem_map.mp hs
      have htH : t * (s0 : MulAut _) * t⁻¹ ∈ splitH K :=
        (Subgroup.mem_normalizer_iff.mp (hTnorm ht) (s0 : MulAut _)).mp s0.2
      have hmem : t * (s0 : MulAut _) * t⁻¹ ∈ Tstar ⊓ splitH K :=
        ⟨Tstar.mul_mem (Tstar.mul_mem ht
            (hST (Subgroup.mem_map_of_mem (splitH K).subtype hs0)))
          (Tstar.inv_mem ht), htH⟩
      rwa [hTstarH] at hmem
    exact Subgroup.eq_of_le_of_card_ge hle (by
      rw [Subgroup.card_map_of_injective (f := (MulAut.conj t).toMonoidHom)
        (MulAut.conj t).injective])
  have hℓ_t : ∀ t ∈ Tstar, ℓ.map (t : MulAut _).toMonoidHom = ℓ := by
    intro t ht
    have h1 : ℓ = CFSG.Quasithin.fixV SH := by
      dsimp [ℓ, SH]
      rw [fixedPointSubgroup_sylow_map S, fixedPointSubgroup_eq_fixV]
    rw [h1, ← fixV_map_conj SH t, hSH_normal t ht, ← h1]
  have hPℓ_t : ∀ t ∈ Tstar,
      (Pℓ.map (splitH K).subtype).map (MulAut.conj t).toMonoidHom =
        Pℓ.map (splitH K).subtype := by
    intro t ht
    dsimp [Pℓ]
    have h := map_subtype_stabilizer_conj_normalizer (H := splitH K) t
      (hTnorm ht) ℓ
    rw [hℓ_t t ht] at h
    exact h
  have hSHsub : SH.subgroupOf (splitH K) = (S : Subgroup ↥(splitH K)) := by
    ext x
    constructor
    · intro hx
      exact (Subgroup.mem_map_iff_mem (splitH K).subtype_injective).mp hx
    · intro hx
      exact Subgroup.mem_map_of_mem (splitH K).subtype hx
  have hB_amb : (Subgroup.normalizer (S : Set ↥(splitH K))).map
        (splitH K).subtype =
      Subgroup.normalizer (SH : Set (MulAut _)) ⊓ splitH K := by
    change (Subgroup.normalizer ((S : Subgroup ↥(splitH K)) : Set _)).map
      (splitH K).subtype = Subgroup.normalizer (SH : Set _) ⊓ splitH K
    have hSHle : SH ≤ splitH K := by
      rintro _ ⟨s, -, rfl⟩
      exact s.2
    have h1 := Subgroup.subgroupOf_normalizer_eq (H := SH) (N := splitH K) hSHle
    rw [hSHsub] at h1
    rw [← h1, Subgroup.subgroupOf_map_subtype]
  have hSHnorm : ∀ t ∈ Tstar,
      (Subgroup.normalizer (SH : Set (MulAut _))).map
        (MulAut.conj t).toMonoidHom =
        Subgroup.normalizer (SH : Set _) := by
    intro t ht
    rw [Subgroup.map_equiv_normalizer_eq SH (MulAut.conj t), hSH_normal t ht]
  have hH_T : ∀ t ∈ Tstar,
      (splitH K).map (MulAut.conj t).toMonoidHom = splitH K := by
    intro t ht
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mp (hTnorm ht)
  have hB_t : ∀ t ∈ Tstar,
      ((Subgroup.normalizer (S : Set ↥(splitH K))).map (splitH K).subtype).map
        (MulAut.conj t).toMonoidHom =
      (Subgroup.normalizer (S : Set ↥(splitH K))).map (splitH K).subtype := by
    intro t ht
    rw [hB_amb, Subgroup.map_inf _ _ _ (MulAut.conj t).injective,
      hSHnorm t ht, hH_T t ht]
  have hB : Subgroup.normalizer (S : Set ↥(splitH K)) =
      (natStdB (K := K)).map (MulAut.conj h).toMonoidHom := by
    change Subgroup.normalizer ((S : Subgroup ↥(splitH K)) : Set (↥(splitH K))) =
      (natStdB (K := K)).map (MulAut.conj h).toMonoidHom
    rw [hconj, ← Subgroup.map_equiv_normalizer_eq (natStdS (K := K)) (MulAut.conj h),
      normalizer_natStdS]
  have hBP : Subgroup.normalizer (S : Set ↥(splitH K)) ≤ Pstar :=
    hmin.1.1.normalizer_le S hmin.1.2.1
  have hBle : (natStdB (K := K)).map (MulAut.conj h).toMonoidHom ≤ Pstar := by
    rwa [← hB]
  have hnotPℓ : ¬ Pstar ≤ (natStdP (K := K)).map
      (MulAut.conj h).toMonoidHom := by
    rw [← hPℓ]
    exact hmin.1.2.2.2
  have hQle : (natStdP0 (K := K)).map (MulAut.conj h).toMonoidHom ≤ Pstar :=
    natStdP0_map_conj_le_of_borel_le_of_not_le_point h hBle hnotPℓ
  have hQpar : IsParabolicTwo ↥(splitH K)
      ((natStdP0 (K := K)).map (MulAut.conj h).toMonoidHom) :=
    (isParabolicTwo_natStdP0 (K := K)).map (MulAut.conj h).toMonoidHom
      (MulAut.conj h).surjective
  have hS_le_Q : (S : Subgroup ↥(splitH K)) ≤
      (natStdP0 (K := K)).map (MulAut.conj h).toMonoidHom := by
    rw [hconj]
    exact Subgroup.map_mono (f := (MulAut.conj h).toMonoidHom)
      (natStdS_le_natStdP0 (K := K))
  have hQnotPℓ : ¬ (natStdP0 (K := K)).map (MulAut.conj h).toMonoidHom ≤ Pℓ := by
    rw [hPℓ]
    intro hle
    exact natStdP0_not_le_natStdP (K := K)
      ((Subgroup.map_le_map_iff_of_injective
        (MulAut.conj h).injective).mp hle)
  have hQgoodT : ∀ t ∈ Tstar,
      (((natStdP0 (K := K)).map (MulAut.conj h).toMonoidHom).map
          (splitH K).subtype).map (MulAut.conj t).toMonoidHom =
        ((natStdP0 (K := K)).map (MulAut.conj h).toMonoidHom).map
          (splitH K).subtype := by
    intro t ht
    set Q : Subgroup ↥(splitH K) :=
      (natStdP0 (K := K)).map (MulAut.conj h).toMonoidHom with hQ
    set Φ : Subgroup ↥(splitH K) → Subgroup ↥(splitH K) := fun P =>
      ((P.map (splitH K).subtype).map (MulAut.conj t).toMonoidHom).comap
        (splitH K).subtype with hΦ
    have hΦmap : ∀ P : Subgroup ↥(splitH K),
        (Φ P).map (splitH K).subtype =
          (P.map (splitH K).subtype).map (MulAut.conj t).toMonoidHom := by
      intro P
      rw [hΦ]
      exact Subgroup.map_comap_eq_self (by
        rw [Subgroup.range_subtype]
        exact le_trans (Subgroup.map_mono (Subgroup.map_subtype_le P))
          (le_of_eq (Subgroup.mem_normalizer_iff_map_conj_eq.mp (hTnorm ht))))
    have hΦmono : Monotone Φ := by
      intro P R hPR
      rw [hΦ]
      exact Subgroup.comap_mono (Subgroup.map_mono (Subgroup.map_mono hPR))
    have hΦPℓ : Φ ((natStdP (K := K)).map (MulAut.conj h).toMonoidHom) =
        (natStdP (K := K)).map (MulAut.conj h).toMonoidHom := by
      rw [hΦ]
      beta_reduce
      have h1 : ((natStdP (K := K)).map (MulAut.conj h).toMonoidHom).map
          (splitH K).subtype = Pℓ.map (splitH K).subtype := by rw [hPℓ]
      rw [h1, hPℓ_t t ht, Subgroup.comap_map_eq_self_of_injective
        (splitH K).subtype_injective, hPℓ]
    have hΦB : Φ ((natStdB (K := K)).map (MulAut.conj h).toMonoidHom) =
        (natStdB (K := K)).map (MulAut.conj h).toMonoidHom := by
      rw [hΦ]
      beta_reduce
      have h1 : ((natStdB (K := K)).map (MulAut.conj h).toMonoidHom).map
          (splitH K).subtype =
          (Subgroup.normalizer (S : Set ↥(splitH K))).map (splitH K).subtype :=
        congrArg (fun X : Subgroup ↥(splitH K) => X.map (splitH K).subtype) hB.symm
      rw [h1, hB_t t ht, Subgroup.comap_map_eq_self_of_injective
        (splitH K).subtype_injective]
      exact hB
    have hΦQnotPℓ : ¬ Φ Q ≤ (natStdP (K := K)).map
        (MulAut.conj h).toMonoidHom := by
      intro hle
      apply hQnotPℓ
      have h1 : (Q.map (splitH K).subtype).map (MulAut.conj t).toMonoidHom ≤
          Pℓ.map (splitH K).subtype := by
        rw [← hΦmap Q, hPℓ]
        exact Subgroup.map_mono hle
      have hcomp_inv : ((MulAut.conj t⁻¹).toMonoidHom.comp
          (MulAut.conj t).toMonoidHom) = MonoidHom.id _ := by
        ext z
        simp [MulAut.conj_apply, mul_assoc]
      have h2 := Subgroup.map_mono (f := (MulAut.conj t⁻¹).toMonoidHom) h1
      rw [Subgroup.map_map, hcomp_inv, Subgroup.map_id,
        hPℓ_t t⁻¹ (Tstar.inv_mem ht)] at h2
      exact (Subgroup.map_le_map_iff_of_injective (f := (splitH K).subtype)
        (splitH K).subtype_injective).mp h2
    have hBleP0 : natStdB (K := K) ≤ natStdP0 (K := K) := by
      rw [natStdB, natStdP0]
      exact Subgroup.map_mono (Subgroup.subgroupOf_mono _
        (borel_le_rankOneParabolic (K := K) 3 0))
    have hQleΦ : Q ≤ Φ Q := by
      have hBQ : (natStdB (K := K)).map (MulAut.conj h).toMonoidHom ≤ Q := by
        dsimp [Q]
        exact Subgroup.map_mono (f := (MulAut.conj h).toMonoidHom) hBleP0
      have hBΦ : (natStdB (K := K)).map (MulAut.conj h).toMonoidHom ≤ Φ Q := by
        have h := hΦmono hBQ
        rwa [hΦB] at h
      exact natStdP0_map_conj_le_of_borel_le_of_not_le_point h hBΦ hΦQnotPℓ
    have hXle : Q.map (splitH K).subtype ≤
        (Q.map (splitH K).subtype).map (MulAut.conj t).toMonoidHom := by
      rw [← hΦmap Q]
      exact Subgroup.map_mono hQleΦ
    have hcard : Nat.card ((Q.map (splitH K).subtype).map
          (MulAut.conj t).toMonoidHom) = Nat.card (Q.map (splitH K).subtype) :=
      Nat.card_congr (Subgroup.equivMapOfInjective (Q.map (splitH K).subtype)
        (MulAut.conj t).toMonoidHom (MulAut.conj t).injective).toEquiv.symm
    have heq : Q.map (splitH K).subtype =
        (Q.map (splitH K).subtype).map (MulAut.conj t).toMonoidHom :=
      Subgroup.eq_of_le_of_card_ge hXle (by rw [hcard])
    exact heq.symm
  have hQne : (natStdP0 (K := K)).map (MulAut.conj h).toMonoidHom ≠ ⊤ := by
    intro htop
    apply natStdP0_ne_top (K := K)
    have hcomp : ((MulAut.conj h⁻¹).toMonoidHom.comp
        (MulAut.conj h).toMonoidHom) = MonoidHom.id ↥(splitH K) := by
      ext x
      simp [MulAut.conj_apply, mul_assoc]
    have h2 := congrArg (fun X : Subgroup ↥(splitH K) =>
      X.map (MulAut.conj h⁻¹).toMonoidHom) htop
    rw [Subgroup.map_map, hcomp, Subgroup.map_id,
      Subgroup.map_top_of_surjective _ (MulAut.conj h⁻¹).surjective] at h2
    exact h2
  have hQgood : Good ((natStdP0 (K := K)).map (MulAut.conj h).toMonoidHom) :=
    ⟨hQpar, hS_le_Q, hQgoodT, hQnotPℓ⟩
  have hPstar_ne_top : Pstar ≠ ⊤ := by
    intro htop
    have hle : (⊤ : Subgroup ↥(splitH K)) ≤
        (natStdP0 (K := K)).map (MulAut.conj h).toMonoidHom := by
      rw [← htop]
      exact hmin.2 hQgood (by rw [htop]; exact le_top)
    exact hQne (top_le_iff.mp hle)
  have hPstar_eq : Pstar = (natStdP0 (K := K)).map
      (MulAut.conj h).toMonoidHom :=
    le_antisymm (hmin.2 hQgood hQle) hQle
  refine ⟨?_, ?_⟩
  · rw [hPstar_eq]
    exact hQne
  · by_cases hm : m = 1
    · right
      refine ⟨hm, ?_⟩
      rw [hPstar_eq]
      have hstdBot : Hinf (natStdP0 (K := K)) = ⊥ :=
        hinf_natStdP0_eq_bot (hbot hm)
      exact Hinf_map_eq_bot (MulAut.conj h) (natStdP0 (K := K)) hstdBot
    · left
      obtain ⟨f, hf, hker⟩ := hmain hm
      have hm2 : 2 ≤ m := by
        have h2K : 2 ≤ Nat.card K := by
          haveI : Fintype K := Fintype.ofFinite K
          rw [Nat.card_eq_fintype_card]
          exact Nat.succ_le_of_lt Fintype.one_lt_card
        have hm0 : m ≠ 0 := by
          intro h0
          rw [h0] at hK
          simp at hK
          omega
        omega
      have hstd : IsL2 (Bar2 (Hinf (natStdP0 (K := K)))) m :=
        isL2_natStdP0_of_surjection (K := K) hm2 hK f hf hker
      rw [hPstar_eq]
      exact isL2_bar2_hinf_map_equiv (MulAut.conj h) (natStdP0 (K := K)) hstd

end NaturalLineFinal

theorem hbot_split (K : Type) [Field K] [Finite K] (hK : Nat.card K = 2) :
    Hinf (rankOneParabolic K 3 0) = ⊥ := by
  haveI : Fintype K := Fintype.ofFinite K
  haveI : CharP K 2 := charP_of_card_eq_prime (p := 2) (by
    rw [← Nat.card_eq_fintype_card]
    exact hK)
  haveI : Finite ((Fin 3 ⊕ Fin 3 → K) ≃ₗ[K] (Fin 3 ⊕ Fin 3 → K)) :=
    Finite.of_injective
      (fun f : (Fin 3 ⊕ Fin 3 → K) ≃ₗ[K] (Fin 3 ⊕ Fin 3 → K) =>
        (f : (Fin 3 ⊕ Fin 3 → K) → (Fin 3 ⊕ Fin 3 → K)))
      (fun a b h => LinearEquiv.ext (congrFun h))
  exact CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit.hinf_rankOneParabolic_split_eq_bot_of_solvable
    (K := K) (r := 3) (0 : Fin 3)
    (CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit.isSolvable_rankOneParabolic_F2
      (K := K) (r := 3) (by norm_num) (0 : Fin 3) hK)

theorem omegaPlus6Natural_holds_cond
    (hmain : ∀ (K : Type) [Field K] [Finite K] (m : ℕ), Nat.card K = 2 ^ m → m ≠ 1 →
      ∃ f : ↥(Hinf (rankOneParabolic K 3 0)) →* Matrix.SpecialLinearGroup (Fin 2) K,
        Function.Surjective f ∧ IsPGroup 2 f.ker) :
    ∀ (K : Type) [Field K] [Finite K] (m : ℕ), Nat.card K = 2 ^ m →
      OmegaPlus6Line (CFSG.Quasithin.H.StdMod (Fin 3 ⊕ Fin 3) K)
        (CFSG.Quasithin.H.natImage
          (CFSG.Open.StatedOmega (CFSG.Open.StatedQuadPlus 3 K))) m := by
  intro K _ _ m hK
  haveI : CharP K 2 := by
    have : Fintype K := Fintype.ofFinite K
    exact charP_of_card_eq_prime_pow (f := m) (by
      rw [← Nat.card_eq_fintype_card]; exact hK)
  refine omegaPlus6Line_natural_of_condition K m hK ?_ ?_
  · intro hm
    exact hmain K m hK hm
  · intro hm1
    exact hbot_split K (by rw [hK, hm1]; norm_num)

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
