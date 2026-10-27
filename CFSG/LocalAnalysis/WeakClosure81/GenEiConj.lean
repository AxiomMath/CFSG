module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DefsE
import CFSG.GroupTheory.SubgroupTransport
import CFSG.GroupTheory.Fitting.MulEquiv
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
  (ECaseI ECaseII tA normAIn InCalE InCalEi genEi IsOmegaColl InFOmega)
open CFSG.LocalAnalysis.UniquenessCase.UC22 (Bar2)
open CFSG.GroupTheory (map_subgroupOf_equivMapOfInjective map_map_mk'_congr map_comap_mk'_congr
  isSylowOf_map_mulEquiv)
open scoped Pointwise

variable {G G' : Type} [Group G] [Group G']

private noncomputable abbrev mapEquiv (e : G ≃* G') (K : Subgroup G) :
    ↥K ≃* ↥(K.map e.toMonoidHom) :=
  Subgroup.equivMapOfInjective K e.toMonoidHom e.injective

theorem eCaseI_map_mulEquiv (e : G ≃* G') (A K : Subgroup G) :
    ECaseI (A.map e.toMonoidHom) (K.map e.toMonoidHom) ↔ ECaseI A K := by
  refine Iff.symm ?_
  have hO : (CFSG.pCore 2 ↥K).map (mapEquiv e K).toMonoidHom =
      CFSG.pCore 2 ↥(K.map e.toMonoidHom) :=
    CFSG.LieType.BorelTits.map_pCore_mulEquiv 2 (mapEquiv e K)
  set φ' : Bar2 K ≃* Bar2 (K.map e.toMonoidHom) :=
    QuotientGroup.congr (CFSG.pCore 2 ↥K) (CFSG.pCore 2 ↥(K.map e.toMonoidHom)) (mapEquiv e K) hO
    with hφ'
  have hbar : (E1.barO2 ↥K (A.subgroupOf K)).map φ'.toMonoidHom =
      E1.barO2 ↥(K.map e.toMonoidHom)
        ((A.map e.toMonoidHom).subgroupOf (K.map e.toMonoidHom)) := by
    have h := map_map_mk'_congr (mapEquiv e K) hO (A.subgroupOf K)
    rw [map_subgroupOf_equivMapOfInjective e.toMonoidHom e.injective] at h
    simpa only [E1.barO2] using h
  have hfit := CFSG.WholeGroup.fittingSubgroup_map_mulEquiv φ'
  unfold ECaseI
  refine exists_congr fun p =>
    and_congr Iff.rfl (and_congr Iff.rfl (and_congr ?_ (and_congr ?_ ?_)))
  · rw [← E1.oTwoPTwo_map_mulEquiv (mapEquiv e K) p, E1.map_eq_top_iff_mulEquiv]
  · rw [← hfit, ← hbar, ← Subgroup.map_commutator, E1.map_inj_mulEquiv]
  · rw [CFSG.LieType.BorelTits.pCoreOf_map_mulEquiv 2 e K,
      Subgroup.relIndex_map_map_of_injective _ _ e.injective]

private theorem normAIn_map_equiv (e : G ≃* G') (A K : Subgroup G)
    (L : Subgroup (↥K ⧸ CFSG.solvableRadical ↥K)) :
    normAIn (A.map e.toMonoidHom) (K.map e.toMonoidHom)
        (L.map (QuotientGroup.congr (CFSG.solvableRadical ↥K)
          (CFSG.solvableRadical ↥(K.map e.toMonoidHom)) (mapEquiv e K)
          (E1.solvableRadical_map_mulEquiv (mapEquiv e K))).toMonoidHom) =
      (normAIn A K L).map e.toMonoidHom := by
  set φ : ↥K ≃* ↥(K.map e.toMonoidHom) := mapEquiv e K with hφ
  set φ' : (↥K ⧸ CFSG.solvableRadical ↥K) ≃*
      (↥(K.map e.toMonoidHom) ⧸ CFSG.solvableRadical ↥(K.map e.toMonoidHom)) :=
    QuotientGroup.congr _ _ φ (E1.solvableRadical_map_mulEquiv φ) with hφ'
  have hR := E1.solvableRadical_map_mulEquiv φ
  have hsub := map_subgroupOf_equivMapOfInjective e.toMonoidHom e.injective A K
  have hnorm : (Subgroup.normalizer (L : Set (↥K ⧸ CFSG.solvableRadical ↥K))).map
      φ'.toMonoidHom = Subgroup.normalizer (L.map φ'.toMonoidHom : Set _) :=
    Subgroup.map_equiv_normalizer_eq L φ'
  have hcomap := map_comap_mk'_congr φ hR hnorm
  have h1 : ((A.subgroupOf K) ⊓
      (Subgroup.normalizer (L : Set (↥K ⧸ CFSG.solvableRadical ↥K))).comap
        (QuotientGroup.mk' (CFSG.solvableRadical ↥K))).map φ.toMonoidHom =
      (A.map e.toMonoidHom).subgroupOf (K.map e.toMonoidHom) ⊓
        (Subgroup.normalizer (L.map φ'.toMonoidHom : Set _)).comap
          (QuotientGroup.mk' (CFSG.solvableRadical ↥(K.map e.toMonoidHom))) := by
    rw [Subgroup.map_inf _ _ _ φ.injective, hsub, hcomap]
  have hcomp : ((K.map e.toMonoidHom).subtype).comp φ.toMonoidHom =
      e.toMonoidHom.comp K.subtype := by
    ext x
    rfl
  unfold normAIn
  rw [← h1, Subgroup.map_map, Subgroup.map_map, hcomp]

theorem eCaseII_map_mulEquiv [Finite G] [Finite G'] (e : G ≃* G') (T A K : Subgroup G) :
    ECaseII (T.map e.toMonoidHom) (A.map e.toMonoidHom) (K.map e.toMonoidHom) ↔
      ECaseII T A K := by
  refine Iff.symm ?_
  have hτ : tA (T.map e.toMonoidHom) (A.map e.toMonoidHom) = (tA T A).map e.toMonoidHom :=
    (E1.tauOf_top_map_mulEquiv e T A).symm
  have hO := E1.oInftyE_map_mulEquiv (mapEquiv e K)
  set φ' : (↥K ⧸ CFSG.solvableRadical ↥K) ≃*
      (↥(K.map e.toMonoidHom) ⧸ CFSG.solvableRadical ↥(K.map e.toMonoidHom)) :=
    QuotientGroup.congr _ _ (mapEquiv e K) (E1.solvableRadical_map_mulEquiv (mapEquiv e K))
    with hφ'
  have hbarA : (E1.barRad ↥K (A.subgroupOf K)).map φ'.toMonoidHom =
      E1.barRad ↥(K.map e.toMonoidHom)
        ((A.map e.toMonoidHom).subgroupOf (K.map e.toMonoidHom)) := by
    have h := map_map_mk'_congr (mapEquiv e K)
      (E1.solvableRadical_map_mulEquiv (mapEquiv e K)) (A.subgroupOf K)
    rw [map_subgroupOf_equivMapOfInjective e.toMonoidHom e.injective] at h
    simpa only [E1.barRad] using h
  have hτ' : (((tA T A).subgroupOf K).map
        (QuotientGroup.mk' (CFSG.solvableRadical ↥K))).map φ'.toMonoidHom =
      ((tA (T.map e.toMonoidHom) (A.map e.toMonoidHom)).subgroupOf (K.map e.toMonoidHom)).map
        (QuotientGroup.mk' (CFSG.solvableRadical ↥(K.map e.toMonoidHom))) := by
    rw [map_map_mk'_congr (mapEquiv e K)
        (E1.solvableRadical_map_mulEquiv (mapEquiv e K)) ((tA T A).subgroupOf K),
      map_subgroupOf_equivMapOfInjective e.toMonoidHom e.injective, ← hτ]
  unfold ECaseII
  refine and_congr (by rw [← E1.solvableRadical_map_mulEquiv (mapEquiv e K),
    E1.isTwoClosed_map_mulEquiv]) (and_congr ?_ (and_congr ?_ ?_))
  · rw [← E1.map_eq_top_iff_mulEquiv (QuotientGroup.congr _ _ (mapEquiv e K) hO),
      CFSG.LieType.BorelTits.map_pCore_mulEquiv 2
        (QuotientGroup.congr _ _ (mapEquiv e K) hO)]
  · have h1 : (twoResidual (⊤ : Subgroup ↥K)).map (mapEquiv e K).toMonoidHom =
        twoResidual (⊤ : Subgroup ↥(K.map e.toMonoidHom)) := by
      rw [E1.twoResidual_map_mulEquiv,
        Subgroup.map_top_of_surjective _ (mapEquiv e K).surjective]
    have h2 : (perfectCore (⊤ : Subgroup ↥K)).map (mapEquiv e K).toMonoidHom =
        perfectCore (⊤ : Subgroup ↥(K.map e.toMonoidHom)) := by
      rw [map_perfectCore, Subgroup.map_top_of_surjective _ (mapEquiv e K).surjective]
    rw [← h1, ← h2, E1.map_inj_mulEquiv]
  · refine E1.exists_subgroup_congr φ' fun L => ?_
    refine and_congr ((CFSG.LocalCores.component_isomorphism φ').1 L) (and_congr ?_ ?_)
    · have hb := E1.map_biSup_conjSub φ'
        (((tA T A).subgroupOf K).map (QuotientGroup.mk' (CFSG.solvableRadical ↥K))) L
      unfold conjSub at hb
      rw [← E1.map_inj_mulEquiv φ', E1.layer_map_mulEquiv, hb, hτ']
    · have hNX : normAIn (A.map e.toMonoidHom) (K.map e.toMonoidHom) (L.map φ'.toMonoidHom) =
          (normAIn A K L).map e.toMonoidHom := normAIn_map_equiv e A K L
      have hIX : (A.map e.toMonoidHom) ⊓ pCoreOf 2 (K.map e.toMonoidHom) =
          (A ⊓ pCoreOf 2 K).map e.toMonoidHom := by
        rw [CFSG.LieType.BorelTits.pCoreOf_map_mulEquiv 2 e K,
          Subgroup.map_inf A (pCoreOf 2 K) e.toMonoidHom e.injective]
      have hX : (⁅L, E1.barRad ↥K (A.subgroupOf K)⁆).map φ'.toMonoidHom =
          ⁅L.map φ'.toMonoidHom,
            E1.barRad ↥(K.map e.toMonoidHom)
              ((A.map e.toMonoidHom).subgroupOf (K.map e.toMonoidHom))⁆ := by
        rw [Subgroup.map_commutator, hbarA]
      rw [← E1.map_inj_mulEquiv φ', hX, hNX, hIX,
        Subgroup.relIndex_map_map_of_injective _ _ e.injective, E1.map_inj_mulEquiv]

theorem inCalE_map_mulEquiv [Finite G] [Finite G'] (e : G ≃* G') (T A K : Subgroup G) :
    InCalE (T.map e.toMonoidHom) (A.map e.toMonoidHom) (K.map e.toMonoidHom) ↔
      InCalE T A K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hτ : tA (T.map e.toMonoidHom) (A.map e.toMonoidHom) = (tA T A).map e.toMonoidHom :=
    (E1.tauOf_top_map_mulEquiv e T A).symm
  unfold InCalE
  rw [hτ, ← Subgroup.map_inf T K e.toMonoidHom e.injective]
  refine and_congr (E1.map_le_map_iff_mulEquiv e)
    (and_congr (isSylowOf_map_mulEquiv e) (and_congr ?_ ?_))
  · rw [CFSG.LieType.BorelTits.pCoreOf_map_mulEquiv 2 e K, E1.map_le_map_iff_mulEquiv]
  · exact or_congr (eCaseI_map_mulEquiv e A K) (eCaseII_map_mulEquiv e T A K)

theorem inCalEi_map_mulEquiv [Finite G] [Finite G'] (e : G ≃* G') (i : ℕ) (T A K : Subgroup G) :
    InCalEi i (T.map e.toMonoidHom) (A.map e.toMonoidHom) (K.map e.toMonoidHom) ↔
      InCalEi i T A K := by
  have hm : E3.mQuot (A.map e.toMonoidHom) (pCoreOf 2 (K.map e.toMonoidHom)) =
      E3.mQuot A (pCoreOf 2 K) := by
    unfold E3.mQuot
    rw [CFSG.LieType.BorelTits.pCoreOf_map_mulEquiv 2 e K,
      Subgroup.relIndex_map_map_of_injective _ _ e.injective]
  unfold InCalEi
  exact and_congr (inCalE_map_mulEquiv e T A K) (by rw [hm])

theorem genEi_map_image [Finite G] [Finite G'] (e : G ≃* G') (i : ℕ) (T : Subgroup G)
    (Ω : Set (Subgroup G)) :
    genEi i (T.map e.toMonoidHom) (Subgroup.map e.toMonoidHom '' Ω) =
      (genEi i T Ω).map e.toMonoidHom := by
  apply le_antisymm
  · refine iSup₂_le fun A' hA' => iSup_le fun hA'T => iSup₂_le fun K' hK' => ?_
    obtain ⟨A, hA, rfl⟩ := hA'
    obtain ⟨K, rfl⟩ : ∃ K : Subgroup G, K.map e.toMonoidHom = K' :=
      ⟨K'.comap e.toMonoidHom, Subgroup.map_comap_eq_self_of_surjective e.surjective K'⟩
    have hK : InCalEi i T A K := (inCalEi_map_mulEquiv e i T A K).mp hK'
    exact Subgroup.map_mono (le_iSup₂_of_le A hA (le_iSup_of_le
      ((E1.map_le_map_iff_mulEquiv e).mp hA'T) (le_iSup₂_of_le K hK le_rfl)))
  · rw [Subgroup.map_le_iff_le_comap]
    refine iSup₂_le fun A hA => iSup_le fun hAT => iSup₂_le fun K hK => ?_
    rw [← Subgroup.map_le_iff_le_comap]
    exact le_iSup₂_of_le (A.map e.toMonoidHom) ⟨A, hA, rfl⟩ (le_iSup_of_le
      (Subgroup.map_mono hAT) (le_iSup₂_of_le (K.map e.toMonoidHom)
        ((inCalEi_map_mulEquiv e i T A K).mpr hK) le_rfl))

theorem conjSub_genEi [Finite G] (i : ℕ) {T : Subgroup G} {Ω : Set (Subgroup G)}
    (hΩ : ∀ A ∈ Ω, ∀ t ∈ T, conjSub t A ∈ Ω) {t : G} (ht : t ∈ T) :
    conjSub t (genEi i T Ω) = genEi i T Ω := by
  have h := genEi_map_image (MulAut.conj t) i T Ω
  have hT : conjSub t T = T := conjSub_eq_iff_mem_normalizer.mpr (Subgroup.le_normalizer ht)
  have hΩt : conjSub t '' Ω = Ω := by
    ext B
    refine ⟨?_, fun hB => ⟨conjSub t⁻¹ B, hΩ B hB t⁻¹ (T.inv_mem ht), ?_⟩⟩
    · rintro ⟨C, hC, rfl⟩
      exact hΩ C hC t ht
    · rw [← conjSub_mul, mul_inv_cancel, conjSub_one]
  change genEi i (conjSub t T) (conjSub t '' Ω) = _ at h
  rw [hT, hΩt] at h
  exact h.symm

theorem le_normalizer_genEi [Finite G] (i : ℕ) {T : Subgroup G} {Ω : Set (Subgroup G)}
    (hΩ : ∀ A ∈ Ω, ∀ t ∈ T, conjSub t A ∈ Ω) :
    T ≤ Subgroup.normalizer (genEi i T Ω : Set G) := fun _ ht =>
  conjSub_eq_iff_mem_normalizer.mp (conjSub_genEi i hΩ ht)

theorem le_normalizer_genEi_of_isOmegaColl [Finite G] (i : ℕ) {T : Subgroup G}
    {Ω : Set (Subgroup G)} (hΩ : IsOmegaColl Ω) :
    T ≤ Subgroup.normalizer (genEi i T Ω : Set G) :=
  le_normalizer_genEi i fun A hA t _ => by
    have h1 := hΩ.conj A hA t⁻¹
    rwa [conjSubgroup_eq_conjSub, inv_inv] at h1

theorem inFOmega_iff_sup_eq_top [Finite G] (i : ℕ) {T : Subgroup G} {Ω : Set (Subgroup G)}
    (hΩ : IsOmegaColl Ω) : InFOmega i T Ω ↔ genEi i T Ω ⊔ T = ⊤ := by
  have hN : T ≤ Subgroup.normalizer (genEi i T Ω : Set G) :=
    le_normalizer_genEi_of_isOmegaColl i hΩ
  unfold InFOmega
  rw [← Subgroup.coe_mul_of_right_le_normalizer_left _ T hN]
  constructor
  · intro h
    exact SetLike.coe_injective (by rw [h, Subgroup.coe_top])
  · intro h
    rw [h, Subgroup.coe_top]

theorem iSup_inCalEi_le_genEi {i : ℕ} {T A : Subgroup G} {Ω : Set (Subgroup G)} (hAΩ : A ∈ Ω)
    (hAT : A ≤ T) : (⨆ J ∈ {J : Subgroup G | InCalEi i T A J}, J) ≤ genEi i T Ω :=
  le_iSup₂_of_le A hAΩ (le_iSup_of_le hAT le_rfl)

theorem le_genEi_of_inCalEi {i : ℕ} {T A K : Subgroup G} {Ω : Set (Subgroup G)} (hAΩ : A ∈ Ω)
    (hAT : A ≤ T) (hK : InCalEi i T A K) : K ≤ genEi i T Ω :=
  (le_iSup₂_of_le (f := fun J (_ : J ∈ {J : Subgroup G | InCalEi i T A J}) => J) K hK
    le_rfl).trans (iSup_inCalEi_le_genEi hAΩ hAT)

end CFSG.LocalAnalysis.WeakClosure81

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.Open Subgroup

theorem IsOmegaColl.exists_mem_le {G : Type} [Group G] [Finite G] {T : Subgroup G}
    (hT : CFSG.Quasithin.IsSylowIn 2 T ⊤) {Ω : Set (Subgroup G)} (hΩ : IsOmegaColl Ω) :
    ∃ A ∈ Ω, A ≤ T := by
  obtain ⟨B, hB⟩ := hΩ.nonempty
  have hB2 : IsPGroup 2 B := IsElemAbelian.isPGroup (hΩ.elemAbelian B hB)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, hBS⟩ := hB2.exists_le_sylow
  have hS : CFSG.Quasithin.IsSylowIn 2 (S : Subgroup G) ⊤ := isSylowIn_top S
  obtain ⟨g, -, hg⟩ := B6.isSylowTwoOf_exists_conj hS hT
  refine ⟨conjSub g B, ?_, ?_⟩
  · have h1 := hΩ.conj B hB g⁻¹
    rwa [conjSubgroup_eq_conjSub, inv_inv] at h1
  · rw [hg]
    exact conjSub_mono g hBS

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
