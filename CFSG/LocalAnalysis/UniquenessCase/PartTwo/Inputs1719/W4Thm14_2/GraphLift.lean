module

public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutPowerMap
public import CFSG.Quasithin.Background.L34OutFacts
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.MaxParabolicConj

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_2

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.ComponentInitial CFSG.QuasithinUnique.Setup
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.ComponentClassification.CatalogueBHigherLinearAction
  CFSG.ComponentClassification.CatalogueBHigherLinearField
  CFSG.ComponentClassification.CatalogueBGraphForm
open CFSG.Blueprint (LieModel)
open Matrix Module
open scoped MatrixGroups Matrix

namespace GraphLiftAux

private theorem map_normalizerMonoidHom_map_subtype {G : Type} [Group G] {L : Subgroup G}
    {x : G} (hx : x ∈ Subgroup.normalizer (L : Set G)) {P : Subgroup G} (hP : P ≤ L) :
    ((P.subgroupOf L).map (L.normalizerMonoidHom ⟨x, hx⟩).toMonoidHom).map L.subtype =
      P.map (MulAut.conj x).toMonoidHom := by
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    obtain ⟨p, hp, rfl⟩ := hz
    refine Subgroup.mem_map.mpr ⟨(p : G), hp, ?_⟩
    exact (Subgroup.normalizerMonoidHom_apply_apply_coe L ⟨x, hx⟩ p).symm
  · rintro ⟨p, hp, rfl⟩
    refine Subgroup.mem_map.mpr
      ⟨(L.normalizerMonoidHom ⟨x, hx⟩) ⟨p, hP hp⟩,
        Subgroup.mem_map.mpr
          ⟨⟨p, hP hp⟩, Subgroup.mem_subgroupOf.mpr hp, rfl⟩, ?_⟩
    exact Subgroup.normalizerMonoidHom_apply_apply_coe L ⟨x, hx⟩ ⟨p, hP hp⟩

private theorem isGraphType_slConjugation_mul {K : Type} [Field K]
    {ν : MulAut SL(3, K)} (hν : L34Out.IsGraphType ν)
    (g : GL (Fin 3) K) :
    L34Out.IsGraphType
      (slConjugation 3 K g * ν) := by
  obtain ⟨A, σ, hA⟩ := hν
  refine ⟨g * A, σ, ?_⟩
  rw [hA, map_mul (slConjugation 3 K) g A]
  group

private theorem slConjugation_toGL_apply_three {K : Type} [Field K] (g h : SL(3, K)) :
    slConjugation 3 K
      (SpecialLinearGroup.toGL g) h = g * h * g⁻¹ := by
  apply SpecialLinearGroup.toGL_injective
  rw [CFSG.ComponentClassification.CatalogueBHigherLinearAction.toGL_slConjugation]
  simp [map_mul, map_inv]

private theorem semilinear_map_stabilizer {K : Type} [Field K] [Finite K] [CharP K 2]
    {ν : MulAut SL(3, K)} {A : GL (Fin 3) K} {σ : K ≃+* K}
    (hν : ν = slConjugation 3 K A *
      slFieldAut (Fin 3) K σ)
    (hνU : ∀ s, s ∈ unitriangular 3 K ↔ ν s ∈ unitriangular 3 K)
    {d : ℕ} (hd : 1 ≤ d) (hdn : d < 3) :
    (stabilizer (flagSpace 3 K d)).map ν.toMonoidHom = stabilizer (flagSpace 3 K d) := by
  classical
  set W : Submodule K (Fin 3 → K) :=
    (LinearFlag.coordImage σ (flagSpace 3 K d)).map
      (mulVecLin (A : Matrix (Fin 3) (Fin 3) K)) with hW
  have hmap : (stabilizer (flagSpace 3 K d)).map ν.toMonoidHom = stabilizer W := by
    rw [hν]
    rw [show ((slConjugation 3 K A *
        slFieldAut (Fin 3) K σ :
          MulAut SL(3, K)).toMonoidHom) =
        (slConjugation 3 K A).toMonoidHom.comp
          (slFieldAut (Fin 3) K σ).toMonoidHom
        from rfl]
    rw [← Subgroup.map_map]
    exact (congrArg (Subgroup.map
      (MulEquiv.toMonoidHom (slConjugation
        3 K A))) (map_stabilizer_slFieldAut σ (flagSpace 3 K d))).trans
      (map_stabilizer_slConjugation A (LinearFlag.coordImage σ (flagSpace 3 K d)))
  have hUmap : (unitriangular 3 K).map ν.toMonoidHom = unitriangular 3 K := by
    ext s
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact (hνU u).mp hu
    · intro hs
      exact ⟨ν.symm s, (hνU (ν.symm s)).mpr (by simpa using hs), by simp⟩
  have hBmap : (upperTriangular 3 K).map ν.toMonoidHom = upperTriangular 3 K := by
    rw [← normalizer_unitriangular (n := 3) (K := K),
      Subgroup.map_equiv_normalizer_eq, hUmap, normalizer_unitriangular]
  have hUT : upperTriangular 3 K ≤ stabilizer W := by
    calc upperTriangular 3 K = (upperTriangular 3 K).map ν.toMonoidHom := hBmap.symm
      _ ≤ (stabilizer (flagSpace 3 K d)).map ν.toMonoidHom :=
            Subgroup.map_mono (upperTriangular_le_stabilizer_flagSpace d)
      _ = stabilizer W := hmap
  have hinv : ∀ u ∈ unitriangular 3 K, ∀ v ∈ W,
      (u : Matrix (Fin 3) (Fin 3) K) *ᵥ v ∈ W := by
    intro u hu v hv
    have huB : u ∈ stabilizer W := hUT (unitriangular_le_upperTriangular 3 K hu)
    have h := mem_stabilizer.mp huB
    rw [← h]
    exact Submodule.mem_map_of_mem hv
  obtain ⟨m, hm, hWm⟩ := eq_flagSpace_of_invariant (K := K) (n := 3) hinv
  have hdim : finrank K W = d := by
    rw [hW, CFSG.Quasithin.H13.NQCat.L34Aut.finrank_map_mulVecLin_gl,
      CFSG.Quasithin.H13.NQCat.L34Aut.finrank_coordImage, finrank_flagSpace (by omega)]
  have hmd : m = d := by
    rw [hWm, finrank_flagSpace hm] at hdim
    exact hdim
  rw [hWm, hmd] at hmap
  exact hmap

private theorem eq_flagStabilizer_of_isMaxParabolicOver {G : Type} [Group G] [Finite G]
    {L S P : Subgroup G} {K : Type} [Field K] [Finite K] [CharP K 2]
    (α : SL(3, K) →* ↥L) (hα : Function.Surjective α)
    (hαc : α.ker ≤ scalars 3 K)
    (hS : S = (unitriangular 3 K).map (L.subtype.comp α))
    (hP : S17.IsMaxParabolicOver L S P) :
    P = (stabilizer (flagSpace 3 K 1)).map (L.subtype.comp α) ∨
      P = (stabilizer (flagSpace 3 K 2)).map (L.subtype.comp α) := by
  classical
  let β : SL(3, K) →* G := L.subtype.comp α
  let R : Subgroup (SL(3, K)) := (P.subgroupOf L).comap α
  have hRmap : R.map α = P.subgroupOf L :=
    Subgroup.map_comap_eq_self_of_surjective hα _
  have hSL : S ≤ L := by
    rw [hS, ← Subgroup.map_map]
    exact Subgroup.map_subtype_le _
  have hSP : S ≤ P := (le_inf hSL (Subgroup.le_normalizer)).trans hP.2.1
  have hUR : unitriangular 3 K ≤ R := by
    intro u hu
    rw [Subgroup.mem_comap]
    have huS : β u ∈ S := by
      rw [hS]
      exact Subgroup.mem_map_of_mem β hu
    exact hSP huS
  have hBR : upperTriangular 3 K ≤ R := by
    intro b hb
    rw [Subgroup.mem_comap]
    have hbN : b ∈ Subgroup.normalizer (unitriangular 3 K : Set (SL(3, K))) := by
      rw [normalizer_unitriangular (n := 3) (K := K)]
      exact hb
    have hbmap : β b ∈ Subgroup.normalizer (S : Set G) := by
      have h := Subgroup.le_normalizer_map (H := unitriangular 3 K) β
        (Subgroup.mem_map_of_mem β hbN)
      rwa [← hS] at h
    exact hP.2.1 ⟨(α b).2, hbmap⟩
  have hRborel : R = flagStabilizer 3 K (borelOvergroupCuts R) :=
    (borel_overgroups R hBR).1
  have hPmap : P = (flagStabilizer 3 K (borelOvergroupCuts R)).map β := by
    calc P = (P.subgroupOf L).map L.subtype :=
          (Subgroup.map_subgroupOf_eq_of_le hP.1).symm
      _ = (R.map α).map L.subtype := by rw [hRmap]
      _ = R.map β := by rw [Subgroup.map_map]
      _ = (flagStabilizer 3 K (borelOvergroupCuts R)).map β := by
            nth_rewrite 1 [hRborel]
            rfl
  set I := borelOvergroupCuts R with hI
  have hIcuts : ∀ i ∈ I, i = 1 ∨ i = 2 := by
    intro i hi
    rw [hI] at hi
    obtain ⟨hi1, hi2, -⟩ := hi
    omega
  by_cases h1 : 1 ∈ I
  · by_cases h2 : 2 ∈ I
    · exfalso
      have hRle1 : R ≤ stabilizer (flagSpace 3 K 1) := by
        intro g hg
        rw [hRborel] at hg
        exact (mem_flagStabilizer.mp hg) 1 h1
      have hRne1 : R ≠ stabilizer (flagSpace 3 K 1) := by
        intro heq
        have hr2Q : reflection 3 K 2 (by norm_num) (by norm_num) ∈
            stabilizer (flagSpace 3 K 1) :=
          reflection_mem_stabilizer_of_ne (n := 3) (i := 1) (j := 2)
            (by norm_num) (by norm_num) (by norm_num)
        have hr2notR : reflection 3 K 2 (by norm_num) (by norm_num) ∉ R := by
          rw [hRborel]
          have hiff := (subflag_stabilizer_generation (K := K) (n := 3) I).2.2 2
            (by norm_num) (by norm_num)
          exact fun hmem => (hiff.mp hmem) h2
        exact hr2notR (heq.symm ▸ hr2Q)
      have hIle1 : flagStabilizer 3 K I ≤ stabilizer (flagSpace 3 K 1) := by
        intro g hg
        exact (mem_flagStabilizer.mp hg) 1 h1
      let Q1 : Subgroup G := (stabilizer (flagSpace 3 K 1)).map β
      have hPleQ1 : P ≤ Q1 := by
        rw [hPmap]
        exact Subgroup.map_mono hIle1
      have hPneQ1 : P ≠ Q1 := by
        intro hPeq
        apply hRne1
        have hPsub : P.subgroupOf L = (stabilizer (flagSpace 3 K 1)).map α := by
          apply Subgroup.map_injective L.subtype_injective
          rw [Subgroup.map_subgroupOf_eq_of_le hP.1, hPeq, Subgroup.map_map]
        change (P.subgroupOf L).comap α = stabilizer (flagSpace 3 K 1)
        rw [hPsub, Subgroup.comap_map_eq_self]
        exact hαc.trans (scalars_le_stabilizer _)
      have hQ1leL : Q1 ≤ L := by
        rw [show Q1 = ((stabilizer (flagSpace 3 K 1)).map α).map L.subtype from by
          rw [Subgroup.map_map]]
        exact Subgroup.map_subtype_le _
      have hQ1neL : Q1 ≠ L := by
        intro hQL
        have hQ1Lne : (stabilizer (flagSpace 3 K 1)).map α ≠ ⊤ :=
          (isMaxParabolicOver_image_stabilizer α hα hαc (d := 1)
            (by norm_num) (by norm_num)).2.2.1
        apply hQ1Lne
        apply Subgroup.map_injective L.subtype_injective
        have hQ1eq : Q1 = ((stabilizer (flagSpace 3 K 1)).map α).map L.subtype := by
          rw [show Q1 = (stabilizer (flagSpace 3 K 1)).map β from rfl, Subgroup.map_map]
        rw [← hQ1eq, hQL, Subgroup.map_top, Subgroup.range_subtype]
      rcases hP.2.2.2 Q1 hPleQ1 hQ1leL with h | h
      · exact hPneQ1 h.symm
      · exact hQ1neL h
    · have hIeq : I = {1} := by
        ext i
        constructor
        · intro hi
          rcases hIcuts i hi with rfl | rfl
          · simp
          · exact absurd hi h2
        · intro hi
          rw [Set.mem_singleton_iff] at hi
          subst i
          exact h1
      left
      rw [hPmap, hIeq, flagStabilizer_singleton]
  · by_cases h2 : 2 ∈ I
    · have hIeq : I = {2} := by
        ext i
        constructor
        · intro hi
          rcases hIcuts i hi with rfl | rfl
          · exact absurd hi h1
          · simp
        · intro hi
          rw [Set.mem_singleton_iff] at hi
          subst i
          exact h2
      right
      rw [hPmap, hIeq, flagStabilizer_singleton]
    · exfalso
      have hIeq : I = ∅ := by
        ext i
        constructor
        · intro hi
          rcases hIcuts i hi with rfl | rfl
          · exact absurd hi h1
          · exact absurd hi h2
        · intro hi
          exact absurd hi (by simp)
      have hRtop : R = ⊤ := by rw [hRborel, hIeq, flagStabilizer_empty]
      have hβrange : β.range = L := by
        rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr hα, Subgroup.map_top,
          Subgroup.range_subtype]
      have hPtop : P = L := by
        rw [hPmap, hIeq, flagStabilizer_empty, Subgroup.map_top, hβrange]
      exact hP.2.2.1 hPtop

end GraphLiftAux

open GraphLiftAux

theorem exists_graphType_of_moves
    {G : Type} [Group G] [Finite G] {L S P : Subgroup G}
    {K : Type} [Field K] [Finite K] [CharP K 2] (α : SL(3, K) →* ↥L)
    (hα : Function.Surjective α) (hαc : α.ker ≤ LinearFlag.scalars 3 K)
    (hodd : Odd (Nat.card α.ker)) (hS : IsSylowIn 2 S L) {x : G}
    (hxL : x ∈ Subgroup.normalizer (L : Set G)) (hxS : x ∈ Subgroup.normalizer (S : Set G))
    (hP : S17.IsMaxParabolicOver L S P) (hmove : P.map (MulAut.conj x).toMonoidHom ≠ P) :
    ∃ ν : MulAut SL(3, K), (∀ s, ((α (ν s) : ↥L) : G) = x * (α s : G) * x⁻¹) ∧
      L34Out.IsGraphType ν := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let β : SL(3, K) →* G := L.subtype.comp α
  obtain ⟨Q, hQ⟩ := exists_sylow_unitriangular (K := K) 2 (n := 3) (by norm_num)
  let Q' : Sylow 2 ↥L := Q.mapSurjective hα
  have hQ'coe : (Q' : Subgroup ↥L) = (unitriangular 3 K).map α := by
    rw [Sylow.coe_mapSurjective, hQ]
  have hA : IsSylowIn 2 ((unitriangular 3 K).map α) (⊤ : Subgroup ↥L) := by
    refine ⟨le_top, ?_, ?_⟩
    · exact hQ ▸ Q.isPGroup'.map α
    · rw [Subgroup.relIndex_top_right, ← hQ'coe]
      exact Q'.not_dvd_index
  have hSαG : IsSylowIn 2 ((unitriangular 3 K).map β) L := by
    have h := (CFSG.Quasithin.E1.isSylowIn_map_of_injective
      (f := L.subtype) L.subtype_injective (P := (unitriangular 3 K).map α)
      (H := (⊤ : Subgroup ↥L))).mpr hA
    simpa [β, Subgroup.map_map, Subgroup.map_top, Subgroup.range_subtype] using h
  obtain ⟨l, hlL, hlconj⟩ := CFSG.Quasithin.Ch1Sec3.exists_conj_of_isSylowIn hS hSαG
  have hl : (unitriangular 3 K).map β = S.map (MulAut.conj l).toMonoidHom := by
    ext y
    rw [hlconj y, Subgroup.mem_map]
    constructor
    · intro hy
      exact ⟨l⁻¹ * y * l, hy, by simp [MulAut.conj_apply, mul_assoc]⟩
    · rintro ⟨s, hs, rfl⟩
      simpa [mul_assoc] using hs
  set x' : G := l * x * l⁻¹ with hx'def
  have hx'L : x' ∈ Subgroup.normalizer (L : Set G) := by
    have hlN : l ∈ Subgroup.normalizer (L : Set G) := Subgroup.le_normalizer hlL
    exact (Subgroup.normalizer (L : Set G)).mul_mem
      ((Subgroup.normalizer (L : Set G)).mul_mem hlN hxL)
      ((Subgroup.normalizer (L : Set G)).inv_mem hlN)
  have hx'Sα : x' ∈ Subgroup.normalizer ((unitriangular 3 K).map β : Set G) := by
    have h := Subgroup.mem_map_of_mem (MulAut.conj l).toMonoidHom hxS
    rw [Subgroup.map_equiv_normalizer_eq] at h
    rw [← hl] at h
    simpa [x', MulAut.conj_apply, mul_assoc] using h
  let θ' : MulAut ↥L := L.normalizerMonoidHom ⟨x', hx'L⟩
  have hAeq : ((unitriangular 3 K).map α).map L.subtype = (unitriangular 3 K).map β := by
    rw [Subgroup.map_map]
  have hθ'A : ∀ s : ↥L, s ∈ (unitriangular 3 K).map α ↔
      θ' s ∈ (unitriangular 3 K).map α := by
    intro s
    have h1 : s ∈ (unitriangular 3 K).map α ↔
        (s : G) ∈ ((unitriangular 3 K).map α).map L.subtype :=
      (Subgroup.mem_map_iff_mem (f := L.subtype) L.subtype_injective).symm
    have h2 : θ' s ∈ (unitriangular 3 K).map α ↔
        (θ' s : G) ∈ ((unitriangular 3 K).map α).map L.subtype :=
      (Subgroup.mem_map_iff_mem (f := L.subtype) L.subtype_injective).symm
    rw [h1, h2, hAeq, Subgroup.normalizerMonoidHom_apply_apply_coe]
    exact Subgroup.mem_normalizer_iff.mp hx'Sα (s : G)
  obtain ⟨ν', hν'α, hν'U⟩ := exists_lift_sl3_of_odd_cover α hα hαc hodd θ' hθ'A
  obtain ⟨Amat, σ, ε, hε, hν'⟩ :=
    CFSG.RankThree.PartOne.AUTSL.exists_eq_std_of_mulAut_sl (K := K) (n := 3)
      (by norm_num) ν'
  have hP' : S17.IsMaxParabolicOver L ((unitriangular 3 K).map β)
      (P.map (MulAut.conj l).toMonoidHom) := by
    have h := S17.isMaxParabolicOver_map_conj (g := l) hP
    rw [CFSG.Quasithin.Ch1Sec3.map_conj_eq_of_mem_normalizer
      (Subgroup.le_normalizer hlL)] at h
    rwa [← hl] at h
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hε with hε0 | hε1
  · exfalso
    have hν'0 : ν' = slConjugation
        3 K Amat * slFieldAut
          (Fin 3) K σ := by
      rw [hν', hε0, pow_zero, mul_one]
    have hfixd : ∀ d, 1 ≤ d → d < 3 →
        (stabilizer (flagSpace 3 K d)).map ν'.toMonoidHom =
          stabilizer (flagSpace 3 K d) :=
      fun d hd hdn => semilinear_map_stabilizer hν'0 hν'U hd hdn
    have hfixQ : ∀ d, 1 ≤ d → d < 3 →
        ((stabilizer (flagSpace 3 K d)).map α).map θ'.toMonoidHom =
          (stabilizer (flagSpace 3 K d)).map α := by
      intro d hd hdn
      rw [Subgroup.map_map]
      have hcomp : θ'.toMonoidHom.comp α = α.comp ν'.toMonoidHom :=
        (MonoidHom.ext hν'α).symm
      rw [hcomp, ← Subgroup.map_map, hfixd d hd hdn]
    have hP'eq := eq_flagStabilizer_of_isMaxParabolicOver α hα hαc
      (S := (unitriangular 3 K).map β) (P := P.map (MulAut.conj l).toMonoidHom) rfl hP'
    have hfixP' : (P.map (MulAut.conj l).toMonoidHom).map
        (MulAut.conj x').toMonoidHom = P.map (MulAut.conj l).toMonoidHom := by
      have hkey : ∀ d, 1 ≤ d → d < 3 →
          (P.map (MulAut.conj l).toMonoidHom).subgroupOf L =
            (stabilizer (flagSpace 3 K d)).map α →
          (P.map (MulAut.conj l).toMonoidHom).map (MulAut.conj x').toMonoidHom =
            P.map (MulAut.conj l).toMonoidHom := by
        intro d hd hdn hdsub
        calc
          (P.map (MulAut.conj l).toMonoidHom).map (MulAut.conj x').toMonoidHom
              = (((P.map (MulAut.conj l).toMonoidHom).subgroupOf L).map
                  θ'.toMonoidHom).map L.subtype :=
                (map_normalizerMonoidHom_map_subtype hx'L hP'.1).symm
          _ = (((stabilizer (flagSpace 3 K d)).map α).map θ'.toMonoidHom).map
                L.subtype := by rw [hdsub]
          _ = ((stabilizer (flagSpace 3 K d)).map α).map L.subtype := by
                rw [hfixQ d hd hdn]
          _ = (stabilizer (flagSpace 3 K d)).map β := by
                rw [Subgroup.map_map]
          _ = P.map (MulAut.conj l).toMonoidHom := by
                rw [← Subgroup.map_subgroupOf_eq_of_le hP'.1, hdsub,
                  ← Subgroup.map_map]
      rcases hP'eq with h | h
      · have hsub1 : (P.map (MulAut.conj l).toMonoidHom).subgroupOf L =
            (stabilizer (flagSpace 3 K 1)).map α := by
          apply Subgroup.map_injective L.subtype_injective
          rw [Subgroup.map_subgroupOf_eq_of_le hP'.1, h]
          exact show ((stabilizer (flagSpace 3 K 1)).map β) =
            ((stabilizer (flagSpace 3 K 1)).map α).map L.subtype by
              rw [Subgroup.map_map]
        exact hkey 1 (by norm_num) (by norm_num) hsub1
      · have hsub1 : (P.map (MulAut.conj l).toMonoidHom).subgroupOf L =
            (stabilizer (flagSpace 3 K 2)).map α := by
          apply Subgroup.map_injective L.subtype_injective
          rw [Subgroup.map_subgroupOf_eq_of_le hP'.1, h]
          exact show ((stabilizer (flagSpace 3 K 2)).map β) =
            ((stabilizer (flagSpace 3 K 2)).map α).map L.subtype by
              rw [Subgroup.map_map]
        exact hkey 2 (by norm_num) (by norm_num) hsub1
    have hcomp : (P.map (MulAut.conj l).toMonoidHom).map
        (MulAut.conj x').toMonoidHom =
        (P.map (MulAut.conj x).toMonoidHom).map (MulAut.conj l).toMonoidHom := by
      rw [Subgroup.map_map, Subgroup.map_map]
      congr 1
      ext p
      change (l * x * l⁻¹) * (l * p * l⁻¹) * (l * x * l⁻¹)⁻¹ =
        l * (x * p * x⁻¹) * l⁻¹
      group
    have hmoveeq : P.map (MulAut.conj x).toMonoidHom = P := by
      apply Subgroup.map_injective (f := (MulAut.conj l).toMonoidHom) (MulAut.conj l).injective
      rw [← hcomp, hfixP']
    exact hmove hmoveeq
  · have hgraph : L34Out.IsGraphType ν' := by
      rw [hν', hε1, pow_one]
      exact ⟨Amat, σ, rfl⟩
    have hβall : ∀ u : SL(3, K), β (ν' u) = x' * β u * x'⁻¹ := by
      intro u
      have h := congrArg L.subtype (hν'α u)
      simpa [β, θ', Subgroup.normalizerMonoidHom_apply_apply_coe] using h
    obtain ⟨h, hh⟩ := hα (⟨l, hlL⟩ : ↥L)
    have hhG : β h = l := by simpa [β] using congrArg L.subtype hh
    have hconj : slConjugation 3 K (SpecialLinearGroup.toGL h) = MulAut.conj h := by
      apply MulEquiv.ext
      intro x
      rw [MulAut.conj_apply]
      exact slConjugation_toGL_apply_three h x
    have hright : ν' * slConjugation 3 K (SpecialLinearGroup.toGL h) * ν'⁻¹ =
        slConjugation 3 K (SpecialLinearGroup.toGL (ν' h)) := by
      rw [hconj]
      apply MulEquiv.ext
      intro x
      rw [slConjugation_toGL_apply_three]
      simp [MulAut.mul_apply, MulAut.conj_apply]
    have hreassoc : slConjugation 3 K (SpecialLinearGroup.toGL h⁻¹) * ν' *
        slConjugation 3 K (SpecialLinearGroup.toGL h) =
        slConjugation 3 K (SpecialLinearGroup.toGL (h⁻¹ * ν' h)) * ν' := by
      calc slConjugation 3 K (SpecialLinearGroup.toGL h⁻¹) * ν' *
            slConjugation 3 K (SpecialLinearGroup.toGL h)
          = slConjugation 3 K (SpecialLinearGroup.toGL h⁻¹) *
              (ν' * slConjugation 3 K (SpecialLinearGroup.toGL h) * ν'⁻¹) * ν' := by
                group
        _ = slConjugation 3 K (SpecialLinearGroup.toGL h⁻¹) *
              slConjugation 3 K (SpecialLinearGroup.toGL (ν' h)) * ν' := by rw [hright]
        _ = slConjugation 3 K (SpecialLinearGroup.toGL (h⁻¹ * ν' h)) * ν' := by
              rw [map_mul (SpecialLinearGroup.toGL), map_mul (slConjugation 3 K)]
    refine ⟨slConjugation 3 K (SpecialLinearGroup.toGL h⁻¹) * ν' *
        slConjugation 3 K (SpecialLinearGroup.toGL h), ?_, ?_⟩
    · intro s
      have hhInv : β h⁻¹ = l⁻¹ := by rw [map_inv, hhG]
      have h1 : (slConjugation 3 K (SpecialLinearGroup.toGL h⁻¹) * ν' *
          slConjugation 3 K (SpecialLinearGroup.toGL h)) s =
          slConjugation 3 K (SpecialLinearGroup.toGL h⁻¹) (ν' (h * s * h⁻¹)) := by
        rw [MulAut.mul_apply, MulAut.mul_apply]
        rw [show (slConjugation 3 K (SpecialLinearGroup.toGL h)) s = h * s * h⁻¹ from
          slConjugation_toGL_apply_three h s]
      have h3 : β (slConjugation 3 K (SpecialLinearGroup.toGL h⁻¹) (ν' (h * s * h⁻¹))) =
          β h⁻¹ * β (ν' (h * s * h⁻¹)) * β h := by
        rw [slConjugation_toGL_apply_three, map_mul, map_mul, inv_inv]
      have h5 : β (h * s * h⁻¹) = l * β s * l⁻¹ := by
        rw [map_mul, map_mul, map_inv, hhG]
      have hβeq2 : β ((slConjugation 3 K (SpecialLinearGroup.toGL h⁻¹) * ν' *
          slConjugation 3 K (SpecialLinearGroup.toGL h)) s) = x * β s * x⁻¹ := by
        calc β ((slConjugation 3 K (SpecialLinearGroup.toGL h⁻¹) * ν' *
              slConjugation 3 K (SpecialLinearGroup.toGL h)) s)
            = β (slConjugation 3 K (SpecialLinearGroup.toGL h⁻¹)
                (ν' (h * s * h⁻¹))) := by rw [h1]
          _ = β h⁻¹ * β (ν' (h * s * h⁻¹)) * β h := h3
          _ = l⁻¹ * (x' * (l * β s * l⁻¹) * x'⁻¹) * l := by
                rw [hβall, h5, hhInv, hhG]
          _ = x * β s * x⁻¹ := by
                simp only [hx'def]
                group
      exact hβeq2
    · rw [hreassoc]
      rw [map_mul]
      exact isGraphType_slConjugation_mul hgraph
        (SpecialLinearGroup.toGL h⁻¹ * SpecialLinearGroup.toGL (ν' h))

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_2
