module

public import CFSG.RankThree.PartTwo.Sec19.Item1923Defs
import CFSG.RankThree.PartTwo.Sec18.Item189StepInspectIL3EvenTools

public section

namespace CFSG.RankThree.PartTwo.Late

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open Matrix
open CFSG.Assembly.RankThreeEven (projSL)

section Model

variable {F : Type} [Field F]

theorem kfl3_stab_inj [Finite F] [CharP F 2] {W U : Submodule F (Fin 3 → F)}
    (hW : ⊥ < W ∧ W < ⊤) (hU : ⊥ < U ∧ U < ⊤) (h : projStabilizer W = projStabilizer U) :
    W = U := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hinj, -⟩ := maximal_parabolics (K := F) (n := 3) 2 (by norm_num)
  exact hinj hW hU h

theorem kfl3_stab_of_isMax [Finite F] [CharP F 2] {Q : Subgroup (projectiveSL 3 F)}
    (hQ : Sec18.IsMaxParabolicRankTwo Q) :
    ∃ W : Submodule F (Fin 3 → F), (⊥ < W ∧ W < ⊤) ∧ projStabilizer W = Q := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hc, T, hT⟩ := hQ
  have hmem : Q ∈ maximalParabolics (projectiveSL 3 F) 2 := ⟨hc, _, ⟨T, rfl⟩, hT⟩
  obtain ⟨hMP, -, -⟩ := maximal_parabolics (K := F) (n := 3) 2 (by norm_num)
  rw [hMP] at hmem
  obtain ⟨W, hW, hWQ⟩ := hmem
  exact ⟨W, hW, hWQ⟩

theorem kfl3_stab_of_isMax_map [Finite F] [CharP F 2] {X : Type} [Group X] [Finite X]
    (e : X ≃* projectiveSL 3 F) {P : Subgroup X} (hP : Sec18.IsMaxParabolicRankTwo P) :
    ∃ W : Submodule F (Fin 3 → F), (⊥ < W ∧ W < ⊤) ∧ P.map e.toMonoidHom = projStabilizer W := by
  obtain ⟨W, hW, h⟩ := kfl3_stab_of_isMax (Sec20.Res7.isMaxParabolicRankTwo_map e hP)
  exact ⟨W, hW, h.symm⟩

theorem kfl3_tr_conj (A : GL (Fin 3) F) (W : Submodule F (Fin 3 → F)) :
    (projStabilizer W).map (conjAut 3 F A : projectiveSL 3 F →* projectiveSL 3 F) =
      projStabilizer (W.map (mulVecLin (A : Matrix (Fin 3) (Fin 3) F))) := by
  obtain ⟨-, -, -, -, -, -, h, -, -, -⟩ := standard_automorphism_transport (K := F) (n := 3)
  exact h A W

theorem kfl3_tr_field (σ : F ≃+* F) (W : Submodule F (Fin 3 → F)) :
    (projStabilizer W).map (fieldAut 3 F σ : projectiveSL 3 F →* projectiveSL 3 F) =
      projStabilizer (coordImage σ W) := by
  obtain ⟨-, -, -, -, -, -, -, h, -, -⟩ := standard_automorphism_transport (K := F) (n := 3)
  exact h σ W

theorem kfl3_tr_dual (W : Submodule F (Fin 3 → F)) :
    (projStabilizer W).map (dualAut 3 F : projectiveSL 3 F →* projectiveSL 3 F) =
      projStabilizer (dotOrth W) := by
  obtain ⟨-, -, -, -, -, -, -, -, h, -⟩ := standard_automorphism_transport (K := F) (n := 3)
  exact h W

theorem kfl3_finrank_map (A : GL (Fin 3) F) (W : Submodule F (Fin 3 → F)) :
    Module.finrank F (W.map (mulVecLin (A : Matrix (Fin 3) (Fin 3) F))) =
      Module.finrank F W :=
  Sec20.Res7.finrank_map_gl A W

theorem kfl3_finrank_eq {W U : Submodule F (Fin 3 → F)} (h : W = U) :
    Module.finrank F W = Module.finrank F U := by
  rw [h]

theorem kfl3_proper_of_finrank {W : Submodule F (Fin 3 → F)}
    (h1 : 1 ≤ Module.finrank F W) (h2 : Module.finrank F W < 3) : ⊥ < W ∧ W < ⊤ :=
  (Sec20.Res7.bot_lt_lt_top_iff W).mpr ⟨h1, h2⟩

theorem kfl3_proper_map (A : GL (Fin 3) F) {W : Submodule F (Fin 3 → F)}
    (hW : ⊥ < W ∧ W < ⊤) :
    ⊥ < W.map (mulVecLin (A : Matrix (Fin 3) (Fin 3) F)) ∧
      W.map (mulVecLin (A : Matrix (Fin 3) (Fin 3) F)) < ⊤ := by
  obtain ⟨h1, h2⟩ := (Sec20.Res7.bot_lt_lt_top_iff W).mp hW
  exact kfl3_proper_of_finrank (by rw [kfl3_finrank_map]; exact h1)
    (by rw [kfl3_finrank_map]; exact h2)

theorem kfl3_map_flip (A : GL (Fin 3) F) (σ : F ≃+* F) (W : Submodule F (Fin 3 → F)) :
    (projStabilizer W).map
        ((conjAut 3 F A * fieldAut 3 F σ * dualAut 3 F : MulAut (projectiveSL 3 F)) :
          projectiveSL 3 F →* projectiveSL 3 F) =
      projStabilizer
        ((coordImage σ (dotOrth W)).map (mulVecLin (A : Matrix (Fin 3) (Fin 3) F))) := by
  rw [Sec20.Res7.map_mulAut_mul, Sec20.Res7.map_mulAut_mul, kfl3_tr_dual, kfl3_tr_field,
    kfl3_tr_conj]

theorem kfl3_finrank_flip (A : GL (Fin 3) F) (σ : F ≃+* F) (W : Submodule F (Fin 3 → F)) :
    Module.finrank F ((coordImage σ (dotOrth W)).map
        (mulVecLin (A : Matrix (Fin 3) (Fin 3) F))) = 3 - Module.finrank F W := by
  rw [kfl3_finrank_map, Sec20.Res7.finrank_coordImage, finrank_dotOrth]

theorem kfl3_flip_step (A : GL (Fin 3) F) (σ : F ≃+* F) {W : Submodule F (Fin 3 → F)}
    (hW : ⊥ < W ∧ W < ⊤) :
    ∃ U : Submodule F (Fin 3 → F), (⊥ < U ∧ U < ⊤) ∧
      Module.finrank F U = 3 - Module.finrank F W ∧
      (projStabilizer W).map
          ((conjAut 3 F A * fieldAut 3 F σ * dualAut 3 F : MulAut (projectiveSL 3 F)) :
            projectiveSL 3 F →* projectiveSL 3 F) = projStabilizer U := by
  obtain ⟨h1, h2⟩ := (Sec20.Res7.bot_lt_lt_top_iff W).mp hW
  refine ⟨(coordImage σ (dotOrth W)).map (mulVecLin (A : Matrix (Fin 3) (Fin 3) F)), ?_,
    kfl3_finrank_flip A σ W, kfl3_map_flip A σ W⟩
  exact kfl3_proper_of_finrank (by rw [kfl3_finrank_flip]; omega)
    (by rw [kfl3_finrank_flip]; omega)

theorem kfl3_stab_conj_proj (h₀ : Matrix.SpecialLinearGroup (Fin 3) F)
    (W : Submodule F (Fin 3 → F)) :
    (projStabilizer W).map (MulAut.conj (proj 3 F h₀)).toMonoidHom =
      projStabilizer (W.map (mulVecLin ((Matrix.SpecialLinearGroup.toGL h₀ : GL (Fin 3) F) :
        Matrix (Fin 3) (Fin 3) F))) := by
  rw [← conjAut_toGL]
  exact kfl3_tr_conj _ _

theorem kfl3_stab_conj_of_finrank {W U : Submodule F (Fin 3 → F)}
    (h : Module.finrank F W = Module.finrank F U) :
    ∃ y : projectiveSL 3 F,
      projStabilizer U = (projStabilizer W).map (MulAut.conj y).toMonoidHom := by
  obtain ⟨g, hg⟩ := exists_map_eq_of_finrank_eq (K := F) (n := 3) h
  refine ⟨proj 3 F g, ?_⟩
  rw [← hg, kfl3_stab_conj_proj] <;> rfl

end Model

section Transport

theorem kfl3_map_conj_map {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) (P : Subgroup X)
    (g : X) :
    (P.map (MulAut.conj g).toMonoidHom).map e.toMonoidHom =
      (P.map e.toMonoidHom).map (MulAut.conj (e g)).toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply]

theorem kfl3_map_congr {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) (α : MulAut X)
    (P : Subgroup X) :
    (P.map e.toMonoidHom).map (MulAut.congr e α : MulAut Y).toMonoidHom =
      (P.map α.toMonoidHom).map e.toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.congr_apply]

theorem kfl3_congr_back {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) (α : MulAut X) :
    MulAut.congr e.symm (MulAut.congr e α) = α := by
  ext x
  simp [MulAut.congr_apply]

theorem kfl3_mem_inner_congr {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) (α : MulAut X) :
    α ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner X ↔
      MulAut.congr e α ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner Y := by
  simp only [CFSG.ComponentClassification.OuterAutomorphisms.inner, MonoidHom.mem_range]
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨e x, (CFSG.ComponentClassification.OuterAutomorphisms.congr_conj e x).symm⟩
  · rintro ⟨y, hy⟩
    refine ⟨e.symm y, ?_⟩
    rw [← CFSG.ComponentClassification.OuterAutomorphisms.congr_conj e.symm y, hy,
      kfl3_congr_back]

theorem kfl3_conj_of_stab {X : Type} [Group X] [Finite X] {n : ℕ}
    (e : X ≃* projectiveSL 3 (GaloisField 2 n)) {P Q : Subgroup X}
    {W V : Submodule (GaloisField 2 n) (Fin 3 → GaloisField 2 n)}
    (hP : P.map e.toMonoidHom = projStabilizer W) (hQ : Q.map e.toMonoidHom = projStabilizer V)
    (h : Module.finrank (GaloisField 2 n) W = Module.finrank (GaloisField 2 n) V) :
    ∃ g : X, Q = P.map (MulAut.conj g).toMonoidHom := by
  obtain ⟨y, hy⟩ := kfl3_stab_conj_of_finrank h
  refine ⟨e.symm y, ?_⟩
  apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
  rw [kfl3_map_conj_map, MulEquiv.apply_symm_apply, hQ, hy, hP]

end Transport

section Index

theorem kfl3_gauss_one (m : ℕ) (hm : 1 < m) : gaussianCoeff 3 1 m = (m : ℚ) ^ 2 + m + 1 := by
  have h1 : (1 : ℚ) < m := by exact_mod_cast hm
  have h0 : (m : ℚ) - 1 ≠ 0 := by
    intro h
    linarith
  rw [gaussianCoeff, Finset.prod_range_one, div_eq_iff (by simpa using h0)]
  simp only [Nat.sub_zero, pow_one]
  ring

theorem kfl3_gauss_two (m : ℕ) (hm : 1 < m) : gaussianCoeff 3 2 m = (m : ℚ) ^ 2 + m + 1 := by
  have h1 : (1 : ℚ) < m := by exact_mod_cast hm
  have h0 : (m : ℚ) - 1 ≠ 0 := by
    intro h
    linarith
  have h2 : (m : ℚ) ^ 2 - 1 ≠ 0 := by
    intro h
    nlinarith
  rw [gaussianCoeff, Finset.prod_range_succ, Finset.prod_range_one]
  norm_num
  field_simp
  ring

theorem kfl3_index_stab {n : ℕ} (hn : Odd n)
    {W : Submodule (GaloisField 2 n) (Fin 3 → GaloisField 2 n)} (hW : ⊥ < W ∧ W < ⊤) :
    (projStabilizer W).index = (2 ^ n) ^ 2 + 2 ^ n + 1 := by
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact Nat.not_odd_zero hn
  have hq : Nat.card (GaloisField 2 n) = 2 ^ n := GaloisField.card 2 n hn0
  have hq1 : 1 < 2 ^ n := Nat.one_lt_two_pow hn0
  obtain ⟨h1, h2⟩ := (Sec20.Res7.bot_lt_lt_top_iff W).mp hW
  have hsub := (subspace_index (K := GaloisField 2 n) (n := 3)
    (k := Module.finrank (GaloisField 2 n) W) (by omega)).2 W rfl
  rw [hq] at hsub
  have key : ((projStabilizer W).index : ℚ) = (((2 ^ n) ^ 2 + 2 ^ n + 1 : ℕ) : ℚ) := by
    rcases (show Module.finrank (GaloisField 2 n) W = 1 ∨
        Module.finrank (GaloisField 2 n) W = 2 by omega) with h | h
    · rw [hsub, h, kfl3_gauss_one _ hq1]
      push_cast
      ring
    · rw [hsub, h, kfl3_gauss_two _ hq1]
      push_cast
      ring
  exact_mod_cast key

end Index

section Borel

theorem kfl3_isCoatom_upper {F : Type} [Field F] {P : Subgroup (projectiveSL 3 F)}
    (hP : P ≠ ⊤) (hBP : projUpperTriangular 3 F ≤ P) (hne : projUpperTriangular 3 F ≠ P) :
    IsCoatom P := by
  classical
  set A := P.comap (proj 3 F) with hA
  have hMA : A.map (proj 3 F) = P :=
    Subgroup.map_comap_eq_self_of_surjective (proj_surjective 3 F) P
  have hBA : upperTriangular 3 F ≤ A := by
    rw [hA, ← Subgroup.map_le_iff_le_comap]
    exact hBP
  obtain ⟨hAI, -⟩ := borel_overgroups A hBA
  set I := borelOvergroupCuts A with hI
  have hsub : I ⊆ {1, 2} := by
    rintro i ⟨hi, hin, -⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    omega
  by_cases h1 : 1 ∈ I <;> by_cases h2 : 2 ∈ I
  · exfalso
    have hI12 : I = {1, 2} := Set.Subset.antisymm hsub (by
      intro i hi
      rcases hi with rfl | rfl
      · exact h1
      · exact h2)
    have hAB : A ≤ upperTriangular 3 F := by
      rw [hAI, hI12, (subflag_stabilizer_generation (K := F) (n := 3) {1, 2}).1,
        Subgroup.closure_le]
      rintro g (hg | ⟨j, hj, hjn, hjI, rfl⟩)
      · exact hg
      · exfalso
        apply hjI
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
        omega
    apply hne
    rw [← hMA, projUpperTriangular, le_antisymm hAB hBA]
  · have hI1 : I = {1} := Set.Subset.antisymm (by
      intro i hi
      rcases hsub hi with rfl | rfl
      · rfl
      · exact absurd hi h2) (by
      intro i hi
      rw [Set.mem_singleton_iff.mp hi]
      exact h1)
    have : P = projStabilizer (flagSpace 3 F 1) := by
      rw [← hMA, hAI, hI1, flagStabilizer_singleton]
      rfl
    rw [this]
    exact isCoatom_projStabilizer_flagSpace (by norm_num) (by norm_num)
  · have hI2 : I = {2} := Set.Subset.antisymm (by
      intro i hi
      rcases hsub hi with rfl | rfl
      · exact absurd hi h1
      · rfl) (by
      intro i hi
      rw [Set.mem_singleton_iff.mp hi]
      exact h2)
    have : P = projStabilizer (flagSpace 3 F 2) := by
      rw [← hMA, hAI, hI2, flagStabilizer_singleton]
      rfl
    rw [this]
    exact isCoatom_projStabilizer_flagSpace (by norm_num) (by norm_num)
  · exfalso
    have hI0 : I = ∅ := Set.eq_empty_iff_forall_notMem.mpr (fun i hi => by
      rcases hsub hi with rfl | rfl
      · exact h1 hi
      · exact h2 hi)
    apply hP
    rw [← hMA, hAI, hI0, flagStabilizer_empty, Subgroup.map_top_of_surjective _
      (proj_surjective 3 F)]

theorem kfl3_isCoatom_borel_model {F : Type} [Field F] [Finite F] [CharP F 2]
    {P : Subgroup (projectiveSL 3 F)} (hP : P ≠ ⊤) (T : Sylow 2 (projectiveSL 3 F))
    (hTP : Subgroup.normalizer ((T : Subgroup (projectiveSL 3 F)) : Set (projectiveSL 3 F)) ≤ P)
    (hne : Subgroup.normalizer ((T : Subgroup (projectiveSL 3 F)) : Set (projectiveSL 3 F)) ≠ P) :
    IsCoatom P := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hmem : Subgroup.normalizer ((T : Subgroup (projectiveSL 3 F)) : Set (projectiveSL 3 F)) ∈
      sylowNormalizers (projectiveSL 3 F) 2 := ⟨T, rfl⟩
  rw [sylowNormalizers_eq (K := F) 2 (by norm_num)] at hmem
  obtain ⟨x, hx⟩ := hmem
  set Φ := MulEquiv.mapSubgroup (MulAut.conj x⁻¹ : projectiveSL 3 F ≃* projectiveSL 3 F) with hΦ
  have hΦB : Φ (Subgroup.normalizer ((T : Subgroup (projectiveSL 3 F)) : Set (projectiveSL 3 F))) =
      projUpperTriangular 3 F := by
    rw [hx]
    show ((projUpperTriangular 3 F).map (MulAut.conj x : projectiveSL 3 F →* projectiveSL 3 F)).map
      (MulAut.conj x⁻¹ : projectiveSL 3 F →* projectiveSL 3 F) = projUpperTriangular 3 F
    rw [Subgroup.map_map]
    have : (MulAut.conj x⁻¹ : projectiveSL 3 F →* projectiveSL 3 F).comp
        (MulAut.conj x : projectiveSL 3 F →* projectiveSL 3 F) = MonoidHom.id _ := by
      ext g
      simp [MulAut.conj_apply, mul_assoc]
    rw [this, Subgroup.map_id]
  rw [← OrderIso.isCoatom_iff Φ P]
  refine kfl3_isCoatom_upper ?_ ?_ ?_
  · intro h
    exact hP (Φ.injective (h.trans Φ.map_top.symm))
  · rw [← hΦB]
    exact Φ.monotone hTP
  · rw [← hΦB]
    exact fun h => hne (Φ.injective h)

theorem kfl3_isCoatom_borel {X : Type} [Group X] [Finite X] {n : ℕ} (hn : Odd n)
    (e₀ : X ≃* projSL 3 (GaloisField 2 n)) (S : Sylow 2 X) {P : Subgroup X} (hP : P ≠ ⊤)
    (hSP : Subgroup.normalizer ((S : Subgroup X) : Set X) ≤ P)
    (hne : Subgroup.normalizer ((S : Subgroup X) : Set X) ≠ P) : IsCoatom P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let e' : X ≃* projectiveSL 3 (GaloisField 2 n) :=
    e₀.trans (KFacts.L34.projSLEquivProjectiveSL 3 (GaloisField 2 n))
  have hs : Function.Surjective e'.toMonoidHom := e'.surjective
  set Ψ := MulEquiv.mapSubgroup e' with hΨ
  have hN : Subgroup.normalizer
      (((S.mapSurjective hs : Sylow 2 (projectiveSL 3 (GaloisField 2 n))) :
        Subgroup (projectiveSL 3 (GaloisField 2 n))) : Set (projectiveSL 3 (GaloisField 2 n))) =
      Ψ (Subgroup.normalizer ((S : Subgroup X) : Set X)) := by
    rw [Sylow.coe_mapSurjective]
    exact (Subgroup.map_equiv_normalizer_eq (S : Subgroup X) e').symm
  rw [← OrderIso.isCoatom_iff Ψ P]
  refine kfl3_isCoatom_borel_model ?_ (S.mapSurjective hs) ?_ ?_
  · intro h
    exact hP (Ψ.injective (h.trans Ψ.map_top.symm))
  · rw [hN]
    exact Ψ.monotone hSP
  · rw [hN]
    exact fun h => hne (Ψ.injective h)

end Borel

theorem kfl3_normalizer_ne {X : Type} [Group X] [Finite X] {n : ℕ} (hn : Odd n)
    (e₀ : X ≃* projSL 3 (GaloisField 2 n)) (S : Sylow 2 X) {P : Subgroup X}
    (hy : ∃ y ∈ P, orderOf y = 3) :
    Subgroup.normalizer ((S : Subgroup X) : Set X) ≠ P := by
  intro h
  obtain ⟨y, hyP, hy3⟩ := hy
  have hyN : y ∈ Subgroup.normalizer ((S : Subgroup X) : Set X) := by
    rw [h]
    exact hyP
  have hy3' : y ^ 3 = 1 := by
    rw [← hy3]
    exact pow_orderOf_eq_one y
  have hy1 : y = 1 := Sec18.eq_one_of_mem_normalizer_projSL189 hn e₀ S hyN hy3'
  rw [hy1, orderOf_one] at hy3
  exact absurd hy3 (by norm_num)

theorem kfl3_index_of_isMax {X : Type} [Group X] [Finite X] {n : ℕ} (hn : Odd n)
    (e₀ : X ≃* projSL 3 (GaloisField 2 n)) {P : Subgroup X}
    (hmax : Sec18.IsMaxParabolicRankTwo P) : P.index = (2 ^ n) ^ 2 + 2 ^ n + 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let e : X ≃* projectiveSL 3 (GaloisField 2 n) :=
    e₀.trans (KFacts.L34.projSLEquivProjectiveSL 3 (GaloisField 2 n))
  obtain ⟨W, hW, hWP⟩ := kfl3_stab_of_isMax_map e hmax
  have hidx : (P.map e.toMonoidHom).index = P.index := Subgroup.index_map_equiv (H := P) e
  have hfin := kfl3_index_stab hn hW
  rw [← hWP] at hfin
  rw [← hidx]
  exact hfin

theorem kfl3_par_one {X : Type} [Group X] [Finite X] {n : ℕ} (hn : Odd n)
    (e₀ : X ≃* projSL 3 (GaloisField 2 n)) {P : Subgroup X}
    (hP : Sec19.IsProperParabolic P) (hy : ∃ y ∈ P, orderOf y = 3) :
    Sec18.IsMaxParabolicRankTwo P ∧ P.index = (2 ^ n) ^ 2 + 2 ^ n + 1 := by
  obtain ⟨hPt, S, hS⟩ := hP
  have hne := kfl3_normalizer_ne hn e₀ S hy
  have hmax : Sec18.IsMaxParabolicRankTwo P :=
    ⟨kfl3_isCoatom_borel hn e₀ S hPt hS hne, S, hS⟩
  exact ⟨hmax, kfl3_index_of_isMax hn e₀ hmax⟩

theorem kfl3_par_two {X : Type} [Group X] [Finite X] {n : ℕ}
    (e : X ≃* projectiveSL 3 (GaloisField 2 n)) {P Q R : Subgroup X}
    (hP : Sec18.IsMaxParabolicRankTwo P) (hQ : Sec18.IsMaxParabolicRankTwo Q)
    (hR : Sec18.IsMaxParabolicRankTwo R) :
    (∃ g : X, Q = P.map (MulAut.conj g).toMonoidHom) ∨
      (∃ g : X, R = P.map (MulAut.conj g).toMonoidHom) ∨
      (∃ g : X, R = Q.map (MulAut.conj g).toMonoidHom) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨W, hW, hWP⟩ := kfl3_stab_of_isMax_map e hP
  obtain ⟨V, hV, hVQ⟩ := kfl3_stab_of_isMax_map e hQ
  obtain ⟨U, hU, hUR⟩ := kfl3_stab_of_isMax_map e hR
  obtain ⟨hW1, hW2⟩ := (Sec20.Res7.bot_lt_lt_top_iff W).mp hW
  obtain ⟨hV1, hV2⟩ := (Sec20.Res7.bot_lt_lt_top_iff V).mp hV
  obtain ⟨hU1, hU2⟩ := (Sec20.Res7.bot_lt_lt_top_iff U).mp hU
  rcases (show Module.finrank (GaloisField 2 n) W = Module.finrank (GaloisField 2 n) V ∨
      Module.finrank (GaloisField 2 n) W = Module.finrank (GaloisField 2 n) U ∨
      Module.finrank (GaloisField 2 n) V = Module.finrank (GaloisField 2 n) U by omega)
    with h | h | h
  · exact Or.inl (kfl3_conj_of_stab e hWP hVQ h)
  · exact Or.inr (Or.inl (kfl3_conj_of_stab e hWP hUR h))
  · exact Or.inr (Or.inr (kfl3_conj_of_stab e hVQ hUR h))

theorem kfl3Par_holds : KFL3Par := by
  intro X _ _ n hn hne
  obtain ⟨e₀⟩ := hne
  refine ⟨fun P hP hy => kfl3_par_one hn e₀ hP hy, fun P Q R hP hQ hR => ?_⟩
  exact kfl3_par_two (e₀.trans (KFacts.L34.projSLEquivProjectiveSL 3 (GaloisField 2 n)))
    hP hQ hR

end CFSG.RankThree.PartTwo.Late
