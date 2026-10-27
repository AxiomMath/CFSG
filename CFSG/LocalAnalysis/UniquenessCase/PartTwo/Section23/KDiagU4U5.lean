module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KDiagL2
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ParabCommUniModelFlag

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabComm.Uni
open Matrix Module Subgroup
open scoped Pointwise

namespace KDiagU4U5

variable {p f : ℕ} {K : Type} [Field K] {r ε : ℕ}

@[expose] noncomputable def conjSU (h : UnitaryFieldData p f K)
    (γ : semilinearSimilitudes h r ε) : hypSU h r ε →* hypSU h r ε where
  toFun g :=
    ⟨(γ : SemiGL (HypIndex r ε) K).left *
        glAut (γ : SemiGL (HypIndex r ε) K).right (g : GL (HypIndex r ε) K) *
        ((γ : SemiGL (HypIndex r ε) K).left)⁻¹, conj_mem_hypSU γ.2 g⟩
  map_one' := by
    apply Subtype.ext
    simp
  map_mul' g g' := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    rw [map_mul]
    group

theorem semilinearAutHom_hypProj (h : UnitaryFieldData p f K) (hr : 1 ≤ r) (hε : ε ≤ 1)
    (γ : semilinearSimilitudes h r ε) (g : hypSU h r ε) :
    semilinearAutHom h hr hε γ (hypProj h r ε g) = hypProj h r ε (conjSU h γ g) := by
  rw [semilinearAutHom_apply]
  rfl

theorem semilinearAutHom_comp_hypProj (h : UnitaryFieldData p f K) (hr : 1 ≤ r) (hε : ε ≤ 1)
    (γ : semilinearSimilitudes h r ε) :
    (semilinearAutHom h hr hε γ).toMonoidHom.comp (hypProj h r ε) =
      (hypProj h r ε).comp (conjSU h γ) := by
  ext g
  exact semilinearAutHom_hypProj h hr hε γ g

theorem inl_smul_submodule (c : GL (HypIndex r ε) K)
    (W : Submodule K (HypIndex r ε → K)) :
    (SemidirectProduct.inl c : SemiGL (HypIndex r ε) K) • W = c • W := by
  rw [semiGL_smul_def]
  simp only [SemidirectProduct.left_inl, SemidirectProduct.right_inl, coordImage_one]
  rfl

theorem mem_flagStabilizer_conjSU (h : UnitaryFieldData p f K) {I : Set ℕ}
    {γ : semilinearSimilitudes h r ε}
    (hγ : ∀ i ∈ I, γ • hypFlag h r ε i = hypFlag h r ε i)
    {g : hypSU h r ε} (hg : g ∈ flagStabilizer h r ε I) :
    conjSU h γ g ∈ flagStabilizer h r ε I := by
  rw [mem_flagStabilizer] at hg ⊢
  intro i hi
  have hgGL : (g : GL (HypIndex r ε) K) • hypFlag h r ε i = hypFlag h r ε i :=
    (Subgroup.smul_def g (hypFlag h r ε i)).trans (hg i hi)
  have hγGL : (γ : SemiGL (HypIndex r ε) K) • hypFlag h r ε i = hypFlag h r ε i :=
    (Subgroup.smul_def γ (hypFlag h r ε i)).trans (hγ i hi)
  have hγinv : γ⁻¹ • hypFlag h r ε i = hypFlag h r ε i := by
    have h := congrArg (fun W => γ⁻¹ • W) (hγ i hi)
    simpa using h.symm
  have hγinvGL : ((γ : SemiGL (HypIndex r ε) K)⁻¹) • hypFlag h r ε i =
      hypFlag h r ε i := by
    rw [← Subgroup.coe_inv, ← MulAction.subgroup_smul_def]
    exact hγinv
  have hconj : ((γ : SemiGL (HypIndex r ε) K) *
      SemidirectProduct.inl (g : GL (HypIndex r ε) K) *
      (γ : SemiGL (HypIndex r ε) K)⁻¹) =
      SemidirectProduct.inl (conjSU h γ g : GL (HypIndex r ε) K) := by
    rw [semiGL_conj_inl]
    rfl
  have hstep : (SemidirectProduct.inl (conjSU h γ g : GL (HypIndex r ε) K) :
      SemiGL (HypIndex r ε) K) • hypFlag h r ε i = hypFlag h r ε i := by
    calc
      (SemidirectProduct.inl (conjSU h γ g : GL (HypIndex r ε) K) :
          SemiGL (HypIndex r ε) K) • hypFlag h r ε i
          = ((γ : SemiGL (HypIndex r ε) K) *
              SemidirectProduct.inl (g : GL (HypIndex r ε) K) *
              (γ : SemiGL (HypIndex r ε) K)⁻¹) • hypFlag h r ε i := by rw [hconj]
      _ = (γ : SemiGL (HypIndex r ε) K) •
            (SemidirectProduct.inl (g : GL (HypIndex r ε) K) •
              (((γ : SemiGL (HypIndex r ε) K)⁻¹) • hypFlag h r ε i)) := by
            rw [mul_smul, mul_smul]
      _ = (γ : SemiGL (HypIndex r ε) K) •
            ((g : GL (HypIndex r ε) K) • hypFlag h r ε i) := by
            rw [hγinvGL, inl_smul_submodule]
      _ = (γ : SemiGL (HypIndex r ε) K) • hypFlag h r ε i := by rw [hgGL]
      _ = hypFlag h r ε i := hγGL
  have hGL : (conjSU h γ g : GL (HypIndex r ε) K) • hypFlag h r ε i =
      hypFlag h r ε i := by
    rw [← inl_smul_submodule]
    exact hstep
  exact (Subgroup.smul_def (conjSU h γ g) (hypFlag h r ε i)).trans hGL

theorem map_flagStabilizer_le (h : UnitaryFieldData p f K) (hr : 1 ≤ r) (hε : ε ≤ 1)
    {I : Set ℕ} {γ : semilinearSimilitudes h r ε}
    (hγ : ∀ i ∈ I, γ • hypFlag h r ε i = hypFlag h r ε i) :
    ((flagStabilizer h r ε I).map (hypProj h r ε)).map
        (semilinearAutHom h hr hε γ).toMonoidHom ≤
      (flagStabilizer h r ε I).map (hypProj h r ε) := by
  rw [Subgroup.map_map, semilinearAutHom_comp_hypProj h hr hε γ, ← Subgroup.map_map]
  refine Subgroup.map_mono (f := hypProj h r ε) ?_
  intro x hx
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
  exact mem_flagStabilizer_conjSU h hγ hy

theorem flagStabilizer_Icc_eq_hypBorel (h : UnitaryFieldData p f K) :
    flagStabilizer h r ε (Set.Icc 1 r) = hypBorel h r ε :=
  rfl

theorem kDiag_hypPSU {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K) (hr : 1 ≤ r)
    (hε : ε ≤ 1) (hn : 3 ≤ 2 * r + ε) (hq : ¬(2 * r + ε = 3 ∧ 2 ^ f = 2)) :
    ∀ (θ : MulAut (hypPSU h r ε)), Odd (orderOf θ) →
    ∀ S : Sylow 2 (hypPSU h r ε),
      (∀ x ∈ (S : Subgroup (hypPSU h r ε)),
        θ x ∈ (S : Subgroup (hypPSU h r ε))) →
    ∀ P : Subgroup (hypPSU h r ε), IsParabolicTwo (hypPSU h r ε) P →
      (S : Subgroup (hypPSU h r ε)) ≤
        Subgroup.normalizer (P : Set (hypPSU h r ε)) →
      ∀ x ∈ P, θ x ∈ P := by
  intro θ _hθ S hSθ P hP hSP x hx
  have hSmap : Subgroup.map (θ : hypPSU h r ε →* hypPSU h r ε)
      (S : Subgroup (hypPSU h r ε)) = (S : Subgroup (hypPSU h r ε)) := by
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · rintro _ ⟨y, hy, rfl⟩
      exact hSθ y hy
    · rw [Subgroup.card_map_of_injective θ.injective]
  have hSP' : (S : Subgroup (hypPSU h r ε)) ≤ P :=
    IsParabolicTwo.le_of_le_normalizer hP S.isPGroup' hSP
  have hNS : Subgroup.normalizer (S : Set (hypPSU h r ε)) ≤ P :=
    hP.normalizer_le S hSP'
  have hmem : Subgroup.normalizer (S : Set (hypPSU h r ε)) ∈ sylowNormalizers h r ε :=
    ⟨S, rfl⟩
  obtain ⟨g, hg⟩ := (mem_sylowNormalizers_iff h hr hε _).mp hmem
  set x₀ : hypPSU h r ε := hypProj h r ε g with hx₀
  set e : MulAut (hypPSU h r ε) := MulAut.conj (x₀⁻¹) with he
  set P' : Subgroup (hypPSU h r ε) := P.map (MulEquiv.toMonoidHom e) with hP'def
  have hNmap : Subgroup.map (MulEquiv.toMonoidHom e)
      (Subgroup.normalizer (S : Set (hypPSU h r ε))) = hypProjBorel h r ε := by
    rw [hg, Subgroup.map_map]
    have hcomp : (MulEquiv.toMonoidHom e).comp
        (MulEquiv.toMonoidHom (MulAut.conj x₀)) = MonoidHom.id _ := by
      ext z
      simp [he, MulAut.conj_apply, MulEquiv.toMonoidHom_eq_coe, MonoidHom.comp_apply,
        MonoidHom.id_apply, mul_assoc]
    rw [hcomp, Subgroup.map_id]
  have hP'B : hypProjBorel h r ε ≤ P' := by
    rw [hP'def, ← hNmap]
    exact Subgroup.map_mono hNS
  set Apre : Subgroup (hypSU h r ε) := P'.comap (hypProj h r ε) with hApre
  have hBA : flagStabilizer h r ε (Set.Icc 1 r) ≤ Apre := by
    rw [hApre, ← Subgroup.map_le_iff_le_comap]
    rw [flagStabilizer_Icc_eq_hypBorel]
    change hypProjBorel h r ε ≤ P'
    exact hP'B
  obtain ⟨c, hc, hc0⟩ := exists_mem_traceZero_ne_zero' h
  obtain ⟨hI, hApre_eq, -, -⟩ := unitary_Borel_overgroups h hr hε hc hc0 Apre hBA
  set I : Set ℕ := overgroupCuts ε h c hc Apre with hIdef
  have hP'I : P' = (flagStabilizer h r ε I).map (hypProj h r ε) := by
    rw [show P' = Apre.map (hypProj h r ε) from
      (Subgroup.map_comap_eq_self_of_surjective (hypProj_surjective h r ε) P').symm,
      hApre_eq]
  set θ' : MulAut (hypPSU h r ε) :=
    (MulAut.conj (x₀⁻¹) : MulAut (hypPSU h r ε)) * θ *
      (MulAut.conj x₀ : MulAut (hypPSU h r ε)) with hθ'
  obtain ⟨γ, hγeq⟩ : ∃ γ : semilinearSimilitudes h r ε,
      semilinearAutHom h hr hε γ = θ' :=
    semilinearAutHom_surjective_of_admissible h hr hε hn hq θ'
  set S' : Subgroup (hypPSU h r ε) :=
    (S : Subgroup (hypPSU h r ε)).map
      (MulEquiv.toMonoidHom (MulAut.conj (x₀⁻¹))) with hS'
  have hS'θ' : Subgroup.map (MulEquiv.toMonoidHom θ') S' = S' := by
    rw [hS', Subgroup.map_map]
    have hcomp : (MulEquiv.toMonoidHom θ').comp
        (MulEquiv.toMonoidHom (MulAut.conj (x₀⁻¹))) =
        (MulEquiv.toMonoidHom (MulAut.conj (x₀⁻¹))).comp
          (θ : hypPSU h r ε →* hypPSU h r ε) := by
      ext z
      simp [hθ', MulAut.conj_apply, MulEquiv.toMonoidHom_eq_coe, MonoidHom.comp_apply,
        mul_assoc]
    rw [hcomp, ← Subgroup.map_map, hSmap]
  have hN' : Subgroup.normalizer (S' : Set (hypPSU h r ε)) = hypProjBorel h r ε := by
    rw [hS', ← Subgroup.map_equiv_normalizer_eq (S : Subgroup (hypPSU h r ε))
        (MulAut.conj (x₀⁻¹) : MulAut (hypPSU h r ε))]
    exact hNmap
  have hBfix : Subgroup.map (MulEquiv.toMonoidHom θ') (hypProjBorel h r ε) =
      hypProjBorel h r ε := by
    rw [← hN', Subgroup.map_equiv_normalizer_eq S' θ', hS'θ']
  have hprojflag_eq : projFlag h r ε (Finset.Icc 1 r) = hypProjBorel h r ε := by
    rw [projFlag, Finset.coe_Icc]
    rfl
  have hγproj : (projFlag h r ε (Finset.Icc 1 r)).map
      (semilinearAutHom h hr hε γ).toMonoidHom = projFlag h r ε (Finset.Icc 1 r) := by
    rw [hprojflag_eq,
      show MulEquiv.toMonoidHom (semilinearAutHom h hr hε γ) = MulEquiv.toMonoidHom θ'
        from congrArg MulEquiv.toMonoidHom hγeq]
    exact hBfix
  have hIr : ∀ c ∈ Finset.Icc 1 r, 1 ≤ c ∧ c ≤ r := by
    intro c hc
    rw [Finset.mem_Icc] at hc
    exact hc
  have hMsmul := smul_hypFlag_eq_of_map_projFlag h hr hε
    (I := Finset.Icc 1 r) hIr γ hγproj
  have hγflag : ∀ i ∈ I, γ • hypFlag h r ε i = hypFlag h r ε i := by
    intro i hi
    have hiIcc : i ∈ Finset.Icc 1 r := by
      rw [Finset.mem_Icc]
      exact hI hi
    have hin : i ≤ 2 * r + ε := by
      have := (Finset.mem_Icc.mp hiIcc).2
      omega
    rw [Subgroup.smul_def, semiGL_smul_def,
      coordImage_hypFlag hε ((γ : SemiGL (HypIndex r ε) K).right) hin]
    exact hMsmul i hiIcc
  have hP'le : Subgroup.map (MulEquiv.toMonoidHom θ') P' ≤ P' := by
    rw [hP'I, ← hγeq]
    exact map_flagStabilizer_le h hr hε hγflag
  have hP'eq : Subgroup.map (MulEquiv.toMonoidHom θ') P' = P' := by
    refine Subgroup.eq_of_le_of_card_ge (H := Subgroup.map
      (MulEquiv.toMonoidHom θ') P') (K := P') hP'le ?_
    rw [Subgroup.card_map_of_injective (f := MulEquiv.toMonoidHom θ') θ'.injective]
  have hPP' : Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj x₀)) P' = P := by
    rw [hP'def, Subgroup.map_map]
    have hcomp : (MulEquiv.toMonoidHom (MulAut.conj x₀)).comp
        (MulEquiv.toMonoidHom e) = MonoidHom.id _ := by
      ext z
      simp [he, MulAut.conj_apply, MulEquiv.toMonoidHom_eq_coe, MonoidHom.comp_apply,
        MonoidHom.id_apply, mul_assoc]
    rw [hcomp, Subgroup.map_id]
  have hθconj : ∀ z : hypPSU h r ε,
      θ (x₀ * z * x₀⁻¹) = x₀ * θ' z * x₀⁻¹ := by
    intro z
    have hz : θ' z = x₀⁻¹ * θ (x₀ * z * x₀⁻¹) * x₀ := by
      simp only [hθ', MulAut.mul_apply, MulAut.conj_apply, MulEquiv.toMonoidHom_eq_coe]
      group
    rw [hz]
    group
  rw [← hPP'] at hx
  obtain ⟨z, hzP, hzx⟩ := Subgroup.mem_map.mp hx
  have hθ'z : θ' z ∈ P' := by
    rw [← hP'eq]
    exact Subgroup.mem_map_of_mem (MulEquiv.toMonoidHom θ') hzP
  have hθconj' : θ (MulEquiv.toMonoidHom (MulAut.conj x₀) z) =
      MulEquiv.toMonoidHom (MulAut.conj x₀) (θ' z) := by
    have hz : MulEquiv.toMonoidHom (MulAut.conj x₀) z = x₀ * z * x₀⁻¹ := by
      rw [MulEquiv.toMonoidHom_eq_coe]
      change (MulAut.conj x₀ : MulAut (hypPSU h r ε)) z = x₀ * z * x₀⁻¹
      rw [MulAut.conj_apply]
    rw [hz, hθconj z, MulEquiv.toMonoidHom_eq_coe]
    change x₀ * θ' z * x₀⁻¹ = (MulAut.conj x₀ : MulAut (hypPSU h r ε)) (θ' z)
    rw [MulAut.conj_apply]
  have hmem : θ (MulEquiv.toMonoidHom (MulAut.conj x₀) z) ∈
      Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj x₀)) P' := by
    rw [hθconj']
    exact Subgroup.mem_map_of_mem (MulEquiv.toMonoidHom (MulAut.conj x₀)) hθ'z
  rw [hPP'] at hmem
  have hzx' : θ (MulEquiv.toMonoidHom (MulAut.conj x₀) z) = θ x := by
    rw [hzx]
  rwa [hzx'] at hmem

end KDiagU4U5

theorem kDiag_of_lieModel_psu4 {n : ℕ} {X : Type} [Group X] [Finite X]
    (hX : CFSG.Blueprint.LieModel X .PSU 4 2 n) :
    ∀ (θ : MulAut X), Odd (orderOf θ) →
    ∀ S : Sylow 2 X, (∀ x ∈ (S : Subgroup X), θ x ∈ (S : Subgroup X)) →
    ∀ (P : Subgroup X), IsParabolicTwo X P →
      (S : Subgroup X) ≤ Subgroup.normalizer (P : Set X) →
      ∀ x ∈ P, θ x ∈ P := by
  have ht : (CFSG.Open.StatedLieTag.PSU) ∈ CFSG.Blueprint.classicalTags := by decide
  have hmodel : CFSG.Open.StatedClassicalModel X .PSU 4 2 n :=
    CFSG.Blueprint.LieModel.statedClassicalModel hX ht
  rw [CFSG.Open.StatedClassicalModel] at hmodel
  obtain ⟨hadm, K, hfield, hfinite, hcard, ⟨e₀⟩⟩ := hmodel
  letI : Field K := hfield
  letI : Finite K := hfinite
  letI : Fintype K := Fintype.ofFinite K
  rw [CFSG.Open.StatedLieAdmissible] at hadm
  have hcard' : Nat.card K = 2 ^ (2 * n) := by
    rw [hcard, ← pow_mul, Nat.mul_comm]
  have h : UnitaryFieldData 2 n K :=
    { prime := Nat.prime_two, one_le := hadm.2.1, card := hcard' }
  obtain ⟨R, hR⟩ := exists_isHypTransport h (r := 2) (ε := 0)
  have ePSU : unitaryPSU h 4 ≃* CFSG.Open.StatedProj (CFSG.Open.StatedSU 4 (2 ^ n) K) :=
    unitaryPSUEquiv h (n := 4) (by norm_num)
  exact kDiag_transport
    (e := e₀.trans (ePSU.symm.trans (hypProjTransport h hR).symm))
    (KDiagU4U5.kDiag_hypPSU h (r := 2) (ε := 0) (by norm_num) (by norm_num) (by norm_num) (by simp))

theorem kDiag_of_lieModel_psu5 {n : ℕ} {X : Type} [Group X] [Finite X]
    (hX : CFSG.Blueprint.LieModel X .PSU 5 2 n) :
    ∀ (θ : MulAut X), Odd (orderOf θ) →
    ∀ S : Sylow 2 X, (∀ x ∈ (S : Subgroup X), θ x ∈ (S : Subgroup X)) →
    ∀ (P : Subgroup X), IsParabolicTwo X P →
      (S : Subgroup X) ≤ Subgroup.normalizer (P : Set X) →
      ∀ x ∈ P, θ x ∈ P := by
  have ht : (CFSG.Open.StatedLieTag.PSU) ∈ CFSG.Blueprint.classicalTags := by decide
  have hmodel : CFSG.Open.StatedClassicalModel X .PSU 5 2 n :=
    CFSG.Blueprint.LieModel.statedClassicalModel hX ht
  rw [CFSG.Open.StatedClassicalModel] at hmodel
  obtain ⟨hadm, K, hfield, hfinite, hcard, ⟨e₀⟩⟩ := hmodel
  letI : Field K := hfield
  letI : Finite K := hfinite
  letI : Fintype K := Fintype.ofFinite K
  rw [CFSG.Open.StatedLieAdmissible] at hadm
  have hcard' : Nat.card K = 2 ^ (2 * n) := by
    rw [hcard, ← pow_mul, Nat.mul_comm]
  have h : UnitaryFieldData 2 n K :=
    { prime := Nat.prime_two, one_le := hadm.2.1, card := hcard' }
  obtain ⟨R, hR⟩ := exists_isHypTransport h (r := 2) (ε := 1)
  have ePSU : unitaryPSU h 5 ≃* CFSG.Open.StatedProj (CFSG.Open.StatedSU 5 (2 ^ n) K) :=
    unitaryPSUEquiv h (n := 5) (by norm_num)
  exact kDiag_transport
    (e := e₀.trans (ePSU.symm.trans (hypProjTransport h hR).symm))
    (KDiagU4U5.kDiag_hypPSU h (r := 2) (ε := 1) (by norm_num) (by norm_num) (by norm_num) (by simp))

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
