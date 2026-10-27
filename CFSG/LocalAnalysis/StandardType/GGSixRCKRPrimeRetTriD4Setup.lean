module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeTriD4PinnedFrame
import CFSG.RankThree.PartOne.KGD.D4Frame
import CFSG.LocalAnalysis.StandardType.KGLangLT5ExcTorus
import CFSG.HardMathSupport.Timmesfeld.LangTorus.TorusAtDatum
import CFSG.HardMathSupport.Timmesfeld.LangTorus.FrobeniusOnRoots
import CFSG.HardMathSupport.Timmesfeld.LangTorus.TwistedE6Base
import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.OuterFourSeitzD4
import CFSG.RankThree.Chevalley.SteinbergCBTrialityPermModule
import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeExcOrbit

public section

namespace CFSG.StandardType.RCKRP

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Universal
  CFSG.StandardType CFSG.StandardType.GGFinModel CFSG.LieType.Chevalley
  CFSG.StandardType.S2MathFi1035Pos CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.StandardType.LieCore

private lemma rckRP_conj_step_one
    {G : Type*} [Group G] {s m n P : G} {F : G →* G} {z : G}
    (hs : s * m = n * P * F s * P⁻¹) :
    s * m * (P * F z * P⁻¹) * m⁻¹ * s⁻¹ =
      n * (P * F (s * z * s⁻¹) * P⁻¹) * n⁻¹ := by
  have h1 : m⁻¹ * s⁻¹ = P * (F s)⁻¹ * P⁻¹ * n⁻¹ := by
    have h2 : m⁻¹ * s⁻¹ = (s * m)⁻¹ := by group
    rw [h2, hs]
    group
  rw [hs, map_mul, map_mul, map_inv]
  calc
    n * P * F s * P⁻¹ * (P * F z * P⁻¹) * m⁻¹ * s⁻¹
        = n * P * F s * P⁻¹ * (P * F z * P⁻¹) * (m⁻¹ * s⁻¹) := by group
    _ = n * P * F s * P⁻¹ * (P * F z * P⁻¹) *
          (P * (F s)⁻¹ * P⁻¹ * n⁻¹) := by rw [h1]
    _ = n * (P * (F s * F z * (F s)⁻¹) * P⁻¹) * n⁻¹ := by group

private lemma rckRP_swap_conj_sq {G : Type*} [Group G] {P Q : G}
    (hPQP : P * Q * P = Q) (hQ2 : Q * Q = 1) (hP3 : P * P * P = 1) :
    Q * P * P * Q = P := by
  have hQPQ : Q * P * Q = P⁻¹ := by
    calc Q * P * Q = Q * (P * Q * P) * P⁻¹ := by group
      _ = Q * Q * P⁻¹ := by rw [hPQP]
      _ = P⁻¹ := by rw [hQ2, one_mul]
  calc Q * P * P * Q = Q * P * (Q * Q) * P * Q := by rw [hQ2]; group
    _ = (Q * P * Q) * (Q * P * Q) := by group
    _ = P⁻¹ * P⁻¹ := by rw [hQPQ]
    _ = P := by
        calc P⁻¹ * P⁻¹ = (P * P * P) * P⁻¹ * P⁻¹ := by rw [hP3, one_mul]
          _ = P := by group

private lemma rckRP_swap_step_two {G : Type*} [Group G] {Q m P : G} {F : G →* G} {z : G}
    (hQ2 : Q * Q = 1) (hQP2Q : Q * P * P * Q = P) (hFQ : F Q = Q) :
    Q * m * (P * P * F z * (P * P)⁻¹) * m⁻¹ * Q =
      (Q * m * Q) * (P * F (Q * z * Q) * P⁻¹) * (Q * m * Q)⁻¹ := by
  have hQinv : Q⁻¹ = Q := inv_eq_of_mul_eq_one_right hQ2
  have hPP : P * P = Q * P * Q := by
    calc P * P = (Q * Q) * P * P * (Q * Q) := by rw [hQ2]; group
      _ = Q * (Q * P * P * Q) * Q := by group
      _ = Q * P * Q := by rw [hQP2Q]
  have hPPinv : (P * P)⁻¹ = Q * P⁻¹ * Q := by
    rw [hPP, mul_inv_rev, mul_inv_rev, hQinv]
    group
  rw [hPPinv, hPP, map_mul, map_mul, hFQ]
  have hQmQinv : (Q * m * Q)⁻¹ = Q * m⁻¹ * Q := by
    rw [mul_inv_rev, mul_inv_rev, hQinv]
    group
  rw [hQmQinv]
  group

private lemma permModuleMap_mul_rootDiagUnit {τ : Tag} {K : Type} [Field K]
    {π : Equiv.Perm (Fin τ.rank)}
    (hπ : ∀ i j, τ.cartan (π i) (π j) = τ.cartan i j) (a : Fin τ.rank → Kˣ) :
    (CFSG.RankThree.Chevalley.permModuleMap hπ K) * rootDiagUnit τ a =
      rootDiagUnit τ (fun i => a (π.symm i)) * (CFSG.RankThree.Chevalley.permModuleMap hπ K) := by
  apply Units.ext
  change (CFSG.RankThree.Chevalley.permModuleMap hπ K :
      Module.End K (RootModule τ K)) * rootDiag a =
    rootDiag (fun i => a (π.symm i)) *
      (CFSG.RankThree.Chevalley.permModuleMap hπ K :
        Module.End K (RootModule τ K))
  refine rootModule_end_ext (fun j => ?_) fun α hα => ?_
  · rw [Module.End.mul_apply, Module.End.mul_apply, rootDiag_hVec,
      CFSG.RankThree.Chevalley.permModuleMap_hVec, rootDiag_hVec]
  · rw [Module.End.mul_apply, Module.End.mul_apply, rootDiag_rootVec a hα, map_smul,
      CFSG.RankThree.Chevalley.permModuleMap_rootVec hπ K α hα,
      rootDiag_rootVec (fun i => a (π.symm i)) (hα.permLattice hπ), rootChar_permLattice]
    simp [Equiv.symm_apply_apply]

private lemma permModuleMap_conj_rootDiagUnit {τ : Tag} {K : Type} [Field K]
    {π : Equiv.Perm (Fin τ.rank)}
    (hπ : ∀ i j, τ.cartan (π i) (π j) = τ.cartan i j) (a : Fin τ.rank → Kˣ) :
    (CFSG.RankThree.Chevalley.permModuleMap hπ K) * rootDiagUnit τ a *
        (CFSG.RankThree.Chevalley.permModuleMap hπ K)⁻¹ =
      rootDiagUnit τ (fun i => a (π.symm i)) := by
  have h := permModuleMap_mul_rootDiagUnit hπ a
  calc (CFSG.RankThree.Chevalley.permModuleMap hπ K) * rootDiagUnit τ a *
        (CFSG.RankThree.Chevalley.permModuleMap hπ K)⁻¹ =
      (rootDiagUnit τ (fun i => a (π.symm i)) *
        (CFSG.RankThree.Chevalley.permModuleMap hπ K)) *
        (CFSG.RankThree.Chevalley.permModuleMap hπ K)⁻¹ := by rw [h]
    _ = rootDiagUnit τ (fun i => a (π.symm i)) := by group

theorem rckTriD4PinnedFrameAt_two
    {τ : Tag} {p₀ : ℕ} {S : LangSetup τ GGL p₀} {Ψ : Set (Fin τ.rank → ℤ)} {h : ℕ}
    {m : ModGL Tag.D4 GGL} (hm : m ∈ monomialSubgroup Tag.D4 GGL)
    (hmC : m ∈ adjointGroup Tag.D4 GGL) (hfr : RCKTriD4PinnedFrameAt S Ψ h 2 m) :
    ∃ m' : ModGL Tag.D4 GGL, m' ∈ monomialSubgroup Tag.D4 GGL ∧
      m' ∈ adjointGroup Tag.D4 GGL ∧ RCKTriD4PinnedFrameAt S Ψ h 1 m' := by
  classical
  obtain ⟨hY, Ξ, ι, hstepOld, hbij, hiform, hrootOld, htorOld⟩ := hfr
  let A := adjointGroup Tag.D4 GGL
  let π : Equiv.Perm (Fin Tag.D4.rank) := by
    change Equiv.Perm (Fin TwistTag.D4.tag.rank)
    exact CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.OuterFourSeitz.d4Swap
  let Q : ModGL Tag.D4 GGL := CFSG.RankThree.Chevalley.permModuleMap
      CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.OuterFourSeitz.d4Swap_cartan GGL
  let P : ModGL Tag.D4 GGL := diagramMap TwistTag.D4 GGL
  have hd4cartan : ∀ i j : Fin Tag.D4.rank,
      Tag.D4.cartan (π i)
        (π j) =
        Tag.D4.cartan i j := by
    intro i j
    change TwistTag.D4.tag.cartan
      (π i)
      (π j) =
      TwistTag.D4.tag.cartan i j
    exact CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.OuterFourSeitz.d4Swap_cartan i j
  have hQmap : A.map (MulAut.conj Q).toMonoidHom = A :=
    CFSG.RankThree.Chevalley.map_conj_permModuleMap_adjointGroup (τ := Tag.D4)
      (π := π)
      hd4cartan GGL
  let Qaut : MulAut A :=
    ((MulAut.conj Q).subgroupMap A).trans (MulEquiv.subgroupCongr hQmap)
  have hQaut_coe : ∀ x : A,
      (Qaut x : ModGL Tag.D4 GGL) = Q * (x : ModGL Tag.D4 GGL) * Q⁻¹ := by
    intro x
    have h1 := MulEquiv.coe_subgroupMap_apply (MulAut.conj Q) A x
    have h2 : ((MulEquiv.subgroupCongr hQmap)
        ((MulEquiv.subgroupMap (MulAut.conj Q) A) x) : ModGL Tag.D4 GGL) =
        (((MulEquiv.subgroupMap (MulAut.conj Q) A) x) : ModGL Tag.D4 GGL) := rfl
    change ((MulEquiv.subgroupCongr hQmap)
      ((MulEquiv.subgroupMap (MulAut.conj Q) A) x) : ModGL Tag.D4 GGL) =
      Q * (x : ModGL Tag.D4 GGL) * Q⁻¹
    rw [h2, h1, MulAut.conj_apply]
  let Ξ' : ↥(rootSpan τ GGL Ψ) ≃* A := Ξ.trans Qaut
  have hcoe : ∀ x : ↥(rootSpan τ GGL Ψ),
      (Ξ' x : ModGL Tag.D4 GGL) = Q * (Ξ x : ModGL Tag.D4 GGL) * Q⁻¹ := by
    intro x
    simp only [Ξ', MulEquiv.trans_apply, hQaut_coe]
  let m' : ModGL Tag.D4 GGL := Q * m * Q⁻¹
  have hm'C : m' ∈ adjointGroup Tag.D4 GGL := by
    have h : m' ∈ A.map (MulAut.conj Q).toMonoidHom := Subgroup.mem_map_of_mem _ hmC
    rwa [hQmap] at h
  have hm'mono : m' ∈ monomialSubgroup Tag.D4 GGL := by
    have hmono : (monomialSubgroup Tag.D4 GGL).map (MulAut.conj Q).toMonoidHom ≤
        monomialSubgroup Tag.D4 GGL := by
      change (monomialSubgroup Tag.D4 GGL).map
        (MulAut.conj (CFSG.RankThree.Chevalley.permModuleMap
          (τ := Tag.D4) hd4cartan GGL)).toMonoidHom ≤ monomialSubgroup Tag.D4 GGL
      rw [monomialSubgroup, Subgroup.map_sup,
        CFSG.RankThree.Chevalley.map_conj_permModuleMap_torusGroup (τ := Tag.D4)
          (π := π) hd4cartan GGL]
      refine sup_le le_sup_left ?_
      rw [MonoidHom.map_closure]
      refine (Subgroup.closure_le _).2 ?_
      rintro _ ⟨g, ⟨i, rfl⟩, rfl⟩
      change (MulAut.conj (CFSG.RankThree.Chevalley.permModuleMap
          (τ := Tag.D4) hd4cartan GGL)) (weylElt Tag.D4 GGL i 1) ∈
        (torusGroup Tag.D4 GGL ⊔ Subgroup.closure (Set.range fun i => weylElt Tag.D4 GGL i 1))
      rw [show (MulAut.conj (CFSG.RankThree.Chevalley.permModuleMap
          (τ := Tag.D4) hd4cartan GGL))
          (weylElt Tag.D4 GGL i 1) = weylElt Tag.D4 GGL
            (π i) 1 from
        CFSG.RankThree.Chevalley.conj_permModuleMap_weylElt (τ := Tag.D4)
          (π := π)
          hd4cartan GGL i 1]
      exact Subgroup.mem_sup_right (Subgroup.subset_closure ⟨
        π i, rfl⟩)
    exact hmono (Subgroup.mem_map_of_mem _ hm)
  have hQ2 : Q * Q = 1 := by
    change CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.OuterFourSeitz.d4SwapMap GGL *
      CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.OuterFourSeitz.d4SwapMap GGL = 1
    exact CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.OuterFourSeitz.d4SwapMap_mul_self GGL
  have hQinv : Q⁻¹ = Q := by
    change (CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.OuterFourSeitz.d4SwapMap GGL)⁻¹ =
      CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.OuterFourSeitz.d4SwapMap GGL
    exact CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.OuterFourSeitz.d4SwapMap_inv GGL
  have hP3 : P * P * P = 1 := by
    have h : P ^ 3 = 1 := diagramMap_pow_order (t := TwistTag.D4) (K := GGL)
    simpa [pow_succ, pow_two] using h
  have hPQP : P * Q * P = Q := by
    change diagramMap TwistTag.D4 GGL *
      CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.OuterFourSeitz.d4SwapMap GGL *
      diagramMap TwistTag.D4 GGL =
      CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.OuterFourSeitz.d4SwapMap GGL
    exact CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.OuterFourSeitz.d4P_mul_swap_mul_d4P GGL
  have hQP2Q : Q * P * P * Q = P := rckRP_swap_conj_sq hPQP hQ2 hP3
  let FrM : ModGL Tag.D4 GGL →* ModGL Tag.D4 GGL :=
    Units.map (entrywiseHom (iterateFrobenius GGL 2 h))
  have hFQ : FrM Q = Q :=
    CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.OuterFourSeitz.units_map_entrywiseHom_labelMap
      (K := GGL) (π := π) (hπ := hd4cartan) (σ := iterateFrobenius GGL 2 h)
  have hstep : ∀ (y : ModGL τ GGL) (hy : y ∈ rootSpan τ GGL Ψ),
      (Ξ' ⟨S.D.step y, hY y hy⟩ : ModGL Tag.D4 GGL) =
        m' * triPsi h 1 (Ξ' ⟨y, hy⟩ : ModGL Tag.D4 GGL) * m'⁻¹ := by
    intro y hy
    set z : ModGL Tag.D4 GGL := (Ξ ⟨y, hy⟩ : ModGL Tag.D4 GGL) with hz
    have htri2 : triPsi h 2 z = P * P * FrM z * (P * P)⁻¹ := by
      have h : triPsi h 2 z = P ^ 2 * FrM z * (P ^ 2)⁻¹ := rfl
      simpa [pow_two] using h
    have htri1 : triPsi h 1 (Q * z * Q⁻¹) = P * FrM (Q * z * Q⁻¹) * P⁻¹ := rfl
    rw [hcoe ⟨S.D.step y, hY y hy⟩, hcoe ⟨y, hy⟩, hstepOld y hy, htri2, htri1, hQinv]
    have hmain := rckRP_swap_step_two (Q := Q) (m := m) (P := P) (F := FrM)
      (z := z) hQ2 hQP2Q hFQ
    calc Q * (m * (P * P * FrM z * (P * P)⁻¹) * m⁻¹) * Q
        = Q * m * (P * P * FrM z * (P * P)⁻¹) * m⁻¹ * Q := by group
      _ = (Q * m * Q) * (P * FrM (Q * z * Q) * P⁻¹) * (Q * m * Q)⁻¹ := hmain
      _ = m' * (P * FrM (Q * z * Q) * P⁻¹) * m'⁻¹ := by
        simp only [m']
        rw [hQinv]
  let ι' : (Fin τ.rank → ℤ) →+ (Fin Tag.D4.rank → ℤ) :=
    (CFSG.LieType.Chevalley.ToralSign.permLatticeHom (τ := Tag.D4)
      π).comp ι
  have hι' : ∀ v, ι' v = permLattice (τ := Tag.D4) π (ι v) := fun _ => rfl
  have hd4symm : ∀ i j : Fin Tag.D4.rank, Tag.D4.cartan
      (π.symm i)
      (π.symm j) =
      Tag.D4.cartan i j := by
    intro i j
    simpa [Equiv.apply_symm_apply] using (hd4cartan (π.symm i) (π.symm j)).symm
  have hbij' : Set.BijOn ι' Ψ {δ | IsRoot Tag.D4 δ} := by
    refine ⟨?_, ?_, ?_⟩
    · intro γ hγ
      exact (hbij.1 hγ).permLattice (π := π) hd4cartan
    · intro γ hγ δ hδ h
      exact hbij.2.1 hγ hδ (CFSG.LieType.Chevalley.ToralSign.permLattice_injective
        π h)
    · intro δ hδ
      have hδ' : IsRoot Tag.D4 (permLattice (τ := Tag.D4) π.symm δ) :=
        hδ.permLattice hd4symm
      obtain ⟨γ, hγ, hγδ⟩ := hbij.2.2 hδ'
      refine ⟨γ, hγ, ?_⟩
      rw [hι', hγδ]
      exact CFSG.LieType.Chevalley.ToralSign.permLattice_symm_permLattice (τ := Tag.D4) π.symm δ
  have hd4B : ∀ i j : Fin Tag.D4.rank, Tag.D4.symmetrizedCartan
      (π i)
      (π j) =
      Tag.D4.symmetrizedCartan i j := by
    intro i j
    simpa [Tag.symmetrizedCartan, Tag.symmetrizer] using hd4cartan i j
  have hiform' : ∀ γ ∈ Ψ, ∀ δ ∈ Ψ,
      CFSG.LieType.Steinberg.Adjoint.iform (ι' γ) (ι' δ) =
        CFSG.LieType.Steinberg.Adjoint.iform γ δ := by
    intro γ hγ δ hδ
    rw [hι', hι', CFSG.LieType.Chevalley.ToralSign.iform_permLattice
      (π := π) hd4B]
    exact hiform γ hγ δ hδ
  have hQroot : ∀ α : Fin Tag.D4.rank → ℤ, IsRoot Tag.D4 α →
      (rootSubgroup Tag.D4 GGL α).map (MulAut.conj Q).toMonoidHom =
        rootSubgroup Tag.D4 GGL (permLattice (τ := Tag.D4) π α) := by
    intro α hα
    exact CFSG.RankThree.Chevalley.map_conj_permModuleMap_rootSubgroup (τ := Tag.D4)
      (π := π) hd4cartan GGL hα
  have hroot' : ∀ γ ∈ Ψ, ∀ (y : ModGL τ GGL) (hy : y ∈ rootSpan τ GGL Ψ),
      y ∈ rootSubgroup τ GGL γ ↔
        (Ξ' ⟨y, hy⟩ : ModGL Tag.D4 GGL) ∈ rootSubgroup Tag.D4 GGL (ι' γ) := by
    intro γ hγ y hy
    rw [hrootOld γ hγ y hy, hcoe ⟨y, hy⟩]
    have hιroot : IsRoot Tag.D4 (ι γ) := hbij.1 hγ
    have hmap := hQroot (ι γ) hιroot
    have hiff : ∀ z : ModGL Tag.D4 GGL,
        Q * z * Q⁻¹ ∈ rootSubgroup Tag.D4 GGL (permLattice (τ := Tag.D4) π (ι γ)) ↔
          z ∈ rootSubgroup Tag.D4 GGL (ι γ) := by
      intro z
      rw [← hmap, Subgroup.mem_map]
      constructor
      · rintro ⟨z', hz', hzQ⟩
        have hzz' : z' = z :=
          (MulAut.conj Q).injective (by simpa [MulAut.conj_apply] using hzQ)
        simpa [hzz'] using hz'
      · intro hz
        exact ⟨z, hz, rfl⟩
    have hι'γ : ι' γ = permLattice (τ := Tag.D4) π (ι γ) := rfl
    rw [hι'γ]
    exact (hiff (Ξ ⟨y, hy⟩ : ModGL Tag.D4 GGL)).symm
  have htorus : ∀ b ∈ torusGroup τ GGL, ∃ t ∈ torusGroup Tag.D4 GGL,
      (∀ (y : ModGL τ GGL) (hy : y ∈ rootSpan τ GGL Ψ)
        (hby : b * y * b⁻¹ ∈ rootSpan τ GGL Ψ),
        (Ξ' ⟨b * y * b⁻¹, hby⟩ : ModGL Tag.D4 GGL) =
          t * (Ξ' ⟨y, hy⟩ : ModGL Tag.D4 GGL) * t⁻¹) ∧
      ∀ γ ∈ Ψ, rckRootVal t (ι' γ) = rckRootVal b γ := by
    intro b hb
    obtain ⟨t, ht, htact, htval⟩ := htorOld b hb
    have ht' : Q * t * Q⁻¹ ∈ torusGroup Tag.D4 GGL := by
      have h : Q * t * Q⁻¹ ∈ (torusGroup Tag.D4 GGL).map
          (MulAut.conj Q).toMonoidHom := Subgroup.mem_map_of_mem _ ht
      have h' : Q * t * Q⁻¹ ∈ (torusGroup Tag.D4 GGL).map
          (MulAut.conj (CFSG.RankThree.Chevalley.permModuleMap
            (τ := Tag.D4) hd4cartan GGL)).toMonoidHom := h
      rwa [CFSG.RankThree.Chevalley.map_conj_permModuleMap_torusGroup (τ := Tag.D4)
        (π := π) hd4cartan GGL] at h'
    refine ⟨Q * t * Q⁻¹, ht', ?_, ?_⟩
    · intro y hy hby
      rw [hcoe ⟨b * y * b⁻¹, hby⟩, hcoe ⟨y, hy⟩, htact y hy hby]
      group
    · intro γ hγ
      have hcoord : rckTorusCoord (Q * t * Q⁻¹) =
          fun i => rckTorusCoord t
            (π.symm i) := by
        apply CFSG.LieType.Chevalley.rootDiagUnit_injective
        rw [rck_rootDiagUnit_coord ht']
        rw [show Q * t * Q⁻¹ = Q * rootDiagUnit Tag.D4 (rckTorusCoord t) * Q⁻¹ by
          rw [rck_rootDiagUnit_coord ht]]
        change CFSG.RankThree.Chevalley.permModuleMap (τ := Tag.D4) hd4cartan GGL *
          rootDiagUnit Tag.D4 (rckTorusCoord t) *
          (CFSG.RankThree.Chevalley.permModuleMap (τ := Tag.D4) hd4cartan GGL)⁻¹ =
          rootDiagUnit Tag.D4 (fun i => rckTorusCoord t (π.symm i))
        exact permModuleMap_conj_rootDiagUnit (τ := Tag.D4) (π := π)
          hd4cartan (rckTorusCoord t)
      rw [← htval γ hγ]
      change rootChar (rckTorusCoord (Q * t * Q⁻¹))
          (permLattice (τ := Tag.D4) π
            (ι γ)) =
        rootChar (rckTorusCoord t) (ι γ)
      rw [hcoord]
      exact (rootChar_permLattice
        (b := fun i => rckTorusCoord t
          (π.symm i))
        π (ι γ)).trans
        (by simp)
  exact ⟨m', hm'mono, hm'C, ⟨hY, Ξ', ι', hstep, hbij', hiform', hroot', htorus⟩⟩

theorem rckTriD4PinnedFrameAt_canonical
    {τ : Tag} {p₀ : ℕ} {S : LangSetup τ GGL p₀} {Ψ : Set (Fin τ.rank → ℤ)} {h : ℕ} (hh : 1 ≤ h)
    {m : ModGL Tag.D4 GGL} (hm : m ∈ monomialSubgroup Tag.D4 GGL)
    (hfr : RCKTriD4PinnedFrameAt S Ψ h 1 m) :
    ∃ u : WeylGroup Tag.D4,
      RCKTriD4PinnedFrameAt S Ψ h 1 (canonicalRep (coxeterSystem Tag.D4) GGL u) := by
  classical
  obtain ⟨hY, Ξ, ι, hstepOld, hbij, hiform, hrootOld, htorOld⟩ := hfr
  obtain ⟨w, k, hk, hmk⟩ :=
    monomialSubgroup_le_torusWeylCosets (τ := Tag.D4) (R := GGL) hm
  let nu : ModGL Tag.D4 GGL := canonicalRep (coxeterSystem Tag.D4) GGL w
  have hnuNorm : nu ∈
      Subgroup.normalizer (torusGroup Tag.D4 GGL : Set (ModGL Tag.D4 GGL)) :=
    (canonical_weyl_root_transport Tag.D4 GGL).2.2 w
  let t0 : ModGL Tag.D4 GGL := nu⁻¹ * k * nu
  have ht0 : t0 ∈ torusGroup Tag.D4 GGL :=
    (Subgroup.mem_normalizer_iff.1 (inv_mem hnuNorm) k).1 hk
  have hm_decomp : m = nu * t0 := by
    rw [hmk]
    show k * nu = nu * t0
    rw [show t0 = nu⁻¹ * k * nu from rfl]
    group
  have hc : nu * t0 * nu⁻¹ ∈ torusGroup Tag.D4 GGL :=
    (Subgroup.mem_normalizer_iff.1 hnuNorm t0).1 ht0
  let P : ModGL Tag.D4 GGL := diagramMap TwistTag.D4 GGL
  let FrM : ModGL Tag.D4 GGL →* ModGL Tag.D4 GGL :=
    Units.map (entrywiseHom (iterateFrobenius GGL 2 h))
  have hQ : nu * P ∈
      Subgroup.normalizer (torusGroup Tag.D4 GGL : Set (ModGL Tag.D4 GGL)) :=
    mul_mem hnuNorm (diagramMap_mem_normalizer (t := TwistTag.D4) (k := GGL))
  have : Fact (2 : ℕ).Prime := ⟨Nat.prime_two⟩
  have : CharP GGL 2 := inferInstance
  obtain ⟨s, hsT, hsLang⟩ :=
    kgLang_torusGroup_lang (τ := Tag.D4) (L := GGL) (ℓ := 2) (e := h) hh
      (Q := nu * P) hQ (nu * t0 * nu⁻¹) hc
  have hsM : s * m = nu * P * FrM s * P⁻¹ := by
    rw [hm_decomp]
    have hfrob : frobTwistGL Tag.D4 GGL 2 h (nu * P) s =
        (nu * P) * FrM s * (nu * P)⁻¹ :=
      frobTwistGL_apply (τ := Tag.D4) (L := GGL) (p := 2) (e := h) (Q := nu * P) (g := s)
    rw [hfrob] at hsLang
    calc s * (nu * t0) = s * (nu * t0 * nu⁻¹) * nu := by group
      _ = s * (s⁻¹ * ((nu * P) * FrM s * (nu * P)⁻¹)) * nu := by rw [← hsLang]
      _ = nu * P * FrM s * P⁻¹ := by group
  have hsA : s ∈ adjointGroup Tag.D4 GGL :=
    (torusGroup_le_adjointGroup (τ := Tag.D4) (k := GGL)) hsT
  let Ξ' : ↥(rootSpan τ GGL Ψ) ≃* ↥(adjointGroup Tag.D4 GGL) :=
    Ξ.trans (MulAut.conj ⟨s, hsA⟩)
  have hcoe : ∀ x : ↥(rootSpan τ GGL Ψ),
      (Ξ' x : ModGL Tag.D4 GGL) = s * (Ξ x : ModGL Tag.D4 GGL) * s⁻¹ := fun _ => rfl
  have hstep : ∀ (y : ModGL τ GGL) (hy : y ∈ rootSpan τ GGL Ψ),
      (Ξ' ⟨S.D.step y, hY y hy⟩ : ModGL Tag.D4 GGL) =
        nu * triPsi h 1 (Ξ' ⟨y, hy⟩ : ModGL Tag.D4 GGL) * nu⁻¹ := by
    intro y hy
    rw [hcoe ⟨S.D.step y, hY y hy⟩, hcoe ⟨y, hy⟩, hstepOld y hy]
    exact rckRP_conj_step_one (F := FrM) hsM
  refine ⟨w, ?_⟩
  refine ⟨hY, Ξ', ι, hstep, hbij, hiform, ?_, ?_⟩
  · intro γ hγ y hy
    rw [hrootOld γ hγ y hy, hcoe ⟨y, hy⟩]
    exact (Subgroup.mem_normalizer_iff.1
      ((torusGroup_le_normalizer_rootSubgroup (R := GGL) (α := ι γ) (hbij.1 hγ)) hsT) _)
  · intro b hb
    obtain ⟨t, ht, htact, htval⟩ := htorOld b hb
    refine ⟨t, ht, ?_, htval⟩
    intro y hy hby
    rw [hcoe ⟨b * y * b⁻¹, hby⟩, hcoe ⟨y, hy⟩, htact y hy hby]
    have hst : s * t = t * s := CFSG.RankThree.PartOne.KE.torusGroup_comm hsT ht
    calc s * (t * (Ξ ⟨y, hy⟩ : ModGL Tag.D4 GGL) * t⁻¹) * s⁻¹
        = (s * t) * ((Ξ ⟨y, hy⟩ : ModGL Tag.D4 GGL) * (s * t)⁻¹) := by group
      _ = (t * s) * ((Ξ ⟨y, hy⟩ : ModGL Tag.D4 GGL) * (t * s)⁻¹) := by rw [hst]
      _ = t * (s * (Ξ ⟨y, hy⟩ : ModGL Tag.D4 GGL) * s⁻¹) * t⁻¹ := by group

theorem exists_retSetup_of_pinnedFrame
    {τ : Tag} {p₀ : ℕ} {S : LangSetup τ GGL p₀} {Ψ : Set (Fin τ.rank → ℤ)} {h : ℕ} (hh : 1 ≤ h)
    (hfr : RCKTriD4PinnedFrame S Ψ h) (hA : RCKTriD4Model h) :
    ∃ SK : LangSetup Tag.D4 GGL 5, SK.D.q = 2 ^ h ∧ SK.D.Φ = triPsi h 1 ∧
      RCKTriD4PinnedFrameAt S Ψ h 1 SK.D.n := by
  classical
  obtain ⟨r, m, hr, hm, hmC, hfrA⟩ := hfr
  obtain ⟨m₁, hm₁, hfr₁⟩ : ∃ m : ModGL Tag.D4 GGL,
      m ∈ monomialSubgroup Tag.D4 GGL ∧ RCKTriD4PinnedFrameAt S Ψ h 1 m := by
    rcases hr with rfl | rfl
    · exact ⟨m, hm, hfrA⟩
    · obtain ⟨m', hm', -, hfr'⟩ := rckTriD4PinnedFrameAt_two hm hmC hfrA
      exact ⟨m', hm', hfr'⟩
  obtain ⟨u, hfrU⟩ := rckTriD4PinnedFrameAt_canonical hh hm₁ hfr₁
  obtain ⟨F, hF, hFin, σ, hTri, ιA, β₀, hιA, hιArange, hβ₀, hβ₀long, hβ₀pos, hβ₀neg⟩ := hA
  have : Fact (2 : ℕ).Prime := ⟨Nat.prime_two⟩
  have hchar : CharP GGL 2 := inferInstance
  let nu : ModGL Tag.D4 GGL := canonicalRep (coxeterSystem Tag.D4) GGL u
  have hnuC : nu ∈ adjointGroup Tag.D4 GGL := canonicalRep_mem_adjointGroup _ _ u
  obtain ⟨g0, hg0C, hg0⟩ :=
    CFSG.RankThree.PartOne.KGD.lang_conjugator_D4 (K := ZMod 2) (ℓ := 2) (f := h) hh
      GGL nu hnuC
  let Fr : GGL →+* GGL := iterateFrobenius GGL 2 h
  have hFr : ∀ c, Fr c = c ^ 2 ^ h := fun c => iterateFrobenius_def 2 h c
  let D : LangDatum Tag.D4 GGL := LangDatum.ofTwist TwistTag.D4 Fr (2 ^ h) hFr u hg0C hg0
  have hDΦ : D.Φ = triPsi h 1 := rfl
  have hDq : D.q = 2 ^ h := rfl
  have hDn : D.n = nu := rfl
  have hfix : D.fix = ιA.range := by
    rw [hιArange]
    rfl
  let : Field F := hF
  let : Finite F := hFin
  have hfinGL : Finite (ModGL Tag.D4 F) := CFSG.LieType.Chevalley.finite_modGL
  have hfinK : Finite (triD4Universal F σ).K := Subtype.finite
  have hFixFinite : Finite D.fix := by
    rw [hfix]
    exact Finite.of_equiv _ (MonoidHom.ofInjective hιA).toEquiv
  have hModelFinite : Finite D.model := by
    have : Finite D.fix := hFixFinite
    refine Finite.of_injective
      (fun x : D.model => (⟨D.g0 * (x : ModGL Tag.D4 GGL) * D.g0⁻¹, ?_⟩ : D.fix))
      (fun x y hxy => ?_)
    · have hx : D.g0 * (x : ModGL Tag.D4 GGL) * D.g0⁻¹ ∈
          D.model.map (MulAut.conj D.g0).toMonoidHom :=
        Subgroup.mem_map_of_mem _ x.2
      rwa [D.map_conj_model] at hx
    · have h : D.g0 * (x : ModGL Tag.D4 GGL) * D.g0⁻¹ =
          D.g0 * (y : ModGL Tag.D4 GGL) * D.g0⁻¹ := congrArg Subtype.val hxy
      exact Subtype.ext ((MulAut.conj D.g0).injective (by simpa [MulAut.conj_apply] using h))
  obtain ⟨ρ, hρ⟩ := frobeniusOnRoots_proved Tag.D4 GGL D
  have hqpow : IsPrimePow (2 ^ h) ∧ ((2 ^ h : ℕ) : GGL) = 0 := by
    constructor
    · exact Nat.prime_two.isPrimePow.pow (by omega)
    · rw [Nat.cast_pow]
      have h2 : ((2 : ℕ) : GGL) = 0 := CharP.cast_eq_zero GGL 2
      rw [h2]
      exact zero_pow (by omega)
  have hpq : ¬ 5 ∣ 2 ^ h := fun h5 => by
    have h52 : 5 ∣ 2 := Nat.prime_five.dvd_of_dvd_pow h5
    norm_num at h52
  let SK : LangSetup Tag.D4 GGL 5 :=
    D.toSetup 5 ρ hρ Nat.prime_five (Or.inl le_rfl) hqpow hpq hModelFinite
  exact ⟨SK, hDq, hDΦ, hfrU⟩


end CFSG.StandardType.RCKRP

end
