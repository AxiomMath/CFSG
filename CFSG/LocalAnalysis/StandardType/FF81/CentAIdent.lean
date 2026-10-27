module

public import CFSG.LocalAnalysis.StandardType.FF81.CentAModelBeta
public import CFSG.LocalAnalysis.StandardType.FF81.CentAIdentPair
public import CFSG.LocalAnalysis.StandardType.FF81.Defs
import CFSG.LocalAnalysis.StandardType.FF81.RootFusionLin
import CFSG.Adapters.SpecialLinearPerfect
import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotFieldNormalize
import TauCeti.GroupTheory.Commutator
import CFSG.Assembly.OrderReductions.InvertedSubgroup
import CFSG.Assembly.OrderReductions.OddInversion
import CFSG.CharacterTheory.Semidihedral.OddFieldLift
import CFSG.LieType.Chevalley.C2E6StandardFixedData
import CFSG.LieType.Chevalley.C2E6SubsystemBruhat
import CFSG.LieType.Chevalley.C2E6UnitaryFourImages
import CFSG.LieType.Chevalley.E6SecondGraphFullCentralizer
import CFSG.LieType.Chevalley.SimplyLacedFieldTwoCover
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGraphFieldArithmetic
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGraphFieldUnitaryData
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenCanonicalField
import CFSG.LocalAnalysis.ComponentInitial.CentralCoverAbelian
import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
import CFSG.LocalAnalysis.ComponentInitial.SylowPointRecovery
import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
import CFSG.LocalAnalysis.SectionRank.TitsCover
import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotLeviFactFour
import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotSetup
import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
import CFSG.Quasithin.Background.A3Components
import CFSG.Quasithin.Background.A3ComponentsAmbient
import CFSG.Quasithin.Background.G11Stmts
import CFSG.RankThree.PartOne.KC.OrthogonalAutSemilinearBridge
import CFSG.Sporadic.J4.Simple
import CFSG.Sporadic.J4Base
import CFSG.Sporadic.Mathieu.M24
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
import CFSG.Walter.JRFacts

public section

namespace CFSG.StandardType.FF81.CentA

open Matrix RootFusionLin
open scoped commutatorElement
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)
open CFSG.StandardType.FrameRoute.FS81 (IsSylow2In)

private noncomputable def caIdent_idx (n : ℕ) : BlkIdx 1 (n + 1) ≃ Fin (n + 3) :=
  (Equiv.sumComm (Fin 1) (Fin (n + 1) ⊕ Fin 1)).trans
    ((Equiv.sumCongr
        ((Equiv.sumComm (Fin (n + 1)) (Fin 1)).trans finSumFinEquiv)
        (Equiv.refl (Fin 1))).trans
      (finSumFinEquiv.trans (finCongr (by omega))))

private theorem caIdent_idx_inl (n : ℕ) (i : Fin 1) :
    caIdent_idx n (.inl i) = (⟨n + 2 + i.1, by omega⟩ : Fin (n + 3)) := by
  obtain rfl : i = 0 := Subsingleton.elim i 0
  simp [caIdent_idx, Fin.natAdd]
  omega

private theorem caIdent_idx_B (n : ℕ) (j : Fin (n + 1)) :
    caIdent_idx n (.inr (.inl j)) = (⟨1 + j.1, by omega⟩ : Fin (n + 3)) := by
  simp [caIdent_idx]
  ext
  simp

private theorem caIdent_idx_C (n : ℕ) (i : Fin 1) :
    caIdent_idx n (.inr (.inr i)) = (⟨i.1, by omega⟩ : Fin (n + 3)) := by
  simp [caIdent_idx]
  ext
  simp

private theorem caIdent_reindex_jGL (n : ℕ) :
    (Matrix.reindexAlgEquiv (ZMod 2) (ZMod 2) (caIdent_idx n))
        ((jGL 1 (n + 1) : GL (BlkIdx 1 (n + 1)) (ZMod 2)) :
          Matrix (BlkIdx 1 (n + 1)) (BlkIdx 1 (n + 1)) (ZMod 2)) =
      ((jN (n + 3) 1 : GL (Fin (n + 3)) (ZMod 2)) :
        Matrix (Fin (n + 3)) (Fin (n + 3)) (ZMod 2)) := by
  ext a b
  obtain ⟨a', rfl⟩ := (caIdent_idx n).surjective a
  obtain ⟨b', rfl⟩ := (caIdent_idx n).surjective b
  rw [Matrix.coe_reindexAlgEquiv, Matrix.reindex_apply, Matrix.submatrix_apply,
    Equiv.symm_apply_apply, Equiv.symm_apply_apply]
  rcases a' with i | j | i <;> rcases b' with j' | j' | i' <;>
    simp only [jGL, uGL, uMat, blk, Matrix.of_apply, jN,
      Matrix.SpecialLinearGroup.coe_GL_coe_matrix, CFSG.StandardType.coe_ggInvSL,
      CFSG.StandardType.ggInvMatrix, CFSG.StandardType.ggInvNil_apply, Matrix.add_apply,
      Matrix.one_apply, caIdent_idx_inl, caIdent_idx_B, caIdent_idx_C]
  all_goals (split_ifs <;> simp_all <;> omega)

private noncomputable def caIdent_reindexGL (n : ℕ) :
    GL (Fin (n + 3)) (ZMod 2) ≃* GL (BlkIdx 1 (n + 1)) (ZMod 2) :=
  Units.mapEquiv (Matrix.reindexAlgEquiv (ZMod 2) (ZMod 2) (caIdent_idx n)).symm

private theorem caIdent_reindexGL_jN (n : ℕ) :
    caIdent_reindexGL n (jN (n + 3) 1) = jGL 1 (n + 1) := by
  apply Units.ext
  rw [caIdent_reindexGL, Units.coe_mapEquiv, ← caIdent_reindex_jGL n]
  exact (Matrix.reindexAlgEquiv (ZMod 2) (ZMod 2) (caIdent_idx n)).symm_apply_apply _

private theorem caIdent_levi_mem_suppGL (m : ℕ) (R : GL (Fin m) (ZMod 2)) :
    leviOne m R ∈ CFSG.SeitzReduction.SymplecticPilot.suppGL (ZMod 2)
      ({i : BlkIdx 1 m | i ≠ Sum.inl 0 ∧ i ≠ Sum.inr (Sum.inr 0)}) := by
  rw [CFSG.SeitzReduction.SymplecticPilot.mem_suppGL]
  intro a b hab
  change (levi (1 : GL (Fin 1) (ZMod 2)) R :
      Matrix (BlkIdx 1 m) (BlkIdx 1 m) (ZMod 2)) a b =
    (1 : Matrix (BlkIdx 1 m) (BlkIdx 1 m) (ZMod 2)) a b
  rw [coe_levi]
  rcases a with i | j | i <;> rcases b with j' | j' | i'
  · simp [blk, Matrix.one_apply]
  · simp [blk, Matrix.one_apply]
  · simp [blk, Matrix.one_apply]
  · simp [blk, Matrix.one_apply]
  · exact absurd ⟨⟨by simp, by simp⟩, ⟨by simp, by simp⟩⟩ hab
  · simp [blk, Matrix.one_apply]
  · simp [blk, Matrix.one_apply]
  · simp [blk, Matrix.one_apply]
  · simp [blk, Matrix.one_apply]

private theorem caIdent_blockMat_apply_of_not {m : ℕ} (A : Matrix (Fin 2) (Fin 2) (ZMod 2))
    {a b : BlkIdx 1 m}
    (h : ¬((a = Sum.inl 0 ∨ a = Sum.inr (Sum.inr 0)) ∧
      (b = Sum.inl 0 ∨ b = Sum.inr (Sum.inr 0)))) :
    CFSG.LieType.Steinberg.Sp.blockMat (Sum.inl 0) (Sum.inr (Sum.inr 0)) A a b =
      (1 : Matrix (BlkIdx 1 m) (BlkIdx 1 m) (ZMod 2)) a b := by
  rw [not_and_or] at h
  rw [CFSG.LieType.Steinberg.Sp.blockMat, Matrix.of_apply]
  rcases h with h | h
  · rw [not_or] at h
    simp [h.1, h.2]
  · rw [not_or] at h
    obtain ⟨hb1, hb2⟩ := h
    by_cases ha1 : a = Sum.inl 0
    · subst ha1
      simp [hb1, hb2, Ne.symm hb1, Ne.symm hb2, Matrix.one_apply]
    · by_cases ha2 : a = Sum.inr (Sum.inr 0)
      · subst ha2
        simp [hb1, hb2, Ne.symm hb1, Ne.symm hb2, Matrix.one_apply]
      · simp [ha1, ha2]

private theorem caIdent_betaStd_mem_suppGL (m : ℕ) :
    betaStd m ∈ CFSG.SeitzReduction.SymplecticPilot.suppGL (ZMod 2)
      ({Sum.inl 0, Sum.inr (Sum.inr 0)} : Set (BlkIdx 1 m)) := by
  rw [CFSG.SeitzReduction.SymplecticPilot.mem_suppGL]
  intro a b hab
  have hmat : (betaStd m : Matrix (BlkIdx 1 m) (BlkIdx 1 m) (ZMod 2)) =
      CFSG.LieType.Steinberg.Sp.blockMat (Sum.inl 0) (Sum.inr (Sum.inr 0))
        (betaTwo : Matrix (Fin 2) (Fin 2) (ZMod 2)) := by
    rw [betaStd, coe_pairGL]
  rw [hmat]
  exact caIdent_blockMat_apply_of_not _ (by simpa using hab)

private theorem caIdent_commute_levi_betaStd (m : ℕ) (R : GL (Fin m) (ZMod 2)) :
    Commute (leviOne m R) (betaStd m) := by
  have hdisj : Disjoint ({Sum.inl 0, Sum.inr (Sum.inr 0)} : Set (BlkIdx 1 m))
      {i : BlkIdx 1 m | i ≠ Sum.inl 0 ∧ i ≠ Sum.inr (Sum.inr 0)} := by
    rw [Set.disjoint_left]
    intro x hx hx'
    rcases hx with rfl | rfl
    · exact hx'.1 rfl
    · exact hx'.2 rfl
  exact CFSG.SeitzReduction.OmegaPilot.commute_of_mem_suppGL_of_disjoint hdisj.symm
    (caIdent_levi_mem_suppGL m R) (caIdent_betaStd_mem_suppGL m)

private theorem caIdent_commutator_mul_mul {Γ : Type*} [Group Γ] {a₁ a₂ z₁ z₂ : Γ}
    (h₁ : Commute a₁ z₁) (h₂ : Commute a₂ z₁) (h₃ : Commute a₁ z₂) (h₄ : Commute a₂ z₂)
    (h₅ : Commute z₁ z₂) :
    ⁅a₁ * z₁, a₂ * z₂⁆ = ⁅a₁, a₂⁆ := by
  have hz : ⁅z₁, z₂⁆ = 1 := h₅.commutator_eq
  have h := TauCeti.commutatorElement_mul_mul_eq_mul_of_commute (a := a₁) (b := z₁)
    (c := a₂) (d := z₂) h₂.symm h₃
    (by rw [hz]; exact Commute.one_right _)
    (by rw [hz]; exact Commute.one_right _)
    (by rw [hz]; exact Commute.one_right _)
  rw [hz, mul_one] at h
  exact h

private theorem caIdent_card_leviB (m : ℕ) :
    Nat.card ↥(leviB m) = Nat.card (GL (Fin m) (ZMod 2)) := by
  change Nat.card ↥((leviOne m).range) = Nat.card (GL (Fin m) (ZMod 2))
  have h := Subgroup.card_map_of_injective (K := (⊤ : Subgroup (GL (Fin m) (ZMod 2))))
    (f := leviOne m) (leviOne_injective m)
  rw [Subgroup.map_top] at h
  rw [h, Nat.card_congr Subgroup.topEquiv.toEquiv]

private theorem caIdent_commutator_sup_le_leviB (m : ℕ) :
    ⁅leviB m ⊔ Subgroup.zpowers (betaStd m), leviB m ⊔ Subgroup.zpowers (betaStd m)⁆ ≤
      leviB m := by
  have hAB : ∀ a ∈ leviB m, ∀ z ∈ Subgroup.zpowers (betaStd m), z * a = a * z := by
    rintro a ⟨R, rfl⟩ z hz
    have hcommR : Commute (leviOne m R) (betaStd m) := caIdent_commute_levi_betaStd m R
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    exact (hcommR.symm.zpow_left k).eq
  have hBnorm : Subgroup.zpowers (betaStd m) ≤ Subgroup.normalizer (leviB m : Set _) := by
    refine (show Subgroup.zpowers (betaStd m) ≤
      Subgroup.centralizer (leviB m : Set _) from ?_).trans
      (Subgroup.centralizer_le_normalizer _)
    intro z hz
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    exact (hAB a ha z hz).symm
  rw [Subgroup.commutator_le]
  intro x hx y hy
  have hx' : x ∈ ((leviB m ⊔ Subgroup.zpowers (betaStd m) : Subgroup _) : Set _) := hx
  have hy' : y ∈ ((leviB m ⊔ Subgroup.zpowers (betaStd m) : Subgroup _) : Set _) := hy
  rw [Subgroup.coe_mul_of_right_le_normalizer_left (leviB m) (Subgroup.zpowers (betaStd m))
    hBnorm] at hx' hy'
  obtain ⟨a₁, ha₁, z₁, hz₁, rfl⟩ := Set.mem_mul.mp hx'
  obtain ⟨a₂, ha₂, z₂, hz₂, rfl⟩ := Set.mem_mul.mp hy'
  have h₁ : Commute a₁ z₁ := (hAB a₁ ha₁ z₁ hz₁).symm
  have h₂ : Commute a₂ z₁ := (hAB a₂ ha₂ z₁ hz₁).symm
  have h₃ : Commute a₁ z₂ := (hAB a₁ ha₁ z₂ hz₂).symm
  have h₄ : Commute a₂ z₂ := (hAB a₂ ha₂ z₂ hz₂).symm
  have h₅ : Commute z₁ z₂ := by
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz₁
    obtain ⟨l, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz₂
    exact ((Commute.refl (betaStd m)).zpow_left k).zpow_right l
  rw [caIdent_commutator_mul_mul h₁ h₂ h₃ h₄ h₅]
  exact Subgroup.commutator_le_self (leviB m) (Subgroup.commutator_mem_commutator ha₁ ha₂)

theorem exists_blockModel {G : Type} [Group G] [Finite G] {n : ℕ} (hn : n = 5 ∨ n = 6)
    {Y L : Subgroup G} {b t : G} (hY : StatedClassicalModel ↥Y .PSL (n + 3) 2 1)
    (hL : StatedClassicalModel ↥L .PSL (n + 1) 2 1) (htY : t ∈ Y) (hbY : b ∈ Y) (hLY : L ≤ Y)
    (hb : orderOf b = 3) (ht : orderOf t = 2) (hinv : t * b * t⁻¹ = b⁻¹)
    (hcen : Subgroup.centralizer ({b} : Set G) ⊓ Y = Subgroup.zpowers b ⊔ L)
    (hsyl : ∃ S : Subgroup G, IsSylow2In S Y ∧ t ∈ S ∧ ∀ s ∈ S, s * t = t * s) :
    ∃ φ : ↥Y ≃* GL (BlkIdx 1 (n + 1)) (ZMod 2), φ ⟨t, htY⟩ = jGL 1 (n + 1) ∧
      φ ⟨b, hbY⟩ = betaStd (n + 1) ∧ ∀ y : ↥Y, (y : G) ∈ L ↔ φ y ∈ leviB (n + 1) := by
  obtain ⟨φ₀⟩ := CFSG.Open.StatedAPI.nonempty_mulEquiv_specialLinear_zmod_two_of_psl hY
  obtain ⟨φY⟩ := nonempty_mulEquiv_gl_of_sl (n := n + 3) ⟨φ₀⟩
  obtain ⟨S, hS, htS, hcommS⟩ := hsyl
  obtain ⟨S', hS'p, hS'max, hS'mem⟩ := exists_maximal_pGroup_of_isSylow2In hS φY
  have hordφt : orderOf (φY ⟨t, htY⟩) = 2 := by
    have h := orderOf_injective φY.toMonoidHom φY.injective ⟨t, htY⟩
    have h2 : orderOf (⟨t, htY⟩ : ↥Y) = 2 := by
      rw [← Subgroup.orderOf_coe]
      simpa using ht
    exact h.trans h2
  have hconj : IsConj (jN (n + 3) 1) (φY ⟨t, htY⟩) := by
    refine isConj_jN_one_of_central_in_sylow (n + 3) (by omega) S' hS'p hS'max
      (φY ⟨t, htY⟩) ((hS'mem ⟨t, htY⟩).2 htS) hordφt ?_
    intro s hs
    obtain ⟨y, rfl⟩ := φY.surjective s
    have hy : (y : G) ∈ S := (hS'mem y).1 hs
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hcommS (y : G) hy)
  obtain ⟨c, hc⟩ := isConj_iff.mp hconj
  have hψ₁ : (φY.trans (MulAut.conj c⁻¹)) ⟨t, htY⟩ = jN (n + 3) 1 := by
    rw [MulEquiv.trans_apply, MulAut.conj_apply, inv_inv, ← hc]
    group
  set ψ : ↥Y ≃* GL (BlkIdx 1 (n + 1)) (ZMod 2) :=
    (φY.trans (MulAut.conj c⁻¹)).trans (caIdent_reindexGL n) with hψdef
  have hψt : ψ ⟨t, htY⟩ = jGL 1 (n + 1) := by
    rw [hψdef, MulEquiv.trans_apply, hψ₁, caIdent_reindexGL_jN]
  set β : GL (BlkIdx 1 (n + 1)) (ZMod 2) := ψ ⟨b, hbY⟩ with hβdef
  have hβord : orderOf β = 3 := by
    rw [hβdef]
    have h := orderOf_injective ψ.toMonoidHom ψ.injective ⟨b, hbY⟩
    have h2 : orderOf (⟨b, hbY⟩ : ↥Y) = 3 := by
      rw [← Subgroup.orderOf_coe]
      simpa using hb
    exact h.trans h2
  have hJβ : jGL 1 (n + 1) * β * (jGL 1 (n + 1))⁻¹ = β⁻¹ := by
    rw [hβdef]
    have hinvY : (⟨t, htY⟩ : ↥Y) * ⟨b, hbY⟩ * (⟨t, htY⟩)⁻¹ = (⟨b, hbY⟩ : ↥Y)⁻¹ := by
      apply Subtype.ext
      simpa using hinv
    have h := congrArg ψ hinvY
    simpa only [map_mul, map_inv, hψt] using h
  obtain ⟨g, hgCent, hgβ⟩ := exists_cent_conj_betaStd β hβord hJβ
  have hgJ : g * jGL 1 (n + 1) * g⁻¹ = jGL 1 (n + 1) := by
    have h : g ∈ Subgroup.centralizer
        ({jGL 1 (n + 1)} : Set (GL (BlkIdx 1 (n + 1)) (ZMod 2))) := hgCent
    have h2 := Subgroup.mem_centralizer_singleton_iff.mp h
    rw [h2]
    group
  set φ : ↥Y ≃* GL (BlkIdx 1 (n + 1)) (ZMod 2) := ψ.trans (MulAut.conj g) with hφdef
  have hφt : φ ⟨t, htY⟩ = jGL 1 (n + 1) := by
    rw [hφdef, MulEquiv.trans_apply, MulAut.conj_apply, hψt, hgJ]
  have hφb : φ ⟨b, hbY⟩ = betaStd (n + 1) := by
    rw [hφdef, MulEquiv.trans_apply, MulAut.conj_apply, ← hβdef]
    exact hgβ
  have hLle_cent : L ≤ Subgroup.centralizer ({b} : Set G) := by
    intro x hx
    have hx' : x ∈ Subgroup.centralizer ({b} : Set G) ⊓ Y := by
      rw [hcen]
      exact Subgroup.mem_sup_right hx
    exact hx'.1
  obtain ⟨eL⟩ := CFSG.Open.StatedAPI.nonempty_mulEquiv_specialLinear_zmod_two_of_psl hL
  obtain ⟨eLG⟩ := nonempty_mulEquiv_gl_of_sl (n := n + 1) ⟨eL⟩
  have hperfL : Group.IsPerfect ↥L := by
    have hSL : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin (n + 1)) (ZMod 2)) :=
      CFSG.ClassicalModels.specialLinear_isPerfect_of_three_le (K := ZMod 2) (n := n + 1)
        (by omega)
    haveI := hSL
    exact Group.IsPerfect.ofSurjective (f := eL.symm.toMonoidHom) eL.symm.surjective
  set LY : Subgroup ↥Y := L.subgroupOf Y with hLYdef
  have hLcomm : ∀ y ∈ LY,
      φ y ∈ leviB (n + 1) ⊔ Subgroup.zpowers (betaStd (n + 1)) := by
    intro y hy
    have hyL : (y : G) ∈ L := by
      rw [hLYdef, Subgroup.mem_subgroupOf] at hy
      exact hy
    have hyb : (⟨b, hbY⟩ : ↥Y) * y = y * ⟨b, hbY⟩ := by
      apply Subtype.ext
      exact (Subgroup.mem_centralizer_singleton_iff.mp (hLle_cent hyL)).symm
    have hψbψ : ψ ⟨b, hbY⟩ * ψ y = ψ y * ψ ⟨b, hbY⟩ := by
      simpa only [map_mul] using congrArg ψ hyb
    have hcomm : φ y * betaStd (n + 1) = betaStd (n + 1) * φ y := by
      rw [← hφb]
      simp only [hφdef, MulEquiv.trans_apply, MulAut.conj_apply]
      rw [← hβdef]
      calc g * ψ y * g⁻¹ * (g * β * g⁻¹) = g * (ψ y * β) * g⁻¹ := by group
        _ = g * (β * ψ y) * g⁻¹ := by rw [hψbψ]
        _ = g * β * g⁻¹ * (g * ψ y * g⁻¹) := by group
    rw [← centralizer_betaStd (n + 1)]
    exact Subgroup.mem_centralizer_singleton_iff.mpr hcomm
  have hKM : LY.map φ.toMonoidHom ≤
      leviB (n + 1) ⊔ Subgroup.zpowers (betaStd (n + 1)) := by
    rintro x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    exact hLcomm y hy
  have hperfLY : Group.IsPerfect ↥LY := by
    rw [hLYdef]
    haveI := hperfL
    exact Group.IsPerfect.ofSurjective
      (f := (Subgroup.subgroupOfEquivOfLe hLY).symm.toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hLY).symm.surjective
  have hperfK : Group.IsPerfect ↥(LY.map φ.toMonoidHom) := by
    haveI := hperfLY
    exact Group.IsPerfect.ofSurjective
      (f := (φ.subgroupMap LY).toMonoidHom) (φ.subgroupMap LY).surjective
  have hKcomm : ⁅LY.map φ.toMonoidHom, LY.map φ.toMonoidHom⁆ = LY.map φ.toMonoidHom :=
    Subgroup.isPerfect_iff.mp hperfK
  have hcommM : ⁅leviB (n + 1) ⊔ Subgroup.zpowers (betaStd (n + 1)),
      leviB (n + 1) ⊔ Subgroup.zpowers (betaStd (n + 1))⁆ ≤ leviB (n + 1) :=
    caIdent_commutator_sup_le_leviB (n + 1)
  have hKleL0 : LY.map φ.toMonoidHom ≤ leviB (n + 1) := by
    rw [← hKcomm]
    exact (Subgroup.commutator_mono hKM hKM).trans hcommM
  have hcardK : Nat.card ↥(LY.map φ.toMonoidHom) = Nat.card ↥L := by
    rw [Subgroup.card_map_of_injective (f := φ.toMonoidHom) φ.injective (K := LY)]
    rw [hLYdef]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hLY).toEquiv
  have hcardL : Nat.card ↥L = Nat.card (GL (Fin (n + 1)) (ZMod 2)) :=
    Nat.card_congr eLG.toEquiv
  have hcardLevi : Nat.card ↥(leviB (n + 1)) = Nat.card (GL (Fin (n + 1)) (ZMod 2)) :=
    caIdent_card_leviB (n + 1)
  have hEqK : LY.map φ.toMonoidHom = leviB (n + 1) := by
    refine Subgroup.eq_of_le_of_card_ge hKleL0 ?_
    rw [hcardLevi, hcardK, hcardL]
  refine ⟨φ, hφt, hφb, ?_⟩
  intro y
  have hy : ((y : G) ∈ L) ↔ y ∈ LY := by
    rw [hLYdef, Subgroup.mem_subgroupOf]
  rw [hy, ← hEqK]
  constructor
  · intro h
    exact Subgroup.mem_map.mpr ⟨y, h, rfl⟩
  · rintro ⟨z, hz, hzy⟩
    rwa [φ.injective hzy] at hz

end CFSG.StandardType.FF81.CentA

end
