module

public import CFSG.GH74.GLS.IVK.Proofs2.Std44
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps6L3Facts
import CFSG.ClassicalInvolution.ModelFacts.Orth15ChainL
import CFSG.LocalAnalysis.ComponentInitial.SteinbergBUProjectivePlaneLinearField
import CFSG.LocalAnalysis.ComponentInitial.LinearHigherConjAutInner
import CFSG.LocalAnalysis.ComponentInitial.LinearCoverModel
import CFSG.GroupTheory.MulAutCongr
public import CFSG.ClassicalInvolution.Models.LinearPairs.RootSL2
public import CFSG.GH74.GLS.IVK.L2.Fixed

public section

namespace CFSG.LocalAnalysis.WeakClosure81.Asch6

open Subgroup CFSG.Open
open CFSG.GH74.GLS.IVK.Proofs2 (linU₀)
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.LocalAnalysis.ComponentInitial.ProjectivePlane
open CFSG.ClassicalInvolution.Models
open scoped MatrixGroups

variable {F : Type} [Field F] [Finite F]

private theorem mulAut_congr_apply_apply {X P : Type*} [Group X] [Group P] (e : X ≃* P)
    (β : MulAut X) (x : X) : (MulAut.congr e) β (e x) = e (β x) := by
  simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]

private theorem mulAut_congr_symm_conj {X P : Type*} [Group X] [Group P] (e : X ≃* P) (y : P) :
    (MulAut.congr e).symm (MulAut.conj y) = MulAut.conj (e.symm y) := by
  have h := mulAut_congr_conj e (e.symm y)
  simp only [MulEquiv.apply_symm_apply] at h
  rw [← h, MulEquiv.symm_apply_apply]

private theorem map_centralizer_eq {G H : Type*} [Group G] [Group H] (e : G ≃* H) (S : Set G) :
    (Subgroup.centralizer S).map e.toMonoidHom = Subgroup.centralizer (e '' S) := by
  refine le_antisymm (Subgroup.map_centralizer_le_centralizer_image S e.toMonoidHom) ?_
  intro y hy
  refine Subgroup.mem_map.mpr ⟨e.symm y, ?_, e.apply_symm_apply y⟩
  rw [Subgroup.mem_centralizer_iff] at hy ⊢
  intro s hs
  have h1 := hy (e s) (Set.mem_image_of_mem e hs)
  simpa using congrArg e.symm h1

omit [Finite F] in
private theorem conj_proj (s g : Matrix.SpecialLinearGroup (Fin 3) F) :
    MulAut.conj (proj 3 F s) (proj 3 F g) = proj 3 F (s * g * s⁻¹) := by
  rw [MulAut.conj_apply, ← map_mul, ← map_inv, ← map_mul]

private theorem exists_ne_one_of_card_four {G : Type*} [Group G] [Finite G] (B : Subgroup G)
    (hB : Nat.card B = 4) : ∃ b ∈ B, b ≠ 1 := by
  have : Fintype B := Fintype.ofFinite _
  have hnt : Nontrivial B := by
    rw [← Finite.one_lt_card_iff_nontrivial, hB]
    norm_num
  obtain ⟨⟨b, hb⟩, hb1⟩ := exists_ne (1 : B)
  exact ⟨b, hb, fun h => hb1 (Subtype.ext h)⟩

private theorem exists_second_ne_one_of_card_four {G : Type*} [Group G] [Finite G]
    {B : Subgroup G} (hB : Nat.card B = 4) {b : G} (hb : b ∈ B) (_hb1 : b ≠ 1) :
    ∃ b' ∈ B, b' ≠ 1 ∧ b' ≠ b := by
  classical
  have : Fintype B := Fintype.ofFinite _
  by_contra hcon
  push Not at hcon
  have hsub : (Finset.univ : Finset B) ⊆ ({1, ⟨b, hb⟩} : Finset B) := by
    intro y _
    by_cases hy : (y : G) = 1
    · rw [Finset.mem_insert]
      exact Or.inl (Subtype.ext hy)
    · rw [Finset.mem_insert, Finset.mem_singleton]
      exact Or.inr (Subtype.ext (hcon (y : G) y.2 hy))
  have h1 := Finset.card_le_card hsub
  rw [Finset.card_univ, ← Nat.card_eq_fintype_card, hB] at h1
  have h2 := Finset.card_le_two (a := (1 : B)) (b := ⟨b, hb⟩)
  omega

private theorem inner_of_conjAut_sq {A : GL (Fin 3) F}
    (h : conjAut 3 F A * conjAut 3 F A = 1) :
    conjAut 3 F A ∈ (MulAut.conj : projectiveSL 3 F →* MulAut (projectiveSL 3 F)).range := by
  rw [← map_mul] at h
  have h1 : conjAut 3 F (A * A) * fieldAut 3 F (1 : F ≃+* F) = 1 := by
    rw [map_one, mul_one]; exact h
  obtain ⟨-, c, hc⟩ := eq_one_of_conjAut_mul_fieldAut_eq_one le_rfl (A * A) 1 h1
  have h2 : c ^ 3 = Matrix.GeneralLinearGroup.det A ^ 2 := by
    have h3 := congrArg Matrix.GeneralLinearGroup.det hc
    rw [Matrix.GeneralLinearGroup.det_scalar, Fintype.card_fin, map_mul] at h3
    simpa [pow_two] using h3
  refine conjAut_mem_range_conj_of_det_eq_pow (n := 3) (A := A)
    (μ := Matrix.GeneralLinearGroup.det A * c⁻¹) ?_
  rw [mul_pow, inv_pow, h2]
  group

omit [Finite F] in
private theorem conjAut_mul_dual_mul_conjAut_mul_dual (A B : GL (Fin 3) F) :
    (conjAut 3 F A * dualAut 3 F) * (conjAut 3 F B * dualAut 3 F) =
      conjAut 3 F (A * Matrix.GeneralLinearGroup.inverseTranspose B) := by
  have hdc := (standard_automorphism_transport (K := F) (n := 3)).2.2.2.2.1 B
  have hdd := (standard_automorphism_transport (K := F) (n := 3)).2.2.2.1
  calc (conjAut 3 F A * dualAut 3 F) * (conjAut 3 F B * dualAut 3 F)
      = conjAut 3 F A * (dualAut 3 F * conjAut 3 F B * dualAut 3 F) := by group
    _ = conjAut 3 F A * conjAut 3 F (Matrix.GeneralLinearGroup.inverseTranspose B) := by
        rw [hdc]
    _ = _ := by rw [map_mul]

private theorem psl3_inner_proj {p e : ℕ} (hp : p.Prime) (he : Odd e)
    (hF : Nat.card F = p ^ e) (B : Subgroup (MulAut (projectiveSL 3 F)))
    (hB : Nat.card B = 4) (hB2 : ∀ β ∈ B, β * β = 1) :
    ∃ β ∈ B, β ≠ 1 ∧
      β ∈ (MulAut.conj : projectiveSL 3 F →* MulAut (projectiveSL 3 F)).range := by
  have he1 : 1 ≤ e := by rcases he with ⟨k, hk⟩; omega
  have hAut : Nat.card (F ≃+* F) = e :=
    (finite_field_automorphism_fixed_field_cardinality hp he1 hF).choose_spec.2.2.2.1
  have hoddAut : Odd (Nat.card (F ≃+* F)) := hAut ▸ he
  set φ : MulAut (projectiveSL 3 F) →* (F ≃+* F) := linearFieldPart F le_rfl with hφdef
  have hφ : ∀ β ∈ B, φ β = 1 := by
    intro β hβ
    have hdvd : Nat.card (B.map φ) ∣ 4 := by
      rw [← hB]; exact Subgroup.card_map_dvd B φ
    have hdvd' : Nat.card (B.map φ) ∣ Nat.card (F ≃+* F) :=
      Subgroup.card_subgroup_dvd_card (B.map φ)
    have hodd : Odd (Nat.card (B.map φ)) := Odd.of_dvd_nat hoddAut hdvd'
    have h1 : Nat.card (B.map φ) = 1 := by
      have hle : Nat.card (B.map φ) ≤ 4 := Nat.le_of_dvd (by norm_num) hdvd
      have hpos : 0 < Nat.card (B.map φ) := Nat.card_pos
      rcases hodd with ⟨k, hk⟩
      interval_cases Nat.card (B.map φ) <;> omega
    have hbot : B.map φ = ⊥ := Subgroup.card_eq_one.mp h1
    have hmem : φ β ∈ B.map φ := Subgroup.mem_map_of_mem φ hβ
    rw [hbot] at hmem
    simpa using hmem
  obtain ⟨β₀, hβ₀B, hβ₀ne⟩ := exists_ne_one_of_card_four B hB
  obtain ⟨A₀, σ₀, ε₀, hε₀, hβ₀⟩ := (automorphism_generation (K := F) (n := 3) le_rfl).2 β₀
  have hσ₀ : σ₀ = 1 := by
    have h := hφ β₀ hβ₀B
    rw [show φ β₀ = linearFieldPart F le_rfl β₀ from rfl, hβ₀,
      linearFieldPart_eq le_rfl hε₀] at h
    exact h
  have hβ₀' : β₀ = conjAut 3 F A₀ * dualAut 3 F ^ ε₀ := by
    rw [hβ₀, hσ₀, map_one, mul_one]
  interval_cases ε₀
  · have hβ : β₀ = conjAut 3 F A₀ := by simpa using hβ₀'
    refine ⟨β₀, hβ₀B, hβ₀ne, ?_⟩
    rw [hβ]
    exact inner_of_conjAut_sq (by rw [← hβ]; exact hB2 β₀ hβ₀B)
  · have hβ₀'' : β₀ = conjAut 3 F A₀ * dualAut 3 F := by simpa using hβ₀'
    obtain ⟨β₁, hβ₁B, hβ₁ne1, hβ₁ne⟩ :=
      exists_second_ne_one_of_card_four hB hβ₀B hβ₀ne
    obtain ⟨A₁, σ₁, ε₁, hε₁, hβ₁⟩ := (automorphism_generation (K := F) (n := 3) le_rfl).2 β₁
    have hσ₁ : σ₁ = 1 := by
      have h := hφ β₁ hβ₁B
      rw [show φ β₁ = linearFieldPart F le_rfl β₁ from rfl, hβ₁,
        linearFieldPart_eq le_rfl hε₁] at h
      exact h
    have hβ₁' : β₁ = conjAut 3 F A₁ * dualAut 3 F ^ ε₁ := by
      rw [hβ₁, hσ₁, map_one, mul_one]
    interval_cases ε₁
    · have hβ₁'' : β₁ = conjAut 3 F A₁ := by simpa using hβ₁'
      refine ⟨β₁, hβ₁B, hβ₁ne1, ?_⟩
      rw [hβ₁'']
      exact inner_of_conjAut_sq (by rw [← hβ₁'']; exact hB2 β₁ hβ₁B)
    · have hβ₁'' : β₁ = conjAut 3 F A₁ * dualAut 3 F := by simpa using hβ₁'
      have hprod : β₀ * β₁ =
          conjAut 3 F (A₀ * Matrix.GeneralLinearGroup.inverseTranspose A₁) := by
        rw [hβ₀'', hβ₁'']
        exact conjAut_mul_dual_mul_conjAut_mul_dual A₀ A₁
      have hmem : β₀ * β₁ ∈ B := B.mul_mem hβ₀B hβ₁B
      have hne : β₀ * β₁ ≠ 1 := by
        intro h
        apply hβ₁ne
        have h2 : β₁ = β₀⁻¹ := eq_inv_of_mul_eq_one_right h
        rw [h2, inv_eq_of_mul_eq_one_right (hB2 β₀ hβ₀B)]
      refine ⟨β₀ * β₁, hmem, hne, ?_⟩
      rw [hprod]
      exact inner_of_conjAut_sq (by rw [← hprod]; exact hB2 (β₀ * β₁) hmem)

private noncomputable def pslEquiv (F : Type) [Field F] :
    StatedProj (StatedSL 3 F) ≃* projectiveSL 3 F :=
  (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 3 F).symm.trans
    (CFSG.LocalAnalysis.ComponentInitial.LinearCover.projectiveSpecialLinearEquivProjectiveSL 3 F)

omit [Finite F] in
private theorem pslEquiv_statedProjMk (s : Matrix.SpecialLinearGroup (Fin 3) F) :
    pslEquiv F (CFSG.RankThree.CentralCover.statedProjMk (StatedSL 3 F)
      (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 F s)) =
        proj 3 F s := by
  have h1 : (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 3 F)
      (QuotientGroup.mk s) = CFSG.RankThree.CentralCover.statedProjMk (StatedSL 3 F)
        (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 F s) :=
    QuotientGroup.congr_mk' _ _ _ _ s
  unfold pslEquiv
  rw [MulEquiv.trans_apply, ← h1, MulEquiv.symm_apply_apply]
  exact QuotientGroup.quotientMulEquivOfEq_mk _ s

private noncomputable def oddDiag₃SL (F : Type) [Field F] : SL(3, F) :=
  ⟨(CFSG.RankThree.CentralCover.oddDiag₃ F : Matrix (Fin 3) (Fin 3) F),
    CFSG.RankThree.CentralCover.det_oddDiag₃ F⟩

omit [Finite F] in
private theorem coe_oddDiag₃SL :
    ((oddDiag₃SL F : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) =
      (CFSG.RankThree.CentralCover.oddDiag₃ F : Matrix (Fin 3) (Fin 3) F) := rfl

omit [Finite F] in
private theorem pslEquiv_linU₀ :
    pslEquiv F (linU₀ F) = proj 3 F (rootInv F (show 2 ≤ 3 by norm_num)) := by
  have h2 : (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 F
      (oddDiag₃SL F) : StatedSL 3 F) = (⟨CFSG.RankThree.CentralCover.oddDiag₃ F,
        Subgroup.subset_closure (CFSG.RankThree.CentralCover.det_oddDiag₃ F)⟩ :
          StatedSL 3 F) := by
    apply Subtype.ext
    apply Units.ext
    rw [CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL_coe]
    rfl
  have h3 : ((oddDiag₃SL F : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) =
      ((rootInv F (show 2 ≤ 3 by norm_num) : SL(3, F)) :
        Matrix (Fin 3) (Fin 3) F) := by
    rw [coe_oddDiag₃SL, coe_rootInv, negBlock_eq_diagonal]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [CFSG.RankThree.CentralCover.oddDiag₃, Matrix.diagonal]
  rw [show linU₀ F = CFSG.RankThree.CentralCover.statedProjMk (StatedSL 3 F)
    ⟨CFSG.RankThree.CentralCover.oddDiag₃ F,
      Subgroup.subset_closure (CFSG.RankThree.CentralCover.det_oddDiag₃ F)⟩ from rfl,
    ← h2, pslEquiv_statedProjMk]
  congr 1
  exact Subtype.ext h3

private noncomputable def psl3xN (F : Type) [Field F] : projectiveSL 3 F :=
  proj 3 F (rootInv F (show 2 ≤ 3 by norm_num))

omit [Finite F] in
private theorem proj_xN_eq :
    proj 3 F (CFSG.ClassicalInvolution.ModelFacts.Orth15.ChainL.xN) = psl3xN F := by
  congr 1
  apply Subtype.ext
  rw [coe_rootInv, negBlock_eq_diagonal]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [CFSG.ClassicalInvolution.ModelFacts.Orth15.ChainL.xN, Matrix.diagonal]

private theorem rootSL2_map_le_commutator (h2 : (2 : F) ≠ 0) (h4 : 4 ≤ Nat.card F) :
    (rootSL2 F (show 2 ≤ 3 by norm_num)).map (proj 3 F) ≤
      ⁅Subgroup.centralizer ({psl3xN F} : Set (projectiveSL 3 F)),
        Subgroup.centralizer ({psl3xN F} : Set (projectiveSL 3 F))⁆ := by
  have hC : (rootSL2 F (show 2 ≤ 3 by norm_num)).map (proj 3 F) ≤
      Subgroup.centralizer ({psl3xN F} : Set (projectiveSL 3 F)) := by
    refine (Subgroup.map_mono (isClassicalSL2_rootSL2 h2
      (show 2 ≤ 3 by norm_num)).le_centralizer).trans ?_
    have h := Subgroup.map_centralizer_le_centralizer_image
      ({rootInv F (show 2 ≤ 3 by norm_num)} : Set (Matrix.SpecialLinearGroup (Fin 3) F))
      (proj 3 F)
    simpa [psl3xN, Set.image_singleton] using h
  have hperf : rootSL2 F (show 2 ≤ 3 by norm_num) =
      ⁅rootSL2 F (show 2 ≤ 3 by norm_num), rootSL2 F (show 2 ≤ 3 by norm_num)⁆ :=
    (Subgroup.isPerfect_iff.mp ((isClassicalSL2_rootSL2 h2
      (show 2 ≤ 3 by norm_num)).isPerfect h4)).symm
  have heq : (rootSL2 F (show 2 ≤ 3 by norm_num)).map (proj 3 F) =
      ⁅(rootSL2 F (show 2 ≤ 3 by norm_num)).map (proj 3 F),
        (rootSL2 F (show 2 ≤ 3 by norm_num)).map (proj 3 F)⁆ := by
    conv_lhs => rw [hperf]
    rw [Subgroup.map_commutator]
  rw [heq]
  exact Subgroup.commutator_mono hC hC

theorem psl3_inner {p e : ℕ} (hp : p.Prime) (_hp2 : p ≠ 2) (he : Odd e) (hF : Nat.card F = p ^ e)
    (B : Subgroup (MulAut (StatedProj (StatedSL 3 F)))) (hB : Nat.card B = 4)
    (hB2 : ∀ β ∈ B, β * β = 1) :
    ∃ β ∈ B, β ≠ 1 ∧ β ∈ (MulAut.conj :
      StatedProj (StatedSL 3 F) →* MulAut (StatedProj (StatedSL 3 F))).range := by
  let Φ : MulAut (StatedProj (StatedSL 3 F)) ≃* MulAut (projectiveSL 3 F) :=
    MulAut.congr (pslEquiv F)
  have hB' : Nat.card (B.map Φ.toMonoidHom) = 4 := by
    rw [Subgroup.card_map_of_injective Φ.injective, hB]
  have hB2' : ∀ β ∈ B.map Φ.toMonoidHom, β * β = 1 := by
    rintro β ⟨b, hb, rfl⟩
    rw [← map_mul, hB2 b hb, map_one]
  obtain ⟨β, hβ, hβne, hinner⟩ :=
    psl3_inner_proj hp he hF (B.map Φ.toMonoidHom) hB' hB2'
  obtain ⟨b, hb, hfb⟩ := hβ
  refine ⟨b, hb, ?_, ?_⟩
  · intro h1
    apply hβne
    rw [← hfb, h1, map_one]
  · obtain ⟨y, hy⟩ := hinner
    refine ⟨(pslEquiv F).symm y, ?_⟩
    have hbconj : b = MulAut.conj ((pslEquiv F).symm y) := by
      calc b = Φ.symm (Φ b) := (MulEquiv.symm_apply_apply Φ b).symm
        _ = Φ.symm β := by rw [show Φ b = β from hfb]
        _ = Φ.symm (MulAut.conj y) := by rw [hy]
        _ = MulAut.conj ((pslEquiv F).symm y) := mulAut_congr_symm_conj (pslEquiv F) y
    exact hbconj.symm

theorem psl3_cent (hF : Odd (Nat.card F)) (h5 : 5 ≤ Nat.card F)
    (β : MulAut (StatedProj (StatedSL 3 F))) (h2 : β * β = 1) (_ht : β (linU₀ F) = linU₀ F)
    (hK : ∀ k ∈ derivedCent (linU₀ F), β k = k) : β = 1 ∨ β = MulAut.conj (linU₀ F) := by
  let e := pslEquiv F
  let α : MulAut (projectiveSL 3 F) := MulAut.congr e β
  have hpe : e (linU₀ F) = psl3xN F := pslEquiv_linU₀ (F := F)
  have h2ne : (2 : F) ≠ 0 := two_ne_zero_of_odd_natCard hF
  have h2' : α * α = 1 := by
    show MulAut.congr e β * MulAut.congr e β = 1
    rw [← map_mul, h2, map_one]
  have hmapC : (Subgroup.centralizer ({linU₀ F} : Set (StatedProj (StatedSL 3 F)))).map
      e.toMonoidHom = Subgroup.centralizer ({psl3xN F} : Set (projectiveSL 3 F)) := by
    rw [map_centralizer_eq e ({linU₀ F} : Set (StatedProj (StatedSL 3 F))),
      Set.image_singleton, hpe]
  have hmapK : (derivedCent (linU₀ F)).map e.toMonoidHom =
      ⁅Subgroup.centralizer ({psl3xN F} : Set (projectiveSL 3 F)),
        Subgroup.centralizer ({psl3xN F} : Set (projectiveSL 3 F))⁆ := by
    unfold derivedCent
    rw [Subgroup.map_commutator, hmapC]
  have hK' : ∀ k ∈ (derivedCent (linU₀ F)).map e.toMonoidHom, α k = k := by
    rintro k ⟨x, hx, rfl⟩
    show MulAut.congr e β (e x) = e x
    rw [mulAut_congr_apply_apply, hK x hx]
  have hfix : ∀ r ∈ rootSL2 F (show 2 ≤ 3 by norm_num), α (proj 3 F r) = proj 3 F r := by
    intro r hr
    apply hK'
    rw [hmapK]
    exact rootSL2_map_le_commutator h2ne (by omega)
      (Subgroup.mem_map_of_mem (proj 3 F) hr)
  rcases CFSG.ClassicalInvolution.ModelFacts.Orth15.ChainL.psl3_aut_centralizing
    h2ne α hfix h2' with hall | hall
  · left
    have hα1 : α = 1 := by
      refine MulEquiv.ext fun y => ?_
      obtain ⟨g, rfl⟩ := proj_surjective 3 F y
      exact hall g
    show β = 1
    apply (MulAut.congr e).injective
    rw [show (MulAut.congr e) β = α from rfl, hα1, map_one]
  · right
    have hαconj : α = MulAut.conj (psl3xN F) := by
      refine MulEquiv.ext fun y => ?_
      obtain ⟨g, rfl⟩ := proj_surjective 3 F y
      rw [hall g, ← proj_xN_eq]
      exact (conj_proj _ g).symm
    show β = MulAut.conj (linU₀ F)
    apply (MulAut.congr e).injective
    rw [show (MulAut.congr e) β = α from rfl, hαconj, mulAut_congr_conj, hpe]

end CFSG.LocalAnalysis.WeakClosure81.Asch6

end
