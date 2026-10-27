module

public import CFSG.RankThree.PartTwo.KFacts.AutPSpOrderThree
public import CFSG.RankThree.PartTwo.KFacts.K71Basic
import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherSymplecticPrimeCentralizer
public import CFSG.RankThree.PartTwo.KFacts.AutKindsStd

public section

namespace CFSG.RankThree.PartTwo.KFacts

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.GH74.GLS.IVK (fixedField mem_fixedField_iff fixedField_apply fixedField_card_pow)
open Matrix

section Scalars

variable {F : Type} [Field F] [CharP F 2]

theorem spScalars_eq_bot : spScalars 2 F = ⊥ := by
  rw [eq_bot_iff]
  intro g hg
  rw [Subgroup.mem_subgroupOf, StatedScalars, MonoidHom.mem_range] at hg
  obtain ⟨c, hc⟩ := hg
  have hsp := CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl.mem_statedSp_iff.mp g.2
  rw [← hc, GeneralLinearGroup.coe_scalar] at hsp
  have hentry := congrFun (congrFun hsp (Sum.inl 0)) (Sum.inr 0)
  simp [Matrix.scalar_apply, Matrix.mul_apply, Matrix.fromBlocks_apply₁₂,
    Matrix.diagonal_apply] at hentry
  have hc2 : (c : F) * c = 1 := by simpa using hentry
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have hsq : ((c : F) + 1) ^ 2 = 0 := by linear_combination hc2 + ((c : F) + 1) * h2
  have hc1 : (c : F) = 1 := by
    have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hsq
    rw [add_eq_zero_iff_eq_neg, CharTwo.neg_eq] at this
    exact this
  rw [Subgroup.mem_bot]
  apply Subtype.ext
  rw [Subgroup.coe_one, ← hc]
  exact Units.ext (by rw [GeneralLinearGroup.coe_scalar, hc1]; simp)

theorem proj_injective_of_charTwo : Function.Injective (proj 2 F) := by
  rw [← MonoidHom.ker_eq_bot_iff, ker_proj, spScalars_eq_bot]

end Scalars

section Incl

variable {F : Type} [Field F]

variable (σ : F ≃+* F)

noncomputable def spIncl : StatedSp 2 (fixedField σ) →* StatedSp 2 F :=
  ((GeneralLinearGroup.map (fixedField σ).subtype).comp (StatedSp 2 (fixedField σ)).subtype)
    |>.codRestrict (StatedSp 2 F) fun g =>
      CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.map_mem_statedSp _ g.2

theorem coe_spIncl_apply (g : StatedSp 2 (fixedField σ)) (i j : Fin 2 ⊕ Fin 2) :
    (((spIncl σ g : StatedSp 2 F) : GL (Fin 2 ⊕ Fin 2) F) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) i j =
      ((g : GL (Fin 2 ⊕ Fin 2) (fixedField σ)) i j : F) :=
  GeneralLinearGroup.map_apply _ i j _

theorem spIncl_injective : Function.Injective (spIncl σ) := by
  intro g h hgh
  apply Subtype.ext
  apply GeneralLinearGroup.ext
  intro i j
  apply Subtype.ext
  rw [← coe_spIncl_apply, ← coe_spIncl_apply, hgh]

theorem mem_range_spIncl_iff (g : StatedSp 2 F) :
    g ∈ (spIncl σ).range ↔ fieldSp 2 F σ g = g := by
  constructor
  · rintro ⟨h, rfl⟩
    apply CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl.statedSp_ext
    rw [coe_fieldSp]
    ext i j
    rw [Matrix.map_apply, coe_spIncl_apply]
    exact fixedField_apply σ _
  · intro hg
    have hfix : ∀ i j, σ (((g : GL (Fin 2 ⊕ Fin 2) F) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) i j) =
        ((g : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) i j := by
      intro i j
      have h1 := congrArg (fun x : StatedSp 2 F =>
        ((x : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) i j) hg
      simpa [coe_fieldSp] using h1
    set M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (fixedField σ) :=
      fun i j => ⟨((g : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) i j,
        (mem_fixedField_iff σ _).mpr (hfix i j)⟩ with hM
    have hMmap : M.map (fixedField σ).subtype =
        ((g : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) := rfl
    have hdet : M.det ≠ 0 := by
      intro h0
      have h1 : (fixedField σ).subtype M.det =
          ((g : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F).det := by
        rw [RingHom.map_det]
        exact congrArg Matrix.det hMmap
      rw [h0, map_zero] at h1
      exact (g : GL (Fin 2 ⊕ Fin 2) F).isUnit.map Matrix.detMonoidHom |>.ne_zero h1.symm
    set A : GL (Fin 2 ⊕ Fin 2) (fixedField σ) := GeneralLinearGroup.mkOfDetNeZero M hdet
    have hA : (A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (fixedField σ)) = M := rfl
    have hAsp : A ∈ StatedSp 2 (fixedField σ) := by
      rw [CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl.mem_statedSp_iff, hA]
      have key : (Mᵀ * fromBlocks 0 1 (-1) 0 * M).map (fixedField σ).subtype =
          (fromBlocks (0 : Matrix (Fin 2) (Fin 2) (fixedField σ)) 1 (-1) 0).map
            (fixedField σ).subtype := by
        rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map,
          CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.formJ_map_ringHom, hMmap]
        exact CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl.mem_statedSp_iff.mp g.2
      exact Matrix.map_injective (fixedField σ).subtype_injective key
    refine ⟨⟨A, hAsp⟩, ?_⟩
    apply CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl.statedSp_ext
    ext i j
    rw [coe_spIncl_apply]
    rfl

end Incl

section Fixed

variable {F : Type} [Field F] [CharP F 2]

theorem fieldAut_proj_eq_proj_iff (σ : F ≃+* F) (g : StatedSp 2 F) :
    fieldAut 2 F σ (proj 2 F g) = proj 2 F g ↔ fieldSp 2 F σ g = g := by
  rw [fieldAut_proj]
  exact proj_injective_of_charTwo.eq_iff

theorem proj_spIncl_injective (σ : F ≃+* F) : Function.Injective ((proj 2 F).comp (spIncl σ)) :=
  proj_injective_of_charTwo.comp (spIncl_injective σ)

theorem mem_range_proj_spIncl_iff (σ : F ≃+* F) (y : StatedProj (StatedSp 2 F)) :
    y ∈ ((proj 2 F).comp (spIncl σ)).range ↔ fieldAut 2 F σ y = y := by
  obtain ⟨g, rfl⟩ := proj_surjective (r := 2) (K := F) y
  rw [fieldAut_proj_eq_proj_iff, ← mem_range_spIncl_iff]
  constructor
  · rintro ⟨h, hh⟩
    exact ⟨h, proj_injective_of_charTwo hh⟩
  · rintro ⟨h, rfl⟩
    exact ⟨h, rfl⟩

end Fixed

section Bar

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

variable {F : Type} [Field F] [Finite F] [CharP F 2]

theorem exists_barCentralizer_mulEquiv_sp4 {a : G} (ha3 : a ^ 3 = 1)
    (hout : InducesOuterTheta a L)
    (e : L ⧸ aschbacherSolvableCore 3 L ≃* StatedProj (StatedSp 2 F)) :
    InducesKind L (stdPinnedPSp4Even F) e a .field ∧
      ∃ σ : F ≃+* F, orderOf σ = 3 ∧ Nat.card (fixedField σ) ^ 3 = Nat.card F ∧
        Nonempty (Sec8.barCentralizer (Subgroup.zpowers a) L ≃* StatedSp 2 (fixedField σ)) := by
  obtain ⟨hN, -⟩ := id hout
  set α := inducedAutHom L e ⟨a, hN⟩ with hαdef
  have hα3 : α ^ 3 = 1 := inducedAutHom_pow_eq_one L e hN ha3
  have hnotin : α ∉ (conjAut 2 F).range := by
    rintro ⟨A, hA⟩
    apply (not_isInnerAut_inducedAutHom_iff L e hN).mpr hout
    rw [← hαdef, ← hA]
    exact conjAut_mem_inner_of_charTwo A
  refine ⟨⟨hN, isField_psp4Even_of_pow_three_eq_one hα3 hnotin⟩, ?_⟩
  obtain ⟨σ, hσ3, H, hαH⟩ := sp4_even_order_three_field_descent α hα3 hnotin
  have hcard := fixedField_card_pow σ
  rw [hσ3] at hcard
  refine ⟨σ, hσ3, hcard, ?_⟩
  refine nonempty_barCentralizer_mulEquiv hN e
    ((conjAut 2 F H : StatedProj (StatedSp 2 F) ≃* StatedProj (StatedSp 2 F)).toMonoidHom.comp
      ((proj 2 F).comp (spIncl σ))) ((conjAut 2 F H).injective.comp (proj_spIncl_injective σ))
    fun z => ?_
  rw [← hαdef, hαH]
  exact mem_range_conj_comp_iff _ _ _ (mem_range_proj_spIncl_iff σ) z

end Bar

section Models

open CFSG.Assembly.RankThreeEven (projImage projSp)
open CFSG.Adapters.RankTwoModelTransports (glCongr statedProjEquivMapMk)

noncomputable def statedSpEquivProjSpOfCharTwo (k : Type) [Field k] [CharP k 2] :
    StatedSp 2 k ≃* projSp 2 k :=
  (MulEquiv.ofBijective (proj 2 k) ⟨proj_injective_of_charTwo, proj_surjective⟩).trans
    (statedProjEquivMapMk (StatedSp 2 k))

noncomputable def statedSpCongr {k k' : Type} [Field k] [Field k'] (φ : k ≃+* k') :
    StatedSp 2 k ≃* StatedSp 2 k' :=
  ((StatedSp 2 k).equivMapOfInjective (glCongr φ).toMonoidHom (glCongr φ).injective).trans
    (MulEquiv.subgroupCongr (CFSG.ClassicalInvolution.Upgrade.glCongr_statedSp φ 2))

theorem barCentralizer_mulEquiv_projSp {G : Type} [Group G] [Finite G] {L : Subgroup G} {a : G}
    {n : ℕ} (hn : n ≠ 0) (ha3 : a ^ 3 = 1) (hout : InducesOuterTheta a L)
    (hL : Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃* projSp 2 (GaloisField 2 (3 * n)))) :
    InducesStdKind L a .field ∧
      Nonempty (Sec8.barCentralizer (Subgroup.zpowers a) L ≃* projSp 2 (GaloisField 2 n)) := by
  obtain ⟨eL⟩ := hL
  set F := GaloisField 2 (3 * n)
  set e : L ⧸ aschbacherSolvableCore 3 L ≃* StatedProj (StatedSp 2 F) :=
    eL.trans (statedProjEquivMapMk (StatedSp 2 F)).symm with he
  obtain ⟨hkind, σ, -, hcard, ⟨ι⟩⟩ := exists_barCentralizer_mulEquiv_sp4 ha3 hout e
  refine ⟨InducesStdKind.psp4even F ⟨e, hkind⟩, ?_⟩
  have hF : Nat.card F = 2 ^ (3 * n) := GaloisField.card 2 (3 * n) (by omega)
  have hk : Nat.card (fixedField σ) = 2 ^ n := by
    rw [hF, pow_mul'] at hcard
    exact Nat.pow_left_injective (by norm_num : 3 ≠ 0) hcard
  let φ : fixedField σ ≃+* GaloisField 2 n :=
    CFSG.ClassicalModels.finiteFieldEquivGaloisField (fixedField σ) 2 n (by omega) hk
  exact ⟨ι.trans ((statedSpCongr φ).trans (statedSpEquivProjSpOfCharTwo (GaloisField 2 n)))⟩

end Models

end CFSG.RankThree.PartTwo.KFacts
