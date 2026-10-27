module

public import CFSG.LocalAnalysis.StandardType.FS81.TwD7CentDecomp
public import CFSG.LocalAnalysis.StandardType.FS81.D6NormAux
public import CFSG.ClassicalGroups.Orthogonal.IsometryConj
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S172CCentType
public import CFSG.RankThree.PartOne.S15K.FamilyForms
public import CFSG.LieType.SeitzGeneration.OrthNonsplitTools
public import CFSG.HardMathSupport.Solomon.LocalBalance.Sec5Statements
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6DInputs
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7Interface
public import CFSG.Holt.Fixed
public import CFSG.LieType.SeitzGeneration.HyperLinear
public import CFSG.LieType.SeitzGeneration.OrthCubeBlocks
public import CFSG.LieType.SeitzGeneration.OrthExLift
public import CFSG.LocalAnalysis.GL83PartI.I_22_5.Setup
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S172CCentLayer
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10FBaseIso
public import CFSG.LocalAnalysis.GLTheoremA.P51.Quaternion
public import CFSG.LocalAnalysis.GLTheoremA.P55.Dihedral
public import CFSG.LocalAnalysis.GLTheoremA.S10.Lemma106107
public import CFSG.LocalAnalysis.GLTheoremA.S11.Inputs119
public import CFSG.LocalAnalysis.GLTheoremA.S11.Inputs16
public import CFSG.LocalAnalysis.GLTheoremA.S11.InputsCE
public import CFSG.LocalAnalysis.GLTheoremA.S11.InputsElim
public import CFSG.LocalAnalysis.GLTheoremA.S3.Lemma35
public import CFSG.LocalAnalysis.GLTheoremA.Sec5Setup
public import CFSG.RankThree.PartOne.CTP.SeitzLinear
public import CFSG.RankThree.PartOne.FOC.CompCommutator
public import CFSG.SignalizerFunctorTheorem.Nonsolvable.SolComponent

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.StandardType.FrameRoute.FS81

open Module QuadraticMap CFSG.LocalAnalysis.GLTheoremA.KD264Lie.OmC
  CFSG.RankThree.OrthogonalInvolutions
open CFSG.RankThree.Classical2 (orthDerived)
open scoped commutatorElement

section TwD7

open CFSG.Open CFSG.Assembly CFSG.ClassicalGroups.Orthogonal CFSG.LieType.SeitzGeneration
  CFSG.LieType.SeitzGeneration.OrthBlk CFSG.LieType.Universal.Spin

theorem nonempty_mulEquiv_om12_m0_twD7 {G : Type} [Group G] [Finite G] {b₀ : G}
    {K E : Subgroup G} (hstd : StdAssumptions b₀ K E Row.twD7)
    {B : Basis3 G (Row.twD7.n + 1)} (hB : Adapted B b₀ K E) (hrec : RecOut Row.twD7 B b₀) :
    Nonempty (↥⁅Subgroup.centralizer ({B.b 1} : Set G) ⊓ K,
      Subgroup.centralizer ({B.b 1} : Set G) ⊓ K⁆ ≃* ↥D6M.Om12) := by
  classical
  obtain ⟨_hsimple, hHyp, hCanon⟩ := id hstd
  obtain ⟨hrow, hdisjEK, hsup, hmax, hcard, -⟩ := hCanon
  obtain ⟨hA, -, -, -, -, -⟩ := hHyp
  obtain ⟨hb₀, hKC, hKn, hcenter, -, -, -, -⟩ := hA
  have hrec' : RecOutTwD7 B b₀ := hrec
  obtain ⟨-, ⟨φ⟩⟩ := isSimpleGroup_and_mulEquiv_of_isRow_twD7 hrow hcenter
  have hdisj : Disjoint (Subgroup.zpowers b₀) K := disjoint_zpowers_of_center hKC hcenter
  have hQ : (polarBilin (quadMinus 7 (ZMod 2) 1 1)).Nondegenerate :=
    nondegenerate_polarBilin_quadMinus_of_finite 7 (ZMod 2)
      (by decide : ∀ s : ZMod 2, s ^ 2 + 1 * s + 1 ≠ 0)
  have h14 : finrank (ZMod 2) (Fin 6 ⊕ Fin 6 ⊕ Fin 2 → ZMod 2) = 14 := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_sum, Fintype.card_fin,
      Fintype.card_fin]
  obtain ⟨B', F, hB', heven, hU2, hφB'⟩ := exists_basis_frame_of_model hQ
    exists_totallySingular_three_quadMinus_seven (n := 7) (by norm_num) φ hb₀ hKC hdisj hsup
    hmax hcard
  have hR : B.realized K ⊆ evenFix0 7 := fun M hM =>
    realized_centralizer_subset_evenFix0_of_recOutTwD7 hB hKC hKn hdisjEK hrec'
      (realized_mono B hKC hM)
  obtain ⟨j, hj⟩ := exists_eq_or_eq_inv_of_realized_evenFix0 (n := 7) (by norm_num) hdisj hB hB'
    hR heven 0
  have hbj : B'.b j.succ ∈ K := hB'.2.2 _ (Fin.succ_ne_zero j)
  obtain ⟨U, hUdef⟩ : ∃ U, U = F.U j := ⟨_, rfl⟩
  obtain ⟨x, hxdef⟩ : ∃ x : (Fin 6 ⊕ Fin 6 ⊕ Fin 2 → ZMod 2) ≃ₗ[ZMod 2]
      (Fin 6 ⊕ Fin 6 ⊕ Fin 2 → ZMod 2), x = F.ι (Multiplicative.ofAdd (Pi.single j 1)) :=
    ⟨_, rfl⟩
  have hφx : ((φ ⟨B'.b j.succ, hbj⟩ : ↥(orthDerived (quadMinus 7 (ZMod 2) 1 1))) :
      (Fin 6 ⊕ Fin 6 ⊕ Fin 2 → ZMod 2) ≃ₗ[ZMod 2] (Fin 6 ⊕ Fin 6 ⊕ Fin 2 → ZMod 2)) = x := by
    rw [hxdef]
    exact hφB' j hbj
  have hnd : PolarNondegOn (quadMinus 7 (ZMod 2) 1 1) U := by
    rw [hUdef]
    exact fun u hu huv => F.nondeg j u hu fun v hv => by
      rw [polar_comm]
      exact huv v hv
  have hUc : IsCompl U (perpOf (quadMinus 7 (ZMod 2) 1 1) U) := isCompl_perp hnd
  have hPnd : PolarNondegOn (quadMinus 7 (ZMod 2) 1 1) (perp (quadMinus 7 (ZMod 2) 1 1) U) :=
    polarNondegOn_perp hQ hnd
  have hP : (polarBilin ((quadMinus 7 (ZMod 2) 1 1).restrict
      (perpOf (quadMinus 7 (ZMod 2) 1 1) U))).Nondegenerate := by
    have hrefl : (polarBilin ((quadMinus 7 (ZMod 2) 1 1).restrict
        (perpOf (quadMinus 7 (ZMod 2) 1 1) U))).IsRefl :=
      (QuadraticMap.isSymm_polarBilin _).isRefl
    refine (LinearMap.IsRefl.nondegenerate_iff_separatingLeft hrefl).mpr ?_
    intro m hm
    refine Submodule.coe_eq_zero.mp (hPnd m m.2 fun y hy => ?_)
    have h := hm ⟨y, hy⟩
    rw [polarBilin_apply_apply] at h
    simpa [QuadraticMap.polar, QuadraticMap.restrict_apply] using h
  have hU2' : finrank (ZMod 2) U = 2 := by rw [hUdef]; exact hU2 j
  have hfin : finrank (ZMod 2) U + finrank (ZMod 2) (perpOf (quadMinus 7 (ZMod 2) 1 1) U) =
      14 := by
    rw [Submodule.finrank_add_eq_of_isCompl hUc, h14]
  have h12 : finrank (ZMod 2) (perpOf (quadMinus 7 (ZMod 2) 1 1) U) = 12 := by
    rw [hU2'] at hfin
    omega
  have hT : ∃ T : Submodule (ZMod 2) (perpOf (quadMinus 7 (ZMod 2) 1 1) U),
      finrank (ZMod 2) T = 3 ∧
        ∀ u ∈ T,
          ((quadMinus 7 (ZMod 2) 1 1).restrict (perpOf (quadMinus 7 (ZMod 2) 1 1) U)) u = 0 :=
    OrthNS.exists_ts_three_comp hPnd (by
      change 8 ≤ finrank (ZMod 2) (perpOf (quadMinus 7 (ZMod 2) 1 1) U)
      rw [h12]
      norm_num)
  have hxΩ : x ∈ orthDerived (quadMinus 7 (ZMod 2) 1 1) := hφx ▸ (φ ⟨B'.b j.succ, hbj⟩).2
  have hx3 : x ^ 3 = 1 := by
    have h3 : (⟨B'.b j.succ, hbj⟩ : ↥K) ^ 3 = 1 := by
      apply Subtype.ext
      rw [Subgroup.coe_pow, ← B'.ord j.succ, OneMemClass.coe_one]
      exact pow_orderOf_eq_one _
    rw [← hφx, ← Subgroup.coe_pow, ← map_pow, h3, map_one, OneMemClass.coe_one]
  have hxU : ∀ u ∈ U, x u ∈ U := fun u hu => by
    rw [hUdef] at hu ⊢
    rw [hxdef]
    exact F.mapsTo _ j u hu
  have hxfix : ∀ v, x v = v ↔ v ∈ perpOf (quadMinus 7 (ZMod 2) 1 1) U := fun v => by
    rw [hxdef, F.fix, hUdef]
    constructor
    · intro h
      exact mem_perp.mpr (h j (by simp))
    · intro h i hi u hu
      have hij : i = j := by
        by_contra hne
        exact hi (by simp [hne])
      subst hij
      exact mem_perp.mp h u hu
  let ι : ↥K →* ((Fin 6 ⊕ Fin 6 ⊕ Fin 2 → ZMod 2) ≃ₗ[ZMod 2] (Fin 6 ⊕ Fin 6 ⊕ Fin 2 → ZMod 2)) :=
    (orthDerived (quadMinus 7 (ZMod 2) 1 1)).subtype.comp φ.toMonoidHom
  have hι : Function.Injective ι := Subtype.val_injective.comp φ.injective
  have hιb : ι ⟨B'.b j.succ, hbj⟩ = x := hφx
  have hιφ : ∀ k : ↥K, ι k = ((φ k : ↥(orthDerived (quadMinus 7 (ZMod 2) 1 1))) :
      (Fin 6 ⊕ Fin 6 ⊕ Fin 2 → ZMod 2) ≃ₗ[ZMod 2] (Fin 6 ⊕ Fin 6 ⊕ Fin 2 → ZMod 2)) :=
    fun _ => rfl
  have hC' : ((Subgroup.centralizer ({B'.b j.succ} : Set G) ⊓ K).subgroupOf K).map ι =
      orthDerived (quadMinus 7 (ZMod 2) 1 1) ⊓ Subgroup.centralizer ({x} : Set
        ((Fin 6 ⊕ Fin 6 ⊕ Fin 2 → ZMod 2) ≃ₗ[ZMod 2] (Fin 6 ⊕ Fin 6 ⊕ Fin 2 → ZMod 2))) := by
    ext g
    constructor
    · intro hg
      obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.mp hg
      rw [Subgroup.mem_subgroupOf] at hk
      refine Subgroup.mem_inf.mpr ⟨(φ k).2, ?_⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hkb : k * ⟨B'.b j.succ, hbj⟩ = ⟨B'.b j.succ, hbj⟩ * k :=
        Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hk).1)
      have h := congrArg ι hkb
      rw [map_mul, map_mul, hιb] at h
      exact h
    · intro hg
      obtain ⟨hgΩ, hgx⟩ := Subgroup.mem_inf.mp hg
      have hg' : ι (φ.symm ⟨g, hgΩ⟩) = g := by rw [hιφ, MulEquiv.apply_symm_apply]
      refine Subgroup.mem_map.mpr ⟨φ.symm ⟨g, hgΩ⟩, ?_, hg'⟩
      rw [Subgroup.mem_subgroupOf]
      refine Subgroup.mem_inf.mpr ⟨?_, (φ.symm ⟨g, hgΩ⟩).2⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hk : φ.symm ⟨g, hgΩ⟩ * ⟨B'.b j.succ, hbj⟩ =
          ⟨B'.b j.succ, hbj⟩ * φ.symm ⟨g, hgΩ⟩ := by
        apply hι
        rw [map_mul, map_mul, hιb, hg']
        exact Subgroup.mem_centralizer_singleton_iff.mp hgx
      exact congrArg Subtype.val hk
  have hcent : Subgroup.centralizer ({B'.b j.succ} : Set G) =
      Subgroup.centralizer ({B.b 1} : Set G) := by
    rcases hj with h | h
    · rw [show B.b 1 = B.b (0 : Fin 7).succ from rfl, h]
    · ext g
      rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff,
        show B.b 1 = B.b (0 : Fin 7).succ from rfl, h]
      exact Commute.inv_right_iff.symm
  let CK' : Subgroup G := Subgroup.centralizer ({B'.b j.succ} : Set G) ⊓ K
  let D : Subgroup ↥K := CK'.subgroupOf K
  let C : Subgroup ((Fin 6 ⊕ Fin 6 ⊕ Fin 2 → ZMod 2) ≃ₗ[ZMod 2]
      (Fin 6 ⊕ Fin 6 ⊕ Fin 2 → ZMod 2)) :=
    orthDerived (quadMinus 7 (ZMod 2) 1 1) ⊓
      Subgroup.centralizer ({x} : Set ((Fin 6 ⊕ Fin 6 ⊕ Fin 2 → ZMod 2) ≃ₗ[ZMod 2]
        (Fin 6 ⊕ Fin 6 ⊕ Fin 2 → ZMod 2)))
  let A : Subgroup ((Fin 6 ⊕ Fin 6 ⊕ Fin 2 → ZMod 2) ≃ₗ[ZMod 2]
      (Fin 6 ⊕ Fin 6 ⊕ Fin 2 → ZMod 2)) :=
    ⁅fixW (quadMinus 7 (ZMod 2) 1 1) U, fixW (quadMinus 7 (ZMod 2) 1 1) U⁆
  have hC'K : D.map ι = C := hC'
  have hxO : x ∈ TauCeti.QuadraticMap.orthogonalGroup (quadMinus 7 (ZMod 2) 1 1) :=
    Subgroup.commutator_le_self _ hxΩ
  have hxP : ∀ w ∈ perpOf (quadMinus 7 (ZMod 2) 1 1) U, x w = w := fun w hw => (hxfix w).mpr hw
  have hfixC : fixW (quadMinus 7 (ZMod 2) 1 1) U ≤
      Subgroup.centralizer ({x} : Set ((Fin 6 ⊕ Fin 6 ⊕ Fin 2 → ZMod 2) ≃ₗ[ZMod 2]
        (Fin 6 ⊕ Fin 6 ⊕ Fin 2 → ZMod 2))) := fun g hg =>
    Subgroup.mem_centralizer_singleton_iff.mpr (commute_of_mem_fixW hUc hxU hxP hg)
  have hAfix : A ≤ fixW (quadMinus 7 (ZMod 2) 1 1) U :=
    Subgroup.commutator_le.mpr fun g hg h hh => by
      rw [commutatorElement_def]
      exact mul_mem (mul_mem (mul_mem hg hh) (inv_mem hg)) (inv_mem hh)
  have hAC : A ≤ C :=
    le_inf (Subgroup.commutator_mono fixW_le_orthogonalGroup fixW_le_orthogonalGroup)
      (hAfix.trans hfixC)
  have hAA : ⁅A, A⁆ = A := commutator_commutator_fixW hUc hP hT
  have hdec : ∀ g ∈ C, ∃ i : ℕ, (x ^ i)⁻¹ * g ∈ A := by
    intro g hg
    obtain ⟨hgΩ, hgx⟩ := Subgroup.mem_inf.mp hg
    obtain ⟨i, hi⟩ := exists_pow_inv_mul_mem_fixW hUc hU2' hxO hx3 hxU hxfix
      (Subgroup.commutator_le_self _ hgΩ) (Subgroup.mem_centralizer_singleton_iff.mp hgx)
    exact ⟨i, mem_commutator_fixW_of_mem_orthDerived hQ hUc hP (by rw [h12]; norm_num) hi
      (mul_mem (inv_mem (pow_mem hxΩ i)) hgΩ)⟩
  have hcomm : ∀ g ∈ C, ∀ i : ℕ, Commute (x ^ i) g := by
    intro g hg i
    have hgx : Commute g x := Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hg).2
    exact hgx.symm.pow_left i
  have hCC : ⁅C, C⁆ = A := by
    apply le_antisymm
    · rw [Subgroup.commutator_le]
      intro g hg g' hg'
      obtain ⟨i, hi⟩ := hdec g hg
      obtain ⟨i', hi'⟩ := hdec g' hg'
      have key := commutatorElement_mul_mul_of_commute (c := x ^ i) (c' := x ^ i')
        (a := (x ^ i)⁻¹ * g) (a' := (x ^ i')⁻¹ * g') (hcomm _ (hAC hi) i)
        (hcomm _ (hAC hi') i) (hcomm _ (hAC hi) i') (hcomm _ (hAC hi') i')
        ((Commute.refl x).pow_pow i i')
      rw [mul_inv_cancel_left, mul_inv_cancel_left] at key
      rw [key]
      have := Subgroup.commutator_mem_commutator hi hi'
      rwa [hAA] at this
    · calc A = ⁅A, A⁆ := hAA.symm
        _ ≤ ⁅C, C⁆ := Subgroup.commutator_mono hAC hAC
  have hAOrth : ((E ⊓ K).subgroupOf K).map
      ((orthDerived (quadMinus 7 (ZMod 2) 1 1)).subtype.comp φ.toMonoidHom) ≤
      orthDerived (quadMinus 7 (ZMod 2) 1 1) := by
    rintro _ ⟨k, -, rfl⟩
    exact (φ k).2
  have hAO : ((E ⊓ K).subgroupOf K).map
      ((orthDerived (quadMinus 7 (ZMod 2) 1 1)).subtype.comp φ.toMonoidHom) ≤
      TauCeti.QuadraticMap.orthogonalGroup (quadMinus 7 (ZMod 2) 1 1) :=
    hAOrth.trans (Subgroup.commutator_le_self _)
  have h14' : finrank (ZMod 2) (Fin 6 ⊕ Fin 6 ⊕ Fin 2 → ZMod 2) = 2 * 7 := by
    rw [h14]
  have htop : (⨆ i, F.U i) = ⊤ :=
    CFSG.StandardType.SevOm.Frame.iSup_pieces_eq_top F h14' hU2
  have hUa : ∀ v ∈ U, (quadMinus 7 (ZMod 2) 1 1) v = 0 → v = 0 := by
    intro v hv hQv
    rw [hUdef] at hv
    by_contra hv0
    have hmp := (CFSG.StandardType.SevOm.Frame.exists_rot_pair F hAO htop j (hU2 j) hv hv0).1
    rw [hmp.qa] at hQv
    exact one_ne_zero hQv
  have hWm : ¬ CFSG.GroupTheory.WeirSylow.IsPlusType ((quadMinus 7 (ZMod 2) 1 1).comp U.subtype) :=
    CFSG.RankThree.PartOne.S15K.not_isPlusType_of_aniso_plane hU2' hUa
  have hWnd : (polarBilin ((quadMinus 7 (ZMod 2) 1 1).comp U.subtype)).Nondegenerate :=
    CFSG.RankThree.PartOne.S15K.polarBilin_comp_subtype_nondegenerate hnd
  have hQminus : ¬ CFSG.GroupTheory.WeirSylow.IsPlusType (quadMinus 7 (ZMod 2) 1 1) :=
    CFSG.GroupTheory.WeirSylow.not_isPlusType_quadMinus (n := 7) (by norm_num)
      (by decide : ∀ s : ZMod 2, s ^ 2 + 1 * s + 1 ≠ 0)
  have hplusComp : CFSG.GroupTheory.WeirSylow.IsPlusType ((quadMinus 7 (ZMod 2) 1 1).comp
      (perpOf (quadMinus 7 (ZMod 2) 1 1) U).subtype) :=
    (CFSG.LocalAnalysis.GLTheoremA.S172C.Cent.isPlusType_comp_polarPerp_iff hQ
      (n := 7) (by rw [h14]) (by norm_num) hWnd hU2' hWm).mpr hQminus
  have hplus : CFSG.GroupTheory.WeirSylow.IsPlusType ((quadMinus 7 (ZMod 2) 1 1).restrict
      (perpOf (quadMinus 7 (ZMod 2) 1 1) U)) := by
    obtain ⟨W, hW, hWs⟩ := hplusComp
    refine ⟨W, hW, fun v hv => ?_⟩
    have := hWs v hv
    simpa [QuadraticMap.restrict_apply, QuadraticMap.comp_apply] using this
  obtain ⟨ψ⟩ := CFSG.GroupTheory.WeirSylow.nonempty_isometry_quadPlus hP
    (n := 6) (by rw [h12]) hplus
  let Q' : QuadraticForm (ZMod 2) (perpOf (quadMinus 7 (ZMod 2) 1 1) U) :=
    (quadMinus 7 (ZMod 2) 1 1).restrict (perpOf (quadMinus 7 (ZMod 2) 1 1) U)
  let O' := TauCeti.QuadraticMap.orthogonalGroup Q'
  have hAeq : A = (commutator ↥O').map (extG hUc) := commutator_fixW_eq_map hUc
  have horth2 : orthDerived Q' = (commutator ↥O').map O'.subtype := by
    rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]
  have hM0K : (⁅CK', CK'⁆ : Subgroup G) ≤ K :=
    (Subgroup.commutator_le_self CK').trans inf_le_right
  have hDsub : D.map K.subtype = CK' := by
    rw [Subgroup.subgroupOf_map_subtype, inf_of_le_left inf_le_right]
  have hDcomm : (⁅D, D⁆ : Subgroup ↥K).map ι = A := by
    rw [Subgroup.map_commutator, hC'K, hCC]
  have hMD : ⁅D, D⁆ = (⁅CK', CK'⁆ : Subgroup G).subgroupOf K := by
    apply Subgroup.map_injective K.subtype_injective
    rw [Subgroup.map_commutator, hDsub, Subgroup.subgroupOf_map_subtype, inf_of_le_left hM0K]
  have eMA : ↥(⁅CK', CK'⁆ : Subgroup G) ≃* ↥A :=
    (Subgroup.subgroupOfEquivOfLe hM0K).symm.trans
      (((MulEquiv.subgroupCongr hMD).symm).trans
        ((Subgroup.equivMapOfInjective (⁅D, D⁆) ι hι).trans
          (MulEquiv.subgroupCongr hDcomm)))
  have eAO : ↥A ≃* ↥(orthDerived Q') :=
    ((MulEquiv.subgroupCongr hAeq).trans
        (Subgroup.equivMapOfInjective (commutator ↥O') (extG hUc) (extG_injective hUc)).symm).trans
      ((Subgroup.equivMapOfInjective (commutator ↥O') O'.subtype O'.subtype_injective).trans
        (MulEquiv.subgroupCongr horth2.symm))
  have hCK_eq : CK' = Subgroup.centralizer ({B.b 1} : Set G) ⊓ K := by
    show Subgroup.centralizer ({B'.b j.succ} : Set G) ⊓ K = _
    rw [hcent]
  have hcommCK : ⁅Subgroup.centralizer ({B.b 1} : Set G) ⊓ K,
      Subgroup.centralizer ({B.b 1} : Set G) ⊓ K⁆ = ⁅CK', CK'⁆ := by
    rw [hCK_eq]
  exact ⟨(MulEquiv.subgroupCongr hcommCK).trans
    (eMA.trans (eAO.trans (commutatorOrthogonalGroupCongr ψ)))⟩

end TwD7

end CFSG.StandardType.FrameRoute.FS81
