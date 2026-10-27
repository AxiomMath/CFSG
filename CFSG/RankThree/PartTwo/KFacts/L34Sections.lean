module

public import CFSG.RankThree.PartTwo.KFacts.L34SL
public import CFSG.RankThree.PartTwo.Sec4.StatementsGraphField
import CFSG.RankThree.PartTwo.Census.Criteria
import CFSG.RankThree.Coprime.InvolutionFixedRankBound
import CFSG.RankThree.Asc83Table.E27
import CFSG.Models.PGLOrders
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.GroupTheory.HallHigmanPiCore
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LieType.Chevalley.LangRootArithmetic
public import CFSG.LocalAnalysis.ComponentInitial.SuzukiModelSchreier
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiModelPointStructure
public import CFSG.RankThree.PartTwo.Sec4.StatementsCensus
public import CFSG.StronglyEmbedded.ParityCriterion

public section

namespace CFSG.RankThree.PartTwo.KFacts.L34

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.RankThree.PartTwo.Sec4

variable {k : Type*} [Field k]

section Bridge

theorem projSL_eq_range_toPGL (n : ℕ) (K : Type*) [Field K] :
    CFSG.Assembly.RankThreeEven.projSL n K =
      (Matrix.SpecialLinearGroup.toPGL :
        Matrix.SpecialLinearGroup (Fin n) K →* Matrix.ProjGenLinGroup (Fin n) K).range := by
  rw [CFSG.Assembly.RankThreeEven.projSL, CFSG.Assembly.RankThreeEven.projImage,
    Matrix.SpecialLinearGroup.toPGL, MonoidHom.range_comp,
    Matrix.SpecialLinearGroup.range_toGL_eq_ker_det]

@[expose] noncomputable def projSLEquivProjectiveSL (n : ℕ) (K : Type*) [Field K] :
    CFSG.Assembly.RankThreeEven.projSL n K ≃* projectiveSL n K :=
  ((QuotientGroup.quotientMulEquivOfEq
      (by rw [Matrix.SpecialLinearGroup.toPGL_ker, scalars_eq_center] :
        scalars n K = (Matrix.SpecialLinearGroup.toPGL :
          Matrix.SpecialLinearGroup (Fin n) K →* Matrix.ProjGenLinGroup (Fin n) K).ker)).trans
    ((QuotientGroup.quotientKerEquivRange _).trans
      (MulEquiv.subgroupCongr (projSL_eq_range_toPGL n K).symm))).symm

end Bridge

section Transport

theorem pRank_three_of_mulEquiv (hk : Nat.card k = 4) {H : Type*} [Group H]
    (e : H ≃* projectiveSL 3 k) : CFSG.pRank 3 H = 2 := by
  rw [CFSG.RankThree.Asc83Table.pRank_congr e, pRank_three_projectiveSL hk]

theorem localRank_three_of_mulEquiv {k : Type} [Field k] [Finite k] (hk : Nat.card k = 4)
    {H : Type} [Group H] [Finite H] (e : H ≃* projectiveSL 3 k) :
    CFSG.Assembly.RankThreeEven.localRank 3 H = 1 := by
  rw [CFSG.RankThree.PartTwo.Census.localRank_eq_of_mulEquiv e Nat.prime_three,
    localRank_three_projectiveSL hk]

theorem card_galoisField_two_two : Nat.card (GaloisField 2 2) = 4 := by
  rw [GaloisField.card 2 2 (by norm_num)]
  norm_num

theorem pRank_three_projSL :
    CFSG.pRank 3 (CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 2 2)) = 2 :=
  pRank_three_of_mulEquiv card_galoisField_two_two (projSLEquivProjectiveSL 3 _)

instance finite_projSL_galoisField :
    Finite (CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 2 2)) :=
  Finite.of_equiv _ (projSLEquivProjectiveSL 3 (GaloisField 2 2)).symm.toEquiv

theorem localRank_three_projSL :
    CFSG.Assembly.RankThreeEven.localRank 3
      (CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 2 2)) = 1 :=
  localRank_three_of_mulEquiv card_galoisField_two_two (projSLEquivProjectiveSL 3 _)

theorem pRank_three_mulAut_projSL :
    CFSG.pRank 3 (MulAut (CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 2 2))) = 2 :=
  pRank_three_mulAut_of_mulEquiv card_galoisField_two_two (projSLEquivProjectiveSL 3 _)

theorem pRank_three_linearAutGroup (hk : Nat.card k = 4) :
    CFSG.pRank 3 (linearAutGroup 3 k) = 2 := by
  have : Finite (MulAut (projectiveSL 3 k)) :=
    Nat.finite_of_card_ne_zero (by rw [card_mulAut hk]; norm_num)
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  apply le_antisymm
  · calc CFSG.pRank 3 (linearAutGroup 3 k) ≤ CFSG.pRank 3 (MulAut (projectiveSL 3 k)) := by
          rw [CFSG.SectionRank.pRank_eq_open_pRank_top, CFSG.SectionRank.pRank_eq_open_pRank_top]
          exact (CFSG.SectionRank.pRank_le_map (by norm_num) _
            (Subgroup.subtype_injective _) ⊤).trans (CFSG.SectionRank.pRank_mono (by norm_num)
              le_top)
      _ = 2 := pRank_three_mulAut hk
  · have hle : (eZero k).map (MulAut.conj : projectiveSL 3 k →* MulAut (projectiveSL 3 k)) ≤
        linearAutGroup 3 k := by
      rintro _ ⟨x, -, rfl⟩
      obtain ⟨g, rfl⟩ := proj_surjective 3 k x
      rw [← conjAut_toGL]
      exact conjAut_mem_linearAutGroup _
    have := CFSG.RankThree.Asc83Table.IsElementaryAbelian.map_hom
      (MulAut.conj : projectiveSL 3 k →* MulAut (projectiveSL 3 k)) (isElementaryAbelian_eZero hk)
    refine CFSG.RankThree.Coprime.le_pRank_of_isElementaryAbelian (by norm_num)
      (CFSG.IsElementaryAbelian.subgroupOf hle) ?_
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv,
      Subgroup.card_map_of_injective (conj_injective hk), card_eZero hk]
    norm_num

end Transport

section Sections

theorem hasSection_card_dvd {J T : Type*} [Group J] [Group T] [Finite J] (h : HasSection J T) :
    Nat.card T ∣ Nat.card J := by
  obtain ⟨H, N, _, ⟨e⟩⟩ := h
  rw [← Nat.card_congr e.toEquiv]
  exact (Subgroup.card_quotient_dvd_card N).trans (Subgroup.card_subgroup_dvd_card H)

theorem hasSection_congr_right {J T T' : Type*} [Group J] [Group T] [Group T']
    (h : HasSection J T) (e : T ≃* T') : HasSection J T' := by
  obtain ⟨H, N, hN, ⟨f⟩⟩ := h
  exact ⟨H, N, hN, ⟨f.trans e⟩⟩

theorem hasSection_quotient {J : Type*} [Group J] (N : Subgroup J) [N.Normal] :
    HasSection J (J ⧸ N) :=
  ⟨⊤, N.subgroupOf ⊤, inferInstance,
    ⟨QuotientGroup.congr (N.subgroupOf ⊤) N Subgroup.topEquiv (by
      ext x
      simp [Subgroup.mem_subgroupOf])⟩⟩

theorem hasSection_of_injective {J J' T : Type*} [Group J] [Group J'] [Group T]
    (h : HasSection J T) (f : J →* J') (hf : Function.Injective f) : HasSection J' T := by
  obtain ⟨H, N, hN, ⟨e⟩⟩ := h
  let φ : H ≃* H.map f := Subgroup.equivMapOfInjective H f hf
  have hN' : (N.map φ.toMonoidHom).Normal := Subgroup.Normal.map hN _ φ.surjective
  refine ⟨H.map f, N.map φ.toMonoidHom, hN', ⟨?_⟩⟩
  exact (QuotientGroup.congr N (N.map φ.toMonoidHom) φ rfl).symm.trans e

theorem hasSection_specialLinearGroup (K : Type*) [Field K] :
    HasSection (Matrix.SpecialLinearGroup (Fin 3) K) (projectiveSL 3 K) :=
  hasSection_quotient (scalars 3 K)

theorem hasSection_specialLinearGroup_galoisField {n : ℕ} (hn : 1 ≤ n) :
    HasSection (Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 (2 * n)))
      (CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 2 2)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨φ⟩ : Nonempty (GaloisField 2 2 →ₐ[ZMod 2] GaloisField 2 (2 * n)) := by
    refine FiniteField.nonempty_algHom_of_finrank_dvd ?_
    rw [GaloisField.finrank 2 (by norm_num), GaloisField.finrank 2 (by omega)]
    exact dvd_mul_right 2 n
  have hinj : Function.Injective (Matrix.SpecialLinearGroup.map φ.toRingHom :
      Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 2) →* _) := by
    intro A B hAB
    apply Subtype.ext
    ext i j
    have := congrFun (congrFun (congrArg (fun C : Matrix.SpecialLinearGroup (Fin 3) _ =>
      (C : Matrix (Fin 3) (Fin 3) (GaloisField 2 (2 * n)))) hAB) i) j
    simpa using φ.toRingHom.injective this
  exact hasSection_congr_right
    (hasSection_of_injective (hasSection_specialLinearGroup (GaloisField 2 2)) _ hinj)
    (projSLEquivProjectiveSL 3 (GaloisField 2 2)).symm

theorem card_projSL :
    Nat.card (CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 2 2)) = 20160 :=
  CFSG.PGLModel.card_projSL_three_four

theorem not_hasSection_of_not_dvd {J : Type*} [Group J] [Finite J] (h : ¬ 20160 ∣ Nat.card J) :
    ¬ HasSection J (CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 2 2)) := fun hs =>
  h (card_projSL ▸ hasSection_card_dvd hs)

theorem card_of_isExtOf {X A B : Type*} [Group X] [Group A] [Group B] (h : IsExtOf X A B) :
    Nat.card X = Nat.card A * Nat.card B := by
  obtain ⟨K, _, ⟨e₁⟩, ⟨e₂⟩⟩ := h
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup K, Nat.card_congr e₁.toEquiv,
    Nat.card_congr e₂.toEquiv]

theorem not_hasSection_of_isExtOf_alternating {X : Type*} [Group X] {m : ℕ} (hm : m = 6 ∨ m = 7)
    (h : IsExtOf X (alternatingGroup (Fin m)) (Multiplicative (ZMod 3))) :
    ¬ HasSection X (CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 2 2)) := by
  have hcard := card_of_isExtOf h
  have h3 : Nat.card (Multiplicative (ZMod 3)) = 3 := by
    rw [Nat.card_eq_fintype_card]
    rfl
  rcases hm with rfl | rfl
  · rw [nat_card_alternatingGroup, h3, Nat.card_fin] at hcard
    have : Finite X := Nat.finite_of_card_ne_zero (by rw [hcard]; decide)
    exact not_hasSection_of_not_dvd (by rw [hcard]; decide)
  · rw [nat_card_alternatingGroup, h3, Nat.card_fin] at hcard
    have : Finite X := Nat.finite_of_card_ne_zero (by rw [hcard]; decide)
    exact not_hasSection_of_not_dvd (by rw [hcard]; decide)

end Sections

section Central

variable {X : Type} [Group X] {U V : Subgroup X}

theorem card_center_of_mulEquiv
    (e : V ≃* Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 2)) :
    Nat.card (Subgroup.center V) = 3 := by
  rw [← card_center_specialLinearGroup card_galoisField_two_two, ← Subgroup.map_center_eq e,
    Subgroup.card_map_of_injective e.injective]

theorem mem_inf_of_mem_center_right (hUV : ∀ u ∈ U, ∀ v ∈ V, u * v = v * u) {x : X}
    (hxU : x ∈ U) (hxV : x ∈ V) : (⟨x, hxU⟩ : U) ∈ Subgroup.center U ∧
      (⟨x, hxV⟩ : V) ∈ Subgroup.center V := by
  refine ⟨Subgroup.mem_center_iff.mpr fun w => Subtype.ext ?_,
    Subgroup.mem_center_iff.mpr fun w => Subtype.ext ?_⟩
  · exact (hUV w w.2 x hxV)
  · exact (hUV x hxU w w.2).symm

theorem inf_eq_map_center_left (hUV : ∀ u ∈ U, ∀ v ∈ V, u * v = v * u) (hU : IsHeisThree U)
    (h3 : Nat.card (U ⊓ V : Subgroup X) = 3) : U ⊓ V = (Subgroup.center U).map U.subtype := by
  have hcard : Nat.card ((Subgroup.center U).map U.subtype) = 3 := by
    rw [Subgroup.card_map_of_injective U.subtype_injective]
    exact hU.1.2.2.2
  have : Finite ((Subgroup.center U).map U.subtype) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  refine (Subgroup.eq_of_le_of_card_ge ?_ (by rw [hcard, h3])).symm |>.symm
  rintro x ⟨hxU, hxV⟩
  exact ⟨⟨x, hxU⟩, (mem_inf_of_mem_center_right hUV hxU hxV).1, rfl⟩

theorem inf_eq_map_center_right (hUV : ∀ u ∈ U, ∀ v ∈ V, u * v = v * u)
    (hV : Nonempty (V ≃* Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 2)))
    (h3 : Nat.card (U ⊓ V : Subgroup X) = 3) : U ⊓ V = (Subgroup.center V).map V.subtype := by
  obtain ⟨e⟩ := hV
  have hcard : Nat.card ((Subgroup.center V).map V.subtype) = 3 := by
    rw [Subgroup.card_map_of_injective V.subtype_injective, card_center_of_mulEquiv e]
  have : Finite ((Subgroup.center V).map V.subtype) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  refine Subgroup.eq_of_le_of_card_ge ?_ (by rw [hcard, h3])
  rintro x ⟨hxU, hxV⟩
  exact ⟨⟨x, hxV⟩, (mem_inf_of_mem_center_right hUV hxU hxV).2, rfl⟩

theorem exists_mul_eq_of_sup_eq_top (hsup : U ⊔ V = ⊤) (hUV : ∀ u ∈ U, ∀ v ∈ V, u * v = v * u)
    (x : X) : ∃ u ∈ U, ∃ v ∈ V, u * v = x := by
  have hle : U ≤ Subgroup.normalizer (V : Set X) := fun u hu =>
    Subgroup.mem_normalizer_iff.mpr fun v => by
      constructor
      · intro hv
        rw [show u * v * u⁻¹ = v by rw [hUV u hu v hv]; group]
        exact hv
      · intro hv
        have h := hUV u hu (u * v * u⁻¹) hv
        have hv' : v = u * v * u⁻¹ := by
          calc v = u⁻¹ * ((u * v * u⁻¹) * u) := by group
            _ = u⁻¹ * (u * (u * v * u⁻¹)) := by rw [← h]
            _ = u * v * u⁻¹ := by group
        rw [hv']
        exact hv
  have hx : x ∈ ((U ⊔ V : Subgroup X) : Set X) := by rw [hsup]; trivial
  rw [Subgroup.coe_mul_of_left_le_normalizer_right U V hle] at hx
  obtain ⟨u, hu, v, hv, rfl⟩ := hx
  exact ⟨u, hu, v, hv, rfl⟩

theorem centralizer_eq_of_isHeisSL (hsup : U ⊔ V = ⊤) (hUV : ∀ u ∈ U, ∀ v ∈ V, u * v = v * u)
    (hV : Nonempty (V ≃* Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 2)))
    (h3 : Nat.card (U ⊓ V : Subgroup X) = 3) :
    Subgroup.centralizer (V : Set X) = U := by
  apply le_antisymm
  · intro x hx
    obtain ⟨u, hu, v, hv, rfl⟩ := exists_mul_eq_of_sup_eq_top hsup hUV x
    rw [Subgroup.mem_centralizer_iff] at hx
    have hvc : (⟨v, hv⟩ : V) ∈ Subgroup.center V := by
      refine Subgroup.mem_center_iff.mpr fun w => Subtype.ext ?_
      change (w : X) * v = v * w
      have h1 := hx w w.2
      have h2 := hUV u hu w w.2
      calc (w : X) * v = u⁻¹ * ((u * w) * v) := by group
        _ = u⁻¹ * ((w * u) * v) := by rw [h2]
        _ = u⁻¹ * (w * (u * v)) := by group
        _ = u⁻¹ * (u * v * w) := by rw [h1]
        _ = v * w := by group
    have hvU : v ∈ U := by
      have : v ∈ U ⊓ V := by
        rw [inf_eq_map_center_right hUV hV h3]
        exact ⟨⟨v, hv⟩, hvc, rfl⟩
      exact this.1
    exact mul_mem hu hvU
  · intro u hu
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    exact (hUV u hu v hv).symm

theorem center_eq_inf_of_isHeisSL (hsup : U ⊔ V = ⊤) (hUV : ∀ u ∈ U, ∀ v ∈ V, u * v = v * u)
    (hU : IsHeisThree U) (hV : Nonempty (V ≃* Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 2)))
    (h3 : Nat.card (U ⊓ V : Subgroup X) = 3) :
    Subgroup.center X = U ⊓ V := by
  apply le_antisymm
  · intro z hz
    have hzU : z ∈ U := by
      rw [← centralizer_eq_of_isHeisSL hsup hUV hV h3, Subgroup.mem_centralizer_iff]
      intro v _
      exact (Subgroup.mem_center_iff.mp hz v)
    have hzc : (⟨z, hzU⟩ : U) ∈ Subgroup.center U :=
      Subgroup.mem_center_iff.mpr fun w => Subtype.ext (Subgroup.mem_center_iff.mp hz w)
    rw [inf_eq_map_center_left hUV hU h3]
    exact ⟨⟨z, hzU⟩, hzc, rfl⟩
  · rintro z ⟨hzU, hzV⟩
    rw [Subgroup.mem_center_iff]
    intro x
    obtain ⟨u, hu, v, hv, rfl⟩ := exists_mul_eq_of_sup_eq_top hsup hUV x
    have h1 := (mem_inf_of_mem_center_right hUV hzU hzV).1
    have h2 := (mem_inf_of_mem_center_right hUV hzU hzV).2
    have hzu : u * z = z * u :=
      congrArg Subtype.val (Subgroup.mem_center_iff.mp h1 ⟨u, hu⟩)
    have hzv : v * z = z * v :=
      congrArg Subtype.val (Subgroup.mem_center_iff.mp h2 ⟨v, hv⟩)
    rw [mul_assoc, hzv, ← mul_assoc, hzu, mul_assoc]

end Central


end CFSG.RankThree.PartTwo.KFacts.L34
