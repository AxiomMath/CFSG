module

public import CFSG.Timmesfeld.LieEmbed.SpF4
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotLeviSp6
public import CFSG.LocalAnalysis.StandardType.GGSelectedF2
public import CFSG.LieType.Steinberg.Classical.Symplectic.RankOne
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotNonsplit
public import CFSG.LocalAnalysis.StandardType.GGTableBF4TwoInputsEndNode
public import CFSG.LocalAnalysis.StandardType.GGSecFiveFieldTwoExc
public import CFSG.LocalAnalysis.StandardType.GGPsiDiagInnerMinus
public import CFSG.RankThree.PartTwo.Sec21.FF81F4Syl3
public import CFSG.RankThree.PartTwo.Sec21.FF81F4Syl3C
public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallExcC5F4ThreeC
public import CFSG.GroupTheory.IsComponentOfMap
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotGraphSpinModelF4
import CFSG.GH74.Generic.S1.Exo.NbLoc
import CFSG.LieType.Ree.Endo
import CFSG.LieType.Chevalley.CoordinateFieldBaseChange
import CFSG.LieType.Chevalley.EvenQuadraticGraphFieldDescent
public import CFSG.Quasithin.Vol2.KGFactC31RuRef
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotGraphSpinModelGen
public import CFSG.RankThree.PartTwo.Sec21.FF81F4Ord3
import CFSG.GH74.Generic.S1.Exo.NbDefs

public section

namespace CFSG.StandardType.FieldTwoF4

open CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Adjoint
  CFSG.Timmesfeld.LieEmbed CFSG.SeitzReduction.F4Pilot CFSG.StandardType.RankOneXfer
  CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.Open CFSG.LieType.Universal.Symplectic
  CFSG.StandardType.TableBF4TwoInputs

section C3Levi


theorem exists_c3Levi_rootLift (K : Type) [Field K] [Finite K] [CharP K 2] :
    ∃ rho : ↥(StatedSp 3 K) →* ↥(adjointGroup .F4 K), Function.Injective rho ∧
      rho.range = C3Levi K ∧
      ∃ phi' : Matrix.SpecialLinearGroup (Fin 2) K →* ↥(StatedSp 3 K), Function.Injective phi' ∧
        (sl2UpperUniSub K).map phi' = (Symplectic.rootDatum 3 K).rootGroup (Pi.single (0 : Fin 3) 1) ∧
        (sl2UpperUniSub K).map (rho.comp phi') =
          (f4Datum K).rootGroup (c3ToF4 (Pi.single (0 : Fin 3) 1)) := by
  set e := c3LeviEquivOfRingEquiv K (RingEquiv.refl K) with he
  let rho : ↥(StatedSp 3 K) →* ↥(adjointGroup .F4 K) := (C3Levi K).subtype.comp e.symm.toMonoidHom
  have hrho : ∀ γ ∈ roots (isFiniteType_cartanC 3) ∅, ∀ c : K,
      rho (Sp.x 3 K γ c) = f4Par K (c3ToF4 γ) c := by
    intro γ hγ c
    have h := c3LeviEquivOfRingEquiv_f4Par (K := K) (RingEquiv.refl K) hγ c
    have h' : e.symm (Sp.x 3 K γ c) = ⟨f4Par K (c3ToF4 γ) c,
        f4Par_mem_C3Levi (c3ToF4_mem_c3LeviRoots hγ) c⟩ := by
      rw [MulEquiv.symm_apply_eq, he, h]
      rfl
    show ((e.symm (Sp.x 3 K γ c) : ↥(C3Levi K)) : ↥(adjointGroup .F4 K)) = f4Par K (c3ToF4 γ) c
    rw [h']
  obtain ⟨phi', hinj', hU, -⟩ := Sp.rankOne (n := 3) (F := K) 0
  have hβ₀ : (Pi.single 0 1 : Fin 3 → ℤ) ∈ roots (isFiniteType_cartanC 3) ∅ :=
    Or.inl ⟨1, 0, by simp⟩
  have hupper' : (sl2UpperUniSub K).map phi' =
      (Symplectic.rootDatum 3 K).rootGroup (Pi.single (0 : Fin 3) 1) := by
    ext g
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨A, ⟨c, rfl⟩, rfl⟩
      rw [hU c]
      exact ((Sp.isParametrization (Pi.single 0 1) hβ₀).1 _).2 ⟨c, rfl⟩
    · intro hg
      obtain ⟨c, rfl⟩ := ((Sp.isParametrization (Pi.single 0 1) hβ₀).1 g).1 hg
      exact ⟨sl2Upper c, ⟨c, rfl⟩, hU c⟩
  refine ⟨rho, Subtype.val_injective.comp e.symm.injective, ?_, phi', hinj', hupper', ?_⟩
  · ext g
    constructor
    · rintro ⟨y, rfl⟩
      exact (e.symm y).2
    · intro hg
      exact ⟨e ⟨g, hg⟩, by simp [rho]⟩
  · rw [← Subgroup.map_map, hupper']
    ext g
    rw [Subgroup.mem_map, Adjoint.mem_rootGroup_iff (isRoot_c3ToF4 hβ₀)]
    constructor
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨c, rfl⟩ := ((Sp.isParametrization (Pi.single 0 1) hβ₀).1 y).1 hy
      exact ⟨c, (hrho _ hβ₀ c).symm⟩
    · rintro ⟨c, rfl⟩
      exact ⟨Sp.x 3 K _ c, ((Sp.isParametrization (Pi.single 0 1) hβ₀).1 _).2 ⟨c, rfl⟩,
        hrho _ hβ₀ c⟩

end C3Levi

section Component


theorem eq_c3Levi_of_isComponentOf (K : Type) [Field K] [Finite K] [CharP K 2]
    (hK : Nat.card K = 2) {M : Subgroup ↥(adjointGroup .F4 K)}
    (hM : CFSG.Assembly.IsComponentOf M
      (Subgroup.centralizer ({nodeElt K} : Set ↥(adjointGroup .F4 K)))) :
    M = C3Levi K := by
  obtain ⟨-, -, hXD⟩ := centralizer_nonsplit (K := K) zpowers_nodeElt_le
    (Subgroup.isCyclic_zpowers _) (card_zpowers_nodeElt hK)
  have hcen := centralizer_singleton_eq_zpowers (nodeElt K)
  have hMC : M ≤ Subgroup.centralizer (Subgroup.zpowers (nodeElt K) : Set _) := hcen ▸ hM.1
  have hcomm : ∀ d ∈ C3Levi K, ∀ y ∈ Subgroup.zpowers (nodeElt K), d * y = y * d :=
    fun d hd y hy => Subgroup.mem_centralizer_iff.1 (hXD hy) d hd
  have hperf : Group.IsPerfect ↥M := Group.IsPerfect.mk hM.2.2.1
  have hMD : M ≤ C3Levi K := CFSG.GH74.Generic.S1.Exo.nb_perfect_le_of_comm_pair hcomm
    (fun y hy y' hy' => by
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy'
      rw [← zpow_add, ← zpow_add, add_comm])
    hperf (fun g hg => by
      obtain ⟨y, hy, d, hd, rfl⟩ := exists_mul_of_mem_centralizer_nonsplit zpowers_nodeElt_le
        (Subgroup.isCyclic_zpowers _) (card_zpowers_nodeElt hK) (hMC hg)
      exact ⟨d, hd, y, hy, (hcomm d hd y hy).symm⟩)
  have hDC : C3Levi K ≤ Subgroup.centralizer ({nodeElt K} : Set ↥(adjointGroup .F4 K)) := by
    rw [hcen]
    exact Subgroup.le_centralizer_iff.1 hXD
  have hcomp := hM.of_le_of_le hMD hDC
  rcases hcomp.2.1.eq_bot_or_eq_of_isSimpleGroup isSimpleGroup_C3Levi with h | h
  · exfalso
    have hnt : Nontrivial (↥M ⧸ Subgroup.center ↥M) := hM.2.2.2.toNontrivial
    have hM1 : Subsingleton ↥M := by
      rw [h]
      infer_instance
    have hS : Subsingleton (↥M ⧸ Subgroup.center ↥M) :=
      (QuotientGroup.mk'_surjective (Subgroup.center ↥M)).subsingleton
    exact false_of_nontrivial_of_subsingleton (↥M ⧸ Subgroup.center ↥M)
  · exact h

end Component

section Actor


theorem exists_inner_rep {G : Type} [Group G] [Finite G] {n f : ℕ}
    {ψ : (ggU .F4 n f).K →* G} {G₀ : Subgroup G}
    (hpres : GGPresentsG0 G₀ (ggU .F4 n f).D .F4 n f ψ) {x : G}
    (hdiag : GGPsiInnerDiag (ggU .F4 n f).D ψ x) :
    ∃ g : (ggU .F4 n f).K, ∀ u, x * ψ u * x⁻¹ = ψ (g * u * g⁻¹) := by
  have hxN := FieldTwoExc.ggPsiInnerDiag_mem_normalizer_exc (Or.inl rfl : FieldTwoExc.GGExcFour .F4)
    hpres hdiag
  obtain ⟨h, hhG, hc⟩ := ggPsiDiagInnerAt_of_ggInnerTag .F4
    (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) G n f ψ G₀ hpres x hxN hdiag
  rw [← hpres.2.1.1] at hhG
  obtain ⟨h', rfl⟩ := hhG
  refine ⟨h'⁻¹, fun u => ?_⟩
  have hmem : ψ (h'⁻¹ * u * h') ∈ (G₀ : Set G) := by
    rw [← hpres.2.1.1]
    exact ⟨_, rfl⟩
  have hcw := Subgroup.mem_centralizer_iff.1 hc _ hmem
  have key : (ψ h')⁻¹ * ψ u * ψ h' * x * ψ h' = x * ψ u * ψ h' := by
    simpa [map_mul, map_inv, mul_assoc] using hcw
  have key2 : (ψ h')⁻¹ * ψ u * ψ h' * x = x * ψ u := mul_right_cancel key
  rw [inv_inv, map_mul, map_mul, map_inv, ← key2]
  group

end Actor

section Classify

open CFSG.LieType.Chevalley


theorem adjointGroupCongr_rho {K M : Type} [Field K] [Field M] (e : K ≃+* M) (i : Fin 4) :
    CFSG.HardMathSupport.Lang.AnisoE6.adjointGroupCongr (τ := .F4) e
        (TableBF4Two.rho K i (uSL 1 * vSL 1)) = TableBF4Two.rho M i (uSL 1 * vSL 1) := by
  apply Subtype.ext
  change baseChangeGL e.toRingHom (rootSL2 .F4 K (TableBF4Two.orthRoot i) (uSL 1 * vSL 1)) =
    rootSL2 .F4 M (TableBF4Two.orthRoot i) (uSL 1 * vSL 1)
  have hu : Matrix.SpecialLinearGroup.map e.toRingHom (uSL (1 : K)) = uSL 1 := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.map_apply_coe]
    ext a b
    fin_cases a <;> fin_cases b <;> simp [uSL]
  have hv : Matrix.SpecialLinearGroup.map e.toRingHom (vSL (1 : K)) = vSL 1 := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.map_apply_coe]
    ext a b
    fin_cases a <;> fin_cases b <;> simp [vSL]
  rw [CFSG.RankThree.Chevalley.baseChangeGL_rootSL2_of_field, map_mul, hu, hv]

theorem order_three_cases_of_card_two {K : Type} [Field K]
    [Finite K] [CharP K 2] (hK : Nat.card K = 2) {g : adjointGroup .F4 K} (hg : orderOf g = 3) :
    (∃ c, c * g * c⁻¹ = TableBF4Two.rho K 3 (uSL 1 * vSL 1)) ∨
      (∃ c, c * g * c⁻¹ =
        TableBF4Two.rho K 0 (uSL 1 * vSL 1) * TableBF4Two.rho K 1 (uSL 1 * vSL 1)) ∨
      (∃ c, c * g * c⁻¹ =
        (TableBF4Two.rho K 0 (uSL 1 * vSL 1) * TableBF4Two.rho K 0 (uSL 1 * vSL 1)) *
          (TableBF4Two.rho K 1 (uSL 1 * vSL 1) * TableBF4Two.rho K 1 (uSL 1 * vSL 1)) *
          (TableBF4Two.rho K 2 (uSL 1 * vSL 1) * TableBF4Two.rho K 2 (uSL 1 * vSL 1))) := by
  classical
  haveI := Fintype.ofFinite K
  let e : K ≃+* ZMod 2 :=
    (ZMod.ringEquiv K (by rw [← Nat.card_eq_fintype_card, hK])).symm
  let Φ := CFSG.HardMathSupport.Lang.AnisoE6.adjointGroupCongr (τ := .F4) e
  have hs : ∀ i, Φ (TableBF4Two.rho K i (uSL 1 * vSL 1)) =
      TableBF4Two.rho (ZMod 2) i (uSL 1 * vSL 1) := adjointGroupCongr_rho e
  have hΦg : orderOf (Φ g) = 3 := by rw [MulEquiv.orderOf_eq]; exact hg
  have hcases := CFSG.RankThree.PartTwo.Sec21.FF81.F4.order_three_cases (x := Φ g) hΦg
  have key : ∀ (c : adjointGroup .F4 (ZMod 2)) (y : adjointGroup .F4 K),
      c * Φ g * c⁻¹ = Φ y → ∃ c', c' * g * c'⁻¹ = y := fun c y h =>
    ⟨Φ.symm c, Φ.injective (by rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]; exact h)⟩
  rcases hcases with ⟨c, hc⟩ | ⟨c, hc⟩ | ⟨c, hc⟩
  · exact Or.inl (key c _ (hc.trans (hs 3).symm))
  · refine Or.inr (Or.inl (key c _ (hc.trans ?_)))
    rw [map_mul Φ, hs, hs]
    rfl
  · refine Or.inr (Or.inr (key c _ (hc.trans ?_)))
    simp only [map_mul Φ, hs]
    rfl

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree in
theorem phi_link_of_card_two {K : Type} [Field K] [Finite K]
    [CharP K ReeTag.F4.prime] (hK : Nat.card K = 2) :
    ∃ d : adjointGroup ReeTag.F4.tag K,
      d * ReeTag.F4.finiteExceptionalAut K (TableBF4Two.rho K 3 (uSL 1 * vSL 1)) * d⁻¹ =
        TableBF4Two.rho K 0 (uSL 1 * vSL 1) * TableBF4Two.rho K 1 (uSL 1 * vSL 1) := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have : CharP (ZMod 2) ReeTag.F4.prime := inferInstanceAs (CharP (ZMod 2) 2)
  let e : ZMod 2 ≃+* K := ZMod.ringEquiv K (by rw [← Nat.card_eq_fintype_card, hK]; rfl)
  let B := adjointBaseChangeHom ReeTag.F4.tag e.toRingHom
  have hs : ∀ i, B (TableBF4Two.rho (ZMod 2) i (uSL 1 * vSL 1)) =
      TableBF4Two.rho K i (uSL 1 * vSL 1) :=
    fun i => Subtype.ext (congrArg Subtype.val (adjointGroupCongr_rho e i))
  have hx : ∀ (i : Fin ReeTag.F4.tag.rank) (c : ZMod 2),
      B (xElement i c) = xElement i (e.toRingHom c) :=
    fun i c => Subtype.ext (baseChangeGL_xUnit _ i c)
  have hy : ∀ (i : Fin ReeTag.F4.tag.rank) (c : ZMod 2),
      B (yElement i c) = yElement i (e.toRingHom c) :=
    fun i c => Subtype.ext (baseChangeGL_yUnit _ i c)
  have hcomm := adjointGroup_hom_ext
    (f := B.comp (ReeTag.F4.finiteExceptionalAut (ZMod 2)).toMonoidHom)
    (g := (ReeTag.F4.finiteExceptionalAut K).toMonoidHom.comp B)
    (fun i c => by
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
      rw [ReeTag.finiteExceptionalAut_xElement, hx, hx, ReeTag.finiteExceptionalAut_xElement,
        map_pow])
    (fun i c => by
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
      rw [ReeTag.finiteExceptionalAut_yElement, hy, hy, ReeTag.finiteExceptionalAut_yElement,
        map_pow])
  obtain ⟨c, hc⟩ := isConj_iff.1 CFSG.RankThree.PartTwo.Sec21.FF81.F4.phi_link_C
  refine ⟨B c, ?_⟩
  have h2 : B (ReeTag.F4.finiteExceptionalAut (ZMod 2) CFSG.RankThree.PartTwo.Sec21.FF81.F4.rAE) =
      ReeTag.F4.finiteExceptionalAut K (TableBF4Two.rho K 3 (uSL 1 * vSL 1)) := by
    rw [← hs 3]
    exact DFunLike.congr_fun hcomm _
  calc B c * ReeTag.F4.finiteExceptionalAut K (TableBF4Two.rho K 3 (uSL 1 * vSL 1)) * (B c)⁻¹
      = B (c * ReeTag.F4.finiteExceptionalAut (ZMod 2) CFSG.RankThree.PartTwo.Sec21.FF81.F4.rAE *
          c⁻¹) := by rw [map_mul B, map_mul B, map_inv B, h2]
    _ = B CFSG.RankThree.PartTwo.Sec21.FF81.F4.rBE := by rw [hc]
    _ = _ := by rw [map_mul B, hs, hs]; rfl

end Classify


section Cases

open CFSG.LieType.Chevalley


theorem isComponentOf_map_centralizer {U : Type} [Group U] (Θ : U ≃* U) {g : U}
    {M : Subgroup U} (hM : CFSG.Assembly.IsComponentOf M (Subgroup.centralizer {g})) :
    CFSG.Assembly.IsComponentOf (M.map Θ.toMonoidHom) (Subgroup.centralizer {Θ g}) := by
  have h := CFSG.isComponentOf_map_mulEquiv Θ (CFSG.Assembly.isComponentOf_iff_open.mp hM)
  have hC : (Subgroup.centralizer ({g} : Set U)).map Θ.toMonoidHom =
      Subgroup.centralizer {Θ g} := by
    ext y
    rw [Subgroup.mem_map_equiv, Subgroup.mem_centralizer_singleton_iff,
      Subgroup.mem_centralizer_singleton_iff, ← Θ.injective.eq_iff, map_mul, map_mul,
      MulEquiv.apply_symm_apply]
  rw [hC] at h
  exact CFSG.Assembly.isComponentOf_iff_open.mpr h

theorem not_isComponentOf_centralizer_zFrame {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK : Nat.card K = 2) {M : Subgroup (adjointGroup .F4 K)}
    (hM : CFSG.Assembly.IsComponentOf M (Subgroup.centralizer
      {(TableBF4Two.rho K 0 (uSL 1 * vSL 1) * TableBF4Two.rho K 0 (uSL 1 * vSL 1)) *
        (TableBF4Two.rho K 1 (uSL 1 * vSL 1) * TableBF4Two.rho K 1 (uSL 1 * vSL 1)) *
        (TableBF4Two.rho K 2 (uSL 1 * vSL 1) * TableBF4Two.rho K 2 (uSL 1 * vSL 1))})) :
    False := by
  set δ := TableBF4Two.torus3 K (fun _ => Multiplicative.ofAdd (1 : ZMod 3)) with hδ
  have hsolv : Group.IsSolvable (Subgroup.centralizer ({δ} : Set (adjointGroup .F4 K))) :=
    SmallExc.F4Two.ggF4TwoThreeCSolv hK
  have hz : (TableBF4Two.rho K 0 (uSL 1 * vSL 1) * TableBF4Two.rho K 0 (uSL 1 * vSL 1)) *
      (TableBF4Two.rho K 1 (uSL 1 * vSL 1) * TableBF4Two.rho K 1 (uSL 1 * vSL 1)) *
      (TableBF4Two.rho K 2 (uSL 1 * vSL 1) * TableBF4Two.rho K 2 (uSL 1 * vSL 1)) = δ * δ := by
    have e : ∀ j : Fin 3, TableBF4Two.rho K j.castSucc (uSL 1 * vSL 1) =
        TableBF4Two.torus3 K (Pi.mulSingle j (Multiplicative.ofAdd 1)) :=
      fun j => torusGen_eq_torus3 j
    rw [show (0 : Fin 4) = (0 : Fin 3).castSucc from rfl, show (1 : Fin 4) = (1 : Fin 3).castSucc
      from rfl, show (2 : Fin 4) = (2 : Fin 3).castSucc from rfl, e, e, e, hδ, ← map_mul,
      ← map_mul, ← map_mul, ← map_mul, ← map_mul, ← map_mul]
    congr 1
    funext j
    fin_cases j <;> rfl
  have hδ3 : δ ^ 3 = 1 := by
    have hv3 : (fun _ => Multiplicative.ofAdd (1 : ZMod 3) : Fin 3 → Multiplicative (ZMod 3)) ^ 3 =
        1 := by decide +kernel
    rw [hδ, ← map_pow, hv3, map_one]
  have hle : M ≤ Subgroup.centralizer ({δ} : Set (adjointGroup .F4 K)) := by
    intro y hy
    have hyz := Subgroup.mem_centralizer_singleton_iff.1 (hM.1 hy)
    rw [hz] at hyz
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hc : Commute y (δ * δ) := hyz
    have h4 : (δ * δ) * (δ * δ) = δ := by
      rw [← pow_two, ← pow_two, ← pow_mul, show 2 * 2 = 3 + 1 from rfl, pow_succ, hδ3, one_mul]
    have := hc.mul_right hc
    rw [h4] at this
    exact this
  have hMsolv : Group.IsSolvable ↥M :=
    solvable_of_solvable_injective (Subgroup.inclusion_injective hle)
  obtain ⟨hperf, hsimp⟩ := hM.2.2
  haveI : Group.IsPerfect ↥M := ⟨hperf⟩
  haveI : Nontrivial ↥M := by
    by_contra hnt
    rw [not_nontrivial_iff_subsingleton] at hnt
    exact hsimp.toNontrivial.exists_pair_ne.elim fun a ha => ha.elim fun b hb =>
      hb (Subsingleton.elim a b)
  exact Group.IsPerfect.not_isSolvable ↥M hMsolv

theorem map_rootGroup_three_of_exceptionalAut {K : Type} [Field K] [Finite K]
    [CharP K CFSG.LieType.Ree.ReeTag.F4.prime] (hK : Nat.card K = 2)
    (φ' : MulAut ↥(adjointGroup .F4 K))
    (hφ' : ∀ x, φ' x = CFSG.LieType.Ree.ReeTag.F4.finiteExceptionalAut K x) :
    ((f4Datum K).rootGroup (Pi.single (3 : Fin (Tag.rank .F4)) 1)).map φ'.toMonoidHom =
      (f4Datum K).rootGroup (Pi.single (0 : Fin (Tag.rank .F4)) 1) := by
  haveI : CharP K 2 := ‹CharP K CFSG.LieType.Ree.ReeTag.F4.prime›
  have hβ : IsRoot .F4 (Pi.single (3 : Fin (Tag.rank .F4)) 1) := isRoot_single .F4 3
  have hβ' : IsRoot .F4 (Pi.single (0 : Fin (Tag.rank .F4)) 1) := isRoot_single .F4 0
  have hshort : (Pi.single 3 1 : Fin CFSG.LieType.Ree.ReeTag.F4.tag.rank → ℤ) ∈
      CFSG.LieType.Ree.ReeTag.F4.shortRoots :=
    ⟨hβ, CFSG.LieType.Ree.ReeTag.lengthParam_eq_one_iff.2 (by decide)⟩
  have hdual : CFSG.LieType.Ree.ReeTag.F4.dualRoot
      (Pi.single 3 1 : Fin CFSG.LieType.Ree.ReeTag.F4.tag.rank → ℤ) = Pi.single 0 1 := by
    decide
  have hsq : ∀ c : K, c ^ 2 = c := fun c => by
    haveI := Fintype.ofFinite K
    have h := FiniteField.pow_card c
    rwa [← Nat.card_eq_fintype_card, hK] at h
  have hφ : ∀ c : K, φ' (f4Par K (Pi.single (3 : Fin (Tag.rank .F4)) 1) c) =
      f4Par K (Pi.single (0 : Fin (Tag.rank .F4)) 1) c := fun c =>
    (hφ' _).trans ((congrArg (CFSG.LieType.Ree.ReeTag.F4.finiteExceptionalAut K)
      (f4Par_eq_pinnedX_charTwo hβ c)).trans
      ((CFSG.LieType.Chevalley.finiteExceptionalAut_pinnedX_short hshort c).trans
        ((Subtype.ext (congrArg₂ (pinnedX Tag.F4 K) hdual (hsq c))).trans
          (f4Par_eq_pinnedX_charTwo hβ' c).symm)))
  ext y
  rw [Subgroup.mem_map, Adjoint.mem_rootGroup_iff hβ']
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨c, rfl⟩ := (Adjoint.mem_rootGroup_iff hβ x).1 hx
    exact ⟨c, (hφ c).symm⟩
  · rintro ⟨c, rfl⟩
    exact ⟨f4Par K (Pi.single (3 : Fin (Tag.rank .F4)) 1) c,
      (Adjoint.mem_rootGroup_iff hβ _).2 ⟨c, rfl⟩, hφ c⟩


theorem selected_of_rootLift {G : Type} [Group G] [Finite G] {ψ : (ggU .F4 0 1).K →* G}
    (hψ : Function.Injective ψ) {L : Subgroup G}
    {rho : ↥(StatedSp 3 (GaloisField 2 1)) →* ↥(adjointGroup .F4 (GaloisField 2 1))}
    (hrho : Function.Injective rho)
    {phi' : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 1) →* ↥(StatedSp 3 (GaloisField 2 1))}
    (hphi' : Function.Injective phi')
    (hU' : (sl2UpperUniSub (GaloisField 2 1)).map phi' =
      (Symplectic.rootDatum 3 (GaloisField 2 1)).rootGroup (Pi.single (0 : Fin 3) 1))
    (σ : MulAut ↥(adjointGroup .F4 (GaloisField 2 1)))
    (hL : (rho.range.map σ.toMonoidHom).map ψ = L)
    {γ : Fin (Tag.rank .F4) → ℤ} (hγ : IsRoot .F4 γ) (u₀ : ↥(adjointGroup .F4 (GaloisField 2 1)))
    (χ : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 1) →* ↥(adjointGroup .F4 (GaloisField 2 1)))
    (hχ : Function.Injective χ)
    (hχU : (sl2UpperUniSub (GaloisField 2 1)).map χ = (f4Datum (GaloisField 2 1)).rootGroup γ)
    (hχσ : ∀ A, u₀ * χ A * u₀⁻¹ = σ (rho (phi' A))) :
    ∃ (t' : StatedLieTag) (n' : ℕ) (ψ' : (ggU t' n' 1).K →* G),
      StatedLieAdmissible t' n' 2 1 ∧ 2 ≤ (ggU t' n' 1).D.rank ∧
        ψ'.ker ≤ Subgroup.center (ggU t' n' 1).K ∧ ψ'.range = L ∧
        ∃ (γ : Fin (ggU .F4 0 1).D.rank → ℤ) (δ : Fin (ggU t' n' 1).D.rank → ℤ)
          (model : SelectedRoot.SelectedSL2Model (ggU .F4 0 1).D (GaloisField 2 1) γ)
          (model' : SelectedRoot.SelectedSL2Model (ggU t' n' 1).D (GaloisField 2 1) δ),
          ∃ u₀ : (ggU .F4 0 1).K,
            ((ψ.comp (MulAut.conj u₀).toMonoidHom).comp model.phi).range =
              (ψ'.comp model'.phi).range := by
  let ψ' : (ggU .PSp 3 1).K →* G := ψ.comp (σ.toMonoidHom.comp rho)
  have hψ' : Function.Injective ψ' := hψ.comp (σ.injective.comp hrho)
  let δ : Fin 3 → ℤ := Pi.single 0 1
  have hδ : δ ∈ roots (isFiniteType_cartanC 3) ∅ := Or.inl ⟨1, 0, by simp [δ]⟩
  obtain ⟨model, hmodel⟩ : ∃ model : SelectedRoot.SelectedSL2Model (ggU .F4 0 1).D
      (GaloisField 2 1) γ, model.phi = χ :=
    have hγD : γ ∈ (ggU .F4 0 1).D.roots := by exact mem_adjDatum_roots.2 hγ
    ⟨SelectedRoot.SelectedSL2Model.ofGF2Upper (ggU .F4 0 1).D γ hγD χ hχ hχU,
      SelectedRoot.SelectedSL2Model.ofGF2Upper_phi (ggU .F4 0 1).D γ hγD χ hχ hχU⟩
  obtain ⟨model', hmodel'⟩ : ∃ model' : SelectedRoot.SelectedSL2Model (ggU .PSp 3 1).D
      (GaloisField 2 1) δ, model'.phi = phi' :=
    ⟨SelectedRoot.SelectedSL2Model.ofGF2Upper (ggU .PSp 3 1).D δ hδ phi' hphi' hU',
      SelectedRoot.SelectedSL2Model.ofGF2Upper_phi (ggU .PSp 3 1).D δ hδ phi' hphi' hU'⟩
  refine ⟨.PSp, 3, ψ', ⟨Nat.prime_two, le_rfl, by norm_num, by decide⟩, by show 2 ≤ 3; norm_num,
    ?_, ?_, γ, δ, model, model', u₀, ?_⟩
  · rw [(MonoidHom.ker_eq_bot_iff ψ').2 hψ']
    exact bot_le
  · have h1 : ψ'.range = ((σ.toMonoidHom.comp rho).range).map ψ := MonoidHom.range_comp _ _
    rw [h1, MonoidHom.range_comp, hL]
  · rw [hmodel, hmodel']
    have h : (ψ.comp (MulAut.conj u₀).toMonoidHom).comp χ = ψ'.comp phi' := by
      ext A
      change ψ (u₀ * χ A * u₀⁻¹) = ψ (σ (rho (phi' A)))
      rw [hχσ]
    exact congrArg MonoidHom.range h

theorem selected_of_isComponentOf {G : Type} [Group G]
    [Finite G] {ψ : (ggU .F4 0 1).K →* G} (hψ : Function.Injective ψ)
    {g : ↥(adjointGroup .F4 (GaloisField 2 1))} (hg : orderOf g = 3)
    {M : Subgroup ↥(adjointGroup .F4 (GaloisField 2 1))}
    (hM : CFSG.Assembly.IsComponentOf M (Subgroup.centralizer {g})) {L : Subgroup G}
    (hML : M.map ψ = L) :
    ∃ (t' : StatedLieTag) (n' : ℕ) (ψ' : (ggU t' n' 1).K →* G),
      StatedLieAdmissible t' n' 2 1 ∧ 2 ≤ (ggU t' n' 1).D.rank ∧
        ψ'.ker ≤ Subgroup.center (ggU t' n' 1).K ∧ ψ'.range = L ∧
        ∃ (γ : Fin (ggU .F4 0 1).D.rank → ℤ) (δ : Fin (ggU t' n' 1).D.rank → ℤ)
          (model : SelectedRoot.SelectedSL2Model (ggU .F4 0 1).D (GaloisField 2 1) γ)
          (model' : SelectedRoot.SelectedSL2Model (ggU t' n' 1).D (GaloisField 2 1) δ),
          ∃ u₀ : (ggU .F4 0 1).K,
            ((ψ.comp (MulAut.conj u₀).toMonoidHom).comp model.phi).range =
              (ψ'.comp model'.phi).range := by
  have hK : Nat.card (GaloisField 2 1) = 2 := by
    rw [GaloisField.card 2 1 (by norm_num)]
    norm_num
  obtain ⟨rho, hrho, hrange, phi', hphi', hU', hU⟩ := exists_c3Levi_rootLift (GaloisField 2 1)
  have hβ₀ : IsRoot .F4 (c3ToF4 (Pi.single (0 : Fin 3) 1)) :=
    isRoot_c3ToF4 (Or.inl ⟨1, 0, by simp⟩)
  rcases order_three_cases_of_card_two hK hg with ⟨c, hc⟩ | ⟨c, hc⟩ | ⟨c, hc⟩
  · have hM' := isComponentOf_map_centralizer (MulAut.conj c) hM
    rw [MulAut.conj_apply, hc] at hM'
    have hMeq := eq_c3Levi_of_isComponentOf (GaloisField 2 1) hK hM'
    have hback : (C3Levi (GaloisField 2 1)).map (MulAut.conj c⁻¹).toMonoidHom = M := by
      have hid : (MulAut.conj c⁻¹).toMonoidHom.comp (MulAut.conj c).toMonoidHom =
          MonoidHom.id _ := by
        ext y
        simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv,
          MonoidHom.id_apply]
        group
      rw [← hMeq, Subgroup.map_map, hid, Subgroup.map_id]
    refine selected_of_rootLift hψ hrho hphi' hU' (MulAut.conj c⁻¹) ?_ hβ₀ c⁻¹ (rho.comp phi')
      (hrho.comp hphi') hU (fun A => by rw [MulAut.conj_apply]; rfl)
    rw [hrange, hback, hML]
  · haveI : CharP (GaloisField 2 1) CFSG.LieType.Ree.ReeTag.F4.prime :=
      inferInstanceAs (CharP (GaloisField 2 1) 2)
    obtain ⟨φ', hφ'⟩ : ∃ φ' : MulAut ↥(adjointGroup .F4 (GaloisField 2 1)),
        ∀ x, φ' x = CFSG.LieType.Ree.ReeTag.F4.finiteExceptionalAut (GaloisField 2 1) x :=
      ⟨CFSG.LieType.Ree.ReeTag.F4.finiteExceptionalAut (GaloisField 2 1), fun _ => rfl⟩
    obtain ⟨d, hd⟩ : ∃ d : ↥(adjointGroup .F4 (GaloisField 2 1)),
        d * φ' (nodeElt (GaloisField 2 1)) * d⁻¹ =
          TableBF4Two.rho (GaloisField 2 1) 0 (uSL 1 * vSL 1) *
            TableBF4Two.rho (GaloisField 2 1) 1 (uSL 1 * vSL 1) := by
      obtain ⟨d, hd⟩ := phi_link_of_card_two (K := GaloisField 2 1) hK
      exact ⟨d, by rw [hφ']; exact hd⟩
    set a := d⁻¹ * c with ha_def
    have ha : a * g * a⁻¹ = φ' (nodeElt (GaloisField 2 1)) := by
      calc a * g * a⁻¹ = d⁻¹ * (c * g * c⁻¹) * d := by rw [ha_def]; group
        _ = d⁻¹ * (d * φ' (nodeElt (GaloisField 2 1)) * d⁻¹) * d := by rw [hc, hd]
        _ = φ' (nodeElt (GaloisField 2 1)) := by group
    let Θ : MulAut ↥(adjointGroup .F4 (GaloisField 2 1)) := (MulAut.conj a).trans φ'.symm
    have hΘg : Θ g = nodeElt (GaloisField 2 1) := by
      change φ'.symm (MulAut.conj a g) = _
      rw [MulAut.conj_apply, ha, MulEquiv.symm_apply_apply]
    have hM' := isComponentOf_map_centralizer Θ hM
    rw [hΘg] at hM'
    have hMeq := eq_c3Levi_of_isComponentOf (GaloisField 2 1) hK hM'
    have hΘs : ∀ v, Θ.symm v = a⁻¹ * φ' v * a := fun v => by
      rw [MulEquiv.symm_apply_eq]
      change v = φ'.symm (MulAut.conj a (a⁻¹ * φ' v * a))
      rw [MulAut.conj_apply, show a * (a⁻¹ * φ' v * a) * a⁻¹ = φ' v by group,
        MulEquiv.symm_apply_apply]
    have hback : (C3Levi (GaloisField 2 1)).map Θ.symm.toMonoidHom = M := by
      have hid : Θ.symm.toMonoidHom.comp Θ.toMonoidHom = MonoidHom.id _ := by
        ext y
        simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply,
          MonoidHom.id_apply]
      rw [← hMeq, Subgroup.map_map, hid, Subgroup.map_id]
    have hc3 : c3ToF4 (Pi.single (0 : Fin 3) 1) = Pi.single (3 : Fin (Tag.rank .F4)) 1 := by
      funext j
      fin_cases j <;> rfl
    refine selected_of_rootLift hψ hrho hphi' hU' Θ.symm ?_ (isRoot_single .F4 0) a⁻¹
      (φ'.toMonoidHom.comp (rho.comp phi')) (φ'.injective.comp (hrho.comp hphi')) ?_ ?_
    · rw [hrange, hback, hML]
    · rw [← Subgroup.map_map, hU, hc3]
      exact map_rootGroup_three_of_exceptionalAut hK φ' hφ'
    · intro A
      rw [hΘs, inv_inv]
      rfl
  · exfalso
    have hM' := isComponentOf_map_centralizer (MulAut.conj c) hM
    rw [MulAut.conj_apply, hc] at hM'
    exact not_isComponentOf_centralizer_zFrame hK hM'


end Cases

section Main

open CFSG.LieType.Chevalley


theorem ggSecFiveQTwoFieldTwoSelectedAt_F4 :
    GGSecFiveQTwoFieldTwoSelectedAt .F4 := by
  have hsel : ∃ γ, Nonempty (SelectedRoot.SelectedSL2Model (ggU .F4 0 1).D (GaloisField 2 1) γ) := by
    obtain ⟨rho, hrho, -, phi', hphi', -, hU⟩ := exists_c3Levi_rootLift (GaloisField 2 1)
    have hβ₀ : IsRoot .F4 (c3ToF4 (Pi.single (0 : Fin 3) 1)) :=
      isRoot_c3ToF4 (Or.inl ⟨1, 0, by simp⟩)
    have hγD : c3ToF4 (Pi.single (0 : Fin 3) 1) ∈ (ggU .F4 0 1).D.roots := by
      exact mem_adjDatum_roots.2 hβ₀
    exact ⟨_, ⟨SelectedRoot.SelectedSL2Model.ofGF2Upper (ggU .F4 0 1).D _ hγD (rho.comp phi')
      (hrho.comp hphi') hU⟩⟩
  refine FieldTwoExc.ggSecFiveQTwoFieldTwoSelectedAt_exc_of_noncentral (Or.inl rfl) hsel ?_
  intro G _ _ B Bs x L D J hC hq n f ψ hpres hdiag hnc
  obtain ⟨hf, -, M, -, -, -, -, -, -, hM, hML, -⟩ :=
    FieldTwoExc.GGConfig.exists_marked_source_component_of_exc_qTwo (Or.inl rfl) hC hq ψ hpres
      hdiag
  subst hf
  obtain rfl : n = 0 := hpres.1.1.2.2
  obtain ⟨g, hg⟩ := exists_inner_rep hpres hdiag
  have hcen : Subgroup.center (ggU .F4 0 1).K = ⊥ :=
    CFSG.LieType.Chevalley.center_adjointGroup_eq_bot (τ := .F4) (K := GaloisField 2 1)
  have hψ : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff, ← hcen]
    exact hpres.2.1.2
  have hcomm : ∀ u, ψ u * x = x * ψ u ↔ u * g = g * u := fun u => by
    rw [eq_comm, ← mul_inv_eq_iff_eq_mul, hg, hψ.eq_iff, mul_inv_eq_iff_eq_mul, eq_comm]
  have hcomap : (Subgroup.centralizer ({x} : Set G)).comap ψ = Subgroup.centralizer {g} := by
    ext u
    rw [Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff,
      Subgroup.mem_centralizer_singleton_iff, hcomm]
  rw [hcomap] at hM
  have hx3 : x ^ 3 = 1 := by
    have hsstar := hC.1.2.2.2.2.2.2.1
    exact hsstar.1.1.2 x hsstar.2.1
  have hpow : ∀ (k : ℕ) (u : (ggU .F4 0 1).K),
      ψ (g ^ k * u * (g ^ k)⁻¹) = x ^ k * ψ u * (x ^ k)⁻¹ := by
    intro k u
    induction k with
    | zero => simp
    | succ k ih =>
      calc ψ (g ^ (k + 1) * u * (g ^ (k + 1))⁻¹) = ψ (g * (g ^ k * u * (g ^ k)⁻¹) * g⁻¹) := by
            rw [pow_succ']
            group
        _ = x * (x ^ k * ψ u * (x ^ k)⁻¹) * x⁻¹ := by rw [← hg, ih]
        _ = x ^ (k + 1) * ψ u * (x ^ (k + 1))⁻¹ := by
            rw [pow_succ']
            group
  have hg3 : g ^ 3 = 1 := by
    have hz : g ^ 3 ∈ Subgroup.center (ggU .F4 0 1).K := by
      rw [Subgroup.mem_center_iff]
      intro u
      have h := hψ ((hpow 3 u).trans (by rw [hx3, one_mul, inv_one, mul_one]))
      exact (mul_inv_eq_iff_eq_mul.1 h).symm
    rw [hcen, Subgroup.mem_bot] at hz
    exact hz
  have hg1 : g ≠ 1 := by
    rintro rfl
    apply hnc
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [← hpres.2.1.1] at hh
    obtain ⟨u, rfl⟩ := hh
    have h1 := hg u
    rw [one_mul, inv_one, mul_one] at h1
    exact (mul_inv_eq_iff_eq_mul.1 h1).symm
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact selected_of_isComponentOf hψ (orderOf_eq_prime hg3 hg1) hM hML

end Main

end CFSG.StandardType.FieldTwoF4

end
