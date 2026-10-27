module

public import CFSG.LocalAnalysis.StandardType.GGKD2Leaf6D3Contracts
public import CFSG.LocalAnalysis.StandardType.GGKD2LinearBlock1615
public import CFSG.LocalAnalysis.StandardType.GGNbrLSideSpTypeGL
public import CFSG.RankThree.GF2n.Stroth80.ClassicalQuasisimple
public import CFSG.LocalAnalysis.ComponentInitial.OddOrthogonalFourGroupCommutant
public import CFSG.LieType.SemisimpleCentralizers.HeldSLFacts
public import CFSG.LieType.SemisimpleCentralizers.OrderThree.CenterQuot
public import CFSG.Assembly.GL83StatedBridge
public import CFSG.RankThree.GF2n.Stroth80.FrobClause
public import CFSG.RankThree.GF2n.Stroth80.GlobalModel
public import CFSG.RankThree.GF2n.Stroth80.Sec310Stmt
public import CFSG.RankThree.GF2n.Stroth80.Sec39Rt
public import CFSG.RankThree.GF2n.Stroth80.Sec4Stmt
public import CFSG.RankThree.GF2n.Stroth80.Sec5Stmt
public import CFSG.RankThree.GF2n.SupIndepDecomp
public import CFSG.RankThree.GF2n.Tim79CentC
public import CFSG.RankThree.GF2n.Tim79CentL
public import CFSG.RankThree.GF2n.Tim79Mod

public section

namespace S2MathAs3_1624

noncomputable section

open CFSG CFSG.Assembly CFSG.StandardType
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ClassicalGroups.UnitaryFlag
open CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCPrimary
  CFSG.RankThree.PartOne.KCUnitary CFSG.RankThree.PartOne.KCUnitaryModel
open CFSG.LieType.SemisimpleCentralizers.Held
open CFSG.LocalAnalysis.GLTheoremA.Y10GInnLin
open scoped MatrixGroups commutatorElement

open CFSG.Open in
private theorem ltrd3j5_main (h1 : CubicFieldBlockContract)
    (h2 : LinearFullCentralizerContract)
    {K : Type} [Field K] [Finite K] [CharP K 2]
    (d : ℕ) (hd : 2 ≤ d) (S : GL (Fin d) K) (κ : Kˣ)
    (hκ : ∀ c : Kˣ, c ^ 3 ≠ κ)
    (hS3 : S ^ 3 = Matrix.GeneralLinearGroup.scalar (Fin d) κ)
    (H : Subgroup (GL (Fin d) K)) (hH : H = StatedSL d K)
    (hSnorm : S ∈ Subgroup.normalizer (H : Set (GL (Fin d) K)))
    (J : Subgroup (LargeEvenProj H))
    (hJ : CFSG.Assembly.IsComponentOf J (ggFixSub (TableB.projConj H ⟨S, hSnorm⟩))) :
    ∃ (m : ℕ) (E : Type) (_ : Field E) (_ : Algebra K E) (_ : Finite E),
      2 ≤ m ∧ d = 3 * m ∧ IsCubicExtension K E ∧
      Nonempty (↥J ⧸ Subgroup.center ↥J ≃*
        ↥(LargeEvenSLGroup (Fin m) E) ⧸
          Subgroup.center ↥(LargeEvenSLGroup (Fin m) E)) := by
  subst hH
  obtain ⟨m, E, hEf, hEalg, hEfin, hm1, hd3m, hcubic, hirr, α, hα3, hadj, b, hb⟩ :=
    h1 K d hd S κ hκ hS3
  obtain ⟨Φ2, hΦ2⟩ :=
    h2 K d hd S κ hκ hS3 m E hEf hEalg hEfin hd3m hcubic α hα3 b hb
  letI : Field E := hEf
  letI : Algebra K E := hEalg
  letI : Finite E := hEfin
  have hαβ : ∀ k : ↥(StatedSL d K),
      LargeEvenProjMk (StatedSL d K) (conjSL S k) =
        TableB.projConj (StatedSL d K) ⟨S, hSnorm⟩ (LargeEvenProjMk (StatedSL d K) k) := by
    intro k
    rfl
  obtain ⟨Mtilde, hMtilde, hMJ⟩ :=
    CFSG.StandardType.TCJ.tcjLin_component_lift (LargeEvenProjMk (StatedSL d K))
      QuotientGroup.mk_surjective ker_projMk_le_center (conjSL S)
      (TableB.projConj (StatedSL d K) ⟨S, hSnorm⟩) hαβ hJ
  let W : Subgroup (GL (Fin d) K) := Mtilde.map (StatedSL d K).subtype
  have hW : CFSG.Assembly.IsComponentOf W
      (Subgroup.centralizer ({S} : Set (GL (Fin d) K)) ⊓ StatedSL d K) := by
    rw [← map_fixSubgroup_conjSL S]
    exact ⟨Subgroup.map_mono hMtilde.1, hMtilde.2.1.map (StatedSL d K).subtype,
      CFSG.Assembly.IsQuasisimple.of_mulEquiv
        (Subgroup.equivMapOfInjective Mtilde (StatedSL d K).subtype Subtype.val_injective).symm
        hMtilde.2.2⟩
  by_cases hm1eq : m = 1
  · exfalso
    subst hm1eq
    let C : Subgroup (GL (Fin d) K) := Subgroup.centralizer ({S} : Set (GL (Fin d) K))
    have hCcomm : ∀ a b : ↥C, a * b = b * a := by
      intro a b
      apply Φ2.injective
      rw [map_mul, map_mul]
      exact CFSG.LieType.SemisimpleCentralizers.OrderThree.mul_comm_GL_fin_of_le_one
        (by omega) _ _
    have hWleC : W ≤ C := fun x hx => (hW.1 hx).1
    have hWcomm : ∀ a b : ↥W, a * b = b * a := by
      intro a b
      apply Subtype.ext
      simp only [Subgroup.coe_mul]
      exact congrArg (fun z : ↥C => (z : GL (Fin d) K))
        (hCcomm ⟨a, hWleC a.2⟩ ⟨b, hWleC b.2⟩)
    exact not_isQuasisimple_of_comm hWcomm
      ((CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_open ↥W).1 hW.2.2)
  have hm2 : 2 ≤ m := by omega
  let C : Subgroup (GL (Fin d) K) := Subgroup.centralizer ({S} : Set (GL (Fin d) K))
  let D : Subgroup (GL (Fin d) K) := ⁅C, C⁆
  have hDleC : D ≤ C := Subgroup.commutator_le_self C
  have hDleSL : D ≤ StatedSL d K := by
    refine Subgroup.commutator_le.2 fun a ha b hb => commutatorElement_mem_statedSL a b
  have hDleCinf : D ≤ C ⊓ StatedSL d K := le_inf hDleC hDleSL
  have hcond : 3 ≤ m ∨ ∃ s : Finset E, s.card = 4 := by
    rcases le_or_gt 3 m with h3 | h3
    · exact Or.inl h3
    · right
      have hcard : 4 ≤ Nat.card E := by
        have hEcard : Nat.card E = Nat.card K ^ 3 := hcubic.2.2
        have hKcard : 2 ≤ Nat.card K := Finite.one_lt_card
        rw [hEcard]
        calc 4 ≤ 2 ^ 3 := by norm_num
          _ ≤ Nat.card K ^ 3 := by gcongr
      haveI : Fintype E := Fintype.ofFinite E
      obtain ⟨s, _, hs⟩ := Finset.exists_subset_card_eq (s := Finset.univ) (n := 4)
        (by simpa [Nat.card_eq_fintype_card] using hcard)
      exact ⟨s, hs⟩
  have hDsub : D.subgroupOf C = commutator ↥C := by
    have hmap : (commutator ↥C).map C.subtype = D := by
      rw [_root_.commutator_def, Subgroup.map_commutator]
      simp only [Subgroup.map_top, Subgroup.range_subtype]
      rfl
    rw [← hmap]
    exact Subgroup.comap_map_eq_self_of_injective C.subtype_injective _
  have hDmap : (D.subgroupOf C).map Φ2.toMonoidHom = StatedSL m E := by
    rw [hDsub, _root_.commutator_def, Subgroup.map_commutator,
      Subgroup.map_top_of_surjective Φ2.toMonoidHom Φ2.surjective, ← _root_.commutator_def]
    exact GGNbrLSideKit.commutator_generalLinear_eq_statedSL hm2 hcond
  have h4E : 4 ≤ Nat.card E := by
    have hEcard : Nat.card E = Nat.card K ^ 3 := hcubic.2.2
    have hKcard : 2 ≤ Nat.card K := Finite.one_lt_card
    rw [hEcard]
    calc 4 ≤ 2 ^ 3 := by norm_num
      _ ≤ Nat.card K ^ 3 := by gcongr
  let eD : ↥D ≃* ↥(StatedSL m E) :=
    (Subgroup.subgroupOfEquivOfLe hDleC).symm.trans
      ((Subgroup.equivMapOfInjective (D.subgroupOf C) Φ2.toMonoidHom Φ2.injective).trans
        (MulEquiv.subgroupCongr hDmap))
  have hDq : CFSG.Assembly.IsQuasisimple ↥D :=
    CFSG.Assembly.IsQuasisimple.of_mulEquiv eD
      ((CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native
        ↥(StatedSL m E)).2
        (CFSG.RankThree.GF2n.Stroth80.statedSL_quasisimple_of_card m E hm2 h4E))
  have hDperf : ⁅D, D⁆ = D := (Subgroup.isPerfect_iff (H := D)).mp ⟨hDq.1⟩
  let CSL : Subgroup (GL (Fin d) K) := C ⊓ StatedSL d K
  have hCSLleC : CSL ≤ C := inf_le_left
  have hDleCSL : D ≤ CSL := hDleCinf
  have hCommEq : ⁅CSL, CSL⁆ = D := by
    apply le_antisymm
    · exact Subgroup.commutator_mono hCSLleC hCSLleC
    · rw [← hDperf]
      exact Subgroup.commutator_mono hDleCSL hDleCSL
  have hmapCSL : (commutator ↥CSL).map CSL.subtype = D := by
    rw [_root_.commutator_def, Subgroup.map_commutator]
    simp only [Subgroup.map_top, Subgroup.range_subtype]
    exact hCommEq
  have hCommq : CFSG.IsQuasisimple (commutator ↥CSL) := by
    have eComm : ↥(commutator ↥CSL) ≃* ↥D :=
      (Subgroup.equivMapOfInjective (commutator ↥CSL) CSL.subtype CSL.subtype_injective).trans
        (MulEquiv.subgroupCongr hmapCSL)
    exact CFSG.IsQuasisimple.of_mulEquiv eComm
      ((CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native ↥D).1 hDq)
  have hWsub : CFSG.IsComponent (W.subgroupOf CSL) := by
    refine ⟨?_, ?_⟩
    · exact (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native
        ↥(W.subgroupOf CSL)).1
        (CFSG.Assembly.IsQuasisimple.of_mulEquiv
          (Subgroup.subgroupOfEquivOfLe hW.1) hW.2.2)
    · exact CFSG.Assembly.IsSubnormal.subgroupOf hW.2.1
  have hDsubCSL : D.subgroupOf CSL = commutator ↥CSL := by
    rw [← hmapCSL]
    exact Subgroup.comap_map_eq_self_of_injective CSL.subtype_injective _
  have hWD : W = D := by
    have h := CFSG.LocalAnalysis.ComponentInitial.eq_commutator_of_isComponent hWsub hCommq
    have hWDsub : W.subgroupOf CSL = D.subgroupOf CSL := h.trans hDsubCSL.symm
    rw [← Subgroup.map_subgroupOf_eq_of_le hW.1, ← Subgroup.map_subgroupOf_eq_of_le hDleCSL,
      hWDsub]
  have hWle : W ≤ StatedSL d K := fun x hx => (hW.1 hx).2
  have hMtilde_eq : Mtilde = W.comap (StatedSL d K).subtype :=
    (Subgroup.comap_map_eq_self_of_injective (StatedSL d K).subtype_injective Mtilde).symm
  have hJeq : J = (W.comap (StatedSL d K).subtype).map (LargeEvenProjMk (StatedSL d K)) := by
    rw [← hMJ, hMtilde_eq]
  have hperf : commutator ↥W = ⊤ := hW.2.2.1
  have hmemJ : ∀ x : ↥Mtilde, LargeEvenProjMk (StatedSL d K) (x : ↥(StatedSL d K)) ∈ J :=
    fun x => by
      rw [← hMJ]
      exact Subgroup.mem_map_of_mem _ x.2
  let fJ : ↥Mtilde →* ↥J :=
    MonoidHom.codRestrict ((LargeEvenProjMk (StatedSL d K)).comp Mtilde.subtype) J hmemJ
  have hfJ : Function.Surjective fJ := by
    rintro ⟨y, hy⟩
    rw [← hMJ] at hy
    obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hy
    exact ⟨⟨z, hz⟩, rfl⟩
  have hkerJ : fJ.ker ≤ Subgroup.center ↥Mtilde := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    have hπ : LargeEvenProjMk (StatedSL d K) (x : ↥(StatedSL d K)) = 1 := congrArg Subtype.val hx
    have hxc : (x : ↥(StatedSL d K)) ∈ Subgroup.center ↥(StatedSL d K) :=
      ker_projMk_le_center (MonoidHom.mem_ker.mpr hπ)
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    exact Subgroup.mem_center_iff.mp hxc _
  let e' : ↥Mtilde ≃* ↥W :=
    Subgroup.equivMapOfInjective Mtilde (StatedSL d K).subtype Subtype.val_injective
  let f' : ↥W →* ↥J := fJ.comp e'.symm.toMonoidHom
  have hsurj' : Function.Surjective f' := hfJ.comp e'.symm.surjective
  have hker' : f'.ker ≤ Subgroup.center ↥W := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    have hw : (e'.symm x : ↥Mtilde) ∈ fJ.ker := by
      rw [MonoidHom.mem_ker]
      exact hx
    have hwc := hkerJ hw
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨z, rfl⟩ := e'.surjective y
    have hx' : x = e' (e'.symm x) := (e'.apply_symm_apply x).symm
    rw [hx', ← map_mul, ← map_mul]
    congr 1
    exact Subgroup.mem_center_iff.mp hwc z
  obtain ⟨ψ⟩ := center_quot_equiv_of_surjective hperf f' hsurj' hker'
  have eW : ↥W ≃* ↥(StatedSL m E) := by
    rw [hWD]
    exact eD
  let φ : ↥W ⧸ Subgroup.center ↥W ≃*
      ↥(StatedSL m E) ⧸ Subgroup.center ↥(StatedSL m E) :=
    QuotientGroup.congr (Subgroup.center ↥W) (Subgroup.center ↥(StatedSL m E)) eW
      (Subgroup.map_center_eq eW)
  refine ⟨m, E, hEf, hEalg, hEfin, hm2, hd3m, hcubic, ?_⟩
  rw [largeEvenSLGroup_eq_statedSL m]
  exact ⟨ψ.trans φ⟩

theorem linearComponent_of_blocks (h1 : CubicFieldBlockContract)
    (h2 : LinearFullCentralizerContract) : LinearComponentContract := by
  intro K hField hFinite hCharP d hd S κ hκ hS3 hSnorm J hJ
  exact ltrd3j5_main (K := K) h1 h2 d hd S κ hκ hS3 (LargeEvenSLGroup (Fin d) K)
    (largeEvenSLGroup_eq_statedSL d) hSnorm J hJ

end

end S2MathAs3_1624

end
