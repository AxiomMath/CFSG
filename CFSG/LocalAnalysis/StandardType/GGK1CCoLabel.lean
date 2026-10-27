module

public import CFSG.LocalAnalysis.StandardType.GGK1CCoDefs
public import CFSG.LocalAnalysis.StandardType.GGK1CCoArith
public import CFSG.LocalAnalysis.StandardType.GGK1CCoPos
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenSymplecticNormalForm
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GSympLabel
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnUniLabelPSU
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnUniData
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnUniScal
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnUniLabelTwo
public import CFSG.LocalAnalysis.StandardType.GGTypeANbrKappaCard
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GCenterQuot
public import CFSG.Assembly.GL83StatedBridge
public import CFSG.RankThree.PartOne.KC.SymplecticInnerPlaneAlt6
public import CFSG.LocalAnalysis.StandardType.GGTPNI1BC
public import CFSG.LocalAnalysis.StandardType.MarkingSmall
public import CFSG.ClassicalInvolution.Models.SymplecticPairs.RootSp2
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.SympInnerExport
public import CFSG.LieType.SemisimpleCentralizers.HeldSLFacts
public import CFSG.Assembly.OpenBridges
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnUniPComp
public import CFSG.RankThree.PartTwo.Sec12.Notation
public import CFSG.RankThree.PartTwo.Sec4.Item47Diag
public import CFSG.RankThree.PartTwo.Sec4.Item47Statement
public import CFSG.RankThree.PartTwo.Sec4.Item47Witness
public import CFSG.RankThree.PartTwo.Sec4.LThreePiItem411
public import CFSG.RankThree.PartTwo.Sec4.ProjSLEquiv

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Open Polynomial
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)
open CFSG.RankThree.Classical (spEnd IsReciprocalTransversal)
open CFSG.RankThree.PartOne.KCPrimary
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
  (spScalars ker_proj proj_surjective spScalars_le_center)

private theorem ggK1CLb_neZero_r {r : ℕ} {K : Type} [Field K] {H : Subgroup (StatedSp r K)}
    (hq : CFSG.IsQuasisimple ↥H) : NeZero r := by
  rcases Nat.eq_zero_or_pos r with hr | hr
  · exfalso
    subst hr
    haveI : Subsingleton (StatedSp 0 K) := inferInstance
    haveI : Subsingleton ↥H := inferInstance
    haveI : Nontrivial ↥H := CFSG.LocalCores.isQuasisimple_nontrivial hq
    obtain ⟨a, b, hab⟩ := (inferInstance : Nontrivial ↥H).exists_pair_ne
    exact hab (Subsingleton.elim a b)
  · exact ⟨hr.ne'⟩

private theorem ggK1CLb_proj_injective {r : ℕ} {K : Type} [Field K] [NeZero r] [CharP K 2] :
    Function.Injective (proj r K) :=
  (CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.proj_bijective_of_charTwo
    (r := r) (K := K)).1

private def ggK1CLb_quot_center_equiv {G H : Type} [Group G] [Group H] (e : G ≃* H) :
    G ⧸ Subgroup.center G ≃* H ⧸ Subgroup.center H :=
  QuotientGroup.congr (Subgroup.center G) (Subgroup.center H) e (Subgroup.map_center_eq e)

private noncomputable def ggK1CLb_map_quot_center_equiv {G G' : Type} [Group G] [Group G']
    (f : G →* G') (hf : Function.Injective f) (H : Subgroup G) :
    ↥H ⧸ Subgroup.center ↥H ≃* ↥(H.map f) ⧸ Subgroup.center ↥(H.map f) :=
  ggK1CLb_quot_center_equiv (Subgroup.equivMapOfInjective H f hf)

private theorem ggK1CLb_sp_label {nf r s : ℕ} {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2 ^ nf) (H : Subgroup (StatedSp r K))
    (hq : CFSG.IsQuasisimple ↥H) (hm : Nonempty (↥H ≃* StatedSp s K)) :
    GGHasLabel (⟨.C, s, nf⟩ : LargeEvenLabel)
      (H.map (proj r K) ⧸ Subgroup.center (H.map (proj r K))) := by
  haveI : Fintype K := Fintype.ofFinite K
  haveI : CharP K 2 := charP_of_card_eq_prime_pow (R := K) (p := 2) (f := nf)
    (by rw [← Nat.card_eq_fintype_card]; exact hK)
  haveI : NeZero r := ggK1CLb_neZero_r hq
  obtain ⟨eModel⟩ := hm
  have eQuotH := ggK1CLb_map_quot_center_equiv (proj r K) (ggK1CLb_proj_injective) H
  have eQuotModel := ggK1CLb_quot_center_equiv eModel
  have eCenter : StatedSp s K ⧸ Subgroup.center (StatedSp s K) ≃* StatedProj (StatedSp s K) :=
    QuotientGroup.quotientMulEquivOfEq
      (CFSG.LieType.Universal.Symplectic.center_eq s K)
  have e : ↥(H.map (proj r K)) ⧸ Subgroup.center ↥(H.map (proj r K)) ≃*
      StatedProj (StatedSp s K) :=
    MulEquiv.trans eQuotH.symm (MulEquiv.trans eQuotModel eCenter)
  exact (tpbc_hasLabel_B_iff_C s nf _).mp
    (CFSG.LocalAnalysis.GLTheoremA.Y10GSympLabel.ggHasLabel_typeB hK e)

private theorem ggK1CLb_qs_hasOrbit (nf : ℕ) (k : ggK1CCo_Kind) :
    (ggK1CCo_kindOrbit nf k).qs = true → ggK1CCo_Kind.hasOrbit k = true := by
  intro h
  cases k with
  | sp s => rfl
  | sl m =>
      cases m with
      | zero => rfl
      | succ m =>
          cases m with
          | zero => simp [ggK1CCo_kindOrbit, ggK1CCo_Kind.hasOrbit] at h
          | succ m => rfl
  | su m =>
      cases m with
      | zero => rfl
      | succ m =>
          cases m with
          | zero => simp [ggK1CCo_kindOrbit, ggK1CCo_Kind.hasOrbit] at h
          | succ m => rfl

theorem ggK1CCo_kind_label {nf r : ℕ} {K : Type} [Field K] [Finite K]
    (kind : ggK1CCo_Kind) (H : Subgroup (StatedSp r K))
    (hq : CFSG.IsQuasisimple ↥H) (hm : ggK1CCo_Kind.Model nf kind H)
    (hK : Nat.card K = 2 ^ nf) :
    GGHasLabel (ggK1CCo_kindOrbit nf kind).lab
      (H.map (proj r K) ⧸ Subgroup.center (H.map (proj r K))) := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  haveI : CharP K 2 := charP_of_card_eq_prime_pow (R := K) (p := 2) (f := nf)
    (by rw [← Nat.card_eq_fintype_card]; exact hK)
  haveI : NeZero r := ggK1CLb_neZero_r hq
  cases kind with
  | sp s =>
    by_cases hs1 : s = 1
    ·
      subst hs1
      have hm1 : Nonempty (↥H ≃* StatedSp 1 K) := by
        simpa [ggK1CCo_Kind.Model] using hm
      have hlab : (ggK1CCo_kindOrbit nf (ggK1CCo_Kind.sp 1)).lab = ⟨.A, 1, nf⟩ := by
        simp [ggK1CCo_kindOrbit]
      rw [hlab]
      obtain ⟨eH⟩ := hm1
      simp only [GGHasLabel, LargeEvenRawDatum, LargeEvenRecipeLinear]
      refine ⟨K, inferInstance, (inferInstance : Finite K), hK, ?_⟩
      have eSL : ↥H ≃* Matrix.SpecialLinearGroup (Fin 2) K :=
        eH.trans (CFSG.ClassicalInvolution.Models.SymplecticPairs.longBlockEquivOne K).symm
      obtain ⟨eQ⟩ := CFSG.LocalAnalysis.GLTheoremA.Y10GCenterQuot.nonempty_centerQuot_sl 2 eSL
      have eMap := ggK1CLb_map_quot_center_equiv (proj r K) ggK1CLb_proj_injective H
      have e : ↥(H.map (proj r K)) ⧸ Subgroup.center ↥(H.map (proj r K)) ≃*
          LargeEvenProj (LargeEvenSLGroup (Fin 2) K) := by
        rw [largeEvenSLGroup_eq_statedSL]
        exact eMap.symm.trans eQ
      exact ⟨e⟩
    · by_cases hcorner : s = 2 ∧ nf = 1
      ·
        obtain ⟨rfl, rfl⟩ := hcorner
        have hm2 : Nonempty (↥H ≃* ↥(commutator (StatedSp 2 K))) := by
          simpa [ggK1CCo_Kind.Model] using hm
        have hlab : (ggK1CCo_kindOrbit 1 (ggK1CCo_Kind.sp 2)).lab = ⟨.B2der, 0, 1⟩ := by
          simp [ggK1CCo_kindOrbit]
        rw [hlab]
        have hK2 : Nat.card K = 2 := by rw [hK, pow_one]
        obtain ⟨eH⟩ := hm2
        have hq_comm : CFSG.IsQuasisimple ↥(commutator (StatedSp 2 K)) :=
          CFSG.LocalCores.isQuasisimple_of_mulEquiv eH hq
        obtain ⟨eSp⟩ := nonempty_largeEvenSpGroup_equiv_sympFour hK2
        have eSp' : StatedSp 2 K ≃* CFSG.ComponentClassification.PresentationLocal.sympFour := by
          rw [← largeEvenSpGroup_eq_statedSp]; exact eSp
        obtain ⟨⟨eA6⟩, -⟩ :=
          CFSG.RankThree.PartOne.derived_alt_index_of_mulEquiv_sympFour eSp'
        haveI : IsSimpleGroup ↥(alternatingGroup (Fin 6)) :=
          alternatingGroup.isSimpleGroup (by simp)
        haveI : IsSimpleGroup ↥(commutator (StatedSp 2 K)) := eA6.isSimpleGroup
        haveI : Group.IsPerfect ↥(commutator (StatedSp 2 K)) := hq_comm.1
        have hcen : Subgroup.center ↥(commutator (StatedSp 2 K)) = ⊥ := by
          rcases (inferInstance :
            (Subgroup.center ↥(commutator (StatedSp 2 K))).Normal).eq_bot_or_eq_top with h | h
          · exact h
          · exact absurd (Subgroup.center_eq_top_iff.1 h)
              (Group.IsPerfect.not_isMulCommutative _)
        have eMap := ggK1CLb_map_quot_center_equiv (proj r K) ggK1CLb_proj_injective H
        have eQuot := ggK1CLb_quot_center_equiv eH
        have e : ↥(H.map (proj r K)) ⧸ Subgroup.center ↥(H.map (proj r K)) ≃*
            alternatingGroup (Fin 6) :=
          (eMap.symm.trans eQuot).trans
            ((QuotientGroup.quotientMulEquivOfEq hcen).trans
              (QuotientGroup.quotientBot.trans eA6))
        exact CFSG.LocalAnalysis.GLTheoremA.Y10GSympLabel.ggHasLabel_b2der e
      ·
        have hm' : Nonempty (↥H ≃* StatedSp s K) := by
          simpa only [ggK1CCo_Kind.Model, if_neg hs1, if_neg hcorner] using hm
        have hlab : (ggK1CCo_kindOrbit nf (ggK1CCo_Kind.sp s)).lab = ⟨.C, s, nf⟩ := by
          simp only [ggK1CCo_kindOrbit, if_neg hs1, if_neg hcorner]
        rw [hlab]
        exact ggK1CLb_sp_label hK H hq hm'
  | sl m =>
    obtain ⟨eH⟩ := hm
    rcases Nat.lt_or_ge m 2 with hm2 | hm2
    ·
      exfalso
      have hm01 : m = 0 ∨ m = 1 := by omega
      haveI : Subsingleton (Matrix.SpecialLinearGroup (Fin m) K) := by
        rcases hm01 with rfl | rfl
        · exact Matrix.SpecialLinearGroup.subsingleton_of_subsingleton
        · exact Matrix.SpecialLinearGroup.subsingleton_of_subsingleton
      haveI : Subsingleton ↥H :=
        ⟨fun x y => eH.injective (Subsingleton.elim (eH x) (eH y))⟩
      haveI : Subsingleton (↥H ⧸ Subgroup.center ↥H) := inferInstance
      obtain ⟨-, -, a, b, hab⟩ := hq
      exact hab (Subsingleton.elim _ _)
    · have hlabel : (ggK1CCo_kindOrbit nf (ggK1CCo_Kind.sl m)).lab =
          ⟨.A, m - 1, nf⟩ := by
        rcases m with _ | _ | k
        · omega
        · omega
        · simp [ggK1CCo_kindOrbit, ggMultBlockA]
      rw [hlabel]
      simp only [GGHasLabel, LargeEvenRawDatum, LargeEvenRecipeLinear]
      refine ⟨K, inferInstance, (inferInstance : Finite K), hK, ?_⟩
      have hm' : (m - 1) + 1 = m := by omega
      have eSL : ↥H ≃* Matrix.SpecialLinearGroup (Fin ((m - 1) + 1)) K := by
        rw [hm']; exact eH
      obtain ⟨eQ⟩ :=
        CFSG.LocalAnalysis.GLTheoremA.Y10GCenterQuot.nonempty_centerQuot_sl ((m - 1) + 1) eSL
      have eMap := ggK1CLb_map_quot_center_equiv (proj r K) ggK1CLb_proj_injective H
      have e : ↥(H.map (proj r K)) ⧸ Subgroup.center ↥(H.map (proj r K)) ≃*
          LargeEvenProj (LargeEvenSLGroup (Fin ((m - 1) + 1)) K) := by
        rw [largeEvenSLGroup_eq_statedSL]
        exact eMap.symm.trans eQ
      exact ⟨e⟩
  | su m =>
    obtain ⟨E, hF, hFin, hEcard, ⟨eH⟩⟩ := hm
    letI : Field E := hF
    letI : Fintype E := hFin
    have hEcard' : Nat.card E = (2 ^ nf) ^ 2 := by
      rw [Nat.card_eq_fintype_card, hEcard, hK]
    obtain ⟨τ, hτm, hτ⟩ :=
      CFSG.LocalAnalysis.GLTheoremA.Y10GInnUni.exists_frob_equiv (n := nf) hEcard'
    have hτK : ∀ x, τ x = x ^ Nat.card K := fun x => by rw [hτm x, hK]
    have hStatedSU : ∀ a : ℕ,
        CFSG.LieType.SemisimpleCentralizers.Held.heldSU a E τ hτ =
          StatedSU a (Nat.card K) E :=
      fun a => CFSG.LieType.SemisimpleCentralizers.Held.hct_heldSU_eq_statedSU
        (a := a) (Q := Nat.card K) hτK
    have hSLsub : ∀ m ≤ 1, Subsingleton ↥(StatedSL m E) := by
      intro m hm
      haveI : Subsingleton (Matrix.SpecialLinearGroup (Fin m) E) := by
        rcases (by omega : m = 0 ∨ m = 1) with rfl | rfl
        · exact Matrix.SpecialLinearGroup.subsingleton_of_subsingleton
        · exact Matrix.SpecialLinearGroup.subsingleton_of_subsingleton
      exact ⟨fun x y =>
        (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL m E).symm.injective
          (Subsingleton.elim _ _)⟩
    have hSUsub : ∀ m ≤ 1, Subsingleton ↥(StatedSU m (Nat.card K) E) := by
      intro m hm
      haveI := hSLsub m hm
      exact ⟨fun a b => Subgroup.inclusion_injective
        (CFSG.Open.StatedAPI.statedSU_le_statedSL m (Nat.card K) E)
        (Subsingleton.elim _ _)⟩
    rcases lt_or_ge m 3 with hm3 | hm3
    · interval_cases m
      · exfalso
        haveI : Subsingleton ↥(StatedSU 0 (Nat.card K) E) := hSUsub 0 (by omega)
        haveI : Subsingleton ↥H :=
          ⟨fun a b => eH.injective (Subsingleton.elim (eH a) (eH b))⟩
        haveI : Subsingleton (↥H ⧸ Subgroup.center ↥H) := inferInstance
        obtain ⟨-, -, a, b, hab⟩ := hq
        exact hab (Subsingleton.elim _ _)
      · exfalso
        haveI : Subsingleton ↥(StatedSU 1 (Nat.card K) E) := hSUsub 1 (by omega)
        haveI : Subsingleton ↥H :=
          ⟨fun a b => eH.injective (Subsingleton.elim (eH a) (eH b))⟩
        haveI : Subsingleton (↥H ⧸ Subgroup.center ↥H) := inferInstance
        obtain ⟨-, -, a, b, hab⟩ := hq
        exact hab (Subsingleton.elim _ _)
      · have hlab : (ggK1CCo_kindOrbit nf (ggK1CCo_Kind.su 2)).lab = ⟨.A, 1, nf⟩ := by
          simp [ggK1CCo_kindOrbit, ggMultBlockA]
        rw [hlab]
        obtain ⟨k, hkF, hkFin, hkcard, ⟨eQ⟩⟩ :=
          CFSG.LocalAnalysis.GLTheoremA.Y10GInnUni.exists_quot_heldSU_two_equiv_psl
            τ hτ hτm hEcard'
        rw [hStatedSU 2] at eQ
        have eMap := ggK1CLb_map_quot_center_equiv (proj r K) ggK1CLb_proj_injective H
        have eQuot := ggK1CLb_quot_center_equiv eH
        simp only [GGHasLabel, LargeEvenRawDatum, LargeEvenRecipeLinear]
        refine ⟨k, hkF, hkFin, hkcard, ?_⟩
        have e : ↥(H.map (proj r K)) ⧸ Subgroup.center ↥(H.map (proj r K)) ≃*
            LargeEvenProj (LargeEvenSLGroup (Fin 2) k) := by
          rw [largeEvenSLGroup_eq_statedSL]
          exact eMap.symm.trans (eQuot.trans eQ)
        exact ⟨e⟩
    · obtain ⟨m', rfl⟩ : ∃ m', m = m' + 3 := ⟨m - 3, by omega⟩
      by_cases hcorner : m' = 0 ∧ nf = 1
      · exfalso
        obtain ⟨hm0, hnf⟩ := hcorner
        subst hm0
        have hτ2 : ∀ x, τ x = x ^ 2 := by intro x; rw [hτm x, hnf]; norm_num
        have hE4 : Nat.card E = 4 := by rw [hEcard', hnf]; norm_num
        have hsolv := CFSG.LocalAnalysis.GLTheoremA.Y10GInnUni.isSolvable_quot_heldSU_three_two
          τ hτ hτ2 hE4
        rw [hStatedSU 3] at hsolv
        have eQuot := ggK1CLb_quot_center_equiv eH
        haveI : IsSimpleGroup (↥H ⧸ Subgroup.center ↥H) := hq.2.1
        haveI : Group.IsSolvable (↥H ⧸ Subgroup.center ↥H) :=
          Group.isSolvable_of_surjective (f := eQuot.symm.toMonoidHom) eQuot.symm.surjective
        exact (CFSG.LocalAnalysis.GLTheoremA.Y10GInnUni.not_isSolvable_quot_center (J := ↥H))
          inferInstance
      · have hlab : (ggK1CCo_kindOrbit nf (ggK1CCo_Kind.su (m' + 3))).lab =
            ⟨.twA, m' + 2, nf⟩ := by
          simp [ggK1CCo_kindOrbit, ggMultBlockA]
        rw [hlab]
        obtain ⟨eQ⟩ :=
          CFSG.LocalAnalysis.GLTheoremA.Y10GInnUni.nonempty_quot_heldSU_equiv_statedProj
            CFSG.LocalAnalysis.GLTheoremA.Y10GInnUni.uniScalar_holds
            (a := m' + 3) (m := nf) τ hτ hτm hEcard' (by omega)
            (by
              intro h
              obtain ⟨h1, h2⟩ := Prod.mk.inj h
              exact hcorner ⟨by omega,
                (Nat.pow_right_injective (by norm_num : 2 ≤ 2)) (by simpa using h2)⟩)
        rw [hStatedSU (m' + 3)] at eQ
        have eMap := ggK1CLb_map_quot_center_equiv (proj r K) ggK1CLb_proj_injective H
        have eQuot := ggK1CLb_quot_center_equiv eH
        have e : ↥(H.map (proj r K)) ⧸ Subgroup.center ↥(H.map (proj r K)) ≃*
            StatedProj (StatedSU (m' + 3) (2 ^ nf) E) := eMap.symm.trans (eQuot.trans eQ)
        have hm1 : (m' + 2) + 1 = m' + 3 := by omega
        have e' : ↥(H.map (proj r K)) ⧸ Subgroup.center ↥(H.map (proj r K)) ≃*
            StatedProj (StatedSU ((m' + 2) + 1) (2 ^ nf) E) := by
          rw [hm1]; exact e
        exact CFSG.LocalAnalysis.GLTheoremA.Y10GInnUni.ggHasLabel_twA
          (b := m' + 2) (m := nf) hEcard' e'

theorem ggK1CCo_family_of_blocks {p nf d r : ℕ} {K : Type} [Field K] [Finite K]
    {x : ↥(StatedSp r K)} {m : List ℕ} (B : ggK1CCo_Blocks p nf d r K x m)
    (hK : Nat.card K = 2 ^ nf) :
    Nonempty (ggK1CCo_Family p nf d r K x m) := by
  classical
  letI : Fintype B.ι := B.fintype
  let L := ggK1CCo_expectedKindList p nf d m
  let O := (ggMultDatumC p nf d m).orbits
  have hO : (L.filter (fun k => ggK1CCo_Kind.hasOrbit k)).map (ggK1CCo_kindOrbit nf) = O :=
    ggK1CCo_kindOrbit_multiset p nf d m
  obtain ⟨g, hg⟩ :=
    @ggK1CCo_pos_equiv nf B.ι B.fintype B.kind L O B.kind_multiset hO
  have hmult : (Finset.univ : Finset B.ι).val.map B.kind = ggK1CCo_expectedKinds p nf d m :=
    B.kind_multiset
  have hkindL : ∀ i, B.kind i ∈ L := by
    intro i
    have hkm := Multiset.mem_map_of_mem B.kind (Finset.mem_univ i)
    rw [hmult] at hkm
    exact Multiset.mem_coe.mp hkm
  have hLmem : ∀ k ∈ L, k ∈ (Finset.univ : Finset B.ι).val.map B.kind := by
    intro k hk
    rw [hmult]
    exact Multiset.mem_coe.mpr hk
  refine ⟨{
    ι := B.ι
    A := B.A
    blk := fun i => ggK1CCo_kindOrbit nf (B.kind i)
    hcomm := B.hcomm
    hjoin := B.hjoin
    hindep := B.hindep
    htame := B.htame
    hmem := ?hmem
    hqs := ?hqs
    hlab := ?hlab
    hreal := ?hreal
    hbij := ?hbij
    hsolv := ?hsolv
  }⟩
  · intro i hq
    have hqs : (ggK1CCo_kindOrbit nf (B.kind i)).qs = true := (B.hqsKind i).mp hq
    have hk : B.kind i ∈ L.filter (fun k => ggK1CCo_Kind.hasOrbit k) := by
      rw [List.mem_filter]
      exact ⟨hkindL i, ggK1CLb_qs_hasOrbit nf (B.kind i) hqs⟩
    have hmem : ggK1CCo_kindOrbit nf (B.kind i) ∈
        (L.filter (fun k => ggK1CCo_Kind.hasOrbit k)).map (ggK1CCo_kindOrbit nf) :=
      List.mem_map.mpr ⟨B.kind i, hk, rfl⟩
    rwa [hO] at hmem
  · intro i hq
    exact (B.hqsKind i).mp hq
  · intro i hq
    exact ggK1CCo_kind_label (B.kind i) ⁅B.A i, B.A i⁆ hq (B.hmodel i hq) hK
  · intro o ho hqs
    have ho' : o ∈ (L.filter (fun k => ggK1CCo_Kind.hasOrbit k)).map (ggK1CCo_kindOrbit nf) := by
      rw [hO]; exact ho
    obtain ⟨k, hk, hko⟩ := List.mem_map.mp ho'
    rw [List.mem_filter] at hk
    obtain ⟨hkL, -⟩ := hk
    obtain ⟨i, -, hi⟩ := Multiset.mem_map.mp (hLmem k hkL)
    rw [← hko] at hqs
    rw [← hi] at hqs
    refine ⟨i, (B.hqsKind i).mpr hqs, ?_⟩
    rw [hi]; exact hko
  · let e : {i : B.ι // CFSG.IsQuasisimple ↥⁅B.A i, B.A i⁆} ≃
        {i : B.ι // (ggK1CCo_kindOrbit nf (B.kind i)).qs = true} :=
      Equiv.subtypeEquiv (Equiv.refl B.ι) (fun i => B.hqsKind i)
    refine ⟨e.trans g, fun i => ?_⟩
    have h := hg (e i)
    dsimp only [O] at h
    rw [show (e i).1 = i.1 from rfl] at h
    exact h
  · intro o ho hqs
    have ho' : o ∈ (L.filter (fun k => ggK1CCo_Kind.hasOrbit k)).map (ggK1CCo_kindOrbit nf) := by
      rw [hO]; exact ho
    obtain ⟨k, hk, hko⟩ := List.mem_map.mp ho'
    rw [List.mem_filter] at hk
    obtain ⟨hkL, hkhas⟩ := hk
    obtain ⟨i, -, hi⟩ := Multiset.mem_map.mp (hLmem k hkL)
    refine ⟨i, ?_, ?_⟩
    · rw [hi]; exact hko
    · rw [← hko] at hqs
      rw [← hi] at hqs
      exact B.hsolv i (by rw [hi]; exact hkhas) hqs

end CFSG.StandardType

end
