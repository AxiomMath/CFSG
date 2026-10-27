module

public import CFSG.LocalAnalysis.StandardType.GGTablePThreeSympDefs
import CFSG.LocalAnalysis.StandardType.GGTablePThreeRLeaf
import CFSG.LocalAnalysis.StandardType.GGTablePThreeSympLift
import CFSG.LocalAnalysis.GLTheoremA.CatA.K1419ClsSympBlock
import CFSG.LocalAnalysis.StandardType.GGTorsionQuotQuasi
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnUniLabelPSU
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnUniScal
import CFSG.Assembly.GL83StatedBridge
import CFSG.Assembly.OpenBridges
import CFSG.HardMathSupport.Solomon.Coordinator.I18_3LInput
import CFSG.HardMathSupport.Solomon.Coordinator.L3C143AltMain
import CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ.Derivation
import CFSG.HardMathSupport.Solomon.UniquenessMaximal.GenL3.Input252
import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6D62
import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6E66
import CFSG.LocalAnalysis.GLTheoremA.CatA.K1419ClsDefs
import CFSG.LocalAnalysis.GLTheoremA.CatA.KD76c
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10FBase2
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnLinPieces
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnUniData
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnUniPComp
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GU64Pieces
import CFSG.LocalAnalysis.GLTheoremA.CatA.YS1011U64Types
import CFSG.LocalAnalysis.GLTheoremA.CatC.ChevQ
import CFSG.LocalAnalysis.GLTheoremA.PartI.I1132
import CFSG.LocalAnalysis.GLTheoremA.PartI.KDSU3Holds
import CFSG.LocalAnalysis.GLTheoremA.PartI.RankTwoDown
import CFSG.LocalAnalysis.GLTheoremA.S10.Bridge
import CFSG.LocalAnalysis.GLTheoremA.S10.Inputs105
import CFSG.LocalAnalysis.GLTheoremA.S10.InputsBeta
import CFSG.LocalAnalysis.GLTheoremA.S10.InputsSetup
import CFSG.LocalAnalysis.GLTheoremA.S11.Inputs119
import CFSG.LocalAnalysis.GLTheoremA.S4.FullCover.MultSporadic
import CFSG.LocalAnalysis.GLTheoremA.S4.YS02Holds
import CFSG.LocalAnalysis.GLTheoremA.S6.Lemma62AuxComp
import CFSG.LocalAnalysis.GLTheoremA.Sec5Setup
import CFSG.LocalAnalysis.RankThreeTheoremC.InvariantTwoBalanceThree
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3Defs
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3Transitive
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.I294Inputs
import CFSG.LocalAnalysis.RankThreeTheoremC.PlaneTransvection
import CFSG.Quasithin.Vol2.KGFactC31RuRef
import CFSG.Quasithin.Vol2.KGFactC31RuRefBase
import CFSG.RankThree.PartTwo.Sec11.Data
import CFSG.RankThree.PartTwo.Sec14.Item1411HJ
import CFSG.RankThree.PartTwo.Sec14.Item143N
import CFSG.RankThree.PartTwo.Sec15.Item157
import CFSG.RankThree.PartTwo.Sec16.Item163ProofR
import CFSG.RankThree.PartTwo.Sec16.Item164Proof
import CFSG.RankThree.PartTwo.Sec16.Item169HJ
import CFSG.RankThree.PartTwo.Sec17.Item1724Two
import CFSG.RankThree.PartTwo.Sec17.Item17TailSteps
import CFSG.RankThree.PartTwo.Sec17.RouteProvers
import CFSG.RankThree.PartTwo.Sec17.RouteProvers142
import CFSG.RankThree.PartTwo.Sec6.Statements
import CFSG.RankThree.S4Free.SuzukiEight
import CFSG.Sporadic.HeldB.Common
import Certificates.Certificate14953
import Certificates.Certificate7233Base
import Certificates.Certificate8166

public section

namespace CFSG.StandardType.TablePThreeKG

open CFSG CFSG.Assembly

section SympShapeProof

open CFSG.LieType.SemisimpleCentralizers.Held

private theorem sympShape_conj_one {G : Type} [Group G] : MulAut.conj (1 : G) = 1 := by
  ext g
  simp [MulAut.conj_apply]

private theorem sympShape_induced_range
    {K : Type} [Field K] [Finite K] {m : ℕ}
    {X : Type} [Group X] [Finite X]
    {A : Subgroup (MulAut X)}
    {θ : X ⧸ Subgroup.center X ≃* LargeEvenProj (LargeEvenSpGroup K m)}
    {Ā : Subgroup (MulAut (LargeEvenProj (LargeEvenSpGroup K m)))}
    (hperf : commutator X = ⊤)
    (hinn : GGInducedInn A θ
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSpGroup K m)) (LargeEvenGSpSet K m)))
    (hmem : ∀ a ∈ A, ggInducedAut θ a ∈ Ā) (hcardĀ : Nat.card Ā = Nat.card A) :
    ∀ a ∈ Ā, a ∈ LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSpGroup K m))
      (LargeEvenGSpSet K m) := by
  intro a ha
  have hf : Function.Injective (ggInducedAut θ) :=
    ggInducedAut_injective_of_perfect hperf θ
  have hcardMap : Nat.card (A.map (ggInducedAut θ)) = Nat.card A :=
    Subgroup.card_map_of_injective hf
  have hle : A.map (ggInducedAut θ) ≤ Ā := by
    intro x hx
    rw [Subgroup.mem_map] at hx
    rcases hx with ⟨y, hy, rfl⟩
    exact hmem y hy
  have hAne : Nat.card A ≠ 0 :=
    Nat.card_ne_zero.mpr ⟨⟨1⟩, inferInstance⟩
  haveI : Finite Ā := Nat.finite_of_card_ne_zero (by rw [hcardĀ]; exact hAne)
  have hEq : A.map (ggInducedAut θ) = Ā :=
    Subgroup.eq_of_le_of_card_ge hle (hcardĀ.trans hcardMap.symm).le
  rw [← hEq] at ha
  rw [Subgroup.mem_map] at ha
  rcases ha with ⟨y, hy, hya⟩
  rw [← hya]
  exact hinn y hy

private theorem sympShape_ggHasLabel_typeA
    {K : Type} [Field K] [Finite K] {a n : ℕ} (ha1 : 1 ≤ a)
    (hK : Nat.card K = 2 ^ n) {X : Type} [Group X]
    (e : X ≃* CFSG.Open.StatedProj (CFSG.Open.StatedSL a K)) :
    GGHasLabel (⟨.A, a - 1, n⟩ : LargeEvenLabel) X := by
  refine ⟨K, inferInstance, inferInstance, hK, ?_⟩
  change Nonempty (X ≃* LargeEvenProj (LargeEvenSLGroup (Fin (a - 1 + 1)) K))
  rw [Nat.sub_add_cancel ha1, CFSG.Assembly.largeEvenSLGroup_eq_statedSL a]
  exact ⟨e⟩

private theorem sympShape_ggHasLabel_twA
    {E : Type} [Field E] [Finite E] {a m : ℕ} (τ : E ≃+* E) (hτ : ∀ x, τ (τ x) = x)
    (hτm : ∀ x, τ x = x ^ 2 ^ m) (hE : Nat.card E = (2 ^ m) ^ 2) (ha : 3 ≤ a)
    (ham : (a, 2 ^ m) ≠ (3, 2)) {X : Type} [Group X]
    (e : X ≃* heldSU a E τ hτ ⧸ Subgroup.center (heldSU a E τ hτ)) :
    GGHasLabel (⟨.twA, a - 1, m⟩ : LargeEvenLabel) X := by
  obtain ⟨eSU⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.Y10GInnUni.nonempty_quot_heldSU_equiv_statedProj
      CFSG.LocalAnalysis.GLTheoremA.Y10GInnUni.uniScalar_holds τ hτ hτm hE ha ham
  refine ⟨E, inferInstance, inferInstance, hE, ?_⟩
  change Nonempty (X ≃* LargeEvenProj (LargeEvenSUGroup (Fin (a - 1 + 1)) E (2 ^ m)))
  rw [Nat.sub_add_cancel (by omega : 1 ≤ a)]
  exact ⟨e.trans eSU⟩

private theorem sympShape_ggHasLabel_typeC
    {K : Type} [Field K] [Finite K] {s n : ℕ} (hK : Nat.card K = 2 ^ n) {X : Type} [Group X]
    (e : X ≃* CFSG.Open.StatedProj (CFSG.Open.StatedSp s K)) :
    GGHasLabel (⟨.C, s, n⟩ : LargeEvenLabel) X := by
  refine ⟨K, inferInstance, inferInstance, hK, ?_⟩
  change Nonempty (X ≃* LargeEvenProj (LargeEvenSpGroup K s))
  exact ⟨e⟩

theorem sympShape_holds :
    ∀ (K : Type) [Field K] [Finite K] (n m : ℕ), Nat.card K = 2 ^ n → (3 ∣ 2 ^ n - 1 ∨ n = 1) →
      ∀ (X : Type) [Group X] [Finite X], commutator X = ⊤ →
        ∀ (θ : X ⧸ Subgroup.center X ≃* LargeEvenProj (LargeEvenSpGroup K m))
          (A : Subgroup (MulAut X)) (δ : MulAut X) (J : Subgroup X), GGKLocal A δ J →
          (∀ Q : Subgroup X, IsComponentOf Q (ggAutFixedSubgroup δ) → Q = J) → 3 ^ 3 ≤ Nat.card A →
          GGInducedInn A θ
            (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSpGroup K m)) (LargeEvenGSpSet K m)) →
          SympShapeConcl n A J := by
  intro K _ _ n m hK hspl X _ _ hperf θ A δ J hKloc huniq hcard hinn
  obtain ⟨Ā, δ', J', hR, hcardĀ, hδ', hmem, hJ', hcen⟩ :=
    leafR_holds X hperf (LargeEvenProj (LargeEvenSpGroup K m)) θ A δ J hKloc huniq hcard
  have hĀI : ∀ a ∈ Ā, a ∈ LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSpGroup K m))
      (LargeEvenGSpSet K m) :=
    sympShape_induced_range hperf hinn hmem hcardĀ
  obtain ⟨x, hx3, hx1, hδx, E, hEsub, hEelem, hEcard⟩ :=
    sympShape_lift (K := K) (m := m) hK hR hĀI
  have hperfJ : commutator ↥J = ⊤ := by
    have hcomp : IsComponentOf J (ggAutFixedSubgroup δ) := hKloc.1.2.2.2.1
    obtain ⟨-, -, hqs⟩ := hcomp
    exact hqs.1
  have hfix : CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup
        (MulAut.conj (CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.proj m K x)) =
      ggAutFixedSubgroup (MulAut.conj
        (CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.proj m K x)) :=
    Subgroup.ext fun _ => Iff.rfl
  have hcompA : IsComponentOf J' (ggAutFixedSubgroup
      (MulAut.conj (CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.proj m K x))) := by
    rw [← hδx]
    exact hR.comp
  have hcompO : CFSG.Open.IsComponentOf J'
      (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup
        (MulAut.conj (CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.proj m K x))) := by
    rw [hfix]
    exact (CFSG.Assembly.isComponentOf_iff_open).mp hcompA
  have huniqO : ∀ Q : Subgroup (LargeEvenProj (LargeEvenSpGroup K m)),
      CFSG.Open.IsComponentOf Q
        (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup
          (MulAut.conj (CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.proj m K x))) →
      Q = J' := by
    intro Q hQ
    have hQa : IsComponentOf Q (ggAutFixedSubgroup
        (MulAut.conj (CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.proj m K x))) := by
      rw [← hfix]
      exact (CFSG.Assembly.isComponentOf_iff_open).mpr hQ
    exact hR.uniq Q (by rwa [← hδx] at hQa)
  have hblock :=
    CFSG.LocalAnalysis.GLTheoremA.K1419.k1419ClsSympBlock_sized (K := K) (m := m) hK x hx3 hx1
      hcompO
  obtain ⟨eJ⟩ := ggTorsion_centerQuot_image_equiv θ hperfJ
  have heJZ : Nonempty (↥J ⧸ Subgroup.center ↥J ≃* ↥J' ⧸ Subgroup.center ↥J') := by
    rw [hJ']
    exact ⟨eJ⟩
  obtain ⟨eJZ⟩ := heJZ
  rcases hblock with hA | hSU | hSp | hA6
  ·
    obtain ⟨a, ha2, hcond, hlabel, hxJ', hrank⟩ := hA
    have hn1 : n ≠ 1 := by
      intro hn
      have hK2 : Nat.card K = 2 := by rw [hK, hn]; norm_num
      rcases hcond with h3 | ⟨-, h4⟩
      · rw [hK2] at h3; norm_num at h3
      · rw [hK2] at h4; norm_num at h4
    have h3n : 3 ∣ 2 ^ n - 1 := by
      rcases hspl with h | h
      · exact h
      · exact absurd h hn1
    left
    refine ⟨a, ha2, h3n, ?_, ?_, ?_⟩
    · exact sympShape_ggHasLabel_typeA (K := K) (a := a) (n := n) (by omega) hK
        (X := ↥J ⧸ Subgroup.center ↥J) (eJZ.trans hlabel.some)
    · intro ha3
      have hxJ'mem : (CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.proj m K x :
          LargeEvenProj (LargeEvenSpGroup K m)) ∈ J' := hxJ' (by rw [ha3])
      have hZJ' : Subgroup.center ↥J' ≠ ⊥ := by
        intro hbot
        have hmemZ : (⟨CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.proj m K x,
            hxJ'mem⟩ : ↥J') ∈ Subgroup.center ↥J' := by
          rw [Subgroup.mem_center_iff]
          intro y
          apply Subtype.ext
          have hyfix := (CFSG.HardMathSupport.Solomon.Coordinator.mem_fixSubgroup.mp
            (hcompO.1 y.2))
          rw [MulAut.conj_apply] at hyfix
          have h := congrArg
            (fun w => w * (CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.proj m K x :
              LargeEvenProj (LargeEvenSpGroup K m))) hyfix
          have h' : (CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.proj m K x :
                LargeEvenProj (LargeEvenSpGroup K m)) *
                (y : LargeEvenProj (LargeEvenSpGroup K m)) =
              (y : LargeEvenProj (LargeEvenSpGroup K m)) *
                (CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.proj m K x :
                  LargeEvenProj (LargeEvenSpGroup K m)) := by
            simpa only [mul_assoc, inv_mul_cancel, mul_one] using h
          exact h'.symm
        have h1 : (⟨CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.proj m K x, hxJ'mem⟩ :
            ↥J') = 1 := by
          rw [← Subgroup.mem_bot, ← hbot]
          exact hmemZ
        have hpx1 : (CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.proj m K x :
            LargeEvenProj (LargeEvenSpGroup K m)) = 1 :=
          congrArg (fun z : ↥J' => (z : LargeEvenProj (LargeEvenSpGroup K m))) h1
        exact hR.ne_one (by rw [hδx, hpx1, sympShape_conj_one])
      intro hJbot
      exact hZJ' ((hcen.1 hJbot).1)
    · intro ha2
      have h9 : Nat.card E ≤ 9 := hrank ha2 huniqO E hEsub hEelem
      omega
  ·
    right; left
    obtain ⟨a, E', hEf, hEfin, τ, hτ, ha2, hn3, hK2a, hτm, hEcard', hlabel, hxJ'⟩ := hSU
    have hn1 : n = 1 := by
      rcases hspl with h | h
      · exact absurd (by rwa [← hK] at h) hn3
      · exact h
    have hK2 : Nat.card K = 2 := by rw [hK, hn1]; norm_num
    have ha4 : 4 ≤ a := hK2a hK2
    refine ⟨hn1, a, ha4, ?_⟩
    letI : Field E' := hEf
    letI : Finite E' := hEfin
    have hE4 : Nat.card E' = (2 ^ 1) ^ 2 := by rw [hEcard', hK2]; norm_num
    have hτm1 : ∀ y, τ y = y ^ 2 ^ 1 := by
      intro y
      rw [pow_one, ← hK2]
      exact hτm y
    have ham : (a, 2 ^ 1) ≠ (3, 2) := by
      intro h
      have h3 : a = 3 := congrArg Prod.fst h
      omega
    exact sympShape_ggHasLabel_twA (E := E') (a := a) (m := 1) τ hτ hτm1 hE4 (by omega) ham
      (X := ↥J ⧸ Subgroup.center ↥J) (eJZ.trans hlabel.some)
  ·
    right; right; left
    obtain ⟨s, hs2, hsne, hlabel⟩ := hSp
    refine ⟨s, hs2, ?_, ?_⟩
    · rintro ⟨hs, hn⟩
      exact hsne ⟨hs, by rw [hK, hn]; norm_num⟩
    · exact sympShape_ggHasLabel_typeC (K := K) (s := s) (n := n) hK
        (X := ↥J ⧸ Subgroup.center ↥J) (eJZ.trans hlabel.some)
  ·
    right; right; right
    obtain ⟨hK2, hcard360⟩ := hA6
    refine ⟨?_, ?_⟩
    · have hpow : 2 ^ n = 2 ^ 1 := by rw [← hK, hK2]; norm_num
      exact Nat.pow_right_injective (a := 2) (by norm_num) hpow
    · rw [Nat.card_congr eJZ.toEquiv, hcard360]

end SympShapeProof

end CFSG.StandardType.TablePThreeKG

end
