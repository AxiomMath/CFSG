module

public import CFSG.LocalAnalysis.StandardType.GGResILineInputs
public import CFSG.LocalAnalysis.StandardType.GGResLeviLE3BridgeA2
public import CFSG.LocalAnalysis.StandardType.GGTorusGenRkTransport
public import CFSG.LocalAnalysis.StandardType.GGTableBUnitDvdAct
public import CFSG.LocalAnalysis.StandardType.GGTBJTwoNodeUnitary
public import CFSG.LocalAnalysis.StandardType.GGTBJTwoNodeUnitarySix
public import CFSG.LocalAnalysis.StandardType.GGTBTorAIndHolds
public import CFSG.LocalAnalysis.StandardType.GGTBTorAIndUFourTwo
public import CFSG.LocalAnalysis.StandardType.GGRCWeylCard
public import CFSG.LocalAnalysis.StandardType.GGTwA5ThreeFrame
public import CFSG.LocalAnalysis.StandardType.GGTableBUnitaryTorusRank
public import CFSG.LocalAnalysis.StandardType.GGResJUnitaryCubicBlock
public import CFSG.LocalAnalysis.StandardType.GGUSixThreeKGWeyl
public import CFSG.LocalAnalysis.StandardType.GGTableBUnitarySixThreeCases
public import CFSG.LocalAnalysis.StandardType.GGUSixThreeKGFieldStruct
public import CFSG.LocalAnalysis.StandardType.GGNbrU63StepTwo
public import CFSG.LocalAnalysis.StandardType.GGUSixShSub
public import CFSG.LocalAnalysis.StandardType.GGTwoNodeRowDimReduced

public section

namespace CFSG.StandardType

open CFSG.Assembly
open CFSG.Open
open CFSG.ClassicalGroups.UnitaryFlag

theorem card_ggAutomizer_eq_factorial_of_unitaryTorusData
    {G : Type} [Group G] [Finite G] {r n : ℕ} {Bs J : Subgroup G}
    [Fact (Nat.Prime 3)]
    (hBs : IsElemAbelian 3 Bs)
    (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs)
    (hN : Bs ≤ Subgroup.normalizer (J : Set G))
    (hpq : 3 ∣ 2 ^ n + 1)
    (hTor : GGTorusTorData (2 ^ n + 1) r (CartanMatrix.A r) (CoxeterMatrix.A r) ↥J
      (ggGamma J hN).range) :
    Nat.card (ggAutomizer J Bs) = (r + 1).factorial := by
  classical
  have hnpos : 0 < n := by
    rcases Nat.eq_zero_or_pos n with rfl | h
    · norm_num at hpq
    · exact h
  have hm : Odd (2 ^ n + 1) :=
    (Nat.even_pow.mpr ⟨even_two, Nat.ne_of_gt hnpos⟩).add_one
  obtain ⟨w, hw⟩ := hTor
  obtain ⟨hnk, -, -, -, -, -, -, -⟩ :=
    ggTD_core (G := G) (p := 3) (m := 2 ^ n + 1) (N := r)
      (C := CartanMatrix.A r) (M := CoxeterMatrix.A r) (Bs := Bs) (X := J)
      hm hpq hBs hSC hN w hw
  obtain ⟨e, -⟩ :=
    ggTD_weyl (G := G) (p := 3) (m := 2 ^ n + 1) (N := r)
      (C := CartanMatrix.A r) (M := CoxeterMatrix.A r) (Bs := Bs) (X := J)
      hN hw (by norm_num) hBs hnk
  calc Nat.card (ggAutomizer J Bs) = Nat.card (CoxeterMatrix.A r).Group :=
        (Nat.card_congr e.toEquiv).symm
    _ = (r + 1).factorial := l05nK3a_card_coxeterA r

theorem GGResHyp.false_of_rankFive_lineJDatum_of_card_ge_eightyone
    {G : Type} [Group G] [Finite G]
    {B Bs L D J K : Subgroup G} {x y : G}
    (hH : GGResHyp 3 B Bs x L D J y K)
    {T : GGResLineJType} (hD : GGResLineJDatum 3 Bs J T)
    (hMark : GGInnerDiagOnLabel
      (fun _ lab => lab.tag = .twA ∧ lab.rank = 5 ∧ 3 ∣ 2 ^ lab.n + 1) 3 Bs J)
    (h81 : ∀ hN : Bs ≤ Subgroup.normalizer (J : Set G),
      3 ^ 4 ≤ Nat.card (ggGamma J hN).range) :
    False := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcfg : GGConfig 3 B Bs x L D J := hH.1
  have hmark : GGInnerDiagOnLabel
      (fun _ lab => lab.tag = .twA ∧ lab.rank = 5 ∧ 3 ∣ ggTorM lab) 3 Bs J := by
    refine largeEvenMarking_mono (fun lab R _ I F θ hP => ?_) hMark
    obtain ⟨hlab, hN', hBsI⟩ := hP
    exact ⟨⟨hlab.1, hlab.2.1, by simpa [ggTorM, hlab.1] using hlab.2.2⟩, hN', hBsI⟩
  obtain ⟨f, hf, hpq, -, hN, hTor⟩ := ggTwA5Three_torData hcfg hmark h81
  have hcard720 : Nat.card (ggAutomizer J Bs) = 720 := by
    have h := card_ggAutomizer_eq_factorial_of_unitaryTorusData
      (hBs := hH.1.2.1.2.1) (hSC := hH.1.2.1.2.2.2) (hN := hN) hpq hTor
    norm_num at h ⊢
    exact h
  have hcard48 := ResJCubicBlock.card_ggAutomizer_le_fortyEight_of_lineJDatum hD
  omega

theorem GGResHyp.card_range_eq_twentyseven_or_ge_eightyone
    {G : Type} [Group G] [Finite G]
    {B Bs L D J K : Subgroup G} {x y : G}
    (hH : GGResHyp 3 B Bs x L D J y K)
    (hMark : GGInnerDiagOnLabel
      (fun _ lab => lab.tag = .twA ∧ lab.rank = 5 ∧ 3 ∣ 2 ^ lab.n + 1) 3 Bs J)
    (hN : Bs ≤ Subgroup.normalizer (J : Set G)) :
    Nat.card (ggGamma J hN).range = 27 ∨
      3 ^ 4 ≤ Nat.card (ggGamma J hN).range := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hperfJ, lab, hΛ, hraw⟩ := hMark
  obtain ⟨tag, r, n⟩ := lab
  obtain ⟨R0, _, I0, F0, hQ0⟩ := largeEvenRawDatum_exists hraw
  obtain ⟨_, _, θ0, hP0⟩ := hQ0
  obtain ⟨hS0, _, _⟩ := hP0
  have htag : tag = .twA := hS0.1
  have hr5 : r = 5 := hS0.2.1
  have hpq : 3 ∣ 2 ^ n + 1 := hS0.2.2
  subst htag
  subst hr5
  have hn : 1 ≤ n := hΛ.1
  have hraw0 := hraw
  dsimp only [LargeEvenRawDatum] at hraw
  obtain ⟨F, hFfield, hFfinite, hFcard, hQ⟩ := hraw
  letI : Field F := hFfield
  letI : Finite F := hFfinite
  obtain ⟨_hsimple, _hnonab, θ, hP⟩ := hQ
  obtain ⟨hS, hN0, hBsI⟩ := hP
  let A0 : Subgroup (MulAut ↥J) := (ggGamma J hN0).range
  have hAe0 : IsElemAbelian 3 A0 := by
    dsimp [A0]
    exact isElemAbelian_range
      (fun a b : ↥Bs => (@IsMulCommutative.is_comm ↥Bs _ hH.1.2.1.2.1.1).comm a b)
      (fun b : ↥Bs => Subtype.ext (by simpa using hH.1.2.1.2.1.2 b b.2))
      (ggGamma J hN0)
  have hT : GGTorusLift 3 3
      (LargeEvenProj (LargeEvenSUGroup (Fin 6) F (2 ^ n))) := by
    have h := ggTorusLift_unitary (K := F) (n := n) (d := 6) (p := 3)
      hFcard hn (by norm_num) (by
        intro h6
        have h6' : 6 = 3 := congrArg Prod.fst h6
        omega) (by norm_num) hpq
    simpa [ggUnitaryTorusRank] using h
  have h27A0 : 27 ≤ Nat.card A0 := by
    have h := GGResHyp.pow_le_card_range_gamma_J_of_torusLift hH θ hT
    simpa [A0] using h
  have hgamma : ggGamma J hN0 = ggGamma J hN := by
    ext b
    rfl
  have hcardeq : Nat.card (ggGamma J hN).range =
      Nat.card (ggGamma J hN0).range := by
    rw [hgamma]
  rw [hcardeq]
  by_cases h81 : 3 ^ 4 ≤ Nat.card (ggGamma J hN0).range
  · exact Or.inr h81
  · left
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.1
      (CFSG.Open.IsElemAbelian.isPGroup hAe0)
    have hk3 : 3 ≤ k := by
      by_contra hklt
      have hk2 : k ≤ 2 := by omega
      have hle : 3 ^ k ≤ 3 ^ 2 := Nat.pow_le_pow_right (by norm_num) hk2
      have h27' : 27 ≤ 3 ^ k := by simpa [hk] using h27A0
      norm_num at hle
      omega
    have hk3' : k ≤ 3 := by
      by_contra hklt
      have hk4 : 4 ≤ k := by omega
      have hle : 3 ^ 4 ≤ 3 ^ k := Nat.pow_le_pow_right (by norm_num) hk4
      apply h81
      rw [show Nat.card (ggGamma J hN0).range = 3 ^ k by simpa [A0] using hk]
      exact hle
    have hk_eq : k = 3 := by omega
    rw [hk, hk_eq]
    norm_num

theorem GGResHyp.card_range_eq_twentyseven_of_rankFive_lineJDatum
    {G : Type} [Group G] [Finite G]
    {B Bs L D J K : Subgroup G} {x y : G}
    (hH : GGResHyp 3 B Bs x L D J y K)
    {T : GGResLineJType} (hD : GGResLineJDatum 3 Bs J T)
    (hMark : GGInnerDiagOnLabel
      (fun _ lab => lab.tag = .twA ∧ lab.rank = 5 ∧ 3 ∣ 2 ^ lab.n + 1) 3 Bs J)
    (hN : Bs ≤ Subgroup.normalizer (J : Set G)) :
    Nat.card (ggGamma J hN).range = 27 := by
  rcases GGResHyp.card_range_eq_twentyseven_or_ge_eightyone hH hMark hN with h | h
  · exact h
  · exact False.elim (GGResHyp.false_of_rankFive_lineJDatum_of_card_ge_eightyone hH hD hMark
      (fun hN' => by
        have hgamma : ggGamma J hN' = ggGamma J hN := by
          ext b
          rfl
        rw [hgamma]
        exact h))

open Matrix CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.RankThree.PartOne.KCUnitaryModel
open CFSG.StandardType.ResJUnitaryActor

theorem GGResHyp.false_of_rankFive_lineJDatum_q_gt_two
    {G : Type} [Group G] [Finite G]
    {B Bs L D J K : Subgroup G} {x y : G}
    (hH : GGResHyp 3 B Bs x L D J y K)
    {T : GGResLineJType} (hD : GGResLineJDatum 3 Bs J T)
    (hMark : GGInnerDiagOnLabel
      (fun _ lab => lab.tag = .twA ∧ lab.rank = 5 ∧
        3 ∣ 2 ^ lab.n + 1 ∧ lab.n ≠ 1) 3 Bs J) :
    False := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hMark27 : GGInnerDiagOnLabel
      (fun _ lab => lab.tag = .twA ∧ lab.rank = 5 ∧ 3 ∣ 2 ^ lab.n + 1) 3 Bs J := by
    refine largeEvenMarking_mono (fun lab R _ I F θ hP => ?_) hMark
    obtain ⟨⟨htag, hrank, hpq, -⟩, hN', hBsI⟩ := hP
    exact ⟨⟨htag, hrank, hpq⟩, hN', hBsI⟩
  obtain ⟨F, hFfield, hFfinite, n, hn2, hpq, hFcard, θ, φ, hU, A, ρ, hN, hAGU, hAiso,
    hφs, hφker, hφcomp, hAprime, hAproj, hYact, hρ⟩ :=
    GGInnerDiagOnLabel.exists_SU6_cover_actors hMark
  letI : Field F := hFfield
  letI : Finite F := hFfinite
  haveI : CharP F 2 := hU.charP
  have hperfJ : commutator ↥J = ⊤ := hMark.1
  let Ab : Subgroup (MulAut (LargeEvenProj (LargeEvenSUGroup (Fin 6) F (2 ^ n)))) :=
    (ggBeta J θ hN).range
  have hcardAb : Nat.card Ab = 27 := by
    dsimp only [Ab]
    rw [NbrU63.card_range_ggBeta_eq hperfJ θ hN]
    exact GGResHyp.card_range_eq_twentyseven_of_rankFive_lineJDatum hH hD hMark27 hN
  have hAb : IsElemAbelian 3 Ab :=
    isElemAbelian_range_ggBeta θ hH.1.2.1.2.1 hN
  have hAbI : ∀ a ∈ Ab, a ∈ LargeEvenMatConjImage
      (LargeEvenProjMk (unitarySU 2 n F 6))
      (LargeEvenGUSet (Fin 6) F (2 ^ n)) := by
    rintro a ⟨b, rfl⟩
    rw [← hAproj b]
    exact ggUSixSh_projConj_mem_matConjImage (hA := hAGU b)
      (hAN := TableBUE.gu_subset_normalizer hU (hAGU b))
  have hBs : IsElemAbelian 3 Bs := hH.1.2.1.2.1
  have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs :=
    hH.1.2.1.2.2.2
  have hAN : ∀ b, A b ∈ Subgroup.normalizer (unitarySU 2 n F 6 : Set (GL (Fin 6) F)) :=
    fun b => TableBUE.gu_subset_normalizer hU (hAGU b)
  have hAA : ∀ b, TableB.projConj (unitarySU 2 n F 6) ⟨A b, hAN b⟩ ∈ Ab := by
    intro b
    exact ⟨b, (hAproj b).symm⟩
  by_cases hfr : ∃ P ∈ primeFormUnitary hU (idGram F 6), ∀ a ∈ Ab,
      ∃ (M : GL (Fin 6) F) (hM : M ∈ LargeEvenGUSet (Fin 6) F (2 ^ n)),
        ((P⁻¹ * M * P : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F).IsDiag ∧
        a = TableB.projConj (unitarySU 2 n F 6)
          ⟨M, TableBUE.gu_subset_normalizer hU hM⟩
  ·
    obtain ⟨P, hP, hframe⟩ := hfr
    have hPgu : P ∈ LargeEvenGUSet (Fin 6) F (2 ^ n) :=
      TableBUD.mem_guSet_of_mem_primeFormUnitary hU hP
    have hPN : P ∈ Subgroup.normalizer (unitarySU 2 n F 6 : Set (GL (Fin 6) F)) :=
      TableBUE.gu_subset_normalizer hU hPgu
    have hPinv : P⁻¹ ∈ primeFormUnitary hU (idGram F 6) :=
      (primeFormUnitary hU (idGram F 6)).inv_mem hP
    let φP : ↥(unitarySU 2 n F 6) →* ↥J :=
      φ.comp (TableBUE.conjSU hU P⁻¹ hPinv).toMonoidHom
    have hModelP : UnitTB.Model φP := by
      refine ⟨hU, hφs.comp (TableBUE.conjSU hU P⁻¹ hPinv).surjective, ?_⟩
      intro g hg
      obtain ⟨c, hc⟩ := hφker (TableBUE.conjSU hU P⁻¹ hPinv g) hg
      refine ⟨c, ?_⟩
      have hcoe := TableBUE.coe_conjSU hU P⁻¹ hPinv g
      have hgmat : (P : GL (Fin 6) F) * (g : GL (Fin 6) F) * (P : GL (Fin 6) F)⁻¹ =
          GeneralLinearGroup.scalar (Fin 6) c := by
        calc (P : GL (Fin 6) F) * (g : GL (Fin 6) F) * (P : GL (Fin 6) F)⁻¹
            = ((P⁻¹ : GL (Fin 6) F)⁻¹) * (g : GL (Fin 6) F) * (P⁻¹ : GL (Fin 6) F) := by
              group
          _ = ((TableBUE.conjSU hU P⁻¹ hPinv g : ↥(unitarySU 2 n F 6)) : GL (Fin 6) F) :=
              hcoe.symm
          _ = GeneralLinearGroup.scalar (Fin 6) c := hc
      have hgscal : (g : GL (Fin 6) F) = GeneralLinearGroup.scalar (Fin 6) c := by
        calc (g : GL (Fin 6) F)
            = (P : GL (Fin 6) F)⁻¹ *
                ((P : GL (Fin 6) F) * (g : GL (Fin 6) F) * (P : GL (Fin 6) F)⁻¹) *
                (P : GL (Fin 6) F) := by group
          _ = (P : GL (Fin 6) F)⁻¹ * GeneralLinearGroup.scalar (Fin 6) c *
                (P : GL (Fin 6) F) := by rw [hgmat]
          _ = GeneralLinearGroup.scalar (Fin 6) c := by
              rw [show (P : GL (Fin 6) F)⁻¹ * GeneralLinearGroup.scalar (Fin 6) c =
                GeneralLinearGroup.scalar (Fin 6) c * (P : GL (Fin 6) F)⁻¹ from
                  (commute_scalar c (P : GL (Fin 6) F)⁻¹).eq]
              group
      rw [hgscal, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply]
    have hdiagP : ∀ a ∈ (ggGamma J hN).range, ∃ t : Fin 6 → F, LineU.ActsDiagU φP a t := by
      rintro a ⟨b, rfl⟩
      obtain ⟨M, hMgu, hMdiag, hMeq⟩ := hframe (ggBeta J θ hN b) ⟨b, rfl⟩
      have hprojEq : TableB.projConj (unitarySU 2 n F 6)
          ⟨A b, TableBUE.gu_subset_normalizer hU (hAGU b)⟩ =
          TableB.projConj (unitarySU 2 n F 6)
            ⟨M, TableBUE.gu_subset_normalizer hU hMgu⟩ :=
        (hAproj b).trans hMeq
      obtain ⟨c, hc⟩ := CFSG.StandardType.Line63.H5.exists_scalar_mul_of_projConj_eq'
        hU hpq (TableBUE.gu_subset_normalizer hU (hAGU b))
        (TableBUE.gu_subset_normalizer hU hMgu) hprojEq
      let D : GL (Fin 6) F := P⁻¹ * A b * P
      have hDn : D ∈ Subgroup.normalizer (unitarySU 2 n F 6 : Set (GL (Fin 6) F)) := by
        dsimp only [D]
        exact Subgroup.mul_mem _
          (Subgroup.mul_mem _ (Subgroup.inv_mem _ hPN) (hAN b)) hPN
      have hAdiag : ((D : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F).IsDiag := by
        have hgroup : D = GeneralLinearGroup.scalar (Fin 6) c * (P⁻¹ * M * P) := by
          dsimp only [D]
          rw [hc]
          calc (P : GL (Fin 6) F)⁻¹ *
                (GeneralLinearGroup.scalar (Fin 6) c * M) * (P : GL (Fin 6) F)
              = ((P : GL (Fin 6) F)⁻¹ * GeneralLinearGroup.scalar (Fin 6) c) * M *
                  (P : GL (Fin 6) F) := by group
            _ = (GeneralLinearGroup.scalar (Fin 6) c * (P : GL (Fin 6) F)⁻¹) * M *
                  (P : GL (Fin 6) F) := by
                rw [(commute_scalar c (P : GL (Fin 6) F)⁻¹).eq]
            _ = GeneralLinearGroup.scalar (Fin 6) c *
                  ((P : GL (Fin 6) F)⁻¹ * M * (P : GL (Fin 6) F)) := by group
        have hmat : ((D : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) =
            (c : F) • (((P⁻¹ * M * P : GL (Fin 6) F)) : Matrix (Fin 6) (Fin 6) F) := by
          simp only [hgroup, Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar,
            Matrix.scalar_apply, ← Matrix.smul_eq_diagonal_mul]
        rw [hmat]
        exact hMdiag.smul (c : F)
      let t : Fin 6 → F := fun i => ((D : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) i i
      have hDt : ((D : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) = diagonal t :=
        hAdiag.diagonal_diag.symm
      refine ⟨t, D, hDn, hDt, ?_⟩
      intro s
      apply Subtype.ext
      change (b : G) * (((φ (TableBUE.conjSU hU P⁻¹ hPinv s) : ↥J)) : G) * (b : G)⁻¹ =
        (((φ (TableBUE.conjSU hU P⁻¹ hPinv (LineU.conjN D hDn s)) : ↥J)) : G)
      rw [hYact b (TableBUE.conjSU hU P⁻¹ hPinv s)]
      have harg : conjSU hU (A b) (hAiso b)
            (TableBUE.conjSU hU P⁻¹ hPinv s) =
          TableBUE.conjSU hU P⁻¹ hPinv (LineU.conjN D hDn s) := by
        apply Subtype.ext
        simp only [conjSU_coe_GL, TableBUE.coe_conjSU, LineU.coe_conjN]
        dsimp only [D]
        group
      rw [harg]
    have hA : IsElemAbelian 3 (ggGamma J hN).range :=
      isElemAbelian_range
        (fun a b : ↥Bs => Subtype.ext (IsElemAbelian.comm hBs a.2 b.2))
        (fun b : ↥Bs => Subtype.ext (by simpa using hBs.2 b b.2)) (ggGamma J hN)
    have hsc : GGTorusSelfCent 3 (ggGamma J hN).range :=
      ggTorusSelfCent_ggGamma hN hSC
    have hcardA : Nat.card (ggGamma J hN).range = 27 :=
      GGResHyp.card_range_eq_twentyseven_of_rankFive_lineJDatum hH hD hMark27 hN
    exact false_of_diagonal_frame_card_twentyseven hModelP hFcard hpq hA hsc hdiagP hcardA
  ·
    have hnofr : ¬ ∃ P ∈ primeFormUnitary hU (idGram F 6), ∀ a ∈ Ab,
        ∃ (M : GL (Fin 6) F) (hM : M ∈ LargeEvenGUSet (Fin 6) F (2 ^ n)),
          ((P⁻¹ * M * P : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F).IsDiag ∧
          a = TableB.projConj (unitarySU 2 n F 6)
            ⟨M, TableBUE.gu_subset_normalizer hU hM⟩ := hfr
    have hcard27 : 3 ^ 3 ≤ Nat.card Ab := by rw [hcardAb]; norm_num
    rcases TableBU63.fieldType_or_heis hU hFcard hpq hAb hAbI hcard27 hnofr with
      ⟨M, hMN, l, hMu, hM3, hl, hMA⟩ |
      ⟨x, y, z, hxN, hyN, hzN, ζ, hxu, hyu, hzu, hxA, hyA, hzA,
        hx3, hz3, hζ3, hζ1, hxy, hxz, hyz, hzs⟩
    ·
      obtain ⟨X, Z, hXN, hZN, ζ, hXu, hZu, hXA, hZA, hX3, hZ3, hζ, hXM, hXZ, hMZ, hZs⟩ :=
        UnitSixThreeKG.exists_fieldStruct hU hFcard hpq hAb hAbI hcardAb hMN hMu hM3 hl hMA
      have hYreal : ∃ b : ↥Bs, TableB.projConj (unitarySU 2 n F 6) ⟨A b, hAN b⟩ =
          TableB.projConj (unitarySU 2 n F 6) ⟨M, hMN⟩ := by
        obtain ⟨b, hb⟩ := hMA
        exact ⟨b, (hAproj b).trans hb⟩
      exact (UnitSixThreeKG.not_noTransvection_of_actual_triple hU hpq hBs hSC φ hφker A hAN
        (fun b => conjSU hU (A b) (hAiso b))
        (fun b g => conjSU_coe_GL hU (A b) (hAiso b) g)
        hYact hXN hMN hZN hXu hMu hZu hζ hX3 hZ3 hXM hXZ hMZ hZs hcardAb
        hXA hMA hZA hAA hYreal) hH.2.2.2.1
    ·
      have hζ : IsPrimitiveRoot ζ 3 :=
        IsPrimitiveRoot.iff_orderOf.mpr (orderOf_eq_prime hζ3 hζ1)
      have hYreal : ∃ b : ↥Bs, TableB.projConj (unitarySU 2 n F 6) ⟨A b, hAN b⟩ =
          TableB.projConj (unitarySU 2 n F 6) ⟨y, hyN⟩ := by
        obtain ⟨b, hb⟩ := hyA
        exact ⟨b, (hAproj b).trans hb⟩
      exact (UnitSixThreeKG.not_noTransvection_of_actual_triple hU hpq hBs hSC φ hφker A hAN
        (fun b => conjSU hU (A b) (hAiso b))
        (fun b g => conjSU_coe_GL hU (A b) (hAiso b) g)
        hYact hxN hyN hzN hxu hyu hzu hζ hx3 hz3 hxy hxz hyz hzs hcardAb
        hxA hyA hzA hAA hYreal) hH.2.2.2.1

open CFSG.StandardType.Line63.H5

theorem GGResHyp.false_of_rankFive_lineJDatum_q_eq_two
    {G : Type} [Group G] [Finite G]
    {B Bs L D J K : Subgroup G} {x y : G}
    (hH : GGResHyp 3 B Bs x L D J y K)
    {T : GGResLineJType} (hD : GGResLineJDatum 3 Bs J T)
    (hMark : GGInnerDiagOnLabel (fun _ lab => lab = ⟨.twA, 5, 1⟩) 3 Bs J) :
    False := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let hN : Bs ≤ Subgroup.normalizer (J : Set G) := GGResHyp.Bs_le_normalizer_J hH
  obtain ⟨F, hFfield, hFfinite, hF4, hU, θ, φ, hφ1, hrange, hφk, A, hAGU, hAN,
    hAprime, hAproj, ρ, hmk, hActs, _hTrue⟩ :=
    GGResHyp.exists_redUnitarySixTwoActors hH hMark hN
  letI : Field F := hFfield
  letI : Finite F := hFfinite
  haveI : CharP F 2 := hU.charP
  have hANu : ∀ b, A b ∈ Subgroup.normalizer
      (unitarySU 2 1 F 6 : Set (GL (Fin 6) F)) := fun b => hAN b
  have hActsEq : ∀ b s,
      redMkB hN b * φ s * (redMkB hN b)⁻¹ = φ (LineU.conjN (A b) (hAN b) s) := by
    intro b s
    obtain ⟨hNorm, hAct⟩ := hActs b
    exact hAct s
  have hFcard : Nat.card F = (2 ^ 1) ^ 2 := by rw [hF4]; norm_num
  have h3n : 3 ∣ 2 ^ 1 + 1 := by norm_num
  have hBs : CFSG.Open.IsElemAbelian 3 Bs := hH.1.2.1.2.1
  have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs :=
    hH.1.2.1.2.2.2
  have hMark27 : GGInnerDiagOnLabel
      (fun _ lab => lab.tag = .twA ∧ lab.rank = 5 ∧ 3 ∣ 2 ^ lab.n + 1) 3 Bs J := by
    refine largeEvenMarking_mono (fun lab R _ I F θ hP => ?_) hMark
    obtain ⟨hS, hN', hBsI⟩ := hP
    rw [hS]
    exact ⟨⟨rfl, rfl, by norm_num⟩, hN', hBsI⟩
  let X : Subgroup (RedGrp J) :=
    (J.subgroupOf (Subgroup.normalizer (J : Set G))).map (redMk J)
  let Bsbar : Subgroup (RedGrp J) := (redMkB hN).range
  have hXeq : X = (redMkL J).range := by
    dsimp only [X, redMkL]
    rw [MonoidHom.range_comp, Subgroup.inclusion_range]
  have hXnormal : X.Normal := by
    rw [hXeq]
    exact redL_normal (L := J)
  haveI : X.Normal := hXnormal
  have hBsbar : CFSG.Open.IsElemAbelian 3 Bsbar := isElemAbelian_redB hN hBs
  have hSCbar : ∀ g ∈ Subgroup.centralizer (Bsbar : Set (RedGrp J)), g ^ 3 = 1 →
      g ∈ Bsbar := redSC hN hBs hSC
  have hNoTrbar : GGNoTransvection 3 Bsbar := noTransvection_red hN hBs hH.2.2.2.1
  let Ab : Subgroup (MulAut (LargeEvenProj (unitarySU 2 1 F 6))) := (ggBeta J θ hN).range
  have hcardAb : Nat.card Ab = 27 := by
    dsimp only [Ab]
    calc Nat.card (ggBeta J θ hN).range
        = Nat.card (ggGamma J hN).range := NbrU63.card_range_ggBeta_eq hMark.1 θ hN
      _ = 27 := GGResHyp.card_range_eq_twentyseven_of_rankFive_lineJDatum hH hD hMark27 hN
  have hAb : IsElemAbelian 3 Ab := by
    dsimp only [Ab]
    exact isElemAbelian_range_ggBeta θ hBs hN
  have hAbI : ∀ a ∈ Ab, a ∈ LargeEvenMatConjImage
      (LargeEvenProjMk (unitarySU 2 1 F 6)) (LargeEvenGUSet (Fin 6) F (2 ^ 1)) := by
    rintro a ⟨b, rfl⟩
    rw [← hAproj b]
    exact ggUSixSh_projConj_mem_matConjImage (hA := hAGU b) (hAN := hAN b)
  have hAA : ∀ b, TableB.projConj (unitarySU 2 1 F 6) ⟨A b, hAN b⟩ ∈ Ab := by
    intro b
    exact ⟨b, (hAproj b).symm⟩
  obtain ⟨hbar, hcardAred_eq⟩ :=
    CFSG.StandardType.card_range_ggGamma_eq_redMk
      (X := J) (B := Bs) (J := J) hN le_rfl hN hMark.1
  let Ared : Subgroup (MulAut ↥X) := (ggGamma X hbar).range
  have hAred : IsElemAbelian 3 Ared := by
    dsimp only [Ared]
    exact isElemAbelian_range
      (fun a b : ↥Bsbar => Subtype.ext (IsElemAbelian.comm hBsbar a.2 b.2))
      (fun b : ↥Bsbar => Subtype.ext (by simpa using hBsbar.2 b b.2)) (ggGamma X hbar)
  have hscRed : GGTorusSelfCent 3 Ared := by
    dsimp only [Ared]
    exact ggTorusSelfCent_ggGamma hbar hSCbar
  have hcardAred : Nat.card Ared = 27 := by
    dsimp only [Ared]
    calc Nat.card (ggGamma X hbar).range
        = Nat.card (ggGamma J hN).range := hcardAred_eq.symm
      _ = 27 := GGResHyp.card_range_eq_twentyseven_of_rankFive_lineJDatum hH hD hMark27 hN
  have hφ1X : ∀ s, φ s ∈ X := by
    intro s
    rw [hXeq]
    exact hφ1 s
  let φX : ↥(unitarySU 2 1 F 6) →* ↥X := φ.codRestrict X hφ1X
  have hφXsurj : Function.Surjective φX := by
    intro z
    have hz : (z : RedGrp J) ∈ φ.range := by
      rw [hrange, ← hXeq]
      exact z.2
    obtain ⟨s, hs⟩ := MonoidHom.mem_range.mp hz
    exact ⟨s, Subtype.ext hs⟩
  by_cases hfr : ∃ P ∈ primeFormUnitary hU (idGram F 6), ∀ a ∈ Ab,
      ∃ (M : GL (Fin 6) F) (hM : M ∈ LargeEvenGUSet (Fin 6) F (2 ^ 1)),
        ((P⁻¹ * M * P : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F).IsDiag ∧
        a = TableB.projConj (unitarySU 2 1 F 6)
          ⟨M, TableBUE.gu_subset_normalizer hU hM⟩
  · obtain ⟨P, hP, hframe⟩ := hfr
    have hPgu : P ∈ LargeEvenGUSet (Fin 6) F (2 ^ 1) :=
      TableBUD.mem_guSet_of_mem_primeFormUnitary hU hP
    have hPN : P ∈ Subgroup.normalizer (unitarySU 2 1 F 6 : Set (GL (Fin 6) F)) :=
      TableBUE.gu_subset_normalizer hU hPgu
    have hPinv : P⁻¹ ∈ primeFormUnitary hU (idGram F 6) :=
      (primeFormUnitary hU (idGram F 6)).inv_mem hP
    let φP : ↥(unitarySU 2 1 F 6) →* ↥X :=
      φX.comp (TableBUE.conjSU hU P⁻¹ hPinv).toMonoidHom
    have hModelP : UnitTB.Model φP := by
      refine ⟨hU, hφXsurj.comp (TableBUE.conjSU hU P⁻¹ hPinv).surjective, ?_⟩
      intro g hg
      have hg' : φ (TableBUE.conjSU hU P⁻¹ hPinv g) = 1 := by
        simpa [φP, φX] using congrArg Subtype.val hg
      obtain ⟨c, hc⟩ := hφk (TableBUE.conjSU hU P⁻¹ hPinv g) hg'
      refine ⟨c, ?_⟩
      have hcoe := TableBUE.coe_conjSU hU P⁻¹ hPinv g
      have hgmat : (P : GL (Fin 6) F) * (g : GL (Fin 6) F) * (P : GL (Fin 6) F)⁻¹ =
          GeneralLinearGroup.scalar (Fin 6) c := by
        calc (P : GL (Fin 6) F) * (g : GL (Fin 6) F) * (P : GL (Fin 6) F)⁻¹
            = ((P⁻¹ : GL (Fin 6) F)⁻¹) * (g : GL (Fin 6) F) * (P⁻¹ : GL (Fin 6) F) := by
              group
          _ = ((TableBUE.conjSU hU P⁻¹ hPinv g : ↥(unitarySU 2 1 F 6)) :
                GL (Fin 6) F) := hcoe.symm
          _ = GeneralLinearGroup.scalar (Fin 6) c := hc
      have hgscal : (g : GL (Fin 6) F) = GeneralLinearGroup.scalar (Fin 6) c := by
        calc (g : GL (Fin 6) F)
            = (P : GL (Fin 6) F)⁻¹ *
                ((P : GL (Fin 6) F) * (g : GL (Fin 6) F) * (P : GL (Fin 6) F)⁻¹) *
                (P : GL (Fin 6) F) := by group
          _ = (P : GL (Fin 6) F)⁻¹ * GeneralLinearGroup.scalar (Fin 6) c *
                (P : GL (Fin 6) F) := by rw [hgmat]
          _ = GeneralLinearGroup.scalar (Fin 6) c := by
              rw [show (P : GL (Fin 6) F)⁻¹ * GeneralLinearGroup.scalar (Fin 6) c =
                GeneralLinearGroup.scalar (Fin 6) c * (P : GL (Fin 6) F)⁻¹ from
                  (commute_scalar c (P : GL (Fin 6) F)⁻¹).eq]
              group
      rw [hgscal, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply]
    have hdiagP : ∀ a ∈ Ared, ∃ t : Fin 6 → F, LineU.ActsDiagU φP a t := by
      rintro a ⟨bbar, rfl⟩
      obtain ⟨b, hb⟩ := MonoidHom.mem_range.mp bbar.2
      have hbbar : bbar = (⟨redMkB hN b, ⟨b, rfl⟩⟩ : Bsbar) := Subtype.ext hb.symm
      subst hbbar
      obtain ⟨M, hMgu, hMdiag, hMeq⟩ := hframe (ggBeta J θ hN b) ⟨b, rfl⟩
      have hprojEq : TableB.projConj (unitarySU 2 1 F 6) ⟨A b, hAN b⟩ =
          TableB.projConj (unitarySU 2 1 F 6)
            ⟨M, TableBUE.gu_subset_normalizer hU hMgu⟩ :=
        (hAproj b).trans hMeq
      obtain ⟨c, hc⟩ := CFSG.StandardType.Line63.H5.exists_scalar_mul_of_projConj_eq'
        hU h3n (hAN b) (TableBUE.gu_subset_normalizer hU hMgu) hprojEq
      let D : GL (Fin 6) F := P⁻¹ * A b * P
      have hDn : D ∈ Subgroup.normalizer (unitarySU 2 1 F 6 : Set (GL (Fin 6) F)) := by
        dsimp only [D]
        exact Subgroup.mul_mem _
          (Subgroup.mul_mem _ (Subgroup.inv_mem _ hPN) (hAN b)) hPN
      have hAdiag : ((D : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F).IsDiag := by
        have hgroup : D = GeneralLinearGroup.scalar (Fin 6) c * (P⁻¹ * M * P) := by
          dsimp only [D]
          rw [hc]
          calc (P : GL (Fin 6) F)⁻¹ *
                (GeneralLinearGroup.scalar (Fin 6) c * M) * (P : GL (Fin 6) F)
              = ((P : GL (Fin 6) F)⁻¹ * GeneralLinearGroup.scalar (Fin 6) c) * M *
                  (P : GL (Fin 6) F) := by group
            _ = (GeneralLinearGroup.scalar (Fin 6) c * (P : GL (Fin 6) F)⁻¹) * M *
                  (P : GL (Fin 6) F) := by
                rw [(commute_scalar c (P : GL (Fin 6) F)⁻¹).eq]
            _ = GeneralLinearGroup.scalar (Fin 6) c *
                  ((P : GL (Fin 6) F)⁻¹ * M * (P : GL (Fin 6) F)) := by group
        have hmat : ((D : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) =
            (c : F) • (((P⁻¹ * M * P : GL (Fin 6) F)) : Matrix (Fin 6) (Fin 6) F) := by
          simp only [hgroup, Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar,
            Matrix.scalar_apply, ← Matrix.smul_eq_diagonal_mul]
        rw [hmat]
        exact hMdiag.smul (c : F)
      let t : Fin 6 → F := fun i => ((D : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) i i
      have hDt : ((D : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) = diagonal t :=
        hAdiag.diagonal_diag.symm
      refine ⟨t, D, hDn, hDt, ?_⟩
      intro s
      apply Subtype.ext
      change ((ggGamma X hbar (⟨redMkB hN b, ⟨b, rfl⟩⟩ : Bsbar)) (φP s) : RedGrp J) =
        (φP (LineU.conjN D hDn s) : RedGrp J)
      rw [ggGamma_coe]
      have h1 : (redMkB hN b) * (φP s : RedGrp J) * (redMkB hN b)⁻¹ =
          (φ (LineU.conjN (A b) (hANu b)
            (TableBUE.conjSU hU P⁻¹ hPinv s)) : RedGrp J) := by
        simpa [φP, φX] using hActsEq b (TableBUE.conjSU hU P⁻¹ hPinv s)
      rw [h1]
      have harg : LineU.conjN (A b) (hANu b)
            (TableBUE.conjSU hU P⁻¹ hPinv s) =
          TableBUE.conjSU hU P⁻¹ hPinv (LineU.conjN D hDn s) := by
        apply Subtype.ext
        simp only [TableBUE.coe_conjSU, LineU.coe_conjN, D]
        group
      rw [harg]
      rfl
    exact false_of_diagonal_frame_card_twentyseven hModelP hFcard h3n hAred hscRed hdiagP hcardAred
  · have hnofr : ¬ ∃ P ∈ primeFormUnitary hU (idGram F 6), ∀ a ∈ Ab,
        ∃ (M : GL (Fin 6) F) (hM : M ∈ LargeEvenGUSet (Fin 6) F (2 ^ 1)),
          ((P⁻¹ * M * P : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F).IsDiag ∧
          a = TableB.projConj (unitarySU 2 1 F 6)
            ⟨M, TableBUE.gu_subset_normalizer hU hM⟩ := hfr
    have hcard27 : 3 ^ 3 ≤ Nat.card Ab := by rw [hcardAb]; norm_num
    let eB : ↥Bs ≃* ↥Bsbar := MonoidHom.ofInjective (redMkB_injective hN hBs)
    let Abar : ↥Bsbar → GL (Fin 6) F := fun bbar => A (eB.symm bbar)
    have hAbarN : ∀ bbar, Abar bbar ∈ Subgroup.normalizer
        (unitarySU 2 1 F 6 : Set (GL (Fin 6) F)) := fun bbar => hAN (eB.symm bbar)
    have hAbarProj : ∀ bbar, TableB.projConj (unitarySU 2 1 F 6)
        ⟨Abar bbar, hAbarN bbar⟩ = ggBeta J θ hN (eB.symm bbar) :=
      fun bbar => hAproj (eB.symm bbar)
    have hAAbar : ∀ bbar, TableB.projConj (unitarySU 2 1 F 6)
        ⟨Abar bbar, hAbarN bbar⟩ ∈ Ab := fun bbar => hAA (eB.symm bbar)
    have hAbarActs : ∀ (bbar : ↥Bsbar) (g : ↥(unitarySU 2 1 F 6)),
        (bbar : RedGrp J) * (φX g : RedGrp J) * (bbar : RedGrp J)⁻¹ =
          (φX (LineU.conjN (Abar bbar) (hAbarN bbar) g) : RedGrp J) := by
      intro bbar g
      have hb : (redMkB hN (eB.symm bbar) : RedGrp J) = (bbar : RedGrp J) :=
        congrArg Subtype.val (eB.apply_symm_apply bbar)
      rw [← hb]
      simpa [φX] using hActsEq (eB.symm bbar) g
    have hφXker : ∀ g : ↥(unitarySU 2 1 F 6), φX g = 1 → ∃ c : Fˣ,
        (g : GL (Fin 6) F) = GeneralLinearGroup.scalar (Fin 6) c := by
      intro g hg
      exact hφk g (by simpa [φX] using congrArg Subtype.val hg)
    rcases TableBU63.fieldType_or_heis hU hFcard h3n hAb hAbI hcard27 hnofr with
      ⟨M, hMN, l, hMu, hM3, hl, hMA⟩ |
      ⟨x, y, z, hxN, hyN, hzN, ζ, hxu, hyu, hzu, hxA, hyA, hzA,
        hx3, hz3, hζ3, hζ1, hxy, hxz, hyz, hzs⟩
    · obtain ⟨X0, Z, hXN, hZN, ζ, hXu, hZu, hXA, hZA, hX3, hZ3, hζ, hXM, hXZ, hMZ, hZs⟩ :=
        UnitSixThreeKG.exists_fieldStruct hU hFcard h3n hAb hAbI hcardAb hMN hMu hM3 hl hMA
      have hYreal : ∃ bbar : ↥Bsbar, TableB.projConj (unitarySU 2 1 F 6)
          ⟨Abar bbar, hAbarN bbar⟩ = TableB.projConj (unitarySU 2 1 F 6) ⟨M, hMN⟩ := by
        obtain ⟨b, hb⟩ := hMA
        refine ⟨eB b, ?_⟩
        have hsymm : eB.symm (eB b) = b := eB.symm_apply_apply b
        have hsub : (⟨Abar (eB b), hAbarN (eB b)⟩ :
            ↥(Subgroup.normalizer (unitarySU 2 1 F 6 : Set (GL (Fin 6) F)))) =
            ⟨A b, hANu b⟩ := by
          apply Subtype.ext
          dsimp only [Abar]
          rw [hsymm]
        rw [hsub]
        exact (hAproj b).trans hb
      exact (UnitSixThreeKG.not_noTransvection_of_actual_triple hU h3n hBsbar hSCbar φX hφXker
        Abar hAbarN (fun bbar => LineU.conjN (Abar bbar) (hAbarN bbar))
        (fun bbar g => LineU.coe_conjN (Abar bbar) (hAbarN bbar) g)
        hAbarActs hXN hMN hZN hXu hMu hZu hζ hX3 hZ3 hXM hXZ hMZ hZs hcardAb
        hXA hMA hZA hAAbar hYreal) hNoTrbar
    · have hζ : IsPrimitiveRoot ζ 3 :=
        IsPrimitiveRoot.iff_orderOf.mpr (orderOf_eq_prime hζ3 hζ1)
      have hYreal : ∃ bbar : ↥Bsbar, TableB.projConj (unitarySU 2 1 F 6)
          ⟨Abar bbar, hAbarN bbar⟩ = TableB.projConj (unitarySU 2 1 F 6) ⟨y, hyN⟩ := by
        obtain ⟨b, hb⟩ := hyA
        refine ⟨eB b, ?_⟩
        have hsymm : eB.symm (eB b) = b := eB.symm_apply_apply b
        have hsub : (⟨Abar (eB b), hAbarN (eB b)⟩ :
            ↥(Subgroup.normalizer (unitarySU 2 1 F 6 : Set (GL (Fin 6) F)))) =
            ⟨A b, hANu b⟩ := by
          apply Subtype.ext
          dsimp only [Abar]
          rw [hsymm]
        rw [hsub]
        exact (hAproj b).trans hb
      exact (UnitSixThreeKG.not_noTransvection_of_actual_triple hU h3n hBsbar hSCbar φX hφXker
        Abar hAbarN (fun bbar => LineU.conjN (Abar bbar) (hAbarN bbar))
        (fun bbar g => LineU.coe_conjN (Abar bbar) (hAbarN bbar) g)
        hAbarActs hxN hyN hzN hxu hyu hzu hζ hx3 hz3 hxy hxz hyz hzs hcardAb
        hxA hyA hzA hAAbar hYreal) hNoTrbar

theorem GGResHyp.false_of_compatible_unitary_marking_rank_ge_three_of_card_le_eight
    {G : Type} [Group G] [Finite G]
    {B Bs L D J K : Subgroup G} {x y : G}
    (hH : GGResHyp 3 B Bs x L D J y K)
    {T : GGResLineJType} (hD : GGResLineJDatum 3 Bs J T)
    (hMark : GGInnerDiagOnLabel
      (fun _ lab => lab.tag = .twA ∧ 3 ∣ 2 ^ lab.n + 1 ∧ 3 ≤ lab.rank) 3 Bs J)
    (hsmall : Nat.card (ggAutomizer J Bs) ≤ 8) : False := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hperfJ, lab, hΛ, hraw⟩ := hMark
  obtain ⟨tag, r, n⟩ := lab
  have hn : 1 ≤ n := hΛ.1
  obtain ⟨R0, _, I0, F0, hQ0⟩ := largeEvenRawDatum_exists hraw
  obtain ⟨_hsimple0, _hnonab0, _θ0, hP0⟩ := hQ0
  obtain ⟨hS0, _hN0raw, _hBsI0⟩ := hP0
  have htag : tag = .twA := hS0.1
  have hpq : 3 ∣ 2 ^ n + 1 := hS0.2.1
  have hr3 : 3 ≤ r := hS0.2.2
  subst htag
  by_cases hr5 : r = 5
  · subst r
    by_cases hn1 : n = 1
    · have hMarkEq : GGInnerDiagOnLabel
          (fun _ lab => lab = ⟨.twA, 5, 1⟩) 3 Bs J := by
        refine ⟨hperfJ, ⟨.twA, 5, n⟩, hΛ,
          largeEvenRawDatum_mono (lab := ⟨.twA, 5, n⟩) ?_ hraw⟩
        rintro R _ I F ⟨hs, hna, θ, hP⟩
        obtain ⟨hS, hN', hBsI⟩ := hP
        obtain ⟨htag', -, -⟩ := hS
        exact ⟨hs, hna, θ, ⟨by
          simp only [LargeEvenLabel.mk.injEq]
          exact ⟨trivial, trivial, hn1⟩, hN', hBsI⟩⟩
      exact (GGResHyp.false_of_rankFive_lineJDatum_q_eq_two hH hD hMarkEq).elim
    · have hMarkGt : GGInnerDiagOnLabel
          (fun _ lab => lab.tag = .twA ∧ lab.rank = 5 ∧
            3 ∣ 2 ^ lab.n + 1 ∧ lab.n ≠ 1) 3 Bs J := by
        refine ⟨hperfJ, ⟨.twA, 5, n⟩, hΛ,
          largeEvenRawDatum_mono (lab := ⟨.twA, 5, n⟩) ?_ hraw⟩
        rintro R _ I F ⟨hs, hna, θ, hP⟩
        obtain ⟨hS, hN', hBsI⟩ := hP
        obtain ⟨htag', hdiv', -⟩ := hS
        exact ⟨hs, hna, θ, ⟨⟨htag', rfl, hdiv', hn1⟩, hN', hBsI⟩⟩
      exact (GGResHyp.false_of_rankFive_lineJDatum_q_gt_two hH hD hMarkGt).elim
  have hraw0 := hraw
  dsimp only [LargeEvenRawDatum] at hraw
  obtain ⟨F, hFfield, hFfinite, hFcard, hQ⟩ := hraw
  letI : Field F := hFfield
  letI : Finite F := hFfinite
  obtain ⟨_hsimple, _hnonab, θ, hP⟩ := hQ
  obtain ⟨hS, hN, hBsI⟩ := hP
  let d : ℕ := r + 1
  have hd3 : 3 ≤ d := by dsimp [d]; omega
  let R : Type := LargeEvenProj (LargeEvenSUGroup (Fin d) F (2 ^ n))
  let I : Set (MulAut R) :=
    LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin d) F (2 ^ n)))
      (LargeEvenGUSet (Fin d) F (2 ^ n))
  let hN0 : Bs ≤ Subgroup.normalizer (J : Set G) :=
    GGResHyp.Bs_le_normalizer_J hH
  have hgamma : ggGamma J hN = ggGamma J hN0 := by
    ext b
    rfl
  let A : Subgroup (MulAut ↥J) := (ggGamma J hN0).range
  have hψ : Function.Surjective (ggQuotHom θ) := ggQuotHom_surjective θ
  have hker : (ggQuotHom θ).ker ≤ Subgroup.center ↥J := by
    rw [ker_ggQuotHom θ]
  have hAe : IsElemAbelian 3 A := by
    dsimp [A]
    exact isElemAbelian_range
      (fun a b : ↥Bs => (@IsMulCommutative.is_comm ↥Bs _ hH.1.2.1.2.1.1).comm a b)
      (fun b : ↥Bs => Subtype.ext (by simpa using hH.1.2.1.2.1.2 b b.2))
      (ggGamma J hN0)
  have hAI : ∀ a ∈ A, ∃ φ ∈ I, ∀ l : ↥J,
      φ (ggQuotHom θ l) = ggQuotHom θ (a l) := by
    rintro a ⟨b, rfl⟩
    refine ⟨ggBeta J θ hN b, ggBeta_mem J θ hN hBsI b, fun l => ?_⟩
    rw [ggBeta_ggQuotHom J hN θ b l, hgamma]
  have hsc : GGTorusSelfCent 3 A := by
    simpa [A, hgamma] using GGResHyp.gamma_J_selfCent hH
  by_cases hr3eq : r = 3
  · subst r
    have hodd : Odd (2 ^ n + 1) := by
      have hnpos : 0 < n := by
        rcases Nat.eq_zero_or_pos n with rfl | h
        · norm_num at hpq
        · exact h
      exact (Nat.even_pow.mpr ⟨even_two, Nat.ne_of_gt hnpos⟩).add_one
    have hcop : Nat.Coprime 4 (2 ^ n + 1) := by
      rw [show 4 = 2 ^ 2 by norm_num]
      exact (Nat.coprime_pow_left_iff (by norm_num : 0 < 2) 2 (2 ^ n + 1)).2
        (Nat.coprime_two_left.mpr hodd)
    have hTor := ggTorusTorW_unitary_liftTwo_weak
      (K := F) (n := n) (p := 3) (N := 3)
      hFcard hn (by norm_num) (by norm_num) hpq hcop
      hψ hker hperfJ hAe hAI hsc
    have h24 : Nat.card (ggAutomizer J Bs) = 24 := by
      have h := card_ggAutomizer_eq_factorial_of_unitaryTorusData
        (hBs := hH.1.2.1.2.1) (hSC := hH.1.2.1.2.2.2) (hN := hN0) hpq hTor
      rw [show Nat.factorial 4 = 24 by norm_num] at h
      exact h
    omega
  · have hr4 : 4 ≤ r := by omega
    by_cases hpd : 3 ∣ r + 1
    · have hr8 : 8 ≤ r := by
        obtain ⟨k, hk⟩ := hpd
        have hk2 : 2 ≤ k := by omega
        have hkne : k ≠ 2 := by
          intro hk2eq
          exact hr5 (by omega)
        have hk3 : 3 ≤ k := by omega
        omega
      have hdq : (d, 2 ^ n) ≠ (3, 2) := by
        intro heq
        have := congrArg Prod.fst heq
        dsimp [d] at this
        omega
      have hT : GGTorusLift 3 (r - 2) R := by
        have h := ggTorusLift_unitary (K := F) (n := n) (d := d) (p := 3)
          hFcard hn hd3 hdq (by norm_num) hpq
        simpa [R, d, ggUnitaryTorusRank, hpd] using h
      have hpow : 3 ^ (r - 2) ≤ Nat.card A := by
        simpa [A, hgamma] using
          GGResHyp.pow_le_card_range_gamma_J_of_torusLift hH θ hT
      have hTB : GGTorusTBGroup 3 (r - 2) R I ↥J (ggQuotHom θ) A := by
        refine ⟨hψ, hker, hperfJ, hAe, hAI, ?_, ?_, hsc⟩
        · exact hpow
        · exact (Nat.pow_le_pow_right (by norm_num) (by omega : 3 ≤ r - 2)).trans hpow
      have hTorW := ggTorusTorW_unitary LineU.unitaryUniversalCover_holds
        (K := F) (n := n) (p := 3) (N := r)
        hFcard (by omega) hr4 (by norm_num) hpq hpd (by
          rintro ⟨h6, -⟩
          exact hr5 (by omega))
      have hTor := hTorW ↥J (ggQuotHom θ) A hTB
      have hfac : Nat.card (ggAutomizer J Bs) = (r + 1).factorial :=
        card_ggAutomizer_eq_factorial_of_unitaryTorusData
          (hBs := hH.1.2.1.2.1) (hSC := hH.1.2.1.2.2.2) (hN := hN0) hpq hTor
      have hge : 24 ≤ (r + 1).factorial := by
        rw [show (24 : ℕ) = Nat.factorial 4 by norm_num]
        exact Nat.factorial_le (by omega)
      omega
    · have hU : LineU.UnitaryCoverAt n (r + 1) F :=
        LineU.unitaryUniversalCover_holds n (r + 1) F hFcard (by omega) (by
          intro h6
          have h6' : r + 1 = 6 := congrArg Prod.fst h6
          exact hpd (by rw [h6']; norm_num))
      have hTor := ggTorusTorW_unitary_coprime_weak
        (K := F) (n := n) (p := 3) (N := r)
        hFcard hn (by omega) (by norm_num) hpq hpd hU
        hψ hker hperfJ hAe hAI hsc
      have hfac : Nat.card (ggAutomizer J Bs) = (r + 1).factorial :=
        card_ggAutomizer_eq_factorial_of_unitaryTorusData
          (hBs := hH.1.2.1.2.1) (hSC := hH.1.2.1.2.2.2) (hN := hN0) hpq hTor
      have hge : 24 ≤ (r + 1).factorial := by
        rw [show (24 : ℕ) = Nat.factorial 4 by norm_num]
        exact Nat.factorial_le (by omega)
      omega

theorem GGResHyp.exists_A2_label_of_compatible_unitary_marking
    {G : Type} [Group G] [Finite G]
    {B Bs L D J K : Subgroup G} {x y : G}
    (hH : GGResHyp 3 B Bs x L D J y K)
    (hD : GGResLineJDatum 3 Bs J .A2)
    (hMark : GGInnerDiagOnLabel
      (fun _ lab => lab.tag = .twA ∧ 3 ∣ 2 ^ lab.n + 1) 3 Bs J) :
    ∃ lab : LargeEvenLabel, LargeEvenInLambda2 lab ∧ ggResLineJLabel .A2 lab ∧
      GGHasLabel lab (J ⧸ Subgroup.center J) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hperfJ, lab, hΛ, hraw⟩ := hMark
  obtain ⟨tag, r, n⟩ := lab
  obtain ⟨R0, _, I0, F0, hQ0⟩ := largeEvenRawDatum_exists hraw
  obtain ⟨_hsimple0, _hnonab0, _θ0, hP0⟩ := hQ0
  obtain ⟨hS0, _hN0raw, _hBsI0⟩ := hP0
  have htag : tag = .twA := hS0.1
  have hpq : 3 ∣ 2 ^ n + 1 := hS0.2
  subst htag
  have hraw0 := hraw
  have hr2le : 2 ≤ r := hΛ.2.1
  by_cases hr2 : r = 2
  · subst r
    refine ⟨⟨.twA, 2, n⟩, hΛ, Or.inr ⟨rfl, rfl, hpq⟩, ?_⟩
    unfold GGHasLabel
    refine largeEvenRawDatum_mono ?_ hraw0
    intro R' _ I' F' hQ'
    obtain ⟨-, -, θ', -⟩ := hQ'
    exact ⟨θ'⟩
  · have hr3 : 3 ≤ r := by omega
    have hcardA2 : Nat.card (ggAutomizer J Bs) = 6 :=
      ggAutomizer_card_of_lineJDatum_A2 (p := 3) rfl hD
    have hsmall : Nat.card (ggAutomizer J Bs) ≤ 8 := by omega
    have hMarkR3 : GGInnerDiagOnLabel
        (fun _ lab => lab.tag = .twA ∧ 3 ∣ 2 ^ lab.n + 1 ∧ 3 ≤ lab.rank) 3 Bs J := by
      refine ⟨hperfJ, ⟨.twA, r, n⟩, hΛ,
        largeEvenRawDatum_mono (lab := ⟨.twA, r, n⟩) ?_ hraw0⟩
      rintro R _ I F ⟨hs, hna, θ, hP⟩
      obtain ⟨hS, hN', hBsI⟩ := hP
      obtain ⟨htag', hpq'⟩ := hS
      exact ⟨hs, hna, θ, ⟨htag', hpq', by omega⟩, hN', hBsI⟩
    exact (GGResHyp.false_of_compatible_unitary_marking_rank_ge_three_of_card_le_eight
      hH hD hMarkR3 hsmall).elim

end CFSG.StandardType

end
