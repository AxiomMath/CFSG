module

public import CFSG.RankThree.PartTwo.Sec15.Gagen155W315xFacts
import CFSG.RankThree.PartTwo.Sec15.Gagen155W315PGroup
import CFSG.RankThree.PartTwo.Sec15.Gagen155W315PBasic
import CFSG.RankThree.PartTwo.Sec15.Gagen155W315PGroupJ
import CFSG.RankThree.PartTwo.Sec15.Gagen155W315PImg
import CFSG.RankThree.PartTwo.Sec15.Item15Res8ProofProd
import CFSG.RankThree.PartTwo.Sec15.Gagen155INorm
import CFSG.RankThree.PartTwo.Sec15.Read148PerfProof
import CFSG.RankThree.PartTwo.Sec14.Item148MainProofKType
import CFSG.RankThree.PartTwo.Sec19.Step1914Tri
import CFSG.RankThree.PartTwo.Sec17.Item17Q0ProofTools
import CFSG.RankThree.PartTwo.Sec15.Sylow155Center
import CFSG.GroupTheory.ElementaryAbelianTransport
import CFSG.GroupTheory.PRankQuotientLift
public import CFSG.RankThree.PartTwo.Sec14.Item148StepOne
public import CFSG.RankThree.PartTwo.Sec15.Item153Twin3ProofNorm

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace Ronan155W315

open Proof155P

theorem data148_of_not_le
    {A L : Subgroup G} {c : G} (h : Sec14Std G A c L) (h148 : Item148 A (lB A))
    {X Y M P : Subgroup G} (hf : Proof155Wx.Facts155W A X Y M P) (hX : X ∈ thetaComponentsIn M)
    (hWO : ¬ w155 A M X ≤ pPrimeCoreOf 3 M) :
    ∃ (c₀ d₀ : G) (L₀ : Subgroup G), Subgroup.zpowers c₀ ∈ omegaA A ∧ L₀ ∈ lA A c₀ ∧
      Nonempty (↥L₀ ⧸ aschbacherSolvableCore 3 ↥L₀ ≃* CFSG.Blueprint.NativeSporadic.J2) ∧
      d₀ ∈ A ∧ d₀ ≠ 1 ∧ IsThreeCentralIn L₀ d₀ ∧
      (∀ y ∈ deltaZero A (lB A) M, ⁅y, d₀⁆ ∈ pPrimeCoreOf 3 M) ∧
      (Nonempty (↥X ⧸ aschbacherSolvableCore 3 ↥X ≃* alternatingGroup (Fin 5)) ∨
        (Sec4.IsTripleCover (↥X ⧸ aschbacherSolvableCore 3 ↥X) (alternatingGroup (Fin 6)) ∧
          Group.IsPerfect (↥X ⧸ aschbacherSolvableCore 3 ↥X))) ∧
      X ⊓ pPrimeCoreOf 3 M ≤ inSubgroup (aschbacherSolvableCore 3) X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  letI : (ker148 A M).Normal := ker148_normal hf.mem_m2.1.2
  set W := w155 A M X with hWdef
  set D := img148 A M (deltaZero A (lB A) M) with hDdef
  have hWΔ : W ≤ deltaZero A (lB A) M := hf.w_le_i0.trans hf.i0_le_deltaZero
  have hXΔ : X ≤ deltaZero A (lB A) M := hf.le_x_i0.trans hf.i0_le_deltaZero
  have hWM : W ≤ M := hWΔ.trans (deltaZero_le M)
  have hAM : A ≤ M := hf.le_am
  have hXMA : X ≤ M ⊔ A := hf.le_xm.trans le_sup_left
  have hWMA : W ≤ M ⊔ A := hWM.trans le_sup_left
  have hΔMA : deltaZero A (lB A) M ≤ M ⊔ A := (deltaZero_le M).trans le_sup_left
  set V := (img148 A M X).subgroupOf D with hVdef
  set E := (img148 A M W).subgroupOf D with hEdef
  have hEimg : img148 A M W ≤ D := by rw [hDdef]; exact img148_mono hWΔ
  have hVimg : img148 A M X ≤ D := by rw [hDdef]; exact img148_mono hXΔ
  have hVsub : V.IsSubnormal := by
    rw [hVdef, hDdef]
    exact Proof153Twin3.isSubnormal_img_subgroupOf hAM hX
  obtain ⟨eX⟩ := Proof155INorm.nonempty_quot_equiv_img (A := A) (M := M)
    (D := deltaZero A (lB A) M) hAM hX hXΔ
  have hVq : CFSG.IsQuasisimple ↥V :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv eX (Proof1515.isQuasisimple_quot_pPrimeCore hf.mem_x4)
  have hVne : V ≠ ⊥ :=
    (Subgroup.nontrivial_iff_ne_bot V).mp (CFSG.LocalCores.isQuasisimple_nontrivial hVq)
  have hEperf : Group.IsPerfect ↥E := by
    rw [hEdef]
    haveI : Group.IsPerfect ↥(img148 A M W) := by
      haveI : Group.IsPerfect W := Proof155Wx.isPerfect_w155 A M X
      exact isPerfect_img148 (A := A) (Y := M) (J := W) hWMA
    exact Group.IsPerfect.ofSurjective
      (f := (Subgroup.subgroupOfEquivOfLe hEimg).symm.toMonoidHom) (MulEquiv.surjective _)
  have hWne : img148 A M W ≠ ⊥ := img148_ne_bot_of_not_le hWM hWO
  have hEne : E ≠ ⊥ := by
    rw [hEdef]
    intro hbot
    apply hWne
    have h1 := congrArg (Subgroup.map D.subtype) hbot
    rwa [Subgroup.map_subgroupOf_eq_of_le hEimg, Subgroup.map_bot] at h1
  have hEsub : E.IsSubnormal := by
    rw [hEdef]
    have hMA : M = M ⊔ A := (sup_eq_left.mpr hAM).symm
    have h2 : (W.subgroupOf (M ⊔ A)).IsSubnormal := by
      rw [← hMA]
      exact CFSG.Open.IsSubnormal.subgroupOf hf.subnormal_w_m
    have h3 : (img148 A M W).IsSubnormal := by
      have h1 := Subgroup.IsSubnormal.map (QuotientGroup.mk'_surjective (ker148 A M)) h2
      simpa [img148] using h1
    exact h3.subgroupOf
  have hcomm : ⁅X, W⁆ ≤ pPrimeCoreOf 3 M := by
    rw [hWdef, Subgroup.commutator_comm]
    exact (commutator_w155_le hf hX).trans
      (CFSG.RankThree.PartTwo.Sec17.Proof17Q0.pCoreOf_le_pPrimeCoreOf M)
  have hVE : ⁅V, E⁆ = ⊥ := by
    rw [hVdef, hEdef, hDdef]
    exact Proof153Twin3.commutator_img_subgroupOf_eq_bot (D := deltaZero A (lB A) M)
      hXΔ hWΔ hΔMA hcomm
  have hsimp : ∀ {S : Type} [Group S] [IsSimpleGroup S], (↥D ≃* S) → False := by
    intro S _ _ e
    exact hEne (eq_bot_of_cover (ψ := MonoidHom.id S) Function.surjective_id
      (by rw [MonoidHom.ker_id]; exact bot_le) (φ := e.symm.toMonoidHom) e.symm.surjective
      hVsub hVq hEperf hVE)
  have hquasi : ∀ {S : Type} [Group S], CFSG.IsQuasisimple S → (↥D ≃* S) → False := by
    intro S _ hS e
    obtain ⟨-, hsimple, -⟩ := hS
    letI : IsSimpleGroup (S ⧸ Subgroup.center S) := hsimple
    exact hEne (eq_bot_of_cover (ψ := QuotientGroup.mk' (Subgroup.center S))
      (QuotientGroup.mk'_surjective _) (by rw [QuotientGroup.ker_mk'])
      (φ := e.symm.toMonoidHom) e.symm.surjective hVsub hVq hEperf hVE)
  have htriple : ∀ {S : Type} [Group S] [IsSimpleGroup S], Sec4.IsTripleCover ↥D S → False := by
    intro S _ _ htc
    obtain ⟨-, ⟨ε⟩⟩ := htc
    obtain ⟨hψ, hk⟩ := Proof153Twin2.tripleCover_cover ε
    exact hEne (eq_bot_of_cover hψ hk (φ := MonoidHom.id ↥D) Function.surjective_id hVsub hVq
      hEperf hVE)
  haveI hA5s : IsSimpleGroup (alternatingGroup (Fin 5)) :=
    alternatingGroup.isSimpleGroup (by simp)
  haveI hA6s : IsSimpleGroup (alternatingGroup (Fin 6)) :=
    alternatingGroup.isSimpleGroup (by simp)
  haveI hA7s : IsSimpleGroup (alternatingGroup (Fin 7)) :=
    alternatingGroup.isSimpleGroup (by simp)
  haveI hA10s : IsSimpleGroup (alternatingGroup (Fin 10)) :=
    alternatingGroup.isSimpleGroup (by simp)
  haveI hONs : IsSimpleGroup CFSG.Blueprint.NativeSporadic.ON :=
    CFSG.Sporadic.ON.isSimpleGroup_ON
  rcases (h148 M hf.mem_m2.1).2 with h1 | h2 | h3 | h4 | h5 | h6 | h7'
  ·
    exfalso
    have hD : img148 A M (deltaZero A (lB A) M) = ⊥ := img148_eq_bot_of_le h1
    haveI hsub : Subsingleton ↥(img148 A M (deltaZero A (lB A) M)) := by
      rw [hD]
      exact inferInstance
    have hVbot : V = ⊥ := by
      rw [eq_bot_iff]
      intro x _
      rw [show x = 1 from Subsingleton.elim x 1]
      exact Subgroup.one_mem ⊥
    exact hVne hVbot
  ·
    exfalso
    obtain ⟨c', hc', hdec, hL'⟩ := h2
    obtain ⟨L', hL', hcases⟩ := hL'
    rcases hcases with ⟨⟨φ⟩⟩ | ⟨-, ⟨φ⟩⟩ | ⟨p, f, e', hp, hf', -, -, hε⟩ | ⟨-, h6 | ⟨⟨φ⟩⟩⟩
    · exact hquasi (Sec6.isQuasisimple_of_mem_thetaComponentsAt hL'.1) φ
    · exact hsimp φ
    · haveI : Fact p.Prime := hp
      rcases hε with ⟨⟨φ⟩⟩ | ⟨h2q, ⟨φ⟩⟩
      · haveI : IsSimpleGroup
            (CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField p f)) :=
          Sec19.Step1914TriProof.isSimpleGroup_projSL_three_of_field _
        exact hsimp φ
      · haveI : IsSimpleGroup (CFSG.Assembly.RankThreeEven.projSU 3 p f) :=
          Sec19.Step1914TriProof.isSimpleGroup_projSU_three_of_ne_two p f hf' (by omega)
        exact hsimp φ
    · exact htriple h6
    · exact hsimp φ
  ·
    obtain ⟨c₀, d₀, L₀, hc₀, hL₀, hJ₀, hd₀A, hd₀1, hd₀c, hdecomp, htypes⟩ := h3
    have hT : IsCentralProductA6Covers ↥D ∨ IsA6CoverTimesA5 ↥D ∨
        Nonempty (↥D ≃* alternatingGroup (Fin 5) × alternatingGroup (Fin 5)) := by
      rcases htypes with hON | hCP | hCTA | ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩ | ⟨hp7, ⟨φ⟩⟩
      · exact (htriple hON).elim
      · exact Or.inl hCP
      · exact Or.inr (Or.inl hCTA)
      · exact Or.inr (Or.inr ⟨φ⟩)
      · exact (hsimp φ).elim
      · haveI : Fact (Nat.Prime 7) := hp7
        haveI : IsSimpleGroup
            (CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 7 1)) :=
          Sec19.Step1914TriProof.isSimpleGroup_projSL_three_of_field _
        exact (hsimp φ).elim
    haveI : Group.IsPerfect ↥D := by
      rw [hDdef]
      exact Read148Perf.isPerfect_img148 h h148 hf.mem_m2.1
    have hrank : ∀ F : Subgroup ↥D, CFSG.Assembly.IsElemAbelian 3 F → Nat.card F ≤ 27 := by
      intro F hF
      have hF' : CFSG.Assembly.IsElemAbelian 3 (F.map D.subtype) :=
        CFSG.Open.IsElemAbelian.map hF D.subtype
      have h1 := Proof15Res8Prod.card_le_of_isElemAbelian_img148 (A := A) (M := M) h
        hf.mem_m2.1.2 hf.mem_m2.2 hF'
      rwa [Subgroup.card_map_of_injective D.subtype_injective] at h1
    obtain ⟨-, hEtype, hNtriv⟩ := prod148_facts hrank hT hVsub hVq hEsub hEperf hEne hVE
    have hEq : CFSG.IsQuasisimple ↥E := (type155_facts hEtype).1
    have hEV : ⁅E, V⁆ = ⊥ := by rw [Subgroup.commutator_comm]; exact hVE
    obtain ⟨-, hVtype, -⟩ := prod148_facts hrank hT hEsub hEq hVsub hVq.1 hVne hEV
    have hXq : CFSG.IsQuasisimple (↥X ⧸ aschbacherSolvableCore 3 ↥X) :=
      isQuasisimple_theta_of_mem_thetaComponentsIn hX
    obtain ⟨-, hθc, hθ3, -, -, -, -⟩ :=
      solvable_prime_complement_core_characterization (H := ↥X) Nat.prime_three
    have : (aschbacherSolvableCore 3 ↥X).Characteristic := hθc
    have hθO : aschbacherSolvableCore 3 ↥X ≤ CFSG.pPrimeCore 3 ↥X :=
      le_sSup ⟨inferInstance, (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hθ3⟩
    have h3V : 3 ∣ Nat.card V := (type155_facts hVtype).2.1
    have h3X : 3 ∣ Nat.card (↥X ⧸ aschbacherSolvableCore 3 ↥X) := by
      have h1 : 3 ∣ (CFSG.pPrimeCore 3 ↥X).index := by
        rw [Subgroup.index, Nat.card_congr eX.toEquiv]
        exact h3V
      exact h1.trans (Subgroup.index_dvd_of_le hθO)
    have hXθ : aschbacherSolvableCore 3 ↥X = CFSG.pPrimeCore 3 ↥X :=
      Sylow155T.aschbacherSolvableCore_eq_pPrimeCore hXq h3X
    have eXθ : ↥X ⧸ aschbacherSolvableCore 3 ↥X ≃* ↥V :=
      (QuotientGroup.quotientMulEquivOfEq hXθ).trans eX
    refine ⟨c₀, d₀, L₀, hc₀, hL₀, hJ₀, hd₀A, hd₀1, hd₀c, ?_, ?_, ?_⟩
    ·
      exact commutator_mem_of_dec (LB := lB A) hdecomp
        (pPrimeCoreOf_deltaZero_le (LB := lB A) hNtriv)
        (le_normalizer_pPrimeCoreOf 3 M (hAM hd₀A))
    ·
      rcases hVtype with hV5 | hV6
      · obtain ⟨φ⟩ := hV5
        exact Or.inl ⟨eXθ.trans φ⟩
      · obtain ⟨htc, -⟩ := hV6
        exact Or.inr ⟨Proof15Res8Diag.isTripleCover_congr eXθ.symm htc, hXq.1⟩
    ·
      obtain ⟨hNn, hN3, -⟩ := inf_pPrimeCoreOf_facts hf.le_xm
      have hN3' : Nat.Coprime 3 (Nat.card ((X ⊓ pPrimeCoreOf 3 M).subgroupOf X)) := by
        rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe
          (inf_le_left : X ⊓ pPrimeCoreOf 3 M ≤ X)).toEquiv]
        exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hN3
      have hle : (X ⊓ pPrimeCoreOf 3 M).subgroupOf X ≤ aschbacherSolvableCore 3 ↥X := by
        rw [hXθ]
        exact le_sSup ⟨hNn, hN3'⟩
      have h1 := Subgroup.map_mono (f := X.subtype) hle
      rwa [Subgroup.map_subgroupOf_eq_of_le (inf_le_left : X ⊓ pPrimeCoreOf 3 M ≤ X)] at h1
  ·
    exfalso
    obtain ⟨⟨φ⟩, -, -⟩ := h4
    exact hsimp φ
  ·
    exfalso
    obtain ⟨-, -, -, n, -, -, -, hn, -, hiso, -⟩ := h5
    rcases hiso with ⟨-, ⟨φ⟩⟩ | ⟨-, ⟨φ⟩⟩
    · haveI : IsSimpleGroup
          (CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 2 (3 * n))) :=
        Sec19.Step1914TriProof.isSimpleGroup_projSL_three_of_field _
      exact hsimp φ
    · have h2 : 2 ^ (3 * n) ≠ 2 := by
        intro h22
        have := Nat.pow_right_injective (le_refl 2) (h22.trans (pow_one 2).symm)
        omega
      haveI : IsSimpleGroup (CFSG.Assembly.RankThreeEven.projSU 3 2 (3 * n)) :=
        Sec19.Step1914TriProof.isSimpleGroup_projSU_three_of_ne_two 2 (3 * n) (by omega) h2
      exact hsimp φ
  ·
    exfalso
    obtain ⟨⟨eJ2⟩, -, -⟩ := h6
    have hcase := j2prod_facts (T := ↥D) eJ2 hVsub hVq hEsub hEperf hEne hVE
    have hcardE : Nat.card E = Nat.card (img148 A M W) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEimg).toEquiv
    have hcardV : Nat.card V = Nat.card (img148 A M X) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVimg).toEquiv
    rcases hcase with ⟨hVrank, h5E⟩ | ⟨h5V, hErank⟩
    ·
      have h5W : 5 ∣ Nat.card W :=
        (hcardE ▸ h5E).trans (Main148.card_img148_dvd hWMA)
      have hXle : CFSG.Open.pRank 5 X ≤ 1 := pRank_five_x_le_one h hf hX h5W
      have h2q : 2 ≤ CFSG.Open.pRank 5
          (⊤ : Subgroup (↥X ⧸ CFSG.pPrimeCore 3 ↥X)) := by
        rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num : 1 < 5) eX]
        exact hVrank
      have h2X : 2 ≤ CFSG.Open.pRank 5 X := by
        rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup X]
        exact CFSG.GroupTheory.two_le_pRank_of_quotient (CFSG.pPrimeCore 3 ↥X) (by norm_num)
          (by norm_num) h2q
      omega
    ·
      have h5X : 5 ∣ Nat.card X :=
        (hcardV ▸ h5V).trans (Main148.card_img148_dvd hXMA)
      have hWle : CFSG.Open.pRank 5 W ≤ 1 := pRank_five_w155_le_one h hf hX h5X
      have h2img : 2 ≤ CFSG.Open.pRank 5 (⊤ : Subgroup ↥(img148 A M W)) := by
        rw [← CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num : 1 < 5)
          (Subgroup.subgroupOfEquivOfLe hEimg)]
        exact hErank
      have h2W : 2 ≤ CFSG.Open.pRank 5 W := by
        rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup W]
        let f : ↥(W.subgroupOf (M ⊔ A)) →* ↥(img148 A M W) :=
          ((QuotientGroup.mk' (ker148 A M)).comp (W.subgroupOf (M ⊔ A)).subtype).codRestrict
            (img148 A M W) (fun x => Subgroup.mem_map.mpr ⟨x.1, x.2, rfl⟩)
        have hfsurj : Function.Surjective f := by
          intro y
          obtain ⟨s, hs, hsy⟩ := Subgroup.mem_map.mp y.2
          exact ⟨⟨s, hs⟩, Subtype.ext hsy⟩
        let g : ↥W →* ↥(img148 A M W) :=
          f.comp (Subgroup.subgroupOfEquivOfLe hWMA).symm.toMonoidHom
        have h2q : 2 ≤ CFSG.Open.pRank 5 (⊤ : Subgroup (↥W ⧸ g.ker)) := by
          rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num : 1 < 5)
            (QuotientGroup.quotientKerEquivOfSurjective g (hfsurj.comp (MulEquiv.surjective _)))]
          exact h2img
        exact CFSG.GroupTheory.two_le_pRank_of_quotient g.ker (by norm_num) (by norm_num) h2q
      omega
  ·
    exact (Proof15Res6.false_of_case148Seven_two h h148 hf.mem_m2 h7').elim

end Ronan155W315

end CFSG.RankThree.PartTwo.Sec15
