module

public import CFSG.RankThree.PartTwo.Sec15.Gagen155W315xFacts
import CFSG.RankThree.PartTwo.Sec15.Gagen155W315PGroup
import CFSG.RankThree.PartTwo.Sec15.Gagen155W315PBasic
import CFSG.RankThree.PartTwo.Sec15.Gagen155W315PGroupJ
import CFSG.RankThree.PartTwo.Sec15.Gagen155W315PImg
import CFSG.RankThree.PartTwo.Sec15.Item15Res6ProofComp
import CFSG.RankThree.PartTwo.Sec15.Gagen155INorm
import CFSG.RankThree.PartTwo.Sec15.Item1515StepsProofRead
import CFSG.RankThree.PartTwo.Sec14.Item148MainProofKType
import CFSG.RankThree.PartTwo.Sec17.Item17Q0ProofTools
import CFSG.RankThree.PartTwo.Sec19.Step1914Tri
import CFSG.GroupTheory.PRankQuotientLift
public import CFSG.RankThree.PartTwo.Sec14.Item148StepOne
public import CFSG.RankThree.PartTwo.Sec15.Item153Twin3ProofNorm

public section

namespace CFSG.RankThree.PartTwo.Sec15.Sylow155NO

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

private theorem eq_bot_of_cover_simple {T X : Type*} [Group T] [Group X] [IsSimpleGroup X]
    (e : T ≃* X) {V E : Subgroup T} (hV : V.IsSubnormal) (hVq : CFSG.IsQuasisimple ↥V)
    (hEp : Group.IsPerfect ↥E) (hVE : ⁅V, E⁆ = ⊥) : E = ⊥ :=
  Proof155P.eq_bot_of_cover (ψ := MonoidHom.id X) Function.surjective_id
    (by rw [MonoidHom.ker_id]; exact bot_le) (φ := e.symm.toMonoidHom) e.symm.surjective
    hV hVq hEp hVE

private theorem eq_bot_of_cover_quasisimple {T X : Type*} [Group T] [Group X]
    (hX : CFSG.IsQuasisimple X) (e : T ≃* X) {V E : Subgroup T} (hV : V.IsSubnormal)
    (hVq : CFSG.IsQuasisimple ↥V) (hEp : Group.IsPerfect ↥E) (hVE : ⁅V, E⁆ = ⊥) : E = ⊥ := by
  obtain ⟨-, hsimple, -⟩ := hX
  letI : IsSimpleGroup (X ⧸ Subgroup.center X) := hsimple
  exact Proof155P.eq_bot_of_cover (ψ := QuotientGroup.mk' (Subgroup.center X))
    (QuotientGroup.mk'_surjective _) (by rw [QuotientGroup.ker_mk'])
    (φ := e.symm.toMonoidHom) e.symm.surjective hV hVq hEp hVE

private theorem eq_bot_of_cover_triple {T S : Type*} [Group T] [Group S] [IsSimpleGroup S]
    (h : Sec4.IsTripleCover T S) {V E : Subgroup T} (hV : V.IsSubnormal)
    (hVq : CFSG.IsQuasisimple ↥V) (hEp : Group.IsPerfect ↥E) (hVE : ⁅V, E⁆ = ⊥) : E = ⊥ := by
  obtain ⟨-, ⟨ε⟩⟩ := h
  obtain ⟨hψ, hk⟩ := Proof153Twin2.tripleCover_cover ε
  exact Proof155P.eq_bot_of_cover hψ hk (φ := MonoidHom.id T) Function.surjective_id hV hVq hEp
    hVE

theorem case148Three_of_not_le
    {A L : Subgroup G} {c : G} (h : Sec14Std G A c L) (h148 : Item148 A (lB A))
    {X Y M P : Subgroup G} (hf : Proof155Wx.Facts155W A X Y M P) (hX : X ∈ thetaComponentsIn M)
    [(ker148 A M).Normal] (hWO : ¬ w155 A M X ≤ pPrimeCoreOf 3 M) :
    ∃ (c' e : G) (L' : Subgroup G), Subgroup.zpowers c' ∈ omegaA A ∧ L' ∈ lA A c' ∧
      Nonempty (↥L' ⧸ aschbacherSolvableCore 3 ↥L' ≃* CFSG.Blueprint.NativeSporadic.J2) ∧
      e ∈ A ∧ e ≠ 1 ∧ IsThreeCentralIn L' e ∧
      deltaZero A (lB A) M = pPrimeCoreOf 3 (deltaZero A (lB A) M) ⊔
        deltaZero A (lB A) (M ⊓ Subgroup.centralizer ({e} : Set G)) ∧
      (IsCentralProductA6Covers ↥(img148 A M (deltaZero A (lB A) M)) ∨
        IsA6CoverTimesA5 ↥(img148 A M (deltaZero A (lB A) M)) ∨
        Nonempty (↥(img148 A M (deltaZero A (lB A) M)) ≃*
          alternatingGroup (Fin 5) × alternatingGroup (Fin 5))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
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
  have hVsub : V.IsSubnormal := by
    rw [hVdef, hDdef]
    exact Proof153Twin3.isSubnormal_img_subgroupOf hAM hX
  obtain ⟨eX⟩ := Proof155INorm.nonempty_quot_equiv_img (A := A) (M := M)
    (D := deltaZero A (lB A) M) hAM hX hXΔ
  have hVq : CFSG.IsQuasisimple ↥V :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv eX (Proof1515.isQuasisimple_quot_pPrimeCore hf.mem_x4)
  have hEperf : Group.IsPerfect ↥E := by
    rw [hEdef]
    haveI : Group.IsPerfect ↥(img148 A M W) := by
      haveI : Group.IsPerfect W := Proof155Wx.isPerfect_w155 A M X
      exact isPerfect_img148 (A := A) (Y := M) (J := W) hWMA
    exact Group.IsPerfect.ofSurjective
      (f := (Subgroup.subgroupOfEquivOfLe hEimg).symm.toMonoidHom) (MulEquiv.surjective _)
  have hWne : img148 A M W ≠ ⊥ := Proof155P.img148_ne_bot_of_not_le hWM hWO
  have hEne : E ≠ ⊥ := by
    rw [hEdef]
    intro hbot
    apply hWne
    have h := congrArg (Subgroup.map D.subtype) hbot
    rwa [Subgroup.map_subgroupOf_eq_of_le hEimg, Subgroup.map_bot] at h
  have hEsub : E.IsSubnormal := by
    rw [hEdef]
    have hMA : M = M ⊔ A := (sup_eq_left.mpr hAM).symm
    have h2 : (W.subgroupOf (M ⊔ A)).IsSubnormal := by
      rw [← hMA]
      exact CFSG.Open.IsSubnormal.subgroupOf hf.subnormal_w_m
    have h3 : (img148 A M W).IsSubnormal := by
      have h := Subgroup.IsSubnormal.map (QuotientGroup.mk'_surjective (ker148 A M)) h2
      simpa [img148] using h
    exact h3.subgroupOf
  have hcomm : ⁅X, W⁆ ≤ pPrimeCoreOf 3 M := by
    rw [hWdef, Subgroup.commutator_comm]
    exact (Proof155P.commutator_w155_le hf hX).trans
      (CFSG.RankThree.PartTwo.Sec17.Proof17Q0.pCoreOf_le_pPrimeCoreOf M)
  have hVE : ⁅V, E⁆ = ⊥ := by
    rw [hVdef, hEdef, hDdef]
    exact Proof153Twin3.commutator_img_subgroupOf_eq_bot (D := deltaZero A (lB A) M)
      hXΔ hWΔ hΔMA hcomm
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
    have hD : D = ⊥ := img148_eq_bot_of_le h1
    haveI hsub : Subsingleton ↥D := by
      rw [hD]
      exact inferInstance
    have hVbot : V = ⊥ := by
      rw [eq_bot_iff]
      intro x _
      rw [show x = 1 from Subsingleton.elim x 1]
      exact Subgroup.one_mem ⊥
    exact absurd hVbot ((Subgroup.nontrivial_iff_ne_bot V).mp
      (CFSG.LocalCores.isQuasisimple_nontrivial hVq))
  ·
    exfalso
    obtain ⟨c', hc', hdec, hL'⟩ := h2
    obtain ⟨L', hL', hcases⟩ := hL'
    rcases hcases with ⟨⟨φ⟩⟩ | ⟨-, ⟨φ⟩⟩ | ⟨p, f, e', hp, hf, -, -, hε⟩ | ⟨-, h6 | ⟨⟨φ⟩⟩⟩
    · exact hEne (eq_bot_of_cover_quasisimple
        (Sec6.isQuasisimple_of_mem_thetaComponentsAt hL'.1) φ hVsub hVq hEperf hVE)
    · exact hEne (eq_bot_of_cover_simple φ hVsub hVq hEperf hVE)
    · haveI : Fact p.Prime := hp
      rcases hε with ⟨⟨φ⟩⟩ | ⟨h2q, ⟨φ⟩⟩
      · haveI : IsSimpleGroup
            (CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField p f)) :=
          Sec19.Step1914TriProof.isSimpleGroup_projSL_three_of_field _
        exact hEne (eq_bot_of_cover_simple φ hVsub hVq hEperf hVE)
      · haveI : IsSimpleGroup (CFSG.Assembly.RankThreeEven.projSU 3 p f) :=
          Sec19.Step1914TriProof.isSimpleGroup_projSU_three_of_ne_two p f hf (by omega)
        exact hEne (eq_bot_of_cover_simple φ hVsub hVq hEperf hVE)
    · exact hEne (eq_bot_of_cover_triple h6 hVsub hVq hEperf hVE)
    · exact hEne (eq_bot_of_cover_simple φ hVsub hVq hEperf hVE)
  ·
    obtain ⟨c', d, L', hc', hL', hJ2, hdA, hd1, hd3, hdecomp, htypes⟩ := h3
    rcases htypes with hON | hCP | hCTA | ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩ | ⟨hp7, ⟨φ⟩⟩
    · exact (hEne (eq_bot_of_cover_triple hON hVsub hVq hEperf hVE)).elim
    · exact ⟨c', d, L', hc', hL', hJ2, hdA, hd1, hd3, hdecomp, Or.inl hCP⟩
    · exact ⟨c', d, L', hc', hL', hJ2, hdA, hd1, hd3, hdecomp, Or.inr (Or.inl hCTA)⟩
    · exact ⟨c', d, L', hc', hL', hJ2, hdA, hd1, hd3, hdecomp, Or.inr (Or.inr ⟨φ⟩)⟩
    · exact (hEne (eq_bot_of_cover_simple φ hVsub hVq hEperf hVE)).elim
    · haveI : Fact (Nat.Prime 7) := hp7
      haveI : IsSimpleGroup
          (CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 7 1)) :=
        Sec19.Step1914TriProof.isSimpleGroup_projSL_three_of_field _
      exact (hEne (eq_bot_of_cover_simple φ hVsub hVq hEperf hVE)).elim
  ·
    obtain ⟨⟨φ⟩, -, -⟩ := h4
    exact (hEne (eq_bot_of_cover_simple φ hVsub hVq hEperf hVE)).elim
  ·
    obtain ⟨-, -, -, n, -, -, -, hn, -, hiso, -⟩ := h5
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    rcases hiso with ⟨-, ⟨φ⟩⟩ | ⟨-, ⟨φ⟩⟩
    · haveI : IsSimpleGroup
          (CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 2 (3 * n))) :=
        Sec19.Step1914TriProof.isSimpleGroup_projSL_three_of_field _
      exact (hEne (eq_bot_of_cover_simple φ hVsub hVq hEperf hVE)).elim
    · have h2 : 2 ^ (3 * n) ≠ 2 := by
        intro h22
        have := Nat.pow_right_injective (le_refl 2) (h22.trans (pow_one 2).symm)
        omega
      haveI : IsSimpleGroup (CFSG.Assembly.RankThreeEven.projSU 3 2 (3 * n)) :=
        Sec19.Step1914TriProof.isSimpleGroup_projSU_three_of_ne_two 2 (3 * n) (by omega) h2
      exact (hEne (eq_bot_of_cover_simple φ hVsub hVq hEperf hVE)).elim
  ·
    exfalso
    obtain ⟨⟨eJ2⟩, -, -⟩ := h6
    have hcase := Proof155P.j2prod_facts (T := ↥D) eJ2 hVsub hVq hEsub hEperf hEne hVE
    have hcardE : Nat.card E = Nat.card (img148 A M W) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEimg).toEquiv
    have hcardV : Nat.card V = Nat.card (img148 A M X) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (img148_mono hXΔ)).toEquiv
    rcases hcase with ⟨hVrank, h5E⟩ | ⟨h5V, hErank⟩
    ·
      have h5W : 5 ∣ Nat.card W :=
        (hcardE ▸ h5E).trans (Main148.card_img148_dvd hWMA)
      have hXle : CFSG.Open.pRank 5 X ≤ 1 := Proof155P.pRank_five_x_le_one h hf hX h5W
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
      have hWle : CFSG.Open.pRank 5 W ≤ 1 := Proof155P.pRank_five_w155_le_one h hf hX h5X
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

end CFSG.RankThree.PartTwo.Sec15.Sylow155NO
