module

public import CFSG.LocalAnalysis.UniquenessCase.UC22KPkg
public import CFSG.LocalAnalysis.UniquenessCase.UC22KFinA
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22sm
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22sn
public import CFSG.LocalAnalysis.UniquenessCase.UC22P21o
public import CFSG.LocalAnalysis.UniquenessCase.UC22K339Zc
import CFSG.LocalAnalysis.UniquenessCase.UC22P22sk
import CFSG.LocalAnalysis.UniquenessCase.UC22P22sb
import CFSG.LocalAnalysis.UniquenessCase.UC22P22si
import CFSG.LocalAnalysis.UniquenessCase.UC22P22sj
import CFSG.LocalAnalysis.UniquenessCase.UC22P22t
import CFSG.LocalAnalysis.UniquenessCase.UC22P22e
import CFSG.LocalAnalysis.UniquenessCase.UC22P22xg
import CFSG.LocalAnalysis.UniquenessCase.UC22P22xh
import CFSG.LocalAnalysis.UniquenessCase.UC22P22xf
import CFSG.LocalAnalysis.UniquenessCase.UC22CmpMain
import CFSG.Quasithin.Background.BlueprintB2Thompson
import CFSG.Quasithin.Background.A3ComponentsAmbient
import CFSG.Quasithin.Background.A3ComponentsBasic
import CFSG.Quasithin.Background.A4V
import CFSG.Quasithin.EmptyFaithful.SBd5Perf
public import CFSG.LocalAnalysis.UniquenessCase.UC22K339Z
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22v
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846d
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846e

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.Quasithin (MinParabolic IsTwoReducedIn VZ thompsonJ baum)
open CFSG.RankThree.PartOne (InClassG tripleE tripleV InClassX oResidualTwo omegaOne omegaOneCenterIn)
open CFSG.LocalAnalysis.UniquenessCase.UC22.F12 (jOf)
open scoped commutatorElement
open P22x P22s

variable {G : Type} [Group G] [Finite G]

theorem uc22k_omegaZJ22_eq (D : Data G) (Ch : Choice2011 G) (h2 : S22_3_2 D Ch) (h3 : S22_3_3 D Ch)
    (h51 : S22_5_1 D Ch) (hH : H1930 D) (c : Ctx22c D Ch) {Y : Subgroup (MBar D.M D.U)} {H : Subgroup G}
    (hpkg : HiPkgK D Y H) (hY : preN D Y = proofN D) :
    omegaZJ22 (pCoreOf 2 H) = omegaZJ22 (D.T ⊓ (proofN D ⊓ centralizer (D.U : Set G))) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hSH, hG, -, -, -, -, -, -, -, B, -, hOB, hCB, -, hBU, hNB⟩ := hpkg
  set S : Subgroup G := proofS D with hSdef
  set R : Subgroup G := pCoreOf 2 H with hRdef
  set X₂ : Subgroup G := D.T ⊓ (proofN D ⊓ centralizer (D.U : Set G)) with hX₂def
  have hRS : R ≤ S := P22k.pCoreOf_le_of_inClassG hSH hG
  have hRT : R ≤ D.T := hRS.trans inf_le_left
  have hX₂T : X₂ ≤ D.T := inf_le_left
  have hCUB : centralizer (D.U : Set G) ≤ centralizer (B : Set G) := Subgroup.centralizer_le hBU
  obtain ⟨B₀, hB₀, hB₀X⟩ := P22so.exists_isMax_le D Ch h2 h3 h51 hH c
  have hB₀X₂ : B₀ ≤ X₂ := le_inf hB₀.1 hB₀X
  have hB₀R : B₀ ≤ R := fun b hb => hCB ⟨P22k.isMax_le_proofS D hB₀ hb, hCUB (hB₀X hb).2⟩
  have hAR : ∀ A, CFSG.Quasithin.IsMaxElemAbelian R A → A ≤ X₂ := by
    intro A hA
    have hAT := P22so.isMax_of_isMax_of_le hB₀ hB₀R hRT hA
    have hAN : A ≤ proofN D := (le_jOf_of_isMax hAT).trans (uc22p22e_jOf_le D.sylowM)
    exact le_inf hAT.1 (le_inf hAN fun a ha => hNB ⟨hY ▸ hAN ha, hOB (hA.1 ha)⟩)
  have hAX : ∀ A, CFSG.Quasithin.IsMaxElemAbelian X₂ A → A ≤ R := by
    intro A hA
    have hAT := P22so.isMax_of_isMax_of_le hB₀ hB₀X₂ hX₂T hA
    exact fun a ha => hCB ⟨P22k.isMax_le_proofS D hAT ha, hCUB (hA.1 ha).2.2⟩
  have hJ : jOf R = jOf X₂ := by
    apply le_antisymm
    · refine jOf_le_of_forall_isMax fun A hA => le_jOf_of_isMax ⟨hAR A hA, hA.2.1, fun Y hYX hYel => ?_⟩
      exact (P22so.isMax_of_isMax_of_le hB₀ hB₀R hRT hA).2.2 Y (hYX.trans hX₂T) hYel
    · refine jOf_le_of_forall_isMax fun A hA => le_jOf_of_isMax ⟨hAX A hA, hA.2.1, fun Y hYR hYel => ?_⟩
      exact (P22so.isMax_of_isMax_of_le hB₀ hB₀X₂ hX₂T hA).2.2 Y (hYR.trans hRT) hYel
  have hER : omegaZJ22 R ≤ X₂ := by
    obtain ⟨A₀, hA₀⟩ := exists_mem_elemThompsonFamily ↥R
    have hmax := isMax_of_mem_family hA₀
    exact (P22k.omegaZJ22_le_of_isMax hmax hmax.1 le_rfl).trans (hAR _ hmax)
  have hEX : omegaZJ22 X₂ ≤ R := by
    obtain ⟨A₀, hA₀⟩ := exists_mem_elemThompsonFamily ↥X₂
    have hmax := isMax_of_mem_family hA₀
    exact (P22k.omegaZJ22_le_of_isMax hmax hmax.1 le_rfl).trans (hAX _ hmax)
  apply le_antisymm
  · intro z hz
    obtain ⟨-, hzc, hz2⟩ := uc22p22e_mem_omegaZJ'.1 hz
    exact uc22p22e_mem_omegaZJ'.2 ⟨hER hz, fun j hj => hzc j (by rw [hJ]; exact hj), hz2⟩
  · intro z hz
    obtain ⟨-, hzc, hz2⟩ := uc22p22e_mem_omegaZJ'.1 hz
    exact uc22p22e_mem_omegaZJ'.2 ⟨hEX hz, fun j hj => hzc j (by rw [← hJ]; exact hj), hz2⟩

theorem uc22k_normalizer_le (D : Data G) (hx : DataExt D) (h61 : UC6.R6_1 D)
    (hTI : ¬ CFSG.CGT.Timmesfeld75.IsTI D.U) {p : ℕ} (hp : p ∈ D.sig) {W : Subgroup G} (hW : W ≠ ⊥)
    (hWle : W ≤ D.T ⊓ (proofN D ⊓ centralizer (D.U : Set G)))
    (hWc : (W.subgroupOf (D.T ⊓ (proofN D ⊓ centralizer (D.U : Set G)))).Characteristic) :
    normalizer (W : Set G) ≤ D.M := by
  classical
  obtain ⟨hpP, -⟩ := D.sig_prime p hp
  haveI : Fact p.Prime := ⟨hpP⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set X : Subgroup G := proofN D ⊓ centralizer (D.U : Set G) with hXdef
  have hV := uc22p22xf_hV D
  have hMN := uc22p22t_M_le_normalizer_jOf D
  have hXM : X ≤ D.M := inf_le_left.trans (uc22p22e_jOf_le_self D.M)
  have hMX : D.M ≤ normalizer (X : Set G) := fun g hg =>
    mem_normalizer_inf (hMN hg) (P22so.mem_normalizer_centralizer_of (hV hg))
  have hX₂ : CFSG.ABGLocalTools.IsSylowOf 2 (D.T ⊓ X) X := D.sylowM.inf_of_le_normalizer hXM hMX
  obtain ⟨P, hPsyl⟩ := CFSG.ABGLocalTools.exists_isSylowOf p D.M
  have hrk : 1 < CFSG.pRank p (MBar D.M D.U) :=
    uc22p22n_one_lt_pRank_mbar D hx h61 (uc22p22e_inCalV_U D) hTI p hp
  have hnc : ¬ IsCyclic ↥(mbarImage D.M D.U P) := by
    refine uc22p22e_not_isCyclic_sylow hpP (uc22p22t_isSylowOf_mbarImage D hPsyl) ?_
    rw [← CFSG.SectionRank.pRank_eq_open_pRank_top]
    omega
  have hPK : P ⊓ X ≤ centralizer (D.U : Set G) := fun x hx => hx.2.2
  obtain ⟨R₀, hR₀M, hR₀p, hR₀nc, hR₀N⟩ :=
    uc22p22t_frattini_bar D hXM hMX le_rfl hX₂ hPsyl.isPGroup hPsyl.le hPK hnc
  have hC := uc22p22e_calCGS_le D h61 hp hR₀M hR₀p hR₀nc hR₀N (inf_le_left : D.T ⊓ X ≤ D.T)
  refine le_trans ?_ hC
  unfold UC6.calCGS
  exact le_iSup_of_le W (le_iSup_of_le hW (le_iSup_of_le hWle (le_iSup_of_le hWc le_rfl)))

theorem uc22k_omegaZJ22_characteristic (R : Subgroup G) : ((omegaZJ22 R).subgroupOf R).Characteristic := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h : (omegaZJ22 R).subgroupOf R = CFSG.elemThompsonCenterTorsion ↥R 2 := by
    unfold omegaZJ22 CFSG.inSubgroup
    exact Subgroup.comap_map_eq_self_of_injective R.subtype_injective _
  rw [h]
  exact CFSG.Quasithin.BlueprintB2.elemThompsonCenterTorsion_characteristic ↥R 2

theorem uc22k_le_M_of_inClassG (D : Data G) (Ch : Choice2011 G) (hx : DataExt D) (h61 : UC6.R6_1 D)
    (h2 : S22_3_2 D Ch) (h3 : S22_3_3 D Ch) (h51 : S22_5_1 D Ch) (hK : K339Z)
    (hH : H1930 D) (c : Ctx22c D Ch) {p : ℕ} (hp : p ∈ D.sig) {m : ℕ} {Nb : Fin m → Subgroup (MBar D.M D.U)}
    (hNb : NbarSplit D Nb) (hHi : ∀ i, ∃ H : Subgroup G, HiPkgK D (Nb i) H)
    (hNne : mbarImage D.M D.U (proofN D) ≠ ⊥) (h6 : Cl22_6Hat D Nb)
    {L X W : Subgroup G} (hSX : proofS D ≤ X) (hLX : L ≤ X)
    (hG : InClassG ↥(proofS D) ↥X (Subgroup.inclusion hSX))
    (hZ : ¬ X ≤ centralizer (omegaOneCenterIn (proofS D) : Set G))
    (hsharp : ∀ A : Subgroup G, CFSG.Quasithin.IsMaxElemAbelian D.T A →
      CFSG.Quasithin.IsMaxElemAbelian D.T ((A ⊓ centralizer (W : Set G)) ⊔ W))
    (hOW : pCoreOf 2 X ≤ centralizer (W : Set G)) (hCW : proofS D ⊓ centralizer (W : Set G) ≤ pCoreOf 2 X) :
    L ≤ D.M := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hLM
  set S : Subgroup G := proofS D with hSdef
  have hS2 : IsPGroup 2 ↥S := D.sylowM.isPGroup.to_le inf_le_left
  have hSJ := centralizer_elemThompsonCenterTorsion_proofS D
  set ι : ↥S →* ↥X := Subgroup.inclusion hSX with hι
  have hZX : ⁅(⊤ : Subgroup ↥X), (omegaOne 2 (Subgroup.center ↥S)).map ι⁆ ≠ ⊥ :=
    commutator_omegaOne_ne_bot hSX hZ
  have hXT : pCoreOf 2 X ≤ D.T := (P22k.pCoreOf_le_of_inClassG hSX hG).trans inf_le_left
  choose Hs hHs using hHi
  have hFi : ∀ i, omegaZJ22 (pCoreOf 2 (Hs i)) = omegaZJ22 (pCoreOf 2 X) := by
    intro i
    obtain ⟨hSH, hGi, hZi, hXi, -, -, -, -, -, -⟩ := hHs i
    set ιi : ↥S →* ↥(Hs i) := Subgroup.inclusion hSH with hιi
    have hZi' : ⁅(⊤ : Subgroup ↥(Hs i)), (omegaOne 2 (Subgroup.center ↥S)).map ιi⁆ ≠ ⊥ :=
      commutator_omegaOne_ne_bot hSH hZi
    rcases hK ↥S hS2 hSJ ↥(Hs i) ιi hGi ↥X ι hG hZi' hZX with h1 | h2' | h3'
    · exact omegaZJ22_eq_of_comap_eq hSH hSX hGi hG h1
    ·
      exfalso
      apply h2'
      rcases P22k.campbell_seed D hSX hSH hG hGi hZ hZi with hc1 | hc3
      · have hEX : omegaZJ22 (pCoreOf 2 (Hs i)) ≤ pCoreOf 2 X := fun e he => by
          simpa using hc1 1 (one_mem _) e he
        have hcomm := P22k.commute_of_pkg_of_sharp D (hHs i) hXT hsharp hOW hCW hEX
        rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
        intro a ha
        rw [Subgroup.mem_centralizer_iff]
        intro b hb
        apply Subtype.ext
        have haF : (a : G) ∈ omegaZJ22 (pCoreOf 2 (Hs i)) := by
          rw [← map_tripleE (Hs i)]
          exact ⟨ιi a, tripleV_le_tripleE ha, rfl⟩
        have hbF : (b : G) ∈ omegaZJ22 (pCoreOf 2 X) := by
          rw [← map_tripleE X]
          exact ⟨ι b, tripleV_le_tripleE hb, rfl⟩
        exact hcomm (b : G) hbF (a : G) haF
      · exact absurd hc3 hXi
    ·
      exfalso
      apply hLM
      intro x hx
      apply h6 i
      apply Subgroup.centralizer_le_normalizer
      rw [Subgroup.mem_centralizer_iff]
      intro e he
      have heS : e ∈ S :=
        uc22p22sb_U_le_proofS D Ch h2 h3 h51 hH c (proofEiHat_le D (preN_le_M D (Nb i)) he)
      have hmem : (⟨e, heS⟩ : ↥S) ∈ (⁅thompsonJ ιi.range, tripleE ↥(Hs i)⁆).comap ιi :=
        K339.mem_commutator_thompsonJ_tripleE hSH (hSH heS) (K339.proofEiHat_le_commutator_jOf D (hHs i) he)
      have hcen := h3' ⟨⟨e, heS⟩, hmem, rfl⟩
      exact (congrArg Subtype.val ((Subgroup.mem_center_iff.1 hcen) ⟨x, hLX hx⟩)).symm
  have hm1 : m ≤ 1 := by
    by_contra hm
    push Not at hm
    have hij : (⟨0, by omega⟩ : Fin m) ≠ ⟨1, hm⟩ := by
      intro h
      exact absurd (congrArg Fin.val h) (by norm_num)
    apply uc22p22sk_proofEiHat_ne D Ch h3 h51 hH c hNb hij
    obtain ⟨-, -, -, -, hb₀, -⟩ := hHs ⟨0, by omega⟩
    obtain ⟨-, -, -, -, hb₁, -⟩ := hHs ⟨1, hm⟩
    rw [← hb₀, ← hb₁, hFi, hFi]
  have hm0 : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · exfalso
      apply hNne
      rw [← hNb.1.1]
      subst h0
      exact iSup_of_empty _
    · exact h0
  set i₀ : Fin m := ⟨0, hm0⟩ with hi₀
  have hNi : preN D (Nb i₀) = proofN D := uc22p22sk_preN_eq D hNb hm1 i₀
  have hF45 := uc22k_omegaZJ22_eq D Ch h2 h3 h51 hH c (hHs i₀) hNi
  have hne : omegaZJ22 (D.T ⊓ (proofN D ⊓ centralizer (D.U : Set G))) ≠ ⊥ := by
    rw [← hF45]
    intro hbot
    obtain ⟨-, -, -, -, -, hEle, -⟩ := hHs i₀
    have hVE : ⁅Hs i₀, omegaZJ22 (pCoreOf 2 (Hs i₀))⁆ ≤ omegaZJ22 (pCoreOf 2 (Hs i₀)) := by
      rw [← map_tripleV, ← map_tripleE]
      exact Subgroup.map_mono tripleV_le_tripleE
    apply (uc22p22xg_proofEiHat_ne_bot D Ch h2 h3 h51 hH c m Nb hNb i₀).1
    rw [eq_bot_iff, ← hbot]
    exact (hEle.trans inf_le_left).trans hVE
  have hNF := uc22k_normalizer_le D hx h61 c.hU hp hne
    (fun z hz => (uc22p22e_mem_omegaZJ'.1 hz).1) (uc22k_omegaZJ22_characteristic _)
  apply hLM
  intro x hx
  apply hNF
  rw [← hF45, hFi i₀]
  exact mem_normalizer_omegaZJ22 (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 X (hLX hx))

theorem uc22k_le_M (h69 : CFSG.ASVolI.B_6_9) (hTC : CFSG.RankThree.PartOne.TauCetiCatalogBridge)
    {D : Data G} {Ch : Choice2011 G} (hx : DataExt D) (h61 : UC6.R6_1 D) (h2 : S22_3_2 D Ch)
    (h3 : S22_3_3 D Ch) (h51 : S22_5_1 D Ch) (h204 : S20_4 D) (hK : K339Z)
    (hH : H1930 D) (c : Ctx22c D Ch) (hS7 : normalizer (proofS D : Set G) ≤ D.M) (hn3 : 3 ≤ c.n) {p : ℕ}
    (hp : p ∈ D.sig) {m : ℕ} {Nb : Fin m → Subgroup (MBar D.M D.U)} (hNb : NbarSplit D Nb)
    (hHi : ∀ i, ∃ H : Subgroup G, HiPkgK D (Nb i) H)
    (hNne : mbarImage D.M D.U (proofN D) ≠ ⊥) (h6 : Cl22_6Hat D Nb) {L : Subgroup G}
    (hLsub : CFSG.Open.IsSubnormal L (c.L0 ⊔ D.T)) (hLL0 : L ≤ c.L0) (hL0L : c.L0 ≤ normalizer (L : Set G))
    (hLp : ⁅L, L⁆ = L) (hLq : CFSG.Open.IsQuasisimple (Bar2 L)) (hshape : NParamSingle (Bar2 L) c.n) :
    L ≤ D.M := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set H : Subgroup G := c.L0 ⊔ D.T with hHdef
  set V₀ : Subgroup G := VZ D.T H with hV₀
  set S : Subgroup G := proofS D with hSdef
  obtain ⟨hU, -, -, hred⟩ := uc22p22se_ffModule c hS7
  have hHN : H ≤ normalizer (V₀ : Set G) := hred.2.1
  have hLN : L ≤ normalizer (V₀ : Set G) := hLL0.trans (le_sup_left.trans hHN)
  have hV : ∀ x ∈ V₀, ∀ y ∈ V₀, x * y = y * x := fun x hx y hy => hU.comm hx hy
  have hZV : D.Z ≤ V₀ := by
    rw [uc22p22se_Z_eq]
    exact CFSG.Quasithin.le_conjClosure _ _
  by_cases hLC : L ≤ centralizer (V₀ : Set G)
  · exact hLC.trans ((Subgroup.centralizer_le hZV).trans c.hCle)
  obtain ⟨e, he, hnat⟩ := uc22p22sh_natural h69 hTC h204 hH c hS7 hn3 hLsub hLL0 hLp hLq hshape
    (fun g hg l hl => ⟨g * l * g⁻¹, (Subgroup.mem_normalizer_iff.1 (hL0L hg) l).1 hl, by
      rw [mul_inv_cancel]
      exact one_mem _⟩) hLC
  obtain ⟨hSL, hsylX, hE⟩ := uc22p22sl_b610 h204 hH c hS7 hLsub hLL0 hL0L hLp he hnat
  by_cases hJW : ⁅thompsonJ D.T, ⁅V₀, L⁆⁆ = ⊥
  · exact uc22p22sl_le_M_of_commutator_eq_bot c hS7 hLN hE hJW
  by_contra hLM
  obtain ⟨F, _, _, hF, α, hα, hαk, β, hβ, hβk, hβα⟩ := hnat
  set α' : ↥L →* Matrix.SpecialLinearGroup (Fin 2) F := (slEquiv F).symm.toMonoidHom.comp α with hα'def
  have hα' : Function.Surjective α' := (slEquiv F).symm.surjective.comp hα
  have hβα' : ∀ (l : ↥L) (u v : ↥⁅V₀, L⁆), (v : G) = l * u * l⁻¹ →
      Multiplicative.toAdd (β v) = (α' l : Matrix (Fin 2) (Fin 2) F).mulVec (Multiplicative.toAdd (β u)) := by
    intro l u v h
    rw [hβα l u v h, hα'def, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, coe_slEquiv_symm]
  have hO : pCoreOf 2 L ≤ centralizer (V₀ : Set G) := by
    refine (pCoreOf_le_of_isSubnormal hLsub).trans fun x hx => ?_
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    exact (Subgroup.mem_centralizer_iff.1 ((uc22p22se_V0_facts c.toCtx21).1 hv).2 x hx).symm
  have hS2 : IsPGroup 2 ↥S := D.sylowM.isPGroup.to_le inf_le_left
  have hJS : thompsonJ D.T ≤ S := by
    rw [← uc22p22se_jOf_eq]
    exact jOf_le_proofS D
  have hSV : S ≤ normalizer (V₀ : Set G) := fun s hs => hHN (Subgroup.mem_sup_right hs.1)
  have hWV : ⁅V₀, L⁆ ≤ V₀ := Subgroup.le_normalizer_iff_commutator_le_left.mp hLN
  have hW₁e : CFSG.Open.IsElemAbelian 2 ⁅V₀, L⁆ :=
    ⟨⟨⟨fun a b => Subtype.ext (hU.comm (hWV a.2) (hWV b.2))⟩⟩, fun x hx => hU.2 x (hWV hx)⟩
  have hLW : L ≤ normalizer ((⁅V₀, L⁆ : Subgroup G) : Set G) := fun l hl =>
    CFSG.Quasithin.SBd5.mem_normalizer_commutator_of (hLN hl) (Subgroup.le_normalizer hl)
  set R : Subgroup G := D.T ⊓ normalizer (L : Set G) with hRdef
  have hRV : R ≤ normalizer (V₀ : Set G) := fun r hr => hHN (Subgroup.mem_sup_right hr.1)
  have hRW₁ : R ≤ normalizer ((⁅V₀, L⁆ : Subgroup G) : Set G) := fun r hr =>
    CFSG.Quasithin.SBd5.mem_normalizer_commutator_of (hRV hr) hr.2
  have hRW₀ : R ≤ normalizer ((⁅V₀, L⁆ ⊓ centralizer (L : Set G) : Subgroup G) : Set G) := fun r hr =>
    mem_normalizer_inf' (hRW₁ hr) (mem_normalizer_centralizer hr.2)
  have hJR : thompsonJ R = thompsonJ D.T :=
    CFSG.Quasithin.B6.thompsonJ_eq_of_le (le_inf (hJS.trans inf_le_left) (hJS.trans hSL)) inf_le_left
  have hV₀T : V₀ ≤ D.T := ((uc22p22se_V0_facts c.toCtx21).1.trans inf_le_left).trans
    (CFSG.Quasithin.B6.pCoreOf_two_le_of_isSylowTwoOf (uc22p22se_isSylowTwoOf D le_sup_right))
  have hYsol : Group.IsSolvable ↥(V₀ ⊓ c.L0) :=
    Group.isSolvable_of_comm fun a b => Subtype.ext (hU.comm a.2.1 b.2.1)
  have hV₀L : V₀ ≤ normalizer (L : Set G) := by
    refine le_normalizer_of_conj fun v hv l hl =>
      conj_mem_of_perfect hYsol (inf_le_right.trans hL0L) hLp (fun l hl => ?_) l hl
    have h1 : v * l * v⁻¹ ∈ c.L0 := (Subgroup.mem_normalizer_iff.1 (c.hL0.1.1 (hV₀T hv)) l).1 (hLL0 hl)
    have h2 : l⁻¹ * v * l ∈ V₀ := by
      have := (Subgroup.mem_normalizer_iff.1 (hLN (L.inv_mem hl)) v).1 hv
      simpa using this
    have h3 : l⁻¹ * (v * l * v⁻¹) ∈ V₀ ⊓ c.L0 := by
      refine ⟨?_, c.L0.mul_mem (c.L0.inv_mem (hLL0 hl)) h1⟩
      have e : l⁻¹ * (v * l * v⁻¹) = (l⁻¹ * v * l) * v⁻¹ := by group
      rw [e]
      exact V₀.mul_mem h2 (V₀.inv_mem hv)
    have e : v * l * v⁻¹ = l * (l⁻¹ * (v * l * v⁻¹)) := by group
    rw [e]
    exact Subgroup.mul_mem_sup hl h3
  have hWR : ⁅V₀, L⁆ ≤ R := fun w hw => ⟨hV₀T (hWV hw), hV₀L (hWV hw)⟩
  have hSR : S ≤ baum R := fun b hb => ⟨⟨hb.1, hSL hb⟩, by
    rw [hJR, ← uc22p22se_proofE_eq]
    exact hb.2⟩
  have hinn := uc22p22si_inner hF he (D.sylowM.isPGroup.to_le inf_le_left) inf_le_right hRW₁ hRW₀ hWR hW₁e hLW
    α' hα' β hβ hβk hβα'
    (fun r hr hr' => mem_centralizer_of_trivial α hαk β hβ hβk hβα hV hLN hLp hr.2 (hRV hr) hr')
    (by rw [hJR]; exact hJW)
  have hinnS : ∀ b ∈ S, ∃ l ∈ L, ∀ u v : ↥⁅V₀, L⁆, (v : G) = (l⁻¹ * b) * u * (l⁻¹ * b)⁻¹ → β v = β u :=
    fun b hb => hinn b (hSR hb)
  have hSW : ¬ S ≤ centralizer ((⁅V₀, L⁆ : Subgroup G) : Set G) := fun h =>
    hJW (Subgroup.commutator_eq_bot_iff_le_centralizer.2 (hJS.trans h))
  have hLSL := le_commutator_of_inner hF (by omega) α hα hαk β hβ hβk hβα hV hLN hLp hLq hO hSL hSV hinnS hSW
  have hSX : S ≤ ⨆ l ∈ L, S.map (MulAut.conj l).toMonoidHom := fun s hs =>
    Subgroup.mem_iSup_of_mem 1 (Subgroup.mem_iSup_of_mem L.one_mem ⟨s, hs, by simp⟩)
  have hX : (⨆ l ∈ L, S.map (MulAut.conj l).toMonoidHom) = L ⊔ S := by
    refine le_antisymm (iSup₂_le fun l hl => ?_) (sup_le (hLSL.trans ?_) hSX)
    · rintro _ ⟨s, hs, rfl⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      exact (L ⊔ S).mul_mem ((L ⊔ S).mul_mem (Subgroup.mem_sup_left hl) (Subgroup.mem_sup_right hs))
        ((L ⊔ S).inv_mem (Subgroup.mem_sup_left hl))
    · rw [Subgroup.commutator_le]
      intro s hs l hl
      have hmem : l * s⁻¹ * l⁻¹ ∈ ⨆ l ∈ L, S.map (MulAut.conj l).toMonoidHom :=
        Subgroup.mem_iSup_of_mem l (Subgroup.mem_iSup_of_mem hl ⟨s⁻¹, S.inv_mem hs, by simp⟩)
      have e : ⁅s, l⁆ = s * (l * s⁻¹ * l⁻¹) := by rw [commutatorElement_def]; group
      rw [e]
      exact mul_mem (hSX hs) hmem
  have hsyl : CFSG.QuasithinUnique.IsSylowTwoOf S (L ⊔ S) := hX ▸ hsylX
  have hchar : CFSG.QuasithinUnique.CharTwo (L ⊔ S) :=
    CFSG.Quasithin.A4.charTwo_sup (charTwo_of_isSubnormal' (uc22p22se_charTwo c.toCtx21) hLsub) hSL hS2
  have hSW₁ : S ≤ normalizer ((⁅V₀, L⁆ : Subgroup G) : Set G) := fun s hs => hRW₁ ⟨hs.1, hSL hs⟩
  have hSW₀ : S ≤ normalizer ((⁅V₀, L⁆ ⊓ centralizer (L : Set G) : Subgroup G) : Set G) := fun s hs =>
    hRW₀ ⟨hs.1, hSL hs⟩
  have hGL : InClassG ↥S ↥(L ⊔ S) (Subgroup.inclusion le_sup_right) :=
    uc22p22sj_inClassG hF he hS2 hSL hsyl.2.2 hchar hLp hLq hSW₁ hSW₀ hLW α' hα' β hβ hβk hβα' hinnS
  have hZ : ¬ L ⊔ S ≤ centralizer (omegaOneCenterIn S : Set G) := fun h =>
    hLM ((le_sup_left.trans h).trans ((Subgroup.centralizer_le (Z_le_omegaOneCenterIn D)).trans c.hCle))
  obtain ⟨hOW, hCW, hsharp⟩ :=
    P22kA.uc22k_lside hF he hS2 hSL hSV hLN hV hLp hLq hsyl α hα hαk β hβ hβk hβα hinnS
  have hsharp' : ∀ A : Subgroup G, CFSG.Quasithin.IsMaxElemAbelian D.T A →
      CFSG.Quasithin.IsMaxElemAbelian D.T ((A ⊓ centralizer ((⁅V₀, L⁆ : Subgroup G) : Set G)) ⊔ ⁅V₀, L⁆) :=
    fun A hA => hsharp D.T A (hWV.trans hV₀T) hW₁e hA (P22k.isMax_le_proofS D hA)
  exact hLM (uc22k_le_M_of_inClassG D Ch hx h61 h2 h3 h51 hK hH c hp hNb hHi hNne h6 le_sup_right
    le_sup_left hGL hZ hsharp' hOW hCW)


theorem uc22k_s22_2_finHat (D : Data G) (Ch : Choice2011 G) (hx : DataExt D) (h61 : UC6.R6_1 D)
    (h2 : S22_3_2 D Ch) (h3 : S22_3_3 D Ch) (h51 : S22_5_1 D Ch) (h204 : S20_4 D)
    (hn3 : H1930 D → ∀ c : Ctx21 D Ch, 3 ≤ c.n)
    (hHi : H1930 D → ∀ c : Ctx22c D Ch, ∀ (m : ℕ) (Nb : Fin m → Subgroup (MBar D.M D.U)), NbarSplit D Nb →
      ∀ i, ∃ H : Subgroup G, HiPkgK D (Nb i) H)
    (hK : K339Z)
    (h69 : CFSG.ASVolI.B_6_9) (hTC : CFSG.RankThree.PartOne.TauCetiCatalogBridge) : S22_2_finHat D Ch := by
  intro hH c p hp m Nb hNb hNne _ _ _ h6 hS7
  have hn : 3 ≤ c.n := hn3 hH c.toCtx21
  have hcomp : ∀ L : Subgroup G, CFSG.Open.IsSubnormal L (c.L0 ⊔ D.T) → L ≤ c.L0 →
      c.L0 ≤ normalizer (L : Set G) → ⁅L, L⁆ = L → CFSG.Open.IsQuasisimple (Bar2 L) →
      NParamSingle (Bar2 L) c.n → L ≤ D.M := fun L hLsub hLL0 hL0L hLp hLq hshape =>
    uc22k_le_M h69 hTC hx h61 h2 h3 h51 h204 hK hH c hS7 hn hp hNb (hHi hH c m Nb hNb) hNne h6 hLsub hLL0
      hL0L hLp hLq hshape
  have hL0n : c.L0 ⊔ D.T ≤ normalizer (c.L0 : Set G) := sup_le Subgroup.le_normalizer c.hL0.1.1
  have hL0sub : CFSG.Open.IsSubnormal c.L0 (c.L0 ⊔ D.T) :=
    CFSG.Quasithin.A3.subnormal_of_normal le_sup_left
      ((Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).2 hL0n)
  apply (uc22p22se_mem_hSet c.toCtx21).2.1
  refine sup_le ?_ D.sylowM.le
  rcases c.hn with hs | ⟨L₁, L₂, hL₁, hL₂, hL0eq, -, hshape⟩
  · exact hcomp c.L0 hL0sub le_rfl Subgroup.le_normalizer c.hL0.1.2.1
      (uc22p22sg_isQuasisimple_bar2_of_shape c.hL0.1.2.1 hs) hs
  · have hfac : ∀ L' : Subgroup G, L' ∈ calC c.L0 → c.L0 ≤ normalizer (L' : Set G) →
        (IsSz (Bar2 L') c.n ∨ IsL2 (Bar2 L') c.n ∨ (c.n = 3 ∧ IsSU3 (Bar2 L') 3)) → L' ≤ D.M := by
      intro L' hLc hL0L hsh
      refine hcomp L' (hLc.1.trans hL0sub) (isSubnormal_le hLc.1) hL0L hLc.2.1 hLc.2.2 ?_
      rcases hsh with h | h | ⟨h3', h⟩
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · refine Or.inr (Or.inr (Or.inl ?_))
        rw [h3']
        exact h
    rw [hL0eq]
    refine sup_le (hfac L₁ hL₁ (le_normalizer_of_mem_calC hL₁ hL₂ hL0eq) (hshape L₁ (by simp)))
      (hfac L₂ hL₂ (le_normalizer_of_mem_calC hL₂ hL₁ (hL0eq.trans (sup_comm L₁ L₂))) (hshape L₂ (by simp)))

end CFSG.LocalAnalysis.UniquenessCase.UC22
