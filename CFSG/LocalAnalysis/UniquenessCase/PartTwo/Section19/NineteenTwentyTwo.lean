module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.MSubBasic
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.StatementsA
public import CFSG.RankThree.PartOne.S12.Sec15Frattini
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.ElevenFourteenFour
public import CFSG.RankThree.PartTwo.Sec19.Census194.RonanC194SpBlocks
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22rk
public import CFSG.LocalAnalysis.UniquenessCase.UC22P2214g
public import CFSG.Quasithin.Background.C2PushBlocks
public import CFSG.LocalAnalysis.UniquenessCase.UC22P20d
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.CtxLemmas
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22ui
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22qv
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22ry
public import CFSG.GroupTheory.SLTwoInvertsElemAbelian
public import CFSG.LocalAnalysis.StandardType.GGSpJoinBstarSplit
public import CFSG.Quasithin.EmptyFaithful.S146zYFCCase
public import CFSG.Quasithin.EmptyFaithful.S1421QA19Tr
public import CFSG.Quasithin.Background.E2TwoLieQuotLift
public import CFSG.Quasithin.EmptyFaithful.S14110AuxBlocks
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.Statements

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

private theorem exists_lift_elemAbelian_to_M (D : Data G) {V₀ : Subgroup G} {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) {N : Type} [Group N] [Finite N]
    {Q : Type} [Group Q] [Finite Q] (π : N →* Q) (hπ : Function.Surjective π)
    (hker : IsPGroup 2 π.ker) (f : N →* G) (hf : Function.Injective f)
    (hNM : ∀ x, f x ∈ D.M) {E : Subgroup Q} (hEel : IsElemAbelian p E)
    (hdisjC : ∀ x : N, π x ∈ E → f x ∈ centralizer (V₀ : Set G) → π x = 1) :
    ∃ X : Subgroup G, X ≤ D.M ∧ IsPGroup p X ∧ IsElemAbelian p X ∧
      Nat.card X = Nat.card E ∧ X ⊓ centralizer (V₀ : Set G) = ⊥ := by
  obtain ⟨X, hXp, hXmap, hXdisj⟩ :=
    CFSG.LocalAnalysis.UniquenessCase.UC6S846.exists_lift_pGroup π hπ hker hp hp2 E
      hEel.isPGroup
  let Xg : Subgroup G := X.map f
  have hXgM : Xg ≤ D.M := by
    rintro _ ⟨x, hx, rfl⟩
    exact hNM x
  have hXgp : IsPGroup p Xg := hXp.map f
  have hXgel : IsElemAbelian p Xg :=
    (CFSG.LocalAnalysis.UniquenessCase.UC6S846.isElemAbelian_of_disjoint_ker π X hXdisj
      (by rw [hXmap]; exact hEel)).map f
  have hXgcard : Nat.card Xg = Nat.card E := by
    rw [Subgroup.card_map_of_injective hf,
      ← CFSG.LocalAnalysis.UniquenessCase.UC6S846.card_map_of_disjoint_ker π X hXdisj, hXmap]
  have hXbot : Xg ⊓ centralizer (V₀ : Set G) = ⊥ := by
    rw [eq_bot_iff]
    rintro y ⟨⟨x, hxX, rfl⟩, hxC⟩
    have hpiE : π x ∈ E := by
      rw [← hXmap]
      exact Subgroup.mem_map_of_mem π hxX
    have hpi1 : π x = 1 := hdisjC x hpiE hxC
    have hxker : x ∈ π.ker := MonoidHom.mem_ker.mpr hpi1
    have hx1 : x = 1 := Subgroup.disjoint_def.mp hXdisj hxX hxker
    exact Subgroup.mem_bot.mpr (by simpa using congrArg f hx1)
  exact ⟨Xg, hXgM, hXgp, hXgel, hXgcard, hXbot⟩

private theorem isCyclic_of_lift_disjoint_centralizer (D : Data G) {V₀ V : Subgroup G}
    (h61 : UC6.R6_1 D) (hH : F11.Hyp11 D V₀ V) {p : ℕ} (hp : p ∈ D.sig) {X : Subgroup G}
    (hXM : X ≤ D.M) (hXp : IsPGroup p X)
    (hXbot : X ⊓ centralizer (V₀ : Set G) = ⊥) : IsCyclic ↥X := by
  have hsub : (X ⊓ centralizer (V₀ : Set G)).subgroupOf X = ⊥ := by
    rw [hXbot, Subgroup.bot_subgroupOf]
  haveI : ((X ⊓ centralizer (V₀ : Set G)).subgroupOf X).Normal := by
    rw [hsub]; infer_instance
  haveI hcyc :=
    CFSG.LocalAnalysis.UniquenessCase.PartTwo.ElevenFourteen.eleven_four_one_of_sig D h61 hH
      hp hXM hXp
  let e : ↥X ⧸ (X ⊓ centralizer (V₀ : Set G)).subgroupOf X ≃* ↥X :=
    (QuotientGroup.quotientMulEquivOfEq hsub).trans QuotientGroup.quotientBot
  exact isCyclic_of_surjective e.toMonoidHom e.surjective

@[expose] def Gap19_22_P (D : Data G) (V₀ V : Subgroup G) (p : ℕ) (L A : Subgroup G)
    (t : G) (B : Subgroup G) (r : ℕ) (h : Ctx19_10 D V₀ V p L A t B r)
    (E : Subgroup G) : Prop :=
  E ≤ A → IsElemAbelian r E → Nat.card E = r ^ 2 →
    Permutes E D.T ∧
      (CFSG.RankThree.PartOne.IsStronglyPEmbedded r D.M ∨
        ∃ P : Subgroup G, CFSG.ABGLocalTools.IsSylowOf r P D.M ∧ E ≤ P ∧
          P ≤ normalizer (E : Set G))

theorem not_centralizer_le_of_not_normalizer_le {D : Data G} {V₀ V : Subgroup G} {p : ℕ}
    {L A : Subgroup G} {t : G} {B : Subgroup G} {r : ℕ}
    (h : Ctx19_10 D V₀ V p L A t B r)
    {A₀ E : Subgroup G} (hA₀A : A₀ ≤ A) (hEA : E ≤ A)
    (hEel : IsElemAbelian r E) (hEcard : Nat.card E = r ^ 2)
    (h12 : R19_12At D V₀ V p L A t B r h)
    (hN : ¬ normalizer (A₀ : Set G) ≤ D.M) :
    ¬ centralizer (A₀ : Set G) ≤ D.M := by
  have hr : r.Prime := h.hr.1
  haveI : Fact r.Prime := ⟨hr⟩
  intro hCM
  have hcommA : IsMulCommutative ↥A := isMulCommutative_of_isZModSq h.hAcard
  have hEC : E ≤ centralizer (A₀ : Set G) :=
    hEA.trans (le_centralizer_of_isMulCommutative_of_le hcommA hA₀A)
  have hEr : IsPGroup r E := CFSG.Open.IsElemAbelian.isPGroup hEel
  have hErC : IsPGroup r (E.subgroupOf (centralizer (A₀ : Set G))) := hEr.comap_subtype
  obtain ⟨Q, hQ⟩ := hErC.exists_le_sylow
  let R : Subgroup G := (Q : Subgroup ↥(centralizer (A₀ : Set G))).map
    (centralizer (A₀ : Set G)).subtype
  have hRsyl : CFSG.ABGLocalTools.IsSylowOf r R (centralizer (A₀ : Set G)) := ⟨Q, rfl⟩
  have hER : E ≤ R := by
    intro e he
    exact ⟨⟨e, hEC he⟩, hQ (Subgroup.mem_subgroupOf.mpr he), rfl⟩
  have hRle : R ≤ centralizer (A₀ : Set G) := Subgroup.map_subtype_le _
  have hRunique : R ∈ CFSG.LocalAnalysis.RankThreeUC.uniqueSet D.M :=
    CFSG.LocalAnalysis.RankThreeUC.mem_uniqueSet_of_le (h12 E hEA hEel hEcard) hER
      (hRle.trans hCM)
  have hNRM : normalizer (R : Set G) ≤ D.M :=
    CFSG.LocalAnalysis.RankThreeUC.normalizer_le_of_mem_uniqueSet D.maxLocal hRunique
  obtain ⟨g, hgN, hgM⟩ := SetLike.not_le_iff_exists.mp hN
  have hgC : g ∈ normalizer (centralizer (A₀ : Set G) : Set G) :=
    CFSG.GorensteinWalter.normalizer_le_normalizer_centralizer_subgroup A₀ hgN
  obtain ⟨k, hkC, hkR⟩ :=
    CFSG.RankThree.PartOne.Sec15Frattini.exists_mem_normalizer_of_isSylowOf hRsyl hgC
  have hkM : k ∈ D.M := hCM hkC
  have hkgM : k⁻¹ * g ∈ D.M := hNRM hkR
  apply hgM
  have hEq : g = k * (k⁻¹ * g) := by group
  rw [hEq]
  exact D.M.mul_mem hkM hkgM

@[expose] def Gap19_22 (D : Data G) (V₀ V : Subgroup G) (p : ℕ) (L A : Subgroup G)
    (t : G) (B : Subgroup G) (r : ℕ) (h : Ctx19_10 D V₀ V p L A t B r) : Prop :=
  (S17.IsL2U3Product (Bar2 (IOf D p L)) (S17.nOf L) ∨
      IsL2Square (Bar2 (IOf D p L)) (S17.nOf L)) →
    ∀ A₀ : Subgroup G, A₀ ≤ A → Nat.card A₀ = r → IsCyclic ↥A₀ →
      ¬ centralizer (A₀ : Set G) ≤ D.M → V₀ ≤ centralizer (A₀ : Set G)

private theorem sp4_two_le_pRank {X : Type} [Group X] [Finite X] {n p : ℕ} (hX : IsSp4 X n)
    (hp : p.Prime) (hdvd : p ∣ 2 ^ n + 1) : 2 ≤ CFSG.Open.pRank p (⊤ : Subgroup X) := by
  obtain ⟨-, F, _, _, hF, ⟨e⟩⟩ := CFSG.Blueprint.LieModel.statedClassicalModel hX (by decide)
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fintype F := Fintype.ofFinite F
  haveI : CharP F 2 :=
    charP_of_card_eq_prime_pow (p := 2) (f := n) (by rw [Fintype.card_eq_nat_card]; exact hF)
  rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt e]
  refine CFSG.RankThree.PartTwo.Sec19.Census194.RonanC194.le_pRank_statedProj_sp (n := 2) hp ?_
  have h1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  have h2 : 1 ≤ (2 ^ n) ^ 2 := Nat.one_le_pow _ _ (by positivity)
  have h3 : (2 ^ n) ^ 2 - 1 = (2 ^ n + 1) * (2 ^ n - 1) := by
    zify [h1, h2]
    ring
  rw [hF, h3]
  exact Dvd.dvd.mul_right hdvd _

theorem alt1_A_le_centralizer (D : Data G) {V₀ V : Subgroup G} {p : ℕ} {L A : Subgroup G}
    {t : G} {B : Subgroup G} {r : ℕ} (h : Ctx19_10 D V₀ V p L A t B r)
    (h61 : UC6.R6_1 D) (h127 : R127 D)
    (hsp : IsSp4 (Bar2 (IOf D p L)) (S17.nOf L))
    (hpn : (2 : ℤ) ^ (S17.nOf L) ≡ -1 [ZMOD (p : ℤ)]) :
    A ≤ centralizer (V₀ : Set G) := by
  classical
  set I := IOf D p L with hIdef
  set n := S17.nOf L with hndef
  have hH : F11.Hyp11 D V₀ V := Hyp125.hyp11 h127 h.hyp.hyp125
  obtain ⟨-, -, hMV₀, -⟩ := uc22p22q_hyp11_unpack D hH
  obtain ⟨hp, hp2⟩ := D.sig_prime p h.hyp.hp
  haveI : Fact p.Prime := ⟨hp⟩
  have hIM : I ≤ D.M := IOf_le_M D p h.hyp.hL.1.1.le
  have hMI : D.M ≤ normalizer (I : Set G) := le_normalizer_IOf D h.hyp.hL.1
  set C : Subgroup G := I ⊓ centralizer (V₀ : Set G) with hCdef
  have hCnorm : I ≤ normalizer (C : Set G) := fun x hx =>
    Subgroup.inf_normalizer_le_normalizer_inf
      ⟨hMI (hIM hx),
        CFSG.GorensteinWalter.normalizer_le_normalizer_centralizer_subgroup V₀ (hMV₀ (hIM hx))⟩
  set Cs : Subgroup ↥I := C.subgroupOf I with hCsdef
  haveI hCs : Cs.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left).mpr hCnorm
  let π : ↥I →* Bar2 I := QuotientGroup.mk' (CFSG.pCore 2 ↥I)
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective _
  haveI : (Cs.map π).Normal := Subgroup.Normal.map hCs π hπ
  haveI : IsSimpleGroup (Bar2 I) :=
    CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hsp
  have hAodd : Odd (Nat.card A) := odd_card_of_ctx19_10 h
  rcases Subgroup.Normal.eq_bot_or_eq_top (Cs.map π) with hbot | htop
  · exfalso
    have hCker : Cs ≤ π.ker := (Subgroup.map_eq_bot_iff _).mp hbot
    have hdvd : p ∣ 2 ^ n + 1 := uc22p22r_dvd_succ hpn
    have hrank : 2 ≤ CFSG.Open.pRank p (⊤ : Subgroup (Bar2 I)) := sp4_two_le_pRank hsp hp hdvd
    obtain ⟨Eb, -, hEbel, hEbcard⟩ :=
      CFSG.SectionRank.exists_pRank hp.one_lt (⊤ : Subgroup (Bar2 I))
    have hker : IsPGroup 2 π.ker := by
      rw [QuotientGroup.ker_mk']; exact CFSG.pCore_isPGroup
    have hdisjC : ∀ x : ↥I, π x ∈ Eb → (x : G) ∈ centralizer (V₀ : Set G) → π x = 1 := by
      intro x _ hxC
      exact MonoidHom.mem_ker.mp
        (hCker (Subgroup.mem_subgroupOf.mpr ⟨x.2, hxC⟩))
    obtain ⟨X, hXM, hXp, hXel, hXcard, hXbot⟩ :=
      exists_lift_elemAbelian_to_M D hp hp2 π hπ hker I.subtype I.subtype_injective
        (fun x => hIM x.2) hEbel hdisjC
    haveI : IsCyclic ↥X :=
      isCyclic_of_lift_disjoint_centralizer D h61 hH h.hyp.hp hXM hXp hXbot
    have hle : p ^ 2 ≤ Nat.card X := by
      rw [hXcard, hEbcard]
      exact Nat.pow_le_pow_right hp.pos hrank
    have hXnc : ¬ IsCyclic ↥X := by
      intro hc
      have hle' := CFSG.StandardType.card_le_of_isElemAbelian_of_cyclic hp hXel hc
      nlinarith [hp.two_le]
    exact hXnc inferInstance
  · intro a ha
    have haI : a ∈ I := h.hA ha
    set a' : ↥I := ⟨a, haI⟩ with ha'def
    have hmem : π a' ∈ Cs.map π := by rw [htop]; exact Subgroup.mem_top _
    obtain ⟨c, hcC, hca⟩ := hmem
    have ho : c⁻¹ * a' ∈ CFSG.pCore 2 ↥I := by
      rw [← QuotientGroup.ker_mk' (CFSG.pCore 2 ↥I)]
      change π (c⁻¹ * a') = 1
      rw [map_mul, map_inv, hca, inv_mul_cancel]
    let φ : ↥I →* ↥I ⧸ Cs := QuotientGroup.mk' Cs
    have hφc : φ c = 1 := (QuotientGroup.eq_one_iff c).mpr hcC
    have hφa : φ a' = φ (c⁻¹ * a') := by rw [map_mul, map_inv, hφc, inv_one, one_mul]
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp CFSG.pCore_isPGroup) ⟨c⁻¹ * a', ho⟩
    have h1 : orderOf (φ a') ∣ 2 ^ k := by
      rw [hφa]
      refine (orderOf_map_dvd φ _).trans ?_
      rw [← hk]
      exact dvd_of_eq (Subgroup.orderOf_coe (⟨c⁻¹ * a', ho⟩ : ↥(CFSG.pCore 2 ↥I)))
    have h2 : orderOf (φ a') ∣ Nat.card A := by
      refine (orderOf_map_dvd φ a').trans ?_
      rw [Subgroup.orderOf_mk]
      exact Subgroup.orderOf_dvd_natCard A ha
    have hcop : Nat.Coprime (Nat.card A) (2 ^ k) :=
      (Nat.coprime_two_right.mpr hAodd).pow_right k
    have h3 : orderOf (φ a') = 1 := by
      have := Nat.dvd_gcd h2 h1
      rw [Nat.Coprime.gcd_eq_one hcop] at this
      exact Nat.dvd_one.mp this
    have h4 : a' ∈ Cs := (QuotientGroup.eq_one_iff a').mp (orderOf_eq_one_iff.mp h3)
    exact (Subgroup.mem_subgroupOf.mp h4).2

theorem alt2_A_le_centralizer (D : Data G) {V₀ V : Subgroup G} {p : ℕ} {L A : Subgroup G}
    {t : G} {B : Subgroup G} {r : ℕ} (h : Ctx19_10 D V₀ V p L A t B r)
    (h61 : UC6.R6_1 D) (h127 : R127 D)
    (hI : IOf D p L = conjClosure D.M L) (hIne : conjClosure D.M L ≠ L)
    (hshape : (IsL2 (Bar2 L) (S17.nOf L) ∧
        (2 : ℤ) ^ (S17.nOf L) ≡ -1 [ZMOD (p : ℤ)]) ∨
      (IsSz (Bar2 L) (S17.nOf L) ∧
        (2 : ℤ) ^ (2 * S17.nOf L) ≡ -1 [ZMOD (p : ℤ)])) :
    A ≤ centralizer (V₀ : Set G) := by
  classical
  set M := D.M with hMdef
  set I := IOf D p L with hIdef
  set n := S17.nOf L with hndef
  have hH : F11.Hyp11 D V₀ V := Hyp125.hyp11 h127 h.hyp.hyp125
  obtain ⟨-, -, hMV₀, -⟩ := uc22p22q_hyp11_unpack D hH
  obtain ⟨hp, hp2⟩ := D.sig_prime p h.hyp.hp
  haveI : Fact p.Prime := ⟨hp⟩
  have hLM : L ≤ M := h.hyp.hL.1.1.le
  have hLcalC : L ∈ calC M := h.hyp.hL.1
  have hLsub : CFSG.Open.IsSubnormal L M := hLcalC.1
  have hLperfect : ⁅L, L⁆ = L := hLcalC.2.1
  have hLq : CFSG.Open.IsQuasisimple (Bar2 L) := hLcalC.2.2
  have hppL : p ∣ Nat.card L := h.hyp.hL.2.2
  haveI : IsSimpleGroup (Bar2 L) := by
    rcases hshape with ⟨hL2, -⟩ | ⟨hSz, -⟩
    · exact CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hL2
    · exact uc22p22r_lieModel_isSimple_twistedB2 hSz
  have hnotN : ¬ M ≤ normalizer (L : Set G) := by
    intro hN
    exact hIne (uc22p2214_conjClosure_eq_of_normal hLM
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hLM).mpr hN))
  obtain ⟨m, hmM, hmN⟩ := SetLike.not_le_iff_exists.mp hnotN
  let Lm : Subgroup G := L.map (MulAut.conj m).toMonoidHom
  have hMmap : M.map (MulAut.conj m).toMonoidHom = M :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer hmM)
  have hLmM : Lm ≤ M := by
    calc Lm = L.map (MulAut.conj m).toMonoidHom := rfl
      _ ≤ M.map (MulAut.conj m).toMonoidHom := Subgroup.map_mono hLM
      _ = M := hMmap
  have hLmcalC : Lm ∈ calC M :=
    CFSG.LocalAnalysis.UniquenessCase.UC6S846.calC_map M (MulAut.conj m) hMmap hLcalC
  have hLm_ne : Lm ≠ L := by
    intro heq
    apply hmN
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr heq
  let C : Subgroup G := M ⊓ centralizer (V₀ : Set G)
  have hCM : C ≤ M := inf_le_left
  have hCnormM : M ≤ normalizer (C : Set G) := by
    intro x hx
    exact Subgroup.inf_normalizer_le_normalizer_inf
      ⟨Subgroup.le_normalizer hx,
        CFSG.GorensteinWalter.normalizer_le_normalizer_centralizer_subgroup V₀ (hMV₀ hx)⟩
  haveI hCsub : (C.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hCM).mpr hCnormM
  let π : ↥M →* CFSG.Quasithin.OTwoQuot M := QuotientGroup.mk' (CFSG.pCore 2 ↥M)
  have hπsurj : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hker2 : IsPGroup 2 π.ker := by
    rw [QuotientGroup.ker_mk']; exact CFSG.pCore_isPGroup
  have hLbcomp : CFSG.IsComponent (CFSG.Quasithin.imageOTwoQuot M L) :=
    CFSG.Quasithin.C2Push.isComponent_imageOTwoQuot_of_isSubnormal hLsub
      (CFSG.Quasithin.E2.isQuasisimple_of_open hLq)
  have hLmbcomp : CFSG.IsComponent (CFSG.Quasithin.imageOTwoQuot M Lm) :=
    CFSG.Quasithin.C2Push.isComponent_imageOTwoQuot_of_isSubnormal hLmcalC.1
      (CFSG.Quasithin.E2.isQuasisimple_of_open hLmcalC.2.2)
  have hLbsimple : IsSimpleGroup (CFSG.Quasithin.imageOTwoQuot M L) := by
    obtain ⟨e⟩ := CFSG.Quasithin.C2Push.nonempty_mulEquiv_pCore_quotient_imageOTwoQuot hLsub
    exact MulEquiv.isSimpleGroup e.symm
  have hLmbsimple : IsSimpleGroup (CFSG.Quasithin.imageOTwoQuot M Lm) := by
    obtain ⟨e⟩ := CFSG.Quasithin.C2Push.nonempty_mulEquiv_pCore_quotient_imageOTwoQuot
      hLmcalC.1
    obtain ⟨e2⟩ := uc22p20d_bar2_conj m L
    exact MulEquiv.isSimpleGroup (e2.trans e).symm
  haveI hCbNormal : (CFSG.Quasithin.imageOTwoQuot M C).Normal := by
    have h := Subgroup.Normal.map (f := π) hCsub hπsurj
    simpa [CFSG.Quasithin.imageOTwoQuot, π] using h
  have hLb_ne : CFSG.Quasithin.imageOTwoQuot M L ≠ CFSG.Quasithin.imageOTwoQuot M Lm := by
    intro heq
    apply hLm_ne
    exact (uc22p22u_calC_ext hLcalC hLmcalC heq).symm
  have hZLb : Subgroup.center (CFSG.Quasithin.imageOTwoQuot M L) = ⊥ :=
    CFSG.Quasithin.S146zY.center_eq_bot_of_isSimpleGroup_of_isQuasisimple hLbcomp.1 hLbsimple
  have hZLmb : Subgroup.center (CFSG.Quasithin.imageOTwoQuot M Lm) = ⊥ :=
    CFSG.Quasithin.S146zY.center_eq_bot_of_isSimpleGroup_of_isQuasisimple hLmbcomp.1 hLmbsimple
  have hLbLmb_comm : ⁅CFSG.Quasithin.imageOTwoQuot M L, CFSG.Quasithin.imageOTwoQuot M Lm⁆ = ⊥ := by
    rcases CFSG.LocalCores.distinct_components_commute hLbcomp hLmbcomp with heq | hbot
    · exact absurd heq hLb_ne
    · exact hbot
  have key_C : A ≤ centralizer (V₀ : Set G) := by
    have le_C_of_image_le : ∀ (X : Subgroup G), X ≤ M → ⁅X, X⁆ = X →
        CFSG.Quasithin.imageOTwoQuot M X ≤ CFSG.Quasithin.imageOTwoQuot M C → X ≤ C := by
      intro X hXM hXperf hXle
      have hle : X ≤ C ⊔ pCoreOf 2 M := by
        intro x hx
        let x' : ↥M := ⟨x, hXM hx⟩
        have hx'' : π x' ∈ CFSG.Quasithin.imageOTwoQuot M C :=
          hXle (Subgroup.mem_map_of_mem π (Subgroup.mem_subgroupOf.mpr hx))
        obtain ⟨c, hc, hcx⟩ := Subgroup.mem_map.mp hx''
        have hmem : x' * c⁻¹ ∈ π.ker := by
          rw [MonoidHom.mem_ker, map_mul, map_inv, hcx, mul_inv_cancel]
        have hmem' : (x' * c⁻¹ : ↥M) ∈ CFSG.pCore 2 ↥M := by
          rwa [QuotientGroup.ker_mk'] at hmem
        have hmem'' : c⁻¹ * (x' * c⁻¹) * c ∈ CFSG.pCore 2 ↥M := by
          simpa using Subgroup.Normal.conj_mem CFSG.pCore_normal (x' * c⁻¹) hmem' c⁻¹
        have hsup : x' ∈ (C.subgroupOf M) ⊔ (CFSG.pCore 2 ↥M) := by
          refine Subgroup.mem_sup_of_normal_left.mpr
            ⟨c, hc, c⁻¹ * (x' * c⁻¹) * c, hmem'', ?_⟩
          group
        have hG := Subgroup.mem_map_of_mem M.subtype hsup
        rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hCM] at hG
        exact hG
      exact CFSG.Quasithin.C2Push.le_of_perfect_le_sup
        (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M)
        (fun x hx => hCnormM (Subgroup.map_subtype_le (CFSG.pCore 2 ↥M) hx)) hXperf hle
    have conj_le_C : ∀ (X : Subgroup G), X ≤ C →
        ∀ g ∈ M, X.map (MulAut.conj g).toMonoidHom ≤ C := by
      intro X hX g hg x hx
      obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
      exact (Subgroup.mem_normalizer_iff.mp (hCnormM hg) y).1 (hX hy)
    have I_le_C : L ≤ C → I ≤ C := by
      intro hL
      rw [hI]
      exact iSup₂_le fun K hK => by
        obtain ⟨g, hg, rfl⟩ := hK
        exact conj_le_C L hL g hg
    by_cases hcase : CFSG.Quasithin.imageOTwoQuot M L ≤ CFSG.Quasithin.imageOTwoQuot M C
    ·
      have hLC : L ≤ C := le_C_of_image_le L hLM hLperfect hcase
      exact h.hA.trans ((I_le_C hLC).trans inf_le_right)
    ·
      have hcommL : ⁅CFSG.Quasithin.imageOTwoQuot M L, CFSG.Quasithin.imageOTwoQuot M C⁆ = ⊥ := by
        rcases CFSG.LocalCores.component_normal_subgroup hLbcomp hCbNormal with hle | hbot
        · exact absurd hle hcase
        · exact hbot
      by_cases hcase' : CFSG.Quasithin.imageOTwoQuot M Lm ≤ CFSG.Quasithin.imageOTwoQuot M C
      ·
        have hLmC : Lm ≤ C := le_C_of_image_le Lm hLmM hLmcalC.2.1 hcase'
        have hL_eq : L = Lm.map (MulAut.conj m⁻¹).toMonoidHom := by
          rw [show Lm = L.map (MulAut.conj m).toMonoidHom from rfl, Subgroup.map_map]
          congr 1
          ext x
          simp [MulAut.conj_apply, mul_assoc]
        have hLC : L ≤ C := by
          rw [hL_eq]
          calc Lm.map (MulAut.conj m⁻¹).toMonoidHom
              ≤ C.map (MulAut.conj m⁻¹).toMonoidHom := Subgroup.map_mono hLmC
            _ = C := Subgroup.mem_normalizer_iff_map_conj_eq.mp (hCnormM (M.inv_mem hmM))
        exact h.hA.trans ((I_le_C hLC).trans inf_le_right)
      ·
        exfalso
        have hcommLm : ⁅CFSG.Quasithin.imageOTwoQuot M Lm,
            CFSG.Quasithin.imageOTwoQuot M C⁆ = ⊥ := by
          rcases CFSG.LocalCores.component_normal_subgroup hLmbcomp hCbNormal with hle | hbot
          · exact absurd hle hcase'
          · exact hbot
        have hCb_bot : CFSG.Quasithin.imageOTwoQuot M C ⊓
            (CFSG.Quasithin.imageOTwoQuot M L ⊔ CFSG.Quasithin.imageOTwoQuot M Lm) = ⊥ := by
          have hcommLLm : ∀ a ∈ CFSG.Quasithin.imageOTwoQuot M L,
              ∀ b ∈ CFSG.Quasithin.imageOTwoQuot M Lm, a * b = b * a := by
            intro a ha b hb
            exact (Subgroup.mem_centralizer_iff.mp
              (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hLbLmb_comm ha) b hb).symm
          have hnorm_m : CFSG.Quasithin.imageOTwoQuot M Lm ≤
              Subgroup.normalizer (CFSG.Quasithin.imageOTwoQuot M L : Set _) := by
            have hcentral : CFSG.Quasithin.imageOTwoQuot M Lm ≤
                Subgroup.centralizer (CFSG.Quasithin.imageOTwoQuot M L : Set _) := by
              intro x hx
              rw [Subgroup.mem_centralizer_iff]
              intro y hy
              exact hcommLLm y hy x hx
            exact hcentral.trans (Subgroup.centralizer_le_normalizer _)
          have hPmul := Subgroup.coe_mul_of_right_le_normalizer_left
            (CFSG.Quasithin.imageOTwoQuot M L) (CFSG.Quasithin.imageOTwoQuot M Lm) hnorm_m
          have hmemP : ∀ {y : CFSG.Quasithin.OTwoQuot M},
              y ∈ (CFSG.Quasithin.imageOTwoQuot M L ⊔ CFSG.Quasithin.imageOTwoQuot M Lm) →
              ∃ a ∈ CFSG.Quasithin.imageOTwoQuot M L,
                ∃ b ∈ CFSG.Quasithin.imageOTwoQuot M Lm, a * b = y := by
            intro y hy
            have hy' : y ∈ ((CFSG.Quasithin.imageOTwoQuot M L ⊔
                CFSG.Quasithin.imageOTwoQuot M Lm :
                  Subgroup (CFSG.Quasithin.OTwoQuot M)) : Set _) := hy
            rw [hPmul] at hy'
            simpa only [Set.mem_mul, SetLike.mem_coe] using hy'
          rw [eq_bot_iff]
          intro z hz
          have hzP : z ∈ (CFSG.Quasithin.imageOTwoQuot M L ⊔
              CFSG.Quasithin.imageOTwoQuot M Lm) := hz.2
          have hzc : ∀ l ∈ (CFSG.Quasithin.imageOTwoQuot M L ⊔
              CFSG.Quasithin.imageOTwoQuot M Lm), z * l = l * z := by
            intro l hl
            obtain ⟨a, ha, b, hb, rfl⟩ := hmemP hl
            have hcommLC : ⁅CFSG.Quasithin.imageOTwoQuot M C,
                CFSG.Quasithin.imageOTwoQuot M L⁆ = ⊥ := by
              rw [Subgroup.commutator_comm]; exact hcommL
            have hcommLmC : ⁅CFSG.Quasithin.imageOTwoQuot M C,
                CFSG.Quasithin.imageOTwoQuot M Lm⁆ = ⊥ := by
              rw [Subgroup.commutator_comm]; exact hcommLm
            have hza : z * a = a * z :=
              (Subgroup.mem_centralizer_iff.mp
                (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcommLC hz.1) a ha).symm
            have hzb : z * b = b * z :=
              (Subgroup.mem_centralizer_iff.mp
                (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcommLmC hz.1) b hb).symm
            calc z * (a * b) = (z * a) * b := by group
              _ = (a * z) * b := by rw [hza]
              _ = a * (z * b) := by group
              _ = a * (b * z) := by rw [hzb]
              _ = (a * b) * z := by group
          have center_eq_one : ∀ {Y : Subgroup (CFSG.Quasithin.OTwoQuot M)},
              Subgroup.center Y = ⊥ → ∀ g ∈ Y,
                (∀ l ∈ Y, g * l = l * g) → g = 1 := by
            intro Y hZY g hg hcent
            have hmem : (⟨g, hg⟩ : ↥Y) ∈ Subgroup.center Y := by
              rw [Subgroup.mem_center_iff]
              intro l
              apply Subtype.ext
              exact (hcent (l : CFSG.Quasithin.OTwoQuot M) l.2).symm
            rw [hZY] at hmem
            exact congrArg Subtype.val (Subgroup.mem_bot.mp hmem)
          have hz1 : z = 1 :=
            CFSG.Quasithin.S14110.center_sup_eq_one (center_eq_one hZLb)
              (center_eq_one hZLmb) hcommLLm z hzP hzc
          exact Subgroup.mem_bot.mpr hz1
        have hpLb : p ∣ Nat.card (CFSG.Quasithin.imageOTwoQuot M L) := by
          obtain ⟨e⟩ := CFSG.Quasithin.C2Push.nonempty_mulEquiv_pCore_quotient_imageOTwoQuot hLsub
          rw [← Nat.card_congr e.toEquiv]
          exact CFSG.Quasithin.QA19.dvd_card_oTwoQuot_of_dvd_card
            (hp.odd_of_ne_two hp2) hppL
        have hpLmb : p ∣ Nat.card (CFSG.Quasithin.imageOTwoQuot M Lm) := by
          have hcardLm : Nat.card Lm = Nat.card L :=
            Subgroup.card_map_of_injective (MulAut.conj m).injective
          obtain ⟨e⟩ := CFSG.Quasithin.C2Push.nonempty_mulEquiv_pCore_quotient_imageOTwoQuot
            hLmcalC.1
          rw [← Nat.card_congr e.toEquiv]
          exact CFSG.Quasithin.QA19.dvd_card_oTwoQuot_of_dvd_card
            (hp.odd_of_ne_two hp2) (hcardLm.symm ▸ hppL)
        obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card'
          (G := ↥(CFSG.Quasithin.imageOTwoQuot M L)) p hpLb
        obtain ⟨v, hv⟩ := exists_prime_orderOf_dvd_card'
          (G := ↥(CFSG.Quasithin.imageOTwoQuot M Lm)) p hpLmb
        let F : Subgroup (CFSG.Quasithin.OTwoQuot M) :=
          Subgroup.zpowers (u : CFSG.Quasithin.OTwoQuot M)
        let F' : Subgroup (CFSG.Quasithin.OTwoQuot M) :=
          Subgroup.zpowers (v : CFSG.Quasithin.OTwoQuot M)
        have hF_le : F ≤ CFSG.Quasithin.imageOTwoQuot M L := Subgroup.zpowers_le.mpr u.2
        have hF'_le : F' ≤ CFSG.Quasithin.imageOTwoQuot M Lm := Subgroup.zpowers_le.mpr v.2
        have hF_card : Nat.card F = p := by
          rw [show F = Subgroup.zpowers (u : CFSG.Quasithin.OTwoQuot M) from rfl, Nat.card_zpowers,
            Subgroup.orderOf_coe, hu]
        have hF_comm : ∀ a ∈ F, ∀ b ∈ F', a * b = b * a := by
          intro a ha b hb
          have h1 : a ∈ CFSG.Quasithin.imageOTwoQuot M L := hF_le ha
          have h2 : b ∈ CFSG.Quasithin.imageOTwoQuot M Lm := hF'_le hb
          have hc := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hLbLmb_comm
          exact (Subgroup.mem_centralizer_iff.mp (hc h1) b h2).symm
        have hF_disj : F ⊓ F' = ⊥ := by
          rw [eq_bot_iff]
          intro x hx
          have hxL : x ∈ CFSG.Quasithin.imageOTwoQuot M L := hF_le hx.1
          have hxL' : x ∈ CFSG.Quasithin.imageOTwoQuot M Lm := hF'_le hx.2
          have hxZ : (⟨x, hxL⟩ : ↥(CFSG.Quasithin.imageOTwoQuot M L)) ∈
              Subgroup.center (CFSG.Quasithin.imageOTwoQuot M L) := by
            rw [Subgroup.mem_center_iff]
            intro y
            apply Subtype.ext
            have hc : CFSG.Quasithin.imageOTwoQuot M Lm ≤
                Subgroup.centralizer (CFSG.Quasithin.imageOTwoQuot M L : Set _) :=
              Subgroup.commutator_eq_bot_iff_le_centralizer.mp
                (by rw [Subgroup.commutator_comm]; exact hLbLmb_comm)
            exact Subgroup.mem_centralizer_iff.mp (hc hxL') (y : CFSG.Quasithin.OTwoQuot M) y.2
          rw [hZLb] at hxZ
          exact Subgroup.mem_bot.mpr (congrArg Subtype.val (Subgroup.mem_bot.mp hxZ))
        have hvord : orderOf (v : CFSG.Quasithin.OTwoQuot M) = p := by
          rw [Subgroup.orderOf_coe, hv]
        have hvF : (v : CFSG.Quasithin.OTwoQuot M) ∉ F := by
          intro hvF
          have hmem : (v : CFSG.Quasithin.OTwoQuot M) ∈ F ⊓ F' :=
            ⟨hvF, Subgroup.mem_zpowers _⟩
          rw [hF_disj] at hmem
          have hv1 : (v : CFSG.Quasithin.OTwoQuot M) = 1 := Subgroup.mem_bot.mp hmem
          have h1 : orderOf (v : CFSG.Quasithin.OTwoQuot M) = 1 := orderOf_eq_one_iff.mpr hv1
          rw [hvord] at h1
          exact hp.ne_one h1
        obtain ⟨hE2el, hE2card⟩ :=
          CFSG.GroupTheory.isElemAbelian_sup_zpowers_of_commute (r := p) hF_card hvord hvF
            (fun a ha => hF_comm a ha (v : CFSG.Quasithin.OTwoQuot M) (Subgroup.mem_zpowers _))
        let E2 : Subgroup (CFSG.Quasithin.OTwoQuot M) := F ⊔ F'
        have hE2_el : IsElemAbelian p E2 := hE2el
        have hE2_card : Nat.card E2 = p ^ 2 := hE2card
        have hE2_sub : (F ⊔ F') ≤
            CFSG.Quasithin.imageOTwoQuot M L ⊔ CFSG.Quasithin.imageOTwoQuot M Lm :=
          sup_le (hF_le.trans le_sup_left) (hF'_le.trans le_sup_right)
        have hE2_p : IsPGroup p E2 := hE2_el.isPGroup
        have hdisjC : ∀ x : ↥M, π x ∈ E2 → (x : G) ∈ centralizer (V₀ : Set G) → π x = 1 := by
          intro x hxE hxC
          have hCmem : x ∈ C.subgroupOf M := Subgroup.mem_subgroupOf.mpr ⟨x.2, hxC⟩
          have hpi : π x ∈ CFSG.Quasithin.imageOTwoQuot M C :=
            Subgroup.mem_map_of_mem π hCmem
          have hbot : π x ∈ CFSG.Quasithin.imageOTwoQuot M C ⊓
              (CFSG.Quasithin.imageOTwoQuot M L ⊔ CFSG.Quasithin.imageOTwoQuot M Lm) :=
            ⟨hpi, hE2_sub hxE⟩
          rw [hCb_bot] at hbot
          exact Subgroup.mem_bot.mp hbot
        obtain ⟨Xg, hXgM, hXgp, hXgel, hXgcard, hXbot⟩ :=
          exists_lift_elemAbelian_to_M D hp hp2 π hπsurj hker2 M.subtype
            M.subtype_injective (fun x => x.2) hE2_el hdisjC
        have hXgcard' : Nat.card Xg = p ^ 2 := by rw [hXgcard, hE2_card]
        haveI : IsCyclic ↥Xg :=
          isCyclic_of_lift_disjoint_centralizer D h61 hH h.hyp.hp hXgM hXgp hXbot
        have hXnc : ¬ IsCyclic ↥Xg := uc22p22u_not_isCyclic_of_card_sq hp hXgel hXgcard'
        exact hXnc inferInstance
  exact key_C

theorem nineteen_twentytwo (D : Data G) {V₀ V : Subgroup G} {p : ℕ} {L A : Subgroup G}
    {t : G} {B : Subgroup G} {r : ℕ} (h : Ctx19_10 D V₀ V p L A t B r)
    (h61 : UC6.R6_1 D) (h127 : R127 D)
    (h171 : S17.R17_1At D V₀ V h.hyp.hyp125)
    (h12 : R19_12At D V₀ V p L A t B r h)
    (hgapP : ∀ (E : Subgroup G), Gap19_22_P D V₀ V p L A t B r h E)
    (hgap : Gap19_22 D V₀ V p L A t B r h) :
    R19_22At D V₀ V p L A t B r h := by
  classical
  have hr : r.Prime := h.hr.1
  haveI : Fact r.Prime := ⟨hr⟩
  have hV0ne : V₀ ≠ ⊥ := ne_bot_of_one_lt_mSub h.hyp.big
  have hAM : A ≤ D.M := A_le_M_of_ctx19_10 D h
  obtain ⟨E, hEA, hEel, hEcard⟩ :=
    exists_isElemAbelian_card_prime_sq_of_isZModSq h.hAcard hr h.hr.2
  have hEm : E ≤ D.M := hEA.trans hAM
  have hEp : IsPGroup r E := CFSG.Open.IsElemAbelian.isPGroup hEel
  have hEpow : ∀ x ∈ E, x ^ r = 1 := hEel.2
  have hAodd : Odd (Nat.card A) := odd_card_of_ctx19_10 h
  have hr2 : r ≠ 2 := by
    intro h2
    have h2dvd : 2 ∣ Nat.card A := h2 ▸ h.hr.2
    exact (Nat.not_even_iff_odd.mpr hAodd) (even_iff_two_dvd.mpr h2dvd)
  have hEnc : ¬ IsCyclic ↥E := uc22p22u_not_isCyclic_of_card_sq hr hEel hEcard
  have hnotP : ¬ F11.InP11 D E := by
    rcases h171 with ⟨-, hsecond⟩
    by_cases hex : ∃ X : Subgroup G, F11.InP11 D X
    · exact fun _ => hV0ne (hsecond hex).1
    · exact fun hE => hex ⟨E, hE⟩
  have hgamma : ¬ rankThreeGamma 1 r E ≤ D.M := by
    intro hle
    apply hnotP
    obtain ⟨hperm, hstrong | hP⟩ := hgapP E hEA hEel hEcard
    · exact ⟨r, hr, hr2, hEm, hEp, hEpow, hEnc, hperm, hle, Or.inl hstrong⟩
    · obtain ⟨P, hPsyl, hEP, hPN⟩ := hP
      exact ⟨r, hr, hr2, hEm, hEp, hEpow, hEnc, hperm, hle,
        Or.inr ⟨E, hEnc, ⟨P, hPsyl, hEP, hPN⟩, hle⟩⟩
  unfold rankThreeGamma GLBCore at hgamma
  obtain ⟨Q, hQE, hQrank, hQN⟩ :
      ∃ Q : Subgroup G, Q ≤ E ∧ 1 ≤ CFSG.Open.pRank (G := G) r Q ∧
        ¬ normalizer (Q : Set G) ≤ D.M := by
    by_contra hcon
    apply hgamma
    refine sSup_le ?_
    rintro N ⟨Q, hQE, hQrank, rfl⟩
    by_contra hNM
    exact hcon ⟨Q, hQE, hQrank, hNM⟩
  have hQ_ne : Q ≠ ⊥ := uc22p22qv_ne_bot_of_pRank hr hQrank
  have hQ_ne_E : Q ≠ E := by
    intro hQeq
    apply hQN
    rw [hQeq]
    exact CFSG.LocalAnalysis.RankThreeUC.normalizer_le_of_mem_uniqueSet D.maxLocal
      (h12 E hEA hEel hEcard)
  have hQcard : Nat.card Q = r :=
    CFSG.GroupTheory.card_eq_prime_of_le_of_card_eq_sq (q := r) hQE hEcard hQ_ne hQ_ne_E
  have hQcyc : IsCyclic ↥Q := isCyclic_of_prime_card hQcard
  have hcent : ¬ centralizer (Q : Set G) ≤ D.M :=
    not_centralizer_le_of_not_normalizer_le h (hQE.trans hEA) hEA hEel hEcard h12 hQN
  have hQA : Q ≤ A := hQE.trans hEA
  have hVQ : V₀ ≤ centralizer (Q : Set G) := by
    have key : ∀ (X : Subgroup G), X ≤ A → A ≤ centralizer (V₀ : Set G) →
        V₀ ≤ centralizer (X : Set G) := by
      intro X hXA hAC
      have h1 : V₀ ≤ centralizer (A : Set G) := Subgroup.le_centralizer_iff.mp hAC
      exact h1.trans (Subgroup.centralizer_le hXA)
    rcases h.h1910.2 with h1 | h2 | h3
    · obtain ⟨hsp, -, -, hpn⟩ := h1
      exact key Q hQA (alt1_A_le_centralizer D h h61 h127 hsp hpn)
    · exact key Q hQA (alt2_A_le_centralizer D h h61 h127 h2.1 h2.2.1 h2.2.2.2)
    · exact hgap h3.1 Q hQA hQcard hQcyc hcent
  exact ⟨Q, h, hQA, hQcard, hQcyc, hcent, hVQ⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19
