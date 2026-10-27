module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S217U3A
public import CFSG.LocalAnalysis.UniquenessCase.UC22S217U3B8Main
public import CFSG.LocalAnalysis.UniquenessCase.UC22S21b
public import CFSG.LocalAnalysis.UniquenessCase.UCFront08UseS5
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.Defs
import CFSG.LocalAnalysis.UniquenessCase.UCKPFI3
import CFSG.LocalAnalysis.UniquenessCase.UCKPCenter
import CFSG.LocalAnalysis.UniquenessCase.UCKPSyl3
import CFSG.LocalAnalysis.UniquenessCase.UCKP1
import CFSG.LocalAnalysis.UniquenessCase.UC22P21a
import CFSG.LocalAnalysis.UniquenessCase.UC22P21d
import CFSG.LocalAnalysis.UniquenessCase.UC22P2214c
import CFSG.LocalAnalysis.UniquenessCase.UC22P22uc
import CFSG.LocalAnalysis.UniquenessCase.UC22P22rj
import CFSG.LocalAnalysis.UniquenessCase.UC22P20p
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Fourteen1c
public import CFSG.LocalAnalysis.UniquenessCase.UC22Bridge
public import CFSG.LocalAnalysis.UniquenessCase.UC22P2214a
import CFSG.Adapters.StatedClassicalSmallOrders
import CFSG.ClassicalInvolution.Models.SymplecticPairs.Quadruple
import CFSG.ClassicalInvolution.QuaternionStructure
import CFSG.ClassicalInvolution.WeakCT.Main
import CFSG.GH74.GLS.Defs
import CFSG.GH74.GLS.Stage1.Thm3.Sec5.Closed
import CFSG.GH74.GLS.Stage1.Thm3.Sec5.Statements
import CFSG.GH74.GLS.Stage1.Thm6.Sec12.Defs
import CFSG.GH74.GLS.Stage1.Thm6.Sec12.Ext
import CFSG.GH74.GLS.Stage2.Final.LayerFDerive
import CFSG.LieType.CurtisTits.Adjoint
import CFSG.LieType.Ree.LargeReeEightTorus
import CFSG.LieType.Ree.LargeReeInvolutionTwoCentralizers
import CFSG.LocalAnalysis.ComponentClassification.CatLeafOddB
import CFSG.LocalAnalysis.ComponentClassification.ExcSelectorEvenE6
import CFSG.LocalAnalysis.ComponentClassification.ExcSelectorEvenTriality
import CFSG.LocalAnalysis.ComponentClassification.ExcSelectorOddE6
import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeMax
import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalOddCentralizer
import CFSG.LocalAnalysis.ComponentInitial.GL3TwoFixedModelCases
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyBasic
import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdentLieAlt
import CFSG.LocalAnalysis.SeitzReduction.CrossCharInputs
import CFSG.LocalAnalysis.SeitzReduction.E6PilotHR4
import CFSG.LocalAnalysis.SeitzReduction.E6PilotLeviPerp
import CFSG.LocalAnalysis.SeitzReduction.E8PilotQ2PositionWork
import CFSG.LocalAnalysis.SeitzReduction.E8PilotSwapLift
import CFSG.LocalAnalysis.SeitzReduction.EPilotEndGraphE6
import CFSG.LocalAnalysis.SeitzReduction.EPilotEndGraphTwistedXi
import CFSG.LocalAnalysis.SeitzReduction.F4PilotCatEvenClassical
import CFSG.LocalAnalysis.SeitzReduction.F4PilotCatSporadic
import CFSG.LocalAnalysis.SeitzReduction.F4PilotEndField
import CFSG.LocalAnalysis.SeitzReduction.F4PilotFieldNeighbourFix
import CFSG.LocalAnalysis.SeitzReduction.F4PilotFieldNeighbourLift
import CFSG.LocalAnalysis.SeitzReduction.F4PilotInnerField
import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveWSmall
import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveWSylow
import CFSG.LocalAnalysis.SeitzReduction.LinearPilotSwapFactorNormalGraph
import CFSG.LocalAnalysis.SeitzReduction.LinearPilotTwistedFusion
import CFSG.LocalAnalysis.SeitzReduction.RankOneBranches
import CFSG.LocalAnalysis.SeitzReduction.RankOneCatSL2TwoFixedA5
import CFSG.LocalAnalysis.SeitzReduction.RankOneHypStarU3
import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotAlignImagesSwap
import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotUniqueTypeGraph
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Fourteen1
import CFSG.RankThree.Chevalley.SteinbergCEF4EvenQPlusWeyl
import CFSG.RankThree.Chevalley.SteinbergCFEvenF4PointwiseInner
import CFSG.RankThree.Classical.SteinbergBJSymplecticSquareZeroCentralizer
import CFSG.RankThree.PartTwo.Census.Classical.EvenUnitary

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC6S846
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7 (Conclusion76)

variable {G : Type} [Group G] [Finite G]

theorem uc22s217u3a_rank (hCen : UCK.U3Center) {M K₀ K₁ : Subgroup G} (hK₀ : K₀ ∈ calC M)
    (hK₁ : K₁ ∈ calC M) (hne : K₀ ≠ K₁) {n : ℕ} (hn : IsPowTwo n) (hX₀ : IsSU3 (Bar2 K₀) n)
    (hX₁ : IsSU3 (Bar2 K₁) n) {r : ℕ} (hr : r.Prime) (hr5 : 5 ≤ r) (hrq : 2 ^ n % r = 1)
    {q : ℕ} (hq : q.Prime) (hq3 : 3 < q) (hqn : q ∣ 2 ^ n + 1) {y : G} (hyM : y ∈ M)
    (hyr : orderOf y = r) (hy₀ : y ∈ normalizer (K₀ : Set G))
    (hy₁ : y ∈ normalizer (K₁ : Set G)) :
    ∃ W : Subgroup G, W ≤ M ⊓ centralizer (zpowers y : Set G) ∧ IsElemAbelian q W ∧
      Nat.card W = q ^ 2 := by
  have hr2 : r ≠ 2 := by omega
  have hr3 : r ≠ 3 := by omega
  have hq2 : q ≠ 2 := by omega
  obtain ⟨hα₀r, hα₀⟩ := uc22s217u3a_inner hX₀ hn hr hr2 hr3 hy₀ hyr
  obtain ⟨hα₁r, hα₁⟩ := uc22s217u3a_inner hX₁ hn hr hr2 hr3 hy₁ hyr
  obtain ⟨z₀, hz₀o, hz₀⟩ := uc22s217u3a_fix hCen hX₀ hr hr2 hr3 hrq hα₀r hα₀ hq hq3 hqn
  obtain ⟨z₁, hz₁o, hz₁⟩ := uc22s217u3a_fix hCen hX₁ hr hr2 hr3 hrq hα₁r hα₁ hq hq3 hqn
  obtain ⟨A₀, hA₀K, hA₀c, hA₀q⟩ := uc22s217u3b_lift_elem hr hr2 hq hq2 hy₀ hyr hz₀o hz₀
  obtain ⟨A₁, hA₁K, hA₁c, hA₁q⟩ := uc22s217u3b_lift_elem hr hr2 hq hq2 hy₁ hyr hz₁o hz₁
  have hZ : ¬ q ∣ Nat.card (center (Bar2 K₀)) := fun h => by
    have := Nat.le_of_dvd (by norm_num) (h.trans (hCen _ n hX₀))
    omega
  exact uc22s217u3b_two_cent hK₀ hK₁ hne hr hr2 hq hq2 hZ hyM hyr hA₀K hA₁K hA₀c hA₁c hA₀q hA₁q

theorem uc22s217u3a_not_mem_or {M K₀ K₁ : Subgroup G} (hK₀ : K₀ ∈ calC M) (hK₁ : K₁ ∈ calC M)
    (hne : K₀ ≠ K₁) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (hZr : ¬ r ∣ Nat.card (center (Bar2 K₀))) {x : G} (hxM : x ∈ M) (hxr : orderOf x = r) :
    x ∉ K₀ ∨ x ∉ K₁ := by
  by_contra h
  push Not at h
  have hxc : Nat.card (zpowers x) = r := by rw [Nat.card_zpowers, hxr]
  have hxne : zpowers x ≠ ⊥ := fun h => by
    rw [h, Subgroup.card_bot] at hxc
    exact hr.ne_one hxc.symm
  obtain ⟨hsn₀, hp₀, hqs₀, hcen₀⟩ := calC_subgroupOf hK₀
  obtain ⟨hsn₁, hp₁, hqs₁, -⟩ := calC_subgroupOf hK₁
  have hK₀M : K₀ ≤ M := hK₀.1.le
  have hK₁M : K₁ ≤ M := hK₁.1.le
  have hne' : K₀.subgroupOf M ≠ K₁.subgroupOf M := by
    intro he
    apply hne
    have := congrArg (Subgroup.map M.subtype) he
    rwa [Subgroup.map_subgroupOf_eq_of_le hK₀M, Subgroup.map_subgroupOf_eq_of_le hK₁M] at this
  have hbot := UC6S898.eq_bot_of_le_inf (A := K₀.subgroupOf M) (A' := K₁.subgroupOf M)
    (E := (zpowers x).subgroupOf M) hr hr2 hsn₀ hp₀ hqs₀ hsn₁ hp₁ hqs₁ hne'
    (by rw [hcen₀]; exact hZr)
    (fun w hw => (Subgroup.zpowers_le.2 h.1) hw) (fun w hw => (Subgroup.zpowers_le.2 h.2) hw)
    ((UC6S898.isElemAbelian_of_card_prime hr hxc).subgroupOf M)
  apply hxne
  have := congrArg (Subgroup.map M.subtype) hbot
  rwa [Subgroup.map_subgroupOf_eq_of_le (Subgroup.zpowers_le.2 hxM), Subgroup.map_bot] at this

theorem uc22s217u3a_normalizer_le (D : Data G) (hCen : UCK.U3Center) {K₀ K₁ : Subgroup G}
    (hK₀ : K₀ ∈ calC D.M) (hK₁ : K₁ ∈ calC D.M) (hne : K₀ ≠ K₁) {n : ℕ} (hn : IsPowTwo n)
    (hX₀ : IsSU3 (Bar2 K₀) n) (hX₁ : IsSU3 (Bar2 K₁) n) {r : ℕ} (hr : r.Prime) (hr5 : 5 ≤ r)
    (hrq : 2 ^ n % r = 1) {q : ℕ} (hq : q.Prime) (hq3 : 3 < q) (hqn : q ∣ 2 ^ n + 1)
    (h76 : Conclusion76 D.M q) {X₀ : Subgroup G} (hX₀K : X₀ ≤ K₀) (hX₀c : Nat.card X₀ = r)
    {x : G} (hxM : x ∈ D.M) (hxr : orderOf x = r) (hxK : x ∉ K₀)
    (hx₀ : x ∈ normalizer (K₀ : Set G)) (hx₁ : x ∈ normalizer (K₁ : Set G)) :
    normalizer (zpowers x : Set G) ≤ D.M := by
  classical
  have hr2 : r ≠ 2 := by omega
  have hr3 : r ≠ 3 := by omega
  have hq2 : q ≠ 2 := by omega
  have hxc : Nat.card (zpowers x) = r := by rw [Nat.card_zpowers, hxr]
  obtain ⟨hα₀r, hα₀⟩ := uc22s217u3a_inner hX₀ hn hr hr2 hr3 hx₀ hxr
  have hZ3 : ∀ z ∈ center (Bar2 K₀), z ^ 3 = 1 := fun z hz =>
    UCK.pow_three_eq_one_of_mem_center (hCen (Bar2 K₀) n hX₀) hz
  obtain ⟨A, hAK, hAc, hAr⟩ :=
    uc22s217u3b_exists_partner hr (by omega) hZ3 hX₀K hX₀c hx₀ hxr hα₀r hα₀
  obtain ⟨hEel, hEc⟩ := uc22s217u3b_sup_elemAbelian hr hxr hxK hAK hAc hAr
  have hEM : zpowers x ⊔ A ≤ D.M := sup_le (Subgroup.zpowers_le.2 hxM) (hAK.trans hK₀.1.le)
  obtain ⟨hα₁r, hα₁⟩ := uc22s217u3a_inner hX₁ hn hr hr2 hr3 hx₁ hxr
  obtain ⟨z, hzo, hz⟩ := uc22s217u3a_fix hCen hX₁ hr hr2 hr3 hrq hα₁r hα₁ hq hq3 hqn
  obtain ⟨Q, hQK, hQc, hQq⟩ :=
    uc22s217u3b_exists_cent_sup hK₀ hK₁ hne hr hr2 hq hq2 hx₁ hzo hz hAK hEel.isPGroup
  have h6 : 0 < CFSG.Open.pRank q (D.M ⊓ centralizer ((zpowers x ⊔ A : Subgroup G) : Set G)) :=
    lt_of_lt_of_le Nat.zero_lt_one (le_pRank' (k := 1) hq (le_inf (hQK.trans hK₁.1.le) hQc)
      (UC6S898.isElemAbelian_of_card_prime hq hQq) (by rw [hQq, pow_one]))
  have hEN : zpowers x ⊔ A ≤ normalizer (K₀ : Set G) ⊓ normalizer (K₁ : Set G) :=
    sup_le (Subgroup.zpowers_le.2 (Subgroup.mem_inf.2 ⟨hx₀, hx₁⟩))
      (le_inf (hAK.trans Subgroup.le_normalizer)
        (hAK.trans (PartTwo.calC_le_normalizer_of_ne hK₁ hK₀ hne.symm)))
  have h7 : ∀ X : Subgroup G, X ≤ zpowers x ⊔ A → Nat.card X = r →
      1 < CFSG.Open.pRank q (D.M ⊓ normalizer (X : Set G)) := by
    intro X hXE hXc
    obtain ⟨y, hyX, hyr, hgen⟩ := UC6S898.exists_generator hr hXc
    have hXy : X = zpowers y := le_antisymm (fun w hw => by
        obtain ⟨k, rfl⟩ := hgen w hw
        exact Subgroup.pow_mem _ (Subgroup.mem_zpowers y) k)
      (Subgroup.zpowers_le.2 hyX)
    subst hXy
    have hyE := hXE (Subgroup.mem_zpowers y)
    have hyN := Subgroup.mem_inf.1 (hEN hyE)
    obtain ⟨W, hWle, hWel, hWc⟩ := uc22s217u3a_rank hCen hK₀ hK₁ hne hn hX₀ hX₁ hr hr5 hrq hq
      hq3 hqn (hEM hyE) hyr hyN.1 hyN.2
    have h2 := le_pRank' hq (hWle.trans (inf_le_inf_left _ (centralizer_le_normalizer _))) hWel hWc
    omega
  have hΓ := h76 r hr _ hEM hEel hEc h6 h7
  exact (UC6S898.normalizer_le_gamma le_sup_left hr (UC6S898.isElemAbelian_of_card_prime hr hxc)
    hxc).trans hΓ

theorem uc22s217u3a_false_of_four_dvd (D : Data G) (Ch : Choice2011 G) (h5 : S21_5 D Ch)
    (hH : H1930 D) (c : Ctx21 D Ch) (hc4 : 4 ∣ c.n) (hCen : UCK.U3Center) {L : Subgroup G}
    (hL : L ∈ calC D.M) (hnN : ¬ (L.subgroupOf D.M).Normal) {n : ℕ} (hn : IsPowTwo n)
    (hn4 : 4 ∣ n) (hX : IsSU3 (Bar2 L) n) {q : ℕ} (hq : q.Prime) (hq3 : 3 < q)
    (hqn : q ∣ 2 ^ n + 1) (h76 : Conclusion76 D.M q) : False := by
  classical
  have h5p : (5 : ℕ).Prime := by norm_num
  haveI : Fact (5 : ℕ).Prime := ⟨h5p⟩
  have h5B : 5 ∣ Nat.card c.B0 := by
    have hmod := uc22s217u3a_two_pow_mod_five hc4
    have : 5 ∈ piSet c.B0 := by
      rw [c.hpi]
      exact ⟨h5p, by omega⟩
    exact this.2
  obtain ⟨b, hb⟩ := exists_prime_orderOf_dvd_card' 5 h5B
  have hbB : (b : G) ∈ c.B0 := b.2
  have hbM : (b : G) ∈ D.M := c.hBM hbB
  have hbr : orderOf (b : G) = 5 := by rw [Subgroup.orderOf_coe, hb]
  have hbN : ∀ K ∈ calC D.M, (b : G) ∈ normalizer (K : Set G) := fun K hK =>
    h5 hH { c with B := c.B0, hB := c.hB0, hle := le_rfl } K hK hbB
  have hLM : L ≤ D.M := hL.1.le
  have hnN' : ¬ D.M ≤ normalizer (L : Set G) := fun h =>
    hnN ((Subgroup.normal_subgroupOf_iff_le_normalizer hLM).2 h)
  obtain ⟨m, hmM, hmN⟩ := SetLike.not_le_iff_exists.1 hnN'
  let f : MulAut G := MulAut.conj m
  have hMf : D.M.map f.toMonoidHom = D.M :=
    UC6S846.mem_normalizer_iff_map_conj.1 (Subgroup.le_normalizer hmM)
  have hL' : L.map f.toMonoidHom ∈ calC D.M := calC_map D.M f hMf hL
  have hne : L ≠ L.map f.toMonoidHom := fun he =>
    hmN (UC6S846.mem_normalizer_iff_map_conj.2 he.symm)
  have hX' : IsSU3 (Bar2 (L.map f.toMonoidHom)) n :=
    uc22p20p_isSU3_of_mulEquiv
      (bar2Equiv (Subgroup.equivMapOfInjective L f.toMonoidHom f.injective)) hX
  have hrq : 2 ^ n % 5 = 1 := uc22s217u3a_two_pow_mod_five hn4
  have h5n : 5 ∣ (2 ^ n) ^ 2 - 1 := by
    have h1 : (2 ^ n) ^ 2 % 5 = 1 := by
      rw [Nat.pow_mod, hrq]
    omega
  obtain ⟨X₀, hX₀L, hX₀c⟩ := uc22s217u3a_exists_card_eq hX h5p (by norm_num) h5n
  have hX₀L' : X₀.map f.toMonoidHom ≤ L.map f.toMonoidHom := Subgroup.map_mono hX₀L
  have hX₀c' : Nat.card (X₀.map f.toMonoidHom) = 5 := by
    rw [Subgroup.card_map_of_injective f.injective, hX₀c]
  have hZ5 : ¬ 5 ∣ Nat.card (center (Bar2 L)) := fun h => by
    have := Nat.le_of_dvd (by norm_num) (h.trans (hCen _ n hX))
    omega
  have hNb : normalizer (zpowers (b : G) : Set G) ≤ D.M := by
    rcases uc22s217u3a_not_mem_or hL hL' hne h5p (by norm_num) hZ5 hbM hbr with hbK | hbK
    · exact uc22s217u3a_normalizer_le D hCen hL hL' hne hn hX hX' h5p le_rfl hrq hq hq3 hqn h76
        hX₀L hX₀c hbM hbr hbK (hbN L hL) (hbN _ hL')
    · exact uc22s217u3a_normalizer_le D hCen hL' hL hne.symm hn hX' hX h5p le_rfl hrq hq hq3 hqn
        h76 hX₀L' hX₀c' hbM hbr hbK (hbN _ hL') (hbN L hL)
  exact s21_2 D Ch hH { c with B := c.B0, hB := c.hB0, hle := le_rfl } (zpowers (b : G))
    (Subgroup.zpowers_le.2 hbB) hNb

theorem uc22s217u3a_false_of_not_isPowTwo (D : Data G) (Ch : Choice2011 G) (h5 : S21_5 D Ch)
    (hH : H1930 D) (c : Ctx21 D Ch) (hc : ¬ IsPowTwo c.n) (hc0 : c.n ≠ 0)
    (hCen : UCK.U3Center) (h869 : F08.R869NS5 D) {L : Subgroup G} (hL : L ∈ calC D.M)
    {n : ℕ} (hn : IsPowTwo n) (hX : IsSU3 (Bar2 L) n) {q : ℕ} (hqσ : q ∈ D.sig)
    (h2q : 2 ≤ CFSG.Open.pRank q (conjClosure D.M L))
    (h5q : q = 5 → 2 ^ 12 ∣ Nat.card (Bar2 (conjClosure D.M L))) : False := by
  classical
  obtain ⟨s, r, hs, hsn, hr, hrs, -⟩ := uc22s217u3b_exists_sr hc0 hc
  haveI : Fact r.Prime := ⟨hr⟩
  have hr5 : 5 ≤ r := UC6S898.prime_ne_two_three_of_dvd hr hs hrs
  have hr2 : r ≠ 2 := by omega
  have hrB : r ∣ Nat.card c.B0 := by
    have hmod : 2 ^ c.n % r = 1 := UCK.two_pow_mod_eq_one hr hrs hsn
    have : r ∈ piSet c.B0 := by
      rw [c.hpi]
      exact ⟨hr, Nat.dvd_of_mod_eq_zero (Nat.sub_mod_eq_zero_of_mod_eq
        (by rw [hmod, Nat.mod_eq_of_lt hr.one_lt]))⟩
    exact this.2
  obtain ⟨b, hb⟩ := exists_prime_orderOf_dvd_card' r hrB
  have hbB : (b : G) ∈ c.B0 := b.2
  have hbM : (b : G) ∈ D.M := c.hBM hbB
  have hbr : orderOf (b : G) = r := by rw [Subgroup.orderOf_coe, hb]
  have hrn := uc22s217u3a_not_dvd_card hn hs hr hrs
  have hcb : ∀ K ∈ conjSetOf D.M L, CentralizesBar (b : G) K := by
    intro K hK
    have hKC := uc22p2214_calC_of_mem_conjSetOf hL hK
    have hbK : (b : G) ∈ normalizer (K : Set G) :=
      h5 hH { c with B := c.B0, hB := c.hB0, hle := le_rfl } K hKC hbB
    obtain ⟨g, -, rfl⟩ := hK
    have hXK : IsSU3 (Bar2 (L.map (MulAut.conj g).toMonoidHom)) n :=
      uc22p20p_isSU3_of_mulEquiv (bar2Equiv (Subgroup.equivMapOfInjective L
        (MulAut.conj g).toMonoidHom (MulAut.conj g).injective)) hX
    exact uc22s217u3a_centralizesBar hCen hXK hn hr hr5 hrn hbK hbr
  obtain ⟨hXM, hMX, hprod⟩ := uc22p22u_conjClosure_isProd le_rfl Subgroup.le_normalizer hL
  have hbX : CentralizesBar (b : G) (conjClosure D.M L) := by
    refine uc22p2214_centralizesBar_conjClosure (hMX hbM) fun K hK k hk => ?_
    have hKC := uc22p2214_calC_of_mem_conjSetOf hL hK
    have h1 : (b : G) * k * (b : G)⁻¹ * k⁻¹ ∈ pCoreOf 2 D.M :=
      uc22p22r_pCoreOf_le_of_isSubnormal hKC.1 ((hcb K hK).2 k hk)
    have hkX : k ∈ conjClosure D.M L := uc22s217u3a_le_conjClosure hK hk
    have h2 : (b : G) * k * (b : G)⁻¹ * k⁻¹ ∈ conjClosure D.M L :=
      (conjClosure D.M L).mul_mem ((mem_normalizer_iff.1 (hMX hbM) k).1 hkX)
        ((conjClosure D.M L).inv_mem hkX)
    exact uc22p2214_pCoreOf_inf_le hXM ⟨h1, h2⟩
  have hbc : Nat.card (zpowers (b : G)) = r := by rw [Nat.card_zpowers, hbr]
  have hXQ := uc22p21d_sup_pCore_eq hr hr2 hbc fun g hg =>
    uc22p21d_centralizesBar_of_mem_zpowers hbX hg
  have hAB : zpowers (b : G) ≤ c.B0 := Subgroup.zpowers_le.2 hbB
  exact s21_2 D Ch hH { c with B := c.B0, hB := c.hB0, hle := le_rfl } (zpowers (b : G)) hAB
    (h869 _ hXM hMX hprod ⟨q, hqσ, h2q, h5q⟩ r hr hr2 (zpowers (b : G)) (hAB.trans c.hBM) hbc hXQ)

theorem uc22s217u3a_not_isSU3_of_griess (hG : CFSG.Open.GriessAllModelsStatement) (D : Data G)
    (Ch : Choice2011 G) (h5 : S21_5 D Ch) (hH : H1930 D) (c : Ctx21 D Ch) (hcn : 3 ≤ c.n)
    (hSg : SigmaStd D) (h76 : ∀ p ∈ D.sig, IsStronglyPEmbedded p D.M → Conclusion76 D.M p)
    (h869 : F08.R869NS5 D) {L : Subgroup G} (hL : L ∈ calC D.M)
    (hnN : ¬ (L.subgroupOf D.M).Normal) {n : ℕ} (hn : IsPowTwo n) : ¬ IsSU3 (Bar2 L) n := by
  intro hX
  have hCen := UCK.u3Center_of_griess hG
  have hSyl := UCK.u3Syl_of_griess hG
  have hn2 : 2 ≤ n := UCK.u3Range (Bar2 L) n hX
  have hn3 : n ≠ 3 := by
    rcases uc22s217u3a_pow_two_cases hn hn2 with h | h <;> omega
  obtain ⟨q, hq, hq3, hqn⟩ := UC6S898.exists_prime_gt_three_dvd hn2 hn3
  obtain ⟨hqσ, hsp, h2q⟩ := uc22s217u3a_sig D hSg hCen hSyl hL hnN hX hq hq3 hqn
  by_cases hc : IsPowTwo c.n
  · have hc4 : 4 ∣ c.n := (uc22s217u3a_pow_two_cases hc (by omega)).resolve_left (by omega)
    rcases uc22s217u3a_pow_two_cases hn hn2 with h2 | h4
    ·
      subst h2
      have hq5 : q = 5 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).1 (by simpa using hqn)
      subst hq5
      have hmod := uc22s217u3a_two_pow_mod_five hc4
      exact uc22s217u3a_false_of_sp D Ch hH c hq (by omega) hsp
    ·
      exact uc22s217u3a_false_of_four_dvd D Ch h5 hH c hc4 hCen hL hnN hn h4 hX hq hq3 hqn
        (h76 q hqσ hsp)
  ·
    have h5q : q = 5 → 2 ^ 12 ∣ Nat.card (Bar2 (conjClosure D.M L)) := by
      rintro rfl
      obtain rfl := uc22s217u3a_eq_two_of_five_dvd hn hn2 hqn
      exact uc22s217u3a_two_pow_twelve_dvd hCen hL hnN hX
    exact uc22s217u3a_false_of_not_isPowTwo D Ch h5 hH c hc (by omega) hCen h869 hL hn hX hqσ h2q
      h5q

theorem s21_17R_one_pow_of_griess (hG : CFSG.Open.GriessAllModelsStatement) (D : Data G)
    (Ch : Choice2011 G) (h5 : S21_5 D Ch) (hn3 : H1930 D → ∀ c : Ctx21 D Ch, 3 ≤ c.n)
    (hSg : SigmaStd D) (h76 : ∀ p ∈ D.sig, IsStronglyPEmbedded p D.M → Conclusion76 D.M p)
    (h869 : F08.R869NS5 D) :
    H1930 D → ∀ c : Ctx21 D Ch, ∀ L ∈ calC D.M, ¬ (L.subgroupOf D.M).Normal →
      ∀ n : ℕ, IsPowTwo n → ¬ IsSU3 (Bar2 L) n :=
  fun hH c _ hL hnN _ hn =>
    uc22s217u3a_not_isSU3_of_griess hG D Ch h5 hH c (hn3 hH c) hSg h76 h869 hL hnN hn

end CFSG.LocalAnalysis.UniquenessCase.UC22
