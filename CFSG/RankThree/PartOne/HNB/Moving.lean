module

public import CFSG.RankThree.PartOne.HNB.RankFour
public import CFSG.RankThree.PartOne.S11.FivePlusInner
public import CFSG.Assembly.CatalogTransport
import CFSG.RankThree.PartOne.S10.AmbientTheta
import CFSG.RankThree.GroupTheory.SteinbergBMVanishingFullPerfectSupplement
import CFSG.RankThree.PartOne.S11.FivePlus
public import CFSG.RankThree.PartOne.HNB.Envelope
public import CFSG.RankThree.PartOne.S10.SectionTenNodesUnconditional
public import CFSG.RankThree.PartOne.S11.TwoActionWiring

public section

namespace CFSG.RankThree.PartOne.HNB

open Subgroup CFSG CFSG.RankThree CFSG.RankThree.GroupTheory CFSG.RankThree.LocalRank
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)
open CFSG.Assembly (InCatalog)
open scoped Pointwise commutatorElement

namespace Actor

variable {G : Type} [Group G] {A L : Subgroup G} (a : Actor G A L)

theorem R_commutator_A0 [Finite G] : ⁅a.R, a.A0⁆ = a.R := by
  apply le_antisymm
  · exact Subgroup.le_normalizer_iff_commutator_le_left.mp a.A0_le_normalizer_R
  · calc a.R = ⁅a.R, Subgroup.zpowers a.c⁆ := a.R_commutator_self.symm
      _ ≤ ⁅a.R, a.A0⁆ := Subgroup.commutator_mono le_rfl (Subgroup.zpowers_le.mpr a.c_mem_A0)

theorem A0_le_normalizer_K : a.A0 ≤ Subgroup.normalizer (a.K : Set G) :=
  sup_le (Subgroup.le_centralizer_iff.mp a.K_le_centralizer_B |>.trans
      (Subgroup.centralizer_le_normalizer _))
    (Subgroup.zpowers_le.mpr (Subgroup.le_normalizer a.y_mem_K))

theorem exists_move [Finite G] (h : SteinbergBM.SectionTenSetup G 5 A) :
    ∃ k ∈ a.K, ∃ r ∈ a.R,
      r * k * r⁻¹ * k⁻¹ ∉ inSubgroup (aschbacherSolvableCore 5) a.H := by
  by_contra hcon
  push Not at hcon
  apply a.commutator_K_R_not_le_theta h
  refine Subgroup.commutator_le.mpr fun k hk r hr => ?_
  have h1 := hcon k hk r hr
  have e : ⁅k, r⁆ = (r * k * r⁻¹ * k⁻¹)⁻¹ := by
    rw [commutatorElement_def]
    group
  rw [e]
  exact Subgroup.inv_mem _ h1

end Actor

namespace Successor

variable {G : Type} [Group G] {A L : Subgroup G} {a : Actor G A L} (s : Successor a)

@[expose] def X' : Subgroup G := s.X.map a.H.subtype

theorem X'_le_H : s.X' ≤ a.H := Subgroup.map_subtype_le _

theorem mem_X'_iff {g : G} : g ∈ s.X' ↔ ∃ hg : g ∈ a.H, (⟨g, hg⟩ : a.H) ∈ s.X := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x.2, hx⟩
  · rintro ⟨hg, hx⟩
    exact ⟨⟨g, hg⟩, hx, rfl⟩

theorem K_le_X' : a.K ≤ s.X' := fun _ hk =>
  s.mem_X'_iff.mpr ⟨a.K_le_H hk, s.hKX (Subgroup.mem_subgroupOf.mpr hk)⟩

theorem X'_subgroupOf : s.X'.subgroupOf a.H = s.X :=
  Subgroup.comap_map_eq_self_of_injective a.H.subtype_injective s.X

theorem X'_mem : s.X' ∈ thetaComponentsAt 5 a.b :=
  mem_thetaComponentsAt_iff.mpr ⟨s.X'_le_H, by rw [s.X'_subgroupOf]; exact s.hX⟩

theorem theta_X' [Finite G] : inSubgroup (aschbacherSolvableCore 5) s.X' =
    s.X' ⊓ inSubgroup (aschbacherSolvableCore 5) a.H :=
  theta_eq_inf_of_mem_thetaComponentsAt (by norm_num) s.X'_mem

theorem le_normalizer_X' {M : Subgroup a.H} (hM : M ≤ Subgroup.normalizer (s.X : Set a.H)) :
    M.map a.H.subtype ≤ Subgroup.normalizer (s.X' : Set G) := by
  rintro _ ⟨m, hm, rfl⟩
  exact Subgroup.le_normalizer_map a.H.subtype ⟨m, hM hm, rfl⟩

theorem A0_le_normalizer' [Finite G] (h : SteinbergBM.SectionTenSetup G 5 A) :
    a.A0 ≤ Subgroup.normalizer (s.X' : Set G) := by
  have := s.le_normalizer_X' (s.A0_le_normalizer h)
  rwa [Subgroup.map_subgroupOf_eq_of_le a.A0_le_H] at this

theorem R_le_normalizer' [Finite G] (h : SteinbergBM.SectionTenSetup G 5 A) :
    a.R ≤ Subgroup.normalizer (s.X' : Set G) := by
  have := s.le_normalizer_X' (s.R_le_normalizer h)
  rwa [Subgroup.map_subgroupOf_eq_of_le a.R_le_H] at this

theorem conj_kernel {n g : G} (hn : n ∈ Subgroup.normalizer (s.X' : Set G))
    (hg : g ∈ thetaQuotientCentralizer 5 ⊤ s.X') :
    n * g * n⁻¹ ∈ thetaQuotientCentralizer 5 ⊤ s.X' := by
  obtain ⟨-, hgN, hgk⟩ := mem_thetaQuotientCentralizer_iff.mp hg
  have h1 : thetaQuotientConj 5 s.X' ⟨g, hgN⟩ = 1 :=
    (thetaQuotientConj_eq_one_iff 5 _ ⟨g, hgN⟩).mpr hgk
  have hngN : n * g * n⁻¹ ∈ Subgroup.normalizer (s.X' : Set G) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ hn hgN) (Subgroup.inv_mem _ hn)
  refine mem_thetaQuotientCentralizer_iff.mpr ⟨Subgroup.mem_top _, hngN,
    (thetaQuotientConj_eq_one_iff 5 _ ⟨n * g * n⁻¹, hngN⟩).mp ?_⟩
  have e : (⟨n * g * n⁻¹, hngN⟩ : Subgroup.normalizer (s.X' : Set G)) =
      ⟨n, hn⟩ * ⟨g, hgN⟩ * ⟨n, hn⟩⁻¹ := rfl
  rw [e, map_mul, map_mul, h1, mul_one, map_inv, mul_inv_cancel]

theorem R_le_kernel [Finite G] (h : SteinbergBM.SectionTenSetup G 5 A)
    (hc : a.c ∈ thetaQuotientCentralizer 5 ⊤ s.X') :
    a.R ≤ thetaQuotientCentralizer 5 ⊤ s.X' := by
  calc a.R = ⁅a.R, Subgroup.zpowers a.c⁆ := a.R_commutator_self.symm
    _ ≤ thetaQuotientCentralizer 5 ⊤ s.X' := by
      refine Subgroup.commutator_le.mpr fun r hr g hg => ?_
      have hg' : g ∈ thetaQuotientCentralizer 5 ⊤ s.X' := (Subgroup.zpowers_le.mpr hc) hg
      have hrN : r ∈ Subgroup.normalizer (s.X' : Set G) := s.R_le_normalizer' h hr
      have e : ⁅r, g⁆ = (r * g * r⁻¹) * g⁻¹ := commutatorElement_def r g
      rw [e]
      exact Subgroup.mul_mem _ (s.conj_kernel hrN hg') (Subgroup.inv_mem _ hg')

theorem c_not_mem_kernel [Finite G] (h : SteinbergBM.SectionTenSetup G 5 A) :
    a.c ∉ thetaQuotientCentralizer 5 ⊤ s.X' := by
  intro hc
  have hR := s.R_le_kernel h hc
  obtain ⟨k, hk, r, hr, hmove⟩ := a.exists_move h
  have h1 := mem_thetaQuotientCentralizer_iff.mp (hR hr)
  have h2 := h1.2.2 k (s.K_le_X' hk)
  rw [s.theta_X'] at h2
  exact hmove h2.2

theorem K_inf_theta [Finite G] : a.K ⊓ inSubgroup (aschbacherSolvableCore 5) s.X' = ⊥ := by
  set T := inSubgroup (aschbacherSolvableCore 5) s.X' with hT
  obtain ⟨hTle, hTn⟩ := theta_le_and_normal (G := G) 5 s.X'
  have hXT : s.X' ≤ Subgroup.normalizer (T : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hTle).mp hTn
  have hsolv : Group.IsSolvable T := (theta_solvable_and_not_dvd (by norm_num) s.X').1
  have hKX : a.K ≤ s.X' := s.K_le_X'
  have hnormK : (T.subgroupOf a.K).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have := (Subgroup.mem_normalizer_iff.mp (hXT (hKX g.2)) (n : G)).mp hn
    simpa using this
  let f : T.subgroupOf a.K →* T :=
    { toFun := fun x => ⟨(x : a.K), Subgroup.mem_subgroupOf.mp x.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hfinj : Function.Injective f := fun x y hxy => by
    have := congrArg Subtype.val hxy
    exact Subtype.ext (Subtype.ext this)
  have hsolv' : Group.IsSolvable (T.subgroupOf a.K) :=
    Group.isSolvable_of_isSolvable_injective hfinj
  have : IsSimpleGroup a.K := a.N.hKsimple
  have hbot : T.subgroupOf a.K = ⊥ :=
    SteinbergBM.eq_bot_of_normal_of_isSolvable_of_isSimpleGroup a.N.hKnonab _ hsolv'
  rw [eq_bot_iff]
  intro g hg
  rw [Subgroup.mem_bot]
  have hmem : (⟨g, hg.1⟩ : a.K) ∈ T.subgroupOf a.K := Subgroup.mem_subgroupOf.mpr hg.2
  rw [hbot, Subgroup.mem_bot] at hmem
  exact congrArg Subtype.val hmem

theorem C_le_B [Finite G] : thetaQuotientCentralizer 5 a.A0 s.X' ≤ a.B := by
  intro g hg
  obtain ⟨hgA, hgN, hgk⟩ := mem_thetaQuotientCentralizer_iff.mp hg
  refine a.centralizer_K_inf_A0_le_B hgA fun k hk => ?_
  have h1 := hgk k (s.K_le_X' hk)
  have hgK : g * k * g⁻¹ ∈ a.K :=
    (Subgroup.mem_normalizer_iff.mp (a.A0_le_normalizer_K hgA) k).mp hk
  have hm : g * k * g⁻¹ * k⁻¹ ∈ a.K ⊓ inSubgroup (aschbacherSolvableCore 5) s.X' :=
    ⟨Subgroup.mul_mem _ hgK (Subgroup.inv_mem _ hk), h1⟩
  rw [s.K_inf_theta, Subgroup.mem_bot] at hm
  calc g * k = g * k * g⁻¹ * k⁻¹ * (k * g) := by group
    _ = k * g := by rw [hm, one_mul]

theorem card_C_le [Finite G] (h : SteinbergBM.SectionTenSetup G 5 A) :
    Nat.card (thetaQuotientCentralizer 5 a.A0 s.X') ≤ 5 := by
  have hCB := s.C_le_B
  have hdvd := Subgroup.card_dvd_of_le hCB
  rw [a.card_B] at hdvd
  have hne : thetaQuotientCentralizer 5 a.A0 s.X' ≠ a.B := by
    intro heq
    apply s.c_not_mem_kernel h
    have hc : a.c ∈ thetaQuotientCentralizer 5 a.A0 s.X' := heq ▸ a.c_mem_B
    obtain ⟨-, hcN, hck⟩ := mem_thetaQuotientCentralizer_iff.mp hc
    exact mem_thetaQuotientCentralizer_iff.mpr ⟨Subgroup.mem_top _, hcN, hck⟩
  have hne25 : Nat.card (thetaQuotientCentralizer 5 a.A0 s.X') ≠ 25 := by
    intro h25
    apply hne
    exact Subgroup.eq_of_le_of_card_ge hCB (by rw [h25, a.card_B])
  have h25 : (25 : ℕ) = 5 ^ 2 := by norm_num
  rw [h25] at hdvd hne25
  obtain ⟨i, hi, hci⟩ := (Nat.dvd_prime_pow (by norm_num : Nat.Prime 5)).mp hdvd
  interval_cases i
  · omega
  · omega
  · exact absurd hci hne25

theorem theta_X_le [Finite G] :
    inSubgroup (aschbacherSolvableCore 5) s.X ≤ aschbacherSolvableCore 5 a.H := by
  unfold inSubgroup
  rw [s.theta_eq, Subgroup.subgroupOf_map_subtype]
  exact inf_le_left

theorem mem_sectionTenZero [Finite G]
    (hbridge : CFSG.Assembly.CatalogImp InCatalog CFSG.Blueprint.Catalog)
    (hK : CatalogPrimeTwoAutomorphismsInner) (h : SteinbergBM.SectionTenSetup G 5 A) :
    s.X' ∈ sectionTenZero 5 a.A0 := by
  have hp : Nat.Prime 5 := by norm_num
  have hKP : CFSG.IsKProper G := h.2.2.1
  have hAL := s.A0_le_normalizer h
  have hQL := s.R_le_normalizer h
  have hA0e : IsElementaryAbelian 5 a.A0 := a.isElementaryAbelian_A0
  have hA : IsPGroup 5 (a.A0.subgroupOf a.H) :=
    (IsElementaryAbelian.isPGroup 5 a.A0).comap_subtype
  have hQ2 : IsPGroup 2 (a.R.subgroupOf a.H) := a.R_isPGroup.comap_subtype
  have hAQ : a.A0.subgroupOf a.H ≤ Subgroup.normalizer ((a.R.subgroupOf a.H : Subgroup a.H) :
      Set a.H) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro g
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    exact Subgroup.mem_normalizer_iff.mp
      (a.A0_le_normalizer_R (Subgroup.mem_subgroupOf.mp hx)) (g : G)
  have hQA : ⁅a.R.subgroupOf a.H, a.A0.subgroupOf a.H⁆ = a.R.subgroupOf a.H := by
    apply Subgroup.map_injective a.H.subtype_injective
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le a.R_le_H,
      Subgroup.map_subgroupOf_eq_of_le a.A0_le_H]
    exact a.R_commutator_A0
  have hLq := s.hX.2.2
  have hcat : CFSG.Blueprint.Catalog ((s.X ⧸ aschbacherSolvableCore 5 s.X) ⧸
      Subgroup.center (s.X ⧸ aschbacherSolvableCore 5 s.X)) := by
    have : IsSimpleGroup ((s.X ⧸ aschbacherSolvableCore 5 s.X) ⧸
        Subgroup.center (s.X ⧸ aschbacherSolvableCore 5 s.X)) := hLq.2.1
    exact hbridge _ hLq.2.2 (inCatalog_quotient_center_of_thetaComponent hKP (a.H_ne_top h) hLq)
  have hmove : ∃ q : a.R.subgroupOf a.H, thetaQuotientAction 5 hQL q ≠ 1 := by
    obtain ⟨k, hk, r, hr, hmv⟩ := a.exists_move h
    refine ⟨⟨⟨r, a.R_le_H hr⟩, Subgroup.mem_subgroupOf.mpr hr⟩, fun h1 => hmv ?_⟩
    have h2 : thetaQuotientConj 5 s.X
        ⟨⟨r, a.R_le_H hr⟩, hQL (Subgroup.mem_subgroupOf.mpr hr)⟩ = 1 := h1
    rw [thetaQuotientConj_eq_one_iff] at h2
    have h3 := h2 ⟨k, a.K_le_H hk⟩ (s.hKX (Subgroup.mem_subgroupOf.mpr hk))
    have h4 := s.theta_X_le h3
    exact ⟨_, h4, rfl⟩
  obtain ⟨T, hTX, hT1, hT2, hAT, hTA⟩ := exists_two_commutator_in_thetaComponent hp
    (by norm_num) hK hAL hQL hA hQ2 hAQ hQA hLq hcat hmove
  refine ⟨mem_thetaComponentFamily_iff.mpr ⟨a.b, a.b_mem_A0, a.b_ne_one, s.X'_mem⟩,
    T.map a.H.subtype, Subgroup.map_mono hTX, ?_, hT2.map _, ?_, ?_⟩
  · intro hbot
    exact hT1 ((Subgroup.map_eq_bot_iff_of_injective T a.H.subtype_injective).mp hbot)
  · intro g hg
    have hgH : g ∈ a.H := a.A0_le_H hg
    exact Subgroup.le_normalizer_map a.H.subtype
      ⟨⟨g, hgH⟩, hAT (Subgroup.mem_subgroupOf.mpr hg), rfl⟩
  · have := congrArg (Subgroup.map a.H.subtype) hTA
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le a.A0_le_H] at this
    exact this.symm

theorem isQuasisimple_X' [Finite G]
    (hbridge : CFSG.Assembly.CatalogImp InCatalog CFSG.Blueprint.Catalog)
    (hK : CatalogPrimeTwoAutomorphismsInner) (h : SteinbergBM.SectionTenSetup G 5 A) :
    CFSG.IsQuasisimple s.X' := by
  by_contra hnq
  have hF0 := s.mem_sectionTenZero hbridge hK h
  have hyp := nonquasisimple_moving_theta_component_scalar_kernel_hyperplane twoActionInputs_of_S9
    G 5 a.A0 (a.sectionTen_A0 h) s.X' hF0 hnq
  have hrel := hyp.2.1
  set C := thetaQuotientCentralizer 5 a.A0 s.X' with hC
  have hCA : C ≤ a.A0 := inf_le_left
  have hcardC : Nat.card (C.subgroupOf a.A0) = Nat.card C :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCA).toEquiv
  have hmul := Subgroup.card_mul_index (C.subgroupOf a.A0)
  rw [hcardC, a.card_A0] at hmul
  have hidx : (C.subgroupOf a.A0).index = 5 := hrel
  rw [hidx] at hmul
  have h5 : Nat.card C ≤ 5 := s.card_C_le h
  norm_num at hmul
  omega

theorem isQuasisimple_X [Finite G]
    (hbridge : CFSG.Assembly.CatalogImp InCatalog CFSG.Blueprint.Catalog)
    (hK : CatalogPrimeTwoAutomorphismsInner) (h : SteinbergBM.SectionTenSetup G 5 A) :
    CFSG.IsQuasisimple s.X :=
  LocalCores.isQuasisimple_of_mulEquiv
    (s.X.equivMapOfInjective a.H.subtype a.H.subtype_injective).symm
    (s.isQuasisimple_X' hbridge hK h)

end Successor

end CFSG.RankThree.PartOne.HNB
