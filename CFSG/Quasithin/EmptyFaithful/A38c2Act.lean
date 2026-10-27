module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246A7Y
public import CFSG.Quasithin.EmptyFaithful.S146C2
public import CFSG.LocalAnalysis.SectionRank.Ccomm.ElementaryAut
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyLinearBinary
public import CFSG.Quasithin.Vol2.Ch10SecA1012Five
public import CFSG.CGT.Timmesfeld75.L2Pair
public import CFSG.CGT.Timmesfeld75.ListWCBasic
public import CFSG.Certificates.Kernel.LocalCompTits.Span
public import CFSG.ClassicalGroups
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCorePrimeCore
public import CFSG.LocalAnalysis.ComponentInitial.SuzukiModelSchreier
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListA7Iso
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L122AProved
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporSimpleTop
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeListed
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.Equivariance
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesBorel
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiModelPointStructure
public import CFSG.Quasithin.Background.A3Structure318Red
public import CFSG.Quasithin.Background.A3Structure36A
public import CFSG.Quasithin.Background.A3Structure36BBase
public import CFSG.Quasithin.Background.A3Structure36BPrimeDataBase
public import CFSG.Quasithin.Background.A3Structure36Base
public import CFSG.Quasithin.Background.B1More13A
public import CFSG.Quasithin.Background.B1More13Defs
public import CFSG.Quasithin.Background.B1MoreEleven
public import CFSG.Quasithin.Background.B4Dual
public import CFSG.Quasithin.Background.B4ModelsAction
public import CFSG.Quasithin.Background.B5CompA
public import CFSG.Quasithin.Background.B5CompB
public import CFSG.Quasithin.Background.F6Amalgams
public import CFSG.Quasithin.Background.F6SolvableQuotient
public import CFSG.Quasithin.Background.F9G2
public import CFSG.Quasithin.Background.InternalSecB51
public import CFSG.Quasithin.Background.InternalSecFF
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtJ4LocCheck
public import CFSG.Quasithin.EmptyFaithful.S1417Sylow
public import CFSG.Quasithin.EmptyFaithful.S1421L246
public import CFSG.Quasithin.EmptyFaithful.S143Pre
public import CFSG.Quasithin.EmptyFaithful.S146C1
public import CFSG.Quasithin.EmptyFaithful.S146G4
public import CFSG.Quasithin.EmptyFaithful.S146ThreeB
public import CFSG.Quasithin.Vol2.Ch10SecA1012Three
public import CFSG.Quasithin.Vol2.Ch10SecA1012Two
public import CFSG.Quasithin.Vol2.Ch10StatementsE
public import CFSG.Quasithin.Vol2.Ch1Faithful
public import CFSG.RankThree.Asc83Table.PermTables
public import CFSG.Sporadic.Schreier.M11
public import CFSG.Sporadic.Schreier.M22
public import CFSG.StronglyEmbedded.ParityCriterion
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CPrime
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.DihedralAut
public import CFSG.Walter.J1
public import Certificates.Data.CFSGNative.MonsterB.Rep4371Model
public import Certificates.Kernel.J4Count.FixCE
public import Certificates.Kernel.J4Count.FixCPairBase1
public import Certificates.Kernel.J4Count.KFactsBase

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.L246A7
open scoped commutatorElement

section QuotAct

variable {K A : Type*} [Group K] [Group A]

theorem actOnQuot_map_eq (N : Subgroup A) (θ : K →* MulAut A)
    (h : ∀ k a, a ∈ N → θ k a ∈ N) (k : K) :
    Subgroup.map ((θ k : A ≃* A) : A →* A) N = N := by
  refine le_antisymm ?_ ?_
  · rintro _ ⟨a, ha, rfl⟩
    exact h k a ha
  · intro x hx
    refine ⟨θ k⁻¹ x, h k⁻¹ x hx, ?_⟩
    show θ k (θ k⁻¹ x) = x
    rw [map_inv]
    simp

noncomputable def actOnQuot (N : Subgroup A) [N.Normal] (θ : K →* MulAut A)
    (h : ∀ k a, a ∈ N → θ k a ∈ N) : K →* MulAut (A ⧸ N) where
  toFun k := QuotientGroup.congr N N (θ k) (actOnQuot_map_eq N θ h k)
  map_one' := by
    ext q
    induction q using QuotientGroup.induction_on with
    | H a => simp [QuotientGroup.congr_mk]
  map_mul' k₁ k₂ := by
    ext q
    induction q using QuotientGroup.induction_on with
    | H a => simp [QuotientGroup.congr_mk]

theorem actOnQuot_mk (N : Subgroup A) [N.Normal] (θ : K →* MulAut A)
    (h : ∀ k a, a ∈ N → θ k a ∈ N) (k : K) (a : A) :
    actOnQuot N θ h k (QuotientGroup.mk a) = QuotientGroup.mk (θ k a) := by
  simp [actOnQuot, QuotientGroup.congr_mk]

end QuotAct

section Block

variable {G : Type} [Group G] {L : Subgroup G}

theorem blockU_le_block_self (L : Subgroup G) : blockU L ≤ L := by
  rw [blockU, Subgroup.commutator_le]
  intro q hq l hl
  have hqL : q ∈ L := CFSG.LieType.BorelTits.pCoreOf_le 2 L hq
  rw [commutatorElement_def]
  exact L.mul_mem (L.mul_mem (L.mul_mem hqL hl) (L.inv_mem hqL)) (L.inv_mem hl)

theorem blockZ_subgroupOf_le_center_blockU (L : Subgroup G) :
    (blockZ L).subgroupOf (blockU L) ≤ Subgroup.center (blockU L) := by
  intro z hz
  rw [Subgroup.mem_center_iff]
  intro u
  apply Subtype.ext
  exact Subgroup.mem_centralizer_iff.mp (Subgroup.mem_subgroupOf.mp hz).2 u
    (blockU_le_block_self L u.2)

instance instNormalBlockZsubU (L : Subgroup G) : ((blockZ L).subgroupOf (blockU L)).Normal :=
  ⟨fun z hz u => by
    rw [Subgroup.mem_center_iff.mp (blockZ_subgroupOf_le_center_blockU L hz) u, mul_inv_cancel_right]
    exact hz⟩

abbrev tildeUL (L : Subgroup G) : Type := ↥(blockU L) ⧸ (blockZ L).subgroupOf (blockU L)

theorem actN_mem_blockZ_subgroupOf (g : ↥(Subgroup.normalizer (L : Set G))) {u : ↥(blockU L)}
    (hu : u ∈ (blockZ L).subgroupOf (blockU L)) :
    actN L g u ∈ (blockZ L).subgroupOf (blockU L) := by
  rw [Subgroup.mem_subgroupOf] at hu ⊢
  have h1 : ((actN L g u : ↥(blockU L)) : G) ∈ blockU L := (actN L g u).2
  rw [actN_coe] at h1 ⊢
  refine ⟨h1, Subgroup.mem_centralizer_iff.mpr fun l hl => ?_⟩
  have hl' : (g : G)⁻¹ * l * (g : G)⁻¹⁻¹ ∈ L :=
    (Subgroup.mem_normalizer_iff.mp (inv_mem g.2) l).mp hl
  have hc := Subgroup.mem_centralizer_iff.mp hu.2 _ hl'
  calc l * ((g : G) * (u : G) * (g : G)⁻¹)
      = (g : G) * (((g : G)⁻¹ * l * (g : G)⁻¹⁻¹) * (u : G)) * (g : G)⁻¹ := by group
    _ = (g : G) * ((u : G) * ((g : G)⁻¹ * l * (g : G)⁻¹⁻¹)) * (g : G)⁻¹ := by rw [hc]
    _ = (g : G) * (u : G) * (g : G)⁻¹ * l := by group

noncomputable def tildeUAct (L : Subgroup G) :
    ↥(Subgroup.normalizer (L : Set G)) →* MulAut (tildeUL L) :=
  actOnQuot _ (actN L) fun _ _ hu => actN_mem_blockZ_subgroupOf _ hu

theorem tildeUAct_mk (g : ↥(Subgroup.normalizer (L : Set G))) (u : ↥(blockU L)) :
    tildeUAct L g (QuotientGroup.mk u) = QuotientGroup.mk (actN L g u) :=
  actOnQuot_mk _ _ _ _ _

theorem tildeUAct_eq_one_of_mem_blockQ (hL : IsShort2 L) (q : ↥(Subgroup.normalizer (L : Set G)))
    (hq : (q : G) ∈ blockQ L) : tildeUAct L q = 1 := by
  ext w
  induction w using QuotientGroup.induction_on with
  | H u =>
    rw [tildeUAct_mk, MulAut.one_apply]
    congr 1
    apply Subtype.ext
    rw [actN_coe]
    have := C1.blockU_comm hL (u : G) u.2 (q : G) hq
    rw [← this]
    group

theorem mem_blockZ_of_tildeUAct_eq_one {g : ↥(Subgroup.normalizer (L : Set G))} (hg : tildeUAct L g = 1)
    {u : G} (hu : u ∈ blockU L) : ((g : G) * u * (g : G)⁻¹)⁻¹ * u ∈ blockZ L := by
  have h1 : tildeUAct L g (QuotientGroup.mk ⟨u, hu⟩) = QuotientGroup.mk ⟨u, hu⟩ := by
    rw [hg, MulAut.one_apply]
  rw [tildeUAct_mk, QuotientGroup.eq] at h1
  have h2 := Subgroup.mem_subgroupOf.mp h1
  simpa [actN_coe] using h2

theorem normalizerL_le_normalizer_blockZ : Subgroup.normalizer (L : Set G) ≤
    Subgroup.normalizer (blockZ L : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro z
  have key : ∀ g ∈ Subgroup.normalizer (L : Set G), ∀ z ∈ blockZ L, g * z * g⁻¹ ∈ blockZ L := by
    intro g hg z hz
    exact ⟨(Subgroup.mem_normalizer_iff.mp (C1.mem_normalizer_blockU hg) z).mp hz.1,
      Subgroup.mem_centralizer_iff.mpr fun l hl => by
        have hl' : g⁻¹ * l * g⁻¹⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp (inv_mem hg) l).mp hl
        have hc := Subgroup.mem_centralizer_iff.mp hz.2 _ hl'
        calc l * (g * z * g⁻¹) = g * ((g⁻¹ * l * g⁻¹⁻¹) * z) * g⁻¹ := by group
          _ = g * (z * (g⁻¹ * l * g⁻¹⁻¹)) * g⁻¹ := by rw [hc]
          _ = g * z * g⁻¹ * l := by group⟩
  refine ⟨fun hz => key g hg z hz, fun hz => ?_⟩
  have h1 := key g⁻¹ (inv_mem hg) _ hz
  have e : g⁻¹ * (g * z * g⁻¹) * g⁻¹⁻¹ = z := by group
  rwa [e] at h1

end Block

section NC

variable {G : Type} [Group G]

theorem exists_nontrivial_conj_of_irr {K Z U : Subgroup G} (hZU : Z ≤ U)
    (hUN : U ≤ Subgroup.normalizer (Z : Set G)) (hsq : ∀ a ∈ U, a ^ 2 ∈ Z)
    (hcard : Z.relIndex U = 16) (hKZ : K ≤ Subgroup.normalizer (Z : Set G))
    (hirr : ∀ W : Subgroup G, Z ≤ W → W ≤ U → K ≤ Subgroup.normalizer (W : Set G) →
      W = Z ∨ W = U) :
    ∃ k ∈ K, ∃ u ∈ U, (k * u * k⁻¹)⁻¹ * u ∉ Z := by
  by_contra hcon
  push Not at hcon
  obtain ⟨a, haU, haZ⟩ : ∃ a ∈ U, a ∉ Z := by
    by_contra hh
    push Not at hh
    have h1 : Z.relIndex U = 1 := Subgroup.relIndex_eq_one.mpr hh
    omega
  have haN := hUN haU
  have ha2 := hsq a haU
  have hWU : twoCoset Z a haN ha2 ≤ U := by
    rintro x (hx | hx)
    · exact hZU hx
    · have e : x = (x * a) * a⁻¹ := by group
      rw [e]
      exact U.mul_mem (hZU hx) (U.inv_mem haU)
  have key : ∀ k ∈ K, ∀ x ∈ twoCoset Z a haN ha2, k * x * k⁻¹ ∈ twoCoset Z a haN ha2 := by
    intro k hk x hx
    have hxU := hWU hx
    have hc := hcon k hk x hxU
    rcases hx with hx | hx
    · exact Or.inl ((Subgroup.mem_normalizer_iff.mp (hKZ hk) x).mp hx)
    · refine Or.inr ?_
      have e : k * x * k⁻¹ * a = (x * ((k * x * k⁻¹)⁻¹ * x)⁻¹ * x⁻¹) * (x * a) := by group
      rw [e]
      exact Z.mul_mem ((Subgroup.mem_normalizer_iff.mp (hUN hxU) _).mp (Z.inv_mem hc)) hx
  have hKW : K ≤ Subgroup.normalizer (twoCoset Z a haN ha2 : Set G) := by
    intro k hk
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨fun hx => key k hk x hx, fun hx => ?_⟩
    have h1 := key k⁻¹ (K.inv_mem hk) _ hx
    have e : k⁻¹ * (k * x * k⁻¹) * k⁻¹⁻¹ = x := by group
    rwa [e] at h1
  rcases hirr _ (le_twoCoset haN ha2) hWU hKW with hW | hW
  · exact haZ (by
      have := mem_twoCoset_self haN ha2
      rwa [hW] at this)
  · have hd : Z.relIndex U ∣ 2 := by
      rw [Subgroup.relIndex_dvd_two_iff]
      refine ⟨a, haU, fun b hb => ?_⟩
      rw [← hW] at hb
      exact hb.symm
    rw [hcard] at hd
    omega

end NC

section Aut

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

omit [Finite G] in
theorem tildeUL_comm (hL : IsShort2 L) (a b : tildeUL L) : a * b = b * a := by
  induction a using QuotientGroup.induction_on with
  | H a =>
    induction b using QuotientGroup.induction_on with
    | H b =>
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
      congr 1
      apply Subtype.ext
      exact C1.blockU_comm hL (a : G) a.2 (b : G) (C1.blockU_le_blockQ hL b.2)

omit [Finite G] in
theorem tildeUL_sq (hL : IsShort2 L) (a : tildeUL L) : a ^ 2 = 1 := by
  induction a using QuotientGroup.induction_on with
  | H a =>
    rw [← QuotientGroup.mk_pow]
    have : a ^ 2 = 1 := Subtype.ext (hL.2.2.1.2 (a : G) a.2)
    rw [this]
    rfl

omit [Finite G] in
theorem card_tildeUL (hidx : ((blockZ L).subgroupOf (blockU L)).index = 2 ^ 4) :
    Nat.card (tildeUL L) = 2 ^ 4 := hidx

theorem mulAut_tildeUL (hL : IsShort2 L)
    (hidx : ((blockZ L).subgroupOf (blockU L)).index = 2 ^ 4) :
    Nat.card (MulAut (tildeUL L)) = 20160 ∧ IsSimpleGroup (MulAut (tildeUL L)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e⟩ := CFSG.SectionRank.Ccomm.nonempty_mulEquiv_of_elementary (p := 2)
    (tildeUL_comm hL) (fun a => tildeUL_sq hL a) (n := 4) (card_tildeUL hidx)
  refine ⟨?_, ?_⟩
  · rw [CFSG.SectionRank.Ccomm.card_mulAut_eq_card_GL e, CFSG.SectionRank.Ccomm.card_GL_zmod]
    simp [Fin.prod_univ_succ]
  · have : IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 4) (ZMod 2)) :=
      Vol2.Ch10.SecA.isSimpleGroup_SL_two (by norm_num)
    exact ((CFSG.SectionRank.Ccomm.elemAutEquivGL e).trans
      (Setup.Family.slEquivGL 4).symm).isSimpleGroup

end Aut

theorem mem_subgroup_of_mem_normalizer_card_2520 {Γ : Type*} [Group Γ] [Finite Γ] [IsSimpleGroup Γ]
    (hΓ : Nat.card Γ = 20160) {H : Subgroup Γ} (hH : Nat.card H = 2520) {T : Γ}
    (hT : T ∈ Subgroup.normalizer (H : Set Γ)) : T ∈ H := by
  have hHN : H ≤ Subgroup.normalizer (H : Set Γ) := Subgroup.le_normalizer
  have hidxH : H.index = 8 := by
    have := H.card_mul_index
    rw [hH, hΓ] at this
    omega
  have h1 := Subgroup.relIndex_mul_index hHN
  rw [hidxH] at h1
  have hle8 : (Subgroup.normalizer (H : Set Γ)).index ≤ 8 :=
    Nat.le_of_dvd (by norm_num) ⟨H.relIndex (Subgroup.normalizer (H : Set Γ)), by rw [← h1]; ring⟩
  have hpos : 0 < (Subgroup.normalizer (H : Set Γ)).index := Nat.pos_of_ne_zero (by
    intro h0
    rw [h0] at h1
    omega)
  have hrel : H.relIndex (Subgroup.normalizer (H : Set Γ)) =
      8 / (Subgroup.normalizer (H : Set Γ)).index := by
    rw [← h1]
    exact (Nat.mul_div_cancel _ hpos).symm
  have hfac : (Subgroup.normalizer (H : Set Γ)) ≠ ⊤ →
      Nat.card Γ ∣ (Subgroup.normalizer (H : Set Γ)).index.factorial := by
    intro hne
    have hcore : (Subgroup.normalizer (H : Set Γ)).normalCore = ⊥ := by
      have := (Subgroup.normalizer (H : Set Γ)).normalCore_normal
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
        (Subgroup.normalizer (H : Set Γ)).normalCore with h | h
      · exact h
      · exact absurd (eq_top_iff.mpr (h ▸ (Subgroup.normalizer (H : Set Γ)).normalCore_le)) hne
    have := (Subgroup.normalizer (H : Set Γ)).index_normalCore_dvd_factorial_index
    rwa [hcore, Subgroup.index_bot] at this
  interval_cases hi : (Subgroup.normalizer (H : Set Γ)).index
  · exfalso
    have htop : Subgroup.normalizer (H : Set Γ) = ⊤ := Subgroup.index_eq_one.mp hi
    have hnorm : H.Normal := Subgroup.normalizer_eq_top_iff.mp htop
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal H with h | h
    · rw [h, Subgroup.card_bot] at hH
      omega
    · rw [h, Subgroup.card_top, hΓ] at hH
      omega
  · exfalso
    have hne : Subgroup.normalizer (H : Set Γ) ≠ ⊤ := fun h => by
      rw [h, Subgroup.index_top] at hi
      omega
    have := hfac hne
    rw [hΓ] at this
    revert this
    decide
  · omega
  · exfalso
    have hne : Subgroup.normalizer (H : Set Γ) ≠ ⊤ := fun h => by
      rw [h, Subgroup.index_top] at hi
      omega
    have := hfac hne
    rw [hΓ] at this
    revert this
    decide
  · omega
  · omega
  · omega
  · have hrel1 : H.relIndex (Subgroup.normalizer (H : Set Γ)) = 1 := by
      rw [hrel]
    exact Subgroup.relIndex_eq_one.mp hrel1 hT

end CFSG.Quasithin
