module

public import CFSG.GroupTheory.Frattini.PSubgroupLift
public import CFSG.GroupTheory.ThreeTranspositions.QuotientLift
public import CFSG.Mathlib.GroupTheory.ClosureSubgroupOf
public import CFSG.RankThree.PartTwo.Sec4.HeringK419OneFieldE9
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanS6.WPF9I
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanS6.WPH2
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanS6.WPH6
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.KInputs811K3Holds
import CFSG.LocalAnalysis.StronglyEmbedded.Normalizer
public import CFSG.HardMathSupport.Solomon.Coordinator.ONCSylow

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONan
section
open CFSG.Open
open CFSG.LocalAnalysis.UniquenessCase.UC22 (Data Opp IsSpor IsAlt)
open CFSG.RankThree.PartOne (IsStronglyPEmbedded IsSylowOf)
open CFSG.RankThree.PartOne.StrongP (conjSub)
open CFSG.LocalAnalysis.UniquenessCase.UCK (ThreeCover)
open scoped commutatorElement Pointwise
variable {G : Type} [Group G] [Finite G] {D : Data G}

theorem Step42Opp_holds'
    (hK2 : K2ONanCentralizer) (c : Ctx82E3 D)
    (hON : UCK.ThreeCover (fun Y _ => IsSpor Y .ONan) c.Lbar) (h7 : D.sig = {7})
    {P : Subgroup G} (hP : CFSG.ABGLocalTools.IsSylowOf 3 P D.M)
    {x : G} (hx : x ∈ P ⊓ c.L) (hx3 : orderOf x = 3) (hxZ : x ∉ zSub P c.L) :
    Step42Opp c P x := by
  classical
  have hF9 := f9_perfectCore' (c := c) (P := P) (a := x) hON hP hx hx3 hxZ hK2
  have hIa : Ia c x = pI x c.L := by
    rw [Ia, pI, CFSG.Quasithin.perfectCore_eq_map_perfectResidual, inSubgroup,
      inf_comm]
  have hgen : Ia c x = Subgroup.closure {y : G | y ∈ Ia c x ∧ orderOf y = 3} :=
    Ia_eq_closure_three c hF9.1
  rw [Step42Opp, pIbar, ← hIa, hgen]
  have hSH : {y : G | y ∈ Ia c x ∧ orderOf y = 3} ⊆ (pH x : Set G) := by
    intro y hy
    exact (Ia_le c x hy.1).2
  rw [Subgroup.closure_subgroupOf hSH, MonoidHom.map_closure]
  refine (Subgroup.closure_le (Opp 3 (⊤ : Subgroup (pX x)))).mpr ?_
  rintro z ⟨y, hy, rfl⟩
  rw [Set.mem_preimage] at hy
  have hyord : orderOf (y : G) = 3 := hy.2
  have hyord' : orderOf y = 3 := by
    rw [← Subgroup.orderOf_coe, hyord]
  have hdvd : orderOf (QuotientGroup.mk' (pDK x) y) ∣ 3 := by
    simpa [hyord'] using orderOf_map_dvd (QuotientGroup.mk' (pDK x)) y
  rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
  · refine Subgroup.subset_closure ⟨Subgroup.mem_top _, 0, ?_⟩
    simpa only [pow_zero] using h1
  · refine Subgroup.subset_closure ⟨Subgroup.mem_top _, 1, ?_⟩
    simpa only [pow_one] using h3

theorem propositionH_step42''''
    (hK2 : K2ONanCentralizer) (c : Ctx82E3 D)
    (hON : UCK.ThreeCover (fun Y _ => IsSpor Y .ONan) c.Lbar) (h7 : D.sig = {7})
    {P : Subgroup G} (hP : CFSG.ABGLocalTools.IsSylowOf 3 P D.M)
    {x : G} (hx : x ∈ P ⊓ c.L) (hx3 : orderOf x = 3) (hxZ : x ∉ zSub P c.L) :
    ¬ CFSG.HallHigman.IsPSolvable 3 ↥(pIbar x c.L) ∧
      360 < Nat.card ↥(pIbar x c.L) ∧
      pIbar x c.L ≤ Opp 3 (⊤ : Subgroup (pX x)) := by
  exact propositionH_step42'' hK2 c hON h7 hP hx hx3 hxZ
    (Step42Surjection_holds hK2 c hON h7 hP hx hx3 hxZ)
    (Step42Opp_holds' hK2 c hON h7 hP hx hx3 hxZ)

theorem frame_commutator_le_Zs_wPH7 (c : Ctx82E3 D)
    (hON : ThreeCover (fun Y _ => IsSpor Y .ONan) c.Lbar)
    {P : Subgroup G} (hP : CFSG.ABGLocalTools.IsSylowOf 3 P D.M) :
    ⁅P ⊓ c.L, P ⊓ c.L⁆ ≤ zSub P c.L := by
  classical
  letI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let N : Subgroup ↥c.L := CFSG.Open.pCore 2 ↥c.L
  let π : ↥c.L →* c.Lbar := QuotientGroup.mk' N
  let Q : Subgroup G := P ⊓ c.L
  let Y : Subgroup ↥c.L := Q.subgroupOf c.L
  have hQsyl : CFSG.ABGLocalTools.IsSylowOf 3 Q c.L :=
    hP.inf_of_le_normalizer c.hyp81.1 c.le_normalizer_L
  obtain ⟨Q', hQ'⟩ := hQsyl.exists_sylow_eq_subgroupOf
  let S : Sylow 3 c.Lbar := Q'.mapSurjective (QuotientGroup.mk'_surjective N)
  have hScoe : (S : Subgroup c.Lbar) = Y.map π := by
    rw [Sylow.coe_mapSurjective, hQ']
  have hQ3 : IsPGroup 3 Q := hQsyl.isPGroup
  have hQsub3 : IsPGroup 3 Y := hQ3.comap_subtype
  have hN2 : IsPGroup 2 N := CFSG.pCore_isPGroup
  have hYdisj : Y ⊓ N = ⊥ :=
    (IsPGroup.disjoint_of_ne 3 2 (by norm_num) Y N hQsub3 hN2).eq_bot
  have hHat : CFSG.HardMathSupport.Solomon.LocalBalance.IsHatON c.Lbar := by
    obtain ⟨hq, hZ, ⟨e⟩⟩ := hON
    obtain ⟨b⟩ := CFSG.Sporadic.Bridge.ON.nonempty_mulEquiv
    have b' : CFSG.Blueprint.NativeSporadic.Carrier .ONan ≃*
        (TauCeti.CFSGIndex.sporadic TauCeti.SporadicName.ONan).Group := b
    exact ⟨hq.1, hZ, ⟨e.trans b'⟩⟩
  have hdata := CFSG.HardMathSupport.Solomon.Coordinator.inputONSylow_holds c.Lbar hHat S
  have hcommS : ∀ x ∈ (S : Subgroup c.Lbar), ∀ y ∈ (S : Subgroup c.Lbar),
      ⁅x, y⁆ ∈ Subgroup.center c.Lbar := hdata.2.2.1
  have hinj : ∀ a b : ↥c.L, a ∈ Y → b ∈ Y → π a = π b → a = b := by
    intro a b ha hb hab
    have h1 : π (a * b⁻¹) = 1 := by rw [map_mul, map_inv, hab, mul_inv_cancel]
    have hN : a * b⁻¹ ∈ N := (QuotientGroup.eq_one_iff (a * b⁻¹)).mp h1
    have hY : a * b⁻¹ ∈ Y := Y.mul_mem ha (Y.inv_mem hb)
    have hbot : a * b⁻¹ ∈ (⊥ : Subgroup ↥c.L) := by
      rw [← hYdisj]
      exact ⟨hY, hN⟩
    have h : a * b⁻¹ = 1 := Subgroup.mem_bot.mp hbot
    calc a = a * b⁻¹ * b := by group
      _ = b := by rw [h, one_mul]
  rw [Subgroup.commutator_le]
  intro x hx y hy
  have hxL : (⟨x, hx.2⟩ : ↥c.L) ∈ Y := by
    rw [Subgroup.mem_subgroupOf]; exact hx
  have hyL : (⟨y, hy.2⟩ : ↥c.L) ∈ Y := by
    rw [Subgroup.mem_subgroupOf]; exact hy
  have hxyQ : ⁅x, y⁆ ∈ Q :=
    Subgroup.commutator_le_of_le (le_refl Q) (le_refl Q)
      (Subgroup.commutator_mem_commutator hx hy)
  refine Subgroup.mem_inf.mpr ⟨hxyQ, Subgroup.mem_centralizer_iff.mpr ?_⟩
  intro z hz
  have hzL : (⟨z, (Subgroup.mem_inf.mp hz).2⟩ : ↥c.L) ∈ Y := by
    rw [Subgroup.mem_subgroupOf]
    exact hz
  have hxS : π (⟨x, hx.2⟩ : ↥c.L) ∈ (S : Subgroup c.Lbar) := by
    rw [hScoe]
    exact Subgroup.mem_map_of_mem π hxL
  have hyS : π (⟨y, hy.2⟩ : ↥c.L) ∈ (S : Subgroup c.Lbar) := by
    rw [hScoe]
    exact Subgroup.mem_map_of_mem π hyL
  have hctr : π (⁅(⟨x, hx.2⟩ : ↥c.L), (⟨y, hy.2⟩ : ↥c.L)⁆) ∈
      Subgroup.center c.Lbar := by
    rw [map_commutatorElement]
    exact hcommS _ hxS _ hyS
  have hxyY : (⁅(⟨x, hx.2⟩ : ↥c.L), (⟨y, hy.2⟩ : ↥c.L)⁆) ∈ Y :=
    mul_mem (mul_mem (mul_mem hxL hyL) (inv_mem hxL)) (inv_mem hyL)
  have hcommL : (⁅(⟨x, hx.2⟩ : ↥c.L), (⟨y, hy.2⟩ : ↥c.L)⁆) * ⟨z, (Subgroup.mem_inf.mp hz).2⟩ =
      ⟨z, (Subgroup.mem_inf.mp hz).2⟩ * ⁅(⟨x, hx.2⟩ : ↥c.L), (⟨y, hy.2⟩ : ↥c.L)⁆ := by
    refine hinj _ _ (mul_mem hxyY hzL) (mul_mem hzL hxyY) ?_
    rw [map_mul, map_mul]
    exact (Subgroup.mem_center_iff.mp hctr _).symm
  have hcommG := congrArg (fun u : ↥c.L => (u : G)) hcommL
  change ⁅x, y⁆ * z = z * ⁅x, y⁆ at hcommG
  exact hcommG.symm

theorem card_inf_L_of_onan_wPH7 (c : Ctx82E3 D)
    (hON : ThreeCover (fun Y _ => IsSpor Y .ONan) c.Lbar)
    {P : Subgroup G} (hP : CFSG.ABGLocalTools.IsSylowOf 3 P D.M) :
    Nat.card ↥(P ⊓ c.L) = 3 ^ 5 := by
  classical
  letI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let N : Subgroup ↥c.L := CFSG.Open.pCore 2 ↥c.L
  let π : ↥c.L →* c.Lbar := QuotientGroup.mk' N
  let Q : Subgroup G := P ⊓ c.L
  let Y : Subgroup ↥c.L := Q.subgroupOf c.L
  have hQsyl : CFSG.ABGLocalTools.IsSylowOf 3 Q c.L :=
    hP.inf_of_le_normalizer c.hyp81.1 c.le_normalizer_L
  obtain ⟨Q', hQ'⟩ := hQsyl.exists_sylow_eq_subgroupOf
  let S : Sylow 3 c.Lbar := Q'.mapSurjective (QuotientGroup.mk'_surjective N)
  have hScoe : (S : Subgroup c.Lbar) = Y.map π := by
    rw [Sylow.coe_mapSurjective, hQ']
  have hQ3 : IsPGroup 3 Q := hQsyl.isPGroup
  have hQsub3 : IsPGroup 3 Y := hQ3.comap_subtype
  have hN2 : IsPGroup 2 N := CFSG.pCore_isPGroup
  have hYdisj : Y ⊓ N = ⊥ :=
    (IsPGroup.disjoint_of_ne 3 2 (by norm_num) Y N hQsub3 hN2).eq_bot
  have hHat : CFSG.HardMathSupport.Solomon.LocalBalance.IsHatON c.Lbar := by
    obtain ⟨hq, hZ, ⟨e⟩⟩ := hON
    obtain ⟨b⟩ := CFSG.Sporadic.Bridge.ON.nonempty_mulEquiv
    have b' : CFSG.Blueprint.NativeSporadic.Carrier .ONan ≃*
        (TauCeti.CFSGIndex.sporadic TauCeti.SporadicName.ONan).Group := b
    exact ⟨hq.1, hZ, ⟨e.trans b'⟩⟩
  have hcardS : Nat.card (S : Subgroup c.Lbar) = 3 ^ 5 :=
    (CFSG.HardMathSupport.Solomon.Coordinator.inputONSylow_holds c.Lbar hHat S).1
  have h1 : Nat.card ↥Q = Nat.card ↥Y :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQsyl.le).toEquiv).symm
  have h2 : Nat.card ↥(Y.map π) = Nat.card ↥Y := by
    apply CFSG.Walter.Suzuki.card_map_of_inf_ker_eq_bot
    rw [QuotientGroup.ker_mk']
    exact hYdisj
  have h3 : Nat.card (S : Subgroup c.Lbar) = Nat.card ↥(Y.map π) := by rw [hScoe]
  calc Nat.card ↥Q = Nat.card ↥Y := h1
    _ = Nat.card ↥(Y.map π) := h2.symm
    _ = Nat.card (S : Subgroup c.Lbar) := h3.symm
    _ = 3 ^ 5 := hcardS

theorem exists_E27_of_onan_wPH7
    (c : Ctx82E3 D) (hON : ThreeCover (fun Y _ => IsSpor Y .ONan) c.Lbar)
    {P : Subgroup G} (hP : CFSG.ABGLocalTools.IsSylowOf 3 P D.M)
    {x : G} (hx : x ∈ P ⊓ c.L) (hx3 : orderOf x = 3) (hxZ : x ∉ zSub P c.L) :
    ∃ A : Subgroup G, A ≤ P ⊓ c.L ∧ x ∈ A ∧ CFSG.Open.IsElemAbelian 3 A ∧
      Nat.card A = 27 := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let Q : Subgroup G := P ⊓ c.L
  have hxQ : x ∈ Q := hx
  have hcardQ : Nat.card ↥Q = 3 ^ 5 := card_inf_L_of_onan_wPH7 c hON hP
  have hexpQ : ∀ a : ↥Q, a ^ 3 = 1 := by
    intro a
    exact Subtype.ext (c.pow_three_eq_one_of_mem_inf_L_of_onan hON hP (a : G) a.2)
  have hcenterQ : Subgroup.center ↥Q = (zSub P c.L).subgroupOf Q := by
    ext a
    rw [Subgroup.mem_center_iff, Subgroup.mem_subgroupOf, Subgroup.mem_inf,
      Subgroup.mem_centralizer_iff]
    constructor
    · intro h
      refine ⟨a.2, fun b hb => ?_⟩
      exact congrArg (fun u : ↥Q => (u : G)) (h ⟨b, hb⟩)
    · rintro ⟨-, hcent⟩ b
      exact Subtype.ext (hcent (b : G) b.2)
  have hZQ : Nat.card (Subgroup.center ↥Q) = 3 := by
    rw [hcenterQ]
    calc Nat.card ↥((zSub P c.L).subgroupOf Q) = Nat.card ↥(zSub P c.L) :=
          Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : zSub P c.L ≤ Q)).toEquiv
      _ = 3 := c.card_inf_centralizer_of_onan hON hP
  have hcommQ : commutator ↥Q ≤ Subgroup.center ↥Q := by
    change ⁅(⊤ : Subgroup ↥Q), (⊤ : Subgroup ↥Q)⁆ ≤ Subgroup.center ↥Q
    rw [Subgroup.commutator_le]
    intro a ha b hb
    rw [hcenterQ, Subgroup.mem_subgroupOf]
    exact frame_commutator_le_Zs_wPH7 c hON hP
      (Subgroup.commutator_mem_commutator a.2 b.2)
  let a : ↥Q := ⟨x, hxQ⟩
  have haZ : a ∉ Subgroup.center ↥Q := by
    intro h
    exact hxZ (Subgroup.mem_subgroupOf.mp (hcenterQ ▸ h))
  obtain ⟨E, -, haE, hEea, hEcard⟩ :=
    CFSG.GroupTheory.ExtraspecialThreeFive.exists_elemAbelian_27_of_index_le_three
      hcardQ hexpQ hZQ hcommQ (H := ⊤) (by simp) (a := a) (by simp) haZ
  refine ⟨E.map Q.subtype, Subgroup.map_subtype_le E, ⟨a, haE, rfl⟩,
    hEea.map Q.subtype, ?_⟩
  rw [Subgroup.card_map_of_injective Q.subtype_injective, hEcard]

theorem two_le_pRank_pHstar_wPH7
    (c : Ctx82E3 D) (hON : ThreeCover (fun Y _ => IsSpor Y .ONan) c.Lbar)
    {P : Subgroup G} (hP : CFSG.ABGLocalTools.IsSylowOf 3 P D.M)
    {x : G} (hx : x ∈ P ⊓ c.L) (hx3 : orderOf x = 3) (hxZ : x ∉ zSub P c.L) :
    2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (pHstar x)) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨A, hAQ, hxA, hAea, hAcard⟩ := exists_E27_of_onan_wPH7 c hON hP hx hx3 hxZ
  have hAH : A ≤ pH x := by
    intro a ha
    rw [pH]
    exact Subgroup.mem_centralizer_singleton_iff.mpr (hAea.comm ha hxA)
  let f : ↥A →* pHstar x :=
    (QuotientGroup.mk' (pK x)).comp (Subgroup.inclusion hAH)
  haveI : IsMulCommutative ↥A := hAea.1
  have hAtop : CFSG.Open.IsElemAbelian 3 (⊤ : Subgroup ↥A) := by
    refine ⟨⟨⟨fun a b => Subtype.ext (mul_comm' a.1 b.1)⟩⟩, ?_⟩
    intro a _
    exact Subtype.ext (hAea.2 a.1 a.2)
  have hAE : CFSG.Open.IsElemAbelian 3 f.range := by
    simpa [MonoidHom.range_eq_map] using CFSG.SectionRank.isElemAbelian_map hAtop f
  have hfker : f.ker = (Subgroup.zpowers x).subgroupOf A := by
    ext a
    constructor
    · intro h
      have h' : (QuotientGroup.mk' (pK x)) ⟨a.1, hAH a.2⟩ = 1 := h
      have h'' : (⟨a.1, hAH a.2⟩ : ↥(pH x)) ∈ pK x :=
        (QuotientGroup.eq_one_iff _).mp h'
      exact Subgroup.mem_subgroupOf.mp h''
    · intro h
      have h' : (⟨a.1, hAH a.2⟩ : ↥(pH x)) ∈ pK x :=
        Subgroup.mem_subgroupOf.mpr h
      exact (QuotientGroup.eq_one_iff _).mpr h'
  have hkercard : Nat.card ↥f.ker = 3 := by
    rw [hfker]
    calc Nat.card ↥((Subgroup.zpowers x).subgroupOf A) = Nat.card ↥(Subgroup.zpowers x) :=
          Nat.card_congr (Subgroup.subgroupOfEquivOfLe
            (Subgroup.zpowers_le.mpr hxA)).toEquiv
      _ = 3 := by rw [Nat.card_zpowers, hx3]
  have hrangecard : Nat.card ↥f.range = 9 := by
    have h := Subgroup.card_ker_mul_card_range f
    rw [hkercard, hAcard] at h
    omega
  exact CFSG.SectionRank.le_pRank (p := 3) (by norm_num) le_top hAE
    (by rw [hrangecard]; norm_num)

theorem isStronglyPEmbedded_map_mulEquiv_wPH7 {A B : Type} [Group A] [Finite A]
    [Group B] [Finite B] {p : ℕ} (e : A ≃* B) {N : Subgroup A}
    (h : IsStronglyPEmbedded p N) :
    IsStronglyPEmbedded p (N.map e.toMonoidHom) := by
  refine ⟨?_, ?_, ?_⟩
  · intro htop
    apply h.1
    ext a
    constructor
    · intro _; exact Subgroup.mem_top a
    · intro _
      have hmem : e a ∈ N.map e.toMonoidHom := by
        rw [htop]; exact Subgroup.mem_top _
      obtain ⟨n, hn, hna⟩ := Subgroup.mem_map.mp hmem
      rw [← e.injective hna]
      exact hn
  · rw [Subgroup.card_map_of_injective e.injective]
    exact h.2.1
  · intro g hg
    have hg' : e.symm g ∉ N := by
      intro hmem
      exact hg (Subgroup.mem_map.mpr ⟨e.symm g, hmem, e.apply_symm_apply g⟩)
    have hnot := h.2.2 (e.symm g) hg'
    have hcomp : e.toMonoidHom.comp (MulAut.conj (e.symm g)).toMonoidHom =
        (MulAut.conj g).toMonoidHom.comp e.toMonoidHom := by
      ext x
      simp [MulAut.conj_apply]
    have hmap' : (N.map e.toMonoidHom).map (MulAut.conj g).toMonoidHom =
        (N.map (MulAut.conj (e.symm g)).toMonoidHom).map e.toMonoidHom := by
      rw [Subgroup.map_map, Subgroup.map_map, hcomp]
    have hEq : (N.map e.toMonoidHom) ⊓
        (N.map e.toMonoidHom).map (MulAut.conj g).toMonoidHom =
        (N ⊓ N.map (MulAut.conj (e.symm g)).toMonoidHom).map e.toMonoidHom := by
      rw [hmap', ← Subgroup.map_inf_eq N (N.map (MulAut.conj (e.symm g)).toMonoidHom)
        e.toMonoidHom e.injective]
    rw [hEq, Subgroup.card_map_of_injective e.injective]
    exact hnot

theorem propositionH_step2'_wPH7
    (hK2 : K2ONanCentralizer) (c : Ctx82E3 D)
    (hON : UCK.ThreeCover (fun Y _ => IsSpor Y .ONan) c.Lbar) (h7 : D.sig = {7})
    {P : Subgroup G} (hP : CFSG.ABGLocalTools.IsSylowOf 3 P D.M)
    (hNZ : Subgroup.normalizer ((zSub P c.L : Subgroup G) : Set G) ≤ D.M)
    {x : G} (hx : x ∈ P ⊓ c.L) (hx3 : orderOf x = 3) (hxZ : x ∉ zSub P c.L)
    (h1 : IsStronglyPEmbedded 3 (pNstar x D.M)) :
    IsStronglyPEmbedded 3 (pNbar x D.M) ∧
      CFSG.pPrimeCore 3 (pX x) = ⊥ ∧
      2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (pX x)) ∧
      CFSG.Open.IsKGroup (pX x) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let H := pH x
  let K := pK x
  let DK := pDK x
  have hxH : x ∈ H := by
    change x ∈ pH x
    rw [pH]
    exact Subgroup.mem_centralizer_singleton_iff.mpr (by group)
  have hKleH : Subgroup.zpowers x ≤ H := Subgroup.zpowers_le.mpr hxH
  have hKcard : Nat.card ↥K = 3 := by
    change Nat.card ↥(pK x) = 3
    rw [pK]
    calc Nat.card ↥((Subgroup.zpowers x).subgroupOf H) =
        Nat.card ↥(Subgroup.zpowers x) :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKleH).toEquiv
      _ = 3 := by rw [Nat.card_zpowers, hx3]
  have hK3 : IsPGroup 3 K := IsPGroup.of_card (n := 1) (by simpa using hKcard)
  have hKcenter : K ≤ Subgroup.center H := by
    intro k hk
    rw [Subgroup.mem_center_iff]
    intro h
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp (Subgroup.mem_subgroupOf.mp hk)
    apply Subtype.ext
    change (h : G) * (k : G) = (k : G) * (h : G)
    have hcomm : Commute x (h : G) :=
      (Subgroup.mem_centralizer_singleton_iff.mp h.2).symm
    rw [← hn]
    exact (hcomm.zpow_left n).eq.symm
  haveI : K.Normal := pK_normal x
  haveI : DK.Normal := pDK_normal x
  have hOstar : CFSG.pPrimeCore 3 (pHstar x) = DK.map (QuotientGroup.mk' K) := by
    have h := CFSG.central_p_subgroup_prime_core_quotient (p := 3) (G := H)
      (Z := K) hKcenter hK3
    have h' : CFSG.pPrimeCore 3 (pHstar x) =
        (pD x).map (QuotientGroup.mk' K) := by
      simpa [pHstar, pD, H, K] using h
    rw [h']
    change (pD x).map (QuotientGroup.mk' (pK x)) =
      (pDK x).map (QuotientGroup.mk' (pK x))
    rw [pDK, Subgroup.map_sup]
    have hKmap : K.map (QuotientGroup.mk' K) = ⊥ := by
      rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
    rw [hKmap, sup_bot_eq]
  let e : (pHstar x ⧸ CFSG.pPrimeCore 3 (pHstar x)) ≃* pX x :=
    (QuotientGroup.quotientMulEquivOfEq hOstar).trans
      (QuotientGroup.quotientQuotientEquivQuotient K DK le_sup_right)
  have he_mk : ∀ n : H,
      e (QuotientGroup.mk (s := CFSG.pPrimeCore 3 (pHstar x))
          (QuotientGroup.mk (s := K) n)) =
        QuotientGroup.mk (s := DK) n := by
    intro n
    simp [e, QuotientGroup.quotientMulEquivOfEq_mk,
      QuotientGroup.quotientQuotientEquivQuotient_apply_mk]
  have hNmap : ((pNstar x D.M).map
      (QuotientGroup.mk' (CFSG.pPrimeCore 3 (pHstar x)))).map e.toMonoidHom =
      pNbar x D.M := by
    rw [pNstar, Subgroup.map_map, Subgroup.map_map, pNbar]
    apply congrArg (fun f : ↥(pH x) →* pX x =>
      Subgroup.map f ((pN x D.M).subgroupOf (pH x)))
    ext n
    exact he_mk n
  have h2 : 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (pHstar x)) :=
    two_le_pRank_pHstar_wPH7 c hON hP hx hx3 hxZ
  haveI : (CFSG.pPrimeCore 3 (pHstar x)).Normal := CFSG.pPrimeCore_normal
  have hOle : CFSG.pPrimeCore 3 (pHstar x) ≤ pNstar x D.M :=
    CFSG.LocalAnalysis.UniquenessCase.UCK.pPrimeCore_le_of_stronglyPEmbedded h1 h2
  have hcop : ¬ 3 ∣ Nat.card (CFSG.pPrimeCore 3 (pHstar x)) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).1 CFSG.pPrimeCore_coprime_card
  have hd : IsStronglyPEmbedded 3
        ((pNstar x D.M).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 (pHstar x)))) ∧
      2 ≤ CFSG.Open.pRank 3
        (⊤ : Subgroup (pHstar x ⧸ CFSG.pPrimeCore 3 (pHstar x))) ∧
      CFSG.pPrimeCore 3
        (pHstar x ⧸ CFSG.pPrimeCore 3 (pHstar x)) = ⊥ := by
    refine ⟨h1.map_quotient hOle hcop, ?_,
      CFSG.pPrimeCore_quotient_eq_bot Nat.prime_three⟩
    rw [CFSG.SectionRank.pRank_quotient_eq _ hcop]
    exact h2
  have hstrong : IsStronglyPEmbedded 3 (pNbar x D.M) := by
    rw [← hNmap]
    exact isStronglyPEmbedded_map_mulEquiv_wPH7 e hd.1
  have hcore : CFSG.pPrimeCore 3 (pX x) = ⊥ := by
    have h := CFSG.pPrimeCore_map_iso 3 e
    rw [hd.2.2] at h
    simpa using h.symm
  have hrank : 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (pX x)) := by
    rw [← CFSG.SectionRank.pRank_top_eq_of_mulEquiv (p := 3) (by norm_num) e]
    exact hd.2.1
  have hHproper : pH x ≠ ⊤ := by
    intro htop
    haveI : IsSimpleGroup G := D.standing.simple
    have hcenter : Subgroup.center G = ⊥ :=
      CFSG.AGLEmbedding.center_eq_bot_of_isSimpleGroup_nonabelian D.standing.nonab
    have hxcenter : x ∈ Subgroup.center G := by
      rw [Subgroup.mem_center_iff]
      intro g
      have hg : g ∈ pH x := htop ▸ Subgroup.mem_top g
      exact Subgroup.mem_centralizer_singleton_iff.mp hg
    rw [hcenter] at hxcenter
    have hx1 : x = 1 := Subgroup.mem_bot.mp hxcenter
    rw [hx1] at hx3
    simp at hx3
  have hKH : CFSG.Open.IsKGroup H := c.kProper.isKGroup H hHproper
  have hKX : CFSG.Open.IsKGroup (pX x) := by
    simpa [pX, H, DK] using hKH.quotient DK
  exact ⟨hstrong, hcore, hrank, hKX⟩

theorem exists_cube_eq_of_isCyclic_three_wPH7 {U : Type} [Group U] [Finite U] [IsCyclic U]
    (hU3 : IsPGroup 3 U) (hcard : 3 < Nat.card U) {x : U} (hx3 : orderOf x = 3) :
    ∃ v : U, v ^ 3 = x := by
  classical
  letI : CommGroup U := IsCyclic.commGroup
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hU3
  have hn2 : 2 ≤ n := by
    rcases n with _ | _ | n
    · simp at hn
      omega
    · simp at hn
      omega
    · omega
  let f : U →* U := powMonoidHom 3
  have hker_card : Nat.card ↥f.ker = 3 := by
    rw [IsCyclic.card_powMonoidHom_ker]
    rw [hn]
    exact Nat.gcd_eq_right (dvd_pow_self 3 (by omega))
  have hxker : x ∈ f.ker := by
    rw [MonoidHom.mem_ker]
    show x ^ 3 = 1
    rw [← hx3]
    exact pow_orderOf_eq_one x
  have hxz : Subgroup.zpowers x = f.ker :=
    Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hxker)
      (by rw [Nat.card_zpowers, hx3, hker_card])
  have hrange_card : Nat.card ↥f.range = 3 ^ (n - 1) := by
    have h := Subgroup.card_ker_mul_card_range f
    rw [hker_card, hn] at h
    have h3n : 3 ^ n = 3 ^ (n - 1) * 3 := by
      rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ n)]
    rw [h3n, mul_comm (3 ^ (n - 1)) 3] at h
    exact Nat.eq_of_mul_eq_mul_left (by norm_num) h
  have h3dvd : 3 ∣ Nat.card ↥f.range := by
    rw [hrange_card]
    have hpow : 3 ^ (n - 1) = 3 ^ (n - 2) * 3 := by
      rw [← pow_succ, show n - 2 + 1 = n - 1 by omega]
    rw [hpow]
    exact dvd_mul_left 3 _
  obtain ⟨y, hyord⟩ := exists_prime_orderOf_dvd_card' (G := ↥f.range) 3 h3dvd
  have hyker : (y : U) ∈ f.ker := by
    rw [MonoidHom.mem_ker]
    show (y : U) ^ 3 = 1
    have hy3 : (y : ↥f.range) ^ 3 = 1 := by
      rw [← hyord]
      exact pow_orderOf_eq_one y
    simpa using congrArg (fun z : ↥f.range => (z : U)) hy3
  have hzy : Subgroup.zpowers (y : U) = f.ker :=
    Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hyker)
      (by rw [Nat.card_zpowers, Subgroup.orderOf_coe, hyord, hker_card])
  have hxrange : x ∈ f.range := by
    have hxker' : x ∈ f.ker := by rw [← hxz]; exact Subgroup.mem_zpowers x
    rw [← hzy] at hxker'
    exact Subgroup.zpowers_le.mpr y.2 hxker'
  obtain ⟨v, hv⟩ := MonoidHom.mem_range.mp hxrange
  exact ⟨v, by simpa [f] using hv⟩

theorem propositionH_F4'_wPH7
    (hK2 : K2ONanCentralizer) (c : Ctx82E3 D)
    (hON : UCK.ThreeCover (fun Y _ => IsSpor Y .ONan) c.Lbar) (h7 : D.sig = {7})
    {P : Subgroup G} (hP : CFSG.ABGLocalTools.IsSylowOf 3 P D.M)
    (hNZ : Subgroup.normalizer ((zSub P c.L : Subgroup G) : Set G) ≤ D.M)
    {x : G} (hx : x ∈ P ⊓ c.L) (hx3 : orderOf x = 3) (hxZ : x ∉ zSub P c.L) :
    Subgroup.zpowers x < P ⊓ Subgroup.centralizer ({x} : Set G) ∧
      ∀ U : Subgroup G, U ≤ P ⊓ Subgroup.centralizer ({x} : Set G) →
        Subgroup.zpowers x < U → ¬ IsCyclic U := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hZcard : Nat.card ↥(zSub P c.L) = 3 := c.card_inf_centralizer_of_onan hON hP
  have hZle : zSub P c.L ≤ P ⊓ Subgroup.centralizer ({x} : Set G) := by
    refine le_inf ((inf_le_left.trans inf_le_left)) ?_
    intro z hz
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      ((Subgroup.mem_centralizer_iff.mp hz.2 x hx).symm)
  constructor
  · have hle : Subgroup.zpowers x ≤ P ⊓ Subgroup.centralizer ({x} : Set G) := by
      refine Subgroup.zpowers_le.mpr ⟨hx.1, ?_⟩
      exact Subgroup.mem_centralizer_singleton_iff.mpr (by group)
    refine lt_of_le_of_ne hle ?_
    intro heq
    have hZle' : zSub P c.L ≤ Subgroup.zpowers x := heq ▸ hZle
    have hZeq : zSub P c.L = Subgroup.zpowers x :=
      Subgroup.eq_of_le_of_card_ge hZle'
        (by rw [Nat.card_zpowers, hx3, hZcard])
    exact hxZ (hZeq.symm ▸ Subgroup.mem_zpowers x)
  · intro U hU hlt hcyc
    have hxU : x ∈ U := hlt.le (Subgroup.mem_zpowers x)
    have hU3 : IsPGroup 3 U := hP.isPGroup.to_le (hU.trans inf_le_left)
    have hcardU : 3 < Nat.card ↥U := by
      have h := Subgroup.card_lt_of_lt hlt
      rwa [Nat.card_zpowers, hx3] at h
    have hxU3 : orderOf (⟨x, hxU⟩ : ↥U) = 3 := by
      rw [Subgroup.orderOf_mk, hx3]
    obtain ⟨v, hv⟩ := exists_cube_eq_of_isCyclic_three_wPH7 hU3 hcardU hxU3
    have hv3 : (v : G) ^ 3 = x := by
      simpa using congrArg (fun w : ↥U => (w : G)) hv
    have hvU : (v : G) ∈ U := v.2
    have hvP : (v : G) ∈ P := hU.trans inf_le_left hvU
    have hvM : (v : G) ∈ D.M := hP.le hvP
    have hxM : x ∈ D.M := hP.le hx.1
    let φ := CFSG.GroupTheory.conjModPCore 2 c.L D.M c.le_normalizer_L
    have hφv3 : IsPGroup 3 (Subgroup.zpowers (φ ⟨(v : G), hvM⟩)) := by
      obtain ⟨k, hk⟩ := hU3.exists_orderOf_dvd_pow v
      have hdvd : orderOf (φ ⟨(v : G), hvM⟩) ∣ 3 ^ k := by
        have h := orderOf_map_dvd φ ⟨(v : G), hvM⟩
        rw [Subgroup.orderOf_mk, Subgroup.orderOf_coe] at h
        exact h.trans (by simpa using hk)
      obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
      rw [IsPGroup.iff_card, Nat.card_zpowers]
      exact ⟨m, hm⟩
    have hinner : φ ⟨(v : G), hvM⟩ ∈
        (MulAut.conj : c.Lbar →* MulAut c.Lbar).range := by
      simpa [CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.innAut] using
        (CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.k3Out_holds c.Lbar hON
          _ hφv3)
    obtain ⟨w, hw⟩ := MonoidHom.mem_range.mp hinner
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hφv3
    rw [Nat.card_zpowers] at hk
    have hconjpow : (MulAut.conj w) ^ (3 ^ k) = 1 := by
      rw [hw, ← hk]
      exact pow_orderOf_eq_one _
    have hconjmap : MulAut.conj (w ^ (3 ^ k)) = 1 := by
      rw [map_pow, hconjpow]
    have hcenter : w ^ (3 ^ k) ∈ Subgroup.center c.Lbar := by
      rw [Subgroup.mem_center_iff]
      intro y
      have h := congrArg (fun f : MulAut c.Lbar => f y) hconjmap
      simp only [MulAut.one_apply, MulAut.conj_apply] at h
      have h2 : w ^ (3 ^ k) * y = y * w ^ (3 ^ k) := by
        calc w ^ (3 ^ k) * y = (w ^ (3 ^ k) * y * (w ^ (3 ^ k))⁻¹) * w ^ (3 ^ k) := by
              group
          _ = y * w ^ (3 ^ k) := by rw [h]
      exact h2.symm
    have hz3 : (w ^ (3 ^ k)) ^ 3 = 1 := by
      have hdvd : orderOf (⟨w ^ (3 ^ k), hcenter⟩ : Subgroup.center c.Lbar) ∣ 3 := by
        have h := orderOf_dvd_natCard (⟨w ^ (3 ^ k), hcenter⟩ : Subgroup.center c.Lbar)
        rwa [hON.2.1] at h
      have h := (orderOf_dvd_iff_pow_eq_one).mp hdvd
      simpa using congrArg (fun z : Subgroup.center c.Lbar => (z : c.Lbar)) h
    have hword : w ^ (3 ^ (k + 1)) = 1 := by
      rw [pow_succ, pow_mul]
      exact hz3
    have hw3p : IsPGroup 3 (Subgroup.zpowers w) := by
      obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp
        (orderOf_dvd_of_pow_eq_one hword)
      rw [IsPGroup.iff_card, Nat.card_zpowers]
      exact ⟨m, hm⟩
    obtain ⟨S, hS⟩ := IsPGroup.exists_le_sylow hw3p
    have hw3 : w ^ 3 = 1 :=
      CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.k3Exp_holds c.Lbar hON S w
        (hS (Subgroup.mem_zpowers w))
    have hφvcube : (φ ⟨(v : G), hvM⟩) ^ 3 = 1 := by
      rw [← hw, ← map_pow, hw3, map_one]
    have hφx : φ ⟨x, hxM⟩ = 1 := by
      have hvM3 : (⟨(v : G), hvM⟩ : ↥D.M) ^ 3 = ⟨x, hxM⟩ := Subtype.ext (by simpa using hv3)
      rw [← hvM3, map_pow, hφvcube]
    have hxker : x ∈ (φ.ker).map D.M.subtype :=
      Subgroup.mem_map.mpr ⟨⟨x, hxM⟩, MonoidHom.mem_ker.mpr hφx, rfl⟩
    have hxcomm :=
      (CFSG.GroupTheory.mem_map_ker_conjModPCore_iff 2 c.L D.M c.le_normalizer_L).mp hxker
    have hdisj := IsPGroup.disjoint_of_ne 3 2 (by norm_num) P
      (CFSG.Open.pCoreOf 2 c.L) hP.isPGroup
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 c.L)
    have hxcent : x ∈ Subgroup.centralizer ((P ⊓ c.L : Subgroup G) : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have hyP : y ∈ P := hy.1
      have hyL : y ∈ c.L := hy.2
      have hmemP : x * y * x⁻¹ * y⁻¹ ∈ P :=
        P.mul_mem (P.mul_mem (P.mul_mem hx.1 hyP) (P.inv_mem hx.1)) (P.inv_mem hyP)
      have hmemO : x * y * x⁻¹ * y⁻¹ ∈ CFSG.Open.pCoreOf 2 c.L := hxcomm.2 y hyL
      have hmem : x * y * x⁻¹ * y⁻¹ ∈ P ⊓ CFSG.Open.pCoreOf 2 c.L := ⟨hmemP, hmemO⟩
      rw [hdisj.eq_bot, Subgroup.mem_bot] at hmem
      calc y * x = (x * y * x⁻¹ * y⁻¹) * (y * x) := by rw [hmem, one_mul]
        _ = x * y := by group
    exact hxZ ⟨hx, hxcent⟩

end
end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONan

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONan
section
open CFSG.Open
open CFSG.LocalAnalysis.UniquenessCase.UC22 (Data Opp IsSpor IsAlt)
open CFSG.RankThree.PartOne (IsStronglyPEmbedded IsSylowOf)
open CFSG.RankThree.PartOne.StrongP (conjSub)
open CFSG.LocalAnalysis.UniquenessCase.UCK (ThreeCover)
open scoped commutatorElement Pointwise
variable {G : Type} [Group G] [Finite G] {D : Data G}
variable {G : Type} [Group G] [Finite G]
variable {D : Data G}

theorem propositionH_step1_wPH7
    (hK2 : K2ONanCentralizer) (c : Ctx82E3 D)
    (hON : UCK.ThreeCover (fun Y _ => IsSpor Y .ONan) c.Lbar) (h7 : D.sig = {7})
    {P : Subgroup G} (hP : CFSG.ABGLocalTools.IsSylowOf 3 P D.M)
    (hNZ : Subgroup.normalizer ((zSub P c.L : Subgroup G) : Set G) ≤ D.M)
    (hΓ : GammaP P D.M) {x : G} (hx : x ∈ P ⊓ c.L) (hx3 : orderOf x = 3)
    (hxZ : x ∉ zSub P c.L)
    (hT : CFSG.ABGLocalTools.IsSylowOf 3 (P ⊓ Subgroup.centralizer ({x} : Set G))
      (Subgroup.centralizer ({x} : Set G)))
    (hnot : ¬ Subgroup.centralizer ({x} : Set G) ≤ D.M) :
    IsStronglyPEmbedded 3 (pNstar x D.M) := by
  haveI : ((Subgroup.zpowers x).subgroupOf
      (Subgroup.centralizer ({x} : Set G))).Normal := pK_normal x
  obtain ⟨hxT, hnc⟩ := propositionH_F4'_wPH7 hK2 c hON h7 hP hNZ hx hx3 hxZ
  have h := strongly_embedded_quot_of_gamma (M := D.M) (P := P)
    (T := P ⊓ Subgroup.centralizer ({x} : Set G)) hT hx3 hxT inf_le_left
    (CFSG.ABGLocalTools.IsSylowOf.le hP) hΓ hnc hnot
  simpa [pNstar, pK, pH] using h

theorem not_isStronglyPEmbedded_of_normal_isPGroup_wPH7 {H : Type*} [Group H] [Finite H]
    {p : ℕ} [Fact p.Prime] {Y N : Subgroup H} (hY : IsStronglyPEmbedded p Y) [N.Normal]
    (hNp : IsPGroup p N) (hNne : N ≠ ⊥) : False := by
  obtain ⟨P, hP, hPY⟩ := hY.exists_isSylowOf_le
  let P' : Sylow p H := hP.2.1.toSylow (by simpa [Subgroup.relIndex_top_right] using hP.2.2)
  have hNP : N ≤ (P' : Subgroup H) := IsPGroup.le_sylow_of_normal hNp P'
  have hNY : N ≤ Y := hNP.trans hPY
  have hpN : p ∣ Nat.card N := by
    rcases hNp.card_eq_or_dvd with h | h
    · exact absurd (Subgroup.card_eq_one.mp h) hNne
    · exact h
  exact hY.not_dvd_card_of_normal_le hNY hpN

theorem not_isStronglyPEmbedded_of_normal_pQuotient_wPH7 {Y : Type} [Group Y] [Finite Y]
    {p : ℕ} [Fact p.Prime] {N M E : Subgroup Y} [N.Normal] [M.Normal]
    (hNM : N ≤ M) (hMp : IsPGroup p (M.map (QuotientGroup.mk' N))) (hMne : M ≠ N)
    (hpN : ¬ p ∣ Nat.card N)
    (hE : IsElemAbelian p E) (hEcard : Nat.card E = p ^ 2) :
    ∀ S : Subgroup Y, ¬ IsStronglyPEmbedded p S := by
  classical
  have hp : p.Prime := Fact.out
  have hcore : ∀ S : Subgroup Y, IsStronglyPEmbedded p S → E ≤ S → False := by
    intro S hS hES
    have hpower : ∀ e : E, e ^ p = 1 := fun e =>
      Subtype.ext (by simpa using hE.2 (e : Y) e.2)
    have hnormalized : E ≤ Subgroup.normalizer (N : Set Y) := by
      rw [N.normalizer_eq_top]
      exact le_top
    have hgen :=
      CFSG.RankThreeEvenClassification.Helpers.coprime_centralizer_generation_of_plane
        p hp E N hpower hEcard hpN hnormalized
    have hNS : N ≤ S := by
      rw [hgen]
      refine iSup_le fun e => iSup_le fun he => ?_
      have he1 : (e : Y) ≠ 1 := fun h => he (Subtype.ext h)
      have hpow : (e : Y) ^ p = 1 := by
        simpa using congrArg (Subtype.val) (hpower e)
      exact fun n hn => hS.centralizer_le he1 hpow (hES e.2) hn.2
    have hq := hS.map_quotient hNS hpN
    have hMne' : M.map (QuotientGroup.mk' N) ≠ ⊥ := by
      intro hbot
      have hle : M ≤ N := by
        have := (Subgroup.map_eq_bot_iff (f := QuotientGroup.mk' N) M).mp hbot
        simpa [QuotientGroup.ker_mk'] using this
      exact hMne (le_antisymm hle hNM)
    exact not_isStronglyPEmbedded_of_normal_isPGroup_wPH7
      (Y := S.map (QuotientGroup.mk' N)) (N := M.map (QuotientGroup.mk' N)) hq hMp hMne'
  intro S hS
  have hEp : IsPGroup p E := IsPGroup.of_card (n := 2) hEcard
  obtain ⟨Q, hEQ⟩ := hEp.exists_le_sylow
  have hQsyl : IsSylowOf p (Q : Subgroup Y) ⊤ :=
    ⟨le_top, Q.isPGroup', by rw [Subgroup.relIndex_top_right]; exact Q.not_dvd_index⟩
  obtain ⟨g, hg⟩ := hS.exists_conj_ge hQsyl
  exact hcore (CFSG.RankThree.PartOne.StrongP.conjSub g S) (hS.conj g) (hEQ.trans hg)

theorem not_isCyclic_of_isElemAbelian_card_nine_wPH7_wPH7 {Q : Type*} [Group Q]
    {E : Subgroup Q} (hE : IsElemAbelian 3 E) (hcard : Nat.card E = 9) :
    ¬ IsCyclic ↥E := by
  intro hCyc
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := ↥E)
  have htop : Subgroup.zpowers g = ⊤ := by
    ext x
    exact ⟨fun _ => Subgroup.mem_top x, fun _ => hg x⟩
  have hgen : orderOf g = 9 := by
    rw [← Nat.card_zpowers, htop, Subgroup.card_top, hcard]
  have hg3 : g ^ 3 = 1 := Subtype.ext (by simpa using hE.2 (g : Q) g.2)
  have hle : orderOf g ≤ 3 := orderOf_le_of_pow_eq_one (by norm_num : 0 < 3) hg3
  omega

theorem exists_elemAbelian_card_nine_of_isTripleCover_wPH7 {Q : Type*} [Group Q] [Finite Q]
    (hT : CFSG.RankThree.PartTwo.Sec4.IsTripleCover Q (alternatingGroup (Fin 6))) :
    ∃ E : Subgroup Q, IsElemAbelian 3 E ∧ Nat.card E = 9 := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hAne : Nonempty (Q ⧸ Subgroup.center Q ≃* alternatingGroup (Fin 6)) := hT.2
  obtain ⟨eA⟩ := hAne
  let Z : Subgroup Q := Subgroup.center Q
  haveI : Z.Normal := by dsimp [Z]; infer_instance
  have hZcard : Nat.card Z = 3 := hT.1
  let q : Q →* Q ⧸ Z := QuotientGroup.mk' Z
  let φ : Q →* alternatingGroup (Fin 6) := eA.toMonoidHom.comp q
  have hφ : Function.Surjective φ :=
    eA.surjective.comp (QuotientGroup.mk'_surjective Z)
  have hkerφ : φ.ker = Z := by
    ext x
    simpa [φ, q] using QuotientGroup.eq_one_iff (N := Z) x
  obtain ⟨E, hEel, hEge⟩ := CFSG.RankThree.PartTwo.Sec4.HeringOF.hasE9_alternatingGroup_six
  have hEp : IsPGroup 3 E := by
    rw [isPGroup_iff_exists_pow_pow_eq_one]
    exact ⟨1, fun x => Subtype.ext (by simpa using hEel.2 (x : alternatingGroup (Fin 6)) x.2)⟩
  obtain ⟨k, hk⟩ := hEp.exists_card_eq
  let R : Subgroup Q := E.comap φ
  have hRmap : R.map φ = E := Subgroup.map_comap_eq_self_of_surjective hφ E
  have hRcard : Nat.card R = 3 * Nat.card E := by
    have h := CFSG.GroupTheory.card_comap_eq_card_ker_mul_card φ hφ E
    rw [hkerφ, hZcard] at h
    exact h
  have hRp : IsPGroup 3 ↥R := by
    refine IsPGroup.of_card (n := k + 1) ?_
    rw [hRcard, hk, pow_succ]
    ring
  have hEcard : Nat.card E = 9 := by
    have hdvd : 3 ^ k ∣ 360 := by
      have h := Subgroup.card_subgroup_dvd_card E
      rw [hk] at h
      rw [nat_card_alternatingGroup] at h
      norm_num at h ⊢
      exact h
    have hk2 : k ≤ 2 := by
      by_contra h
      have h3 : 3 ^ 3 ∣ 3 ^ k := pow_dvd_pow 3 (by omega)
      exact (by norm_num : ¬ (27 : ℕ) ∣ 360) (h3.trans hdvd)
    have hk_ge : 2 ≤ k := by
      by_contra h
      have hk1 : k ≤ 1 := by omega
      have h3 : 3 ^ k ≤ 3 := by
        calc 3 ^ k ≤ 3 ^ 1 := pow_le_pow_right₀ (by norm_num) hk1
          _ = 3 := by norm_num
      rw [hk] at hEge
      omega
    have hk_eq : k = 2 := by omega
    rw [hk, hk_eq]
    norm_num
  have hRnc : ¬ IsCyclic ↥R := by
    intro hRcyc
    have hmapcyc : IsCyclic ↥(R.map φ) := by
      let ψ : ↥R →* ↥(R.map φ) :=
        (φ.comp R.subtype).codRestrict (R.map φ)
          (fun x => Subgroup.mem_map_of_mem φ x.2)
      exact isCyclic_of_surjective ψ (by
        intro y
        obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.mp y.2
        exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩)
    rw [hRmap] at hmapcyc
    exact not_isCyclic_of_isElemAbelian_card_nine_wPH7_wPH7 hEel hEcard hmapcyc
  obtain ⟨B, hB, hBel, hBcard⟩ :=
    CFSG.Quasithin.A1c.exists_isElemAbelian_card_sq (p := 3) (by norm_num) hRp hRnc
  exact ⟨B, hBel, hBcard⟩

theorem hasE9_of_exists_elemAbelian_card_nine_wPH7 {Q : Type*} [Group Q] [Finite Q]
    (h : ∃ E : Subgroup Q, IsElemAbelian 3 E ∧ Nat.card E = 9) :
    CFSG.GroupTheory.ThreeTranspositions.HasE9 Q := by
  classical
  obtain ⟨E, hE, hcard⟩ := h
  haveI hEnt : Nontrivial E := Finite.one_lt_card_iff_nontrivial.mp (by rw [hcard]; norm_num)
  obtain ⟨x, hx1⟩ := exists_ne (1 : E)
  have hxE : (x : Q) ∈ E := x.2
  have hx3 : (x : Q) ^ 3 = 1 := hE.2 (x : Q) x.2
  have hxord : orderOf (x : Q) = 3 := by
    have hdvd : orderOf (x : Q) ∣ 3 := orderOf_dvd_of_pow_eq_one hx3
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
    · exact absurd (orderOf_eq_one_iff.mp h1) (fun h => hx1 (Subtype.ext h))
    · exact h3
  have hxcard : Nat.card (Subgroup.zpowers (x : Q)) = 3 := by
    rw [Nat.card_zpowers, hxord]
  obtain ⟨y, hyE, hyx⟩ : ∃ y ∈ E, y ∉ Subgroup.zpowers (x : Q) := by
    by_contra hnot
    push Not at hnot
    have hsub : E ≤ Subgroup.zpowers (x : Q) := fun y hy => hnot y hy
    have hdvd : Nat.card E ∣ Nat.card (Subgroup.zpowers (x : Q)) :=
      Subgroup.card_dvd_of_le hsub
    rw [hcard, hxcard] at hdvd
    norm_num at hdvd
  have hy3 : y ^ 3 = 1 := hE.2 y hyE
  have hyord : orderOf y = 3 := by
    have hdvd : orderOf y ∣ 3 := orderOf_dvd_of_pow_eq_one hy3
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
    · exact absurd (orderOf_eq_one_iff.mp h1) (fun h =>
        hyx (by rw [h]; exact Subgroup.one_mem _))
    · exact h3
  have hcomm : Commute (x : Q) y := by
    have hc := hE.1.is_comm.comm (⟨(x : Q), hxE⟩ : E) (⟨y, hyE⟩ : E)
    exact congrArg Subtype.val hc
  exact ⟨(x : Q), y, hxord, hyord, hcomm, hyx⟩

theorem exists_elemAbelian_card_nine_of_quotient_wPH7 {Y : Type*} [Group Y] [Finite Y]
    {N : Subgroup Y} [N.Normal] (hN : ¬ 3 ∣ Nat.card N)
    (h : ∃ E : Subgroup (Y ⧸ N), IsElemAbelian 3 E ∧ Nat.card E = 9) :
    ∃ E : Subgroup Y, IsElemAbelian 3 E ∧ Nat.card E = 9 := by
  have hE9 : CFSG.GroupTheory.ThreeTranspositions.HasE9 (Y ⧸ N) :=
    hasE9_of_exists_elemAbelian_card_nine_wPH7 h
  have hlift : CFSG.GroupTheory.ThreeTranspositions.HasE9 Y :=
    CFSG.GroupTheory.ThreeTranspositions.hasE9_of_hasE9_quotient N hN hE9
  obtain ⟨x, y, hx, hy, hcomm, hyx⟩ := hlift
  have hxcard : Nat.card (Subgroup.zpowers x) = 3 := by rw [Nat.card_zpowers, hx]
  have hcomm' : ∀ a ∈ Subgroup.zpowers x, a * y = y * a := by
    intro a ha
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    exact (hcomm.zpow_left n).eq
  obtain ⟨hel, hcard⟩ :=
    CFSG.GroupTheory.isElemAbelian_sup_zpowers_of_commute (r := 3) hxcard hy hyx hcomm'
  exact ⟨Subgroup.zpowers x ⊔ Subgroup.zpowers y, hel, hcard⟩

theorem map_inf_comap_eq_wPH7_wPH7 {A B : Type*} [Group A] [Group B] (f : A →* B)
    (W : Subgroup A) (J : Subgroup B) : (W ⊓ J.comap f).map f = W.map f ⊓ J := by
  ext x
  constructor
  · rintro ⟨w, ⟨hw, hwJ⟩, rfl⟩
    exact ⟨⟨w, hw, rfl⟩, hwJ⟩
  · rintro ⟨⟨w, hw, rfl⟩, hJ⟩
    exact ⟨w, ⟨hw, hJ⟩, rfl⟩

theorem map_conjSub_wPH7_wPH7 {A B : Type*} [Group A] [Group B] (f : A →* B) (g : A)
    (T : Subgroup A) :
    (CFSG.RankThree.PartOne.StrongP.conjSub g T).map f =
      CFSG.RankThree.PartOne.StrongP.conjSub (f g) (T.map f) := by
  rw [CFSG.RankThree.PartOne.StrongP.conjSub, CFSG.RankThree.PartOne.StrongP.conjSub,
    Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply, map_mul]

theorem stronglyPEmbedded_comap_of_surjective_wPH7 {A B : Type*} [Group A] [Group B]
    [Finite A] [Finite B] {p : ℕ} [Fact p.Prime] (f : A →* B)
    (hf : Function.Surjective f) (hker : ¬ p ∣ Nat.card f.ker)
    {S : Subgroup B} (hS : IsStronglyPEmbedded p S) :
    IsStronglyPEmbedded p (S.comap f) := by
  classical
  set T : Subgroup A := S.comap f with hT
  have hker_le_T : f.ker ≤ T := by
    intro x hx
    rw [hT, Subgroup.mem_comap, MonoidHom.mem_ker.mp hx]
    exact S.one_mem
  have himgT : T.map f = S := Subgroup.map_comap_eq_self_of_surjective hf S
  have hcardT : Nat.card T = Nat.card f.ker * Nat.card S := by
    rw [hT]
    exact CFSG.GroupTheory.card_comap_eq_card_ker_mul_card f hf S
  refine ⟨?_, ?_, ?_⟩
  · intro htop
    apply hS.1
    rw [← himgT, htop, Subgroup.map_top, MonoidHom.range_eq_top.mpr hf]
  · rw [hcardT]
    exact dvd_mul_of_dvd_right hS.2.1 _
  · intro g hgT
    have hfg : f g ∉ S := fun h => hgT (Subgroup.mem_comap.mpr h)
    have hmap : (T ⊓ CFSG.RankThree.PartOne.StrongP.conjSub g T).map f =
        S ⊓ CFSG.RankThree.PartOne.StrongP.conjSub (f g) S := by
      have h1 : (CFSG.RankThree.PartOne.StrongP.conjSub g T).map f =
          CFSG.RankThree.PartOne.StrongP.conjSub (f g) (T.map f) := map_conjSub_wPH7_wPH7 f g T
      rw [inf_comm, map_inf_comap_eq_wPH7_wPH7 f (CFSG.RankThree.PartOne.StrongP.conjSub g T) S,
        hT, h1, himgT, inf_comm]
    let D : Subgroup A := T ⊓ CFSG.RankThree.PartOne.StrongP.conjSub g T
    let I : Subgroup B := S ⊓ CFSG.RankThree.PartOne.StrongP.conjSub (f g) S
    have hI : D.map f = I := hmap
    let φ : ↥D →* ↥I := (f.comp D.subtype).codRestrict I fun x => by
      have hx : (f.comp D.subtype) x ∈ D.map f := Subgroup.mem_map_of_mem f x.2
      rwa [hI] at hx
    have hφ : Function.Surjective φ := by
      intro y
      have hy : (y : B) ∈ D.map f := by rw [hI]; exact y.2
      obtain ⟨x, hx, hx'⟩ := Subgroup.mem_map.mp hy
      exact ⟨⟨x, hx⟩, Subtype.ext hx'⟩
    have hker_le_D : f.ker ≤ D := by
      refine le_inf hker_le_T ?_
      intro k hk
      rw [CFSG.RankThree.PartOne.StrongP.mem_conjSub_iff]
      exact hker_le_T (by
        simpa using (inferInstance : f.ker.Normal).conj_mem k hk g⁻¹)
    have hkerφ : Nat.card φ.ker = Nat.card f.ker := by
      have hkereq : φ.ker = f.ker.subgroupOf D := by
        ext x
        constructor
        · intro hx
          rw [MonoidHom.mem_ker] at hx
          rw [Subgroup.mem_subgroupOf]
          exact MonoidHom.mem_ker.mp (congrArg Subtype.val hx)
        · intro hx
          rw [MonoidHom.mem_ker]
          apply Subtype.ext
          exact MonoidHom.mem_ker.mp (Subgroup.mem_subgroupOf.mp hx)
      rw [hkereq, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hker_le_D).toEquiv]
    have hcardD : Nat.card D = Nat.card f.ker * Nat.card I := by
      have h := CFSG.GroupTheory.card_comap_eq_card_ker_mul_card φ hφ (⊤ : Subgroup ↥I)
      have h' : Nat.card D = Nat.card φ.ker * Nat.card I := by
        simpa [Subgroup.comap_top] using h
      rwa [hkerφ] at h'
    intro hdvd
    rw [hcardD] at hdvd
    rcases (Fact.out : p.Prime).dvd_mul.mp hdvd with h | h
    · exact hker h
    · exact hS.2.2 (f g) hfg h

theorem propositionH_step43''_wPH7
    (hK2 : K2ONanCentralizer) (c : Ctx82E3 D)
    (hON : UCK.ThreeCover (fun Y _ => IsSpor Y .ONan) c.Lbar) (h7 : D.sig = {7})
    {P : Subgroup G} (hP : CFSG.ABGLocalTools.IsSylowOf 3 P D.M)
    {x : G} (hx : x ∈ P ⊓ c.L) (hx3 : orderOf x = 3) (hxZ : x ∉ zSub P c.L)
    (hF9 : F9PerfectCore c P x) :
    ∀ S : Subgroup ↥(pIbar x c.L), ¬ IsStronglyPEmbedded 3 S := by
  classical
  let I := perfectCoreL c x
  let N : Subgroup ↥I := CFSG.pCore 2 ↥I
  haveI hNnormal : N.Normal := CFSG.pCore_normal
  have hIeq : I = pI x c.L := by
    dsimp [I]
    symm
    rw [pI, perfectCoreL, CFSG.Quasithin.perfectCore_eq_map_perfectResidual, inSubgroup, pH,
      inf_comm]
  have hT : CFSG.RankThree.PartTwo.Sec4.IsTripleCover (↥I ⧸ N)
      (alternatingGroup (Fin 6)) := hF9.1
  have hpN : ¬ 3 ∣ Nat.card N := by
    obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥I)).exists_card_eq
    rw [hk]
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp
      (Nat.Coprime.pow_right k (by norm_num))
  have hQ9 : ∃ E : Subgroup (↥I ⧸ N), IsElemAbelian 3 E ∧ Nat.card E = 9 :=
    exists_elemAbelian_card_nine_of_isTripleCover_wPH7 hT
  obtain ⟨E, hEel, hEcard⟩ :=
    exists_elemAbelian_card_nine_of_quotient_wPH7 (Y := ↥I) (N := N) hpN hQ9
  let Zbar : Subgroup (↥I ⧸ N) := Subgroup.center (↥I ⧸ N)
  let M : Subgroup ↥I := Zbar.comap (QuotientGroup.mk' N)
  haveI hZbarNormal : Zbar.Normal := by dsimp [Zbar]; infer_instance
  haveI hMnormal : M.Normal := inferInstance
  have hNM : N ≤ M := by
    intro n hn
    simp only [M, Subgroup.mem_comap]
    have hn1 : QuotientGroup.mk' N n = 1 := by
      rw [← MonoidHom.mem_ker, QuotientGroup.ker_mk']
      exact hn
    rw [hn1]
    exact Subgroup.one_mem Zbar
  have hMmap : M.map (QuotientGroup.mk' N) = Zbar :=
    Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective N) Zbar
  have hMp : IsPGroup 3 (M.map (QuotientGroup.mk' N)) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [hMmap, hT.1]
    norm_num
  have hMne : M ≠ N := by
    intro hMN
    have hbot : M.map (QuotientGroup.mk' N) = ⊥ := by rw [hMN]; simp
    rw [hMmap] at hbot
    have hZ3 : Nat.card Zbar = 3 := hT.1
    rw [hbot] at hZ3
    simp at hZ3
  have hno : ∀ S : Subgroup ↥I, ¬ IsStronglyPEmbedded 3 S :=
    not_isStronglyPEmbedded_of_normal_pQuotient_wPH7 (Y := ↥I) (p := 3)
      (N := N) (M := M) (E := E) hNM hMp hMne hpN hEel hEcard
  intro S hS
  let inc : ↥I →* ↥(pH x) := Subgroup.inclusion (by
    dsimp [I]
    exact (perfectCoreL_le c x).trans inf_le_right)
  let φ₀ : ↥I →* pX x := (QuotientGroup.mk' (pDK x)).comp inc
  have hrange₀ : φ₀.range = pIbar x c.L := by
    ext z
    constructor
    · rintro ⟨y, rfl⟩
      rw [pIbar]
      refine Subgroup.mem_map_of_mem (QuotientGroup.mk' (pDK x))
        (Subgroup.mem_subgroupOf.mpr ?_)
      have hyI : (y : G) ∈ pI x c.L := by
        rw [← hIeq]
        exact y.2
      have hcoe : ((inc y : ↥(pH x)) : G) = (y : G) := Subgroup.coe_inclusion _ y
      rw [hcoe]
      exact hyI
    · intro hz
      rw [pIbar] at hz
      obtain ⟨w, hw, hwz⟩ := Subgroup.mem_map.mp hz
      have hwI : (w : G) ∈ I := by
        rw [hIeq]
        exact Subgroup.mem_subgroupOf.mp hw
      refine ⟨⟨(w : G), hwI⟩, ?_⟩
      dsimp only [φ₀, MonoidHom.comp_apply]
      rw [← hwz]
      congr 1
  let e : ↥(φ₀.range) ≃* ↥(pIbar x c.L) := MulEquiv.subgroupCongr hrange₀
  let φbar : ↥I →* ↥(pIbar x c.L) := e.toMonoidHom.comp φ₀.rangeRestrict
  have hφbar : Function.Surjective φbar :=
    e.surjective.comp φ₀.rangeRestrict_surjective
  have hker_iff : ∀ y : ↥I, φbar y = 1 ↔ φ₀ y = 1 := by
    intro y
    have h1 : φbar y = 1 ↔ φ₀.rangeRestrict y = 1 := by
      change e (φ₀.rangeRestrict y) = 1 ↔ φ₀.rangeRestrict y = 1
      exact e.map_eq_one_iff
    have h2 : φ₀.rangeRestrict y = 1 ↔ φ₀ y = 1 := by
      constructor
      · intro h
        exact congrArg Subtype.val h
      · intro h
        exact Subtype.ext h
    exact h1.trans h2
  have hker_image : ∀ y : ↥I, y ∈ φbar.ker →
      (y : G) ∈ (CFSG.pCore 2 ↥(pI x c.L)).map (pI x c.L).subtype := by
    intro y hy
    have hy1 : φ₀ y = 1 := (hker_iff y).mp (MonoidHom.mem_ker.mp hy)
    have hmemH : inc y ∈ pDK x := by
      have hv : φ₀ y = 1 := hy1
      have hq1 : QuotientGroup.mk' (pDK x) (inc y) = 1 := by
        simpa [φ₀] using hv
      exact (QuotientGroup.eq_one_iff (N := pDK x) (inc y)).mp hq1
    have hyI : (y : G) ∈ pI x c.L := by rw [← hIeq]; exact y.2
    have hmem : (y : G) ∈ pI x c.L ⊓ ((pDK x).map (pH x).subtype) :=
      ⟨hyI, Subgroup.mem_map_of_mem (pH x).subtype hmemH⟩
    exact propositionH_step41''' hK2 c hON h7 hP hx hx3 hxZ hmem
  have hpker : ¬ 3 ∣ Nat.card φbar.ker := by
    have hsub : φbar.ker.map I.subtype ≤
        (CFSG.pCore 2 ↥(pI x c.L)).map (pI x c.L).subtype := by
      rintro g ⟨y, hy, rfl⟩
      exact hker_image y hy
    have h2map : IsPGroup 2 ((CFSG.pCore 2 ↥(pI x c.L)).map (pI x c.L).subtype) :=
      IsPGroup.map (CFSG.pCore_isPGroup (p := 2) (G := ↥(pI x c.L))) _
    have h2img : IsPGroup 2 (φbar.ker.map I.subtype) := IsPGroup.to_le h2map hsub
    let ψ : ↥(φbar.ker) →* ↥(φbar.ker.map I.subtype) :=
      (I.subtype.comp φbar.ker.subtype).codRestrict _
        (fun y => Subgroup.mem_map_of_mem _ y.2)
    have hψ : Function.Injective ψ := by
      intro a b hab
      apply Subtype.ext
      have h := congrArg Subtype.val hab
      simpa [ψ] using h
    have h2 : IsPGroup 2 ↥(φbar.ker) := IsPGroup.of_injective h2img ψ hψ
    obtain ⟨k, hk⟩ := h2.exists_card_eq
    rw [hk]
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp
      (Nat.Coprime.pow_right k (by norm_num))
  exact hno (S.comap φbar) (stronglyPEmbedded_comap_of_surjective_wPH7 φbar hφbar hpker hS)

theorem propositionH_step44'_wPH7 (hK2 : K2ONanCentralizer) (c : Ctx82E3 D)
    (hON : UCK.ThreeCover (fun Y _ => IsSpor Y .ONan) c.Lbar) (h7 : D.sig = {7})
    {P : Subgroup G} (hP : CFSG.ABGLocalTools.IsSylowOf 3 P D.M)
    {x : G} (hx : x ∈ P ⊓ c.L) (hx3 : orderOf x = 3) (hxZ : x ∉ zSub P c.L)
    (hNbar : IsStronglyPEmbedded 3 (pNbar x D.M))
    (h43 : ∀ S : Subgroup ↥(pIbar x c.L), ¬ IsStronglyPEmbedded 3 S)
    (h42 : ¬ CFSG.HallHigman.IsPSolvable 3 ↥(pIbar x c.L) ∧
      360 < Nat.card ↥(pIbar x c.L) ∧
      pIbar x c.L ≤ Opp 3 (⊤ : Subgroup (pX x))) :
    ∃ g : pX x, pIbar x c.L ≤ (pNbar x D.M).map (MulAut.conj g).toMonoidHom := by
  classical
  letI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h3dvd : 3 ∣ Nat.card ↥(pIbar x c.L) := by
    by_contra h3
    have hcop : Nat.Coprime 3 (Nat.card ↥(pIbar x c.L)) :=
      (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3
    exact h42.1 (fun H _ T _ _ => Or.inr
      (Nat.Coprime.coprime_dvd_right
        (T.index_dvd_card.trans (Subgroup.card_subgroup_dvd_card H)) hcop))
  obtain ⟨Q⟩ : Nonempty (Sylow 3 ↥(pIbar x c.L)) := inferInstance
  let Q' : Subgroup (pX x) := (Q : Subgroup ↥(pIbar x c.L)).map (pIbar x c.L).subtype
  obtain ⟨P', hQ'P'⟩ := Q.isPGroup'.map (pIbar x c.L).subtype |>.exists_le_sylow
  have hP'syl : CFSG.RankThree.PartOne.IsSylowOf 3 (P' : Subgroup (pX x)) ⊤ :=
    ⟨le_top, P'.isPGroup', by
      rw [Subgroup.relIndex_top_right]
      exact P'.not_dvd_index⟩
  obtain ⟨g, hg⟩ := hNbar.exists_conj_ge hP'syl
  have hQ'le : Q' ≤ conjSub g (pNbar x D.M) := hQ'P'.trans hg
  refine ⟨g, ?_⟩
  by_contra hnot
  have hQ'ne : Q' ≠ ⊥ := by
    intro hbot
    apply Sylow.ne_bot_of_dvd_card Q h3dvd
    exact (Subgroup.map_eq_bot_iff_of_injective _ (pIbar x c.L).subtype_injective).mp hbot
  have hpQ' : 3 ∣ Nat.card Q' := by
    rcases (Q.isPGroup'.map (pIbar x c.L).subtype).card_eq_or_dvd with h | h
    · exact absurd (Subgroup.card_eq_one.mp h) hQ'ne
    · exact h
  have hdvd : 3 ∣ Nat.card (pIbar x c.L ⊓ conjSub g (pNbar x D.M) : Subgroup (pX x)) :=
    hpQ'.trans (Subgroup.card_dvd_of_le (le_inf (Subgroup.map_subtype_le _) hQ'le))
  exact h43 _ ((hNbar.conj g).subgroupOf hnot hdvd)

theorem propositionH_contradiction''
    (hK35w : UCK.K35w) (hK2 : K2ONanCentralizer)
    (c : Ctx82E3 D)
    (hON : UCK.ThreeCover (fun Y _ => IsSpor Y .ONan) c.Lbar) (h7 : D.sig = {7})
    {P : Subgroup G} (hP : CFSG.ABGLocalTools.IsSylowOf 3 P D.M)
    (hNZ : Subgroup.normalizer ((zSub P c.L : Subgroup G) : Set G) ≤ D.M)
    (hΓ : GammaP P D.M) {x : G} (hx : x ∈ P ⊓ c.L) (hx3 : orderOf x = 3)
    (hxZ : x ∉ zSub P c.L)
    (hT : CFSG.ABGLocalTools.IsSylowOf 3 (P ⊓ Subgroup.centralizer ({x} : Set G))
      (Subgroup.centralizer ({x} : Set G)))
    (hnot : ¬ Subgroup.centralizer ({x} : Set G) ≤ D.M) : False := by
  have h1 := propositionH_step1_wPH7 hK2 c hON h7 hP hNZ hΓ hx hx3 hxZ hT hnot
  have h2 := propositionH_step2'_wPH7 hK2 c hON h7 hP hNZ hx hx3 hxZ h1
  have h3 := propositionH_step3 hK35w c h2
  have h42 := propositionH_step42'''' hK2 c hON h7 hP hx hx3 hxZ
  have hF9 := f9_perfectCore' (c := c) (P := P) (a := x) hON hP hx hx3 hxZ hK2
  have hF9' : F9PerfectCore c P x := ⟨hF9.1, hF9.2.1, hF9.2.2.1⟩
  have h43 := propositionH_step43''_wPH7 hK2 c hON h7 hP hx hx3 hxZ hF9'
  have h44 := propositionH_step44'_wPH7 hK2 c hON h7 hP hx hx3 hxZ h2.1 h43 h42
  exact propositionH_step5 hK35w c h3 h42 h44

end
end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONan

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONan
section
open CFSG.Open
open CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo.Sec4
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.LocalAnalysis.UniquenessCase.UC22 (Data IsSpor)
variable {G : Type} [Group G] [Finite G]
variable {D : Data G}

theorem centralizer_le_of_gamma'
    (hK35w : UCK.K35w) (hK2 : K2ONanCentralizer)
    (hK6 : K6ONanClasses) (c : Ctx82E3 D)
    (hON : UCK.ThreeCover (fun Y _ => IsSpor Y .ONan) c.Lbar) (h7 : D.sig = {7})
    {P : Subgroup G} (hP : CFSG.ABGLocalTools.IsSylowOf 3 P D.M)
    (hNZ : Subgroup.normalizer ((zSub P c.L : Subgroup G) : Set G) ≤ D.M)
    (hΓ : GammaP P D.M) :
    ∀ x ∈ P ⊓ c.L, orderOf x = 3 → x ∉ zSub P c.L →
      Subgroup.centralizer ({x} : Set G) ≤ D.M := by
  intro x hx hx3 hxZ
  obtain ⟨y, hy, hy3, hyZ, hT, hiff⟩ :=
    exists_sylow_centralizer_of_gamma' hK6 c hON h7 hP hNZ x hx hx3 hxZ
  by_contra hnot
  exact propositionH_contradiction'' hK35w hK2 c hON h7 hP hNZ hΓ hy hy3 hyZ hT
    (fun hle => hnot (hiff.mp hle))

end
end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONan
