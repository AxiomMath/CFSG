module

public import CFSG.RankThree.PartTwo.Sec15.Sylow155R1Defs
public import CFSG.RankThree.PartTwo.Sec15.Sylow155R1MidDefs
import CFSG.RankThree.PartTwo.Sec15.Sylow155R1L65
import CFSG.RankThree.PartTwo.Sec15.Sylow155R1L140
import CFSG.RankThree.PartTwo.Sec15.Sylow155R1R0
import CFSG.RankThree.PartTwo.Sec15.Sylow155R1Ker
import CFSG.RankThree.PartTwo.Sec15.Sylow155R1MidGrp
import CFSG.RankThree.PartTwo.Sec4.StepsBender
public import CFSG.RankThree.PartTwo.Sec15.Gagen155Y1Defs
public import CFSG.RankThree.PartTwo.Sec15.Sylow155Swap
public import CFSG.RankThree.PartTwo.Sec4.Census.Open46
public import CFSG.RankThree.PartTwo.Sec4.Item41Narrow

public section

namespace CFSG.RankThree.PartTwo.Sec15.Sylow155R1

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS

variable {G : Type} [Group G] [Finite G]

private theorem conjNormal_eq_one_iff {Q : Type*} [Group Q] {N : Subgroup Q} [N.Normal] (x : Q) :
    (MulAut.conjNormal x : MulAut ↥N) = 1 ↔ ∀ y ∈ N, x * y = y * x := by
  constructor
  · intro h y hy
    have h1 : (MulAut.conjNormal x : MulAut ↥N) ⟨y, hy⟩ = ⟨y, hy⟩ := by rw [h]; rfl
    have h2 := congrArg Subtype.val h1
    simp only [MulAut.conjNormal_apply] at h2
    exact mul_inv_eq_iff_eq_mul.mp h2
  · intro h
    refine MulEquiv.ext fun y => Subtype.ext ?_
    rw [MulAut.conjNormal_apply, MulAut.one_apply, h y y.2, mul_inv_cancel_right]

private theorem center_eq_bot_of_isComponent {Q : Type*} [Group Q] {Yc : Subgroup Q}
    (hYc : CFSG.IsComponent Yc) (hs : IsSimpleGroup ↥Yc) : Subgroup.center ↥Yc = ⊥ := by
  haveI := hs
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center ↥Yc) with h | h
  · exact h
  · exfalso
    haveI : Nontrivial (↥Yc ⧸ Subgroup.center ↥Yc) := hYc.1.2.1.toNontrivial
    obtain ⟨q, hq⟩ := exists_ne (1 : ↥Yc ⧸ Subgroup.center ↥Yc)
    induction q using QuotientGroup.induction_on with
    | H x => exact hq ((QuotientGroup.eq_one_iff x).mpr (h ▸ Subgroup.mem_top x))

private theorem odd_orderOf_of_mem_pPrimeCoreOf_two {K : Subgroup G} {g : G}
    (hg : g ∈ pPrimeCoreOf 2 K) : Odd (orderOf g) := by
  obtain ⟨g₀, hg₀N, rfl⟩ := hg
  have h1 : orderOf (K.subtype g₀) =
      orderOf (⟨g₀, hg₀N⟩ : ↥(CFSG.pPrimeCore 2 ↥K)) := by
    rw [Subgroup.orderOf_mk]
    exact Subgroup.orderOf_coe g₀
  rw [h1]
  have hc : Nat.Coprime 2 (orderOf (⟨g₀, hg₀N⟩ : ↥(CFSG.pPrimeCore 2 ↥K))) :=
    Nat.Coprime.coprime_dvd_right (orderOf_dvd_natCard _) CFSG.pPrimeCore_coprime_card
  exact Nat.odd_iff.mpr (by
    have := (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mp hc
    omega)

private theorem centralizer_le_res1C (A L : Subgroup G) :
    Subgroup.centralizer (A : Set G) ≤ Res1C A L := fun x hx =>
  Subgroup.mem_centralizer_iff.mpr fun b hb =>
    Subgroup.mem_centralizer_iff.mp hx b (Subgroup.mem_inf.mp hb).1

private theorem conj_mem_pCoreOf {M : Subgroup G} {m v : G} (hm : m ∈ M)
    (hv : v ∈ CFSG.Open.pCoreOf 2 M) : m * v * m⁻¹ ∈ CFSG.Open.pCoreOf 2 M :=
  (Subgroup.mem_normalizer_iff.mp (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M hm) v).mp hv

private theorem orderOf_res1_point {A : Subgroup G} {c : G} {L : Subgroup G}
    {Yc : Subgroup (Res1Q A L)} (hS : Sec14Std G A c L) {c' : ↥(Res1C A L)}
    (hc'Y : QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(Res1C A L)) c' ∈ Yc) (hc' : (c' : G) = c) :
    orderOf (⟨_, hc'Y⟩ : ↥Yc) = 3 := by
  have hN : ¬ 3 ∣ Nat.card (CFSG.pPrimeCore 3 ↥(Res1C A L)) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp CFSG.pPrimeCore_coprime_card
  have hcmem := zpowers_mem_omegaA_iff.mp hS.zpowers_mem_omegaA
  have hc3 : orderOf c = 3 := by
    rw [← Nat.card_zpowers]
    exact hcmem.2.1
  have hcc : c ^ 3 = 1 := hc3 ▸ pow_orderOf_eq_one c
  have hc'3 : c' ^ 3 = 1 := Subtype.ext (by simpa [hc'] using hcc)
  have hy3 : (⟨_, hc'Y⟩ : ↥Yc) ^ 3 = 1 := by
    apply Subtype.ext
    show QuotientGroup.mk' _ c' ^ 3 = 1
    rw [← map_pow, hc'3, map_one]
  refine orderOf_eq_prime hy3 fun h => ?_
  have h1 : QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(Res1C A L)) c' = 1 := congrArg Subtype.val h
  have hcN : c' ∈ CFSG.pPrimeCore 3 ↥(Res1C A L) := (QuotientGroup.eq_one_iff c').mp h1
  have hc'1 : c' = 1 :=
    Sec4.eq_one_of_pow_prime_pow_eq_one Nat.prime_three hN hcN (a := 1) (by simpa using hc'3)
  have hc1 : c = 1 := by rw [← hc', hc'1]; rfl
  rw [hc1, orderOf_one] at hc3
  omega

theorem res1_eq_one_of_mem_of_centralizes (h1 : Sec4.Item4_1LargePrime)
    (h2 : Sec4.Item4_1ThreeCover) (h43 : Sec4.Item4_3) (hin : Sec4.Census.CoverInputs46)
    (h143 : Y1SecondFormExcl) {A L : Subgroup G} {c : G} (hR : Sec15R G A c L)
    (hW : Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G))
    (h142 : Concl142 A (lB A)) {X K Y M T : Subgroup G} (hC : Ctx155 A X K Y M T)
    {Yc : Subgroup (Res1Q A L)} (hY : Res1AtOf A c L M Yc) (hsimple : IsSimpleGroup ↥Yc)
    {u : ↥(Res1C A L)} (hu : (u : G) ∈ Subgroup.centralizer (A : Set G) ⊓ M)
    (huZ : (u : G) ∈ Subgroup.centralizer (delta A (lB A) (CFSG.Open.pCoreOf 2 M) : Set G))
    (hodd : Odd (orderOf u)) (hu3 : Nat.Coprime (orderOf u) 3)
    (huY : ∀ y ∈ Yc, QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(Res1C A L)) u * y =
      y * QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(Res1C A L)) u) :
    u = 1 := by
  obtain ⟨hhyp, -, -, hcomp, -⟩ := hY
  have hS := hR.toSec14Std
  have hcL : c ∉ L := res1_not_mem hS hcomp
  have hπ3 : Nat.Coprime (orderOf (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(Res1C A L)) u)) 3 :=
    Nat.Coprime.coprime_dvd_left (orderOf_map_dvd _ _) hu3
  have h1' := res1_eq_one_of_centralizes hS hhyp hcomp hsimple hπ3 huY
  have huΘ : u ∈ CFSG.pPrimeCore 3 ↥(Res1C A L) := (QuotientGroup.eq_one_iff u).mp h1'
  have hval : (u : G) = 1 :=
    res1_eq_one_of_mem_pPrimeCoreOf h1 h2 h43 hin h143 hR hW h142 hC hhyp hcL hu huZ
      (by rwa [Subgroup.orderOf_coe]) ⟨u, huΘ, rfl⟩
  exact Subtype.ext hval

private theorem res1_comm_point {A L : Subgroup G} {c : G} (hcA : c ∈ A)
    {c' x : ↥(Res1C A L)} (hc' : (c' : G) = c)
    (hx : (x : G) ∈ Subgroup.centralizer (A : Set G)) :
    QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(Res1C A L)) x *
        QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(Res1C A L)) c' =
      QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(Res1C A L)) c' *
        QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(Res1C A L)) x := by
  rw [← map_mul, ← map_mul]
  congr 1
  apply Subtype.ext
  show (x : G) * (c' : G) = (c' : G) * (x : G)
  rw [hc']
  exact (Subgroup.mem_centralizer_iff.mp hx c hcA).symm

private theorem res1_eq_one_of_mem_layerOddPreimage (h1 : Sec4.Item4_1LargePrime)
    (h2 : Sec4.Item4_1ThreeCover) (h43 : Sec4.Item4_3) (hin : Sec4.Census.CoverInputs46)
    (h143 : Y1SecondFormExcl) {A L : Subgroup G} {c : G} (hR : Sec15R G A c L)
    (hW : Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G))
    (h142 : Concl142 A (lB A)) {X K Y M T P : Subgroup G} (hC : Ctx155 A X K Y M T)
    (hE : End155N A X K Y M T P) (h146 : Item146 A (lB A)) (hRP : CFSG.Open.pCoreOf 2 Y ≤ P)
    (hIX : delta A (lB A) M ≤ Subgroup.normalizer (X : Set G)) {Yc : Subgroup (Res1Q A L)}
    (hY : Res1AtOf A c L M Yc) (hsimple : IsSimpleGroup ↥Yc)
    (hEA : layerOddPreimage
        (delta A (lB A) (CFSG.Open.pCoreOf 2 Y ⊔ pPrimeCoreOf 3 (u155 A M X))) ≤
      Subgroup.centralizer (A : Set G))
    {u : ↥(Res1C A L)} (hu : (u : G) ∈ layerOddPreimage
      (delta A (lB A) (CFSG.Open.pCoreOf 2 Y ⊔ pPrimeCoreOf 3 (u155 A M X))))
    (hodd : Odd (orderOf u))
    (huY : ∀ y ∈ Yc, QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(Res1C A L)) u * y =
      y * QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(Res1C A L)) u) :
    u = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS := hR.toSec14Std
  set H := delta A (lB A) (CFSG.Open.pCoreOf 2 Y ⊔ pPrimeCoreOf 3 (u155 A M X)) with hHdef
  obtain ⟨hHQ, hRH, -, -⟩ := Sylow155B1.delta_host_facts hS h146 hC hE hRP
    (Sylow155S.sup_mem_invariant hC hE hRP) (Sylow155S.sup_le_u155 hE hRP)
    (Sylow155S.p_le_normalizer_sup hE) le_sup_left
  have hHI : H ≤ delta A (lB A) M :=
    (delta_le _).trans ((Sylow155S.sup_le_u155 hE hRP).trans inf_le_left)
  have hHM : H ≤ M := hHI.trans (delta_le M)
  obtain ⟨-, hIZ⟩ := Sylow155B1.delta_pCore_facts hS h146 hC
  have hZH : delta A (lB A) (CFSG.Open.pCoreOf 2 M) ≤ H :=
    (Sylow155B1.delta_pCore_le_r hS h146 hC hE hIX).trans hRH
  have hZ2 : IsPGroup 2 (delta A (lB A) (CFSG.Open.pCoreOf 2 M)) :=
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M).to_le (delta_le _)
  have hEZ : layerOddPreimage H ≤
      Subgroup.centralizer (delta A (lB A) (CFSG.Open.pCoreOf 2 M) : Set G) :=
    layerOddPreimage_le_centralizer hZ2 hZH (hHI.trans hIZ)
  have hEH : layerOddPreimage H ≤ H := layerOddPreimage_le_self H
  have hH3 : ¬ 3 ∣ Nat.card H := (isPiSubgroup_piCompl_iff Nat.prime_three H).mp hHQ.1.2.1
  have hu3 : Nat.Coprime (orderOf u) 3 := by
    have hdvd := orderOf_dvd_natCard (⟨(u : G), hEH hu⟩ : ↥H)
    rw [Subgroup.orderOf_mk, Subgroup.orderOf_coe] at hdvd
    exact Nat.Coprime.coprime_dvd_left hdvd
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hH3).symm
  exact res1_eq_one_of_mem_of_centralizes h1 h2 h43 hin h143 hR hW h142 hC hY hsimple
    (Subgroup.mem_inf.mpr ⟨hEA hu, hHM (hEH hu)⟩) (hEZ hu) hodd hu3 huY

theorem res1_eq_one_of_mem_pPrimeCoreOf_two (h1 : Sec4.Item4_1LargePrime)
    (h2 : Sec4.Item4_1ThreeCover) (h43 : Sec4.Item4_3) (hin : Sec4.Census.CoverInputs46)
    (h143 : Y1SecondFormExcl) {A L : Subgroup G} {c : G} (hR : Sec15R G A c L)
    (hW : Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G))
    (h142 : Concl142 A (lB A)) {X K Y M T P : Subgroup G} (hC : Ctx155 A X K Y M T)
    (hE : End155N A X K Y M T P) (h146 : Item146 A (lB A)) (hRP : CFSG.Open.pCoreOf 2 Y ≤ P)
    (hIX : delta A (lB A) M ≤ Subgroup.normalizer (X : Set G)) {Yc : Subgroup (Res1Q A L)}
    (hY : Res1AtOf A c L M Yc) (hsimple : IsSimpleGroup ↥Yc)
    (hEA : layerOddPreimage
        (delta A (lB A) (CFSG.Open.pCoreOf 2 Y ⊔ pPrimeCoreOf 3 (u155 A M X))) ≤
      Subgroup.centralizer (A : Set G))
    {u : ↥(Res1C A L)} (hu : (u : G) ∈ pPrimeCoreOf 2
      (delta A (lB A) (CFSG.Open.pCoreOf 2 Y ⊔ pPrimeCoreOf 3 (u155 A M X))))
    (huY : ∀ y ∈ Yc, QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(Res1C A L)) u * y =
      y * QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(Res1C A L)) u) :
    u = 1 :=
  res1_eq_one_of_mem_layerOddPreimage h1 h2 h43 hin h143 hR hW h142 hC hE h146 hRP hIX hY hsimple
    hEA (pPrimeCoreOf_two_le_layerOddPreimage _ hu)
    (by rw [← Subgroup.orderOf_coe]; exact odd_orderOf_of_mem_pPrimeCoreOf_two hu) huY

theorem res1_layerOddPreimage_eq_of_autSolv (h1 : Sec4.Item4_1LargePrime)
    (h2 : Sec4.Item4_1ThreeCover) (h43 : Sec4.Item4_3) (hin : Sec4.Census.CoverInputs46)
    (h143 : Y1SecondFormExcl) {A L : Subgroup G} {c : G} (hR : Sec15R G A c L)
    (hW : Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G))
    (h142 : Concl142 A (lB A)) {X K Y M T P : Subgroup G} (hC : Ctx155 A X K Y M T)
    (hE : End155N A X K Y M T P) (h146 : Item146 A (lB A)) (hRP : CFSG.Open.pCoreOf 2 Y ≤ P)
    (hIX : delta A (lB A) M ≤ Subgroup.normalizer (X : Set G)) {Yc : Subgroup (Res1Q A L)}
    (hY : Res1AtOf A c L M Yc) (hsimple : IsSimpleGroup ↥Yc) (hsolv : Res1AutSolv ↥Yc)
    (hEA : layerOddPreimage
        (delta A (lB A) (CFSG.Open.pCoreOf 2 Y ⊔ pPrimeCoreOf 3 (u155 A M X))) ≤
      Subgroup.centralizer (A : Set G)) :
    layerOddPreimage (delta A (lB A) (CFSG.Open.pCoreOf 2 Y ⊔ pPrimeCoreOf 3 (u155 A M X))) =
      pPrimeCoreOf 2 (delta A (lB A) (CFSG.Open.pCoreOf 2 Y ⊔ pPrimeCoreOf 3 (u155 A M X))) := by
  classical
  have hS := hR.toSec14Std
  set H := delta A (lB A) (CFSG.Open.pCoreOf 2 Y ⊔ pPrimeCoreOf 3 (u155 A M X)) with hHdef
  set E₀ := layerOddPreimage H with hE₀def
  have hY' := hY
  obtain ⟨hhyp, -, -, ⟨hYcomp, hcY, -⟩, -⟩ := hY'
  haveI hYn : Yc.Normal := res1_isComponent_normal hS hhyp hYcomp
  set C := Res1C A L with hCdef
  set π := QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥C) with hπdef
  let ρ : Res1Q A L →* MulAut ↥Yc := MulAut.conjNormal
  have hEC : E₀ ≤ C := hEA.trans (centralizer_le_res1C A L)
  have hcA : c ∈ A := (zpowers_mem_omegaA_iff.mp hS.zpowers_mem_omegaA).1
  obtain ⟨c', hc'Y, hc'⟩ := hcY
  have hc'val : (c' : G) = c := hc'
  set y : ↥Yc := ⟨π c', hc'Y⟩ with hydef
  have hy : orderOf y = 3 := orderOf_res1_point hS hc'Y hc'val
  have hfixy : ∀ x : ↥C, (x : G) ∈ Subgroup.centralizer (A : Set G) → ρ (π x) y = y := by
    intro x hx
    apply Subtype.ext
    show π x * π c' * (π x)⁻¹ = π c'
    rw [mul_inv_eq_iff_eq_mul]
    exact res1_comm_point hcA hc'val hx
  let φ : ↥E₀ →* MulAut ↥Yc := ρ.comp (π.comp (Subgroup.inclusion hEC))
  have hφrange : Group.IsSolvable φ.range := by
    refine hsolv y hy φ.range ?_
    rintro _ ⟨e, rfl⟩
    exact hfixy (Subgroup.inclusion hEC e) (hEA e.2)
  have hφker : ∀ x ∈ φ.ker, Odd (orderOf x) → x = 1 := by
    intro x hx hodd
    have hρ : ρ (π (Subgroup.inclusion hEC x)) = 1 := MonoidHom.mem_ker.mp hx
    have h1 := res1_eq_one_of_mem_layerOddPreimage h1 h2 h43 hin h143 hR hW h142 hC hE h146 hRP
      hIX hY hsimple hEA (u := Subgroup.inclusion hEC x) x.2
      (by rw [orderOf_injective _ (Subgroup.inclusion_injective hEC)]; exact hodd)
      ((conjNormal_eq_one_iff (π (Subgroup.inclusion hEC x))).mp hρ)
    exact Subgroup.inclusion_injective hEC (by rw [h1, map_one])
  exact layerOddPreimage_eq_of_isSolvable (isSolvable_of_ker_odd_eq_one φ hφrange hφker)

theorem res1_comm_of_autFix {A L : Subgroup G} {c : G} (hS : Sec14Std G A c L)
    (h142 : Concl142 A (lB A)) {X K Y M T P : Subgroup G} (hC : Ctx155 A X K Y M T)
    (hE : End155N A X K Y M T P) (h146 : Item146 A (lB A)) (hRP : CFSG.Open.pCoreOf 2 Y ≤ P)
    {Yc : Subgroup (Res1Q A L)} (hY : Res1AtOf A c L M Yc) (hsimple : IsSimpleGroup ↥Yc)
    (hfix : Res1AutFix ↥Yc) :
    ∀ x : ↥(Res1C A L), (x : G) ∈ CFSG.Open.pCoreOf 2 Y ⊓ Subgroup.centralizer (A : Set G) →
      ∀ y ∈ Yc, QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(Res1C A L)) x * y =
        y * QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(Res1C A L)) x := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hAM : A ≤ M := fun a ha => hC.mem_m.2 (Subgroup.mem_sup_left ha)
  set R := CFSG.Open.pCoreOf 2 Y with hRdef
  obtain ⟨-, hRH, -, -⟩ := Sylow155B1.delta_host_facts hS h146 hC hE hRP
    (Sylow155S.sup_mem_invariant hC hE hRP) (Sylow155S.sup_le_u155 hE hRP)
    (Sylow155S.p_le_normalizer_sup hE) le_sup_left
  have hRM : R ≤ M := hRH.trans
    (((delta_le _).trans ((Sylow155S.sup_le_u155 hE hRP).trans inf_le_left)).trans (delta_le M))
  have hY' := hY
  obtain ⟨hhyp, -, -, ⟨hYcomp, hcY, -⟩, -⟩ := hY'
  haveI hYn : Yc.Normal := res1_isComponent_normal hS hhyp hYcomp
  set C := Res1C A L with hCdef
  set π := QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥C) with hπdef
  let ρ : Res1Q A L →* MulAut ↥Yc := MulAut.conjNormal
  have hcA : c ∈ A := (zpowers_mem_omegaA_iff.mp hS.zpowers_mem_omegaA).1
  obtain ⟨c', hc'Y, hc'⟩ := hcY
  have hc'val : (c' : G) = c := hc'
  set y : ↥Yc := ⟨π c', hc'Y⟩ with hydef
  have hy : orderOf y = 3 := orderOf_res1_point hS hc'Y hc'val
  have hfixy : ∀ x : ↥C, (x : G) ∈ Subgroup.centralizer (A : Set G) → ρ (π x) y = y := by
    intro x hx
    apply Subtype.ext
    show π x * π c' * (π x)⁻¹ = π c'
    rw [mul_inv_eq_iff_eq_mul]
    exact res1_comm_point hcA hc'val hx
  set W : Subgroup ↥C := (CFSG.Open.pCoreOf 2 M ⊓ C).subgroupOf C with hWdef
  have hWconj : ∀ m : ↥C, (m : G) ∈ M → ∀ q ∈ W, m * q * m⁻¹ ∈ W := by
    intro m hm q hq
    rw [hWdef, Subgroup.mem_subgroupOf, Subgroup.mem_inf] at hq ⊢
    exact ⟨by simpa using conj_mem_pCoreOf hm hq.1, (m * q * m⁻¹).2⟩
  set Vh : Subgroup (MulAut ↥Yc) := (W.map π).map ρ with hVhdef
  set R₀ : Subgroup ↥Yc := Vh.comap MulAut.conj with hR₀def
  have hcy : MulAut.conj y = ρ (π c') := (MulAut.conjNormal_val (H := Yc) (h := y)).symm
  have hρconj : ∀ m : ↥C, (m : G) ∈ M → ∀ r ∈ R₀, ρ (π m) r ∈ R₀ := by
    intro m hm r hr
    obtain ⟨_, ⟨w, hw, rfl⟩, hwr⟩ := hr
    refine ⟨π (m * w * m⁻¹), ⟨m * w * m⁻¹, hWconj m hm w hw, rfl⟩, ?_⟩
    have e1 : MulAut.conj (ρ (π m) r) = ρ (π m) * MulAut.conj r * (ρ (π m))⁻¹ := by
      ext z
      simp
    rw [e1, ← hwr]
    simp
  have hR₀ne : R₀ ≠ ⊥ := by
    obtain ⟨w, hwM, y₀, hy₀Y, hy₀1, hy₀w⟩ := res1_exists_inner hS hAM h142 hY
    intro hbot
    have hmem : (⟨y₀, hy₀Y⟩ : ↥Yc) ∈ R₀ := by
      refine ⟨π w, ⟨w, Subgroup.mem_subgroupOf.mpr ⟨hwM, w.2⟩, rfl⟩, ?_⟩
      refine MulEquiv.ext fun z => Subtype.ext ?_
      simp only [ρ, MulAut.conjNormal_apply, MulAut.conj_apply, Subgroup.coe_mul,
        Subgroup.coe_inv]
      exact hy₀w z z.2
    rw [hbot, Subgroup.mem_bot] at hmem
    exact hy₀1 (congrArg Subtype.val hmem)
  have hcenter : Subgroup.center ↥Yc = ⊥ := center_eq_bot_of_isComponent hYcomp hsimple
  have hW2 : IsPGroup 2 W :=
    ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M).to_le inf_le_left).comap_subtype
  have hR₀2 : IsPGroup 2 R₀ := by
    refine IsPGroup.comap_of_ker_isPGroup ((hW2.map π).map ρ) MulAut.conj ?_
    have hker : (MulAut.conj : ↥Yc →* MulAut ↥Yc).ker = ⊥ := by
      rw [eq_bot_iff]
      intro z hz
      rw [← hcenter]
      rw [Subgroup.mem_center_iff]
      intro w
      have h := congrArg (fun α : MulAut ↥Yc => α w) (MonoidHom.mem_ker.mp hz)
      simp only [MulAut.conj_apply, MulAut.one_apply] at h
      exact (mul_inv_eq_iff_eq_mul.mp h).symm
    rw [hker]
    exact IsPGroup.of_bot
  have hyR₀ : ∀ r ∈ R₀, y * r * y⁻¹ ∈ R₀ := by
    intro r hr
    have hcM : (c' : G) ∈ M := by rw [hc'val]; exact hAM hcA
    have h := hρconj c' hcM r hr
    have e1 : ρ (π c') r = y * r * y⁻¹ := by rw [← hcy]; rfl
    rwa [e1] at h
  set CR : Subgroup ↥C := (R ⊓ Subgroup.centralizer (A : Set G)).subgroupOf C with hCRdef
  set Xh : Subgroup (MulAut ↥Yc) := (CR.map π).map ρ with hXhdef
  have hR2 : IsPGroup 2 R := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Y
  have hX2 : IsPGroup 2 Xh := ((hR2.to_le inf_le_left).comap_subtype.map π).map ρ
  have hXy : ∀ α ∈ Xh, α y = y := by
    rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact hfixy x (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hx)).2
  have hXR : ∀ α ∈ Xh, ∀ r ∈ R₀, α r ∈ R₀ := by
    rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩ r hr
    exact hρconj x (hRM (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hx)).1) r hr
  have hXbot : Xh = ⊥ := hfix y hy R₀ hR₀ne hR₀2 hyR₀ Xh hX2 hXy hXR
  intro x hx
  have hmem : ρ (π x) ∈ Xh := ⟨π x, ⟨x, Subgroup.mem_subgroupOf.mpr hx, rfl⟩, rfl⟩
  rw [hXbot, Subgroup.mem_bot] at hmem
  exact (conjNormal_eq_one_iff (π x)).mp hmem

theorem res1_pPrimeCoreOf_le_of_comm (h1 : Sec4.Item4_1LargePrime)
    (h2 : Sec4.Item4_1ThreeCover) (h43 : Sec4.Item4_3) (hin : Sec4.Census.CoverInputs46)
    (h143 : Y1SecondFormExcl) {A L : Subgroup G} {c : G} (hR : Sec15R G A c L)
    (hW : Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G))
    (h142 : Concl142 A (lB A)) {X K Y M T P : Subgroup G} (hC : Ctx155 A X K Y M T)
    (hE : End155N A X K Y M T P) (h146 : Item146 A (lB A)) (hRP : CFSG.Open.pCoreOf 2 Y ≤ P)
    (hIX : delta A (lB A) M ≤ Subgroup.normalizer (X : Set G)) {Yc : Subgroup (Res1Q A L)}
    (hY : Res1AtOf A c L M Yc) (hsimple : IsSimpleGroup ↥Yc)
    (hEA : layerOddPreimage
        (delta A (lB A) (CFSG.Open.pCoreOf 2 Y ⊔ pPrimeCoreOf 3 (u155 A M X))) ≤
      Subgroup.centralizer (A : Set G))
    (hcomm : ∀ x : ↥(Res1C A L),
      (x : G) ∈ CFSG.Open.pCoreOf 2 Y ⊓ Subgroup.centralizer (A : Set G) →
        ∀ y ∈ Yc, QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(Res1C A L)) x * y =
          y * QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(Res1C A L)) x) :
    pPrimeCoreOf 2 (delta A (lB A) (CFSG.Open.pCoreOf 2 Y ⊔ pPrimeCoreOf 3 (u155 A M X))) ≤
      n155 A K := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hS := hR.toSec14Std
  set R := CFSG.Open.pCoreOf 2 Y with hRdef
  set H := delta A (lB A) (R ⊔ pPrimeCoreOf 3 (u155 A M X)) with hHdef
  set O := pPrimeCoreOf 2 H with hOdef
  obtain ⟨hHQ, hRH, -, -⟩ := Sylow155B1.delta_host_facts hS h146 hC hE hRP
    (Sylow155S.sup_mem_invariant hC hE hRP) (Sylow155S.sup_le_u155 hE hRP)
    (Sylow155S.p_le_normalizer_sup hE) le_sup_left
  have hAH : A ≤ Subgroup.normalizer (H : Set G) := hHQ.1.2.2
  have hAO : A ≤ Subgroup.normalizer (O : Set G) :=
    hAH.trans (normalizer_le_normalizer_pPrimeCoreOf_two H)
  have hOE : O ≤ layerOddPreimage H := pPrimeCoreOf_two_le_layerOddPreimage H
  have hOA : O ≤ Subgroup.centralizer (A : Set G) := hOE.trans hEA
  have hCA : Subgroup.centralizer (A : Set G) ≤ Res1C A L := centralizer_le_res1C A L
  have hHO : H ≤ Subgroup.normalizer (O : Set G) := le_normalizer_pPrimeCoreOf 2 H
  have hY' := hY
  obtain ⟨hhyp, -, -, ⟨hYcomp, -, -⟩, -⟩ := hY'
  haveI hYn : Yc.Normal := res1_isComponent_normal hS hhyp hYcomp
  set π := QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(Res1C A L)) with hπdef
  let ρ : Res1Q A L →* MulAut ↥Yc := MulAut.conjNormal
  have hCRO : R ⊓ Subgroup.centralizer (A : Set G) ≤ Subgroup.centralizer (O : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro o ho
    have hxH : x ∈ H := hRH (Subgroup.mem_inf.mp hx).1
    set x' : ↥(Res1C A L) := ⟨x, hCA (Subgroup.mem_inf.mp hx).2⟩
    set o' : ↥(Res1C A L) := ⟨o, hCA (hOA ho)⟩
    have hk : ((o' * x' * o'⁻¹ * x'⁻¹ : ↥(Res1C A L)) : G) ∈ O := by
      show o * x * o⁻¹ * x⁻¹ ∈ O
      have h1 : x * o⁻¹ * x⁻¹ ∈ O :=
        (Subgroup.mem_normalizer_iff.mp (hHO hxH) o⁻¹).mp (O.inv_mem ho)
      have e : o * x * o⁻¹ * x⁻¹ = o * (x * o⁻¹ * x⁻¹) := by group
      rw [e]
      exact O.mul_mem ho h1
    have hρx : ρ (π x') = 1 := (conjNormal_eq_one_iff (π x')).mpr (hcomm x' hx)
    have hρk : ρ (π (o' * x' * o'⁻¹ * x'⁻¹)) = 1 := by
      simp only [map_mul, map_inv, hρx, mul_one, inv_one, mul_inv_cancel]
    have hk1 := res1_eq_one_of_mem_pPrimeCoreOf_two h1 h2 h43 hin h143 hR hW h142 hC hE h146 hRP
      hIX hY hsimple hEA hk ((conjNormal_eq_one_iff (π (o' * x' * o'⁻¹ * x'⁻¹))).mp hρk)
    have hk1' : o * x * o⁻¹ * x⁻¹ = 1 := congrArg Subtype.val hk1
    calc o * x = o * x * o⁻¹ * x⁻¹ * (x * o) := by group
      _ = x * o := by rw [hk1', one_mul]
  have hA27 : Nat.card A = 27 := hS.toSec13Data.mem_partTwoE.2.1
  have hA3 : IsPGroup 3 A := IsPGroup.of_card (n := 3) (by rw [hA27]; norm_num)
  have hR2 : IsPGroup 2 R := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Y
  have hRO : R ≤ Subgroup.centralizer (O : Set G) :=
    le_centralizer_of_cent_inf_le hR2 hA3 (Sylow155B1.le_normalizer_r hC)
      (hRH.trans hHO) hOA hCRO
  have hON : O ≤ Subgroup.normalizer (R : Set G) :=
    (Subgroup.le_centralizer_iff.mp hRO).trans (Subgroup.centralizer_le_normalizer _)
  have hOQ : O ∈ scriptQ A (lB A) := mem_scriptQ_of_le hHQ (pPrimeCoreOf_le 2 H) hAO
  have hRne : R ≠ ⊥ := hC.isY.1.1.2
  have hchar : (R.subgroupOf R).Characteristic := by
    rw [Subgroup.subgroupOf_self]
    infer_instance
  exact (le_delta hOQ hON).trans (hE.claim R hRne le_rfl hchar)

theorem res1_layerOddPreimage_le_of_le_centralizer (h1 : Sec4.Item4_1LargePrime)
    (h2 : Sec4.Item4_1ThreeCover) (h43 : Sec4.Item4_3) (hin : Sec4.Census.CoverInputs46)
    (h143 : Y1SecondFormExcl) {A L : Subgroup G} {c : G} (hR : Sec15R G A c L)
    (hW : Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G))
    (h142 : Concl142 A (lB A)) {X K Y M T P : Subgroup G} (hC : Ctx155 A X K Y M T)
    (hE : End155N A X K Y M T P) (h146 : Item146 A (lB A)) (hRP : CFSG.Open.pCoreOf 2 Y ≤ P)
    (hIX : delta A (lB A) M ≤ Subgroup.normalizer (X : Set G)) {Yc : Subgroup (Res1Q A L)}
    (hY : Res1AtOf A c L M Yc) (hsimple : IsSimpleGroup ↥Yc) (hsolv : Res1AutSolv ↥Yc)
    (hfix : Res1AutFix ↥Yc)
    (hEA : layerOddPreimage
        (delta A (lB A) (CFSG.Open.pCoreOf 2 Y ⊔ pPrimeCoreOf 3 (u155 A M X))) ≤
      Subgroup.centralizer (A : Set G)) :
    layerOddPreimage (delta A (lB A) (CFSG.Open.pCoreOf 2 Y ⊔ pPrimeCoreOf 3 (u155 A M X))) ≤
      n155 A K :=
  (res1_layerOddPreimage_eq_of_autSolv h1 h2 h43 hin h143 hR hW h142 hC hE h146 hRP hIX hY
    hsimple hsolv hEA).le.trans
    (res1_pPrimeCoreOf_le_of_comm h1 h2 h43 hin h143 hR hW h142 hC hE h146 hRP hIX hY hsimple hEA
      (res1_comm_of_autFix hR.toSec14Std h142 hC hE h146 hRP hY hsimple hfix))

end CFSG.RankThree.PartTwo.Sec15.Sylow155R1
