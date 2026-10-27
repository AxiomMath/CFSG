module

public import CFSG.RankThree.PartTwo.Sec15.Sylow155R1Cent361
public import CFSG.RankThree.PartTwo.Sec15.Liebeck155R1T150Pump
import CFSG.RankThree.PartTwo.Sec15.Sylow155R1Cent162
public import CFSG.RankThree.PartTwo.Sec15.Sylow155R1T203

public section

namespace CFSG.RankThree.PartTwo.Sec15.Liebeck155R1T150

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS
open CFSG.RankThree.PartTwo.Sec15.Sylow155R3.Thm90
open CFSG.RankThree.PartTwo.Sec15.Sylow155R1
open scoped commutatorElement

namespace Pump

section Restrict

variable {G : Type} [Group G]

theorem isElemAbelian_subgroupOf {p : ℕ} {A Y : Subgroup G}
    (hA : CFSG.Assembly.IsElemAbelian p A) : CFSG.Assembly.IsElemAbelian p (A.subgroupOf Y) := by
  have hcomm : IsMulCommutative (A.subgroupOf Y) := by
    refine ⟨⟨fun a b => ?_⟩⟩
    have h' := hA.1.is_comm.comm (⟨(a.1 : G), a.2⟩ : ↥A) ⟨(b.1 : G), b.2⟩
    have h'' : (a.1 : G) * (b.1 : G) = (b.1 : G) * (a.1 : G) := congrArg Subtype.val h'
    exact Subtype.ext (Subtype.ext h'')
  refine ⟨hcomm, fun g hg => ?_⟩
  exact Subtype.ext (by simpa using hA.2 (g : G) (Subgroup.mem_subgroupOf.mp hg))

variable [Finite G] in
noncomputable def thetaQuotEquivSubgroupOf {L Y : Subgroup G} (hLY : L ≤ Y) :
    ↥(L.subgroupOf Y) ⧸ aschbacherSolvableCore 3 ↥(L.subgroupOf Y) ≃*
      ↥L ⧸ aschbacherSolvableCore 3 ↥L :=
  QuotientGroup.congr _ _ (Subgroup.subgroupOfEquivOfLe hLY)
    (aschbacherSolvableCore_map_mulEquiv Nat.prime_three _)

variable [Finite G] in
theorem subgroupOf_mem_thetaComponentsAt {c : G} {L : Subgroup G}
    (hL : L ∈ thetaComponentsAt 3 c) {Y : Subgroup G} (hLY : L ≤ Y) (hcY : c ∈ Y) :
    L.subgroupOf Y ∈ thetaComponentsAt 3 (⟨c, hcY⟩ : ↥Y) := by
  obtain ⟨hLc, hLsub, hLperf⟩ := thetaComponentsAt_facts hL
  have hLq := Sec6.isQuasisimple_of_mem_thetaComponentsAt hL
  set D := Subgroup.centralizer ({(⟨c, hcY⟩ : ↥Y)} : Set ↥Y) with hDdef
  have hMYD : L.subgroupOf Y ≤ D := fun y hy => by
    have hyL : (y : G) ∈ L := hy
    have h1 := Subgroup.mem_centralizer_singleton_iff.mp (hLc hyL)
    exact Subgroup.mem_centralizer_singleton_iff.mpr (Subtype.ext h1)
  have hsubLC : SubnormalIn L (Subgroup.centralizer ({c} : Set G) ⊓ Y) := by
    have h := SubnormalIn.inf Y (hLsub : SubnormalIn L (Subgroup.centralizer ({c} : Set G)))
    rwa [inf_eq_left.mpr hLY] at h
  have hsubMY : SubnormalIn (L.subgroupOf Y) D := by
    have h := SubnormalIn.subgroupOf Y
      (inf_le_right : Subgroup.centralizer ({c} : Set G) ⊓ Y ≤ Y) hsubLC
    have hD : (Subgroup.centralizer ({c} : Set G) ⊓ Y).subgroupOf Y = D := by
      ext y
      constructor
      · intro hy
        have h1 := Subgroup.mem_centralizer_singleton_iff.mp
          (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hy)).1
        exact Subgroup.mem_centralizer_singleton_iff.mpr (Subtype.ext h1)
      · intro hy
        have h1 := congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp hy)
        exact Subgroup.mem_subgroupOf.mpr
          (Subgroup.mem_inf.mpr ⟨Subgroup.mem_centralizer_singleton_iff.mpr h1, y.2⟩)
    rw [hD] at h
    exact h
  let eR : ↥L ≃* ↥((L.subgroupOf Y).subgroupOf D) :=
    (Subgroup.subgroupOfEquivOfLe hLY).symm.trans (Subgroup.subgroupOfEquivOfLe hMYD).symm
  have hN : (L.subgroupOf Y).subgroupOf D ∈ thetaComponents 3 ↥D := by
    refine ⟨?_, hsubMY, ?_⟩
    · have := hLperf
      exact Group.IsPerfect.ofSurjective (f := eR.toMonoidHom) eR.surjective
    · exact CFSG.LocalCores.isQuasisimple_of_mulEquiv
        (QuotientGroup.congr _ _ eR (aschbacherSolvableCore_map_mulEquiv Nat.prime_three eR)) hLq
  exact mem_thetaComponentsIn_iff.mpr ⟨hMYD, hN⟩

end Restrict

end Pump

@[expose] def Res1T150A10 (Q : ∀ (X : Type) [Group X], Prop)
    (P : ∀ (Y : Type) [Group Y], Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L X K Y M T P' : Subgroup G)
    (Yc : Subgroup (Res1Q A L)) (z : G), Res1Tau Q P A c L X K Y M T P' Yc z →
    ∀ j ∈ res1J A X Y M z, j ≠ 1 →
    ∀ Λ : Subgroup ↥(Subgroup.centralizer ({j} : Set G)),
      Λ ∈ thetaComponents 3 ↥(Subgroup.centralizer ({j} : Set G)) →
      A.subgroupOf (Subgroup.centralizer ({j} : Set G)) ≤ Subgroup.normalizer (Λ : Set _) →
      ∀ c' : ↥(Subgroup.centralizer ({j} : Set G)), (c' : G) = c →
      L.subgroupOf (Subgroup.centralizer ({j} : Set G)) ≤
        Λ ⊓ Subgroup.centralizer ({c'} : Set ↥(Subgroup.centralizer ({j} : Set G))) →
      c' ∉ Sec4.thetaQuotCentralizer Λ →
      Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* alternatingGroup (Fin 7)) →
      Nonempty (Pump.ThetaCenterQuot Λ ≃* alternatingGroup (Fin 10)) → False

@[expose] def Res1T150Acts (Q : ∀ (X : Type) [Group X], Prop)
    (P : ∀ (Y : Type) [Group Y], Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L X K Y M T P' : Subgroup G)
    (Yc : Subgroup (Res1Q A L)) (z : G), Res1Tau Q P A c L X K Y M T P' Yc z →
    ∀ j ∈ res1J A X Y M z, j ≠ 1 →
    ∀ Λ : Subgroup ↥(Subgroup.centralizer ({j} : Set G)),
      Λ ∈ thetaComponents 3 ↥(Subgroup.centralizer ({j} : Set G)) →
      A.subgroupOf (Subgroup.centralizer ({j} : Set G)) ≤ Subgroup.normalizer (Λ : Set _) →
      ∀ c' : ↥(Subgroup.centralizer ({j} : Set G)), (c' : G) = c →
      L.subgroupOf (Subgroup.centralizer ({j} : Set G)) ≤
        Λ ⊓ Subgroup.centralizer ({c'} : Set ↥(Subgroup.centralizer ({j} : Set G))) →
      c' ∉ Sec4.thetaQuotCentralizer Λ →
      ⁅L, CFSG.Open.pCoreOf 2 X⁆ ≤ (aschbacherSolvableCore 3
        ↥(Subgroup.centralizer ({j} : Set G))).map (Subgroup.centralizer ({j} : Set G)).subtype

namespace Pump

section Tau

variable {G : Type} [Group G] [Finite G] {Q : ∀ (X : Type) [Group X], Prop}
  {P : ∀ (Y : Type) [Group Y], Prop} {A : Subgroup G} {c : G} {L X K Y M T P' : Subgroup G}
  {Yc : Subgroup (Res1Q A L)} {z : G}

theorem sectionFourHyp_centralizer (τ : Res1Tau Q P A c L X K Y M T P' Yc z) {j : G}
    (hj1 : j ≠ 1) : SectionFourHyp ↥(Subgroup.centralizer ({j} : Set G)) := by
  have hT4 : TheoremFourHyp G := τ.std.toTheoremFourHyp
  refine hT4.sectionFourHyp fun htop => ?_
  have hjz : j ∈ Subgroup.center G := by
    rw [Subgroup.mem_center_iff]
    intro g
    have hg : g ∈ Subgroup.centralizer ({j} : Set G) := htop ▸ Subgroup.mem_top g
    exact Subgroup.mem_centralizer_singleton_iff.mp hg
  have := hT4.isSimpleGroup
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center G) with hb | ht
  · rw [hb, Subgroup.mem_bot] at hjz
    exact hj1 hjz
  · obtain ⟨a, b, hab⟩ := hT4.nonabelian
    apply hab
    have ha : a ∈ Subgroup.center G := ht ▸ Subgroup.mem_top a
    exact (Subgroup.mem_center_iff.mp ha b).symm

theorem a_le_centralizer_of_mem_j (τ : Res1Tau Q P A c L X K Y M T P' Yc z) {j : G}
    (hj : j ∈ res1J A X Y M z) : A ≤ Subgroup.centralizer ({j} : Set G) :=
  fun a ha => Subgroup.mem_centralizer_iff.mpr fun h hh => by
    rw [Set.mem_singleton_iff.mp hh]
    exact (Subgroup.mem_centralizer_iff.mp (τ.j_le_centralizer hj) a ha).symm

theorem acts_of_k150 (h1 : Sec4.Item4_1LargePrime) (h2 : Sec4.Item4_1ThreeCover)
    (h149 : Item149 A (lB A)) (τ : Res1Tau Q P A c L X K Y M T P' Yc z)
    (hJs : IsSimpleGroup (↥L ⧸ aschbacherSolvableCore 3 ↥L))
    (hK : K150For (↥L ⧸ aschbacherSolvableCore 3 ↥L)) {j : G} (hj : j ∈ res1J A X Y M z)
    (hj1 : j ≠ 1)
    (hA10 : ∀ Λ : Subgroup ↥(Subgroup.centralizer ({j} : Set G)),
      Λ ∈ thetaComponents 3 ↥(Subgroup.centralizer ({j} : Set G)) →
      A.subgroupOf (Subgroup.centralizer ({j} : Set G)) ≤ Subgroup.normalizer (Λ : Set _) →
      ∀ c' : ↥(Subgroup.centralizer ({j} : Set G)), (c' : G) = c →
      L.subgroupOf (Subgroup.centralizer ({j} : Set G)) ≤
        Λ ⊓ Subgroup.centralizer ({c'} : Set ↥(Subgroup.centralizer ({j} : Set G))) →
      c' ∉ Sec4.thetaQuotCentralizer Λ →
      Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* alternatingGroup (Fin 7)) →
      Nonempty (Pump.ThetaCenterQuot Λ ≃* alternatingGroup (Fin 10)) → False) :
    ∀ Λ : Subgroup ↥(Subgroup.centralizer ({j} : Set G)),
      Λ ∈ thetaComponents 3 ↥(Subgroup.centralizer ({j} : Set G)) →
      A.subgroupOf (Subgroup.centralizer ({j} : Set G)) ≤ Subgroup.normalizer (Λ : Set _) →
      ∀ c' : ↥(Subgroup.centralizer ({j} : Set G)), (c' : G) = c →
      L.subgroupOf (Subgroup.centralizer ({j} : Set G)) ≤
        Λ ⊓ Subgroup.centralizer ({c'} : Set ↥(Subgroup.centralizer ({j} : Set G))) →
      c' ∉ Sec4.thetaQuotCentralizer Λ →
      ⁅L, CFSG.Open.pCoreOf 2 X⁆ ≤ (aschbacherSolvableCore 3
        ↥(Subgroup.centralizer ({j} : Set G))).map
          (Subgroup.centralizer ({j} : Set G)).subtype := by
  intro Λ hΛ hAΛ c' hc' hLΛ hcc
  exfalso
  obtain rfl : c' = ⟨c, a_le_centralizer_of_mem_j τ hj τ.std.mem_A⟩ := Subtype.ext hc'
  have hLY : L ≤ Subgroup.centralizer ({j} : Set G) :=
    τ.l_le.trans (τ.x_le_centralizer_of_mem_j h149 hj)
  exact hcc (mem_thetaQuotCentralizer_of_k150 (sectionFourHyp_centralizer τ hj1) h1 h2
    (isElemAbelian_subgroupOf τ.std.isElemAbelian) (Subgroup.mem_subgroupOf.mpr τ.std.mem_A)
    (subgroupOf_mem_thetaComponentsAt τ.std.mem_thetaComponentsAt hLY _)
    (thetaQuotEquivSubgroupOf hLY) hJs hK
    (fun Λ' hΛ' hAΛ' hLΛ' hcΛ' h7 h10 => hA10 Λ' hΛ' hAΛ' _ rfl hLΛ' hcΛ' h7 h10) hΛ hAΛ hLΛ)

theorem commutator_le_theta_of_tau_of_acts (h45 : Sec4.Item4_5) (h48 : Sec4.Item4_8)
    (h149 : Item149 A (lB A)) (τ : Res1Tau Q P A c L X K Y M T P' Yc z) {j : G}
    (hj : j ∈ res1J A X Y M z) (hj1 : j ≠ 1)
    (hacts : ∀ Λ : Subgroup ↥(Subgroup.centralizer ({j} : Set G)),
      Λ ∈ thetaComponents 3 ↥(Subgroup.centralizer ({j} : Set G)) →
      A.subgroupOf (Subgroup.centralizer ({j} : Set G)) ≤ Subgroup.normalizer (Λ : Set _) →
      ∀ c' : ↥(Subgroup.centralizer ({j} : Set G)), (c' : G) = c →
      L.subgroupOf (Subgroup.centralizer ({j} : Set G)) ≤
        Λ ⊓ Subgroup.centralizer ({c'} : Set ↥(Subgroup.centralizer ({j} : Set G))) →
      c' ∉ Sec4.thetaQuotCentralizer Λ →
      ⁅L, CFSG.Open.pCoreOf 2 X⁆ ≤ (aschbacherSolvableCore 3
        ↥(Subgroup.centralizer ({j} : Set G))).map (Subgroup.centralizer ({j} : Set G)).subtype) :
    ⁅L, CFSG.Open.pCoreOf 2 X⁆ ≤ (aschbacherSolvableCore 3
      ↥(Subgroup.centralizer ({j} : Set G))).map (Subgroup.centralizer ({j} : Set G)).subtype := by
  set Yj := Subgroup.centralizer ({j} : Set G) with hYj
  have hYjS : SectionFourHyp ↥Yj := sectionFourHyp_centralizer τ hj1
  have hAY : A ≤ Yj := a_le_centralizer_of_mem_j τ hj
  have hXY : X ≤ Yj := τ.x_le_centralizer_of_mem_j h149 hj
  have hLX : L ≤ X := τ.l_le
  have hLY : L ≤ Yj := hLX.trans hXY
  have hcA : c ∈ A := τ.std.mem_A
  have hcY : c ∈ Yj := hAY hcA
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set U := CFSG.Open.pCoreOf 2 X with hU
  have hUp : IsPGroup 2 U := (CFSG.pCore_isPGroup (p := 2) (G := ↥X)).map X.subtype
  have hUX : U ≤ X := Subgroup.map_subtype_le _
  have hUY : U ≤ Yj := hUX.trans hXY
  have hXU : X ≤ Subgroup.normalizer (U : Set G) :=
    Subgroup.le_normalizer.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 X)
  have := hUp.isNilpotent
  have hUsol : Group.IsSolvable ↥(U.subgroupOf Yj) :=
    Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.subgroupOfEquivOfLe hUY).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hUY).injective
  have hL' : L.subgroupOf Yj ∈ thetaComponentsAt 3 (⟨c, hcY⟩ : ↥Yj) :=
    subgroupOf_mem_thetaComponentsAt τ.std.mem_thetaComponentsAt hLY hcY
  have hAe : CFSG.Assembly.IsElemAbelian 3 (A.subgroupOf Yj) :=
    isElemAbelian_subgroupOf τ.std.isElemAbelian
  have hA27 : Nat.card (A.subgroupOf Yj) = 27 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAY).toEquiv).trans τ.std.card_eq
  have hc'A : (⟨c, hcY⟩ : ↥Yj) ∈ A.subgroupOf Yj := Subgroup.mem_subgroupOf.mpr hcA
  have hc'1 : (⟨c, hcY⟩ : ↥Yj) ≠ 1 := fun h => τ.std.ne_one (congrArg Subtype.val h)
  have hLX' : L.subgroupOf Yj ≤ X.subgroupOf Yj := fun x hx => hLX hx
  have hUX' : U.subgroupOf Yj ≤ X.subgroupOf Yj := fun x hx => hUX hx
  have hXU' : X.subgroupOf Yj ≤ Subgroup.normalizer ((U.subgroupOf Yj : Subgroup ↥Yj) : Set ↥Yj) :=
    fun x hx => Subgroup.mem_normalizer_iff.mpr fun y =>
      Subgroup.mem_normalizer_iff.mp (hXU hx) (y : G)
  have hL1 : L.subgroupOf Yj ≠ ⊥ := by
    rw [← Subgroup.nontrivial_iff_ne_bot]
    have hq := Sec6.isQuasisimple_of_mem_thetaComponentsAt τ.std.mem_thetaComponentsAt
    have := CFSG.LocalCores.isQuasisimple_nontrivial hq
    have : Nontrivial ↥L := (QuotientGroup.mk'_surjective (aschbacherSolvableCore 3 ↥L)).nontrivial
    exact (Subgroup.subgroupOfEquivOfLe hLY).symm.injective.nontrivial
  have hread : ⁅L, U⁆ ≤ (aschbacherSolvableCore 3 ↥Yj).map Yj.subtype →
      ∀ u ∈ U.subgroupOf Yj, ∀ l ∈ L.subgroupOf Yj,
        u * l * u⁻¹ * l⁻¹ ∈ aschbacherSolvableCore 3 ↥Yj := by
    intro H u hu l hl
    obtain ⟨w, hw, hwe⟩ := H (Subgroup.commutator_mem_commutator (Subgroup.mem_subgroupOf.mp hl)
      (Subgroup.mem_subgroupOf.mp hu))
    have hlu : l * u * l⁻¹ * u⁻¹ = w :=
      Subtype.ext (by change _ = Yj.subtype w; rw [hwe, commutatorElement_def]; rfl)
    have h2 : u * l * u⁻¹ * l⁻¹ = (l * u * l⁻¹ * u⁻¹)⁻¹ := by group
    rw [h2, hlu]
    exact (aschbacherSolvableCore 3 ↥Yj).inv_mem hw
  have hP := Pump.pump150_of_acts hYjS h45 h48 hAe hA27 hc'A hc'1 hL' hL1 hLX' hUX' hXU' hUsol
    fun Λ hΛ hAΛ hLΛ hcc => hread (hacts Λ hΛ hAΛ ⟨c, hcY⟩ rfl hLΛ hcc)
  rw [Subgroup.commutator_le]
  intro l hl u hu
  have hlY : l ∈ Yj := hLY hl
  have huY : u ∈ Yj := hUY hu
  have h := hP ⟨u, huY⟩ hu ⟨l, hlY⟩ hl
  refine ⟨(⟨u, huY⟩ * ⟨l, hlY⟩ * ⟨u, huY⟩⁻¹ * ⟨l, hlY⟩⁻¹ : ↥Yj)⁻¹,
    (aschbacherSolvableCore 3 ↥Yj).inv_mem h, ?_⟩
  change (u * l * u⁻¹ * l⁻¹)⁻¹ = ⁅l, u⁆
  rw [commutatorElement_def]
  group

theorem commutator_le_theta_of_tau (h1 : Sec4.Item4_1LargePrime) (h2 : Sec4.Item4_1ThreeCover)
    (h45 : Sec4.Item4_5) (h48 : Sec4.Item4_8) (h149 : Item149 A (lB A))
    (τ : Res1Tau Q P A c L X K Y M T P' Yc z)
    (hJs : IsSimpleGroup (↥L ⧸ aschbacherSolvableCore 3 ↥L))
    (hK : K150For (↥L ⧸ aschbacherSolvableCore 3 ↥L)) {j : G} (hj : j ∈ res1J A X Y M z)
    (hj1 : j ≠ 1)
    (hA10 : ∀ Λ : Subgroup ↥(Subgroup.centralizer ({j} : Set G)),
      Λ ∈ thetaComponents 3 ↥(Subgroup.centralizer ({j} : Set G)) →
      A.subgroupOf (Subgroup.centralizer ({j} : Set G)) ≤ Subgroup.normalizer (Λ : Set _) →
      ∀ c' : ↥(Subgroup.centralizer ({j} : Set G)), (c' : G) = c →
      L.subgroupOf (Subgroup.centralizer ({j} : Set G)) ≤
        Λ ⊓ Subgroup.centralizer ({c'} : Set ↥(Subgroup.centralizer ({j} : Set G))) →
      c' ∉ Sec4.thetaQuotCentralizer Λ →
      Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* alternatingGroup (Fin 7)) →
      Nonempty (Pump.ThetaCenterQuot Λ ≃* alternatingGroup (Fin 10)) → False) :
    ⁅L, CFSG.Open.pCoreOf 2 X⁆ ≤ (aschbacherSolvableCore 3
      ↥(Subgroup.centralizer ({j} : Set G))).map (Subgroup.centralizer ({j} : Set G)).subtype :=
  commutator_le_theta_of_tau_of_acts h45 h48 h149 τ hj hj1
    (acts_of_k150 h1 h2 h149 τ hJs hK hj hj1 hA10)

end Tau

end Pump

theorem res1Thm150b_of_acts (h45 : Sec4.Item4_5) (h48 : Sec4.Item4_8)
    (h149 : Sec16.Item149S14) {Q : ∀ (X : Type) [Group X], Prop}
    {P : ∀ (Y : Type) [Group Y], Prop} (hacts : Res1T150Acts Q P) :
    Sylow155R1.Res1Thm150b Q P :=
  fun G _ _ A c L X K Y M T P' Yc z τ j hj hj1 =>
    Pump.commutator_le_theta_of_tau_of_acts h45 h48 (h149 G A c L τ.std) τ hj hj1
      (hacts G A c L X K Y M T P' Yc z τ j hj hj1)

theorem res1Thm150b_of (h1 : Sec4.Item4_1LargePrime) (h2 : Sec4.Item4_1ThreeCover)
    (h45 : Sec4.Item4_5) (h48 : Sec4.Item4_8)
    (hK7 : K150For (alternatingGroup (Fin 7))) (hK22 : K150For CFSG.Blueprint.NativeSporadic.M22)
    {Q : ∀ (X : Type) [Group X], Prop} {P : ∀ (Y : Type) [Group Y], Prop}
    (hQ : ∀ (X : Type) [Group X], Q X →
      Nonempty (X ≃* alternatingGroup (Fin 7)) ∨ Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.M22))
    (h149 : Sec16.Item149S14) (hQs : Res1QE9 Q) (hA10 : Res1T150A10 Q P) :
    Sylow155R1.Res1Thm150b Q P := by
  intro G _ _ A c L X K Y M T P' Yc z τ j hj hj1
  have hK : K150For (↥L ⧸ aschbacherSolvableCore 3 ↥L) := by
    rcases hQ _ τ.q with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
    · exact Pump.K150For.congr e.symm hK7
    · exact Pump.K150For.congr e.symm hK22
  exact Pump.commutator_le_theta_of_tau h1 h2 h45 h48 (h149 G A c L τ.std) τ (hQs _ τ.q).1 hK hj
    hj1
    (hA10 G A c L X K Y M T P' Yc z τ j hj hj1)

end CFSG.RankThree.PartTwo.Sec15.Liebeck155R1T150
