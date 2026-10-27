module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312M23Core
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312M23Blk
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312WordsHat
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312WordsIdx
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312WordsDefs
public import CFSG.LocalAnalysis.QuasithinUnique.K1.SporadicBase
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatLat
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312M23Norm
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312M23Shape
public import Certificates.Certificate4170
public import CFSG.CGT.Timmesfeld75.L2Pair
public import CFSG.CGT.Timmesfeld75.ListWCBasic
public import CFSG.Certificates.Kernel.LocalCompTits.Span
public import CFSG.ClassicalGroups
public import CFSG.LocalAnalysis.ComponentInitial.PGroupRankOneClassification
public import CFSG.LocalAnalysis.ComponentInitial.SmallLinearIsomorphisms
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporSimpleTop
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeListed
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.Equivariance
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesBorel
public import CFSG.Quasithin.Background.A3Structure318Red
public import CFSG.Quasithin.Background.A3Structure36A
public import CFSG.Quasithin.Background.A3Structure36BAction
public import CFSG.Quasithin.Background.A3Structure36BBase
public import CFSG.Quasithin.Background.A3Structure36BCase3Base
public import CFSG.Quasithin.Background.A3Structure36BCasesBase
public import CFSG.Quasithin.Background.A3Structure36BCommonBase
public import CFSG.Quasithin.Background.A3Structure36BFrattini
public import CFSG.Quasithin.Background.A3Structure36BHeisBase
public import CFSG.Quasithin.Background.A3Structure36BHomocyclic
public import CFSG.Quasithin.Background.A3Structure36BPrimeDataBase
public import CFSG.Quasithin.Background.A3Structure36BStarBase
public import CFSG.Quasithin.Background.A3Structure36Base
public import CFSG.Quasithin.Background.A3Structure38Part3
public import CFSG.Quasithin.Background.B1MoreElevenE
public import CFSG.Quasithin.Background.B1MoreNineG
public import CFSG.Quasithin.Background.B4ModelsAction
public import CFSG.Quasithin.Background.B4ModelsIso
public import CFSG.Quasithin.Background.C2Basic
public import CFSG.Quasithin.Background.C2Inputs
public import CFSG.Quasithin.Background.E3Cent
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312RuPerf
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtJ4LocCheck
public import Certificates.Data.CFSGNative.MonsterB.Rep4371Model
public import Certificates.Kernel.J4Count.FixCE
public import Certificates.Kernel.J4Count.FixCPairBase1
public import Certificates.Kernel.J4Count.KFactsBase

public section

namespace CFSG.Quasithin.A312M23

open CFSG.QuasithinUnique.K1.SporadicPerm CFSG.QuasithinUnique.Ch1.SporLat
open CFSG.QuasithinUnique.Vol2Native.A312L CFSG.Quasithin
open CFSG.Quasithin.A312Words
open scoped Pointwise

variable {Γ : Type} [Group Γ] [Finite Γ] {n : ℕ} [MulAction Γ (Fin n)]
  {Lab : Type} [DecidableEq Lab] [Hashable Lab] [Inhabited Lab]

variable {G : Type} [Group G] [Finite G] {α : Type} [MulAction G α]

theorem perm_kind {S B Y : Subgroup G} {ol : List G} {t : G} (hS : IsPGroup 2 S)
    (hB : B ∈ lFamily S) (hY : B ⊔ S = Y) (hid : IdxTwoData Y ol t) {m : ℕ} (pt : Fin m → α)
    (hpt : Function.Injective pt) (hYp : ∀ z ∈ Y, ∀ i, ∃ j, z • pt i = pt j) (vl : List G)
    (hvol : ∀ v ∈ vl, v ∈ Subgroup.closure {x | x ∈ ol})
    (hvfix : ∀ a ∈ vl, ∀ i, a • pt i = pt i) {sizeV sizeE sizeY : ℕ}
    (hcard : Nat.card Y = sizeY) (hsz : sizeY = sizeV * sizeE)
    (hV : Nat.card (Subgroup.closure {x | x ∈ vl}) = sizeV)
    (hE : Nat.card (Subgroup.closure {e | e ∈ ol.map (rhoFn Y pt hpt hYp)}) = sizeE) :
    perfectCore Y = Subgroup.closure {x | x ∈ ol} ∧ ⁅Y, Y⁆ ≤ Subgroup.closure {x | x ∈ ol} ∧
      Nat.card (Subgroup.closure {x | x ∈ ol}) =
        Nat.card (Subgroup.closure {x | x ∈ vl}) * sizeE := by
  obtain ⟨hol, hcommY, -⟩ := perfectCore_quotient hS hB hY hid
  have hge := ext_core_ge (fun g hg => hid.mem g hg) pt hpt hYp vl hvol hvfix
  rw [hV, hE] at hge
  have hNY : Subgroup.closure {x | x ∈ ol} ≤ Y :=
    (Subgroup.closure_le Y).mpr fun g hg => hid.mem g hg
  have hNeq : Subgroup.closure {x | x ∈ ol} = Y :=
    Subgroup.eq_of_le_of_card_ge hNY (by rw [hcard, hsz]; exact hge)
  have hAN : perfectCore Y = Subgroup.closure {x | x ∈ ol} :=
    le_antisymm ((perfectCore_le Y).trans hNeq.ge) ((Subgroup.closure_le _).mpr hol)
  exact ⟨hAN, hcommY.trans hAN.le, by rw [hNeq, hcard, hsz, hV]⟩

theorem alt_kind {S B Y : Subgroup G} {ol : List G} {t : G} (hS : IsPGroup 2 S)
    (hB : B ∈ lFamily S) (hY : B ⊔ S = Y) (hid : IdxTwoData Y ol t)
    (hn : ∀ v ∈ Subgroup.closure {x | x ∈ ol}, t⁻¹ * v * t ∈ Subgroup.closure {x | x ∈ ol})
    (hnot : t ∉ Subgroup.closure {x | x ∈ ol}) {vl : List G} {sizeV sizeE sizeY : ℕ}
    (hcard : Nat.card Y = sizeY) (hsz : sizeY = 2 * (sizeV * sizeE))
    (hV : Nat.card (Subgroup.closure {x | x ∈ vl}) = sizeV) :
    perfectCore Y = Subgroup.closure {x | x ∈ ol} ∧ ⁅Y, Y⁆ ≤ Subgroup.closure {x | x ∈ ol} ∧
      Nat.card (Subgroup.closure {x | x ∈ ol}) =
        Nat.card (Subgroup.closure {x | x ∈ vl}) * sizeE := by
  obtain ⟨hA, hcomm, -, -, hY2⟩ := perfectCore_eq_closure hS hB hY hid hn
  have h2 := hY2 hnot
  refine ⟨hA, hcomm, ?_⟩
  rw [hV]
  omega

section Facts

variable {S B' Y : Subgroup G} {k m r : ℕ}

theorem isExt_e2_perm_alt_facts {tr : Bool} (hF : E2Facts α Y k m r false tr)
    (hcard : Nat.card Y = 2 ^ k * r) (hS : IsPGroup 2 S) (hB' : B' ∈ lFamily S)
    (hY : B' ⊔ S = Y) (hm : 5 ≤ m) (hr : r = m.factorial / 2) :
    IsExt ↥B' (fun V _ => IsE2 k V) (fun Y _ => IsAlt m Y) := by
  obtain ⟨ol, t, hdata, -, -, pt, hpt, hYp, vl, hvol, hVnorm, hvc, hvsq, hvfix, hV, hE, -⟩ := hF
  obtain ⟨hA, hcomm, hN⟩ := perm_kind hS hB' hY hdata pt hpt hYp vl hvol hvfix hcard rfl hV hE
  exact e2_alt_of_core hB' hY hdata hA hcomm pt hpt hYp vl hvol hVnorm hvc hvsq hvfix hE hN hV hm
    hr

theorem isExt_e2_alt_alt_facts {tr : Bool} (hF : E2Facts α Y k m r true tr)
    (hcard : Nat.card Y = 2 * (2 ^ k * r)) (hS : IsPGroup 2 S) (hB' : B' ∈ lFamily S)
    (hY : B' ⊔ S = Y) (hm : 5 ≤ m) (hr : r = m.factorial / 2) :
    IsExt ↥B' (fun V _ => IsE2 k V) (fun Y _ => IsAlt m Y) := by
  obtain ⟨ol, t, hdata, halt, -, pt, hpt, hYp, vl, hvol, hVnorm, hvc, hvsq, hvfix, hV, hE, -⟩ :=
    hF
  obtain ⟨hn, hnot⟩ := halt rfl
  obtain ⟨hA, hcomm, hN⟩ := alt_kind (sizeE := r) hS hB' hY hdata hn hnot hcard rfl hV
  exact e2_alt_of_core hB' hY hdata hA hcomm pt hpt hYp vl hvol hVnorm hvc hvsq hvfix hE hN hV hm
    hr

theorem isExt_e2_perm_psl32_facts (hF : E2Facts α Y k 7 168 false true)
    (hcard : Nat.card Y = 2 ^ k * 168) (hS : IsPGroup 2 S) (hB' : B' ∈ lFamily S)
    (hY : B' ⊔ S = Y) : IsExt ↥B' (fun V _ => IsE2 k V) (fun Y _ => IsPSL 3 2 1 Y) := by
  obtain ⟨ol, t, hdata, -, -, pt, hpt, hYp, vl, hvol, hVnorm, hvc, hvsq, hvfix, hV, hE, htr⟩ :=
    hF
  obtain ⟨hA, hcomm, hN⟩ := perm_kind hS hB' hY hdata pt hpt hYp vl hvol hvfix hcard rfl hV hE
  exact e2_psl32_of_core hB' hY hdata hA hcomm rfl pt hpt hYp vl hvol hVnorm hvc hvsq hvfix hE hN
    hV rfl (htr rfl)

theorem isExt_e2_alt_psl32_facts (hF : E2Facts α Y k 7 168 true true)
    (hcard : Nat.card Y = 2 * (2 ^ k * 168)) (hS : IsPGroup 2 S) (hB' : B' ∈ lFamily S)
    (hY : B' ⊔ S = Y) : IsExt ↥B' (fun V _ => IsE2 k V) (fun Y _ => IsPSL 3 2 1 Y) := by
  obtain ⟨ol, t, hdata, halt, -, pt, hpt, hYp, vl, hvol, hVnorm, hvc, hvsq, hvfix, hV, hE, htr⟩ :=
    hF
  obtain ⟨hn, hnot⟩ := halt rfl
  obtain ⟨hA, hcomm, hN⟩ := alt_kind (sizeE := 168) hS hB' hY hdata hn hnot hcard rfl hV
  exact e2_psl32_of_core hB' hY hdata hA hcomm rfl pt hpt hYp vl hvol hVnorm hvc hvsq hvfix hE hN
    hV rfl (htr rfl)

end Facts

end CFSG.Quasithin.A312M23
