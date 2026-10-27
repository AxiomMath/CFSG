module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312M23Core
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312M23Blk
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312WordsHat
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312WordsIdx
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312WordsDefs
public import CFSG.LocalAnalysis.QuasithinUnique.K1.SporadicBase
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatLat
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312ExtShapesBase
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312RuCases
public import CFSG.Sporadic.Mathieu.M22
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
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312RuL32
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312RuPerf
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312RuSimple
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtJ4LocCheck
public import Certificates.Data.CFSGNative.MonsterB.Rep4371Model
public import Certificates.Kernel.J4Count.FixCE
public import Certificates.Kernel.J4Count.FixCPairBase1
public import Certificates.Kernel.J4Count.KFactsBase

public section

namespace CFSG.Quasithin.A312M23

open CFSG.QuasithinUnique.K1.SporadicPerm CFSG.QuasithinUnique.Ch1.SporLat
open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.Vol2Native.A312L
open CFSG.Quasithin.A312Words CFSG.Quasithin.A312ExtShapes CFSG.Quasithin.A312Ru
open CFSG.Sporadic.Mathieu (m22gA m22gB m22_eq card_M22 fam_m22_simplicity)
open CFSG.Blueprint
open scoped Pointwise commutatorElement

theorem commutator_eq_top_of_simple {X : Type} [Group X] [IsSimpleGroup X]
    (h : ∃ a b : X, a * b ≠ b * a) : commutator X = ⊤ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator X) with hb | ht
  · exfalso
    obtain ⟨a, b, hab⟩ := h
    apply hab
    have : ⁅a, b⁆ ∈ commutator X :=
      Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
    rw [hb, Subgroup.mem_bot, commutatorElement_eq_one_iff_commute] at this
    exact this
  · exact ht

theorem m22_iso_of_rho {G : Type} [Group G] [Finite G]
    {α : Type} [MulAction G α] {Y : Subgroup G} (pt : Fin 22 → α)
    (hpt : Function.Injective pt) (hY : ∀ z ∈ Y, ∀ i, ∃ j, z • pt i = pt j) {eA eB : G}
    (hA : eA ∈ Y) (hB : eB ∈ Y) (hcA' : rhoFn Y pt hpt hY eA = m22gA)
    (hcB' : rhoFn Y pt hpt hY eB = m22gB) (hcard : Nat.card Y = 443520) :
    Nonempty (↥Y ≃* ↥NativeSporadic.M22) := by
  classical
  let ρ := actHom Y pt hpt hY
  have hle : NativeSporadic.M22 ≤ ρ.range := by
    rw [m22_eq, Subgroup.closure_le]
    rintro x (rfl | rfl)
    · exact ⟨⟨eA, hA⟩, by rw [← rhoFn_of_mem hA]; exact hcA'⟩
    · exact ⟨⟨eB, hB⟩, by rw [← rhoFn_of_mem hB]; exact hcB'⟩
  have hM : Nat.card NativeSporadic.M22 = 443520 := card_M22
  have h1 := Subgroup.card_ker_mul_card_range ρ
  rw [hcard] at h1
  have hr : 443520 ≤ Nat.card ρ.range := hM ▸ Subgroup.card_le_of_le hle
  have hpos : 0 < Nat.card ρ.ker := Nat.card_pos
  have hk1 : Nat.card ρ.ker = 1 := by nlinarith
  have hker : ρ.ker = ⊥ := Subgroup.eq_bot_of_card_eq _ hk1
  have hrange : ρ.range = NativeSporadic.M22 := by
    refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
    rw [hk1, one_mul] at h1
    rw [h1, hM]
  exact ⟨(MonoidHom.ofInjective ((MonoidHom.ker_eq_bot_iff ρ).mp hker)).trans
    (MulEquiv.subgroupCongr hrange)⟩

theorem perm_eq_of_getD {g h : Equiv.Perm (Fin 22)} {L : List ℕ}
    (hg : ∀ i, (g i).val = L.getD i.val 0) (hh : tab 22 h = L) : g = h :=
  Equiv.ext fun i => Fin.ext (by rw [hg i, ← hh, tab_getD]; rfl)

theorem m22_iso_of_facts {G : Type} [Group G] [Finite G]
    {α : Type} [MulAction G α] {Y : Subgroup G} (hF : M22Facts α Y)
    (hcard : Nat.card Y = 443520) : Nonempty (↥Y ≃* ↥NativeSporadic.M22) := by
  obtain ⟨pt, hpt, hYp, eA, eB, hA, hB, hgA, hgB⟩ := hF
  exact m22_iso_of_rho pt hpt hYp hA hB (perm_eq_of_getD hgA m22_tab_a)
    (perm_eq_of_getD hgB m22_tab_b) hcard

theorem eq_of_m22 {G : Type} [Group G] [Finite G]
    {S B Y : Subgroup G} (hB : B ∈ lFamily S) (hY : B ⊔ S = Y)
    (e : ↥Y ≃* ↥NativeSporadic.M22) : B = Y := by
  obtain ⟨-, -, hsimple⟩ := fam_m22_simplicity
  have hsY : IsSimpleGroup ↥Y := (MulEquiv.isSimpleGroup_congr e).mpr hsimple
  have hcard : ¬ (Nat.card ↥NativeSporadic.M22).Prime := by
    rw [card_M22]
    norm_num
  have hnab : ∃ a b : ↥NativeSporadic.M22, a * b ≠ b * a := nonabelian_of_simple hcard
  have hnabY : ∃ a b : ↥Y, a * b ≠ b * a :=
    nonabelian_of_simple (by rw [Nat.card_congr e.toEquiv]; exact hcard)
  have hperf : ⁅Y, Y⁆ = Y :=
    Subgroup.isPerfect_iff.mp (Group.isPerfect_def.mpr (commutator_eq_top_of_simple hnabY))
  have hker : Group.IsSolvable e.toMonoidHom.ker := by
    have : e.toMonoidHom.ker = ⊥ := (MonoidHom.ker_eq_bot_iff _).mpr e.injective
    rw [this]
    infer_instance
  exact eq_of_perfect_simple_quotient hB hY le_rfl (by rw [hperf]) hperf hnab e.toMonoidHom
    e.surjective hker

variable {Γ : Type} [Group Γ] [Finite Γ] {n : ℕ} [MulAction Γ (Fin n)]
  {Lab : Type} [DecidableEq Lab] [Hashable Lab] [Inhabited Lab]

theorem isSporadic_m22_of_facts {G : Type} [Group G] [Finite G]
    {α : Type} [MulAction G α] {S B' Y : Subgroup G} (hF : M22Facts α Y)
    (hcard : Nat.card Y = 443520) (hB' : B' ∈ lFamily S) (hY : B' ⊔ S = Y) :
    IsSporadic .M22 ↥B' := by
  obtain ⟨e⟩ := m22_iso_of_facts hF hcard
  have hBY : B' = Y := eq_of_m22 hB' hY e
  subst hBY
  exact ⟨e⟩

end CFSG.Quasithin.A312M23
