module

public import CFSG.RankThree.GF2n.Tim79aCitedAS
public import CFSG.Quasithin.Background.SmithB45J2Holds
public import CFSG.Quasithin.Background.B5Sec
public import CFSG.Quasithin.MS93.S38EAQuot
public import CFSG.Quasithin.H13.NQBlockOddRankOneBridge
public import CFSG.Quasithin.Background.B5Basic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.RankThree.GF2n.Tim79a

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.B5 CFSG.Quasithin.MS93.S38E
open scoped commutatorElement Matrix

theorem inf_centSec_eq_bot_of_isSimpleGroup {V : Type*} [CommGroup V]
    {L : Subgroup (MulAut V)} [IsSimpleGroup ↥L] {W N : Subgroup V}
    (hLW : L ≤ stabSub W) (hLN : L ≤ stabSub N) (hnc : NonCent L W N) :
    L ⊓ centSec W N = ⊥ := by
  have hker : (B5.secHom L hLW hLN).ker = ⊥ := by
    rw [eq_bot_iff]
    intro g hg
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (B5.secHom L hLW hLN).ker with h | h
    · exact Subgroup.mem_bot.mpr (by simpa [h] using hg)
    · exfalso
      obtain ⟨l, hl, w, hw, hlw⟩ := hnc
      have h1 : B5.secHom L hLW hLN ⟨l, hl⟩ = 1 := by
        rw [← MonoidHom.mem_ker, h]
        exact Subgroup.mem_top _
      have h2 := congrArg (fun φ : MulAut (Sec W N) => φ (QuotientGroup.mk ⟨w, hw⟩)) h1
      rw [B5.secHom_mk, MulAut.one_apply] at h2
      have h3 : (l w)⁻¹ * w ∈ N := by
        have h3' := QuotientGroup.eq.mp h2
        rw [Subgroup.mem_subgroupOf] at h3'
        simpa only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_mk] using h3'
      exact hlw (by simpa [mul_comm] using N.inv_mem h3)
  rw [eq_bot_iff]
  intro x hx
  have hmem : (⟨x, hx.1⟩ : ↥L) ∈ (B5.secHom L hLW hLN).ker :=
    (B5.mem_ker_secHom L hLW hLN ⟨x, hx.1⟩).2 hx.2
  rw [hker, Subgroup.mem_bot] at hmem
  exact Subgroup.mem_bot.mpr (congrArg Subtype.val hmem)

theorem aschbacherHJRepresentationStatement_holds :
    AschbacherHJRepresentationStatement := by
  classical
  intro n ρ hρ
  by_contra hn
  push Not at hn
  let V := Multiplicative (Fin n → ZMod 2)
  let ρL : NativeSporadic.J2 →* (Module.End (ZMod 2) (Fin n → ZMod 2))ˣ :=
    (Matrix.GeneralLinearGroup.toLin (n := Fin n) (R := ZMod 2)).toMonoidHom.comp ρ
  let ρA : NativeSporadic.J2 →* MulAut V :=
    (CFSG.Quasithin.H13.NQBlock.unitsToMulAut (W := Fin n → ZMod 2)).comp ρL
  have hρL : Function.Injective ρL :=
    (Matrix.GeneralLinearGroup.toLin (n := Fin n) (R := ZMod 2)).injective.comp hρ
  have hρA : Function.Injective ρA :=
    (CFSG.Quasithin.H13.NQBlock.unitsToMulAut_injective
      (W := Fin n → ZMod 2)).comp hρL
  let L : Subgroup (MulAut V) := ρA.range
  haveI hJ2simple : IsSimpleGroup NativeSporadic.J2 := CFSG.Sporadic.J2.isSimpleGroup_J2
  haveI hLsimple : IsSimpleGroup ↥L :=
    MulEquiv.isSimpleGroup (MonoidHom.ofInjective hρA).symm
  have hcardL : Nat.card ↥L = 604800 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hρA).toEquiv]
    exact CFSG.Sporadic.J2.card_J2
  have hnc : ¬ IsMulCommutative ↥L := by
    intro hc
    haveI : IsMulCommutative ↥L := hc
    have hprime : (Nat.card ↥L).Prime := Group.is_simple_iff_prime_card.mp inferInstance
    rw [hcardL] at hprime
    norm_num at hprime
  have hperf : Group.IsPerfect ↥L :=
    TauCeti.IsSimpleGroup.isPerfect_of_not_isMulCommutative hnc
  have hKp : ⁅L, L⁆ = L := by
    haveI : Group.IsPerfect ↥L := hperf
    exact Subgroup.commutator_eq_self
  have hnoncent : NonCent L ⊤ ⊥ := by
    obtain ⟨k, hk1⟩ := exists_ne (1 : ↥L)
    have hkne : (k : MulAut V) ≠ 1 := fun h => hk1 (Subtype.ext h)
    obtain ⟨v, hv⟩ : ∃ v : V, (k : MulAut V) v ≠ v := by
      by_contra h
      push Not at h
      exact hkne (MulEquiv.ext h)
    refine ⟨(k : MulAut V), k.2, v, Subgroup.mem_top v, ?_⟩
    rw [Subgroup.mem_bot]
    exact fun h => hv (mul_inv_eq_one.mp h)
  obtain ⟨W', N', hN'W', hW'Top, hirr, hnc'⟩ :=
    CFSG.Quasithin.MS93.S38EA.exists_irrSec_nonCent (Y := V) le_rfl hKp
      (Nat.card V) ⊤ ⊥ (by rw [Subgroup.card_top, Subgroup.card_bot]; omega) bot_le
      (fun _ _ _ _ => Subgroup.mem_top _)
      (fun _ _ w hw => by
        rw [Subgroup.mem_bot] at hw ⊢
        rw [hw, map_one])
      hnoncent
  have hLW : L ≤ stabSub W' := CFSG.Quasithin.B1.le_stabSub_of_invariant hirr.2.1
  have hLN : L ≤ stabSub N' := CFSG.Quasithin.B1.le_stabSub_of_invariant hirr.2.2.1
  have hfaith : L ⊓ centSec W' N' = ⊥ :=
    inf_centSec_eq_bot_of_isSimpleGroup (L := L) (W := W') (N := N') hLW hLN hnc'
  let L' : Subgroup (MulAut (Sec W' N')) := autSec L W' N'
  have hIrr : XMod.IsIrrSec ↥L' (⊥ : Subgroup (Sec W' N')) ⊤ :=
    B5.isIrrSec_autSec (L := L) (W := W') (C := N') hirr.1
      (fun J hJ => hirr.2.2.2 J hJ) hLW hLN
  have hSpor : NativeSporadic.IsSporadic ↥L' .J2 :=
    ⟨(B5.secEquiv L hLW hLN hfaith).symm.trans (MonoidHom.ofInjective hρA).symm⟩
  have hexpSec : ∀ v : Sec W' N', v * v = 1 := by
    intro v
    induction v using QuotientGroup.induction_on with
    | H w =>
      rw [← QuotientGroup.mk_mul]
      have hw : (w : V) * (w : V) = 1 := by
        apply Multiplicative.toAdd.injective
        rw [toAdd_mul, toAdd_one]
        funext i
        exact CharTwo.add_self_eq_zero _
      rw [show w * w = 1 by exact Subtype.ext hw, QuotientGroup.mk_one]
  have hexpSecPow : ∀ v : Sec W' N', v ^ 2 = 1 := fun v => by
    rw [pow_two]
    exact hexpSec v
  have hSecLe : Nat.card (Sec W' N') ≤ Nat.card ↥W' := by
    have h := CFSG.Quasithin.card_sec_mul (V := V) (W := W') (U := N') hirr.1.le
    rw [← h]
    exact Nat.le_mul_of_pos_right _ Nat.card_pos
  have hWle : Nat.card ↥W' ≤ Nat.card V := by
    simpa using Subgroup.card_le_of_le hW'Top
  have hVcard : Nat.card V = 2 ^ n := by
    rw [Nat.card_congr (Multiplicative.toAdd (α := Fin n → ZMod 2)), Nat.card_fun,
      Nat.card_eq_fintype_card (α := Fin n), Fintype.card_fin, Nat.card_zmod]
  have hnlt : 2 ^ n < 2 ^ 12 := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).2 hn
  have hlt4096 : Nat.card (Sec W' N') < 4096 := by
    have h1 : Nat.card (Sec W' N') ≤ 2 ^ n := hSecLe.trans (hWle.trans_eq hVcard)
    calc Nat.card (Sec W' N') ≤ 2 ^ n := h1
      _ < 2 ^ 12 := hnlt
      _ = 4096 := by norm_num
  have hcardSec : Nat.card (Sec W' N') < 2 ^ 24 :=
    hlt4096.trans (by norm_num)
  have hSmall : J2SmallModules := CFSG.Quasithin.J2Mod.j2SmallModules_holds
  obtain ⟨π, hπ⟩ := hSmall (Sec W' N') hexpSecPow L' hSpor hIrr hcardSec
  have hcardSec4096 : Nat.card (Sec W' N') = 4096 := by
    obtain ⟨e, -⟩ := CFSG.Quasithin.J2Row.exists_equiv_of_zornQ hπ
    rw [Nat.card_congr e.toEquiv, CFSG.Quasithin.J2Row.card_W6]
  omega

end CFSG.RankThree.GF2n.Tim79a
