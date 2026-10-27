module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.MinimalCounterexample
public import CFSG.ThirdParty.QiuzhenCFSG.BenderGlauberman.Defs

import CFSG.ThirdParty.QiuzhenCFSG.BenderGlauberman.TheoremC
import all CFSG.ThirdParty.QiuzhenCFSG.BenderGlauberman.Defs
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.FinalTheorem
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma28Helpers
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma27Infra
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.PreambleInvolutions
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Reflection

namespace CFSG
end CFSG
open CFSG

open scoped Pointwise

namespace CFSG.GorensteinWalter

noncomputable section

universe u

private lemma eq_sup_zpowers_of_index_two_probe
    {G : Type u} [Group G] [Finite G]
    {H K : Subgroup G} (hK : K ≤ H) {x : G}
    (hxH : x ∈ H) (hxK : x ∉ K) (hindex : (K.subgroupOf H).index = 2) :
    H = K ⊔ Subgroup.zpowers x := by
  classical
  let Q := ↥H ⧸ (K.subgroupOf H)
  have hQcard : Nat.card Q = 2 := hindex
  let q1 : Q := QuotientGroup.mk (s := K.subgroupOf H) (1 : ↥H)
  let q2 : Q := QuotientGroup.mk (s := K.subgroupOf H) (⟨x, hxH⟩ : ↥H)
  have hq1q2 : q1 ≠ q2 := by
    intro h
    exact hxK (by
      simpa [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv]
        using (QuotientGroup.eq.mp h))
  have hall : ∀ z : Q, z = q1 ∨ z = q2 := by
    intro z
    by_cases hz : z = q1
    · exact Or.inl hz
    · rcases (Nat.card_eq_two_iff' q1).mp hQcard with ⟨y0, _hy0ne, hy0uniq⟩
      exact Or.inr ((hy0uniq z hz).trans (hy0uniq q2 (Ne.symm hq1q2)).symm)
  refine le_antisymm ?_ ?_
  · intro y hy
    by_cases hyq : QuotientGroup.mk (s := K.subgroupOf H) (⟨y, hy⟩ : ↥H) = q1
    · exact SetLike.le_def.mp le_sup_left (by
        simpa [inv_inv] using (K.inv_mem (by
          simpa [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv]
            using (QuotientGroup.eq.mp hyq))))
    · have hyq2 : QuotientGroup.mk (s := K.subgroupOf H) (⟨y, hy⟩ : ↥H) = q2 :=
        (hall (QuotientGroup.mk (s := K.subgroupOf H) (⟨y, hy⟩ : ↥H))).resolve_left hyq
      have hmem : y⁻¹ * x ∈ K := by
        simpa [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv]
          using (QuotientGroup.eq.mp hyq2)
      have hxEq : x * (y⁻¹ * x)⁻¹ = y := by group
      rw [← hxEq]
      exact (K ⊔ Subgroup.zpowers x).mul_mem
        (SetLike.le_def.mp le_sup_right (Subgroup.mem_zpowers x))
        (SetLike.le_def.mp le_sup_left (K.inv_mem hmem))
  · exact sup_le hK (by
      intro z hz
      rcases (Subgroup.mem_zpowers_iff.mp hz) with ⟨k, hk⟩
      rw [← hk]
      exact H.zpow_mem hxH k)

private lemma invertedSubgroup_normal_in_H_probe
    {G : Type u} [Group G] [Finite G]
    (c : BenderGlauberman.Hyp11 G)
    {I : Subgroup G}
    (hS0cent : c.S0 ≤ Subgroup.centralizer (I : Set G))
    (hIinv : BenderGlauberman.IsInvertedBy c.t1 I)
    (hInorm : IsNormalIn I c.U)
    (hIleU : I ≤ c.U) :
    c.H ≤ Subgroup.normalizer (I : Set G) := by
  have hUle : c.U ≤ Subgroup.normalizer (I : Set G) := by
    intro u hu
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · exact hInorm.2 u hu x
    · intro hx
      have hx' := hInorm.2 u⁻¹ (c.U.inv_mem hu) (u * x * u⁻¹) hx
      have hEq : u⁻¹ * (u * x * u⁻¹) * u = x := by group
      simpa [hEq, inv_inv] using hx'
  have hS0le : c.S0 ≤ Subgroup.normalizer (I : Set G) :=
    hS0cent.trans (Subgroup.centralizer_le_normalizer (I : Set G))
  have ht1norm : c.t1 ∈ Subgroup.normalizer (I : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      simpa [hIinv x hx] using I.inv_mem hx
    · intro hx
      have hEq : c.t1 * (c.t1 * x * c.t1⁻¹) * c.t1⁻¹ = x := by
        have ht1sq : c.t1 * c.t1 = 1 := by
          simpa [pow_two] using c.t1_involution.2
        have ht1inv : c.t1⁻¹ = c.t1 := inv_eq_of_mul_eq_one_right ht1sq
        rw [ht1inv]
        calc
          c.t1 * (c.t1 * x * c.t1) * c.t1 =
              (c.t1 * c.t1) * x * (c.t1 * c.t1) := by group
          _ = x := by rw [ht1sq]; simp
      rw [← hEq]
      simpa [hIinv (c.t1 * x * c.t1⁻¹) hx] using I.inv_mem hx
  have hSle : (c.S : Subgroup G) ≤ Subgroup.normalizer (I : Set G) := by
    rw [eq_sup_zpowers_of_index_two_probe c.S0_le_S c.t1_mem_S
      c.t1_not_mem_S0 (BenderGlauberman.S0_index c)]
    exact sup_le hS0le (Subgroup.zpowers_le.mpr ht1norm)
  rw [← c.H_eq_US]
  exact sup_le hUle hSle

private lemma exists_conj_mem_S_of_involution_H_probe
    {G : Type u} [Group G] [Finite G]
    (c : BenderGlauberman.Hyp11 G) {y : G}
    (hyH : y ∈ c.H) (hyInv : IsInvolution y) :
    ∃ h : c.H, (h : G) * y * (h : G)⁻¹ ∈ (c.S : Subgroup G) := by
  classical
  let Y : Subgroup G := Subgroup.zpowers y
  have hYH : Y ≤ c.H := Subgroup.zpowers_le.mpr hyH
  let YH : Subgroup c.H := Y.subgroupOf c.H
  have hyord : orderOf y = 2 := orderOf_eq_prime hyInv.2 hyInv.1
  have hYp : IsPGroup 2 Y :=
    IsPGroup.of_card (n := 1) (by simp [Y, Nat.card_zpowers, hyord])
  have hYHp : IsPGroup 2 YH :=
    hYp.of_equiv (Subgroup.subgroupOfEquivOfLe hYH).symm
  obtain ⟨Q, hYHQ⟩ := IsPGroup.exists_le_sylow (G := c.H) hYHp
  let P : Sylow 2 c.H := c.S.subtype (BenderGlauberman.S_le_H c)
  obtain ⟨h, hh⟩ :=
    @MulAction.IsPretransitive.exists_smul_eq
      c.H (Sylow 2 c.H) inferInstance inferInstance Q P
  refine ⟨h, ?_⟩
  have hyYH : (⟨y, hyH⟩ : c.H) ∈ YH := Subgroup.mem_zpowers y
  have hyQ : (⟨y, hyH⟩ : c.H) ∈ Q := hYHQ hyYH
  have hyMap : (MulAut.conj h) (⟨y, hyH⟩ : c.H) ∈
      (Q : Subgroup c.H).map (MulAut.conj h).toMonoidHom :=
    Subgroup.mem_map_of_mem (MulAut.conj h).toMonoidHom hyQ
  have hh' := congrArg (fun R : Sylow 2 c.H ↦ (R : Subgroup c.H)) hh
  change (Q : Subgroup c.H).map (MulAut.conj h).toMonoidHom =
      (P : Subgroup c.H) at hh'
  rw [hh'] at hyMap
  exact hyMap

private lemma involution_centralizing_nontrivial_invertedSubgroup_eq_t_probe
    {G : Type u} [Group G] [Finite G]
    (c : BenderGlauberman.Hyp11 G)
    {I X : Subgroup G}
    (hS0cent : c.S0 ≤ Subgroup.centralizer (I : Set G))
    (hIinv : BenderGlauberman.IsInvertedBy c.t1 I)
    (hInormH : c.H ≤ Subgroup.normalizer (I : Set G))
    (hIodd : Nat.Coprime 2 (Nat.card I))
    (hIleU : I ≤ c.U)
    (hXne : X ≠ ⊥) (hXI : X ≤ I)
    {y : G} (hyH : y ∈ c.H) (hyInv : IsInvolution y)
    (hycent : y ∈ Subgroup.centralizer (X : Set G)) :
    y = c.t := by
  classical
  obtain ⟨h, hyS⟩ := exists_conj_mem_S_of_involution_H_probe c hyH hyInv
  let y' : G := (h : G) * y * (h : G)⁻¹
  have hy'S : y' ∈ (c.S : Subgroup G) := hyS
  have hy'Inv : IsInvolution y' := by
    constructor
    · intro hy'1
      apply hyInv.1
      have : y = (h : G)⁻¹ * y' * (h : G) := by simp [y']; group
      rw [this, hy'1]
      group
    · calc
        y' ^ 2 = (h : G) * (y ^ 2) * (h : G)⁻¹ := by simp [y', pow_two]
        _ = 1 := by rw [hyInv.2]; group
  have hhcent : (h : G) ∈ Subgroup.centralizer ({c.t} : Set G) := by
    rw [← c.H_eq_centralizer]
    exact h.2
  have hcomm : c.t * (h : G) = (h : G) * c.t :=
    (Subgroup.mem_centralizer_iff.mp hhcent) c.t (by simp)
  have hconjt : (h : G) * c.t * (h : G)⁻¹ = c.t := by
    calc
      (h : G) * c.t * (h : G)⁻¹ = (c.t * (h : G)) * (h : G)⁻¹ := by rw [hcomm]
      _ = c.t := by group
  by_cases hy'S0 : y' ∈ c.S0
  · have hy'2 : (⟨y', hy'S0⟩ : c.S0) ^ 2 = 1 := by
      apply Subtype.ext
      exact hy'Inv.2
    rcases (BenderGlauberman.S0_sq_eq_one_iff c).mp hy'2 with hy'1 | hy't
    · exact False.elim (hy'Inv.1 (congrArg Subtype.val hy'1))
    · have hy't' : y' = c.t := congrArg Subtype.val hy't
      have hyback : y = (h : G)⁻¹ * y' * (h : G) := by simp [y']; group
      calc
        y = (h : G)⁻¹ * y' * (h : G) := hyback
        _ = (h : G)⁻¹ * c.t * (h : G) := by rw [hy't']
        _ = c.t := by
          calc
            (h : G)⁻¹ * c.t * (h : G) = (h : G)⁻¹ * (c.t * (h : G)) := by group
            _ = (h : G)⁻¹ * ((h : G) * c.t) := by rw [hcomm]
            _ = c.t := by group
  · let yS : c.S := ⟨y', hy'S⟩
    let t1S : c.S := ⟨c.t1, c.t1_mem_S⟩
    have hyS0' : yS ∉ c.S0.subgroupOf (c.S : Subgroup G) := by
      exact fun hy ↦ hy'S0 (Subgroup.mem_subgroupOf.mp hy)
    have ht1S0 : t1S ∉ c.S0.subgroupOf (c.S : Subgroup G) := by
      exact fun ht ↦ c.t1_not_mem_S0 (Subgroup.mem_subgroupOf.mp ht)
    have hyrS0sub : yS * t1S ∈ c.S0.subgroupOf (c.S : Subgroup G) :=
      (Subgroup.mul_mem_iff_of_index_two (BenderGlauberman.S0_index c)).2
        (by simp [hyS0', ht1S0])
    have hyrS0 : y' * c.t1 ∈ c.S0 := by
      exact Subgroup.mem_subgroupOf.mp hyrS0sub
    obtain ⟨x, hxne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hXne
    let x' : G := (h : G) * (x : G) * (h : G)⁻¹
    have hxI : (x : G) ∈ I := hXI x.2
    have hx'I : x' ∈ I := by
      exact (Subgroup.mem_normalizer_iff.mp (hInormH h.2) (x : G)).mp hxI
    have hx'ne : x' ≠ 1 := by
      intro hx'1
      apply hxne
      apply Subtype.ext
      have hxback : (x : G) = (h : G)⁻¹ * x' * (h : G) := by simp [x']; group
      rw [hxback, hx'1]
      simp
    have hy'fix : y' * x' * y'⁻¹ = x' := by
      have hycomm : (x : G) * y = y * (x : G) :=
        (Subgroup.mem_centralizer_iff.mp hycent) (x : G) x.2
      calc
        y' * x' * y'⁻¹ =
            (h : G) * (y * (x : G) * y⁻¹) * (h : G)⁻¹ := by
              simp [y', x']; group
        _ = (h : G) * (x : G) * (h : G)⁻¹ := by
          have : y * (x : G) * y⁻¹ = (x : G) := by
            rw [← hycomm]
            group
          rw [this]
        _ = x' := rfl
    have hrcent : (y' * c.t1) * x' * (y' * c.t1)⁻¹ = x' := by
      have hrmem := hS0cent hyrS0
      have hcomm : x' * (y' * c.t1) = (y' * c.t1) * x' :=
        (Subgroup.mem_centralizer_iff.mp hrmem) x' hx'I
      rw [← hcomm]
      group
    have hy'comm : y' * x' = x' * y' := by
      exact mul_inv_eq_iff_eq_mul.mp (by simpa [mul_assoc] using hy'fix)
    have hrcomm : (y' * c.t1) * x' = x' * (y' * c.t1) := by
      exact mul_inv_eq_iff_eq_mul.mp (by simpa [mul_assoc] using hrcent)
    have ht1comm : c.t1 * x' = x' * c.t1 := by
      apply mul_left_cancel (a := y')
      calc
        y' * (c.t1 * x') = (y' * c.t1) * x' := by group
        _ = x' * (y' * c.t1) := hrcomm
        _ = (x' * y') * c.t1 := by group
        _ = (y' * x') * c.t1 := by rw [hy'comm]
        _ = y' * (x' * c.t1) := by group
    have ht1fix : c.t1 * x' * c.t1⁻¹ = x' := by
      rw [ht1comm]
      group
    have hx'eqinv : x' = x'⁻¹ := ht1fix.symm.trans (hIinv x' hx'I)
    have hx'2 : x' ^ 2 = 1 := by
      rw [pow_two]
      calc
        x' * x' = x'⁻¹ * x' := congrArg (fun z : G ↦ z * x') hx'eqinv
        _ = 1 := by simp
    have hxsub2 : (⟨x', hx'I⟩ : I) ^ 2 = 1 := by
      apply Subtype.ext
      exact hx'2
    have hxsub1 := eq_one_of_sq_eq_one_of_coprime_two hIodd hxsub2
    exact False.elim (hx'ne (congrArg Subtype.val hxsub1))

private lemma card_conjClass_eq_index_probe
    {G : Type u} [Group G] [Finite G] (x : G) :
    Nat.card (ConjClasses.mk x).carrier =
      (Subgroup.centralizer ({x} : Set G)).index := by
  classical
  let : Fintype G := Fintype.ofFinite G
  have hst := MulAction.card_orbit_mul_card_stabilizer_eq_card_group (ConjAct G) x
  have hst' : Fintype.card (ConjClasses.mk x).carrier *
      Fintype.card (MulAction.stabilizer (ConjAct G) x) = Fintype.card G := by
    simpa [ConjAct.orbit_eq_carrier_conjClasses] using hst
  let e : MulAction.stabilizer (ConjAct G) x ≃
      ↑(Subgroup.centralizer ({x} : Set G)) :=
    { toFun := fun y ↦
        ⟨ConjAct.ofConjAct y.1, by
          rw [Subgroup.mem_centralizer_iff]
          intro z hz
          simp at hz
          rw [hz]
          have hy : y.1 • x = x := y.2
          rw [ConjAct.smul_def] at hy
          have hmain : ConjAct.ofConjAct y.1 * x = x * ConjAct.ofConjAct y.1 := by
            calc
              ConjAct.ofConjAct y.1 * x =
                  (ConjAct.ofConjAct y.1 * x * (ConjAct.ofConjAct y.1)⁻¹) *
                    ConjAct.ofConjAct y.1 := by group
              _ = x * ConjAct.ofConjAct y.1 := by rw [hy]
          exact hmain.symm⟩
      invFun := fun z ↦ ⟨ConjAct.toConjAct (z : G), by
        change ConjAct.toConjAct (z : G) • x = x
        rw [ConjAct.toConjAct_smul]
        exact mul_inv_eq_of_eq_mul
          ((Subgroup.mem_centralizer_iff.mp z.2) x (by simp)).symm⟩
      left_inv := by intro y; apply Subtype.ext; rfl
      right_inv := by intro z; apply Subtype.ext; rfl }
  have hC : Fintype.card (MulAction.stabilizer (ConjAct G) x) =
      Nat.card (↑(Subgroup.centralizer ({x} : Set G))) := by
    rw [Nat.card_eq_fintype_card]
    exact Fintype.card_congr e
  have hN : (Subgroup.centralizer ({x} : Set G)).index *
      Fintype.card (MulAction.stabilizer (ConjAct G) x) = Fintype.card G := by
    rw [hC]
    rw [← Nat.card_eq_fintype_card]
    exact Subgroup.index_mul_card (Subgroup.centralizer ({x} : Set G))
  rw [Nat.card_eq_fintype_card]
  exact Nat.mul_right_cancel
    (by positivity : 0 < Fintype.card (MulAction.stabilizer (ConjAct G) x)) (by
      rw [← hN] at hst'
      exact hst')

private lemma card_t_orbit_eq_H_index_probe
    {G : Type u} [Group G] [Finite G]
    (c : BenderGlauberman.Hyp11 G) :
    Nat.card (↑(MulAction.orbit (ConjAct G) c.t)) = c.H.index := by
  rw [ConjAct.orbit_eq_carrier_conjClasses]
  rw [card_conjClass_eq_index_probe, c.H_eq_centralizer]

public theorem invertedSubgroup_card_coprime_H_index
    {G : Type u} [Group G] [Finite G]
    (c : BenderGlauberman.Hyp11 G)
    {I : Subgroup G}
    (hS0cent : c.S0 ≤ Subgroup.centralizer (I : Set G))
    (hIinv : BenderGlauberman.IsInvertedBy c.t1 I)
    (hInorm : IsNormalIn I c.U)
    (hIleU : I ≤ c.U)
    (hIodd : Nat.Coprime 2 (Nat.card I))
    (hNX : ∀ X : Subgroup G, X ≠ ⊥ → X ≤ I →
      Subgroup.normalizer (X : Set G) ≤ c.H) :
    Nat.Coprime (Nat.card I) c.H.index := by
  classical
  have hUleH : c.U ≤ c.H := by
    rw [← c.H_eq_US]
    exact le_sup_left
  have hInormH : c.H ≤ Subgroup.normalizer (I : Set G) :=
    invertedSubgroup_normal_in_H_probe c hS0cent hIinv hInorm hIleU
  by_contra hcop
  rcases Nat.Prime.not_coprime_iff_dvd.mp hcop with ⟨p, hp, hpI, hpH⟩
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨x, hxord⟩ := exists_prime_orderOf_dvd_card' (G := I) p hpI
  have hxordG : orderOf (x : G) = p := by
    rw [Subgroup.orderOf_coe]
    exact hxord
  have hxneSub : x ≠ 1 := by
    intro hx1
    apply hp.ne_one
    calc
      p = orderOf x := hxord.symm
      _ = 1 := by rw [hx1]; simp
  have hxne : (x : G) ≠ 1 := by
    intro hx1
    exact hxneSub (Subtype.ext hx1)
  let X : Subgroup G := Subgroup.zpowers (x : G)
  have hXne : X ≠ ⊥ := Subgroup.zpowers_ne_bot.mpr hxne
  have hXI : X ≤ I := Subgroup.zpowers_le.mpr x.2
  have hXp : IsPGroup p X := by
    apply IsPGroup.of_card (n := 1)
    simp [X, Nat.card_zpowers, hxordG]
  let Ω := ↑(MulAction.orbit (ConjAct G) c.t)
  let ρ : X →* ConjAct G :=
    ConjAct.toConjAct.toMonoidHom.comp X.subtype
  let : MulAction X Ω := MulAction.compHom Ω ρ
  let tΩ : Ω := ⟨c.t, MulAction.mem_orbit_self c.t⟩
  have htfix : tΩ ∈ MulAction.fixedPoints X Ω := by
    rw [MulAction.mem_fixedPoints]
    intro a
    apply Subtype.ext
    change (a : G) * c.t * (a : G)⁻¹ = c.t
    have haH : (a : G) ∈ c.H :=
      (hXI a.2 |> hIleU |> hUleH)
    have hacent : (a : G) ∈ Subgroup.centralizer ({c.t} : Set G) := by
      rw [← c.H_eq_centralizer]
      exact haH
    have hacomm : c.t * (a : G) = (a : G) * c.t :=
      (Subgroup.mem_centralizer_iff.mp hacent) c.t (by simp)
    calc
      (a : G) * c.t * (a : G)⁻¹ = (c.t * (a : G)) * (a : G)⁻¹ := by rw [hacomm]
      _ = c.t := by group
  have hfixedUnique : Subsingleton (↑(MulAction.fixedPoints X Ω)) := by
    constructor
    intro z w
    have heq_t : ∀ q : ↑(MulAction.fixedPoints X Ω), q.1 = tΩ := by
      intro q
      apply Subtype.ext
      let y : G := q.1.1
      obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.mp q.1.2
      have hyeq : ConjAct.ofConjAct g * c.t * (ConjAct.ofConjAct g)⁻¹ = y := by
        simpa [y, ConjAct.smul_def] using hg
      have hyInv : IsInvolution y := by
        constructor
        · intro hy1
          apply c.t_involution.1
          have htback : c.t = (ConjAct.ofConjAct g)⁻¹ * y * ConjAct.ofConjAct g := by
            rw [← hyeq]
            group
          rw [htback, hy1]
          group
        · calc
            y ^ 2 = ConjAct.ofConjAct g * (c.t ^ 2) *
                (ConjAct.ofConjAct g)⁻¹ := by rw [← hyeq]; simp [pow_two]
            _ = 1 := by rw [c.t_involution.2]; group
      have hycent : y ∈ Subgroup.centralizer (X : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro a ha
        let aX : X := ⟨a, ha⟩
        have hfixa := (MulAction.mem_fixedPoints.mp q.2) aX
        have hfixval := congrArg (fun v : Ω ↦ (v : G)) hfixa
        change a * y * a⁻¹ = y at hfixval
        exact mul_inv_eq_iff_eq_mul.mp (by simpa [mul_assoc] using hfixval)
      have hyH : y ∈ c.H :=
        hNX X hXne hXI
          ((Subgroup.centralizer_le_normalizer (X : Set G)) hycent)
      exact involution_centralizing_nontrivial_invertedSubgroup_eq_t_probe
        c hS0cent hIinv hInormH hIodd hIleU hXne hXI hyH hyInv hycent
    apply Subtype.ext
    exact (heq_t z).trans (heq_t w).symm
  have hfixedCard : Nat.card (↑(MulAction.fixedPoints X Ω)) = 1 :=
    Nat.card_eq_one_iff_unique.mpr ⟨hfixedUnique, ⟨⟨tΩ, htfix⟩⟩⟩
  have hmod := hXp.card_modEq_card_fixedPoints Ω
  rw [card_t_orbit_eq_H_index_probe c, hfixedCard] at hmod
  have hp1 : p ∣ 1 := (hmod.dvd_iff (dvd_refl p)).mp hpH
  exact hp.ne_one (Nat.dvd_one.mp hp1)

public theorem forbiddenConfiguration_reflection_inverted_eq_U
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (hfc : ForbiddenConfiguration c)
    {s : G} (hs : c.IsReflection s) :
    invertedElements c.U s = (c.U : Set G) := by
  classical
  let : Fintype G := Fintype.ofFinite G
  have hone := fact_2_preamble_involutions_conjugate_proved hmin
  have hHSU := fact_2_preamble_H_eq_SU_proved hmin c
  obtain ⟨a, ha⟩ :=
    (Subgroup.isCyclic_iff_exists_zpowers_eq_top c.S0).mp c.S0_cyclic
  have haS0 : a ∈ c.S0 := by
    rw [← ha]
    exact Subgroup.mem_zpowers a
  have haS : a ∈ (c.S : Subgroup G) := c.S0_le_S haS0
  have hsInv : IsInvolution s :=
    centralizerSetup_reflection_isInvolution c hs
  let t2 : G := s * a
  have ht2S : t2 ∈ (c.S : Subgroup G) :=
    (c.S : Subgroup G).mul_mem hs.1 haS
  have ht2not : t2 ∉ c.S0 := by
    intro ht2
    have hs0 : t2 * a⁻¹ ∈ c.S0 :=
      c.S0.mul_mem ht2 (c.S0.inv_mem haS0)
    apply hs.2
    simpa [t2, mul_assoc] using hs0
  have ht2Inv : IsInvolution t2 :=
    centralizerSetup_reflection_isInvolution c ⟨ht2S, ht2not⟩
  have htprod : s * t2 = a := by
    have hss : s * s = 1 := by simpa [pow_two] using hsInv.2
    calc
      s * t2 = s * (s * a) := rfl
      _ = (s * s) * a := (mul_assoc s s a).symm
      _ = a := by rw [hss]; simp
  let bg : BenderGlauberman.Hyp11 G := {
    S := c.S
    m := c.m
    one_le_m := c.one_le_m
    dihedralEquiv := c.dihedralEquiv
    S0 := c.S0
    S0_le_S := c.S0_le_S
    S0_cyclic := c.S0_cyclic
    S_index_two := c.S_index_two
    t := c.t
    t_mem_S0 := c.t_mem_S0
    t_involution := c.t_involution
    one_involution_class := hone
    s := s
    s_mem_S := hs.1
    s_not_mem_S0 := hs.2
    s_involution := hsInv
    t1 := s
    t2 := t2
    t1_mem_S := hs.1
    t1_not_mem_S0 := hs.2
    t1_involution := hsInv
    t2_mem_S := ht2S
    t2_not_mem_S0 := ht2not
    t2_involution := ht2Inv
    S0_eq_zpowers := by rw [htprod]; exact ha.symm
    H := c.H
    H_eq_centralizer := c.H_eq_centralizer
    H_eq_US := by simpa [CentralizerSetup.U, sup_comm] using hHSU
  }
  obtain ⟨I1, hI1, hI1norm, hNX1⟩ := hfc.2 s hs
  obtain ⟨I2, hI2, hI2norm, hNX2⟩ := hfc.2 t2 ⟨ht2S, ht2not⟩
  have hUodd : Nat.Coprime 2 (Nat.card c.U) := by
    change Nat.Coprime 2
      (Nat.card (↑((pPrimeCore 2 c.H).map c.H.subtype)))
    rw [Subgroup.card_map_of_injective c.H.subtype_injective]
    exact pPrimeCore_coprime_card (p := 2) (G := c.H)
  have hUleH : c.U ≤ c.H :=
    Subgroup.map_subtype_le (H := c.H) (pPrimeCore 2 c.H)
  have hI1leU : I1 ≤ c.U := by
    intro x hx
    have hx' : x ∈ invertedElements c.U s := by
      rw [← hI1]
      exact hx
    exact hx'.1
  have hI2leU : I2 ≤ c.U := by
    intro x hx
    have hx' : x ∈ invertedElements c.U t2 := by
      rw [← hI2]
      exact hx
    exact hx'.1
  have hI1odd : Nat.Coprime 2 (Nat.card I1) :=
    hUodd.coprime_dvd_right (Subgroup.card_dvd_of_le hI1leU)
  have hI2odd : Nat.Coprime 2 (Nat.card I2) :=
    hUodd.coprime_dvd_right (Subgroup.card_dvd_of_le hI2leU)
  have hI1inv : BenderGlauberman.IsInvertedBy s I1 := by
    intro x hx
    have hx' : x ∈ invertedElements c.U s := by
      rw [← hI1]
      exact hx
    exact hx'.2
  have hI2inv : BenderGlauberman.IsInvertedBy t2 I2 := by
    intro x hx
    have hx' : x ∈ invertedElements c.U t2 := by
      rw [← hI2]
      exact hx
    exact hx'.2
  let : BenderGlauberman.Hyp11KData bg := {
    K1 := I1
    K2 := I2
    K1_le_H := hI1leU.trans hUleH
    K2_le_H := hI2leU.trans hUleH
    K1_odd := hI1odd
    K2_odd := hI2odd
    K1_inverted := hI1inv
    K2_inverted := hI2inv
    K1_maximal := by
      intro X hXH hXodd hXinv x hx
      have hXU : X ≤ c.U :=
        odd_order_subgroup_le_U_of_H_eq_SU hmin c hXH hXodd
      have hx' : x ∈ invertedElements c.U s := ⟨hXU hx, hXinv x hx⟩
      rw [← hI1] at hx'
      exact hx'
    K2_maximal := by
      intro X hXH hXodd hXinv x hx
      have hXU : X ≤ c.U :=
        odd_order_subgroup_le_U_of_H_eq_SU hmin c hXH hXodd
      have hx' : x ∈ invertedElements c.U t2 := ⟨hXU hx, hXinv x hx⟩
      rw [← hI2] at hx'
      exact hx'
  }
  have haCentU : a ∈ Subgroup.centralizer (c.U : Set G) := hfc.1 haS0
  have hact : ∀ x : G, x ∈ c.U →
      t2 * x * t2⁻¹ = s * x * s⁻¹ := by
    intro x hxU
    have hcomm : x * a = a * x :=
      (Subgroup.mem_centralizer_iff.mp haCentU) x hxU
    have hafix : a * x * a⁻¹ = x := by
      rw [← hcomm]
      group
    calc
      t2 * x * t2⁻¹ = s * (a * x * a⁻¹) * s⁻¹ := by simp [t2]; group
      _ = s * x * s⁻¹ := by rw [hafix]
  have hI12 : I1 = I2 := by
    ext x
    change x ∈ (I1 : Set G) ↔ x ∈ (I2 : Set G)
    rw [hI1, hI2]
    constructor
    · rintro ⟨hxU, hxinv⟩
      exact ⟨hxU, by rw [hact x hxU]; exact hxinv⟩
    · rintro ⟨hxU, hxinv⟩
      exact ⟨hxU, by rw [hact x hxU] at hxinv; exact hxinv⟩
  have mem_centralizerIn_fixed (X : Subgroup G) (r x : G) :
      x ∈ centralizerIn X r ↔ x ∈ X ∧ r * x * r⁻¹ = x := by
    constructor
    · intro hx
      refine ⟨hx.1, ?_⟩
      have hcomm : r * x = x * r :=
        (Subgroup.mem_centralizer_iff.mp hx.2) r (by simp)
      rw [hcomm]
      group
    · rintro ⟨hxX, hxfix⟩
      refine ⟨hxX, ?_⟩
      change x ∈ Subgroup.centralizer ({r} : Set G)
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      have hzr : z = r := by simpa using hz
      rw [hzr]
      exact mul_inv_eq_iff_eq_mul.mp (by simpa [mul_assoc] using hxfix)
  have hB12 : bg.B1 = bg.B2 := by
    ext x
    change x ∈ centralizerIn c.U s ↔ x ∈ centralizerIn c.U t2
    rw [mem_centralizerIn_fixed, mem_centralizerIn_fixed]
    constructor
    · rintro ⟨hxU, hxfix⟩
      exact ⟨hxU, by rw [hact x hxU]; exact hxfix⟩
    · rintro ⟨hxU, hxfix⟩
      exact ⟨hxU, by rw [hact x hxU] at hxfix; exact hxfix⟩
  have hUdecomp : bg.U = bg.B1 ⊔ I1 := by
    apply le_antisymm
    · intro x hxU
      rcases fact_1_5_ii_decomposition bg.t1_involution hUodd
          (fun u hu ↦ BenderGlauberman.S_normalizes_U bg bg.t1 bg.t1_mem_S u hu)
          x hxU with ⟨b, hb, i, hi, hxi⟩
      rw [hxi]
      exact (bg.B1 ⊔ I1).mul_mem
        (SetLike.le_def.mp le_sup_left hb)
        (SetLike.le_def.mp le_sup_right (by
          change i ∈ (I1 : Set G)
          rw [hI1]
          exact hi))
    · exact sup_le inf_le_left hI1leU
  have hK : bg.K = I1 := by
    change I1 ⊓ I2 = I1
    rw [← hI12, inf_idem]
  have hB : bg.B = bg.B1 := by
    simp [BenderGlauberman.Hyp11.B, hB12]
  have hA : bg.B1 ⊓ bg.K2 = ⊥ := by
    apply le_bot_iff.mp
    intro x hx
    have hxB : x ∈ bg.B1 := (Subgroup.mem_inf.mp hx).1
    have hxI2 : x ∈ I2 := (Subgroup.mem_inf.mp hx).2
    have hxI1 : x ∈ I1 := by simpa [hI12] using hxI2
    have hxfix : s * x * s⁻¹ = x :=
      (mem_centralizerIn_fixed c.U s x).mp hxB |>.2
    have hxinv : s * x * s⁻¹ = x⁻¹ := hI1inv x hxI1
    have hxeq : x = x⁻¹ := hxfix.symm.trans hxinv
    have hx2 : x ^ 2 = 1 := by
      rw [pow_two]
      calc
        x * x = x⁻¹ * x := congrArg (fun z : G ↦ z * x) hxeq
        _ = 1 := by simp
    have hxsub2 : (⟨x, hxI1⟩ : I1) ^ 2 = 1 := by
      apply Subtype.ext
      exact hx2
    have hxsub1 := eq_one_of_sq_eq_one_of_coprime_two hI1odd hxsub2
    exact congrArg Subtype.val hxsub1
  have hBU : bg.B ⊔ bg.K = bg.U := by
    rw [hB, hK, ← hUdecomp]
  have hI1eqU : I1 = c.U := by
    by_contra hne
    have hTheoremU : bg.U = (bg.B1 ⊓ bg.K2) ⊔ (bg.B ⊔ bg.K) := by
      rw [hA, hBU]
      simp
    have hTheoremInt : (bg.B1 ⊓ bg.K2) ⊓ (bg.B ⊔ bg.K) = ⊥ := by
      rw [hA]
      simp
    have hTheoremComm : ⁅bg.B1 ⊓ bg.K2, bg.B ⊔ bg.K⁆ = ⊥ := by
      rw [hA]
      simp
    have hTheoremCop : Nat.Coprime (Nat.card bg.K) bg.H.index := by
      rw [hK]
      have hS0centI1 : bg.S0 ≤ Subgroup.centralizer (I1 : Set G) := by
        intro s hs x hx
        exact (Subgroup.mem_centralizer_iff.mp (hfc.1 hs)) x (hI1leU hx)
      exact invertedSubgroup_card_coprime_H_index bg hS0centI1 hI1inv
        hI1norm hI1leU hI1odd hNX1
    have hBne : bg.B ≠ ⊥ := by
      intro hBbot
      apply hne
      calc
        I1 = bg.K := hK.symm
        _ = bg.B ⊔ bg.K := by rw [hBbot]; simp
        _ = bg.U := hBU
        _ = c.U := rfl
    have hBleU : bg.B ≤ bg.U := by
      rw [hB]
      exact inf_le_left
    have hBodd : Odd (Nat.card bg.B) :=
      Nat.coprime_two_left.mp
        (hUodd.coprime_dvd_right (Subgroup.card_dvd_of_le hBleU))
    let : Group.IsSolvable bg.B := odd_order_theorem bg.B hBodd
    let : Nontrivial bg.B := (Subgroup.nontrivial_iff_ne_bot bg.B).mpr hBne
    have hB' : ⁅bg.B, bg.B⁆ ≠ bg.B := by
      intro hperfect
      have hlt := Group.IsSolvable.commutator_lt_top_of_nontrivial (G := bg.B)
      apply hlt.ne
      apply (Subgroup.map_subtype_inj (H := bg.B)).mp
      rw [Subgroup.map_subtype_commutator, hperfect]
      simpa [MonoidHom.range_eq_map] using
        (Subgroup.range_subtype (H := bg.B)).symm
    have hFrob : bg.U ≠ bg.B ⊔ bg.K →
        BenderGlauberman.IsFrobeniusGroupWithKernel (bg.B ⊔ bg.K) bg.K := by
      intro hneBU
      exact False.elim (hneBU hBU.symm)
    exact (BenderGlauberman.theorem_C bg hTheoremU hTheoremInt hTheoremComm
      hTheoremCop hB' hFrob) (minimalCounterexample_isSimple hmin)
  calc
    invertedElements c.U s = (I1 : Set G) := hI1.symm
    _ = (c.U : Set G) := congrArg (fun H : Subgroup G ↦ (H : Set G)) hI1eqU

end

end CFSG.GorensteinWalter
