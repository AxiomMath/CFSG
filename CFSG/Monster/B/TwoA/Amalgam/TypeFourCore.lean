module

public import CFSG.Monster.B.TwoA.Amalgam.OrderFourCore
public import CFSG.Monster.B.TwoA.Sp8.Par1Center
public import Certificates.Certificate3014
public import Certificates.Certificate3017
public import Certificates.Certificate3019
public import Certificates.Certificate3026
public import Certificates.Certificate3028
public import Certificates.Certificate3057
public import Certificates.Certificate3058
public import Certificates.Certificate3060
public import Certificates.Certificate16022
public import Certificates.Certificate3025
public import Certificates.Certificate3041
public import Certificates.Certificate3042
public import Certificates.Certificate3054
public import Certificates.Certificate3055
public import Certificates.Certificate3061
public import Certificates.Certificate3072
public import Certificates.Certificate3073
public import Certificates.Certificate3074
public import Certificates.Certificate3076
public import Certificates.Certificate3078
public import Certificates.Certificate3079
public import Certificates.Certificate16001
public import Certificates.Certificate16016
public import Certificates.Certificate16021
public import Certificates.Certificate16033
public import Certificates.Certificate16951
public import CFSG.Monster.B.Classical.PlaneAut
public import CFSG.Monster.B.TwoA.Base.GeomNative
public import CFSG.Monster.B.TwoA.Par3.MainBase
public import CFSG.Monster.B.TwoA.Sp8.GenActionBase
public import CFSG.Monster.B.TwoA.Sp8.NormalizerBase
public import CFSG.Monster.B.TwoA.Sp8.Orth8Base
public import CFSG.Monster.B.TwoA.Sp8.SubgeomBuildingBase
public import CFSG.Monster.B.TwoA.Sp8.SubgeomFive
public import CFSG.Monster.B.TwoA.Sp8.SubgeomFiveBase
public import CFSG.Monster.B.TwoA.Sp8.SubgeomIsoBase
public import CFSG.Monster.B.TwoA.Sp8.SubgeomStdBase
public import CFSG.Monster.B.TwoA.Unitary.Twenty

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Amalgam

open CFSG.Monster CFSG.Monster.B CFSG.Monster.B.Short CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Sp8
open CFSG.Monster.B.Co2 (v0 wAct_mul wAct_one wAct_inv_apply wAct_apply_inv)

@[expose] def cNE (k : Jhat) : Subgroup Dfull :=
  Ehat ⊓ Subgroup.centralizer {cQ} ⊓ Subgroup.centralizer {(labE k : Dfull)}

@[expose] def Q4 (k : Jhat) : Subgroup Dfull := P1 ⊓ Subgroup.centralizer {(labE k : Dfull)}

@[expose] def p1cProj :
    P1 ⧸ Subgroup.zpowers cP1 →* Unitary.Usig :=
  QuotientGroup.lift _ p1Proj zpowers_cP1_le_ker

theorem p1cProj_mk
    (g : P1) : p1cProj (QuotientGroup.mk g) = p1Proj g :=
  QuotientGroup.lift_mk _ _ g

variable {k : Jhat}

theorem Q4_le_P1 : Q4 k ≤ P1 := inf_le_left

theorem Q4_le_Jhat : Q4 k ≤ Jhat := Q4_le_P1.trans P1_le_Jhat

theorem cNE_le_N1 : cNE k ≤ N1 := inf_le_left

theorem cNE_le_Q4 : cNE k ≤ Q4 k := fun _ hx => ⟨N1_le_P1 hx.1, hx.2⟩

theorem Q4_inf_Ehat : Q4 k ⊓ Ehat = cNE k := by
  ext x
  simp only [Q4, cNE, P1, Subgroup.mem_inf]
  exact ⟨fun ⟨⟨⟨_, hc⟩, hr⟩, he⟩ => ⟨⟨he, hc⟩, hr⟩,
    fun ⟨⟨he, hc⟩, hr⟩ => ⟨⟨⟨Ehat_le_Jhat he, hc⟩, hr⟩, he⟩⟩

theorem mem_centralizer_of_conj {g r : Dfull} (h : g⁻¹ * r * g = r) :
    g ∈ Subgroup.centralizer {r} :=
  Subgroup.mem_centralizer_singleton_iff.2 (by
    calc g * r = g * (g⁻¹ * r * g) := by rw [h]
      _ = r * g := by group)

theorem conj_of_mem_centralizer {g r : Dfull} (h : g ∈ Subgroup.centralizer {r}) :
    g⁻¹ * r * g = r := by
  rw [mul_assoc, ← Subgroup.mem_centralizer_singleton_iff.1 h, inv_mul_cancel_left]

theorem conj_labE_cases {g : Jhat}
    (hg : wAct v0 (jhatToKv0 g) (psiW (labE k)) = psiW (labE k)) :
    (g : Dfull)⁻¹ * labE k * g = labE k ∨ (g : Dfull)⁻¹ * labE k * g = labE k * xhat :=
  fiber_cases ((psiW_conj g.2 (labE k).2).trans hg)

@[expose] def cJ : Jhat := ⟨cQ, Ehat_le_Jhat cQ_mem_Ehat⟩

theorem jhatToKv0_cJ : jhatToKv0 cJ = 1 :=
  jhatToKv0_eq_one_of_mem_Ehat cJ.2 cQ_mem_Ehat

section Pair

variable (hk0 : cvOf (jhatS k) ≠ cv0) (hk : ¬ cgraph.Adj cv0 (cvOf (jhatS k)))

include hk0 hk in
theorem piPt_mem_tauOrb :
    (piPt k : Wv v0) ∈ Unitary.usigOrbit Unitary.tauW := by
  rcases (Set.ext_iff.1 Unitary.OmegaW_eq_union _).1 (piPt k).2 with (h1 | h1) | h1
  · exact absurd ((adj_cv0_iff_piPt hk0).2 (Or.inl h1)) hk
  · exact absurd ((adj_cv0_iff_piPt hk0).2 (Or.inr h1)) hk
  · exact h1

include hk0 hk in
theorem cQ_mul_labE :
    cQ * (labE k : Dfull) = labE k * cQ * xhat := by
  have h := Ehat_comm cE (labE k)
  rw [psiW_cE, ← piPt_eq_psiW, bV_sigmaW_of_mem_tauOrb (piPt_mem_tauOrb hk0 hk), ZMod.val_one,
    pow_one] at h
  exact h

include hk0 hk in
theorem cQ_not_mem_centralizer :
    cQ ∉ Subgroup.centralizer {(labE k : Dfull)} := by
  intro h
  have h1 := Subgroup.mem_centralizer_singleton_iff.1 h
  rw [cQ_mul_labE hk0 hk] at h1
  exact xhat_ne_one (mul_eq_left.1 h1)

include hk0 hk in
theorem conj_mul_cQ
    {g : Dfull} (hg : g⁻¹ * labE k * g = labE k * xhat) :
    (g * cQ)⁻¹ * labE k * (g * cQ) = labE k := by
  have h1 := cQ_mul_labE hk0 hk
  have hxc : xhat * cQ = cQ * xhat := xhat_comm_cQ
  have hcinv : cQ⁻¹ = cQ := inv_eq_of_mul_eq_one_right cQ_mul_self
  calc (g * cQ)⁻¹ * labE k * (g * cQ) = cQ⁻¹ * (g⁻¹ * labE k * g) * cQ := by group
    _ = cQ * (labE k * xhat) * cQ := by rw [hg, hcinv]
    _ = (cQ * labE k) * (xhat * cQ) := by group
    _ = (labE k * cQ * xhat) * (cQ * xhat) := by rw [h1, hxc]
    _ = labE k * (cQ * (xhat * cQ) * xhat) := by group
    _ = labE k * (cQ * (cQ * xhat) * xhat) := by rw [hxc]
    _ = labE k * ((cQ * cQ) * (xhat * xhat)) := by group
    _ = labE k := by rw [cQ_mul_self, xhat_mul_self, mul_one, mul_one]

include hk0 hk in
theorem map_Q4 :
    ((Q4 k).subgroupOf Jhat).map jhatToKv0 = Unitary.Usig ⊓ wStab (psiW (labE k)) := by
  ext u
  constructor
  · rintro ⟨g, hg, rfl⟩
    have hg' : (g : Dfull) ∈ Q4 k := hg
    refine ⟨jhatToKv0_mem_Usig hg'.1, ?_⟩
    show wAct v0 (jhatToKv0 g) (psiW (labE k)) = psiW (labE k)
    calc wAct v0 (jhatToKv0 g) (psiW (labE k))
        = psiW ⟨(g : Dfull)⁻¹ * labE k * g, conj_mem_Ehat g.2 (labE k).2⟩ :=
          (psiW_conj g.2 (labE k).2).symm
      _ = psiW (labE k) := congrArg psiW (Subtype.ext (conj_of_mem_centralizer hg'.2))
  · rintro ⟨hu, hτ⟩
    obtain ⟨p, hp, rfl⟩ := exists_P1_of_mem_Usig hu
    rcases conj_labE_cases hτ with h | h
    · exact ⟨p, ⟨hp, mem_centralizer_of_conj h⟩, rfl⟩
    · refine ⟨p * cJ, ⟨P1.mul_mem hp cQ_mem_P1, mem_centralizer_of_conj ?_⟩, ?_⟩
      · exact conj_mul_cQ hk0 hk h
      · rw [map_mul, jhatToKv0_cJ, mul_one]

theorem orderOf_cN1 : orderOf cN1 = 2 :=
  orderOf_eq_prime (by rw [sq]; exact Subtype.ext cQ_mul_self)
    fun h => cQ_ne_one (congrArg Subtype.val h)

@[expose] def cNEhom (k : Jhat) : cNE k →* N1 ⧸ Subgroup.zpowers cN1 :=
  (QuotientGroup.mk' _).comp (Subgroup.inclusion cNE_le_N1)

theorem cNEhom_apply (x : cNE k) :
    cNEhom k x = QuotientGroup.mk ⟨x, cNE_le_N1 x.2⟩ := rfl

include hk0 hk in
theorem mem_cNE_or_mul_cQ
    {n : Dfull} (hn : n ∈ N1) : n ∈ cNE k ∨ n * cQ ∈ cNE k := by
  have hnJ : n ∈ Jhat := P1_le_Jhat (N1_le_P1 hn)
  have hπ : jhatToKv0 ⟨n, hnJ⟩ = 1 := jhatToKv0_eq_one_of_mem_Ehat hnJ hn.1
  have hτ : wAct v0 (jhatToKv0 ⟨n, hnJ⟩) (psiW (labE k)) = psiW (labE k) := by
    rw [hπ, wAct_one, Module.End.one_apply]
  rcases conj_labE_cases (g := ⟨n, hnJ⟩) hτ with h | h
  · exact Or.inl ⟨hn, mem_centralizer_of_conj h⟩
  · exact Or.inr ⟨N1.mul_mem hn cQ_mem_N1, mem_centralizer_of_conj (conj_mul_cQ hk0 hk h)⟩

include hk0 hk in
theorem cNEhom_bijective :
    Function.Bijective (cNEhom k) := by
  constructor
  · intro x y h
    rw [cNEhom_apply, cNEhom_apply, QuotientGroup.eq,
      mem_zpowers_iff_of_orderOf_eq_two orderOf_cN1] at h
    rcases h with h | h
    · exact Subtype.ext (by
        have h' := congrArg Subtype.val h
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, OneMemClass.coe_one] at h'
        exact inv_mul_eq_one.1 h')
    · exfalso
      have h' : ((x : Dfull))⁻¹ * y = cQ := by
        have := congrArg Subtype.val h
        simp only [Subgroup.coe_mul, Subgroup.coe_inv] at this
        exact this
      apply cQ_not_mem_centralizer hk0 hk
      rw [← h']
      exact ((cNE k).mul_mem ((cNE k).inv_mem x.2) y.2).2
  · intro q
    obtain ⟨n, rfl⟩ := QuotientGroup.mk_surjective q
    rcases mem_cNE_or_mul_cQ hk0 hk n.2 with h | h
    · exact ⟨⟨n, h⟩, rfl⟩
    · refine ⟨⟨_, h⟩, ?_⟩
      rw [cNEhom_apply, QuotientGroup.eq, mem_zpowers_iff_of_orderOf_eq_two orderOf_cN1]
      right
      apply Subtype.ext
      show ((n : Dfull) * cQ)⁻¹ * n = cQ
      rw [mul_inv_rev, inv_mul_cancel_right, inv_eq_of_mul_eq_one_right cQ_mul_self]

@[expose] def cNEEquiv :
    cNE k ≃* N1 ⧸ Subgroup.zpowers cN1 :=
  MulEquiv.ofBijective (cNEhom k) (cNEhom_bijective hk0 hk)

theorem cNEEquiv_apply
    (x : cNE k) :
    cNEEquiv hk0 hk x = QuotientGroup.mk ⟨x, cNE_le_N1 x.2⟩ := rfl

include hk0 hk in
theorem cNE_extraspecial :
    CFSG.IsExtraspecialPGroup 2 (cNE k) :=
  isExtraspecialPGroup_of_mulEquiv (cNEEquiv hk0 hk).symm N1_quot_extraspecial

include hk0 hk in
theorem natCard_cNE :
    Nat.card (cNE k) = 2 ^ 21 :=
  (Nat.card_congr (cNEEquiv hk0 hk).toEquiv).trans natCard_N1_quot_c

theorem mk_P1_eq_iff {x y : P1} :
    (QuotientGroup.mk' (Subgroup.zpowers cP1) x = QuotientGroup.mk' _ y) ↔
      (x : Dfull) = y ∨ ((x : Dfull))⁻¹ * y = cQ := by
  rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq, mem_zpowers_cP1]
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  exact or_congr_left ⟨fun h => inv_mul_eq_one.1 h, fun h => inv_mul_eq_one.2 h⟩

theorem mk_mul_cP1 (x : P1) : QuotientGroup.mk' (Subgroup.zpowers cP1) (x * cP1) =
    QuotientGroup.mk' _ x := by
  rw [mk_P1_eq_iff]
  right
  show ((x : Dfull) * cQ)⁻¹ * x = cQ
  rw [mul_inv_rev, inv_mul_cancel_right, inv_eq_of_mul_eq_one_right cQ_mul_self]

include hk0 hk in
theorem injOn_mk_of_le
    {H : Subgroup Dfull} (hH : H ≤ Q4 k) :
    Set.InjOn (QuotientGroup.mk' (Subgroup.zpowers cP1)) (H.subgroupOf P1) := by
  intro x hx y hy h
  rcases mk_P1_eq_iff.1 h with h | h
  · exact Subtype.ext h
  · exfalso
    apply cQ_not_mem_centralizer hk0 hk
    rw [← h]
    exact (hH (H.mul_mem (H.inv_mem hx) hy)).2

include hk0 hk in
theorem map_cNE_quot :
    ((cNE k).subgroupOf P1).map (QuotientGroup.mk' (Subgroup.zpowers cP1)) =
    (N1.subgroupOf P1).map (QuotientGroup.mk' (Subgroup.zpowers cP1)) := by
  apply le_antisymm
  · exact Subgroup.map_mono fun x hx => cNE_le_N1 hx
  · rintro _ ⟨x, hx, rfl⟩
    rcases mem_cNE_or_mul_cQ hk0 hk hx with h | h
    · exact ⟨x, h, rfl⟩
    · exact ⟨x * cP1, h, mk_mul_cP1 x⟩

include hk0 hk in
theorem map_Q4_quot :
    ((Q4 k).subgroupOf P1).map (QuotientGroup.mk' (Subgroup.zpowers cP1)) =
    ((wStab (psiW (labE k))).subgroupOf Unitary.Usig).comap p1cProj := by
  ext q
  constructor
  · rintro ⟨g, hg, rfl⟩
    rw [Subgroup.mem_comap, QuotientGroup.mk'_apply, p1cProj_mk, Subgroup.mem_subgroupOf,
      coe_p1Proj]
    have hm := (SetLike.ext_iff.1 (map_Q4 hk0 hk) (jhatToKv0 ⟨g, P1_le_Jhat g.2⟩)).1
      ⟨⟨g, P1_le_Jhat g.2⟩, hg, rfl⟩
    exact hm.2
  · intro hq
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
    rw [Subgroup.mem_comap, p1cProj_mk, Subgroup.mem_subgroupOf, coe_p1Proj] at hq
    have hτ : wAct v0 (jhatToKv0 ⟨g, P1_le_Jhat g.2⟩) (psiW (labE k)) = psiW (labE k) := hq
    rcases conj_labE_cases hτ with h | h
    · exact ⟨g, ⟨g.2, mem_centralizer_of_conj h⟩, rfl⟩
    · exact ⟨g * cP1, ⟨P1.mul_mem g.2 cQ_mem_P1, mem_centralizer_of_conj
        (conj_mul_cQ hk0 hk h)⟩, mk_mul_cP1 g⟩

section Orbit

attribute [local instance] wLeftAction

theorem natCard_stab_of_mem_tauOrb
    {x : Wv v0} (hx : x ∈ Unitary.usigOrbit Unitary.tauW) :
    Nat.card ((wStab x).subgroupOf Unitary.Usig) = 13063680 := by
  have hst : MulAction.stabilizer Unitary.Usig x = (wStab x).subgroupOf Unitary.Usig := by
    ext u
    rw [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf, mem_wStab]
    change wAct v0 (u : Kstab v0)⁻¹ x = x ↔ _
    constructor
    · intro h
      conv_lhs => rw [← h]
      exact wAct_apply_inv _ _
    · intro h
      conv_lhs => rw [← h]
      exact wAct_inv_apply _ _
  have h1 := Subgroup.card_mul_index (MulAction.stabilizer Unitary.Usig x)
  rw [MulAction.index_stabilizer, ← Unitary.usigOrbit_eq_orbit, Unitary.usigOrbit_eq_of_mem hx,
    Unitary.ncard_usigOrbit_tau, Unitary.natCard_Usig, hst] at h1
  omega

end Orbit

@[expose] def q4Proj (k : Jhat) : Q4 k →* Kstab v0 :=
  jhatToKv0.comp (Subgroup.inclusion Q4_le_Jhat)

include hk0 hk in
theorem natCard_Q4 :
    Nat.card (Q4 k) = 2 ^ 21 * 13063680 := by
  have hker : (q4Proj k).ker = (cNE k).subgroupOf (Q4 k) := by
    ext g
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, ← Q4_inf_Ehat, q4Proj,
      MonoidHom.comp_apply, ← MonoidHom.mem_ker, ker_jhatToKv0, Subgroup.mem_subgroupOf]
    exact ⟨fun h => ⟨g.2, h⟩, fun h => h.2⟩
  have hrange : (q4Proj k).range = Unitary.Usig ⊓ wStab (psiW (labE k)) := by
    rw [← map_Q4 hk0 hk]
    ext u
    constructor
    · rintro ⟨g, rfl⟩
      exact ⟨Subgroup.inclusion Q4_le_Jhat g, g.2, rfl⟩
    · rintro ⟨g, hg, rfl⟩
      exact ⟨⟨g, hg⟩, rfl⟩
  have hτ : psiW (labE k) ∈ Unitary.usigOrbit Unitary.tauW := by
    rw [← piPt_eq_psiW]
    exact piPt_mem_tauOrb hk0 hk
  have hcard : Nat.card ↥(Unitary.Usig ⊓ wStab (psiW (labE k))) = 13063680 := by
    rw [inf_comm, ← Subgroup.subgroupOf_map_subtype, ← natCard_stab_of_mem_tauOrb hτ]
    exact (Nat.card_congr (Subgroup.equivMapOfInjective _ _
      (Subgroup.subtype_injective Unitary.Usig)).toEquiv).symm
  have hkc : Nat.card ↥((cNE k).subgroupOf (Q4 k)) = 2 ^ 21 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe cNE_le_Q4).toEquiv).trans (natCard_cNE hk0 hk)
  have h1 := Subgroup.card_mul_index (q4Proj k).ker
  rw [Subgroup.index_ker, hrange, hcard, hker, hkc] at h1
  exact h1.symm

include hk0 hk in
theorem exists_P1_tauW :
    ∃ p : Jhat, (p : Dfull) ∈ P1 ∧ psiW (labE (k * p)) = Unitary.tauW := by
  obtain ⟨u, hu, hτ⟩ := piPt_mem_tauOrb hk0 hk
  obtain ⟨p, hp, hpu⟩ := exists_P1_of_mem_Usig (Unitary.Usig.inv_mem hu)
  refine ⟨p, hp, ?_⟩
  rw [← piPt_eq_psiW, coe_piPt_mul, hpu, ← hτ, wAct_inv_apply]

end Pair

end CFSG.Monster.B.TwoA.Amalgam
