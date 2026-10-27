module

public import CFSG.Monster.B.TwoA.Sp8.Par1
public import CFSG.Monster.B.Short.InvolutionCentralizer
public import CFSG.Monster.B.Cbar.LocalStructure
public import CFSG.Monster.B.Recog.GenericParity
public import Certificates.Certificate3014
public import Certificates.Certificate3017
public import Certificates.Certificate3019
public import Certificates.Certificate3025
public import Certificates.Certificate3026
public import Certificates.Certificate3028
public import Certificates.Certificate3041
public import Certificates.Certificate3042
public import Certificates.Certificate3057
public import Certificates.Certificate3058
public import Certificates.Certificate3060
public import Certificates.Certificate3061
public import Certificates.Certificate3062
public import Certificates.Certificate3175
public import Certificates.Certificate16016
public import Certificates.Certificate16022
public import Certificates.Certificate16951

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Sp8

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice
  CFSG.Monster.Griess CFSG.Monster.Visible CFSG.Monster.Generated CFSG.Monster.B.Short
  CFSG.Monster.B CFSG.Monster.VisQuot CFSG.Monster.ScalarKernel CFSG.Monster.B.Co2
  CFSG.Monster.B.TwoA

local notation "PSU6" => CFSG.ClassicalGroups.UnitaryFlag.unitaryPSU Unitary.hF4 6

theorem isExtraspecialPGroup_of_mulEquiv {p : ℕ} {G H : Type*} [Group G] [Group H] (e : G ≃* H)
    (h : CFSG.IsExtraspecialPGroup p G) : CFSG.IsExtraspecialPGroup p H := by
  obtain ⟨hp, hcomm, hfrat, hcard⟩ := h
  have hc : (Subgroup.center G).map (e : G →* H) = Subgroup.center H := Subgroup.map_center_eq e
  have hcomm' : (commutator G).map (e : G →* H) = commutator H := by
    rw [commutator_def, commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
      MonoidHom.range_eq_top.2 e.surjective]
  have hfrat' : (frattini G).map (e : G →* H) = frattini H := by
    apply le_antisymm
    · rw [Subgroup.map_le_iff_le_comap]
      exact frattini_le_comap_frattini_of_surjective e.surjective
    · intro x hx
      refine ⟨e.symm x, frattini_le_comap_frattini_of_surjective
        (φ := (e.symm : H →* G)) e.symm.surjective hx, ?_⟩
      exact e.apply_symm_apply x
  refine ⟨hp.of_equiv e, ?_, ?_, ?_⟩
  · rw [← hcomm', ← hc, hcomm]
  · rw [← hfrat', ← hc, hfrat]
  · rw [← hc, ← hcard]
    exact (Nat.card_congr (Subgroup.equivMapOfInjective _ _ e.injective).toEquiv).symm

theorem center_eq_bot_of_not_prime {N : Type*} [Group N] [IsSimpleGroup N] [Finite N]
    (h : ¬ (Nat.card N).Prime) : Subgroup.center N = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center N) with hc | hc
  · exact hc
  · exfalso
    apply h
    have hcomm : ∀ a b : N, a * b = b * a := fun a b =>
      ((Subgroup.mem_center_iff.1 (hc ▸ Subgroup.mem_top a)) b).symm
    let _ : CommGroup N := { (inferInstance : Group N) with mul_comm := hcomm }
    exact IsSimpleGroup.prime_card

theorem center_PSU6 : Subgroup.center PSU6 = ⊥ := by
  have := Unitary.isSimpleGroup_unitaryPSU
  have : Finite PSU6 := Nat.finite_of_card_ne_zero (by rw [Unitary.natCard_unitaryPSU]; norm_num)
  exact center_eq_bot_of_not_prime (by rw [Unitary.natCard_unitaryPSU]; norm_num)

theorem mul_self_C2 : ∀ x : Multiplicative (ZMod 2), x * x = 1 := by
  decide

theorem PSU62_sq_of_center {w : Unitary.PSU62} (hw : w ∈ Subgroup.center Unitary.PSU62) :
    w * w = 1 := by
  have hr : (w * w).right = 1 := by
    rw [SemidirectProduct.mul_right]
    exact mul_self_C2 _
  have hww : w * w = SemidirectProduct.inl (w * w).left :=
    SemidirectProduct.ext (by rw [SemidirectProduct.left_inl])
      (by rw [hr, SemidirectProduct.right_inl])
  have hc : w * w ∈ Subgroup.center Unitary.PSU62 := Subgroup.mul_mem _ hw hw
  have hm : (w * w).left ∈ Subgroup.center PSU6 := by
    rw [Subgroup.mem_center_iff]
    intro k
    have h1 := Subgroup.mem_center_iff.1 hc (SemidirectProduct.inl k)
    rw [hww, ← map_mul, ← map_mul] at h1
    exact SemidirectProduct.inl_injective h1
  rw [center_PSU6, Subgroup.mem_bot] at hm
  rw [hww, hm, map_one]

theorem center_Usig :
    Subgroup.center Unitary.Usig = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  rw [Subgroup.mem_bot]
  let Φ : Unitary.Usig ≃* Unitary.PSU62 := Unitary.phiU.trans Unitary.thetaEquiv
  have hΦ : Φ z ∈ Subgroup.center Unitary.PSU62 := by
    rw [← Subgroup.map_center_eq Φ]
    exact ⟨z, hz, rfl⟩
  have hzz : z ^ 2 = 1 := by
    apply Φ.injective
    rw [map_pow, sq, PSU62_sq_of_center hΦ, map_one]
  let _ : MulAction Unitary.Usig (Fin 891) := Unitary.natAction
  have hmod := CFSG.Monster.B.Recog.card_modEq_card_fixedBy (α := Fin 891) hzz
  rw [Nat.card_fin] at hmod
  have hne : (MulAction.fixedBy (Fin 891) z).Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    intro he
    rw [he, Nat.card_of_isEmpty] at hmod
    exact absurd hmod (by decide)
  obtain ⟨j₀, hj₀⟩ := hne
  have hfix : ∀ j : Fin 891, z • j = j := by
    intro j
    obtain ⟨u, hu, h⟩ := Unitary.transitive_n6vec j₀ j
    have hj : (⟨u, hu⟩ : Unitary.Usig)⁻¹ • j₀ = j := by
      apply Unitary.n6vec_injective
      change Unitary.n6vec (Unitary.natIdx ((⟨u, hu⟩ : Unitary.Usig)⁻¹)⁻¹ j₀) = Unitary.n6vec j
      rw [inv_inv, Unitary.n6vec_natIdx]
      exact h
    rw [← hj, ← mul_smul, (Subgroup.mem_center_iff.1 hz _).symm, mul_smul]
    exact congrArg _ hj₀
  apply Unitary.rhoN_injective
  ext j
  rw [map_one, Equiv.Perm.one_apply]
  exact congrArg Fin.val (hfix j)

theorem Ehat_extraspecial : CFSG.IsExtraspecialPGroup 2 Ehat :=
  isExtraspecialPGroup_of_mulEquiv ehatEquiv Ebar_extraspecial.1

theorem center_Ehat :
    Subgroup.center Ehat = Subgroup.zpowers xhatE := by
  have hcard := Ehat_extraspecial.2.2.2
  have hle : Subgroup.zpowers xhatE ≤ Subgroup.center Ehat := by
    rw [Subgroup.zpowers_le, Subgroup.mem_center_iff]
    intro e
    exact Subtype.ext (xhat_comm_of_mem_Jhat (Ehat_le_Jhat e.2))
  exact (Subgroup.eq_of_le_of_card_ge hle
    (by rw [hcard, Nat.card_zpowers, orderOf_xhatE])).symm

theorem cE_mul_self :
    cE * cE = 1 := Subtype.ext cQ_mul_self

theorem orderOf_cE :
    orderOf cE = 2 :=
  orderOf_eq_prime (by rw [sq]; exact cE_mul_self) fun h => cQ_ne_one (congrArg Subtype.val h)

theorem cE_not_mem_center :
    cE ∉ Subgroup.center Ehat := by
  rw [center_Ehat, mem_zpowers_iff_of_orderOf_eq_two orderOf_xhatE]
  rintro (h | h)
  · exact cQ_ne_one (congrArg Subtype.val h)
  · exact cQ_ne_xhat (congrArg Subtype.val h)

theorem invCent_quot_extraspecial :
    CFSG.IsExtraspecialPGroup 2 (Subgroup.centralizer {cE} ⧸ Subgroup.zpowers (rD cE)) :=
  (extraspecial_involution_centralizer_quotient (P := Ehat) (n := 11) (by norm_num)
    Ehat_extraspecial (by rw [natCard_Ehat]) center_Ehat orderOf_cE cE_not_mem_center).2.2.2.2.1

theorem natCard_invCent_quot :
    Nat.card (Subgroup.centralizer {cE} ⧸ Subgroup.zpowers (rD cE)) = 2 ^ (2 * 11 - 1) :=
  (extraspecial_involution_centralizer_quotient (P := Ehat) (n := 11) (by norm_num)
    Ehat_extraspecial (by rw [natCard_Ehat]) center_Ehat orderOf_cE cE_not_mem_center).2.2.2.2.2.1

theorem cQ_mem_N1 : cQ ∈ N1 := ⟨cQ_mem_Ehat, Subgroup.mem_centralizer_singleton_iff.2 rfl⟩

theorem xhat_mem_N1 :
    xhat ∈ N1 := EU_sigLine_le_N1 xhat_mem_EU

@[expose] def cN1 : N1 := ⟨cQ, cQ_mem_N1⟩

theorem cN1_mem_center :
    cN1 ∈ Subgroup.center N1 := by
  rw [center_N1]
  exact cQ_mem_closure

instance zpowers_cN1_normal :
    (Subgroup.zpowers cN1).Normal :=
  ⟨fun n hn g => by
    have hz : n ∈ Subgroup.center N1 := (Subgroup.zpowers_le.2 cN1_mem_center) hn
    rw [Subgroup.mem_center_iff.1 hz g, mul_inv_cancel_right]
    exact hn⟩

theorem map_invCent : (Subgroup.centralizer {cE}).map Ehat.subtype = N1 := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, Subgroup.mem_centralizer_singleton_iff.2
      (congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.1 hy))⟩
  · rintro ⟨hx, hc⟩
    exact ⟨⟨x, hx⟩, Subgroup.mem_centralizer_singleton_iff.2
      (Subtype.ext (Subgroup.mem_centralizer_singleton_iff.1 hc)), rfl⟩

@[expose] def invCentEquiv : Subgroup.centralizer {cE} ≃* N1 :=
  (Subgroup.equivMapOfInjective _ Ehat.subtype Subtype.val_injective).trans
    (MulEquiv.subgroupCongr map_invCent)

theorem invCentEquiv_rD : invCentEquiv (rD cE) = cN1 := Subtype.ext rfl

@[expose] def n1QuotEquiv :
    Subgroup.centralizer {cE} ⧸ Subgroup.zpowers (rD cE) ≃* N1 ⧸ Subgroup.zpowers cN1 :=
  QuotientGroup.congr _ _ invCentEquiv (by
    rw [MonoidHom.map_zpowers]
    exact congrArg Subgroup.zpowers invCentEquiv_rD)

theorem N1_quot_extraspecial :
    CFSG.IsExtraspecialPGroup 2 (N1 ⧸ Subgroup.zpowers cN1) :=
  isExtraspecialPGroup_of_mulEquiv n1QuotEquiv invCent_quot_extraspecial

theorem natCard_N1_quot_c :
    Nat.card (N1 ⧸ Subgroup.zpowers cN1) = 2 ^ 21 := by
  rw [← Nat.card_congr n1QuotEquiv.toEquiv]
  exact natCard_invCent_quot

theorem cQ_mem_P1 : cQ ∈ P1 := N1_le_P1 cQ_mem_N1

theorem xhat_mem_P1 :
    xhat ∈ P1 := N1_le_P1 xhat_mem_N1

@[expose] def cP1 : P1 := ⟨cQ, cQ_mem_P1⟩

@[expose] def xP1 :
    P1 := ⟨xhat, xhat_mem_P1⟩

theorem cP1_mem_center : cP1 ∈ Subgroup.center P1 := by
  rw [Subgroup.mem_center_iff]
  intro g
  apply Subtype.ext
  exact (Subgroup.mem_centralizer_singleton_iff.1 g.2.2)

theorem xP1_mem_center :
    xP1 ∈ Subgroup.center P1 := by
  rw [Subgroup.mem_center_iff]
  intro g
  exact Subtype.ext (xhat_comm_of_mem_Jhat (P1_le_Jhat g.2))

instance zpowers_cP1_normal :
    (Subgroup.zpowers cP1).Normal :=
  ⟨fun n hn g => by
    have hz : n ∈ Subgroup.center P1 := (Subgroup.zpowers_le.2 cP1_mem_center) hn
    rw [Subgroup.mem_center_iff.1 hz g, mul_inv_cancel_right]
    exact hn⟩

theorem orderOf_cP1 :
    orderOf cP1 = 2 :=
  orderOf_eq_prime (by rw [sq]; exact Subtype.ext cQ_mul_self)
    fun h => cQ_ne_one (congrArg Subtype.val h)

theorem mem_zpowers_cP1
    {g : P1} :
    g ∈ Subgroup.zpowers cP1 ↔ (g : Dfull) = 1 ∨ (g : Dfull) = cQ := by
  rw [mem_zpowers_iff_of_orderOf_eq_two orderOf_cP1]
  constructor
  · rintro (h | h)
    · exact Or.inl (congrArg Subtype.val h)
    · exact Or.inr (congrArg Subtype.val h)
  · rintro (h | h)
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr (Subtype.ext h)

theorem zpowers_cP1_le_ker :
    Subgroup.zpowers cP1 ≤ p1Proj.ker := by
  rw [Subgroup.zpowers_le, ker_p1Proj, Subgroup.mem_subgroupOf]
  exact cQ_mem_N1

theorem mem_N1_of_center
    {y : P1}
    (hy : QuotientGroup.mk y ∈ Subgroup.center (P1 ⧸ Subgroup.zpowers cP1)) : (y : Dfull) ∈ N1 := by
  have hc : p1Proj y ∈ Subgroup.center Unitary.Usig := by
    rw [Subgroup.mem_center_iff]
    intro u
    obtain ⟨g, rfl⟩ := p1Proj_surjective u
    have h1 := Subgroup.mem_center_iff.1 hy (QuotientGroup.mk g)
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq] at h1
    have h2 := zpowers_cP1_le_ker h1
    rw [MonoidHom.mem_ker, map_mul, map_inv, map_mul, map_mul, inv_mul_eq_one] at h2
    exact h2
  rw [center_Usig, Subgroup.mem_bot, ← MonoidHom.mem_ker, ker_p1Proj] at hc
  exact hc

theorem mem_closure_of_center
    {y : P1}
    (hy : QuotientGroup.mk y ∈ Subgroup.center (P1 ⧸ Subgroup.zpowers cP1)) :
    (y : Dfull) ∈ Subgroup.closure {xhat, cQ} := by
  have hyN := mem_N1_of_center hy
  rw [← EU_sigLine, ← mem_center_N1 hyN]
  intro h hh
  have hc := Ehat_commutator (Ehat.inv_mem (N1_le_Ehat hyN)) (Ehat.inv_mem (N1_le_Ehat hh))
  rcases zmod2_cases (bV (psiW ⟨(y : Dfull)⁻¹, Ehat.inv_mem (N1_le_Ehat hyN)⟩)
    (psiW ⟨h⁻¹, Ehat.inv_mem (N1_le_Ehat hh)⟩)) with hb | hb
  · rw [hb, ZMod.val_zero, pow_zero] at hc
    calc (y : Dfull) * h = (h * y) * ((y : Dfull)⁻¹ * h⁻¹ * (y : Dfull)⁻¹⁻¹ * h⁻¹⁻¹) := by group
      _ = h * y := by rw [hc, mul_one]
  · exfalso
    have h1 := Subgroup.mem_center_iff.1 hy (QuotientGroup.mk ⟨h, N1_le_P1 hh⟩)
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, mem_zpowers_cP1] at h1
    have e : (((⟨h, N1_le_P1 hh⟩ * y)⁻¹ * (y * ⟨h, N1_le_P1 hh⟩) : P1) : Dfull) =
        (y : Dfull)⁻¹ * h⁻¹ * (y : Dfull)⁻¹⁻¹ * h⁻¹⁻¹ := by
      push_cast
      group
    rw [e, hc, hb, show (1 : ZMod 2).val = 1 from rfl, pow_one] at h1
    rcases h1 with h1 | h1
    · exact xhat_ne_one h1
    · exact cQ_ne_xhat h1.symm

theorem center_P1_quot :
    Subgroup.center (P1 ⧸ Subgroup.zpowers cP1) =
    Subgroup.zpowers (QuotientGroup.mk xP1) := by
  apply le_antisymm
  · intro q hq
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
    have hy := mem_closure_of_center hq
    rw [← range_kleinHom] at hy
    obtain ⟨v, hv⟩ := hy
    have e : y = xP1 ^ (Multiplicative.toAdd v).1.val * cP1 ^ (Multiplicative.toAdd v).2.val :=
      Subtype.ext (by rw [← hv]; rfl)
    rw [e, QuotientGroup.mk_mul, QuotientGroup.mk_pow, QuotientGroup.mk_pow,
      (QuotientGroup.eq_one_iff _).2 (Subgroup.mem_zpowers cP1), one_pow, mul_one]
    exact Subgroup.npow_mem_zpowers _ _
  · rw [Subgroup.zpowers_le, Subgroup.mem_center_iff]
    intro q
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, Subgroup.mem_center_iff.1 xP1_mem_center g]

theorem orderOf_mk_xP1 :

    orderOf (QuotientGroup.mk xP1 : P1 ⧸ Subgroup.zpowers cP1) = 2 := by
  apply orderOf_eq_prime
  · rw [← QuotientGroup.mk_pow, sq, QuotientGroup.eq_one_iff,
      show xP1 * xP1 = 1 from Subtype.ext xhat_mul_self]
    exact Subgroup.one_mem _
  · intro h
    rw [QuotientGroup.eq_one_iff, mem_zpowers_cP1] at h
    rcases h with h | h
    · exact xhat_ne_one h
    · exact cQ_ne_xhat h.symm

theorem natCard_center_P1_quot :
    Nat.card (Subgroup.center (P1 ⧸ Subgroup.zpowers cP1)) = 2 := by
  rw [center_P1_quot, Nat.card_zpowers, orderOf_mk_xP1]

theorem native_F4_point_stabilizer_central_involution :
    Subgroup.center Unitary.Usig = ⊥ ∧
    CFSG.IsExtraspecialPGroup 2 (N1 ⧸ Subgroup.zpowers cN1) ∧
    Nat.card (N1 ⧸ Subgroup.zpowers cN1) = 2 ^ 21 ∧
    Subgroup.center (P1 ⧸ Subgroup.zpowers cP1) = Subgroup.zpowers (QuotientGroup.mk xP1) ∧
    Nat.card (Subgroup.center (P1 ⧸ Subgroup.zpowers cP1)) = 2 :=
  ⟨center_Usig, N1_quot_extraspecial, natCard_N1_quot_c, center_P1_quot, natCard_center_P1_quot⟩

end CFSG.Monster.B.TwoA.Sp8
