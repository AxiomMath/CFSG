module

public import CFSG.Monster.Existence.ShortCentralizer
public import CFSG.Monster.B.TwoA.Census.CentralSqrt
public import CFSG.Monster.Existence.TwoB

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.Existence

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice
  CFSG.Monster.Griess CFSG.Monster.Visible CFSG.Monster.Generated CFSG.Monster.B.Short
  CFSG.Monster.B CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Census

theorem tauhatA_not_commute_xhatA : tauhatA * xhatA ≠ xhatA * tauhatA := by
  intro h
  have h1 : tauhatA * xhatA * tauhatA⁻¹ = xhatA := by rw [h, mul_inv_cancel_right]
  rw [tauhatA, ← iotaA_xbar, ← map_inv, ← map_mul, ← map_mul, taubar_conj_xbar] at h1
  exact xbar_ne_ybar (iotaA_injective h1).symm

theorem commutator_DA :
    commutator DA = ⊤ := by
  have : IsSimpleGroup DA := isSimpleGroup_DA
  have hn : (commutator DA).Normal := inferInstance
  rcases hn.eq_bot_or_eq_top with h | h
  · exfalso
    have hc := (commutator_eq_bot_iff_center_eq_top DA).1 h
    apply tauhatA_not_commute_xhatA
    have hx : xhatA ∈ Subgroup.center DA := hc ▸ Subgroup.mem_top _
    exact Subgroup.mem_center_iff.1 hx tauhatA
  · exact h

theorem center_DA :
    Subgroup.center DA = ⊥ := by
  have : IsSimpleGroup DA := isSimpleGroup_DA
  rcases (Subgroup.center DA).normal_of_characteristic.eq_bot_or_eq_top with h | h
  · exact h
  · exfalso
    apply tauhatA_not_commute_xhatA
    have hx : xhatA ∈ Subgroup.center DA := h ▸ Subgroup.mem_top _
    exact (Subgroup.mem_center_iff.1 hx tauhatA)

@[expose] noncomputable def cA :
    CfullA := inclGenA ⟨cSqrt, Jstar_le_Cgen cSqrt_mem_Jstar⟩

theorem cA_sq :
    cA * cA = tStarA := Subtype.ext cSqrt_sq

theorem commutator_CfullA :
    commutator CfullA = ⊤ := by
  have hmap : (commutator CfullA).map piA = ⊤ := by
    rw [commutator_def, Subgroup.map_commutator, Subgroup.map_top_of_surjective _ piA_surjective,
      ← commutator_def, commutator_DA]
  set N := commutator CfullA
  have hsup : N ⊔ ZstarA = ⊤ := by
    rw [← ker_piA, ← Subgroup.comap_map_eq, hmap, Subgroup.comap_top]
  have hdecomp : ∀ g : CfullA, g ∈ N ∨ g * tStarA ∈ N := by
    intro g
    have hg : g ∈ N ⊔ ZstarA := hsup ▸ Subgroup.mem_top g
    rw [Subgroup.mem_sup_of_normal_right] at hg
    obtain ⟨n, hn, z, hz, rfl⟩ := hg
    rcases (Short.mem_zpowers_iff_of_orderOf_eq_two orderOf_tStarA).1 hz with rfl | rfl
    · left; rwa [mul_one]
    · right
      rw [mul_assoc, ← sq, ← orderOf_tStarA, pow_orderOf_eq_one, mul_one]
      exact hn
  have htN : tStarA ∈ N := by
    have hcomm : cA * tStarA = tStarA * cA := Subgroup.mem_center_iff.1 tStarA_mem_center cA
    rcases hdecomp cA with h | h
    · rw [← cA_sq]; exact N.mul_mem h h
    · have : (cA * tStarA) * (cA * tStarA) = tStarA := by
        rw [show (cA * tStarA) * (cA * tStarA) = cA * cA * (tStarA * tStarA) by
          rw [mul_assoc, ← mul_assoc tStarA, ← hcomm, mul_assoc, mul_assoc], cA_sq,
          ← mul_assoc, ← sq, ← pow_succ, show 2 + 1 = 3 from rfl]
        rw [show (3 : ℕ) = 2 + 1 from rfl, pow_succ, ← orderOf_tStarA, pow_orderOf_eq_one,
          one_mul]
      rw [← this]; exact N.mul_mem h h
  rw [eq_top_iff, ← hsup]
  exact sup_le le_rfl (Subgroup.zpowers_le.2 htN)

instance isPerfect_CfullA :
    Group.IsPerfect CfullA := Group.isPerfect_def.2 commutator_CfullA

theorem center_CfullA :
    Subgroup.center CfullA = ZstarA := by
  apply le_antisymm
  · intro g hg
    rw [← ker_piA, MonoidHom.mem_ker]
    have h : piA g ∈ Subgroup.center DA :=
      Subgroup.map_center_le_center piA_surjective ⟨g, hg, rfl⟩
    rw [center_DA, Subgroup.mem_bot] at h
    exact h
  · exact (Subgroup.zpowers_le).2 tStarA_mem_center

@[expose] noncomputable def tGriess : MGriess := ⟨tStar, Gmat_le_AutO (Cgen_le tStar_mem_Cgen).1⟩

theorem map_cent_tGriess : (cent tGriess).map AutO.subtype = CfullA := by
  ext g
  constructor
  · rintro ⟨h, hh, rfl⟩
    refine ⟨h.2, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
    exact congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.1 hh)
  · rintro ⟨hg, hc⟩
    refine ⟨⟨g, hg⟩, ?_, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
    exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.1 hc)

noncomputable def centTEquiv : cent tGriess ≃* CfullA :=
  ((cent tGriess).equivMapOfInjective AutO.subtype AutO.subtype_injective).trans
    (MulEquiv.subgroupCongr map_cent_tGriess)

theorem centTEquiv_self :
    centTEquiv ⟨tGriess, self_mem_cent tGriess⟩ = tStarA := by rfl

theorem isPerfect_cent_tGriess :
    Group.IsPerfect (cent tGriess) :=
  Group.IsPerfect.ofSurjective (f := centTEquiv.symm.toMonoidHom) centTEquiv.symm.surjective

theorem center_cent_tGriess :
    (Subgroup.center (cent tGriess)).map (cent tGriess).subtype = Subgroup.zpowers tGriess := by
  have h1 : Subgroup.center (cent tGriess) = Subgroup.zpowers ⟨tGriess, self_mem_cent tGriess⟩ := by
    rw [← center_map_mulEquiv centTEquiv.symm, center_CfullA, ZstarA, MonoidHom.map_zpowers,
      ← centTEquiv_self]
    simp
  rw [h1, MonoidHom.map_zpowers]
  rfl

noncomputable def quotCentTEquiv :
    cent tGriess ⧸ Subgroup.center (cent tGriess) ≃* DA :=
  QuotientGroup.congr _ _ centTEquiv (by rw [← center_CfullA]; exact center_map_mulEquiv centTEquiv)

theorem isTwoACentralizer_tGriess_of_equiv
    (e : DA ≃* Blueprint.NativeSporadic.B) :
    IsTwoACentralizer tGriess :=
  ⟨isPerfect_cent_tGriess, center_cent_tGriess, ⟨quotCentTEquiv.trans e⟩⟩

variable {G : Type} [Group G]

theorem IsTwoACentralizer.of_isConj {a b : G} (h : IsTwoACentralizer a) (hab : IsConj a b) :
    IsTwoACentralizer b := by
  obtain ⟨c, rfl⟩ := isConj_iff.1 hab
  obtain ⟨hp, hz, ⟨e⟩⟩ := h
  let f : cent (c * a * c⁻¹) ≃* cent a := centConjEquiv c a
  have hfz : ∀ g : cent (c * a * c⁻¹), (f g : G) = c⁻¹ * g * c := fun _ => rfl
  have hcenter : (Subgroup.center (cent (c * a * c⁻¹))).map f.toMonoidHom =
      Subgroup.center (cent a) := center_map_mulEquiv f
  refine ⟨Group.IsPerfect.ofSurjective (f := f.symm.toMonoidHom) f.symm.surjective, ?_, ?_⟩
  · ext y
    constructor
    · rintro ⟨g, hg, rfl⟩
      have : f g ∈ Subgroup.center (cent a) := hcenter ▸ ⟨g, hg, rfl⟩
      have hmem : ((f g : cent a) : G) ∈ Subgroup.zpowers a := hz ▸ ⟨_, this, rfl⟩
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hmem
      refine Subgroup.mem_zpowers_iff.2 ⟨k, ?_⟩
      rw [hfz] at hk
      calc (c * a * c⁻¹) ^ k = c * a ^ k * c⁻¹ := by
            rw [show c * a * c⁻¹ = MulAut.conj c a from rfl, ← map_zpow]; rfl
        _ = c * (c⁻¹ * g * c) * c⁻¹ := by rw [hk]
        _ = g := by group
    · intro hy
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
      have hak : a ^ k ∈ (Subgroup.center (cent a)).map (cent a).subtype :=
        hz ▸ zpow_mem (Subgroup.mem_zpowers a) k
      obtain ⟨w, hw, hwa⟩ := hak
      refine ⟨f.symm w, ?_, ?_⟩
      · rw [← hcenter] at hw
        obtain ⟨v, hv, rfl⟩ := hw
        simpa using hv
      · have : ((f.symm w : cent (c * a * c⁻¹)) : G) = c * w * c⁻¹ := rfl
        change ((f.symm w : cent (c * a * c⁻¹)) : G) = (c * a * c⁻¹) ^ k
        rw [this, show ((w : cent a) : G) = a ^ k from hwa]
        rw [show c * a * c⁻¹ = MulAut.conj c a from rfl, ← map_zpow]; rfl
  · exact ⟨(QuotientGroup.congr _ _ f hcenter).trans e⟩

end CFSG.Monster.Existence
