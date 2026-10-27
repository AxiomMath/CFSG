module

public import CFSG.Monster.B.TwoA.Base.FullCent
public import CFSG.Monster.B.Cbar.Simple
public import CFSG.Monster.Existence.Monolith

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.Existence

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice
  CFSG.Monster.Griess CFSG.Monster.Visible CFSG.Monster.Generated CFSG.Monster.B.Short
  CFSG.Monster.B CFSG.Monster.B.TwoA

@[expose] noncomputable def CfullA : Subgroup (SpaceB ≃ₗ[ℚ] SpaceB) :=
  AutO ⊓ Subgroup.centralizer {tStar}

theorem Cgen_le_CfullA : Cgen ≤ CfullA := fun _ hg =>
  ⟨Gmat_le_AutO (Cgen_le hg).1, (Cgen_le hg).2⟩

instance : Finite CfullA :=
  Finite.of_injective (Subgroup.inclusion (inf_le_left : CfullA ≤ AutO))
    (Subgroup.inclusion_injective _)

theorem tStar_mem_CfullA : tStar ∈ CfullA := Cgen_le_CfullA tStar_mem_Cgen

theorem commute_tStar_of_mem_CfullA {g : SpaceB ≃ₗ[ℚ] SpaceB} (hg : g ∈ CfullA) :
    g * tStar = tStar * g :=
  Subgroup.mem_centralizer_singleton_iff.1 hg.2

@[expose] noncomputable def tStarA : CfullA := ⟨tStar, tStar_mem_CfullA⟩

@[expose] noncomputable def ZstarA : Subgroup CfullA := Subgroup.zpowers tStarA

theorem tStarA_mem_center : tStarA ∈ Subgroup.center CfullA := by
  rw [Subgroup.mem_center_iff]
  intro g
  exact Subtype.ext (commute_tStar_of_mem_CfullA g.2)

instance ZstarA_normal : ZstarA.Normal :=
  Subgroup.normal_of_le_center ((Subgroup.zpowers_le).2 tStarA_mem_center)

theorem orderOf_tStarA : orderOf tStarA = 2 := by
  rw [tStarA, Subgroup.orderOf_mk, orderOf_tStar]

abbrev DA : Type := CfullA ⧸ ZstarA

@[expose] noncomputable def piA : CfullA →* DA := QuotientGroup.mk' ZstarA

theorem piA_surjective : Function.Surjective piA := QuotientGroup.mk'_surjective ZstarA

theorem ker_piA : piA.ker = ZstarA := QuotientGroup.ker_mk' ZstarA

theorem piA_eq_one_iff (g : CfullA) : piA g = 1 ↔ g = 1 ∨ g = tStarA := by
  rw [← MonoidHom.mem_ker, ker_piA, ZstarA]
  exact Short.mem_zpowers_iff_of_orderOf_eq_two orderOf_tStarA

instance : Finite DA := Finite.of_surjective piA piA_surjective

@[expose] noncomputable def inclGenA : Cgen →* CfullA := Subgroup.inclusion Cgen_le_CfullA

theorem Zstar_le_comapA : Zstar ≤ ZstarA.comap inclGenA := by
  rw [Zstar, Subgroup.zpowers_le, Subgroup.mem_comap]
  exact Subgroup.mem_zpowers _

@[expose] noncomputable def iotaA : Cbar →* DA :=
  QuotientGroup.map Zstar ZstarA inclGenA Zstar_le_comapA

theorem iotaA_kappa (g : Cgen) : iotaA (kappa g) = piA (inclGenA g) := rfl

theorem iotaA_injective : Function.Injective iotaA := by
  rw [injective_iff_map_eq_one]
  intro c hc
  obtain ⟨g, rfl⟩ := kappa_surjective c
  rw [iotaA_kappa, piA_eq_one_iff] at hc
  rw [kappa_eq_one_iff]
  rcases hc with h | h
  · exact .inl (Subtype.ext (show (g : SpaceB ≃ₗ[ℚ] SpaceB) = 1 from congrArg Subtype.val h))
  · exact .inr (Subtype.ext (show (g : SpaceB ≃ₗ[ℚ] SpaceB) = tStar from congrArg Subtype.val h))

@[expose] noncomputable def xA : CfullA := inclGenA xC

@[expose] noncomputable def xhatA : DA := piA xA

theorem iotaA_xbar : iotaA xbar = xhatA := rfl

@[expose] noncomputable def JhatA : Subgroup DA := (Jstar.subgroupOf CfullA).map piA

@[expose] noncomputable def EhatA : Subgroup DA := Ebar.map iotaA

@[expose] noncomputable def ShatA : Subgroup DA := iotaA.range

@[expose] noncomputable def tauhatA : DA := iotaA taubar

theorem JhatA_eq_map : JhatA = Jbar.map iotaA := by
  rw [JhatA, Jbar, Subgroup.map_map]
  ext d
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact ⟨⟨g, Jstar_le_Cgen hg⟩, hg, rfl⟩
  · rintro ⟨g, hg, rfl⟩
    exact ⟨inclGenA g, hg, rfl⟩

theorem orderOf_xhatA : orderOf xhatA = 2 := by
  rw [← iotaA_xbar, orderOf_injective iotaA iotaA_injective, orderOf_xbar]

theorem JhatA_le_centralizer_xhatA :
    JhatA ≤ Subgroup.centralizer {xhatA} := by
  rw [JhatA_eq_map, ← iotaA_xbar]
  rintro _ ⟨c, hc, rfl⟩
  rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
  rw [← centralizer_xbar] at hc
  rw [(Subgroup.mem_centralizer_singleton_iff.1 hc)]

theorem centralizer_xhatA_le_JhatA :
    Subgroup.centralizer {xhatA} ≤ JhatA := by
  intro d hd
  obtain ⟨g, rfl⟩ := piA_surjective d
  rw [Subgroup.mem_centralizer_singleton_iff] at hd
  have h1 : piA (g * xA * g⁻¹ * xA⁻¹) = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv]
    change piA g * xhatA * (piA g)⁻¹ * xhatA⁻¹ = 1
    rw [hd]
    group
  have hcomm : (g : SpaceB ≃ₗ[ℚ] SpaceB) * xmat * (g : SpaceB ≃ₗ[ℚ] SpaceB)⁻¹ = xmat := by
    rcases (piA_eq_one_iff _).1 h1 with h2 | h2
    · have h3 := congrArg Subtype.val h2
      change (g : SpaceB ≃ₗ[ℚ] SpaceB) * xmat * (g : SpaceB ≃ₗ[ℚ] SpaceB)⁻¹ * xmat⁻¹ = 1 at h3
      exact mul_inv_eq_one.1 h3
    · exfalso
      have h3 := congrArg Subtype.val h2
      change (g : SpaceB ≃ₗ[ℚ] SpaceB) * xmat * (g : SpaceB ≃ₗ[ℚ] SpaceB)⁻¹ * xmat⁻¹ =
        tStar at h3
      have h4 : (g : SpaceB ≃ₗ[ℚ] SpaceB) * xmat * (g : SpaceB ≃ₗ[ℚ] SpaceB)⁻¹ =
          rhoEquiv (zQ * rStar) := by
        rw [← tStar_mul_xmat, ← h3]
        group
      have e1 := trace_conj (g : SpaceB ≃ₗ[ℚ] SpaceB) xmat
      rw [h4, trace_rho_short isShortCoord_zQ_mul_rStar, trace_xmat] at e1
      norm_num at e1
  have hgx : (g : SpaceB ≃ₗ[ℚ] SpaceB) ∈ Gvis := by
    refine (mem_Hmat_iff_of_mem_AutO g.2.1).2 ?_
    calc xmat * (g : SpaceB ≃ₗ[ℚ] SpaceB) =
        (g : SpaceB ≃ₗ[ℚ] SpaceB) * xmat * (g : SpaceB ≃ₗ[ℚ] SpaceB)⁻¹ *
          (g : SpaceB ≃ₗ[ℚ] SpaceB) := by rw [hcomm]
      _ = (g : SpaceB ≃ₗ[ℚ] SpaceB) * xmat := by group
  exact ⟨g, ⟨hgx, Subgroup.mem_centralizer_singleton_iff.2 (commute_tStar_of_mem_CfullA g.2)⟩,
    rfl⟩

theorem centralizer_xhatA : Subgroup.centralizer {xhatA} = JhatA :=
  le_antisymm centralizer_xhatA_le_JhatA JhatA_le_centralizer_xhatA

theorem center_EhatA : (Subgroup.center EhatA).map EhatA.subtype = Subgroup.zpowers xhatA := by
  rw [map_center_eq_inf_centralizer, EhatA, ← map_inf_centralizer iotaA_injective,
    ← map_center_eq_inf_centralizer, map_center_Ebar, MonoidHom.map_zpowers, iotaA_xbar]

theorem centralizer_EhatA :
    JhatA ⊓ Subgroup.centralizer (EhatA : Set DA) = Subgroup.zpowers xhatA := by
  rw [JhatA_eq_map, EhatA, ← map_inf_centralizer iotaA_injective, centralizer_Ebar,
    MonoidHom.map_zpowers, iotaA_xbar]

theorem EhatA_le_JhatA : EhatA ≤ JhatA := by
  rw [JhatA_eq_map]
  exact Subgroup.map_mono Ebar_le_Jbar

theorem conj_mem_EhatA {g e : DA} (hg : g ∈ JhatA) (he : e ∈ EhatA) : g⁻¹ * e * g ∈ EhatA := by
  rw [JhatA_eq_map] at hg
  obtain ⟨g₀, hg₀, rfl⟩ := hg
  obtain ⟨e₀, he₀, rfl⟩ := he
  exact ⟨g₀⁻¹ * e₀ * g₀, conj_mem_Ebar hg₀ he₀, by rw [map_mul, map_mul, map_inv]⟩

theorem isPGroup_EhatA : IsPGroup 2 EhatA :=
  Ebar_extraspecial.1.1.of_equiv (Ebar.equivMapOfInjective iotaA iotaA_injective)

theorem JhatA_le_ShatA : JhatA ≤ ShatA := by
  rw [JhatA_eq_map]
  rintro _ ⟨c, -, rfl⟩
  exact ⟨c, rfl⟩

theorem xC_mul_yC : xC * yC = zC := by
  apply Subtype.ext
  change xmat * xmatTau = xmatTau2
  rw [xmat_eq_xB, xmatTau_eq, xmatTau2_eq, xB_mul_yB]

theorem cycle_tauhatA :
    tauhatA * (tauhatA * xhatA * tauhatA⁻¹) * tauhatA⁻¹ =
      xhatA * (tauhatA * xhatA * tauhatA⁻¹) := by
  rw [tauhatA, ← iotaA_xbar, ← map_inv, ← map_mul, ← map_mul, taubar_conj_xbar, ← map_mul,
    ← map_mul, taubar_conj_ybar, ← map_mul, xbar, ybar, zbar, ← map_mul, xC_mul_yC]

theorem xhatA_mul_self : xhatA * xhatA = 1 := by
  rw [← iotaA_xbar, ← map_mul, xbar_mul_self, map_one]

theorem tauhatA_mem_ShatA : tauhatA ∈ ShatA := ⟨taubar, rfl⟩

instance :
    IsSimpleGroup ShatA :=
  have : IsSimpleGroup Cbar := short_centralizer_generated_quotient_simple.2.2.1
  (MonoidHom.ofInjective iotaA_injective).symm.isSimpleGroup

theorem exists_sylow_DA :
    ∃ P : Sylow 2 DA, (P : Subgroup DA) ≤ JhatA ∧
    (Subgroup.center (P : Subgroup DA)).map (P : Subgroup DA).subtype =
      Subgroup.zpowers xhatA := by
  have hQH : EhatA ≤ Subgroup.centralizer {xhatA} := centralizer_xhatA ▸ EhatA_le_JhatA
  have hQn : (EhatA.subgroupOf (Subgroup.centralizer {xhatA})).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have hg : ((g⁻¹ : Subgroup.centralizer {xhatA}) : DA) ∈ JhatA := by
      rw [← centralizer_xhatA]; exact (g⁻¹).2
    have h := conj_mem_EhatA hg hn
    simpa using h
  have hCQ : Subgroup.centralizer {xhatA} ⊓ Subgroup.centralizer (EhatA : Set DA) =
      Subgroup.zpowers xhatA := by
    rw [centralizer_xhatA]
    exact centralizer_EhatA
  obtain ⟨h1, -, -, -⟩ := B.prime_centralizer_sylow_control orderOf_xhatA hQH hQn isPGroup_EhatA
    center_EhatA hCQ
  obtain ⟨P, hP, hZ⟩ := h1 default
  refine ⟨P, ?_, hZ⟩
  rw [hP, ← centralizer_xhatA]
  exact Subgroup.map_subtype_le _

theorem isSimpleGroup_DA :
    IsSimpleGroup DA := by
  obtain ⟨P, hPJ, hZ⟩ := exists_sylow_DA
  have hC : Subgroup.centralizer {xhatA} ≤ ShatA := centralizer_xhatA ▸ JhatA_le_ShatA
  exact isSimpleGroup_of_cycle xhatA_mul_self tauhatA_mem_ShatA cycle_tauhatA hC P
    (hPJ.trans JhatA_le_ShatA)
    ((normalizer_le_centralizer_of_center orderOf_xhatA hZ).trans hC)

theorem odd_index_ShatA : Odd ShatA.index := by
  obtain ⟨P, hPJ, -⟩ := exists_sylow_DA
  have h1 := P.not_dvd_index
  have h2 : ShatA.index ∣ (P : Subgroup DA).index := Subgroup.index_dvd_of_le
    (hPJ.trans JhatA_le_ShatA)
  exact Nat.odd_iff.2 (Nat.two_dvd_ne_zero.1 fun h => h1 (h.trans h2))

end CFSG.Monster.Existence
