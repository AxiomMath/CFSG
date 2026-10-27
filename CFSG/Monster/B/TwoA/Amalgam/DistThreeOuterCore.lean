module

public import CFSG.Monster.B.TwoA.Amalgam.EightOrbitsBridge
public import CFSG.Monster.B.TwoA.Amalgam.DerivedCoverMain
public import CFSG.Monster.B.TwoA.Unitary.TransvSwitch

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Amalgam

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.C2E6Std
open CFSG.LieType.Chevalley.C2E6Std.FieldExtension
open CFSG.LieType.Chevalley.CosetBuilding CFSG.Monster.B.Geometry CFSG.Monster.B.E6
  CFSG.Monster.B.E6.StdF4
open CFSG.Monster CFSG.Monster.B CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Sp8

theorem ker_eq_comap_of_isSimpleGroup {H A B : Type*} [Group H] [Group A] [Group B] [Finite A]
    {π : H →* A} (hπ : Function.Surjective π) {A₀ : Subgroup A} (hidx : A₀.index = 2)
    (hs : IsSimpleGroup A₀) (hcard : 2 < Nat.card A₀) {χ : H →* B} [Finite B]
    (hB : Nat.card B = 2) (hN : π.ker ≤ χ.ker) {h₀ : H} (hh₀ : χ h₀ ≠ 1) :
    χ.ker = A₀.comap π := by
  have hrange : Nat.card χ.range = 2 := by
    refine le_antisymm (hB ▸ Subgroup.card_le_card_group _) ?_
    have h1 : ({1, χ h₀} : Set B) ⊆ (χ.range : Set B) := by
      rintro _ (rfl | rfl)
      · exact χ.range.one_mem
      · exact ⟨h₀, rfl⟩
    have h2 := Set.ncard_le_ncard h1 (Set.toFinite _)
    rw [Set.ncard_pair hh₀.symm, ← Nat.card_coe_set_eq] at h2
    exact h2
  have hidxK : χ.ker.index = 2 := by rw [Subgroup.index_ker, hrange]
  have hle : A₀.comap π ≤ χ.ker := by
    set M : Subgroup A := χ.ker.map π with hM
    have hMn : M.Normal := Subgroup.Normal.map inferInstance π hπ
    have hMidx : M.index ≤ 2 := by
      have h := Subgroup.index_map_dvd χ.ker hπ
      rw [hidxK] at h
      exact Nat.le_of_dvd (by norm_num) h
    have hM₀n : (M.subgroupOf A₀).Normal := hMn.subgroupOf A₀
    rcases hs.eq_bot_or_eq_top_of_normal (M.subgroupOf A₀) with h | h
    · exfalso
      have hinj : Function.Injective ((QuotientGroup.mk' M).comp A₀.subtype) := by
        rw [injective_iff_map_eq_one]
        intro a ha
        have ha' : (a : A) ∈ M := (QuotientGroup.eq_one_iff _).1 ha
        have : a ∈ M.subgroupOf A₀ := Subgroup.mem_subgroupOf.2 ha'
        rw [h] at this
        exact (Subgroup.mem_bot.1 this)
      have hle' := Nat.card_le_card_of_injective _ hinj
      rw [← Subgroup.index_eq_card] at hle'
      omega
    · intro k hk
      have hk' : π k ∈ M := by
        have : (⟨π k, hk⟩ : A₀) ∈ M.subgroupOf A₀ := by rw [h]; trivial
        exact Subgroup.mem_subgroupOf.1 this
      obtain ⟨h₁, hh₁, he⟩ := hk'
      have hn : h₁⁻¹ * k ∈ π.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, he, inv_mul_cancel]
      have := χ.ker.mul_mem hh₁ (hN hn)
      rwa [mul_inv_cancel_left] at this
  have hidxC : (A₀.comap π).index = 2 := by
    rw [Subgroup.index_comap_of_surjective _ hπ, hidx]
  have : (χ.ker).FiniteIndex := ⟨by rw [hidxK]; norm_num⟩
  exact (Subgroup.eq_of_index_dvd_index hle (by rw [hidxC, hidxK])).symm

theorem isSimpleGroup_linU :
    IsSimpleGroup Unitary.linU := by
  obtain ⟨e⟩ := Unitary.nonempty_linU_equiv
  have hK : Nat.card CFSG.Fischer.F4 = (2 ^ 1) ^ 2 := Unitary.hF4.card_eq_sq
  have hs := CFSG.ClassicalGroups.Unitary.isSimpleGroup_statedProj_statedSU CFSG.Fischer.F4 2 1 hK
    6 (by norm_num) (by decide)
  have e' := CFSG.ClassicalGroups.UnitaryFlag.unitaryPSUEquiv Unitary.hF4 (n := 6) (by norm_num)
  exact @MulEquiv.isSimpleGroup _ _ _ _ hs (e.trans e')

theorem natCard_linU :
    Nat.card Unitary.linU = 9196830720 := by
  have h := Subgroup.card_mul_index Unitary.linU
  rw [Unitary.index_linU, Unitary.natCard_Usig] at h
  omega

theorem P1_le_Eam_d3 :
    P1 ≤ Eam := fun _ hx => Pc_le_Eam 0 hx

@[expose] def pc0Proj :
    Pc 0 →* Unitary.Usig :=
  p1Proj.comp (Subgroup.inclusion (le_of_eq Pc_zero_eq_P1))

theorem pc0Proj_surjective :
    Function.Surjective pc0Proj := by
  intro u
  obtain ⟨p, hp⟩ := p1Proj_surjective u
  exact ⟨⟨p, (show (p : Dfull) ∈ Pc 0 from p.2)⟩, hp⟩

section Field

variable {θ : Eam ⧸ Subgroup.zpowers cE' ≃* GStar}

@[expose] def fieldChi
    (θ : Eam ⧸ Subgroup.zpowers cE' ≃* GStar) : Pc 0 →* betaGroup :=
  SemidirectProduct.rightHom.comp (rho1 θ)

theorem fieldChi_apply
    (p : Pc 0) : fieldChi θ p = (rho1 θ p).right := rfl

theorem exists_fieldChi_ne_one
    {f : Chamber ≃ C2E6Std.stdChamber}
    (hadj : ∀ (i : Fin Tag.F4.rank) (x y : Chamber), chamberCS.adj i x y ↔
      stdDistanceF4 (f x) (f y) = 1 ∨ stdDistanceF4 (f x) (f y) = (coxeterSystem .F4).simple i)
    (hfeq : ∀ (z : Chamber) (e : Eam), f (chamberMul z e⁻¹) = θ (QuotientGroup.mk e) • f z)
    (hfB : f baseChamber = c₀) : ∃ p : Pc 0, fieldChi θ p ≠ 1 := by
  set b : betaGroup := ⟨betaG, Subgroup.mem_zpowers _⟩ with hb
  have hmem : (SemidirectProduct.inr b : GStar) ∈ parStar firstJ := by
    rw [mem_parStar, SemidirectProduct.left_inr]
    exact one_mem _
  obtain ⟨p, hp⟩ := exists_rho1_eq hadj hfeq hfB hmem
  refine ⟨p, ?_⟩
  rw [fieldChi_apply, hp, SemidirectProduct.right_inr]
  intro h
  exact betaG_ne_one (congrArg Subtype.val h)

theorem ker_pc0Proj_le_ker_fieldChi
    {f : Chamber ≃ C2E6Std.stdChamber}
    (hadj : ∀ (i : Fin Tag.F4.rank) (x y : Chamber), chamberCS.adj i x y ↔
      stdDistanceF4 (f x) (f y) = 1 ∨ stdDistanceF4 (f x) (f y) = (coxeterSystem .F4).simple i)
    (hfeq : ∀ (z : Chamber) (e : Eam), f (chamberMul z e⁻¹) = θ (QuotientGroup.mk e) • f z)
    (hfB : f baseChamber = c₀) : pc0Proj.ker ≤ (fieldChi θ).ker := by
  intro n hn
  have hn' : (Subgroup.inclusion (le_of_eq Pc_zero_eq_P1) n : P1) ∈ p1Proj.ker := hn
  rw [ker_p1Proj, Subgroup.mem_subgroupOf] at hn'
  have h := rho1_mem_radStar hadj hfeq hfB (n := n) hn'
  rw [MonoidHom.mem_ker, fieldChi_apply]
  exact (mem_radStar.1 h).2

end Field

theorem mem_commutator_iff_p1Proj
    {x : Dfull} (hx : x ∈ P1) :
    (⟨x, P1_le_Eam_d3 hx⟩ : Eam) ∈ commutator Eam ↔ p1Proj ⟨x, hx⟩ ∈ Unitary.linU := by
  obtain ⟨θ₁, f₁, h1, h2, h3⟩ := short_F4_standard_twisted_E6_quotient
  obtain ⟨θ, f, hadj, -, hfeq, hfB⟩ := exists_normalized_quotient θ₁ f₁ h1 h2 h3
  have hder := short_F4_derived_standard_perfect_cover.2.2.2.2.2.2.2.2.2 θ
  have hker := ker_eq_comap_of_isSimpleGroup pc0Proj_surjective Unitary.index_linU
    isSimpleGroup_linU (by rw [natCard_linU]; norm_num) card_betaGroup
    (ker_pc0Proj_le_ker_fieldChi (θ := θ) hadj hfeq hfB)
    (exists_fieldChi_ne_one hadj hfeq hfB).choose_spec
  set p : Pc 0 := ⟨x, (show x ∈ Pc 0 from hx)⟩ with hp
  have e1 : (⟨x, P1_le_Eam_d3 hx⟩ : Eam) ∈ commutator Eam ↔ p ∈ (fieldChi θ).ker := by
    rw [hder, Subgroup.mem_comap, MonoidHom.mem_ker, fieldChi_apply]
    show θ (QuotientGroup.mk _) ∈ (SemidirectProduct.inl : stdGroup →* GStar).range ↔ _
    rw [SemidirectProduct.range_inl_eq_ker_rightHom, MonoidHom.mem_ker]
    rfl
  rw [e1, hker, Subgroup.mem_comap]
  rfl

end CFSG.Monster.B.TwoA.Amalgam
