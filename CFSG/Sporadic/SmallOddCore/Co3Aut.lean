module

public import CFSG.Sporadic.Schreier.Co3FirstAut
public import CFSG.Sporadic.Schreier.Co3SecondImage
public import CFSG.Sporadic.Schreier.MathieuSylowAutM12
public import CFSG.Sporadic.SmallOddCore.TableFacts

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

universe u

namespace CFSG.Sporadic.SmallOddCore

open Subgroup CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Co3 CFSG.Blueprint
open CFSG.ComponentClassification.OuterAutomorphisms

section Restrict

variable {X : Type*} [Group X]

@[expose] def restrictAut {P H : Subgroup X} (hHP : H ≤ P) (α : MulAut P)
    (h1 : ∀ x : H, ((α ⟨x, hHP x.2⟩ : P) : X) ∈ H)
    (h2 : ∀ x : H, ((α.symm ⟨x, hHP x.2⟩ : P) : X) ∈ H) : MulAut H where
  toFun x := ⟨α ⟨x, hHP x.2⟩, h1 x⟩
  invFun x := ⟨α.symm ⟨x, hHP x.2⟩, h2 x⟩
  left_inv x := by
    apply Subtype.ext
    simp only [Subtype.coe_eta, MulEquiv.symm_apply_apply]
  right_inv x := by
    apply Subtype.ext
    simp only [Subtype.coe_eta, MulEquiv.apply_symm_apply]
  map_mul' x y := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    rw [show (⟨(x : X) * y, hHP (x * y).2⟩ : P) = ⟨x, hHP x.2⟩ * ⟨y, hHP y.2⟩ from rfl, map_mul]
    rfl

theorem restrictAut_apply {P H : Subgroup X} (hHP : H ≤ P) (α : MulAut P) (h1 h2) (x : H) :
    ((restrictAut hHP α h1 h2 x : H) : X) = α ⟨x, hHP x.2⟩ := rfl

end Restrict

theorem co3ZP_coe :
    (co3ZP : Equiv.Perm (Fin 276)) = co3Z := rfl

theorem co3TtP_coe :
    (co3TtP : Equiv.Perm (Fin 276)) = co3Tt := rfl

theorem co3ZM1_coe :
    (co3ZM1 : Equiv.Perm (Fin 276)) = co3Z := rfl

theorem co3TtM1_coe :
    (co3TtM1 : Equiv.Perm (Fin 276)) = co3Tt := rfl

theorem co3TtM1_P :
    (⟨(co3TtM1 : Equiv.Perm (Fin 276)), co3M1_le_P co3TtM1.2⟩ : co3P) = co3TtP :=
  Subtype.ext (co3TtM1_coe.trans co3TtP_coe.symm)

theorem co3TtP_mem_M :
    (co3TtP : Equiv.Perm (Fin 276)) ∈ co3M := by
  rw [co3TtP_coe]
  exact co3Tt_mem_M

theorem co3_mem_M_iff
    (x : co3P) :
    (x : Equiv.Perm (Fin 276)) ∈ co3M ↔ x * co3ZP = co3ZP * x := by
  rw [co3M_eq_centralizer, mem_inf, mem_centralizer_singleton_iff]
  constructor
  · rintro ⟨-, h⟩
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, co3ZP_coe]
    exact h
  · intro h
    have h' := congrArg Subtype.val h
    rw [Subgroup.coe_mul, Subgroup.coe_mul, co3ZP_coe] at h'
    exact ⟨x.2, h'⟩

theorem co3_mem_M1_iff
    (x : co3P) :
    (x : Equiv.Perm (Fin 276)) ∈ co3M1 ↔ x * co3TtP = co3TtP * x := by
  rw [co3M1_eq_centralizer, mem_inf, mem_centralizer_singleton_iff]
  constructor
  · rintro ⟨-, h⟩
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, co3TtP_coe]
    exact h
  · intro h
    have h' := congrArg Subtype.val h
    rw [Subgroup.coe_mul, Subgroup.coe_mul, co3TtP_coe] at h'
    exact ⟨x.2, h'⟩

theorem comm_of_fix {G : Type*} [Group G] (α : MulAut G) {g x : G} (hg : α g = g)
    (hx : x * g = g * x) : α x * g = g * α x := by
  have := congrArg α hx
  rwa [map_mul, map_mul, hg] at this

theorem eq_one_of_isPerfect {H K : Type*} [Group H] [Group K] [Group.IsPerfect H] (f : H →* K)
    (hf : ∀ a b : H, f a * f b = f b * f a) (x : H) : f x = 1 := by
  have hc : commutator H ≤ f.ker := by
    rw [commutator_def, commutator_le]
    intro a _ b _
    rw [MonoidHom.mem_ker, commutatorElement_def]
    simp only [map_mul, map_inv]
    rw [hf a b]
    group
  have hx : x ∈ commutator H := by
    rw [Group.IsPerfect.commutator_eq_top]
    trivial
  exact hc hx

theorem co3_aut_eq_one
    (γ : MulAut co3P)
    (hM : ∀ x : co3P, (x : Equiv.Perm (Fin 276)) ∈ co3M → γ x = x)
    (hκ : ∀ x : co3P, ∀ hx : (x : Equiv.Perm (Fin 276)) ∈ co3M1,
      ∀ hx' : ((γ x : co3P) : Equiv.Perm (Fin 276)) ∈ co3M1,
      co3Kappa1 ⟨γ x, hx'⟩ = co3Kappa1 ⟨x, hx⟩) : γ = 1 := by
  have hγt : γ co3TtP = co3TtP := hM _ co3TtP_mem_M
  have hγinv_t : γ.symm co3TtP = co3TtP := by
    rw [MulEquiv.symm_apply_eq, hγt]
  have h1 : ∀ x : co3M1, ((γ ⟨x, co3M1_le_P x.2⟩ : co3P) : Equiv.Perm (Fin 276)) ∈ co3M1 := by
    intro x
    rw [co3_mem_M1_iff]
    exact comm_of_fix γ hγt ((co3_mem_M1_iff ⟨x, co3M1_le_P x.2⟩).1 x.2)
  have h2 : ∀ x : co3M1,
      ((γ.symm ⟨x, co3M1_le_P x.2⟩ : co3P) : Equiv.Perm (Fin 276)) ∈ co3M1 := by
    intro x
    rw [co3_mem_M1_iff]
    exact comm_of_fix γ.symm hγinv_t ((co3_mem_M1_iff ⟨x, co3M1_le_P x.2⟩).1 x.2)
  set γ1 := restrictAut co3M1_le_P γ h1 h2
  have hdef : ∀ x : co3M1, x⁻¹ * γ1 x ∈ co3Kappa1.ker := by
    intro x
    rw [MonoidHom.mem_ker, map_mul, map_inv, inv_mul_eq_one]
    have := hκ ⟨x, co3M1_le_P x.2⟩ x.2 (h1 x)
    exact this.symm
  have hcent : ∀ x : co3M1, x⁻¹ * γ1 x ∈ center co3M1 := fun x =>
    co3Z1_le_center (by rw [co3Z1, ← co3Kappa1_ker]; exact hdef x)
  let c : co3M1 →* co3M1 := MonoidHom.mk' (fun x => x⁻¹ * γ1 x) (by
    intro x y
    have hx := mem_center_iff.mp (hcent x)
    rw [map_mul, mul_inv_rev]
    calc y⁻¹ * x⁻¹ * (γ1 x * γ1 y) = y⁻¹ * (x⁻¹ * γ1 x) * γ1 y := by group
      _ = (x⁻¹ * γ1 x) * y⁻¹ * γ1 y := by rw [← hx y⁻¹]
      _ = x⁻¹ * γ1 x * (y⁻¹ * γ1 y) := by group)
  have hc_apply : ∀ x, c x = x⁻¹ * γ1 x := fun _ => rfl
  have hcL : ∀ x ∈ co3L1, c x = 1 := by
    intro x hx
    have : Group.IsPerfect co3L1 := by
      have := co3L_isPerfect
      exact Group.IsPerfect.ofSurjective (f := (subgroupOfEquivOfLe co3L_le_M1).symm.toMonoidHom)
        (subgroupOfEquivOfLe co3L_le_M1).symm.surjective
    have h := eq_one_of_isPerfect (c.comp co3L1.subtype) (fun a b => by
      have ha := mem_center_iff.mp (hcent a)
      simp only [MonoidHom.comp_apply, coe_subtype, hc_apply]
      exact (ha (b⁻¹ * γ1 b)).symm) ⟨x, hx⟩
    simpa using h
  have hct : c co3TtM1 = 1 := by
    rw [hc_apply, inv_mul_eq_one]
    apply Subtype.ext
    rw [restrictAut_apply, co3TtM1_P, hγt, co3TtP_coe, co3TtM1_coe]
  have hcZ : ∀ x ∈ co3Z1, c x = 1 := by
    intro x hx
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hx
    rw [map_zpow, hct, one_zpow]
  have hc1 : ∀ x : co3M1, c x = 1 := by
    intro x
    have hker : co3L1 ⊔ co3Z1 ≤ c.ker := sup_le (fun y hy => hcL y hy) (fun y hy => hcZ y hy)
    rw [co3L1_sup_Z1] at hker
    exact hker trivial
  have hM1 : ∀ x : co3P, (x : Equiv.Perm (Fin 276)) ∈ co3M1 → γ x = x := by
    intro x hx
    have h := hc1 ⟨x, hx⟩
    rw [hc_apply, inv_mul_eq_one] at h
    apply Subtype.ext
    have := congrArg Subtype.val h
    rw [restrictAut_apply] at this
    exact this.symm
  have htop : co3M.subgroupOf co3P ⊔ co3M1.subgroupOf co3P = ⊤ := by
    rw [← subgroupOf_sup co3M_le_P co3M1_le_P, co3M_sup_M1, subgroupOf_self]
  have hfix : co3M.subgroupOf co3P ⊔ co3M1.subgroupOf co3P ≤
      MonoidHom.eqLocus γ.toMonoidHom (MonoidHom.id co3P) :=
    sup_le (fun x hx => hM x (mem_subgroupOf.mp hx)) (fun x hx => hM1 x (mem_subgroupOf.mp hx))
  rw [htop] at hfix
  exact MulEquiv.ext fun x => hfix trivial

theorem co3Kappa1_mem
    (x : co3M1) : co3Kappa1 x ∈ NativeSporadic.M12 :=
  co3Kappa1_range ▸ (⟨x, rfl⟩ : co3Kappa1 x ∈ co3Kappa1.range)

theorem co3_descent
    (β1 : MulAut co3M1) (hβ1t : β1 co3TtM1 = co3TtM1) :
    ∃ δ : MulAut NativeSporadic.M12, ∀ x : co3M1,
      ((δ ⟨co3Kappa1 x, co3Kappa1_mem x⟩ : NativeSporadic.M12) : Equiv.Perm (Fin 12)) =
        co3Kappa1 (β1 x) := by
  have hker : co3Kappa1.ker.map (β1 : co3M1 →* co3M1) = co3Kappa1.ker := by
    rw [co3Kappa1_ker, MonoidHom.map_zpowers, MonoidHom.coe_ofClass, hβ1t]
  have he : ∀ y : co3M1, QuotientGroup.quotientKerEquivRange co3Kappa1
      (y : co3M1 ⧸ co3Kappa1.ker) = co3Kappa1.rangeRestrict y := fun _ => rfl
  refine ⟨((MulEquiv.subgroupCongr co3Kappa1_range).symm.trans
    (((QuotientGroup.quotientKerEquivRange co3Kappa1).symm.trans
      (QuotientGroup.congr co3Kappa1.ker co3Kappa1.ker β1 hker)).trans
      (QuotientGroup.quotientKerEquivRange co3Kappa1))).trans
    (MulEquiv.subgroupCongr co3Kappa1_range), fun x => ?_⟩
  have h1 : (MulEquiv.subgroupCongr co3Kappa1_range).symm ⟨co3Kappa1 x, co3Kappa1_mem x⟩ =
      co3Kappa1.rangeRestrict x :=
    Subtype.ext (by rw [MulEquiv.subgroupCongr_symm_apply, MonoidHom.coe_rangeRestrict])
  have h2 : (QuotientGroup.quotientKerEquivRange co3Kappa1).symm (co3Kappa1.rangeRestrict x) =
      (x : co3M1 ⧸ co3Kappa1.ker) := by
    rw [MulEquiv.symm_apply_eq, he]
  rw [MulEquiv.trans_apply, MulEquiv.trans_apply, MulEquiv.trans_apply, MulEquiv.trans_apply, h1,
    h2, QuotientGroup.congr_mk, he, MulEquiv.subgroupCongr_apply, MonoidHom.coe_rangeRestrict]

theorem co3_sylow_normalize
    (α : MulAut co3P) : ∃ g : co3P, ∀ y : co3P,
    (y : Equiv.Perm (Fin 276)) ∈ co3T ↔ ∃ x : co3P, (x : Equiv.Perm (Fin 276)) ∈ co3T ∧
      y = (MulAut.conj g * α) x := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcard : Nat.card ↥((co3T.subgroupOf co3P).map α.toMonoidHom) =
      2 ^ (Nat.card co3P).factorization 2 := by
    rw [Subgroup.card_map_of_injective α.injective, card_co3T_subgroupOf, card_co3P,
      show (495766656000 : ℕ) = 2 ^ 10 * 484147125 by norm_num,
      factorization_two_pow_mul (by norm_num)]
    norm_num
  let S₂ : Sylow 2 co3P := Sylow.ofCard _ hcard
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq co3P S₂ co3TSylow
  refine ⟨g, fun y => ?_⟩
  have hy : y ∈ (co3TSylow : Subgroup co3P) ↔ y ∈ ((g • S₂ : Sylow 2 co3P) : Subgroup co3P) := by
    rw [hg]
  rw [co3TSylow_coe, mem_subgroupOf, Sylow.coe_subgroup_smul,
    Subgroup.mem_smul_pointwise_iff_exists] at hy
  rw [hy]
  constructor
  · rintro ⟨s, hs, rfl⟩
    have hs' : s ∈ (co3T.subgroupOf co3P).map α.toMonoidHom := hs
    obtain ⟨x, hx, rfl⟩ := mem_map.mp hs'
    exact ⟨x, mem_subgroupOf.mp hx, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨α x, (mem_map_of_mem α.toMonoidHom (mem_subgroupOf.mpr hx) : _), rfl⟩

theorem co3_fix_z
    (β : MulAut co3P) (hg : ∀ y : co3P, (y : Equiv.Perm (Fin 276)) ∈ co3T ↔
    ∃ x : co3P, (x : Equiv.Perm (Fin 276)) ∈ co3T ∧ y = β x) : β co3ZP = co3ZP := by
  have hzT : (co3ZP : Equiv.Perm (Fin 276)) ∈ co3T := by
    rw [co3ZP_coe]
    exact co3Z_mem_T
  have hzc : ∀ y ∈ co3T, co3Z * y = y * co3Z := ((co3T_center_iff co3Z).2 (Or.inr rfl)).2
  have h1 : ((β co3ZP : co3P) : Equiv.Perm (Fin 276)) ∈ co3T := (hg _).2 ⟨co3ZP, hzT, rfl⟩
  have h2 : ∀ y ∈ co3T,
      ((β co3ZP : co3P) : Equiv.Perm (Fin 276)) * y = y * (β co3ZP : co3P) := by
    intro y hy
    obtain ⟨x, hx, hxy⟩ := (hg ⟨y, co3T_le_P hy⟩).1 hy
    have hzx : co3ZP * x = x * co3ZP := by
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_mul, co3ZP_coe]
      exact hzc x hx
    have := congrArg (fun w => ((β w : co3P) : Equiv.Perm (Fin 276))) hzx
    simp only [map_mul, Subgroup.coe_mul] at this
    have hy' : y = ((β x : co3P) : Equiv.Perm (Fin 276)) := congrArg Subtype.val hxy
    rw [hy']
    exact this
  rcases (co3T_center_iff _).1 ⟨h1, h2⟩ with h | h
  · exfalso
    have h0 : β co3ZP = 1 := Subtype.ext (by rw [h, Subgroup.coe_one])
    rw [MulEquiv.map_eq_one_iff] at h0
    exact co3Z_ne_one (by rw [← co3ZP_coe, h0, Subgroup.coe_one])
  · exact Subtype.ext (by rw [h, co3ZP_coe])

theorem co3_inner_on_M
    (β : MulAut co3P) (hβz : β co3ZP = co3ZP) :
    ∃ m : co3P, ∀ x : co3P, (x : Equiv.Perm (Fin 276)) ∈ co3M → (MulAut.conj m⁻¹ * β) x = x := by
  have hβz' : β.symm co3ZP = co3ZP := by rw [MulEquiv.symm_apply_eq, hβz]
  have h1 : ∀ x : co3M, ((β ⟨x, co3M_le_P x.2⟩ : co3P) : Equiv.Perm (Fin 276)) ∈ co3M :=
    fun x => by
      rw [co3_mem_M_iff]
      exact comm_of_fix β hβz ((co3_mem_M_iff ⟨x, co3M_le_P x.2⟩).1 x.2)
  have h2 : ∀ x : co3M, ((β.symm ⟨x, co3M_le_P x.2⟩ : co3P) : Equiv.Perm (Fin 276)) ∈ co3M :=
    fun x => by
      rw [co3_mem_M_iff]
      exact comm_of_fix β.symm hβz' ((co3_mem_M_iff ⟨x, co3M_le_P x.2⟩).1 x.2)
  obtain ⟨m, hm⟩ := co3M_allInner (restrictAut co3M_le_P β h1 h2)
  refine ⟨⟨m, co3M_le_P m.2⟩, fun x hx => ?_⟩
  have e1 : ((restrictAut co3M_le_P β h1 h2 ⟨x, hx⟩ : co3M) : Equiv.Perm (Fin 276)) =
      ((β x : co3P) : Equiv.Perm (Fin 276)) := by
    rw [restrictAut_apply]
  have e2 : ((MulAut.conj m ⟨x, hx⟩ : co3M) : Equiv.Perm (Fin 276)) =
      (m : Equiv.Perm (Fin 276)) * x * (m : Equiv.Perm (Fin 276))⁻¹ := by
    rw [MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_mk]
  have h3 : ((β x : co3P) : Equiv.Perm (Fin 276)) =
      (m : Equiv.Perm (Fin 276)) * x * (m : Equiv.Perm (Fin 276))⁻¹ :=
    (e1.symm.trans
      (congrArg (fun φ : MulAut co3M => ((φ ⟨x, hx⟩ : co3M) : Equiv.Perm (Fin 276))) hm)).trans e2
  apply Subtype.ext
  rw [MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv,
    inv_inv, Subgroup.coe_mk, h3]
  group

theorem co3_fix_M_kappa
    (β : MulAut co3P)
    (hβM : ∀ x : co3P, (x : Equiv.Perm (Fin 276)) ∈ co3M → β x = x) :
    ∃ v : Equiv.Perm (Fin 12), (v = 1 ∨ v = co3Kappa1 co3ZM1) ∧
      ∀ x : co3P, ∀ hx : (x : Equiv.Perm (Fin 276)) ∈ co3M1,
        ∀ hx' : ((β x : co3P) : Equiv.Perm (Fin 276)) ∈ co3M1,
          co3Kappa1 ⟨β x, hx'⟩ = v * co3Kappa1 ⟨x, hx⟩ * v⁻¹ := by
  have hβt : β co3TtP = co3TtP := hβM _ co3TtP_mem_M
  have hβt' : β.symm co3TtP = co3TtP := by rw [MulEquiv.symm_apply_eq, hβt]
  have k1 : ∀ x : co3M1, ((β ⟨x, co3M1_le_P x.2⟩ : co3P) : Equiv.Perm (Fin 276)) ∈ co3M1 :=
    fun x => by
      rw [co3_mem_M1_iff]
      exact comm_of_fix β hβt ((co3_mem_M1_iff ⟨x, co3M1_le_P x.2⟩).1 x.2)
  have k2 : ∀ x : co3M1, ((β.symm ⟨x, co3M1_le_P x.2⟩ : co3P) : Equiv.Perm (Fin 276)) ∈ co3M1 :=
    fun x => by
      rw [co3_mem_M1_iff]
      exact comm_of_fix β.symm hβt' ((co3_mem_M1_iff ⟨x, co3M1_le_P x.2⟩).1 x.2)
  have hβ1t : restrictAut co3M1_le_P β k1 k2 co3TtM1 = co3TtM1 := by
    apply Subtype.ext
    rw [restrictAut_apply, co3TtM1_P, hβt, co3TtP_coe, co3TtM1_coe]
  obtain ⟨δ, hδ⟩ := co3_descent (restrictAut co3M1_le_P β k1 k2) hβ1t
  have hδH : ∀ h (hh : h ∈ co3D0Img) (hh' : h ∈ NativeSporadic.M12), δ ⟨h, hh'⟩ = ⟨h, hh'⟩ := by
    intro h hh hh'
    obtain ⟨d, hd, rfl⟩ := mem_map.mp hh
    have hdM : ((d : co3M1) : Equiv.Perm (Fin 276)) ∈ co3M :=
      (mem_inf.mp (co3D0_le (mem_subgroupOf.mp hd))).1
    have hβd : restrictAut co3M1_le_P β k1 k2 d = d := by
      apply Subtype.ext
      rw [restrictAut_apply, hβM ⟨d, co3M1_le_P d.2⟩ hdM]
    apply Subtype.ext
    rw [hδ d, hβd]
  obtain ⟨-, -, hcentH, -, hHM12, S, hS⟩ := CTUC_Co3_second_centralizer_intersection_image
  have hfixS : ∀ s ∈ (S : Subgroup NativeSporadic.M12), δ s = s := by
    intro s hs
    have := hδH s (hS (mem_map_of_mem _ hs)) s.2
    simpa using this
  obtain ⟨c, -, hcδ⟩ := m12_sylow_pointwise_inner S δ hfixS
  have hcH : ((c : NativeSporadic.M12) : Equiv.Perm (Fin 12)) ∈
      ((centralizer (co3D0Img : Set (Equiv.Perm (Fin 12))) ⊓ NativeSporadic.M12 :
        Subgroup (Equiv.Perm (Fin 12))) : Set (Equiv.Perm (Fin 12))) := by
    refine mem_inf.mpr ⟨mem_centralizer_iff.mpr fun h hh => ?_, (c : NativeSporadic.M12).2⟩
    have hh' := hHM12 hh
    have h1 := hcδ ⟨h, hh'⟩
    rw [hδH h hh hh'] at h1
    have h2 := congrArg Subtype.val h1
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h2
    calc h * ((c : NativeSporadic.M12) : Equiv.Perm (Fin 12))
        = (((c : NativeSporadic.M12) : Equiv.Perm (Fin 12)) * h *
            ((c : NativeSporadic.M12) : Equiv.Perm (Fin 12))⁻¹) *
            ((c : NativeSporadic.M12) : Equiv.Perm (Fin 12)) := by rw [← h2]
      _ = ((c : NativeSporadic.M12) : Equiv.Perm (Fin 12)) * h := by group
  rw [hcentH, Set.mem_insert_iff, Set.mem_singleton_iff] at hcH
  refine ⟨((c : NativeSporadic.M12) : Equiv.Perm (Fin 12)), hcH, fun x hx hx' => ?_⟩
  have hb : (⟨β x, hx'⟩ : co3M1) = restrictAut co3M1_le_P β k1 k2 ⟨x, hx⟩ :=
    Subtype.ext (by rw [restrictAut_apply])
  rw [hb, ← hδ ⟨x, hx⟩, hcδ]
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]

theorem co3_fix_M
    (β : MulAut co3P)
    (hβM : ∀ x : co3P, (x : Equiv.Perm (Fin 276)) ∈ co3M → β x = x) :
    β = 1 ∨ β = MulAut.conj co3ZP := by
  obtain ⟨v, hv, hκ⟩ := co3_fix_M_kappa β hβM
  rcases hv with rfl | rfl
  · left
    refine co3_aut_eq_one β hβM fun x hx hx' => ?_
    rw [hκ x hx hx', one_mul, inv_one, mul_one]
  · right
    have hβt : β co3TtP = co3TtP := hβM _ co3TtP_mem_M
    have hγM : ∀ x : co3P, (x : Equiv.Perm (Fin 276)) ∈ co3M →
        (MulAut.conj co3ZP⁻¹ * β) x = x := by
      intro x hx
      have hxz := (co3_mem_M_iff x).1 hx
      rw [MulAut.mul_apply, hβM x hx, MulAut.conj_apply, inv_inv]
      calc co3ZP⁻¹ * x * co3ZP = co3ZP⁻¹ * (x * co3ZP) := by group
        _ = co3ZP⁻¹ * (co3ZP * x) := by rw [hxz]
        _ = x := by group
    have hγ : MulAut.conj co3ZP⁻¹ * β = 1 := by
      refine co3_aut_eq_one _ hγM fun x hx hx' => ?_
      have hbx : ((β x : co3P) : Equiv.Perm (Fin 276)) ∈ co3M1 := by
        rw [co3_mem_M1_iff]
        exact comm_of_fix β hβt ((co3_mem_M1_iff x).1 hx)
      have hsplit : (⟨(MulAut.conj co3ZP⁻¹ * β) x, hx'⟩ : co3M1) =
          co3ZM1⁻¹ * ⟨β x, hbx⟩ * co3ZM1 := by
        apply Subtype.ext
        simp only [MulAut.mul_apply, MulAut.conj_apply, inv_inv, Subgroup.coe_mul,
          Subgroup.coe_inv, co3ZP_coe, co3ZM1_coe]
      rw [hsplit, map_mul, map_mul, map_inv, hκ x hx hbx]
      group
    calc β = MulAut.conj co3ZP * (MulAut.conj co3ZP⁻¹ * β) := by
          rw [← mul_assoc, ← map_mul, mul_inv_cancel, map_one, one_mul]
      _ = MulAut.conj co3ZP := by rw [hγ, mul_one]

theorem co3P_allInner :
    ∀ α : MulAut co3P, ∃ p : co3P, α = MulAut.conj p := by
  intro α
  obtain ⟨g, hg⟩ := co3_sylow_normalize α
  obtain ⟨m, hm⟩ := co3_inner_on_M _ (co3_fix_z _ hg)
  have key : ∀ q : co3P, MulAut.conj m⁻¹ * (MulAut.conj g * α) = MulAut.conj q →
      α = MulAut.conj (g⁻¹ * m * q) := by
    intro q hq
    have : α = MulAut.conj g⁻¹ * MulAut.conj m * (MulAut.conj m⁻¹ * (MulAut.conj g * α)) := by
      simp only [map_inv]
      group
    rw [this, hq, map_mul, map_mul]
  rcases co3_fix_M _ hm with h | h
  · exact ⟨g⁻¹ * m * 1, key 1 (by rw [h, map_one])⟩
  · exact ⟨g⁻¹ * m * co3ZP, key co3ZP h⟩

theorem inner_eq_top_of_allInner {G : Type*} [Group G]
    (h : ∀ α : MulAut G, ∃ g : G, α = MulAut.conj g) : inner G = ⊤ := by
  refine eq_top_iff.2 fun α _ => ?_
  obtain ⟨g, rfl⟩ := h α
  exact ⟨g, rfl⟩

theorem co3_allInner :
    ∀ α : MulAut NativeSporadic.Co3, ∃ g : NativeSporadic.Co3, α = MulAut.conj g :=
  @allInner_of_mulEquiv NativeSporadic.Co3 co3P Units.instGroup co3P.toGroup co3PermEquiv
    co3P_allInner

theorem ctuc_co3_all_automorphisms_inner :
    ((∀ α : MulAut co3P, ∃ p : co3P, α = MulAut.conj p) ∧ inner co3P = ⊤) ∧
      ((∀ α : MulAut NativeSporadic.Co3, ∃ g : NativeSporadic.Co3, α = MulAut.conj g) ∧
        inner NativeSporadic.Co3 = ⊤) ∧
      ∀ (G : Type u) [Group G], Nonempty (G ≃* NativeSporadic.Co3) →
        (∀ α : MulAut G, ∃ g : G, α = MulAut.conj g) ∧ inner G = ⊤ := by
  refine ⟨⟨co3P_allInner, inner_eq_top_of_allInner co3P_allInner⟩,
    ⟨co3_allInner, @inner_eq_top_of_allInner NativeSporadic.Co3 Units.instGroup co3_allInner⟩,
    ?_⟩
  rintro G _ ⟨e⟩
  have hG := @allInner_of_mulEquiv G NativeSporadic.Co3 _ Units.instGroup e co3_allInner
  exact ⟨hG, inner_eq_top_of_allInner hG⟩

end CFSG.Sporadic.SmallOddCore
