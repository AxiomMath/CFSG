module

public import CFSG.Monster.B.E6.StdF4FiberCore
public import CFSG.Monster.B.E6.StdF4FiberSets
public import CFSG.Monster.B.TwoA.Amalgam.CosetGraphRootCore
public import CFSG.Monster.B.TwoA.Amalgam.TypeFourCore

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Amalgam

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.C2E6Std
open CFSG.LieType.Chevalley.C2E6Std.FieldExtension
open CFSG.LieType.Chevalley.CosetBuilding CFSG.Monster.B.Geometry CFSG.Monster.B.E6.StdF4
open CFSG.Monster CFSG.Monster.B CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Sp8

theorem smul_c₀_mem_residue_iff
    (γ : GStar) (J : Set (Fin 4)) :
    γ • c₀ ∈ residue ncs stdDistance J c₀ ↔ γ ∈ parStar J := by
  have h : γ • c₀ = ((γ.left : stdGroup) : C2E6Std.stdChamber) := by
    rw [show c₀ = ((1 : stdGroup) : C2E6Std.stdChamber) from rfl, smul_mk, map_one, mul_one]
  rw [h]
  exact mem_baseResidue_iff J γ.left

theorem mem_parStar_inter
    {J J' : Set (Fin 4)} {γ : GStar} :
    γ ∈ parStar (J ∩ J') ↔ γ ∈ parStar J ∧ γ ∈ parStar J' := by
  rw [← smul_c₀_mem_residue_iff, ← smul_c₀_mem_residue_iff, ← smul_c₀_mem_residue_iff,
    ← residue_inter isWeylDistanceBuilding_stdDistance]
  exact Iff.rfl

theorem fibIF_one_eq : ((fibIF 1 : Finset (Fin 4)) : Set (Fin 4)) = {i | i ≠ 0} ∩ {i | i ≠ 1} := by
  ext i
  fin_cases i <;> simp [fibIF]

theorem fibIF_two_eq : ((fibIF 2 : Finset (Fin 4)) : Set (Fin 4)) = {i | i ≠ 0} ∩ {i | i ≠ 3} := by
  ext i
  fin_cases i <;> simp [fibIF]

theorem mem_parIStar_iff
    {d : Fin 5} {γ : GStar} :
    γ ∈ parIStar d ↔ γ ∈ parStar ((fibIF d : Finset (Fin 4)) : Set (Fin 4)) :=
  Iff.rfl

@[expose] def rho1
    (θ : Eam ⧸ Subgroup.zpowers cE' ≃* GStar) : Pc 0 →* GStar :=
  (rho0 θ).comp (Subgroup.inclusion (Pc_le_Eam 0))

theorem rho1_apply
    (θ : Eam ⧸ Subgroup.zpowers cE' ≃* GStar) (p : Pc 0) :
    rho1 θ p = θ (QuotientGroup.mk ⟨p, Pc_le_Eam 0 p.2⟩) := rfl

section Quotient

variable {θ : Eam ⧸ Subgroup.zpowers cE' ≃* GStar} {f : Chamber ≃ C2E6Std.stdChamber}
  (hadj : ∀ (i : Fin Tag.F4.rank) (x y : Chamber), chamberCS.adj i x y ↔
    stdDistanceF4 (f x) (f y) = 1 ∨ stdDistanceF4 (f x) (f y) = (coxeterSystem .F4).simple i)
  (hfeq : ∀ (z : Chamber) (e : Eam), f (chamberMul z e⁻¹) = θ (QuotientGroup.mk e) • f z)
  (hfB : f baseChamber = c₀)

include hadj hfeq hfB in
theorem mem_Pc_iff_of_quotient
    (j : Fin 4) (e : Eam) :
    (e : Dfull) ∈ Pc j ↔ θ (QuotientGroup.mk e) ∈ parStar {i | i ≠ j} := by
  have hL : nativeIdx ⁻¹' {k : Fin Tag.F4.rank | k ≠ j} = {i : Fin 4 | i ≠ j} :=
    Set.ext fun _ => Iff.rfl
  have hres : ∀ z : Chamber, f '' vtx j z = residue ncs stdDistance {i | i ≠ j} (f z) :=
    fun z => (image_residue_chamberCS_of_adj hadj {k : Fin Tag.F4.rank | k ≠ j} z).trans
      (congrArg (fun L => residue ncs stdDistance L (f z)) hL)
  have h1 : chamberOf e⁻¹ = chamberMul baseChamber e⁻¹ := by
    rw [chamberMul_chamberOf, one_mul e⁻¹]
  have h2 : f (chamberOf e⁻¹) = θ (QuotientGroup.mk e) • c₀ := by
    rw [h1, hfeq, hfB]
  have hve : vtx j (chamberOf e⁻¹) = vtx j baseChamber ↔ (e : Dfull) ∈ Pc j := by
    rw [vtx_eq_iff j e⁻¹ 1, one_mul e⁻¹⁻¹, inv_inv e]
  have e1 : f '' vtx j (chamberOf e⁻¹) =
      residue ncs stdDistance {i | i ≠ j} (θ (QuotientGroup.mk e) • c₀) :=
    (hres _).trans (congrArg (residue ncs stdDistance {i | i ≠ j}) h2)
  have e2 : f '' vtx j baseChamber = residue ncs stdDistance {i | i ≠ j} c₀ :=
    (hres _).trans (congrArg (residue ncs stdDistance {i | i ≠ j}) hfB)
  refine hve.symm.trans ((Set.image_injective.mpr f.injective).eq_iff.symm.trans
    ((iff_of_eq (congrArg₂ (· = ·) e1 e2)).trans ?_))
  constructor
  · intro h
    have hm := self_mem_residue (cs := ncs) (δ := stdDistance) {i : Fin 4 | i ≠ j}
      (θ (QuotientGroup.mk e) • c₀)
    rw [h] at hm
    exact (smul_c₀_mem_residue_iff _ _).1 hm
  · intro h
    exact residue_eq_of_mem isWeylDistanceBuilding_stdDistance
      ((smul_c₀_mem_residue_iff _ _).2 h)

include hadj hfeq hfB in
theorem rho1_mem_parStar
    (p : Pc 0) : rho1 θ p ∈ parStar firstJ := by
  rw [firstJ_eq]
  exact (mem_Pc_iff_of_quotient hadj hfeq hfB 0 ⟨p, Pc_le_Eam 0 p.2⟩).1 p.2

include hadj hfeq hfB in
theorem exists_rho1_eq
    {γ : GStar} (hγ : γ ∈ parStar firstJ) : ∃ p : Pc 0, rho1 θ p = γ := by
  obtain ⟨q, hq⟩ := θ.surjective γ
  obtain ⟨e, rfl⟩ := QuotientGroup.mk_surjective q
  rw [firstJ_eq, ← hq] at hγ
  exact ⟨⟨e, (mem_Pc_iff_of_quotient hadj hfeq hfB 0 e).2 hγ⟩, hq⟩

include hadj hfeq hfB in
theorem mem_Pc_one_iff_rho1
    (p : Pc 0) : (p : Dfull) ∈ Pc 1 ↔ rho1 θ p ∈ parIStar 1 := by
  rw [mem_parIStar_iff, fibIF_one_eq, mem_parStar_inter]
  have h0 := (mem_Pc_iff_of_quotient hadj hfeq hfB 0 ⟨p, Pc_le_Eam 0 p.2⟩).1 p.2
  exact (mem_Pc_iff_of_quotient hadj hfeq hfB 1 ⟨p, Pc_le_Eam 0 p.2⟩).trans
    ⟨fun h => ⟨h0, h⟩, fun h => h.2⟩

include hadj hfeq hfB in
theorem mem_Pc_three_iff_rho1
    (p : Pc 0) : (p : Dfull) ∈ Pc 3 ↔ rho1 θ p ∈ parIStar 2 := by
  rw [mem_parIStar_iff, fibIF_two_eq, mem_parStar_inter]
  have h0 := (mem_Pc_iff_of_quotient hadj hfeq hfB 0 ⟨p, Pc_le_Eam 0 p.2⟩).1 p.2
  exact (mem_Pc_iff_of_quotient hadj hfeq hfB 3 ⟨p, Pc_le_Eam 0 p.2⟩).trans
    ⟨fun h => ⟨h0, h⟩, fun h => h.2⟩

include hadj hfeq hfB in
theorem rho1_mem_radStar
    {n : Pc 0} (hn : (n : Dfull) ∈ N1) : rho1 θ n ∈ radStar := by
  set M : Subgroup (Pc 0) := N1.subgroupOf (Pc 0)
  set M' : Subgroup GStar := M.map (rho1 θ)
  have hM'P : M' ≤ parStar firstJ := by
    rintro _ ⟨m, -, rfl⟩
    exact rho1_mem_parStar hadj hfeq hfB m
  have hnormal : (M'.subgroupOf (parStar firstJ)).Normal := by
    refine ⟨fun x hx γ => ?_⟩
    obtain ⟨m, hm, hmx⟩ := Subgroup.mem_subgroupOf.1 hx
    obtain ⟨p, hp⟩ := exists_rho1_eq hadj hfeq hfB γ.2
    rw [Subgroup.mem_subgroupOf]
    refine ⟨p * m * p⁻¹, conj_mem_N1 p.2 hm, ?_⟩
    rw [map_mul, map_mul, map_inv, hp, hmx]
    rfl
  have hpM : IsPGroup 2 M := by
    have hN : IsPGroup 2 N1 := IsPGroup.of_card natCard_N1
    let e : M ≃* N1 := Subgroup.subgroupOfEquivOfLe N1_le_P1
    exact hN.of_equiv e.symm
  have hpM' : IsPGroup 2 (M'.subgroupOf (parStar firstJ)) := by
    let e : M'.subgroupOf (parStar firstJ) ≃* M' := Subgroup.subgroupOfEquivOfLe hM'P
    exact (hpM.map (rho1 θ)).of_equiv e.symm
  have hle := le_pCore_of_normal hnormal hpM'
  rw [pCore_parStar] at hle
  have hmem : (⟨rho1 θ n, rho1_mem_parStar hadj hfeq hfB n⟩ : parStar firstJ) ∈
      M'.subgroupOf (parStar firstJ) :=
    Subgroup.mem_subgroupOf.2 ⟨n, hn, rfl⟩
  exact Subgroup.mem_subgroupOf.1 (hle hmem)

end Quotient

section Pair

variable {θ : Eam ⧸ Subgroup.zpowers cE' ≃* GStar} {k : Jhat}
  (hk0 : cvOf (jhatS k) ≠ cv0) (hk : ¬ cgraph.Adj cv0 (cvOf (jhatS k)))

abbrev q4P (k : Jhat) : Subgroup (Pc 0) := (Q4 k).subgroupOf (Pc 0)

include hk0 hk in
theorem rho1_injOn_q4P :
    Set.InjOn (rho1 θ) (q4P k) := by
  intro x hx y hy h
  have h1 : (QuotientGroup.mk ⟨x, Pc_le_Eam 0 x.2⟩ : Eam ⧸ Subgroup.zpowers cE') =
      QuotientGroup.mk ⟨y, Pc_le_Eam 0 y.2⟩ := θ.injective h
  have h2 := (mk_eq_mk_iff_P1 x y).2 h1
  exact injOn_mk_of_le hk0 hk le_rfl hx hy h2

theorem natCard_radStar : Nat.card radStar = 2 ^ 21 := by
  rw [← card_radStarP]
  exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe radStar_le_parStar).toEquiv).symm

variable {f : Chamber ≃ C2E6Std.stdChamber}
  (hadj : ∀ (i : Fin Tag.F4.rank) (x y : Chamber), chamberCS.adj i x y ↔
    stdDistanceF4 (f x) (f y) = 1 ∨ stdDistanceF4 (f x) (f y) = (coxeterSystem .F4).simple i)
  (hfeq : ∀ (z : Chamber) (e : Eam), f (chamberMul z e⁻¹) = θ (QuotientGroup.mk e) • f z)
  (hfB : f baseChamber = c₀)

include hk0 hk hadj hfeq hfB in
theorem map_cNE_eq_radStar :
    ((cNE k).subgroupOf (Pc 0)).map (rho1 θ) = radStar := by
  have hle : ((cNE k).subgroupOf (Pc 0)).map (rho1 θ) ≤ radStar := by
    rintro _ ⟨n, hn, rfl⟩
    exact rho1_mem_radStar hadj hfeq hfB (cNE_le_N1 hn)
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [natCard_radStar]
  have hinj : Set.InjOn (rho1 θ) ((cNE k).subgroupOf (Pc 0)) := fun x hx y hy h =>
    rho1_injOn_q4P hk0 hk (θ := θ) (show (x : Dfull) ∈ Q4 k from cNE_le_Q4 hx)
      (show (y : Dfull) ∈ Q4 k from cNE_le_Q4 hy) h
  have hcard : Nat.card (((cNE k).subgroupOf (Pc 0)).map (rho1 θ)) =
      Nat.card ((cNE k).subgroupOf (Pc 0)) := by
    have e1 := Nat.card_coe_set_eq ((rho1 θ) '' ((cNE k).subgroupOf (Pc 0) : Set (Pc 0)))
    have e2 := Nat.card_coe_set_eq ((cNE k).subgroupOf (Pc 0) : Set (Pc 0))
    rw [hinj.ncard_image] at e1
    rw [← Subgroup.coe_map] at e1
    exact e1.trans e2.symm
  have hle' : cNE k ≤ Pc 0 := (cNE_le_Q4 (k := k)).trans Q4_le_P1
  rw [hcard, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle').toEquiv, natCard_cNE hk0 hk]

include hk0 hk hadj hfeq hfB in
theorem radStar_le_map_q4P :
    radStar ≤ (q4P k).map (rho1 θ) := by
  rw [← map_cNE_eq_radStar hk0 hk hadj hfeq hfB]
  exact Subgroup.map_mono fun x hx => cNE_le_Q4 hx

include hadj hfeq hfB in
theorem map_le_parStar
    (Q : Subgroup (Pc 0)) : Q.map (rho1 θ) ≤ parStar firstJ := by
  rintro _ ⟨p, -, rfl⟩
  exact rho1_mem_parStar hadj hfeq hfB p

end Pair

end CFSG.Monster.B.TwoA.Amalgam
