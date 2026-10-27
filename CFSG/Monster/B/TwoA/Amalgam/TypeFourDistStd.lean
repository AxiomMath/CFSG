module

public import CFSG.Monster.B.E6.StdF4Pair
public import CFSG.Monster.B.TwoA.Amalgam.EightOrbitsQuot

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Amalgam

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.C2E6Std
open CFSG.LieType.Chevalley.C2E6Std.FieldExtension
open CFSG.LieType.Chevalley.CosetBuilding CFSG.Monster.B.Geometry CFSG.Monster.B.E6.StdF4
open CFSG.Fischer CFSG.Monster CFSG.Monster.B CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Sp8
  CFSG.Monster.B.TwoA.Unitary
open CFSG.LieType.Chevalley.C2E6Overlap (K)
open CFSG.Monster.B.E6.FixedE6 (fixedL formL)
open CFSG.Monster.B.E6.FixedE6Root (rootVecOf a0L rootVecOf_rootInv bijOn_rootVecOf)
open Module
open scoped Pointwise

theorem quotSp_one : quotSp 1 = Tsp := ite_eq_right (by decide)

theorem quotSp_two : quotSp 2 = Rsp := ite_eq_left rfl

theorem flagSub_zero_le_flagSub_two_iff
    (γ γ' : parStar firstJ) :
    flagSub 0 (parLeft γ) ≤ flagSub 2 (parLeft γ') ↔
      ∃ δ : parStar firstJ, (γ : GStar)⁻¹ * δ ∈ parIStar 2 ∧ (γ' : GStar)⁻¹ * δ ∈ parIStar 1 := by
  constructor
  · intro h
    have hR : finrank K (flagSub 0 (parLeft γ)) = 1 := (residueFlag _).finrank_sub 0
    have hT : flagSub 2 (parLeft γ') ∈ isoSubs 2 := flagSub_mem_isoSubs 2 _
    obtain ⟨F, hF0, hF2⟩ := exists_flag_of_le hR hT h
    obtain ⟨p, hp⟩ := QuotientGroup.mk_surjective (residueFlag.symm F)
    have hpF : residueFlag (QuotientGroup.mk p) = F := by rw [hp, Equiv.apply_symm_apply]
    have hpG : (p : ModGL Tag.E6 K) ∈ stdGroup := nativeParabolic_le_stdGroup firstJ p.2
    have hδ : SemidirectProduct.inl (⟨p, hpG⟩ : stdGroup) ∈ parStar firstJ := p.2
    refine ⟨⟨_, hδ⟩, ?_, ?_⟩
    · refine (flagSub_eq_iff_parIStar (d := 2) (Or.inr (Or.inl rfl)) γ ⟨_, hδ⟩).1 ?_
      show flagSub 0 (parLeft γ) = (residueFlag (QuotientGroup.mk p)).sub 0
      rw [hpF, hF0]
    · refine (flagSub_eq_iff_parIStar (d := 1) (Or.inl rfl) γ' ⟨_, hδ⟩).1 ?_
      show flagSub 2 (parLeft γ') = (residueFlag (QuotientGroup.mk p)).sub 2
      rw [hpF, hF2]
  · rintro ⟨δ, h2, h1⟩
    have e2 : flagSub 0 (parLeft γ) = flagSub 0 (parLeft δ) :=
      (flagSub_eq_iff_parIStar (d := 2) (Or.inr (Or.inl rfl)) γ δ).2 h2
    have e1 : flagSub 2 (parLeft γ') = flagSub 2 (parLeft δ) :=
      (flagSub_eq_iff_parIStar (d := 1) (Or.inl rfl) γ' δ).2 h1
    rw [e2, e1]
    exact (residueFlag _).mono (show (0 : Fin 3) ≤ 2 by decide)

theorem mem_leftCoset_inter_iff
    {A B : Subgroup (Pc 0)} (g h : Pc 0) :
    (g • (A : Set (Pc 0)) ∩ h • (B : Set (Pc 0))).Nonempty ↔
      ∃ x : Pc 0, g⁻¹ * x ∈ A ∧ h⁻¹ * x ∈ B := by
  simp only [Set.Nonempty, Set.mem_inter_iff, mem_leftCoset_iff, SetLike.mem_coe]

section Quotient

variable {θ : Eam ⧸ Subgroup.zpowers cE' ≃* GStar} {f : Chamber ≃ C2E6Std.stdChamber}
  (hadj : ∀ (i : Fin Tag.F4.rank) (x y : Chamber), chamberCS.adj i x y ↔
    stdDistanceF4 (f x) (f y) = 1 ∨ stdDistanceF4 (f x) (f y) = (coxeterSystem .F4).simple i)
  (hfeq : ∀ (z : Chamber) (e : Eam), f (chamberMul z e⁻¹) = θ (QuotientGroup.mk e) • f z)
  (hfB : f baseChamber = c₀)

include hadj hfeq hfB in
theorem actP1_Rsp_le_actP1_Tsp_iff
    (g g' : Pc 0) :
    actP1 g Rsp ≤ actP1 g' Tsp ↔ ∃ δ : parStar firstJ,
      (rho1 θ g)⁻¹ * δ ∈ parIStar 2 ∧ (rho1 θ g')⁻¹ * δ ∈ parIStar 1 := by
  have hinc := incidence_iff actP1_Tsp_iff actP1_Rsp_iff (Rsp_le_Hsp.trans Hsp_le_Tsp)
    (by rw [finrank_Rsp, uIso_Tsp.1]; omega) htr_TR g' g
  have hno : ¬ actP1 g' Tsp ≤ actP1 g Rsp := fun h => by
    have h' := Submodule.finrank_mono h
    rw [finrank_actP1, finrank_actP1, finrank_Rsp, uIso_Tsp.1] at h'
    omega
  have key : (∃ x : Pc 0, g'⁻¹ * x ∈ (Pc 1).subgroupOf (Pc 0) ∧
      g⁻¹ * x ∈ (Pc 3).subgroupOf (Pc 0)) ↔ ∃ δ : parStar firstJ,
        (rho1 θ g)⁻¹ * δ ∈ parIStar 2 ∧ (rho1 θ g')⁻¹ * δ ∈ parIStar 1 := by
    constructor
    · rintro ⟨x, hx1, hx3⟩
      have h1 := (mem_Pc_one_iff_rho1 hadj hfeq hfB (g'⁻¹ * x)).1
        (Subgroup.mem_subgroupOf.1 hx1)
      have h3 := (mem_Pc_three_iff_rho1 hadj hfeq hfB (g⁻¹ * x)).1
        (Subgroup.mem_subgroupOf.1 hx3)
      rw [map_mul, map_inv] at h1 h3
      exact ⟨⟨_, rho1_mem_parStar hadj hfeq hfB x⟩, h3, h1⟩
    · rintro ⟨δ, h2, h1⟩
      obtain ⟨x, hx⟩ := exists_rho1_eq hadj hfeq hfB δ.2
      refine ⟨x, Subgroup.mem_subgroupOf.2 ((mem_Pc_one_iff_rho1 hadj hfeq hfB _).2 ?_),
        Subgroup.mem_subgroupOf.2 ((mem_Pc_three_iff_rho1 hadj hfeq hfB _).2 ?_)⟩
      · rw [map_mul, map_inv, hx]
        exact h1
      · rw [map_mul, map_inv, hx]
        exact h2
  rw [← key, ← mem_leftCoset_inter_iff, hinc]
  exact ⟨fun h => Or.inr h, fun h => h.resolve_left hno⟩

include hadj hfeq hfB in
theorem commute_iff_nquot_le
    {p q : GStar} (hp : p ∈ fibOrbit 1) (hq : q ∈ fibOrbit 2) :
    Commute p q ↔ nquot θ 2 q ≤ nquot θ 1 p := by
  obtain ⟨g', rfl⟩ := exists_rho1_conj hadj hfeq hfB hp
  obtain ⟨g, rfl⟩ := exists_rho1_conj hadj hfeq hfB hq
  have hγ := rho1_mem_parStar hadj hfeq hfB g
  have hγ' := rho1_mem_parStar hadj hfeq hfB g'
  rw [commute_iff_fibSub_le hp hq, nquot_conj hadj hfeq hfB (Or.inl rfl),
    nquot_conj hadj hfeq hfB (Or.inr (Or.inl rfl)), quotSp_one, quotSp_two,
    actP1_Rsp_le_actP1_Tsp_iff hadj hfeq hfB, fibSub_conj_one ⟨_, hγ'⟩,
    fibSub_conj_two ⟨_, hγ⟩, flagSub_zero_le_flagSub_two_iff]

end Quotient

theorem orderOf_mul_eq_three_iff
    (x y : Pts) :
    orderOf ((x : stdGroup) * y) = 3 ↔ relIdx x y = 4 := by
  obtain ⟨k, i, hx, hy⟩ := CFSG.Monster.B.E6.FixedE6Root.exists_conj_pair x.2 y.2
  have hrel : relPt x y = i := by rw [hx, hy, relPt_conj_pair]
  have hord : orderOf ((x : stdGroup) * y) = repOrder i := by
    rw [hx, hy, show k * rootInv * k⁻¹ * (k * repPoint i * k⁻¹) =
      MulAut.conj k (rootInv * repPoint i) by rw [MulAut.conj_apply]; group,
      MulEquiv.orderOf_eq, orderOf_rootInv_mul_repPoint]
  rw [hord, Fin.ext_iff, val_relIdx, hrel]
  fin_cases i <;> decide

theorem orderOf_rootInv_mul_eq_three_iff
    {z : stdGroup} (hz : z ∈ rootClass) :
    orderOf (rootInv * z) = 3 ↔ SemidirectProduct.inl z ∈ fibOrbit 4 := by
  rw [mem_fibOrbit_iff hz 4]
  have h := orderOf_mul_eq_three_iff basePt ⟨z, hz⟩
  rw [Fin.ext_iff, val_relIdx] at h
  exact h

theorem formL_a0L_rootVecOf_of_mem_fibOrbit_four
    {z : stdGroup} (hz : z ∈ rootClass)
    (h4 : SemidirectProduct.inl z ∈ fibOrbit 4) : formL a0L (rootVecOf z) = 1 := by
  rw [← rootVecOf_rootInv]
  exact (formL_rootVecOf_eq_one_iff (IsConj.refl _) hz).2
    ((orderOf_rootInv_mul_eq_three_iff hz).2 h4)

theorem ncard_orderOf_mul_eq_three
    {A : Set GStar} (hA : A ⊆ fibOrbit 1)
    (hU : ∀ p ∈ A, conjOrbit radStar p ⊆ A) {y : stdGroup} (hy : y ∈ rootClass)
    (h4 : SemidirectProduct.inl y ∈ fibOrbit 4) :
    2 * {p | p ∈ A ∧ orderOf (p.left * y) = 3}.ncard = A.ncard := by
  set S := {p | p ∈ A ∧ orderOf (p.left * y) = 3} with hS
  have hroot : ∀ p ∈ A, p.left ∈ rootClass ∧ p = SemidirectProduct.inl p.left := by
    intro p hp
    obtain ⟨z, hz, rfl⟩ := exists_inl_of_mem_fibOrbit (hA hp)
    exact ⟨hz, rfl⟩
  have hΦinj : Set.InjOn (fun p : GStar => rootVecOf p.left) A := by
    intro p hp q hq h
    obtain ⟨hp1, hp2⟩ := hroot p hp
    obtain ⟨hq1, hq2⟩ := hroot q hq
    rw [hp2, hq2, bijOn_rootVecOf.injOn hp1 hq1 h]
  have hform : ∀ p ∈ A,
      (orderOf (p.left * y) = 3 ↔ formL (rootVecOf p.left) (rootVecOf y) = 1) := fun p hp =>
    (formL_rootVecOf_eq_one_iff (hroot p hp).1 hy).symm
  have ha0 : formL a0L (rootVecOf y) = 1 := formL_a0L_rootVecOf_of_mem_fibOrbit_four hy h4
  have hpair : ∀ p ∈ A, ∃ p' ∈ A, rootVecOf p'.left = rootVecOf p.left + a0L := by
    intro p hp
    have hmem : rootVecOf p.left + a0L ∈
        (fun y : GStar => rootVecOf y.left) '' conjOrbit radStar p := by
      rw [image_rootVec_conjOrbit (hA hp)]
      exact Or.inr rfl
    obtain ⟨p', hp', e⟩ := hmem
    exact ⟨p', hU p hp hp', e⟩
  have hshift : ∀ p ∈ A, ∀ p' ∈ A, rootVecOf p'.left = rootVecOf p.left + a0L →
      (p' ∈ S ↔ p ∉ S) := by
    intro p hp p' hp' e
    have hb : formL (rootVecOf p'.left) (rootVecOf y) =
        formL (rootVecOf p.left) (rootVecOf y) + 1 := by
      rw [e, map_add, LinearMap.add_apply, ha0]
    constructor
    · intro h' h
      have h1 := (hform p' hp').1 h'.2
      have h2 := (hform p hp).1 h.2
      rw [hb, h2] at h1
      exact absurd h1 (by decide)
    · intro h
      refine ⟨hp', (hform p' hp').2 ?_⟩
      rw [hb]
      have h2 : formL (rootVecOf p.left) (rootVecOf y) ≠ 1 := fun h2 =>
        h ⟨hp, (hform p hp).2 h2⟩
      generalize formL (rootVecOf p.left) (rootVecOf y) = b at h2 ⊢
      revert b
      decide
  have h2a : ∀ a : fixedL, a + a0L + a0L = a := fun a => by
    rw [add_assoc, ← two_smul (ZMod 2) a0L, show (2 : ZMod 2) = 0 from rfl, zero_smul, add_zero]
  have hτ : (fun a => a + a0L) '' ((fun p : GStar => rootVecOf p.left) '' S) =
      (fun p : GStar => rootVecOf p.left) '' (A \ S) := by
    ext b
    constructor
    · rintro ⟨_, ⟨p, hpS, rfl⟩, rfl⟩
      obtain ⟨p', hp'A, hp'⟩ := hpair p hpS.1
      exact ⟨p', ⟨hp'A, fun h => (hshift p hpS.1 p' hp'A hp').1 h hpS⟩, hp'⟩
    · rintro ⟨q, ⟨hqA, hqS⟩, rfl⟩
      obtain ⟨q', hq'A, hq'⟩ := hpair q hqA
      refine ⟨_, ⟨q', (hshift q hqA q' hq'A hq').2 hqS, rfl⟩, ?_⟩
      show rootVecOf q'.left + a0L = rootVecOf q.left
      rw [hq', h2a]
  have hSA : S ⊆ A := fun p hp => hp.1
  have e1 : ((fun p : GStar => rootVecOf p.left) '' S).ncard = S.ncard :=
    (hΦinj.mono hSA).ncard_image
  have e2 : ((fun p : GStar => rootVecOf p.left) '' (A \ S)).ncard = (A \ S).ncard :=
    (hΦinj.mono Set.sdiff_subset).ncard_image
  have e3 : ((fun a => a + a0L) '' ((fun p : GStar => rootVecOf p.left) '' S)).ncard =
      ((fun p : GStar => rootVecOf p.left) '' S).ncard :=
    Set.ncard_image_of_injective _ (add_left_injective a0L)
  have e4 := Set.ncard_sdiff_add_ncard_of_subset hSA (Set.toFinite A)
  rw [hτ, e2, e1] at e3
  omega

end CFSG.Monster.B.TwoA.Amalgam
