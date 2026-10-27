module

public import CFSG.RankThree.PartTwo.Sec4.Ronan148LT1G2

public section

namespace CFSG.RankThree.PartTwo.Sec4.Ronan148L

section Gen

variable {G : Type} [Group G] [Finite G]

theorem exists_le_of_equiv_comm {T : Type} [Group T] {C Y : Subgroup G} (eC : ↥C ≃* T)
    {Q : Subgroup T} (hcomm : ∀ x y : T, x * y * x⁻¹ * y⁻¹ ∈ Q) (hYC : Y ≤ C)
    (hp : Group.IsPerfect ↥Y) : ∃ N : Subgroup G, N ≤ C ∧ Y ≤ N ∧ Nonempty (↥N ≃* ↥Q) := by
  refine ⟨(Q.comap eC.toMonoidHom).map C.subtype, Subgroup.map_subtype_le _, ?_,
    ⟨((Q.comap eC.toMonoidHom).equivMapOfInjective C.subtype C.subtype_injective).symm.trans
      (RonanK429Lie.comapEquiv eC Q)⟩⟩
  exact le_of_commutators_mem hYC hp fun x hx y hy => by
    refine ⟨⟨x, hx⟩ * ⟨y, hy⟩ * (⟨x, hx⟩ : ↥C)⁻¹ * (⟨y, hy⟩ : ↥C)⁻¹, ?_, rfl⟩
    show eC _ ∈ Q
    rw [map_mul, map_mul, map_mul, map_inv, map_inv]
    exact hcomm _ _

theorem eq_bot_of_equiv_comm {T : Type} [Group T] {C Y : Subgroup G} (eC : ↥C ≃* T)
    {Q : Subgroup T} (hQ : CFSG.IsQuasisimple ↥Q) (h3Q : 3 ∣ Nat.card Q)
    (hcomm : ∀ x y : T, x * y * x⁻¹ * y⁻¹ ∈ Q) (hYC : Y ≤ C)
    (hsub : (Y.subgroupOf C).IsSubnormal) (hp : Group.IsPerfect ↥Y)
    (h3 : ¬ 3 ∣ Nat.card Y) : Y = ⊥ := by
  obtain ⟨N, hNC, hYN, ⟨eN⟩⟩ := exists_le_of_equiv_comm eC hcomm hYC hp
  have hNq : CFSG.IsQuasisimple ↥N := CFSG.LocalCores.isQuasisimple_of_mulEquiv eN.symm hQ
  have h3N : 3 ∣ Nat.card N := by
    rw [Nat.card_congr eN.toEquiv]
    exact h3Q
  exact eq_bot_of_le_quasisimple hYN hNC hsub hNq h3N hp h3

theorem eq_bot_of_equiv_comm_simple {T : Type} [Group T] {C Y : Subgroup G} (eC : ↥C ≃* T)
    {Q : Subgroup T} (hQ : IsSimpleGroup ↥Q) (h3Q : 3 ∣ Nat.card Q)
    (hcomm : ∀ x y : T, x * y * x⁻¹ * y⁻¹ ∈ Q) (hYC : Y ≤ C)
    (hsub : (Y.subgroupOf C).IsSubnormal) (hp : Group.IsPerfect ↥Y)
    (h3 : ¬ 3 ∣ Nat.card Y) : Y = ⊥ := by
  obtain ⟨N, hNC, hYN, ⟨eN⟩⟩ := exists_le_of_equiv_comm eC hcomm hYC hp
  have hNs : IsSimpleGroup N := (MulEquiv.isSimpleGroup_congr eN).2 hQ
  by_contra hne
  have hYN' : Y = N := RonanK429Lie.eq_of_subnormal_of_le_simple hYN hNC hsub hNs hne
  apply h3
  rw [hYN', Nat.card_congr eN.toEquiv]
  exact h3Q

theorem eq_bot_of_le_solvable {Y M : Subgroup G} (hYM : Y ≤ M) (hM : Group.IsSolvable ↥M)
    (hp : Group.IsPerfect ↥Y) : Y = ⊥ := by
  haveI := hM
  haveI : Group.IsSolvable ↥Y :=
    Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hYM)
      (Subgroup.inclusion_injective hYM)
  by_contra hne
  haveI : Nontrivial ↥Y := (Subgroup.nontrivial_iff_ne_bot Y).mpr hne
  exact Group.IsPerfect.not_isSolvable ↥Y inferInstance

theorem eq_bot_of_equiv_comm_solvable {T : Type} [Group T] {C Y : Subgroup G} (eC : ↥C ≃* T)
    {Q : Subgroup T} (hQ : Group.IsSolvable ↥Q) (hcomm : ∀ x y : T, x * y * x⁻¹ * y⁻¹ ∈ Q)
    (hYC : Y ≤ C) (hp : Group.IsPerfect ↥Y) : Y = ⊥ := by
  obtain ⟨N, -, hYN, ⟨eN⟩⟩ := exists_le_of_equiv_comm eC hcomm hYC hp
  haveI := hQ
  have hN : Group.IsSolvable ↥N := solvable_of_surjective (f := eN.symm.toMonoidHom)
    eN.symm.surjective
  exact eq_bot_of_le_solvable hYN hN hp

theorem eq_bot_of_equiv_quasisimple {T : Type} [Group T] {C Y : Subgroup G} (eC : ↥C ≃* T)
    (hT : CFSG.IsQuasisimple T) (h3T : 3 ∣ Nat.card T) (hYC : Y ≤ C)
    (hsub : (Y.subgroupOf C).IsSubnormal) (hp : Group.IsPerfect ↥Y)
    (h3 : ¬ 3 ∣ Nat.card Y) : Y = ⊥ := by
  have hC : CFSG.IsQuasisimple ↥C := CFSG.LocalCores.isQuasisimple_of_mulEquiv eC.symm hT
  have h3C : 3 ∣ Nat.card C := by
    rw [Nat.card_congr eC.toEquiv]
    exact h3T
  exact eq_bot_of_le_quasisimple hYC le_rfl hsub hC h3C hp h3

theorem eq_bot_of_equiv_simple {T : Type} [Group T] {C Y : Subgroup G} (eC : ↥C ≃* T)
    (hT : IsSimpleGroup T) (h3T : 3 ∣ Nat.card T) (hYC : Y ≤ C)
    (hsub : (Y.subgroupOf C).IsSubnormal) (h3 : ¬ 3 ∣ Nat.card Y) : Y = ⊥ := by
  have hCs : IsSimpleGroup C := (MulEquiv.isSimpleGroup_congr eC).2 hT
  by_contra hne
  have hYC' : Y = C := RonanK429Lie.eq_of_subnormal_of_le_simple hYC le_rfl hsub hCs hne
  apply h3
  rw [hYC', Nat.card_congr eC.toEquiv]
  exact h3T

end Gen

end CFSG.RankThree.PartTwo.Sec4.Ronan148L
