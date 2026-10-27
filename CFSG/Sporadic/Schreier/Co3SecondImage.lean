module

public import CFSG.Sporadic.Schreier.Co3Generation
public import CFSG.Sporadic.Schreier.Co3SecondImageCheck
public import CFSG.Certificates.SubgroupEnumeration

public noncomputable section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Sporadic.Schreier.Co3

open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.Sporadic.Schreier.Co3.Native CFSG.Sporadic.Mathieu CFSG.Blueprint

theorem co3Z_mem_M1 :
    co3Z ∈ co3M1 := by
  rw [co3M1_eq_centralizer]
  refine Subgroup.mem_inf.2 ⟨co3Z_mem_P, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
  exact (Subgroup.mem_centralizer_singleton_iff.1 (co3M_le_centralizer co3Tt_mem_M)).symm

@[expose] def co3ZM1 :
    co3M1 := ⟨co3Z, co3Z_mem_M1⟩

theorem co3D0_le_M1 :
    co3D0 ≤ co3M1 := fun _ h => (Subgroup.mem_inf.1 (co3D0_le h)).2

@[expose] def co3D0Img :
    Subgroup (Equiv.Perm (Fin 12)) := (co3D0.subgroupOf co3M1).map co3Kappa1

abbrev co3D0ImgGens :
    Set (Equiv.Perm (Fin 12)) := Set.range fun k : Fin 5 => co3D0K k

theorem co3D0K_mem
    (k : Fin 5) : co3D0K k ∈ co3D0Img := by
  refine ⟨co3D0M1 k k.2, ?_, ?_⟩
  · rw [SetLike.mem_coe, Subgroup.mem_subgroupOf]
    exact Subgroup.subset_closure ⟨k, k.2, rfl⟩
  · rw [co3D0K, dite_eq_left k.2]

theorem co3Kappa1_mem_closure
    {d : Equiv.Perm (Fin 276)} (hd : d ∈ co3D0) (hd1 : d ∈ co3M1) :
    co3Kappa1 ⟨d, hd1⟩ ∈ Subgroup.closure co3D0ImgGens := by
  rw [co3D0] at hd
  refine Subgroup.closure_induction (p := fun d _ => ∀ hd1 : d ∈ co3M1,
    co3Kappa1 ⟨d, hd1⟩ ∈ Subgroup.closure co3D0ImgGens) ?_ ?_ ?_ ?_ hd hd1
  · rintro _ ⟨k, hk, rfl⟩ h1
    apply Subgroup.subset_closure
    refine ⟨⟨k, hk⟩, ?_⟩
    show co3D0K k = co3Kappa1 ⟨co3D0Gen k, h1⟩
    rw [co3D0K, dite_eq_left hk]
    rfl
  · intro h1
    have e : (⟨1, h1⟩ : co3M1) = 1 := rfl
    rw [e, map_one]
    exact Subgroup.one_mem _
  · intro x y hx hy ihx ihy h1
    have hx1 : x ∈ co3M1 := co3D0_le_M1 (by rw [co3D0]; exact hx)
    have hy1 : y ∈ co3M1 := co3D0_le_M1 (by rw [co3D0]; exact hy)
    have e : (⟨x * y, h1⟩ : co3M1) = ⟨x, hx1⟩ * ⟨y, hy1⟩ := rfl
    rw [e, map_mul]
    exact Subgroup.mul_mem _ (ihx hx1) (ihy hy1)
  · intro x hx ihx h1
    have hx1 : x ∈ co3M1 := co3D0_le_M1 (by rw [co3D0]; exact hx)
    have e : (⟨x⁻¹, h1⟩ : co3M1) = (⟨x, hx1⟩ : co3M1)⁻¹ := rfl
    rw [e, map_inv]
    exact Subgroup.inv_mem _ (ihx hx1)

theorem co3D0Img_eq_closure :
    co3D0Img = Subgroup.closure co3D0ImgGens := by
  apply le_antisymm
  · rintro _ ⟨⟨d, hd1⟩, hd, rfl⟩
    exact co3Kappa1_mem_closure (Subgroup.mem_subgroupOf.1 hd) hd1
  · rw [Subgroup.closure_le]
    rintro _ ⟨k, rfl⟩
    exact co3D0K_mem k

@[expose] def co3D0ImgElt (i : ℕ) : Equiv.Perm (Fin 12) := permOfArr 12 co3D0ImgRec.1[i]!

theorem rep_co3D0ImgElt
    {i : ℕ} (hi : i < 192) : Rep 12 co3D0ImgRec.1[i]! (co3D0ImgElt i) :=
  (rep_permOfArr (co3D0Img_check.2.2.2.1 i hi)).1

theorem co3D0ImgElt_zero : co3D0ImgElt 0 = 1 :=
  eq_of_eqA (rep_co3D0ImgElt (by norm_num)) rep_idA co3D0Img_check.2.1

theorem co3D0ImgElt_succ
    {i : ℕ} (hi : i < 192) (h1 : 1 ≤ i) :
    co3D0ImgElt i = co3D0K co3D0ImgRec.2.2[i]! * co3D0ImgElt co3D0ImgRec.2.1[i]! := by
  obtain ⟨hpar, hlab, heq⟩ := co3D0Img_check.2.2.1 i hi h1
  exact eq_of_eqA (rep_co3D0ImgElt hi)
    (rep_compA (rep_co3D0Kappa1 hlab) (rep_co3D0ImgElt (by omega))) heq

theorem co3D0ImgElt_mem_closure
    (i : ℕ) :
    i < 192 → co3D0ImgElt i ∈ Subgroup.closure co3D0ImgGens := by
  refine Nat.strong_induction_on i fun i ih hi => ?_
  rcases Nat.eq_zero_or_pos i with rfl | h1
  · rw [co3D0ImgElt_zero]
    exact Subgroup.one_mem _
  · obtain ⟨hpar, hlab, -⟩ := co3D0Img_check.2.2.1 i hi h1
    rw [co3D0ImgElt_succ hi h1]
    exact Subgroup.mul_mem _ (Subgroup.subset_closure ⟨⟨_, hlab⟩, rfl⟩) (ih _ hpar (by omega))

@[expose] def co3D0ImgSet : Set (Equiv.Perm (Fin 12)) := Set.range fun i : Fin 192 => co3D0ImgElt i

theorem co3D0ImgSet_eq :
    co3D0ImgSet = (Subgroup.closure co3D0ImgGens : Set (Equiv.Perm (Fin 12))) := by
  refine subgroup_enumeration_completeness_of_transitions co3D0ImgGens co3D0ImgSet
    ⟨0, co3D0ImgElt_zero⟩ ?_ ?_ ?_
  · rintro _ ⟨i, rfl⟩
    exact SubgroupEnumeration.wordWitness_of_mem_closure (co3D0ImgElt_mem_closure i i.2)
  · rintro _ ⟨k, rfl⟩ _ ⟨i, rfl⟩
    obtain ⟨j, hj, he⟩ := co3D0Img_check.2.2.2.2.2.1 k k.2 i i.2
    exact ⟨⟨j, hj⟩, (eq_of_eqA (rep_compA (rep_co3D0Kappa1 k.2) (rep_co3D0ImgElt i.2))
      (rep_co3D0ImgElt hj) he).symm⟩
  · rintro _ ⟨k, rfl⟩ _ ⟨i, rfl⟩
    obtain ⟨j, hj, he⟩ := co3D0Img_check.2.2.2.2.2.2.1 k k.2 i i.2
    have hinv := rep_inv_of_isInvA (rep_co3D0Kappa1 k.2) (co3D0Img_check.2.2.2.2.1 k k.2)
    exact ⟨⟨j, hj⟩, (eq_of_eqA (rep_compA hinv (rep_co3D0ImgElt i.2)) (rep_co3D0ImgElt hj) he).symm⟩

theorem co3D0ImgElt_injective :
    Function.Injective fun i : Fin 192 => co3D0ImgElt i := by
  intro i j h
  by_contra hne
  rcases Nat.lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with hlt | hlt
  · have h' := co3D0Img_check.2.2.2.2.2.2.2 j j.2 i hlt
    rw [← Bool.not_eq_true, eqA_iff (rep_co3D0ImgElt j.2) (rep_co3D0ImgElt i.2)] at h'
    exact h' h.symm
  · have h' := co3D0Img_check.2.2.2.2.2.2.2 i i.2 j hlt
    rw [← Bool.not_eq_true, eqA_iff (rep_co3D0ImgElt i.2) (rep_co3D0ImgElt j.2)] at h'
    exact h' h

theorem card_co3D0Img :
    Nat.card co3D0Img = 192 := by
  rw [co3D0Img_eq_closure, ← SetLike.coe_sort_coe, ← co3D0ImgSet_eq, co3D0ImgSet,
    Nat.card_range_of_injective co3D0ImgElt_injective, Nat.card_fin]

theorem co3ZM1_comm
    (k : ℕ) (hk : k < 5) : co3ZM1 * co3D0M1 k hk = co3D0M1 k hk * co3ZM1 := by
  apply Subtype.ext
  exact (Subgroup.mem_centralizer_singleton_iff.1
    (co3M_le_centralizer (Subgroup.mem_inf.1 (co3D0Gen_mem hk)).1)).symm

theorem co3Kappa1_z_comm
    (k : ℕ) (hk : k < 5) :
    co3Kappa1 co3ZM1 * co3D0K k = co3D0K k * co3Kappa1 co3ZM1 := by
  rw [co3D0K, dite_eq_left hk, ← map_mul, ← map_mul, co3ZM1_comm k hk]

theorem co3Z_ne_Tt :
    co3Z ≠ co3Tt := by
  intro h
  obtain ⟨p, hpz, hpt, hp⟩ : ∃ p ∈ co3IzNat, p ∉ co3ItNat ∧ p < 276 := by decide
  have h1 := (co3Iz_spec ⟨p, hp⟩).1 hpz
  rw [h] at h1
  exact hpt ((co3It_spec ⟨p, hp⟩).2 h1)

theorem co3Kappa1_z_ne_one :
    co3Kappa1 co3ZM1 ≠ 1 := by
  intro h
  have hmem : co3ZM1 ∈ co3Kappa1.ker := h
  rw [co3Kappa1_ker, Subgroup.mem_zpowers_iff] at hmem
  obtain ⟨k, hk⟩ := hmem
  have hk2 : co3TtM1 ^ k = co3TtM1 ^ (k % 2) := by
    rw [← zpow_mod_orderOf, orderOf_co3TtM1]
    norm_num
  rw [hk2] at hk
  rcases Int.emod_two_eq_zero_or_one k with h0 | h0
  · rw [h0, zpow_zero] at hk
    exact co3Z_ne_one (congrArg Subtype.val hk).symm
  · rw [h0, zpow_one] at hk
    exact co3Z_ne_Tt (congrArg Subtype.val hk).symm

theorem mem_co3D0ImgCent
    (x : Equiv.Perm (Fin 12)) :
    x ∈ Subgroup.centralizer (co3D0Img : Set (Equiv.Perm (Fin 12))) ⊓ NativeSporadic.M12 ↔
      x ∈ NativeSporadic.M12 ∧ ∀ k < 5, x * co3D0K k = co3D0K k * x := by
  rw [Subgroup.mem_inf, co3D0Img_eq_closure, Subgroup.centralizer_closure,
    Subgroup.mem_centralizer_iff]
  constructor
  · rintro ⟨h, hx⟩
    exact ⟨hx, fun k hk => (h _ ⟨⟨k, hk⟩, rfl⟩).symm⟩
  · rintro ⟨hx, h⟩
    refine ⟨?_, hx⟩
    rintro _ ⟨k, rfl⟩
    exact (h k k.2).symm

theorem co3Kappa1_z_mem_M12 :
    co3Kappa1 co3ZM1 ∈ NativeSporadic.M12 := by
  rw [← co3Kappa1_range]
  exact ⟨co3ZM1, rfl⟩

theorem co3D0Img_centralizer :
    ((Subgroup.centralizer (co3D0Img : Set (Equiv.Perm (Fin 12))) ⊓ NativeSporadic.M12 :
      Subgroup (Equiv.Perm (Fin 12))) : Set (Equiv.Perm (Fin 12))) = {1, co3Kappa1 co3ZM1} := by
  set S := ((Subgroup.centralizer (co3D0Img : Set (Equiv.Perm (Fin 12))) ⊓ NativeSporadic.M12 :
    Subgroup (Equiv.Perm (Fin 12))) : Set (Equiv.Perm (Fin 12))) with hS
  have hS' : S = {x | x ∈ NativeSporadic.M12 ∧ ∀ k < 5, x * co3D0K k = co3D0K k * x} := by
    ext x
    rw [hS, SetLike.mem_coe, mem_co3D0ImgCent]
    rfl
  have hsub : ({1, co3Kappa1 co3ZM1} : Set (Equiv.Perm (Fin 12))) ⊆ S := by
    rw [hS']
    rintro x (rfl | rfl)
    · exact ⟨NativeSporadic.M12.one_mem, fun k _ => by rw [one_mul, mul_one]⟩
    · exact ⟨co3Kappa1_z_mem_M12, fun k hk => co3Kappa1_z_comm k hk⟩
  have hcard : Nat.card S = 2 := by
    rw [hS', ← card_co3D0Cent]
    exact Nat.card_congr (Equiv.subtypeSubtypeEquivSubtypeInter (· ∈ NativeSporadic.M12)
      fun x => ∀ k < 5, x * co3D0K k = co3D0K k * x).symm
  have h2 : S.ncard = 2 := by rw [← Nat.card_coe_set_eq, hcard]
  exact (Set.eq_of_subset_of_ncard_le hsub
    (by rw [h2, Set.ncard_pair (Ne.symm co3Kappa1_z_ne_one)]) (Set.toFinite _)).symm

theorem co3D0Img_le_M12 :
    co3D0Img ≤ NativeSporadic.M12 := by
  rw [← co3Kappa1_range]
  rintro _ ⟨y, -, rfl⟩
  exact ⟨y, rfl⟩

theorem co3D0Img_sylow :
    ∃ S : Sylow 2 NativeSporadic.M12,
    (S : Subgroup NativeSporadic.M12).map NativeSporadic.M12.subtype ≤ co3D0Img := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set H := co3D0Img.subgroupOf NativeSporadic.M12
  have hH : Nat.card H = 192 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe co3D0Img_le_M12).toEquiv, card_co3D0Img]
  obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime (G := H) 2 (n := 6)
    (by rw [hH]; norm_num)
  set K' : Subgroup NativeSporadic.M12 := K.map H.subtype
  have hK' : Nat.card K' = 2 ^ 6 := by
    rw [← hK]
    exact (Nat.card_congr (K.equivMapOfInjective H.subtype H.subtype_injective).toEquiv).symm
  have hp : IsPGroup 2 K' := IsPGroup.of_card hK'
  have hidx : K'.index = 1485 := by
    have h := K'.card_mul_index
    rw [hK', m12_card] at h
    omega
  refine ⟨hp.toSylow (by rw [hidx]; decide), ?_⟩
  rw [IsPGroup.toSylow_coe]
  rintro _ ⟨x, ⟨y, -, rfl⟩, rfl⟩
  exact Subgroup.mem_subgroupOf.1 y.2

theorem CTUC_Co3_second_centralizer_intersection_image :
    co3Z ∈ co3M1 ∧ Nat.card co3D0Img = 192 ∧
    ((Subgroup.centralizer (co3D0Img : Set (Equiv.Perm (Fin 12))) ⊓ NativeSporadic.M12 :
      Subgroup (Equiv.Perm (Fin 12))) : Set (Equiv.Perm (Fin 12))) = {1, co3Kappa1 co3ZM1} ∧
    co3Kappa1 co3ZM1 ≠ 1 ∧ co3D0Img ≤ NativeSporadic.M12 ∧
    ∃ S : Sylow 2 NativeSporadic.M12,
      (S : Subgroup NativeSporadic.M12).map NativeSporadic.M12.subtype ≤ co3D0Img :=
  ⟨co3Z_mem_M1, card_co3D0Img, co3D0Img_centralizer, co3Kappa1_z_ne_one, co3D0Img_le_M12,
    co3D0Img_sylow⟩

end CFSG.Sporadic.Schreier.Co3
