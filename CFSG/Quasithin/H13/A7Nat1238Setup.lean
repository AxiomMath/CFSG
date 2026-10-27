module

public import CFSG.Quasithin.H13.A7NatSixLocal

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13.A7

open Equiv Equiv.Perm Subgroup CFSG.Open CFSG.Quasithin CFSG.Quasithin.SteinbergCB
open scoped commutatorElement

@[expose] def vecFS : Fin 7 → ZMod 2 := fun i => if i = 5 ∨ i = 6 then 1 else 0

theorem vecFS_mem : vecFS ∈ evenWeight 7 := by
  rw [mem_evenWeight]
  decide

theorem hammingNorm_vecFS : hammingNorm vecFS = 2 := by
  decide

theorem permAct7_vecFS_iff (σ : Perm (Fin 7)) :
    permAct7 σ vecFS = vecFS ↔ (σ 5 = 5 ∧ σ 6 = 6) ∨ (σ 5 = 6 ∧ σ 6 = 5) :=
  permAct7_fix_iff_of_weight_two (by decide) hammingNorm_vecFS rfl rfl σ

@[expose] def altFive : Subgroup (alternatingGroup (Fin 7)) where
  carrier := {σ | (σ : Perm (Fin 7)) 5 = 5 ∧ (σ : Perm (Fin 7)) 6 = 6}
  mul_mem' {a b} ha hb := by
    simp only [Set.mem_ofPred_eq, Subgroup.coe_mul, Perm.mul_apply] at ha hb ⊢
    rw [hb.1, ha.1, hb.2, ha.2]
    exact ⟨rfl, rfl⟩
  one_mem' := ⟨rfl, rfl⟩
  inv_mem' {a} ha := by
    simp only [Set.mem_ofPred_eq, Subgroup.coe_inv] at ha ⊢
    exact ⟨(Perm.inv_eq_iff_eq).2 ha.1.symm, (Perm.inv_eq_iff_eq).2 ha.2.symm⟩

theorem mem_altFive {σ : alternatingGroup (Fin 7)} :
    σ ∈ altFive ↔ (σ : Perm (Fin 7)) 5 = 5 ∧ (σ : Perm (Fin 7)) 6 = 6 := Iff.rfl

theorem five_le_seven : 5 ≤ 7 := by norm_num

@[expose] noncomputable def altLift5 :
    ↥(alternatingGroup (Fin 5)) →* ↥(alternatingGroup (Fin 7)) :=
  ((Equiv.Perm.viaEmbeddingHom (Fin.castLEEmb five_le_seven)).comp
      (alternatingGroup (Fin 5)).subtype).codRestrict (alternatingGroup (Fin 7)) fun σ => by
    have h := σ.2
    rw [Equiv.Perm.mem_alternatingGroup] at h ⊢
    have key : Equiv.Perm.sign (Equiv.Perm.viaEmbeddingHom
        (Fin.castLEEmb five_le_seven) (σ : Equiv.Perm (Fin 5))) =
        Equiv.Perm.sign (σ : Equiv.Perm (Fin 5)) := by
      classical
      rw [Equiv.Perm.viaEmbeddingHom_apply, Equiv.Perm.viaEmbedding]
      convert Equiv.Perm.sign_extendDomain (σ : Equiv.Perm (Fin 5))
        (Equiv.ofInjective (Fin.castLEEmb five_le_seven).1
          (Fin.castLEEmb five_le_seven).2)
    exact key.trans h

theorem altLift5_injective : Function.Injective altLift5 := by
  intro a b h
  apply Subtype.ext
  apply Equiv.Perm.viaEmbeddingHom_injective (Fin.castLEEmb five_le_seven)
  exact congrArg Subtype.val h

theorem altLift5_apply_of_ge (σ : alternatingGroup (Fin 5)) {j : Fin 7} (hj : 5 ≤ (j : ℕ)) :
    (altLift5 σ : Perm (Fin 7)) j = j := by
  classical
  show Equiv.Perm.viaEmbedding (σ : Perm (Fin 5)) (Fin.castLEEmb five_le_seven) j = j
  apply Equiv.Perm.viaEmbedding_apply_of_notMem
  rintro ⟨i, hi⟩
  have := i.2
  have h6 : ((Fin.castLEEmb five_le_seven : Fin 5 ↪ Fin 7) i : ℕ) = i := rfl
  rw [hi] at h6
  omega

theorem altLift5_mem (σ : alternatingGroup (Fin 5)) : altLift5 σ ∈ altFive :=
  ⟨altLift5_apply_of_ge σ (by decide), altLift5_apply_of_ge σ (by decide)⟩

theorem card_filter_alt_five : (Finset.univ.filter fun σ : Perm (Fin 7) =>
    sign σ = 1 ∧ σ 5 = 5 ∧ σ 6 = 6).card = 60 := by
  decide +kernel

theorem nat_card_altFive : Nat.card altFive = 60 := by
  rw [← card_filter_alt_five, ← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
  refine Nat.card_congr ⟨fun x => ⟨(x : alternatingGroup (Fin 7)), ?_⟩,
    fun x => ⟨⟨(x : Perm (Fin 7)), mem_alternatingGroup.2 (x.2).1⟩, (x.2).2⟩,
    fun x => rfl, fun x => rfl⟩
  exact ⟨mem_alternatingGroup.1 (x : alternatingGroup (Fin 7)).2, x.2⟩

@[expose] noncomputable def altFiveEquiv : alternatingGroup (Fin 5) ≃* altFive :=
  MulEquiv.ofBijective (altLift5.codRestrict altFive altLift5_mem) (by
    have hinj : Function.Injective (altLift5.codRestrict altFive altLift5_mem) := fun a b h =>
      altLift5_injective (congrArg Subtype.val h)
    refine ⟨hinj, ?_⟩
    have hcard : Nat.card (alternatingGroup (Fin 5)) = Nat.card altFive := by
      rw [nat_card_altFive, nat_card_alternatingGroup, Nat.card_fin]
      rfl
    exact (Function.Injective.bijective_of_nat_card_le hinj hcard.ge).2)

theorem isSimpleGroup_altFive : IsSimpleGroup altFive := by
  have : IsSimpleGroup (alternatingGroup (Fin 5)) :=
    alternatingGroup.isSimpleGroup (by rw [Nat.card_fin])
  exact altFiveEquiv.symm.isSimpleGroup

@[expose] def a5cyc012 : alternatingGroup (Fin 7) :=
  ⟨swap 0 1 * swap 1 2, by rw [mem_alternatingGroup]; decide⟩

@[expose] def a5cyc123 : alternatingGroup (Fin 7) :=
  ⟨swap 1 2 * swap 2 3, by rw [mem_alternatingGroup]; decide⟩

@[expose] def a5dbl0123 : alternatingGroup (Fin 7) :=
  ⟨swap 0 1 * swap 2 3, by rw [mem_alternatingGroup]; decide⟩

theorem a5cyc012_mem : a5cyc012 ∈ altFive := by
  rw [mem_altFive]
  decide

theorem a5cyc123_mem : a5cyc123 ∈ altFive := by
  rw [mem_altFive]
  decide

theorem a5dbl0123_mem : a5dbl0123 ∈ altFive := by
  rw [mem_altFive]
  decide

theorem orderOf_a5cyc012 : orderOf a5cyc012 = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [a5cyc012, Subgroup.orderOf_mk]
  exact orderOf_eq_prime (by decide) (by decide)

theorem altFive_nonabelian : ∃ a b : altFive, a * b ≠ b * a :=
  ⟨⟨a5cyc012, a5cyc012_mem⟩, ⟨a5cyc123, a5cyc123_mem⟩, fun h => by
    have h2 := congrArg (fun x : altFive => ((x : alternatingGroup (Fin 7)) :
      Perm (Fin 7))) h
    exact absurd h2 (by decide)⟩

theorem isPerfect_altFive : Group.IsPerfect altFive := by
  have hs := isSimpleGroup_altFive
  rw [Group.isPerfect_def]
  rcases @IsSimpleGroup.eq_bot_or_eq_top_of_normal _ _ hs (commutator altFive)
      inferInstance with h | h
  · exfalso
    obtain ⟨a, b, hab⟩ := altFive_nonabelian
    apply hab
    have h1 : ⁅a, b⁆ = 1 := by
      have := commutator_mem_commutator (mem_top a) (mem_top b)
      rw [← _root_.commutator_def, h, mem_bot] at this
      exact this
    rwa [commutatorElement_eq_one_iff_mul_comm] at h1
  · exact h

theorem commutator_altFive : ⁅altFive, altFive⁆ = altFive :=
  (Subgroup.isPerfect_iff).1 isPerfect_altFive

theorem oTwoUpper_altFive : oTwoUpper altFive = altFive := by
  refine oTwoUpper_eq_self_of_simple isSimpleGroup_altFive a5cyc012_mem ?_ ?_
  · intro h
    have := congrArg (fun σ : alternatingGroup (Fin 7) => (σ : Perm (Fin 7)) 0) h
    exact absurd this (by decide)
  · rw [orderOf_a5cyc012]
    decide

theorem altFive_le_stabA7_vecFS : altFive ≤ stabA7 vecFS := fun σ hσ => by
  rw [mem_stabA7, permAct7_vecFS_iff]
  exact Or.inl hσ

theorem mem_altFive_of_odd {σ : alternatingGroup (Fin 7)} (hσ : σ ∈ stabA7 vecFS)
    (ho : Odd (orderOf σ)) : σ ∈ altFive := by
  rw [mem_stabA7, permAct7_vecFS_iff] at hσ
  rcases hσ with h | ⟨h5, h6⟩
  · exact h
  · exfalso
    obtain ⟨m, hm⟩ := ho
    have hsq : ((σ : Perm (Fin 7)) ^ 2) 5 = 5 := by
      rw [pow_two, Perm.mul_apply, h5, h6]
    have hpow : ∀ k : ℕ, ((σ : Perm (Fin 7)) ^ (2 * k + 1)) 5 = 6 := by
      intro k
      induction k with
      | zero => simpa using h5
      | succ k ih =>
        rw [show 2 * (k + 1) + 1 = 2 + (2 * k + 1) by ring, pow_add, Perm.mul_apply, ih,
          pow_two, Perm.mul_apply, h6, h5]
    have h1 : ((σ : Perm (Fin 7)) ^ orderOf σ) = 1 := by
      have := pow_orderOf_eq_one σ
      exact congrArg Subtype.val this
    have h2 := hpow m
    rw [← hm, h1] at h2
    exact absurd h2 (by decide)

theorem oTwoUpper_stabA7_vecFS : oTwoUpper (stabA7 vecFS) = altFive := by
  refine le_antisymm ((closure_le _).2 fun σ hσ => mem_altFive_of_odd hσ.1 hσ.2) ?_
  calc altFive = oTwoUpper altFive := oTwoUpper_altFive.symm
    _ ≤ oTwoUpper (stabA7 vecFS) := oTwoUpper_mono altFive_le_stabA7_vecFS

theorem perfectCore_subgroupOf_of_le {G : Type*} [Group G] [Finite G] {H L : Subgroup G}
    (hHL : H ≤ L) :
    (perfectCore H).subgroupOf L = perfectCore (H.subgroupOf L) := by
  have h1 := map_perfectCore L.subtype (H.subgroupOf L)
  rw [Subgroup.map_subgroupOf_eq_of_le hHL] at h1
  rw [← h1]
  exact Subgroup.comap_map_eq_self_of_injective L.subtype_injective _

section Le

variable {G : Type} [Group G] [Finite G] {L V : Subgroup G}
  {ψ : V ≃* Multiplicative (evenWeight 7)}

theorem natLam_map_Le_two (hLV : L ≤ normalizer (V : Set G))
    (hLact : ∀ l ∈ L, ∃ σ ∈ alternatingGroup (Fin 7), IsCoordAct ψ l σ)
    (hLonto : ∀ σ ∈ alternatingGroup (Fin 7), ∃ l ∈ L, IsCoordAct ψ l σ)
    {e : V} (he : vec ψ e = vecFS) :
    ((oTwoUpper (L ⊓ centralizer ({(e : G)} : Set G))).subgroupOf L).map
      (natLam hLV hLact) = altFive := by
  rw [oTwoUpper_subgroupOf inf_le_left, ← oTwoUpper_map,
    natLam_map_inf_centralizer hLV hLact hLonto e, he, oTwoUpper_stabA7_vecFS]

theorem natLam_map_Ke_two (hLV : L ≤ normalizer (V : Set G))
    (hLact : ∀ l ∈ L, ∃ σ ∈ alternatingGroup (Fin 7), IsCoordAct ψ l σ)
    (hLonto : ∀ σ ∈ alternatingGroup (Fin 7), ∃ l ∈ L, IsCoordAct ψ l σ)
    {e : V} (he : vec ψ e = vecFS) :
    ((perfectCore (oTwoUpper (L ⊓ centralizer ({(e : G)} : Set G)))).subgroupOf L).map
      (natLam hLV hLact) = altFive := by
  rw [perfectCore_subgroupOf_of_le ((oTwoUpper_le _).trans inf_le_left), map_perfectCore,
    natLam_map_Le_two hLV hLact hLonto he, (perfectCore_eq_self_iff _).2 commutator_altFive]

end Le

end CFSG.Quasithin.H13.A7
