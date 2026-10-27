module

public import CFSG.Sporadic.SuzRecog.SuzL34.Facts

public section

namespace CFSG.Sporadic.SuzRecog.SuzL34

open CFSG.Sporadic.SuzRecog.SuzL34Cert
open Subgroup

variable {G : Type*} [Group G] {L : Subgroup G}

noncomputable def bitAction (e : Fin 16 ≃ ↥L) :
    ↥(normalizer (L : Set G)) →* Equiv.Perm (Fin 16) :=
  (Equiv.permCongrHom e.symm).toMonoidHom.comp
    ((MulAut.toPerm (M := ↥L)).comp (Subgroup.normalizerMonoidHom (H := L)))

theorem coe_bitAction_apply (e : Fin 16 ≃ ↥L) (g : ↥(normalizer (L : Set G))) (i : Fin 16) :
    ((e (bitAction e g i) : ↥L) : G) = (g : G) * (e i : G) * (g : G)⁻¹ := by
  have h : bitAction e g i = e.symm ((Subgroup.normalizerMonoidHom (H := L) g) (e i)) := rfl
  rw [h, Equiv.apply_symm_apply]
  rfl

theorem bitAction_xor (e : Fin 16 ≃ ↥L) (he : ∀ i j, (e (xor16 i j) : G) = e i * e j)
    (g : ↥(normalizer (L : Set G))) (i j : Fin 16) :
    bitAction e g (xor16 i j) = xor16 (bitAction e g i) (bitAction e g j) := by
  apply e.injective
  apply Subtype.ext
  rw [coe_bitAction_apply]
  have h1 : (e (xor16 (bitAction e g i) (bitAction e g j)) : G) =
      (e (bitAction e g i) : G) * (e (bitAction e g j) : G) := he _ _
  rw [h1, coe_bitAction_apply, coe_bitAction_apply, he i j]
  group

theorem bitAction_eq_one_iff (e : Fin 16 ≃ ↥L) (g : ↥(normalizer (L : Set G))) :
    bitAction e g = 1 ↔ (g : G) ∈ centralizer (L : Set G) := by
  have hinj : Function.Injective (MulAut.toPerm (M := ↥L)) := by
    intro a b h
    exact MulEquiv.ext fun x => congrArg (fun p : Equiv.Perm ↥L => p x) h
  have hker : bitAction e g = 1 ↔ Subgroup.normalizerMonoidHom (H := L) g = 1 := by
    constructor
    · intro h
      have h' : (Equiv.permCongrHom e.symm) ((MulAut.toPerm (M := ↥L))
          (Subgroup.normalizerMonoidHom (H := L) g)) = 1 := by
        simpa [bitAction] using h
      have h'' : (MulAut.toPerm (M := ↥L))
          (Subgroup.normalizerMonoidHom (H := L) g) = 1 := by
        apply (Equiv.permCongrHom e.symm).injective
        rw [h', map_one]
      exact hinj h''
    · intro h
      have h1 : e.symm.permCongr (1 : Equiv.Perm ↥L) = 1 := by
        ext x
        simp [Equiv.permCongr_apply]
      simp [bitAction, h, h1]
  rw [hker, ← MonoidHom.mem_ker, Subgroup.normalizerMonoidHom_ker, Subgroup.mem_subgroupOf]

theorem card_map_bitAction_mul [Finite G] (e : Fin 16 ≃ ↥L) {H : Subgroup G}
    (hH : H ≤ normalizer (L : Set G)) :
    Nat.card ↥((H.subgroupOf (normalizer (L : Set G))).map (bitAction e)) *
      Nat.card ↥(H ⊓ centralizer (L : Set G)) = Nat.card ↥H := by
  let N := normalizer (L : Set G)
  let K := H.subgroupOf N
  let f : K →* Equiv.Perm (Fin 16) := (bitAction e).comp K.subtype
  have hrange : f.range = K.map (bitAction e) := by
    ext y
    rw [MonoidHom.mem_range, Subgroup.mem_map]
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x, x.2, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩
  have hker : f.ker = ((H ⊓ centralizer (L : Set G)).subgroupOf N).subgroupOf K := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf,
      Subgroup.mem_inf]
    constructor
    · intro hx
      exact ⟨Subgroup.mem_subgroupOf.mp x.2, (bitAction_eq_one_iff e (x : N)).mp hx⟩
    · rintro ⟨hxH, hxC⟩
      exact (bitAction_eq_one_iff e (x : N)).mpr hxC
  have hker_card : Nat.card ↥f.ker = Nat.card ↥(H ⊓ centralizer (L : Set G)) := by
    rw [hker]
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (show
      (H ⊓ centralizer (L : Set G)).subgroupOf N ≤ K from ?_)).toEquiv]
    · exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_trans inf_le_left hH)).toEquiv
    · intro x hx
      rw [Subgroup.mem_subgroupOf] at hx ⊢
      exact (Subgroup.mem_inf.mp hx).1
  have hK_card : Nat.card ↥K = Nat.card ↥H :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hH).toEquiv
  have hmain := Subgroup.card_ker_mul_card_range f
  rw [hker_card, hrange, hK_card] at hmain
  rw [mul_comm]
  exact hmain

end CFSG.Sporadic.SuzRecog.SuzL34

namespace CFSG.Sporadic.SuzRecog.SuzL34Cert

open CFSG.Sporadic.SuzRecog.C1Model
open CFSG.Monster.B.Co2
open Subgroup

theorem l1BasisPerm_mem {k : ℕ} (hk : k < 4) : l1BasisPerm k ∈ decSubgroup l1Decs := by
  unfold l1BasisPerm decSubgroup
  apply Subgroup.subset_closure
  refine Set.mem_image_of_mem decPerm ?_
  have hlen : k < l1Decs.length := by simp [l1Decs]; omega
  rw [List.getD_eq_getElem (l := l1Decs) (d := ([], 1)) hlen]
  exact List.getElem_mem _

theorem l1Elt_mem (i : Fin 16) : l1Elt i ∈ decSubgroup l1Decs := by
  unfold l1Elt
  apply Subgroup.list_prod_mem
  intro x hx
  obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hx
  rw [List.mem_range] at hk
  by_cases h : i.val.testBit k
  · rw [if_pos h]
    exact l1BasisPerm_mem hk
  · rw [if_neg h]
    exact Subgroup.one_mem _

private theorem prod_bit_ite_mul {M : Type*} [CommMonoid M] (b : ℕ → M)
    (hb : ∀ k < 4, b k * b k = 1) (i j : Fin 16) :
    ((List.range 4).map (fun k => if i.val.testBit k then b k else 1)).prod *
      ((List.range 4).map (fun k => if j.val.testBit k then b k else 1)).prod =
    ((List.range 4).map
      (fun k => if (i.val ^^^ j.val).testBit k then b k else 1)).prod := by
  rw [← List.prod_toFinset (fun k => if i.val.testBit k then b k else 1)
      (List.nodup_range (n := 4)),
    ← List.prod_toFinset (fun k => if j.val.testBit k then b k else 1)
      (List.nodup_range (n := 4)),
    ← List.prod_toFinset (fun k => if (i.val ^^^ j.val).testBit k then b k else 1)
      (List.nodup_range (n := 4))]
  rw [← Finset.prod_mul_distrib, List.toFinset_range]
  apply Finset.prod_congr rfl
  intro k hk
  rw [Finset.mem_range] at hk
  rw [Nat.testBit_xor]
  cases hi : i.val.testBit k <;> cases hj : j.val.testBit k <;> simp [hi, hj, hb k hk]

private theorem l1Elt_eq_prod (i : Fin 16) :
    l1Elt i = ((List.range 4).map
      fun k => if i.val.testBit k then l1BasisPerm k else 1).prod := rfl

private theorem prod_range_four {M : Type*} [Monoid M] (f : ℕ → M) :
    ((List.range 4).map f).prod = f 0 * (f 1 * (f 2 * f 3)) := by
  have h : List.range 4 = [0, 1, 2, 3] := by decide
  rw [h]
  simp [List.prod]

theorem l1Elt_zero : l1Elt (0 : Fin 16) = 1 := by
  rw [l1Elt_eq_prod]
  change ((List.range 4).map
    (fun j => if (0 : Fin 16).val.testBit j then l1BasisPerm j else 1)).prod = 1
  rw [prod_range_four]
  simp

private theorem xor16_self (i : Fin 16) : xor16 i i = 0 := by
  apply Fin.ext
  simp [xor16]

theorem l1Elt_two_pow (k : ℕ) (hk : k < 4) :
    l1Elt (⟨2 ^ k, by
      calc 2 ^ k ≤ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) (by omega)
        _ < 16 := by norm_num⟩ : Fin 16) = l1BasisPerm k := by
  rw [l1Elt_eq_prod]
  change ((List.range 4).map
    (fun j => if (2 ^ k).testBit j then l1BasisPerm j else 1)).prod = l1BasisPerm k
  rw [prod_range_four]
  have hbit : ∀ j < 4, (2 ^ k).testBit j = decide (j = k) := by
    intro j hj
    rw [Nat.testBit_two_pow]
    simp [eq_comm]
  simp only [hbit 0 (by norm_num), hbit 1 (by norm_num),
    hbit 2 (by norm_num), hbit 3 (by norm_num)]
  interval_cases k <;> simp

private theorem l1_elem_abelian (hF1 : F1Prop) :
    CFSG.Open.IsElemAbelian 2 (decSubgroup l1Decs) := by
  unfold F1Prop at hF1
  exact hF1.2.2.2.2.1

theorem l1Decs_closure :
    decSubgroup l1Decs =
      Subgroup.closure ({l1BasisPerm 0, l1BasisPerm 1, l1BasisPerm 2, l1BasisPerm 3} :
        Set (Equiv.Perm (Fin 1782))) := by
  unfold decSubgroup
  congr 1
  ext x
  simp [l1Decs, l1BasisPerm, eq_comm]

open scoped IsMulCommutative

theorem l1Elt_xor (hF1 : F1Prop) (i j : Fin 16) :
    l1Elt (xor16 i j) = l1Elt i * l1Elt j := by
  have hEA := l1_elem_abelian hF1
  haveI : IsMulCommutative ↥(decSubgroup l1Decs) := hEA.1
  let b : ℕ → ↥(decSubgroup l1Decs) := fun k =>
    if hk : k < 4 then ⟨l1BasisPerm k, l1BasisPerm_mem hk⟩ else 1
  have hb : ∀ k < 4, b k * b k = 1 := by
    intro k hk
    have h := hEA.2 (b k) (b k).2
    apply Subtype.ext
    simpa [pow_two] using h
  have hF_eq : ∀ i : Fin 16, l1Elt i =
      (((List.range 4).map fun k => if i.val.testBit k then b k else 1).prod :
        Equiv.Perm (Fin 1782)) := by
    intro i
    unfold l1Elt
    rw [Subgroup.val_list_prod]
    simp only [List.map_map, Function.comp_def]
    congr 1
    apply List.map_congr_left
    intro k hk
    rw [List.mem_range] at hk
    by_cases h : i.val.testBit k
    · simp [b, h, dif_pos hk]
    · simp [b, h]
  have hF_eq_sub : ∀ i : Fin 16, (⟨l1Elt i, l1Elt_mem i⟩ : ↥(decSubgroup l1Decs)) =
      ((List.range 4).map fun k => if i.val.testBit k then b k else 1).prod := by
    intro i
    apply Subtype.ext
    exact hF_eq i
  have hsub : (⟨l1Elt (xor16 i j), l1Elt_mem (xor16 i j)⟩ : ↥(decSubgroup l1Decs)) =
      (⟨l1Elt i, l1Elt_mem i⟩ : ↥(decSubgroup l1Decs)) *
        (⟨l1Elt j, l1Elt_mem j⟩ : ↥(decSubgroup l1Decs)) := by
    rw [hF_eq_sub (xor16 i j), hF_eq_sub i, hF_eq_sub j]
    rw [show (xor16 i j).val = i.val ^^^ j.val from rfl]
    exact (prod_bit_ite_mul b hb i j).symm
  exact Subtype.ext_iff.mp hsub

@[expose] noncomputable def l1Equiv (hF1 : F1Prop) : Fin 16 ≃ ↥(decSubgroup l1Decs) := by
  classical
  let L1 := decSubgroup l1Decs
  let f : Fin 16 → ↥L1 := fun i => ⟨l1Elt i, l1Elt_mem i⟩
  have hf_mul : ∀ i j, f (xor16 i j) = f i * f j := fun i j =>
    Subtype.ext (l1Elt_xor hF1 i j)
  have hf_one : f 0 = 1 := Subtype.ext l1Elt_zero
  let K : Subgroup ↥L1 :=
    { carrier := Set.range f
      one_mem' := ⟨0, hf_one⟩
      mul_mem' := by
        rintro _ _ ⟨i, rfl⟩ ⟨j, rfl⟩
        exact ⟨xor16 i j, hf_mul i j⟩
      inv_mem' := by
        rintro _ ⟨i, rfl⟩
        have hi : f i * f i = 1 := by
          rw [← hf_mul i i, xor16_self, hf_one]
        exact ⟨i, (inv_eq_of_mul_eq_one_right hi).symm⟩ }
  have hgen : ∀ k < 4, l1BasisPerm k ∈ K.map L1.subtype := by
    intro k hk
    refine Subgroup.mem_map.mpr ⟨f ⟨2 ^ k, ?_⟩, ⟨_, rfl⟩, ?_⟩
    · calc 2 ^ k ≤ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) (by omega)
        _ < 16 := by norm_num
    exact l1Elt_two_pow k hk
  have hmap_ge : L1 ≤ K.map L1.subtype := by
    change decSubgroup l1Decs ≤ K.map L1.subtype
    rw [l1Decs_closure]
    apply (Subgroup.closure_le (K := K.map L1.subtype)).mpr
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl
    exacts [hgen 0 (by norm_num), hgen 1 (by norm_num),
      hgen 2 (by norm_num), hgen 3 (by norm_num)]
  have hmap : K.map L1.subtype = L1 :=
    le_antisymm (Subgroup.map_subtype_le K) hmap_ge
  have htop : (⊤ : Subgroup ↥L1).map L1.subtype = L1 := by
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hK : K = ⊤ :=
    Subgroup.map_injective L1.subtype_injective (by rw [hmap, htop])
  have hsurj : Function.Surjective f := by
    intro x
    have hx : x ∈ K := by rw [hK]; exact Subgroup.mem_top x
    exact hx
  have hbij : Function.Bijective f := by
    rw [Fintype.bijective_iff_surjective_and_card]
    refine ⟨hsurj, ?_⟩
    rw [Fintype.card_fin, ← Nat.card_eq_fintype_card]
    have hcard : Nat.card ↥(decSubgroup l1Decs) = 16 := by
      unfold F1Prop at hF1
      exact hF1.2.2.2.2.2.1
    exact hcard.symm
  exact Equiv.ofBijective f hbij

theorem coe_l1Equiv (hF1 : F1Prop) (i : Fin 16) :
    ((l1Equiv hF1 i : ↥(decSubgroup l1Decs)) : Equiv.Perm (Fin 1782)) = l1Elt i := rfl

end CFSG.Sporadic.SuzRecog.SuzL34Cert

end
