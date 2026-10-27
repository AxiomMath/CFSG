module

public import CFSG.LocalAnalysis.StandardType.GGA11Defs

public section

open CFSG CFSG.Assembly CFSG.StandardType Matrix CFSG.LieType.Universal
  CFSG.LieType.Universal.SpecialLinear CFSG.LieType.RootSystem CFSG.LieType.CurtisTits CoxeterSystem

namespace CFSG.StandardType.A11

private def a11rc_f9 (a : Fin 12) : Fin 9 := if h : a.val < 9 then ⟨a.val, h⟩ else 0

private noncomputable def a11rc_tvGens : Set (SL 9) :=
  {g | ∃ (i j : Fin 9) (hij : i ≠ j), SpecialLinearGroup.transvection hij 1 = g}

private noncomputable def a11rc_TV (i j : Fin 9) : SL 9 :=
  if h : i ≠ j then SpecialLinearGroup.transvection h 1 else 1

private theorem a11rc_TV_of_ne {i j : Fin 9} (h : i ≠ j) :
    a11rc_TV i j = SpecialLinearGroup.transvection h 1 := dif_pos h

private theorem a11rc_TV_self (i : Fin 9) : a11rc_TV i i = 1 := dif_neg (fun h => h rfl)

private theorem a11rc_blk_ne_three (a : Fin 12) (ha : a.val < 9) : blk a ≠ 3 := by
  revert ha; fin_cases a <;> decide

private theorem a11rc_swapBlocks_three : swapBlocks 3 = 1 := by decide

private theorem a11rc_swapBlocks_apply_self (l : Fin 4) (a : Fin 12) :
    swapBlocks l (swapBlocks l a) = a := by
  revert l a; decide

private theorem a11rc_val_lt_of_blk_ne (l : Fin 4) (a : Fin 12) (h : blk a ≠ l) :
    (swapBlocks l a).val < 9 := by
  revert h; fin_cases l <;> fin_cases a <;> decide

private theorem a11rc_TV_congr {i j i' j' : Fin 9} (hi : i = i') (hj : j = j') :
    a11rc_TV i j = a11rc_TV i' j' := by
  subst hi; subst hj; rfl

private theorem a11rc_tv9_eq_TV (a b : Fin 12) (ha : a.val < 9) (hb : b.val < 9) :
    tv9 a b = a11rc_TV (a11rc_f9 a) (a11rc_f9 b) := by
  rw [tv9]
  by_cases hab : a = b
  · subst hab
    rw [dif_neg (by simp)]
    rw [a11rc_TV_self]
  · have hne : a11rc_f9 a ≠ a11rc_f9 b := by
      intro h
      apply hab
      apply Fin.ext
      simpa only [a11rc_f9, dif_pos ha, dif_pos hb] using congrArg Fin.val h
    rw [dif_pos ⟨ha, hb, hab⟩, a11rc_TV_of_ne hne]
    exact transvection_eq_of_eq _ _
      (by rw [a11rc_f9, dif_pos ha]) (by rw [a11rc_f9, dif_pos hb]) 1

private theorem a11rc_signedPerm_det (π : Equiv.Perm (Fin 9)) :
    (signedPerm π (1 : Fin 9 → F2)).det = 1 := by
  let S : Submonoid (Equiv.Perm (Fin 9)) :=
    { carrier := {x | (signedPerm x (1 : Fin 9 → F2)).det = 1}
      one_mem' := by
        simp only [Set.mem_setOf_eq]
        rw [signedPerm_one]
        simp
      mul_mem' := by
        intro x y hx hy
        simp only [Set.mem_setOf_eq] at hx hy ⊢
        have hmul : signedPerm (x * y) (1 : Fin 9 → F2) =
            signedPerm x (1 : Fin 9 → F2) * signedPerm y (1 : Fin 9 → F2) := by
          rw [signedPerm_mul_signedPerm]
          congr 1
          funext s
          simp
        rw [hmul, det_mul, hx, hy, one_mul] }
  have hgen : (Set.range (fun i : Fin 8 => Equiv.swap i.castSucc i.succ)) ⊆ S := by
    rintro _ ⟨k, rfl⟩
    change (signedPerm (Equiv.swap k.castSucc k.succ) (1 : Fin 9 → F2)).det = 1
    have h := coe_weylRep_of_two 8 two_eq_zero k
    rw [← h]
    exact (weylRep 8 F2 k).2
  have hle : Submonoid.closure (Set.range (fun i : Fin 8 => Equiv.swap i.castSucc i.succ)) ≤ S :=
    Submonoid.closure_le.mpr hgen
  exact hle (by rw [Equiv.Perm.mclosure_swap_castSucc_succ 8]; trivial)

private noncomputable def a11rc_signedPermHom : Equiv.Perm (Fin 9) →* SL 9 where
  toFun π := ⟨signedPerm π (1 : Fin 9 → F2), a11rc_signedPerm_det π⟩
  map_one' := by
    apply Subtype.ext
    change signedPerm 1 (1 : Fin 9 → F2) = (1 : Matrix (Fin 9) (Fin 9) F2)
    rw [signedPerm_one]
    exact diagonal_one
  map_mul' π π' := by
    apply Subtype.ext
    change signedPerm (π * π') (1 : Fin 9 → F2) = signedPerm π 1 * signedPerm π' 1
    rw [signedPerm_mul_signedPerm]
    congr 1
    funext s
    simp

private theorem a11rc_permSL_gen (k : Fin 8) :
    permSL 8 (Equiv.swap k.castSucc k.succ) =
      a11rc_signedPermHom (Equiv.swap k.castSucc k.succ) := by
  have hsimple : typeAWeylHom 8 (Equiv.swap k.castSucc k.succ) =
      (coxeterMatrix (isFiniteType_A 8)).toCoxeterSystem.simple k :=
    typeARealizes_inj 8 (typeAWeylOf_spec 8 _) (typeARealizes_simple 8 k)
  show slWeylLift 8 two_eq_zero (typeAWeylHom 8 (Equiv.swap k.castSucc k.succ)) =
    a11rc_signedPermHom (Equiv.swap k.castSucc k.succ)
  rw [hsimple, slWeylLift_simple]
  apply Subtype.ext
  change ((weylRep 8 F2 k : SL 9) : Matrix (Fin 9) (Fin 9) F2) =
    signedPerm (Equiv.swap k.castSucc k.succ) 1
  rw [coe_weylRep_of_two 8 two_eq_zero k]

private theorem a11rc_permSL_eq (π : Equiv.Perm (Fin 9)) :
    permSL 8 π = a11rc_signedPermHom π := by
  let S : Submonoid (Equiv.Perm (Fin 9)) :=
    { carrier := {x | permSL 8 x = a11rc_signedPermHom x}
      one_mem' := by simp
      mul_mem' := by
        intro x y hx hy
        simp only [Set.mem_setOf_eq] at hx hy ⊢
        rw [map_mul, map_mul, hx, hy] }
  have hle : Submonoid.closure (Set.range (fun i : Fin 8 => Equiv.swap i.castSucc i.succ)) ≤ S := by
    rw [Submonoid.closure_le]
    rintro _ ⟨k, rfl⟩
    exact a11rc_permSL_gen k
  exact hle (by rw [Equiv.Perm.mclosure_swap_castSucc_succ 8]; trivial)

private theorem a11rc_coe_permSL (π : Equiv.Perm (Fin 9)) :
    ((permSL 8 π : SL 9) : Matrix (Fin 9) (Fin 9) F2) = signedPerm π 1 := by
  rw [a11rc_permSL_eq]
  rfl

private theorem a11rc_permSL_conj_TV (π : Equiv.Perm (Fin 9)) (i j : Fin 9) :
    permSL 8 π * a11rc_TV i j * (permSL 8 π)⁻¹ = a11rc_TV (π i) (π j) := by
  by_cases hij : i = j
  · subst hij
    rw [a11rc_TV_self, a11rc_TV_self, mul_one, mul_inv_cancel]
  · rw [a11rc_TV_of_ne hij, a11rc_TV_of_ne (π.injective.ne hij)]
    have hcoe : ((permSL 8 π : SL 9) : Matrix (Fin 9) (Fin 9) F2) = signedPerm π 1 :=
      a11rc_coe_permSL π
    rw [conj_transvection_of_coe_eq_signedPerm hcoe (fun s => by simp)]
    simp

private noncomputable def a11rc_phi (l : Fin 4) (z : Fin 12) (hz : blk z ≠ l) : Fin 9 :=
  ⟨(swapBlocks l z).val, a11rc_val_lt_of_blk_ne l z hz⟩

private theorem a11rc_f9_phi (l : Fin 4) (z : Fin 12) (hz : blk z ≠ l) :
    a11rc_f9 (swapBlocks l z) = a11rc_phi l z hz := by
  unfold a11rc_phi a11rc_f9
  split_ifs with h
  · rfl
  · exact absurd (a11rc_val_lt_of_blk_ne l z hz) h

private theorem a11rc_tvAt_eq (l : Fin 4) (a b : Fin 12) (ha : blk a ≠ l) (hb : blk b ≠ l) :
    tvAt l a b = a11rc_TV (a11rc_phi l a ha) (a11rc_phi l b hb) := by
  rw [tvAt, a11rc_tv9_eq_TV (swapBlocks l a) (swapBlocks l b)
        (a11rc_val_lt_of_blk_ne l a ha) (a11rc_val_lt_of_blk_ne l b hb)]
  apply a11rc_TV_congr
  · exact a11rc_f9_phi l a ha
  · exact a11rc_f9_phi l b hb

private theorem a11rc_trAt_eq (l : Fin 4) (a b : Fin 12) (hab : a ≠ b)
    (ha : blk a ≠ l) (hb : blk b ≠ l) :
    trAt l a b = permSL 8 (Equiv.swap (a11rc_phi l a ha) (a11rc_phi l b hb)) := by
  rw [trAt, dif_pos ⟨a11rc_val_lt_of_blk_ne l a ha, a11rc_val_lt_of_blk_ne l b hb, hab⟩]
  rfl

private theorem a11rc_swapBlocks_conj (l : Fin 4) (p q z : Fin 12) :
    swapBlocks l (Equiv.swap p q z) =
      (Equiv.swap (swapBlocks l p) (swapBlocks l q)) (swapBlocks l z) := by
  rw [Equiv.swap_apply_apply (swapBlocks l) p q]
  simp [Equiv.Perm.mul_apply]

private theorem a11rc_fin_swap_val (x y w : Fin 12) (hx : x.val < 9) (hy : y.val < 9)
    (hw : w.val < 9) :
    ((Equiv.swap (⟨x.val, hx⟩ : Fin 9) (⟨y.val, hy⟩ : Fin 9)) (⟨w.val, hw⟩ : Fin 9)).val =
      ((Equiv.swap x y) w).val := by
  simp only [Equiv.swap_apply_def]
  by_cases hwx : w = x <;> by_cases hwy : w = y <;> simp_all [Fin.ext_iff]

private theorem a11rc_phi_swap (l : Fin 4) (p q z : Fin 12) (hpq : p ≠ q)
    (hp : blk p ≠ l) (hq : blk q ≠ l) (hz : blk z ≠ l)
    (hz' : blk (Equiv.swap p q z) ≠ l) :
    a11rc_phi l (Equiv.swap p q z) hz' =
      (Equiv.swap (a11rc_phi l p hp) (a11rc_phi l q hq)) (a11rc_phi l z hz) := by
  apply Fin.ext
  simp only [a11rc_phi, a11rc_f9]
  rw [a11rc_fin_swap_val (swapBlocks l p) (swapBlocks l q) (swapBlocks l z)
        (a11rc_val_lt_of_blk_ne l p hp) (a11rc_val_lt_of_blk_ne l q hq)
        (a11rc_val_lt_of_blk_ne l z hz)]
  exact congrArg Fin.val (a11rc_swapBlocks_conj l p q z)

private theorem a11rc_conj_tvAt {G : Type} [Group G] (Φ : Fin 4 → SL 9 →* G)
    (ρ : Equiv.Perm (Fin 12) →* G) (hrho : RhoEval Φ ρ)
    (l : Fin 4) (p q r s : Fin 12) (hpq : p ≠ q) (hrs : r ≠ s)
    (hlp : blk p ≠ l) (hlq : blk q ≠ l) (hlr : blk r ≠ l) (hls : blk s ≠ l) :
    ρ (Equiv.swap p q) * Φ l (tvAt l r s) * (ρ (Equiv.swap p q))⁻¹ =
      Φ l (tvAt l (Equiv.swap p q r) (Equiv.swap p q s)) := by
  have hpr : blk (Equiv.swap p q r) ≠ l := by
    rcases eq_or_ne r p with h | h
    · subst h; rw [Equiv.swap_apply_left]; exact hlq
    rcases eq_or_ne r q with h' | h'
    · subst h'; rw [Equiv.swap_apply_right]; exact hlp
    · rw [Equiv.swap_apply_of_ne_of_ne h h']; exact hlr
  have hps : blk (Equiv.swap p q s) ≠ l := by
    rcases eq_or_ne s p with h | h
    · subst h; rw [Equiv.swap_apply_left]; exact hlq
    rcases eq_or_ne s q with h' | h'
    · subst h'; rw [Equiv.swap_apply_right]; exact hlp
    · rw [Equiv.swap_apply_of_ne_of_ne h h']; exact hls
  rw [hrho l p q hpq hlp hlq, ← map_inv, ← map_mul, ← map_mul]
  congr 1
  rw [a11rc_trAt_eq l p q hpq hlp hlq, a11rc_tvAt_eq l r s hlr hls,
    a11rc_tvAt_eq l (Equiv.swap p q r) (Equiv.swap p q s) hpr hps,
    a11rc_permSL_conj_TV]
  rw [a11rc_phi_swap l p q r hpq hlp hlq hlr hpr,
    a11rc_phi_swap l p q s hpq hlp hlq hls hps]

private theorem a11rc_exists_block_two (a b : Fin 12) :
    ∃ l : Fin 4, blk a ≠ l ∧ blk b ≠ l := by
  revert a b; decide

private theorem a11rc_exists_block_three (a b c : Fin 12) :
    ∃ l : Fin 4, blk a ≠ l ∧ blk b ≠ l ∧ blk c ≠ l := by
  revert a b c; decide

private theorem a11rc_exists_base_pair (a b : Fin 12) (hab : a ≠ b) :
    ∃ a0 b0 : Fin 12, a0.val < 8 ∧ b0.val < 8 ∧ a0 ≠ b0 ∧ a0 ≠ a ∧ a0 ≠ b ∧ b0 ≠ b := by
  revert a b; decide

private noncomputable def a11rc_TVS (i j : Fin 8) : SL 8 :=
  if h : i ≠ j then SpecialLinearGroup.transvection h 1 else 1

private theorem a11rc_TV_castSucc (i j : Fin 8) :
    a11rc_TV i.castSucc j.castSucc = slBlockHom 7 F2 (a11rc_TVS i j) := by
  by_cases hij : i = j
  · subst hij
    rw [a11rc_TV_self]
    rw [show a11rc_TVS i i = 1 by rw [a11rc_TVS]; exact dif_neg (fun h => h rfl), map_one]
  · rw [a11rc_TV_of_ne (fun h => hij (Fin.castSucc_injective 8 h))]
    rw [show a11rc_TVS i j = SpecialLinearGroup.transvection hij 1 by
      rw [a11rc_TVS]; exact dif_pos hij]
    rw [slBlockHom_transvection]

private theorem a11rc_base_mem {G : Type} [Group G] (Φ : Fin 4 → SL 9 →* G)
    (ρ : Equiv.Perm (Fin 12) →* G) (hcoh : Coherent Φ)
    (a b : Fin 12) (ha : a.val < 8) (hb : b.val < 8) (hab : a ≠ b)
    (m : Fin 4) (hm : blk a ≠ m) (hm' : blk b ≠ m) :
    Φ m (tvAt m a b) ∈ Clos (Φ 3) ρ := by
  have h3a : blk a ≠ 3 := a11rc_blk_ne_three a (by omega)
  have h3b : blk b ≠ 3 := a11rc_blk_ne_three b (by omega)
  have hco := hcoh m 3 a b hab hm hm' h3a h3b
  rw [hco, tvAt, a11rc_swapBlocks_three]
  simp only [Equiv.Perm.one_apply]
  rw [a11rc_tv9_eq_TV a b (by omega) (by omega)]
  have hfa : a11rc_f9 a = (⟨a.val, ha⟩ : Fin 8).castSucc := by
    rw [a11rc_f9, dif_pos (by omega)]
    rfl
  have hfb : a11rc_f9 b = (⟨b.val, hb⟩ : Fin 8).castSucc := by
    rw [a11rc_f9, dif_pos (by omega)]
    rfl
  rw [hfa, hfb, a11rc_TV_castSucc]
  exact Subgroup.subset_closure ⟨1, a11rc_TVS ⟨a.val, ha⟩ ⟨b.val, hb⟩, by simp⟩

private theorem a11rc_clos_conj {G : Type} [Group G] (Φ : Fin 4 → SL 9 →* G)
    (ρ : Equiv.Perm (Fin 12) →* G) (w : Equiv.Perm (Fin 12)) {c : G}
    (hc : c ∈ Clos (Φ 3) ρ) :
    ρ w * c * (ρ w)⁻¹ ∈ Clos (Φ 3) ρ := by
  have hconj : Subgroup.map (MulAut.conj (ρ w)).toMonoidHom (Clos (Φ 3) ρ) ≤ Clos (Φ 3) ρ := by
    unfold Clos
    rw [MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨x, ⟨w', s, rfl⟩, rfl⟩
    refine Subgroup.subset_closure ⟨w * w', s, ?_⟩
    show (ρ w * (ρ w' * Φ 3 (slBlockHom 7 F2 s) * (ρ w')⁻¹) * (ρ w)⁻¹)
        = ρ (w * w') * Φ 3 (slBlockHom 7 F2 s) * (ρ (w * w'))⁻¹
    rw [map_mul]
    group
  exact hconj ⟨c, hc, by
    change (MulAut.conj (ρ w)) c = ρ w * c * (ρ w)⁻¹
    rw [MulAut.conj_apply]⟩

private theorem a11rc_root_mem {G : Type} [Group G] (Φ : Fin 4 → SL 9 →* G)
    (ρ : Equiv.Perm (Fin 12) →* G) (hcoh : Coherent Φ) (hrho : RhoEval Φ ρ)
    (l : Fin 4) (a b : Fin 12) (hab : a ≠ b) (hla : blk a ≠ l) (hlb : blk b ≠ l) :
    Φ l (tvAt l a b) ∈ Clos (Φ 3) ρ := by
  obtain ⟨a0, b0, ha0, hb0, hab0, ha0a, ha0b, hb0b⟩ := a11rc_exists_base_pair a b hab
  obtain ⟨m0, hm0a, hm0b⟩ := a11rc_exists_block_two a0 b0
  obtain ⟨m1, hm1a, hm1b, hm1b0⟩ := a11rc_exists_block_three a0 b b0
  obtain ⟨m2, hm2A0, hm2B, hm2A⟩ := a11rc_exists_block_three a0 b a
  have hbase0 : Φ m0 (tvAt m0 a0 b0) ∈ Clos (Φ 3) ρ :=
    a11rc_base_mem Φ ρ hcoh a0 b0 ha0 hb0 hab0 m0 hm0a hm0b
  have hbase1 : Φ m1 (tvAt m1 a0 b0) ∈ Clos (Φ 3) ρ :=
    (hcoh m0 m1 a0 b0 hab0 hm0a hm0b hm1a hm1b0) ▸ hbase0
  have hL1 : ρ (Equiv.swap b0 b) * Φ m1 (tvAt m1 a0 b0) * (ρ (Equiv.swap b0 b))⁻¹ ∈
      Clos (Φ 3) ρ :=
    a11rc_clos_conj Φ ρ (Equiv.swap b0 b) hbase1
  have hmove1 := a11rc_conj_tvAt Φ ρ hrho m1 b0 b a0 b0 hb0b hab0 hm1b0 hm1b hm1a hm1b0
  rw [Equiv.swap_apply_of_ne_of_ne hab0 ha0b, Equiv.swap_apply_left] at hmove1
  have hX1 : Φ m1 (tvAt m1 a0 b) ∈ Clos (Φ 3) ρ := hmove1 ▸ hL1
  have hX1' : Φ m2 (tvAt m2 a0 b) ∈ Clos (Φ 3) ρ :=
    (hcoh m1 m2 a0 b ha0b hm1a hm1b hm2A0 hm2B) ▸ hX1
  have hL2 : ρ (Equiv.swap a0 a) * Φ m2 (tvAt m2 a0 b) * (ρ (Equiv.swap a0 a))⁻¹ ∈
      Clos (Φ 3) ρ :=
    a11rc_clos_conj Φ ρ (Equiv.swap a0 a) hX1'
  have hmove2 := a11rc_conj_tvAt Φ ρ hrho m2 a0 a a0 b ha0a ha0b hm2A0 hm2A hm2A0 hm2B
  rw [Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne (Ne.symm ha0b) (Ne.symm hab)] at hmove2
  have hX2 : Φ m2 (tvAt m2 a b) ∈ Clos (Φ 3) ρ := hmove2 ▸ hL2
  exact (hcoh m2 l a b hab hm2A hm2B hla hlb) ▸ hX2

private theorem a11rc_F2_eq_zero_or_one (c : F2) : c = 0 ∨ c = 1 := by
  classical
  haveI : Fintype F2 := Fintype.ofFinite F2
  have hcard : Fintype.card F2 = 2 := by
    rw [← Nat.card_eq_fintype_card]
    exact GaloisField.card 2 1 (by omega)
  have h01 : (0 : F2) ≠ 1 := zero_ne_one
  have huniv : ({0, 1} : Finset F2) = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [Finset.card_insert_of_notMem (by simp [h01]), Finset.card_singleton]
    omega
  have : c ∈ ({0, 1} : Finset F2) := by rw [huniv]; exact Finset.mem_univ c
  simpa using this

private theorem a11rc_transvection_zero {i j : Fin 9} (hij : i ≠ j) :
    SpecialLinearGroup.transvection hij (0 : F2) = 1 := by
  have h := map_one (SpecialLinearGroup.transvectionHom (A := F2) hij)
  simpa using h

private theorem a11rc_blk_swapBlocks (l : Fin 4) (a : Fin 12) :
    blk (swapBlocks l a) = Equiv.swap l 3 (blk a) := by
  revert l a; decide

private theorem a11rc_tvGens_closure :
    Subgroup.closure (a11rc_tvGens) = ⊤ := by
  rw [eq_top_iff, ← iSup_fundamentalRootSubgroup_eq_top (m := 8) (F := F2)]
  refine iSup_le fun k => iSup_le fun s => ?_
  intro x hx
  cases s with
  | false =>
    obtain ⟨c, rfl⟩ := (mem_rootSubgroup (F := F2) (i := k.succ) (j := k.castSucc)
      (k.castSucc_lt_succ.ne') x).mp hx
    rcases a11rc_F2_eq_zero_or_one c with hc | hc
    · subst hc; rw [a11rc_transvection_zero]; exact Subgroup.one_mem _
    · subst hc; exact Subgroup.subset_closure ⟨k.succ, k.castSucc, k.castSucc_lt_succ.ne', rfl⟩
  | true =>
    obtain ⟨c, rfl⟩ := (mem_rootSubgroup (F := F2) (i := k.castSucc) (j := k.succ)
      (k.castSucc_lt_succ.ne) x).mp hx
    rcases a11rc_F2_eq_zero_or_one c with hc | hc
    · subst hc; rw [a11rc_transvection_zero]; exact Subgroup.one_mem _
    · subst hc; exact Subgroup.subset_closure ⟨k.castSucc, k.succ, k.castSucc_lt_succ.ne, rfl⟩

private theorem a11rc_range_gen {G : Type} [Group G] (Φ : Fin 4 → SL 9 →* G)
    (ρ : Equiv.Perm (Fin 12) →* G) (hcoh : Coherent Φ) (hrho : RhoEval Φ ρ)
    (l : Fin 4) (i j : Fin 9) (hij : i ≠ j) :
    Φ l (SpecialLinearGroup.transvection hij 1) ∈ Clos (Φ 3) ρ := by
  let a : Fin 12 := swapBlocks l (Fin.castLE (by omega : 9 ≤ 12) i)
  let b : Fin 12 := swapBlocks l (Fin.castLE (by omega : 9 ≤ 12) j)
  have hblka : blk (Fin.castLE (by omega : 9 ≤ 12) i) ≠ 3 :=
    a11rc_blk_ne_three _ (by simp)
  have hblkb : blk (Fin.castLE (by omega : 9 ≤ 12) j) ≠ 3 :=
    a11rc_blk_ne_three _ (by simp)
  have hla : blk a ≠ l := by
    intro hh
    have h2 := congrArg (Equiv.swap l 3) hh
    rw [show a = swapBlocks l (Fin.castLE (by omega : 9 ≤ 12) i) from rfl,
      a11rc_blk_swapBlocks, Equiv.swap_apply_self, Equiv.swap_apply_left] at h2
    exact hblka h2
  have hlb : blk b ≠ l := by
    intro hh
    have h2 := congrArg (Equiv.swap l 3) hh
    rw [show b = swapBlocks l (Fin.castLE (by omega : 9 ≤ 12) j) from rfl,
      a11rc_blk_swapBlocks, Equiv.swap_apply_self, Equiv.swap_apply_left] at h2
    exact hblkb h2
  have hab : a ≠ b := by
    intro hh
    have h' : (Fin.castLE (by omega : 9 ≤ 12) i) = (Fin.castLE (by omega : 9 ≤ 12) j) := by
      have := congrArg (swapBlocks l) hh
      simpa only [a, b, a11rc_swapBlocks_apply_self] using this
    exact hij (Fin.ext (by simpa using congrArg Fin.val h'))
  have hroot := a11rc_root_mem Φ ρ hcoh hrho l a b hab hla hlb
  have htv : tvAt l a b = SpecialLinearGroup.transvection hij 1 := by
    rw [tvAt, show a = swapBlocks l (Fin.castLE (by omega : 9 ≤ 12) i) from rfl,
      show b = swapBlocks l (Fin.castLE (by omega : 9 ≤ 12) j) from rfl,
      a11rc_swapBlocks_apply_self, a11rc_swapBlocks_apply_self,
      a11rc_tv9_eq_TV (Fin.castLE (by omega : 9 ≤ 12) i) (Fin.castLE (by omega : 9 ≤ 12) j)
        (by exact i.isLt) (by exact j.isLt)]
    have hfi : a11rc_f9 (Fin.castLE (by omega : 9 ≤ 12) i) = i := by
      unfold a11rc_f9
      rw [dif_pos (by exact i.isLt)]
      rfl
    have hfj : a11rc_f9 (Fin.castLE (by omega : 9 ≤ 12) j) = j := by
      unfold a11rc_f9
      rw [dif_pos (by exact j.isLt)]
      rfl
    rw [a11rc_TV_congr hfi hfj, a11rc_TV_of_ne hij]
  rwa [htv] at hroot

private theorem a11rc_range_le {G : Type} [Group G] (Φ : Fin 4 → SL 9 →* G)
    (ρ : Equiv.Perm (Fin 12) →* G) (hcoh : Coherent Φ) (hrho : RhoEval Φ ρ)
    (l : Fin 4) : (Φ l).range ≤ Clos (Φ 3) ρ := by
  have hpre : a11rc_tvGens ⊆ (Subgroup.comap (Φ l) (Clos (Φ 3) ρ) : Set (SL 9)) := by
    rintro g ⟨i, j, hij, rfl⟩
    exact a11rc_range_gen Φ ρ hcoh hrho l i j hij
  have htop : (⊤ : Subgroup (SL 9)) ≤ Subgroup.comap (Φ l) (Clos (Φ 3) ρ) := by
    rw [← a11rc_tvGens_closure, Subgroup.closure_le]
    exact hpre
  intro g hg
  obtain ⟨x, rfl⟩ := hg
  exact (Subgroup.mem_comap).mp (htop (Subgroup.mem_top x))

private theorem a11rc_rho_range_le {G : Type} [Group G] (Φ : Fin 4 → SL 9 →* G)
    (ρ : Equiv.Perm (Fin 12) →* G) (hrho : RhoEval Φ ρ) :
    ρ.range ≤ ⨆ l, (Φ l).range := by
  rw [MonoidHom.range_eq_map, ← Equiv.Perm.closure_isSwap (α := Fin 12),
    MonoidHom.map_closure, Subgroup.closure_le]
  rintro _ ⟨σ, hσ, rfl⟩
  obtain ⟨x, y, hxy, rfl⟩ := hσ
  obtain ⟨l, hlx, hly⟩ := a11rc_exists_block_two x y
  rw [hrho l x y hxy hlx hly]
  exact Subgroup.mem_iSup_of_mem l ⟨trAt l x y, rfl⟩

theorem a11RhoClosInput_holds :
    ∀ (G : Type) [Group G] (Φ : Fin 4 → SL 9 →* G) (ρ : Equiv.Perm (Fin 12) →* G),
      Coherent Φ → RhoEval Φ ρ →
        (∀ l, (Φ l).range ≤ Clos (Φ 3) ρ) ∧ ρ.range ≤ ⨆ l, (Φ l).range := by
  intro G _ Φ ρ hcoh hrho
  exact ⟨fun l => a11rc_range_le Φ ρ hcoh hrho l, a11rc_rho_range_le Φ ρ hrho⟩

end CFSG.StandardType.A11

end
