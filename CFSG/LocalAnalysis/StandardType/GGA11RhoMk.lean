module

public import CFSG.LocalAnalysis.StandardType.GGA11Defs
public import CFSG.LocalAnalysis.StandardType.GGTypeABstarFarProofCoxeter

public section

open CFSG CFSG.Assembly CFSG.StandardType Matrix CFSG.LieType.Universal
  CFSG.LieType.Universal.SpecialLinear CFSG.LieType.RootSystem SpecialLinearGroup

namespace CFSG.StandardType.A11

private def a11rm_f9 (x : Fin 12) (h : x.val < 9) : Fin 9 := ⟨x.val, h⟩

private theorem a11rm_swapBlocks_val_lt :
    ∀ (l : Fin 4) (a : Fin 12), blk a ≠ l → (swapBlocks l a).val < 9 := by
  decide

private theorem a11rm_swapBlocks_ne {l : Fin 4} {a b : Fin 12} (h : a ≠ b) :
    swapBlocks l a ≠ swapBlocks l b :=
  fun he => h ((swapBlocks l).injective he)

private theorem a11rm_f9_ne {x y : Fin 12} {hx : x.val < 9} {hy : y.val < 9} (h : x ≠ y) :
    a11rm_f9 x hx ≠ a11rm_f9 y hy :=
  fun he => h (Fin.ext (by simpa [a11rm_f9] using congrArg Fin.val he))

private theorem a11rm_tvAt_eq (l : Fin 4) (a b : Fin 12)
    (ha : blk a ≠ l) (hb : blk b ≠ l) (hab : a ≠ b) :
    tvAt l a b = SpecialLinearGroup.transvection
      (show a11rm_f9 (swapBlocks l a) (a11rm_swapBlocks_val_lt l a ha) ≠
            a11rm_f9 (swapBlocks l b) (a11rm_swapBlocks_val_lt l b hb) from
        fun he => a11rm_swapBlocks_ne hab (Fin.ext (by simpa [a11rm_f9] using congrArg Fin.val he)))
      (1 : F2) := by
  unfold tvAt tv9
  rw [dif_pos ⟨a11rm_swapBlocks_val_lt l a ha, a11rm_swapBlocks_val_lt l b hb, a11rm_swapBlocks_ne hab⟩]
  rfl

private theorem a11rm_trAt_eq (l : Fin 4) (a b : Fin 12)
    (ha : blk a ≠ l) (hb : blk b ≠ l) (hab : a ≠ b) :
    trAt l a b = permSL 8 (Equiv.swap
      (a11rm_f9 (swapBlocks l a) (a11rm_swapBlocks_val_lt l a ha))
      (a11rm_f9 (swapBlocks l b) (a11rm_swapBlocks_val_lt l b hb))) := by
  unfold trAt
  rw [dif_pos ⟨a11rm_swapBlocks_val_lt l a ha, a11rm_swapBlocks_val_lt l b hb, hab⟩]
  rfl

private theorem a11rm_tv_mul_tv_mul_tv (i j : Fin 9) (hij : i ≠ j) :
    ((SpecialLinearGroup.transvection hij (1 : F2) *
      SpecialLinearGroup.transvection hij.symm (1 : F2) *
      SpecialLinearGroup.transvection hij (1 : F2) : SL 9) : Matrix (Fin 9) (Fin 9) F2) =
      signedPerm (Equiv.swap i j) (1 : Fin 9 → F2) := by
  rw [← coeMonoidHom_apply]
  simp only [map_mul, coeMonoidHom_apply, transvection_coe, Matrix.add_mul, Matrix.mul_add,
    Matrix.one_mul, Matrix.mul_one, single_mul_single_same,
    single_mul_single_of_ne _ _ _ _ hij.symm]
  ext r s
  simp only [Matrix.add_apply, Matrix.one_apply, single_apply, signedPerm_apply,
    Equiv.swap_apply_def, Matrix.zero_apply, Pi.one_apply]
  grind

private theorem a11rm_typeARealizes_eq {m : ℕ}
    {w : (coxeterMatrix (isFiniteType_A m)).Group}
    {π : Equiv.Perm (Fin (m + 1))} (h : TypeARealizes m w π) : w = typeAWeylHom m π :=
  typeARealizes_inj m h (typeAWeylOf_spec m π)

private theorem a11rm_typeARealizes_perm_unique {m : ℕ}
    {w : (coxeterMatrix (isFiniteType_A m)).Group}
    {π π' : Equiv.Perm (Fin (m + 1))}
    (h : TypeARealizes m w π) (h' : TypeARealizes m w π') : π = π' :=
  typeAWeylHom_injective m (by rw [← a11rm_typeARealizes_eq h, ← a11rm_typeARealizes_eq h'])

private theorem a11rm_permSL_coe (m : ℕ) (π : Equiv.Perm (Fin (m + 1))) :
    ((permSL m π : SL (m + 1)) : Matrix (Fin (m + 1)) (Fin (m + 1)) F2) =
      signedPerm π (1 : Fin (m + 1) → F2) := by
  obtain ⟨π', hcoe, hact⟩ := slWeylLift_signedPerm (m := m) two_eq_zero (typeAWeylHom m π)
  have hπ' : TypeARealizes m (typeAWeylHom m π) π' := hact
  have hπ : TypeARealizes m (typeAWeylHom m π) π := typeAWeylOf_spec m π
  have hEq : π = π' := a11rm_typeARealizes_perm_unique hπ hπ'
  rw [hEq] at hcoe ⊢
  simpa [permSL, SpecialLinearGroup.coeMonoidHom_apply] using hcoe

private theorem a11rm_permSL_swap_eq_transvection (i j : Fin 9) (hij : i ≠ j) :
    permSL 8 (Equiv.swap i j) =
      SpecialLinearGroup.transvection hij (1 : F2) *
      SpecialLinearGroup.transvection hij.symm (1 : F2) *
      SpecialLinearGroup.transvection hij (1 : F2) := by
  apply coeMonoidHom_injective
  change ((permSL 8 (Equiv.swap i j) : SL 9) : Matrix (Fin 9) (Fin 9) F2) =
    ((SpecialLinearGroup.transvection hij (1 : F2) *
      SpecialLinearGroup.transvection hij.symm (1 : F2) *
      SpecialLinearGroup.transvection hij (1 : F2) : SL 9) : Matrix (Fin 9) (Fin 9) F2)
  rw [a11rm_permSL_coe]
  exact (a11rm_tv_mul_tv_mul_tv i j hij).symm

private theorem a11rm_trAt_eq_tvAt_mul (l : Fin 4) (a b : Fin 12)
    (ha : blk a ≠ l) (hb : blk b ≠ l) (hab : a ≠ b) :
    trAt l a b = tvAt l a b * tvAt l b a * tvAt l a b := by
  rw [a11rm_trAt_eq l a b ha hb hab, a11rm_tvAt_eq l a b ha hb hab,
    a11rm_tvAt_eq l b a hb ha hab.symm]
  exact a11rm_permSL_swap_eq_transvection _ _ _

private theorem a11rm_coh {G : Type} [Group G] (Φ : Fin 4 → SL 9 →* G) (hΦ : Coherent Φ)
    (l m : Fin 4) (a b : Fin 12) (hab : a ≠ b)
    (ha : blk a ≠ l) (hb : blk b ≠ l) (ha' : blk a ≠ m) (hb' : blk b ≠ m) :
    Φ l (trAt l a b) = Φ m (trAt m a b) := by
  rw [a11rm_trAt_eq_tvAt_mul l a b ha hb hab, a11rm_trAt_eq_tvAt_mul m a b ha' hb' hab]
  rw [map_mul, map_mul, map_mul, map_mul]
  rw [hΦ l m a b hab ha hb ha' hb', hΦ l m b a hab.symm hb ha hb' ha']

private def a11rm_pairExp (i j k n : Fin 9) : ℕ :=
  if (i = k ∧ j = n) ∨ (i = n ∧ j = k) then 1
  else if i = k ∨ i = n ∨ j = k ∨ j = n then 3 else 2

private def a11rm_pairExp12 (a b c d : Fin 12) : ℕ :=
  if (a = c ∧ b = d) ∨ (a = d ∧ b = c) then 1
  else if a = c ∨ a = d ∨ b = c ∨ b = d then 3 else 2

private theorem a11rm_f9_eq_iff {x y : Fin 12} {hx : x.val < 9} {hy : y.val < 9} :
    a11rm_f9 x hx = a11rm_f9 y hy ↔ x = y := by
  constructor
  · intro h; exact Fin.ext (by simpa [a11rm_f9] using congrArg Fin.val h)
  · intro h; subst h; rfl

private theorem a11rm_pairExp_eq12 (a b c d : Fin 12)
    (ha : a.val < 9) (hb : b.val < 9) (hc : c.val < 9) (hd : d.val < 9) :
    a11rm_pairExp (a11rm_f9 a ha) (a11rm_f9 b hb) (a11rm_f9 c hc) (a11rm_f9 d hd) =
      a11rm_pairExp12 a b c d := by
  simp only [a11rm_pairExp, a11rm_pairExp12, a11rm_f9_eq_iff]

private theorem a11rm_pairExp12_congr (f : Fin 12 → Fin 12) (hf : Function.Injective f)
    (a b c d : Fin 12) :
    a11rm_pairExp12 (f a) (f b) (f c) (f d) = a11rm_pairExp12 a b c d := by
  simp only [a11rm_pairExp12, hf.eq_iff]

private theorem a11rm_pairExp12_coxeter :
    ∀ r t : Fin 11, a11rm_pairExp12 r.castSucc r.succ t.castSucc t.succ =
      coxeterMatrix (isFiniteType_A 11) r t := by
  simp only [coxeterMatrix_A_apply]
  decide

private theorem a11rm_pairExp_eq (l : Fin 4) (r t : Fin 11)
    (hr1 : blk r.castSucc ≠ l) (hr2 : blk r.succ ≠ l)
    (ht1 : blk t.castSucc ≠ l) (ht2 : blk t.succ ≠ l) :
    a11rm_pairExp
      (a11rm_f9 (swapBlocks l r.castSucc) (a11rm_swapBlocks_val_lt l _ hr1))
      (a11rm_f9 (swapBlocks l r.succ) (a11rm_swapBlocks_val_lt l _ hr2))
      (a11rm_f9 (swapBlocks l t.castSucc) (a11rm_swapBlocks_val_lt l _ ht1))
      (a11rm_f9 (swapBlocks l t.succ) (a11rm_swapBlocks_val_lt l _ ht2)) =
    coxeterMatrix (isFiniteType_A 11) r t := by
  rw [a11rm_pairExp_eq12, a11rm_pairExp12_congr (swapBlocks l) (swapBlocks l).injective,
    a11rm_pairExp12_coxeter]

private theorem a11rm_braid_pow (a b c : Fin 9) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    (Equiv.swap a b * Equiv.swap a c)^3 = 1 := by
  have h1 : Equiv.swap a b * Equiv.swap a c * Equiv.swap a b = Equiv.swap b c := by
    ext x; simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_def]; grind
  have h2 : Equiv.swap a c * Equiv.swap a b * Equiv.swap a c = Equiv.swap b c := by
    ext x; simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_def]; grind
  calc (Equiv.swap a b * Equiv.swap a c)^3
      = (Equiv.swap a b * Equiv.swap a c * Equiv.swap a b) *
        (Equiv.swap a c * Equiv.swap a b * Equiv.swap a c) := by
        simp only [pow_succ, pow_zero, one_mul, mul_assoc]
    _ = Equiv.swap b c * Equiv.swap b c := by rw [h1, h2]
    _ = 1 := Equiv.swap_mul_self b c

private theorem a11rm_commute_swap (a b c d : Fin 9) (hab : a ≠ b) (hcd : c ≠ d)
    (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) :
    Equiv.swap a b * Equiv.swap c d = Equiv.swap c d * Equiv.swap a b := by
  ext x; simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_def]; grind

private theorem a11rm_disjoint_pow (a b c d : Fin 9) (hab : a ≠ b) (hcd : c ≠ d)
    (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) :
    (Equiv.swap a b * Equiv.swap c d)^2 = 1 := by
  have hcomm := a11rm_commute_swap a b c d hab hcd hac had hbc hbd
  rw [sq]
  calc Equiv.swap a b * Equiv.swap c d * (Equiv.swap a b * Equiv.swap c d)
      = Equiv.swap a b * (Equiv.swap c d * Equiv.swap a b) * Equiv.swap c d := by
        simp only [mul_assoc]
    _ = Equiv.swap a b * (Equiv.swap a b * Equiv.swap c d) * Equiv.swap c d := by rw [hcomm]
    _ = Equiv.swap a b * Equiv.swap a b * (Equiv.swap c d * Equiv.swap c d) := by
        simp only [mul_assoc]
    _ = 1 := by rw [Equiv.swap_mul_self, Equiv.swap_mul_self, mul_one]

private theorem a11rm_pairExp_pow (i j k n : Fin 9) (hij : i ≠ j) (hkn : k ≠ n) :
    (Equiv.swap i j * Equiv.swap k n) ^ a11rm_pairExp i j k n = 1 := by
  rw [a11rm_pairExp]
  by_cases h1 : (i = k ∧ j = n) ∨ (i = n ∧ j = k)
  · rw [if_pos h1]
    rcases h1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rw [Equiv.swap_mul_self]; simp
    · rw [Equiv.swap_comm i j, Equiv.swap_mul_self]; simp
  · rw [if_neg h1]
    by_cases h2 : i = k ∨ i = n ∨ j = k ∨ j = n
    · rw [if_pos h2]
      rcases h2 with h | h | h | h
      · subst k
        have hjn : j ≠ n := fun hjn => h1 (Or.inl ⟨rfl, hjn⟩)
        simpa using a11rm_braid_pow i j n hij hkn hjn
      · subst n
        have hik : i ≠ k := fun hki => hkn hki.symm
        have hjk : j ≠ k := fun hjk => h1 (Or.inr ⟨rfl, hjk⟩)
        simpa [Equiv.swap_comm] using a11rm_braid_pow i j k hij hik hjk
      · subst k
        have hin : i ≠ n := fun hin => h1 (Or.inr ⟨hin, rfl⟩)
        simpa [Equiv.swap_comm] using a11rm_braid_pow j i n hij.symm hkn hin
      · subst n
        have hik : i ≠ k := fun hik => h1 (Or.inl ⟨hik, rfl⟩)
        simpa [Equiv.swap_comm] using a11rm_braid_pow j i k hij.symm hkn.symm hik
    · rw [if_neg h2]
      have hik : i ≠ k := fun h => h2 (Or.inl h)
      have hin : i ≠ n := fun h => h2 (Or.inr (Or.inl h))
      have hjk : j ≠ k := fun h => h2 (Or.inr (Or.inr (Or.inl h)))
      have hjn : j ≠ n := fun h => h2 (Or.inr (Or.inr (Or.inr h)))
      simpa using a11rm_disjoint_pow i j k n hij hkn hik hin hjk hjn

private theorem a11rm_exists_block_avoid2 :
    ∀ a b : Fin 12, ∃ l : Fin 4, blk a ≠ l ∧ blk b ≠ l := by decide

private theorem a11rm_exists_block_avoid4 :
    ∀ r t : Fin 11, ∃ l : Fin 4,
      blk r.castSucc ≠ l ∧ blk r.succ ≠ l ∧ blk t.castSucc ≠ l ∧ blk t.succ ≠ l := by
  decide

private noncomputable def a11rm_g {G : Type} [Group G] (Φ : Fin 4 → SL 9 →* G)
    (r : Fin 11) : G :=
  Φ (Classical.choose (a11rm_exists_block_avoid2 r.castSucc r.succ))
    (trAt (Classical.choose (a11rm_exists_block_avoid2 r.castSucc r.succ)) r.castSucc r.succ)

private theorem a11rm_g_eq {G : Type} [Group G] (Φ : Fin 4 → SL 9 →* G) (hΦ : Coherent Φ)
    (r : Fin 11) (l : Fin 4) (hl1 : blk r.castSucc ≠ l) (hl2 : blk r.succ ≠ l) :
    a11rm_g Φ r = Φ l (trAt l r.castSucc r.succ) := by
  unfold a11rm_g
  exact a11rm_coh Φ hΦ _ l _ _ (Fin.castSucc_lt_succ.ne)
    (Classical.choose_spec (a11rm_exists_block_avoid2 r.castSucc r.succ)).1
    (Classical.choose_spec (a11rm_exists_block_avoid2 r.castSucc r.succ)).2 hl1 hl2

private theorem a11rm_trAt_mul_trAt_pow (l : Fin 4) (r t : Fin 11)
    (hl1 : blk r.castSucc ≠ l) (hl2 : blk r.succ ≠ l)
    (ht1 : blk t.castSucc ≠ l) (ht2 : blk t.succ ≠ l) :
    (trAt l r.castSucc r.succ * trAt l t.castSucc t.succ) ^
      (coxeterMatrix (isFiniteType_A 11) r t) = 1 := by
  have hperm : (Equiv.swap
        (a11rm_f9 ((swapBlocks l) r.castSucc) (a11rm_swapBlocks_val_lt l _ hl1))
        (a11rm_f9 ((swapBlocks l) r.succ) (a11rm_swapBlocks_val_lt l _ hl2)) *
      Equiv.swap
        (a11rm_f9 ((swapBlocks l) t.castSucc) (a11rm_swapBlocks_val_lt l _ ht1))
        (a11rm_f9 ((swapBlocks l) t.succ) (a11rm_swapBlocks_val_lt l _ ht2))) ^
        (coxeterMatrix (isFiniteType_A 11) r t) = 1 := by
    rw [← a11rm_pairExp_eq l r t hl1 hl2 ht1 ht2]
    exact a11rm_pairExp_pow _ _ _ _
      (a11rm_f9_ne (a11rm_swapBlocks_ne (Fin.castSucc_lt_succ.ne)))
      (a11rm_f9_ne (a11rm_swapBlocks_ne (Fin.castSucc_lt_succ.ne)))
  rw [a11rm_trAt_eq l r.castSucc r.succ hl1 hl2 (Fin.castSucc_lt_succ.ne),
      a11rm_trAt_eq l t.castSucc t.succ ht1 ht2 (Fin.castSucc_lt_succ.ne)]
  calc (permSL 8 (Equiv.swap _ _) * permSL 8 (Equiv.swap _ _)) ^
        (coxeterMatrix (isFiniteType_A 11) r t)
      = (permSL 8 (Equiv.swap _ _ * Equiv.swap _ _)) ^
        (coxeterMatrix (isFiniteType_A 11) r t) := by
          rw [map_mul]
    _ = permSL 8 ((Equiv.swap _ _ * Equiv.swap _ _) ^
        (coxeterMatrix (isFiniteType_A 11) r t)) := (map_pow (permSL 8) _ _).symm
    _ = permSL 8 1 := by rw [hperm]
    _ = 1 := map_one (permSL 8)

private theorem a11rm_coxeter {G : Type} [Group G] (Φ : Fin 4 → SL 9 →* G) (hΦ : Coherent Φ)
    (r t : Fin 11) :
    (a11rm_g Φ r * a11rm_g Φ t) ^ (coxeterMatrix (isFiniteType_A 11) r t) = 1 := by
  obtain ⟨l, hl1, hl2, ht1, ht2⟩ := a11rm_exists_block_avoid4 r t
  rw [a11rm_g_eq Φ hΦ r l hl1 hl2, a11rm_g_eq Φ hΦ t l ht1 ht2]
  have hmain := a11rm_trAt_mul_trAt_pow l r t hl1 hl2 ht1 ht2
  calc (Φ l (trAt l r.castSucc r.succ) * Φ l (trAt l t.castSucc t.succ)) ^
        (coxeterMatrix (isFiniteType_A 11) r t)
      = (Φ l (trAt l r.castSucc r.succ * trAt l t.castSucc t.succ)) ^
        (coxeterMatrix (isFiniteType_A 11) r t) := by
          rw [map_mul]
    _ = Φ l ((trAt l r.castSucc r.succ * trAt l t.castSucc t.succ) ^
        (coxeterMatrix (isFiniteType_A 11) r t)) := (map_pow (Φ l) _ _).symm
    _ = Φ l 1 := by rw [hmain]
    _ = 1 := map_one (Φ l)

private noncomputable def a11rm_rho0 {G : Type} [Group G] (Φ : Fin 4 → SL 9 →* G)
    (hΦ : Coherent Φ) : (coxeterMatrix (isFiniteType_A 11)).Group →* G :=
  (coxeterMatrix (isFiniteType_A 11)).toCoxeterSystem.lift
    ⟨a11rm_g Φ, fun r t => a11rm_coxeter Φ hΦ r t⟩

private noncomputable def a11rm_rho {G : Type} [Group G] (Φ : Fin 4 → SL 9 →* G)
    (hΦ : Coherent Φ) : Equiv.Perm (Fin 12) →* G :=
  (a11rm_rho0 Φ hΦ).comp (typeAWeylEquiv 11).toMonoidHom

private theorem a11rm_rho_simple {G : Type} [Group G] (Φ : Fin 4 → SL 9 →* G) (hΦ : Coherent Φ)
    (r : Fin 11) :
    a11rm_rho Φ hΦ (Equiv.swap r.castSucc r.succ) = a11rm_g Φ r := by
  unfold a11rm_rho a11rm_rho0
  rw [MonoidHom.comp_apply]
  rw [show (typeAWeylEquiv 11).toMonoidHom (Equiv.swap r.castSucc r.succ) =
      (coxeterMatrix (isFiniteType_A 11)).toCoxeterSystem.simple r from typeAWeylEquiv_swap 11 r]
  exact (coxeterMatrix (isFiniteType_A 11)).toCoxeterSystem.lift_apply_simple _ r

private theorem a11rm_exists_block_avoid3 :
    ∀ a b c : Fin 12, ∃ l : Fin 4, blk a ≠ l ∧ blk b ≠ l ∧ blk c ≠ l := by decide

private theorem a11rm_perm_swap_conj (a b d : Fin 12) (hab : a ≠ b) (had : a ≠ d)
    (hbd : b ≠ d) :
    Equiv.swap b d * Equiv.swap a b * Equiv.swap b d = Equiv.swap a d := by
  ext x
  simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_def]
  grind

private theorem a11rm_perm_swap_conj9 (a b d : Fin 9) (hab : a ≠ b) (had : a ≠ d)
    (hbd : b ≠ d) :
    Equiv.swap b d * Equiv.swap a b * Equiv.swap b d = Equiv.swap a d := by
  ext x
  simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_def]
  grind

private theorem a11rm_trAt_conj (l : Fin 4) (a b d : Fin 12)
    (ha : blk a ≠ l) (hb : blk b ≠ l) (hd : blk d ≠ l)
    (hab : a ≠ b) (had : a ≠ d) (hbd : b ≠ d) :
    trAt l b d * trAt l a b * trAt l b d = trAt l a d := by
  rw [a11rm_trAt_eq l b d hb hd hbd, a11rm_trAt_eq l a b ha hb hab,
    a11rm_trAt_eq l a d ha hd had]
  rw [← map_mul, ← map_mul]
  congr 1
  exact a11rm_perm_swap_conj9 _ _ _
    (a11rm_f9_ne (a11rm_swapBlocks_ne hab))
    (a11rm_f9_ne (a11rm_swapBlocks_ne had))
    (a11rm_f9_ne (a11rm_swapBlocks_ne hbd))

private theorem a11rm_rho_step {G : Type} [Group G] (Φ : Fin 4 → SL 9 →* G) (hΦ : Coherent Φ)
    (ρ : Equiv.Perm (Fin 12) →* G) (a b d : Fin 12)
    (hab : a ≠ b) (had : a ≠ d) (hbd : b ≠ d)
    (hPab : ∀ l, blk a ≠ l → blk b ≠ l → ρ (Equiv.swap a b) = Φ l (trAt l a b))
    (hPbd : ∀ l, blk b ≠ l → blk d ≠ l → ρ (Equiv.swap b d) = Φ l (trAt l b d)) :
    ∀ l, blk a ≠ l → blk d ≠ l → ρ (Equiv.swap a d) = Φ l (trAt l a d) := by
  intro l hl_a hl_d
  obtain ⟨m, hm_a, hm_b, hm_d⟩ := a11rm_exists_block_avoid3 a b d
  have hperm : Equiv.swap a d = Equiv.swap b d * Equiv.swap a b * Equiv.swap b d :=
    (a11rm_perm_swap_conj a b d hab had hbd).symm
  calc ρ (Equiv.swap a d)
      = ρ (Equiv.swap b d * Equiv.swap a b * Equiv.swap b d) := by rw [hperm]
    _ = ρ (Equiv.swap b d) * ρ (Equiv.swap a b) * ρ (Equiv.swap b d) := by
          rw [map_mul, map_mul]
    _ = Φ m (trAt m b d) * Φ m (trAt m a b) * Φ m (trAt m b d) := by
          rw [hPbd m hm_b hm_d, hPab m hm_a hm_b]
    _ = Φ m (trAt m b d * trAt m a b * trAt m b d) := by
          rw [map_mul, map_mul]
    _ = Φ m (trAt m a d) := by rw [a11rm_trAt_conj m a b d hm_a hm_b hm_d hab had hbd]
    _ = Φ l (trAt l a d) := a11rm_coh Φ hΦ m l a d had hm_a hm_d hl_a hl_d

private theorem a11rm_RhoEval_base {G : Type} [Group G] (Φ : Fin 4 → SL 9 →* G) (hΦ : Coherent Φ)
    (ρ : Equiv.Perm (Fin 12) →* G)
    (hbase : ∀ r : Fin 11, ρ (Equiv.swap r.castSucc r.succ) = a11rm_g Φ r) :
    ∀ r : Fin 11, ∀ l, blk r.castSucc ≠ l → blk r.succ ≠ l →
      ρ (Equiv.swap r.castSucc r.succ) = Φ l (trAt l r.castSucc r.succ) := by
  intro r l hl1 hl2
  rw [hbase r, a11rm_g_eq Φ hΦ r l hl1 hl2]

private theorem a11rm_rhoEval_aux {G : Type} [Group G] (Φ : Fin 4 → SL 9 →* G) (hΦ : Coherent Φ)
    (ρ : Equiv.Perm (Fin 12) →* G)
    (hbase : ∀ r : Fin 11, ρ (Equiv.swap r.castSucc r.succ) = a11rm_g Φ r) :
    ∀ a b : Fin 12, a.val < b.val → ∀ l, blk a ≠ l → blk b ≠ l →
      ρ (Equiv.swap a b) = Φ l (trAt l a b) := by
  intro a b
  induction b using Fin.induction with
  | zero => intro hab; omega
  | succ i ih =>
    intro hab l hl_a hl_b
    by_cases hlt : a.val < i.val
    · refine a11rm_rho_step Φ hΦ ρ a i.castSucc i.succ ?_ ?_ ?_
        (fun l' hl1 hl2 => ih (by simpa only [Fin.val_castSucc] using hlt) l' hl1 hl2)
        (a11rm_RhoEval_base Φ hΦ ρ hbase i) l hl_a hl_b
      · intro he
        have := congrArg Fin.val he
        simp only [Fin.val_castSucc] at this
        omega
      · intro he
        have := congrArg Fin.val he
        simp only [Fin.val_succ] at this
        omega
      · exact Fin.castSucc_lt_succ.ne
    · have hab' : a.val < i.val + 1 := by simpa [Fin.val_succ] using hab
      have ha : a = i.castSucc := by
        apply Fin.ext
        simp only [Fin.val_castSucc]
        omega
      subst ha
      rw [hbase i, a11rm_g_eq Φ hΦ i l hl_a hl_b]

private theorem a11rm_trAt_comm (l : Fin 4) (a b : Fin 12) : trAt l a b = trAt l b a := by
  unfold trAt
  by_cases h : (swapBlocks l a).val < 9 ∧ (swapBlocks l b).val < 9 ∧ a ≠ b
  · rw [dif_pos h]
    have h' : (swapBlocks l b).val < 9 ∧ (swapBlocks l a).val < 9 ∧ b ≠ a :=
      ⟨h.2.1, h.1, h.2.2.symm⟩
    rw [dif_pos h']
    exact congrArg (permSL 8) (Equiv.swap_comm _ _)
  · rw [dif_neg h]
    have h' : ¬ ((swapBlocks l b).val < 9 ∧ (swapBlocks l a).val < 9 ∧ b ≠ a) :=
      fun hh => h ⟨hh.2.1, hh.1, hh.2.2.symm⟩
    rw [dif_neg h']

theorem a11RhoMkInput_holds : ∀ (G : Type) [Group G] (Φ : Fin 4 → SL 9 →* G), Coherent Φ → ∃ ρ : Equiv.Perm (Fin 12) →* G, RhoEval Φ ρ := by
  intro G _ Φ hΦ
  refine ⟨a11rm_rho Φ hΦ, ?_⟩
  intro l a b hab ha hb
  rcases lt_or_gt_of_ne hab with h | h
  · exact a11rm_rhoEval_aux Φ hΦ (a11rm_rho Φ hΦ) (a11rm_rho_simple Φ hΦ) a b h l ha hb
  · have hh := a11rm_rhoEval_aux Φ hΦ (a11rm_rho Φ hΦ) (a11rm_rho_simple Φ hΦ) b a h l hb ha
    rw [← Equiv.swap_comm a b, a11rm_trAt_comm l b a] at hh
    exact hh

end CFSG.StandardType.A11

end
