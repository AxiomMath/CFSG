module

public import CFSG.LocalAnalysis.StandardType.FS81.OddCoreOrthRows

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.StandardType.FrameRoute.FS81

open scoped Matrix

@[expose] def hSeven : Set (Matrix (Fin 8) (Fin 8) (ZMod 3)) :=
  spSet fun σ s => σ 0 = 0 ∧ s 0 = 1 ∧ σ 1 = 1 ∧ ∏ i : Fin 6, s i.succ.succ = 1

theorem spMat_one_eq_diagonal {k : ℕ} (s : Fin k → ZMod 3) : spMat 1 s = Matrix.diagonal s := by
  ext i j
  by_cases h : i = j
  · subst h
    simp [spMat_apply]
  · simp [spMat_apply, h]

theorem eq_one_of_commute_sgn_pairs {m : GL (Fin 8) (ZMod 3)} {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hp3 : p ≠ 3) (hm : m ^ p = 1)
    (he : (m : Matrix (Fin 8) (Fin 8) (ZMod 3)) *ᵥ Pi.single 0 1 = Pi.single 0 1)
    (hc : ∀ j k : Fin 8, 2 ≤ j.val → 2 ≤ k.val → j ≠ k →
      (m : Matrix (Fin 8) (Fin 8) (ZMod 3)) * spMat 1 (sgnOn {j, k}) =
        spMat 1 (sgnOn {j, k}) * (m : Matrix (Fin 8) (Fin 8) (ZMod 3))) : m = 1 := by
  set M := (m : Matrix (Fin 8) (Fin 8) (ZMod 3)) with hM
  have hzero : ∀ a b : Fin 8, a ≠ b → (2 ≤ a.val ∨ 2 ≤ b.val) → M a b = 0 := by
    intro a b hab hab2
    have key : ∀ T : Finset (Fin 8), M * spMat 1 (sgnOn T) = spMat 1 (sgnOn T) * M →
        sgnOn T a ≠ sgnOn T b → M a b = 0 := by
      intro T hT hne
      have h := congrFun (congrFun hT a) b
      rw [spMat_one_eq_diagonal, Matrix.mul_diagonal, Matrix.diagonal_mul] at h
      have h' : (sgnOn T b - sgnOn T a) * M a b = 0 := by rw [sub_mul, mul_comm, h]; ring
      rcases mul_eq_zero.mp h' with h0 | h0
      · exact absurd (sub_eq_zero.mp h0).symm hne
      · exact h0
    obtain ⟨k, hk2, hka, hkb⟩ := (by decide : ∀ a b : Fin 8, ∃ k : Fin 8, 2 ≤ k.val ∧ k ≠ a ∧
      k ≠ b) a b
    rcases hab2 with ha2 | hb2
    · refine key {a, k} (hc a k ha2 hk2 hka.symm) ?_
      simp only [sgnOn, Finset.mem_insert, Finset.mem_singleton, true_or, if_true, Ne.symm hab,
        Ne.symm hkb, or_self, if_false]
      decide
    · refine key {b, k} (hc b k hb2 hk2 hkb.symm) ?_
      simp only [sgnOn, Finset.mem_insert, Finset.mem_singleton, true_or, if_true, hab,
        Ne.symm hka, or_self, if_false]
      decide
  have hcol0 : ∀ a, M a 0 = (Pi.single (0 : Fin 8) (1 : ZMod 3) : Fin 8 → ZMod 3) a := by
    intro a
    have := congrFun he a
    rwa [Matrix.mulVec_single_one, Matrix.col_apply] at this
  have hM00 : M 0 0 = 1 := by rw [hcol0]; simp
  have hM10 : M 1 0 = 0 := by rw [hcol0]; simp
  have hrow : ∀ a : Fin 8, 2 ≤ a.val → ∀ v, (M *ᵥ v) a = M a a * v a := by
    intro a ha v
    simp only [Matrix.mulVec, dotProduct]
    rw [Finset.sum_eq_single a]
    · intro b _ hba
      rw [hzero a b (Ne.symm hba) (Or.inl ha), zero_mul]
    · intro h
      exact absurd (Finset.mem_univ a) h
  have hrow1 : ∀ v, (M *ᵥ v) 1 = M 1 1 * v 1 := by
    intro v
    simp only [Matrix.mulVec, dotProduct]
    rw [Finset.sum_eq_single 1]
    · intro b _ hb1
      by_cases hb0 : b = 0
      · rw [hb0, hM10, zero_mul]
      · have hb2 : 2 ≤ b.val := by
          have h0 : b.val ≠ 0 := fun h => hb0 (Fin.ext h)
          have h1 : b.val ≠ 1 := fun h => hb1 (Fin.ext h)
          omega
        rw [hzero 1 b (Ne.symm hb1) (Or.inr hb2), zero_mul]
    · intro h
      exact absurd (Finset.mem_univ 1) h
  have hrow0 : ∀ v, (M *ᵥ v) 0 = v 0 + M 0 1 * v 1 := by
    intro v
    simp only [Matrix.mulVec, dotProduct]
    rw [Fin.sum_univ_succ, Fin.sum_univ_succ, hM00, one_mul]
    have : ∀ i : Fin 6, M 0 i.succ.succ * v i.succ.succ = 0 := by
      intro i
      rw [hzero 0 i.succ.succ (by decide +revert) (Or.inr (by simp [Fin.val_succ]))]
      exact zero_mul _
    simp only [this, Finset.sum_const_zero, add_zero]
    rfl
  have hMp : M ^ p = 1 := by rw [hM, ← Units.val_pow_eq_pow_val, hm, Units.val_one]
  have hpow1 : ∀ c : ZMod 3, c ^ p = 1 → c = 1 := by
    intro c hcp
    obtain ⟨q, hq⟩ : Odd p := hp.odd_of_ne_two hp2
    have hc3 : ∀ q : ℕ, ∀ c : ZMod 3, c ^ (2 * q + 1) = c := by
      intro q
      induction q with
      | zero => intro c; simp
      | succ q ih =>
        intro c
        rw [show 2 * (q + 1) + 1 = (2 * q + 1) + 2 by ring, pow_add, ih]
        revert c
        decide
    rw [hq, hc3] at hcp
    exact hcp
  have hdiag : ∀ a : Fin 8, 2 ≤ a.val → M a a = 1 := by
    intro a ha
    have hk : ∀ k : ℕ, (M ^ k *ᵥ Pi.single a 1) a = M a a ^ k := by
      intro k
      induction k with
      | zero => simp
      | succ k ih => rw [pow_succ', ← Matrix.mulVec_mulVec, hrow a ha, ih, pow_succ']
    have := hk p
    rw [hMp, Matrix.one_mulVec, Pi.single_eq_same] at this
    exact hpow1 _ this.symm
  have h11 : M 1 1 = 1 := by
    have hk : ∀ k : ℕ, (M ^ k *ᵥ Pi.single 1 1) 1 = M 1 1 ^ k := by
      intro k
      induction k with
      | zero => simp
      | succ k ih => rw [pow_succ', ← Matrix.mulVec_mulVec, hrow1, ih, pow_succ']
    have := hk p
    rw [hMp, Matrix.one_mulVec, Pi.single_eq_same] at this
    exact hpow1 _ this.symm
  have h01 : M 0 1 = 0 := by
    have hk1 : ∀ k : ℕ, (M ^ k *ᵥ Pi.single 1 1) 1 = 1 := by
      intro k
      induction k with
      | zero => simp
      | succ k ih => rw [pow_succ', ← Matrix.mulVec_mulVec, hrow1, ih, h11, mul_one]
    have hk : ∀ k : ℕ, (M ^ k *ᵥ Pi.single 1 1) 0 = k * M 0 1 := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        rw [pow_succ', ← Matrix.mulVec_mulVec, hrow0, ih, hk1, mul_one]
        push_cast
        ring
    have := hk p
    rw [hMp, Matrix.one_mulVec] at this
    simp only [Pi.single_apply] at this
    have hp0 : (p : ZMod 3) ≠ 0 := by
      rw [Ne, ZMod.natCast_eq_zero_iff]
      intro h3
      exact hp3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp h3).symm
    rcases mul_eq_zero.mp this.symm with h | h
    · exact absurd h hp0
    · exact h
  apply Units.ext
  rw [Units.val_one, ← hM]
  refine Matrix.ext_of_mulVec_single fun b => ?_
  rw [Matrix.one_mulVec]
  funext a
  rw [Matrix.mulVec_single_one, Matrix.col_apply]
  by_cases hb0 : b = 0
  · subst hb0
    exact hcol0 a
  by_cases hb1 : b = 1
  · subst hb1
    by_cases ha0 : a = 0
    · subst ha0
      rw [h01]
      simp
    by_cases ha1 : a = 1
    · subst ha1
      rw [h11]
      simp
    have ha2 : 2 ≤ a.val := by
      have h0 : a.val ≠ 0 := fun h => ha0 (Fin.ext h)
      have h1 : a.val ≠ 1 := fun h => ha1 (Fin.ext h)
      omega
    rw [hzero a 1 ha1 (Or.inl ha2)]
    simp [ha1]
  have hb2 : 2 ≤ b.val := by
    have h0 : b.val ≠ 0 := fun h => hb0 (Fin.ext h)
    have h1 : b.val ≠ 1 := fun h => hb1 (Fin.ext h)
    omega
  by_cases hab : a = b
  · subst hab
    rw [hdiag a hb2]
    simp
  · rw [hzero a b hab (Or.inr hb2)]
    simp [hab]

@[expose] def fixE0 (k : ℕ) : Subgroup (GL (Fin (k + 1)) (ZMod 3)) where
  carrier := {x | (x : Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 3)) *ᵥ Pi.single 0 1 = Pi.single 0 1}
  mul_mem' := fun {x y} hx hy => by
    simp only [Set.mem_setOf_eq] at hx hy ⊢
    rw [Units.val_mul, ← Matrix.mulVec_mulVec, hy, hx]
  one_mem' := by simp only [Set.mem_setOf_eq, Units.val_one, Matrix.one_mulVec]
  inv_mem' := fun {x} hx => by
    simp only [Set.mem_setOf_eq] at hx ⊢
    conv_lhs => rw [← hx]
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]

theorem mem_fixE0 {k : ℕ} {x : GL (Fin (k + 1)) (ZMod 3)} :
    x ∈ fixE0 k ↔ (x : Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 3)) *ᵥ Pi.single 0 1 = Pi.single 0 1 :=
  Iff.rfl

theorem spMat_comm_diag_perm {k : ℕ} (α : Fin k → ZMod 3) (π : Equiv.Perm (Fin k))
    (hπ : π * π = 1) :
    spMat 1 α * spMat π (fun _ => 1) * spMat 1 α * spMat π (fun _ => 1) =
      spMat 1 (fun x => α x * α (π x)) := by
  rw [spMat_mul, spMat_mul, spMat_mul, one_mul, mul_one, hπ]
  refine spMat_congr rfl fun x => ?_
  simp only [Equiv.Perm.coe_one, id, mul_one]
  have : π (π x) = x := by rw [← Equiv.Perm.mul_apply, hπ, Equiv.Perm.one_apply]
  rw [this, mul_comm]

theorem sgnOn_pair_comm {k : ℕ} {i j l : Fin k} (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l) :
    (fun x => sgnOn {i, l} x * sgnOn {i, l} (Equiv.swap j l x)) = sgnOn {j, l} := by
  funext x
  by_cases hxj : x = j
  · subst hxj
    rw [Equiv.swap_apply_left]
    simp [sgnOn, Ne.symm hij, hjl]
  by_cases hxl : x = l
  · subst hxl
    rw [Equiv.swap_apply_right]
    simp [sgnOn, hjl, Ne.symm hjl, Ne.symm hij]
  rw [Equiv.swap_apply_of_ne_of_ne hxj hxl]
  have h1 := sign_mul_self (isSign_sgnOn {i, l}) x
  rw [h1]
  simp [sgnOn, hxj, hxl]

theorem prod_succ_succ_sgnOn {T : Finset (Fin 8)} (h0 : (0 : Fin 8) ∉ T) (h1 : (1 : Fin 8) ∉ T) :
    ∏ i : Fin 6, sgnOn T i.succ.succ = (-1) ^ T.card := by
  have e0 : sgnOn T 0 = 1 := if_neg h0
  have e1 : sgnOn T (Fin.succ 0) = 1 := if_neg h1
  rw [← prod_sgnOn T, Fin.prod_univ_succ (fun i : Fin 8 => sgnOn T i),
    Fin.prod_univ_succ (fun i : Fin 7 => sgnOn T i.succ), e0, e1, one_mul, one_mul]

theorem sgnOn_mem_hSeven {T : Finset (Fin 8)} (h0 : (0 : Fin 8) ∉ T) (h1 : (1 : Fin 8) ∉ T)
    (heven : Even T.card) : spMat 1 (sgnOn T) ∈ hSeven :=
  ⟨1, sgnOn T, isSign_sgnOn T, ⟨rfl, if_neg h0, rfl, by rw [prod_succ_succ_sgnOn h0 h1,
    heven.neg_one_pow]⟩, rfl⟩

theorem perm_mem_hSeven {π : Equiv.Perm (Fin 8)} (h0 : π 0 = 0) (h1 : π 1 = 1) :
    spMat π (fun _ => 1) ∈ hSeven :=
  ⟨π, fun _ => 1, fun _ => Or.inl rfl, ⟨h0, rfl, h1, by simp⟩, rfl⟩

theorem e7_eq_one_of_fix {Xg Mg : Subgroup (GL (Fin (7 + 1)) (ZMod 3))}
    (hH : ∀ A ∈ hSeven, ∃ x ∈ Xg, (x : Matrix (Fin 8) (Fin 8) (ZMod 3)) = A)
    (hcard : Nat.card ↥(Xg ⊓ fixE0 7) = 2903040)
    (hMX : Mg ≤ Xg) (hMn : ∀ g ∈ Xg, ∀ m ∈ Mg, g * m * g⁻¹ ∈ Mg)
    {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hMp : ∀ m ∈ Mg, m ^ p = 1)
    {m : GL (Fin (7 + 1)) (ZMod 3)} (hm : m ∈ Mg)
    (he : (m : Matrix (Fin 8) (Fin 8) (ZMod 3)) *ᵥ Pi.single 0 1 = Pi.single 0 1) : m = 1 := by
  have : Fact p.Prime := ⟨hp⟩
  set Z := Mg ⊓ fixE0 7 with hZ
  have hZle : Z ≤ Xg ⊓ fixE0 7 := fun z hz => ⟨hMX hz.1, hz.2⟩
  have hZdvd : Nat.card Z ∣ 2903040 := hcard ▸ Subgroup.card_dvd_of_le hZle
  have hZp : IsPGroup p ↥Z := fun z => ⟨1, Subtype.ext (by
    rw [pow_one, Subgroup.coe_pow, hMp z z.2.1, Subgroup.coe_one])⟩
  obtain ⟨a, ha⟩ := hZp.exists_card_eq
  have hmZ : m ∈ Z := ⟨hm, he⟩
  have ha1 : a ≤ 1 := by
    by_contra h
    have hp2 : p ^ 2 ∣ 2903040 :=
      (pow_dvd_pow p (by omega : 2 ≤ a)).trans (ha ▸ hZdvd)
    have hcop : Nat.Coprime (p ^ 2) (2 ^ 10 * 3 ^ 4) := by
      apply Nat.Coprime.pow_left
      apply Nat.Coprime.mul_right
      · exact Nat.Coprime.pow_right _ ((Nat.coprime_primes hp Nat.prime_two).mpr (by omega))
      · exact Nat.Coprime.pow_right _ ((Nat.coprime_primes hp Nat.prime_three).mpr (by omega))
    have h35 : p ^ 2 ∣ 35 := hcop.dvd_of_dvd_mul_left (by norm_num at hp2 ⊢; exact hp2)
    have h35' := Nat.le_of_dvd (by norm_num) h35
    have hple : p ≤ 5 := by nlinarith
    have hp5' : p = 5 := le_antisymm hple hp5
    subst hp5'
    norm_num at h35
  by_contra hm1
  have hcardZ : Nat.card Z = p := by
    interval_cases a
    · rw [pow_zero] at ha
      exact absurd (Subgroup.eq_bot_of_card_eq Z ha ▸ hmZ) (by simpa using hm1)
    · rw [pow_one] at ha
      exact ha
  have hgen : Subgroup.zpowers (⟨m, hmZ⟩ : ↥Z) = ⊤ :=
    zpowers_eq_top_of_prime_card hcardZ (fun h => hm1 (congrArg Subtype.val h))
  have hpowmap : ∀ x ∈ Xg ⊓ fixE0 7, ∃ i : ℤ, x * m * x⁻¹ = m ^ i := by
    intro x hx
    have hxZ : x * m * x⁻¹ ∈ Z := ⟨hMn x hx.1 m hm, (fixE0 7).mul_mem ((fixE0 7).mul_mem hx.2 he)
      ((fixE0 7).inv_mem hx.2)⟩
    have hmem : (⟨x * m * x⁻¹, hxZ⟩ : ↥Z) ∈ Subgroup.zpowers (⟨m, hmZ⟩ : ↥Z) := hgen ▸ trivial
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp hmem
    exact ⟨i, (congrArg Subtype.val hi).symm.trans (by simp)⟩
  have hcomm : ∀ x y : GL (Fin (7 + 1)) (ZMod 3), x ∈ Xg ⊓ fixE0 7 → y ∈ Xg ⊓ fixE0 7 →
      x * x = 1 → y * y = 1 → x * y * x * y * m = m * (x * y * x * y) := by
    intro x y hx hy hxx hyy
    have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right hxx
    have hyi : y⁻¹ = y := inv_eq_of_mul_eq_one_right hyy
    obtain ⟨i, hi⟩ := hpowmap x hx
    obtain ⟨j, hj⟩ := hpowmap y hy
    have hxt : ∀ t : ℤ, x * m ^ t * x⁻¹ = m ^ (i * t) := by
      intro t
      rw [← conj_zpow, hi, ← zpow_mul]
    have hyt : ∀ t : ℤ, y * m ^ t * y⁻¹ = m ^ (j * t) := by
      intro t
      rw [← conj_zpow, hj, ← zpow_mul]
    have hii : m ^ (i * i) = m := by
      have h1 : x * (x * m * x⁻¹) * x⁻¹ = m := by
        rw [show x * (x * m * x⁻¹) * x⁻¹ = (x * x) * m * (x⁻¹ * x⁻¹) by group, hxx, hxi, hxx]
        group
      rw [hi, hxt] at h1
      exact h1
    have hjj : m ^ (j * j) = m := by
      have h1 : y * (y * m * y⁻¹) * y⁻¹ = m := by
        rw [show y * (y * m * y⁻¹) * y⁻¹ = (y * y) * m * (y⁻¹ * y⁻¹) by group, hyy, hyi, hyy]
        group
      rw [hj, hyt] at h1
      exact h1
    have hconj : (x * y * x * y) * m * (x * y * x * y)⁻¹ = m := by
      have e1 : (x * y * x * y) * m * (x * y * x * y)⁻¹ =
          x * (y * (x * (y * m * y⁻¹) * x⁻¹) * y⁻¹) * x⁻¹ := by
        group
      rw [e1, hj, hxt, hyt, hxt]
      have : i * (j * (i * j)) = (i * i) * (j * j) := by ring
      rw [this, zpow_mul, hii, hjj]
    calc x * y * x * y * m = (x * y * x * y) * m * (x * y * x * y)⁻¹ * (x * y * x * y) := by group
      _ = m * (x * y * x * y) := by rw [hconj]
  refine hm1 (eq_one_of_commute_sgn_pairs hp (by omega) (by omega) (hMp m hm) he fun j k hj hk hjk => ?_)
  obtain ⟨i, hi2, hij, hik⟩ := (by decide : ∀ a b : Fin 8, ∃ k : Fin 8, 2 ≤ k.val ∧ k ≠ a ∧
    k ≠ b) j k
  have hne01 : ∀ a : Fin 8, 2 ≤ a.val → a ≠ 0 ∧ a ≠ 1 := fun a ha =>
    ⟨fun h => by rw [h] at ha; simp at ha, fun h => by rw [h] at ha; simp at ha⟩
  have hα : spMat 1 (sgnOn {i, k}) ∈ hSeven := by
    refine sgnOn_mem_hSeven ?_ ?_ (by rw [Finset.card_pair hik]; exact even_two)
    · simp [Ne.symm (hne01 i hi2).1, Ne.symm (hne01 k hk).1]
    · simp [Ne.symm (hne01 i hi2).2, Ne.symm (hne01 k hk).2]
  have hπ : spMat (Equiv.swap j k) (fun _ => 1) ∈ hSeven :=
    perm_mem_hSeven (Equiv.swap_apply_of_ne_of_ne (hne01 j hj).1.symm (hne01 k hk).1.symm)
      (Equiv.swap_apply_of_ne_of_ne (hne01 j hj).2.symm (hne01 k hk).2.symm)
  obtain ⟨x, hxX, hx⟩ := hH _ hα
  obtain ⟨y, hyX, hy⟩ := hH _ hπ
  have hxe : x ∈ fixE0 7 := by rw [mem_fixE0, hx]; exact spMat_mulVec_e0 rfl (if_neg (by
    simp [Ne.symm (hne01 i hi2).1, Ne.symm (hne01 k hk).1]))
  have hye : y ∈ fixE0 7 := by
    rw [mem_fixE0, hy]
    exact spMat_mulVec_e0 (Equiv.swap_apply_of_ne_of_ne (hne01 j hj).1.symm (hne01 k hk).1.symm) rfl
  have hxx : x * x = 1 := gl_mul_self hx (by rw [one_mul]) (fun t => by
    simpa using sign_mul_self (isSign_sgnOn {i, k}) t)
  have hyy : y * y = 1 := gl_mul_self hy (Equiv.swap_mul_self j k) (fun _ => by simp)
  have hc := hcomm x y ⟨hxX, hxe⟩ ⟨hyX, hye⟩ hxx hyy
  have hmat : ((x * y * x * y : GL (Fin (7 + 1)) (ZMod 3)) : Matrix (Fin 8) (Fin 8) (ZMod 3)) =
      spMat 1 (sgnOn {j, k}) := by
    simp only [Units.val_mul]
    rw [hx, hy, spMat_comm_diag_perm _ _ (Equiv.swap_mul_self j k),
      sgnOn_pair_comm hij hik hjk]
  have := congrArg Units.val hc
  simp only [Units.val_mul] at this
  rw [← Units.val_mul, ← Units.val_mul, ← Units.val_mul, hmat] at this
  exact this.symm

theorem e7_inverts {Xg Mg : Subgroup (GL (Fin (7 + 1)) (ZMod 3))}
    (hH : ∀ A ∈ hSeven, ∃ x ∈ Xg, (x : Matrix (Fin 8) (Fin 8) (ZMod 3)) = A)
    (hcard : Nat.card ↥(Xg ⊓ fixE0 7) = 2903040)
    (hMX : Mg ≤ Xg) (hMn : ∀ g ∈ Xg, ∀ m ∈ Mg, g * m * g⁻¹ ∈ Mg)
    (hMc : ∀ a ∈ Mg, ∀ b ∈ Mg, a * b = b * a)
    {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hMp : ∀ m ∈ Mg, m ^ p = 1)
    {σ : GL (Fin (7 + 1)) (ZMod 3)} (hσX : σ ∈ Xg) (hσ2 : σ * σ = 1)
    (hσe : (σ : Matrix (Fin 8) (Fin 8) (ZMod 3)) *ᵥ Pi.single 0 1 = Pi.single 0 1)
    {w : Fin 8 → ZMod 3}
    (hfix : ∀ v, (σ : Matrix (Fin 8) (Fin 8) (ZMod 3)) *ᵥ v = v →
      ∃ c d : ZMod 3, v = c • Pi.single 0 1 + d • w)
    {m : GL (Fin (7 + 1)) (ZMod 3)} (hm : m ∈ Mg) : σ * m * σ⁻¹ = m⁻¹ :=
  inv_of_centralizer_trivial hMn hMc hσX hσ2 (fun m' hm' hcomm =>
    e7_eq_one_of_fix hH hcard hMX hMn hp hp5 hMp hm'
      (mulVec_fix_of_commute hp hp5 (hMp m' hm') hcomm hσe hfix)) hm

theorem e7_eq_bot {Xg Mg : Subgroup (GL (Fin (7 + 1)) (ZMod 3))}
    (hH : ∀ A ∈ hSeven, ∃ x ∈ Xg, (x : Matrix (Fin 8) (Fin 8) (ZMod 3)) = A)
    (hcard : Nat.card ↥(Xg ⊓ fixE0 7) = 2903040)
    (hMX : Mg ≤ Xg) (hMn : ∀ g ∈ Xg, ∀ m ∈ Mg, g * m * g⁻¹ ∈ Mg)
    (hMc : ∀ a ∈ Mg, ∀ b ∈ Mg, a * b = b * a)
    {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hMp : ∀ m ∈ Mg, m ^ p = 1) : Mg = ⊥ := by
  set T₁ : Finset (Fin 8) := {1, 2, 3, 4, 5, 6, 7} with hT₁
  set T₂ : Finset (Fin 8) := {1, 2, 3, 4, 5} with hT₂
  set T₃ : Finset (Fin 8) := {2, 3, 4, 5, 6, 7} with hT₃
  obtain ⟨s₁, hs₁X, hs₁⟩ := hH (spMat 1 (sgnOn T₁))
    ⟨1, sgnOn T₁, isSign_sgnOn T₁, ⟨rfl, by decide, rfl, by decide⟩, rfl⟩
  obtain ⟨s₂, hs₂X, hs₂⟩ := hH (spMat (Equiv.swap 6 7) (sgnOn T₂))
    ⟨Equiv.swap 6 7, sgnOn T₂, isSign_sgnOn T₂, ⟨by decide, by decide, by decide, by decide⟩, rfl⟩
  obtain ⟨s₃, hs₃X, hs₃⟩ := hH (spMat 1 (sgnOn T₃))
    ⟨1, sgnOn T₃, isSign_sgnOn T₃, ⟨rfl, by decide, rfl, by decide⟩, rfl⟩
  obtain ⟨y, hyX, hy⟩ := hH (spMat 1 (sgnOn ({2, 6} : Finset (Fin 8))))
    ⟨1, _, isSign_sgnOn _, ⟨rfl, by decide, rfl, by decide⟩, rfl⟩
  obtain ⟨z₁, hz₁X, hz₁⟩ := hH _ (perm_mem_hSeven (π := Equiv.swap 2 6 * Equiv.swap 3 7)
    (by decide) (by decide))
  obtain ⟨z₂, hz₂X, hz₂⟩ := hH _ (perm_mem_hSeven (π := Equiv.swap 4 6 * Equiv.swap 5 7)
    (by decide) (by decide))
  have hyi : y⁻¹ = y := inv_eq_of_mul_eq_one_right (gl_mul_self hy (by decide) (by decide))
  have hz₁i : z₁⁻¹ = z₁ := inv_eq_of_mul_eq_one_right (gl_mul_self hz₁ (by decide) (by decide))
  have hz₂i : z₂⁻¹ = z₂ := inv_eq_of_mul_eq_one_right (gl_mul_self hz₂ (by decide) (by decide))
  have hinv₁ : ∀ m ∈ Mg, s₁ * m * s₁⁻¹ = m⁻¹ := fun m hm =>
    e7_inverts hH hcard hMX hMn hMc hp hp5 hMp hs₁X (gl_mul_self hs₁ (by decide) (by decide))
      (by rw [hs₁]; exact spMat_mulVec_e0 rfl (by decide)) (w := 0) (fun v hv => by
        rw [hs₁] at hv
        have hz : ∀ i ∈ T₁, v i = 0 := fun i hi => eq_zero_of_mulVec_sgnOn hv hi
        refine ⟨v 0, 0, funext fun i => ?_⟩
        by_cases hi : i = 0
        · subst hi
          simp
        · have hiT : i ∈ T₁ := by
            rw [hT₁]
            revert hi
            revert i
            decide
          simp [hi, hz i hiT]) hm
  have hinv₂ : ∀ m ∈ Mg, s₂ * m * s₂⁻¹ = m⁻¹ := fun m hm =>
    e7_inverts hH hcard hMX hMn hMc hp hp5 hMp hs₂X (gl_mul_self hs₂ (by decide) (by decide))
      (by rw [hs₂]; exact spMat_mulVec_e0 (by decide) (by decide))
      (w := Pi.single 6 1 + Pi.single 7 1) (fun v hv => by
        rw [hs₂] at hv
        obtain ⟨hz, h67⟩ := mulVec_swap_sgnOn (T := T₂) (by decide) (by decide) hv
        refine ⟨v 0, v 6, funext fun i => ?_⟩
        fin_cases i <;> simp [hz, hT₂, h67]) hm
  have hinv₃ : ∀ m ∈ Mg, s₃ * m * s₃⁻¹ = m⁻¹ := fun m hm =>
    e7_inverts hH hcard hMX hMn hMc hp hp5 hMp hs₃X (gl_mul_self hs₃ (by decide) (by decide))
      (by rw [hs₃]; exact spMat_mulVec_e0 rfl (by decide)) (w := Pi.single 1 1) (fun v hv => by
        rw [hs₃] at hv
        have hz : ∀ i ∈ T₃, v i = 0 := fun i hi => eq_zero_of_mulVec_sgnOn hv hi
        refine ⟨v 0, v 1, funext fun i => ?_⟩
        fin_cases i <;> simp [hz, hT₃]) hm
  have hc := cent_of_inverts hinv₁ hinv₂
  have hu := cent_mul hc (cent_conj hMn hc hyX)
  have hprod := cent_mul (cent_mul (cent_conj hMn hu hz₁X) (cent_conj hMn hu hz₂X)) hu
  have hword : z₁ * (s₁ * s₂ * (y * (s₁ * s₂) * y⁻¹)) * z₁⁻¹ *
      (z₂ * (s₁ * s₂ * (y * (s₁ * s₂) * y⁻¹)) * z₂⁻¹) * (s₁ * s₂ * (y * (s₁ * s₂) * y⁻¹)) =
      s₃ := by
    rw [hyi, hz₁i, hz₂i]
    apply Units.ext
    simp only [Units.val_mul]
    rw [hs₁, hs₂, hs₃, hy, hz₁, hz₂]
    simp only [spMat_mul, mul_assoc]
    exact spMat_congr (by decide) (by decide)
  rw [hword] at hprod
  exact eq_bot_of_inverting hp (by omega) hMp hinv₃ hprod

end CFSG.StandardType.FrameRoute.FS81

end
