module

public import Mathlib.GroupTheory.RegularWreathProduct

public section

namespace CFSG.Quasithin.H13.L319

abbrev S3Wr : Type := Equiv.Perm (Fin 3) ≀ᵣ Multiplicative (ZMod 2)

private instance : Fintype S3Wr := Fintype.ofEquiv _ (RegularWreathProduct.equivProd _ _).symm

private instance : DecidableEq S3Wr :=
  Function.Injective.decidableEq (RegularWreathProduct.equivProd _ _).injective

def oddSub : Subgroup S3Wr := Subgroup.closure {w : S3Wr | Odd (orderOf w)}

private lemma perm3_pow_six : ∀ σ : Equiv.Perm (Fin 3), σ ^ 6 = 1 := by decide

private lemma perm3_mul_cube : ∀ σ τ : Equiv.Perm (Fin 3), σ ^ 3 = 1 → τ ^ 3 = 1 → (σ * τ) ^ 3 = 1 := by
  decide

private lemma perm3_cube_of_odd_pow {σ : Equiv.Perm (Fin 3)} {n : ℕ} (hn : n % 2 = 1)
    (h : σ ^ n = 1) : σ ^ 3 = 1 := by
  have key : ∀ τ : Equiv.Perm (Fin 3), ∀ r : ℕ, r < 6 → r % 2 = 1 → τ ^ r = 1 → τ ^ 3 = 1 := by
    decide
  exact key σ (n % 6) (Nat.mod_lt _ (by norm_num)) (by omega)
    ((pow_eq_pow_mod n (perm3_pow_six σ)).symm.trans h)

private lemma zmod2_eq_one_of_pow {x : Multiplicative (ZMod 2)} {n : ℕ} (hn : n % 2 = 1)
    (h : x ^ n = 1) : x = 1 := by
  have key : ∀ y : Multiplicative (ZMod 2), y ^ 2 = 1 := by decide
  have h1 := (pow_eq_pow_mod n (key x)).symm.trans h
  rwa [hn, pow_one] at h1

private lemma divisor_nine_eq_three : ∀ m : ℕ, m < 10 → m ∣ 9 → m ≠ 1 → m ≠ 9 → m = 3 := by
  decide

private lemma small_six_dvd : ∀ m : ℕ, m < 7 → m ∣ 6 → ¬ 3 ∣ m → m ≤ 2 := by decide

private def baseHom : (Multiplicative (ZMod 2) → Equiv.Perm (Fin 3)) →* S3Wr where
  toFun f := ⟨f, 1⟩
  map_one' := rfl
  map_mul' f g := by ext <;> simp

private lemma baseHom_apply (f : Multiplicative (ZMod 2) → Equiv.Perm (Fin 3)) :
    baseHom f = ⟨f, 1⟩ := rfl

private lemma baseHom_injective : Function.Injective baseHom := fun f g h => by
  simpa [baseHom_apply] using congrArg RegularWreathProduct.left h

private lemma eq_baseHom_of_right (w : S3Wr) (hw : w.right = 1) : w = baseHom w.left := by
  ext <;> simp [baseHom_apply, hw]

private def cubeSub : Subgroup S3Wr where
  carrier := {w | w.right = 1 ∧ ∀ x, (w.left x) ^ 3 = 1}
  one_mem' := ⟨rfl, fun x => by simp⟩
  mul_mem' := by
    rintro a b ⟨ha1, ha2⟩ ⟨hb1, hb2⟩
    refine ⟨by simp [ha1, hb1], fun x => ?_⟩
    simpa [ha1] using perm3_mul_cube _ _ (ha2 x) (hb2 x)
  inv_mem' := by
    rintro a ⟨ha1, ha2⟩
    exact ⟨by simp [ha1], fun x => by simp [ha1, inv_pow, ha2 x]⟩

private lemma mem_cubeSub_iff_pow (w : S3Wr) : w ∈ cubeSub ↔ w ^ 3 = 1 := by
  constructor
  · rintro ⟨hr, hl⟩
    have hcube : w.left ^ 3 = 1 := funext fun x => hl x
    calc w ^ 3 = (baseHom w.left) ^ 3 := by rw [← eq_baseHom_of_right w hr]
      _ = baseHom (w.left ^ 3) := (map_pow _ _ _).symm
      _ = 1 := by rw [hcube, map_one]
  · intro h
    have hr : w.right = 1 := by
      have h1 : RegularWreathProduct.rightHom (w ^ 3) = (RegularWreathProduct.rightHom w) ^ 3 :=
        map_pow _ _ _
      rw [h, map_one] at h1
      exact zmod2_eq_one_of_pow (by norm_num) h1.symm
    have hcube : w.left ^ 3 = 1 := by
      apply baseHom_injective
      rw [map_pow, map_one, ← eq_baseHom_of_right w hr, h]
    refine ⟨hr, fun x => ?_⟩
    simpa using congrFun hcube x

theorem S3Wr_card : Nat.card S3Wr = 72 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

theorem S3Wr_odd_pow_three (w : S3Wr) (hw : Odd (orderOf w)) : w ^ 3 = 1 := by
  have hn : orderOf w % 2 = 1 := Nat.odd_iff.mp hw
  have hpow : w ^ orderOf w = 1 := pow_orderOf_eq_one w
  have hr : w.right = 1 := by
    have h1 : RegularWreathProduct.rightHom (w ^ orderOf w) =
        (RegularWreathProduct.rightHom w) ^ orderOf w := map_pow _ _ _
    rw [hpow, map_one] at h1
    exact zmod2_eq_one_of_pow hn h1.symm
  have hl : w.left ^ orderOf w = 1 := by
    apply baseHom_injective
    rw [map_pow, map_one, ← eq_baseHom_of_right w hr, hpow]
  have hcube : w.left ^ 3 = 1 := by
    funext x
    have hx := congrFun hl x
    simp only [Pi.pow_apply, Pi.one_apply] at hx ⊢
    exact perm3_cube_of_odd_pow hn hx
  calc w ^ 3 = (baseHom w.left) ^ 3 := by rw [← eq_baseHom_of_right w hr]
    _ = baseHom (w.left ^ 3) := (map_pow _ _ _).symm
    _ = 1 := by rw [hcube, map_one]

private lemma odd_iff_mem_cubeSub (w : S3Wr) : Odd (orderOf w) ↔ w ∈ cubeSub := by
  rw [mem_cubeSub_iff_pow]
  refine ⟨fun h => S3Wr_odd_pow_three w h, fun h => ?_⟩
  exact Odd.of_dvd_nat ⟨1, rfl⟩ (orderOf_dvd_of_pow_eq_one h)

private lemma oddSub_eq_cubeSub : oddSub = cubeSub := by
  refine le_antisymm ((Subgroup.closure_le _).2 fun w hw => (odd_iff_mem_cubeSub w).1 hw) fun w hw => ?_
  exact Subgroup.subset_closure ((odd_iff_mem_cubeSub w).2 hw)

theorem mem_oddSub_iff (w : S3Wr) : w ∈ oddSub ↔ Odd (orderOf w) := by
  rw [oddSub_eq_cubeSub, odd_iff_mem_cubeSub]

theorem oddSub_card : Nat.card oddSub = 9 := by
  rw [oddSub_eq_cubeSub, Nat.card_congr (Equiv.subtypeEquivRight mem_cubeSub_iff_pow),
    Nat.card_eq_fintype_card]
  decide +kernel

private lemma zpowers_cases {k x : S3Wr} (hk3 : k ^ 3 = 1) (hk1 : k ≠ 1)
    (hx : x ∈ Subgroup.zpowers k) : x = 1 ∨ x = k ∨ x = k⁻¹ := by
  have hord : orderOf k = 3 := orderOf_eq_prime hk3 hk1
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
  have hmod : k ^ (i % 3) = k ^ i := by
    have h := zpow_mod_orderOf k i
    rw [hord] at h
    simpa using h
  have hcases : i % 3 = 0 ∨ i % 3 = 1 ∨ i % 3 = 2 := by omega
  rcases hcases with h | h | h
  · left
    rw [← hmod, h, zpow_zero]
  · right; left
    rw [← hmod, h, zpow_one]
  · right; right
    rw [← hmod, h, zpow_two]
    exact eq_inv_of_mul_eq_one_left (by rw [← pow_three', hk3])

private lemma mem_normalizer_zpowers_iff {k : S3Wr} (hk3 : k ^ 3 = 1) (hk1 : k ≠ 1) (g : S3Wr) :
    g ∈ Subgroup.normalizer ((Subgroup.zpowers k : Subgroup S3Wr) : Set S3Wr) ↔
      g * k * g⁻¹ = k ∨ g * k * g⁻¹ = k⁻¹ := by
  rw [Subgroup.mem_set_normalizer_iff]
  constructor
  · intro hg
    rcases zpowers_cases hk3 hk1 ((hg k).1 (Subgroup.mem_zpowers k)) with h | h | h
    · exact (hk1 (by simpa using h)).elim
    · exact Or.inl h
    · exact Or.inr h
  · intro hg
    have hz : Subgroup.zpowers (g * k * g⁻¹) = Subgroup.zpowers k := by
      rcases hg with h | h
      · rw [h]
      · rw [h, Subgroup.zpowers_inv]
    have hmap : (Subgroup.zpowers k).map (MulAut.conj g).toMonoidHom = Subgroup.zpowers k := by
      rw [MonoidHom.map_zpowers]
      exact hz
    intro x
    have hiff := Subgroup.mem_map_iff_mem (f := (MulAut.conj g).toMonoidHom)
      (MulAut.conj g).injective (K := Subgroup.zpowers k) (x := x)
    rw [hmap] at hiff
    exact hiff.symm

private lemma card_normalizer_zpowers {k : S3Wr} (hk3 : k ^ 3 = 1) (hk1 : k ≠ 1) :
    Nat.card (Subgroup.normalizer ((Subgroup.zpowers k : Subgroup S3Wr) : Set S3Wr)) = 36 := by
  have hall : ∀ m : S3Wr, m ^ 3 = 1 → m ≠ 1 →
      Fintype.card {g : S3Wr // g * m * g⁻¹ = m ∨ g * m * g⁻¹ = m⁻¹} = 36 := by
    decide +kernel
  rw [Nat.card_congr (Equiv.subtypeEquivRight (fun g => mem_normalizer_zpowers_iff hk3 hk1 g)),
    Nat.card_eq_fintype_card]
  exact hall k hk3 hk1

theorem oddSub_irreducible (S : Subgroup S3Wr) (hS : IsPGroup 2 S) (hS8 : Nat.card S = 8)
    (K : Subgroup S3Wr) (hK : K ≤ oddSub) (hSK : S ≤ Subgroup.normalizer (K : Set S3Wr)) :
    K = ⊥ ∨ K = oddSub := by
  by_cases hK0 : K = ⊥
  · exact Or.inl hK0
  refine Or.inr ?_
  by_contra hKT
  have hdvd : Nat.card K ∣ 9 := by
    have h := Subgroup.card_dvd_of_le hK
    rwa [oddSub_card] at h
  have hK3 : Nat.card K = 3 := by
    have hne1 : Nat.card K ≠ 1 := fun h => hK0 (Subgroup.card_eq_one.1 h)
    have hne9 : Nat.card K ≠ 9 := fun h =>
      hKT (Subgroup.eq_of_le_of_card_ge hK (le_of_eq (by rw [oddSub_card, h])))
    have hlt : Nat.card K < 10 := by
      have := Nat.le_of_dvd (by norm_num) hdvd
      omega
    exact divisor_nine_eq_three _ hlt hdvd hne1 hne9
  obtain ⟨⟨k, hkK⟩, hk1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hK0
  have hk1' : k ≠ 1 := fun h => hk1 (Subtype.ext h)
  have hk3 : k ^ 3 = 1 := by
    have hkO : k ∈ oddSub := hK hkK
    rw [oddSub_eq_cubeSub] at hkO
    exact (mem_cubeSub_iff_pow k).1 hkO
  have hord : orderOf k = 3 := orderOf_eq_prime hk3 hk1'
  have hKz : Subgroup.zpowers k = K := by
    refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hkK) (le_of_eq ?_)
    rw [Nat.card_zpowers, hord, hK3]
  subst hKz
  have h8 := Subgroup.card_dvd_of_le hSK
  rw [hS8, card_normalizer_zpowers hk3 hk1'] at h8
  norm_num at h8

theorem perm_three_elemAbelian_card_le_two (A : Subgroup (Equiv.Perm (Fin 3)))
    (hA : ∀ a ∈ A, a * a = 1) : Nat.card A ≤ 2 := by
  have h6 : Nat.card (Equiv.Perm (Fin 3)) = 6 := by
    rw [Nat.card_eq_fintype_card]
    decide
  have hdvd : Nat.card A ∣ 6 := by
    have h := Subgroup.card_subgroup_dvd_card A
    rwa [h6] at h
  have h3 : ¬ 3 ∣ Nat.card A := by
    intro h
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := A) 3 h
    have hx2 : (x : Equiv.Perm (Fin 3)) ^ 2 = 1 := by
      rw [sq]
      exact hA _ x.2
    have hord : orderOf (x : Equiv.Perm (Fin 3)) = 3 := by
      rw [Subgroup.orderOf_coe]
      exact hx
    have h2 := orderOf_dvd_of_pow_eq_one hx2
    rw [hord] at h2
    norm_num at h2
  have hlt : Nat.card A < 7 := by
    have := Nat.le_of_dvd (by norm_num) hdvd
    omega
  exact small_six_dvd _ hlt hdvd h3

end CFSG.Quasithin.H13.L319
