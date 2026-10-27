module

public import CFSG.Quasithin.Background.C124YZModel
public import CFSG.Quasithin.Background.C124BlkQuot
public import CFSG.Quasithin.Background.B5FinS8Schur
public import CFSG.CGT.PushingUpLit.CGT6.EmbAltPerm

public section

namespace CFSG.Quasithin.SmithC27

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin Equiv Equiv.Perm

@[expose] def c3B8 : Perm (Fin 8) := swap 0 2 * swap 0 1

@[expose] def s3B8 : Subgroup (Perm (Fin 8)) where
  carrier := {σ | σ = 1 ∨ σ = swap 0 1 ∨ σ = swap 0 2 ∨ σ = swap 1 2 ∨ σ = c3B8 ∨ σ = c3B8⁻¹}
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq] at ha hb ⊢
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hb with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  one_mem' := Or.inl rfl
  inv_mem' := by
    intro a ha
    simp only [Set.mem_ofPred_eq] at ha ⊢
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem mem_s3B8_iff {σ : Perm (Fin 8)} :
    σ ∈ s3B8 ↔ σ = 1 ∨ σ = swap 0 1 ∨ σ = swap 0 2 ∨ σ = swap 1 2 ∨ σ = c3B8 ∨ σ = c3B8⁻¹ :=
  Iff.rfl

theorem swap_mem_s3B8 : swap (0 : Fin 8) 1 ∈ s3B8 := Or.inr (Or.inl rfl)

theorem c3B8_mem_s3B8 : c3B8 ∈ s3B8 := Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))

theorem zpowers_swap_le_s3B8 : Subgroup.zpowers (swap (0 : Fin 8) 1) ≤ s3B8 :=
  (Subgroup.zpowers_le).2 swap_mem_s3B8

theorem card_s3B8 : Nat.card s3B8 = 6 := by
  classical
  have hset : (s3B8 : Set (Perm (Fin 8))) =
      ↑({1, swap 0 1, swap 0 2, swap 1 2, c3B8, c3B8⁻¹} : Finset (Perm (Fin 8))) := by
    ext σ
    simp only [SetLike.mem_coe, mem_s3B8_iff, Finset.coe_insert, Finset.coe_singleton,
      Set.mem_insert_iff, Set.mem_singleton_iff]
  rw [← SetLike.coe_sort_coe, Nat.card_coe_set_eq, hset, Set.ncard_coe_finset]
  decide

theorem mem_zpowers_swap_iff_B8 {σ : Perm (Fin 8)} :
    σ ∈ Subgroup.zpowers (swap (0 : Fin 8) 1) ↔ σ = 1 ∨ σ = swap 0 1 := by
  constructor
  · intro h
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 h
    exact C124.YZ.zpow_eq_one_or_self' (by decide) k
  · rintro (rfl | rfl)
    · exact Subgroup.one_mem _
    · exact Subgroup.mem_zpowers _

theorem orderOf_swap_B8 : orderOf (swap (0 : Fin 8) 1) = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact orderOf_eq_prime (by decide) (by decide)

theorem card_zpowers_swap_B8 : Nat.card (Subgroup.zpowers (swap (0 : Fin 8) 1)) = 2 := by
  rw [Nat.card_zpowers, orderOf_swap_B8]

theorem c3B8_ne_one : c3B8 ≠ 1 := by decide

theorem c3B8_mem_alt : c3B8 ∈ alternatingGroup (Fin 8) := by
  rw [mem_alternatingGroup, c3B8, map_mul, sign_swap (by decide), sign_swap (by decide)]
  decide

theorem c3B8_facts {τ : Perm (Fin 8)} (hτ : τ = c3B8 ∨ τ = c3B8⁻¹) :
    τ ∈ alternatingGroup (Fin 8) ∧ τ * swap 0 1 ≠ swap 0 1 * τ := by
  rcases hτ with rfl | rfl
  · exact ⟨c3B8_mem_alt, by decide⟩
  · exact ⟨inv_mem c3B8_mem_alt, by decide⟩

theorem s3B8_cases {σ : Perm (Fin 8)} (hσ : σ ∈ s3B8)
    (hσ' : σ ∉ Subgroup.zpowers (swap (0 : Fin 8) 1)) :
    (σ = c3B8 ∨ σ = c3B8⁻¹) ∨ (σ * swap 0 1 = c3B8 ∨ σ * swap 0 1 = c3B8⁻¹) := by
  rw [mem_zpowers_swap_iff_B8, not_or] at hσ'
  obtain ⟨h1, h2⟩ := hσ'
  rcases hσ with rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd rfl h1
  · exact absurd rfl h2
  · right; left; rfl
  · right; right; decide
  · left; left; rfl
  · left; right; rfl

theorem s3B8_pow_three {σ : Perm (Fin 8)} (hσ : σ ∈ s3B8) (h3 : σ ^ 3 = 1) :
    σ = 1 ∨ σ = c3B8 ∨ σ = c3B8⁻¹ := by
  rcases hσ with rfl | rfl | rfl | rfl | rfl | rfl
  · left; rfl
  · exact absurd h3 (by decide)
  · exact absurd h3 (by decide)
  · exact absurd h3 (by decide)
  · right; left; rfl
  · right; right; rfl

theorem exists_perm_eq_zero_one_B8 {a b : Fin 8} (hab : a ≠ b) :
    ∃ π : Perm (Fin 8), π a = 0 ∧ π b = 1 := by
  set b' := swap a 0 b with hb'
  have hb'0 : b' ≠ 0 := by
    intro h
    apply hab
    have : swap a 0 b = swap a 0 a := by rw [← hb', h, swap_apply_left]
    exact ((swap a 0).injective this).symm
  refine ⟨swap b' 1 * swap a 0, ?_, ?_⟩
  · rw [Perm.mul_apply, swap_apply_left, swap_apply_of_ne_of_ne (Ne.symm hb'0) (by decide)]
  · rw [Perm.mul_apply, ← hb', swap_apply_left]

theorem dm8_mul_self (d : C124.YZ.DM 8) : d * d = 1 := by
  induction d using QuotientGroup.induction_on with
  | H x =>
    rw [← QuotientGroup.mk_mul]
    have hx : x * x = 1 := Subtype.ext (G6.permMod_mul_self (n := 8) x.1)
    rw [hx, QuotientGroup.mk_one]

theorem mk_eq_one_iff_B8 (x : ↥(G6.coreMod 8)) :
    (QuotientGroup.mk x : B5FinS8.Mod8) = 1 ↔
      (Multiplicative.toAdd (x : G6.PermMod 8) = 0 ∨
        Multiplicative.toAdd (x : G6.PermMod 8) = fun _ => 1) := by
  have h := B5FinS8.mk_eq_mk_iff x 1
  have h1 : Multiplicative.toAdd ((1 : ↥(G6.coreMod 8)) : G6.PermMod 8) = 0 := rfl
  rw [h1, add_zero] at h
  exact h

private theorem toAdd_pelt_mul_inv (a b c d : Fin 8) :
    Multiplicative.toAdd
        (((B5FinS8.pelt a b * (B5FinS8.pelt c d)⁻¹ : ↥(G6.coreMod 8))) : G6.PermMod 8) =
      B5FinS8.pv a b + -B5FinS8.pv c d := rfl

private theorem pv_facts_B8 :
    ¬ (B5FinS8.pv 0 3 + -B5FinS8.pv 1 3 = 0 ∨ B5FinS8.pv 0 3 + -B5FinS8.pv 1 3 = fun _ => 1) ∧
    ¬ (B5FinS8.pv 1 3 + -B5FinS8.pv 2 3 = 0 ∨ B5FinS8.pv 1 3 + -B5FinS8.pv 2 3 = fun _ => 1) ∧
    ¬ ((B5FinS8.pv 0 3 + -B5FinS8.pv 1 3) + (B5FinS8.pv 1 3 + -B5FinS8.pv 2 3) = 0 ∨
      (B5FinS8.pv 0 3 + -B5FinS8.pv 1 3) + (B5FinS8.pv 1 3 + -B5FinS8.pv 2 3) = fun _ => 1) := by
  decide +kernel

private theorem mod8_c3_facts :
    B5FinS8.pclass 0 3 * (B5FinS8.pclass 1 3)⁻¹ ≠ 1 ∧
    B5FinS8.pclass 1 3 * (B5FinS8.pclass 2 3)⁻¹ ≠ 1 ∧
    B5FinS8.pclass 0 3 * (B5FinS8.pclass 1 3)⁻¹ ≠
      B5FinS8.pclass 1 3 * (B5FinS8.pclass 2 3)⁻¹ := by
  simp only [B5FinS8.pclass, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul]
  obtain ⟨h1, h2, h3⟩ := pv_facts_B8
  refine ⟨?_, ?_, ?_⟩
  · rw [Ne, mk_eq_one_iff_B8, toAdd_pelt_mul_inv]
    exact h1
  · rw [Ne, mk_eq_one_iff_B8, toAdd_pelt_mul_inv]
    exact h2
  · intro h
    have h' := (B5FinS8.mk_eq_mk_iff _ _).1 h
    rw [toAdd_pelt_mul_inv, toAdd_pelt_mul_inv] at h'
    exact h3 h'

theorem dm8_c3_facts :
    C124.YZ.pairQ (0 : Fin 8) 3 * (C124.YZ.dAct 8 c3B8 (C124.YZ.pairQ 0 3))⁻¹ ≠ 1 ∧
    C124.YZ.pairQ (1 : Fin 8) 3 * (C124.YZ.dAct 8 c3B8 (C124.YZ.pairQ 1 3))⁻¹ ≠ 1 ∧
    C124.YZ.pairQ (0 : Fin 8) 3 * (C124.YZ.dAct 8 c3B8 (C124.YZ.pairQ 0 3))⁻¹ ≠
      C124.YZ.pairQ (1 : Fin 8) 3 * (C124.YZ.dAct 8 c3B8 (C124.YZ.pairQ 1 3))⁻¹ := by
  have e1 : C124.YZ.dAct 8 c3B8 (C124.YZ.pairQ 0 3) = C124.YZ.pairQ 1 3 := by
    rw [C124.YZ.dAct_pairQ]
    rfl
  have e2 : C124.YZ.dAct 8 c3B8 (C124.YZ.pairQ 1 3) = C124.YZ.pairQ 2 3 := by
    rw [C124.YZ.dAct_pairQ]
    rfl
  rw [e1, e2]
  exact mod8_c3_facts

theorem dm8_eq_bot_or_top (W : Subgroup (C124.YZ.DM 8))
    (hW : ∀ σ ∈ alternatingGroup (Fin 8), ∀ d ∈ W, C124.YZ.dAct 8 σ d ∈ W) :
    W = ⊥ ∨ W = ⊤ := by
  by_cases hb : W = ⊥
  · exact Or.inl hb
  right
  obtain ⟨⟨d, hdW⟩, hd1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hb
  have hd1' : d ≠ 1 := fun h => hd1 (Subtype.ext h)
  obtain ⟨x, rfl⟩ : ∃ x : ↥(G6.coreMod 8), (QuotientGroup.mk x : B5FinS8.Mod8) = d :=
    QuotientGroup.mk_surjective d
  set N : Subgroup (G6.PermMod 8) :=
    (W.comap (QuotientGroup.mk' B5FinS8.Ker8)).map (G6.coreMod 8).subtype with hN
  have hNinv : ∀ σ ∈ alternatingGroup (Fin 8), ∀ y ∈ N, G6.permAct 8 σ y ∈ N := by
    rintro σ hσ _ ⟨z, hz, rfl⟩
    exact ⟨⟨G6.permAct 8 σ z, G6.permAct_mem_coreMod σ z.2⟩, hW σ hσ _ hz, rfl⟩
  have hx0 : (x : G6.PermMod 8) ≠ 1 := fun h =>
    hd1' ((mk_eq_one_iff_B8 x).2 (Or.inl (by rw [h]; rfl)))
  have hx1 : (x : G6.PermMod 8) ≠ G6.allOnes 8 := fun h =>
    hd1' ((mk_eq_one_iff_B8 x).2 (Or.inr (by rw [h]; rfl)))
  have hle := CFSG.CGT.PushingUpLit.CGT6.coreMod_le_of_invariant (by norm_num) hNinv
    ⟨x, hdW, rfl⟩ hx0 hx1
  rw [eq_top_iff]
  intro q _
  obtain ⟨y, rfl⟩ : ∃ y : ↥(G6.coreMod 8), (QuotientGroup.mk y : B5FinS8.Mod8) = q :=
    QuotientGroup.mk_surjective q
  obtain ⟨z, hz, hzy⟩ := hle y.2
  have hzy' : z = y := Subtype.ext hzy
  rw [← hzy']
  exact hz

private theorem permWeight_sub_mem_B8 (σ : Perm (Fin 8)) {x y : ↥(evenWeight 8)}
    (h : -x + y ∈ constWeight 8) : -permWeight 8 σ x + permWeight 8 σ y ∈ constWeight 8 := by
  intro i j
  have := h (σ⁻¹ i) (σ⁻¹ j)
  simpa [permWeight] using this

theorem altQuotEquiv_dAct_B8 (σ : Perm (Fin 8)) (d : C124.YZ.DM 8) (x : ↥(evenWeight 8))
    (hx : (QuotientAddGroup.mk x : AltHeart 8) =
      Multiplicative.toAdd (C124.altQuotEquiv 8 (by norm_num) d)) :
    (QuotientAddGroup.mk (permWeight 8 σ x) : AltHeart 8) =
      Multiplicative.toAdd (C124.altQuotEquiv 8 (by norm_num) (C124.YZ.dAct 8 σ d)) := by
  obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective d
  have h2 : Multiplicative.toAdd (C124.altQuotEquiv 8 (by norm_num)
      (C124.YZ.dAct 8 σ (QuotientGroup.mk m))) = (QuotientAddGroup.mk
        (permWeight 8 σ (Multiplicative.toAdd (C124.coreEvenEquiv 8 m))) : AltHeart 8) := rfl
  rw [h2]
  have h3 : (QuotientAddGroup.mk x : AltHeart 8) =
      QuotientAddGroup.mk (Multiplicative.toAdd (C124.coreEvenEquiv 8 m)) := by
    rw [hx]
    rfl
  rw [QuotientAddGroup.eq] at h3 ⊢
  exact permWeight_sub_mem_B8 σ h3

end CFSG.Quasithin.SmithC27
