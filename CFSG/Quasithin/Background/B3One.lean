module

public import CFSG.Quasithin.Background.B3Rank

public section

namespace CFSG.Quasithin.B3

variable {n : ℕ}

theorem eVec_ne_one (hn : 1 ≤ n) : eVec n ≠ 1 := by
  intro h
  have := congrArg (fun w : U n => w.val ⟨0, hn⟩) h
  simp [eVec] at this

theorem card_Esub (hn : 1 ≤ n) : Nat.card ↥(Esub n) = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  unfold Esub
  rw [Nat.card_zpowers]
  exact orderOf_eq_prime (by rw [pow_two]; exact eVec_mul_self) (eVec_ne_one hn)

theorem card_U' (n : ℕ) : Nat.card (U n) = 2 ^ n := by
  rw [Nat.card_eq_fintype_card, card_U]

theorem wt_surjective (hn : 1 ≤ n) : Function.Surjective (wt n) := by
  intro y
  refine ⟨⟨fun i => if i = ⟨0, hn⟩ then Multiplicative.toAdd y else 0⟩, ?_⟩
  show Multiplicative.ofAdd (∑ i : Fin n, if i = (⟨0, hn⟩ : Fin n) then Multiplicative.toAdd y else 0)
    = y
  rw [Finset.sum_ite_eq' Finset.univ (⟨0, hn⟩ : Fin n) (fun _ => Multiplicative.toAdd y)]
  simp

theorem card_U0 (hn : 1 ≤ n) : Nat.card ↥(U0 n) * 2 = 2 ^ n := by
  have h := Subgroup.card_ker_mul_card_range (wt n)
  rw [MonoidHom.range_eq_top.2 (wt_surjective hn), Subgroup.card_top, card_U'] at h
  have h2 : Nat.card (Multiplicative (ZMod 2)) = 2 := by simp
  rw [h2] at h
  exact h

theorem card_V_mul (k : Mod) : Nat.card (Mod.V n k) * cN n k = Nat.card ↥(k.W n) := by
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup ((k.N n).subgroupOf (k.W n))
  have h2 : Nat.card ↥((k.N n).subgroupOf (k.W n)) = Nat.card ↥(k.N n ⊓ k.W n) := by
    rw [← Subgroup.inf_subgroupOf_right (k.N n) (k.W n)]
    exact Nat.card_congr
      (Subgroup.subgroupOfEquivOfLe (inf_le_right : k.N n ⊓ k.W n ≤ k.W n)).toEquiv
  rw [h2] at h1
  exact h1.symm

@[expose] def supp (w : U n) : Finset (Fin n) := Finset.univ.filter (fun i => w.val i ≠ 0)

theorem zmod2_eq_ite (x : ZMod 2) : x = if x ≠ 0 then 1 else 0 := by
  revert x
  decide

theorem sum_val_eq_card (w : U n) : ∑ i, w.val i = ((supp w).card : ZMod 2) := by
  unfold supp
  rw [Finset.card_filter]
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  exact zmod2_eq_ite _

theorem mem_U0_iff_even (w : U n) : w ∈ U0 n ↔ (supp w).card % 2 = 0 := by
  have h1 : w ∈ U0 n ↔ ∑ i, w.val i = 0 := by
    show wt n w = 1 ↔ _
    have h2 : wt n w = Multiplicative.ofAdd (∑ i, w.val i) := rfl
    rw [h2]
    exact ofAdd_eq_one
  rw [h1, sum_val_eq_card, ZMod.natCast_eq_zero_iff, Nat.dvd_iff_mod_eq_zero]

theorem eVec_mem_U0_iff : eVec n ∈ U0 n ↔ n % 2 = 0 := by
  rw [mem_U0_iff_even]
  have : supp (eVec n) = Finset.univ := by
    ext i
    simp [supp, eVec]
  rw [this, Finset.card_univ, Fintype.card_fin]

@[expose] def pairs (n : ℕ) : Set (U n) := {w | ∃ i j : Fin n, i ≠ j ∧ w = pair i j}

theorem mem_supp {w : U n} {i : Fin n} : i ∈ supp w ↔ w.val i ≠ 0 := by
  simp [supp]

theorem val_eq_one_of_mem_supp {w : U n} {i : Fin n} (h : i ∈ supp w) : w.val i = 1 := by
  have h1 := zmod2_eq_ite (w.val i)
  rw [mem_supp] at h
  simpa [h] using h1

theorem supp_pair_mul_ssubset (w : U n) {a b : Fin n} (ha : a ∈ supp w) (hb : b ∈ supp w) :
    supp (w * pair a b) ⊂ supp w := by
  have hwa := val_eq_one_of_mem_supp ha
  have hwb := val_eq_one_of_mem_supp hb
  rw [Finset.ssubset_iff_of_subset]
  · refine ⟨a, ha, ?_⟩
    rw [mem_supp]
    intro h
    apply h
    simp only [U.val_mul, pair, hwa, true_or, ite_true]
    decide
  · intro i hi
    rw [mem_supp] at hi ⊢
    intro h0
    apply hi
    simp only [U.val_mul, pair, h0, zero_add]
    by_cases hia : i = a ∨ i = b
    · exfalso
      rcases hia with rfl | rfl
      · rw [hwa] at h0
        exact one_ne_zero h0
      · rw [hwb] at h0
        exact one_ne_zero h0
    · simp [hia]

theorem exists_second {w : U n} (hw : w ∈ U0 n) {a : Fin n} (ha : a ∈ supp w) :
    ∃ b ∈ supp w, b ≠ a := by
  have hev := (mem_U0_iff_even w).1 hw
  have hpos : 0 < (supp w).card := Finset.card_pos.2 ⟨a, ha⟩
  have : 1 < (supp w).card := by omega
  exact Finset.exists_mem_ne this a

theorem U0_le_closure_pairs : U0 n ≤ Subgroup.closure (pairs n) := by
  intro w hw
  induction' hc : (supp w).card using Nat.strong_induction_on with m ih generalizing w
  by_cases h0 : supp w = ∅
  · have : w = 1 := by
      ext i
      show w.val i = 0
      by_contra hne
      have hmem : i ∈ supp w := mem_supp.2 hne
      rw [h0] at hmem
      exact absurd hmem (Finset.notMem_empty i)
    rw [this]
    exact Subgroup.one_mem _
  · obtain ⟨a, ha⟩ := Finset.nonempty_iff_ne_empty.2 h0
    obtain ⟨b, hb, hba⟩ := exists_second hw ha
    have hw' : w * pair a b ∈ U0 n := (U0 n).mul_mem hw (pair_mem_U0 hba.symm)
    have hlt : (supp (w * pair a b)).card < m := by
      rw [← hc]
      exact Finset.card_lt_card (supp_pair_mul_ssubset w ha hb)
    have h1 := ih (supp (w * pair a b)).card hlt hw' rfl
    have h2 : w = (w * pair a b) * pair a b := by
      rw [mul_assoc, U_mul_self, mul_one]
    rw [h2]
    exact Subgroup.mul_mem _ h1 (Subgroup.subset_closure ⟨a, b, hba.symm, rfl⟩)

theorem exists_third (hn : 3 ≤ n) (a c : Fin n) : ∃ b : Fin n, b ≠ a ∧ b ≠ c := by
  by_contra hcon
  push Not at hcon
  have hsub : (Finset.univ : Finset (Fin n)) ⊆ {a, c} := by
    intro x _
    by_cases h1 : x = a
    · simp [h1]
    · simp [hcon x h1]
  have h4 := Finset.card_le_card hsub
  have h5 : ({a, c} : Finset (Fin n)).card ≤ 2 := Finset.card_le_two
  simp only [Finset.card_univ, Fintype.card_fin] at h4
  omega

theorem exists_pair_mul (hn : 3 ≤ n) {x : U n} (h1 : x ≠ 1) (h2 : x ≠ eVec n) :
    ∃ σ : Gp n, σ ∈ alternatingGroup (Fin n) ∧
      ∃ p q : Fin n, p ≠ q ∧ x * permAct n σ x = pair p q := by
  obtain ⟨a, ha⟩ : ∃ a, x.val a ≠ 0 := by
    by_contra h
    push Not at h
    exact h1 (U.ext fun i => h i)
  obtain ⟨c, hc⟩ : ∃ c, x.val c ≠ 1 := by
    by_contra h
    push Not at h
    exact h2 (U.ext fun i => h i)
  have hxa : x.val a = 1 := by
    have h3 := zmod2_eq_ite (x.val a)
    simpa [ha] using h3
  have hxc : x.val c = 0 := by
    have h3 := zmod2_eq_ite (x.val c)
    by_contra hne
    simp only [ne_eq, hne, not_false_eq_true, ite_true] at h3
    exact hc h3
  have hac : a ≠ c := by
    intro h
    rw [h] at hxa
    rw [hxa] at hxc
    exact one_ne_zero hxc
  obtain ⟨b, hba, hbc⟩ := exists_third hn a c
  have hab : a ≠ b := hba.symm
  set σ : Gp n := Equiv.swap a b * Equiv.swap b c with hσdef
  have hσ : σ ∈ alternatingGroup (Fin n) := by
    rw [Equiv.Perm.mem_alternatingGroup, hσdef, map_mul, Equiv.Perm.sign_swap hab,
      Equiv.Perm.sign_swap hbc]
    decide
  have hsymm : ∀ i, σ.symm i = Equiv.swap b c (Equiv.swap a b i) := by
    intro i
    simp [hσdef, Equiv.Perm.mul_def, Equiv.symm_swap]
  have hsa : σ.symm a = c := by
    rw [hsymm, Equiv.swap_apply_left, Equiv.swap_apply_left]
  have hsb : σ.symm b = a := by
    rw [hsymm, Equiv.swap_apply_right, Equiv.swap_apply_of_ne_of_ne hab hac]
  have hsc : σ.symm c = b := by
    rw [hsymm, Equiv.swap_apply_of_ne_of_ne hac.symm hbc.symm, Equiv.swap_apply_right]
  have hso : ∀ i, i ≠ a → i ≠ b → i ≠ c → σ.symm i = i := by
    intro i hia hib hic
    rw [hsymm, Equiv.swap_apply_of_ne_of_ne hia hib, Equiv.swap_apply_of_ne_of_ne hib hic]
  refine ⟨σ, hσ, ?_⟩
  by_cases hxb : x.val b = 1
  · refine ⟨a, c, hac, ?_⟩
    ext i
    rw [U.val_mul, permAct_val]
    by_cases hia : i = a
    · subst hia
      rw [hsa, hxa, hxc]
      simp [pair]
    · by_cases hib : i = b
      · subst hib
        rw [hsb, hxb, hxa]
        simp [pair, hia, hbc]
        decide
      · by_cases hic : i = c
        · subst hic
          rw [hsc, hxb, hxc]
          simp [pair]
        · rw [hso i hia hib hic]
          simp [pair, hia, hic]
          exact CharTwo.add_self_eq_zero _
  · have hxb0 : x.val b = 0 := by
      have h3 := zmod2_eq_ite (x.val b)
      by_contra hne
      simp only [ne_eq, hne, not_false_eq_true, ite_true] at h3
      exact hxb h3
    refine ⟨a, b, hab, ?_⟩
    ext i
    rw [U.val_mul, permAct_val]
    by_cases hia : i = a
    · subst hia
      rw [hsa, hxa, hxc]
      simp [pair]
    · by_cases hib : i = b
      · subst hib
        rw [hsb, hxb0, hxa]
        simp [pair]
      · by_cases hic : i = c
        · subst hic
          rw [hsc, hxb0, hxc]
          simp [pair, hia, hib]
        · rw [hso i hia hib hic]
          simp [pair, hia, hib]
          exact CharTwo.add_self_eq_zero _

theorem exists_perm_alt_pair (hn : 4 ≤ n) {p q p' q' : Fin n} (hpq : p ≠ q) (hpq' : p' ≠ q') :
    ∃ τ : Gp n, τ ∈ alternatingGroup (Fin n) ∧ τ p = p' ∧ τ q = q' := by
  set q1 := Equiv.swap p p' q with hq1
  have hq1p' : q1 ≠ p' := by
    intro h
    have h2 : Equiv.swap p p' q = Equiv.swap p p' p := by
      rw [← hq1, h, Equiv.swap_apply_left]
    exact hpq (Equiv.injective _ h2).symm
  set τ0 : Gp n := Equiv.swap q1 q' * Equiv.swap p p' with hτ0
  have h0p : τ0 p = p' := by
    rw [hτ0, Equiv.Perm.mul_apply, Equiv.swap_apply_left]
    exact Equiv.swap_apply_of_ne_of_ne hq1p'.symm hpq'
  have h0q : τ0 q = q' := by
    rw [hτ0, Equiv.Perm.mul_apply, ← hq1, Equiv.swap_apply_left]
  by_cases hs : Equiv.Perm.sign τ0 = 1
  · exact ⟨τ0, Equiv.Perm.mem_alternatingGroup.2 hs, h0p, h0q⟩
  · have hcard : 2 ≤ (Finset.univ \ {p', q'}).card := by
      have h4 := Finset.card_le_card_sdiff_add_card (s := (Finset.univ : Finset (Fin n)))
        (t := {p', q'})
      have h5 : ({p', q'} : Finset (Fin n)).card ≤ 2 := Finset.card_le_two
      simp only [Finset.card_univ, Fintype.card_fin] at h4
      omega
    obtain ⟨r, hr, s', hs', hrs⟩ := Finset.one_lt_card.1 hcard
    simp only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton,
      true_and, not_or] at hr hs'
    refine ⟨Equiv.swap r s' * τ0, ?_, ?_, ?_⟩
    · rw [Equiv.Perm.mem_alternatingGroup, map_mul, Equiv.Perm.sign_swap hrs]
      rcases Int.units_eq_one_or (Equiv.Perm.sign τ0) with h | h
      · exact absurd h hs
      · rw [h]
        decide
    · rw [Equiv.Perm.mul_apply, h0p]
      exact Equiv.swap_apply_of_ne_of_ne (Ne.symm hr.1) (Ne.symm hs'.1)
    · rw [Equiv.Perm.mul_apply, h0q]
      exact Equiv.swap_apply_of_ne_of_ne (Ne.symm hr.2) (Ne.symm hs'.2)

theorem U0_le_of_invariant (hn : 4 ≤ n) {X : Subgroup (U n)}
    (hX : ∀ g ∈ alternatingGroup (Fin n), ∀ x ∈ X, permAct n g x ∈ X)
    {x : U n} (hxX : x ∈ X) (h1 : x ≠ 1) (h2 : x ≠ eVec n) : U0 n ≤ X := by
  obtain ⟨σ, hσ, p, q, hpq, hy⟩ := exists_pair_mul (by omega) h1 h2
  have hpair : pair p q ∈ X := hy ▸ X.mul_mem hxX (hX σ hσ x hxX)
  refine U0_le_closure_pairs.trans ((Subgroup.closure_le _).2 ?_)
  rintro _ ⟨i, j, hij, rfl⟩
  obtain ⟨τ, hτ, hτp, hτq⟩ := exists_perm_alt_pair hn hpq hij
  have h3 := hX τ hτ _ hpair
  rwa [permAct_pair, hτp, hτq] at h3

theorem pair_not_mem_Esub (hn : 3 ≤ n) (i j : Fin n) : pair i j ∉ Esub n := by
  rw [mem_Esub_iff]
  rintro (h | h)
  · have := congrArg (fun w : U n => w.val i) h
    simp [pair] at this
  · obtain ⟨k, hki, hkj⟩ := exists_third hn i j
    have := congrArg (fun w : U n => w.val k) h
    simp [pair, eVec, hki, hkj] at this

theorem B3_1_1 (hn : 5 ≤ n) :
    Nontrivial (Mod.V n Mod.ut0) ∧
    ∀ X : Subgroup (Mod.V n Mod.ut0),
      (∀ g ∈ alternatingGroup (Fin n), ∀ v ∈ X, Mod.act n Mod.ut0 g v ∈ X) → X = ⊥ ∨ X = ⊤ := by
  let π : ↥(U0 n) →* Mod.V n Mod.ut0 := QuotientGroup.mk' ((Esub n).subgroupOf (U0 n))
  have hπ : ∀ (g : Gp n) (w : ↥(U0 n)),
      Mod.act n Mod.ut0 g (π w) = π ⟨permAct n g w, isInv_U0 n g w w.2⟩ := fun g w => rfl
  have hker : ∀ w : ↥(U0 n), π w = 1 ↔ (w : U n) ∈ Esub n := fun w => QuotientGroup.eq_one_iff w
  constructor
  · obtain ⟨i, j, hij⟩ : ∃ i j : Fin n, i ≠ j := by
      obtain ⟨b, hb, -⟩ := exists_third (by omega : 3 ≤ n) ⟨0, by omega⟩ ⟨0, by omega⟩
      exact ⟨b, ⟨0, by omega⟩, hb⟩
    refine ⟨⟨1, π ⟨pair i j, pair_mem_U0 hij⟩, ?_⟩⟩
    intro h
    exact pair_not_mem_Esub (by omega) i j ((hker _).1 h.symm)
  · intro X hX
    let X' : Subgroup (U n) := (X.comap π).map (U0 n).subtype
    have hX'inv : ∀ g ∈ alternatingGroup (Fin n), ∀ x ∈ X', permAct n g x ∈ X' := by
      rintro g hg _ ⟨w, hw, rfl⟩
      refine ⟨⟨permAct n g w, isInv_U0 n g w w.2⟩, ?_, rfl⟩
      have h1 := hX g hg (π w) hw
      rw [hπ] at h1
      exact h1
    by_cases hcase : ∀ x ∈ X', x ∈ Esub n
    · left
      rw [eq_bot_iff]
      intro v hv
      obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective v
      have hw : (w : U n) ∈ X' := ⟨w, hv, rfl⟩
      rw [Subgroup.mem_bot]
      exact (hker w).2 (hcase _ hw)
    · right
      push Not at hcase
      obtain ⟨x, hxX', hxE⟩ := hcase
      have hx1 : x ≠ 1 := fun h => hxE (h ▸ Subgroup.one_mem _)
      have hxe : x ≠ eVec n := fun h => hxE (h ▸ Subgroup.mem_zpowers _)
      have hU0 : U0 n ≤ X' := U0_le_of_invariant (by omega) hX'inv hxX' hx1 hxe
      rw [eq_top_iff]
      intro v _
      obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective v
      obtain ⟨w', hw'X, hw'w⟩ := hU0 w.2
      have : w' = w := Subtype.ext hw'w
      subst this
      exact hw'X

theorem card_U0' (hn : 1 ≤ n) : Nat.card ↥(U0 n) = 2 ^ (n - 1) := by
  have h := card_U0 hn
  have h2 : 2 ^ n = 2 ^ (n - 1) * 2 := by
    rw [← pow_succ]
    congr 1
    omega
  omega

theorem rk_Vut0 (hn : 1 ≤ n) :
    rk (Mod.V n Mod.ut0) = (if n % 2 = 0 then n - 2 else n - 1) := by
  have h1 := card_V_mul (n := n) Mod.ut0
  have h2 : cN n Mod.ut0 = Nat.card ↥(Esub n ⊓ U0 n) := rfl
  have h3 : Nat.card ↥(Mod.W n Mod.ut0) = 2 ^ (n - 1) := card_U0' hn
  unfold rk
  by_cases hev : n % 2 = 0
  · have hE : Esub n ⊓ U0 n = Esub n :=
      inf_eq_left.2 (Subgroup.zpowers_le.2 (eVec_mem_U0_iff.2 hev))
    rw [h2, hE, card_Esub hn, h3] at h1
    have h4 : Nat.card (Mod.V n Mod.ut0) = 2 ^ (n - 2) := by
      have h5 : 2 ^ (n - 1) = 2 ^ (n - 2) * 2 := by
        rw [← pow_succ]
        congr 1
        omega
      omega
    simp only [hev, ite_true]
    rw [h4, padicValNat.prime_pow]
  · have hE : Esub n ⊓ U0 n = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      obtain ⟨hxE, hxU⟩ := hx
      rw [Subgroup.mem_bot]
      rcases (mem_Esub_iff x).1 hxE with h | h
      · exact h
      · exfalso
        rw [h] at hxU
        exact hev (eVec_mem_U0_iff.1 hxU)
    rw [h2, hE, Subgroup.card_bot, h3] at h1
    have h4 : Nat.card (Mod.V n Mod.ut0) = 2 ^ (n - 1) := by omega
    simp only [hev, ite_false]
    rw [h4, padicValNat.prime_pow]

theorem not_mem_U0_exists (hn : 1 ≤ n) : ∃ w : U n, w ∉ U0 n := by
  obtain ⟨w, hw⟩ := wt_surjective hn (Multiplicative.ofAdd 1)
  refine ⟨w, fun h => ?_⟩
  have h1 : wt n w = 1 := h
  rw [hw] at h1
  exact one_ne_zero (ofAdd_eq_one.1 h1)

theorem mul_mem_U0_of_not_mem {w x : U n} (hw : w ∉ U0 n) (hx : x ∉ U0 n) : w * x ∈ U0 n := by
  show wt n (w * x) = 1
  rw [map_mul]
  have hw' : wt n w ≠ 1 := hw
  have hx' : wt n x ≠ 1 := hx
  generalize wt n w = a at hw' ⊢
  generalize wt n x = b at hx' ⊢
  revert a b
  decide

theorem B3_1_2 (hn : 5 ≤ n) (hodd : n % 2 = 1) :
    U0 n ⊓ Esub n = ⊥ ∧ U0 n ⊔ Esub n = ⊤ ∧ rk (Mod.V n Mod.ut0) = n - 1 ∧
    ∃ φ : Mod.V n Mod.ut0 ≃* Mod.V n Mod.u0, ∀ (g : Gp n) (v : Mod.V n Mod.ut0),
      φ (Mod.act n Mod.ut0 g v) = Mod.act n Mod.u0 g (φ v) := by
  have hEU : Esub n ⊓ U0 n = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxE, hxU⟩ := hx
    rw [Subgroup.mem_bot]
    rcases (mem_Esub_iff x).1 hxE with h | h
    · exact h
    · exfalso
      rw [h] at hxU
      have := eVec_mem_U0_iff.1 hxU
      omega
  have heU : eVec n ∉ U0 n := fun h => by
    have := eVec_mem_U0_iff.1 h
    omega
  refine ⟨by rw [inf_comm]; exact hEU, ?_, ?_, ?_⟩
  · rw [eq_top_iff]
    intro w _
    by_cases hw : w ∈ U0 n
    · exact Subgroup.mem_sup_left hw
    · have h1 : w * eVec n ∈ U0 n := mul_mem_U0_of_not_mem hw heU
      have h2 : w = (w * eVec n) * eVec n := by rw [mul_assoc, eVec_mul_self, mul_one]
      rw [h2]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left h1) (Subgroup.mem_sup_right (Subgroup.mem_zpowers _))
  · rw [rk_Vut0 (by omega)]
    simp [show ¬ n % 2 = 0 by omega]
  · have hMN : (Esub n).subgroupOf (U0 n) = (⊥ : Subgroup (U n)).subgroupOf (U0 n) := by
      ext x
      simp only [Subgroup.mem_subgroupOf, Subgroup.mem_bot]
      constructor
      · intro hx
        have : (x : U n) ∈ Esub n ⊓ U0 n := ⟨hx, x.2⟩
        rw [hEU, Subgroup.mem_bot] at this
        exact this
      · intro hx
        rw [hx]
        exact Subgroup.one_mem _
    have h1 : ((Mod.N n Mod.ut0).subgroupOf (Mod.W n Mod.ut0)).Normal :=
      Subgroup.normal_of_isMulCommutative _
    have h2 : ((Mod.N n Mod.u0).subgroupOf (Mod.W n Mod.ut0)).Normal :=
      Subgroup.normal_of_isMulCommutative _
    have hMN' : (Mod.N n Mod.ut0).subgroupOf (Mod.W n Mod.ut0) =
        (Mod.N n Mod.u0).subgroupOf (Mod.W n Mod.ut0) := hMN
    refine ⟨@QuotientGroup.quotientMulEquivOfEq _ _ _ _ h1 h2 hMN', fun g v => ?_⟩
    induction v using QuotientGroup.induction_on with
    | H w => rfl

theorem B3_1_3 (hn : 5 ≤ n) (hev : n % 2 = 0) :
    (Esub n < U0 n ∧ U0 n < ⊤) ∧
    (∀ (g : Gp n), ∀ x ∈ Esub n, permAct n g x ∈ Esub n) ∧
    (∀ (g : Gp n), ∀ x ∈ U0 n, permAct n g x ∈ U0 n) ∧
    (∀ X : Subgroup (U n), (∀ g ∈ alternatingGroup (Fin n), ∀ x ∈ X, permAct n g x ∈ X) →
      X = ⊥ ∨ X = Esub n ∨ X = U0 n ∨ X = ⊤) ∧
    rk (Mod.V n Mod.ut0) = n - 2 := by
  have heU : eVec n ∈ U0 n := eVec_mem_U0_iff.2 hev
  have hEle : Esub n ≤ U0 n := Subgroup.zpowers_le.2 heU
  refine ⟨⟨?_, ?_⟩, isInv_Esub n, isInv_U0 n, ?_, ?_⟩
  · refine lt_of_le_of_ne hEle fun h => ?_
    have : pair (⟨0, by omega⟩ : Fin n) ⟨1, by omega⟩ ∈ U0 n :=
      pair_mem_U0 (by simp [Fin.ext_iff])
    rw [← h] at this
    exact pair_not_mem_Esub (by omega) _ _ this
  · refine lt_of_le_of_ne le_top fun h => ?_
    obtain ⟨w, hw⟩ := not_mem_U0_exists (by omega : 1 ≤ n)
    exact hw (h ▸ Subgroup.mem_top w)
  · intro X hX
    by_cases hX0 : ∀ x ∈ X, x ∈ U0 n
    · by_cases hXE : ∀ x ∈ X, x ∈ Esub n
      · by_cases he : eVec n ∈ X
        · right; left
          apply le_antisymm
          · intro x hx
            exact hXE x hx
          · exact Subgroup.zpowers_le.2 he
        · left
          rw [eq_bot_iff]
          intro x hx
          rw [Subgroup.mem_bot]
          rcases (mem_Esub_iff x).1 (hXE x hx) with h | h
          · exact h
          · exact absurd (h ▸ hx) he
      · right; right; left
        push Not at hXE
        obtain ⟨x, hxX, hxE⟩ := hXE
        have hx1 : x ≠ 1 := fun h => hxE (h ▸ Subgroup.one_mem _)
        have hxe : x ≠ eVec n := fun h => hxE (h ▸ Subgroup.mem_zpowers _)
        exact le_antisymm hX0 (U0_le_of_invariant (by omega) hX hxX hx1 hxe)
    · right; right; right
      push Not at hX0
      obtain ⟨x, hxX, hxU⟩ := hX0
      have hx1 : x ≠ 1 := fun h => hxU (h ▸ Subgroup.one_mem _)
      have hxe : x ≠ eVec n := fun h => hxU (h ▸ heU)
      have hU := U0_le_of_invariant (by omega) hX hxX hx1 hxe
      rw [eq_top_iff]
      intro w _
      by_cases hw : w ∈ U0 n
      · exact hU hw
      · have h1 : w * x ∈ U0 n := mul_mem_U0_of_not_mem hw hxU
        have h2 : w = (w * x) * x := by rw [mul_assoc, U_mul_self, mul_one]
        rw [h2]
        exact X.mul_mem (hU h1) hxX
  · rw [rk_Vut0 (by omega)]
    simp [hev]

end CFSG.Quasithin.B3
