module

public import CFSG.Quasithin.Vol2.Ch3Sec3HatModel

public section

namespace CFSG.Quasithin.H13.HatN

open CFSG.Quasithin.H13.HatC CFSG.Quasithin.H13.HatM

theorem mactN_xor (m : List ℕ) (a b : ℕ) :
    ∀ n, mactN m (a ^^^ b) n = mactN m a n ^^^ mactN m b n
  | 0 => by simp [mactN]
  | n + 1 => by
    simp only [mactN, mactN_xor m a b n, Nat.testBit_xor]
    cases a.testBit n <;> cases b.testBit n <;>
      simp [Nat.xor_assoc, Nat.xor_comm, Nat.xor_left_comm]

theorem mact_xor (m : List ℕ) (a b : ℕ) : mact m (a ^^^ b) = mact m a ^^^ mact m b :=
  mactN_xor m a b 6

theorem mact_lt' (x : MulAut W6) (c : ℕ) : mact (mcode ⇑x) c < 64 :=
  mact_lt (fun _ hk => mcode_getD_lt _ hk) c

theorem mact_mul (x y : MulAut W6) {c : ℕ} (hc : c < 64) :
    mact (mcode ⇑(x * y)) c = mact (mcode ⇑x) (mact (mcode ⇑y) c) := by
  apply dec_injective (mact_lt' _ _) (mact_lt' _ _)
  rw [dec_mact _ hc, dec_mact _ (mact_lt' y c), dec_mact _ hc]
  rfl

theorem mact_one {c : ℕ} (hc : c < 64) : mact (mcode ⇑(1 : MulAut W6)) c = c := by
  apply dec_injective (mact_lt' _ _) hc
  rw [dec_mact _ hc]
  rfl

theorem mact_inj (x : MulAut W6) {a b : ℕ} (ha : a < 64) (hb : b < 64)
    (h : mact (mcode ⇑x) a = mact (mcode ⇑x) b) : a = b := by
  have h1 := congrArg dec h
  rw [dec_mact x ha, dec_mact x hb] at h1
  have h2 := x.injective (Multiplicative.toAdd.injective h1)
  exact dec_injective ha hb (congrArg Multiplicative.toAdd h2)

theorem mact_inv_of {x : MulAut W6} {a b : ℕ} (ha : a < 64) (h : mact (mcode ⇑x) a = b) :
    mact (mcode ⇑x⁻¹) b = a := by
  rw [← h, ← mact_mul _ _ ha, inv_mul_cancel, mact_one ha]

theorem mcode_eq (x : MulAut W6) : mcode ⇑x = [mact (mcode ⇑x) 1, mact (mcode ⇑x) 2,
    mact (mcode ⇑x) 4, mact (mcode ⇑x) 8, mact (mcode ⇑x) 16, mact (mcode ⇑x) 32] := by
  have hlen : (mcode ⇑x).length = 6 := by simp [mcode]
  have hg : ∀ k < 6, (mcode ⇑x).getD k 0 = mact (mcode ⇑x) (2 ^ k) := fun k hk => by
    rw [mcode_getD _ hk, enc_apply x _ (by interval_cases k <;> norm_num)]
  apply List.ext_getElem (by simp [hlen])
  intro k hk1 hk2
  have hk : k < 6 := by rwa [hlen] at hk1
  rw [← List.getD_eq_getElem _ 0 hk1, hg k hk]
  interval_cases k <;> rfl

@[expose] def H18 : List ℕ := [1, 2, 3, 4, 8, 12, 16, 21, 27, 30, 32, 39, 42, 45, 48, 54, 57, 63]

@[expose] def h18w : List (ℕ × List ℕ) := [(1, []), (2, [1, 1, 0, 1]), (3, [0, 1, 1, 1]),
  (4, [0]), (8, [0, 1, 1, 0, 1]), (12, [0, 0, 1, 1, 1]), (16, [1]), (21, [0, 1]), (27, [0, 1, 1]),
  (30, [0, 1, 0, 1]), (32, [1, 1, 1, 0, 1]), (39, [1, 1, 0, 1, 1, 1]), (42, [0, 1, 1, 1, 0, 1]),
  (45, [1, 0, 1]), (48, [1, 0, 1, 1, 1]), (54, [1, 0, 1, 1, 1, 0, 1]), (57, [1, 1]),
  (63, [1, 1, 1])]

@[expose] def s4w : List (ℕ × List ℕ) := [(4, []), (8, [1, 0, 1, 1, 0, 0, 1]),
  (12, [0, 0, 1, 1, 0, 1, 1]), (16, [1, 0, 0, 0, 1, 1]), (21, [0, 0, 1]), (27, [0, 0, 0, 1, 0]),
  (30, [1, 1, 1, 1, 0, 0]), (32, [1, 1, 1, 0, 0, 1, 1]), (39, [0, 0, 1, 0, 0, 0, 1, 1, 0]),
  (42, [1, 1, 1, 0, 0, 1, 0, 1, 1, 0]), (45, [0, 0, 1, 0, 0, 1]), (48, [0, 0, 0, 1, 1, 0]),
  (54, [1, 1, 1, 1, 0, 1, 1, 0]), (57, [1, 0, 1, 1]), (63, [1, 1, 1, 1, 0, 1, 0])]

@[expose] def candw : List (List ℕ × List ℕ) := [([1, 2, 4, 8, 16, 32], []),
  ([1, 2, 4, 8, 21, 42], [0, 0, 0, 1, 0, 0, 0, 1]),
  ([1, 2, 4, 8, 30, 39], [0, 1, 0, 0, 0, 1, 0, 1]),
  ([1, 2, 4, 8, 27, 45], [0, 0, 1, 1, 1, 1, 0, 0, 1, 0, 0])]

theorem chk_orbits : (∀ c < 64, c = 0 ∨ c ∈ H18 ∨ c ∈ orbw.map Prod.fst) ∧ 0 ∉ H18 ∧
    (∀ c ∈ H18, c < 64) ∧ H18.Nodup ∧ H18.length = 18 ∧
    (∀ c ∈ H18, mact g1c c ∈ H18 ∧ mact g2c c ∈ H18 ∧ mact sgc c ∈ H18) ∧
    (∀ p ∈ h18w, mact (wval p.2) 1 = p.1 ∧ ∀ i ∈ p.2, i < 2) ∧ h18w.map Prod.fst = H18 := by
  decide +kernel

theorem chk_words : (∀ c ∈ H18, 1 ^^^ c ∈ H18 → c = 2 ∨ c = 3) ∧
    (∀ c ∈ H18, 4 ^^^ c ∈ H18 → c = 8 ∨ c = 12) ∧ mact sgc 1 = 1 ∧ mact sgc 3 = 2 ∧
    (∀ p ∈ s4w, mact (wval p.2) 1 = 1 ∧ mact (wval p.2) 2 = 2 ∧ mact (wval p.2) 4 = p.1 ∧
      ∀ i ∈ p.2, i < 2) ∧
    (∀ c ∈ H18, c ≠ 1 → c ≠ 2 → c ≠ 3 → c ∈ s4w.map Prod.fst) ∧
    (∀ p ∈ candw, wval p.2 = p.1 ∧ ∀ i ∈ p.2, i < 2) := by
  decide +kernel

theorem chk_last : ∀ c8 ∈ [8, 12], ∀ c16 ∈ H18, ∀ c32 ∈ H18,
    (∀ v ∈ H18, mact [1, 2, 4, c8, c16, c32] v ∈ H18) →
      [1, 2, 4, c8, c16, c32] ∈ candw.map Prod.fst := by
  decide +kernel

@[expose] def setStab (S : List ℕ) (hS : ∀ c ∈ S, c < 64) : Subgroup (MulAut W6) where
  carrier := {x | ∀ c ∈ S, mact (mcode ⇑x) c ∈ S}
  mul_mem' := fun {x y} hx hy c hc => by
    show mact (mcode ⇑(x * y)) c ∈ S
    rw [mact_mul x y (hS c hc)]
    exact hx _ (hy c hc)
  one_mem' := fun c hc => by
    show mact (mcode ⇑(1 : MulAut W6)) c ∈ S
    rw [mact_one (hS c hc)]
    exact hc
  inv_mem' := fun {x} hx => by
    have hpow : ∀ k : ℕ, ∀ c ∈ S, mact (mcode ⇑(x ^ k)) c ∈ S := by
      intro k
      induction k with
      | zero =>
        intro c hc
        rw [pow_zero, mact_one (hS c hc)]
        exact hc
      | succ k ih =>
        intro c hc
        rw [pow_succ, mact_mul _ _ (hS c hc)]
        exact ih _ (hx c hc)
    have e : x⁻¹ = x ^ (orderOf x - 1) := by
      rw [eq_comm, ← mul_eq_one_iff_eq_inv, ← pow_succ, Nat.sub_add_cancel
        (orderOf_pos x), pow_orderOf_eq_one]
    show ∀ c ∈ S, mact (mcode ⇑x⁻¹) c ∈ S
    rw [e]
    exact hpow _

theorem Gam0_le_setStab {S : List ℕ} (hS : ∀ c ∈ S, c < 64) (h1 : ∀ c ∈ S, mact g1c c ∈ S)
    (h2 : ∀ c ∈ S, mact g2c c ∈ S) : Gam0 ≤ setStab S hS := by
  refine (Subgroup.closure_le _).mpr ?_
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl
  · show ∀ c ∈ S, mact (mcode ⇑hg1) c ∈ S
    rw [mcode_hg1]
    exact h1
  · show ∀ c ∈ S, mact (mcode ⇑hg2) c ∈ S
    rw [mcode_hg2]
    exact h2

theorem Nor0_le_setStab : Nor0 ≤ setStab H18 chk_orbits.2.2.1 := by
  refine (Subgroup.closure_le _).mpr ?_
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl
  · show ∀ c ∈ H18, mact (mcode ⇑hg1) c ∈ H18
    rw [mcode_hg1]
    exact fun c hc => (chk_orbits.2.2.2.2.2.1 c hc).1
  · show ∀ c ∈ H18, mact (mcode ⇑hg2) c ∈ H18
    rw [mcode_hg2]
    exact fun c hc => (chk_orbits.2.2.2.2.2.1 c hc).2.1
  · show ∀ c ∈ H18, mact (mcode ⇑hsg) c ∈ H18
    rw [mcode_hsg]
    exact fun c hc => (chk_orbits.2.2.2.2.2.1 c hc).2.2

theorem mem_H18_of_normalizer {y : MulAut W6}
    (hy : y ∈ Subgroup.normalizer (Gam0 : Set (MulAut W6))) {c : ℕ} (hc : c ∈ H18) :
    mact (mcode ⇑y) c ∈ H18 := by
  classical
  have hc64 : c < 64 := chk_orbits.2.2.1 c hc
  set d := mact (mcode ⇑y) c with hd
  have hd64 : d < 64 := mact_lt' y c
  have hzero : mact (mcode ⇑y) 0 = 0 := by
    apply dec_injective (mact_lt' _ _) (by norm_num)
    rw [dec_mact _ (by norm_num), dec_zero]
    show Multiplicative.toAdd (y 1) = 0
    rw [map_one]
    rfl
  have hd0 : d ≠ 0 := by
    intro h0
    have h1 : c = 0 := mact_inj y hc64 (by norm_num) (by rw [← hd, h0, hzero])
    exact chk_orbits.2.1 (h1 ▸ hc)
  rcases chk_orbits.1 d hd64 with h | h | h
  · exact absurd h hd0
  · exact h
  exfalso
  have hyi : y⁻¹ ∈ Subgroup.normalizer (Gam0 : Set (MulAut W6)) := Subgroup.inv_mem _ hy
  have hconj : ∀ g ∈ Gam0, y⁻¹ * g * y ∈ Gam0 := by
    intro g hg
    have := (Subgroup.mem_normalizer_iff.mp hyi g).mp hg
    simpa using this
  have hyd : mact (mcode ⇑y⁻¹) d = c := mact_inv_of hc64 hd.symm
  obtain ⟨⟨d', wd⟩, hpd, hdd⟩ := List.mem_map.mp h
  simp only at hdd
  obtain ⟨hwd, hwd2⟩ := orb_checks.1 _ hpd
  have hGH := Gam0_le_setStab chk_orbits.2.2.1 (fun c hc => (chk_orbits.2.2.2.2.2.1 c hc).1)
    (fun c hc => (chk_orbits.2.2.2.2.2.1 c hc).2.1)
  have hmem : ∀ e ∈ orbw.map Prod.fst, mact (mcode ⇑y⁻¹) e ∈ H18 := by
    intro e he
    obtain ⟨⟨e', we⟩, hp, rfl⟩ := List.mem_map.mp he
    obtain ⟨hwe, hwe2⟩ := orb_checks.1 _ hp
    set g := welt we * (welt wd)⁻¹ with hg
    have hgG : g ∈ Gam0 :=
      Gam0.mul_mem (welt_mem_Gam0 _ hwe2) (Gam0.inv_mem (welt_mem_Gam0 _ hwd2))
    have h17 : mact (mcode ⇑(welt wd)⁻¹) d = 17 :=
      mact_inv_of (by norm_num) (by rw [mcode_welt]; exact hwd.trans hdd)
    have he' : e' = mact (mcode ⇑g) d := by
      rw [hg, mact_mul _ _ hd64, h17, mcode_welt]
      exact hwe.symm
    simp only
    rw [he', ← mact_mul _ _ hd64, show y⁻¹ * g = (y⁻¹ * g * y) * y⁻¹ by group,
      mact_mul _ _ hd64, hyd]
    exact hGH (hconj g hgG) c hc
  have hlt : ∀ e ∈ orbw.map Prod.fst, e < 64 := by
    intro e he
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp he
    exact orb_checks.2.2.2.2.1 p hp
  let f : {e // e ∈ orbw.map Prod.fst} → {e // e ∈ H18} :=
    fun e => ⟨mact (mcode ⇑y⁻¹) e.1, hmem e.1 e.2⟩
  have hf : Function.Injective f := fun e₁ e₂ h12 =>
    Subtype.ext (mact_inj y⁻¹ (hlt _ e₁.2) (hlt _ e₂.2) (congrArg Subtype.val h12))
  have h1 := Nat.card_le_card_of_injective f hf
  rw [card_subtype_mem _ orb_checks.2.2.1, card_subtype_mem _ chk_orbits.2.2.2.1,
    List.length_map, orb_checks.2.2.2.1, chk_orbits.2.2.2.2.1] at h1
  omega

theorem mem_Nor0_of_normalizer {y : MulAut W6}
    (hy : y ∈ Subgroup.normalizer (Gam0 : Set (MulAut W6))) : y ∈ Nor0 := by
  have hS := chk_orbits.2.2.1
  have hPy : y ∈ setStab H18 hS := fun c hc => mem_H18_of_normalizer hy hc
  have hPN := Nor0_le_setStab
  have hm1 : (1 : ℕ) ∈ H18 := by decide
  have hm2 : (2 : ℕ) ∈ H18 := by decide
  have hm4 : (4 : ℕ) ∈ H18 := by decide
  have hm8 : (8 : ℕ) ∈ H18 := by decide
  have hm12 : (12 : ℕ) ∈ H18 := by decide
  have hm16 : (16 : ℕ) ∈ H18 := by decide
  have hm32 : (32 : ℕ) ∈ H18 := by decide
  obtain ⟨y₁, ⟨n₁, hn₁, rfl⟩, hy₁1⟩ :
      ∃ y₁, (∃ n ∈ Nor0, y₁ = n * y) ∧ mact (mcode ⇑y₁) 1 = 1 := by
    obtain ⟨⟨c1, w1⟩, hp, hpc⟩ := List.mem_map.mp
      (chk_orbits.2.2.2.2.2.2.2 ▸ hPy 1 hm1 : mact (mcode ⇑y) 1 ∈ h18w.map Prod.fst)
    obtain ⟨hw1, hw1'⟩ := chk_orbits.2.2.2.2.2.2.1 _ hp
    refine ⟨(welt w1)⁻¹ * y, ⟨(welt w1)⁻¹, Gam0_le_Nor0 (Gam0.inv_mem
      (welt_mem_Gam0 _ hw1')), rfl⟩, ?_⟩
    rw [mact_mul _ _ (by norm_num)]
    refine mact_inv_of (by norm_num) ?_
    rw [mcode_welt]
    exact hw1.trans hpc
  have hy₁S : n₁ * y ∈ setStab H18 hS := (setStab H18 hS).mul_mem (hPN hn₁) hPy
  obtain ⟨y₂, ⟨n₂, hn₂, rfl⟩, hy₂1, hy₂2⟩ :
      ∃ y₂, (∃ n ∈ Nor0, y₂ = n * y) ∧ mact (mcode ⇑y₂) 1 = 1 ∧ mact (mcode ⇑y₂) 2 = 2 := by
    have h3 : 1 ^^^ mact (mcode ⇑(n₁ * y)) 2 ∈ H18 := by
      rw [← hy₁1, ← mact_xor]
      exact hy₁S 3 (by decide)
    rcases chk_words.1 _ (hy₁S 2 hm2) h3 with h2 | h2
    · exact ⟨n₁ * y, ⟨n₁, hn₁, rfl⟩, hy₁1, h2⟩
    · refine ⟨hsg * (n₁ * y), ⟨hsg * n₁, Nor0.mul_mem (gen_mem_Nor0 2) hn₁, by group⟩, ?_, ?_⟩
      · rw [mact_mul _ _ (by norm_num), hy₁1, mcode_hsg]
        exact chk_words.2.2.1
      · rw [mact_mul _ _ (by norm_num), h2, mcode_hsg]
        exact chk_words.2.2.2.1
  have hy₂S : n₂ * y ∈ setStab H18 hS := (setStab H18 hS).mul_mem (hPN hn₂) hPy
  obtain ⟨y₃, ⟨n₃, hn₃, rfl⟩, hy₃1, hy₃2, hy₃4⟩ :
      ∃ y₃, (∃ n ∈ Nor0, y₃ = n * y) ∧ mact (mcode ⇑y₃) 1 = 1 ∧ mact (mcode ⇑y₃) 2 = 2 ∧
        mact (mcode ⇑y₃) 4 = 4 := by
    set c4 := mact (mcode ⇑(n₂ * y)) 4 with hc4
    have hc4H : c4 ∈ H18 := hy₂S 4 hm4
    have hne : ∀ a < 64, a ≠ 4 → mact (mcode ⇑(n₂ * y)) a ≠ c4 := fun a ha h4 h =>
      h4 (mact_inj _ ha (by norm_num) h)
    have hy₂3 : mact (mcode ⇑(n₂ * y)) 3 = 3 := by
      rw [show (3 : ℕ) = 1 ^^^ 2 by decide, mact_xor, hy₂1, hy₂2]
    have hc41 : c4 ≠ 1 := fun h => hne 1 (by norm_num) (by norm_num) (hy₂1.trans h.symm)
    have hc42 : c4 ≠ 2 := fun h => hne 2 (by norm_num) (by norm_num) (hy₂2.trans h.symm)
    have hc43 : c4 ≠ 3 := fun h => hne 3 (by norm_num) (by norm_num) (hy₂3.trans h.symm)
    obtain ⟨⟨c, w⟩, hp, hpc⟩ := List.mem_map.mp (chk_words.2.2.2.2.2.1 c4 hc4H hc41 hc42 hc43)
    simp only at hpc
    obtain ⟨hw1, hw2, hw4, hw'⟩ := chk_words.2.2.2.2.1 _ hp
    have hg : (welt w)⁻¹ ∈ Nor0 := Gam0_le_Nor0 (Gam0.inv_mem (welt_mem_Gam0 _ hw'))
    refine ⟨(welt w)⁻¹ * (n₂ * y), ⟨(welt w)⁻¹ * n₂, Nor0.mul_mem hg hn₂, by group⟩, ?_, ?_, ?_⟩
    · rw [mact_mul _ _ (by norm_num), hy₂1]
      exact mact_inv_of (by norm_num) (by rw [mcode_welt]; exact hw1)
    · rw [mact_mul _ _ (by norm_num), hy₂2]
      exact mact_inv_of (by norm_num) (by rw [mcode_welt]; exact hw2)
    · rw [mact_mul _ _ (by norm_num), ← hc4]
      exact mact_inv_of (by norm_num) (by rw [mcode_welt, hw4, hpc])
  have hy₃S : n₃ * y ∈ setStab H18 hS := (setStab H18 hS).mul_mem (hPN hn₃) hPy
  have h12 : 4 ^^^ mact (mcode ⇑(n₃ * y)) 8 ∈ H18 := by
    rw [← hy₃4, ← mact_xor]
    exact hy₃S 12 hm12
  have h8 : mact (mcode ⇑(n₃ * y)) 8 ∈ [8, 12] := by
    rcases chk_words.2.1 _ (hy₃S 8 hm8) h12 with h | h <;> rw [h] <;> decide
  have hcode := mcode_eq (n₃ * y)
  rw [hy₃1, hy₃2, hy₃4] at hcode
  have hcand := chk_last _ h8 _ (hy₃S 16 hm16) _ (hy₃S 32 hm32) (by
    rw [← hcode]
    exact hy₃S)
  rw [← hcode] at hcand
  obtain ⟨⟨m, w⟩, hp, hpm⟩ := List.mem_map.mp hcand
  obtain ⟨hw, hw'⟩ := chk_words.2.2.2.2.2.2 _ hp
  have hy₃G : n₃ * y ∈ Gam0 := by
    have e : n₃ * y = welt w := mcode_injective (by rw [mcode_welt]; exact (hw.trans hpm).symm)
    rw [e]
    exact welt_mem_Gam0 _ hw'
  have e : y = n₃⁻¹ * (n₃ * y) := by group
  rw [e]
  exact Nor0.mul_mem (Nor0.inv_mem hn₃) (Gam0_le_Nor0 hy₃G)

theorem hatA6Normalizer_holds : HatA6Normalizer := by
  apply le_antisymm (fun y hy => mem_Nor0_of_normalizer hy)
  refine (Subgroup.closure_le _).mpr ?_
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  have hsg_inv : hsg⁻¹ = hsg := inv_eq_of_mul_eq_one_right hsg_sq
  rcases hx with rfl | rfl | rfl
  · exact Subgroup.le_normalizer (Subgroup.subset_closure (by simp))
  · exact Subgroup.le_normalizer (Subgroup.subset_closure (by simp))
  · show hsg ∈ Subgroup.normalizer (Gam0 : Set (MulAut W6))
    rw [Subgroup.mem_normalizer_iff]
    intro g
    rw [hsg_inv]
    refine ⟨hsg_conj_mem, fun hg => ?_⟩
    have h1 := hsg_conj_mem hg
    have e : hsg * (hsg * g * hsg) * hsg = g := by
      rw [← mul_assoc, ← mul_assoc, hsg_sq, one_mul, mul_assoc, hsg_sq, mul_one]
    rwa [e] at h1

end CFSG.Quasithin.H13.HatN
