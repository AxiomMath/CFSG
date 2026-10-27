module

public import CFSG.Quasithin.Vol2.F134TitsBridge
public import CFSG.Quasithin.Vol2.F134RuBasic
public import CFSG.Quasithin.Vol2.F134M23Basic

public section

namespace CFSG.Quasithin.F134

open CFSG.Blueprint CFSG.Quasithin.P134
open scoped Pointwise

@[expose] noncomputable def titsWord : List ℕ → GL (Fin 26) (ZMod 2)
  | [] => 1
  | i :: w => titsRhoN i * titsWord w

theorem glCode26_titsWord : ∀ w : List ℕ, (∀ c ∈ w, c < 10) → glCode26 (titsWord w) = titsWordC w
  | [], _ => glCode26_one
  | i :: w, hw => by
    rw [titsWord, titsWordC, glCode26_mul, glCode26_titsRhoN (hw i List.mem_cons_self),
      glCode26_titsWord w fun c hc => hw c (List.mem_cons_of_mem _ hc)]

theorem titsWord_mem : ∀ w : List ℕ, titsWord w ∈ titsGroup
  | [] => one_mem _
  | i :: w => mul_mem (titsRhoN_mem i) (titsWord_mem w)

@[expose] noncomputable def titsTGen (k : ℕ) : GL (Fin 26) (ZMod 2) :=
  titsWord (titsTGenW.getD k [])

@[expose] noncomputable def titsSyl : Subgroup (GL (Fin 26) (ZMod 2)) :=
  Subgroup.closure {x | ∃ k < 2, titsTGen k = x}

theorem glCode26_titsTGen {k : ℕ} (hk : k < 2) : glCode26 (titsTGen k) = titsTG k := by
  obtain ⟨h1, h2⟩ := tits_tgen_check k hk
  rw [titsTGen, glCode26_titsWord _ h1]
  exact h2

theorem titsTGen_mem {k : ℕ} (hk : k < 2) : titsTGen k ∈ titsSyl :=
  Subgroup.subset_closure ⟨k, hk, rfl⟩

theorem titsSyl_le : titsSyl ≤ titsGroup := by
  rw [titsSyl, Subgroup.closure_le]
  rintro _ ⟨k, -, rfl⟩
  exact titsWord_mem _

@[expose] noncomputable def titsTWord : List ℕ → GL (Fin 26) (ZMod 2)
  | [] => 1
  | k :: w => titsTGen k * titsTWord w

theorem glCode26_titsTWord : ∀ w : List ℕ, (∀ c ∈ w, c < 2) →
    glCode26 (titsTWord w) = titsTWordC w
  | [], _ => glCode26_one
  | k :: w, hw => by
    rw [titsTWord, titsTWordC, glCode26_mul, glCode26_titsTGen (hw k List.mem_cons_self),
      glCode26_titsTWord w fun c hc => hw c (List.mem_cons_of_mem _ hc)]

theorem titsTWord_mem : ∀ w : List ℕ, (∀ c ∈ w, c < 2) → titsTWord w ∈ titsSyl
  | [], _ => one_mem _
  | k :: w, hw => mul_mem (titsTGen_mem (hw k List.mem_cons_self))
      (titsTWord_mem w fun c hc => hw c (List.mem_cons_of_mem _ hc))

@[expose] noncomputable def titsXE (p : ℕ) : GL (Fin 26) (ZMod 2) := titsTWord (titsXW.getD p [])

theorem glCode26_titsXE {p : ℕ} (hp : p < 11) : glCode26 (titsXE p) = titsXC p := by
  obtain ⟨h1, h2⟩ := tits_x_check p hp
  rw [titsXE, glCode26_titsTWord _ h1]
  exact h2

theorem titsXE_mem {p : ℕ} (hp : p < 11) : titsXE p ∈ titsSyl :=
  titsTWord_mem _ (tits_x_check p hp).1

@[expose] noncomputable def titsFold (f : ℕ → Bool) (X : ℕ → GL (Fin 26) (ZMod 2))
    (u : GL (Fin 26) (ZMod 2)) (l : List ℕ) : GL (Fin 26) (ZMod 2) :=
  l.foldl (fun acc p => bif f p then acc * X p else acc) u

theorem titsFold_nil (f : ℕ → Bool) (X : ℕ → GL (Fin 26) (ZMod 2)) (u : GL (Fin 26) (ZMod 2)) :
    titsFold f X u [] = u := by
  rw [titsFold, List.foldl_nil]

theorem titsFold_cons (f : ℕ → Bool) (X : ℕ → GL (Fin 26) (ZMod 2)) (u : GL (Fin 26) (ZMod 2))
    (p : ℕ) (l : List ℕ) :
    titsFold f X u (p :: l) = titsFold f X (bif f p then u * X p else u) l := by
  rw [titsFold, titsFold, List.foldl_cons]

theorem glCode26_titsFold (f : ℕ → Bool) (X : ℕ → GL (Fin 26) (ZMod 2)) (C : ℕ → ℕ)
    (l : List ℕ) : ∀ (u : GL (Fin 26) (ZMod 2)), (∀ p ∈ l, glCode26 (X p) = C p) →
      glCode26 (titsFold f X u l) =
        l.foldl (fun acc p => bif f p then mulF26 acc (C p) else acc) (glCode26 u) := by
  induction l with
  | nil => intro u _; rw [titsFold_nil, List.foldl_nil]
  | cons p l ih =>
    intro u hX
    have e2 : glCode26 (bif f p then u * X p else u) =
        (bif f p then mulF26 (glCode26 u) (C p) else glCode26 u) := by
      cases f p
      · rw [Bool.cond_false, Bool.cond_false]
      · rw [Bool.cond_true, Bool.cond_true, glCode26_mul, hX p List.mem_cons_self]
    rw [titsFold_cons, List.foldl_cons, ih _ fun q hq => hX q (List.mem_cons_of_mem _ hq), e2]

theorem titsFold_of_false (f : ℕ → Bool) (X : ℕ → GL (Fin 26) (ZMod 2)) (l : List ℕ) :
    ∀ (u : GL (Fin 26) (ZMod 2)), (∀ p ∈ l, f p = false) → titsFold f X u l = u := by
  induction l with
  | nil => intro u _; rw [titsFold_nil]
  | cons p l ih =>
    intro u hf
    rw [titsFold_cons, hf p List.mem_cons_self, Bool.cond_false]
    exact ih u fun q hq => hf q (List.mem_cons_of_mem _ hq)

theorem titsFold_mem (f : ℕ → Bool) (X : ℕ → GL (Fin 26) (ZMod 2))
    (H : Subgroup (GL (Fin 26) (ZMod 2))) (l : List ℕ) :
    ∀ (u : GL (Fin 26) (ZMod 2)), u ∈ H → (∀ p ∈ l, f p = true → X p ∈ H) →
      titsFold f X u l ∈ H := by
  induction l with
  | nil => intro u hu _; rw [titsFold_nil]; exact hu
  | cons p l ih =>
    intro u hu hX
    rw [titsFold_cons]
    refine ih _ ?_ fun q hq => hX q (List.mem_cons_of_mem _ hq)
    cases hf : f p
    · rw [Bool.cond_false]
      exact hu
    · rw [Bool.cond_true]
      exact mul_mem hu (hX p List.mem_cons_self hf)

@[expose] noncomputable def titsTAE (a : ℕ) : GL (Fin 26) (ZMod 2) :=
  titsFold a.testBit titsXE 1 (List.range 6)

@[expose] noncomputable def titsTBE (b : ℕ) : GL (Fin 26) (ZMod 2) :=
  titsFold b.testBit (fun p => titsXE (6 + p)) 1 (List.range 5)

@[expose] noncomputable def titsNFE (e : ℕ) : GL (Fin 26) (ZMod 2) :=
  titsTAE (e % 64) * titsTBE (e / 64)

theorem glCode26_titsNFE {e : ℕ} (he : e < 2048) : glCode26 (titsNFE e) = titsNFC e := by
  have ha : glCode26 (titsTAE (e % 64)) = titsTAC (e % 64) := by
    rw [titsTAE, glCode26_titsFold _ _ titsXC _ _ fun p hp =>
      glCode26_titsXE (by have := List.mem_range.mp hp; omega), glCode26_one]
    exact tits_ta_check _ (Nat.mod_lt _ (by norm_num))
  have hb : glCode26 (titsTBE (e / 64)) = titsTBC (e / 64) := by
    rw [titsTBE, glCode26_titsFold _ _ (fun p => titsXC (6 + p)) _ _ fun p hp =>
      glCode26_titsXE (by have := List.mem_range.mp hp; omega), glCode26_one]
    exact tits_tb_check _ (by omega)
  rw [titsNFE, glCode26_mul, ha, hb]
  rfl

theorem titsNFE_mem (e : ℕ) : titsNFE e ∈ titsSyl := by
  refine mul_mem (titsFold_mem _ _ _ _ _ (one_mem _) fun p hp _ => titsXE_mem ?_)
    (titsFold_mem _ _ _ _ _ (one_mem _) fun p hp _ => titsXE_mem ?_)
  · have := List.mem_range.mp hp
    omega
  · have := List.mem_range.mp hp
    omega

theorem titsNFE_zero : titsNFE 0 = 1 := by
  rw [titsNFE, Nat.zero_mod, Nat.zero_div, titsTAE, titsTBE,
    titsFold_of_false _ _ _ _ fun p _ => Nat.zero_testBit p,
    titsFold_of_false _ _ _ _ fun p _ => Nat.zero_testBit p, mul_one]

theorem titsNFE_mem_pcSub {e i : ℕ} (hb : ∀ q < i, e.testBit q = false) :
    titsNFE e ∈ pcSub 11 titsXE i := by
  refine mul_mem (titsFold_mem _ _ _ _ _ (one_mem _) fun p hp hpe => ?_)
    (titsFold_mem _ _ _ _ _ (one_mem _) fun p hp hpe => ?_)
  · have hp6 := List.mem_range.mp hp
    have hbit : e.testBit p = true := by
      rw [show (64 : ℕ) = 2 ^ 6 by norm_num, Nat.testBit_mod_two_pow] at hpe
      simpa [hp6] using hpe
    have hip : i ≤ p := by
      by_contra h
      rw [hb p (by omega)] at hbit
      exact Bool.false_ne_true hbit
    exact mem_pcSub hip (by omega)
  · have hp5 := List.mem_range.mp hp
    have hbit : e.testBit (6 + p) = true := by
      rw [show (64 : ℕ) = 2 ^ 6 by norm_num, Nat.testBit_div_two_pow] at hpe
      rwa [add_comm]
    have hip : i ≤ 6 + p := by
      by_contra h
      rw [hb (6 + p) (by omega)] at hbit
      exact Bool.false_ne_true hbit
    exact mem_pcSub hip (by omega)

theorem titsSyl_isPGroup : IsPGroup 2 titsSyl := by
  have hsq : ∀ i < 11, titsXE i ^ 2 ∈ pcSub 11 titsXE (i + 1) := by
    intro i hi
    obtain ⟨he, hb, hc⟩ := tits_sq_check i hi
    have : titsXE i ^ 2 = titsNFE (titsSq i) := eq_of_glCode26 (by
      rw [sq, glCode26_mul, glCode26_titsXE hi, glCode26_titsNFE he]
      exact hc)
    rw [this]
    exact titsNFE_mem_pcSub hb
  have hcj : ∀ i < 11, ∀ j < 11, i < j →
      (titsXE i)⁻¹ * titsXE j * titsXE i ∈ pcSub 11 titsXE (i + 1) := by
    intro i hi j hj hij
    obtain ⟨he, hb, hc⟩ := tits_cj_check i hi j hj hij
    have h : titsXE j * titsXE i = titsXE i * titsNFE (titsCj i j) := eq_of_glCode26 (by
      rw [glCode26_mul, glCode26_mul, glCode26_titsXE hi, glCode26_titsXE hj,
        glCode26_titsNFE he]
      exact hc)
    have : (titsXE i)⁻¹ * titsXE j * titsXE i = titsNFE (titsCj i j) := by
      rw [mul_assoc, h, ← mul_assoc, inv_mul_cancel, one_mul]
    rw [this]
    exact titsNFE_mem_pcSub hb
  have hpc := isPGroup_two_of_pc 11 titsXE hsq hcj
  refine hpc.to_le ?_
  rw [titsSyl, Subgroup.closure_le]
  rintro _ ⟨k, hk, rfl⟩
  obtain ⟨he, hc⟩ := tits_tnf_check k hk
  have : titsTGen k = titsNFE (titsTnf k) :=
    eq_of_glCode26 (by rw [glCode26_titsTGen hk, glCode26_titsNFE he]; exact hc)
  rw [this]
  exact titsNFE_mem_pcSub fun q hq => absurd hq (Nat.not_lt_zero q)

theorem titsRhoN_mem_titsSyl {i : ℕ} (hi : i < 10) (h2 : 2 ≤ i) : titsRhoN i ∈ titsSyl := by
  obtain ⟨he, hc⟩ := tits_rnf_check i hi h2
  have : titsRhoN i = titsNFE (titsRnf i) :=
    eq_of_glCode26 (by rw [glCode26_titsRhoN hi, glCode26_titsNFE he]; exact hc)
  rw [this]
  exact titsNFE_mem _

@[expose] noncomputable def titsDP (j : ℕ) : GL (Fin 26) (ZMod 2) := titsWord (titsDW.getD j [])

theorem glCode26_titsDP {j : ℕ} (hj : j < 18) : glCode26 (titsDP j) = titsDC j := by
  obtain ⟨h1, h2⟩ := tits_d_check.2.2 j hj
  rw [titsDP, glCode26_titsWord _ h1]
  exact h2

theorem titsDP_zero : titsDP 0 = 1 := by
  rw [titsDP, tits_d_check.1]
  rfl

theorem titsDP_one : titsDP 1 = titsRhoN 1 := by
  rw [titsDP, tits_d_check.2.1, titsWord, titsWord, mul_one]

@[expose] def titsCover : Set (GL (Fin 26) (ZMod 2)) :=
  {x | ∃ j < 18, ∃ t ∈ titsSyl, ∃ t' ∈ titsSyl, x = t * titsDP j * t'}

theorem one_mem_titsCover : (1 : GL (Fin 26) (ZMod 2)) ∈ titsCover :=
  ⟨0, by norm_num, 1, one_mem _, 1, one_mem _, by rw [titsDP_zero]; group⟩

theorem titsCover_mul_T {x s : GL (Fin 26) (ZMod 2)} (hx : x ∈ titsCover) (hs : s ∈ titsSyl) :
    x * s ∈ titsCover := by
  obtain ⟨j, hj, t, ht, t', ht', rfl⟩ := hx
  exact ⟨j, hj, t, ht, t' * s, mul_mem ht' hs, by group⟩

theorem tits_coset_g {c : ℕ} (hc : c < 2) {t : GL (Fin 26) (ZMod 2)} (ht : t ∈ titsSyl) :
    ∃ s < titsM c, ∃ v ∈ titsSyl, t * titsRhoN c = titsNFE (titsR c s) * titsRhoN c * v := by
  obtain ⟨hM, hR0, hcl⟩ := tits_gcl_check c hc
  refine closure_subset_of_left_closed (S := {x | ∃ k < 2, titsTGen k = x})
    (P := {t | ∃ s < titsM c, ∃ v ∈ titsSyl,
      t * titsRhoN c = titsNFE (titsR c s) * titsRhoN c * v})
    (fun s _ => ⟨orderOf s, orderOf_pos s, pow_orderOf_eq_one s⟩)
    ⟨0, hM, 1, one_mem _, by rw [hR0, titsNFE_zero]; group⟩ ?_ ht
  rintro p ⟨s, hs, v, hv, hpv⟩ _ ⟨k, hk, rfl⟩
  obtain ⟨hs', hr, hr', hcert⟩ := hcl k hk s hs
  have key : titsTGen k * titsNFE (titsR c s) * titsRhoN c =
      titsNFE (titsR c (titsCL c (titsM c * k + s) / 2048)) * titsRhoN c *
        titsNFE (titsCL c (titsM c * k + s) % 2048) := eq_of_glCode26 (by
    rw [glCode26_mul, glCode26_mul, glCode26_mul, glCode26_mul, glCode26_titsTGen hk,
      glCode26_titsNFE hr, glCode26_titsRhoN (by omega), glCode26_titsNFE hr',
      glCode26_titsNFE (Nat.mod_lt _ (by norm_num))]
    exact hcert)
  refine ⟨_, hs', titsNFE (titsCL c (titsM c * k + s) % 2048) * v, mul_mem (titsNFE_mem _) hv,
    ?_⟩
  calc titsTGen k * p * titsRhoN c = titsTGen k * (p * titsRhoN c) := by group
    _ = titsTGen k * (titsNFE (titsR c s) * titsRhoN c * v) := by rw [hpv]
    _ = titsTGen k * titsNFE (titsR c s) * titsRhoN c * v := by group
    _ = _ := by rw [key]; group

theorem titsCover_mul_g {c : ℕ} (hc : c < 2) {x : GL (Fin 26) (ZMod 2)} (hx : x ∈ titsCover) :
    x * titsRhoN c ∈ titsCover := by
  obtain ⟨j, hj, t, ht, t', ht', rfl⟩ := hx
  obtain ⟨s, hs, v, hv, hve⟩ := tits_coset_g hc ht'
  obtain ⟨hk, hr, hdeq⟩ := tits_gdec_check c hc j hj s hs
  generalize titsDec c (titsM c * j + s) = e at hk hdeq
  have hd : titsDP j * titsNFE (titsR c s) * titsRhoN c =
      titsNFE (e / 2048 % 2048) * titsDP (e / 4194304) * titsNFE (e % 2048) :=
    eq_of_glCode26 (by
      rw [glCode26_mul, glCode26_mul, glCode26_mul, glCode26_mul, glCode26_titsDP hj,
        glCode26_titsNFE hr, glCode26_titsRhoN (by omega),
        glCode26_titsNFE (Nat.mod_lt _ (by norm_num)), glCode26_titsDP hk,
        glCode26_titsNFE (Nat.mod_lt _ (by norm_num))]
      exact hdeq)
  refine ⟨e / 4194304, hk, t * titsNFE (e / 2048 % 2048), mul_mem ht (titsNFE_mem _),
    titsNFE (e % 2048) * v, mul_mem (titsNFE_mem _) hv, ?_⟩
  calc t * titsDP j * t' * titsRhoN c = t * titsDP j * (t' * titsRhoN c) := by group
    _ = t * titsDP j * (titsNFE (titsR c s) * titsRhoN c * v) := by rw [hve]
    _ = t * (titsDP j * titsNFE (titsR c s) * titsRhoN c) * v := by group
    _ = _ := by rw [hd]; group

theorem titsCover_mul_rho {x : GL (Fin 26) (ZMod 2)} (hx : x ∈ titsCover) (i : ℕ) :
    x * titsRhoN i ∈ titsCover := by
  rcases Nat.lt_or_ge i 2 with h2 | h2
  · exact titsCover_mul_g h2 hx
  · rcases Nat.lt_or_ge i 10 with h10 | h10
    · exact titsCover_mul_T hx (titsRhoN_mem_titsSyl h10 h2)
    · rw [titsRhoN, dite_eq_right (by omega), mul_one]
      exact hx

theorem titsGroup_subset_cover : (titsGroup : Set (GL (Fin 26) (ZMod 2))) ⊆ titsCover := by
  refine closure_subset_of_right_closed
    (fun s _ => ⟨orderOf s, orderOf_pos s, pow_orderOf_eq_one s⟩) one_mem_titsCover ?_
  rintro p hp _ ⟨i, rfl⟩
  exact titsCover_mul_rho hp i

theorem tits_not_mem_of_bad {H : Subgroup (GL (Fin 26) (ZMod 2))} (hTH : titsSyl ≤ H)
    (hp : ∀ p, (p = 5 ∨ p = 13) → ¬ p ∣ Nat.card H) {j : ℕ} (hj : j < 18) (hj2 : 2 ≤ j)
    (hD : titsDP j ∈ H) : False := by
  obtain ⟨hp', hu, hpow, hne⟩ := tits_bad_check j hj hj2
  set p := titsBad j % 32 with hpdef
  have hprime : p.Prime := by rcases hp' with h | h <;> rw [h] <;> norm_num
  have : Fact p.Prime := ⟨hprime⟩
  let x : H := ⟨(titsDP j * titsNFE (titsBad j / 1024)) ^ (titsBad j / 32 % 32),
    pow_mem (mul_mem hD (hTH (titsNFE_mem _))) _⟩
  have hcode : glCode26 (x : GL (Fin 26) (ZMod 2)) = titsPow (titsBad j / 32 % 32)
      (mulF26 (titsDC j) (titsNFC (titsBad j / 1024))) := by
    show glCode26 ((titsDP j * titsNFE (titsBad j / 1024)) ^ (titsBad j / 32 % 32)) = _
    rw [glCode26_pow, glCode26_mul, glCode26_titsDP hj, glCode26_titsNFE hu, glCode26_one]
    rfl
  have hxp : x ^ p = 1 := by
    apply Subtype.ext
    apply eq_of_glCode26
    rw [Subgroup.coe_pow, glCode26_pow, hcode, Subgroup.coe_one, glCode26_one]
    exact hpow
  have hx1 : x ≠ 1 := by
    intro h
    apply hne
    rw [← hcode, h, Subgroup.coe_one, glCode26_one]
  exact hp p hp' (orderOf_eq_prime hxp hx1 ▸ orderOf_dvd_natCard x)

theorem tits_card_le {H : Subgroup (GL (Fin 26) (ZMod 2))} (hTH : titsSyl ≤ H)
    (hH : H ≤ titsGroup) (hp : ∀ p, (p = 5 ∨ p = 13) → ¬ p ∣ Nat.card H) :
    Nat.card H ≤ 3 * Nat.card titsSyl := by
  have : Finite titsSyl := Subgroup.instFiniteSubtypeMem _
  refine card_le_of_cover ![1, titsRhoN 1, titsNFE (titsR 1 1) * titsRhoN 1] fun h hh => ?_
  obtain ⟨j, hj, t, ht, t', ht', rfl⟩ := titsGroup_subset_cover (hH hh)
  have hD : titsDP j ∈ H := by
    have e : titsDP j = t⁻¹ * (t * titsDP j * t') * t'⁻¹ := by group
    rw [e]
    exact mul_mem (mul_mem (inv_mem (hTH ht)) hh) (inv_mem (hTH ht'))
  rcases Nat.lt_or_ge j 2 with hj2 | hj2
  · interval_cases j
    · exact ⟨0, t * t', mul_mem ht ht', by rw [titsDP_zero]; simp⟩
    · obtain ⟨s, hs, v, hv, e⟩ := tits_coset_g (c := 1) (by norm_num) ht
      have hM : titsM 1 = 2 := by decide +kernel
      rw [hM] at hs
      have h0 : titsR 1 0 = 0 := (tits_gcl_check 1 (by norm_num)).2.1
      rw [titsDP_one]
      interval_cases s
      · refine ⟨1, v * t', mul_mem hv ht', ?_⟩
        rw [e, h0, titsNFE_zero]
        simp [mul_assoc]
      · exact ⟨2, v * t', mul_mem hv ht', by rw [e]; simp [mul_assoc]⟩
  · exact (tits_not_mem_of_bad hTH hp hj hj2 hD).elim

theorem tits_embedding
    {X : Type} [Group X] (h : ReeTitsModel X .Tits 2 1) :
    ∃ φ : X →* GL (Fin 26) (ZMod 2), Function.Injective φ ∧ (∀ x, φ x ∈ titsGroup) ∧
      ∀ y ∈ titsGroup, ∃ x, φ x = y := by
  obtain ⟨ψ⟩ := titsEquiv h
  refine ⟨(Subgroup.subtype _).comp (ψ : X →* ↥titsGroup), fun a b h => ψ.injective
    (Subgroup.subtype_injective _ h), fun x => (ψ x).2, fun y hy => ?_⟩
  obtain ⟨x, hx⟩ := ψ.surjective ⟨y, hy⟩
  exact ⟨x, congrArg Subtype.val hx⟩

theorem noE9Config_tits
    : NoE9Config fun (X : Type) [Group X] => ReeTitsModel X .Tits 2 1 := by
  intro A _ _ L P T hL hcfg
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨φ₀, hφ₀, hφ₀mem, hφ₀surj⟩ := tits_embedding hL
  obtain ⟨φ, hφ, hφG, -, hTφ⟩ :=
    E9Config.exists_model_conj hcfg hφ₀ hφ₀mem hφ₀surj titsSyl_le titsSyl_isPGroup
  have hHL : P ⊔ (T ⊓ L) ≤ L := E9Config.sup_inf_le hcfg
  have hS := E9Config.isSylowTwoOf_inf hcfg
  obtain ⟨K, hKdef⟩ : ∃ R : Subgroup (GL (Fin 26) (ZMod 2)),
      R = ((P ⊔ (T ⊓ L)).subgroupOf L).map φ := ⟨_, rfl⟩
  have hTK : titsSyl ≤ K := by
    rw [hKdef]
    exact hTφ.trans (Subgroup.map_mono (Subgroup.subgroupOf_mono L le_sup_right))
  have hKM : K ≤ titsGroup := by
    rw [hKdef]
    rintro _ ⟨u, -, rfl⟩
    exact hφG _
  have hKc : Nat.card K = Nat.card (P ⊔ (T ⊓ L) : Subgroup A) := by
    rw [hKdef, ← Nat.card_congr (((P ⊔ (T ⊓ L)).subgroupOf L).equivMapOfInjective _ hφ).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHL).toEquiv]
  have hHc := E9Config.card_sup_inf hcfg
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hS.2.1
  have hle := tits_card_le hTK hKM fun p hp => by
    rw [hKc, hHc, hk]
    have hprime : p.Prime := by rcases hp with h | h <;> rw [h] <;> norm_num
    exact prime_not_dvd_nine_mul_two_pow hprime (by rcases hp with h | h <;> omega)
      (by rcases hp with h | h <;> omega)
  have hTU : Nat.card titsSyl ≤ Nat.card (T ⊓ L : Subgroup A) := by
    rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hS.1).toEquiv,
      Nat.card_congr (((T ⊓ L).subgroupOf L).equivMapOfInjective _ hφ).toEquiv]
    have : Finite (((T ⊓ L).subgroupOf L).map φ) := Subgroup.instFiniteSubtypeMem _
    exact Subgroup.card_le_of_le hTφ
  have hpos : 0 < Nat.card titsSyl := Nat.card_pos
  rw [hKc, hHc] at hle
  omega

end CFSG.Quasithin.F134
