module

public import CFSG.Quasithin.Vol2.F134RuCheck
public import CFSG.Quasithin.Vol2.F134RuCheckD
public import CFSG.Quasithin.Vol2.F134RuCover
public import CFSG.Quasithin.Vol2.F134RuBad
public import CFSG.Quasithin.Vol2.F134RuBasic
public import CFSG.Quasithin.Vol2.F134M23Basic

public section

namespace CFSG.Quasithin.F134

open CFSG.Blueprint CFSG.Quasithin.P134
open scoped Pointwise

theorem eq_of_glCode28 {u v : GL (Fin 28) (ZMod 2)} (h : glCode28 u = glCode28 v) : u = v :=
  glCode28_injective h

@[expose] noncomputable def ruWord : List ℕ → GL (Fin 28) (ZMod 2)
  | [] => 1
  | c :: w => (if c = 0 then ruUA else ruUB) * ruWord w

theorem glCode28_ruWord : ∀ w : List ℕ, glCode28 (ruWord w) = ruWordC w
  | [] => glCode28_one
  | c :: w => by
    rw [ruWord, ruWordC, glCode28_mul, glCode28_ruWord w]
    split_ifs
    · rw [glCode28_ruUA]
    · rw [glCode28_ruUB]

theorem ruWord_mem : ∀ w : List ℕ, ruWord w ∈ ruGroup
  | [] => one_mem _
  | c :: w => by
    refine mul_mem ?_ (ruWord_mem w)
    split_ifs
    · exact Subgroup.subset_closure (Set.mem_insert _ _)
    · exact Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)

@[expose] noncomputable def ruTGen (k : ℕ) : GL (Fin 28) (ZMod 2) := ruWord (ruTGenW.getD k [])

@[expose] noncomputable def ruT : Subgroup (GL (Fin 28) (ZMod 2)) :=
  Subgroup.closure {x | ∃ k < 3, ruTGen k = x}

theorem glCode28_ruTGen {k : ℕ} (hk : k < 3) : glCode28 (ruTGen k) = ruTG k := by
  rw [ruTGen, glCode28_ruWord]
  exact (ru_tgen_check k hk).2

theorem ruTGen_mem {k : ℕ} (hk : k < 3) : ruTGen k ∈ ruT := Subgroup.subset_closure ⟨k, hk, rfl⟩

theorem ruT_le : ruT ≤ ruGroup := by
  rw [ruT, Subgroup.closure_le]
  rintro _ ⟨k, -, rfl⟩
  exact ruWord_mem _

@[expose] noncomputable def ruTWord : List ℕ → GL (Fin 28) (ZMod 2)
  | [] => 1
  | k :: w => ruTGen k * ruTWord w

theorem glCode28_ruTWord : ∀ w : List ℕ, (∀ c ∈ w, c < 3) → glCode28 (ruTWord w) = ruTWordC w
  | [], _ => glCode28_one
  | k :: w, hw => by
    rw [ruTWord, ruTWordC, glCode28_mul, glCode28_ruTGen (hw k List.mem_cons_self),
      glCode28_ruTWord w fun c hc => hw c (List.mem_cons_of_mem _ hc)]

theorem ruTWord_mem : ∀ w : List ℕ, (∀ c ∈ w, c < 3) → ruTWord w ∈ ruT
  | [], _ => one_mem _
  | k :: w, hw => mul_mem (ruTGen_mem (hw k List.mem_cons_self))
      (ruTWord_mem w fun c hc => hw c (List.mem_cons_of_mem _ hc))

@[expose] noncomputable def ruXE (p : ℕ) : GL (Fin 28) (ZMod 2) := ruTWord (ruXW.getD p [])

theorem glCode28_ruXE {p : ℕ} (hp : p < 14) : glCode28 (ruXE p) = ruXC p := by
  obtain ⟨h1, h2⟩ := ru_x_check p hp
  rw [ruXE, glCode28_ruTWord _ h1]
  exact h2

theorem ruXE_mem {p : ℕ} (hp : p < 14) : ruXE p ∈ ruT := ruTWord_mem _ (ru_x_check p hp).1

@[expose] noncomputable def foldProd (f : ℕ → Bool) (X : ℕ → GL (Fin 28) (ZMod 2))
    (u : GL (Fin 28) (ZMod 2)) (l : List ℕ) : GL (Fin 28) (ZMod 2) :=
  l.foldl (fun acc p => bif f p then acc * X p else acc) u

theorem foldProd_nil (f : ℕ → Bool) (X : ℕ → GL (Fin 28) (ZMod 2)) (u : GL (Fin 28) (ZMod 2)) :
    foldProd f X u [] = u := by
  rw [foldProd, List.foldl_nil]

theorem foldProd_cons (f : ℕ → Bool) (X : ℕ → GL (Fin 28) (ZMod 2)) (u : GL (Fin 28) (ZMod 2))
    (p : ℕ) (l : List ℕ) :
    foldProd f X u (p :: l) = foldProd f X (bif f p then u * X p else u) l := by
  rw [foldProd, foldProd, List.foldl_cons]

theorem glCode28_foldProd (f : ℕ → Bool) (X : ℕ → GL (Fin 28) (ZMod 2)) (C : ℕ → ℕ)
    (l : List ℕ) : ∀ (u : GL (Fin 28) (ZMod 2)), (∀ p ∈ l, glCode28 (X p) = C p) →
      glCode28 (foldProd f X u l) =
        l.foldl (fun acc p => bif f p then mulF28 acc (C p) else acc) (glCode28 u) := by
  induction l with
  | nil => intro u _; rw [foldProd_nil, List.foldl_nil]
  | cons p l ih =>
    intro u hX
    have e2 : glCode28 (bif f p then u * X p else u) =
        (bif f p then mulF28 (glCode28 u) (C p) else glCode28 u) := by
      cases f p
      · rw [Bool.cond_false, Bool.cond_false]
      · rw [Bool.cond_true, Bool.cond_true, glCode28_mul, hX p List.mem_cons_self]
    rw [foldProd_cons, List.foldl_cons, ih _ fun q hq => hX q (List.mem_cons_of_mem _ hq), e2]

theorem foldProd_of_false (f : ℕ → Bool) (X : ℕ → GL (Fin 28) (ZMod 2)) (l : List ℕ) :
    ∀ (u : GL (Fin 28) (ZMod 2)), (∀ p ∈ l, f p = false) → foldProd f X u l = u := by
  induction l with
  | nil => intro u _; rw [foldProd_nil]
  | cons p l ih =>
    intro u hf
    rw [foldProd_cons, hf p List.mem_cons_self, Bool.cond_false]
    exact ih u fun q hq => hf q (List.mem_cons_of_mem _ hq)

theorem foldProd_mem (f : ℕ → Bool) (X : ℕ → GL (Fin 28) (ZMod 2))
    (H : Subgroup (GL (Fin 28) (ZMod 2))) (l : List ℕ) :
    ∀ (u : GL (Fin 28) (ZMod 2)), u ∈ H → (∀ p ∈ l, f p = true → X p ∈ H) →
      foldProd f X u l ∈ H := by
  induction l with
  | nil => intro u hu _; rw [foldProd_nil]; exact hu
  | cons p l ih =>
    intro u hu hX
    rw [foldProd_cons]
    refine ih _ ?_ fun q hq => hX q (List.mem_cons_of_mem _ hq)
    cases hf : f p
    · rw [Bool.cond_false]
      exact hu
    · rw [Bool.cond_true]
      exact mul_mem hu (hX p List.mem_cons_self hf)

@[expose] noncomputable def ruTAE (a : ℕ) : GL (Fin 28) (ZMod 2) :=
  foldProd a.testBit ruXE 1 (List.range 7)

@[expose] noncomputable def ruTBE (b : ℕ) : GL (Fin 28) (ZMod 2) :=
  foldProd b.testBit (fun p => ruXE (7 + p)) 1 (List.range 7)

@[expose] noncomputable def ruNFE (e : ℕ) : GL (Fin 28) (ZMod 2) :=
  ruTAE (e % 128) * ruTBE (e / 128)

theorem glCode28_ruNFE {e : ℕ} (he : e < 16384) : glCode28 (ruNFE e) = ruNFC e := by
  have ha : glCode28 (ruTAE (e % 128)) = ruTAC (e % 128) := by
    rw [ruTAE, glCode28_foldProd _ _ ruXC _ _ fun p hp =>
      glCode28_ruXE (by have := List.mem_range.mp hp; omega), glCode28_one]
    exact ru_ta_check _ (Nat.mod_lt _ (by norm_num))
  have hb : glCode28 (ruTBE (e / 128)) = ruTBC (e / 128) := by
    rw [ruTBE, glCode28_foldProd _ _ (fun p => ruXC (7 + p)) _ _ fun p hp =>
      glCode28_ruXE (by have := List.mem_range.mp hp; omega), glCode28_one]
    exact ru_tb_check _ (by omega)
  rw [ruNFE, glCode28_mul, ha, hb]
  rfl

theorem ruNFE_mem (e : ℕ) : ruNFE e ∈ ruT := by
  refine mul_mem (foldProd_mem _ _ _ _ _ (one_mem _) fun p hp _ => ruXE_mem ?_)
    (foldProd_mem _ _ _ _ _ (one_mem _) fun p hp _ => ruXE_mem ?_)
  · have := List.mem_range.mp hp
    omega
  · have := List.mem_range.mp hp
    omega

theorem ruNFE_zero : ruNFE 0 = 1 := by
  rw [ruNFE, Nat.zero_mod, Nat.zero_div, ruTAE, ruTBE,
    foldProd_of_false _ _ _ _ fun p _ => Nat.zero_testBit p,
    foldProd_of_false _ _ _ _ fun p _ => Nat.zero_testBit p, mul_one]

theorem ruNFE_mem_pcSub {e i : ℕ} (hb : ∀ q < i, e.testBit q = false) :
    ruNFE e ∈ pcSub 14 ruXE i := by
  refine mul_mem (foldProd_mem _ _ _ _ _ (one_mem _) fun p hp hpe => ?_)
    (foldProd_mem _ _ _ _ _ (one_mem _) fun p hp hpe => ?_)
  · have hp7 := List.mem_range.mp hp
    have hbit : e.testBit p = true := by
      rw [show (128 : ℕ) = 2 ^ 7 by norm_num, Nat.testBit_mod_two_pow] at hpe
      simpa [hp7] using hpe
    have hip : i ≤ p := by
      by_contra h
      rw [hb p (by omega)] at hbit
      exact Bool.false_ne_true hbit
    exact mem_pcSub hip (by omega)
  · have hp7 := List.mem_range.mp hp
    have hbit : e.testBit (7 + p) = true := by
      rw [show (128 : ℕ) = 2 ^ 7 by norm_num, Nat.testBit_div_two_pow] at hpe
      rwa [add_comm]
    have hip : i ≤ 7 + p := by
      by_contra h
      rw [hb (7 + p) (by omega)] at hbit
      exact Bool.false_ne_true hbit
    exact mem_pcSub hip (by omega)

theorem ruT_isPGroup : IsPGroup 2 ruT := by
  have hsq : ∀ i < 14, ruXE i ^ 2 ∈ pcSub 14 ruXE (i + 1) := by
    intro i hi
    obtain ⟨he, hb, hc⟩ := ru_sq_check i hi
    have : ruXE i ^ 2 = ruNFE (ruSq i) := eq_of_glCode28 (by
      rw [sq, glCode28_mul, glCode28_ruXE hi, glCode28_ruNFE he]
      exact hc)
    rw [this]
    exact ruNFE_mem_pcSub hb
  have hcj : ∀ i < 14, ∀ j < 14, i < j → (ruXE i)⁻¹ * ruXE j * ruXE i ∈ pcSub 14 ruXE (i + 1) := by
    intro i hi j hj hij
    obtain ⟨he, hb, hc⟩ := ru_cj_check i hi j hj hij
    have h : ruXE j * ruXE i = ruXE i * ruNFE (ruCj i j) := eq_of_glCode28 (by
      rw [glCode28_mul, glCode28_mul, glCode28_ruXE hi, glCode28_ruXE hj, glCode28_ruNFE he]
      exact hc)
    have : (ruXE i)⁻¹ * ruXE j * ruXE i = ruNFE (ruCj i j) := by
      rw [mul_assoc, h, ← mul_assoc, inv_mul_cancel, one_mul]
    rw [this]
    exact ruNFE_mem_pcSub hb
  have hpc := isPGroup_two_of_pc 14 ruXE hsq hcj
  refine hpc.to_le ?_
  rw [ruT, Subgroup.closure_le]
  rintro _ ⟨k, hk, rfl⟩
  obtain ⟨he, hc⟩ := ru_tnf_check k hk
  have : ruTGen k = ruNFE (ruTnf k) :=
    eq_of_glCode28 (by rw [glCode28_ruTGen hk, glCode28_ruNFE he]; exact hc)
  rw [this]
  exact ruNFE_mem_pcSub fun q hq => absurd hq (Nat.not_lt_zero q)

@[expose] noncomputable def ruGP (c : ℕ) : GL (Fin 28) (ZMod 2) := ruWord (ruGW.getD c [])

theorem glCode28_ruGP {c : ℕ} (hc : c < 2) : glCode28 (ruGP c) = ruG c := by
  rw [ruGP, glCode28_ruWord]
  exact (ru_g_check c hc).2

@[expose] noncomputable def ruLetE (l : ℕ) : GL (Fin 28) (ZMod 2) :=
  if l < 16384 then ruNFE l else ruGP (l - 16384)

theorem glCode28_ruLetE {l : ℕ} (hl : l < 16386) : glCode28 (ruLetE l) = ruLet l := by
  unfold ruLetE ruLet
  split_ifs with h
  · exact glCode28_ruNFE h
  · exact glCode28_ruGP (by omega)

theorem ruLetE_mem (l : ℕ) : ruLetE l ∈ ruGroup := by
  unfold ruLetE
  split_ifs
  · exact ruT_le (ruNFE_mem l)
  · exact ruWord_mem _

@[expose] noncomputable def ruLWord : List ℕ → GL (Fin 28) (ZMod 2)
  | [] => 1
  | l :: w => ruLetE l * ruLWord w

theorem glCode28_ruLWord : ∀ w : List ℕ, (∀ l ∈ w, l < 16386) →
    glCode28 (ruLWord w) = ruLWordC w
  | [], _ => glCode28_one
  | l :: w, hw => by
    rw [ruLWord, ruLWordC, glCode28_mul, glCode28_ruLetE (hw l List.mem_cons_self),
      glCode28_ruLWord w fun l' hl' => hw l' (List.mem_cons_of_mem _ hl')]

theorem ruLWord_mem : ∀ w : List ℕ, ruLWord w ∈ ruGroup
  | [] => one_mem _
  | l :: w => mul_mem (ruLetE_mem l) (ruLWord_mem w)

@[expose] noncomputable def ruDP (j : ℕ) : GL (Fin 28) (ZMod 2) := ruLWord (ruDW.getD j [])

theorem glCode28_ruDP {j : ℕ} (hj : j < 847) : glCode28 (ruDP j) = ruD j := by
  obtain ⟨h1, h2⟩ := ru_d_check hj
  rw [ruDP, glCode28_ruLWord _ h1]
  exact h2

theorem ruDP_zero : ruDP 0 = 1 := by
  rw [ruDP, ru_dw_zero]
  rfl

@[expose] def ruU : Set (GL (Fin 28) (ZMod 2)) :=
  {x | ∃ j < 847, ∃ t ∈ ruT, ∃ t' ∈ ruT, x = t * ruDP j * t'}

theorem one_mem_ruU : (1 : GL (Fin 28) (ZMod 2)) ∈ ruU :=
  ⟨0, by norm_num, 1, one_mem _, 1, one_mem _, by rw [ruDP_zero]; group⟩

theorem ruU_mul_T {x s : GL (Fin 28) (ZMod 2)} (hx : x ∈ ruU) (hs : s ∈ ruT) : x * s ∈ ruU := by
  obtain ⟨j, hj, t, ht, t', ht', rfl⟩ := hx
  exact ⟨j, hj, t, ht, t' * s, mul_mem ht' hs, by group⟩

theorem ru_coset_g {c : ℕ} (hc : c < 2) {t : GL (Fin 28) (ZMod 2)} (ht : t ∈ ruT) :
    ∃ s < ruM c, ∃ v ∈ ruT, t * ruGP c = ruNFE (ruR c s) * ruGP c * v := by
  obtain ⟨hM, hR0, hcl⟩ := ru_gcl_check c hc
  refine closure_subset_of_left_closed (S := {x | ∃ k < 3, ruTGen k = x})
    (P := {t | ∃ s < ruM c, ∃ v ∈ ruT, t * ruGP c = ruNFE (ruR c s) * ruGP c * v})
    (fun s _ => ⟨orderOf s, orderOf_pos s, pow_orderOf_eq_one s⟩)
    ⟨0, hM, 1, one_mem _, by rw [hR0, ruNFE_zero]; group⟩ ?_ ht
  rintro p ⟨s, hs, v, hv, hpv⟩ _ ⟨k, hk, rfl⟩
  obtain ⟨hs', hr, hr', hcert⟩ := hcl k hk s hs
  have key : ruTGen k * ruNFE (ruR c s) * ruGP c = ruNFE (ruR c (ruCL c (ruM c * k + s) / 16384)) *
      ruGP c * ruNFE (ruCL c (ruM c * k + s) % 16384) := eq_of_glCode28 (by
    rw [glCode28_mul, glCode28_mul, glCode28_mul, glCode28_mul, glCode28_ruTGen hk,
      glCode28_ruNFE hr, glCode28_ruGP hc, glCode28_ruNFE hr',
      glCode28_ruNFE (Nat.mod_lt _ (by norm_num))]
    exact hcert)
  refine ⟨_, hs', ruNFE (ruCL c (ruM c * k + s) % 16384) * v, mul_mem (ruNFE_mem _) hv, ?_⟩
  calc ruTGen k * p * ruGP c = ruTGen k * (p * ruGP c) := by group
    _ = ruTGen k * (ruNFE (ruR c s) * ruGP c * v) := by rw [hpv]
    _ = ruTGen k * ruNFE (ruR c s) * ruGP c * v := by group
    _ = _ := by rw [key]; group

theorem ruU_mul_g {c : ℕ} (hc : c < 2) {x : GL (Fin 28) (ZMod 2)} (hx : x ∈ ruU) :
    x * ruGP c ∈ ruU := by
  obtain ⟨j, hj, t, ht, t', ht', rfl⟩ := hx
  obtain ⟨s, hs, v, hv, hve⟩ := ru_coset_g hc ht'
  obtain ⟨hk, hr, hdeq⟩ := ru_gdec_spec hc hj hs
  generalize ruDec c (ruM c * j + s) = e at hk hdeq
  have hd : ruDP j * ruNFE (ruR c s) * ruGP c =
      ruNFE (e / 16384 % 16384) * ruDP (e / 268435456) * ruNFE (e % 16384) := eq_of_glCode28 (by
    rw [glCode28_mul, glCode28_mul, glCode28_mul, glCode28_mul, glCode28_ruDP hj,
      glCode28_ruNFE hr, glCode28_ruGP hc, glCode28_ruNFE (Nat.mod_lt _ (by norm_num)),
      glCode28_ruDP hk, glCode28_ruNFE (Nat.mod_lt _ (by norm_num))]
    exact hdeq)
  refine ⟨e / 268435456, hk, t * ruNFE (e / 16384 % 16384), mul_mem ht (ruNFE_mem _),
    ruNFE (e % 16384) * v, mul_mem (ruNFE_mem _) hv, ?_⟩
  calc t * ruDP j * t' * ruGP c = t * ruDP j * (t' * ruGP c) := by group
    _ = t * ruDP j * (ruNFE (ruR c s) * ruGP c * v) := by rw [hve]
    _ = t * (ruDP j * ruNFE (ruR c s) * ruGP c) * v := by group
    _ = _ := by rw [hd]; group

theorem ruU_mul_LetE {x : GL (Fin 28) (ZMod 2)} (hx : x ∈ ruU) {l : ℕ} (hl : l < 16386) :
    x * ruLetE l ∈ ruU := by
  unfold ruLetE
  split_ifs with h
  · exact ruU_mul_T hx (ruNFE_mem l)
  · exact ruU_mul_g (by omega) hx

theorem ruU_mul_LWord : ∀ (w : List ℕ), (∀ l ∈ w, l < 16386) → ∀ {x : GL (Fin 28) (ZMod 2)},
    x ∈ ruU → x * ruLWord w ∈ ruU
  | [], _, x, hx => by rw [ruLWord, mul_one]; exact hx
  | l :: w, hw, x, hx => by
    rw [ruLWord, ← mul_assoc]
    exact ruU_mul_LWord w (fun l' hl' => hw l' (List.mem_cons_of_mem _ hl'))
      (ruU_mul_LetE hx (hw l List.mem_cons_self))

theorem ruU_mul_ab {x : GL (Fin 28) (ZMod 2)} (hx : x ∈ ruU) :
    x * ruUA ∈ ruU ∧ x * ruUB ∈ ruU := by
  obtain ⟨h1, h2, h3, h4⟩ := ru_ab_check
  have ha : ruUA = ruLWord ruAW :=
    eq_of_glCode28 (by rw [glCode28_ruUA, glCode28_ruLWord _ h2, h1])
  have hb : ruUB = ruLWord ruBW :=
    eq_of_glCode28 (by rw [glCode28_ruUB, glCode28_ruLWord _ h4, h3])
  rw [ha, hb]
  exact ⟨ruU_mul_LWord _ h2 hx, ruU_mul_LWord _ h4 hx⟩

theorem ruGroup_subset_U : (ruGroup : Set (GL (Fin 28) (ZMod 2))) ⊆ ruU := by
  refine closure_subset_of_right_closed
    (fun s _ => ⟨orderOf s, orderOf_pos s, pow_orderOf_eq_one s⟩) one_mem_ruU ?_
  rintro p hp s (rfl | rfl)
  · exact (ruU_mul_ab hp).1
  · exact (ruU_mul_ab hp).2

@[expose] def RuBadPrime (p : ℕ) : Prop := p = 5 ∨ p = 7 ∨ p = 13 ∨ p = 29

theorem ru_not_mem_of_bad {H : Subgroup (GL (Fin 28) (ZMod 2))} (hTH : ruT ≤ H)
    (hp : ∀ p, RuBadPrime p → ¬ p ∣ Nat.card H) {j : ℕ} (hj : j < 847) (hj3 : 3 ≤ j)
    (hD : ruDP j ∈ H) : False := by
  obtain ⟨hp', hu, hpow, hne⟩ := ru_bad_check hj hj3
  set p := ruBad j % 32 with hpdef
  have hprime : p.Prime := by rcases hp' with h | h | h | h <;> rw [h] <;> norm_num
  have : Fact p.Prime := ⟨hprime⟩
  let x : H := ⟨(ruDP j * ruNFE (ruBad j / 1024)) ^ (ruBad j / 32 % 32),
    pow_mem (mul_mem hD (hTH (ruNFE_mem _))) _⟩
  have hcode : glCode28 (x : GL (Fin 28) (ZMod 2)) = powC28 ruOneC (ruBad j / 32 % 32)
      (mulF28 (ruD j) (ruNFC (ruBad j / 1024))) := by
    show glCode28 ((ruDP j * ruNFE (ruBad j / 1024)) ^ (ruBad j / 32 % 32)) = _
    rw [glCode28_pow, glCode28_mul, glCode28_ruDP hj, glCode28_ruNFE hu, glCode28_one]
  have hxp : x ^ p = 1 := by
    apply Subtype.ext
    apply eq_of_glCode28
    rw [Subgroup.coe_pow, glCode28_pow, hcode, Subgroup.coe_one, glCode28_one]
    exact hpow
  have hx1 : x ≠ 1 := by
    intro h
    apply hne
    rw [← hcode, h, Subgroup.coe_one, glCode28_one]
  exact hp p (by rcases hp' with h | h | h | h <;> [left; (right; left); (right; right; left);
    (right; right; right)] <;> exact h) (orderOf_eq_prime hxp hx1 ▸ orderOf_dvd_natCard x)

theorem ru_cos {j : ℕ} (hj0 : 0 < j) (hj : j < 3) {t : GL (Fin 28) (ZMod 2)} (ht : t ∈ ruT) :
    ∃ r < 2, ∃ v ∈ ruT, t * ruDP j = ruNFE (ruCR j r) * ruDP j * v := by
  obtain ⟨hR0, hcos⟩ := ru_cos_check (j - 1) (by omega)
  rw [Nat.sub_add_cancel hj0] at hR0 hcos
  refine closure_subset_of_left_closed (S := {x | ∃ k < 3, ruTGen k = x})
    (P := {t | ∃ r < 2, ∃ v ∈ ruT, t * ruDP j = ruNFE (ruCR j r) * ruDP j * v})
    (fun s _ => ⟨orderOf s, orderOf_pos s, pow_orderOf_eq_one s⟩)
    ⟨0, by norm_num, 1, one_mem _, by rw [hR0, ruNFE_zero]; group⟩ ?_ ht
  rintro p ⟨r, hr, v, hv, hpv⟩ _ ⟨k, hk, rfl⟩
  obtain ⟨hr', hcr, hcr', hcert⟩ := hcos k hk r hr
  have key : ruTGen k * ruNFE (ruCR j r) * ruDP j = ruNFE (ruCR j (ruCosE j (2 * k + r) / 16384)) *
      ruDP j * ruNFE (ruCosE j (2 * k + r) % 16384) := eq_of_glCode28 (by
    rw [glCode28_mul, glCode28_mul, glCode28_mul, glCode28_mul, glCode28_ruTGen hk,
      glCode28_ruNFE hcr, glCode28_ruDP (by omega), glCode28_ruNFE hcr',
      glCode28_ruNFE (Nat.mod_lt _ (by norm_num))]
    exact hcert)
  refine ⟨_, hr', ruNFE (ruCosE j (2 * k + r) % 16384) * v, mul_mem (ruNFE_mem _) hv, ?_⟩
  calc ruTGen k * p * ruDP j = ruTGen k * (p * ruDP j) := by group
    _ = ruTGen k * (ruNFE (ruCR j r) * ruDP j * v) := by rw [hpv]
    _ = ruTGen k * ruNFE (ruCR j r) * ruDP j * v := by group
    _ = _ := by rw [key]; group

theorem ru_card_le {H : Subgroup (GL (Fin 28) (ZMod 2))} (hTH : ruT ≤ H) (hH : H ≤ ruGroup)
    (hp : ∀ p, RuBadPrime p → ¬ p ∣ Nat.card H) : Nat.card H ≤ 5 * Nat.card ruT := by
  have : Finite ruT := Subgroup.instFiniteSubtypeMem _
  refine card_le_of_cover ![1, ruDP 1, ruNFE (ruCR 1 1) * ruDP 1, ruDP 2,
    ruNFE (ruCR 2 1) * ruDP 2] fun h hh => ?_
  obtain ⟨j, hj, t, ht, t', ht', rfl⟩ := ruGroup_subset_U (hH hh)
  have hD : ruDP j ∈ H := by
    have e : ruDP j = t⁻¹ * (t * ruDP j * t') * t'⁻¹ := by group
    rw [e]
    exact mul_mem (mul_mem (inv_mem (hTH ht)) hh) (inv_mem (hTH ht'))
  rcases Nat.lt_or_ge j 3 with hj3 | hj3
  · interval_cases j
    · exact ⟨0, t * t', mul_mem ht ht', by rw [ruDP_zero]; simp⟩
    · obtain ⟨r, hr, v, hv, e⟩ := ru_cos (j := 1) (by norm_num) (by norm_num) ht
      interval_cases r
      · refine ⟨1, v * t', mul_mem hv ht', ?_⟩
        rw [e]
        have h0 : ruCR 1 0 = 0 := (ru_cos_check 0 (by norm_num)).1
        simp [h0, ruNFE_zero, mul_assoc]
      · exact ⟨2, v * t', mul_mem hv ht', by rw [e]; simp [mul_assoc]⟩
    · obtain ⟨r, hr, v, hv, e⟩ := ru_cos (j := 2) (by norm_num) (by norm_num) ht
      interval_cases r
      · refine ⟨3, v * t', mul_mem hv ht', ?_⟩
        rw [e]
        have h0 : ruCR 2 0 = 0 := (ru_cos_check 1 (by norm_num)).1
        simp [h0, ruNFE_zero, mul_assoc]
      · exact ⟨4, v * t', mul_mem hv ht', by rw [e]; simp [mul_assoc]⟩
  · exact (ru_not_mem_of_bad hTH hp hj hj3 hD).elim

@[expose] noncomputable def carrierRuEquiv : NativeSporadic.Carrier .Ru ≃* NativeSporadic.Ru :=
  MulEquiv.refl _

theorem ru_embedding {X : Type} [Group X] (e : X ≃* NativeSporadic.Carrier .Ru) :
    ∃ φ : X →* GL (Fin 28) (ZMod 2), Function.Injective φ ∧ (∀ x, φ x ∈ ruGroup) ∧
      ∀ y ∈ ruGroup, ∃ x, φ x = y := by
  obtain ⟨ψ, -⟩ : ∃ ψ : X ≃* ↥ruGroup, ψ = (e.trans carrierRuEquiv).trans ruNativeEquiv :=
    ⟨_, rfl⟩
  refine ⟨(Subgroup.subtype _).comp (ψ : X →* ↥ruGroup), fun a b h => ψ.injective
    (Subgroup.subtype_injective _ h), fun x => (ψ x).2, fun y hy => ?_⟩
  obtain ⟨x, hx⟩ := ψ.surjective ⟨y, hy⟩
  exact ⟨x, congrArg Subtype.val hx⟩

theorem noE9Config_ru :
    NoE9Config fun (X : Type) [Group X] => Nonempty (X ≃* NativeSporadic.Carrier .Ru) := by
  intro A _ _ L P T ⟨e⟩ hcfg
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨φ₀, hφ₀, hφ₀mem, hφ₀surj⟩ := ru_embedding e
  obtain ⟨φ, hφ, hφG, -, hTφ⟩ :=
    E9Config.exists_model_conj hcfg hφ₀ hφ₀mem hφ₀surj ruT_le ruT_isPGroup
  have hHL : P ⊔ (T ⊓ L) ≤ L := E9Config.sup_inf_le hcfg
  have hS := E9Config.isSylowTwoOf_inf hcfg
  obtain ⟨K, hKdef⟩ : ∃ R : Subgroup (GL (Fin 28) (ZMod 2)),
      R = ((P ⊔ (T ⊓ L)).subgroupOf L).map φ := ⟨_, rfl⟩
  have hTK : ruT ≤ K := by
    rw [hKdef]
    exact hTφ.trans (Subgroup.map_mono (Subgroup.subgroupOf_mono L le_sup_right))
  have hKM : K ≤ ruGroup := by
    rw [hKdef]
    rintro _ ⟨u, -, rfl⟩
    exact hφG _
  have hKc : Nat.card K = Nat.card (P ⊔ (T ⊓ L) : Subgroup A) := by
    rw [hKdef, ← Nat.card_congr (((P ⊔ (T ⊓ L)).subgroupOf L).equivMapOfInjective _ hφ).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHL).toEquiv]
  have hHc := E9Config.card_sup_inf hcfg
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hS.2.1
  have hle := ru_card_le hTK hKM fun p hp => by
    rw [hKc, hHc, hk]
    have hprime : p.Prime := by rcases hp with h | h | h | h <;> rw [h] <;> norm_num
    exact prime_not_dvd_nine_mul_two_pow hprime (by rcases hp with h | h | h | h <;> omega)
      (by rcases hp with h | h | h | h <;> omega)
  have hTU : Nat.card ruT ≤ Nat.card (T ⊓ L : Subgroup A) := by
    rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hS.1).toEquiv,
      Nat.card_congr (((T ⊓ L).subgroupOf L).equivMapOfInjective _ hφ).toEquiv]
    have : Finite (((T ⊓ L).subgroupOf L).map φ) := Subgroup.instFiniteSubtypeMem _
    exact Subgroup.card_le_of_le hTφ
  have hpos : 0 < Nat.card ruT := Nat.card_pos
  rw [hKc, hHc] at hle
  omega

theorem orderThree_ru :
    OrderThree fun (X : Type) [Group X] => Nonempty (X ≃* NativeSporadic.Carrier .Ru) := by
  intro X _ ⟨e⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hl, h3, hne⟩ := ru_three_check
  obtain ⟨φ, hφ, -, hφsurj⟩ := ru_embedding e
  obtain ⟨x, hx⟩ := hφsurj (ruLWord ruThreeW) (ruLWord_mem _)
  have hcode : glCode28 (ruLWord ruThreeW) = ruLWordC ruThreeW := glCode28_ruLWord _ hl
  have hx3 : x ^ 3 = 1 := hφ (by
    rw [map_pow, hx, map_one]
    apply eq_of_glCode28
    rw [pow_succ', pow_succ', pow_one, glCode28_mul, glCode28_mul, hcode, glCode28_one]
    exact h3)
  have hx1 : x ≠ 1 := fun h => hne (by rw [← hcode, ← hx, h, map_one, glCode28_one])
  rw [← orderOf_eq_prime hx3 hx1]
  exact orderOf_dvd_natCard x

end CFSG.Quasithin.F134
